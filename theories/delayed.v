From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import agree auth excl updates local_updates.
From esop Require Import typetranslation corecalculus specification types overlap oneshot.
From stdpp Require Import gmap set coPset.

Section Definitions.
  Context `{allG Σ}.
  Local Open Scope I.

  Definition simulation:
    env → expr → hexpr → gset gname → type → hexpr → conn_map → conn_map → iProp Σ
    := simulation_body int_s_type int_s_heap.
  
  Definition delayed_typed Γ η e e' A τ η' :=
    ∀ D N σ,
      (int_i_env Γ D N σ ∗ int_i_heap η D N)
        -∗ WP subst (of_val <$> σ) e
        {{ xᵢ, ∃ Nᵢ' D' d', ⌜N ≡[ not_new A ]≡ Nᵢ' ∧ D' !! RET = Some d'⌝ ∧
                            int_i_type τ d' Nᵢ'  xᵢ ∧
                            (□simulation Γ e' η A τ η' D D') ∧
                            int_i_heap η' D' Nᵢ' }}.
  Record delayed_simulation U Γ (η: hexpr) e e' A (τ: type) (η': hexpr) :=
    Delayed {
        ds_used_names: names Γ ∪ names η ⊆ U;
        ds_type_e: typing U Γ e η A τ η';
        ds_type_e': typing U Γ e' η A τ η';
        ds_sim: delayed_typed Γ η e e' A τ η'
      }.
End Definitions.

Section Meta.
  Context `{allG Σ}.
  Local Open Scope I.
  (** Meta-theory: The binding lemma *)
  Definition strengthen Γ x (d: val) (D D': conn_map) := <[var x:=d]>(D ~[conn_env Γ]~> D').
  
  Lemma strengthen_env_generic
        (int_ty: type → @intT_type Σ) (ϕ: conn_map → name_map → iProp Σ)
        (Γ: env) (τ: type) x (D D': conn_map) v d (σ: gmap string val)
        (N N': name_map)
        (L: gset conn_name) (disj: conn_env Γ ⊥ L) (notin: var x ∉ L) O (Osub: names Γ ⊆ O)
        (ϕ_local: Proper (overlap L ==> eq ==> (⊣⊢)) ϕ)
        (int_local: ∀ τ, Proper (eq ==> overlap (names τ) ==> eq ==> (⊣⊢)) (int_ty τ)):
    int_env_pre int_ty Γ D N σ -∗ (⌜N ≡[O]≡ N'⌝ ∗ int_ty τ d N' v ∗ ϕ D' N') -∗
         let D'' := strengthen Γ x d D D' in
         int_env_pre int_ty (<[x:=τ]>Γ) D'' N' (<[x:=v]>σ) ∗ ϕ D'' N'.
  Proof.
    iIntros "intΓ [eqN [intτ ϕ]]".
    iDestruct "eqN" as %eqN; cbn.
    iSplitR "ϕ".
    { iDestruct "intΓ" as "[dom intΓ]".
      iDestruct "dom" as %[domσ domD].
      iSplit.
      { iPureIntro; split.
        { intros y; by rewrite !lookup_insert_is_Some domσ. }
        { intros y.
          rewrite /strengthen !lookup_insert_is_Some.
          intros [<-|[neqxy iny]]; first auto.
          right; split; first congruence.
          rewrite lookup_merge_along_in; first auto.
          rewrite elem_of_conn_env; exists y; auto. }
      }
      iIntros (x' τ' v' d' [lookupτ [lookupv lookupd]]).
      destruct (decide (x=x')) as [<-|neq].
      { rewrite lookup_insert in lookupd; injection lookupd as <-.
        rewrite lookup_insert in lookupv; injection lookupv as <-.
        rewrite lookup_insert in lookupτ; injection lookupτ as <-.
        iFrame.
      } {
        rewrite lookup_insert_ne in lookupτ; last done.
        rewrite lookup_insert_ne in lookupd; last congruence.
        rewrite lookup_insert_ne in lookupv; last done.
        iSpecialize ("intΓ" $! x' τ' v' d' with "[]").
        { iPureIntro; repeat split; auto.
          rewrite lookup_merge_along_in in lookupd; auto.
          rewrite elem_of_conn_env.
          exists x'; split; eauto. }
        assert (names τ' ⊆ O).
        { etrans; last done.
          intros ξ inξ.
          rewrite elem_of_names_env; eauto. }
        iApply (int_local with "intΓ").
        1,3: done.
        eapply overlap_sub; done. }
    }
    enough (overlap L D' (<[var x:=d]>(D ~[conn_env Γ]~> D'))) as ov.
    { by rewrite /strengthen -ov. }
    intros n inn.
    rewrite lookup_insert_ne.
    2: by intros <-.
    rewrite lookup_merge_along_not_in; first done.
    clear -disj inn.
    set_solver.
  Qed.

  Lemma bind_existential_part (x: string) e K Γ τ₁ τ₂ η₁ η₂ η₃ A₁ A₂ (D₁ D₂ D₃: conn_map) d
        (d_good: D₂!!RET = Some d) (Γ_names_good: names Γ ⊥ A₁)
        (x_fresh: ∀ e', subst_ctx (<[x:=e']>∅) K = K):
    simulation Γ e η₁ A₁ τ₁ η₂ D₁ D₂
               -∗ simulation (<[x:=τ₁]>Γ) (fill_ctx x K) η₂ A₂ τ₂ η₃
               (strengthen Γ x d D₁ D₂) D₃
               -∗ simulation Γ (fill_ctx e K) η₁ (A₁ ∪ A₂) τ₂ η₃ D₁ D₃.
  Proof.
    iIntros "sime simK".
    iIntros (N σ p K') "#ctx [#Γ pre] step".
    rewrite subst_fill fill_ctx_app.
    iMod ("sime" $! N σ p (subst_ctx (of_val <$> σ) K++K')
          with "ctx [$Γ $pre] step") as (v₁) "[post step]".
    iDestruct "post" as (d' N') "[props [ty pre]]".
    iDestruct "props" as %[eqN eqd].
    replace d' with d in * by congruence.
    iPoseProof (strengthen_env_generic int_s_type (int_s_heap η₂) Γ τ₁ x D₁ D₂
                                       v₁ d σ N N' (conn_heap η₂))
      as "str".
    { intro; rewrite elem_of_conn_env elem_of_conn_heap => [[? [? _]] [? [? _]]]; congruence. }
    { by rewrite elem_of_conn_heap => [[? [? _]]]. }
    { done. }
    { intros D D' eqD ?? <-; by apply int_s_heap_local. }
    iDestruct ("str" with "Γ [$ty $pre]") as "[Γ' pre]".
    { iPureIntro.
      assert (of_gset (names Γ) ⊆ not_new A₁).
      { intro ξ.
        rewrite elem_of_of_gset elem_of_not_new => [inξ].
        intros []%Γ_names_good; done. }
      apply overlap_cast, (overlap_sub (not_new A₁)); auto.
    }
    rewrite -fill_ctx_app -(subst_val v₁ (of_val <$> σ)) -subst_fill.
    iMod ("simK" $! N' (<[x := v₁]>σ) p K' with "ctx [$Γ' $pre] [step]")
      as (v₂) "[post step]".
    { rewrite fmap_insert subst_insert_r; auto using val_closed.
      rewrite (subst_fill (<[x:=of_val v₁]>∅)) x_fresh /= lookup_insert //. }
    iDestruct "post" as (d'' N'') "[eqs post]".
    iModIntro.
    iExists v₂; iFrame.
    iExists d'', N''; iFrame.
    iDestruct "eqs" as %[eqN' eqd'].
    iPureIntro; split; auto.
    eapply overlap_trans; eauto.
  Qed.

  Lemma bind_universal_part (x: string) e e' K K' Γ τ₁ τ₂ η₁ η₂ η₃ A₁ A₂
        (Γ_names_good: names Γ ⊥ A₁)
        (x_fresh: ∀ e', subst_ctx (<[x:=e']>∅) K = K)
        (x_fresh': ∀ e', subst_ctx (<[x:=e']>∅) K' = K'):
    delayed_typed Γ η₁ e e' A₁ τ₁ η₂
                  -∗ delayed_typed (<[x:=τ₁]>Γ) η₂ (fill_ctx x K) (fill_ctx x K') A₂ τ₂ η₃
                  -∗ delayed_typed Γ η₁ (fill_ctx e K) (fill_ctx e' K') (A₁ ∪ A₂) τ₂ η₃.
  Proof.
    iIntros "dele delK".
    iIntros (D Ni σi) "[#intΓ intη]".
    rewrite subst_fill.
    iApply wp_bind.
    iSpecialize ("dele" $! D Ni σi with "[$intΓ $intη]").
    iApply (wp_wand with "dele [-]").
    iIntros (v) "post".
    iDestruct "post" as (Ni' D' d') "[rel [intτ [#sim intη']]]".
    replace (fill_ctx (of_val v) (subst_ctx (of_val <$> σi) K))
    with (subst (of_val <$> (<[x:=v]>σi)) (fill_ctx x K)); cycle 1.
    { rewrite fmap_insert subst_insert_r; auto using val_closed.
      rewrite subst_fill /= lookup_insert x_fresh -(subst_val _ (of_val <$> σi)) -subst_fill.
      rewrite subst_val //. }
    iDestruct "rel" as %[eqN eqd].
    iSpecialize ("delK" $! (strengthen Γ x d' D D') Ni' (<[x:=v]>σi) with "[intτ intη']").
    { iApply (strengthen_env_generic
                int_i_type (int_i_heap η₂) Γ τ₁ x D D' v d' σi Ni Ni' (conn_heap η₂)
              with "intΓ [intτ intη']").
      - intro n.
        rewrite elem_of_conn_env elem_of_conn_heap => [[? [? _]] [? [? _]]]; congruence.
      - rewrite elem_of_conn_heap => [[? [? _]]]; done.
      - done.
      - intros D₁ D₂ eqD ?? <-.
        apply int_i_heap_local; auto; done.
      - iFrame.
        iPureIntro.
        assert (of_gset (names Γ) ⊆ not_new A₁).
        { intro ξ; rewrite elem_of_of_gset elem_of_not_new; exact (Γ_names_good ξ). }
        apply overlap_cast, (overlap_sub (not_new A₁)); auto.
    }
    iApply (wp_wand with "delK").
    iIntros (v') "post".
    iDestruct "post" as (Ni'' D'' d'') "[pure [intτ [#sim' intη]]]".
    iDestruct "pure" as %[eqN' eqD'].
    iExists Ni'', D'', d''; iFrame.
    iSplit.
    { iPureIntro; repeat split; eauto using overlap_trans. }
    iAlways.
    iApply (bind_existential_part with "sim sim'"); auto.
  Qed.

  Lemma delayed_bind
        (x: string) e e' K K' Γ τ₁ τ₂ η₁ η₂ η₃ U A₁ A₂
        (x_fresh: ∀ e', subst_ctx (<[x:=e']>∅) K = K)
        (x_fresh': ∀ e', subst_ctx (<[x:=e']>∅) K' = K')
        (dele: delayed_simulation U Γ η₁ e e' A₁ τ₁ η₂)
        (delK: delayed_simulation (U ∪ A₁) (<[x:=τ₁]>Γ) η₂ (fill_ctx x K) (fill_ctx x K') A₂ τ₂ η₃):
    delayed_typed Γ η₁ (fill_ctx e K) (fill_ctx e' K') (A₁ ∪ A₂) τ₂ η₃.
  Proof.
    destruct dele as [namese tye tye' dele].
    destruct delK as [namesK tyK tyK' delK].
    iApply bind_universal_part.
    2,3: done.
    2: iApply dele.
    2: iApply delK.
    apply typing_good_names in tye.
    2,3: clear -namese; set_solver.
    set_solver.
  Qed.
End Meta.
