From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import agree auth excl updates local_updates.
From esop Require Import typetranslation corecalculus specification types overlap oneshot.
From stdpp Require Import gmap set coPset.

Module Delayed(AxSem: AxiomaticSemantics).
  Module Import Axiomatics := AxSem <+ AxiomaticFacts.
  Instance: WaitPermissions :=
    Build_WaitPermissions axiomaticIrisG _ (@wait).

  Section Definitions.
    Context `{specStateG Σ} {Hiris: wp_axiomaticIrisG Σ} `{taskDataG Σ, InitialConfiguration}.
    Instance: axiomaticIrisG Σ := Hiris.
    Typeclasses Transparent axiomaticIrisG.
    Local Open Scope I.

    Definition simulation Γ e η A τ η' D M D' M': iProp Σ :=
      ∀ N σ, existential_triple ⊤ initial_cfg
                                (int_s_env Γ D M N σ ∗ int_s_heap η D M N)
                                (subst (of_val <$> σ) e)
                                (λ v, ∃ d N',
                                    ⌜M ≡[not_new A]≡ M' ∧ N ≡[not_new A]≡ N' ∧ D' !! RET = Some d⌝ ∧
                                    int_s_type τ d M' N' v ∗ int_s_heap η' D' M' N').
    
    Definition delayed_typed Γ η e e' A τ η' :=
      ∀ D M N σ,
        (int_i_env Γ D M N σ ∗ int_i_heap η D M N)
          -∗ WP subst (of_val <$> σ) e
          {{ xᵢ, ∃ Nᵢ' M' D' d', ⌜N ≡[ not_new A ]≡ Nᵢ' ∧ M ≡[ not_new A ]≡ M' ∧
                                 D' !! RET = Some d'⌝ ∗
                             int_i_type τ d' M' Nᵢ'  xᵢ ∗
                             int_i_heap η' D' M' Nᵢ' ∗
                             □simulation Γ e' η A τ η' D M D' M' }}.
    Record delayed_simulation U Γ (η: heap) e e' A (τ: type) (η': heap) :=
      Delayed {
          ds_used_names: names Γ ∪ names η ⊆ U;
          ds_type_e: typing U Γ e η A τ η';
          ds_type_e': typing U Γ e' η A τ η';
          ds_sim: delayed_typed Γ η e e' A τ η'
        }.

    (** Meta-theory: The binding lemma *)
    Definition strengthen Γ x (d: val) (D D': conn_map) := <[var x:=d]>(D ~[names_env Γ]~> D').
    
    Lemma strengthen_env_generic
          (int_ty: type → @int_type Σ) (ϕ: conn_map → task_map → name_map → iProp Σ)
          (Γ: env) (τ: type) x (D D': conn_map) v d (σ: gmap string val) (M M': task_map)
          (N N': name_map)
          (L: gset conn_name) (disj: names_env Γ ⊥ L) (notin: var x ∉ L) O (Osub: names Γ ⊆ O)
          (ϕ_local: Proper (overlap L ==> eq ==> eq ==> (⊣⊢)) ϕ)
          (int_local: ∀ τ, Proper (eq ==> overlap (names τ) ==> overlap (names τ) ==> eq ==> (⊣⊢))
                                  (int_ty τ)):
      intΓ int_ty Γ D M N σ -∗ (⌜N ≡[O]≡ N' ∧ M ≡[O]≡ M'⌝ ∗ int_ty τ d M' N' v ∗ ϕ D' M' N') -∗
           let D'' := strengthen Γ x d D D' in
           intΓ int_ty (<[x:=τ]>Γ) D'' M' N' (<[x:=v]>σ) ∗ ϕ D'' M' N'.
    Proof.
      iIntros "intΓ [eqN [intτ ϕ]]".
      iDestruct "eqN" as %[eqM eqN]; cbn.
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
            rewrite elem_of_names_env; exists y; auto. }
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
            rewrite elem_of_names_env.
            exists x'; split; eauto. }
          assert (names τ' ⊆ O).
          { etrans; last done.
            intros ξ inξ.
            rewrite env_elem_of_names; eauto. }
          iApply (int_local with "intΓ").
          1,4: done.
          all: eapply overlap_mono; eauto; done. }
      }
      enough (overlap L D' (<[var x:=d]>(D ~[names_env Γ]~> D'))) as ov.
      { by rewrite /strengthen -ov. }
      intros n inn.
      rewrite lookup_insert_ne.
      2: by intros <-.
      rewrite lookup_merge_along_not_in; first done.
      clear -disj inn.
      set_solver.
    Qed.

    Lemma good_overlap A A': not_new (A ∪ A') ⊆ not_new A ∩ not_new A'.
    Proof.
      intro ξ.
      rewrite /not_new elem_of_intersection !elem_of_difference !elem_of_of_gset
              not_elem_of_union.
      tauto.
    Qed.

    Lemma overlap_trans {X} A A' (N N' N'': gmap gname X):
      N ≡[not_new A]≡ N' → N' ≡[not_new A']≡ N'' →
      N ≡[not_new (A ∪ A')]≡ N''.
    Proof.
      intros ov1 ov2.
      pose proof (good_overlap A A') as ov.
      etrans.
      all: eapply overlap_mono.
      2,3,6,7: done.
      2,4: eassumption.
      all: clear -ov.
      all: set_solver.
    Qed.

    Local Open Scope I.
    Context {wait_Proper: ∀ t, Proper (pointwise_relation _ (⊣⊢) ==> (⊣⊢)) (wait t)}.
    
    Lemma existential_part (x: string) e K Γ τ₁ τ₂ η₁ η₂ η₃ A₁ A₂ (D₁ D₂ D₃: conn_map)
          (M₁ M₂ M₃: task_map) d
          (d_good: D₂!!RET = Some d) (Γ_names_good: names Γ ⊥ A₁)
          (x_fresh: ∀ e', subst_ctx (<[x:=e']>∅) K = K):
      simulation Γ e η₁ A₁ τ₁ η₂ D₁ M₁ D₂ M₂
                 -∗ simulation (<[x:=τ₁]>Γ) (fill_ctx x K) η₂ A₂ τ₂ η₃
                 (strengthen Γ x d D₁ D₂) M₂ D₃ M₃
                 -∗ simulation Γ (fill_ctx e K) η₁ (A₁ ∪ A₂) τ₂ η₃ D₁ M₁ D₃ M₃.
    Proof.
      iIntros "sime simK".
      iIntros (N σ p K') "#ctx [#Γ pre] step".
      rewrite subst_fill fill_ctx_app.
      iMod ("sime" $! N σ p (subst_ctx (of_val <$> σ) K++K')
              with "ctx [$Γ $pre] step") as (v₁) "[post step]".
      iDestruct "post" as (d' N') "[props [ty pre]]".
      iDestruct "props" as %[eqM [eqN eqd]].
      replace d' with d in * by congruence.
      iPoseProof (strengthen_env_generic int_s_type (int_s_heap η₂) Γ τ₁ x D₁ D₂
                                         v₁ d σ M₁ M₂ N N' (names_heap η₂))
        as "str".
      { intro n.
        rewrite elem_of_names_env.
        rewrite /names_heap elem_of_of_list elem_of_list_fmap.
        intros [? [-> _]] [? [[=] _]]. }
      { rewrite /names_heap elem_of_of_list elem_of_list_fmap.
        intros [? [[=] _]]. }
      { done. }
      { intros D D' eqD ?? <- ?? <-; by apply int_s_heap_local. }
      { apply int_s_type_local. }
      iDestruct ("str" with "Γ [$ty $pre]") as "[Γ' pre]".
      { iPureIntro.
        assert (of_gset (names Γ) ⊆ not_new A₁).
        { intro ξ; rewrite elem_of_of_gset /not_new elem_of_difference elem_of_of_gset.
          clear -Γ_names_good; set_solver. }
        split.
        all: apply overlap_cast.
        all: eapply overlap_mono.
        all: done.
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
      iDestruct "eqs" as %[eqM' [eqN' eqd']].
      iPureIntro; repeat split; auto.
      all: eapply overlap_trans; eauto.
    Qed.

    Lemma wp_bind_inv K E e ϕ:
      WP fill_ctx e K @ E {{ ϕ }} ⊢ WP e @ E {{ v, WP fill_ctx (of_val v) K @ E {{ ϕ }} }}.
    Proof.
      revert e ϕ.
      induction K using rev_ind; iIntros (e ϕ) "wp"; cbn.
      { iApply (wp_wand with "wp").
        iIntros (v); iApply wp_value'. }
      rewrite -!fill_ctx_app /=.
      iPoseProof (wp_bind_item_inv with "wp") as "wp".
      iPoseProof (IHK with "wp") as "wp".
      iApply (wp_wand with "wp").
      iIntros (v) "wp".
      rewrite -fill_ctx_app /=.
      iApply wp_bind_item; done.
    Qed.
    
    Lemma wp_bind K E e ϕ:
      WP e@E {{ v, WP fill_ctx (of_val v) K @ E {{ ϕ }} }}
         -∗ WP fill_ctx e K @ E {{ ϕ }}.
    Proof.
      revert e ϕ.
      induction K using rev_ind; iIntros (e ϕ) "wp"; cbn.
      { iApply (wp_strong_mono with "[$wp]"); first done.
        iIntros (v); iApply wp_value_inv. }
      rewrite -!fill_ctx_app /=.
      iApply wp_bind_item.
      iApply IHK.
      iApply (wp_wand with "wp").
      iIntros (v) "wp".
      iApply wp_bind_item_inv.
      rewrite -fill_ctx_app; done.
    Qed.
    
    Lemma universal_part (x: string) e e' K K' Γ τ₁ τ₂ η₁ η₂ η₃ A₁ A₂
          (Γ_names_good: names Γ ⊥ A₁)
          (x_fresh: ∀ e', subst_ctx (<[x:=e']>∅) K = K)
          (x_fresh': ∀ e', subst_ctx (<[x:=e']>∅) K' = K'):
      delayed_typed Γ η₁ e e' A₁ τ₁ η₂
                    -∗ delayed_typed (<[x:=τ₁]>Γ) η₂ (fill_ctx x K) (fill_ctx x K') A₂ τ₂ η₃
                    -∗ delayed_typed Γ η₁ (fill_ctx e K) (fill_ctx e' K') (A₁ ∪ A₂) τ₂ η₃.
    Proof.
      iIntros "dele delK".
      iIntros (D M Ni σi) "[#intΓ intη]".
      rewrite subst_fill.
      iApply wp_bind.
      iSpecialize ("dele" $! D M Ni σi with "[$intΓ $intη]").
      iApply (wp_wand with "dele [-]").
      iIntros (v) "post".
      iDestruct "post" as (Ni' M' D' d') "[rel [intτ [intη' #sim]]]".
      replace (fill_ctx (of_val v) (subst_ctx (of_val <$> σi) K))
        with (subst (of_val <$> (<[x:=v]>σi)) (fill_ctx x K)); cycle 1.
      { rewrite fmap_insert subst_insert_r; auto using val_closed.
        rewrite subst_fill /= lookup_insert x_fresh -(subst_val _ (of_val <$> σi)) -subst_fill.
        rewrite subst_val //. }
      iDestruct "rel" as %[eqN [eqM eqd]].
      iSpecialize ("delK" $! (strengthen Γ x d' D D') M' Ni' (<[x:=v]>σi) with "[intτ intη']").
      { iApply (strengthen_env_generic
                  int_i_type (int_i_heap η₂)
                  Γ τ₁ x D D' v d' σi M M' Ni Ni' (names_heap η₂)
                  with "intΓ [intτ intη']").
        - intro n.
          rewrite /names_env /names_heap !elem_of_of_list !elem_of_list_fmap.
          intros [? [-> _]] [? [[=] _]].
        - rewrite /names_heap elem_of_of_list elem_of_list_fmap.
          intros [? [[=] _]].
        - done.
        - intros D₁ D₂ eqD ?? <- ?? <-.
          apply int_i_heap_local; auto; done.
        - iFrame.
          iPureIntro.
          assert (of_gset (names Γ) ⊆ not_new A₁).
          { intro ξ; rewrite elem_of_of_gset /not_new elem_of_difference elem_of_of_gset.
            clear -Γ_names_good; set_solver. }
          split; apply overlap_cast; by eapply overlap_mono.
      }
      iApply (wp_wand with "delK").
      iIntros (v') "post".
      iDestruct "post" as (Ni'' M'' D'' d'') "[pure [intτ [intη #sim']]]".
      iDestruct "pure" as %[eqN' [eqM' eqD']].
      iExists Ni'', M'', D'', d''; iFrame.
      iSplit.
      { iPureIntro; repeat split; auto.
        all: by eapply overlap_trans; eauto. }
      iAlways.
      iApply (existential_part with "sim sim'"); auto.
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
      iApply universal_part.
      2,3: done.
      2: iApply dele.
      2: iApply delK.
      apply typing_good_names in tye.
      - destruct tye as [disj _].
        clear -disj namese.
        set_solver.
      - intros x' τ' mt ξ inξ.
        apply namese, elem_of_union, or_introl, env_elem_of_names.
        eauto.
      - clear -namese; set_solver.
    Qed.

    (** Meta theory: The framing lemma *)
    Definition frame ηf (D D': conn_map): conn_map := D ~[names_heap ηf]~> D'.

    Lemma frame_generic          
          (int_ty: type → @int_type Σ) (int_he: heap → @int_heap Σ) τ (η ηf: heap)          
          D D' d v (M M': task_map) (N N': name_map)
          (novM: M ≡[names ηf]≡ M') (novN: N ≡[names ηf]≡ N')
          (int_he_split: ∀ D'' M'' N'',
              int_he (hstar η ηf) D'' M'' N'' ⊣⊢ int_he η D'' M'' N'' ∗ int_he ηf D'' M'' N'')
          (int_he_local: ∀ η,
              Proper (overlap (names_heap η) ==> overlap (names η) ==>
                              overlap (names η) ==> (≡)) (int_he η))
          (disj: names η ⊥ names ηf):
      int_he ηf D M N -∗ (⌜D' !! RET = Some d⌝ ∗ int_ty τ d M' N' v ∗ int_he η D' M' N') -∗
             (⌜frame ηf D D' !! RET = Some d⌝) ∗
             int_ty τ d M' N' v ∗ int_he (hstar η ηf) (frame ηf D D') M' N'.
    Proof.
      iIntros "frame [eqd [type heap]]".
      iFrame.
      iSplitL "eqd".
      { iDestruct "eqd" as %eqd.
        iPureIntro.
        rewrite /frame lookup_merge_along_not_in //.
        rewrite /names_heap elem_of_of_list elem_of_list_fmap.
        intros [? [[=] _]]. }
      rewrite int_he_split.
      iSplitL "heap".
      - iApply (int_he_local with "heap").
        2,3: done.
        apply overlap_merge_along_r.
        rewrite /names_heap => [n].
        rewrite !elem_of_of_list !elem_of_list_fmap.
        intros [ξ [-> inηf%elem_of_elements]] [? [[=<-] inη%elem_of_elements]].
        apply (disj ξ); done.
      - by iApply (int_he_local with "frame"); first apply overlap_merge_along_l.
    Qed.

    Lemma int_s_rec_split n η η' D M N:
      int_s_heap_rec n (hstar η η') D M N ⊣⊢ int_s_heap_rec n η D M N ∗ int_s_heap_rec n η' D M N.
    Proof. destruct n; done. Qed.
    
    Lemma int_s_heap_split η η' D M N:
      int_s_heap (hstar η η') D M N ⊣⊢ (int_s_heap η D M N ∗ int_s_heap η' D M N).
    Proof.
      iSplit.
      { iIntros "pre".
        iDestruct "pre" as (n) "pre".
        rewrite int_s_rec_split.
        iDestruct "pre" as "[pre pre']".
        iSplitL "pre"; iExists n; iFrame.
      } {
        iIntros "[pre pre']".
        iDestruct "pre" as (n) "pre".
        iDestruct "pre'" as (n') "pre'".
        iExists (max n n').
        rewrite int_s_rec_split.
        iSplitL "pre".
        all: iApply int_s_heap_rec_mono; last iFrame.
        all: auto with arith.
      }
    Qed.
    
    Lemma frame_existential Γ e (η: heap) A τ (η': heap) D D' D'' M M' (ηf: heap)
          (disj': names η' ⊥ names ηf) (disj: names η ⊥ names ηf) (disj'': names ηf ⊥ A):
      simulation Γ e η A τ η' D M D' M' -∗
                 simulation Γ e (hstar η ηf) A τ (hstar η' ηf) (frame ηf D'' D) M
                 (frame ηf D'' D') M'.
    Proof.
      iIntros "sim".
      iIntros (N σ p K) "ctx [env pre] move".
      rewrite int_s_heap_split.
      iDestruct "pre" as "[pre frame]".
      iMod ("sim" with "ctx [env pre] move") as (v) "[post move]".
      { iSplitL "env".
        - iApply (int_s_env_local with "env").
          2-4: done.
          symmetry.
          apply overlap_merge_along_r.
          rewrite /names_heap /names_env => [n].
          rewrite !elem_of_of_list !elem_of_list_fmap.
          intros [? [-> _]] [? [[=] _]].
        - iApply (int_s_heap_local with "pre").
          2-3: done.
          symmetry.
          apply overlap_merge_along_r.
          rewrite /names_heap => [n].
          rewrite !elem_of_of_list !elem_of_list_fmap.
          intros [x [-> inη%elem_of_elements]] [? [[=<-] inηf%elem_of_elements]].
          apply (disj x); auto. }
      iDestruct "post" as (d N') "[eqs [type post]]".
      iModIntro; iExists v; iFrame.
      iDestruct "eqs" as %[eqM [eqN eqd]].
      iExists d, N'.
      assert (of_gset (names ηf) ⊆ not_new A).
      { clear -disj''; intro.
        rewrite /not_new elem_of_difference !elem_of_of_gset.
        set_solver. }
      iPoseProof (frame_generic int_s_type int_s_heap τ η' ηf D'' D' d v M M' N N'
                    with "[frame] [$type $post]") as "post".
      1,2: apply overlap_cast; eapply overlap_mono; eauto.
      3,5: done.
      - apply int_s_heap_split.
      - intro; apply int_s_heap_local.
      - iApply (int_s_heap_local with "frame").
        2,3: done.
        symmetry; apply overlap_merge_along_l.
      - iDestruct "post" as "[% [$$]]"; auto.
    Qed.

    Lemma simulation_local Γ e η A τ η':
      Proper (overlap (names_env Γ ∪ names_heap η) ==> (=) ==>
                      overlap ({[RET]} ∪ names_heap η') ==> (=) ==> (⊣⊢))
             (simulation Γ e η A τ η').
    Proof.
      iIntros (D D' eqD M M' <- E E' eqE L L' <-).
      rewrite /simulation /existential_triple.
      f_equiv; intro N.
      f_equiv; intro σ.
      f_equiv; intro p.
      f_equiv; intro K.
      do 2 f_equiv.
      { f_equiv.
        - apply int_s_env_local.
          2-4: done.
          eapply overlap_mono.
          2-4: done.
          apply union_subseteq_l.
        - apply int_s_heap_local.
          2,3: done.
          eapply overlap_mono.
          2-4: done.
          apply union_subseteq_r. }
      do 3 f_equiv; intro v.
      do 2 f_equiv; intro d.
      f_equiv; intro N'.
      f_equiv.
      { rewrite (eqE RET); first done.
        clear; set_solver. }
      f_equiv.
      apply int_s_heap_local.
      2,3: done.
      eapply overlap_mono.
      2-4: done.
      clear; set_solver.
    Qed.
    
    Lemma closed_frame Γ e e' (η: heap) A τ (η' ηf: heap)
          (disj': names η' ⊥ names ηf) (disj: names η ⊥ names ηf) (disj'': names ηf ⊥ A):
      delayed_typed Γ η e e' A τ η' -∗
                    delayed_typed Γ (hstar η ηf) e e' A τ (hstar η' ηf).
    Proof.
      iIntros "del".
      iIntros (D M N σ); cbn -[difference].
      iIntros "[env [pre frame]]".
      iSpecialize ("del" $! D M N σ with "[$env $pre]").
      iApply (wp_wand with "del").
      iIntros (v) "post".
      iDestruct "post" as (N' M' D' d') "[eqs [type [post sim]]]".
      iExists N', M', (frame ηf D D'), d'.
      iFrame.
      iDestruct "eqs" as %[eqM [eqN eqD']].
      iSplit.
      { iPureIntro; split; auto.
        rewrite /frame lookup_merge_along_not_in; first done.
        rewrite /names_heap elem_of_of_list elem_of_list_fmap.
        intros [? [[=] _]]. }
      iSplitR "sim".
      { iSplitL "post".
        - iApply (int_i_heap_local with "post").
          2,3: done.
          apply overlap_merge_along_r.
          intro n.
          rewrite !elem_of_names_heap.
          intros [ξ [-> inηf]] [? [[=<-] inη']].
          apply (disj' ξ); done.
        - assert (of_gset (names ηf) ⊆ not_new A).
          { clear -disj''; intro; rewrite elem_of_difference !elem_of_of_gset; set_solver. }
          iApply (int_i_heap_local with "frame").
          2,3: apply overlap_cast; eapply overlap_mono; done.
          apply overlap_merge_along_l. }
      iAssert (□simulation Γ e' (η ⊗ ηf) A τ (η' ⊗ ηf) (frame ηf D D) M (frame ηf D D') M')
        with "[sim]" as "sim".
      { iDestruct "sim" as "#sim"; iAlways; iApply (frame_existential with "sim"); auto. }
      iDestruct "sim" as "#sim"; iAlways.
      iApply (simulation_local with "sim").
      2-4: done.
      intros n _.
      rewrite /frame merge_along_cases.
      destruct bool_decide; done.
    Qed.
    
    (** Meta-theory: Strengthening the environment. *)
    Definition restrict_subst' {A} (e: option A) (τ: option type) :=
      match τ with Some _ => e | None => None end.
    Definition restrict_subst {A} (Γ: env) (σ: gmap string A) := merge restrict_subst' σ Γ.
    Instance: ∀ A, DiagNone (@restrict_subst' A).
    Proof. done. Qed.
    Lemma lookup_restrict_subst_is_Some {A} (Γ: env) (σ: gmap string A) x:
      is_Some (restrict_subst Γ σ !! x) ↔ is_Some (Γ!!x) ∧ is_Some (σ!!x).
    Proof.
      rewrite /restrict_subst lookup_merge.
      enough (∀ o, is_Some (restrict_subst' (σ!!x) o) ↔ is_Some o ∧ is_Some (σ !! x))
        as -> by done.
      intros [τ|]; cbn.
      - intuition eauto.
      - rewrite -!not_eq_None_Some; tauto.
    Qed.
    
    Lemma restrict_env (int_ty: type → @int_type Σ) Γ Γ' D M N σ (sub: Γ ⊆ Γ'):
      intΓ int_ty Γ' D M N σ -∗ intΓ int_ty Γ D M N (restrict_subst Γ σ).
    Proof.
      rewrite /intΓ.
      iIntros "[maps env]".
      iDestruct "maps" as %[domσ domD].
      iSplit.
      { iPureIntro; split; intro.
        - rewrite lookup_restrict_subst_is_Some.
          split; last tauto.
          intro inx; split; auto.
          eapply domσ, lookup_weaken_is_Some; done.
        - intro inx.
          eapply domD, lookup_weaken_is_Some; done. }
      iIntros (x τ v d) "pre".
      iDestruct "pre" as %[eqτ [eqv eqd]].
      iApply ("env" $! x τ v d).
      iPureIntro.
      repeat split; auto.
      - by eapply lookup_weaken.
      - by rewrite /restrict_subst lookup_merge eqτ in eqv.
    Qed.

    Lemma subst_restrict_with_type `(ty: typing U Γ e η A τ η'):
      ∀ σ, subst (restrict_subst Γ σ) e = subst σ e.
    Proof.
      induction ty; intros; cbn.
      1,2,3,6,7,8,9: congruence.
      - by rewrite /restrict_subst lookup_merge Γx.
      - rewrite IHty1; do 2 f_equal.
        rewrite -(IHty2 (delete' x σ)); f_equal.
        apply map_eq; intro y.
        rewrite lookup_delete'_cases /restrict_subst !lookup_merge lookup_delete'_cases.
        destruct (bool_decide_reflect (BNamed y ≠ x)) as [neqx|<-%dec_stable].
        + rewrite /restrict_subst' /insert'.
          destruct x; first done.
          rewrite lookup_insert_ne; congruence.
        + by destruct (insert' (BNamed y) τ₁ Γ !! y).
    Qed.

    Lemma restrict_env_fmap `(f: A → B) Γ m:
      f <$> restrict_subst Γ m = restrict_subst Γ (f <$> m).
    Proof.
      apply map_eq; intro y.
      rewrite /restrict_subst lookup_fmap !lookup_merge lookup_fmap /restrict_subst'.
      match goal with |- f <$> match ?a with _ => _ end = _ => by destruct a end.
    Qed.
    
    Lemma closed_strengthen U Γ Γ' e e' η A A' τ η'
          (ty: typing U Γ e η A τ η')
          (ty': typing U Γ e' η A τ η')
          (subΓ: Γ ⊆ Γ') (subA: A ⊆ A'):
      delayed_typed Γ η e e' A τ η' -∗ delayed_typed Γ' η e e' A' τ η'.
    Proof.
      assert (not_new A' ⊆ not_new A).
      { intro; rewrite /not_new !elem_of_difference !elem_of_of_gset.
        clear -subA; set_solver. }
      iIntros "spec".
      iIntros (D M N σ) "[env pre]".
      iSpecialize ("spec" $! D M N (restrict_subst Γ σ) with "[env $pre]").
      { by iApply (restrict_env with "env"). }
      rewrite restrict_env_fmap (subst_restrict_with_type ty).
      iApply (wp_wand with "spec").
      iIntros (v) "post".
      iDestruct "post" as (N' M' D' d') "[eqs [type [post sim]]]".
      iExists N', M', D', d'; iFrame.
      iDestruct "eqs" as %[eqN [eqm eqd]].
      iSplit.
      { iPureIntro; repeat split; auto.        
        all: eapply overlap_mono; done. }
      clear eqN N N' σ v.
      iDestruct "sim" as "#sim"; iAlways.
      iIntros (N σ p K) "ctx [env pre] move".
      rewrite -(subst_restrict_with_type ty') -restrict_env_fmap.
      iMod ("sim" $! N (restrict_subst Γ σ) p K with "ctx [env $pre] move") as (v) "[post move]".
      { by iApply (restrict_env with "env"). }
      iModIntro; iExists v; iFrame.
      iDestruct "post" as (d N') "[eqs [type post]]".
      iExists d, N'; iFrame.
      iDestruct "eqs" as %[eqM [eqN eqD]].
      iPureIntro; repeat split; auto.
      all: by eapply overlap_mono.
    Qed.

    (** Closure: variables. *)
    Lemma to_of_val v: to_val (of_val v) = Some v.
    Proof.
      destruct v; first done.
      rewrite /= decide_left; done.
    Qed.
    
    Lemma closed_variable (x: string) τ:
      delayed_typed (<[x:=τ]>∅) hemp x x ∅ τ hemp.
    Proof.
      iIntros (D M N σ) "[[env_names env] _]".
      iDestruct "env_names" as %[domσ domD].
      assert (is_Some (σ !! x)) as [v val_x].
      { apply domσ; rewrite lookup_insert; eauto. }
      assert (is_Some (D !! var x)) as [d conn_x].
      { apply domD; rewrite lookup_insert; eauto. }
      rewrite /= lookup_fmap val_x /=.
      iApply wp_value'.
      iExists N, M, (<[RET:=d]>D), d.
      rewrite /int_i_emp; iFrame.
      iSplit.
      { rewrite lookup_insert; auto. }
      iSplitL "env".
      { iApply ("env" $! x τ v d).
        iPureIntro; split; auto.
        apply lookup_insert. }
      iSplit; auto.
      iAlways.
      iIntros (N' σ' p K) "ctx [[env_names env] heap] move".
      iDestruct "env_names" as %[domσ' _].
      assert (is_Some (σ' !! x)) as [v' val'_x].
      { apply domσ'; rewrite lookup_insert; eauto. }
      rewrite /= lookup_fmap val'_x /=.
      iModIntro; iExists v'; iFrame.
      iExists d, N'.
      rewrite lookup_insert.
      iSplit; auto.
      iSplitL "env".
      - iApply ("env" $! x τ v' d).
        rewrite lookup_insert; auto.
      - by iExists 0.
    Qed.

    (** Closure: constants. *)
    Lemma closed_true: delayed_typed ∅ hemp Ctrue Ctrue ∅ tbool hemp.
    Proof.
      iIntros (D M N σ) "_".
      change (Const Ctrue) with (of_val (VConst Ctrue)).
      rewrite subst_closed_empty; last by apply val_closed.
      iApply wp_value'.
      iExists N, M, (<[RET:=VConst Ctrue]>D), (VConst Ctrue).
      rewrite lookup_insert; iSplit; auto.
      iSplit.
      { iPureIntro; auto. }
      iSplit; auto.
      iAlways.
      iIntros (N' σ' p K) "ctx _ move".
      iModIntro.
      iExists Ctrue.
      rewrite subst_val; iFrame.
      iExists Ctrue, N'.
      rewrite lookup_insert; iSplit; auto.
      iSplit.
      - iPureIntro; auto.
      - by iExists 0.
    Qed.

    Lemma closed_false: delayed_typed ∅ hemp Cfalse Cfalse ∅ tbool hemp.
    Proof.
      iIntros (D M N σ) "_".
      change (Const Cfalse) with (of_val (VConst Cfalse)).
      rewrite subst_closed_empty; last by apply val_closed.
      iApply wp_value'.
      iExists N, M, (<[RET:=VConst Cfalse]>D), (VConst Cfalse).
      rewrite lookup_insert; iSplit; auto.
      iSplit.
      { iPureIntro; auto. }
      iSplit; auto.
      iAlways.
      iIntros (N' σ' p K) "ctx _ move".
      iModIntro.
      iExists Cfalse.
      rewrite subst_val; iFrame.
      iExists Cfalse, N'.
      rewrite lookup_insert; iSplit; auto.
      iSplit.
      - iPureIntro; auto.
      - by iExists 0.
    Qed.

    Lemma closed_unit: delayed_typed ∅ hemp Cunit Cunit ∅ tunit hemp.
    Proof.
      iIntros (D M N σ) "_".
      change (Const Cunit) with (of_val (VConst Cunit)).
      rewrite subst_closed_empty; last by apply val_closed.
      iApply wp_value'.
      iExists N, M, (<[RET:=VConst Cunit]>D), (VConst Cunit).
      rewrite lookup_insert; iSplit; auto.
      iSplit.
      { iPureIntro; auto. }
      iSplit; auto.
      iAlways.
      iIntros (N' σ' p K) "ctx _ move".
      iModIntro.
      iExists Cunit.
      rewrite subst_val; iFrame.
      iExists Cunit, N'.
      rewrite lookup_insert; iSplit; auto.
      iSplit.
      - iPureIntro; auto.
      - by iExists 0.
    Qed.

    (** Closure: Memory operations *)
    Lemma closed_alloc (x: string) (τ: type) ξ (ξ_fresh: ξ ∉ names τ):
      delayed_typed (<[x:=τ]>∅) hemp (Alloc x) (Alloc x) {[ξ]} (tref ξ) (hpt ξ τ).
    Proof.
      iIntros (D M N σ) "[[env_names env] _]".
      iDestruct "env_names" as %[domσ domD].
      assert (is_Some (σ !! x)) as [v val_x].
      { apply domσ; rewrite lookup_insert; eauto. }
      assert (is_Some (D !! var x)) as [d conn_x].
      { apply domD; rewrite lookup_insert; eauto. }
      rewrite /= lookup_fmap val_x /=.
      iApply (wp_wand with "[]").
      { iApply wp_alloc.
        apply to_of_val. }
      iIntros (?) "post".
      iDestruct "post" as (l) "[% mt]"; subst.
      iExists (<[ξ:=Loc l]>N), M, (<[RET := d]>(<[name ξ := d]>D)), d.
      iSplit.
      { iPureIntro.
        rewrite lookup_insert; repeat split; auto.
        intro n.
        rewrite /not_new elem_of_difference elem_of_of_gset not_elem_of_singleton => [[_ neqξ]].
        rewrite lookup_insert_ne; congruence. }
      iSplit.
      { iPureIntro; exists l; rewrite lookup_insert; auto. }
      iSplitL "mt env".
      { iExists l, d, v; iFrame.
        rewrite !lookup_insert lookup_insert_ne ?lookup_insert; last discriminate.
        iSplit; auto.
        iSpecialize  ("env" $! x τ v d with "[]").
        { rewrite lookup_insert; auto. }
        iApply (int_i_type_local with "env").
        1,2,4: done.
        intros ξ' inξ'.
        apply lookup_insert_ne.
        congruence. }
      iAlways.
      iIntros (N' σ' p K) "ctx [[env_names env] _] move".
      iDestruct "env_names" as %[domσ' _].
      assert (is_Some (σ' !! x)) as [v' val'_x].
      { apply domσ'; rewrite lookup_insert; eauto. }
      rewrite /= lookup_fmap val'_x /=.
      iMod (simulate_alloc with "ctx move") as (l') "[move post]"; eauto using to_of_val.
      iModIntro; iExists (Cloc l'); iFrame.
      iExists d, (<[ξ:=Loc l']>N').
      iSplit.
      { rewrite lookup_insert; iPureIntro; repeat split; auto.
        intros ξ'.
        rewrite /not_new elem_of_difference elem_of_of_gset not_elem_of_singleton.
        intros [_ neqξ].
        rewrite lookup_insert_ne; done. }
      iSplitR.
      { iExists l'; rewrite lookup_insert; auto. }
      iExists 0; cbn.
      iExists l', d, v'; iFrame.
      rewrite lookup_insert lookup_insert_ne ?lookup_insert; last discriminate.
      iSplit; auto.
      iSpecialize ("env" $! x τ v' d with "[]").
      { rewrite lookup_insert; auto. }
      iApply (int_s_type_local with "env").
      1,2,4: done.
      intros ξ' inξ'.
      rewrite lookup_insert_ne; congruence.
    Qed.

    Implicit Types x y: string.

    Lemma int_s_heap_pt ξ τ D M N:
      int_s_heap (hpt ξ τ) D M N ⊣⊢ int_s_heap_rec 0 (hpt ξ τ) D M N.
    Proof.
      iSplit.
      - iIntros "pre".
        iDestruct "pre" as ([|n]) "pre"; auto.
      - iIntros "pre".
        iExists 0; done.
    Qed.
    
    Lemma closed_read x ξ τ:
      delayed_typed (<[x:=tref ξ]>∅) (hpt ξ τ) (Read x) (Read x) ∅ τ (hpt ξ τ).
    Proof.
      iIntros (D M N σ) "[[env_names env] pt]".
      iDestruct "env_names" as %[domσ domD].
      assert (is_Some (σ !! x)) as [v val_x].
      { apply domσ; rewrite lookup_insert; eauto. }
      assert (is_Some (D !! var x)) as [d conn_x].
      { apply domD; rewrite lookup_insert; eauto. }
      rewrite /= lookup_fmap val_x /=.
      iDestruct ("env" $! x (tref ξ) v d with "[]") as %[l [ref ->]].
      { rewrite lookup_insert; auto. }
      iDestruct "pt" as (l' d' v') "[eqs [mt #val]]".
      iDestruct "eqs" as %[ref' eqd].
      rewrite ref in ref'; injection ref' as <-.
      iApply (wp_wand with "[mt]").
      { iApply (wp_read with "mt"). }
      iIntros (v) "[% mt]"; subst v'.
      iExists N, M, (<[RET:=d']>D), d'.
      iFrame.
      rewrite lookup_insert.
      iSplit; auto.
      iSplit; auto.
      iSplitL.
      { iExists l, d', v; iFrame; iSplit; auto.
        rewrite lookup_insert_ne; auto. }
      iClear "val".
      clear v l val_x ref N domσ σ.
      iAlways.
      iIntros (N σ p K) "ctx [[env_names env] pt] move".
      iDestruct "env_names" as %[domσ _].
      assert (is_Some (σ !! x)) as [v val_x].
      { apply domσ; rewrite lookup_insert; eauto. }
      rewrite /= lookup_fmap val_x /=.
      iDestruct ("env" $! x (tref ξ) v d with "[]") as "ref".
      { rewrite lookup_insert; auto. }
      iDestruct "ref" as %[l [ref ->]].
      rewrite int_s_heap_pt.
      iDestruct "pt" as (l' d'' v) "[eqs [pt #type]]".
      iDestruct "eqs" as %[eql eqd'].
      rewrite ref in eql; injection eql as <-.
      rewrite eqd in eqd'; injection eqd' as <-.
      iMod (simulate_read with "ctx move pt") as "[move pt]"; auto.
      iModIntro.
      iExists v; iFrame.
      iExists d', N.
      rewrite lookup_insert.
      iSplit; first done.
      iSplit; first done.
      rewrite int_s_heap_pt.
      iExists l, d', v; iFrame; iSplit; auto.
      rewrite lookup_insert_ne; auto.
    Qed.

    Lemma closed_write x y ξ τ (neq: x ≠ y):
      delayed_typed (<[x:=tref ξ]>(<[y:=τ]>∅)) (hpt ξ τ) (Write x y) (Write x y) ∅ tunit (hpt ξ τ).
    Proof.
      iIntros (D M N σ) "[[env_names #env] pt]".
      iDestruct "env_names" as %[domσ domD].
      assert (is_Some (σ !! x)) as [v val_x].
      { apply domσ; rewrite lookup_insert; eauto. }
      assert (is_Some (D !! var x)) as [d conn_x].
      { apply domD; rewrite lookup_insert; eauto. }
      rewrite /= lookup_fmap val_x /=.
      assert (is_Some (σ !! y)) as [w val_y].
      { apply domσ; rewrite lookup_insert_ne ?lookup_insert; eauto. }
      assert (is_Some (D !! var y)) as [d' conn_y].
      { apply domD; rewrite lookup_insert_ne ?lookup_insert; eauto. }
      rewrite /= lookup_fmap val_y /=.
      iDestruct "pt" as (l' dl v') "[eqs [mt #val]]".
      iDestruct "eqs" as %[ref' eqd].
      iDestruct ("env" $! x (tref ξ) v d with "[]") as %[l [ref ->]].
      { rewrite lookup_insert; auto. }
      rewrite ref in ref'; injection ref' as <-.
      iPoseProof (wp_write ⊤ l (of_val w) w with "[mt]") as "wp".
      { apply to_of_val. }
      { iExists v'; iFrame. }
      iApply (wp_wand with "wp").
      iIntros (?) "[% mt]"; subst.
      iExists N, M, (<[RET:=VConst Cunit]>(<[name ξ := d']>D)), Cunit.
      rewrite lookup_insert.
      iSplit; auto.
      iSplit; auto.
      iSplitL "mt".
      { iExists l, d', w.
        iFrame.
        rewrite lookup_insert_ne ?lookup_insert; last auto.
        iSplit; auto.
        iApply ("env" $! y τ w d').
        rewrite lookup_insert_ne; last done.
        rewrite lookup_insert; auto. }
      iClear "env".
      iAlways.
      iIntros (N' σ' p K) "ctx [[env_names #env] pt] move".
      iDestruct "env_names" as %[domσ' _].
      assert (is_Some (σ' !! x)) as [u val'_x].
      { apply domσ'; rewrite lookup_insert; eauto. }
      rewrite /= lookup_fmap val'_x /=.
      assert (is_Some (σ' !! y)) as [w' val'_y].
      { apply domσ'; rewrite lookup_insert_ne ?lookup_insert; eauto. }
      rewrite lookup_fmap val'_y /=.
      iDestruct ("env" $! x (tref ξ) u d with "[]") as %[l' [ref' ->]].
      { rewrite lookup_insert; auto. }
      rewrite int_s_heap_pt /= /int_s_pt.
      iDestruct "pt" as (l'' d'' u') "[eqs [pt _]]".
      iDestruct "eqs" as %[eql'' eqd''].
      rewrite ref' in eql''; injection eql'' as <-.
      rewrite eqd in eqd''; injection eqd'' as <-.
      iMod (simulate_write with "ctx move [pt]") as "[move pt]".
      1,2: eauto using to_of_val.
      { iExists u'; iFrame. }
      iModIntro; iExists Cunit; iFrame.
      iExists Cunit, N'.
      rewrite lookup_insert.
      iSplit; auto.
      iSplit; first done.
      rewrite int_s_heap_pt.
      iExists l', d', w'; iFrame.
      rewrite lookup_insert_ne ?lookup_insert; last done.
      iSplit; first done.
      iApply ("env" $! y).
      rewrite lookup_insert_ne ?lookup_insert; last done.
      auto.
    Qed.
    
    (** Closure: If *)
    Lemma closed_if x Γ η A τ η' e₁ e₁' e₂ e₂' (x_type: Γ !! x = Some tbool):
      delayed_typed Γ η e₁ e₁' A τ η' -∗
                    delayed_typed Γ η e₂ e₂' A τ η' -∗
                    delayed_typed Γ η (If x e₁ e₂) (If x e₁' e₂') A τ η'.
    Proof.
      iIntros "dtt dtf".
      iIntros (D M N σ) "[#env pre]".
      iPoseProof ("env") as "[env_names env_types]".
      iDestruct "env_names" as %[domσ domD].
      assert (is_Some (σ !! x)) as [v val_x].
      { apply domσ; rewrite x_type; eauto. }
      assert (is_Some (D !! var x)) as [d conn_x].
      { apply domD; rewrite x_type; eauto. }
      rewrite /= lookup_fmap val_x /=.
      iDestruct ("env_types" $! x tbool v d with "[]") as %[[->| ->] <-]; first auto.
      { iApply wp_if_true.
        iSpecialize ("dtt" $! D M N σ with "[$env $pre]").
        iApply (wp_wand with "dtt").
        iClear "env env_types dtf".
        iIntros (v) "post".
        iDestruct "post" as (N' M' D' d') "[names [ty [heap #sim]]]".
        iExists N', M', D', d'; iFrame.
        clear N N' d' domσ σ val_x v.
        iAlways.
        iIntros (N σ p K) "#ctx [#env pre] move".
        iPoseProof ("env") as "[env_names env_types]".
        iDestruct "env_names" as %[domσ _].
        assert (is_Some (σ !! x)) as [v val_x].
        { apply domσ; rewrite x_type; eauto. }
        iDestruct ("env_types" $! x tbool v Ctrue with "[]") as %[_ ->]; first auto.
        rewrite /= lookup_fmap val_x /=.
        iMod (simulate_if_true with "ctx move") as "move"; first auto.
        iApply ("sim" with "ctx [$env $pre] move").
      }{
        iApply wp_if_false.
        iSpecialize ("dtf" $! D M N σ with "[$env $pre]").
        iApply (wp_wand with "dtf").
        iClear "env env_types dtt".
        iIntros (v) "post".
        iDestruct "post" as (N' M' D' d') "[names [ty [heap #sim]]]".
        iExists N', M', D', d'; iFrame.
        clear N N' d' domσ σ val_x v.
        iAlways.
        iIntros (N σ p K) "#ctx [#env pre] move".
        iPoseProof ("env") as "[env_names env_types]".
        iDestruct "env_names" as %[domσ _].
        assert (is_Some (σ !! x)) as [v val_x].
        { apply domσ; rewrite x_type; eauto. }
        iDestruct ("env_types" $! x tbool v Cfalse with "[]") as %[_ ->]; first auto.
        rewrite /= lookup_fmap val_x /=.
        iMod (simulate_if_false with "ctx move") as "move"; first auto.
        iApply ("sim" with "ctx [$env $pre] move").
      }
    Qed.

    (** Closure: Let *)
    Lemma closed_let x y Γ η A τ τ' η' e e' (x_type: Γ !! x = Some τ) (y_fresh: Γ !! y = None):
      delayed_typed (<[y:= τ]> Γ) η e e' A τ' η' -∗
                    delayed_typed Γ η (Let (BNamed y) x e) (Let (BNamed y) x e') A τ' η'.
    Proof.
      iIntros "del".
      iIntros (D M N σ) "[#env pre]".
      iPoseProof ("env") as "[env_names env_types]".
      iDestruct "env_names" as %[domσ domD].
      assert (is_Some (σ !! x)) as [v val_x].
      { apply domσ; rewrite x_type; eauto. }
      assert (is_Some (D !! var x)) as [d conn_x].
      { apply domD; rewrite x_type; eauto. }
      rewrite /= lookup_fmap val_x /=.
      iApply wp_app; first apply to_of_val.
      rewrite /=.
      rewrite subst_subst; cycle 1.
      { intros x' e''.
        rewrite lookup_delete_Some lookup_fmap fmap_Some => [[_ [v' [_ ->]]]].
        apply val_closed. }
      replace (subst_merge (<[y:=of_val v]> ∅) (delete y (of_val <$> σ)))
        with (of_val <$> <[y:=v]>σ); cycle 1.
      { apply map_eq; intro z.
        rewrite /subst_merge lookup_merge /subst_merge'.
        destruct (decide (y=z)) as [<-|neq].
        - by rewrite lookup_delete lookup_fmap !lookup_insert.
        - rewrite lookup_fmap !lookup_delete_ne; last done.
          rewrite !lookup_insert_ne; auto.
          rewrite lookup_empty lookup_fmap.
          destruct (σ !! z) as [w|]; cbn; trivial.
          rewrite subst_val; trivial. }
      iSpecialize ("del" $! (<[var y := d]>D) M N (<[y:=v]> σ) with "[env pre]").
      { iSplit; first iSplit.
        - iPureIntro.
          setoid_rewrite lookup_insert_is_Some.
          split; first by setoid_rewrite domσ.
          intros z [eqy|[??]]; subst; auto.
          destruct (decide (var y = var z)); auto.
        - iIntros (x' τ'' v' d' [mtτ [mtv mtd]]).
          destruct (decide (y = x')) as [<-|neq].
          + rewrite lookup_insert in mtd; injection mtd as <-.
            rewrite lookup_insert in mtv; injection mtv as <-.
            rewrite lookup_insert in mtτ; injection mtτ as <-.
            iApply ("env_types" $! x); auto.
          + rewrite lookup_insert_ne in mtd; last congruence.
            rewrite lookup_insert_ne in mtv; last congruence.
            rewrite lookup_insert_ne in mtτ; last congruence.
            iApply ("env_types" $! x'); auto.
        - iApply (int_i_heap_local with "pre").
          2,3: done.
          intro n.
          rewrite /names_heap elem_of_of_list elem_of_list_fmap.
          intros [ξ [-> _]].
          apply lookup_insert_ne; done. }
      iApply (wp_wand with "del").
      iIntros (w) "post".
      iDestruct "post" as (N' M' D' d') "[eqs [ty [heap #sim]]]".
      iExists N', M', D', d'; iFrame.
      iClear "env env_types".
      clear v val_x N' d' w σ domσ N.
      iAlways.
      iIntros (N σ p K) "#ctx [#env pre] move".
      cbn -[difference].
      iPoseProof ("env") as "[env_names env_types]".
      iDestruct "env_names" as %[domσ _].
      assert (is_Some (σ !! x)) as [v val_x].
      { apply domσ; rewrite x_type; eauto. }
      rewrite /= lookup_fmap val_x /=.
      iMod (simulate_app with "ctx move") as "move"; eauto using to_of_val.
      rewrite /= subst_subst; cycle 1.
      { intros x' e''.
        rewrite lookup_delete_Some lookup_fmap fmap_Some => [[_ [v' [_ ->]]]].
        apply val_closed. }
      replace (subst_merge (<[y:=of_val v]> ∅) (delete y (of_val <$> σ)))
        with (of_val <$> <[y:=v]>σ); cycle 1.
      { apply map_eq; intro z.
        rewrite /subst_merge lookup_merge /subst_merge'.
        destruct (decide (y=z)) as [<-|neq].
        - by rewrite lookup_delete lookup_fmap !lookup_insert.
        - rewrite lookup_fmap !lookup_delete_ne; last done.
          rewrite !lookup_insert_ne; auto.
          rewrite lookup_empty lookup_fmap.
          destruct (σ !! z) as [w|]; cbn; trivial.
          rewrite subst_val; trivial. }
      iSpecialize ("sim" $! N (<[y:=v]> σ) with "ctx [env pre]").
      { iSplit; first iSplit.
        - iPureIntro.
          setoid_rewrite lookup_insert_is_Some.
          split; first by setoid_rewrite domσ.
          intros z [eqy|[??]]; subst; auto.
          destruct (decide (var y = var z)); auto.
        - iIntros (x' τ'' v' d' [mtτ [mtv mtd]]).
          destruct (decide (y = x')) as [<-|neq].
          + rewrite lookup_insert in mtd; injection mtd as <-.
            rewrite lookup_insert in mtv; injection mtv as <-.
            rewrite lookup_insert in mtτ; injection mtτ as <-.
            iApply ("env_types" $! x); auto.
          + rewrite lookup_insert_ne in mtd; last congruence.
            rewrite lookup_insert_ne in mtv; last congruence.
            rewrite lookup_insert_ne in mtτ; last congruence.
            iApply ("env_types" $! x'); auto.
        - iApply (int_s_heap_local with "pre").
          2,3: done.
          intro n.
          rewrite /names_heap elem_of_of_list elem_of_list_fmap.
          intros [ξ [-> _]].
          apply lookup_insert_ne; done. }
      iApply "sim"; auto.
    Qed.

    (** Closure: Async operations *)
    Lemma delete_insert_eq {A} (ξ: gname) (a: A) (m: gmap gname A):
      delete ξ m = delete ξ (<[ξ:=a]>m).
    Proof.
      apply map_eq; intro ξ'.
      destruct (decide (ξ = ξ')) as [<-|neq].
      - by rewrite !lookup_delete.
      - by rewrite !lookup_delete_ne ?lookup_insert_ne.
    Qed.

    Ltac intro_equiv x := f_equiv; intro x.

    Lemma closed_post (Γ: env) (η: heap) e e' A (τ: type) (η': heap) ξ
          (ξ_fresh_Γ: ξ ∉ names Γ) (ξ_fresh_η: ξ ∉ names η) (ξ_fresh_A: ξ ∉ A)
          (ξ_fresh_τ: ξ ∉ names τ) (ξ_fresh_η': ξ ∉ names η'):
      delayed_typed Γ η e e' A τ η' -∗
                    delayed_typed Γ η (Post e) (Post e') {[ξ]} (ttask ξ A τ) (hwait ξ A η').
    Proof.
      iIntros "del".
      iIntros (D M N σ) "pre"; cbn [subst].
      (* Allocate ghost state *)
      iApply fupd_wp.
      iMod (own_alloc (@unset conn_mapC)) as (γD) "ownD"; first done.
      iMod (own_alloc (@unset name_mapC)) as (γN) "ownN"; first done.
      iMod (own_alloc (@unset task_mapC)) as (γM) "ownM"; first done.
      set (T := TaskData e' Γ η η' A D M γD γM γN).
      iMod (own_alloc (to_agree T)) as (γ) "#ownγ"; first done.
      iAssert (WP subst (of_val <$> σ) e {{ x,
                                            int_i_promise_body int_s_type int_s_heap
                                                               M N A τ
                                                               (int_i_type τ) γ  x ∗
                                                               int_i_wait_body γ η'
                                                               (int_i_heap η') A
                                                               M N }})
        with "[ownD ownM ownN del pre]"
        as "wp".
      { iSpecialize ("del" with "pre").
        iApply wp_fupd.
        iApply (wp_wand with "del").
        iIntros (v) "H".
        iDestruct "H" as (N' M' D' d') "[eqs [ty [heap sim]]]".
        iMod (own_update _ _ (agreed D') with "ownD") as "#ownD"; first apply oneshot_update.
        iMod (own_update _ _ (agreed (M': task_mapC)) with "ownM") as "#ownM";
          first apply oneshot_update.
        iMod (own_update _ _ (agreed (N': name_mapC)) with "ownN") as "#ownN";
          first apply oneshot_update.
        iModIntro.
        iDestruct "eqs" as %[eqN [eqM eqd]].
        iSplitR "heap".
        - iExists T, D', M', N'.
          iSplit.
          { repeat iSplit; auto. }
          rewrite /ip_impl /ip_sim.
          iSplitL "ty".
          { iExists d'; iSplit; last done.
            iPureIntro.
            assert (of_gset (names τ ∖ A) ⊆ not_new A).
            { clear; intro; rewrite /not_new elem_of_difference !elem_of_of_gset; set_solver. }
            repeat split; auto.
            all: apply overlap_cast; by eapply overlap_mono. }
          iDestruct "sim" as "#sim"; iAlways.
          iIntros (Ns Ns' σs eqNs _ p K) "ctx pre move".
          iMod ("sim" with "ctx pre move") as (vs) "[post move]".
          iModIntro; iExists vs; iFrame.
          iDestruct "post" as (ds Ns'') "[maps [type heap]]".
          iDestruct "maps" as %[eqM' [eqN' eqd']].
          rewrite eqd in eqd'; injection eqd' as <-.
          iExists d', (Ns'' ~[A]~> Ns).
          iSplit.
          { iPureIntro; split; last done.
            intro ξ'.
            rewrite /not_new elem_of_difference elem_of_of_gset => [[_ notinξ']].
            rewrite lookup_merge_along_not_in; done. }
          iSplitL "type".
          + iApply (int_s_type_local with "type").
            1,2,4: done.
            intros ξ' inξ'.
            destruct (decide (ξ' ∈ A)) as [case|case].
            * by rewrite lookup_merge_along_in.
            * rewrite lookup_merge_along_not_in; last done.
              rewrite (eqNs ξ'); last rewrite elem_of_difference elem_of_union; auto.
              rewrite (eqN' ξ'); first done.
              rewrite /not_new elem_of_difference elem_of_of_gset; split; auto; clear; set_solver.
          + iApply (int_s_heap_local with "heap").
            1,2,4: done.
            intros ξ' inξ'.
            destruct (decide (ξ' ∈ A)) as [case|case].
            * by rewrite lookup_merge_along_in.
            * rewrite lookup_merge_along_not_in; last done.
              rewrite (eqNs ξ'); last rewrite elem_of_difference elem_of_union; auto.
              rewrite (eqN' ξ'); first done.
              rewrite /not_new elem_of_difference elem_of_of_gset; split; auto; clear; set_solver.
        - iExists T, D', N', M'; iFrame.
          iSplit.
          { by repeat iSplit. }
          assert (of_gset (names η' ∖ A) ⊆ not_new A).
          { clear; intro; rewrite /not_new elem_of_difference !elem_of_of_gset; set_solver. }
          iPureIntro; split.
          all: apply overlap_cast; eapply overlap_mono; eauto. }
      iPoseProof (wp_post ⊤ with "wp") as "wp".
      iModIntro.
      iApply wp_fupd.
      iApply (wp_wand with "wp").
      iIntros (v) "H".
      iDestruct "H" as (t) "[% wait]"; subst.
      iPoseProof (wait_split with "wait") as "waits".
      iPoseProof (fupd_mask_mono _ ⊤ with "waits") as "waits"; first auto.
      iMod "waits" as "[promise wait]".      
      iMod (inv_alloc promiseN with "promise") as "promise".
      iAssert (int_i_type (Promise(ξ,A) τ) Cunit (<[ξ:=γ]>M) (<[ξ:=Task t]>N) (Ctid t))
        with "[promise]" as "promise".
      { cbn; iExists t, γ; iSplit.
        - rewrite !lookup_insert; auto.
        - iApply (inv_Proper with "promise").
          apply wait_Proper; intro v.
          rewrite /int_i_promise_body /ip_impl.
          intro_equiv U; intro_equiv D'; intro_equiv M'; intro_equiv N'.          
          do 8 f_equiv.
          + apply (overlap_iff (names τ ∖ A)); first done.
            intros ξ' inξ'.
            rewrite -delete_insert_eq.
            apply lookup_delete_ne.
            clear -inξ' ξ_fresh_τ; set_solver.
          + apply (overlap_iff (names τ ∖ A)); first done.
            intros ξ' inξ'.
            rewrite -delete_insert_eq.
            apply lookup_delete_ne.
            clear -inξ' ξ_fresh_τ; set_solver. }
      iAssert (int_i_heap (Wait(ξ,A) η') (<[name ξ:=VConst Cunit]>(<[RET:=VConst Cunit]>∅))
                          (<[ξ:=γ]>M) (<[ξ:=Task t]>N))
        with "[wait]" as "wait".
      { cbn; iExists t, γ.
        rewrite !lookup_insert; iSplit; auto.
        iApply (wait_Proper with "wait"); intro v.
        rewrite /int_i_wait_body.
        intro_equiv U; intro_equiv D'; intro_equiv N'; intro_equiv M'.
        do 4 f_equiv.
        - rewrite -!(symmetry_iff (overlap _) N').
          apply (overlap_iff (names η' ∖ A)); first done.
          intros ξ' inξ'.
          rewrite -delete_insert_eq.
          apply lookup_delete_ne.
          clear -inξ' ξ_fresh_η'; set_solver.
        - rewrite -!(symmetry_iff (overlap _) M').
          apply (overlap_iff (names η' ∖ A)); first done.
          intros ξ' inξ'.
          rewrite -delete_insert_eq.
          apply lookup_delete_ne.
          clear -inξ' ξ_fresh_η'; set_solver. }
      iModIntro.
      iExists (<[ξ:=Task t]>N), (<[ξ:=γ]>M),
        (<[name ξ:=VConst Cunit]>(<[RET:=VConst Cunit]>∅)), (VConst Cunit).
      iFrame.
      iSplit.
      { rewrite lookup_insert_ne; last discriminate.
        rewrite lookup_insert.
        iPureIntro.
        repeat split.
        all: intro ξ'; rewrite /not_new elem_of_difference elem_of_of_gset
                               elem_of_singleton => [[_ notin]].
        all: by rewrite lookup_insert_ne. }
      clear σ N.
      iAlways.
      iIntros (N σ p K) "#ctx [env pre] move"; cbn -[difference].
      iMod (simulate_post with "ctx move") as (p') "[move [move' neq]]"; auto.
      iDestruct "pre" as (n) "pre".
      iExists (Ctid p'); iFrame.
      iExists (VConst Cunit), (<[ξ:=Task p']>N).
      iModIntro.
      iAssert (int_s_heap (Wait(ξ,A) η') (<[name ξ:=VConst Cunit]>(<[RET:=VConst Cunit]>∅))
                          (<[ξ:=γ]>M) (<[ξ:=Task p']>N))
        with "[pre move' env]" as "$".
      { iExists (S n); cbn.
        iExists p', γ, T, σ.
        iSplit.
        { iPureIntro; rewrite !lookup_insert; repeat split; auto.
          intro ξ'.
          rewrite elem_of_difference => [[inη' notinA]].
          rewrite lookup_insert_ne //.
          intros <-; contradiction.
        }
        iFrame.
        iSplit; auto.
        iExists N; iFrame. }
      iDestruct "neq" as %neq.
      iSplit.
      { iPureIntro; repeat split.
        - intros ξ'.
          rewrite /not_new elem_of_difference elem_of_of_gset not_elem_of_singleton => [[_ ?]].
          rewrite lookup_insert_ne; done.
        - intros ξ'.
          rewrite /not_new elem_of_difference elem_of_of_gset not_elem_of_singleton => [[_ ?]].
          rewrite lookup_insert_ne; done.
        - by rewrite lookup_insert_ne ?lookup_insert. }
      iExists γ, T.
      iSplit; auto.
      iPureIntro.
      exists p'.
      rewrite !lookup_insert.
      repeat split; auto.
      intros ξ'.
      rewrite elem_of_difference => [[inξ' _]].
      rewrite lookup_insert_ne; cbn; congruence.
    Qed.

    Instance wait_proper: Proper (eq ==> pointwise_relation _ (⊣⊢) ==> (⊣⊢)) (wait (Σ := Σ)).
    Proof. solve_proper. Qed.
    
    Lemma closed_wait x ξ A (τ: type) (η: heap) (nssep: (↑waitN: coPset) ⊥ ↑promiseN)
          (ξ_not_in_τ: ξ ∉ names τ) (ξ_not_in_η: ξ ∉ names η):
      delayed_typed (<[x:=ttask ξ A τ]>∅) (hwait ξ A η) (Wait x) (Wait x) A τ η.
    Proof.
      iIntros (D M N σ) "[[env_names env] pre]".
      iDestruct "env_names" as %[domσ domD].
      assert (is_Some (σ !! x)) as [v val_x].
      { apply domσ; rewrite lookup_insert; eauto. }
      assert (is_Some (D !! var x)) as [d conn_x].
      { apply domD; rewrite lookup_insert; eauto. }
      iDestruct ("env" $! x _ v d with "[]") as "#promise".
      { rewrite lookup_insert; eauto. }
      rewrite /= lookup_fmap val_x /=.
      iDestruct "promise" as (t γ) "[eqs promise]".
      iDestruct "eqs" as %[nameξ [mtξ ->]].
      iApply fupd_wp.
      iInv promiseN as "promisewait" "close".
      rewrite /typetranslation.wp_wait /=.
      iPoseProof (wait_split_later with "[promisewait]") as "split".
      { iNext.
        iApply (wait_proper with "promisewait"); first done.
        iIntros (v); iSplit.
        - iIntros "[pb _]"; iExact "pb".
        - rewrite /int_i_promise_body.
          iIntros "#pre".
          iSplit; iExact "pre". }
      iPoseProof (fupd_mask_mono _ (⊤ ∖ ↑promiseN) with "split") as "split"; first solve_ndisj.
      iMod "split" as "[promisewait pw']".
      iMod ("close" with "pw'") as "_".
      iDestruct "pre" as (t' γ') "[mtξ' pre]".
      rewrite mtξ nameξ.
      iDestruct "mtξ'" as %[[=<-] [=<-]].
      iPoseProof (wait_combine_later with "[$pre $promisewait]") as "wait".
      iPoseProof (fupd_mask_mono _ ⊤ with "wait") as "wait"; first solve_ndisj.
      iMod "wait" as "wait".
      iModIntro.
      iPoseProof (wp_wait with "wait") as "wp".
      iApply (wp_wand with "wp").
      iIntros (v) "[wb pb]".
      rewrite /int_i_wait_body /int_i_promise_body.
      iDestruct "wb" as (T D' N' M') "[[#eqT [#eqD [#eqN #eqM]]] [eqnames heap]]".
      iClear "promise".
      iDestruct "pb" as (T' D'' M'' N'') "[[eqT' [eqD' [eqN' eqM']]] [promise #sim]]".
      iDestruct "promise" as (d') "[eqnames' type]".
      iDestruct "eqnames" as %[eqN eqM].
      iDestruct "eqnames'" as %[eqD [eqN' eqM']].
      iPoseProof (own_valid_2 with "eqT eqT'") as "eqT'".
      rewrite uPred.discrete_valid.
      iDestruct "eqT'" as %?%agree_op_invL'; subst T'.
      iPoseProof (own_valid_2 with "eqD eqD'") as "eqD'".
      iPoseProof (own_valid_2 with "eqN eqN'") as "eqN'".
      iPoseProof (own_valid_2 with "eqM eqM'") as "eqM'".
      rewrite !uPred.discrete_valid.
      iDestruct "eqD'" as %?%(agreed_valid D' D'')%leibniz_equiv; subst D''. 
      iDestruct "eqN'" as %?%(agreed_valid N' N'')%leibniz_equiv; subst N''. 
      iDestruct "eqM'" as %?%(agreed_valid M' M'')%leibniz_equiv; subst M''.
      iExists (N' ~[A]~> N).
      iExists (M' ~[A]~> M).
      iExists (<[RET:=d']>D').
      iExists d'.      
      repeat iSplit.
      1,2,3: iPureIntro.
      { intros ξ' inξ'.
        rewrite lookup_merge_along_not_in; first done.
        rewrite /not_new elem_of_difference elem_of_of_gset in inξ' * => [[_ notinξ']]; done. }
      { intros ξ' inξ'.
        rewrite lookup_merge_along_not_in; first done.
        rewrite /not_new elem_of_difference elem_of_of_gset in inξ' * => [[_ notinξ']]; done. }
      { by rewrite lookup_insert. }
      { iApply (int_i_type_local with "type").
        1,4: done.
        all: intros ξ' inξ'.
        all: destruct (decide (ξ' ∈ A)) as [case|case].
        1,3: by rewrite lookup_merge_along_in.
        all: rewrite lookup_merge_along_not_in; last done.
        - rewrite (eqM' ξ'); last by rewrite elem_of_difference.
          rewrite lookup_delete_ne; first done.
          intros <-; contradiction.
        - rewrite (eqN' ξ'); last by rewrite elem_of_difference.
          rewrite lookup_delete_ne; first done.
          intros <-; contradiction. }
      { iApply (int_i_heap_local with "heap").
        { intro n; rewrite elem_of_names_heap; intros [ξ' [-> inξ']].
          apply lookup_insert_ne; discriminate. }
        all: intros ξ' inξ'.
        all: destruct (decide (ξ' ∈ A)) as [case|case].
        1,3: by rewrite lookup_merge_along_in.
        all: rewrite lookup_merge_along_not_in; last done.
        - rewrite -(eqM ξ'); last by rewrite elem_of_difference.
          rewrite lookup_delete_ne; first done.
          intros <-; contradiction.
        - rewrite -(eqN ξ'); last by rewrite elem_of_difference.
          rewrite lookup_delete_ne; first done.
          intros <-; contradiction. }
      iAlways.
      iClear "eqN".
      clear N N' eqN eqN' σ domσ val_x v nameξ.
      iIntros (N σ p K) "#ctx [[env_names env] pre] move".
      iDestruct "env_names" as %[domσ _].
      assert (is_Some (σ !! x)) as [v val_x].
      { apply domσ; rewrite lookup_insert; eauto. }
      iSpecialize ("env" $! x _ v d with "[]").
      { rewrite lookup_insert; auto. }
      iRename "env" into "promise".
      iDestruct "pre" as (n) "pre".
      destruct n; cbn -[difference].
      all: iDestruct "pre" as (t' γ' U σ') "[maps [ownU [move' wait]]]".
      { iDestruct "wait" as (?) "[_ []]". }
      iDestruct "wait" as (Npre) "pre".
      iDestruct "promise" as (γ'' T'') "[agree'' promise]".
      iDestruct "promise" as %[t'' [mtt'' [mtγ'' [-> eqMτ]]]].
      iDestruct "maps" as %[mtt' [mtγ' [<- [<- eqMη]]]].
      rewrite mtt' in mtt''; injection mtt'' as <-.
      rewrite mtγ' in mtγ''; injection mtγ'' as <-.
      rewrite mtξ in mtγ'; injection mtγ' as <-.
      iPoseProof (own_valid_2 with "eqT ownU") as "ownU".
      iPoseProof (own_valid_2 with "eqT agree''") as "agree''".
      rewrite !uPred.discrete_valid.
      iDestruct "ownU" as %?%(agreed_valid T U)%leibniz_equiv; subst U.
      iDestruct "agree''" as %?%(agreed_valid T _)%leibniz_equiv; subst.
      rewrite lookup_fmap val_x /=.
      iMod (simulate_wait_schedule with "ctx move move'") as "[move move']"; first done.
      rename T'' into T.
      iSpecialize ("sim" $! (Npre ~[(names τ ∪ names (td_post T)) ∖ td_alloc T]~> N) Npre σ'
                         (overlap_merge_along_l _ _ _) eq_refl).
      iMod ("sim" $! _ [] with "ctx [pre] move'") as (v) "[post move']".
      { iDestruct "pre" as "[$ pre]"; iExists n; iFrame. }
      iDestruct "post" as (d'' N'') "[names [type heap]]".
      iMod (simulate_done_schedule with "ctx move' move") as "[move' move]".
      1,2: eauto using to_of_val.
      iAssert (⌜t' ≠ p⌝) with "[move move']" as %neqp.
      { iDestruct "move" as "[move _]".
        iPoseProof (own_valid_2 with "move move'") as "valid".
        rewrite /task_runnable /task_done -auth.auth_frag_op uPred.discrete_valid.
        iDestruct "valid" as %valid; iPureIntro.
        intros ->.
        rewrite auth_valid_eq /= in valid.
        specialize (valid p).
        rewrite gmap.lookup_op !lookup_singleton in valid.
        contradiction. }
      iMod (simulate_wait_done with "ctx move move'") as "[move move']".
      1,2: done.
      iModIntro; iExists v; iFrame.
      iExists d'', (N'' ~[ td_alloc T ]~> N); iFrame.
      rewrite lookup_insert.
      iDestruct "names" as %[eqN eqD'].
      repeat iSplit.
      1,2,3: iPureIntro.
      - intro ξ'.
        rewrite /not_new elem_of_difference elem_of_of_gset => [[_ notin]].
        rewrite lookup_merge_along_not_in; done.
      - intro ξ'.
        rewrite /not_new elem_of_difference elem_of_of_gset => [[_ notin]].
        rewrite lookup_merge_along_not_in; done.
      - congruence.
      - iApply (int_s_type_local with "type").
        1,4: done.
        + intros ξ' inξ'.
          destruct (decide (ξ' ∈ td_alloc T)) as [case|case].
          * by rewrite lookup_merge_along_in.
          * rewrite lookup_merge_along_not_in; last done.
            rewrite (eqM' ξ').
            2: rewrite /not_new elem_of_difference; auto.
            rewrite lookup_delete_ne; first done; congruence.
        + intros ξ' inξ'.
          destruct (decide (ξ' ∈ td_alloc T)) as [case|case].
          * by rewrite lookup_merge_along_in.
          * rewrite lookup_merge_along_not_in; last done.
            rewrite -(eqN ξ').
            2: rewrite /not_new elem_of_difference elem_of_of_gset; clear -case; set_solver.
            rewrite lookup_merge_along_in.
            shelve.
      - iApply (int_s_heap_local with "post").
        + intro n'.
          rewrite elem_of_names_heap =>[[ξ' [-> inξ']]].
          rewrite lookup_insert_ne; done.
        + intros ξ' inξ'.
          destruct (decide (ξ' ∈ td_alloc T)) as [case|case].
          * by rewrite lookup_merge_along_in.
          * rewrite lookup_merge_along_not_in; last done.
            rewrite -(eqM''' ξ').
            2: rewrite /not_new elem_of_difference elem_of_of_gset; clear -case; set_solver.
            rewrite (eqM'' ξ'); first done.
            rewrite elem_of_difference; auto.
        + intros ξ' inξ'.
          destruct (decide (ξ' ∈ td_alloc T)) as [case|case].
          * by rewrite lookup_merge_along_in.
          * rewrite lookup_merge_along_not_in; last done.
            rewrite -(eqN''' ξ').
            2: rewrite /not_new elem_of_difference elem_of_of_gset; clear -case; set_solver.
            rewrite (eqN ξ'); first done.
            rewrite elem_of_difference; auto.
    Qed.
    