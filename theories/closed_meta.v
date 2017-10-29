From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import invariants.
From esop Require Import overlap delayed specification typetranslation types corecalculus.
From stdpp Require Import gmap coPset.

Section Theory.
  Context `{allG Σ}.
  (** Meta theory: The framing lemma *)
  Definition frame ηf (D D': conn_map): conn_map := D ~[conn_heap ηf]~> D'.

  Lemma frame_generic          
        (int_ty: type → @intT_type Σ) (int_he: hexpr → @intT_heap Σ) τ (η ηf: hexpr)
        D D' d v (N N': name_map)
        (novN: N ≡[names ηf]≡ N')
        (int_he_split: ∀ D'' N'',
            int_he (hstar η ηf) D'' N'' ⊣⊢ int_he η D'' N'' ∗ int_he ηf D'' N'')
        (int_he_local: ∀ η,
            Proper (overlap (conn_heap η) ==> overlap (names η) ==> (≡)) (int_he η))
        (disj: names η ⊥ names ηf):
    int_he ηf D N -∗ (⌜D' !! RET = Some d⌝ ∗ int_ty τ d N' v ∗ int_he η D' N') -∗
           (⌜frame ηf D D' !! RET = Some d⌝) ∗
           int_ty τ d N' v ∗ int_he (hstar η ηf) (frame ηf D D') N'.
  Proof.
    iIntros "frame [eqd [type heap]]".
    iFrame.
    iSplitL "eqd".
    { iDestruct "eqd" as %eqd.
      iPureIntro.
      rewrite /frame lookup_merge_along_not_in //.
      rewrite elem_of_conn_heap => [[? [? _]]]; done. }
    rewrite int_he_split.
    iSplitL "heap".
    - iApply (int_he_local with "heap").
      2,3: done.
      apply overlap_merge_along_r.
      intro ξ.
      rewrite !elem_of_conn_heap => [[ξ₁ [eq₁ in₁]] [ξ₂ [eq₂ in₂]]]; subst.
      injection eq₂ as <-; apply (disj ξ₁); done.
    - by iApply (int_he_local with "frame"); first apply overlap_merge_along_l.
  Qed.

  Lemma int_s_rec_split n η η' D N:
    int_s_heap_rec n (hstar η η') D N ⊣⊢ int_s_heap_rec n η D N ∗ int_s_heap_rec n η' D N.
  Proof. destruct n; done. Qed.
  
  Lemma int_s_heap_split η η' D N:
    int_s_heap (hstar η η') D N ⊣⊢ (int_s_heap η D N ∗ int_s_heap η' D N).
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
  
  Lemma frame_existential Γ e (η: hexpr) A τ (η': hexpr) D D' D'' (ηf: hexpr)
        (disj': names η' ⊥ names ηf) (disj: names η ⊥ names ηf) (disj'': names ηf ⊥ A):
    simulation Γ e η A τ η' D D' -∗
               simulation Γ e (hstar η ηf) A τ (hstar η' ηf) (frame ηf D'' D)
               (frame ηf D'' D').
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
        intro n.
        rewrite elem_of_conn_heap elem_of_conn_env => [[ξ [??]] [ξ' [eqξ ?]]].
        subst; discriminate.
      - iApply (int_s_heap_local with "pre"); last done.
        rewrite /frame; symmetry.
        apply: overlap_merge_along_r => [n].
        rewrite !elem_of_conn_heap => [[ξ [??]] [ξ' [eqξ ?]]]; subst.
        injection eqξ as <-.
        apply (disj ξ); done. }
    iDestruct "post" as (d N') "[eqs [type post]]".
    iModIntro; iExists v; iFrame.
    iDestruct "eqs" as %[eqN eqd].
    iExists d, N'.
    assert ((of_gset (names ηf): coPset) ⊆ (not_new A: coPset)).
    { intro x; rewrite elem_of_of_gset elem_of_not_new; exact (disj'' x). }
    iPoseProof (frame_generic int_s_type int_s_heap τ η' ηf D'' D' d v N N'
                with "[frame] [$type $post]") as "post".
    all: try done.
    { apply overlap_cast, (overlap_sub (not_new A)); last done.
      intro x; rewrite elem_of_of_gset elem_of_not_new; exact (disj'' x). }
    - apply int_s_heap_split.
    - intro; apply int_s_heap_local.
    - iApply (int_s_heap_local with "frame"); last done.
      symmetry; apply overlap_merge_along_l.
    - iDestruct "post" as "[% [$$]]"; auto.
  Qed.

  Lemma simulation_local Γ e η A τ η':
    Proper (overlap (conn_env Γ ∪ conn_heap η) ==> overlap ({[RET]} ∪ conn_heap η') ==> (⊣⊢))
           (simulation Γ e η A τ η').
  Proof.
    iIntros (D D' eqD E E' eqE).
    rewrite /simulation /simulation_body /existential_triple.
    f_equiv; intro N.
    f_equiv; intro σ.
    f_equiv; intro p.
    f_equiv; intro K.
    do 2 f_equiv.
    { f_equiv.
      - apply int_s_env_local.
        2-4: done.
        eapply overlap_sub; last done.
        apply union_subseteq_l.
      - apply int_s_heap_local.
        2,3: done.
        eapply overlap_sub; last done.
        apply union_subseteq_r. }
    do 3 f_equiv; intro v.
    do 2 f_equiv; intro d.
    f_equiv; intro N'.
    f_equiv.
    { rewrite (eqE RET); first done.
      clear; set_solver. }
    f_equiv.
    apply int_s_heap_local; last done.
    eapply overlap_sub; last done.
    apply union_subseteq_r.
  Qed.
  
  Lemma closed_frame Γ e e' (η: hexpr) A τ (η' ηf: hexpr)
        (disj': names η' ⊥ names ηf) (disj: names η ⊥ names ηf) (disj'': names ηf ⊥ A):
    delayed_typed Γ η e e' A τ η' -∗
                  delayed_typed Γ (hstar η ηf) e e' A τ (hstar η' ηf).
  Proof.
    iIntros "del".
    iIntros (D N σ); cbn -[difference].
    iIntros "[env [pre frame]]".
    iSpecialize ("del" $! D N σ with "[$env $pre]").
    iApply (wp_wand with "del").
    iIntros (v) "post".
    iDestruct "post" as (N' D' d') "[eqs [type [#sim post]]]".
    iExists N', (frame ηf D D'), d'.
    iFrame.
    iDestruct "eqs" as %[eqN eqD'].
    iSplit.
    { iPureIntro; split; auto.
      rewrite /frame lookup_merge_along_not_in; first done.
      rewrite elem_of_conn_heap => [[? [? _]]]; done. }
    iSplit.
    { iAlways.
      iIntros (Ns Ds p K) "ctx [env pre] move".
      rewrite int_s_heap_split.
      iDestruct "pre" as "[pre frame]".
      iMod ("sim" with "ctx [$env $pre] move") as (v') "[post move]".
      iModIntro; iExists v'; iFrame.
      iDestruct "post" as (d Ns') "[names [type post]]".
      iDestruct "names" as %[eqNs eqDs].
      iPoseProof (frame_generic with "frame [type $post]") as "post".
      - apply overlap_cast, (overlap_sub (not_new A)); last done.
        intro ξ; rewrite elem_of_of_gset elem_of_not_new; exact (disj'' ξ).
      - by intros; rewrite int_s_heap_split.
      - apply int_s_heap_local.
      - done.
      - iSplit; first done; iExact "type".
      - iExists d, _.
        iDestruct "post" as "[? [$$]]".
        iDestruct "post" as %->; iPureIntro; auto. }
    iSplitR "frame"; iApply int_i_heap_local.
    3,6: iFrame.
    2: done.
    - rewrite /frame overlap_merge_along_r; first done.
      intro n; rewrite !elem_of_conn_heap => [[ξ [??]] [? [eqξ ?]]]; subst.
      injection eqξ as <-; by apply (disj' ξ).
    - apply overlap_merge_along_l.
    - apply overlap_cast, (overlap_sub (not_new A)); last done.
      intro ξ; rewrite !elem_of_of_gset elem_of_not_new; exact (disj'' ξ).
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
  
  Lemma restrict_env (int_ty: type → @intT_type Σ) Γ Γ' D N σ (sub: Γ ⊆ Γ'):
    int_env_pre int_ty Γ' D N σ -∗ int_env_pre int_ty Γ D N (restrict_subst Γ σ).
  Proof.
    rewrite /int_env_pre.
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
    iIntros (D N σ) "[env pre]".
    iSpecialize ("spec" $! D N (restrict_subst Γ σ) with "[env $pre]").
    { by iApply (restrict_env with "env"). }
    rewrite restrict_env_fmap (subst_restrict_with_type ty).
    iApply (wp_wand with "spec").
    iIntros (v) "post".
    iDestruct "post" as (N' D' d') "[eqs [type [#sim post]]]".
    iExists N', D', d'; iFrame.
    iDestruct "eqs" as %[eqN eqd].
    iSplit.
    { iPureIntro; repeat split; auto.        
      all: eapply overlap_mono; done. }
    clear eqN N N' σ v; iAlways.
    iIntros (N σ p K) "ctx [env pre] move".
    rewrite -(subst_restrict_with_type ty') -restrict_env_fmap.
    iMod ("sim" $! N (restrict_subst Γ σ) p K with "ctx [env $pre] move") as (v) "[post move]".
    { by iApply (restrict_env with "env"). }
    iModIntro; iExists v; iFrame.
    iDestruct "post" as (d N') "[eqs [type post]]".
    iExists d, N'; iFrame.
    iDestruct "eqs" as %[eqN eqD].
    iPureIntro; repeat split; auto.
    all: by eapply overlap_mono.
  Qed.

  (** Meta theory: Generalized contexts and the binding lemma. *)
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
               -∗ simulation (<[x:=τ₁]>Γ) (fill_gctx x K) η₂ A₂ τ₂ η₃
               (strengthen Γ x d D₁ D₂) D₃
               -∗ simulation Γ (fill_gctx e K) η₁ (A₁ ∪ A₂) τ₂ η₃ D₁ D₃.
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

End Theory.