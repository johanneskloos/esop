From esop Require Import types corecalculus closure delayed typetranslation.
From stdpp Require Import gmap prelude.
From mathcomp Require Import ssreflect.

Section ectx_typing.
  Context (hU: lnames) (hΓ: env) (hη: hexpr) (hA: lnames) (hτ: type) (hη': hexpr).
  Notation "x :! l" := (l ++ [x]) (at level 50).
  
  Inductive ectx_typing:
    lnames → env → list ectx_item → hexpr → lnames → type → hexpr → Prop :=
  | etyhole: ectx_typing hU hΓ [] hη hA hτ hη'
  | etyletl U Γ (x: binder) η₁ η₂ η₃ τ₁ τ₂ A₁ A₂ e K:
      typing U Γ e η₁ A₁ τ₁ η₂ →
      ectx_typing (U ∪ A₁) (insert' x τ₁ Γ) K η₂ A₂ τ₂ η₃ →
      ectx_typing U Γ (EAppL e :! (ERec BAnon x :! K)) η₁ (A₁ ∪ A₂) τ₂ η₃
  | etyletr U Γ (x: binder) η₁ η₂ η₃ τ₁ τ₂ A₁ A₂ e K:
      ectx_typing U Γ K η₁ A₁ τ₁ η₂ →
      typing (U ∪ A₁) (insert' x τ₁ Γ) e η₂ A₂ τ₂ η₃ →
      ectx_typing U Γ (EAppR (Rec BAnon x e) :! K) η₁ (A₁ ∪ A₂) τ₂ η₃
  | etyifl U Γ η₁ η₂ η₃ τ A₁ A₂ K e e':
      ectx_typing U Γ K η₁ A₁ tbool η₂ →
      typing (U ∪ A₁) Γ e η₂ A₂ τ η₃ →
      typing (U ∪ A₁) Γ e' η₂ A₂ τ η₃ →
      ectx_typing U Γ (EIfL e e' :! K) η₁ (A₁ ∪ A₂) τ η₃
  | etyifm U Γ η₁ η₂ η₃ τ A₁ A₂ K e e':
      typing U Γ e η₁ A₁ tbool η₂ →
      ectx_typing (U ∪ A₁) Γ K η₂ A₂ τ η₃ →
      typing (U ∪ A₁) Γ e' η₂ A₂ τ η₃ →
      ectx_typing U Γ (EIfM e e' :! K) η₁ (A₁ ∪ A₂) τ η₃
  | etyifr U Γ η₁ η₂ η₃ τ A₁ A₂ K e e':
      typing U Γ e η₁ A₁ tbool η₂ →
      typing (U ∪ A₁) Γ e' η₂ A₂ τ η₃ →
      ectx_typing (U ∪ A₁) Γ K η₂ A₂ τ η₃ →
      ectx_typing U Γ (EIfR e e' :! K) η₁ (A₁ ∪ A₂) τ η₃
  | etyref U Γ K η₁ η₂ τ A ξ (ξ_fresh: ξ ∉ U ∪ A) (post_wf: heap_wf (U ∪ A ∪ {[ξ]}) (η₂ ⊗ ξ ↦ τ)):
      ectx_typing U Γ K η₁ A τ η₂ →
      ectx_typing U Γ (EAlloc :! K) η₁ (A ∪ {[ ξ ]}) (Ref(ξ)) (η₂ ⊗ ξ ↦ τ)
  | etyread U Γ K η₁ η₂ ξ τ A:
      ectx_typing U Γ K η₁ A (Ref(ξ)) (η₂ ⊗ ξ ↦ τ) →
      ectx_typing U Γ (ERead :! K) η₁ A τ (η₂ ⊗ ξ ↦ τ)
  | etywritel U Γ K e η₁ η₂ η₃ ξ τ A₁ A₂:
      ectx_typing U Γ K η₁ A₁ (Ref(ξ)) η₂ →
      typing (U ∪ A₁) Γ e η₂ A₂ τ (η₃ ⊗ ξ ↦ τ) →
      ectx_typing U Γ (EWriteL e :! K) η₁ (A₁ ∪ A₂) Unit (η₃ ⊗ ξ ↦ τ)
  | etywriter U Γ K e η₁ η₂ η₃ ξ τ A₁ A₂:
      typing U Γ e η₁ A₁ (Ref(ξ)) η₂ →
      ectx_typing (U ∪ A₁) Γ K η₂ A₂ τ (η₃ ⊗ ξ ↦ τ) →
      ectx_typing U Γ (EWriteR e :! K) η₁ (A₁ ∪ A₂) Unit (η₃ ⊗ ξ ↦ τ)
  | etypost U Γ K η₁ η₂ τ A ξ (ξ_fresh: ξ ∉ U ∪ A) (wf_post: heap_wf (U ∪ {[ξ]}) (Wait(ξ,A) η₂)):
      ectx_typing U Γ K η₁ A τ η₂ → 
      ectx_typing U Γ (EPost :! K) η₁ {[ξ]} (Promise(ξ,A) τ) (Wait(ξ,A) η₂)
  | etywait U Γ K (η₁ η₂ η₃: hexpr) τ ξ A₁ A₂ (wfη: heap_wf (U ∪ A₁ ∪ A₂) (η₂ ⊗ η₃)) (disj: A₂ ⊥ U)
           (ξ_not_in_τ: ξ ∉ names τ) (ξ_not_in_η₃: ξ ∉ names η₃) (disjA: A₁ ⊥ A₂):
      ectx_typing U Γ K η₁ A₁ (ttask ξ A₂ τ) (η₂ ⊗ hwait ξ A₂ η₃) →
      ectx_typing U Γ (EWait :! K) η₁ (A₁ ∪ A₂) τ (η₂ ⊗ η₃)
  | etyframe U Γ K (η₁ η₂: hexpr) τ A (ηf: hexpr)
            (disjη: res_names η₁ ⊥ res_names ηf)
            (disjη': res_names η₂ ⊥ res_names ηf)
            (disjA: A ⊥ names ηf) (wf: heap_wf (U ∪ A) ηf):
      ectx_typing U Γ K η₁ A τ η₂ →
      ectx_typing U Γ K (η₁ ⊗ ηf) A τ (η₂ ⊗ ηf)
  | etyweaken U Γ K η₁ η₂ τ A U' Γ' A' (env_good: names Γ ⊆ U) (pre_good: names η₁ ⊆ U) (disjUA: U' ⊥ A')
             (subU: U ⊆ U') (subΓ: Γ ⊆ Γ') (subA: A ⊆ A') (wf: heap_wf (A' ∪ U') η₂):
      ectx_typing U Γ K η₁ A τ η₂ →
      ectx_typing U' Γ' K η₁ A' τ η₂
  | etyproper U U' Γ K η₁ η₁' A A' τ η₂ η₂'
             (eqU: U ≡ U') (eqη₁: η₁ ≡ η₁') (eqA: A ≡ A') (eqη₂: η₂ ≡ η₂'):
      ectx_typing U Γ K η₁ A τ η₂ → ectx_typing U' Γ K η₁' A' τ η₂'.

  Lemma fill_typing e (tye: typing hU hΓ e hη hA hτ hη') U Γ K η A τ η':
    ectx_typing U Γ K η A τ η' →
    typing U Γ (fill_ectx e K) η A τ η'.
  Proof.
    induction 1; auto.
    all: rewrite -?fill_ectx_app /=.
    all: try by econstructor; eauto.
    eapply typroper; eauto.
  Qed.
End ectx_typing.

Lemma ectx_closed `{allG Σ}
      `(ty: ectx_typing hU hΓ hη hA hτ hη' U Γ K η A τ η'): ∀ e e',
    names Γ ⊆ U → heap_wf U η →
    delayed_simulation hU hΓ hη e e' hA hτ hη' →
    delayed_simulation U Γ η (fill_ectx e K) (fill_ectx e' K) A τ η'.
Proof.
  induction ty; intros * Γgood ηwf sim; first done.
  all: rewrite -?fill_ectx_app /=.
  - eapply closure_let; eauto using fundamental.
    destruct (typing_good_names _ _ _ _ _ _ _ H0) as [disj [subτ subη]];
      auto using heap_wf_names.
    apply IHty; auto.
    + intros ξ [?|?]%elem_of_names_env_insert'; auto.
      apply elem_of_union_l; auto.
    + eapply typing_wf; eauto.
  - eapply closure_let; eauto using fundamental.
    apply IHty in sim; auto.
    destruct sim.
    apply fundamental; auto.
    + eapply typing_wf; eauto.
    + intros ξ [?|?]%elem_of_names_env_insert'; last by apply elem_of_union_l; auto.
      apply typing_good_names in ds_type_e; auto.
      * by destruct ds_type_e as [_ [sub _]]; apply sub.
      * etrans; last eassumption.
        apply union_subseteq_r.
  - assert (names Γ ⊆ U ∪ A₁) by (etrans; first apply Γgood; apply union_subseteq_l).
    assert (heap_wf (U ∪ A₁) η₂).
    { apply IHty in sim; auto.
      destruct sim as [_ ty' _ _].
      apply typing_wf in ty'; auto. }
    eapply closure_if; auto.
    all: apply fundamental; auto.
  - assert (names Γ ⊆ U ∪ A₁) by (etrans; first apply Γgood; apply union_subseteq_l).
    assert (heap_wf (U ∪ A₁) η₂).
    { apply typing_wf in H0; eauto. }
    eapply closure_if; auto.
    all: apply fundamental; auto.
  - assert (names Γ ⊆ U ∪ A₁) by (etrans; first apply Γgood; apply union_subseteq_l).
    assert (heap_wf (U ∪ A₁) η₂).
    { apply typing_wf in H0; eauto. }
    eapply closure_if; auto.
    all: apply fundamental; auto.
  - apply closure_ref; auto.
  - apply closure_read; auto.
  - assert (names Γ ⊆ U ∪ A₁) by (etrans; first apply Γgood; apply union_subseteq_l).
    assert (heap_wf (U ∪ A₁) η₂).
    { apply IHty in sim; auto.
      destruct sim as [_ ty' _ _].
      apply typing_wf in ty'; auto. }
    eapply closure_write; auto.
    all: apply fundamental; auto.
  - assert (names Γ ⊆ U ∪ A₁) by (etrans; first apply Γgood; apply union_subseteq_l).
    assert (heap_wf (U ∪ A₁) η₂).
    { apply typing_wf in H0; eauto. }
    eapply closure_write; auto.
    all: apply fundamental; auto.
  - apply closure_post; auto.
  - eapply closure_wait; eauto.
  - apply closure_frame; auto.
    + by inversion_clear ηwf.
    + apply IHty; auto.
      inversion_clear ηwf; done.
  - eapply closure_weaken; last eapply IHty; eauto.
    eapply strengthen_heap_wf; first eauto.
    all:eauto.
  - eapply closure_proper; last apply IHty;eauto.
    + by rewrite eqU.
    + by rewrite eqU.
    + by rewrite eqU eqη₁.
Qed.
