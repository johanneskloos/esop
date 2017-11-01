From iris.proofmode Require Import tactics.
From esop Require Import closed_async closed_basic closed_memory closed_meta delayed types
     typetranslation corecalculus exprfacts stringfresh.
From iris.base_logic.lib Require Import invariants.
From stdpp Require Import gmap.

(** Reformulation of the closure lemmas in the form used by the typing relation. *)
Section FullClosure.
  Context `{allG Σ} (U: gset gname) (Γ: env) (good_env: names Γ ⊆ U).

  Lemma closure_true: delayed_simulation U Γ ∅ Ctrue Ctrue ∅ Bool ∅.
  Proof.
    split.
    2,3: constructor.
    { by rewrite right_id. }
    iApply (closed_strengthen ∅).
    5: iApply closed_true.
    1,2: constructor.
    2: apply empty_subseteq.
    rewrite map_subseteq_spec => [??]; rewrite lookup_empty => [?]; done.
  Qed.
  
  Lemma closure_false: delayed_simulation U Γ ∅ Cfalse Cfalse ∅ Bool ∅.
  Proof.
    split.
    2,3: constructor.
    { by rewrite right_id. }
    iApply (closed_strengthen ∅).
    5: iApply closed_false.
    1,2: constructor.
    - by rewrite map_subseteq_spec => [??]; rewrite lookup_empty => [?].
    - done.
  Qed.
  
  Lemma closure_unit: delayed_simulation U Γ ∅ Cunit Cunit ∅ Unit ∅.
  Proof.
    split.
    2,3: constructor.
    { by rewrite right_id. }
    iApply (closed_strengthen ∅).
    5: iApply closed_unit.
    1,2: constructor.
    - by rewrite map_subseteq_spec => [??]; rewrite lookup_empty => [?].
    - done.
  Qed.

  Lemma closure_var x τ (type_x: Γ !! x = Some τ):
    delayed_simulation U Γ ∅ x x ∅ τ ∅.
  Proof.
    split.
    2,3: by constructor.
    { by rewrite right_id. }
    iApply (closed_strengthen ∅).
    5: iApply closed_variable.
    1,2: constructor; apply lookup_insert.
    2: done.
    rewrite map_subseteq_spec => [x' τ'].
    rewrite lookup_insert_Some lookup_empty.
    intros [[<- <-]|[_ [=]]]; done.
  Qed.

  Lemma subst_empty e: subst ∅ e = e.
  Proof.
    induction e; rewrite /=; try congruence.
    - by rewrite lookup_empty.
    - f_equal.
      assert (∀ b, delete' b (∅: gmap string expr) = ∅) as red.
      { destruct b; first done.
        apply delete_empty. }
      rewrite !red IHe //.
  Qed.

  Lemma dom_insert' {A} b (x: A) m: dom (gset string) (insert' b x m) = {[?b]} ∪ dom _ m.
  Proof.
    apply leibniz_equiv.
    destruct b.
    - rewrite /= left_id //.
    - rewrite /= dom_insert //.
  Qed.

  Lemma type_var_string U' (Γ': env) x τ (val_x: Γ' !! x = Some τ) (η: hexpr) (wf: heap_wf U' η):
    typing U' Γ' x η ∅ τ η.
  Proof.
    rewrite -(left_id hemp hstar η).
    apply tyframe.
    1-3: apply disjoint_empty_l.
    2: by constructor.
    rewrite union_empty_r_L; done.
  Qed.

  Lemma names_env_insert Γ' x τ: names (<[x:=τ]> Γ') ⊆ names τ ∪ names Γ'.
  Proof.
    intro ξ.
    rewrite elem_of_union !elem_of_names_env.
    intros [x' [τ' [[[??]|[??]]%lookup_insert_Some inξ]]]; subst; eauto.
  Qed.
  
  Lemma good_after_bind {e η A τ η' y}:
    names η ⊆ U →
    typing U Γ e η A τ η' →
    names (<[y:=τ]>Γ) ∪ names η' ⊆ U ∪ A.
  Proof.
    intros subη [disj [subτ subη']]%typing_good_names; auto.
    pose proof (names_env_insert Γ y τ) as sub.
    clear -sub subη' subτ good_env.
    set_solver.
  Qed.
  
  Lemma closure_let (x: binder) η₁ η₂ η₃ τ₁ τ₂ A₁ A₂ e₁ e₂ e₁' e₂':
    heap_wf U η₁ →
    delayed_simulation U Γ η₁ e₁ e₁' A₁ τ₁ η₂ →
    delayed_simulation (U ∪ A₁) (insert' x τ₁ Γ) η₂ e₂ e₂' A₂ τ₂ η₃ →
    delayed_simulation U Γ η₁ (Let x e₁ e₂) (Let x e₁' e₂') (A₁ ∪ A₂) τ₂ η₃.
  Proof.
    intros wf [good₁ ty₁ ty₁' del₁] [good₂ ty₂ ty₂' del₂].
    assert (typing U Γ (Let x e₁ e₂) η₁ (A₁ ∪ A₂) τ₂ η₃) as ty_let.
    { econstructor; eauto. }
    assert (typing U Γ (Let x e₁' e₂') η₁ (A₁ ∪ A₂) τ₂ η₃) as ty_let'.
    { econstructor; eauto. }
    split.
    1-3: done.
    set (y := fresh (dom (gset string) Γ)).
    assert (∀ (e': expr) z, z ∈ dom (gset string) (insert' x τ₁ Γ) →
                            delete' x (<[y:=e']>∅) !! z = None).
    { intros *.
      rewrite dom_insert' elem_of_union elem_of_singleton' => [[<-|inz]].
      - rewrite /= lookup_delete //.
      - rewrite lookup_delete'_None lookup_insert_ne ?lookup_empty; first auto.
        intros <-.
        apply is_fresh in inz; done. }
    iApply (delayed_bind_strong y e₁ e₁'
                                [EAppR (Rec BAnon x e₂)]
                                [EAppR (Rec BAnon x e₂')]
                                Γ τ₁ τ₂ η₁ η₂ η₃ U A₁ A₂).
    1,2: intro; rewrite /= (subst_closed (dom _ (insert' x τ₁ Γ))) //.
    1,3: by eapply typing_closed.
    1,2: auto.
    1,2: repeat constructor; rewrite /= left_id -(dom_insert' x τ₁ Γ); by eapply typing_closed.
    1: by split.
    rewrite -(union_empty_l_L A₂).
    assert (∀ e, typing (U ∪ A₁) (insert' x τ₁ Γ) e η₂ A₂ τ₂ η₃ →
                 typing (U ∪ A₁ ∪ ∅) (insert' x τ₁ (<[y:=τ₁]>Γ)) e η₂ A₂ τ₂ η₃).
    { intro.
      apply typing_good_names in ty₁.
      2,3: clear -good₁; set_solver.
      destruct ty₁ as [disj₁ [subτ₁ subη₂]].
      assert (names (insert' x τ₁ Γ) ⊆ U ∪ A₁).
      { intro ξ; rewrite elem_of_names_env => [[x' [τ' [mt inξ]]]].
        rewrite lookup_insert' in mt * => [[[? ?]|[neq mt]]]; subst; first auto.
        rewrite elem_of_union; left.
        apply good₁, elem_of_union; left.
        rewrite elem_of_names_env; eauto. }
      apply typing_good_names in ty₂; auto.
      destruct ty₂ as [[??]%disjoint_union_r [??]].
      apply tyweaken.
      1,2,6: done.
      2: rewrite right_id; done.
      1: rewrite right_id; apply disjoint_union_l; split; auto.
      2: rewrite union_empty_r_L union_comm_L.
      2: eapply typing_wf; first done.
      2: by eapply typing_wf.
      apply map_subseteq_spec.
      intros x' τ'.
      rewrite !lookup_insert'.
      intros [case|[neq lookup]]; auto.
      right; split; trivial.
      rewrite lookup_insert_ne //.
      intros <-.
      apply (elem_of_dom_2 (D:=gset string)) in lookup.
      apply is_fresh in lookup; done. }
    split.
    2,3: eapply tylet; auto.
    2,3: apply type_var_string; first apply lookup_insert.
    2,3: by eapply typing_wf.
    { eapply good_after_bind; eauto.
      clear -good₁; set_solver. }
    destruct x.
    - iApply closed_let_anon; first apply lookup_insert.
      rewrite union_empty_l_L.
      iApply closed_strengthen.
      5: iApply del₂.
      1,2,4: done.
      apply map_subseteq_spec.
      intros x' τ' mt.
      rewrite lookup_insert_ne; first done.
      intros <-.
      apply (elem_of_dom_2 (D:=gset string)), is_fresh in mt; done.
    - iApply closed_let; first apply lookup_insert.
      rewrite union_empty_l_L.
      iApply closed_strengthen.
      5: iApply del₂.
      1,2,4: done.
      apply map_subseteq_spec.
      intros x' τ' mt.
      rewrite lookup_insert' in mt * => [[[eqx <-]|[neqx mt]]].
      + injection eqx as <-; apply lookup_insert.
      + rewrite lookup_insert_ne; last congruence.
        rewrite lookup_insert_ne; first done.
        intros <-.
        apply (elem_of_dom_2 (D:=gset string)), is_fresh in mt; done.
  Qed.

  Lemma ext_env_with_fresh (Γ': env) τ: Γ' ⊆ <[fresh (dom (gset string) Γ') := τ]>Γ'.
  Proof.
    apply insert_subseteq.
    rewrite -(not_elem_of_dom (D:=gset string)).
    apply is_fresh.
  Qed.
  
  Lemma closure_if η₁ η₂ η₃ τ A₁ A₂ e₁ e₁' e₂ e₂' e₃ e₃':
    heap_wf U η₁ →
    delayed_simulation U Γ η₁ e₁ e₁' A₁ tbool η₂ →
    delayed_simulation (U ∪ A₁) Γ η₂ e₂ e₂' A₂ τ η₃ →
    delayed_simulation (U ∪ A₁) Γ η₂ e₃ e₃' A₂ τ η₃ →
    delayed_simulation U Γ η₁ (If e₁ e₂ e₃) (If e₁' e₂' e₃') (A₁ ∪ A₂) τ η₃.
  Proof.
    intros wf [good₁ ty₁ ty₁' del₁] [good₂ ty₂ ty₂' del₂] [good₃ ty₃ ty₃' del₃].
    assert (names η₁ ⊆ U).
    { etrans; last done. apply union_subseteq_r. }
    destruct (typing_good_names _ _ _ _ _ _ _ ty₁) as [disj₁ [subτ₁ subη₂]].
    1,2: done.
    destruct (typing_good_names _ _ _ _ _ _ _ ty₂) as [disj₂ [subτ₂ subη₃]].
    { trans U; first done. apply union_subseteq_l. }
    { done. }
    split; first done.
    1,2: by econstructor.
    set (x:=fresh (dom (gset string) Γ)).
    iApply (delayed_bind x e₁ e₁' [CIf e₂ e₃] [CIf e₂' e₃'] Γ tbool τ η₁ η₂ η₃ U A₁ A₂).
    1,2: intro; rewrite /= !(subst_closed (dom _ Γ)) //.
    1,3,5,7: by eapply typing_closed.
    1,2,3,4: intros y iny; rewrite lookup_insert_ne ?lookup_empty //.
    1,2,3,4: intros <-; by apply is_fresh in iny.
    - by split.
    - split.
      + eapply good_after_bind; eauto.
      + cbn.
        rewrite -(union_empty_l_L A₂).
        apply tyif with (η₂ := η₂).
        { apply type_var_string; first apply lookup_insert. by eapply typing_wf. }
        all: rewrite union_empty_r_L.
        all: eapply (tyweaken (U ∪ A₁) Γ); try done.
        3,6: rewrite union_comm_L.
        3,4: eapply typing_wf; first done.
        3,4: by eapply typing_wf.
        2,4: apply ext_env_with_fresh.
        all: etrans; first done.
        all: apply union_subseteq_l.
      + cbn.
        rewrite -(union_empty_l_L A₂).
        apply tyif with (η₂ := η₂).
        { apply type_var_string; first apply lookup_insert. by eapply typing_wf. }
        all: rewrite union_empty_r_L.
        all: eapply (tyweaken (U ∪ A₁) Γ); try done.
        3,6: rewrite union_comm_L.
        3,4: eapply typing_wf; first done.
        3,4: by eapply typing_wf.
        2,4: apply ext_env_with_fresh.
        all: etrans; first done.
        all: apply union_subseteq_l.
      + iApply closed_if.
        * apply lookup_insert.
        * iApply closed_strengthen; last iApply del₂.
          all: try done.
          apply ext_env_with_fresh.
        * iApply closed_strengthen; last iApply del₃.
          all: try done.
          apply ext_env_with_fresh.
  Qed.

  Lemma strengthen_heap_wf Ξ η: heap_wf Ξ η → ∀ Ξ', Ξ' ⊆ Ξ → names η ⊆ Ξ' → heap_wf Ξ' η.
  Proof.
    induction 1; intros; constructor; auto.
    - apply IHheap_wf1; auto.
      etrans; last done.
      apply union_subseteq_l.
    - apply IHheap_wf2; auto.
      etrans; last done.
      apply union_subseteq_r.
    - by apply H1, elem_of_union, or_introl, elem_of_singleton.
    - etrans; last done.
      apply union_subseteq_r.
    - by apply H2, elem_of_union, or_introl, elem_of_singleton.
    - by intros ? ?%H1; apply disj.
    - apply IHheap_wf.
      + by apply union_mono.
      + cbn -[union] in H2.
        clear -H2.
        intros ξ' inξ'.
        rewrite elem_of_union.
        destruct (decide (ξ' ∈ A)) as [case|case]; auto.
        left; apply H2.
        rewrite elem_of_union elem_of_difference; auto.
  Qed.
  
      
  Lemma closure_ref e e' η₁ η₂ τ A ξ (ξ_fresh: ξ ∉ U ∪ A) (wf: heap_wf (U ∪ A ∪ {[ξ]}) (η₂ ⊗ ξ ↦ τ)):
    delayed_simulation U Γ η₁ e e' A τ η₂ →
    delayed_simulation U Γ η₁ (Alloc e) (Alloc e') (A ∪ {[ ξ ]}) (Ref(ξ)) (η₂ ⊗ ξ ↦ τ).
  Proof.
    intros [good tye tye' del].
    split.
    1: done.
    1,2: by constructor.
    set (x := fresh (dom (gset string) Γ)).
    iApply (delayed_bind x e e' [CAlloc] [CAlloc] Γ τ (Ref(ξ)) η₁ η₂ (η₂ ⊗ ξ ↦ τ)).
    1,2: done.
    1: by split.
    destruct (typing_good_names _ _ _ _ _ _ _ tye) as [disj [subτ subη₂]].
    1,2: clear -good; set_solver.
    assert (typing (U ∪ A) (<[x:=τ]>∅) (Alloc x) η₂ {[ξ]} (Ref(ξ)) (η₂ ⊗ ξ ↦ τ)).
    { rewrite -(union_empty_l_L {[ξ]}).
      constructor; first by rewrite union_empty_r.
      { by rewrite union_empty_r_L. }
      rewrite -(left_id hemp hstar η₂).
      apply tyframe.
      1-3: apply disjoint_empty_l.
      2: constructor; apply lookup_insert.
      inversion_clear wf as [|??? _ wf' _| |].
      rewrite union_empty_r_L.
      eapply strengthen_heap_wf; try done.
      apply union_subseteq_l. }
    assert (typing (U ∪ A) (<[x:=τ]>Γ) (Alloc x) η₂ {[ξ]} (Ref(ξ)) (η₂ ⊗ ξ ↦ τ)).
    { eapply tyweaken; last done.
      2,4,6: done.
      2: by rewrite disjoint_singleton_r.
      - intros ξ'.
        rewrite elem_of_names_env => [[x' [τ' [mt inξ']]]].
        rewrite lookup_insert_Some in mt * => [[[??]|[? contra]]].
        + subst; auto.
        + by apply lookup_empty_Some in contra.
      - apply insert_mono, map_subseteq_spec.
        intros ?? []%lookup_empty_Some.
      - by rewrite union_comm_L. }
    split.
    2,3: done.
    { eapply good_after_bind; eauto.
      etrans; last done.
      apply union_subseteq_r. }
    rewrite comm -{1}(left_id hemp hstar η₂).
    iApply closed_frame.
    { cbn; apply disjoint_singleton_l.
      contradict ξ_fresh.
      apply subη₂, res_names_sub_names, ξ_fresh. }
    { apply disjoint_empty_l. }
    { apply disjoint_singleton_r.
      contradict ξ_fresh.
      apply subη₂, ξ_fresh. }
    iApply (closed_strengthen (U ∪ A) (<[x:=τ]>∅)).
    4: done.
    1,2: rewrite -(left_id hemp hstar (hpt ξ τ)).
    1,2: rewrite -(union_empty_l_L {[ξ]}).
    1,2: apply tyref.
    1,4: by rewrite union_empty_r_L.
    2,4: apply type_var_string; last constructor.
    2,3: apply lookup_insert.
    1,2: rewrite left_id.
    1,2: constructor.
    1,3: by apply elem_of_union_r, elem_of_singleton.
    1,2: rewrite right_id.
    1,2: etrans; first done.
    1,2: apply union_subseteq_l.
    { apply insert_mono, map_subseteq_spec.
      intros ?? []%lookup_empty_Some. }
    iApply closed_alloc.
    contradict ξ_fresh; auto.
  Qed.

  Lemma closure_read e e' η₁ η₂ ξ τ A:
    heap_wf U η₁ →
    delayed_simulation U Γ η₁ e e' A (Ref(ξ)) (η₂ ⊗ ξ ↦ τ) →
    delayed_simulation U Γ η₁ (Read e) (Read e') A τ (η₂ ⊗ ξ ↦ τ).
  Proof.
    intros wf [good ty ty' del].
    split; first done.
    1,2: by constructor.
    set (x := fresh (dom (gset string) Γ)).
    rewrite -(union_empty_r_L A).
    iApply (delayed_bind x e e' [CRead] [CRead] Γ (Ref(ξ)) τ).
    1,2: done.
    { by split. }
    split.
    { eapply good_after_bind; last done.
      etrans; last apply good.
      apply union_subseteq_r. }
    1,2: constructor; apply type_var_string; first apply lookup_insert.
    1,2: by eapply typing_wf.
    iApply (closed_strengthen (U ∪ A) (<[x:=tref ξ]>∅)).
    4: done.
    1,2: constructor; apply type_var_string; first apply lookup_insert.
    1,2: by eapply typing_wf.
    { apply insert_mono, map_subseteq_spec.
      intros ?? []%lookup_empty_Some. }
    rewrite comm.
    apply typing_wf in ty; auto.
    inversion_clear ty.
    iApply closed_frame.
    1,2: done.
    { apply disjoint_empty_r. }
    iApply closed_read.
  Qed.

  Lemma closure_write e₁ e₁' e₂ e₂' η₁ η₂ η₃ ξ τ A₁ A₂:
    heap_wf U η₁ →
    delayed_simulation U Γ η₁ e₁ e₁' A₁ (Ref(ξ)) η₂ →
    delayed_simulation (U ∪ A₁) Γ η₂ e₂ e₂' A₂ τ (η₃ ⊗ ξ ↦ τ) →
    delayed_simulation U Γ η₁ (Write e₁ e₂) (Write e₁' e₂') (A₁ ∪ A₂) tunit (η₃ ⊗ ξ ↦ τ).
  Proof.
    intros wf [good₁ ty₁ ty₁' del₁] [good₂ ty₂ ty₂' del₂].
    split; first done.
    1,2: by econstructor.
    set (x := fresh (dom (gset string) Γ)).
    iApply (delayed_bind x e₁ e₁' [CWriteL e₂] [CWriteL e₂']).
    1,2: intro; cbn; do 2 f_equal; apply (subst_closed (dom _ Γ)).
    1,3: by eapply typing_closed.
    1,2: intros y iny; rewrite lookup_insert_None lookup_empty; split; auto.
    1,2: by intros <-; apply is_fresh in iny.
    1: by split.
    cbn.
    apply typing_good_names in ty₁'; auto.
    2: etrans; last done; apply union_subseteq_r.
    destruct ty₁' as [disj₁ [inξ subη₂]].
    destruct (typing_good_names _ _ _ _ _ _ _ ty₂) as [[disj₂ disj₂']%disjoint_union_r [_ subη₃]].
    { etrans; first done. apply union_subseteq_l. }
    { done. }
    split.
    { apply union_least; auto.
      etrans; first apply names_env_insert.
      apply union_least; auto.
      etrans; first done.
      apply union_subseteq_l. }
    1-3: rewrite -(union_empty_l_L A₂).
    1,2: econstructor.
    1,3: apply type_var_string; first apply lookup_insert.
    1,2: by eapply typing_wf.
    1,2: rewrite union_empty_r_L.
    1,2: eapply tyweaken; last done.
    1,8: etrans; first done; apply union_subseteq_l.
    1,3,5,7,9,11: done.
    1,4: apply disjoint_union_l; auto.
    1,3: apply insert_subseteq, (not_elem_of_dom (D:=gset string)), is_fresh.
    1,2: rewrite union_comm_L; eapply typing_wf; first done.
    1,2: by eapply typing_wf.
    rewrite union_comm_L.
    set (y := fresh (dom (gset string) (<[x:=tref ξ]>Γ))).
    assert (y ≠ x).
    { intros eqxy; subst y.
      pose proof (is_fresh (dom (gset string) (<[x:=tref ξ]>Γ))) as contra.
      rewrite eqxy dom_insert not_elem_of_union not_elem_of_singleton in contra *.
      tauto. }
    iApply (delayed_bind_strong y e₂ e₂' [EWriteR x] [EWriteR x] (<[x:=tref ξ]>Γ) τ tunit
                                η₂ (η₃ ⊗ ξ ↦ τ) (η₃ ⊗ ξ ↦ τ) (U ∪ A₁) A₂ ∅).
    1,2: intro; rewrite /= lookup_insert_ne //.
    1,2: repeat constructor.
    1,2: rewrite dom_insert elem_of_union elem_of_singleton; auto.
    { split.
      2,3: apply tyweaken with (U := U ∪ A₁) (Γ := Γ) (A:=A₂); try done.
      3,7: apply disjoint_union_l; auto.
      2,5: etrans; first done; apply union_subseteq_l.
      2,4: apply insert_subseteq, (not_elem_of_dom (D:=gset string)), is_fresh.
      2,3: rewrite union_comm_L.
      2,3: eapply typing_wf; try done.
      2,3: by eapply typing_wf.
      { apply union_least; auto.
        etrans; first apply names_env_insert.
        apply union_least; auto.
        etrans; first done.
        apply union_subseteq_l. }
      iApply closed_strengthen; last iApply del₂.
      4: done.
      3: apply insert_subseteq, (not_elem_of_dom (D:=gset string)), is_fresh.
      1,2: done. }
    cbn.
    apply typing_wf in ty₂'; last by eapply typing_wf.
    inversion_clear ty₂' as [|??? disjξ wfη₃ wfξ| |].
    assert (typing (U ∪ A₁ ∪ A₂) (<[y:=τ]>(<[x:=tref ξ]>∅)) (Write x y) (ξ ↦ τ) (∅ ∪ ∅) Unit (ξ ↦ τ))
      as ty.
    { rewrite -(left_id hemp hstar (hpt ξ τ)).
      eapply tywrite.
      - apply type_var_string.
        + rewrite lookup_insert_ne // lookup_insert //.
        + by rewrite left_id.
      - apply type_var_string.
        + apply lookup_insert.
        + by rewrite left_id union_empty_r_L. }
    assert (typing (U ∪ A₁ ∪ A₂) (<[y:=τ]>(<[x:=tref ξ]>Γ)) (Write x y) (ξ ↦ τ) (∅ ∪ ∅) Unit (ξ ↦ τ)).
    { eapply tyweaken; last done.
      all: rewrite ?union_empty_l_L; auto.
      4: apply insert_mono, insert_mono, map_subseteq_spec.
      4: intros ?? []%lookup_empty_Some.
      3: apply disjoint_empty_r.
      2: by eapply heap_wf_names.
      etrans; first apply names_env_insert.
      apply union_least; first by inversion_clear wfξ.
      etrans; first apply names_env_insert.
      etrans; last apply union_subseteq_l.
      apply union_least; auto.
      apply empty_subseteq. }
    rewrite (comm hstar η₃).
    split.
    2,3: rewrite -(union_empty_l_L ∅).
    2,3: constructor; auto.
    2,4: rewrite left_id; apply disjoint_empty_l.
    2,3: by rewrite !union_empty_r_L.
    { apply union_least.
      - etrans; first apply (names_env_insert (<[x:=tref ξ]>Γ) y τ).
        apply union_least.
        { apply typing_good_names in ty₂; try tauto.
          etrans; first done. apply union_subseteq_l. }
        etrans; first apply names_env_insert.
        etrans; last apply union_subseteq_l.
        apply union_least; auto.
        etrans; first done.
        apply union_subseteq_l.
      - cbn -[union]; apply union_least.
        + inversion_clear wfξ.
          apply union_least; auto.
          apply elem_of_subseteq_singleton; done.
        + by apply heap_wf_names. }
    iApply closed_frame; auto.
    { apply disjoint_empty_r. }
    rewrite union_empty_l_L insert_commute // in ty *.
    iApply (closed_strengthen (U ∪ A₁ ∪ A₂)).
    1,2,4: done.
    2: iApply closed_write; auto.
    rewrite insert_commute //.
    apply insert_mono, insert_mono, map_subseteq_spec.
    intros ?? []%lookup_empty_Some.
  Qed.

  Lemma closure_post e e' η₁ η₂ τ A ξ (ξ_fresh: ξ ∉ U ∪ A) (wf: heap_wf (U ∪ {[ξ]}) (Wait(ξ,A) η₂)):
    delayed_simulation U Γ η₁ e e' A τ η₂ →
    delayed_simulation U Γ η₁ (Post e) (Post e') {[ξ]} (Promise(ξ,A) τ) (Wait(ξ,A) η₂).
  Proof.
    intros [good tye tye' del].
    split; auto.
    1,2: by constructor.
    rewrite not_elem_of_union in ξ_fresh * => [[notinU notinA]].
    apply typing_good_names in tye; auto.
    2: etrans; last done; apply union_subseteq_r.
    destruct tye as [disj [subτ subη]].
    iApply closed_post; auto.
    4: iApply del.
    - contradict notinU.
      apply good, elem_of_union_r, notinU.
    - by intros [?|?]%subτ%elem_of_union.
    - by intros [?|?]%subη%elem_of_union.
  Qed.

  Lemma closure_wait e e' (η₁ η₂ η₃: hexpr) (τ: type) ξ A₁ A₂
        (disjA: A₁ ⊥ A₂) (disjU: U ⊥ A₂) (wf: heap_wf (U ∪ A₁ ∪ A₂) (η₂ ⊗ η₃))
        (ξ_τ: ξ ∉ names τ) (ξ_η₃: ξ ∉ names η₃):
    heap_wf U η₁ →
    delayed_simulation U Γ η₁ e e' A₁ (ttask ξ A₂ τ) (η₂ ⊗ hwait ξ A₂ η₃) →
    delayed_simulation U Γ η₁ (Wait e) (Wait e') (A₁ ∪ A₂) τ (η₂ ⊗ η₃).
  Proof.
    intros wfη₁ [good tye tye' del].
    split; first done.
    1,2: econstructor; try done.
    pose proof (typing_wf _ _ _ _ _ _ _ tye' wfη₁) as wf'.
    set (x := fresh (dom (gset string) Γ)).
    iApply (delayed_bind x e e' [CWait] [CWait]).
    1,2: done.
    { by split. }
    split.
    2,3: rewrite -(union_empty_l_L A₂).
    2,3: eapply tywait.
    all: rewrite ?union_empty_r_L ?union_empty_l_L.
    2,4,5,7,9,10: done.
    3,5: apply type_var_string; first apply lookup_insert.
    3,4: done.
    2,3: apply disjoint_union_r; auto.
    { apply union_least.
      - etrans; first apply names_env_insert.
        apply union_least.
        2: by etrans; last apply union_subseteq_l.
        apply typing_good_names in tye; try tauto.
        by etrans; first apply union_subseteq_r.
      - apply typing_good_names in tye; try tauto.
          by etrans; first apply union_subseteq_r. }
    rewrite !(comm hstar η₂).
    iApply closed_frame.
    { by inversion_clear wf. }
    { apply typing_wf in tye; auto.
      inversion_clear tye; done. }
    { apply typing_good_names in tye; auto.
      2: etrans; last apply good; apply union_subseteq_r.
      destruct tye as [_ [_ sub]].
      intros ξ' inξ'.
      enough (ξ' ∈ U ∪ A₁) as [?|?]%elem_of_union.
      { by apply disjU. }
      { by apply disjA. }
      apply sub, elem_of_union_l, inξ'. }                
    assert (heap_wf (U ∪ A₁) (Wait(ξ,A₂) η₃)).
    { apply typing_wf in tye; auto.
      inversion_clear tye; done. }
    iApply (closed_strengthen (U ∪ A₁) (<[x:=ttask ξ A₂ τ]>∅)).
    4: done.
    1,2: rewrite -(union_empty_l_L A₂).
    1,2: rewrite -{2}(left_id hemp hstar η₃).
    1,2: eapply tywait; auto; try done.
    1,4: rewrite union_empty_r_L !left_id.
    1,2: by inversion_clear wf.
    1,3: apply disjoint_union_r; auto.
    1,2: rewrite union_empty_l_L !left_id.
    1,2: by apply type_var_string; first apply lookup_insert.
    { apply insert_mono, map_subseteq_spec.
      intros ?? []%lookup_empty_Some. }
    by iApply closed_wait.
  Qed.

  Lemma closure_frame e e' (η₁ η₂: hexpr) (τ: type) A (ηf: hexpr)
        (disj₁: res_names η₁ ⊥ res_names ηf)
        (disj₂: res_names η₂ ⊥ res_names ηf)
        (disjA: A ⊥ names ηf)
        (wf_post: heap_wf (U ∪ A) ηf):
    heap_wf U ηf →
    delayed_simulation U Γ η₁ e e' A τ η₂ →
    delayed_simulation U Γ (η₁ ⊗ ηf) e e' A τ (η₂ ⊗ ηf).
  Proof.
    intros wf_pre [good tye tye' del].
    split.
    2,3: by apply tyframe.
    { rewrite union_assoc.
      apply union_least; auto.
      apply heap_wf_names in wf_pre; done. }
    iApply closed_frame; auto.
    iApply del.
  Qed.

  Lemma closure_weaken e e' (η₁ η₂: hexpr) A τ U' Γ' A'
        (namesΓ: names Γ' ⊆ U') (namesη₁: names η₁ ⊆ U')
        (disj: U ⊥ A) (subU: U' ⊆ U) (subΓ: Γ' ⊆ Γ) (subA: A' ⊆ A)
        (wf: heap_wf (A ∪ U) η₂):
    delayed_simulation U' Γ' η₁ e e' A' τ η₂ →
    delayed_simulation U Γ η₁ e e' A τ η₂.
  Proof.
    intros [good tye tye' del].
    split.
    { apply union_least; auto.
      etrans; done. }
    1,2: eapply (tyweaken U' Γ'); eassumption.
    iApply closed_strengthen.
    5: iApply del.
    all: done.
  Qed.

  Lemma closure_proper (U': lnamesC) (η₁ η₁': hexpr) e e' (A A': lnames) τ (η₂ η₂': hexpr)
        (eqU: (U: lnamesC) ≡ U') (eqη₁: η₁ ≡ η₁') (eqA: A ≡ A') (eqη₂: η₂ ≡ η₂'):
    delayed_simulation U Γ η₁ e e' A τ η₂ →
    delayed_simulation U' Γ η₁' e e' A' τ η₂'.
  Proof.
    intros [good tye tye' del].
    split.
    2,3: by eapply typroper.
    { by rewrite -eqU -eqη₁. }
    rewrite -eqη₁ -eqη₂.
    apply leibniz_equiv in eqA.
    apply leibniz_equiv in eqU.
    subst; done.
  Qed.
End FullClosure.