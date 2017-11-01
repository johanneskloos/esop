From mathcomp Require Import ssreflect.
From stdpp Require Import gmap option strings.
From esop Require Import corecalculus.

Definition subst_ectx_item σ i :=
  match i with
  | EAppL e => EAppL (subst σ e)
  | EAppR e => EAppR (subst σ e)
  | EIfL e e' => EIfL (subst σ e) (subst σ e')
  | EIfM e e' => EIfM (subst σ e) (subst σ e')
  | EIfR e e' => EIfR (subst σ e) (subst σ e')
  | EAlloc => EAlloc
  | ERead => ERead
  | EWriteL e => EWriteL (subst σ e)
  | EWriteR e => EWriteR (subst σ e)
  | EWait => EWait
  | EPost => EPost
  | ERec f x => ERec f x
  end.
Definition subst_ectx σ (K: list ectx_item) := subst_ectx_item σ <$> K.                         

Definition of_ectx_item i :=
  match i return option ctx_item with
  | EAppL e => Some (CAppL e)
  | EAppR e => CAppR <$> to_val e
  | EIfL e e' => Some (CIf e e')
  | EIfM _ _ => None
  | EIfR _ _ => None
  | EAlloc => Some CAlloc
  | ERead => Some CRead
  | EWriteL e => Some (CWriteL e)
  | EWriteR e => CWriteR <$> to_val e
  | EWait => Some CWait
  | EPost => None
  | ERec f x => None
  end.
Fixpoint of_ectx K :=
  match K return option (list ctx_item) with
  | [] => Some []
  | i::K => of_ectx_item i ≫= λ i', (i' ::) <$> of_ectx K
  end.

Variant reduced (X: gset string): expr → Prop :=
| red_const (c: const): reduced X c
| red_lambda (f x: binder) (e: expr) (eclosed: Closed ({[?f]} ∪ {[?x]} ∪ X) e):
    reduced X (Rec f x e)
| red_var (x: string) (inx: x ∈ X): reduced X x.

Lemma reduced_to_val e: reduced ∅ e → is_Some (to_val e).
Proof.
  destruct 1; eauto.
  - rewrite right_id in eclosed * => [eclosed].
    rewrite /= decide_left; eauto.
  - set_solver.
Qed.
Lemma reduced_of_val v: reduced ∅ (of_val v).
Proof. destruct v; constructor; rewrite ?right_id //. Qed.

Variant reduced_ectx_item (X: gset string): ectx_item → Prop :=
| REIAppL e: reduced_ectx_item X (EAppL e)
| REIAppR e (red: reduced X e): reduced_ectx_item X (EAppR e)
| REIAppIf e e': reduced_ectx_item X (EIfL e e')
| REIAlloc: reduced_ectx_item X EAlloc
| REIRead: reduced_ectx_item X ERead
| REIWriteL e: reduced_ectx_item X (EWriteL e)
| REIWriteR e (red: reduced X e): reduced_ectx_item X (EWriteR e)
| REIWait: reduced_ectx_item X EWait.
                               
Lemma of_ectx_item_reduced i: reduced_ectx_item ∅ i → is_Some (of_ectx_item i).
Proof.
  destruct 1; cbn; eauto.
  all: apply reduced_to_val in red; destruct red as [? ->]; eauto.
Qed.

Definition to_ectx_item i :=
  match i return ectx_item with
  | CAppL e => EAppL e
  | CAppR v => EAppR (of_val v)
  | CIf e e' => EIfL e e'
  | CAlloc => EAlloc
  | CRead => ERead
  | CWriteL e => EWriteL e
  | CWriteR v => EWriteR (of_val v)
  | CWait => EWait
  end.
Lemma of_to_ectx_item i: of_ectx_item (to_ectx_item i) = Some i.
Proof.
  destruct i; try done.
  all: by rewrite /= to_of_val.
Qed.
Lemma to_ectx_item_reduced i: reduced_ectx_item ∅ (to_ectx_item i).
Proof.
  destruct i; rewrite /=; constructor.
  all: apply reduced_of_val.
Qed.
Lemma to_of_ectx_item i i': of_ectx_item i = Some i' → to_ectx_item i' = i.
Proof.
  destruct i; simplify_eq 1.
  all: try by intros <-.
  all: rewrite fmap_Some => [[v [eqv ->]]].
  all: by rewrite /= (of_to_val e v).
Qed.

Definition to_ectx (K: list _): list _ := to_ectx_item <$> K.
Definition reduced_ectx X := Forall (reduced_ectx_item X).

Lemma subst_fill_ectx_item σ i e X: reduced_ectx_item X i →
  subst σ (fill_ectx_item e i) =
  fill_ectx_item (subst σ e) (subst_ectx_item σ i).
Proof. by destruct 1. Qed.

Lemma subst_fill_ectx X σ K e: reduced_ectx X K →
  subst σ (fill_ectx e K) =
  fill_ectx (subst σ e) (subst_ectx σ K).
Proof.
  intro red; revert e.
  induction red; intro; rewrite /= //.
  rewrite IHred (subst_fill_ectx_item σ _ _ X); done.
Qed.

Lemma fill_of_ectx_item i i' (eqi: of_ectx_item i = Some i') e:
  fill_ectx_item e i = fill_ctx_item e i'.
Proof.
  destruct i; simplify_eq eqi; intro eqi'; subst; try done.
  all: rewrite fmap_Some in eqi' * => [[v [eqv ->]]].
  all: rewrite /= (of_to_val _ _ eqv) //.
Qed.

Lemma fill_of_ectx K K' (eqi: of_ectx K = Some K') e:
  fill_ectx e K = fill_ctx e K'.
Proof.
  revert e K' eqi.
  induction K as [|i K IH]; rewrite /= =>[e K' eqK'].
  { by injection eqK' as <-. }
  rewrite bind_Some in eqK' * => [[i' [eqi eqK']]].
  rewrite fmap_Some in eqK' * => [[K'' [eqK ->]]].
  rewrite /= (IH _ _ eqK) (fill_of_ectx_item _ _ eqi) //.
Qed.

Lemma reduced_ectx_of_ectx K: reduced_ectx ∅ K → is_Some (of_ectx K).
Proof.
  induction 1; cbn; eauto.
  destruct (of_ectx_item_reduced _ H) as [i' ->].
  destruct IHForall as [K' ->].
  eauto.
Qed.

Lemma reduced_closed X X' e: reduced X e → Closed X' e → reduced X' e.
Proof. destruct 1; inversion_clear 1; by constructor. Qed.

Lemma fmap_delete' `(f: A → B) b m: delete' b (f <$> m) = f <$> (delete' b m).
Proof.
  destruct b; first done.
  rewrite /= fmap_delete //.
Qed.

Lemma dom_delete' {A} b (m: gmap string A):
  dom (gset string) (delete' b m) = (dom _ m) ∖ {[? b ]}.
Proof.
  destruct b; simpl.
  - set_solver.
  - apply leibniz_equiv.
    rewrite dom_delete //.
Qed.

Lemma subst_closed' X X' σ e: map_Forall (λ k e', k ∈ X → Closed X' e') σ →
                              X ⊆ X' ∪ dom _ σ →
                              Closed X e → Closed X' (subst σ e).
Proof.
  intros good_subst bound closed.
  revert X' σ good_subst bound.
  induction closed; rewrite /= => [X' σ good_subst bound]; try constructor; auto.
  - destruct (σ !! x) eqn:inx.
    + apply (good_subst x e); auto.
    + constructor.
      rewrite -(not_elem_of_dom (D:=gset string)) in inx * => [notindom].
      set_solver.
  - apply IHclosed.
    + intros x' e'.
      rewrite !lookup_delete' !elem_of_union !elem_of_singleton'.
      intros [neqf [neqx mt]] [[case|case]|inx'].
      1,2: contradiction.
      apply good_subst in mt.
      eapply closed_mono.
      2: done.
      2: eauto.
      clear; set_solver.
    + intro y.
      rewrite !elem_of_union !dom_delete' !elem_of_difference !elem_of_singleton'.
      specialize (bound y); rewrite elem_of_union in bound *.
      intuition.
      destruct (decide (BNamed y = f)); auto.
      destruct (decide (BNamed y = x)); auto.
Qed.

Lemma reduced_subst_val σ e: reduced (dom _ σ) e → reduced ∅ (subst (of_val <$> σ) e).
Proof.
  intro red.
  destruct red; rewrite /=.
  - constructor.
  - constructor.
    rewrite !fmap_delete'.
    apply (subst_closed' ({[?f]} ∪ {[?x]} ∪ dom _ σ)); auto.
    + intros x' e'.
      rewrite lookup_fmap fmap_Some => [[v [lookup ->]]].
      rewrite !lookup_delete' in lookup * => [[neqf [neqx lookup]] _].
      eapply (closed_mono ∅).
      * clear; set_solver.
      * done.
      * apply val_closed.
    + clear; rewrite dom_fmap !dom_delete'.
      intro y.
      rewrite !elem_of_union !elem_of_difference !elem_of_empty.
      destruct (decide (y ∈ {[?f]})); auto.
      destruct (decide (y ∈ {[?x]})); auto.
      tauto.
  - rewrite lookup_fmap.
    rewrite elem_of_dom in inx * => [[v ->]].
    apply reduced_of_val.
Qed.

Lemma reduced_subst_ectx_item_val σ i:
  reduced_ectx_item (dom _ σ) i → reduced_ectx_item ∅ (subst_ectx_item (of_val <$> σ) i).
Proof. destruct 1; cbn; constructor; auto using reduced_subst_val. Qed.
Lemma reduced_subst_ectx_val σ K:
  reduced_ectx (dom _ σ) K → reduced_ectx ∅ (subst_ectx (of_val <$> σ) K).
Proof. induction 1; constructor; auto using reduced_subst_ectx_item_val. Qed.

Lemma of_to_ectx K: of_ectx (to_ectx K) = Some K.
Proof.
  induction K as [|i K IH]; first done.
  rewrite /= of_to_ectx_item IH //.
Qed.
