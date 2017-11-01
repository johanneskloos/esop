(** DWFM soundness proofs - The core calculus. *)
From stdpp Require Import strings gmap.
From mathcomp Require Import ssreflect.

(** The core language. Difference to ESOP submission: recursive functions added. *)
Definition loc := positive.
Definition tid := positive.
Variant const := Ctrue | Cfalse | Cunit | Cloc (l: loc) | Ctid (t: tid).
Variant binder := BAnon | BNamed (x: string).
Inductive expr :=
| Const (c: const)
| Var (x: string)
| Rec (f x: binder) (e: expr)
| App (e e': expr)
| If (e e' e'': expr)
| Alloc (e: expr)
| Read (e: expr)
| Write (e e': expr)
| Post (e: expr)
| Wait (e: expr).
Coercion Const: const >-> expr.
Coercion Var: string >-> expr.
Definition singleton' b: gset string := match b with BNamed x => {[x]} | BAnon => ∅ end.
Notation "{[? b ]}" := (singleton' b).
Inductive Closed: gset string → expr → Prop :=
| const_closed X c: Closed X (Const c)
| var_closed X x: x ∈ X → Closed X (Var x)
| rec_closed X f x e: Closed ({[? f]} ∪ {[? x ]} ∪ X) e → Closed X (Rec f x e)
| app_closed X e₁ e₂: Closed X e₁ → Closed X e₂ → Closed X (App e₁ e₂)
| if_closed X e₁ e₂ e₃: Closed X e₁ → Closed X e₂ → Closed X e₃ → Closed X (If e₁ e₂ e₃)
| alloc_closed X e₁: Closed X e₁ → Closed X (Alloc e₁)
| read_closed X e₁: Closed X e₁ → Closed X (Read e₁)
| write_closed X e₁ e₂: Closed X e₁ → Closed X e₂ → Closed X (Write e₁ e₂)
| post_closed X e₁: Closed X e₁ → Closed X (Post e₁)
| wait_closed X e₁: Closed X e₁ → Closed X (Wait e₁).
Instance expr_eq_dec: EqDecision expr.
Proof. cbv -[not]. repeat decide equality. Qed.

Instance: ∀ X e, ProofIrrel (Closed X e).
Proof.
  enough (∀ X X' e e' (eqX: X = X') (eqe: e = e') (H: Closed X e) (H': Closed X' e'),
             H = eq_rect_r (Closed X) (eq_rect_r (λ X, Closed X e') H' eqX) eqe)
    as irr.
  { intros; red; apply (irr X X e e eq_refl eq_refl). }
  fix IH 7.
  intros.
  destruct H, H'; try discriminate.
  all: subst; injection eqe; subst; repeat intros <-.
  all: try (pattern eqe; apply (Eqdep_dec.K_dec_type expr_eq_dec); cbn; f_equal).
  all: try apply (IH _ _ _ _ eq_refl eq_refl).
  Guarded.
  apply eq_pi, _.
Qed.
Instance: ∀ X e, Decision (Closed X e).
Proof.
  fix IH 2.
  destruct e; cbn.
  6,7,9,10: destruct (IH X e); last by right; inversion_clear 1.
  4,5,10: destruct (IH X e1); last by right; inversion_clear 1.
  4,5,6: destruct (IH X e2); last by right; inversion_clear 1.
  5: destruct (IH X e3); last by right; inversion_clear 1.
  2: destruct (decide (x ∈ X)); last by right; inversion_clear 1.
  3: destruct (IH ({[? f]} ∪ {[? x ]} ∪ X) e); last by right; inversion_clear 1.
  all: by left; constructor.
Defined.

Variant val :=
| VConst (c: const)
| VRec (f x: binder) (e: expr) {e_closed: Closed ({[? f]} ∪ {[? x ]}) e}.
Coercion VConst: const >-> val.
                                                               
Variant ctx_item :=
| CAppL (e': expr)
| CAppR (v: val)
| CIf (e' e'': expr)
| CAlloc
| CRead
| CWriteL (e': expr)
| CWriteR (v: val)
| CWait.
Variant ectx_item :=
| ERec (f x: binder)
| EAppL (e': expr)
| EAppR (e: expr)
| EIfL (e' e'': expr)
| EIfM (e e'': expr)
| EIfR (e e': expr)
| EAlloc
| ERead
| EWriteL (e': expr)
| EWriteR (e: expr)
| EPost
| EWait.

Definition of_val v :=
  match v with
  | VConst c => Const c
  | VRec f x e _ => Rec f x e
  end.
Definition to_val e :=
  match e with
  | Const c => Some (VConst c)
  | Rec f x e => match decide (Closed ({[? f]} ∪ {[? x]}) e) with
                 | left H => Some (@VRec f x e H)
                 | right _ => None
                 end
  | _ => None
  end.

Definition fill_ctx_item e c :=
  match c with
  | CAppL e' => App e e'
  | CAppR v => App (of_val v) e
  | CIf e' e'' => If e e' e''
  | CAlloc => Alloc e
  | CRead => Read e
  | CWriteL e' => Write e e'
  | CWriteR v => Write (of_val v) e
  | CWait => Wait e
  end.
Definition fill_ectx_item e c :=
  match c with
  | ERec f x => Rec f x e
  | EAppL e' => App e e'
  | EAppR e' => App e' e
  | EIfL e' e'' => If e e' e''
  | EIfM e' e'' => If e' e e''
  | EIfR e' e'' => If e' e'' e
  | EAlloc => Alloc e
  | ERead => Read e
  | EWriteL e' => Write e e'
  | EWriteR e' => Write e' e
  | EPost => Post e
  | EWait => Wait e
  end.
Definition fill_ctx := foldl fill_ctx_item.
Definition fill_ectx := foldl fill_ectx_item.

Definition delete' {A} b (m: gmap string A) :=
  match b with BAnon => m | BNamed x => delete x m end.

Fixpoint subst σ e :=
  let s := subst σ in
  match e with
  | Const l => Const l
  | Var x => match σ !! x with Some e => e | None => Var x end
  | Rec f x e => Rec f x (subst (delete' f (delete' x σ)) e)
  | App e e' => App (s e) (s e')
  | Alloc e => Alloc (s e)
  | Read e => Read (s e)
  | Write e e' => Write (s e) (s e')
  | If e e' e'' => If (s e) (s e') (s e'')
  | Post e => Post (s e)
  | Wait e => Wait (s e)
  end.
Definition subst' b e e' :=
  match b with BAnon => e' | BNamed x => subst (<[x:=e]>∅) e' end.

Definition subst_ctx_item σ i :=
  match i with
  | CAppL e' => CAppL (subst σ e')
  | CAppR v => CAppR v
  | CIf e' e'' => CIf (subst σ e') (subst σ e'')
  | CAlloc => CAlloc
  | CRead => CRead
  | CWriteL e' => CWriteL (subst σ e')
  | CWriteR v => CWriteR v
  | CWait => CWait
  end.
Definition subst_ctx σ (K: list ctx_item) := subst_ctx_item σ <$> K.

Local Opaque union.
Lemma elem_of_singleton' b x: x ∈ {[? b ]} ↔ BNamed x = b.
Proof.
  destruct b; rewrite /= ?elem_of_singleton ?elem_of_empty;
    intuition congruence.
Qed.
Lemma lookup_delete' {A} b (v: A) m x: delete' b m !! x = Some v ↔ BNamed x ≠ b ∧ m !! x = Some v.
Proof with try intuition congruence.
  destruct b as [|y]; rewrite /=...
  destruct (decide (x=y)) as [<-|neq].
  - rewrite lookup_delete...
  - rewrite lookup_delete_ne...
Qed.
Lemma lookup_delete'_None {A} b (m: gmap string A) x:
  delete' b m !! x = None ↔ BNamed x = b ∨ m!!x = None.
Proof.
  destruct b as [|y]; cbn.
  - intuition discriminate.
  - destruct (decide (x=y)) as [<-|neq].
    + rewrite lookup_delete; tauto.
    + rewrite lookup_delete_ne; intuition congruence.
Qed.

Instance: EqDecision binder.
Proof. solve_decision. Qed.

Lemma lookup_delete'_cases {A} b x (m: gmap string A):
  delete' b m !! x = if bool_decide (BNamed x ≠ b) then m!!x else None.
Proof.
  destruct (bool_decide_reflect (BNamed x ≠ b)) as [case|case].
  - apply option_eq; intro v.
    rewrite lookup_delete'; tauto.
  - apply lookup_delete'_None.
    left; by apply dec_stable.
Qed.

Lemma subst_closed X e: Closed X e → ∀ σ (disj: ∀ x, x ∈ X → σ !! x = None), subst σ e = e.
Proof.
  induction 1; intros.
  all: rewrite /= ?IHClosed ?IHClosed1 ?IHClosed2 ?IHClosed3; auto.
  - rewrite disj //.
  - intros y.
    rewrite !elem_of_union !elem_of_singleton' !lookup_delete'_None.
    intuition.
Qed.

Lemma subst_closed_empty e σ: Closed ∅ e → subst σ e = e.
Proof.
  intro; apply (subst_closed ∅); auto.
  set_solver.
Qed.

Instance Closed_proper: Proper ((≡) ==> eq ==> iff) Closed.
Proof. by intros ?? <-%leibniz_equiv ?? <-. Qed.

Lemma val_closed v: Closed ∅ (of_val v).
Proof.
  destruct v; constructor.
  rewrite right_id; done.
Qed.

Corollary subst_val v σ: subst σ (of_val v) = of_val v.
Proof. apply subst_closed_empty, val_closed. Qed.

Lemma subst_fill σ K e: subst σ (fill_ctx e K) = fill_ctx (subst σ e) (subst_ctx σ K).
Proof.
  revert e; unfold subst_ctx.
  induction K as [|I K IH]; cbn; intros; first done.
  rewrite IH; f_equal.
  destruct I; try done.
  all: rewrite /= subst_val //.
Qed.

Hint Constructors Closed.
Lemma closed_mono: Proper ((⊆) ==> (=) ==> impl) Closed.
Proof.
  intros X X' sub e ? <- closed; revert X' sub.
  induction closed; eauto.
  intros; constructor.
  apply IHclosed.
  clear -sub; set_solver.
Qed.

Lemma closed_subst X e: Closed X e → ∀ σ (closed: ∀ x e, x ∈ X → σ !! x = Some e →
                                                         Closed X e),
      Closed X (subst σ e).
Proof.
  induction 1; cbn; eauto; intros.
  - destruct (σ!!x) as [e|] eqn:mt.
    + by apply (closed x).
    + by constructor.
  - constructor.
    apply IHClosed.
    intros x' e'.
    rewrite !elem_of_union !elem_of_singleton' !lookup_delete'.
    intros [[?|?]|inx'].
    1,2: tauto.
    intros [_ [_ mt]].
    generalize (closed x' e' inx' mt).
    apply closed_mono; auto.
    clear; set_solver.
Qed.

Lemma closed_subst_val X e σ: Closed X e → Closed X (subst (of_val <$> σ) e).
Proof.
  intro closed.
  apply closed_subst; auto.
  intros x e' inx.
  rewrite lookup_fmap fmap_Some.
  intros [v [_ ->]].
  eapply closed_mono.
  - apply empty_subseteq.
  - done.
  - apply val_closed.
Qed.

Definition subst_merge' σ e e' :=
  match e' with
  | Some e' => Some (subst σ e')
  | None => e
  end.
Instance: ∀ σ, DiagNone (subst_merge' σ).
Proof. done. Qed.

Definition subst_merge σ σ' := merge (subst_merge' σ) σ σ'.

Lemma subst_subst σ σ' e:
  (∀ x e, σ' !! x = Some e → Closed ∅ e) →
  subst σ (subst σ' e) = subst (subst_merge σ σ') e.
Proof.
  revert σ σ'.
  induction e; intros ?? good_subst; cbn.
  all: rewrite ?IHe ?IHe1 ?IHe2 ?IHe3; auto.
  { rewrite /subst_merge lookup_merge.
    destruct (σ' !! x) as [e'|] eqn:subst'; done. }
  { apply f_equal, (f_equal (λ σ, subst σ e)), map_eq; intro y.
    apply option_eq; intro e'.
    rewrite /subst_merge lookup_merge /subst_merge' !lookup_delete' lookup_merge
            lookup_delete'_cases.
    destruct (bool_decide_reflect (BNamed y ≠ f)) as [neqy|<-%dec_stable]; cycle 1.
    { rewrite lookup_delete; intuition congruence. }
    rewrite lookup_delete'_cases.
    destruct (bool_decide_reflect (BNamed y ≠ x)) as [neqx|<-%dec_stable]; cycle 1.
    { rewrite lookup_delete' lookup_delete; intuition congruence. }
    destruct (σ' !! y) as [e''|] eqn:mty.
    + rewrite !subst_closed_empty; eauto; tauto.
    + by rewrite !lookup_delete'. }
  { intros x' e'.
    rewrite !lookup_delete'; intuition eauto. }
Qed.

Lemma subst_insert_r σ x e e' (e_closed: Closed ∅ e):
  subst (<[x:=e]>σ) e' =
  subst σ (subst (<[x:=e]>∅) e').
Proof.
  rewrite subst_subst.
  { apply (f_equal (λ σ, subst σ e')), map_eq; intro y.
    rewrite /subst_merge lookup_merge.
    destruct (decide (x=y)) as [<-|neq].
    - by rewrite !lookup_insert /= subst_closed_empty.
    - by rewrite !lookup_insert_ne ?lookup_empty /=. }
  intros x' e''.
  rewrite lookup_insert_Some lookup_empty.
  intuition congruence.
Qed.

Lemma fill_ctx_app K K' e: fill_ctx (fill_ctx e K) K' = fill_ctx e (K++K').
Proof. by rewrite /fill_ctx foldl_app. Qed.
Lemma fill_ectx_app K K' e: fill_ectx (fill_ectx e K) K' = fill_ectx e (K++K').
Proof. by rewrite /fill_ectx foldl_app. Qed.


Definition heap := gmap loc val.
Variant task_state := running (e: expr) | done (v: val).
Definition task_buffer := gmap tid task_state.

Variant head_step (p: tid): expr → heap → task_buffer → expr → heap → task_buffer → Prop :=
| step_app f x e e' v h t:
    to_val e' = Some v →
    head_step p (App (Rec f x e) e') h t (subst' f (Rec f x e) (subst' x e' e)) h t
| step_if_true e' e'' h t:
    head_step p (If (Const Ctrue) e' e'') h t e' h t
| step_if_false e' e'' h t:
    head_step p (If (Const Cfalse) e' e'') h t e'' h t
| step_alloc e v h t l:
    to_val e = Some v →
    h !! l = None →
    head_step p (Alloc e) h t (Cloc l) (<[l:=v]>h) t
| step_read l h t v:
    h !! l = Some v →
    head_step p (Read (Cloc l)) h t (of_val v) h t
| step_write l e' v h t:
    to_val e' = Some v →
    is_Some (h!!l) →
    head_step p (Write (Cloc l) e') h t Cunit (<[l:=v]>h) t
| step_post e p' h t:
    t !! p' = None →
    p ≠ p' →
    head_step p (Post e) h t (Ctid p') h (<[p':=running e]>t)
| step_wait_done p' h t v:
    t !! p' = Some (done v) →
    head_step p (Wait (Ctid p')) h t (of_val v) h t.
Variant local_step (p: tid): expr → heap → task_buffer → expr → heap → task_buffer → Prop :=
| local_step_from_head_step K e h t e' h' t':
    head_step p e h t e' h' t' →
    local_step p (fill_ctx e K) h t (fill_ctx e' K) h' t'.

Definition is_running (t: task_buffer) p := ∃ e, t !! p = Some (running e).

Variant global_step: heap → task_buffer → tid → heap → task_buffer → tid → Prop :=
| global_local p h t h' t' e e':
    t !! p = Some (running e) → t' !! p = Some (running e') →
    local_step p e h (delete p t) e' h' (delete p t') →
    global_step h t p h' t' p
| global_wait_schedule h t K p p' p'':
    t !! p = Some (running (fill_ctx (Wait (Ctid p'')) K)) →
    is_running t p' →
    global_step h t p h t p'
| global_done_schedule h t p p' v e:
    to_val e = Some v →
    t !! p = Some (running e) →
    is_running t p' →
    global_step h t p h (<[p := done v]>t) p'.

Definition reducible e := ∃ p T H e' T' H', head_step p e T H e' T' H'.
Definition stuck e := ¬reducible e.
Definition atomic e := reducible e ∧ ∀ p T H e' T' H', head_step p e T H e' T' H' → stuck e'.

Lemma to_of_val v: to_val (of_val v) = Some v.
Proof.
  destruct v; first done.
  rewrite /= decide_left; done.
Qed.
    
Lemma of_to_val e v: to_val e = Some v → of_val v = e.
Proof.
  destruct e; try done.
  - destruct v; last done.
    injection 1 as <-; done.
  - cbn.
    destruct decide; simplify_eq 1.
    intros <-; done.
Qed.

