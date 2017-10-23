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
Definition add' b (X: gset string) := match b with BNamed x => {[x]} ∪ X | BAnon => X end.
Inductive Closed: gset string → expr → Prop :=
| const_closed X c: Closed X (Const c)
| var_closed X x: x ∈ X → Closed X (Var x)
| rec_closed X f x e: Closed (add' f (add' x X)) e → Closed X (Rec f x e)
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
  3: destruct (IH (add' f (add' x X)) e); last by right; inversion_clear 1.
  all: by left; constructor.
Defined.

Variant val :=
| VConst (c: const)
| VRec (f x: binder) (e: expr) {e_closed: Closed (add' f (add' x ∅)) e}.
                                                               
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
| EWait.

Definition of_val v :=
  match v with
  | VConst c => Const c
  | VRec f x e _ => Rec f x e
  end.
Definition to_val e :=
  match e with
  | Const c => Some (VConst c)
  | Rec f x e => match decide (Closed (add' f (add' x ∅)) e) with
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

