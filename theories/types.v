(** DWFM soundness proofs - The type system. *)
From esop Require Import corecalculus.
From stdpp Require Import gmap strings set.
From iris.algebra Require Import big_op.

Definition lname := positive.
Definition lnames := gset lname.

Inductive type :=
| tbool
| tunit
| tref (ξ: lname)
| ttask (ξ: lname) (A: lnames) (τ: type)
with
heap :=
| hemp
| hstar (η η': heap)
| hpt (ξ: lname) (τ: type)
| hwait (ξ: lname) (A: lnames) (η: heap).
Bind Scope ty_scope with type.
Bind Scope he_scope with heap.
Notation Bool := tbool.
Notation Unit := tunit.
Notation "'Ref(' ξ ')'" := (tref ξ) (at level 30): ty_scope.
Notation "'Promise(' ξ ',' A ')' τ" := (ttask ξ A τ) (at level 30): ty_scope.
Infix "⊗" := hstar (at level 45): he_scope.
Infix "↦" := hpt (at level 35): he_scope.
Notation "'Wait(' ξ ',' A ')' η" := (hwait ξ A η) (at level 40): he_scope.
Notation "∅" := hemp: he_scope.
(* TODO: Add function types. For now, we simply type let expressions. *)
Instance: EqDecision type.
Proof. solve_decision. Qed.
Instance: EqDecision heap.
Proof. solve_decision. Qed.

Definition env := gmap string type.

Definition insert' {A} b (y: A) (m: gmap string A) :=
  match b with BNamed x => <[x:=y]>m | BAnon => m end.
Definition Let b e e' := App (Rec BAnon b e') e.

(* TODO - figure out how to get a nice notation working. *)
Inductive typing: lnames → env → expr → heap → lnames → type → heap → Prop :=
| tytrue U Γ: typing U Γ Ctrue ∅ ∅ Bool ∅
| tyfalse U Γ: typing U Γ Ctrue ∅ ∅ Bool ∅
| tyunit  U Γ: typing U Γ Cunit ∅ ∅ Unit ∅
| tyvar U Γ (x: string) τ (Γx: Γ !! x = Some τ): typing U Γ x ∅ ∅ τ ∅
| tylet U Γ (x: binder) η₁ η₂ η₃ τ₁ τ₂ A₁ A₂ e₁ e₂:
    typing U Γ e₁ η₁ A₁ τ₁ η₂ →
    typing (U ∪ A₁) (insert' x τ₁ Γ) e₂ η₂ A₂ τ₂ η₃ →
    typing U Γ (Let x e₁ e₂) η₁ (A₁ ∪ A₂) τ₂ η₃
| tyref U Γ e η₁ η₂ τ A ξ (ξ_fresh: ξ ∉ U ∪ A):
    typing U Γ e η₁ A τ η₂ →
    typing U Γ (Alloc e) η₁ (A ∪ {[ ξ ]}) (Ref(ξ)) (η₂ ⊗ ξ ↦ τ)
| tyread U Γ e η₁ η₂ ξ τ A:
    typing U Γ e η₁ A (Ref(ξ)) (η₂ ⊗ ξ ↦ τ) →
    typing U Γ (Read e) η₁ A τ (η₂ ⊗ ξ ↦ τ)
| tywrite U Γ e e' η₁ η₂ η₃ ξ τ A₁ A₂:
    typing U Γ e η₁ A₁ (Ref(ξ)) η₂ →
    typing (U ∪ A₁) Γ e' η₂ A₂ τ (η₃ ⊗ ξ ↦ τ) →
    typing U Γ (Write e e') η₁ (A₁ ∪ A₂) Unit (η₃ ⊗ ξ ↦ τ)
| typost U Γ e η₁ η₂ τ A ξ (ξ_fresh: ξ ∉ U ∪ A):
    typing U Γ e η₁ A τ η₂ →
    typing U Γ (Post e) η₁ {[ξ]} (Promise(ξ,A) τ) (Wait(ξ,A) η₂).

Class Names A := names: A → gset lname.

Fixpoint ty_names τ: gset lname :=
  match τ with
  | tbool => ∅
  | tunit => ∅
  | tref ξ => {[ ξ ]}
  | ttask ξ A τ => {[ ξ ]} ∪ (ty_names τ ∖ A)
  end.
Instance: Names type := ty_names.

Fixpoint he_names η: gset lname :=
  match η with
  | hemp => ∅
  | hstar η η' => he_names η ∪ he_names η'
  | hpt ξ τ => {[ ξ ]} ∪ ty_names τ
  | hwait ξ A η => {[ ξ ]} ∪ (he_names η ∖ A)
  end.
Instance: Names heap := he_names.

Instance combine_names `{Names A, Names B}: Names (A*B) := λ p, names (p.1) ∪ names (p.2).
Canonical Structure lnamesC := leibnizC lnames.
Instance lnamesC_union: Union lnamesC := (∪).
Instance lnamesC_monoid: Monoid lnamesC_union := Build_Monoid lnamesC (∪) ∅ _ _ _ _.

Instance: Names env := λ Γ, [^ (∪) map] _ ↦ τ ∈ Γ, (names τ: lnamesC).

Definition good_env U (Γ: env) := ∀ x τ, Γ!!x = Some τ → names τ ⊆ U.
Lemma lookup_insert' {A} x b y z (m: gmap string A):
  insert' b x m !! y = Some z ↔ (b = BNamed y ∧ x = z) ∨ (b ≠ BNamed y ∧ m!!y = Some z).
Proof.
  unfold insert'.
  destruct b as [|b].
  - intuition congruence.
  - destruct (decide (b = y)) as [<-|neq].
    + rewrite lookup_insert; intuition congruence.
    + rewrite lookup_insert_ne; intuition congruence.
Qed.

Lemma typing_good_names U Γ e η τ η' A:
  typing U Γ e η A τ η' →
  good_env U Γ → names η ⊆ U →
  A ⊥ U ∧ names τ ⊆ U ∪ A ∧ names η' ⊆ U ∪ A.
Proof.
  induction 1; intros env_good pre_good; cbn -[union].
  1,2,3: repeat split; set_solver.
  all: try (destruct IHtyping; auto; set_solver).
  - repeat split.
    1,3: set_solver.
    rewrite right_id; apply (env_good x τ Γx).
  - destruct IHtyping1 as [disj1 [ty1 post1]]; auto.
    destruct IHtyping2 as [disj2 [ty2 post2]]; auto.
    { intros x' τ'; rewrite lookup_insert'.
      intros [[? <-]|[? ?%env_good]]; auto; set_solver. }
    set_solver.
  - destruct IHtyping1 as [disj1 [ty1 post1]]; auto.
    destruct IHtyping2 as [disj2 [ty2 post2]]; auto.
    { intros x' τ' ?%env_good; set_solver. }
    set_solver.
Qed.