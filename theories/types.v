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
hexpr :=
| hemp
| hstar (η η': hexpr)
| hpt (ξ: lname) (τ: type)
| hwait (ξ: lname) (A: lnames) (η: hexpr).
Bind Scope ty_scope with type.
Bind Scope he_scope with hexpr.
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
Instance: EqDecision hexpr.
Proof. solve_decision. Qed.

Definition env := gmap string type.

Definition insert' {A} b (y: A) (m: gmap string A) :=
  match b with BNamed x => <[x:=y]>m | BAnon => m end.
Definition Let b e e' := App (Rec BAnon b e') e.

(* TODO - figure out how to get a nice notation working. *)
Inductive typing: lnames → env → expr → hexpr → lnames → type → hexpr → Prop :=
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
Instance: Names hexpr := he_names.

Instance combine_names `{Names A, Names B}: Names (A*B) := λ p, names (p.1) ∪ names (p.2).
Canonical Structure lnamesC := leibnizC lnames.
Instance lnamesC_union: Union lnamesC := (∪).
Instance lnamesC_monoid: Monoid lnamesC_union := Build_Monoid lnamesC (∪) ∅ _ _ _ _.

Instance names_env: Names env := λ Γ, [^ (∪) map] _ ↦ τ ∈ Γ, (names τ: lnamesC).
Lemma elem_of_names_env_empty ξ: ¬ξ ∈ names (∅: env).
Proof. rewrite /names /names_env big_opM_empty elem_of_empty => [[]]. Qed.
Lemma elem_of_names_env_insert x τ (Γ: env) ξ (x_fresh: Γ!!x = None):
  ξ ∈ names (<[x:=τ]>Γ) ↔ ξ ∈ names τ ∨ ξ ∈ names Γ.
Proof. rewrite /names /names_env big_opM_insert ?elem_of_union; done. Qed.

Lemma elem_of_names_env ξ (Γ: env): ξ ∈ names Γ ↔ ∃ x τ, Γ !! x = Some τ ∧ ξ ∈ names τ.
Proof.
  induction Γ as [|x τ Γ x_fresh IH] using map_ind.
  - trans False.
    { split; [apply elem_of_names_env_empty|done]. }
    setoid_rewrite lookup_empty.
    split; first done.
    intros [? [? [[=] _]]].
  - rewrite elem_of_names_env_insert ?IH; last done.
    split.
    { intros [inξ|[x' [τ' [mt inξ]]]].
      { exists x, τ; rewrite lookup_insert; auto. }
      exists x', τ'; rewrite lookup_insert_ne; auto.
      intros <-; by rewrite x_fresh in mt. }
    { intros [x' [τ' [mt inξ]]].
      destruct (decide (x=x')) as [<-|neq].
      { rewrite lookup_insert in mt; injection mt as <-; auto. }
      rewrite lookup_insert_ne in mt; eauto. }
Qed.

Lemma elem_of_names_env_insert_gen x τ (Γ: env) ξ:
  ξ ∈ names (<[x:=τ]>Γ) → ξ ∈ names τ ∨ ξ ∈ names Γ.
Proof.
  assert (<[x:=τ]>Γ = <[x:=τ]>(delete x Γ)) as ->.
  { by apply map_eq; intro; rewrite insert_delete. }
  rewrite elem_of_names_env_insert; last apply lookup_delete.
  intros [case|case]; auto.
  right.
  rewrite elem_of_names_env in case * => [[x' [τ' [mtx inξ]]]].
  rewrite elem_of_names_env.
  exists x', τ'; split; auto.
  rewrite lookup_delete_Some in mtx * => [[_ ?]]; done.
Qed.

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
  names Γ ⊆ U → names η ⊆ U →
  A ⊥ U ∧ names τ ⊆ U ∪ A ∧ names η' ⊆ U ∪ A.
Proof.
  induction 1; intros env_good pre_good; cbn -[union].
  1,2,3: repeat split; set_solver.
  all: try (destruct IHtyping; auto; set_solver).
  - repeat split.
    1,3: set_solver.
    rewrite right_id.
    trans (names Γ); last done.
    intro; rewrite elem_of_names_env; eauto.
  - destruct IHtyping1 as [disj1 [ty1 post1]]; auto.
    destruct IHtyping2 as [disj2 [ty2 post2]]; auto.
    { destruct x; cbn.
      - trans U; auto; apply union_subseteq_l.
      - trans (names τ₁ ∪ names Γ).
        + intro; rewrite elem_of_union; apply elem_of_names_env_insert_gen.
        + apply union_least; auto.
          trans U; auto; apply union_subseteq_l. }
    set_solver.
  - destruct IHtyping1 as [disj1 [ty1 post1]]; auto.
    destruct IHtyping2 as [disj2 [ty2 post2]]; auto.
    { etrans; first done; apply union_subseteq_l. }
    set_solver.
Qed.