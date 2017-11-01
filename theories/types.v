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
  | hpt ξ τ => {[ ξ ]} ∪ names τ
  | hwait ξ A η => {[ ξ ]} ∪ (he_names η ∖ A)
  end.
Instance: Names hexpr := he_names.

Fixpoint res_names η: gset lname :=
  match η with
  | hemp => ∅
  | hstar η η' => res_names η ∪ res_names η'
  | hpt ξ τ => {[ ξ ]}
  | hwait ξ A η => {[ ξ ]} ∪ (res_names η ∖ A)
  end.
         
Inductive hexpr_equiv: Equiv hexpr :=
| hee_refl: Reflexive (≡)
| hee_symm: Symmetric (≡)
| hee_trans: Transitive (≡)
| hee_proper_star: Proper ((≡) ==> (≡) ==> (≡)) hstar
| hee_proper_wait: ∀ ξ A, Proper ((≡) ==> (≡)) (hwait ξ A)
| hee_assoc: Assoc (≡) hstar
| hee_comm: Comm (≡) hstar
| hee_left: LeftId (≡) hemp hstar.
Instance hexpr_equivalence: Equivalence hexpr_equiv.
Proof. split; [apply hee_refl|apply hee_symm|apply hee_trans]. Qed.
Existing Instances hee_proper_star hee_proper_wait hee_assoc hee_comm hee_left hexpr_equiv.
Instance: RightId (≡) hemp hstar.
Proof. intro; rewrite comm left_id //. Qed.

Instance he_names_proper: Proper ((≡) ==> (=)) he_names.
Proof.
  intros η η' eqη.
  apply leibniz_equiv.
  induction eqη; simpl; try done.
  - by etrans.
  - by f_equiv.
  - by do 2 f_equiv.
  - by rewrite assoc.
  - by rewrite comm.
  - by rewrite left_id.
Qed.

Instance res_names_proper: Proper ((≡) ==> (=)) res_names.
Proof.
  intros η η' eqη.
  apply leibniz_equiv.
  induction eqη; simpl; try done.
  - by etrans.
  - by f_equiv.
  - by do 2 f_equiv.
  - by rewrite assoc.
  - by rewrite comm.
  - by rewrite left_id.
Qed.

Lemma res_names_sub_names η: res_names η ⊆ names η.
Proof.
  induction η; cbn -[union]; try done.
  - by apply union_mono.
  - apply union_subseteq_l.
  - apply union_mono; first done.
    apply difference_mono; done.
Qed.

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

Lemma elem_of_names_env_insert' x τ (Γ: env) ξ:
  ξ ∈ names (insert' x τ Γ) → ξ ∈ names τ ∨ ξ ∈ names Γ.
Proof.
  destruct x; last apply elem_of_names_env_insert_gen.
  auto.
Qed.

Inductive heap_wf: lnames → hexpr → Prop :=
| wf_emp Ξ: heap_wf Ξ hemp
| wf_star Ξ η₁ η₂ (disj: res_names η₁ ⊥ res_names η₂):
    heap_wf Ξ η₁ → heap_wf Ξ η₂ → heap_wf Ξ (η₁ ⊗ η₂)
| wf_pt Ξ ξ τ (inξ: ξ ∈ Ξ) (sub: names τ ⊆ Ξ): heap_wf Ξ (ξ ↦ τ)
| wf_wait Ξ ξ A η (inξ: ξ ∈ Ξ) (notinξ: ξ ∉ names η)
          (disj: Ξ ⊥ A):
    heap_wf (Ξ ∪ A) η → heap_wf Ξ (hwait ξ A η).

Lemma heap_wf_star Ξ η₁ η₂:
  heap_wf Ξ (η₁ ⊗ η₂) ↔ heap_wf Ξ η₁ ∧ heap_wf Ξ η₂ ∧ res_names η₁ ⊥ res_names η₂.
Proof.
  split.
  - inversion_clear 1; auto.
  - by intros [?[??]]; constructor.
Qed.

Lemma heap_wf_wait Ξ ξ A η:
  heap_wf Ξ (hwait ξ A η) ↔ ξ ∈ Ξ ∧ ξ ∉ names η ∧ Ξ ⊥ A ∧ heap_wf (Ξ ∪ A) η.
Proof.
  split.
  - inversion_clear 1; auto.
  - by intros [?[?[??]]]; constructor.
Qed.

Instance heap_wf_proper: Proper ((≡) ==> (≡) ==> iff) heap_wf.
Proof.
  intros Ξ ? <-%leibniz_equiv.
  intros η η' eqη; revert Ξ.
  induction eqη as [η|η₁ η₂ eqη|η₁ η₂ η₃ eq₁₂ IH₁₂ eq₂₃ IH₂₃|η₁ η₁' eqη₁ IHη₁ η₂ η₂' eqη₂ IHη₂
                    |ξ A η η' eqη IH|η₁ η₂ η₃|η₁ η₂|η];
    intro.
  - done.
  - done.
  - by rewrite IH₁₂.
  - by rewrite !heap_wf_star IHη₁ IHη₂ eqη₁ eqη₂.
  - by rewrite !heap_wf_wait IH eqη.
  - rewrite !heap_wf_star; cbn.
    rewrite disjoint_union_r disjoint_union_l.
    tauto.
  - rewrite !heap_wf_star.
    intuition.
  - rewrite heap_wf_star.
    intuition.
    + constructor.
    + apply disjoint_empty_l.
Qed.

(* TODO - figure out how to get a nice notation working. *)
Inductive typing: lnames → env → expr → hexpr → lnames → type → hexpr → Prop :=
| tytrue U Γ: typing U Γ Ctrue ∅ ∅ Bool ∅
| tyfalse U Γ: typing U Γ Cfalse ∅ ∅ Bool ∅
| tyunit  U Γ: typing U Γ Cunit ∅ ∅ Unit ∅
| tyvar U Γ (x: string) τ (Γx: Γ !! x = Some τ): typing U Γ x ∅ ∅ τ ∅
| tylet U Γ (x: binder) η₁ η₂ η₃ τ₁ τ₂ A₁ A₂ e₁ e₂:
    typing U Γ e₁ η₁ A₁ τ₁ η₂ →
    typing (U ∪ A₁) (insert' x τ₁ Γ) e₂ η₂ A₂ τ₂ η₃ →
    typing U Γ (Let x e₁ e₂) η₁ (A₁ ∪ A₂) τ₂ η₃
| tyif U Γ η₁ η₂ η₃ τ A₁ A₂ e₁ e₂ e₃:
    typing U Γ e₁ η₁ A₁ tbool η₂ →
    typing (U ∪ A₁) Γ e₂ η₂ A₂ τ η₃ →
    typing (U ∪ A₁) Γ e₃ η₂ A₂ τ η₃ →
    typing U Γ (If e₁ e₂ e₃) η₁ (A₁ ∪ A₂) τ η₃              
| tyref U Γ e η₁ η₂ τ A ξ (ξ_fresh: ξ ∉ U ∪ A) (post_wf: heap_wf (U ∪ A ∪ {[ξ]}) (η₂ ⊗ ξ ↦ τ)):
    typing U Γ e η₁ A τ η₂ →
    typing U Γ (Alloc e) η₁ (A ∪ {[ ξ ]}) (Ref(ξ)) (η₂ ⊗ ξ ↦ τ)
| tyread U Γ e η₁ η₂ ξ τ A:
    typing U Γ e η₁ A (Ref(ξ)) (η₂ ⊗ ξ ↦ τ) →
    typing U Γ (Read e) η₁ A τ (η₂ ⊗ ξ ↦ τ)
| tywrite U Γ e e' η₁ η₂ η₃ ξ τ A₁ A₂:
    typing U Γ e η₁ A₁ (Ref(ξ)) η₂ →
    typing (U ∪ A₁) Γ e' η₂ A₂ τ (η₃ ⊗ ξ ↦ τ) →
    typing U Γ (Write e e') η₁ (A₁ ∪ A₂) Unit (η₃ ⊗ ξ ↦ τ)
| typost U Γ e η₁ η₂ τ A ξ (ξ_fresh: ξ ∉ U ∪ A) (wf_post: heap_wf (U ∪ {[ξ]}) (Wait(ξ,A) η₂)):
    typing U Γ e η₁ A τ η₂ →
    typing U Γ (Post e) η₁ {[ξ]} (Promise(ξ,A) τ) (Wait(ξ,A) η₂)
| tywait U Γ e (η₁ η₂ η₃: hexpr) τ ξ A₁ A₂ (wfη: heap_wf (U ∪ A₁ ∪ A₂) (η₂ ⊗ η₃)) (disj: A₂ ⊥ U)
         (ξ_not_in_τ: ξ ∉ names τ) (ξ_not_in_η₃: ξ ∉ names η₃) (disjA: A₁ ⊥ A₂):
    typing U Γ e η₁ A₁ (ttask ξ A₂ τ) (η₂ ⊗ hwait ξ A₂ η₃) →
    typing U Γ (Wait e) η₁ (A₁ ∪ A₂) τ (η₂ ⊗ η₃)         
| tyframe U Γ e (η₁ η₂: hexpr) τ A (ηf: hexpr)
          (disjη: res_names η₁ ⊥ res_names ηf)
          (disjη': res_names η₂ ⊥ res_names ηf)
          (disjA: A ⊥ names ηf) (wf: heap_wf (U ∪ A) ηf):
    typing U Γ e η₁ A τ η₂ →
    typing U Γ e (η₁ ⊗ ηf) A τ (η₂ ⊗ ηf)
| tyweaken U Γ e η₁ η₂ τ A U' Γ' A' (env_good: names Γ ⊆ U) (pre_good: names η₁ ⊆ U) (disjUA: U' ⊥ A')
           (subU: U ⊆ U') (subΓ: Γ ⊆ Γ') (subA: A ⊆ A') (wf: heap_wf (A' ∪ U') η₂):
    typing U Γ e η₁ A τ η₂ →
    typing U' Γ' e η₁ A' τ η₂
| typroper U U' Γ e η₁ η₁' A A' τ η₂ η₂'
           (eqU: U ≡ U') (eqη₁: η₁ ≡ η₁') (eqA: A ≡ A') (eqη₂: η₂ ≡ η₂'):
    typing U Γ e η₁ A τ η₂ → typing U' Γ e η₁' A' τ η₂'.
Instance: Proper ((≡) ==> (=) ==> (=) ==> (≡) ==> (≡) ==> (=) ==> (≡) ==> iff) typing.
Proof.
  intros U ? <-%leibniz_equiv Γ ? <- e ? <- η₁ η₁' eqη₁ A ? <-%leibniz_equiv τ ? <- η₂ η₂' eqη₂.
  split; apply typroper; done.
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
  induction 1; intros env_good' pre_good'; cbn -[union].
  1,2,3: repeat split; try apply disjoint_empty_l; try apply empty_subseteq.
  - split; first apply disjoint_empty_l.
    split; last apply empty_subseteq.
    rewrite right_id.
    etrans; last apply env_good'.
    intro ξ.
    rewrite elem_of_names_env.
    exists x,τ; auto.
  - destruct IHtyping1 as [disj₁ [subτ₁ subη₂]]; auto.
    destruct IHtyping2 as [[disj₂ disjA]%disjoint_union_r [subτ₂ subη₃]]; auto.
    { intros ξ [?|?]%elem_of_names_env_insert'; auto.
      apply elem_of_union_l; auto. }
    rewrite !assoc disjoint_union_l; auto.
  - destruct IHtyping1 as [disj₁ [subτ₁ subη₂]]; auto.
    destruct IHtyping2 as [[disj₂ disjA]%disjoint_union_r [subτ₂ subη₃]]; auto.
    { etrans; first done. apply union_subseteq_l. }
    rewrite !assoc disjoint_union_l; auto.
  - destruct IHtyping as [disj [subτ subη']]; auto.
    rewrite not_elem_of_union in ξ_fresh * => [[??]].
    repeat split.
    + rewrite disjoint_union_l disjoint_singleton_l; auto.
    + rewrite assoc; apply union_subseteq_r.
    + rewrite (comm (∪) {[ξ]}) !assoc; apply union_mono; last done.
      apply union_least; done.
  - destruct IHtyping as [disj [subτ subη']]; auto.
    repeat split; auto.
    etrans; last apply subη'.
    etrans; last apply union_subseteq_r.
    apply union_subseteq_r.
  - destruct IHtyping1 as [disj [subτ subη']]; auto.
    destruct IHtyping2 as [disj' [subτ' subη'']]; auto.
    { by etrans; last apply union_subseteq_l. }
    rewrite disjoint_union_r in disj' * => [[??]].
    rewrite disjoint_union_l; split; auto.
    split.
    { apply empty_subseteq. }
    rewrite (assoc (∪) U); done.
  - destruct IHtyping as [disj₁ [subτ₁ subη₂]]; auto.
    rewrite not_elem_of_union in ξ_fresh * => [[??]].
    rewrite disjoint_singleton_l.
    split; auto.
    split; (rewrite comm; apply union_mono; last done).
    + clear -subτ₁; set_solver.
    + clear -subη₂; set_solver.
  - destruct IHtyping as [disj' [subτ subη]]; auto.
    rewrite disjoint_union_l.
    rewrite !assoc.
    repeat split; auto.
    + intros ξ' inξ'.
      rewrite elem_of_union.
      destruct (decide (ξ' ∈ A₂)); auto.
      left; apply subτ.
      rewrite /= elem_of_union elem_of_difference; auto.
    + apply union_least.
      * etrans; last apply union_subseteq_l.
        etrans; last apply subη.
        apply union_subseteq_l.
      * intros ξ' inξ'.
        rewrite elem_of_union.
        destruct (decide (ξ' ∈ A₂)); auto.
        left; apply subη.
        cbn -[union].
        do 2 apply elem_of_union_r.
        rewrite elem_of_difference; auto.
  - destruct IHtyping as [disj [subτ subη]]; auto.
    + etrans; last apply pre_good'.
      apply union_subseteq_l.
    + repeat split; auto.
      apply union_least; auto.
      trans U; last apply union_subseteq_l.
      etrans; last apply pre_good'.
      apply union_subseteq_r.
  - destruct IHtyping as [disj [namesτ namesη']]; auto.
    repeat split; auto.
    + etrans; first apply namesτ.
      apply union_mono; done.
    + etrans; first apply namesη'.
      apply union_mono; done.
  - subst.
    apply leibniz_equiv in eqU; subst.
    apply leibniz_equiv in eqA; subst.
    rewrite -eqη₂.
    destruct IHtyping as [? [??]]; auto.
    rewrite eqη₁; done.
Qed.

Lemma heap_wf_names U η: heap_wf U η → names η ⊆ U.
Proof.
  induction 1; cbn -[union].
  - apply empty_subseteq.
  - by apply union_least.
  - apply union_least; auto.
    apply elem_of_subseteq_singleton; done.
  - apply union_least.
    + by apply elem_of_subseteq_singleton.
    + clear -IHheap_wf.
      set_solver.
Qed.

Lemma typing_wf  U Γ e η τ η' A:
  typing U Γ e η A τ η' → heap_wf U η → heap_wf (U ∪ A) η'.
Proof.
  induction 1; intro wf'.
  1-4: constructor.
  all: try by rewrite ?union_assoc_L; auto.
  - inversion_clear wf'.
    constructor; auto.
  - by rewrite union_comm_L.
  - apply leibniz_equiv in eqU.
    apply leibniz_equiv in eqA.
    subst.
    rewrite -eqη₂.
    apply IHtyping.
    rewrite eqη₁; done.
Qed.
