From iris.proofmode Require Import tactics.
From esop Require Import closed_async closed_basic closed_memory closed_meta delayed types
     typetranslation corecalculus.
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
    - by rewrite map_subseteq_spec => [??]; rewrite lookup_empty => [?].
    - done.
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

  Lemma closure_let (x: binder) η₁ η₂ η₃ τ₁ τ₂ A₁ A₂ e₁ e₂ e₁' e₂':
    delayed_simulation U Γ η₁ e₁ e₁' A₁ τ₁ η₂ →
    delayed_simulation (U ∪ A₁) (insert' x τ₁ Γ) η₂ e₂ e₂' A₂ τ₂ η₃ →
    delayed_simulation U Γ η₁ (Let x e₁ e₂) (Let x e₁' e₂') (A₁ ∪ A₂) τ₂ η₃.
  Proof.
    intros [good₁ ty₁ ty₁' del₁] [good₂ ty₂ ty₂' del₂].
    split.
    - done.
    - by econstructor.
    - by econstructor.
    - destruct x as [|x].
      + admit.
      + iPoseProof (delayed_bind $! x e₁ e₁' [CAppR
  Qed.
  
End FullClosure.