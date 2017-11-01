From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import agree auth excl updates local_updates.
From esop Require Import typetranslation corecalculus specification types overlap oneshot.
From stdpp Require Import gmap set coPset.

Section Definitions.
  Context `{allG Σ}.
  Local Open Scope I.

  Definition simulation:
    env → expr → hexpr → gset gname → type → hexpr → conn_map → conn_map → iProp Σ
    := simulation_body int_s_type int_s_heap.
  Global Instance simulation_proper:
    Proper ((=) ==> (=) ==> (≡) ==> (=) ==> (=) ==> (≡) ==> (=) ==> (=) ==> (≡))
           simulation.
  Proof.
    rewrite /simulation /simulation_body /existential_triple.
    intros Γ ? <- e ? <- η₁ η₁' eqη₁ A ? <- τ ? <- η₂ η₂' eqη₂ D ? <- D' ? <-.
    f_equiv; intro N.
    f_equiv; intro σ.
    f_equiv; intro p.
    f_equiv; intro K.
    do 3 f_equiv.
    { by apply int_s_heap_proper. }
    do 2 f_equiv; intro v.
    do 2 f_equiv; intro d.
    f_equiv; intro N'.
    do 2 f_equiv.
    apply int_s_heap_proper; done.
  Qed.
  
  Definition delayed_typed Γ η e e' A τ η' :=
    ∀ D N σ,
      (int_i_env Γ D N σ ∗ int_i_heap η D N)
        -∗ WP subst (of_val <$> σ) e
        {{ xᵢ, ∃ Nᵢ' D' d', ⌜N ≡[ not_new A ]≡ Nᵢ' ∧ D' !! RET = Some d'⌝ ∧
                            int_i_type τ d' Nᵢ'  xᵢ ∧
                            (□simulation Γ e' η A τ η' D D') ∧
                            int_i_heap η' D' Nᵢ' }}.
  Global Instance delayed_typed_proper:
    Proper ((=) ==> (≡) ==> (=) ==> (=) ==> (=) ==> (=) ==> (≡) ==> (⊣⊢))
           delayed_typed.
  Proof.
    intros Γ ? <- η₁ η₁' eqη₁ e ? <- e' ? <- A ? <- τ ? <- η₂ η₂' eqη₂.
    rewrite /delayed_typed.
    f_equiv; intro D.
    f_equiv; intro N.
    f_equiv; intro σ.
    f_equiv.
    { by f_equiv; apply int_i_heap_proper. }
    apply wp_proper; intro v.
    f_equiv; intro N'.
    f_equiv; intro D'.
    f_equiv; intro d'.
    do 3 f_equiv.
    2: by apply int_i_heap_proper.
    f_equiv.
    apply simulation_proper; done.
  Qed.
  
  Record delayed_simulation U Γ (η: hexpr) e e' A (τ: type) (η': hexpr) :=
    Delayed {
        ds_used_names: names Γ ∪ names η ⊆ U;
        ds_type_e: typing U Γ e η A τ η';
        ds_type_e': typing U Γ e' η A τ η';
        ds_sim: delayed_typed Γ η e e' A τ η'
      }.
  Global Instance delayed_simulation_proper:
    Proper ((=) ==> (=) ==> (≡) ==> (=) ==> (=) ==> (=) ==> (=) ==> (≡) ==> iff)
           delayed_simulation.
  Proof.
    intros U ? <- Γ ? <- η₁ η₁' eqη₁ e ? <- e' ? <- A ? <- τ ? <- η₂ η₂' eqη₂.
    revert η₁ η₁' eqη₁ η₂ η₂' eqη₂.
    apply proper_sym_impl_iff_2.
    1,2: apply _.
    intros η₁ η₁' eqη₁ η₂ η₂' eqη₂ [good ty ty' del].
    split.
    - by rewrite -eqη₁.
    - by rewrite -eqη₁ -eqη₂.
    - by rewrite -eqη₁ -eqη₂.
    - by rewrite -eqη₁ -eqη₂.
  Qed.
  
End Definitions.
