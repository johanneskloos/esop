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
  
  Definition delayed_typed Γ η e e' A τ η' :=
    ∀ D N σ,
      (int_i_env Γ D N σ ∗ int_i_heap η D N)
        -∗ WP subst (of_val <$> σ) e
        {{ xᵢ, ∃ Nᵢ' D' d', ⌜N ≡[ not_new A ]≡ Nᵢ' ∧ D' !! RET = Some d'⌝ ∧
                            int_i_type τ d' Nᵢ'  xᵢ ∧
                            (□simulation Γ e' η A τ η' D D') ∧
                            int_i_heap η' D' Nᵢ' }}.
  Record delayed_simulation U Γ (η: hexpr) e e' A (τ: type) (η': hexpr) :=
    Delayed {
        ds_used_names: names Γ ∪ names η ⊆ U;
        ds_type_e: typing U Γ e η A τ η';
        ds_type_e': typing U Γ e' η A τ η';
        ds_sim: delayed_typed Γ η e e' A τ η'
      }.
End Definitions.

Section Meta.
  Context `{allG Σ}.
  Local Open Scope I.
End Meta.
