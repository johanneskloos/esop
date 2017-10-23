From iris.algebra Require Import agree excl csum updates.

Definition oneshot A := csum (excl unit) (agree A).
Canonical Structure oneshotR (A: ofeT) := csumR (exclR unitC) (agreeR A).
Definition unset {A: ofeT}: oneshotR A := Cinl (Excl ()).
Definition agreed {A: ofeT} (x: A): oneshotR A := Cinr (to_agree x).

Section Facts.
  Context {A: ofeT}.

  Global Instance agreed_ne: NonExpansive (@agreed A).
  Proof. solve_proper. Qed.

  Global Instance unset_exclusive: Exclusive (@unset A).
  Proof. apply _. Qed.

  Global Instance agreed_persistent (x: A): Persistent (agreed x).
  Proof. apply _. Qed.
  
  Lemma oneshot_update (x: A): unset ~~> agreed x.
  Proof. by apply cmra_update_exclusive. Qed.

  Lemma agreed_valid (x y: A): ✓(agreed x ⋅ agreed y) → x ≡ y.
  Proof.
    rewrite /agreed Cinr_op.
    apply agree_op_inv'.
  Qed.

  Context `{Discrete A}.
  Global Instance oneshot_discrete: CMRADiscrete (oneshotR A).
  Proof. apply _. Qed.
End Facts.