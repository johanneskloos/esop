From stdpp Require Import fin_maps collections gmap coPset.

Definition overlap `{Collection A C, FinMap A M} {B} (s: C) (m m': M B) :=
  ∀ x, x ∈ s → m!!x = m'!!x.

Instance overlap_equivalence `{Collection A C, FinMap A M} (s: C) {B}:
  Equivalence (overlap s (B:=B)).
Proof. firstorder. Qed.

Instance overlap_mono `{Collection A C, FinMap A M} {B}:
  Proper ((⊆) --> (=) ==> (=) ==> impl) (overlap (A:=A) (C:=C) (M:=M) (B:=B)).
Proof.
  intros s s' sub m ? <- m' ? <- ovm x inx.
  apply ovm, sub, inx.
Qed.

Infix "≡[ s ]≡" := (overlap s) (at level 70).

Lemma overlap_iff `{Collection A C, FinMap A M} {B} (s s': C) (m m' m'': M B)
      (sub: s' ⊆ s) (eqm: m' ≡[ s ]≡ m''):
  m ≡[ s' ]≡ m' ↔ m ≡[ s' ]≡ m''.
Proof.
  enough (m' ≡[ s' ]≡ m'').
  { split; intro; etrans; done. }
  eapply overlap_mono; eauto.
Qed.
