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

Definition merge_along_loop `{FinMap A M} {B} (m: M B) k (m': M B) :=
  match m!!k with Some v => <[k:=v]>m' | None => delete k m' end.

Definition merge_along `{FinCollection A C, FinMap A M} {B} (s: C) (m m': M B) :=
  collection_fold (merge_along_loop m) m' s.
Infix "~[ s ]~>" := (merge_along s) (at level 50).

Section Facts.
  Context `{FinCollection A C, FinMap A M}.
  Instance elem_of_dec_C (x: A) (s: C): Decision (x ∈ s) := elem_of_dec_slow x s.

  Lemma merge_along_cases
        {B} (s: C) (m m': M B) (k: A):
    (m ~[s]~> m')!!k = if bool_decide (k ∈ s) then m!!k else m'!!k.
  Proof.
    unfold merge_along.
    refine (collection_fold_ind
              (λ m'' s'', m''!!k = if bool_decide (k ∈ s'') then m!!k else m'!!k)
              (merge_along_loop m)
              m' _ _ _ s);
      try done.
    - intros m'' ? <- s' s'' eqs.
      rewrite (bool_decide_iff (k ∈ s') (k ∈ s'')); auto.
    - rewrite bool_decide_false; auto.
      set_solver.
    - intros k' s' m'' notin IH.
      unfold merge_along_loop.
      destruct (decide (k = k')) as [<-|neq].
      + destruct (m!!k).
        * by rewrite lookup_insert, bool_decide_true by set_solver.
        * by rewrite lookup_delete, bool_decide_true by set_solver.
      + rewrite <-(bool_decide_iff (k ∈ s') (k ∈ {[k']} ∪ s')) by set_solver.
        rewrite <- IH.
        destruct (m!!k').
        * by rewrite lookup_insert_ne.
        * by rewrite lookup_delete_ne.
  Qed.

  Lemma lookup_merge_along_in {B} (s: C) (m m': M B) (k: A) (ink: k ∈ s):
    (m ~[s]~> m')!!k = m!!k.
  Proof. by rewrite merge_along_cases, bool_decide_true. Qed.
  Lemma lookup_merge_along_not_in {B} (s: C) (m m': M B) (k: A) (ink: k ∉ s):
    (m ~[s]~> m')!!k = m'!!k.
  Proof. by rewrite merge_along_cases, bool_decide_false. Qed.

  Lemma overlap_merge_along_l {B} (s: C) (m m': M B):
    (m ~[s]~> m') ≡[ s ]≡ m.
  Proof.
    intros k ink.
    rewrite lookup_merge_along_in; done.
  Qed.

  Lemma overlap_merge_along_r {B} (s s': C) (disj: s ⊥ s') (m m': M B):
    (m ~[s]~> m') ≡[ s' ]≡ m'.
  Proof.
    intros k ink.
    rewrite lookup_merge_along_not_in; auto.
    set_solver.
  Qed.
End Facts.

Lemma overlap_cast (s: gset positive) {B} (N N': gmap positive B):
  N ≡[s]≡ N' ↔ N ≡[of_gset s]≡ N'.
Proof.
  unfold overlap.
  setoid_rewrite elem_of_of_gset.
  done.
Qed.
