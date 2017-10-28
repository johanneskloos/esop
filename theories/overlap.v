From mathcomp Require Import ssreflect.
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

Lemma overlap_sub `{Collection A C, FinMap A M} {B}
  (s' s: C) (m m': M B): s ⊆ s' → m ≡[ s' ]≡ m' → m ≡[s]≡ m'.
Proof.
  intros sub.
  apply overlap_mono; done.
Qed.

Lemma overlap_iff `{Collection A C, FinMap A M} {B} (s s': C) (m m' m'': M B)
      (sub: s' ⊆ s) (eqm: m' ≡[ s ]≡ m''):
  m ≡[ s' ]≡ m' ↔ m ≡[ s' ]≡ m''.
Proof.
  enough (m' ≡[ s' ]≡ m'').
  { split; intro; etrans; done. }
  apply (overlap_sub s); done.
Qed.

Definition merge_along_loop `{FinMap A M} {B} (m: M B) k (m': M B) :=
  match m!!k with Some v => <[k:=v]>m' | None => delete k m' end.

Definition merge_along `{FinCollection A C, FinMap A M} {B} (s: C) (m m': M B) :=
  collection_fold (merge_along_loop m) m' s.
Infix "~[ s ]~>" := (merge_along s) (at level 50).

Section Facts.
  Context `{FinCollection A C, FinMap A M}.
  Instance elem_of_dec_C (x: A) (s: C): Decision (x ∈ s) := elem_of_dec_slow x s.

  Lemma lookup_merge_along_cases
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
        * rewrite lookup_insert bool_decide_true; set_solver.
        * rewrite lookup_delete bool_decide_true; set_solver.
      + rewrite <-(bool_decide_iff (k ∈ s') (k ∈ {[k']} ∪ s')) by set_solver.
        rewrite <- IH.
        destruct (m!!k').
        * by rewrite lookup_insert_ne.
        * by rewrite lookup_delete_ne.
  Qed.

  Lemma lookup_merge_along_in {B} (s: C) (m m': M B) (k: A) (ink: k ∈ s):
    (m ~[s]~> m')!!k = m!!k.
  Proof. by rewrite lookup_merge_along_cases bool_decide_true. Qed.
  Lemma lookup_merge_along_not_in {B} (s: C) (m m': M B) (k: A) (ink: k ∉ s):
    (m ~[s]~> m')!!k = m'!!k.
  Proof. by rewrite lookup_merge_along_cases bool_decide_false. Qed.

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

  Global Instance overlap_delete_proper {B} (s: C): Proper (eq ==> overlap s ==> overlap s)
                                                           (delete (M:=M B)).
  Proof.
    intros k ? <- m m' eqm k' ink'.
    destruct (decide (k=k')) as [<-|neq].
    - by rewrite !lookup_delete.
    - rewrite !lookup_delete_ne; auto.
  Qed.
End Facts.

Lemma overlap_cast (s: gset positive) {B} (N N': gmap positive B):
  N ≡[s]≡ N' ↔ N ≡[of_gset s]≡ N'.
Proof.
  unfold overlap.
  setoid_rewrite elem_of_of_gset.
  done.
Qed.

Definition not_new A: coPset := ⊤ ∖ of_gset A.
Lemma elem_of_not_new x A: x ∈ not_new A ↔ x ∉ A.
Proof.
  rewrite /not_new elem_of_difference elem_of_of_gset.
  intuition; split.
Qed.

Lemma good_overlap A A': not_new (A ∪ A') ⊆ not_new A ∩ not_new A'.
Proof.
  intro ξ.
  rewrite /not_new elem_of_intersection !elem_of_difference !elem_of_of_gset
          not_elem_of_union.
  tauto.
Qed.

Lemma overlap_trans {X} A A' (N N' N'': gmap positive X):
  N ≡[not_new A]≡ N' → N' ≡[not_new A']≡ N'' →
  N ≡[not_new (A ∪ A')]≡ N''.
Proof.
  intros ov1 ov2.
  pose proof (good_overlap A A') as ov.
  etrans.
  all: eapply overlap_sub; last eassumption.
  all: clear -ov; set_solver.
Qed.

