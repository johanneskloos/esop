From stdpp Require Import strings gmap fin_collections pretty.
From mathcomp Require Import ssreflect.

Section General.
  Context `{FinCollection A C}.
  Definition set_recursion {B} (f: ∀ c, (∀ c', c' ⊂ c → B) → B) (c: C): B :=
    Fix collection_wf (const B) f c.

  Lemma set_recursion_unfold {B} (f: ∀ c, (∀ c', c' ⊂ c → B) → B)
        (f_proper: ∀ x g g', (∀ c' H, g c' H = g' c' H) → f x g = f x g')
        c:
    set_recursion f c = f c (λ c' _, set_recursion f c').
  Proof. rewrite /set_recursion {1}Fix_eq //. Qed.

  Lemma set_recursion_unfold' {B} (eqB: Equiv B) (f: ∀ c, (∀ c', c' ⊂ c → B) → B)
        (f_proper: ∀ x g g', (∀ c' H, g c' H ≡ g' c' H) → f x g ≡ f x g')
        c:
    set_recursion f c ≡ f c (λ c' _, set_recursion f c').
  Proof.
    unfold set_recursion, Fix.
    destruct (collection_wf c); cbn.
    apply f_proper.
    intros c' subc.
    generalize (a c' subc) as acc, (collection_wf c') as acc'.
    clear c subc a.
    induction c' as [c IH] using (well_founded_ind collection_wf).
    intros [acc] [acc']; cbn.
    apply: f_proper => [c' sub].
    apply IH, sub.
  Qed.

  Lemma subset_difference_in {x: A} {s: C} (inx: x ∈ s): s ∖ {[ x ]} ⊂ s.
  Proof. set_solver. Qed.
End General.

Section FreshString.
  Context `{FinCollection string C} `{InDec: ∀ (x: string) (s: C), Decision (x ∈ s)} (prefix: string).

  Definition cand (n: N) := prefix +:+ pretty n.
  Definition find_fresh_string (s: C) n :=
    set_recursion (λ (c: C) rec (n: N),
                   let x := cand n in
                   match decide (x ∈ c) return string with
                   | left H => rec (c ∖ {[ x ]}) (subset_difference_in H) (1+n)%N
                   | right _ => x
                   end) s n.
  Lemma find_fresh_string_spec c: ∀ n, ∃ m,
        find_fresh_string c n = cand m ∧
        (n ≤ m)%N ∧
        cand m ∉ c ∧
        ∀ i, (n ≤ i < m)%N → cand i ∈ c.
  Proof.
    unfold find_fresh_string.
    induction c as [c IH] using (well_founded_ind collection_wf).
    intro.
    rewrite (set_recursion_unfold' (pointwise_relation N eq)).
    2: intros * eqg i; destruct decide; auto; apply eqg.
    destruct decide as [case|case].
    - destruct (IH _ (subset_difference_in case) (1+n)%N) as [m [eqrec [bound [notin inlow]]]].
      exists m; repeat (split; auto).
      + lia.
      + contradict notin.
        rewrite elem_of_difference; split; auto.
        rewrite elem_of_singleton /cand.
        intros ?%string_app_inj%pretty_N_inj; lia.
      + intros i [lb ub].
        destruct (decide (i = n)) as [<-|neq]; auto.
        enough (cand i ∈ c ∖ {[ cand n ]}) as [??]%elem_of_difference by done.
        apply inlow; lia.
    - exists n; repeat split; auto.
      intros; lia.
  Qed.
End FreshString.

Instance fresh_string `{FinCollection string C} `{InDec: ∀ (x: string) (s: C), Decision (x ∈ s)}:
  Fresh string C := λ c, find_fresh_string "~" c 0%N.
Instance fresh_string_spec `{FinCollection string C} `{InDec: ∀ (x: string) (s: C), Decision (x ∈ s)}:
  FreshSpec string C.
Proof.
  split.
  - apply _.
  - intros * eqXY.
    pose proof (find_fresh_string_spec "~" X 0%N) as specX.
    pose proof (find_fresh_string_spec "~" Y 0%N) as specY.
    unfold fresh, fresh_string.
    destruct specX as [mX [-> [_ [notinX inX]]]].
    destruct specY as [mY [-> [_ [notinY inY]]]].
    destruct (N.lt_trichotomy mX mY) as [case|[->|case]].
    2: done.
    + contradict notinX.
      rewrite eqXY.
      apply inY; lia.
    + contradict notinY.
      rewrite -eqXY.
      apply inX; lia.
  - intros.
    unfold fresh, fresh_string.
    destruct (find_fresh_string_spec "~" X 0%N) as [m [-> [_ [? _]]]]; auto.
Qed.
