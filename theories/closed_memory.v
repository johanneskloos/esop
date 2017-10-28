From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import invariants.
From esop Require Import overlap delayed specification typetranslation types corecalculus.
From stdpp Require Import gmap coPset.

Section Theory.
  Context `{allG Σ}.
  Local Open Scope I.
  Implicit Types x y: string.
  (** Closure: Memory operations *)
  Lemma closed_alloc (x: string) (τ: type) ξ (ξ_fresh: ξ ∉ names τ):
    delayed_typed (<[x:=τ]>∅) hemp (Alloc x) (Alloc x) {[ξ]} (tref ξ) (hpt ξ τ).
  Proof.
    iIntros (D N σ) "[[env_names env] _]".
    iDestruct "env_names" as %[domσ domD].
    assert (is_Some (σ !! x)) as [v val_x].
    { apply domσ; rewrite lookup_insert; eauto. }
    assert (is_Some (D !! var x)) as [d conn_x].
    { apply domD; rewrite lookup_insert; eauto. }
    rewrite /= lookup_fmap val_x /=.
    iApply (wp_wand with "[]").
    { iApply wp_alloc.
      apply to_of_val. }
    iIntros (?) "post".
    iDestruct "post" as (l) "[% mt]"; subst.
    iExists (<[ξ:=Loc l]>N), (<[RET := d]>(<[name ξ := d]>D)), d.
    iSplit.
    { iPureIntro.
      rewrite lookup_insert; repeat split; auto.
      intro n.
      rewrite /not_new elem_of_difference elem_of_of_gset not_elem_of_singleton => [[_ neqξ]].
      rewrite lookup_insert_ne; congruence. }
    iSplit.
    { iPureIntro; exists l; rewrite lookup_insert; auto. }
    iSplitR "mt env".
    { iAlways.
      iIntros (N' σ' p K) "ctx [[env_names env] _] move".
      iDestruct "env_names" as %[domσ' _].
      assert (is_Some (σ' !! x)) as [v' val'_x].
      { apply domσ'; rewrite lookup_insert; eauto. }
      rewrite /= lookup_fmap val'_x /=.
      iMod (simulate_alloc with "ctx move") as (l') "[move post]"; eauto using to_of_val.
      iModIntro; iExists (Cloc l'); iFrame.
      iExists d, (<[ξ:=Loc l']>N').
      iSplit.
      { rewrite lookup_insert; iPureIntro; repeat split; auto.
        intros ξ'.
        rewrite /not_new elem_of_difference elem_of_of_gset not_elem_of_singleton.
        intros [_ neqξ].
        rewrite lookup_insert_ne; done. }
      iSplitR.
      { iExists l'; rewrite lookup_insert; auto. }
      iExists 0; cbn.
      iExists l', d, v'; iFrame.
      rewrite lookup_insert lookup_insert_ne ?lookup_insert; last discriminate.
      iSplit; auto.
      iSpecialize ("env" $! x τ v' d with "[]").
      { rewrite /int_env_data lookup_insert; auto. }
      iApply (int_s_type_local with "env").
      all: try done.
      intros ξ' inξ'.
      rewrite lookup_insert_ne; congruence. }
    { iExists l, d, v; iFrame.
      rewrite !lookup_insert lookup_insert_ne ?lookup_insert; last discriminate.
      iSplit; auto.
      iSpecialize  ("env" $! x τ v d with "[]").
      { rewrite /int_env_data lookup_insert; auto. }
      iApply (int_i_type_local with "env").
      all: try done.
      intros ξ' inξ'.
      rewrite lookup_insert_ne; congruence. }
  Qed.

  Lemma int_s_heap_pt ξ τ D N:
    int_s_heap (hpt ξ τ) D N ⊣⊢ int_s_heap_rec 0 (hpt ξ τ) D N.
  Proof.
    iSplit.
    - iIntros "pre".
      iDestruct "pre" as ([|n]) "pre"; auto.
    - iIntros "pre".
      iExists 0; done.
  Qed.
  
  Lemma closed_read x ξ τ:
    delayed_typed (<[x:=tref ξ]>∅) (hpt ξ τ) (Read x) (Read x) ∅ τ (hpt ξ τ).
  Proof.
    iIntros (D N σ) "[[env_names env] pt]".
    iDestruct "env_names" as %[domσ domD].
    assert (is_Some (σ !! x)) as [v val_x].
    { apply domσ; rewrite lookup_insert; eauto. }
    assert (is_Some (D !! var x)) as [d conn_x].
    { apply domD; rewrite lookup_insert; eauto. }
    rewrite /= lookup_fmap val_x /=.
    iDestruct ("env" $! x (tref ξ) v d with "[]") as %[l [ref ->]].
    { rewrite /int_env_data lookup_insert; auto. }
    iDestruct "pt" as (l' d' v') "[eqs [mt #val]]".
    iDestruct "eqs" as %[ref' eqd].
    rewrite ref in ref'; injection ref' as <-.
    iApply (wp_wand with "[mt]").
    { iApply (wp_read with "mt"). }
    iIntros (v) "[% mt]"; subst v'.
    iExists N, (<[RET:=d']>D), d'.
    iFrame.
    rewrite lookup_insert.
    iSplit; auto.
    iSplit; auto.
    iSplitR.
    { iClear "val".
      clear v l val_x ref N domσ σ.
      iAlways.
      iIntros (N σ p K) "ctx [[env_names env] pt] move".
      iDestruct "env_names" as %[domσ _].
      assert (is_Some (σ !! x)) as [v val_x].
      { apply domσ; rewrite lookup_insert; eauto. }
      rewrite /= lookup_fmap val_x /=.
      iDestruct ("env" $! x (tref ξ) v d with "[]") as "ref".
      { rewrite /int_env_data lookup_insert; auto. }
      iDestruct "ref" as %[l [ref ->]].
      rewrite int_s_heap_pt.
      iDestruct "pt" as (l' d'' v) "[eqs [pt #type]]".
      iDestruct "eqs" as %[eql eqd'].
      rewrite ref in eql; injection eql as <-.
      rewrite eqd in eqd'; injection eqd' as <-.
      iMod (simulate_read with "ctx move pt") as "[move pt]"; auto.
      iModIntro.
      iExists v; iFrame.
      iExists d', N.
      rewrite lookup_insert.
      iSplit; first done.
      iSplit; first done.
      rewrite int_s_heap_pt.
      iExists l, d', v; iFrame; iSplit; auto.
      rewrite lookup_insert_ne; auto. }
    { iExists l, d', v; iFrame; iSplit; auto.
      rewrite lookup_insert_ne; auto. }
  Qed.

  Lemma closed_write x y ξ τ (neq: x ≠ y):
    delayed_typed (<[x:=tref ξ]>(<[y:=τ]>∅)) (hpt ξ τ) (Write x y) (Write x y) ∅ tunit (hpt ξ τ).
  Proof.
    iIntros (D N σ) "[[env_names #env] pt]".
    iDestruct "env_names" as %[domσ domD].
    assert (is_Some (σ !! x)) as [v val_x].
    { apply domσ; rewrite lookup_insert; eauto. }
    assert (is_Some (D !! var x)) as [d conn_x].
    { apply domD; rewrite lookup_insert; eauto. }
    rewrite /= lookup_fmap val_x /=.
    assert (is_Some (σ !! y)) as [w val_y].
    { apply domσ; rewrite lookup_insert_ne ?lookup_insert; eauto. }
    assert (is_Some (D !! var y)) as [d' conn_y].
    { apply domD; rewrite lookup_insert_ne ?lookup_insert; eauto. }
    rewrite /= lookup_fmap val_y /=.
    iDestruct "pt" as (l' dl v') "[eqs [mt #val]]".
    iDestruct "eqs" as %[ref' eqd].
    iDestruct ("env" $! x (tref ξ) v d with "[]") as %[l [ref ->]].
    { rewrite /int_env_data lookup_insert; auto. }
    rewrite ref in ref'; injection ref' as <-.
    iPoseProof (wp_write ⊤ l (of_val w) w with "[mt]") as "wp".
    { apply to_of_val. }
    { iExists v'; iFrame. }
    iApply (wp_wand with "wp").
    iIntros (?) "[% mt]"; subst.
    iExists N, (<[RET:=VConst Cunit]>(<[name ξ := d']>D)), Cunit.
    rewrite lookup_insert.
    iSplit; auto.
    iSplit; auto.
    iSplitR "mt".
    {     iClear "env".
          iAlways.
          iIntros (N' σ' p K) "ctx [[env_names #env] pt] move".
          iDestruct "env_names" as %[domσ' _].
          assert (is_Some (σ' !! x)) as [u val'_x].
          { apply domσ'; rewrite lookup_insert; eauto. }
          rewrite /= lookup_fmap val'_x /=.
          assert (is_Some (σ' !! y)) as [w' val'_y].
          { apply domσ'; rewrite lookup_insert_ne ?lookup_insert; eauto. }
          rewrite lookup_fmap val'_y /=.
          iDestruct ("env" $! x (tref ξ) u d with "[]") as %[l' [ref' ->]].
          { rewrite /int_env_data lookup_insert; auto. }
          rewrite int_s_heap_pt /= /int_s_pt.
          iDestruct "pt" as (l'' d'' u') "[eqs [pt _]]".
          iDestruct "eqs" as %[eql'' eqd''].
          rewrite ref' in eql''; injection eql'' as <-.
          rewrite eqd in eqd''; injection eqd'' as <-.
          iMod (simulate_write with "ctx move [pt]") as "[move pt]".
          1,2: eauto using to_of_val.
          { iExists u'; iFrame. }
          iModIntro; iExists Cunit; iFrame.
          iExists Cunit, N'.
          rewrite lookup_insert.
          iSplit; auto.
          iSplit; first done.
          rewrite int_s_heap_pt.
          iExists l', d', w'; iFrame.
          rewrite lookup_insert_ne ?lookup_insert; last done.
          iSplit; first done.
          iApply ("env" $! y).
          rewrite /int_env_data lookup_insert_ne ?lookup_insert; last done.
          auto. }
    { iExists l, d', w.
      iFrame.
      rewrite lookup_insert_ne ?lookup_insert; last auto.
      iSplit; auto.
      iApply ("env" $! y τ w d').
      rewrite /int_env_data lookup_insert_ne; last done.
      rewrite lookup_insert; auto. }
  Qed.
End Theory.