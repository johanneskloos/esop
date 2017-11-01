From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import invariants.
From esop Require Import overlap delayed specification typetranslation types corecalculus.
From stdpp Require Import gmap coPset.

Section Theory.
  Context `{allG Σ}.
  (** Closure: variables. *)
  Lemma closed_variable (x: string) τ:
    delayed_typed (<[x:=τ]>∅) hemp x x ∅ τ hemp.
  Proof.
    iIntros (D N σ) "[[env_names env] _]".
    iDestruct "env_names" as %[domσ domD].
    assert (is_Some (σ !! x)) as [v val_x].
    { apply domσ; rewrite lookup_insert; eauto. }
    assert (is_Some (D !! var x)) as [d conn_x].
    { apply domD; rewrite lookup_insert; eauto. }
    rewrite /= lookup_fmap val_x /=.
    iApply wp_value'.
    iExists N, (<[RET:=d]>D), d.
    rewrite /int_i_emp; iFrame.
    iSplit.
    { rewrite lookup_insert; auto. }
    iSplitL "env".
    { iApply ("env" $! x τ v d).
      iPureIntro; split; auto.
      apply lookup_insert. }
    iSplit; auto.
    iAlways.
    iIntros (N' σ' p K) "ctx [[env_names env] heap] move".
    iDestruct "env_names" as %[domσ' _].
    assert (is_Some (σ' !! x)) as [v' val'_x].
    { apply domσ'; rewrite lookup_insert; eauto. }
    rewrite /= lookup_fmap val'_x /=.
    iModIntro; iExists v'; iFrame.
    iExists d, N'.
    rewrite lookup_insert.
    iSplit; auto.
    iSplitL "env".
    - iApply ("env" $! x τ v' d).
      rewrite /int_env_data lookup_insert; auto.
    - by iExists 0.
  Qed.

  (** Closure: constants. *)
  Lemma closed_true: delayed_typed ∅ hemp Ctrue Ctrue ∅ tbool hemp.
  Proof.
    iIntros (D N σ) "_".
    change (Const Ctrue) with (of_val (VConst Ctrue)).
    rewrite subst_closed_empty; last by apply val_closed.
    iApply wp_value'.
    iExists N, (<[RET:=VConst Ctrue]>D), (VConst Ctrue).
    rewrite lookup_insert; iSplit; auto.
    iSplit.
    { iPureIntro; auto. }
    iSplit; auto.
    iAlways.
    iIntros (N' σ' p K) "ctx _ move".
    iModIntro.
    iExists Ctrue.
    rewrite subst_val; iFrame.
    iExists Ctrue, N'.
    rewrite lookup_insert; iSplit; auto.
    iSplit.
    - iPureIntro; auto.
    - by iExists 0.
  Qed.

  Lemma closed_false: delayed_typed ∅ hemp Cfalse Cfalse ∅ tbool hemp.
  Proof.
    iIntros (D N σ) "_".
    change (Const Cfalse) with (of_val (VConst Cfalse)).
    rewrite subst_closed_empty; last by apply val_closed.
    iApply wp_value'.
    iExists N, (<[RET:=VConst Cfalse]>D), (VConst Cfalse).
    rewrite lookup_insert; iSplit; auto.
    iSplit.
    { iPureIntro; auto. }
    iSplit; auto.
    iAlways.
    iIntros (N' σ' p K) "ctx _ move".
    iModIntro.
    iExists Cfalse.
    rewrite subst_val; iFrame.
    iExists Cfalse, N'.
    rewrite lookup_insert; iSplit; auto.
    iSplit.
    - iPureIntro; auto.
    - by iExists 0.
  Qed.

  Lemma closed_unit: delayed_typed ∅ hemp Cunit Cunit ∅ tunit hemp.
  Proof.
    iIntros (D N σ) "_".
    change (Const Cunit) with (of_val (VConst Cunit)).
    rewrite subst_closed_empty; last by apply val_closed.
    iApply wp_value'.
    iExists N, (<[RET:=VConst Cunit]>D), (VConst Cunit).
    rewrite lookup_insert; iSplit; auto.
    iSplit.
    { iPureIntro; auto. }
    iSplit; auto.
    iAlways.
    iIntros (N' σ' p K) "ctx _ move".
    iModIntro.
    iExists Cunit.
    rewrite subst_val; iFrame.
    iExists Cunit, N'.
    rewrite lookup_insert; iSplit; auto.
    iSplit.
    - iPureIntro; auto.
    - by iExists 0.
  Qed.

    
  (** Closure: If *)
  Implicit Types x y: string.
  Lemma closed_if x Γ η A τ η' e₁ e₁' e₂ e₂' (x_type: Γ !! x = Some tbool):
    delayed_typed Γ η e₁ e₁' A τ η' -∗
                  delayed_typed Γ η e₂ e₂' A τ η' -∗
                  delayed_typed Γ η (If x e₁ e₂) (If x e₁' e₂') A τ η'.
  Proof.
    iIntros "dtt dtf".
    iIntros (D N σ) "[#env pre]".
    iPoseProof ("env") as "[env_names env_types]".
    iDestruct "env_names" as %[domσ domD].
    assert (is_Some (σ !! x)) as [v val_x].
    { apply domσ; rewrite x_type; eauto. }
    assert (is_Some (D !! var x)) as [d conn_x].
    { apply domD; rewrite x_type; eauto. }
    rewrite /= lookup_fmap val_x /=.
    iDestruct ("env_types" $! x tbool v d with "[]") as %[[->| ->] <-]; first auto.
    { iApply wp_if_true.
      iSpecialize ("dtt" $! D N σ with "[$env $pre]").
      iApply (wp_wand with "dtt").
      iClear "env env_types dtf".
      iIntros (v) "post".
      iDestruct "post" as (N' D' d') "[names [ty [#sim heap]]]".
      iExists N', D', d'; iFrame.
      clear N N' d' domσ σ val_x v.
      iAlways.
      iIntros (N σ p K) "#ctx [#env pre] move".
      iPoseProof ("env") as "[env_names env_types]".
      iDestruct "env_names" as %[domσ _].
      assert (is_Some (σ !! x)) as [v val_x].
      { apply domσ; rewrite x_type; eauto. }
      iDestruct ("env_types" $! x tbool v Ctrue with "[]") as %[_ ->]; first auto.
      rewrite /= lookup_fmap val_x /=.
      iMod (simulate_if_true with "ctx move") as "move"; first auto.
      iApply ("sim" with "ctx [$env $pre] move").
    }{
      iApply wp_if_false.
      iSpecialize ("dtf" $! D N σ with "[$env $pre]").
      iApply (wp_wand with "dtf").
      iClear "env env_types dtt".
      iIntros (v) "post".
      iDestruct "post" as (N' D' d') "[names [ty [#sim heap]]]".
      iExists N', D', d'; iFrame.
      clear N N' d' domσ σ val_x v.
      iAlways.
      iIntros (N σ p K) "#ctx [#env pre] move".
      iPoseProof ("env") as "[env_names env_types]".
      iDestruct "env_names" as %[domσ _].
      assert (is_Some (σ !! x)) as [v val_x].
      { apply domσ; rewrite x_type; eauto. }
      iDestruct ("env_types" $! x tbool v Cfalse with "[]") as %[_ ->]; first auto.
      rewrite /= lookup_fmap val_x /=.
      iMod (simulate_if_false with "ctx move") as "move"; first auto.
      iApply ("sim" with "ctx [$env $pre] move").
    }
  Qed.

  (** Closure: Let *)
  Lemma closed_let x y Γ η A τ τ' η' e e' (x_type: Γ !! x = Some τ):
    delayed_typed (<[y:= τ]> Γ) η e e' A τ' η' -∗
                  delayed_typed Γ η (Let (BNamed y) x e) (Let (BNamed y) x e') A τ' η'.
  Proof.
    iIntros "del".
    iIntros (D N σ) "[#env pre]".
    iPoseProof ("env") as "[env_names env_types]".
    iDestruct "env_names" as %[domσ domD].
    assert (is_Some (σ !! x)) as [v val_x].
    { apply domσ; rewrite x_type; eauto. }
    assert (is_Some (D !! var x)) as [d conn_x].
    { apply domD; rewrite x_type; eauto. }
    rewrite /= lookup_fmap val_x /=.
    iApply wp_app; first apply to_of_val.
    rewrite /=.
    rewrite subst_subst; cycle 1.
    { intros x' e''.
      rewrite lookup_delete_Some lookup_fmap fmap_Some => [[_ [v' [_ ->]]]].
      apply val_closed. }
    replace (subst_merge (<[y:=of_val v]> ∅) (delete y (of_val <$> σ)))
    with (of_val <$> <[y:=v]>σ); cycle 1.
    { apply map_eq; intro z.
      rewrite /subst_merge lookup_merge /subst_merge'.
      destruct (decide (y=z)) as [<-|neq].
      - by rewrite lookup_delete lookup_fmap !lookup_insert.
      - rewrite lookup_fmap !lookup_delete_ne; last done.
        rewrite !lookup_insert_ne; auto.
        rewrite lookup_empty lookup_fmap.
        destruct (σ !! z) as [w|]; cbn; trivial.
        rewrite subst_val; trivial. }
    iSpecialize ("del" $! (<[var y := d]>D) N (<[y:=v]> σ) with "[env pre]").
    { iSplit; first iSplit.
      - iPureIntro; rewrite /int_env_doms.
        setoid_rewrite lookup_insert_is_Some.
        split; first by setoid_rewrite domσ.
        intros z [eqy|[??]]; subst; auto.
        destruct (decide (var y = var z)); auto.
      - iIntros (x' τ'' v' d' [mtτ [mtv mtd]]).
        destruct (decide (y = x')) as [<-|neq].
        + rewrite lookup_insert in mtd; injection mtd as <-.
          rewrite lookup_insert in mtv; injection mtv as <-.
          rewrite lookup_insert in mtτ; injection mtτ as <-.
          iApply ("env_types" $! x); auto.
        + rewrite lookup_insert_ne in mtd; last congruence.
          rewrite lookup_insert_ne in mtv; last congruence.
          rewrite lookup_insert_ne in mtτ; last congruence.
          iApply ("env_types" $! x'); auto.
      - iApply (int_i_heap_local with "pre").
        2,3: done.
        intro n.
        rewrite elem_of_conn_heap.
        intros [ξ [-> _]].
        apply lookup_insert_ne; done. }
    iApply (wp_wand with "del").
    iIntros (w) "post".
    iDestruct "post" as (N' D' d') "[eqs [ty [#sim heap]]]".
    iExists N', D', d'; iFrame.
    iClear "env env_types".
    clear v val_x N' d' w σ domσ N.
    iAlways.
    iIntros (N σ p K) "#ctx [#env pre] move".
    cbn -[difference].
    iPoseProof ("env") as "[env_names env_types]".
    iDestruct "env_names" as %[domσ _].
    assert (is_Some (σ !! x)) as [v val_x].
    { apply domσ; rewrite x_type; eauto. }
    rewrite /= lookup_fmap val_x /=.
    iMod (simulate_app with "ctx move") as "move"; eauto using to_of_val.
    rewrite /= subst_subst; cycle 1.
    { intros x' e''.
      rewrite lookup_delete_Some lookup_fmap fmap_Some => [[_ [v' [_ ->]]]].
      apply val_closed. }
    replace (subst_merge (<[y:=of_val v]> ∅) (delete y (of_val <$> σ)))
    with (of_val <$> <[y:=v]>σ); cycle 1.
    { apply map_eq; intro z.
      rewrite /subst_merge lookup_merge /subst_merge'.
      destruct (decide (y=z)) as [<-|neq].
      - by rewrite lookup_delete lookup_fmap !lookup_insert.
      - rewrite lookup_fmap !lookup_delete_ne; last done.
        rewrite !lookup_insert_ne; auto.
        rewrite lookup_empty lookup_fmap.
        destruct (σ !! z) as [w|]; cbn; trivial.
        rewrite subst_val; trivial. }
    iSpecialize ("sim" $! N (<[y:=v]> σ) with "ctx [env pre]").
    { iSplit; first iSplit.
      - iPureIntro; rewrite /int_env_doms.
        setoid_rewrite lookup_insert_is_Some.
        split; first by setoid_rewrite domσ.
        intros z [eqy|[??]]; subst; auto.
        destruct (decide (var y = var z)); auto.
      - iIntros (x' τ'' v' d' [mtτ [mtv mtd]]).
        destruct (decide (y = x')) as [<-|neq].
        + rewrite lookup_insert in mtd; injection mtd as <-.
          rewrite lookup_insert in mtv; injection mtv as <-.
          rewrite lookup_insert in mtτ; injection mtτ as <-.
          iApply ("env_types" $! x); auto.
        + rewrite lookup_insert_ne in mtd; last congruence.
          rewrite lookup_insert_ne in mtv; last congruence.
          rewrite lookup_insert_ne in mtτ; last congruence.
          iApply ("env_types" $! x'); auto.
      - iApply (int_s_heap_local with "pre").
        2,3: done.
        intro n.
        rewrite elem_of_conn_heap.
        intros [ξ [-> _]].
        apply lookup_insert_ne; done. }
    iApply "sim"; auto.
  Qed.

  Lemma closed_let_anon x Γ η A τ τ' η' e e' (x_type: Γ !! x = Some τ):
    delayed_typed Γ η e e' A τ' η' -∗
                  delayed_typed Γ η (Let BAnon x e) (Let BAnon x e') A τ' η'.
  Proof.
    iIntros "del".
    iIntros (D N σ) "[#env pre]".
    iPoseProof ("env") as "[env_names env_types]".
    iDestruct "env_names" as %[domσ domD].
    assert (is_Some (σ !! x)) as [v val_x].
    { apply domσ; rewrite x_type; eauto. }
    assert (is_Some (D !! var x)) as [d conn_x].
    { apply domD; rewrite x_type; eauto. }
    rewrite /= lookup_fmap val_x /=.
    iApply wp_app; first apply to_of_val.
    rewrite /=.
    iSpecialize ("del" $! D N σ with "[$env $pre]").
    iApply (wp_wand with "del").
    iIntros (w) "post".
    iDestruct "post" as (N' D' d') "[eqs [ty [#sim heap]]]".
    iExists N', D', d'; iFrame.
    iClear "env env_types".
    clear v val_x N' d' w σ domσ N.
    iAlways.
    iIntros (N σ p K) "#ctx [#env pre] move".
    cbn -[difference].
    iPoseProof ("env") as "[env_names env_types]".
    iDestruct "env_names" as %[domσ _].
    assert (is_Some (σ !! x)) as [v val_x].
    { apply domσ; rewrite x_type; eauto. }
    rewrite /= lookup_fmap val_x /=.
    iMod (simulate_app with "ctx move") as "move"; eauto using to_of_val.
    iSpecialize ("sim" $! N σ with "ctx [$env $pre]").
    iApply "sim"; auto.
  Qed.
End Theory.