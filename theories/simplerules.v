From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import invariants.
From esop Require Import corecalculus types delayed closed_meta closure typetranslation
     specification overlap contexttypes exprfacts.
From stdpp Require Import gmap coPset.

Section SimpleRules.
  Context `{allG Σ}.
  Local Open Scope I.
  
  Lemma sound_asynchronise U Γ e η A τ η' ξ:
    names Γ ⊆ U →
    heap_wf U η →
    ξ ∉ U →
    ξ ∉ A →
    heap_wf (U ∪ {[ξ]}) (hwait ξ A η') →
    typing U Γ e η A τ η' →
    delayed_simulation U Γ η (Wait (Post e)) e ({[ξ]} ∪ A) τ η'.
  Proof.
    intros goodΓ wfη ξ_fresh ξ_not_A wtwait ty.
    destruct (typing_good_names _ _ _ _ _ _ _ ty) as [disj [subτ subη]]; auto using heap_wf_names.
    split; auto.
    - apply union_least; auto using heap_wf_names.
    - rewrite -(left_id hemp hstar η').
      eapply tywait.
      6: rewrite left_id; constructor; auto.
      + inversion_clear wtwait.
        rewrite left_id //.
      + apply typing_good_names in ty; auto using heap_wf_names.
      + by intros [?|?]%subτ%elem_of_union.
      + by intros [?|?]%subη%elem_of_union.
      + by apply disjoint_singleton_l.
      + rewrite not_elem_of_union; auto.
    - eapply tyweaken; last done.
      1,2,4,5: auto using heap_wf_names.
      + rewrite disjoint_union_r disjoint_singleton_r; auto.
      + apply union_subseteq_r.
      + inversion_clear wtwait.
        rewrite union_comm_L union_assoc_L //.
    - iIntros (D N σ) "pre".
      rewrite /=.
      iApply (wp_bind [CWait]).
      apply fundamental in ty; auto.
      destruct ty as [_ _ _ ty].
      iPoseProof (ty $! D N σ with "pre") as "del".
      iPoseProof (wp_post ⊤ (subst (of_val <$> σ) e)
                          (λ _ v, ∃ N' D' d',
                              ⌜N ≡[ not_new A ]≡ N' ∧ D' !! RET = Some d'⌝ ∧
                              int_i_type τ d' N' v ∧
                              □simulation Γ e η A τ η' D D' ∧
                              int_i_heap η' D' N')
                          (TaskData e Γ η η ∅ ∅ ξ ξ) with "[del]")
        as "post".
      { by iIntros (t) "_". }
      iApply (wp_wand with "post").
      iIntros (v) "post".
      iDestruct "post" as (t) "[% [wait _]]".
      cbn -[union not_new]; subst.
      iPoseProof (wp_wait with "[$wait]") as "wait".
      iApply (wp_wand with "wait").
      iIntros (v) "post".
      iDestruct "post" as (N' D' d') "[names [type [#sim heap]]]".
      iDestruct "names" as %[eqN eqD'].
      iExists N', D', d'; iFrame.
      iSplit.
      + iPureIntro; split; auto.
        eapply overlap_sub; last done.
        intro; rewrite !elem_of_not_new not_elem_of_union; tauto.
      + iAlways.
        clear N N' eqN σ v.
        iIntros (N σ p K) "ctx pre move".
        iMod ("sim" with "ctx pre move") as (v) "[post move]".
        iModIntro.
        iExists v; iFrame.
        iDestruct "post" as (d N') "[names post]".
        iExists d, N'; iFrame.
        iDestruct "names" as %[eqN eqD].
        iPureIntro; split; auto.
        eapply overlap_sub; last done.
        intro; rewrite !elem_of_not_new not_elem_of_union; tauto.
  Qed.

  Coercion BNamed: string >-> binder.

  Lemma fill_ctx_fill_ectx K e: fill_ctx e K = fill_ectx e (to_ectx K).
  Proof.
    revert e.
    induction K as [|I K IH]; first done.
    destruct I; intro; rewrite /= IH //.
  Qed.

  Lemma to_ectx_app K K': to_ectx (K++K') = to_ectx K ++ to_ectx K'.
  Proof. rewrite /to_ectx fmap_app //. Qed.

  Lemma typing_subst:
    ∀ (U : gset lname) (Γ : env) (e : expr) (η₁ : hexpr) (A₁ : lnames) (τ₁ : type) 
      (η₂ : hexpr) (x : string) (K : list ctx_item) (A₂ : lnames) (τ₂ : type) 
      (η₃ : hexpr),
      typing U Γ e η₁ A₁ τ₁ η₂
      → typing (U ∪ A₁) (<[x:=τ₁]> Γ) (fill_ctx x K) η₂ A₂ τ₂ η₃
      → typing U Γ (fill_ctx e K) η₁ (A₁ ∪ A₂) τ₂ η₃.
  Proof.
    intros U Γ e η₁ A₁ τ₁ η₂ x K A₂ τ₂ η₃ tye tyK.
  Admitted.
  
  Lemma sound_to_anf U Γ e η₁ A₁ τ₁ η₂ (x: string) K A₂ τ₂ η₃:
    (∀ e', subst_ctx (<[x:=e']>∅) K = K) →
    names Γ ⊆ U →
    heap_wf U η₁ →
    typing U Γ e η₁ A₁ τ₁ η₂ →
    typing (U ∪ A₁) (<[x:=τ₁]>Γ) (fill_ctx x K) η₂ A₂ τ₂ η₃ →
    delayed_simulation U Γ η₁ (Let x e (fill_ctx x K)) (fill_ctx e K) (A₁ ∪ A₂) τ₂ η₃.
  Proof.
    intros x_not_in_K goodΓ wfη₁ tye tyK.
    split.
    { apply union_least; auto using heap_wf_names. }
    { by eapply tylet. }
    { by eapply typing_subst. }
    rewrite (fill_ctx_fill_ectx K e).
    iApply (delayed_bind_strong x e e [EAppR (Rec BAnon x (fill_ctx x K))] (to_ectx K)); cbn.
    { intro; rewrite delete_insert; last apply lookup_empty. rewrite subst_empty //. }
    { intro; rewrite subst_ectx_to_ectx x_not_in_K //. }
    { repeat constructor.
      apply typing_closed in tyK.
      rewrite dom_insert in tyK *.
      rewrite /= left_id //. }
    { clear.
      pose proof (to_ectx_reduced K) as red.
      induction red; constructor; auto.
      destruct H; constructor; auto.
      all: eapply reduced_mono; last done.
      all: apply empty_subseteq. }
    { by apply fundamental in tye. }
    assert (names (<[x:=τ₁]>Γ) ⊆ U ∪ A₁) as subenv.
    { apply typing_good_names in tye; auto using heap_wf_names.
      etrans; first apply names_env_insert.
      apply union_least; first tauto.
      etrans; first done.
      apply union_subseteq_l. }
    assert (heap_wf (U ∪ A₁) η₂) as wfη₂ by by eapply typing_wf.
    split.
    { apply typing_good_names in tye; auto using heap_wf_names.
      destruct tye as [disjA₁ [namesτ namesη]]; by apply union_least. }
    { rewrite -(union_empty_l_L A₂).
      eapply tylet; last by rewrite union_empty_r_L /= insert_insert.
      apply type_var_string; auto.
      apply lookup_insert. }
    { by rewrite -fill_ctx_fill_ectx. }
    apply fundamental in tyK; auto.
    destruct tyK as [_ tyK _ simK].
    iIntros (D N σ) "[#env pre]".
    iPoseProof "env" as "[#names #ty]".
    iDestruct "names" as %[domσ domD].
    assert (is_Some (σ !! x)) as [v val_x].
    { rewrite -domσ lookup_insert; eauto. }    
    rewrite /= lookup_fmap val_x /=.
    iApply wp_app; first apply to_of_val.
    rewrite /= subst_subst.
    2: intros x' e'; rewrite lookup_delete_Some lookup_fmap fmap_Some => [[_ [v' [_ ->]]]].
    2: apply val_closed.
    assert (subst_merge (<[x:=of_val v]>∅) (delete x (of_val <$> σ)) = of_val <$> σ)
      as ->.
    { apply map_eq; intro y.
      rewrite /subst_merge lookup_merge /subst_merge' lookup_fmap.
      destruct (decide (x = y)) as [<-|neq].
      - rewrite lookup_delete !lookup_insert val_x //.
      - rewrite lookup_delete_ne // !lookup_insert_ne // lookup_fmap.
        destruct (σ !! y) as [v'|] eqn:mt.
        + rewrite /= subst_val //.
        + rewrite /= lookup_empty //. }
    iPoseProof (simK $! D N σ with "[$pre $env]") as "sim".
    iApply (wp_wand with "sim").
    iIntros (v') "post".
    iDestruct "post" as (N' D' d') "[names [ty' [#sim post]]]".
    iExists N', D', d'; iFrame.
    iAlways.
    iClear "env ty".
    clear N N' v val_x v' domσ σ.
    iIntros (N σ p K') "ctx pre move".
    iApply ("sim" with "ctx pre [move]").
    rewrite fill_ctx_fill_ectx //.
  Qed.

  Lemma sound_from_anf U Γ e η₁ A₁ τ₁ η₂ (x: string) K A₂ τ₂ η₃:
    (∀ e', subst_ctx (<[x:=e']>∅) K = K) →
    names Γ ⊆ U →
    heap_wf U η₁ →
    typing U Γ e η₁ A₁ τ₁ η₂ →
    typing (U ∪ A₁) (<[x:=τ₁]>Γ) (fill_ctx x K) η₂ A₂ τ₂ η₃ →
    delayed_simulation U Γ η₁ (fill_ctx e K) (Let x e (fill_ctx x K)) (A₁ ∪ A₂) τ₂ η₃.
  Proof.
    intros x_not_in_K goodΓ wfη₁ tye tyK.
    split.
    { apply union_least; auto using heap_wf_names. }
    { by eapply typing_subst. }
    { by eapply tylet. }
    rewrite (fill_ctx_fill_ectx K e).
    iApply (delayed_bind_strong x e e (to_ectx K) [EAppR (Rec BAnon x (fill_ctx x K))]); cbn.
    { intro; rewrite subst_ectx_to_ectx x_not_in_K //. }
    { intro; rewrite delete_insert; last apply lookup_empty. rewrite subst_empty //. }
    { clear.
      pose proof (to_ectx_reduced K) as red.
      induction red; constructor; auto.
      destruct H; constructor; auto.
      all: eapply reduced_mono; last done.
      all: apply empty_subseteq. }
    { repeat constructor.
      apply typing_closed in tyK.
      rewrite dom_insert in tyK *.
      rewrite /= left_id //. }
    { by apply fundamental in tye. }
    assert (names (<[x:=τ₁]>Γ) ⊆ U ∪ A₁) as subenv.
    { apply typing_good_names in tye; auto using heap_wf_names.
      etrans; first apply names_env_insert.
      apply union_least; first tauto.
      etrans; first done.
      apply union_subseteq_l. }
    assert (heap_wf (U ∪ A₁) η₂) as wfη₂ by by eapply typing_wf.
    split.
    { apply typing_good_names in tye; auto using heap_wf_names.
      destruct tye as [disjA₁ [namesτ namesη]]; by apply union_least. }
    { by rewrite -fill_ctx_fill_ectx. }
    { rewrite -(union_empty_l_L A₂).
      eapply tylet; last by rewrite union_empty_r_L /= insert_insert.
      apply type_var_string; auto.
      apply lookup_insert. }
    apply fundamental in tyK; auto.
    destruct tyK as [_ tyK _ simK].
    iIntros (D N σ) "[#env pre]".
    iPoseProof (simK $! D N σ with "[$env $pre]") as "sim".
    rewrite fill_ctx_fill_ectx.
    iApply (wp_wand with "sim").
    iIntros (v) "post".
    iDestruct "post" as (N' D' d') "[names [type [#sim post]]]".
    iExists N', D', d'; iFrame.
    iClear "env"; clear N σ v N' d'.
    iAlways.
    iIntros (N σ p K') "#ctx [#env pre] move".
    rewrite /=.
    iSpecialize ("sim" with "ctx [$env $pre]").
    iDestruct "env" as "[names env]".
    iDestruct "names" as %[domσ _].
    assert (is_Some (σ !! x)) as [v val_x].
    { rewrite -domσ lookup_insert; eauto. }
    iMod (simulate_app with "ctx move") as "move"; first auto.
    {  rewrite lookup_fmap val_x; apply to_of_val. }
    iApply "sim".
    rewrite /= lookup_fmap val_x /=.
    rewrite subst_subst.
    - enough (subst_merge (<[x:=of_val v]>∅) (delete x (of_val <$> σ)) = of_val <$> σ) as -> by done.
      apply map_eq; intro y.
      rewrite /subst_merge lookup_merge /subst_merge'.
      destruct (decide (x=y)) as [<-|neq].
      + rewrite lookup_delete lookup_insert lookup_fmap val_x //.
      + rewrite lookup_delete_ne // !lookup_fmap.
        destruct (σ!!y) as [w|].
        * rewrite /= subst_val //.
        * rewrite /= lookup_insert_ne // lookup_empty //.
    - intros y w.
      rewrite lookup_delete_Some lookup_fmap fmap_Some => [[_ [u [_ ->]]]].
      apply val_closed.
  Qed.

  Lemma sound_left_if_intro U Γ e₁ e₂ e₃ η₁ η₂ η₃ (x y: string) A₁ A₂ τ₁ τ₂:
    x ≠ y →
    names Γ ⊆ U →
    heap_wf U η₁ →
    typing U Γ e₁ η₁ A₁ τ₁ η₂ →
    Γ !! x = Some tbool →
    typing (U ∪ A₁) (<[y:=τ₁]>Γ) e₂ η₂ A₂ τ₂ η₃ →
    typing (U ∪ A₁) (<[y:=τ₁]>Γ) e₃ η₂ A₂ τ₂ η₃ →
    delayed_simulation U Γ η₁
                       (If x (Let y e₁ e₂) (Let y e₁ e₃))
                       (Let y e₁ (If x e₂ e₃))
                       (A₁ ∪ A₂) τ₂ η₃.
  Proof.
    intros neqxy Γgood η₁wf ty₁ tyx ty₂ ty₃.
    assert (heap_wf (U ∪ A₁) η₂) as η₂wf by by eapply typing_wf.
    destruct (typing_good_names _ _ _ _ _ _ _ ty₁) as [disj₁ [subτ₁ subη₂]]; auto using heap_wf_names.
    assert (names (<[y:=τ₁]>Γ) ⊆ U ∪ A₁) as names_sub.
    { etrans; first apply names_env_insert.
      apply union_least; auto.
      etrans; first done.
      apply union_subseteq_l. }
    apply fundamental in ty₁; auto.
    destruct ty₁ as [_ ty₁ _ sim₁].
    apply fundamental in ty₂; auto.
    destruct ty₂ as [_ ty₂ _ sim₂].
    apply fundamental in ty₃; auto.
    destruct ty₃ as [_ ty₃ _ sim₃].
    split.
    { apply union_least; auto using heap_wf_names. }
    { rewrite -(union_empty_l_L (A₁ ∪ A₂)).
      econstructor.
      - by apply type_var_string.
      - rewrite union_empty_r_L; eapply tylet; eauto.
      - rewrite union_empty_r_L; eapply tylet; eauto. }
    { eapply tylet; eauto.
      rewrite -(union_empty_l_L A₂).
      econstructor.
      - apply type_var_string; auto.
        rewrite lookup_insert_ne //.
      - rewrite union_empty_r_L; eauto.
      - rewrite union_empty_r_L; eauto. }
    iIntros (D N σ) "[#env pre]".
    iPoseProof (sim₁ with "[$env $pre]") as "sim₁".
    iPoseProof "env" as "[names env_types]".
    iDestruct "names" as %[domσ domD].
    assert (is_Some (σ!!x)) as [v val_x].
    { rewrite -domσ tyx; eauto. }
    assert (is_Some (D!!var x)) as [d conn_x].
    { apply domD; rewrite tyx; eauto. }
    rewrite /= lookup_fmap val_x /=.
    iPoseProof ("env_types" $! x tbool v d with "[]") as "tyx".
    { iPureIntro; red; auto. }
    iDestruct "tyx" as %[cases ->].
    destruct cases as [->| ->].
    { rewrite /=.
      iApply wp_if_true.
      assert (Closed (∅ ∪ {[?y]}) (subst (delete y (of_val <$> σ)) e₂)) as closed.
      { apply (subst_closed' (dom _ (<[y:=τ₁]>Γ))).
        - intros k e'.
          rewrite lookup_delete_Some lookup_fmap fmap_Some => [[_ [v [_ ->]]] _].
          eapply closed_mono; [apply empty_subseteq|done|apply val_closed].
        - rewrite dom_delete /= => [ξ]; clear -domσ.
          rewrite left_id elem_of_union elem_of_difference !elem_of_singleton dom_fmap.
          rewrite dom_insert elem_of_union !elem_of_dom domσ elem_of_singleton.
          destruct (decide (ξ = y)) as [<-|neq]; tauto.
        - by eapply typing_closed. }
      iApply (wp_bind [CAppR (@VRec BAnon y _ closed)]).
      iApply (wp_wand with "sim₁").
      iIntros (v) "post".
      iDestruct "post" as (N' D' d') "[names [type [#sim post]]]".
      rewrite /=.
      iApply wp_app; first apply to_of_val.
      rewrite /= subst_subst.
      2: intros x' e'; rewrite lookup_delete_Some lookup_fmap fmap_Some.
      2: intros [_ [w [_ ->]]]; apply val_closed.
      assert (subst_merge (<[y:=of_val v]>∅) (delete y (of_val <$> σ)) = of_val <$> (<[y:=v]>σ))
        as ->.
      { apply map_eq; intro z.
        rewrite /subst_merge lookup_merge /subst_merge'.
        destruct (decide (y=z)) as [<-|neq].
        - rewrite lookup_fmap lookup_insert lookup_delete lookup_insert //.
        - rewrite lookup_fmap lookup_insert_ne // lookup_delete_ne // lookup_insert_ne // lookup_fmap.
          destruct (σ !! z).
          + rewrite /= subst_val //.
          + rewrite /= lookup_empty //. }
      iDestruct "names" as %[ovN eqd'].
      iPoseProof (strengthen_env_generic int_i_type (int_i_heap η₂) Γ τ₁ y D D' v d' σ N N'
                                         (conn_heap η₂)
                    with "env [$type $post]")
        as "pre".
      3: done.
      { intro n; rewrite elem_of_conn_env elem_of_conn_heap.
        intros [z [-> _]] [ξ [[=] _]]. }
      { rewrite elem_of_conn_heap; intros [ξ [[=] _]]. }
      { intros D₁ D₂ eqD N'' ? <-.
        iApply int_i_heap_local; done. }
      { iPureIntro.
        apply overlap_cast, (overlap_sub (not_new A₁)); last done.
        intro ξ; rewrite elem_of_of_gset elem_of_not_new.
        apply typing_good_names in ty₁; auto using heap_wf_names.
        destruct ty₁ as [disj _].
        intros ??; by apply (disj ξ). }
      iPoseProof (sim₂ with "pre") as "sim₂".
      iApply (wp_wand with "sim₂").
      iIntros (v') "post".
      iDestruct "post" as (N'' D'' d'') "[names [type [#sim' post]]]".
      iExists N'', D'', d''; iFrame.
      iDestruct "names" as %[eqN' eqd''].
      iSplitL.
      { iPureIntro; split; eauto using overlap_trans. }
      iClear "env env_types".
      clear N N' N'' ovN eqN' closed val_x domσ v' v σ.
      iAlways.
      iIntros (N σ p K) "#ctx [#env pre] move".
      iPoseProof "env" as "[env_names env_types]".
      iDestruct "env_names" as %[domσ _].
      assert (is_Some (σ!!x)) as [v val_x].
      { rewrite -domσ tyx; eauto. }
      iDestruct ("env_types" $! x Bool v Ctrue with "[]") as %[_ ->].
      { iPureIntro; split; auto. }
      rewrite /= lookup_delete_ne // lookup_fmap val_x /=.
      assert (∀ (c: const), Closed ({[?BAnon]} ∪ {[?y]})
                                   (If c (subst (delete y (of_val <$> σ)) e₂)
                                       (subst (delete y (of_val <$> σ)) e₃)))
        as closed. {
        intro.
        repeat constructor; apply (subst_closed' (dom _ (<[y:=τ₁]>Γ))).
        3,6: by eapply typing_closed.
        1,3: intros k e'; rewrite lookup_delete_Some lookup_fmap fmap_Some => [[_ [v [_ ->]]] _].
        1,2: eapply closed_mono; [apply empty_subseteq|done|apply val_closed].
        1,2: rewrite left_id dom_insert /= dom_delete => [z].
        1,2: rewrite !elem_of_union elem_of_difference !elem_of_singleton.
        1,2: rewrite dom_fmap !elem_of_dom domσ.
        1,2: destruct (decide (z=y)); tauto.
      }
      match goal with |- context [fill_ctx ?e _] =>
                      change e with (fill_ctx (subst (of_val <$> σ) e₁)
                                              [CAppR (@VRec BAnon y _ (closed Ctrue))])
      end.
      rewrite fill_ctx_app.
      iMod ("sim" with "ctx [$env $pre] move") as (v) "[post move]".
      iDestruct "post" as (d N') "[names [type pre]]".
      rewrite -fill_ctx_app /=.
      iMod (simulate_app with "ctx move") as "move"; auto using to_of_val.
      rewrite /=.
      iMod (simulate_if_true with "ctx move") as "move"; first done.
      rewrite /= subst_subst.
      2: intros x' e'; rewrite lookup_delete_Some lookup_fmap fmap_Some.
      2: intros [_ [w [_ ->]]]; apply val_closed.
      assert (subst_merge (<[y:=of_val v]>∅) (delete y (of_val <$> σ)) = of_val <$> (<[y:=v]>σ))
        as ->.
      { apply map_eq; intro z.
        rewrite /subst_merge lookup_merge /subst_merge'.
        destruct (decide (y=z)) as [<-|neq].
        - rewrite lookup_fmap lookup_insert lookup_delete lookup_insert //.
        - rewrite lookup_fmap lookup_insert_ne // lookup_delete_ne // lookup_insert_ne // lookup_fmap.
          destruct (σ !! z).
          + rewrite /= subst_val //.
          + rewrite /= lookup_empty //. }
      iDestruct "names" as %[ovN eqd].
      rewrite eqd' in eqd; injection eqd as <-.
      iPoseProof (strengthen_env_generic int_s_type (int_s_heap η₂) Γ τ₁ y D D' v d' σ N N'
                                         (conn_heap η₂)
                    with "env [$type $pre]")
        as "pre".
      3: done.
      { intro n; rewrite elem_of_conn_env elem_of_conn_heap.
        intros [z [-> _]] [ξ [[=] _]]. }
      { rewrite elem_of_conn_heap; intros [ξ [[=] _]]. }
      { intros D₁ D₂ eqD N'' ? <-.
        iApply int_s_heap_local; done. }
      { iPureIntro.
        apply overlap_cast, (overlap_sub (not_new A₁)); last done.
        intro ξ; rewrite elem_of_of_gset elem_of_not_new.
        apply typing_good_names in ty₁; auto using heap_wf_names.
        destruct ty₁ as [disj _].
        intros ??; by apply (disj ξ). }
      iMod ("sim'" with "ctx pre move") as (v') "[post move]".
      iModIntro; iExists v'; iFrame.
      iDestruct "post" as (d N'') "[names rest]".
      iExists d, N''; iFrame.
      iDestruct "names" as %[eqN' eqd].
      iPureIntro; split; auto.
      by eapply overlap_trans.
    } {
      rewrite /=.
      iApply wp_if_false.
      assert (Closed (∅ ∪ {[?y]}) (subst (delete y (of_val <$> σ)) e₃)) as closed.
      { apply (subst_closed' (dom _ (<[y:=τ₁]>Γ))).
        - intros k e'.
          rewrite lookup_delete_Some lookup_fmap fmap_Some => [[_ [v [_ ->]]] _].
          eapply closed_mono; [apply empty_subseteq|done|apply val_closed].
        - rewrite dom_delete /= => [ξ]; clear -domσ.
          rewrite left_id elem_of_union elem_of_difference !elem_of_singleton dom_fmap.
          rewrite dom_insert elem_of_union !elem_of_dom domσ elem_of_singleton.
          destruct (decide (ξ = y)) as [<-|neq]; tauto.
        - by eapply typing_closed. }
      iApply (wp_bind [CAppR (@VRec BAnon y _ closed)]).
      iApply (wp_wand with "sim₁").
      iIntros (v) "post".
      iDestruct "post" as (N' D' d') "[names [type [#sim post]]]".
      rewrite /=.
      iApply wp_app; first apply to_of_val.
      rewrite /= subst_subst.
      2: intros x' e'; rewrite lookup_delete_Some lookup_fmap fmap_Some.
      2: intros [_ [w [_ ->]]]; apply val_closed.
      assert (subst_merge (<[y:=of_val v]>∅) (delete y (of_val <$> σ)) = of_val <$> (<[y:=v]>σ))
        as ->.
      { apply map_eq; intro z.
        rewrite /subst_merge lookup_merge /subst_merge'.
        destruct (decide (y=z)) as [<-|neq].
        - rewrite lookup_fmap lookup_insert lookup_delete lookup_insert //.
        - rewrite lookup_fmap lookup_insert_ne // lookup_delete_ne // lookup_insert_ne // lookup_fmap.
          destruct (σ !! z).
          + rewrite /= subst_val //.
          + rewrite /= lookup_empty //. }
      iDestruct "names" as %[ovN eqd'].
      iPoseProof (strengthen_env_generic int_i_type (int_i_heap η₂) Γ τ₁ y D D' v d' σ N N'
                                         (conn_heap η₂)
                    with "env [$type $post]")
        as "pre".
      3: done.
      { intro n; rewrite elem_of_conn_env elem_of_conn_heap.
        intros [z [-> _]] [ξ [[=] _]]. }
      { rewrite elem_of_conn_heap; intros [ξ [[=] _]]. }
      { intros D₁ D₂ eqD N'' ? <-.
        iApply int_i_heap_local; done. }
      { iPureIntro.
        apply overlap_cast, (overlap_sub (not_new A₁)); last done.
        intro ξ; rewrite elem_of_of_gset elem_of_not_new.
        apply typing_good_names in ty₁; auto using heap_wf_names.
        destruct ty₁ as [disj _].
        intros ??; by apply (disj ξ). }
      iPoseProof (sim₃ with "pre") as "sim₃".
      iApply (wp_wand with "sim₃").
      iIntros (v') "post".
      iDestruct "post" as (N'' D'' d'') "[names [type [#sim' post]]]".
      iExists N'', D'', d''; iFrame.
      iDestruct "names" as %[eqN' eqd''].
      iSplitL.
      { iPureIntro; split; eauto using overlap_trans. }
      iClear "env env_types".
      clear N N' N'' ovN eqN' closed val_x domσ v' v σ.
      iAlways.
      iIntros (N σ p K) "#ctx [#env pre] move".
      iPoseProof "env" as "[env_names env_types]".
      iDestruct "env_names" as %[domσ _].
      assert (is_Some (σ!!x)) as [v val_x].
      { rewrite -domσ tyx; eauto. }
      iDestruct ("env_types" $! x Bool v Cfalse with "[]") as %[_ ->].
      { iPureIntro; split; auto. }
      rewrite /= lookup_delete_ne // lookup_fmap val_x /=.
      assert (∀ (c: const), Closed ({[?BAnon]} ∪ {[?y]})
                                   (If c (subst (delete y (of_val <$> σ)) e₂)
                                       (subst (delete y (of_val <$> σ)) e₃)))
        as closed. {
        intro.
        repeat constructor; apply (subst_closed' (dom _ (<[y:=τ₁]>Γ))).
        3,6: by eapply typing_closed.
        1,3: intros k e'; rewrite lookup_delete_Some lookup_fmap fmap_Some => [[_ [v [_ ->]]] _].
        1,2: eapply closed_mono; [apply empty_subseteq|done|apply val_closed].
        1,2: rewrite left_id dom_insert /= dom_delete => [z].
        1,2: rewrite !elem_of_union elem_of_difference !elem_of_singleton.
        1,2: rewrite dom_fmap !elem_of_dom domσ.
        1,2: destruct (decide (z=y)); tauto.
      }
      match goal with |- context [fill_ctx ?e _] =>
                      change e with (fill_ctx (subst (of_val <$> σ) e₁)
                                              [CAppR (@VRec BAnon y _ (closed Cfalse))])
      end.
      rewrite fill_ctx_app.
      iMod ("sim" with "ctx [$env $pre] move") as (v) "[post move]".
      iDestruct "post" as (d N') "[names [type pre]]".
      rewrite -fill_ctx_app /=.
      iMod (simulate_app with "ctx move") as "move"; auto using to_of_val.
      rewrite /=.
      iMod (simulate_if_false with "ctx move") as "move"; first done.
      rewrite /= subst_subst.
      2: intros x' e'; rewrite lookup_delete_Some lookup_fmap fmap_Some.
      2: intros [_ [w [_ ->]]]; apply val_closed.
      assert (subst_merge (<[y:=of_val v]>∅) (delete y (of_val <$> σ)) = of_val <$> (<[y:=v]>σ))
        as ->.
      { apply map_eq; intro z.
        rewrite /subst_merge lookup_merge /subst_merge'.
        destruct (decide (y=z)) as [<-|neq].
        - rewrite lookup_fmap lookup_insert lookup_delete lookup_insert //.
        - rewrite lookup_fmap lookup_insert_ne // lookup_delete_ne // lookup_insert_ne // lookup_fmap.
          destruct (σ !! z).
          + rewrite /= subst_val //.
          + rewrite /= lookup_empty //. }
      iDestruct "names" as %[ovN eqd].
      rewrite eqd' in eqd; injection eqd as <-.
      iPoseProof (strengthen_env_generic int_s_type (int_s_heap η₂) Γ τ₁ y D D' v d' σ N N'
                                         (conn_heap η₂)
                    with "env [$type $pre]")
        as "pre".
      3: done.
      { intro n; rewrite elem_of_conn_env elem_of_conn_heap.
        intros [z [-> _]] [ξ [[=] _]]. }
      { rewrite elem_of_conn_heap; intros [ξ [[=] _]]. }
      { intros D₁ D₂ eqD N'' ? <-.
        iApply int_s_heap_local; done. }
      { iPureIntro.
        apply overlap_cast, (overlap_sub (not_new A₁)); last done.
        intro ξ; rewrite elem_of_of_gset elem_of_not_new.
        apply typing_good_names in ty₁; auto using heap_wf_names.
        destruct ty₁ as [disj _].
        intros ??; by apply (disj ξ). }
      iMod ("sim'" with "ctx pre move") as (v') "[post move]".
      iModIntro; iExists v'; iFrame.
      iDestruct "post" as (d N'') "[names rest]".
      iExists d, N''; iFrame.
      iDestruct "names" as %[eqN' eqd].
      iPureIntro; split; auto.
      by eapply overlap_trans.
    }
  Qed.

  Lemma sound_left_if_elim U Γ e₁ e₂ e₃ η₁ η₂ η₃ (x y: string) A₁ A₂ τ₁ τ₂:
    x ≠ y →
    names Γ ⊆ U →
    heap_wf U η₁ →
    typing U Γ e₁ η₁ A₁ τ₁ η₂ →
    Γ !! x = Some tbool →
    typing (U ∪ A₁) (<[y:=τ₁]>Γ) e₂ η₂ A₂ τ₂ η₃ →
    typing (U ∪ A₁) (<[y:=τ₁]>Γ) e₃ η₂ A₂ τ₂ η₃ →
    delayed_simulation U Γ η₁
                       (Let y e₁ (If x e₂ e₃))
                       (If x (Let y e₁ e₂) (Let y e₁ e₃))
                       (A₁ ∪ A₂) τ₂ η₃.
  Proof.
    intros neqxy Γgood η₁wf ty₁ tyx ty₂ ty₃.
    assert (heap_wf (U ∪ A₁) η₂) as η₂wf by by eapply typing_wf.
    destruct (typing_good_names _ _ _ _ _ _ _ ty₁) as [disj₁ [subτ₁ subη₂]]; auto using heap_wf_names.
    assert (names (<[y:=τ₁]>Γ) ⊆ U ∪ A₁) as names_sub.
    { etrans; first apply names_env_insert.
      apply union_least; auto.
      etrans; first done.
      apply union_subseteq_l. }
    apply fundamental in ty₁; auto.
    destruct ty₁ as [_ ty₁ _ sim₁].
    apply fundamental in ty₂; auto.
    destruct ty₂ as [_ ty₂ _ sim₂].
    apply fundamental in ty₃; auto.
    destruct ty₃ as [_ ty₃ _ sim₃].
    destruct (sound_left_if_intro U Γ e₁ e₂ e₃ η₁ η₂ η₃ x y A₁ A₂ τ₁ τ₂) as [good ty ty' _]; auto.
    split.
    1-3: done.
    clear good ty ty'.
    iIntros (D N σ) "[#env pre]".
    rewrite /= lookup_delete_ne //.
    iPoseProof "env" as "[envnames envtypes]".
    iDestruct "envnames" as %[domσ domD].
    assert (is_Some (σ!!x)) as [v val_x].
    { rewrite -domσ tyx; eauto. }
    assert (is_Some (D!!var x)) as [d conn_x].
    { apply domD; rewrite tyx; eauto. }
    rewrite lookup_fmap val_x /=.
    iDestruct ("envtypes" $! x tbool v d with "[]") as %[cases ->].
    { iPureIntro; red; auto. }
    assert (Closed (∅ ∪ {[?y]}) (If (of_val d) (subst (delete y (of_val <$> σ)) e₂)
                                    (subst (delete y (of_val <$> σ)) e₃)))
      as closed. {
      repeat constructor.
      - eapply closed_mono; [apply empty_subseteq|done|apply val_closed].
      - apply (subst_closed' (dom _ (<[y:=τ₁]>Γ))).
        + intros k e'; rewrite lookup_delete_Some lookup_fmap fmap_Some => [[_ [v [_ ->]]] _].
          eapply closed_mono; [apply empty_subseteq|done|apply val_closed].
        + rewrite dom_insert left_id /= dom_delete => [z].
          rewrite !elem_of_union elem_of_difference dom_fmap !elem_of_dom domσ !elem_of_singleton.
          destruct (decide (z = y)); tauto.
        + by eapply typing_closed.
      - apply (subst_closed' (dom _ (<[y:=τ₁]>Γ))).
        + intros k e'; rewrite lookup_delete_Some lookup_fmap fmap_Some => [[_ [v [_ ->]]] _].
          eapply closed_mono; [apply empty_subseteq|done|apply val_closed].
        + rewrite dom_insert left_id /= dom_delete => [z].
          rewrite !elem_of_union elem_of_difference dom_fmap !elem_of_dom domσ !elem_of_singleton.
          destruct (decide (z = y)); tauto.
        + by eapply typing_closed.
    }
    match goal with |- context C [ App ?e₁ ?e₂ ] =>
                    change (App e₁ e₂) with (fill_ctx e₂ [CAppR (@VRec BAnon y _ closed)])
    end.
    iApply wp_bind.
    iPoseProof (sim₁ $! D N σ with "[$env $pre]") as "sim₁".
    iApply (wp_wand with "sim₁").
    iIntros (v) "post".
    iDestruct "post" as (N' D' d') "[names [type [#sim post]]]".
    iDestruct "names" as %[ovN eqd'].
    rewrite /=.
    iApply wp_app; first apply to_of_val.
    rewrite /= subst_val.
    iPoseProof (strengthen_env_generic int_i_type (int_i_heap η₂) Γ τ₁ y D D' v d' σ N N'
                                       (conn_heap η₂)
                  with "env [$type $post]")
      as "pre".
    3: done.
    { intro n; rewrite elem_of_conn_env elem_of_conn_heap.
      intros [z [-> _]] [ξ [[=] _]]. }
    { rewrite elem_of_conn_heap; intros [ξ [[=] _]]. }
    { intros D₁ D₂ eqD N'' ? <-.
      iApply int_i_heap_local; done. }
    { iPureIntro.
      apply overlap_cast, (overlap_sub (not_new A₁)); last done.
      intro ξ; rewrite elem_of_of_gset elem_of_not_new.
      apply typing_good_names in ty₁; auto using heap_wf_names.
      destruct ty₁ as [disj _].
      intros ??; by apply (disj ξ). }
    rewrite !subst_subst.
    2,3: intros x' e'; rewrite lookup_delete_Some lookup_fmap fmap_Some => [[_ [w [_ ->]]]].
    2,3: apply val_closed.
    assert (subst_merge (<[y:=of_val v]>∅) (delete y (of_val <$> σ)) = of_val <$> (<[y:=v]>σ))
      as ->. {
      apply map_eq; intro z.
      rewrite /subst_merge lookup_merge /subst_merge'.
      destruct (decide (y = z)) as [<-|neq].
      - rewrite lookup_delete lookup_fmap !lookup_insert //.
      - rewrite lookup_delete_ne // !lookup_fmap !lookup_insert_ne //.
        destruct (σ !! z).
        + rewrite /= subst_val //.
        + rewrite /= lookup_empty //.
    }
    destruct cases as [-> | ->]; simpl.
    { iApply wp_if_true.
      iPoseProof (sim₂ with "pre") as "sim₂".
      iApply (wp_wand with "sim₂").
      iIntros (v') "post".
      iDestruct "post" as (N'' D'' d'') "[names [type [#sim' heap]]]".
      iExists N'', D'', d''; iFrame.
      iDestruct "names" as %[ovN' eqd''].
      iSplit.
      { iPureIntro; split; eauto using overlap_trans. }
      iClear "env envtypes".
      clear N N' N'' ovN ovN' σ domσ val_x closed v v'.
      iAlways.
      iIntros (N σ p K) "#ctx [#env pre] move".
      iPoseProof "env" as "[envnames envtypes]".
      iDestruct "envnames" as %[domσ _].
      assert (is_Some (σ!!x)) as [v val_x].
      { rewrite -domσ tyx; eauto. }
      iDestruct ("envtypes" $! x tbool v Ctrue with "[]") as %[_ ->].
      { iPureIntro; red; auto. }
      rewrite /= lookup_fmap val_x /=.
      iMod (simulate_if_true with "ctx move") as "move"; first done.
      assert (Closed (∅ ∪ {[?y]}) (subst (delete y (of_val <$> σ)) e₂)) as closed. {
        repeat constructor.
        apply (subst_closed' (dom _ (<[y:=τ₁]>Γ))).
        + intros k e'; rewrite lookup_delete_Some lookup_fmap fmap_Some => [[_ [v [_ ->]]] _].
          eapply closed_mono; [apply empty_subseteq|done|apply val_closed].
        + rewrite dom_insert left_id /= dom_delete => [z].
          rewrite !elem_of_union elem_of_difference dom_fmap !elem_of_dom domσ !elem_of_singleton.
          destruct (decide (z = y)); tauto.
        + by eapply typing_closed. }
      match goal with |- context C [ fill_ctx ?e _ ] =>
                      change e with (fill_ctx (subst (of_val <$> σ) e₁)
                                              [CAppR (@VRec BAnon y _ closed)])
      end.
      rewrite fill_ctx_app.
      iMod ("sim" with "ctx [$env $pre] move") as (v) "[post move]".
      rewrite -fill_ctx_app /=.
      iMod (simulate_app with "ctx move") as "move".
      { done. }
      { apply to_of_val. }
      rewrite /= subst_subst.
      2: intros x' e'; rewrite lookup_delete_Some lookup_fmap fmap_Some => [[_ [w [_ ->]]]].
      2: apply val_closed.
      assert (subst_merge (<[y:=of_val v]>∅) (delete y (of_val <$> σ)) = of_val <$> (<[y:=v]>σ))
        as ->. {
        apply map_eq; intro z.
        rewrite /subst_merge lookup_merge /subst_merge'.
        destruct (decide (y = z)) as [<-|neq].
        - rewrite lookup_delete lookup_fmap !lookup_insert //.
        - rewrite lookup_delete_ne // !lookup_fmap !lookup_insert_ne //.
          destruct (σ !! z).
          + rewrite /= subst_val //.
          + rewrite /= lookup_empty //.
      }
      iDestruct "post" as (d N') "[names [type post]]".
      iDestruct "names" as %[ovN eqd].
      rewrite eqd' in eqd; injection eqd as <-.
      iPoseProof (strengthen_env_generic int_s_type (int_s_heap η₂) Γ τ₁ y D D' v d' σ N N'
                                         (conn_heap η₂)
                    with "env [$type $post]")
        as "pre".
      3: done.
      { intro n; rewrite elem_of_conn_env elem_of_conn_heap.
        intros [z [-> _]] [ξ [[=] _]]. }
      { rewrite elem_of_conn_heap; intros [ξ [[=] _]]. }
      { intros D₁ D₂ eqD N'' ? <-.
        iApply int_s_heap_local; done. }
      { iPureIntro.
        apply overlap_cast, (overlap_sub (not_new A₁)); last done.
        intro ξ; rewrite elem_of_of_gset elem_of_not_new.
        apply typing_good_names in ty₁; auto using heap_wf_names.
        destruct ty₁ as [disj _].
        intros ??; by apply (disj ξ). }
      iMod ("sim'" with "ctx pre move") as (v') "[post move]".
      iModIntro; iExists v'; iFrame.
      iDestruct "post" as (d N'') "[names rest]".
      iDestruct "names" as %[ovN' eqd].
      rewrite eqd'' in eqd; injection eqd as <-.
      iExists d'', N''; iFrame.
      iPureIntro; split; eauto using overlap_trans.
    } {
      iApply wp_if_false.
      iPoseProof (sim₃ with "pre") as "sim₃".
      iApply (wp_wand with "sim₃").
      iIntros (v') "post".
      iDestruct "post" as (N'' D'' d'') "[names [type [#sim' heap]]]".
      iExists N'', D'', d''; iFrame.
      iDestruct "names" as %[ovN' eqd''].
      iSplit.
      { iPureIntro; split; eauto using overlap_trans. }
      iClear "env envtypes".
      clear N N' N'' ovN ovN' σ domσ val_x closed v v'.
      iAlways.
      iIntros (N σ p K) "#ctx [#env pre] move".
      iPoseProof "env" as "[envnames envtypes]".
      iDestruct "envnames" as %[domσ _].
      assert (is_Some (σ!!x)) as [v val_x].
      { rewrite -domσ tyx; eauto. }
      iDestruct ("envtypes" $! x tbool v Cfalse with "[]") as %[_ ->].
      { iPureIntro; red; auto. }
      rewrite /= lookup_fmap val_x /=.
      iMod (simulate_if_false with "ctx move") as "move"; first done.
      assert (Closed (∅ ∪ {[?y]}) (subst (delete y (of_val <$> σ)) e₃)) as closed. {
        repeat constructor.
        apply (subst_closed' (dom _ (<[y:=τ₁]>Γ))).
        + intros k e'; rewrite lookup_delete_Some lookup_fmap fmap_Some => [[_ [v [_ ->]]] _].
          eapply closed_mono; [apply empty_subseteq|done|apply val_closed].
        + rewrite dom_insert left_id /= dom_delete => [z].
          rewrite !elem_of_union elem_of_difference dom_fmap !elem_of_dom domσ !elem_of_singleton.
          destruct (decide (z = y)); tauto.
        + by eapply typing_closed. }
      match goal with |- context C [ fill_ctx ?e _ ] =>
                      change e with (fill_ctx (subst (of_val <$> σ) e₁)
                                              [CAppR (@VRec BAnon y _ closed)])
      end.
      rewrite fill_ctx_app.
      iMod ("sim" with "ctx [$env $pre] move") as (v) "[post move]".
      rewrite -fill_ctx_app /=.
      iMod (simulate_app with "ctx move") as "move".
      { done. }
      { apply to_of_val. }
      rewrite /= subst_subst.
      2: intros x' e'; rewrite lookup_delete_Some lookup_fmap fmap_Some => [[_ [w [_ ->]]]].
      2: apply val_closed.
      assert (subst_merge (<[y:=of_val v]>∅) (delete y (of_val <$> σ)) = of_val <$> (<[y:=v]>σ))
        as ->. {
        apply map_eq; intro z.
        rewrite /subst_merge lookup_merge /subst_merge'.
        destruct (decide (y = z)) as [<-|neq].
        - rewrite lookup_delete lookup_fmap !lookup_insert //.
        - rewrite lookup_delete_ne // !lookup_fmap !lookup_insert_ne //.
          destruct (σ !! z).
          + rewrite /= subst_val //.
          + rewrite /= lookup_empty //.
      }
      iDestruct "post" as (d N') "[names [type post]]".
      iDestruct "names" as %[ovN eqd].
      rewrite eqd' in eqd; injection eqd as <-.
      iPoseProof (strengthen_env_generic int_s_type (int_s_heap η₂) Γ τ₁ y D D' v d' σ N N'
                                         (conn_heap η₂)
                    with "env [$type $post]")
        as "pre".
      3: done.
      { intro n; rewrite elem_of_conn_env elem_of_conn_heap.
        intros [z [-> _]] [ξ [[=] _]]. }
      { rewrite elem_of_conn_heap; intros [ξ [[=] _]]. }
      { intros D₁ D₂ eqD N'' ? <-.
        iApply int_s_heap_local; done. }
      { iPureIntro.
        apply overlap_cast, (overlap_sub (not_new A₁)); last done.
        intro ξ; rewrite elem_of_of_gset elem_of_not_new.
        apply typing_good_names in ty₁; auto using heap_wf_names.
        destruct ty₁ as [disj _].
        intros ??; by apply (disj ξ). }
      iMod ("sim'" with "ctx pre move") as (v') "[post move]".
      iModIntro; iExists v'; iFrame.
      iDestruct "post" as (d N'') "[names rest]".
      iDestruct "names" as %[ovN' eqd].
      rewrite eqd'' in eqd; injection eqd as <-.
      iExists d'', N''; iFrame.
      iPureIntro; split; eauto using overlap_trans.
    }
  Qed.

  Lemma sound_right_if_intro U Γ e₁ e₂ e₃ e₄ η₁ η₂ η₃ η₄ τ₁ τ₂ A₁ A₂ A₃ (x: string):
    names Γ ⊆ U →
    heap_wf U η₁ →
    typing U Γ e₁ η₁ A₁ tbool η₂ →
    typing (U ∪ A₁) Γ e₂ η₂ A₂ τ₁ η₃ →
    typing (U ∪ A₁) Γ e₃ η₂ A₂ τ₁ η₃ →
    typing (U ∪ A₁ ∪ A₂) (<[x:=τ₁]>Γ) e₄ η₃ A₃ τ₂ η₄ →
    delayed_simulation U Γ η₁
                       (If e₁ (Let x e₂ e₄) (Let x e₃ e₄))
                       (Let x (If e₁ e₂ e₃) e₄)
                       (A₁ ∪ A₂ ∪ A₃) τ₂ η₄.
  Proof.
    intros namesΓ wfη₁ ty₁ ty₂ ty₃ ty₄.
    destruct (fundamental _ _ _ _ _ _ _ wfη₁ namesΓ ty₁) as [_ _ _ sim₁].
    destruct (typing_good_names _ _ _ _ _ _ _ ty₁ namesΓ) as [disjA₁ _]; auto using heap_wf_names.
    pose proof (typing_wf _ _ _ _ _ _ _ ty₁ wfη₁) as wfη₂.
    assert (names Γ ⊆ U ∪ A₁) as namesΓ'.
    { etrans; first done. apply union_subseteq_l. }
    destruct (fundamental _ _ _ _ _ _ _ wfη₂ namesΓ' ty₂) as [_ _ _ sim₂].
    destruct (fundamental _ _ _ _ _ _ _ wfη₂ namesΓ' ty₃) as [_ _ _ sim₃].
    destruct (typing_good_names _ _ _ _ _ _ _ ty₂ namesΓ') as [disjA₂ [namesτ₁ namesη₃]];
      auto using heap_wf_names.
    pose proof (typing_wf _ _ _ _ _ _ _ ty₂ wfη₂) as wfη₃.
    assert (names (<[x:=τ₁]>Γ) ⊆ U ∪ A₁ ∪ A₂) as namesΓ''.
    { etrans; first apply names_env_insert.
      apply union_least; auto.
      etrans; first done.
      apply union_subseteq_l. }
    destruct (fundamental _ _ _ _ _ _ _ wfη₃ namesΓ'' ty₄) as [_ _ _ sim₄].
    destruct (typing_good_names _ _ _ _ _ _ _ ty₄ namesΓ'') as [disjA₃ [namesτ₂ namesη₄]];
      auto using heap_wf_names.
    split.
    { apply union_least; auto using heap_wf_names. }
    { rewrite -union_assoc_L.
      eapply tyif; first done.
      all: by eapply tylet. }
    { eapply tylet.
      - by eapply tyif.
      - by rewrite union_assoc_L. }
    iIntros (D N σ) "[#env pre]".
    iApply (wp_bind [CIf (subst (of_val <$> σ) (Let x e₂ e₄)) (subst (of_val <$> σ) (Let x e₃ e₄))]
                    ⊤ (subst (of_val <$> σ) e₁)).
    iPoseProof (sim₁ with "[$env $pre]") as "sim".
    iApply (wp_wand with "sim").
    iIntros (v) "post".
    iDestruct "post" as (N' D' d') "[names [ty [#sim₁ post]]]".
    iDestruct "names" as %[ovN eqd'].
    cbn -[not_new Let].
    iPoseProof "env" as "[envnames _]".
    iDestruct "envnames" as %[domσ domD].
    assert (Closed (∅ ∪ {[x]}) (subst (delete x (of_val <$> σ)) e₄)) as closed.
    { apply (subst_closed' (dom _ (<[x:=τ₁]>Γ))).
      - intros k e'.
        rewrite lookup_delete_Some lookup_fmap fmap_Some => [[_ [w [_ ->]]] _].
        eapply closed_mono; [apply empty_subseteq|done|apply val_closed].
      - intros z.
        rewrite dom_insert dom_delete dom_fmap left_id !elem_of_union elem_of_difference.
        rewrite !elem_of_singleton !elem_of_dom domσ.
        destruct (decide (z=x)); tauto.
      - by eapply typing_closed. }
    iDestruct "ty" as %[[-> | ->] <-].
    { iApply wp_if_true.
      iApply (wp_bind [CAppR (@VRec BAnon x _ closed)] ⊤ (subst (of_val <$> σ) e₂)).
      set (D'' := D' ~[conn_heap η₂]~> D).
      set (N'' := N' ~[A₁]~> N).
      iAssert (int_i_env Γ D'' N'' σ) with "[env]" as "#env'".
      { iApply (int_i_env_local with "env").
        - apply overlap_merge_along_r.
          intro; rewrite elem_of_conn_heap elem_of_conn_env => [[ξ [-> _]] [y [? _]]] //.
        - apply overlap_merge_along_r.
          intros ξ inξ inξ'.
          apply (disjA₁ ξ); auto.
        - done. }
      iAssert (int_i_heap η₂ D'' N'') with "[post]" as "pre".
      { iApply (int_i_heap_local with "post").
        - apply overlap_merge_along_l.
        - intros ξ inξ.
          destruct (decide (ξ ∈ A₁)) as [case|case].
          + rewrite lookup_merge_along_in //.
          + rewrite lookup_merge_along_not_in // (ovN ξ) // elem_of_not_new //. }
      iPoseProof (sim₂ with "[$env' $pre]") as "sim₂".
      iApply (wp_wand with "sim₂").
      iIntros (v') "post".
      iDestruct "post" as (N''' D''' d''') "[names [type [#sim₂ post]]]".
      iApply wp_app; first apply to_of_val.
      rewrite /= subst_subst.
      2: intros x' e'; rewrite -fmap_delete lookup_fmap fmap_Some => [[w [_ ->]]].
      2: apply val_closed.
      assert (subst_merge (<[x:=of_val v']>∅) (delete x (of_val <$> σ)) = of_val <$> (<[x:=v']>σ))
        as ->. {
        apply map_eq; intro z.
        destruct (decide (x = z)) as [<-|neq].
        - rewrite /subst_merge lookup_merge /subst_merge' lookup_delete lookup_insert lookup_fmap
                  lookup_insert //.
        - rewrite /subst_merge lookup_merge /subst_merge' lookup_delete_ne // !lookup_fmap
                  !lookup_insert_ne //.
          destruct (σ !! z).
          + rewrite /= subst_val //.
          + rewrite /= lookup_empty //.
      }
      iDestruct "names" as %[ovN' eqd''].
      set (DD := D''' ~[conn_heap η₃]~> D'').
      set (NN := N''' ~[A₂]~> N'').
      iAssert (int_i_env (<[x:=τ₁]>Γ) (<[var x := d''']>DD) NN (<[x:=v']>σ))
        with "[env' type]" as "env''".
      { iAssert (int_i_env Γ DD NN σ) with "[env']" as "env''".
        { iApply (int_i_env_local with "env'").
          - apply overlap_merge_along_r.
            intro; rewrite elem_of_conn_heap elem_of_conn_env => [[ξ [-> _]] [y [? _]]] //.
          - apply overlap_merge_along_r.
            intros ξ inξ inξ'.
            apply (disjA₂ ξ); auto.
          - done. }
        iDestruct "env''" as "[envnames envtypes]".
        iDestruct "envnames" as %[domσ' domD'].
        iSplit.
        - iPureIntro; split.
          + intro y.
            rewrite -!(elem_of_dom (D:=gset string)) !dom_insert !elem_of_union !elem_of_dom domσ' //.
          + intro y.
            rewrite -(elem_of_dom (D:=gset string)) -(elem_of_dom (D:=gset conn_name)).
            rewrite !dom_insert !elem_of_union !elem_of_dom !elem_of_singleton.
            intros [->|?%domD']; auto.
        - iIntros (y τ v d [mtΓ%lookup_insert_Some [mtDD mtσ]]).
          destruct mtΓ as [[<- <-]|[neqx mtΓ]].
          + rewrite lookup_insert in mtσ; injection mtσ as ->.
            rewrite lookup_insert in mtDD; injection mtDD as ->.
            iApply (int_i_type_local with "type").
            1,3: done.
            intros ξ inξ.
            destruct (decide (ξ ∈ A₂)) as [case|case].
            * rewrite lookup_merge_along_in //.
            * rewrite lookup_merge_along_not_in // (ovN' ξ) // elem_of_not_new //.
          + iApply "envtypes".
            rewrite lookup_insert_ne // in mtDD.
            rewrite lookup_insert_ne // in mtσ.
            iPureIntro; red; eauto.
            congruence. }
      iAssert (int_i_heap η₃ (<[var x := d''']>DD) NN) with "[post]" as "pre".
      { iApply (int_i_heap_local with "post").
        - trans DD; last apply overlap_merge_along_l.
          intro n.
          rewrite elem_of_conn_heap => [[ξ [-> _]]].
          rewrite lookup_insert_ne //.
        - intros ξ inξ.
          destruct (decide (ξ ∈ A₂)) as [case|case].
          + rewrite lookup_merge_along_in //.
          + rewrite lookup_merge_along_not_in // (ovN' ξ) // elem_of_not_new //. }
      iPoseProof (sim₄ with "[$env'' $pre]") as "sim₄".
      iApply (wp_wand with "sim₄").
      iIntros (v'') "post".
      iDestruct "post" as (NN' DD' dd') "[names [type [#sim₃ post]]]".
      iExists NN', DD', dd'; iFrame.
      iDestruct "names" as %[ovN'' eqd'''].
      iSplit.
      { iPureIntro; split; auto.
        trans N''.
        { apply (overlap_sub (not_new A₁)).
          - intro ξ; rewrite !elem_of_not_new !not_elem_of_union => [[[? _] _]] //.
          - intro ξ; rewrite elem_of_not_new => [inξ].
            rewrite lookup_merge_along_not_in //. }
        trans NN.
        { apply (overlap_sub (not_new A₂)).
          - intro ξ; rewrite !elem_of_not_new !not_elem_of_union => [[[? _] _]] //.
          - intro ξ; rewrite elem_of_not_new => [inξ].
            rewrite /NN (lookup_merge_along_not_in A₂) //. }
        eapply (overlap_sub (not_new A₃)); last done.
        intro ξ; rewrite !elem_of_not_new !not_elem_of_union; tauto. }
      iAlways.
      iClear "env env'".
      clear N N' N'' N''' NN NN' ovN ovN' ovN'' v' v'' σ domσ closed.
      iIntros (N σ p K) "#ctx [#env pre] move".
      iPoseProof "env" as "[env_names _]".
      iDestruct "env_names" as %[domσ _].
      assert (Closed (∅ ∪ {[x]}) (subst (delete x (of_val <$> σ)) e₄)) as closed.
      { apply (subst_closed' (dom _ (<[x:=τ₁]>Γ))).
        - intros k e'.
          rewrite lookup_delete_Some lookup_fmap fmap_Some => [[_ [w [_ ->]]] _].
          eapply closed_mono; [apply empty_subseteq|done|apply val_closed].
        - intros z.
          rewrite dom_insert dom_delete dom_fmap left_id !elem_of_union elem_of_difference.
          rewrite !elem_of_singleton !elem_of_dom domσ.
          destruct (decide (z=x)); tauto.
        - by eapply typing_closed. }
      change (subst (of_val <$> σ) (Let x (If e₁ e₂ e₃) e₄))
        with (fill_ctx (subst (of_val <$> σ) e₁)
                       [CIf (subst (of_val <$> σ) e₂) (subst (of_val <$> σ) e₃);
                        CAppR (@VRec BAnon x (subst _ e₄) closed)]).
      rewrite fill_ctx_app.
      iMod ("sim₁" with "ctx [$env $pre] move") as (v) "[post move]".
      iDestruct "post" as (d N') "[names [type post]]".
      iDestruct "names" as %[ovN eqd].
      rewrite eqd' in eqd; injection eqd as <-.
      set (N'' := N' ~[A₁]~> N).
      iAssert (int_s_env Γ D'' N'' σ) with "[env]" as "#env'".
      { iApply (int_s_env_local with "env").
        - apply overlap_merge_along_r.
          intro; rewrite elem_of_conn_heap elem_of_conn_env => [[ξ [-> _]] [y [? _]]] //.
        - apply overlap_merge_along_r.
          intros ξ inξ inξ'.
          apply (disjA₁ ξ); auto.
        - done. }
      iAssert (int_s_heap η₂ D'' N'') with "[post]" as "pre".
      { iApply (int_s_heap_local with "post").
        - apply overlap_merge_along_l.
        - intros ξ inξ.
          destruct (decide (ξ ∈ A₁)) as [case|case].
          + rewrite lookup_merge_along_in //.
          + rewrite lookup_merge_along_not_in // (ovN ξ) // elem_of_not_new //. }
      iDestruct "type" as %[_ ->].
      cbn [app].
      rewrite (lock (CAppR _ :: _)) /=.
      iMod (simulate_if_true with "ctx move") as "move"; first done.
      iMod ("sim₂" with "ctx [$env' $pre] move") as (v') "[post move]".
      iDestruct "post" as (d N''') "[names [type heap]]".
      iDestruct "names" as %[ovN' eqd].
      rewrite eqd'' in eqd; injection eqd as <-.
      set (NN := N''' ~[A₂]~> N'').
      iAssert (int_s_env (<[x:=τ₁]>Γ) (<[var x := d''']>DD) NN (<[x:=v']>σ))
        with "[env' type]" as "env''".
      { iAssert (int_s_env Γ DD NN σ) with "[env']" as "env''".
        { iApply (int_s_env_local with "env'").
          - apply overlap_merge_along_r.
            intro; rewrite elem_of_conn_heap elem_of_conn_env => [[ξ [-> _]] [y [? _]]] //.
          - apply overlap_merge_along_r.
            intros ξ inξ inξ'.
            apply (disjA₂ ξ); auto.
          - done. }
        iDestruct "env''" as "[envnames envtypes]".
        iDestruct "envnames" as %[domσ' domD'].
        iSplit.
        - iPureIntro; split.
          + intro y.
            rewrite -!(elem_of_dom (D:=gset string)) !dom_insert !elem_of_union !elem_of_dom domσ' //.
          + intro y.
            rewrite -(elem_of_dom (D:=gset string)) -(elem_of_dom (D:=gset conn_name)).
            rewrite !dom_insert !elem_of_union !elem_of_dom !elem_of_singleton.
            intros [->|?%domD']; auto.
        - iIntros (y τ v d [mtΓ%lookup_insert_Some [mtDD mtσ]]).
          destruct mtΓ as [[<- <-]|[neqx mtΓ]].
          + rewrite lookup_insert in mtσ; injection mtσ as ->.
            rewrite lookup_insert in mtDD; injection mtDD as ->.
            iApply (int_s_type_local with "type").
            1,3: done.
            intros ξ inξ.
            destruct (decide (ξ ∈ A₂)) as [case|case].
            * rewrite lookup_merge_along_in //.
            * rewrite lookup_merge_along_not_in // (ovN' ξ) // elem_of_not_new //.
          + iApply "envtypes".
            rewrite lookup_insert_ne // in mtDD.
            rewrite lookup_insert_ne // in mtσ.
            iPureIntro; red; eauto.
            congruence. }
      iAssert (int_s_heap η₃ (<[var x := d''']>DD) NN) with "[heap]" as "pre".
      { iApply (int_s_heap_local with "heap").
        - trans DD; last apply overlap_merge_along_l.
          intro n.
          rewrite elem_of_conn_heap => [[ξ [-> _]]].
          rewrite lookup_insert_ne //.
        - intros ξ inξ.
          destruct (decide (ξ ∈ A₂)) as [case|case].
          + rewrite lookup_merge_along_in //.
          + rewrite lookup_merge_along_not_in // (ovN' ξ) // elem_of_not_new //. }
      rewrite -lock /=.
      iMod (simulate_app with "ctx move") as "move"; first done.
      { apply to_of_val. }
      rewrite /= subst_subst.
      2: intros x' e'; rewrite -fmap_delete lookup_fmap fmap_Some => [[w [_ ->]]].
      2: apply val_closed.
      assert (subst_merge (<[x:=of_val v']>∅) (delete x (of_val <$> σ)) = of_val <$> (<[x:=v']>σ))
        as ->. {
        apply map_eq; intro z.
        destruct (decide (x = z)) as [<-|neq].
        - rewrite /subst_merge lookup_merge /subst_merge' lookup_delete lookup_insert lookup_fmap
                  lookup_insert //.
        - rewrite /subst_merge lookup_merge /subst_merge' lookup_delete_ne // !lookup_fmap
                  !lookup_insert_ne //.
          destruct (σ !! z).
          + rewrite /= subst_val //.
          + rewrite /= lookup_empty //.
      }
      iMod ("sim₃" with "ctx [$env'' $pre] move") as (v) "[post move]".
      iModIntro; iExists v; iFrame.
      iDestruct "post" as (d NN') "[names [type heap]]".
      iExists d, NN'; iFrame.
      iDestruct "names" as %[ovN'' eqd].
      iPureIntro; split; auto.
      trans N''.
      { apply (overlap_sub (not_new A₁)).
          - intro ξ; rewrite !elem_of_not_new !not_elem_of_union => [[[? _] _]] //.
          - intro ξ; rewrite elem_of_not_new => [inξ].
            rewrite lookup_merge_along_not_in //. }
      trans NN.
      { apply (overlap_sub (not_new A₂)).
        - intro ξ; rewrite !elem_of_not_new !not_elem_of_union => [[[? _] _]] //.
        - intro ξ; rewrite elem_of_not_new => [inξ].
          rewrite /NN (lookup_merge_along_not_in A₂) //. }
      eapply (overlap_sub (not_new A₃)); last done.
      intro ξ; rewrite !elem_of_not_new !not_elem_of_union; tauto.
    } {
      iApply wp_if_false.
      iApply (wp_bind [CAppR (@VRec BAnon x _ closed)] ⊤ (subst (of_val <$> σ) e₃)).
      set (D'' := D' ~[conn_heap η₂]~> D).
      set (N'' := N' ~[A₁]~> N).
      iAssert (int_i_env Γ D'' N'' σ) with "[env]" as "#env'".
      { iApply (int_i_env_local with "env").
        - apply overlap_merge_along_r.
          intro; rewrite elem_of_conn_heap elem_of_conn_env => [[ξ [-> _]] [y [? _]]] //.
        - apply overlap_merge_along_r.
          intros ξ inξ inξ'.
          apply (disjA₁ ξ); auto.
        - done. }
      iAssert (int_i_heap η₂ D'' N'') with "[post]" as "pre".
      { iApply (int_i_heap_local with "post").
        - apply overlap_merge_along_l.
        - intros ξ inξ.
          destruct (decide (ξ ∈ A₁)) as [case|case].
          + rewrite lookup_merge_along_in //.
          + rewrite lookup_merge_along_not_in // (ovN ξ) // elem_of_not_new //. }
      iPoseProof (sim₃ with "[$env' $pre]") as "sim₂".
      iApply (wp_wand with "sim₂").
      iIntros (v') "post".
      iDestruct "post" as (N''' D''' d''') "[names [type [#sim₂ post]]]".
      iApply wp_app; first apply to_of_val.
      rewrite /= subst_subst.
      2: intros x' e'; rewrite -fmap_delete lookup_fmap fmap_Some => [[w [_ ->]]].
      2: apply val_closed.
      assert (subst_merge (<[x:=of_val v']>∅) (delete x (of_val <$> σ)) = of_val <$> (<[x:=v']>σ))
        as ->. {
        apply map_eq; intro z.
        destruct (decide (x = z)) as [<-|neq].
        - rewrite /subst_merge lookup_merge /subst_merge' lookup_delete lookup_insert lookup_fmap
                  lookup_insert //.
        - rewrite /subst_merge lookup_merge /subst_merge' lookup_delete_ne // !lookup_fmap
                  !lookup_insert_ne //.
          destruct (σ !! z).
          + rewrite /= subst_val //.
          + rewrite /= lookup_empty //.
      }
      iDestruct "names" as %[ovN' eqd''].
      set (DD := D''' ~[conn_heap η₃]~> D'').
      set (NN := N''' ~[A₂]~> N'').
      iAssert (int_i_env (<[x:=τ₁]>Γ) (<[var x := d''']>DD) NN (<[x:=v']>σ))
        with "[env' type]" as "env''".
      { iAssert (int_i_env Γ DD NN σ) with "[env']" as "env''".
        { iApply (int_i_env_local with "env'").
          - apply overlap_merge_along_r.
            intro; rewrite elem_of_conn_heap elem_of_conn_env => [[ξ [-> _]] [y [? _]]] //.
          - apply overlap_merge_along_r.
            intros ξ inξ inξ'.
            apply (disjA₂ ξ); auto.
          - done. }
        iDestruct "env''" as "[envnames envtypes]".
        iDestruct "envnames" as %[domσ' domD'].
        iSplit.
        - iPureIntro; split.
          + intro y.
            rewrite -!(elem_of_dom (D:=gset string)) !dom_insert !elem_of_union !elem_of_dom domσ' //.
          + intro y.
            rewrite -(elem_of_dom (D:=gset string)) -(elem_of_dom (D:=gset conn_name)).
            rewrite !dom_insert !elem_of_union !elem_of_dom !elem_of_singleton.
            intros [->|?%domD']; auto.
        - iIntros (y τ v d [mtΓ%lookup_insert_Some [mtDD mtσ]]).
          destruct mtΓ as [[<- <-]|[neqx mtΓ]].
          + rewrite lookup_insert in mtσ; injection mtσ as ->.
            rewrite lookup_insert in mtDD; injection mtDD as ->.
            iApply (int_i_type_local with "type").
            1,3: done.
            intros ξ inξ.
            destruct (decide (ξ ∈ A₂)) as [case|case].
            * rewrite lookup_merge_along_in //.
            * rewrite lookup_merge_along_not_in // (ovN' ξ) // elem_of_not_new //.
          + iApply "envtypes".
            rewrite lookup_insert_ne // in mtDD.
            rewrite lookup_insert_ne // in mtσ.
            iPureIntro; red; eauto.
            congruence. }
      iAssert (int_i_heap η₃ (<[var x := d''']>DD) NN) with "[post]" as "pre".
      { iApply (int_i_heap_local with "post").
        - trans DD; last apply overlap_merge_along_l.
          intro n.
          rewrite elem_of_conn_heap => [[ξ [-> _]]].
          rewrite lookup_insert_ne //.
        - intros ξ inξ.
          destruct (decide (ξ ∈ A₂)) as [case|case].
          + rewrite lookup_merge_along_in //.
          + rewrite lookup_merge_along_not_in // (ovN' ξ) // elem_of_not_new //. }
      iPoseProof (sim₄ with "[$env'' $pre]") as "sim₄".
      iApply (wp_wand with "sim₄").
      iIntros (v'') "post".
      iDestruct "post" as (NN' DD' dd') "[names [type [#sim₃ post]]]".
      iExists NN', DD', dd'; iFrame.
      iDestruct "names" as %[ovN'' eqd'''].
      iSplit.
      { iPureIntro; split; auto.
        trans N''.
        { apply (overlap_sub (not_new A₁)).
          - intro ξ; rewrite !elem_of_not_new !not_elem_of_union => [[[? _] _]] //.
          - intro ξ; rewrite elem_of_not_new => [inξ].
            rewrite lookup_merge_along_not_in //. }
        trans NN.
        { apply (overlap_sub (not_new A₂)).
          - intro ξ; rewrite !elem_of_not_new !not_elem_of_union => [[[? _] _]] //.
          - intro ξ; rewrite elem_of_not_new => [inξ].
            rewrite /NN (lookup_merge_along_not_in A₂) //. }
        eapply (overlap_sub (not_new A₃)); last done.
        intro ξ; rewrite !elem_of_not_new !not_elem_of_union; tauto. }
      iAlways.
      iClear "env env'".
      clear N N' N'' N''' NN NN' ovN ovN' ovN'' v' v'' σ domσ closed.
      iIntros (N σ p K) "#ctx [#env pre] move".
      iPoseProof "env" as "[env_names _]".
      iDestruct "env_names" as %[domσ _].
      assert (Closed (∅ ∪ {[x]}) (subst (delete x (of_val <$> σ)) e₄)) as closed.
      { apply (subst_closed' (dom _ (<[x:=τ₁]>Γ))).
        - intros k e'.
          rewrite lookup_delete_Some lookup_fmap fmap_Some => [[_ [w [_ ->]]] _].
          eapply closed_mono; [apply empty_subseteq|done|apply val_closed].
        - intros z.
          rewrite dom_insert dom_delete dom_fmap left_id !elem_of_union elem_of_difference.
          rewrite !elem_of_singleton !elem_of_dom domσ.
          destruct (decide (z=x)); tauto.
        - by eapply typing_closed. }
      change (subst (of_val <$> σ) (Let x (If e₁ e₂ e₃) e₄))
        with (fill_ctx (subst (of_val <$> σ) e₁)
                       [CIf (subst (of_val <$> σ) e₂) (subst (of_val <$> σ) e₃);
                        CAppR (@VRec BAnon x (subst _ e₄) closed)]).
      rewrite fill_ctx_app.
      iMod ("sim₁" with "ctx [$env $pre] move") as (v) "[post move]".
      iDestruct "post" as (d N') "[names [type post]]".
      iDestruct "names" as %[ovN eqd].
      rewrite eqd' in eqd; injection eqd as <-.
      set (N'' := N' ~[A₁]~> N).
      iAssert (int_s_env Γ D'' N'' σ) with "[env]" as "#env'".
      { iApply (int_s_env_local with "env").
        - apply overlap_merge_along_r.
          intro; rewrite elem_of_conn_heap elem_of_conn_env => [[ξ [-> _]] [y [? _]]] //.
        - apply overlap_merge_along_r.
          intros ξ inξ inξ'.
          apply (disjA₁ ξ); auto.
        - done. }
      iAssert (int_s_heap η₂ D'' N'') with "[post]" as "pre".
      { iApply (int_s_heap_local with "post").
        - apply overlap_merge_along_l.
        - intros ξ inξ.
          destruct (decide (ξ ∈ A₁)) as [case|case].
          + rewrite lookup_merge_along_in //.
          + rewrite lookup_merge_along_not_in // (ovN ξ) // elem_of_not_new //. }
      iDestruct "type" as %[_ ->].
      cbn [app].
      rewrite (lock (CAppR _ :: _)) /=.
      iMod (simulate_if_false with "ctx move") as "move"; first done.
      iMod ("sim₂" with "ctx [$env' $pre] move") as (v') "[post move]".
      iDestruct "post" as (d N''') "[names [type heap]]".
      iDestruct "names" as %[ovN' eqd].
      rewrite eqd'' in eqd; injection eqd as <-.
      set (NN := N''' ~[A₂]~> N'').
      iAssert (int_s_env (<[x:=τ₁]>Γ) (<[var x := d''']>DD) NN (<[x:=v']>σ))
        with "[env' type]" as "env''".
      { iAssert (int_s_env Γ DD NN σ) with "[env']" as "env''".
        { iApply (int_s_env_local with "env'").
          - apply overlap_merge_along_r.
            intro; rewrite elem_of_conn_heap elem_of_conn_env => [[ξ [-> _]] [y [? _]]] //.
          - apply overlap_merge_along_r.
            intros ξ inξ inξ'.
            apply (disjA₂ ξ); auto.
          - done. }
        iDestruct "env''" as "[envnames envtypes]".
        iDestruct "envnames" as %[domσ' domD'].
        iSplit.
        - iPureIntro; split.
          + intro y.
            rewrite -!(elem_of_dom (D:=gset string)) !dom_insert !elem_of_union !elem_of_dom domσ' //.
          + intro y.
            rewrite -(elem_of_dom (D:=gset string)) -(elem_of_dom (D:=gset conn_name)).
            rewrite !dom_insert !elem_of_union !elem_of_dom !elem_of_singleton.
            intros [->|?%domD']; auto.
        - iIntros (y τ v d [mtΓ%lookup_insert_Some [mtDD mtσ]]).
          destruct mtΓ as [[<- <-]|[neqx mtΓ]].
          + rewrite lookup_insert in mtσ; injection mtσ as ->.
            rewrite lookup_insert in mtDD; injection mtDD as ->.
            iApply (int_s_type_local with "type").
            1,3: done.
            intros ξ inξ.
            destruct (decide (ξ ∈ A₂)) as [case|case].
            * rewrite lookup_merge_along_in //.
            * rewrite lookup_merge_along_not_in // (ovN' ξ) // elem_of_not_new //.
          + iApply "envtypes".
            rewrite lookup_insert_ne // in mtDD.
            rewrite lookup_insert_ne // in mtσ.
            iPureIntro; red; eauto.
            congruence. }
      iAssert (int_s_heap η₃ (<[var x := d''']>DD) NN) with "[heap]" as "pre".
      { iApply (int_s_heap_local with "heap").
        - trans DD; last apply overlap_merge_along_l.
          intro n.
          rewrite elem_of_conn_heap => [[ξ [-> _]]].
          rewrite lookup_insert_ne //.
        - intros ξ inξ.
          destruct (decide (ξ ∈ A₂)) as [case|case].
          + rewrite lookup_merge_along_in //.
          + rewrite lookup_merge_along_not_in // (ovN' ξ) // elem_of_not_new //. }
      rewrite -lock /=.
      iMod (simulate_app with "ctx move") as "move"; first done.
      { apply to_of_val. }
      rewrite /= subst_subst.
      2: intros x' e'; rewrite -fmap_delete lookup_fmap fmap_Some => [[w [_ ->]]].
      2: apply val_closed.
      assert (subst_merge (<[x:=of_val v']>∅) (delete x (of_val <$> σ)) = of_val <$> (<[x:=v']>σ))
        as ->. {
        apply map_eq; intro z.
        destruct (decide (x = z)) as [<-|neq].
        - rewrite /subst_merge lookup_merge /subst_merge' lookup_delete lookup_insert lookup_fmap
                  lookup_insert //.
        - rewrite /subst_merge lookup_merge /subst_merge' lookup_delete_ne // !lookup_fmap
                  !lookup_insert_ne //.
          destruct (σ !! z).
          + rewrite /= subst_val //.
          + rewrite /= lookup_empty //.
      }
      iMod ("sim₃" with "ctx [$env'' $pre] move") as (v) "[post move]".
      iModIntro; iExists v; iFrame.
      iDestruct "post" as (d NN') "[names [type heap]]".
      iExists d, NN'; iFrame.
      iDestruct "names" as %[ovN'' eqd].
      iPureIntro; split; auto.
      trans N''.
      { apply (overlap_sub (not_new A₁)).
          - intro ξ; rewrite !elem_of_not_new !not_elem_of_union => [[[? _] _]] //.
          - intro ξ; rewrite elem_of_not_new => [inξ].
            rewrite lookup_merge_along_not_in //. }
      trans NN.
      { apply (overlap_sub (not_new A₂)).
        - intro ξ; rewrite !elem_of_not_new !not_elem_of_union => [[[? _] _]] //.
        - intro ξ; rewrite elem_of_not_new => [inξ].
          rewrite /NN (lookup_merge_along_not_in A₂) //. }
      eapply (overlap_sub (not_new A₃)); last done.
      intro ξ; rewrite !elem_of_not_new !not_elem_of_union; tauto.
    }
  Qed.

  Lemma sound_right_if_elim U Γ e₁ e₂ e₃ e₄ η₁ η₂ η₃ η₄ τ₁ τ₂ A₁ A₂ A₃ (x: string):
    names Γ ⊆ U →
    heap_wf U η₁ →
    typing U Γ e₁ η₁ A₁ tbool η₂ →
    typing (U ∪ A₁) Γ e₂ η₂ A₂ τ₁ η₃ →
    typing (U ∪ A₁) Γ e₃ η₂ A₂ τ₁ η₃ →
    typing (U ∪ A₁ ∪ A₂) (<[x:=τ₁]>Γ) e₄ η₃ A₃ τ₂ η₄ →
    delayed_simulation U Γ η₁
                       (Let x (If e₁ e₂ e₃) e₄)
                       (If e₁ (Let x e₂ e₄) (Let x e₃ e₄))
                       (A₁ ∪ A₂ ∪ A₃) τ₂ η₄.
  Proof.
    intros namesΓ wfη₁ ty₁ ty₂ ty₃ ty₄.
    destruct (sound_right_if_intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ namesΓ wfη₁ ty₁ ty₂ ty₃ ty₄)
      as [good ty ty' _].
    split; auto.
    iIntros (D N σ) "[#env pre]".
    iPoseProof "env" as "[envnames _]".
    iDestruct "envnames" as %[domσ domD].
    assert (Closed (∅ ∪ {[x]}) (subst (delete x (of_val <$> σ)) e₄)) as closed.
    { apply (subst_closed' (dom _ (<[x:=τ₁]>Γ))).
      - intros k e'.
        rewrite lookup_delete_Some lookup_fmap fmap_Some => [[_ [w [_ ->]]] _].
        eapply closed_mono; [apply empty_subseteq|done|apply val_closed].
      - intros z.
        rewrite dom_insert dom_delete dom_fmap left_id !elem_of_union elem_of_difference.
        rewrite !elem_of_singleton !elem_of_dom domσ.
        destruct (decide (z=x)); tauto.
      - by eapply typing_closed. }
    iApply (wp_bind [CIf (subst (of_val <$> σ) e₂) (subst (of_val <$> σ) e₃);
                     CAppR (@VRec BAnon x _ closed)]
                    ⊤ (subst (of_val <$> σ) e₁)).
    destruct (fundamental _ _ _ _ _ _ _ wfη₁ namesΓ ty₁) as [_ _ _ sim₁].
    destruct (typing_good_names _ _ _ _ _ _ _ ty₁ namesΓ) as [disjA₁ _]; auto using heap_wf_names.
    pose proof (typing_wf _ _ _ _ _ _ _ ty₁ wfη₁) as wfη₂.
    assert (names Γ ⊆ U ∪ A₁) as namesΓ'.
    { etrans; first done. apply union_subseteq_l. }
    destruct (fundamental _ _ _ _ _ _ _ wfη₂ namesΓ' ty₂) as [_ _ _ sim₂].
    destruct (fundamental _ _ _ _ _ _ _ wfη₂ namesΓ' ty₃) as [_ _ _ sim₃].
    destruct (typing_good_names _ _ _ _ _ _ _ ty₂ namesΓ') as [disjA₂ [namesτ₁ namesη₃]];
      auto using heap_wf_names.
    pose proof (typing_wf _ _ _ _ _ _ _ ty₂ wfη₂) as wfη₃.
    assert (names (<[x:=τ₁]>Γ) ⊆ U ∪ A₁ ∪ A₂) as namesΓ''.
    { etrans; first apply names_env_insert.
      apply union_least; auto.
      etrans; first done.
      apply union_subseteq_l. }
    destruct (fundamental _ _ _ _ _ _ _ wfη₃ namesΓ'' ty₄) as [_ _ _ sim₄].
    destruct (typing_good_names _ _ _ _ _ _ _ ty₄ namesΓ'') as [disjA₃ [namesτ₂ namesη₄]];
      auto using heap_wf_names.
    iPoseProof (sim₁ with "[$env $pre]") as "sim".
    iApply (wp_wand with "sim").
    iIntros (v) "post".
    iDestruct "post" as (N' D' d') "[names [type [#sim₁ post]]]".
    iDestruct "names" as %[ovN eqd'].
    set (D'' := D' ~[conn_heap η₂]~> D).
    set (N'' := N' ~[A₁]~> N).
    iAssert (int_i_env Γ D'' N'' σ) with "[env]" as "#env'".
    { iApply (int_i_env_local with "env").
      - apply overlap_merge_along_r.
        intro; rewrite elem_of_conn_heap elem_of_conn_env => [[ξ [-> _]] [y [? _]]] //.
      - apply overlap_merge_along_r.
        intros ξ inξ inξ'.
        apply (disjA₁ ξ); auto.
      - done. }
    iAssert (int_i_heap η₂ D'' N'') with "[post]" as "pre".
    { iApply (int_i_heap_local with "post").
      - apply overlap_merge_along_l.
      - intros ξ inξ.
        destruct (decide (ξ ∈ A₁)) as [case|case].
        + rewrite lookup_merge_along_in //.
        + rewrite lookup_merge_along_not_in // (ovN ξ) // elem_of_not_new //. }
    assert (N ≡[not_new A₁]≡ N'') as ovN''.
    { intro ξ.
      rewrite elem_of_not_new => [inξ].
      rewrite lookup_merge_along_not_in //. }
    rewrite (lock [CAppR _]) /=.
    iDestruct "type" as %[cases ->].
    destruct cases as [ -> | -> ].
    { iApply wp_bind.
      iApply wp_if_true.
      iPoseProof (sim₂ with "[$env' $pre]") as "sim".
      iApply (wp_wand with "sim").
      iIntros (v) "post".
      iDestruct "post" as (N''' D''' d''') "[names [type [#sim₂ post]]]".
      iDestruct "names" as %[ovN''' eqd].
      iPoseProof (strengthen_env_generic int_i_type (int_i_heap η₃) Γ τ₁ x _ _ _ _ _ _ _
                                         (conn_heap η₃)
                    with "env' [$type $post]") as "pre".
      { intro n; rewrite elem_of_conn_env elem_of_conn_heap => [[y [-> _]] [ξ [? _]]] //. }
      { rewrite elem_of_conn_heap => [[? [? _]]] //. }
      { done. }
      { intros ??? ?? <-; apply int_i_heap_local; done. }
      { iPureIntro.
        intros ξ inξ.
        apply ovN'''.
        rewrite elem_of_not_new => [?].
        apply (disjA₂ ξ); done. }
      iPoseProof (sim₄ with "pre") as "sim".
      rewrite -lock /=.
      iApply wp_app; first apply to_of_val.
      rewrite /= subst_subst.
      2: intros x' e'; rewrite -fmap_delete lookup_fmap fmap_Some => [[w [_ ->]]].
      2: apply val_closed.
      assert (subst_merge (<[x:=of_val v]>∅) (delete x (of_val <$> σ)) = of_val <$> (<[x:=v]>σ))
        as ->. {
        apply map_eq; intro z.
        destruct (decide (x = z)) as [<-|neq].
        - rewrite /subst_merge lookup_merge /subst_merge' lookup_delete lookup_insert lookup_fmap
                  lookup_insert //.
        - rewrite /subst_merge lookup_merge /subst_merge' lookup_delete_ne // !lookup_fmap
                  !lookup_insert_ne //.
          destruct (σ !! z).
          + rewrite /= subst_val //.
          + rewrite /= lookup_empty //.
      }
      iApply (wp_wand with "sim").
      iIntros (v') "post".
      iDestruct "post" as (NN DD dd) "[names [type [#sim₃ heap]]]".
      iExists NN, DD, dd; iFrame.
      iDestruct "names" as %[ovNN eqd''].
      iSplit.
      { iPureIntro; split; last done.
        eapply overlap_trans; last done.
        eapply overlap_trans; done. }
      iClear "env env'".
      clear N N' N'' N''' NN ovN ovN'' ovN''' ovNN σ closed domσ v.
      iAlways.
      iIntros (N σ p K) "#ctx [#env pre] move".
      cbn -[Let not_new].
      change (If (subst (of_val <$> σ) e₁)
                 (subst (of_val <$> σ) (Let x e₂ e₄))
                 (subst (of_val <$> σ) (Let x e₃ e₄)))
        with (fill_ctx (subst (of_val <$> σ) e₁)
                       [CIf (subst (of_val <$> σ) (Let x e₂ e₄))
                            (subst (of_val <$> σ) (Let x e₃ e₄))]).
      rewrite fill_ctx_app.
      iMod ("sim₁" with "ctx [$env $pre] move") as (v) "[post move]".
      iDestruct "post" as (d N') "[names [type post]]".
      iDestruct "names" as %[ovN eqdd].
      rewrite eqd' in eqdd; injection eqdd as <-.
      iDestruct "type" as %[_ ->].
      iMod (simulate_if_true with "ctx move") as "move"; first done.
      set (N'' := N' ~[A₁]~> N).
      iAssert (int_s_env Γ D'' N'' σ) with "[env]" as "#env'".
      { iApply (int_s_env_local with "env").
        - apply overlap_merge_along_r.
          intro; rewrite elem_of_conn_heap elem_of_conn_env => [[ξ [-> _]] [y [? _]]] //.
        - apply overlap_merge_along_r.
          intros ξ inξ inξ'.
          apply (disjA₁ ξ); auto.
        - done. }
      iAssert (int_s_heap η₂ D'' N'') with "[post]" as "pre".
      { iApply (int_s_heap_local with "post").
        - apply overlap_merge_along_l.
        - intros ξ inξ.
          destruct (decide (ξ ∈ A₁)) as [case|case].
          + rewrite lookup_merge_along_in //.
          + rewrite lookup_merge_along_not_in // (ovN ξ) // elem_of_not_new //. }
      assert (N ≡[not_new A₁]≡ N'') as ovN''.
      { intro ξ.
        rewrite elem_of_not_new => [inξ].
        rewrite lookup_merge_along_not_in //. }
      iDestruct "env" as "[env_names _]".
      iDestruct "env_names" as %[domσ _].
      assert (Closed (∅ ∪ {[x]}) (subst (delete x (of_val <$> σ)) e₄)) as closed.
      { apply (subst_closed' (dom _ (<[x:=τ₁]>Γ))).
        - intros k e'.
          rewrite lookup_delete_Some lookup_fmap fmap_Some => [[_ [w [_ ->]]] _].
          eapply closed_mono; [apply empty_subseteq|done|apply val_closed].
        - intros z.
          rewrite dom_insert dom_delete dom_fmap left_id !elem_of_union elem_of_difference.
          rewrite !elem_of_singleton !elem_of_dom domσ.
          destruct (decide (z=x)); tauto.
        - by eapply typing_closed. }
      change (subst (of_val <$> σ) (Let x e₂ e₄))
        with (fill_ctx (subst (of_val <$> σ) e₂) [CAppR (@VRec BAnon x _ closed)]).
      rewrite fill_ctx_app.
      iMod ("sim₂" with "ctx [$env' $pre] move") as (v) "[post move]".
      iDestruct "post" as (d'' N''') "[names [type post]]".
      iDestruct "names" as %[ovN''' eqd'''].
      iPoseProof (strengthen_env_generic int_s_type (int_s_heap η₃) Γ τ₁ x _ _ _ _ _ _ _
                                         (conn_heap η₃)
                    with "env' [$type $post]") as "pre".
      { intro n; rewrite elem_of_conn_env elem_of_conn_heap => [[y [-> _]] [ξ [? _]]] //. }
      { rewrite elem_of_conn_heap => [[? [? _]]] //. }
      { done. }
      { intros ??? ?? <-; apply int_s_heap_local; done. }
      { iPureIntro.
        intros ξ inξ.
        apply ovN'''.
        rewrite elem_of_not_new => [?].
        apply (disjA₂ ξ); done. }
      rewrite eqd in eqd'''; injection eqd''' as <-.
      iMod (simulate_app with "ctx move") as "move"; first done.
      { apply to_of_val. }
      rewrite /= subst_subst.
      2: intros x' e'; rewrite -fmap_delete lookup_fmap fmap_Some => [[w [_ ->]]].
      2: apply val_closed.
      assert (subst_merge (<[x:=of_val v]>∅) (delete x (of_val <$> σ)) = of_val <$> (<[x:=v]>σ))
        as ->. {
        apply map_eq; intro z.
        destruct (decide (x = z)) as [<-|neq].
        - rewrite /subst_merge lookup_merge /subst_merge' lookup_delete lookup_insert lookup_fmap
                  lookup_insert //.
        - rewrite /subst_merge lookup_merge /subst_merge' lookup_delete_ne // !lookup_fmap
                  !lookup_insert_ne //.
          destruct (σ !! z).
          + rewrite /= subst_val //.
          + rewrite /= lookup_empty //.
      }
      iMod ("sim₃" with "ctx pre move") as (v'') "[post move]".
      iDestruct "post" as (d NN') "[names [type post]]".
      iModIntro.
      iExists v''; iFrame.
      iExists d, NN'; iFrame.
      iDestruct "names" as %[ovNN' eqd'''].
      iPureIntro; split; last done.
      eapply overlap_trans; last done.
      eapply overlap_trans; done.
    } {
      iApply wp_bind.
      iApply wp_if_false.
      iPoseProof (sim₃ with "[$env' $pre]") as "sim".
      iApply (wp_wand with "sim").
      iIntros (v) "post".
      iDestruct "post" as (N''' D''' d''') "[names [type [#sim₂ post]]]".
      iDestruct "names" as %[ovN''' eqd].
      iPoseProof (strengthen_env_generic int_i_type (int_i_heap η₃) Γ τ₁ x _ _ _ _ _ _ _
                                         (conn_heap η₃)
                    with "env' [$type $post]") as "pre".
      { intro n; rewrite elem_of_conn_env elem_of_conn_heap => [[y [-> _]] [ξ [? _]]] //. }
      { rewrite elem_of_conn_heap => [[? [? _]]] //. }
      { done. }
      { intros ??? ?? <-; apply int_i_heap_local; done. }
      { iPureIntro.
        intros ξ inξ.
        apply ovN'''.
        rewrite elem_of_not_new => [?].
        apply (disjA₂ ξ); done. }
      iPoseProof (sim₄ with "pre") as "sim".
      rewrite -lock /=.
      iApply wp_app; first apply to_of_val.
      rewrite /= subst_subst.
      2: intros x' e'; rewrite -fmap_delete lookup_fmap fmap_Some => [[w [_ ->]]].
      2: apply val_closed.
      assert (subst_merge (<[x:=of_val v]>∅) (delete x (of_val <$> σ)) = of_val <$> (<[x:=v]>σ))
        as ->. {
        apply map_eq; intro z.
        destruct (decide (x = z)) as [<-|neq].
        - rewrite /subst_merge lookup_merge /subst_merge' lookup_delete lookup_insert lookup_fmap
                  lookup_insert //.
        - rewrite /subst_merge lookup_merge /subst_merge' lookup_delete_ne // !lookup_fmap
                  !lookup_insert_ne //.
          destruct (σ !! z).
          + rewrite /= subst_val //.
          + rewrite /= lookup_empty //.
      }
      iApply (wp_wand with "sim").
      iIntros (v') "post".
      iDestruct "post" as (NN DD dd) "[names [type [#sim₃ heap]]]".
      iExists NN, DD, dd; iFrame.
      iDestruct "names" as %[ovNN eqd''].
      iSplit.
      { iPureIntro; split; last done.
        eapply overlap_trans; last done.
        eapply overlap_trans; done. }
      iClear "env env'".
      clear N N' N'' N''' NN ovN ovN'' ovN''' ovNN σ closed domσ v.
      iAlways.
      iIntros (N σ p K) "#ctx [#env pre] move".
      cbn -[Let not_new].
      change (If (subst (of_val <$> σ) e₁)
                 (subst (of_val <$> σ) (Let x e₂ e₄))
                 (subst (of_val <$> σ) (Let x e₃ e₄)))
        with (fill_ctx (subst (of_val <$> σ) e₁)
                       [CIf (subst (of_val <$> σ) (Let x e₂ e₄))
                            (subst (of_val <$> σ) (Let x e₃ e₄))]).
      rewrite fill_ctx_app.
      iMod ("sim₁" with "ctx [$env $pre] move") as (v) "[post move]".
      iDestruct "post" as (d N') "[names [type post]]".
      iDestruct "names" as %[ovN eqdd].
      rewrite eqd' in eqdd; injection eqdd as <-.
      iDestruct "type" as %[_ ->].
      iMod (simulate_if_false with "ctx move") as "move"; first done.
      set (N'' := N' ~[A₁]~> N).
      iAssert (int_s_env Γ D'' N'' σ) with "[env]" as "#env'".
      { iApply (int_s_env_local with "env").
        - apply overlap_merge_along_r.
          intro; rewrite elem_of_conn_heap elem_of_conn_env => [[ξ [-> _]] [y [? _]]] //.
        - apply overlap_merge_along_r.
          intros ξ inξ inξ'.
          apply (disjA₁ ξ); auto.
        - done. }
      iAssert (int_s_heap η₂ D'' N'') with "[post]" as "pre".
      { iApply (int_s_heap_local with "post").
        - apply overlap_merge_along_l.
        - intros ξ inξ.
          destruct (decide (ξ ∈ A₁)) as [case|case].
          + rewrite lookup_merge_along_in //.
          + rewrite lookup_merge_along_not_in // (ovN ξ) // elem_of_not_new //. }
      assert (N ≡[not_new A₁]≡ N'') as ovN''.
      { intro ξ.
        rewrite elem_of_not_new => [inξ].
        rewrite lookup_merge_along_not_in //. }
      iDestruct "env" as "[env_names _]".
      iDestruct "env_names" as %[domσ _].
      assert (Closed (∅ ∪ {[x]}) (subst (delete x (of_val <$> σ)) e₄)) as closed.
      { apply (subst_closed' (dom _ (<[x:=τ₁]>Γ))).
        - intros k e'.
          rewrite lookup_delete_Some lookup_fmap fmap_Some => [[_ [w [_ ->]]] _].
          eapply closed_mono; [apply empty_subseteq|done|apply val_closed].
        - intros z.
          rewrite dom_insert dom_delete dom_fmap left_id !elem_of_union elem_of_difference.
          rewrite !elem_of_singleton !elem_of_dom domσ.
          destruct (decide (z=x)); tauto.
        - by eapply typing_closed. }
      change (subst (of_val <$> σ) (Let x e₃ e₄))
        with (fill_ctx (subst (of_val <$> σ) e₃) [CAppR (@VRec BAnon x _ closed)]).
      rewrite fill_ctx_app.
      iMod ("sim₂" with "ctx [$env' $pre] move") as (v) "[post move]".
      iDestruct "post" as (d'' N''') "[names [type post]]".
      iDestruct "names" as %[ovN''' eqd'''].
      iPoseProof (strengthen_env_generic int_s_type (int_s_heap η₃) Γ τ₁ x _ _ _ _ _ _ _
                                         (conn_heap η₃)
                    with "env' [$type $post]") as "pre".
      { intro n; rewrite elem_of_conn_env elem_of_conn_heap => [[y [-> _]] [ξ [? _]]] //. }
      { rewrite elem_of_conn_heap => [[? [? _]]] //. }
      { done. }
      { intros ??? ?? <-; apply int_s_heap_local; done. }
      { iPureIntro.
        intros ξ inξ.
        apply ovN'''.
        rewrite elem_of_not_new => [?].
        apply (disjA₂ ξ); done. }
      rewrite eqd in eqd'''; injection eqd''' as <-.
      iMod (simulate_app with "ctx move") as "move"; first done.
      { apply to_of_val. }
      rewrite /= subst_subst.
      2: intros x' e'; rewrite -fmap_delete lookup_fmap fmap_Some => [[w [_ ->]]].
      2: apply val_closed.
      assert (subst_merge (<[x:=of_val v]>∅) (delete x (of_val <$> σ)) = of_val <$> (<[x:=v]>σ))
        as ->. {
        apply map_eq; intro z.
        destruct (decide (x = z)) as [<-|neq].
        - rewrite /subst_merge lookup_merge /subst_merge' lookup_delete lookup_insert lookup_fmap
                  lookup_insert //.
        - rewrite /subst_merge lookup_merge /subst_merge' lookup_delete_ne // !lookup_fmap
                  !lookup_insert_ne //.
          destruct (σ !! z).
          + rewrite /= subst_val //.
          + rewrite /= lookup_empty //.
      }
      iMod ("sim₃" with "ctx pre move") as (v'') "[post move]".
      iDestruct "post" as (d NN') "[names [type post]]".
      iModIntro.
      iExists v''; iFrame.
      iExists d, NN'; iFrame.
      iDestruct "names" as %[ovNN' eqd'''].
      iPureIntro; split; last done.
      eapply overlap_trans; last done.
      eapply overlap_trans; done.
    }
  Qed.
  
End SimpleRules.