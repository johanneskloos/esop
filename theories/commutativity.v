From iris.proofmode Require Import tactics.
From esop Require Import types delayed closure types corecalculus specification typetranslation
     exprfacts overlap.
From stdpp Require Import gmap.

Section Commutativity.
  Context `{allG Σ}.

  Coercion BNamed: string >-> binder.
  
  Lemma commute_sound U Γ (η₁ η₂ η₁' η₂' η': hexpr) (τ₁ τ₂ τ: type) A₁ A₂ A₃ (x y: string) ex ey e:
    Γ !! x = None →
    Γ !! y = None →
    x ≠ y →
    heap_wf U (η₁ ⊗ η₂) →
    heap_wf (U ∪ A₁) (η₁' ⊗ η₂) →
    heap_wf (U ∪ A₂) (η₁ ⊗ η₂') →
    heap_wf (U ∪ A₁ ∪ A₂) (η₁' ⊗ η₂') →
    heap_wf (U ∪ A₁) η₂ →
    heap_wf (U ∪ A₂) η₁ →
    A₁ ⊥ A₂ →
    names Γ ⊆ U →
    heap_wf U η₁ →
    heap_wf U η₂ →
    typing U Γ ex η₁ A₁ τ₁ η₁' →
    typing U Γ ey η₂ A₂ τ₂ η₂' →
    typing (U ∪ A₁ ∪ A₂) (<[x:=τ₁]>(<[y:=τ₂]>Γ)) e (η₁' ⊗ η₂') A₃ τ η' →
    delayed_simulation U Γ (η₁ ⊗ η₂)
                       (Let x ex (Let y ey e)) (Let y ey (Let x ex e))
                       (A₁ ∪ A₂ ∪ A₃) τ η'.
  Proof.
    intros x_fresh y_fresh x_neq_y disjη disjη₁ disjη₂ disjη' wf₂ wf₁ disjA
           Γgood wfη₁ wfη₂ [_ tyx _ simx]%fundamental [_ tyy _ simy]%fundamental tye; auto.
    assert (delayed_simulation (U ∪ A₁ ∪ A₂) (<[x:=τ₁]>(<[y:=τ₂]>Γ)) (η₁' ⊗ η₂') e e A₃ τ η') as sime.
    { apply fundamental; auto.
      apply typing_good_names in tyx; auto using heap_wf_names.
      apply typing_good_names in tyy; auto using heap_wf_names.
      destruct tyx as [_ [sub₁ _]], tyy as [_ [sub₂ _]].
      intros ξ [inξ|[inξ|inξ]%names_env_insert%elem_of_union]%names_env_insert%elem_of_union.
      - apply elem_of_union_l; auto.
      - rewrite -assoc (union_comm A₁) assoc.
        apply elem_of_union_l; auto.
      - apply elem_of_union_l, elem_of_union_l; auto. }
    destruct sime as [goode _ _ sime].
    split.
    { apply union_least; auto; cbn.
      apply union_least; by apply heap_wf_names. }
    { rewrite -union_assoc_L.
      apply tylet with (η₂ := hstar η₁' η₂) (τ₁ := τ₁).
      { apply tyframe; auto.
        - by inversion_clear disjη.
        - by inversion_clear disjη₁.
        - apply typing_good_names in tyx; auto using heap_wf_names.
          destruct tyx as [disjU _].
          intros ξ inξ%disjU inξ'.
          apply heap_wf_names in wfη₂.
          apply wfη₂ in inξ'; done. }
      apply tylet with (η₂ := hstar η₁' η₂') (τ₁ := τ₂).
      { rewrite !(comm hstar η₁').
        apply tyframe.
        - by inversion_clear disjη₁.
        - by inversion_clear disjη'.
        - apply typing_good_names in tyy; auto using heap_wf_names.
          destruct tyy as [disjU _].
          apply typing_good_names in tyx; auto using heap_wf_names.
          destruct tyx as [_ [_ sub]].
          intros ξ inξ [?|?]%sub%elem_of_union; eauto.
        - by inversion_clear disjη'.
        - eapply tyweaken; last apply tyy; auto using heap_wf_names.
          + apply typing_good_names in tyy; auto using heap_wf_names.
            destruct tyy as [disj _].
            apply disjoint_union_l; auto.
          + apply union_subseteq_l.
          + by apply insert_subseteq.
          + rewrite union_comm_L; by inversion_clear disjη'. }
      rewrite /= insert_commute //. }
    { rewrite (union_comm_L A₁).
      rewrite -union_assoc_L.
      apply tylet with (η₂ := hstar η₁ η₂') (τ₁ := τ₂).
      { rewrite !(comm hstar η₁).
        apply tyframe; auto.
        - by inversion_clear disjη.
        - by inversion_clear disjη₂.
        - apply typing_good_names in tyy; auto using heap_wf_names.
          destruct tyy as [disjU _].
          intros ξ inξ%disjU inξ'.
          apply heap_wf_names in wfη₁.
          apply wfη₁ in inξ'; done. }
      apply tylet with (η₂ := hstar η₁' η₂') (τ₁ := τ₁).
      { apply tyframe.
        - by inversion_clear disjη₂.
        - by inversion_clear disjη'.
        - apply typing_good_names in tyx; auto using heap_wf_names.
          destruct tyx as [disjU _].
          apply typing_good_names in tyy; auto using heap_wf_names.
          destruct tyy as [_ [_ sub]].
          intros ξ inξ [?|?]%sub%elem_of_union; eauto.
        - inversion_clear disjη'.
          rewrite -union_assoc_L (union_comm_L A₂) union_assoc_L //.
        - eapply tyweaken; last apply tyx; auto using heap_wf_names.
          + apply typing_good_names in tyx; auto using heap_wf_names.
            destruct tyx as [disj _].
            apply disjoint_union_l; auto.
          + apply union_subseteq_l.
          + by apply insert_subseteq.
          + rewrite union_assoc_L (union_comm_L A₁); by inversion_clear disjη'. }
      rewrite /= -union_assoc_L (union_comm_L A₂) union_assoc_L //. }
    iIntros (D N σ) "[#env pre]".
    cbn [int_i_heap].
    iDestruct "pre" as "[pre₁ pre₂]".
    rewrite /=.
    iPoseProof "env" as "[#names _]".
    iDestruct "names" as %[domσ domD].
    assert (Closed (dom _ Γ) ey) as closed_ey by by eapply closed_meta.typing_closed.
    rewrite (closed_meta.subst_local _ _ closed_ey (delete x _) (of_val <$> σ)).
    2: intros z inz%elem_of_dom; rewrite lookup_delete_ne //.
    2: intros ?; subst; rewrite x_fresh in inz; by apply is_Some_None in inz.
    assert (Closed (∅ ∪ {[x]}) (Let y (subst (of_val <$> σ) ey)
                                    (subst (delete y (delete x (of_val <$> σ))) e)))
      as closed_body_1.
    { repeat constructor; cbn -[union].
      - eapply subst_closed'; last by eapply closed_meta.typing_closed.
        + intros k e'.
          rewrite !lookup_delete_Some lookup_fmap fmap_Some => [[_ [_ [v [_ ->]]]] _].
          eapply closed_mono; [apply empty_subseteq|done|apply val_closed].
        + rewrite !dom_insert !left_id (union_comm {[y]} {[x]}) -!assoc.
          apply union_least; first apply union_subseteq_l.
          apply union_least.
          * etrans; last apply union_subseteq_r.
            apply union_subseteq_l.
          * rewrite !dom_delete => [ξ].
            rewrite !elem_of_union !elem_of_difference !elem_of_singleton dom_fmap !elem_of_dom domσ.
            destruct (decide (ξ = x)); auto.
            destruct (decide (ξ = y)); auto.
      - eapply subst_closed'; last by done.
        + intros k e'.
          rewrite lookup_fmap fmap_Some => [[v [_ ->]] _].
          eapply closed_mono; [apply empty_subseteq|done|apply val_closed].
        + etrans; last apply union_subseteq_r.
          rewrite dom_fmap => [ξ].
          rewrite !elem_of_dom; apply domσ. }
    pose (i := @VRec BAnon x _ closed_body_1).
    match goal with |- context C [ App ?e _ ] =>  change e with (of_val i) end.
    iApply (wp_bind [CAppR i]).
    iPoseProof (simx $! D N σ with "[$env $pre₁]") as "wp".
    iApply (wp_wand with "wp").
    iIntros (vx) "postx"; cbn [fill_ctx fill_ctx_item foldl].
    iApply wp_app; first apply to_of_val.
    cbn [subst' subst Let].
    iDestruct "postx" as (N' D' d') "[names [type₁ [#sim₁ post₁]]]".
    iDestruct "names" as %[ov₁ eqd'].
    rewrite (subst_closed ∅ (subst (of_val <$> σ) ey)); cycle 1.
    { eapply subst_closed'; [| |by eapply closed_meta.typing_closed].
      - intros k e'.
        rewrite lookup_fmap fmap_Some => [[v [_ ->]] _].
        apply val_closed.
      - rewrite left_id => [ξ].
        rewrite dom_fmap !elem_of_dom domσ //. }
    { intros ? []%elem_of_empty. }
    assert (Closed (∅ ∪ {[y]})
                   (subst (delete y (<[x:=of_val vx]>∅))
                          (subst (delete y (delete x (of_val <$> σ))) e)))
      as closed_body_2.
    { rewrite subst_subst.
      apply (subst_closed' (dom _ (<[x:=τ₁]>(<[y:=τ₂]>Γ)))).
      - intros k e'.
        rewrite /subst_merge lookup_merge /subst_merge'.
        destruct (decide (y = k)) as [<-|neqy].
        { rewrite lookup_delete lookup_delete_Some => [[contra _]]; tauto. }
        rewrite lookup_delete_ne //.
        destruct (decide (x = k)) as [<-|neqx].
        { rewrite lookup_delete lookup_delete_ne // lookup_insert.
          injection 1 as <-; intros _.
          eapply closed_mono; [apply empty_subseteq|done|apply val_closed]. }
        rewrite lookup_delete_ne // lookup_fmap.
        destruct (σ !! k) eqn:case; cbn.
        + rewrite subst_val; injection 1 as <-; intros _.
          eapply closed_mono; [apply empty_subseteq|done|apply val_closed].
        + rewrite lookup_delete_Some lookup_insert_ne // lookup_empty.
          intros [_ [=]].
      - rewrite !dom_insert left_id /subst_merge.
        rewrite assoc (union_comm {[x]}) -assoc.
        apply union_mono; first done.
        intros ξ inξ.
        rewrite elem_of_dom lookup_merge /subst_merge'.
        destruct (decide (y = ξ)) as [<-|neqy].
        { rewrite elem_of_union elem_of_singleton in inξ * => [[?|contra]].
          - congruence.
          - rewrite elem_of_dom y_fresh in contra *.
            intros []%is_Some_None. }
        rewrite lookup_delete_ne //.
        rewrite elem_of_union elem_of_singleton in inξ * => [[<-|inΓ]].
        { rewrite lookup_delete lookup_delete_ne // lookup_insert; eauto. }
        assert (x ≠ ξ).
        { intros <-.
          rewrite elem_of_dom x_fresh in inΓ *.
          apply is_Some_None. }
        rewrite !lookup_delete_ne //.
        rewrite lookup_fmap elem_of_dom domσ /= in inΓ * => [[v ->]].
        rewrite /=; eauto.
      - by eapply closed_meta.typing_closed.
      - intros k e'.
        rewrite !lookup_delete_Some lookup_fmap fmap_Some.
        intros [_ [_ [v [_ ->]]]].
        apply val_closed. }
    clear i.
    set (i := @VRec BAnon y _ closed_body_2).
    match goal with |- context C [ App ?e _ ] =>  change e with (of_val i) end.
    iApply (wp_bind [CAppR i]).
    iPoseProof (simy $! (D' ~[conn_heap η₁']~> D) (N' ~[names η₁']~> N) σ with "[env pre₂]")
      as "wp".
    { iSplit.
      - iApply (int_i_env_local with "env").
        + apply overlap_merge_along_r.
          intro n.
          rewrite elem_of_conn_heap elem_of_conn_env.
          intros [? [-> _]] [? [[=] _]].
        + intros ξ inξ.
          destruct (decide (ξ ∈ names η₁')) as [case|case].
          * rewrite lookup_merge_along_in //.
            rewrite (ov₁ ξ) // elem_of_not_new.
            apply typing_good_names in tyx; auto.
            destruct tyx as [disj _].
            intros []%disj; auto using heap_wf_names.
            apply heap_wf_names; done.
          * rewrite lookup_merge_along_not_in //.
        + done.
      - iApply (int_i_heap_local with "pre₂").
        + apply overlap_merge_along_r.
          intro n.
          rewrite !elem_of_conn_heap.
          intros [ξ [-> in₁]] [? [[=<-] in₂]].
          inversion_clear disjη₁.
          by apply (disj ξ).
        + intros ξ inξ.
          destruct (decide (ξ ∈ names η₁')) as [case|case].
          * rewrite lookup_merge_along_in //.
            rewrite (ov₁ ξ) // elem_of_not_new.
            apply typing_good_names in tyx; auto using heap_wf_names.
            destruct tyx as [disj [_ subη]].
            apply subη in case.
            rewrite elem_of_union in case * => [[case|case]].
            -- intros []%disj; auto using heap_wf_names.
            -- apply heap_wf_names in wfη₂.
               apply wfη₂, disj in inξ; done.
          * rewrite lookup_merge_along_not_in //. }
    iApply (wp_wand with "wp").
    iIntros (vy) "post".
    cbn -[not_new].
    iApply wp_app; first apply to_of_val.
    cbn -[not_new].
    iDestruct "post" as (N'' D'' d'') "[names [type₂ [#sim₂ post₂]]]".
    iDestruct "names" as %[ov₂ eqd''].
    rewrite !subst_subst.
    replace (subst_merge (subst_merge (<[y := of_val vy]> ∅)
                                      (delete y (<[x:=of_val vx]> ∅)))
                         (delete y (delete x (of_val <$> σ))))
    with (of_val <$> (<[ x:= vx ]>(<[y := vy]>σ))); cycle 1.
    { apply: map_eq => [z].
      rewrite /subst_merge lookup_merge !fmap_insert /subst_merge'.
      destruct (decide (y = z)) as [<-|neqy].
      { rewrite lookup_insert_ne // lookup_insert lookup_delete lookup_merge lookup_delete
                lookup_insert //. }
      destruct (decide (x = z)) as [<-|neqx].
      { rewrite lookup_insert lookup_delete_ne // lookup_delete lookup_merge lookup_delete_ne //
                lookup_insert subst_val //. }
      rewrite !lookup_insert_ne // !lookup_delete_ne // lookup_fmap.
      destruct (σ !! z) as [v|] eqn:mtz.
      - rewrite /= subst_val //. 
      - rewrite /= lookup_merge lookup_delete_ne // lookup_insert_ne // lookup_empty
                lookup_insert_ne //. }
    2: intros x' e'; rewrite !lookup_delete_Some lookup_fmap fmap_Some => [[_ [_ [v' [_ ->]]]]].
    2: apply val_closed.
    2: intros x' e'; rewrite lookup_delete_Some lookup_insert_Some lookup_empty.
    2: intros [_ [[??]|[_ [=]]]]; subst; apply val_closed.
    iPoseProof (sime $! (<[var x := d']> (<[var y := d'']>
                                          (D'' ~[conn_heap η₂']~> (D' ~[conn_heap η₁']~> D))))
                     (N'' ~[names η₂']~> N') (<[x:=vx]>(<[y:=vy]>σ))
                with "[-]") as "wp".
    { iSplitL "type₁ type₂".
      { iDestruct "env" as "[_ env]".
        iSplit; first iPureIntro.
        { split.
          - intro z.
            rewrite -!(elem_of_dom (D:=gset string)) !dom_insert !elem_of_union !elem_of_dom domσ //.
          - intro z.
            rewrite -!(elem_of_dom (D:=gset string)) -(elem_of_dom (D:=gset conn_name)).
            rewrite !dom_insert !elem_of_union !elem_of_dom.
            rewrite !elem_of_singleton.
            intros [->|[->|inz%domD]]; auto.
            right; right.
            destruct (decide (var z ∈ conn_heap η₂')) as [inD''|notinD''].
            { rewrite lookup_merge_along_in //.
              
    }
    iApply (wp_wand with "wp").
End Commutativity.