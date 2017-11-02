From iris.proofmode Require Import tactics.
From esop Require Import corecalculus types delayed closed_meta closure typetranslation
     specification overlap.
From stdpp Require Import gmap.

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
End SimpleRules.