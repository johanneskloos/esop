From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import fancy_updates.
From esop Require Import types delayed closure types corecalculus specification typetranslation
     exprfacts overlap closed_meta.
From stdpp Require Import gmap coPset.

Section Commutativity.
  Context `{allG Σ}.
  Coercion BNamed: string >-> binder.
  Context (Γ: env) (η₁ η₁' η₂ η₂' η': hexpr) (τ₁ τ₂ τ: type) (U A₁ A₂ A: lnames) (e₁ e₂ e: expr).
  Context (x y: string) (neq: x ≠ y).
  Context (wf_U_η₁: heap_wf U η₁) (wf_U_η₂: heap_wf U η₂) (η₁₂_nov: res_names η₁ ⊥ res_names η₂).
  Context (wf_UA₂_η₁: heap_wf (U ∪ A₂) η₁) (wf_UA₁_η₂: heap_wf (U ∪ A₁) η₂).
  Context (η₁'₂_nov: res_names η₁' ⊥ res_names η₂) (η₁₂'_nov: res_names η₁ ⊥ res_names η₂').
  Context (wf_UA₁₂_η₁'₂: heap_wf (U ∪ A₁ ∪ A₂) (η₁' ⊗ η₂')).
  Context (ty₁: typing U Γ e₁ η₁ A₁ τ₁ η₁').
  Context (ty₂: typing U Γ e₂ η₂ A₂ τ₂ η₂').
  Context (ty: typing (U ∪ A₁ ∪ A₂) (<[x:=τ₁]>(<[y:=τ₂]>Γ)) e (η₁' ⊗ η₂') A τ η').
  Context (disjA: A₁ ⊥ A₂) (goodΓ: names Γ ⊆ U) (x_fresh: Γ!!x = None) (y_fresh: Γ!!y = None).

  Lemma wf_UA₁_η₁': heap_wf (U ∪ A₁) η₁'.
  Proof. by eapply typing_wf. Qed.
  Lemma wf_UA₂_η₂': heap_wf (U ∪ A₂) η₂'.
  Proof. by eapply typing_wf. Qed.

  Lemma names_η₁: names η₁ ⊆ U.
  Proof. by apply heap_wf_names. Qed.
  Lemma names_η₂: names η₂ ⊆ U.
  Proof. by apply heap_wf_names. Qed.
  Lemma names_η₁': names η₁' ⊆ U ∪ A₁.
  Proof. by apply heap_wf_names, wf_UA₁_η₁'. Qed.
  Lemma names_η₂': names η₂' ⊆ U ∪ A₂.
  Proof. by apply heap_wf_names, wf_UA₂_η₂'. Qed.

  Lemma wf_UA₁_η₁'₂: heap_wf (U ∪ A₁) (η₁' ⊗ η₂).
  Proof. constructor; auto using wf_UA₁_η₁'. Qed.
  Lemma wf_UA₂_η₁₂': heap_wf (U ∪ A₂) (η₁ ⊗ η₂').
  Proof. constructor; auto using wf_UA₂_η₂'. Qed.

  
  Lemma disj_U_A₁: A₁ ⊥ U.
  Proof. eapply typing_good_names; eauto using names_η₁. Qed.
  Lemma disj_U_A₂: A₂ ⊥ U.
  Proof. eapply typing_good_names; eauto using names_η₂. Qed.
    
  Lemma ty₁_η₂: typing U Γ e₁ (η₁ ⊗ η₂) A₁ τ₁ (η₁' ⊗ η₂).
  Proof.
    constructor; auto.
    intros ξ inA₁ ?%names_η₂%disj_U_A₁; done.
  Qed.
  Lemma ty₂_η₁: typing U Γ e₂ (η₁ ⊗ η₂) A₂ τ₂ (η₁ ⊗ η₂').
  Proof.
    rewrite !(comm hstar η₁).
    constructor; auto.
    intros ξ inA₂ ?%names_η₁%disj_U_A₂; done.
  Qed.
  Lemma ty₁_η₂': typing (U ∪ A₂) Γ e₁ (η₁ ⊗ η₂') A₁ τ₁ (η₁' ⊗ η₂').
  Proof.
    constructor; auto.
    - by inversion_clear wf_UA₁₂_η₁'₂.
    - intros ξ inA₁ [?|?]%names_η₂'%elem_of_union.
      + by apply (disj_U_A₁ ξ).
      + by apply (disjA ξ).
    - rewrite -union_assoc_L (union_comm_L A₂) union_assoc_L.
      by inversion_clear wf_UA₁₂_η₁'₂.
    - eapply tyweaken; last done.
      all: auto using names_η₁.
      + rewrite disjoint_union_l; split; auto.
        symmetry; apply disj_U_A₁.
      + apply union_subseteq_l.
      + rewrite union_assoc_L (union_comm_L A₁).
        by inversion_clear wf_UA₁₂_η₁'₂.
  Qed.
  Lemma ty₂_η₁': typing (U ∪ A₁) Γ e₂ (η₁' ⊗ η₂) A₂ τ₂ (η₁' ⊗ η₂').
  Proof.
    rewrite !(comm hstar η₁').
    constructor; auto.
    - by inversion_clear wf_UA₁₂_η₁'₂.
    - intros ξ inA₁ [?|?]%names_η₁'%elem_of_union.
      + by apply (disj_U_A₂ ξ).
      + by apply (disjA ξ).
    - by inversion_clear wf_UA₁₂_η₁'₂.
    - eapply tyweaken; last done.
      all: auto using names_η₂.
      + rewrite disjoint_union_l; split; auto.
        symmetry; apply disj_U_A₂.
      + apply union_subseteq_l.
      + rewrite (union_comm_L A₂).
        by inversion_clear wf_UA₁₂_η₁'₂.
  Qed.
  Lemma ty₂_with_x: typing (U ∪ A₁) (<[x:=τ₁]>Γ) e₂ (η₁' ⊗ η₂) A₂ τ₂ (η₁' ⊗ η₂').
  Proof.
    eapply tyweaken;last apply ty₂_η₁'.
    all: try done.
    - etrans; first done.
      apply union_subseteq_l.
    - apply union_least; auto using names_η₁'.
      etrans; first apply names_η₂.
      apply union_subseteq_l.
    - rewrite disjoint_union_l.
      split; auto.
      symmetry; auto using disj_U_A₂.
    - by apply insert_subseteq.
    - by rewrite (union_comm_L A₂).
  Qed.
  Lemma ty₁_with_x: typing (U ∪ A₂) (<[y:=τ₂]>Γ) e₁ (η₁ ⊗ η₂') A₁ τ₁ (η₁' ⊗ η₂').
  Proof.
    eapply tyweaken;last apply ty₁_η₂'.
    all: try done.
    - etrans; first done.
      apply union_subseteq_l.
    - apply union_least; auto using names_η₂'.
      etrans; first apply names_η₁.
      apply union_subseteq_l.
    - rewrite disjoint_union_l.
      split; auto.
      symmetry; auto using disj_U_A₁.
    - by apply insert_subseteq.
    - by rewrite union_assoc_L (union_comm_L A₁).
  Qed.

  Lemma type_x_first:
    typing U Γ (Let x e₁ (Let y e₂ e)) (η₁ ⊗ η₂) (A₁ ∪ A₂ ∪ A) τ η'.
  Proof.
    rewrite -union_assoc_L.
    eapply tylet; first apply ty₁_η₂.
    eapply tylet; first apply ty₂_with_x.
    rewrite /= insert_commute //.
  Qed.
  Lemma type_y_first:
    typing U Γ (Let y e₂ (Let x e₁ e)) (η₁ ⊗ η₂) (A₁ ∪ A₂ ∪ A) τ η'.
  Proof.
    rewrite (union_comm_L A₁) -union_assoc_L.
    eapply tylet; first apply ty₂_η₁.
    eapply tylet; first apply ty₁_with_x.
    rewrite -union_assoc_L (union_comm_L A₂) union_assoc_L //.
  Qed.

  Lemma names_τ₁: names τ₁ ⊆ U ∪ A₁.
  Proof. eapply typing_good_names; eauto using heap_wf_names. Qed.
  Lemma names_τ₂: names τ₂ ⊆ U ∪ A₂.
  Proof. eapply typing_good_names; eauto using heap_wf_names. Qed.
  
  Lemma sim_e₁: delayed_typed Γ η₁ e₁ e₁ A₁ τ₁ η₁'.
  Proof. eapply fundamental; last done; auto. Qed.
  Lemma sim_e₂: delayed_typed Γ η₂ e₂ e₂ A₂ τ₂ η₂'.
  Proof. eapply fundamental; last done; auto. Qed.
  Lemma sim_e: delayed_typed (<[x:=τ₁]>(<[y:=τ₂]>Γ)) (η₁' ⊗ η₂') e e A τ η'.
  Proof.
    eapply fundamental; last done; auto.
    etrans; first apply names_env_insert.
    apply union_least.
    { etrans; first apply names_τ₁.
      apply union_subseteq_l. }
    etrans; first apply names_env_insert.
    apply union_least.
    { etrans; first apply names_τ₂.
      apply union_mono; last done.
      apply union_subseteq_l. }
    etrans; first done.
    rewrite -assoc.
    apply union_subseteq_l.
  Qed.

  Lemma val_closed' X v: Closed X (of_val v).
  Proof.
    eapply closed_mono.
    - apply empty_subseteq.
    - done.
    - apply val_closed.
  Qed.
  
  Lemma subst_closed'' (X X': gset string) (σ: gmap string val) e':
    X ⊆ X' ∪ dom _ σ → Closed X e' → Closed X' (subst (of_val <$> σ) e').
  Proof.
    intro subX.
    apply subst_closed'.
    - intros k e''.
      rewrite lookup_fmap fmap_Some => [[v [_ ->]] _].
      apply val_closed'.
    - by rewrite dom_fmap.
  Qed.

  Lemma subst_singleton_subst_delete z v σ e':
    subst (<[z:=of_val v]>∅) (subst (delete z (of_val <$> σ)) e') =
    subst (of_val <$> (<[z:=v]>σ)) e'.
  Proof.
    rewrite subst_subst.
    2: intros x' e''; rewrite -fmap_delete lookup_fmap fmap_Some => [[w [_ ->]]]; apply val_closed.
    f_equiv.
    apply map_eq; intro u.
    destruct (decide (u = z)) as [<-|nequ].
    { rewrite /subst_merge lookup_merge /subst_merge' lookup_delete lookup_fmap !lookup_insert //. }
    rewrite /subst_merge lookup_merge /subst_merge' lookup_delete_ne // !lookup_insert_ne //.
    rewrite !lookup_fmap lookup_insert_ne //.
    destruct (σ !! u).
    - rewrite /= subst_val //.
    - rewrite /= lookup_empty //.
  Qed.
  
  Lemma sim_main: delayed_typed Γ (η₁ ⊗ η₂)
                                (Let y e₂ (Let x e₁ e))
                                (Let x e₁ (Let y e₂ e))
                                (A₁ ∪ A₂ ∪ A) τ η'.
  Proof.
    iIntros (D N σ) "[#env [pre₁ pre₂]]".
    iPoseProof (sim_e₂ $! D N with "[$env $pre₂]") as "sim".
    iPoseProof "env" as "[env_names _]".
    iDestruct "env_names" as %[domσ domD].
    assert (domσ': dom (gset string) Γ ≡ dom _ σ).
    { intro; rewrite !elem_of_dom //. }
    assert (Closed (∅ ∪ {[y]}) (subst (delete y (of_val <$> σ)) (Let x e₁ e))) as closed.
    { rewrite -fmap_delete.
      apply (subst_closed'' (dom _ (<[y:=τ₂]>Γ))).
      - rewrite dom_delete left_id.
        rewrite union_comm difference_union dom_insert union_comm domσ' //.
      - repeat constructor.
        + rewrite /= left_id -(dom_insert _ x τ₁).
          by eapply typing_closed.
        + eapply closed_mono.
          * rewrite dom_insert; apply union_subseteq_r.
          * done.
          * by eapply typing_closed. }
    iApply (wp_bind [CAppR (@VRec BAnon y _ closed)] ⊤ (subst (of_val <$> σ) e₂)).
    iApply (wp_wand with "sim").
    iIntros (v₂) "post".
    iDestruct "post" as (N₂ D₂ d₂) "[names [type₂ [#sim₂ post₂]]]".
    iDestruct "names" as %[ov₂ eqd₂].
    iApply wp_app; first apply to_of_val.
    rewrite /= delete_commute.
    rewrite subst_singleton_subst_delete.
    rewrite delete_insert_ne // delete_empty -fmap_delete.
    rewrite (subst_singleton_subst_delete y v₂ (delete x σ)).
    clear closed.
    assert (Closed (∅ ∪ {[x]}) (subst (of_val <$> <[y:=v₂]> (delete x σ)) e)) as closed.
    { apply (subst_closed'' (dom _ (<[x:=τ₁]>(<[y:=τ₂]>Γ)))).
      - rewrite left_id dom_insert comm -assoc dom_delete difference_union !dom_insert.
        rewrite assoc -(union_comm {[x]}) assoc (union_comm {[x]}) domσ' //.
      - by eapply typing_closed. }
    rewrite (subst_local (dom _ Γ) e₁ _ _ (of_val <$> σ)).
    2: by eapply typing_closed.
    2: intros z inz; rewrite fmap_insert lookup_insert_ne //.
    2: intros <-; rewrite elem_of_dom y_fresh in inz * => [[??]] //.
    iApply (wp_bind [CAppR (@VRec BAnon x _ closed)] ⊤ (subst (of_val <$> σ) e₁)).
    set (D₂' := D₂ ~[conn_heap η₂']~> D).
    set (N₂' := N₂ ~[A₂]~> N).
    iAssert (int_i_heap η₁ D₂' N₂') with "[pre₁]" as "pre₁".
    { iApply (int_i_heap_local with "pre₁").
      - apply overlap_merge_along_r.
        intros n.
        rewrite !elem_of_conn_heap => [[ξ [-> in₁]] [? [eqξ in₂]]].
        injection eqξ as <-.
        apply (η₁₂'_nov ξ); done.
      - intros ξ inξ%names_η₁.
        rewrite lookup_merge_along_not_in //.
        intros inξ'%disj_U_A₂; auto. }
    iAssert (int_i_env Γ D₂' N₂' σ) as "env'".
    { iApply (int_i_env_local with "env").
      - apply overlap_merge_along_r.
        intros n.
        rewrite elem_of_conn_heap elem_of_conn_env => [[? [-> _]] [? [? ]]] //.
      - intros ξ inξ%goodΓ.
        rewrite lookup_merge_along_not_in //.
        intros inξ'%disj_U_A₂; auto.
      - done. }
    iPoseProof (sim_e₁ with "[$env' $pre₁]") as "sim".
    iApply (wp_wand with "sim").
    iIntros (v₁) "post".
    iDestruct "post" as (N₁ D₁ d₁) "[names [type₁ [#sim₁ post₁]]]".
    iDestruct "names" as %[ov₁ eqd₁].
    iApply wp_app; first apply to_of_val.
    rewrite /= -delete_insert_ne // fmap_delete subst_singleton_subst_delete.
    set (D'' := <[var x:=d₁]>(<[var y:=d₂]>(D₁ ~[conn_heap η₁']~> (D₂ ~[conn_heap η₂']~> D)))).
    set (N'' := N₁ ~[A₁]~> (N₂ ~[A₂]~> N)).
    assert (D'' !! var x = Some d₁) by rewrite lookup_insert //.
    assert (D'' !! var y = Some d₂) by (rewrite lookup_insert_ne ?lookup_insert //; congruence).
    assert (D'' ≡[conn_env Γ]≡ D).
    { intros n.
      rewrite elem_of_conn_env => [[z [-> inz]]].
      rewrite lookup_insert_ne.
      2: injection 1 as <-; rewrite x_fresh in inz; by apply is_Some_None in inz.
      rewrite lookup_insert_ne.
      2: injection 1 as <-; rewrite y_fresh in inz; by apply is_Some_None in inz.
      rewrite lookup_merge_along_not_in.
      2: rewrite elem_of_conn_heap => [[? [? _]]] //.
      rewrite lookup_merge_along_not_in // elem_of_conn_heap => [[? [? _]]] //. }
    assert (D'' ≡[conn_heap η₁']≡ D₁).
    { intros n.
      rewrite elem_of_conn_heap => [[z [-> inz]]].
      rewrite !lookup_insert_ne //.
      rewrite lookup_merge_along_in //.
      rewrite elem_of_conn_heap; eauto. }
    assert (D'' ≡[conn_heap η₂']≡ D₂).
    { intros n.
      rewrite elem_of_conn_heap => [[z [-> inz]]].
      rewrite !lookup_insert_ne //.
      rewrite lookup_merge_along_not_in.
      2: rewrite elem_of_conn_heap => [[? [eqξ inz']]]; injection eqξ as <-.
      2: inversion_clear wf_UA₁₂_η₁'₂; eapply disj; done.
      rewrite lookup_merge_along_in //.
      rewrite elem_of_conn_heap; eauto. }
    assert (ov_disj_A₁: ∀ X, X ⊥ A₁ → N'' ≡[X]≡ N₂).
    { intros X disj ξ inξ.
      rewrite lookup_merge_along_not_in.
      - destruct (decide (ξ ∈ A₂)); first by rewrite lookup_merge_along_in.
        rewrite lookup_merge_along_not_in // (ov₂ ξ) // elem_of_not_new //.
      - exact (disj ξ inξ). }
    assert (N'' ≡[names τ₂]≡ N₂).
    { apply ov_disj_A₁.
      intros ξ [inξ|inξ]%names_τ₂%elem_of_union inA.
      - by apply (disj_U_A₁ ξ).
      - by apply (disjA ξ). }
    assert (N'' ≡[names η₂']≡ N₂).
    { apply ov_disj_A₁.
      intros ξ [inξ|inξ]%names_η₂'%elem_of_union inA.
      - by apply (disj_U_A₁ ξ).
      - by apply (disjA ξ). }
    assert (ov_disj_A₂: ∀ X, X ⊥ A₂ → N'' ≡[X]≡ N₁).
    { intros X disj ξ inξ.
      destruct (decide (ξ ∈ A₁));first by rewrite lookup_merge_along_in.
      assert (ξ ∉ A₂).
      { exact (disj ξ inξ). }
      rewrite !lookup_merge_along_not_in //.
      rewrite -(ov₁ ξ) ?elem_of_not_new //.
      rewrite lookup_merge_along_not_in //. }
    assert (N'' ≡[names τ₁]≡ N₁).
    { apply ov_disj_A₂.
      intros ξ [inξ|inξ]%names_τ₁%elem_of_union inA.
      - by apply (disj_U_A₂ ξ).
      - by apply (disjA ξ). }
    assert (N'' ≡[names η₁']≡ N₁).
    { apply ov_disj_A₂.
      intros ξ [inξ|inξ]%names_η₁'%elem_of_union inA.
      - by apply (disj_U_A₂ ξ).
      - by apply (disjA ξ). }
    iAssert (int_i_heap η₁' D'' N'') with "[post₁]" as "pre₁".
    { by iApply (int_i_heap_local with "post₁"). }
    iAssert (int_i_heap η₂' D'' N'') with "[post₂]" as "pre₂".
    { iApply (int_i_heap_local with "post₂"); try done. }
    iAssert (int_i_type τ₁ d₁ N'' v₁) with "[type₁]" as "type₁".
    { by iApply (int_i_type_local with "type₁"). }
    iAssert (int_i_type τ₂ d₂ N'' v₂) with "[type₂]" as "type₂".
    { by iApply (int_i_type_local with "type₂"). }
    iAssert (int_i_env Γ D'' N'' σ) as "env'".
    { iApply (int_i_env_local with "env"); try done.
      intros ξ inξ%goodΓ.
      rewrite !lookup_merge_along_not_in //.
      - by intro; apply disj_U_A₂ in inξ.
      - by intro; apply disj_U_A₁ in inξ. }
    iAssert (int_i_env (<[x:=τ₁]>(<[y:=τ₂]>Γ)) D'' N'' (<[x:=v₁]>(<[y:=v₂]>σ)))
    with "[env' type₁ type₂]" as "env'". {
      iDestruct "env'" as "[_ env_types]".
      iSplit.
      - iPureIntro.
        split; intro z.
        + rewrite -!(elem_of_dom (D:=gset string)) !dom_insert !elem_of_union !elem_of_dom domσ //.
        + rewrite -(elem_of_dom (D:=gset string)) -(elem_of_dom (D:=gset conn_name)).
          rewrite !dom_insert !elem_of_union !elem_of_singleton !elem_of_dom.
          intros [->|[->|inz]]; auto.
          do 2 right.
          rewrite !lookup_merge_along_not_in; auto.
          all: rewrite elem_of_conn_heap => [[? [? _]]] //.
      - iIntros (x' τ' v' d' [mtτ [mtv mtd]]).
        rewrite !lookup_insert_Some in mtτ * => cases.
        destruct cases as [[<- <-]|[neqx [[<- <-]|[neqy mtx]]]].
        + rewrite lookup_insert in mtd; injection mtd as <-.
          rewrite lookup_insert in mtv; injection mtv as <-.
          done.
        + rewrite lookup_insert_ne in mtd; last congruence.
          rewrite lookup_insert in mtd; injection mtd as <-.
          rewrite lookup_insert_ne // lookup_insert in mtv; injection mtv as <-.
          done.
        + rewrite !lookup_insert_ne // in mtv.
          iApply ("env_types" $! x').
          iPureIntro; red; auto. }
    iPoseProof (sim_e with "[$env' $pre₁ $pre₂]") as "sim".
    iApply (wp_wand with "sim").
    iIntros (v) "post".
    iDestruct "post" as (N' D' d') "[names [type [#sim post]]]".
    iExists N', D', d'; iFrame.
    iDestruct "names" as %[ov eqd'].
    iSplit.
    { iPureIntro; split; auto.
      trans N''.
      - intro ξ.
        rewrite elem_of_not_new !not_elem_of_union => [[[notA₁ notA₂] notA]].
        rewrite !lookup_merge_along_not_in //.
      - eapply overlap_sub; last done.
        intro; rewrite !elem_of_not_new !not_elem_of_union; tauto. }
    iClear "env".
    generalize dependent N.
    intros ? _ _ _ ? _ _ _ _ _ _ _.
    clear N'' N' N₁ N₂ N σ domσ v v₁ v₂ domσ' closed.
    iAlways.
    iIntros (N σ p K) "#ctx [#env pre] move".
    cbn [int_s_heap].
    rewrite int_s_heap_split.
    iDestruct "pre" as "[pre₁ pre₂]".
    iAssert (int_s_heap η₁ D₂' N) with "[pre₁]" as "pre₁".
    { iApply (int_s_heap_local with "pre₁"); last done.
      apply overlap_merge_along_r.
      intro n.
      rewrite !elem_of_conn_heap => [[ξ [-> inξ]] [? [eqξ inξ']]].
      injection eqξ as <-.
      apply (η₁₂'_nov ξ); done. }
    iAssert (int_s_env Γ D₂' N σ) as "env'".
    { iApply (int_s_env_local with "env").
      2,3: done.
      intro n.
      rewrite elem_of_conn_env => [[z [-> inz]]].
      rewrite lookup_merge_along_not_in //.
      rewrite elem_of_conn_heap => [[? [? _]]] //. }
    iPoseProof "env" as "[env_names _]".
    iDestruct "env_names" as %[domσ _].
    assert (dom (gset string) Γ ≡ dom _ σ) as domσ'.
    { intro; rewrite !elem_of_dom //. }
    assert (closed: Closed (∅ ∪ {[x]}) (subst (delete x (of_val <$> σ)) (Let y e₂ e))).
    { rewrite -fmap_delete.
      apply (subst_closed'' (dom _ (<[x:=τ₁]>Γ))).
      - rewrite left_id comm dom_delete difference_union dom_insert domσ' comm //.
      - repeat constructor.
        + rewrite /= left_id -(dom_insert _ y τ₂) insert_commute //.
          eapply typing_closed; eauto.
        + rewrite dom_insert.
          eapply closed_mono.
          * apply union_subseteq_r.
          * done.
          * by eapply typing_closed. }
    change (subst (of_val <$> σ) (Let x e₁ (Let y e₂ e)))
    with (fill_ctx (subst (of_val <$> σ) e₁) [CAppR (@VRec BAnon x _ closed)]).
    rewrite fill_ctx_app.
    iMod ("sim₁" with "ctx [$env' $pre₁] move") as (v₁) "[post move]".
    iDestruct "post" as (d₁' N₁) "[names [type₁ post₁]]".
    iDestruct "names" as %[ov₁ eqd].
    rewrite eqd₁ in eqd; injection eqd as <-.
    rewrite -fill_ctx_app.
    cbn -[Let not_new].
    iMod (simulate_app with "ctx move") as "move"; first done.
    { apply to_of_val. }
    rewrite /= subst_singleton_subst_delete.
    rewrite delete_commute delete_insert_ne //.
    rewrite delete_empty -fmap_delete subst_singleton_subst_delete.
    clear closed.
    assert (Closed (∅ ∪ {[y]}) (subst (of_val <$> <[x:=v₁]>(delete y σ)) e)) as closed.
    { apply (subst_closed'' (dom _ (<[x:=τ₁]>(<[y:=τ₂]>Γ)))).
      2: by eapply typing_closed.
      rewrite left_id comm !dom_insert domσ' -assoc dom_delete difference_union.
      rewrite -(union_comm {[y]}) //. }
    match goal with |- context C [ fill_ctx ?e _ ] =>
                    change e with
                    (fill_ctx (subst (of_val <$> <[x:=v₁]>σ) e₂)
                              [CAppR (@VRec BAnon y _ closed)])
    end.
    rewrite fill_ctx_app.
    rewrite fmap_insert (subst_local (dom _ Γ) e₂ _ _ (of_val <$> σ)).
    2: by eapply typing_closed.
    2: intro z; rewrite elem_of_dom => [inz].
    2: apply lookup_insert_ne; intros <-.
    2: rewrite x_fresh in inz; by apply is_Some_None in inz.
    iMod ("sim₂" with "ctx [$env $pre₂] move") as (v₂) "[post move]".
    iDestruct "post" as (d₂' N₂) "[names [type₂ post₂]]".
    iDestruct "names" as %[ov₂ eqd].
    rewrite eqd₂ in eqd; injection eqd as <-.
    rewrite -fill_ctx_app /=.
    iMod (simulate_app with "ctx move") as "move"; first done.
    { apply to_of_val. }
    rewrite /= -delete_insert_ne // fmap_delete subst_singleton_subst_delete.
    rewrite insert_commute //.
    set (N'' := N₁ ~[A₁]~> (N₂ ~[A₂]~> N)).
    assert (ov_disj_A₁: ∀ X, X ⊥ A₁ → N'' ≡[X]≡ N₂).
    { intros X disj ξ inξ.
      rewrite lookup_merge_along_not_in.
      - destruct (decide (ξ ∈ A₂)); first by rewrite lookup_merge_along_in.
        rewrite lookup_merge_along_not_in // (ov₂ ξ) // elem_of_not_new //.
      - exact (disj ξ inξ). }
    assert (N'' ≡[names τ₂]≡ N₂).
    { apply ov_disj_A₁.
      intros ξ [inξ|inξ]%names_τ₂%elem_of_union inA.
      - by apply (disj_U_A₁ ξ).
      - by apply (disjA ξ). }
    assert (N'' ≡[names η₂']≡ N₂).
    { apply ov_disj_A₁.
      intros ξ [inξ|inξ]%names_η₂'%elem_of_union inA.
      - by apply (disj_U_A₁ ξ).
      - by apply (disjA ξ). }
    assert (ov_disj_A₂: ∀ X, X ⊥ A₂ → N'' ≡[X]≡ N₁).
    { intros X disj ξ inξ.
      destruct (decide (ξ ∈ A₁));first by rewrite lookup_merge_along_in.
      assert (ξ ∉ A₂).
      { exact (disj ξ inξ). }
      rewrite !lookup_merge_along_not_in //.
      rewrite -(ov₁ ξ) ?elem_of_not_new //. }
    assert (N'' ≡[names τ₁]≡ N₁).
    { apply ov_disj_A₂.
      intros ξ [inξ|inξ]%names_τ₁%elem_of_union inA.
      - by apply (disj_U_A₂ ξ).
      - by apply (disjA ξ). }
    assert (N'' ≡[names η₁']≡ N₁).
    { apply ov_disj_A₂.
      intros ξ [inξ|inξ]%names_η₁'%elem_of_union inA.
      - by apply (disj_U_A₂ ξ).
      - by apply (disjA ξ). }
    iAssert (int_s_heap η₁' D'' N'') with "[post₁]" as "pre₁".
    { by iApply (int_s_heap_local with "post₁"). }
    iAssert (int_s_heap η₂' D'' N'') with "[post₂]" as "pre₂".
    { iApply (int_s_heap_local with "post₂"); try done. }
    iAssert (int_s_type τ₁ d₁ N'' v₁) with "[type₁]" as "type₁".
    { by iApply (int_s_type_local with "type₁"). }
    iAssert (int_s_type τ₂ d₂ N'' v₂) with "[type₂]" as "type₂".
    { by iApply (int_s_type_local with "type₂"). }
    iAssert (int_s_env Γ D'' N'' σ) as "env'".
    { iApply (int_s_env_local with "env"); try done.
      intros ξ inξ%goodΓ.
      rewrite !lookup_merge_along_not_in //.
      - by intro; apply disj_U_A₂ in inξ.
      - by intro; apply disj_U_A₁ in inξ. }
    iAssert (int_s_env (<[x:=τ₁]>(<[y:=τ₂]>Γ)) D'' N'' (<[x:=v₁]>(<[y:=v₂]>σ)))
    with "[env' type₁ type₂]" as "env'". {
      iDestruct "env'" as "[_ env_types]".
      iSplit.
      - iPureIntro.
        split; intro z.
        + rewrite -!(elem_of_dom (D:=gset string)) !dom_insert !elem_of_union !elem_of_dom domσ //.
        + rewrite -(elem_of_dom (D:=gset string)) -(elem_of_dom (D:=gset conn_name)).
          rewrite !dom_insert !elem_of_union !elem_of_singleton !elem_of_dom.
          intros [->|[->|inz]]; auto.
          do 2 right.
          rewrite !lookup_merge_along_not_in; auto.
          all: rewrite elem_of_conn_heap => [[? [? _]]] //.
      - iIntros (x' τ' v' d'' [mtτ [mtv mtd]]).
        rewrite !lookup_insert_Some in mtτ * => cases.
        destruct cases as [[<- <-]|[neqx [[<- <-]|[neqy mtx]]]].
        + rewrite lookup_insert in mtd; injection mtd as <-.
          rewrite lookup_insert in mtv; injection mtv as <-.
          done.
        + rewrite lookup_insert_ne in mtd; last congruence.
          rewrite lookup_insert in mtd; injection mtd as <-.
          rewrite lookup_insert_ne // lookup_insert in mtv; injection mtv as <-.
          done.
        + rewrite !lookup_insert_ne // in mtv.
          iApply ("env_types" $! x').
          iPureIntro; red; auto. }
    iMod ("sim" with "ctx [$env' pre₁ pre₂] move") as (v) "[post move]".
    { rewrite int_s_heap_split; iFrame. }
    iModIntro; iExists v; iFrame.
    iDestruct "post" as (d N') "[names rest]".
    iExists d, N'; iFrame.
    iDestruct "names" as %[eqN eqd].
    iPureIntro; split; auto.
    trans N''.
    - intros ξ.
      rewrite elem_of_not_new !not_elem_of_union => [[[notA₁ notA₂] notA]].
      rewrite !lookup_merge_along_not_in //.
    - eapply overlap_sub; last done.
      intro.
      rewrite !elem_of_not_new !not_elem_of_union.
      tauto.
  Qed.

  Lemma sound_commute:
    delayed_simulation U Γ (η₁ ⊗ η₂)
                       (Let y e₂ (Let x e₁ e))
                       (Let x e₁ (Let y e₂ e))
                       (A₁ ∪ A₂ ∪ A) τ η'.
  Proof.
    split.
    - apply union_least; first done.
      apply union_least; apply heap_wf_names; done.
    - apply type_y_first.
    - apply type_x_first.
    - apply sim_main.
  Qed.
  
End Commutativity.