From iris.proofmode Require Import tactics classes.
From iris.base_logic.lib Require Import invariants own.
From iris.algebra Require Import updates agree big_op.
From esop Require Import types oneshot specification corecalculus overlap.
From stdpp Require Import gmap coPset.

Variant name_entry := Loc (l: loc) | Task (t: tid) (γ: gname).
Definition name_map := gmap gname name_entry.
Variant conn_name := RET | name (ξ: gname) | var (x: string).
Instance: EqDecision conn_name.
Proof. solve_decision. Defined.
Definition conn_name_encode c :=
  (match c with RET => 1 | name ξ => ξ~0 | var x => (encode x)~1 end)%positive.
Definition conn_name_decode p :=
  (match p with 1 => Some RET | ξ~0 => Some (name ξ) | x~1 => var <$> decode x end)%positive.
Instance: Countable conn_name :=
  Build_Countable conn_name _ conn_name_encode conn_name_decode _.
Proof.
  destruct x; auto.
  rewrite /conn_name_encode /conn_name_decode decode_encode; done.
Qed.

Definition conn_map := gmap conn_name val.
Definition int_type {Σ} := val → name_map → val → iProp Σ.
Definition int_heap {Σ} := conn_map → name_map → iProp Σ.

Definition names_heap (η: types.heap): gset conn_name := of_list (name <$> (elements (names η))).
Lemma elem_of_names_heap (d: conn_name) η:
  (d ∈ names_heap η ↔ ∃ ξ: gname, d = name ξ ∧ ξ ∈ names η)%type.
Proof.
  rewrite /names_heap elem_of_of_list elem_of_list_fmap.
  f_equiv; intro ξ. by rewrite elem_of_elements.
Qed.

Definition names_env (Γ: env): gset conn_name := of_list (var <$> fst <$> map_to_list Γ).
Lemma elem_of_names_env n (Γ: env): n ∈ names_env Γ ↔ ∃ x, n = var x ∧ is_Some (Γ !! x).
Proof.
  rewrite /names_env elem_of_of_list -list_fmap_compose elem_of_list_fmap.
  split.
  { intros [[x τ] [-> isin%elem_of_map_to_list]].
    eauto.
  } {
    intros [x [-> [τ isin%elem_of_map_to_list]]].
    exists (x,τ); auto.
  }
Qed.
Lemma env_elem_of_names ξ (Γ: env): ξ ∈ names Γ ↔ ∃ x τ, Γ !! x = Some τ ∧ ξ ∈ names τ.
Proof.
  rewrite {1}/names /Names_instance_2.
  induction Γ as [|x τ] using map_ind.
  { rewrite big_opM_empty elem_of_empty.
    setoid_rewrite lookup_empty.
    firstorder. }
  rewrite big_opM_insert; last done.
  rewrite elem_of_union IHΓ.
  split.
  { intros [inξ|[x' [τ' [lookup inξ]]]].
    - exists x, τ.
      rewrite lookup_insert; auto.
    - exists x', τ'.
      rewrite lookup_insert_ne; auto.
      intros <-.
      rewrite H in lookup; discriminate. }
  intros [x' [τ' [mt inξ]]].
  destruct (decide (x=x')) as [<-|neq].
  { rewrite lookup_insert in mt.
    injection mt as <-; auto. }
  rewrite lookup_insert_ne in mt; last done.
  eauto.
Qed.

Record task_data :=
  TaskData {
      td_expr: expr;
      td_env: env;
      td_pre: types.heap;
      td_post: types.heap;
      td_alloc: gset gname;
      td_D_pre: conn_map;
      td_D_name: gname;
      td_N_name: gname
    }.
Canonical Structure task_dataC := leibnizC task_data.
Canonical Structure conn_mapC := leibnizC conn_map.
Canonical Structure name_mapC := leibnizC name_map.
Class taskDataG Σ :=
  { td_taskData_inG:> inG Σ (agreeR task_dataC);
    td_connData_inG:> inG Σ (oneshotR conn_mapC);
    td_nameData_inG:> inG Σ (oneshotR name_mapC) }.
Local Open Scope I.

Definition intΓ {Σ} (iτ: type → int_type) (Γ: env) (D: conn_map) (N: name_map)
           (σ: gmap string val): iProp Σ :=
  ⌜(∀ x: string, is_Some (Γ !! x) ↔ is_Some (σ !! x)) ∧
   (∀ x: string, is_Some (Γ !! x) → is_Some (D !! var x))⌝ ∧
  ∀ (x: string) τ v d, ⌜Γ !! x = Some τ ∧
                       σ !! x = Some v ∧
                       D !! var x = Some d⌝ → iτ τ d N v.

Definition not_new A: coPset := ⊤ ∖ of_gset A.
Class InitialConfiguration := initial_cfg: cfg.
Class WaitPermissions :=
  { wp_axiomaticIrisG: gFunctors → Set;
    wp_axiomatic_implies_inv :> ∀ `{wp_axiomaticIrisG Σ}, invG Σ;
    wp_wait: ∀ `{wp_axiomaticIrisG Σ}, tid → (val → iProp Σ) → iProp Σ }.
Existing Class wp_axiomaticIrisG.

Definition simulation_body `{specStateG Σ, invG Σ, inG Σ heapR,InitialConfiguration}
           iτ (iη: types.heap → int_heap) Γ e η A τ η' D D': iProp Σ :=
  ∀ N σ, existential_triple ⊤ initial_cfg
                            (intΓ iτ Γ D N σ ∗ iη η D N)
                            (subst (of_val <$> σ) e)
                            (λ v, ∃ d N',
                                ⌜N ≡[not_new A]≡ N' ∧ D' !! RET = Some d⌝ ∧
                                iτ τ d N' v ∗ iη η' D' N').

Section TypeInterpretation.
  Context `{WaitPermissions, implStateG Σ, specStateG Σ, taskDataG Σ}.
  Context `{wp_axiomaticIrisG _ Σ,InitialConfiguration}.
  Implicit Type d : val.
  Implicit Type N: name_map.
  Implicit Type x: val.

  Definition int_i_bool d N x: iProp Σ := ⌜(x = Ctrue ∨ x = Cfalse) ∧ x = d⌝.
  Definition int_s_bool := int_i_bool.
  Definition int_i_unit d N x: iProp Σ := ⌜x = Cunit⌝.
  Definition int_s_unit := int_i_unit.
  Definition int_i_ref (ξ: gname) d N x: iProp Σ := ⌜∃ l: loc, N!!ξ = Some (Loc l) ∧ x = Cloc l⌝.
  Definition int_s_ref := int_i_ref.
  Definition int_s_promise ξ d N x: iProp Σ := ⌜∃ t γ, N!!ξ = Some (Task t γ) ∧ x = Ctid t⌝.

  (** We build the implementation interpretation of promise in stages. *)
  (** Access to the task data. *)
  Definition ip_data γ U (D': conn_map) (N': name_map) :=
    own γ (to_agree U) ∗ own (td_D_name U) (agreed D') ∗ own (td_N_name U) (agreed N').
  (** The easy parts: name map and implementation interpretation. *)
  Definition ip_impl (A: gset gname) (τ: type) (τi: @int_type Σ) (D': conn_map) N' N y :=
    ∃ d, ⌜D' !! RET = Some d ∧ N' ≡[ names τ ∖ A ]≡ N⌝ ∗ τi d N' y.
  Definition ip_sim iτs iηs τ U D' :=
    simulation_body iτs iηs
                    (td_env U) (td_expr U) (td_pre U) (td_alloc U) τ (td_post U) (td_D_pre U) D'.
  (** Put together the inner pieces of the interpretation of promises... *)
  Definition promiseN := nroot .@ "promise".
  Definition int_i_promise_body iτs iηs N A τ τi γ v :=
    ∃ U D' N',
      ip_data γ U D' N' ∗ ip_impl A τ τi D' N' N v ∗ □ip_sim iτs iηs τ U D'.
  Definition int_i_promise iτs iηs ξ A τ τi d N x :=
    ∃ t γ, ⌜N !! ξ = Some (Task t γ) ∧ x = Ctid t⌝ ∧
           inv promiseN (wp_wait t (int_i_promise_body iτs iηs (delete ξ N) A τ τi γ)).
End TypeInterpretation.

Section HeapInterpretation.
  Context `{WaitPermissions, implStateG Σ, specStateG Σ, wp_axiomaticIrisG _ Σ, taskDataG Σ}.
  Implicit Type N : name_map.
  Implicit Type D : conn_map.
  Local Open Scope I.

  Definition int_i_emp D N: iProp Σ := True.
  Definition int_s_emp := int_i_emp.
  Definition int_i_star (iη iη': int_heap) D N: iProp Σ := iη D N ∗ iη' D N.
  Definition int_s_star := int_i_star.
  Definition int_i_pt ξ (iτ: int_type) D N: iProp Σ :=
    ∃ l d v, ⌜N!!ξ = Some (Loc l) ∧ D!!name ξ = Some d⌝ ∗ mapstoI l v 1%Qp ∗ iτ d N v.
  Definition int_s_pt ξ (iτ: int_type) D N: iProp Σ :=
    ∃ l d v, ⌜N!!ξ = Some (Loc l) ∧ D!!name ξ = Some d⌝ ∗ mapstoS l v 1%Qp ∗ iτ d N v.
  Definition int_i_wait_body γ (η: types.heap) (iη: int_heap) A N :=
    ∃ U D' N', ip_data γ U D' N' ∗ ⌜N ≡[ names η ∖ A]≡ N'⌝ ∗ iη D' N'.
  Definition int_i_wait ξ A η (iη: int_heap) D N: iProp Σ :=
    ∃ t γ, ⌜N!!ξ = Some (Task t γ)⌝ ∗ wp_wait t (λ _, int_i_wait_body γ η iη A (delete ξ N)).
  (* Use the lower-level interpretations here *)
  Definition int_s_wait_pre iτs' (iηs': types.heap → int_heap) U N' σ: iProp Σ :=
    intΓ iτs' (td_env U) (td_D_pre U) N' σ ∗ iηs' (td_pre U) (td_D_pre U) N'.
  Definition int_s_wait iτs' iηs' ξ A η D N :=
    ∃ t γ U N' σ,
      ⌜N!!ξ = Some (Task t γ) ∧ td_post U = η ∧ N' ≡[names η ∖ A]≡ N⌝ ∧
      t ⤇ run: (subst (of_val <$> σ) (td_expr U)) ∗ int_s_wait_pre iτs' iηs' U N' σ.
End HeapInterpretation.

Section Interpretations.
  Context `{WaitPermissions, implStateG Σ, specStateG Σ, wp_axiomaticIrisG _ Σ, taskDataG Σ}.
  Context `{InitialConfiguration, ∀ t, Proper (pointwise_relation _ (≡) ==> (≡)) (wp_wait t)}.
  Implicit Type N: name_map.
  Implicit Type D: conn_map.
  Implicit Type x: val.
  Implicit Type d: val.
  Local Open Scope I.
  
  Fixpoint int_s_type τ: @int_type Σ :=
    match τ with
    | tbool => int_s_bool
    | tunit => int_s_unit
    | tref ξ => int_s_ref ξ
    | ttask ξ A τ => int_s_promise ξ
    end.
  Fixpoint int_s_heap_approx iη η: @int_heap Σ :=
    match η with
    | hemp => int_s_emp
    | hstar η η' => int_s_star (int_s_heap_approx iη η) (int_s_heap_approx iη η')
    | hpt ξ τ => int_s_pt ξ (int_s_type τ)
    | hwait ξ A η => int_s_wait int_s_type iη ξ A η
    end.
  Fixpoint int_s_heap_rec n η :=
    int_s_heap_approx (match n with
                       | O => λ _ _ _, False%I
                       | S n => int_s_heap_rec n
                       end)
                      η.
  Definition int_s_heap η: @int_heap Σ := λ D N, ∃ n, int_s_heap_rec n η D N.

  Fixpoint int_i_type τ: @int_type Σ :=
    match τ with
    | tbool => int_i_bool
    | tunit => int_i_unit
    | tref ξ => int_i_ref ξ
    | ttask ξ A τ => int_i_promise int_s_type int_s_heap ξ A τ (int_i_type τ)
    end.
  Fixpoint int_i_heap η: @int_heap Σ :=
    match η with
    | hemp => int_i_emp
    | hstar η η' => int_i_star (int_i_heap η) (int_i_heap η')
    | hpt ξ τ => int_i_pt ξ (int_i_type τ)
    | hwait ξ A η => int_i_wait ξ A η (int_i_heap η)
    end.

  Definition int_s_env := intΓ int_s_type.
  Definition int_i_env := intΓ int_i_type.
  
  (** Basic properties of interpretation *)
  Global Instance int_s_type_persistent τ d N v:  PersistentP (int_s_type τ d N v).
  Proof. destruct τ; apply _. Qed.
  Global Instance int_i_type_persistent τ d N v:  PersistentP (int_i_type τ d N v).
  Proof. destruct τ; apply _. Qed.
  Global Instance int_s_env_persistent Γ D N σ: PersistentP (int_s_env Γ D N σ).
  Proof. apply _. Qed.
  Global Instance int_i_env_persistent Γ D N σ: PersistentP (int_i_env Γ D N σ).
  Proof. apply _. Qed.

  Global Instance int_s_type_local τ:
    Proper ((=) ==> overlap (names τ) ==> (=) ==> (⊣⊢)) (int_s_type τ).
  Proof.
    induction τ; intros d ? <- N N' eqN x ? <-; cbn; try done.
    - rewrite /int_s_ref /int_i_ref.
      rewrite eqN; first done.
      cbn; set_solver.
    - rewrite /int_s_promise.
      rewrite eqN; first done.
      cbn -[union]; set_solver.
  Qed.

  Global Instance int_i_type_local τ:
    Proper ((=) ==> overlap (names τ) ==> (=) ==> (⊣⊢)) (int_i_type τ).
  Proof.
    induction τ; intros d ? <- N N' eqN x ? <-; cbn; try done.
    - rewrite /int_i_ref eqN; first done.
      cbn; set_solver.
    - rewrite /int_i_promise /int_i_promise_body /ip_impl.
      rewrite (eqN ξ); last set_solver.
      do 21 f_equiv.
      apply (overlap_iff ((names (ttask ξ A τ)))).
      + apply union_subseteq_r.
      + intros ξ' inξ'.
        destruct (decide (ξ = ξ')) as [<-|neq].
        * by rewrite !lookup_delete.
        * rewrite !lookup_delete_ne; auto.
  Qed.

  Lemma names_heap_star η η': (names_heap (η ⊗ η') ≡ names_heap η ∪ names_heap η')%C.
  Proof.
    rewrite /names_heap => ξ.
    rewrite elem_of_union !elem_of_of_list !elem_of_list_fmap /=.
    setoid_rewrite elem_of_elements.
    change (names (hstar η η')) with (names η ∪ names η').
    setoid_rewrite elem_of_union.
    split.
    - intros [? [? [?|?]]]; eauto.
    - intros [[? [??]]|[? [??]]]; eauto.
  Qed.
  
  Lemma int_s_heap_approx_local
        iη (iη_proper: ∀ (η: types.heap),
               Proper (overlap (names_heap η) ==> overlap (names η) ==> (⊣⊢)) (iη η)) η:
    Proper (overlap (names_heap η) ==> overlap (names η) ==> (⊣⊢)) (int_s_heap_approx iη η).
  Proof.
    induction η; intros D D' eqD N N' eqN; cbn.
    - done.
    - rewrite /int_s_star /int_i_star.
      f_equiv; [apply IHη1|apply IHη2].
      all: eapply overlap_mono; eauto.
      all: cbn.
      1,3: rewrite names_heap_star.
      all: clear; set_solver.
    - rewrite /int_s_pt.
      setoid_rewrite (eqN ξ); last by set_solver.
      rewrite eqD; cycle 1.
      { rewrite /names_heap elem_of_of_list elem_of_list_fmap.
        exists ξ; split; auto.
        rewrite elem_of_elements; set_solver. }
      enough (∀ d v, int_s_type τ d N v ⊣⊢ int_s_type τ d N' v) as eqint.
      { by setoid_rewrite eqint. }
      intros; apply int_s_type_local; auto.
      eapply overlap_mono; eauto.
      set_solver.
    - rewrite /int_s_wait /=.
      do 10 f_equiv.
      rewrite (eqN ξ); last set_solver.
      do 4 f_equiv.
      apply (overlap_iff ((names (hwait ξ A η)))); eauto.
      apply union_subseteq_r.
  Qed.

  Lemma int_s_heap_rec_local n: ∀ η,
      Proper (overlap (names_heap η) ==> overlap (names η) ==> (⊣⊢)) (int_s_heap_rec n η).
  Proof.
    induction n as [|n IH]; intros; cbn; apply int_s_heap_approx_local; auto.
    solve_proper.
  Qed.

  Lemma int_s_heap_local η:
    Proper (overlap (names_heap η) ==> overlap (names η) ==> (⊣⊢)) (int_s_heap η).
  Proof.
    intros D D' eqD N N' eqN.
    rewrite /int_s_heap.
    f_equiv; intro n.
    apply int_s_heap_rec_local; done.
  Qed.
  
  Lemma int_i_heap_local η:
    Proper (overlap (names_heap η) ==> overlap (names η) ==> (⊣⊢)) (int_i_heap η).
  Proof.
    induction η; intros D D' eqD N N' eqN; cbn.
    - done.
    - rewrite /int_s_star /int_i_star.
      f_equiv; [apply IHη1|apply IHη2].
      all: eapply overlap_mono; eauto.
      all: cbn.
      1,3: rewrite names_heap_star.
      all: clear; set_solver.
    - rewrite /int_i_pt.
      rewrite (eqN ξ); last set_solver.
      rewrite (eqD (name ξ)).
      2: rewrite /names_heap elem_of_of_list elem_of_list_fmap.
      2: eexists; split; eauto.
      2: rewrite elem_of_elements; set_solver.
      assert (N ≡[ names τ ]≡ N') as eqN'.
      { intros ξ' inξ; apply eqN; set_solver. }
      enough (∀ d v, int_i_type τ d N v ⊣⊢ int_i_type τ d N' v) as eqτ.
      { by setoid_rewrite eqτ. }
      intros; by apply int_i_type_local.
    - rewrite /int_i_wait /int_i_wait_body.
      rewrite (eqN ξ); last set_solver.
      enough (∀ N'', delete ξ N ≡[ names η ∖ A ]≡ N'' ↔
                       delete ξ N' ≡[ names η ∖ A ]≡ N'')
        as eqN'.
      { by setoid_rewrite eqN'. }
      intro.
      rewrite -!(symmetry_iff (overlap (names η ∖ A)) N'').
      apply (overlap_iff (names (hwait ξ A η))).
      + apply union_subseteq_r.
      + intros ξ' inξ'.
        destruct (decide (ξ = ξ')) as [<-|neq].
        * by rewrite !lookup_delete.
        * rewrite !lookup_delete_ne; auto.
  Qed.

  Lemma intΓ_local (ϕ: type → @int_type Σ)
        (ϕ_local: ∀ τ, Proper ((=) ==> overlap (names τ) ==> (=) ==> (⊣⊢)) (ϕ τ)) Γ:
    Proper (overlap (names_env Γ) ==> overlap (names Γ) ==> (=) ==> (⊣⊢)) (intΓ ϕ Γ).
  Proof.
    intros D D' eqD N N' eqN σ ? <-.
    rewrite /intΓ.
    assert (pure_l_and: ∀ P P' (Q Q': iProp Σ) (eqP: (P ↔ P')%type) (eqQ: P → Q ⊣⊢ Q'),
               ⌜P⌝ ∧ Q ⊣⊢ ⌜P'⌝ ∧ Q').
    { intros; rewrite -eqP.
      iSplit; iIntros "[% pre]"; rewrite eqQ; auto. }
    apply pure_l_and.
    { apply and_iff_compat_l, forall_proper; intro.
      destruct (decide (is_Some (Γ!!x))) as [[τ tyx]|]; last tauto.
      rewrite (eqD (var x)); first done.
      rewrite elem_of_names_env.
      exists x; eauto. }
    intros [domσ domD].
    f_equiv; intro x.
    f_equiv; intro τ.
    f_equiv; intro v.
    f_equiv; intro d.
    destruct (decide (Γ!!x = Some τ)) as [mt|].
    2: iSplit; iIntros "_ %"; intuition discriminate.
    assert (var x ∈ names_env Γ) as in_var_x.
    { rewrite elem_of_names_env; exists x; rewrite mt; eauto. }
    rewrite (eqD (var x)); last done.
    f_equiv.
    apply ϕ_local; try done.
    eapply overlap_mono.
    2,3,4: done.
    intro ξ.
    rewrite env_elem_of_names.
    exists x,τ; auto.
  Qed.

  Lemma int_i_env_local Γ: 
    Proper (overlap (names_env Γ) ==> overlap (names Γ) ==> (=) ==> (⊣⊢)) (int_i_env  Γ).
  Proof. apply intΓ_local, int_i_type_local. Qed.
  Lemma int_s_env_local Γ: 
    Proper (overlap (names_env Γ) ==> overlap (names Γ) ==> (=) ==> (⊣⊢)) (int_s_env  Γ).
  Proof. apply intΓ_local, int_s_type_local. Qed.
  
  Lemma int_s_heap_approx_mono ϕ ϕ' (mono: ∀ η D N, ϕ η D N -∗ ϕ' η D N) η:
    ∀ D N, int_s_heap_approx ϕ η D N -∗ int_s_heap_approx ϕ' η D N.
  Proof.
    induction η; cbn.
    - iIntros (??) "$".
    - iIntros (D N) "[I1 I2]".
      iSplitL "I1".
      + iApply (IHη1 with "I1").
      + iApply (IHη2 with "I2").
    - iIntros (??) "$".
    - iIntros (D N).
      rewrite /int_s_wait /int_s_wait_pre.
      iIntros "pre".
      iDestruct "pre" as (t γ U N' σ) "[pre [move [env wait]]]".
      iExists t,γ,U,N',σ; iFrame.
      iApply (mono with "wait").
  Qed.
  Lemma int_s_heap_rec_S n: ∀ η D N, int_s_heap_rec n η D N -∗ int_s_heap_rec (S n) η D N.
  Proof.
    rewrite -Nat.add_1_r.
    induction n as [|n IH]; cbn.
    all: iIntros (η D N) "pre"; iApply (int_s_heap_approx_mono with "pre").
    - iIntros (???) "[]".
    - exact IH.
  Qed.
  
  Lemma int_s_heap_rec_mono n n' (len: n ≤ n'):
    ∀ η D N, int_s_heap_rec n η D N -∗ int_s_heap_rec n' η D N.
  Proof.
    induction len.
    { iIntros (???) "$". }
    iIntros (η D N) "pre".
    iApply (int_s_heap_rec_S with "[-]").
    iApply (IHlen with "pre").
  Qed.
End Interpretations.
