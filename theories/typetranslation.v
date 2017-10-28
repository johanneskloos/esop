From iris.proofmode Require Import tactics classes.
From iris.base_logic.lib Require Import invariants own.
From iris.algebra Require Import updates agree big_op gmap.
From esop Require Import types oneshot specification corecalculus overlap.
From stdpp Require Import gmap coPset.

Variant name_entry := Loc (l: loc) | Task (t: tid).
Definition name_map := gmap gname name_entry.

Variant conn_name := RET | name (ξ: gname) | var (x: string).
Instance conn_name_eq_dec: EqDecision conn_name.
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

Definition intT_type {Σ} := val → name_map → val → iProp Σ.
Definition intT_heap {Σ} := conn_map → name_map → iProp Σ.

Definition conn_heap (η: hexpr): gset conn_name := of_list (name <$> (elements (names η))).
Lemma elem_of_conn_heap (d: conn_name) η:
  (d ∈ conn_heap η ↔ ∃ ξ: gname, d = name ξ ∧ ξ ∈ names η)%type.
Proof.
  rewrite /conn_heap elem_of_of_list elem_of_list_fmap.
  f_equiv; intro ξ. by rewrite elem_of_elements.
Qed.

Definition conn_env (Γ: env): gset conn_name := of_list (var <$> fst <$> map_to_list Γ).
Lemma elem_of_conn_env n (Γ: env): n ∈ conn_env Γ ↔ ∃ x, n = var x ∧ is_Some (Γ !! x).
Proof.
  rewrite /conn_env elem_of_of_list -list_fmap_compose elem_of_list_fmap.
  split.
  { intros [[x τ] [-> isin%elem_of_map_to_list]]; eauto. }
  { intros [x [-> [τ isin%elem_of_map_to_list]]]; exists (x,τ); auto. }
Qed.

Record task_data :=
  TaskData {
      td_expr: expr;
      td_env: env;
      td_pre: hexpr;
      td_post: hexpr;
      td_alloc: gset gname;
      td_D_pre: conn_map;
      td_D_name: gname;
      td_N_name: gname;
    }.

Canonical Structure task_dataC := leibnizC task_data.
Canonical Structure conn_mapC := leibnizC conn_map.
Canonical Structure name_mapC := leibnizC name_map.

Class taskDataG Σ :=
  { td_common_inG:> inG Σ (agreeR task_dataC);
    td_connData_inG:> inG Σ (oneshotR conn_mapC);
    td_nameData_inG:> inG Σ (oneshotR name_mapC);
    td_specNameData_inG :> inG Σ (gmapR tid (oneshotR name_mapC));
    spec_name_map_name: gname
  }.
Local Open Scope I.

Definition int_env_doms (Γ: env) (D: conn_map) (σ: gmap string val): Prop :=
  (∀ x: string, is_Some (Γ !! x) ↔ is_Some (σ !! x)) ∧
  (∀ x: string, is_Some (Γ !! x) → is_Some (D !! var x)).
Definition int_env_data (Γ: env) (D: conn_map) (σ: gmap string val) x τ v d: Prop :=
  Γ !! x = Some τ ∧ σ !! x = Some v ∧ D !! var x = Some d.
Definition int_env_pre {Σ} (iτ: type → intT_type) Γ D N σ: iProp Σ :=
  ⌜int_env_doms Γ D σ⌝ ∧ ∀ x τ v d, ⌜int_env_data Γ D σ x τ v d⌝ → iτ τ d N v.

Definition simulation_body `{specStateG Σ,invG Σ,inG Σ heapR,InitialConfiguration,SpecTaskDataG Σ}
           (iτ: type → intT_type) (iη: hexpr → intT_heap)
           Γ e η A τ η' D D': iProp Σ :=
  ∀ N σ, existential_triple ⊤
                            (int_env_pre iτ Γ D N σ ∗ iη η D N)
                            (subst (of_val <$> σ) e)
                            (λ v, ∃ d N',
                                ⌜N ≡[not_new A]≡ N' ∧ D' !! RET = Some d⌝ ∧
                                iτ τ d N' v ∗ iη η' D' N').

Instance: ImplTaskDataT := task_data.
Instance: SpecTaskDataT := name_map.

Class allG Σ :=
  { all_aigG :> axiomaticIrisG Σ;
    all_ssG :> specStateG Σ;
    all_tdG :> taskDataG Σ;
    all_ic :> InitialConfiguration;
    all_stdG :> SpecTaskDataG Σ }.
    
Section TypeInterpretation.
  Context `{allG Σ}.
  Implicit Type d : val.
  Implicit Type N: name_map.
  Implicit Type x: val.

  Definition int_i_bool d N x: iProp Σ := ⌜(x = Ctrue ∨ x = Cfalse) ∧ x = d⌝.
  Definition int_s_bool d N x := int_i_bool d N x.
  Definition int_i_unit d N x: iProp Σ := ⌜x = Cunit⌝.
  Definition int_s_unit d N x := int_i_unit d N x.
  Definition int_i_ref (ξ: gname) d N x: iProp Σ := ⌜∃ l: loc, N!!ξ = Some (Loc l) ∧ x = Cloc l⌝.
  Definition int_s_ref ξ d N x := int_i_ref ξ d N x.

  Definition int_s_promise ξ A (τ: type) d N x: iProp Σ :=
    ∃ t (Npre: name_mapC), spec_task_agree t Npre ∗
          ⌜N!!ξ = Some (Task t) ∧ Npre ≡[names τ ∖ A]≡ N⌝.

  (* Why is this needed? FIXME *)
  Global Instance: implStateG Σ := aig_impl_state.

  (** We build the implementation interpretation of promise in stages. *)
  (** Access to the task data. *)
  Definition ip_data (t: tid) (U: task_dataC) (D': conn_map) (N': name_map): iProp Σ :=
    task_agree t U ∗ own (td_D_name U) (agreed D') ∗ own (td_N_name U) (agreed N').
  
  (** The easy parts: name map and implementation interpretation. *)
  Definition ip_impl (A: gset gname) (τ: type) (τi: @intT_type Σ) (D': conn_map) N' N y :=
    ∃ d, ⌜D' !! RET = Some d ∧ N' ≡[ names τ ∖ A ]≡ N⌝ ∗ τi d N' y.
  Definition ip_sim (iτs: type → @intT_type Σ) (iηs: hexpr → @intT_heap Σ)
             A (τ: type) U D': iProp Σ :=
    ⌜A = td_alloc U⌝ ∧
    simulation_body iτs iηs (td_env U) (td_expr U) (td_pre U) (td_alloc U) τ (td_post U)
                    (td_D_pre U) D'.

  (** Put together the inner pieces of the interpretation of promises... *)
  Definition promiseN := nroot .@ "promise".
  Definition int_i_promise_body iτs iηs N A τ τi t v :=
    ∃ U D' N', ip_data t U D' N' ∗ ip_impl A τ τi D' N' N v ∗ □ip_sim iτs iηs A τ U D'.
  Definition int_i_promise iτs iηs ξ A τ τi d N x :=
    ∃ t, ⌜N !! ξ = Some (Task t) ∧ x = Ctid t⌝ ∧
           inv promiseN (wait t (int_i_promise_body iτs iηs N A τ τi)).
End TypeInterpretation.

Section HeapInterpretation.
  Context `{allG Σ}.
  Implicit Type N : name_map.
  Implicit Type D : conn_map.
  Local Open Scope I.

  Definition int_i_emp D N: iProp Σ := True.
  Definition int_s_emp D N: iProp Σ := True.
  Definition int_i_star (iη iη': intT_heap) D N: iProp Σ := iη D N ∗ iη' D N.
  Definition int_s_star (iη iη': intT_heap) D N: iProp Σ := iη D N ∗ iη' D N.
  Definition int_i_pt ξ (iτ: intT_type) D N: iProp Σ :=
    ∃ l d v, ⌜N!!ξ = Some (Loc l) ∧ D!!name ξ = Some d⌝ ∗ mapstoI l v 1%Qp ∗ iτ d N v.
  Definition int_s_pt ξ (iτ: intT_type) D N: iProp Σ :=
    ∃ l d v, ⌜N!!ξ = Some (Loc l) ∧ D!!name ξ = Some d⌝ ∗ mapstoS l v 1%Qp ∗ iτ d N v.
  Definition int_i_wait_body (η: hexpr) (iη: intT_heap) A N t (_: val): iProp Σ :=
    ∃ U D' N', ip_data t U D' N' ∗ ⌜N ≡[ names η ∖ A]≡ N'⌝ ∗ iη D' N'.
  Definition int_i_wait (ξ: gname) A η (iη: intT_heap) D N: iProp Σ :=
    ∃ t, ⌜N!!ξ = Some (Task t) ∧ D!!name ξ = Some (VConst (Ctid t))⌝ ∗
                                                  wait t (int_i_wait_body η iη A N).

  (* Use the lower-level interpretations here *)
  Definition int_s_wait_pre iτs' (iηs': hexpr → intT_heap) U N ts σ: iProp Σ :=
    ∃ Npre N, int_env_pre iτs' (td_env U) (td_D_pre U) Npre σ ∗
                          iηs' (td_pre U) (td_D_pre U) Npre  ∗
                          spec_task_agree ts Npre ∗
                          ⌜Npre ≡[names (td_post U) ∖ td_alloc U]≡ N⌝.
  
  Definition int_s_wait iτs' iηs' ξ A η D N: iProp Σ :=
    ∃ ti ts U σ,
      ⌜N!!ξ = Some (Task ts) ∧ D!!name ξ = Some (VConst (Ctid ti)) ∧ td_post U = η ∧ td_alloc U = A⌝ ∧
      task_agree ti U ∗
      ts ⤇ run: (subst (of_val <$> σ) (td_expr U)) ∗ int_s_wait_pre iτs' iηs' U N ts σ.
  
End HeapInterpretation.

Section Interpretations.
  Context `{allG Σ}.
  Implicit Type N: name_map.
  Implicit Type D: conn_map.
  Implicit Type x: val.
  Implicit Type d: val.
  Local Open Scope I.
  
  Fixpoint int_s_type τ: @intT_type Σ :=
    match τ with
    | tbool => int_s_bool
    | tunit => int_s_unit
    | tref ξ => int_s_ref ξ
    | ttask ξ A τ => int_s_promise ξ A τ
    end.
  Fixpoint int_s_heap_approx iη η: @intT_heap Σ :=
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
  Definition int_s_heap η: @intT_heap Σ := λ D N, ∃ n, int_s_heap_rec n η D N.

  Fixpoint int_i_type τ: @intT_type Σ :=
    match τ with
    | tbool => int_i_bool
    | tunit => int_i_unit
    | tref ξ => int_i_ref ξ
    | ttask ξ A τ => int_i_promise int_s_type int_s_heap ξ A τ (int_i_type τ)
    end.
  Fixpoint int_i_heap η: @intT_heap Σ :=
    match η with
    | hemp => int_i_emp
    | hstar η η' => int_i_star (int_i_heap η) (int_i_heap η')
    | hpt ξ τ => int_i_pt ξ (int_i_type τ)
    | hwait ξ A η => int_i_wait ξ A η (int_i_heap η)
    end.

  Definition int_s_env := int_env_pre int_s_type.
  Definition int_i_env := int_env_pre int_i_type.
  
  (** Basic properties of interpretation *)
  Global Instance int_s_type_persistent τ d N v:  PersistentP (int_s_type τ d N v).
  Proof. destruct τ; apply _. Qed.
  Global Instance int_i_type_persistent τ d N v:  PersistentP (int_i_type τ d N v).
  Proof. destruct τ; apply _. Qed.
  Global Instance int_s_env_persistent Γ D N σ: PersistentP (int_s_env Γ D N σ).
  Proof. apply _. Qed.
  Global Instance int_i_env_persistent Γ D N σ: PersistentP (int_i_env Γ D N σ).
  Proof. apply _. Qed.

  Notation ov x := (overlap (names x)).
  Global Instance int_s_type_local τ:
    Proper ((=) ==> ov τ ==> (=) ==> (⊣⊢)) (int_s_type τ).
  Proof.
    induction τ; intros d ? <- N N' eqN x ? <-; cbn; try done.
    - rewrite /int_s_ref /int_i_ref.
      rewrite eqN; first done.
      cbn; set_solver.
    - rewrite /int_s_promise.
      f_equiv; intro T.
      f_equiv; intro Npre.
      do 2 f_equiv.
      rewrite (eqN ξ); last (clear; set_solver).
      f_equiv.
      apply (overlap_iff (names (ttask ξ A τ))); last done.
      apply union_subseteq_r.
  Qed.

  Instance wait_Proper t: Proper (pointwise_relation _ (pointwise_relation _ (≡)) ==> (⊣⊢)) (wait t).
  Proof.
    intros ϕ ϕ' eqϕ.
    rewrite equiv_dist => [n].
    apply: wait_nonexpansive => [t' v'].
    rewrite eqϕ //.
  Qed.
  
  Global Instance int_i_type_local τ:
    Proper ((=) ==> ov τ ==> (=) ==> (⊣⊢)) (int_i_type τ).
  Proof.
    induction τ; intros d ? <- N N' eqN x ? <-; cbn; try done.
    - rewrite /int_i_ref eqN; first done.
      cbn; set_solver.
    - rewrite /int_i_promise /int_i_promise_body /ip_impl.
      rewrite (eqN ξ); last set_solver.
      f_equiv; intro t.
      do 3 f_equiv; intros t' v'.
      f_equiv; intro U.
      f_equiv; intro D'.
      f_equiv; intro N''.
      do 2 f_equiv.
      f_equiv; intro d'.
      do 3 f_equiv.
      apply (overlap_iff ((names (ttask ξ A τ)))); last done.
      apply union_subseteq_r.
  Qed.

  Lemma exists_or {A} (P Q: A → Prop): ((∃ x: A, P x ∨ Q x) ↔ (∃ x: A, P x) ∨ (∃ x: A, Q x))%type.
  Proof. clear H Σ. firstorder. Qed.
  
  Lemma conn_heap_star η η': (conn_heap (η ⊗ η') ≡ conn_heap η ∪ conn_heap η')%C.
  Proof.
    rewrite /conn_heap => ξ.
    rewrite elem_of_union !elem_of_of_list !elem_of_list_fmap /=.
    setoid_rewrite elem_of_elements.
    change (names (hstar η η')) with (names η ∪ names η').
    setoid_rewrite elem_of_union.
    rewrite -exists_or.
    apply exist_proper; intro.
    tauto.
  Qed.
  
  Lemma int_s_heap_approx_local
        iη (iη_proper: ∀ (η: hexpr),
               Proper (overlap (conn_heap η) ==> ov η ==> (⊣⊢)) (iη η)) η:
    Proper (overlap (conn_heap η) ==> ov η ==> (⊣⊢)) (int_s_heap_approx iη η).
  Proof.
    induction η; intros D D' eqD N N' eqN; cbn.
    - done.
    - rewrite /int_s_star /int_i_star.
      f_equiv; [apply IHη1|apply IHη2].
      all: eapply overlap_mono; eauto.
      all: cbn.
      1,3: rewrite conn_heap_star.
      all: clear; set_solver.
    - rewrite /int_s_pt.
      setoid_rewrite (eqN ξ); last (rewrite /= elem_of_union elem_of_singleton; auto).
      rewrite eqD; cycle 1.
      { rewrite elem_of_conn_heap.
        exists ξ; split; auto.
        rewrite /= elem_of_union elem_of_singleton; auto. }
      enough (∀ d v, int_s_type τ d N v ⊣⊢ int_s_type τ d N' v) as eqint.
      { by setoid_rewrite eqint. }
      intros; apply int_s_type_local; auto.
      eapply overlap_sub; last done.
      apply union_subseteq_r.
    - rewrite /int_s_wait /=.
      f_equiv; intro ti.
      f_equiv; intro ts.
      f_equiv; intro U.
      f_equiv; intro σ.
      f_equiv.
      rewrite (eqN ξ); last (clear; set_solver).
      rewrite (eqD (name ξ)); first done.
      rewrite elem_of_conn_heap; exists ξ.
      split; auto.
      clear; set_solver.
  Qed.

  Lemma int_s_heap_rec_local n: ∀ η,
      Proper (overlap (conn_heap η) ==> overlap (names η) ==> (⊣⊢))
             (int_s_heap_rec n η).
  Proof.
    induction n as [|n IH]; intros; cbn; apply int_s_heap_approx_local; auto.
    solve_proper.
  Qed.

  Lemma int_s_heap_local η:
    Proper (overlap (conn_heap η) ==> overlap (names η) ==> (⊣⊢)) (int_s_heap η).
  Proof.
    intros D D' eqD N N' eqN.
    rewrite /int_s_heap.
    f_equiv; intro n.
    apply int_s_heap_rec_local; done.
  Qed.
  
  Lemma int_i_heap_local η:
    Proper (overlap (conn_heap η) ==> overlap (names η) ==> (⊣⊢)) (int_i_heap η).
  Proof.
    induction η; intros D D' eqD N N' eqN; cbn.
    - done.
    - rewrite /int_s_star /int_i_star.
      f_equiv; [apply IHη1|apply IHη2].
      all: eapply overlap_sub; last done.
      1,3: rewrite conn_heap_star.
      all: clear; set_solver.
    - rewrite /int_i_pt.
      rewrite (eqN ξ); last set_solver.
      rewrite (eqD (name ξ)).
      2: rewrite elem_of_conn_heap /=.
      2: eexists _; split; auto; apply elem_of_union; rewrite elem_of_singleton; auto.
      assert (N ≡[ names τ ]≡ N') as eqN'.
      { intros ξ' inξ; apply eqN; set_solver. }
      enough (∀ d v, int_i_type τ d N v ⊣⊢ int_i_type τ d N' v) as eqτ.
      { by setoid_rewrite eqτ. }
      intros; by apply int_i_type_local.
    - rewrite /int_i_wait /int_i_wait_body.
      rewrite (eqN ξ); last set_solver.
      rewrite (eqD (name ξ)).
      2: rewrite elem_of_conn_heap; exists ξ; split; auto; clear; set_solver.
      f_equiv; intro t.
      do 2 f_equiv.
      intros t' _.
      f_equiv; intro U.
      f_equiv; intro D''.
      f_equiv; intro N''.
      do 3 f_equiv.
      rewrite -!(symmetry_iff (overlap _) N'').
      eapply overlap_iff; last done.
      apply union_subseteq_r.
  Qed.

  Lemma intΓ_local (ϕ: type → @intT_type Σ)
        (ϕ_local: ∀ τ, Proper ((=) ==> ov τ ==> (=) ==> (⊣⊢)) (ϕ τ)) Γ:
    Proper (overlap (conn_env Γ) ==> ov Γ ==> (=) ==> (⊣⊢)) (int_env_pre ϕ Γ).
  Proof.
    intros D D' eqD N N' eqN σ ? <-.
    rewrite /int_env_pre.
    assert (pure_l_and: ∀ P P' (Q Q': iProp Σ) (eqP: (P ↔ P')%type) (eqQ: P → Q ⊣⊢ Q'),
               ⌜P⌝ ∧ Q ⊣⊢ ⌜P'⌝ ∧ Q').
    { intros; rewrite -eqP.
      iSplit; iIntros "[% pre]"; rewrite eqQ; auto. }
    apply pure_l_and.
    { apply and_iff_compat_l, forall_proper; intro.
      destruct (decide (is_Some (Γ!!x))) as [[τ tyx]|]; last tauto.
      rewrite (eqD (var x)); first done.
      rewrite elem_of_conn_env.
      exists x; eauto. }
    intros [domσ domD].
    f_equiv; intro x.
    f_equiv; intro τ.
    f_equiv; intro v.
    f_equiv; intro d.
    rewrite /int_env_data.
    destruct (decide (Γ !! x = Some τ)) as [type_x|contra].
    2: iSplit; iIntros "_"; iIntros ([? _]); congruence.
    rewrite (eqD (var x)).
    2: rewrite elem_of_conn_env; exists x; rewrite type_x; eauto.
    f_equiv.
    apply ϕ_local.
    1,3: done.
    apply (overlap_sub (names Γ)); last done.
    intros ξ inξ.
    rewrite elem_of_names_env.
    exists x, τ; auto.
  Qed.

  Lemma int_i_env_local Γ: 
    Proper (overlap (conn_env Γ) ==> ov Γ ==> (=) ==> (⊣⊢)) (int_i_env  Γ).
  Proof. apply intΓ_local, int_i_type_local. Qed.
  Lemma int_s_env_local Γ: 
    Proper (overlap (conn_env Γ) ==> ov Γ ==> (=) ==> (⊣⊢)) (int_s_env  Γ).
  Proof. apply intΓ_local, int_s_type_local. Qed.

  Local Open Scope I.
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
      iDestruct "pre" as (t γ U σ) "[names [agree [move pre]]]".
      iExists t,γ,U,σ; iFrame.
      iDestruct "pre" as (N') "wait".
      iExists N'.
      iDestruct "wait" as (N'') "[$ [ϕ rest]]".
      iExists N''; iFrame.
      iApply (mono with "ϕ").
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

