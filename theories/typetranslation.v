From iris.proofmode Require Import tactics classes.
From iris.base_logic.lib Require Import invariants own.
From iris.algebra Require Import updates agree big_op.
From esop Require Import types oneshot specification corecalculus overlap.
From stdpp Require Import gmap coPset.

Module TypeTranslation(AxSem: AxiomaticSemantics).
  Module Import Axiomatics := AxSem <+ AxiomaticFacts.
  Variant name_entry := Loc (l: loc) | Task (t: tid) (γ: gname).
  Definition name_map := gmap gname name_entry.
  Variant conn_name := RET | name (ξ: gname) | var (x: string).
  Instance: EqDecision conn_name.
  Proof. solve_decision. Defined.
  Instance: Countable conn_name :=
    Build_Countable conn_name _
      (λ c, match c with RET => 1 | name ξ => ξ~0 | var x => (encode x)~1 end)%positive
      (λ p, match p with 1 => Some RET | ξ~0 => Some (name ξ) | x~1 => var <$> decode x end)%positive
      _.
  Proof.
    destruct x; auto.
    rewrite decode_encode; done.
  Qed.
  
  Definition conn_map := gmap conn_name val.
  Coercion VConst: const >-> val.
  
  Definition int_type {Σ} := val → name_map → val → iProp Σ.
  Definition int_heap {Σ} := conn_map → name_map → iProp Σ.

  Record task_data :=
    TaskData {
        td_expr: expr;
        td_env: env;
        td_pre: types.heap;
        td_post: types.heap;
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
  
  (** First, define functions for each case separately. *)
  Section TypeInterpretation.
    Context `{implStateG Σ, specStateG Σ, axiomaticIrisG Σ, taskDataG Σ} (c0: cfg).

    Local Open Scope I.
    Definition intΓ (iτ: type → int_type) (Γ: env) (D: conn_map) (N: name_map)
               (σ: gmap string val): iProp Σ :=
      ⌜∀ x: string, is_Some (Γ !! x) ↔ is_Some (σ !! x)⌝ ∧
            ⌜∀ x: string, is_Some (Γ !! x) → is_Some (D !! var x)⌝ ∧
                          ∀ (x: string) τ v d, ⌜Γ !! x = Some τ ∧
                                               σ !! x = Some v ∧
                                               D !! var x = Some d⌝ → iτ τ d N v.
    Definition not_new (Γ: env) (η: types.heap) (τ: type) (η': types.heap): coPset :=
      of_gset (names Γ ∪ names η) ∖ of_gset (names τ ∪ names η').

    Definition simulation' iτ iτ' (iη iη': types.heap → int_heap) Γ e η τ η' D D': iProp Σ :=
      ∀ N σ, existential_triple ⊤ c0
                                (intΓ iτ Γ D N σ ∗ iη η D N)
                                (subst (of_val <$> σ) e)
                                (λ v, ∃ d N',
                                    ⌜N ≡[not_new Γ η τ η']≡ N' ∧ D' !! RET = Some d⌝ ∧
                                    iτ' τ d N' v ∗ iη' η' D' N').
    
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
      ∃ d, ⌜D' !! RET = Some d ∧ N' ≡[ of_gset (names τ) ∖ of_gset A ]≡ N⌝ ∗ τi d N' y.
    (** The simuation triple. Note that we have a bit of trouble here: As given in the
        paper, the construction is not neccesarily well-founded. The complications with
        the different its and so on are here to allow us to build a well-founded fixpoint
        later on. *)
    Definition ip_sim iτs iτs' iηs iηs' τ U D' :=
      simulation' iτs iτs' iηs iηs' (td_env U) (td_expr U) (td_pre U) τ (td_post U) (td_D_pre U) D'.
    (** Now, note that we only need to make our fixpoint well-founded for the
        preconditions: τ is known to be structurally smaller, and the interpretation
        of types does not recurse into that of heaps, so we can simply use the
        same-level functions for the postconditions. But the names in the preconditions
        will never be in allocation sets, so we can treat them as constant - in other
        words, we can look up the task ids of all the ξ in the precondition! This allows
        us to write down a description of type depth (i.e., how long a chain of promises
        it induces). 
        us to get the levels for those tasks, and formulate an invariant. *)
    Fixpoint ty_all_tasks (ϕ: gname → iProp Σ) τ :=
      match τ return iProp Σ with
      | ttask ξ _ τ => ϕ ξ ∗ ty_all_tasks ϕ τ
      | tref _ | tunit | tbool => True
      end.
    Fixpoint he_all_tasks (ϕ: gname → iProp Σ) η :=
      match η return iProp Σ with
      | hwait ξ _ η => ϕ ξ ∗ he_all_tasks ϕ η
      | hstar η η' => he_all_tasks ϕ η ∗ he_all_tasks ϕ η'
      | hpt _ _ | hemp => True
      end.
    Definition env_all_tasks ϕ (Γ: env) := ∀ (x: string) τ, ⌜Γ !! x = Some τ⌝ → ty_all_tasks ϕ τ.
    Fixpoint depth N n γ {struct n} :=
      match n return iProp Σ with
      | O => False
      | S n => ∀ γ (U: task_data),
          own γ (to_agree U) -∗
                     let ϕ ξ := (∀ p γ, ⌜N !! ξ = Some (Task p γ)⌝ → depth N n γ)
                     in env_all_tasks ϕ (td_env U) ∗ he_all_tasks ϕ (td_pre U)
      end.
    (** Put together the inner pieces of the interpretation of promises... *)
    Definition promiseN := nroot .@ "promise".
    Definition int_i_promise_body iτs iτs' iηs iηs' N A τ τi γ v :=
      ∀ U D' N',
        ip_data γ U D' N' ∗ ip_impl A τ τi D' N' N v ∗ ip_sim iτs iτs' iηs iηs' τ U D'.
    Definition int_i_promise iτs iτs' iηs iηs' ξ A τ τi d N x :=
      ∃ t γ, ⌜N !! ξ = Some (Task t γ) ∧ x = Ctid t⌝ ∧
           inv promiseN (wait t (int_i_promise_body iτs iτs' iηs iηs' N A τ τi γ)).
  End TypeInterpretation.
  Section HeapInterpretation.
    Context `{implStateG Σ, specStateG Σ, axiomaticIrisG Σ, taskDataG Σ} (c0: cfg).
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
      ∃ U D' N', ip_data γ U D' N' ∗ ⌜N ≡[ of_gset (names η) ∖ of_gset A]≡ N'⌝ ∗ iη D' N'.
    Definition int_i_wait ξ A η (iη: int_heap) D N: iProp Σ :=
      ∃ t γ, ⌜N!!ξ = Some (Task t γ)⌝ ∗ wait t (λ _, int_i_wait_body γ η iη A N).
    (* Use the lower-level interpretations here *)
    Definition int_s_wait_pre iτs' (iηs': types.heap → int_heap) U N' σ: iProp Σ :=
      intΓ iτs' (td_env U) (td_D_pre U) N' σ ∗ iηs' (td_pre U) (td_D_pre U) N'.
    Definition int_s_wait iτs' iηs' ξ A η D N :=
      ∃ t γ U N' σ,
        ⌜N!!ξ = Some (Task t γ) ∧ td_post U = η ∧ N' ≡[of_gset (names η) ∖ of_gset A]≡ N⌝ ∧
        t ⤇ run: (subst (of_val <$> σ) (td_expr U)) ∗ int_s_wait_pre iτs' iηs' U N' σ.
  End HeapInterpretation.

  Section Interpretations.
    Context `{implStateG Σ, specStateG Σ, axiomaticIrisG Σ, taskDataG Σ} (c0: cfg).
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
      match n return @int_heap Σ with
      | O => int_s_heap_approx (λ _ _ _, False%I) η
      | S n => int_s_heap_approx (int_s_heap_rec n) η
      end.
    Definition heap_depth N n η :=
      he_all_tasks (λ ξ, ∀ t γ, ⌜N !! t = Some (Task t γ)⌝ → depth N n γ) η.
    Definition int_s_heap η: @int_heap Σ := λ D N, ∃ n, int_s_heap_rec n η D N.

    Fixpoint int_i_type τ: @int_type Σ :=
      match τ with
      | tbool => int_i_bool
      | tunit => int_i_unit
      | tref ξ => int_i_ref ξ
      | ttask ξ A τ => int_i_promise c0 int_s_type int_s_type int_s_heap int_s_heap
                                     ξ A τ (int_i_type τ)
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
    
    Global Instance wait_proper t: Proper (pointwise_relation _ (≡) ==> (≡)) (@wait Σ t).
    Proof.
      intros ϕ ϕ' eqϕ.
      rewrite equiv_dist; intro.
      apply wait_nonexpansive; intro v.
      rewrite eqϕ; done.
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
        apply (overlap_iff (of_gset (names (ttask ξ A τ)))).
        + cbn -[union]; intro.
          rewrite elem_of_difference !elem_of_of_gset.
          set_solver.
        + intro; rewrite elem_of_of_gset; auto.
    Qed.

    Definition names_heap (η: types.heap): gset conn_name := of_list (name <$> (elements (names η))).
    Lemma elem_of_names_heap (d: conn_name) η:
      (d ∈ names_heap η ↔ ∃ ξ: gname, d = name ξ ∧ ξ ∈ names η)%type.
    Proof.
      rewrite /names_heap elem_of_of_list elem_of_list_fmap.
      f_equiv; intro ξ. by rewrite elem_of_elements.
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
        apply (overlap_iff (of_gset (names (hwait ξ A η)))); eauto.
        + intro ξ'.
          rewrite elem_of_difference !elem_of_of_gset.
          set_solver.
        + intros ξ'; rewrite elem_of_of_gset; auto.
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
        enough (∀ N'', N ≡[ of_gset (names η) ∖ of_gset A ]≡ N'' ↔
                         N' ≡[ of_gset (names η) ∖ of_gset A ]≡ N'')
          as eqN'.
        { by setoid_rewrite eqN'. }
        intros.
        enough (N''≡[ of_gset (names η) ∖ of_gset A ]≡ N ↔
                   N'' ≡[ of_gset (names η) ∖ of_gset A ]≡ N')
          as ov.
        { split; intros eqN' ξ' inξ'; symmetry; apply ov; eauto; done. }
        apply (overlap_iff (of_gset (names (hwait ξ A η)))).
        + intro; rewrite elem_of_difference !elem_of_of_gset; set_solver.
        + intros ?; rewrite elem_of_of_gset; auto.
    Qed.

    Definition env_names (Γ: env): gset conn_name := of_list (var <$> fst <$> map_to_list Γ).
    Lemma intΓ_local (ϕ: type → @int_type Σ)
          (ϕ_local: ∀ τ, Proper ((=) ==> overlap (names τ) ==> (=) ==> (⊣⊢)) (ϕ τ)) Γ:
      Proper (overlap (env_names Γ) ==> overlap (names Γ) ==> (=) ==> (⊣⊢)) (intΓ ϕ Γ).
    Proof.
      intros D D' eqD N N' eqN σ ? <-.
      rewrite /intΓ.
      f_equiv.
      assert (∀ (x: string), is_Some (Γ !! x) → (is_Some (D!!var x) ↔ is_Some (D'!!var x)))
        as eqD'.
      { intros x [τ mtx].
        rewrite eqD; first done.
        rewrite /env_names elem_of_of_list -list_fmap_compose elem_of_list_fmap.
        exists (x,τ); split; auto.
        rewrite elem_of_map_to_list; done. }
      f_equiv.
      { f_equiv.
        apply forall_proper; intro.
        specialize (eqD' x); tauto. }
      f_equiv; intro x.
      f_equiv; intro τ.
      f_equiv; intro v.
      f_equiv; intro d.
      destruct (Γ!!x) as [τ'|] eqn:mtx.
      2: iSplit; iIntros "pre"; iIntros ([[=]?]).
      rewrite (eqD (var x)); cycle 1.
      { rewrite /env_names elem_of_of_list -list_fmap_compose elem_of_list_fmap.
        exists (x,τ'); split; auto; rewrite elem_of_map_to_list; done. }
      assert ({τ' = τ} + {τ' ≠ τ}) as [->|neq].
      { decide equality.
        1, 3: apply (decide (ξ = ξ0)).
        apply (decide (A = A0)). }
      2: iSplit; iIntros "pre"; iIntros ([??]); congruence.
      f_equiv.
      apply ϕ_local; auto.
      eapply (overlap_mono (names Γ)); eauto.
      intros ξ inξ.
      rewrite /names /Names_instance_2.
      clear eqD eqN eqD'.
      induction Γ using map_ind.
      { rewrite lookup_empty in mtx; done. }
      destruct (decide (i=x)) as [->|neq].
      + rewrite big_opM_insert; last done.
        rewrite lookup_insert in mtx.
        injection mtx as ->.
        set_solver.
      + rewrite big_opM_insert; last done.
        rewrite lookup_insert_ne in mtx; last done.
        set_solver.
    Qed.
  End Interpretations.
End TypeTranslation.