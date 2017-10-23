(** Soundness proof for DWFM - Iris preliminaries. *)
(* We cannot use genHeap here - the genHeapG type class embeds the resource
  name for the heap, so we'd be getting conflicts. *)
From iris.base_logic.lib Require Import invariants own fractional.
From iris.base_logic Require Import big_op.
From iris.algebra Require Import agree auth excl frac gmap updates local_updates.
From iris.proofmode Require Import tactics classes.
From stdpp Require Import fin_map_dom.
From esop Require Import corecalculus.

(** Adequacy for asynchronous programs: This gives a simplified version of
 the adequacy condition from [program_logic/adequacy]. *)
Record cfg := CFG { cfg_heap: heap; cfg_tb: task_buffer; cfg_task: tid }.
Definition cfg_step c c' :=
  global_step (cfg_heap c) (cfg_tb c) (cfg_task c) (cfg_heap c') (cfg_tb c') (cfg_task c').
Definition cfg_steps := rtc cfg_step.
Definition main_task := 1%positive.
Definition cfg_init e h := CFG h {[ main_task := running e ]} main_task.

(** OFEs for various base types. *)
Canonical Structure locC := leibnizC loc.
Canonical Structure tidC := leibnizC tid.
Canonical Structure exprC := leibnizC expr.
Canonical Structure valC := leibnizC val.
Canonical Structure task_stateC := leibnizC task_state.

(** Ghost state representation of specification heap and task buffer. This defines the
  (U)CMRAs that make up everything. *)
Definition heapContentUR := gmapUR loc (prodR fracR (agreeR valC)).
Definition heapR := authR heapContentUR.
Definition heapUR := authUR heapContentUR.
Definition taskContentUR := gmapUR tid (exclR task_stateC).
Definition taskbufferR := authR taskContentUR.
Definition taskbufferUR := authUR taskContentUR.

(** A cell that records the running task. *)
Definition runningTaskR := authR (optionUR (exclR tidC)).

(** A map for accessing task data. We use a level of indirection: The specification of
 post gives us a wait permissions and a proof that the task information map
 contains a single positive number that we specified. We use this to store
 a reference to further ghost state that contains the information we need. *)
Definition taskDataR := gmapR tid (agreeR positiveC).

(** Implementation heap and simulation state, presented to be usable from Iris. *)
Class implStateG Σ :=
  { impl_state_heap:> inG Σ heapR;
    impl_task_data :> inG Σ taskDataR;
    impl_state_heap_name: gname;
    impl_task_data_name: gname
  }.
Class specStateG Σ :=
  { spec_state_heap_name: gname;
    spec_state_task_buffer:> inG Σ taskbufferR;
    spec_state_running_task:> inG Σ runningTaskR;
    spec_state_task_buffer_name: gname;
    spec_state_running_task_name: gname
  }.

(** We can now define mapsto and task predicates. *)
Section ImplPredicates.
  Context `{implStateG Σ}.
  Definition mapsto_cell l v q: heapContentUR := {[ l := (q, to_agree v) ]}.
  Definition heap_authoritative (h: heap): heapContentUR :=
    (1%Qp,) <$> to_agree <$> h.
  Definition mapstoI l v q := own impl_state_heap_name (◯mapsto_cell l v q).
  Definition authHeapI h := own impl_state_heap_name (●heap_authoritative h).
  Definition task_agree p d := own impl_task_data_name {[ p := to_agree d ]}.
End ImplPredicates.

Section SpecPredicates.
  Context `{specStateG Σ, inG Σ heapR}.
  Local Open Scope I.
  Definition mapstoS l v q := own spec_state_heap_name (◯mapsto_cell l v q).
  Definition authHeapS h := own spec_state_heap_name (●heap_authoritative h).

  Definition task_runnable p e: taskbufferR := ◯{[ p := Excl (running e) ]}.
  Definition task_done p v: taskbufferR := ◯{[ p := Excl (done v) ]}.
  Definition task_pending p e := own spec_state_task_buffer_name (task_runnable p e).
  Definition task_running p e := task_pending p e ∗ own spec_state_running_task_name (◯Excl' p).
  Definition task_finished p v := own spec_state_task_buffer_name (task_done p v).

  Definition task_buffer_translate (t: task_buffer): taskbufferR := ●(Excl <$> t).
  Definition task_authoritative t (p: tid) :=
    own spec_state_task_buffer_name (task_buffer_translate t) ∗
        own spec_state_running_task_name (●Excl' p).
  Definition cfg_authoriative c :=
    authHeapS (cfg_heap c) ∗ task_authoritative (cfg_tb c) (cfg_task c).
End SpecPredicates.

Notation "l ↦{ q }ᵢ v" := (mapstoI l v q%Qp) (at level 20, q at level 50): uPred_scope.
Notation "l ↦{ q }ₛ v" := (mapstoS l v q%Qp) (at level 20, q at level 50): uPred_scope.
Notation "l ↦ᵢ v" := (l ↦{1}ᵢ v)%I (at level 20): uPred_scope.
Notation "l ↦ₛ v" := (l ↦{1}ₛ v)%I (at level 20): uPred_scope.
Notation "l ↦{ q }ᵢ -" := (∃ v, l ↦{q%Qp}ᵢ v)%I (at level 20, q at level 50): uPred_scope.
Notation "l ↦{ q }ₛ -" := (∃ v, l ↦{q%Qp}ₛ v)%I (at level 20, q at level 50): uPred_scope.
Notation "l ↦ᵢ -" := (l ↦{1}ᵢ -)%I (at level 20): uPred_scope.
Notation "l ↦ₛ -" := (l ↦{1}ₛ -)%I (at level 20): uPred_scope.
Notation "p ⤇ 'run:' e" := (task_pending p e) (at level 20).
Notation "p ⤇ 'active:' e" := (task_running p e) (at level 20).
Notation "p ⤇ 'done:' v" := (task_finished p v) (at level 20).


Record async_adequate e h (ϕ: val → Prop) :=
  { async_result: ∀ c v,
      cfg_steps (cfg_init e h) c → cfg_tb c !! main_task = Some (done v) → ϕ v;
    async_safe: ∀ c, cfg_steps (cfg_init e h) c →
                     (∃ c', cfg_step c c') ∨ ¬∃ t e, cfg_tb c !! t = Some (running e);
    async_has_main: ∀ c, cfg_steps (cfg_init e h) c → is_Some (cfg_tb c !! main_task)
  }.

(** Axiomatic semantics.

  With the current setup of Iris, expressing the natural semantics
  of asynchronous programs as a [Language] in the sense of the
  [program_logic] sublibrary doesn't work properly: we cannot model
  threads being disabled, but have to go through a lock-based implementation
  instead, or write a scheduler. Since this is quite annoying, we simply
  axiomatize a WP-like approach here.

  TODO: Properly implement a weakestpre that allows tasks to be disabled. *)
Module Type AxiomaticSemantics.
  Parameter axiomaticIrisG: gFunctors → Set.
  Existing Class axiomaticIrisG.
  Declare Instance axiomaticIrisG_invG `{axiomaticIrisG Σ}: invG Σ.
  Declare Instance axiomaticIrisG_implStateG `{axiomaticIrisG Σ}: implStateG Σ.

  Parameter wp: ∀ `{axiomaticIrisG Σ}, coPset -c> expr -c> (val -c> iProp Σ) -c> iProp Σ.
  Notation "'WP' e @ E {{ Φ } }" := (wp E e Φ)
           (at level 20, e, Φ at level 200,
            format "'[' 'WP'  e  '/' @  E  {{  Φ  } } ']'") : uPred_scope.
  Notation "'WP' e {{ Φ } }" := (wp ⊤ e Φ)
           (at level 20, e, Φ at level 200,
            format "'[' 'WP'  e  '/' {{  Φ  } } ']'") : uPred_scope.
  
  Notation "'WP' e @ E {{ v , Q } }" := (wp E e (λ v, Q))
           (at level 20, e, Q at level 200,
            format "'[' 'WP'  e  '/' @  E  {{  v ,  Q  } } ']'") : uPred_scope.
  Notation "'WP' e {{ v , Q } }" := (wp ⊤ e (λ v, Q))
           (at level 20, e, Q at level 200,
            format "'[' 'WP'  e  '/' {{  v ,  Q  } } ']'") : uPred_scope.

  Section InIris.
    Context `{axiomaticIrisG Σ, inG Σ heapUR} (heap_name task_buffer_name: gname).
    Local Open Scope I.

    (** Local operations *)
    Axiom wp_const: ∀ E (c: const), WP c @ E {{ x, ⌜x = VConst c⌝ }}.
    Axiom wp_app: ∀ E f x e e' v ϕ,
        to_val e' = Some v →
        WP subst' f (Rec f x e) (subst' x e' e) @ E {{ ϕ }} ⊢
        WP App (Rec f x e) e' @ E {{ ϕ }}.
    Axiom wp_if_true: ∀ E e e' ϕ,
        WP e @ E {{ ϕ }} ⊢ WP If Ctrue e e' @ E {{ ϕ }}.
    Axiom wp_if_false: ∀ E e e' ϕ,
        WP e' @ E {{ ϕ }} ⊢ WP If Cfalse e e' @ E {{ ϕ }}.
    Axiom wp_alloc: ∀ E e v,
        to_val e = Some v →
        WP Alloc e @ E {{ x, ∃ l, ⌜x = VConst (Cloc l)⌝ ∗ l ↦ᵢ v }}.
    Axiom wp_read: ∀ E l v q,
        l ↦{q}ᵢ v ⊢ WP Read (Cloc l) @ E {{ x, ⌜x = v⌝ ∗ l ↦{q}ᵢ v }}.
    Axiom wp_write: ∀ E l e v,
        to_val e = Some v →
        l ↦ᵢ - ⊢ WP Write (Cloc l) e @ E {{ x, ⌜x = VConst Cunit⌝ ∗ l ↦ᵢ v }}.

    (** Axiomatization of wait permissions. *)
    Parameter wait: tid → (val → iProp Σ) → iProp Σ.
    Parameter waitN: namespace.
    Declare Instance wait_nonexpansive t n:
      Proper (pointwise_relation _ (dist n) ==> dist n) (wait t).
    Axiom wait_split: ∀ t ϕ₁ ϕ₂,
        wait t (λ v, ϕ₁ v ∗ ϕ₂ v) ={↑waitN}=∗ wait t ϕ₁ ∗ wait t ϕ₂.
    Axiom wait_combine: ∀ t ϕ₁ ϕ₂,
        wait t ϕ₁ ∗ wait t ϕ₂ ={↑waitN}=∗ wait t (λ v, ϕ₁ v ∗ ϕ₂ v).

    (** Task operations *)
    Axiom wp_post: ∀ E e ϕ,
        WP e {{ ϕ }} ⊢
        WP Post e @ E {{ v, ∃ t, ⌜v = VConst (Ctid t)⌝ ∗ wait t ϕ }}.
    Axiom wp_wait: ∀ E t ϕ,
        wait t ϕ ⊢ WP Wait (Ctid t) @ E {{ v, ϕ v }}.
    
    (** Meta-theory and bind rule; this duplicates parts of [program_logic/weakestpre],
        namely everything that requires unfolding. The rest can be shown from these axioms. *)
    Declare Instance wp_nonexpansive E e n:
      Proper (pointwise_relation _ (dist n) ==> dist n) (wp E e).
    Axiom wp_value': ∀ E ϕ v, ϕ v ⊢ WP of_val v @ E {{ ϕ }}.
    Axiom wp_value_inv: ∀ E ϕ v, WP of_val v @ E {{ ϕ }} ={E}=∗ ϕ v.
    Axiom wp_strong_mono: ∀ E E' e ϕ ψ,
        E ⊆ E' → (∀ v, ϕ v ={E'}=∗ ψ v) ∗ WP e @ E {{ ϕ }} ⊢ WP e @ E' {{ ψ }}.
    Axiom fupd_wp: ∀ E e ϕ, (|={E}=> WP e @ E {{ ϕ }}) ⊢ WP e @ E {{ ϕ }}.

    Parameter atomic: expr → Prop.
    Existing Class atomic.
    Axiom wp_atomic: ∀ E E' e ϕ,
        atomic e →
        (|={E,E'}=> WP e @ E' {{ v, |={E',E}=> ϕ v }}) ⊢ WP e @ E {{ ϕ }}.
    Axiom atomic_alloc: ∀ e v, to_val e = Some v → atomic (Alloc e).
    Axiom atomic_read: ∀ l, atomic (Read (Cloc l)).
    Axiom atomic_write: ∀ l e v, to_val e = Some v → atomic (Write (Cloc l) e).
    Axiom atomic_post: ∀ e, atomic (Post e).
    Axiom atomic_skip: ∀ f x e v e' v',
        to_val e = Some v → to_val e' = Some v' →
        atomic (App (Rec f x e) e').
    
    Axiom wp_step_fupd: ∀ E E' e P ϕ,
      to_val e = None →
      E' ⊆ E →
      (|={E,E'}▷=> P) -∗ WP e @ E' {{ v, P ={E}=∗ ϕ v }} -∗ WP e @ E {{ ϕ }}.
    Axiom wp_bind_item: ∀ K E e ϕ,
        WP e @ E {{ v, WP (fill_ectx_item (of_val v) K) @ E {{ ϕ }} }} ⊢
        WP (fill_ectx_item e K) @ E {{ ϕ }}.
    Axiom wp_bind_item_inv: ∀ K E e ϕ,
        WP (fill_ectx_item e K) @ E {{ ϕ }} ⊢
        WP e @ E {{ v, WP (fill_ectx_item (of_val v) K) @ E {{ ϕ }} }}.

    (** This duplicates results from [program_logic/adequacy]. *)
    Axiom wp_adequate: ∀ h e ϕ,
        (|={⊤}=> authHeapI h ∗ WP e {{ v, ⌜ϕ v⌝ }}) → async_adequate e h ϕ.
  End InIris.
End AxiomaticSemantics.

Module AxiomaticFacts(Import AxSem: AxiomaticSemantics).
  Section InIris.
    Context `{axiomaticIrisG Σ, inG Σ heapUR} (heap_name task_buffer_name: gname).
    Local Open Scope I.
    Global Instance wp_proper E e: Proper (pointwise_relation _ (≡) ==> (≡)) (wp E e).
    Proof.
      intros ϕ ϕ' eqϕ; by apply equiv_dist => n; apply wp_nonexpansive => v; apply equiv_dist.
    Qed.
    
    Lemma wp_mono E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → WP e @ E {{ Φ }} ⊢ WP e @ E {{ Ψ }}.
    Proof.
      iIntros (HΦ) "H"; iApply (wp_strong_mono E E); auto.
      iIntros "{$H}" (v) "?". by iApply HΦ.
    Qed.
    Lemma wp_mask_mono E1 E2 e Φ : E1 ⊆ E2 → WP e @ E1 {{ Φ }} ⊢ WP e @ E2 {{ Φ }}.
    Proof. iIntros (?) "H"; iApply (wp_strong_mono E1 E2); auto. iFrame; eauto. Qed.
    Global Instance wp_mono' E e :
      Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp E e).
    Proof. by intros Φ Φ' ?; apply wp_mono. Qed.

    (*
    Lemma wp_value E Φ e v `(to_val e = Some v): Φ v ⊢ WP e @ E {{ Φ }}.
    Proof. intros; rewrite -(of_to_val e v) //; by apply wp_value'. Qed.*)
    Lemma wp_fupd E e Φ : WP e @ E {{ v, |={E}=> Φ v }} ⊢ WP e @ E {{ Φ }}.
    Proof. iIntros "H". iApply (wp_strong_mono E); try iFrame; auto. Qed.
    Lemma wp_value_fupd' E Φ v : (|={E}=> Φ v) ⊢ WP of_val v @ E {{ Φ }}.
    Proof. intros. by rewrite -wp_fupd -wp_value'. Qed.
    (*
    Lemma wp_value_fupd E Φ e v `{!IntoVal e v} : (|={E}=> Φ v) ⊢ WP e @ E {{ Φ }}.
    Proof. intros. rewrite -wp_fupd -wp_value //. Qed.*)

    Lemma wp_frame_l E e Φ R : R ∗ WP e @ E {{ Φ }} ⊢ WP e @ E {{ v, R ∗ Φ v }}.
    Proof. iIntros "[??]". iApply (wp_strong_mono E E _ Φ); try iFrame; eauto. Qed.
    Lemma wp_frame_r E e Φ R : WP e @ E {{ Φ }} ∗ R ⊢ WP e @ E {{ v, Φ v ∗ R }}.
    Proof. iIntros "[??]". iApply (wp_strong_mono E E _ Φ); try iFrame; eauto. Qed.

    Lemma wp_frame_step_l E1 E2 e Φ R :
      to_val e = None → E2 ⊆ E1 →
      (|={E1,E2}▷=> R) ∗ WP e @ E2 {{ Φ }} ⊢ WP e @ E1 {{ v, R ∗ Φ v }}.
    Proof.
      iIntros (??) "[Hu Hwp]". iApply (wp_step_fupd with "Hu"); try done.
      iApply (wp_mono with "Hwp"). by iIntros (?) "$$".
    Qed.
    Lemma wp_frame_step_r E1 E2 e Φ R :
      to_val e = None → E2 ⊆ E1 →
      WP e @ E2 {{ Φ }} ∗ (|={E1,E2}▷=> R) ⊢ WP e @ E1 {{ v, Φ v ∗ R }}.
    Proof.
      rewrite [(WP _ @ _ {{ _ }} ∗ _)%I]comm.
      setoid_rewrite (comm _ _ R).
      apply wp_frame_step_l.
    Qed.
    Lemma wp_frame_step_l' E e Φ R :
      to_val e = None → ▷ R ∗ WP e @ E {{ Φ }} ⊢ WP e @ E {{ v, R ∗ Φ v }}.
    Proof. iIntros (?) "[??]". iApply (wp_frame_step_l E E); try iFrame; eauto. Qed.
    Lemma wp_frame_step_r' E e Φ R :
      to_val e = None → WP e @ E {{ Φ }} ∗ ▷ R ⊢ WP e @ E {{ v, Φ v ∗ R }}.
    Proof. iIntros (?) "[??]". iApply (wp_frame_step_r E E); try iFrame; eauto. Qed.

    Lemma wp_wand E e Φ Ψ :
      WP e @ E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ E {{ Ψ }}.
    Proof.
      iIntros "Hwp H". iApply (wp_strong_mono E); auto.
      iIntros "{$Hwp}" (?) "?". by iApply "H".
    Qed.
    Lemma wp_wand_l E e Φ Ψ :
      (∀ v, Φ v -∗ Ψ v) ∗ WP e @ E {{ Φ }} ⊢ WP e @ E {{ Ψ }}.
    Proof. iIntros "[H Hwp]". iApply (wp_wand with "Hwp H"). Qed.
    Lemma wp_wand_r E e Φ Ψ :
      WP e @ E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @ E {{ Ψ }}.
    Proof. iIntros "[Hwp H]". iApply (wp_wand with "Hwp H"). Qed.
  End InIris.
End AxiomaticFacts.

(** Simulation-side ghost state semantics. *)
Section Simulation.
  Context `{specStateG Σ, invG Σ, inG Σ heapR}.
  Local Open Scope I.
  
  Definition spec_state_invariant c₀: iProp Σ := ∃ c, ⌜cfg_steps c₀ c⌝ ∗ cfg_authoriative c.
  Definition specN := nroot .@ "spec".
  Definition spec_ctx c₀ := inv specN (spec_state_invariant c₀).

  Context (c₀: cfg) (E: coPset) (Egood: ↑specN ⊆ E) (p: tid) (K: list ctx_item).
  Notation ctx := (spec_ctx c₀).
  Notation ACT e := (p ⤇ active: fill_ctx e K).

  Lemma simulate_local_step {A} e (e': A → expr) ϕ ϕ':
    ctx -∗ ACT e -∗ ϕ -∗
        (∀ h t e'', ⌜t !! p = None⌝ → ϕ ∗ authHeapS h ∗ task_authoritative (<[p:=e'']>t) p
                ={E ∖ ↑specN}=∗ ∃ h' t' a, ϕ' a ∗ authHeapS h' ∗ task_authoritative (<[p:=e'']>t') p ∗
                                            ⌜head_step p e h t (e' a) h' t' ∧ t' !! p = None⌝)
    ={E}=∗ ∃ a, ACT (e' a) ∗ ϕ' a.
  Proof.
    iIntros "ctx [task act] pre move".
    iMod (inv_open_timeless with "ctx") as "[inv close]"; auto.
    iDestruct "inv" as ([h t p']) "[steps [heap [tasks sched]]]"; cbn.
    iDestruct "steps" as %steps.
    iAssert (⌜p = p'⌝) with "[act sched]" as %<-.
    { iPoseProof (own_valid_2 with "sched act") as "valid".
      rewrite uPred.discrete_valid auth_valid_discrete_2 /=.
      iDestruct "valid" as %[?%Excl_included%leibniz_equiv _]; auto. }
    iAssert (⌜t !! p = Some (running (fill_ctx e K))⌝) with "[tasks task]" as %task.
    { iPoseProof (own_valid_2 with "tasks task") as "valid".
      rewrite uPred.discrete_valid auth_valid_discrete_2 /= singleton_included.
      iDestruct "valid" as %[[e'' [mt%leibniz_equiv incl]] _].
      rewrite lookup_fmap fmap_Some in mt * => [[s [-> ?]]]; subst.
      apply Excl_included, leibniz_equiv in incl.
      subst; auto. }
    iMod ("move" $! h (delete p t)
          with "[] [$pre $heap tasks $sched]") as (h' t' a) "[post [heap [[tasks sched] step]]]".
    { rewrite lookup_delete; auto. }
    { rewrite insert_delete insert_id; eauto. }
    set (e'' := fill_ctx (e' a) K).
    iDestruct "step" as %[step task'].
    iMod (own_update_2 _ _ _
                       (task_buffer_translate (<[p:=running e'']>t') ⋅ task_runnable p e'')
          with "tasks task")
      as "[tasks task]".
    { rewrite /task_buffer_translate /task_runnable fmap_insert.
      apply auth_update.
      rewrite -(insert_insert t' p _ (running (fill_ctx e K))) !fmap_insert.
      eapply singleton_local_update.
      - by rewrite lookup_insert.
      - apply exclusive_local_update; split. }
    iFrame.
    rewrite /task_buffer_translate.
    iExists a; iFrame.
    iApply "close".
    iExists (CFG h' (<[p:=running e'']>t') p); iFrame.
    iPureIntro.
    eapply rtc_r; eauto.
    econstructor 1; cbn; eauto.
    { apply lookup_insert. }
    split.
    rewrite delete_insert; auto.
  Qed.

  Lemma simulate_local_step_det e e' ϕ ϕ':
    ctx -∗ ACT e -∗ ϕ -∗
        (∀ h t e'', ⌜t !! p = None⌝ → ϕ ∗ authHeapS h ∗ task_authoritative (<[p:=e'']>t) p
                ={E ∖ ↑specN}=∗ ∃ h' t', ϕ' ∗ authHeapS h' ∗ task_authoritative (<[p:=e'']>t') p ∗
                                            ⌜head_step p e h t e' h' t' ∧ t' !! p = None⌝)
    ={E}=∗ ACT e' ∗ ϕ'.
  Proof.
    iIntros "ctx act pre move".
    iMod (simulate_local_step (A:=unit) e (λ _, e') ϕ (λ _, ϕ') with "ctx act pre [move]")
      as ([]) "$"; auto.
    iIntros (h t e'' p_not_in_t) "pre".
    iMod ("move" with "[] pre") as (h' t') "post"; first done.
    iModIntro; by iExists h', t', ().
  Qed.

  Lemma simulate_local_step_pure e e' (step: ∀ p h t, head_step p e h t e' h t):
    ctx -∗ ACT e ={E}=∗ ACT e'.
  Proof.
    iIntros "ctx act".
    iMod (simulate_local_step_det e e' True True with "ctx act [] []") as "[$ _]"; auto.
    iIntros (h t e'' p_not_in_t) "[_ [heap task]]".
    iModIntro; iExists h, t; iFrame.
    iPureIntro.
    split; auto.
  Qed.
  
  Lemma simulate_app f x e e' v (e'_val: to_val e' = Some v):
    ctx -∗ ACT (App (Rec f x e) e') ={E}=∗ ACT (subst' f (Rec f x e) (subst' x e' e)).
  Proof. iApply simulate_local_step_pure; econstructor; eauto. Qed.

  Lemma simulate_if_true e e':
    ctx -∗ ACT (If Ctrue e e') ={E}=∗ ACT e.
  Proof. iApply simulate_local_step_pure; econstructor; eauto. Qed.

  Lemma simulate_if_false e e':
    ctx -∗ ACT (If Cfalse e e') ={E}=∗ ACT e'.
  Proof. iApply simulate_local_step_pure; econstructor; eauto. Qed.

  Lemma simulate_alloc_strong (bad: gset loc) e v (e_value: to_val e = Some v):
    ctx -∗ ACT (Alloc e) ={E}=∗ ∃ (l: loc), ACT (Cloc l) ∗ l ↦ₛ v ∧ (⌜l ∉ bad⌝).
  Proof.
    iIntros "ctx act".
    iApply (simulate_local_step _ _ True with "ctx act [] []"); first done.
    iIntros (h t e'' p_not_in_t) "[_ [heap taskbuffer]]".
    set (pool := dom (gset gname) h ∪ bad).
    pose proof (is_fresh pool) as is_fresh.
    set (l := fresh pool).
    iMod (own_update _ _ (●heap_authoritative (<[l := v]>h) ⋅ ◯mapsto_cell l v 1%Qp)
          with "heap") as "[heap pt]".
    { apply auth_update_alloc.
      rewrite /heap_authoritative !fmap_insert.
      apply alloc_singleton_local_update; last done.
      rewrite !lookup_fmap !fmap_None -(not_elem_of_dom (D:=gset gname)).
      set_solver. }
    iModIntro.
    iExists (<[l:=v]>h), t, l; iFrame.
    iPureIntro.
    split; first set_solver.
    split; last done.
    econstructor; first done.
    rewrite -(not_elem_of_dom (D:=gset gname)); set_solver.
  Qed.

  Corollary simulate_alloc e v (e_value: to_val e = Some v):
    ctx -∗ ACT (Alloc e) ={E}=∗ ∃ l, ACT (Cloc l) ∗ l ↦ₛ v.
  Proof.
    iIntros "ctx act".
    iMod (simulate_alloc_strong ∅ with "ctx act") as (l) "[? [? _]]"; first done.
    iModIntro; iExists l; iFrame.
  Qed.

  Lemma simulate_read l q v:
    ctx -∗ ACT (Read (Cloc l)) -∗ l ↦{q}ₛ v ={E}=∗ ACT (of_val v) ∗ l ↦{q}ₛ v.
  Proof.
    iIntros "ctx act pre".
    iApply (simulate_local_step_det with "ctx act pre []").
    iIntros (h t e'' p_not_in_t) "[pt [heap tasks]]".
    iModIntro; iExists h, t.
    iAssert (⌜h !! l = Some v⌝) with "[heap pt]" as %mt.
    { iPoseProof (own_valid_2 with "heap pt") as "valid".
      rewrite uPred.discrete_valid auth_valid_discrete_2 /mapsto_cell /heap_authoritative.
      rewrite singleton_included.
      iDestruct "valid" as %[[[q' agv] [[[q'' agv'] [mt [eqq eqv]]]%equiv_Some_inv_r' incl]] _].
      iPureIntro; cbn in *.
      apply leibniz_equiv in eqq; subst.
      rewrite !lookup_fmap fmap_Some in mt * => [[agv'' [mt eqs]]].
      injection eqs as -> <-.
      rewrite fmap_Some in mt * => [[v' [mt ?]]]; subst.
      apply Some_pair_included_total_2  in incl.
      destruct incl as [_ incl].
      rewrite eqv to_agree_included in incl *.
      intros ->%leibniz_equiv; done. }
    iFrame.
    iPureIntro; split; auto.
    constructor; done.
  Qed.

  Lemma simulate_write l e v (e_val: to_val e = Some v):
    ctx -∗ ACT (Write (Cloc l) e) -∗ l ↦ₛ - ={E}=∗ ACT Cunit ∗ l ↦ₛ v.
  Proof.
    iIntros "ctx act pre".
    iApply (simulate_local_step_det with "ctx act pre []").
    iIntros (h t e'' p_not_in_t) "[pt [heap tasks]]".
    iDestruct "pt" as (v') "pt".
    iAssert (⌜is_Some (h!!l)⌝) with "[heap pt]" as %alloc.
    { iPoseProof (own_valid_2 with "heap pt") as "valid".
      rewrite uPred.discrete_valid auth_valid_discrete_2 /mapsto_cell /heap_authoritative.
      rewrite singleton_included.
      iDestruct "valid" as %[[[q' agv] [[[q'' agv'] [mt _]]%equiv_Some_inv_r' incl]] _].
      iPureIntro.
      rewrite !lookup_fmap fmap_Some in mt * => [[agv'' [mt _]]].
      rewrite fmap_Some in mt * => [[v'' [-> _]]]; eauto. }
    iMod (own_update_2 _ _ _ (●heap_authoritative (<[l := v]>h) ⋅ ◯mapsto_cell l v 1%Qp)
          with "heap pt") as "[heap pt]".
    { apply auth_update.
      rewrite /heap_authoritative /mapsto_cell !fmap_insert.
      destruct alloc as [? mt].
      eapply singleton_local_update.
      { by rewrite !lookup_fmap mt. }
      apply exclusive_local_update; done. }
    iModIntro; iExists (<[l:=v]>h), t; iFrame.
    iPureIntro; split; auto.
    constructor; done.
  Qed.

  Lemma simulate_post_strong (bad: gset tid) e:
    ctx -∗ ACT (Post e) ={E}=∗ ∃ (p': tid), ACT (Ctid p') ∗ p' ⤇ run: e ∗ ⌜p' ≠ p ∧ p' ∉ bad⌝.
  Proof.
    iIntros "ctx act".
    iApply (simulate_local_step _ _ True with "ctx act [] []"); first done.
    iIntros (h t e'' p_not_in_t) "[_ [heap [taskbuffer sched]]]".
    set (pool := bad ∪ dom (gset tid) t ∪ {[ p ]}).
    set (p' := fresh pool).
    pose proof (is_fresh pool) as p'_fresh.
    iExists h, (<[p' := running e]>t), p'; iFrame.
    iMod (own_update _ _
                     (task_buffer_translate (<[p:=e'']>(<[p':=running e]>t)) ⋅ task_runnable p' e)
          with "taskbuffer")
      as "[$$]".
    { apply auth_update_alloc.
      rewrite insert_commute; last set_solver.
      rewrite !fmap_insert.
      apply alloc_singleton_local_update; last done.
      rewrite lookup_insert_ne; last set_solver.
      rewrite lookup_fmap fmap_None -(not_elem_of_dom (D:=gset gname)).
      set_solver. }
    iPureIntro.
    split; first set_solver.
    split; first constructor.
    3: rewrite lookup_insert_ne.
    1: rewrite -(not_elem_of_dom (D:=gset gname)).
    all: set_solver.
  Qed.

  Corollary simulate_post e:
    ctx -∗ ACT (Post e) ={E}=∗ ∃ (p': tid), ACT (Ctid p') ∗ p' ⤇ run: e ∗ ⌜p' ≠ p⌝.
  Proof.
    iIntros "ctx act".
    iMod (simulate_post_strong ∅ e with "ctx act") as (p') "[act [task %]]".
    iModIntro; iExists p'; iFrame.
    iPureIntro; tauto.
  Qed.

  Lemma simulate_wait_done p' v (neq: p ≠ p'):
    ctx -∗ ACT (Wait (Ctid p')) -∗ p' ⤇ done: v ={E}=∗ ACT (of_val v) ∗ p' ⤇ done: v.
  Proof.
    iIntros "ctx act pre".
    iApply (simulate_local_step_det with "ctx act pre").
    iIntros (h t e'' p_not_in_t) "[done [heap [task sched]]]".
    iAssert (⌜t !! p' = Some (done v)⌝) with "[done task]" as %result.
    { iPoseProof (own_valid_2 with "task done") as "valid".
      rewrite uPred.discrete_valid auth_valid_discrete_2 singleton_included.
      iDestruct "valid" as %[[y [lookup%leibniz_equiv incl]] valid].
      rewrite lookup_fmap fmap_Some in lookup * => [[x [lookup ?]]]; subst.
      apply Some_included_exclusive in incl.
      2: apply _.
      2: done.
      apply leibniz_equiv in incl.
      injection incl as <-.
      rewrite lookup_insert_ne in lookup; done. }
    iModIntro; iExists h, t; iFrame.
    iPureIntro; split; auto.
    constructor; done.
  Qed.

  Lemma simulate_schedule_step p' e e' s
        (move: ∀ h t, t !! p = Some (running e) →
                      t !! p' = Some (running e') → global_step h t p h (<[p := s]>t) p'):
    ctx -∗ p ⤇ active: e -∗ p' ⤇ run: e'
    ={E}=∗ own spec_state_task_buffer_name (◯{[p:=Excl s]}) ∗ p' ⤇ active: e'.
  Proof.
    iIntros "ctx [taskp act] taskp'".
    iMod (inv_open_timeless with "ctx") as "[inv close]"; first done.
    iDestruct "inv" as ([h t p'']) "[steps [heap [tasks sched]]]".
    iDestruct "steps" as %steps.
    iAssert (⌜p'' = p⌝) with "[sched act]" as %->.
    { iPoseProof (own_valid_2 with "sched act") as "valid".
      rewrite uPred.discrete_valid auth_valid_discrete_2.
      iDestruct "valid" as %[eqp _].
      apply Some_included_exclusive in eqp.
      2: apply _.
      2: done.
      apply leibniz_equiv in eqp.
      injection eqp as ->; done. }
    iAssert (⌜t !! p = Some (running e)⌝) with "[tasks taskp]" as %taskp.
    { iPoseProof (own_valid_2 with "tasks taskp") as "valid".
      rewrite uPred.discrete_valid auth_valid_discrete_2 singleton_included.
      iDestruct "valid" as %[[y [lookup%leibniz_equiv incl]] valid].
      rewrite lookup_fmap fmap_Some in lookup * => [[x [lookup ?]]]; subst.
      apply Some_included_exclusive in incl.
      2: apply _.
      2: done.
      apply leibniz_equiv in incl.
      injection incl as <-; done. }
    iAssert (⌜t !! p' = Some (running e')⌝) with "[tasks taskp']" as %taskp'.
    { iPoseProof (own_valid_2 with "tasks taskp'") as "valid".
      rewrite uPred.discrete_valid auth_valid_discrete_2 singleton_included.
      iDestruct "valid" as %[[y [lookup%leibniz_equiv incl]] valid].
      rewrite lookup_fmap fmap_Some in lookup * => [[x [lookup ?]]]; subst.
      apply Some_included_exclusive in incl.
      2: apply _.
      2: done.
      apply leibniz_equiv in incl.
      injection incl as <-; done. }
    cbn in *.
    iMod (own_update_2  _ _ _ (task_buffer_translate (<[p:=s]>t) ⋅ ◯{[p:=Excl s]})
          with "tasks taskp")
      as "[tasks taskp]".
    { apply auth_update.
      rewrite fmap_insert.
      eapply singleton_local_update.
      { by rewrite lookup_fmap taskp. }
      apply exclusive_local_update; done. }
    iMod (own_update_2 _ (●Excl' p) _ (●Excl' p' ⋅ ◯Excl' p') with "sched act") as "[sched act]".
    { by apply auth_update, option_local_update, exclusive_local_update. }
    iFrame.
    iApply "close".
    iExists (CFG h (<[p:=s]>t) p').
    iFrame.
    iPureIntro.
    eapply rtc_r; eauto.
    apply move; done.
  Qed.

  Lemma simulate_wait_schedule p' p'' e:
    ctx -∗ ACT (Wait (Ctid p'')) -∗ p' ⤇ run: e
    ={E}=∗ p ⤇ run: fill_ctx (Wait (Ctid p'')) K ∗ p' ⤇ active: e.
  Proof.
    iApply simulate_schedule_step.
    intros * taskp taskp'.
    rewrite insert_id; auto.
    econstructor 2; eauto.
    exists e; done.
  Qed.

  Lemma simulate_done_schedule p' v e e' (is_val: to_val e = Some v):
    ctx -∗ p ⤇ active: e -∗ p' ⤇ run: e' ={E}=∗ p ⤇ done: v ∗ p' ⤇ active: e'.
  Proof.
    iApply simulate_schedule_step.
    intros * taskp taskp'.
    constructor 3 with e; auto.
    exists e'; done.
  Qed.
End Simulation.

Section ExistentialTriple.
  Context `{specStateG Σ, invG Σ, inG Σ heapR} (E: coPset) (c: cfg).
  Definition existential_triple (ϕ: iProp Σ) e (ϕ': val → iProp Σ): iProp Σ :=
    (∀ p K, spec_ctx c -∗ ϕ -∗ p ⤇ active: fill_ctx e K
                                           ={E}=∗ ∃ v, ϕ' v ∗ p ⤇ active: fill_ctx (of_val v) K)%I.
  Global Instance existential_triple_proper:
    Proper ((⊢) --> (=) ==> pointwise_relation val (⊢) ==> (⊢)) existential_triple.
  Proof. rewrite /existential_triple. solve_proper. Qed.
End ExistentialTriple.

