From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import agree auth.
From esop Require Import overlap delayed specification typetranslation types corecalculus oneshot.
From stdpp Require Import gmap coPset.

Section Theory.
  Context `{allG Σ}.
  (** Closure: Async operations *)
  Ltac intro_equiv x := f_equiv; intro x.
  Local Open Scope I.
  
  Lemma closed_post (Γ: env) (η: hexpr) e e' A (τ: type) (η': hexpr) ξ
        (ξ_fresh_Γ: ξ ∉ names Γ) (ξ_fresh_η: ξ ∉ names η) (ξ_fresh_A: ξ ∉ A)
        (ξ_fresh_τ: ξ ∉ names τ) (ξ_fresh_η': ξ ∉ names η'):
    delayed_typed Γ η e e' A τ η' -∗
                  delayed_typed Γ η (Post e) (Post e') {[ξ]} (ttask ξ A τ) (hwait ξ A η').
  Proof.
    iIntros "del".
    iIntros (D N σ) "pre"; cbn [subst].
    (* Allocate ghost state *)
    iApply fupd_wp.
    iMod (own_alloc (@unset conn_mapC)) as (γD) "ownD"; first done.
    iMod (own_alloc (@unset name_mapC)) as (γN) "ownN"; first done.
    set (T := TaskData e' Γ η η' A D γD γN).
    set (promise_body t x := int_i_promise_body int_s_type int_s_heap N A τ (int_i_type τ) t x).
    set (wait_body t x := int_i_wait_body η' (int_i_heap η') A N t x).
    iAssert (∀ t, task_agree t T -∗ WP subst (of_val <$> σ) e
                             {{ x, promise_body t x ∗ wait_body t x }})
            with "[ownD ownN del pre]" as "wp".
    { iSpecialize ("del" with "pre").
      iIntros (t) "#agree_t".
      iApply wp_fupd.
      iApply (wp_wand with "del").
      iIntros (v) "H".
      iDestruct "H" as (N' D' d') "[eqs [ty [#sim heap]]]".
      iMod (own_update _ _ (agreed D') with "ownD") as "#ownD"; first apply oneshot_update.
      iMod (own_update _ _ (agreed (N': leibnizC name_map)) with "ownN") as "#ownN";
        first apply oneshot_update.
      iModIntro.
      iDestruct "eqs" as %[eqN eqd].
      iSplitR "heap".
      - iExists T, D', N'.
        iSplit.
        { repeat iSplit; auto. }
        rewrite /ip_impl /ip_sim.
        iSplitL "ty".
        { iExists d'; iSplit; last done.
          iPureIntro.
          assert (of_gset (names τ ∖ A) ⊆ not_new A).
          { intro; rewrite elem_of_of_gset elem_of_not_new elem_of_difference; tauto. }
          repeat split; auto.
          all: apply overlap_cast; by eapply overlap_mono. }
        iAlways.
        iSplit; first done.
        iExact "sim".
      - iExists T, D', N'; iFrame.
        repeat iSplit; auto.
        iPureIntro.
        apply overlap_cast, (overlap_sub (not_new A)); last done.
        intro; rewrite elem_of_of_gset elem_of_difference elem_of_not_new; tauto. }
    iPoseProof (wp_post ⊤ with "wp") as "wp".
    iModIntro.
    iApply wp_fupd.
    iApply (wp_wand with "wp").
    iIntros (v) "H".
    iDestruct "H" as (t) "[% [wait #t_agree]]"; subst.
    iPoseProof (wait_split with "wait") as "waits".
    iPoseProof (fupd_mask_mono _ ⊤ with "waits") as "waits"; first auto.
    iMod "waits" as "[promise wait]".      
    iMod (inv_alloc promiseN with "promise") as "promise".
    iAssert (int_i_type (Promise(ξ,A) τ) Cunit (<[ξ:=Task t]>N) (Ctid t))
    with "[promise]" as "promise".
    { cbn; iExists t; iSplit.
      - rewrite !lookup_insert; auto.
      - iApply (inv_Proper with "promise").
        apply wait_Proper; intros t' v'.
        rewrite /promise_body /int_i_promise_body /ip_impl.
        intro_equiv U; intro_equiv D'; intro_equiv N'.
        do 2 f_equiv; intro_equiv d.
        do 3 f_equiv.
        apply (overlap_iff (names τ ∖ A)); first done.
        intros ξ' inξ'.
        rewrite lookup_insert_ne; first done.
        clear -inξ' ξ_fresh_τ; set_solver. }
    iAssert (int_i_heap (Wait(ξ,A) η') (<[name ξ:=VConst (Ctid t)]>(<[RET:=VConst Cunit]>∅))
                        (<[ξ:=Task t]>N))
    with "[wait]" as "wait".
    { cbn; iExists t.
      rewrite !lookup_insert; iSplit; auto.
      iApply (wait_Proper with "wait"); intros t' v.
      rewrite /wait_body /int_i_wait_body.
      intro_equiv U; intro_equiv D'; intro_equiv N'.
      do 4 f_equiv.
      intro ξ'; rewrite elem_of_difference => [[inξ' notinξ']].
      rewrite lookup_insert_ne; first done.
      intros <-; contradiction. }
    iModIntro.
    iExists (<[ξ:=Task t]>N), (<[name ξ:=VConst (Ctid t)]>(<[RET:=VConst Cunit]>∅)), (VConst Cunit).
    iFrame.
    iSplit.
    { rewrite lookup_insert_ne ?lookup_insert; last discriminate.
      iPureIntro; split; last done.
      intros ξ'.
      rewrite elem_of_not_new not_elem_of_singleton => [neq].
      rewrite lookup_insert_ne; done. }
    clear σ N promise_body wait_body.
    iAlways.
    iIntros (N σ p K) "#ctx [env pre] move"; cbn -[difference].
    iMod (simulate_post ⊤ _ p K N with "ctx move") as (p') "[move [move' [#agree neq]]]"; auto.
    iModIntro.
    iDestruct "pre" as (n) "pre".
    iExists (Ctid p'); iFrame.
    iExists (VConst Cunit), (<[ξ:=Task p']>N).
    iSplit.
    { iDestruct "neq" as %neq; iPureIntro.
      split.
      - intro ξ'; rewrite elem_of_not_new not_elem_of_singleton => [neq'].
        rewrite lookup_insert_ne; done.
      - rewrite lookup_insert_ne ?lookup_insert; done. }
    iSplit.
    { rewrite /int_s_promise.
      iExists p', N.
      iSplit; first done.
      rewrite lookup_insert.
      iPureIntro; repeat split; auto.
      intros ξ'.
      rewrite elem_of_difference => [[inξ' notinξ']].
      rewrite lookup_insert_ne; first done.
      intros <-; contradiction. }
    iExists (S n); rewrite /= /int_s_wait.
    iExists t, p', T, σ.
    iSplit.
    { iPureIntro; rewrite !lookup_insert; auto. }
    iSplit; auto.
    iFrame.
    iExists N; iFrame.
    iSplit; auto.
    { iPureIntro.
      intro ξ'.
      rewrite elem_of_difference => [[inξ' notinξ']].
      rewrite lookup_insert_ne; first done.
      intros <-; contradiction. }
    Unshelve. auto.
  Qed.

  Instance wait_proper t:
    Proper (pointwise_relation _ (pointwise_relation _ (≡)) ==> (⊣⊢)) (wait t).
  Proof.
    intros ϕ ϕ' eqϕ.
    rewrite equiv_dist => [n].
    apply: wait_nonexpansive => [t' v].
    rewrite eqϕ; done.
  Qed.

  Lemma task_agree_eq t U U': task_agree t U -∗ task_agree t U' -∗ ⌜U = U'⌝.
  Proof.
    iIntros "ag ag'".
    iPoseProof (own_valid_2 with "ag ag'") as "valid".
    rewrite uPred.discrete_valid.
    rewrite gmap.op_singleton gmap.singleton_valid.
    iDestruct "valid" as %->%agree.agree_op_invL'; auto.
  Qed.

  
  Lemma agreed_equiv {A: ofeT} {Adiscr: Discrete A}
        {inA: inG Σ (oneshotR A)} γ (x x': A):
    (own γ (agreed x) -∗ own γ (agreed x') -∗ ⌜x ≡ x'⌝).
  Proof.
    iIntros "ag ag'".
    iPoseProof (own_valid_2 with "ag ag'") as "valid".
    rewrite uPred.discrete_valid /agreed csum.Cinr_op.
    iDestruct "valid" as %?%agree.agree_op_inv'; auto.
  Qed.

  Lemma agreed_eq {A: Type}
        {inA: inG Σ (oneshotR (leibnizC A))} γ (x x': A):
    (own γ (agreed (x: leibnizC A)) -∗ own γ (agreed (x': leibnizC A)) -∗ ⌜x = x'⌝).
  Proof. iApply (@agreed_equiv (leibnizC A) _ inA γ x x'). Qed.

  Lemma spec_task_agree_eq t A A': spec_task_agree t A -∗ spec_task_agree t A' -∗ ⌜A = A'⌝.
  Proof.
    iIntros "ag ag'".
    rewrite /spec_task_agree.
    iPoseProof (own_valid_2 with "ag ag'") as "valid".
    rewrite uPred.discrete_valid.
    rewrite -auth_frag_op gmap.op_singleton.
    iDestruct "valid" as %<-%gmap.singleton_valid%agree_op_invL'; auto.
  Qed.
  
  Lemma closed_wait (x: string) ξ A (τ: type) (η: hexpr)
        (ξ_not_in_τ: ξ ∉ names τ) (ξ_not_in_η: ξ ∉ names η):
    delayed_typed (<[x:=ttask ξ A τ]>∅) (hwait ξ A η) (Wait x) (Wait x) A τ η.
  Proof.
    iIntros (D N σ) "[[env_names env] pre]".
    iDestruct "env_names" as %[domσ domD].
    assert (is_Some (σ !! x)) as [v val_x].
    { apply domσ; rewrite lookup_insert; eauto. }
    assert (is_Some (D !! var x)) as [d conn_x].
    { apply domD; rewrite lookup_insert; eauto. }
    iDestruct ("env" $! x _ v d with "[]") as "#promise".
    { rewrite /int_env_data lookup_insert; eauto. }
    rewrite /= lookup_fmap val_x /=.
    iDestruct "promise" as (t) "[eqs promise]".
    iDestruct "eqs" as %[taskξ ->].
    iApply fupd_wp.
    iInv promiseN as "promisewait" "close".
    iPoseProof (wait_split_later with "[promisewait]") as "split".
    { iNext.
      iApply (wait_proper t with "promisewait").
      iIntros (t' v); iSplit.
      - iIntros "[pb _]"; iExact "pb".
      - rewrite /int_i_promise_body.
        iIntros "#pre".
        iSplit; iExact "pre". }
    iPoseProof (fupd_mask_mono _ (⊤ ∖ ↑promiseN) with "split") as "split"; first solve_ndisj.
    iMod "split" as "[promisewait pw']".
    iMod ("close" with "pw'") as "_".
    iDestruct "pre" as (t') "[names pre]".
    rewrite taskξ.
    iDestruct "names" as %[[=<-] taskξD].
    iPoseProof (wait_combine_later with "[$pre $promisewait]") as "wait".
    iPoseProof (fupd_mask_mono _ ⊤ with "wait") as "wait"; first solve_ndisj.
    iMod "wait" as "wait".
    iModIntro.
    iPoseProof (wp_wait with "wait") as "wp".
    iApply (wp_wand with "wp").
    iIntros (v) "[wb pb]".
    iDestruct "wb" as (U D' N') "[[#agreeU [#agreeD' #agreeN']] [ovη post]]".
    iDestruct "ovη" as %ovη.
    iDestruct "pb" as (U' D'' N'') "[[agreeU' [agreeD'' agreeN'']] [H #sim]]".
    iDestruct "H" as (d') "[names type]".
    iDestruct "names" as %[eqd' ovτ].
    iDestruct (task_agree_eq with "agreeU agreeU'") as %<-; iClear "agreeU'".
    iDestruct (agreed_eq (A := conn_map) with "agreeD' agreeD''") as %<-; iClear "agreeD''".
    iDestruct (agreed_eq (A := name_map) with "agreeN' agreeN''") as %<-; iClear "agreeN''".
    iExists (N' ~[A]~> N), D', d'.
    repeat iSplit.
    { iPureIntro.
      intro ξ'.
      rewrite elem_of_not_new => [notinξ'].
      rewrite lookup_merge_along_not_in; done. }
    { done. }
    { iApply (int_i_type_local with "type").
      1,3: done.
      intros ξ' inξ'.
      destruct (decide (ξ' ∈ A)) as [case|case].
      - by rewrite lookup_merge_along_in.
      - rewrite lookup_merge_along_not_in; last done.
        rewrite (ovτ ξ') ?elem_of_difference; auto. }
    all: cycle 1.
    { iApply (int_i_heap_local with "post").
      { done. }
      intros ξ' inξ'.
      destruct (decide (ξ' ∈ A)) as [case|case].
      - by rewrite lookup_merge_along_in.
      - rewrite lookup_merge_along_not_in; last done.
        rewrite (ovη ξ') ?elem_of_difference; auto. }
    iClear "post type promise agreeN'"; iAlways.
    clear N N' ovη ovτ taskξ σ domσ val_x v.
    iIntros (N σ p K) "#ctx [[env_names promise] wait] move".
    iDestruct "env_names" as %[domσ _].
    assert (is_Some (σ !! x)) as [v val_x].
    { apply domσ; rewrite lookup_insert; eauto. }    
    iSpecialize ("promise" $! x (ttask ξ A τ) v d with "[]").
    { rewrite /int_env_data lookup_insert; auto. }
    iDestruct "sim" as "[% sim]"; subst A.
    iDestruct "promise" as (ts Npre) "[agreePre names]".
    iDestruct "names" as %[taskξ [Npreτ ->]].
    iDestruct "wait" as ([|n]) "wait"; cbn [int_s_heap int_s_heap_rec int_s_heap_approx].
    all: iDestruct "wait" as (ti' ts' U' σ') "[names [agreeU' [move' pre]]]".
    all: iDestruct "pre" as (Npre') "[env [pre [agreeNpre' Npreη]]]".
    { iDestruct "pre" as "[]". }
    rewrite taskξ taskξD.
    iDestruct "names" as %[[=<-] [[=<-] [eqη ->]]].
    iDestruct (task_agree_eq with "agreeU agreeU'") as %<-; iClear "agreeU'".
    iDestruct (spec_task_agree_eq with "agreePre agreeNpre'") as %<-.
    iSpecialize ("sim" $! Npre σ' ts [] with "ctx [$env pre]").
    { by iExists n. }
    iDestruct "Npreη" as %Npreη; iClear "agreeNpre' agreePre agreeU agreeD'".
    rewrite /= lookup_fmap val_x /=.
    iMod (simulate_wait_schedule with "ctx move move'") as "[move move']"; first auto.
    iMod ("sim" with "move'") as (v) "[post move']".
    iMod (simulate_done_schedule with "ctx move' move") as "[move' move]"; first auto.
    { apply to_of_val. }
    iAssert (⌜p ≠ ts⌝) with "[move move']" as %neqp.
    { iDestruct "move" as "[move _]".
      iPoseProof (own_valid_2 with "move move'") as "valid".
      rewrite /task_runnable /task_done -auth_frag_op uPred.discrete_valid.
      iDestruct "valid" as %valid.
      iPureIntro; intros <-.
      rewrite gmap.op_singleton in valid.
      rewrite auth_valid_eq /= gmap.singleton_valid in valid * => [[]]. }
    iMod (simulate_wait_done with "ctx move move'") as "[move _]"; auto.
    iExists v; iFrame.
    iModIntro.
    iDestruct "post" as (ds' Ns') "[names [type heap]]".
    iDestruct "names" as %[Npre' eqD'].
    iExists ds', (Ns' ~[td_alloc U]~> N).
    iSplit.
    { iPureIntro; split; auto.
      intros ξ'.
      rewrite elem_of_not_new => [notinξ'].
      rewrite lookup_merge_along_not_in; done. }
    iSplit.
    - iApply (int_s_type_local with "type").
      1,3: done.
      intros ξ' inξ'.
      destruct (decide (ξ' ∈ td_alloc U)) as [case|case].
      { by rewrite lookup_merge_along_in. }
      rewrite lookup_merge_along_not_in; last done.
      rewrite -(Npreτ ξ') ?elem_of_difference; last done.
      rewrite (Npre' ξ') ?elem_of_not_new; done.
    - rewrite (int_s_heap_proper _ _ eqη).
      iApply (int_s_heap_local with "heap").
      1: done.
      intros ξ' inξ'.
      destruct (decide (ξ' ∈ td_alloc U)) as [case|case].
      { by rewrite lookup_merge_along_in. }
      rewrite lookup_merge_along_not_in; last done.
      rewrite -(Npreη ξ') ?elem_of_difference.
      2: by rewrite eqη.
      rewrite (Npre' ξ') ?elem_of_not_new; done.
  Qed.
End Theory.