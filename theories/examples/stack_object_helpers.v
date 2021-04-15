From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules rules_LoadU_derived logrel fundamental region_invariants_revocation region_invariants_static region_invariants_batch_uninitialized.
From cap_machine Require Export iris_extra addr_reg_sample region_macros contiguous stack_macros_helpers macros.

Section stack_object.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          `{MonRef: MonRefG (leibnizO _) CapR_rtc Σ} {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.


  (* The following lemma will be used to make sure that any object passed as a parameter *)
  (* on the stack, will be disjoint from the current stack *)
  Lemma input_stack_disjoint W a0 a1 a2 p l b e a :
    (a0 + 1)%a = Some a1 →
    readAllowed p = true →
    Forall (λ a, W.1 !! a = Some Monotemporary ∨ (∃ w, W.1 !! a = Some (Uninitialized w))) (region_addrs a1 a2) →
    interp W (inr (p,l,b,e,a)) ∗ future_pub_a_mono a0 (λ Wv, interp Wv.1 Wv.2) (inr (p,l,b,e,a)) -∗
    ⌜(region_addrs b e) ## (region_addrs a1 a2)⌝.
  Proof.
    iIntros (Hincr Hra Hforall) "[#Hvalid #Hmono] /=".
    rewrite elem_of_disjoint. iIntros (i Hin1 Hin2).
    iDestruct (readAllowed_implies_region_conditions with "Hvalid") as "Hcond";auto.
    iDestruct (big_sepL_elem_of with "Hcond") as (p' Hflows) "[Hrwcond %]";eauto.
    assert (W.1 !! i = Some Monotemporary ∨ W.1 !! i = Some Permanent) as Hi.
    { destruct (pwl p);auto. destruct l;auto. }
    revert Hforall; rewrite Forall_forall =>Hforall. apply Hforall in Hin2 as Ha.
    destruct Ha as [Ha | [w Ha] ]; destruct Hi as [Hi | Hi];try congruence.
    apply elem_of_region_addrs in Hin1 as Hlelt1. destruct Hlelt1 as [Hle1 Hlt1].
    apply elem_of_region_addrs in Hin2 as Hlelt2. destruct Hlelt2 as [Hle2 Hlt2].
    assert (related_sts_a_world W (<s[i:=Uninitialized (inl 0%Z)]s> W) a0) as Hpub.
    { split;[|apply related_sts_pub_plus_refl]. simpl.
      split;[rewrite dom_insert_L;set_solver|].
      intros i0 x y Hx Hy. destruct (decide (i = i0));simplify_map_eq.
      - rewrite lookup_insert in Hy. inversion Hy. eright;[|left].
        rewrite decide_True;[|solve_addr]. right. constructor.
      - rewrite lookup_insert_ne// Hx in Hy. inversion Hy. left. }
    iSpecialize ("Hmono" $! W _ Hpub with "Hvalid").
    iDestruct (readAllowed_implies_region_conditions with "Hmono") as "Hcond'";auto.
    iDestruct (big_sepL_elem_of with "Hcond'") as (p'' Hflows') "[_ %]";eauto.
    iPureIntro.
    destruct (pwl p).
    - rewrite /region_state_pwl_mono /= lookup_insert in H1. done.
    - rewrite /region_state_nwl /= lookup_insert in H1. destruct l; try done.
      destruct H1;done.
  Qed.


  (* Useful lemma to extract the states of all the unused part of the stack *)
  Lemma state_unused_stack (i : nat) W lstk (bstk estk astk a : Addr) :
      (bstk + i ≤ astk)%Z →
      (bstk + i)%a = Some a →
      interp W (inr (URWLX, lstk, bstk, estk, astk)) -∗
      ⌜Forall (λ a0 : Addr, W.1 !! a0 = Some Monotemporary ∨ (∃ w : Word, W.1 !! a0 = Some (Uninitialized w))) (region_addrs a estk)⌝.
  Proof.
    iIntros (Hbounds Hsome) "Hvalid".
    rewrite Forall_forall. iIntros (x Hx).
    rewrite fixpoint_interp1_eq /=. destruct lstk;try done.
    iDestruct "Hvalid" as "[Hlo Hhi]".
    apply elem_of_region_addrs in Hx as Hconds. destruct Hconds as [Hle Hlt].
    destruct (decide (astk <= estk)%Z).
    - assert (addr_reg.min astk estk = astk) as ->;[solve_addr|].
      assert (addr_reg.max bstk astk = astk) as ->;[solve_addr|].
      destruct (decide (x < astk)%Z).
      + iDestruct (big_sepL_elem_of _ _ x with "Hlo") as (p Hflows) "[Hcond Hpure]".
        { apply elem_of_region_addrs. solve_addr. }
        iDestruct "Hpure" as %Hcond. auto.
      + iDestruct (big_sepL_elem_of _ _ x with "Hhi") as (p Hflows) "[Hcond Hpure]".
        { apply elem_of_region_addrs. solve_addr. }
        iDestruct "Hpure" as %Hcond. auto.
    - assert (addr_reg.min astk estk = estk) as ->;[solve_addr|].
      iDestruct (big_sepL_elem_of _ _ x with "Hlo") as (p Hflows) "[Hcond Hpure]".
      { apply elem_of_region_addrs. solve_addr. }
      iDestruct "Hpure" as %Hcond. auto.
  Qed.

  (* lemma for opening a stack object from region, which may be either a heap object or an uninitialized stack object *)
  Lemma open_stack_object_pre_mid l l' W p :
    NoDup l → l ## l' → (∀ a', a' ∈ l → (W.1 !! a' = Some Permanent ∨ (∃ w, W.1 !! a' = Some (Uninitialized w)))) →
    sts_full_world W ∗ open_region_many l' W ∗ ([∗ list] a' ∈ l, ∃ p' : Perm, ⌜PermFlows p p'⌝ ∗ read_write_cond a' p' interp) -∗
    sts_full_world W ∗ ∃ wps, ([∗ list] a;wp ∈ l;wps, a ↦ₐ[wp.2] wp.1) ∗ ▷ (([∗ list] a;wp ∈ l;wps, a ↦ₐ[wp.2] wp.1) -∗ open_region_many l' W)
                                                                       ∗ ([∗ list] a;wp ∈ l;wps, ⌜W.1 !! a = Some Permanent ∨ W.1 !! a = Some (Uninitialized wp.1)⌝)
                                                                       ∗ ⌜Forall (λ w, PermFlows p w.2) wps⌝.
  Proof.
    iIntros (Hdup Hdisj Hcond) "[Hsts [Hr #Hrels] ]".
    iInduction l as [|x l] "IH" forall (l' Hdisj).
    - iFrame. iExists []. auto.
    - apply NoDup_cons in Hdup as [Hnin Hdup].
      apply disjoint_cons in Hdisj as Hnin'.
      apply disjoint_swap in Hdisj;auto.
      iSimpl in "Hrels". iDestruct "Hrels" as "[Hx Hrels]".
      iDestruct "Hx" as (p' Hflows) "Hrel".
      destruct Hcond with x as [Hperm | [w Huninit] ];[constructor|..].
      + iDestruct (region_open_next_perm with "[$Hrel $Hsts $Hr]") as (v) "(Hsts & Hstate & Hr & Hx & % & #Hmono & #Hvalid)";auto.
        iDestruct ("IH" with "[] [] [] Hrels Hsts Hr") as "[Hsts Hws]";auto.
        { iPureIntro. intros a Ha. apply Hcond. constructor. auto. }
        iFrame. iDestruct "Hws" as (wps) "(Hws & Hcls & Hcond & %)". iExists ((v,p') :: wps).
        iFrame. iSplit;auto. iNext.
        iIntros "[Hx Hxs]". simpl.
        iDestruct ("Hcls" with "Hxs") as "Hr".
        iDestruct (region_close_next_perm with "[$Hstate $Hr $Hx]") as "Hr";auto. apply _.
      + iDestruct (region_open_next_monouninit_w with "[$Hrel $Hsts $Hr]") as "(Hr & Hsts & Hstate & Hx & %)";eauto.
        iDestruct ("IH" with "[] [] [] Hrels Hsts Hr") as "[Hsts Hws]";auto.
        { iPureIntro. intros a Ha. apply Hcond. constructor. auto. }
        iFrame. iDestruct "Hws" as (wps) "(Hws & Hcls & Hcond & %)". iExists ((w,p') :: wps).
        iFrame. iSplit;auto. iNext.
        iIntros "[Hx Hxs]". simpl.
        iDestruct ("Hcls" with "Hxs") as "Hr".
        iDestruct (region_close_next_uninit with "[$Hstate $Hr $Hx]") as "Hr";auto. apply _.
  Qed.

  Lemma open_stack_object_pre l W p :
    NoDup l → (∀ a', a' ∈ l → (W.1 !! a' = Some Permanent ∨ (∃ w, W.1 !! a' = Some (Uninitialized w)))) →
    sts_full_world W ∗ region W ∗ ([∗ list] a' ∈ l, ∃ p' : Perm, ⌜PermFlows p p'⌝ ∗ read_write_cond a' p' interp) -∗
    sts_full_world W ∗ ∃ wps, ([∗ list] a;wp ∈ l;wps, a ↦ₐ[wp.2] wp.1) ∗ ▷ (([∗ list] a;wp ∈ l;wps, a ↦ₐ[wp.2] wp.1) -∗ region W)
                                                                       ∗ ([∗ list] a;wp ∈ l;wps, ⌜W.1 !! a = Some Permanent ∨ W.1 !! a = Some (Uninitialized wp.1)⌝)
                                                                       ∗ ⌜Forall (λ w, PermFlows p w.2) wps⌝.
  Proof.
    iIntros (Hdup Hcond) "[Hsts [Hr #Hrels] ]".
    iDestruct (region_open_nil with "Hr") as "Hr".
    iDestruct (open_stack_object_pre_mid with "[$Hsts $Hr]") as "[Hsts Hws]";eauto. apply disjoint_nil_r. exact (addr_reg.top). (*??*)
    iFrame. iDestruct "Hws" as (ws) "(?&HH&?)". iExists ws. iFrame. iNext. iIntros "H".
    iApply region_open_nil. iApply "HH". iFrame.
  Qed.

  Lemma open_stack_object W p b e :
    (∀ a', (b <= a' < e)%a → (W.1 !! a' = Some Permanent ∨ (∃ w, W.1 !! a' = Some (Uninitialized w)))) →
    sts_full_world W ∗ region W ∗ ([∗ list] a' ∈ (region_addrs b e), ∃ p' : Perm, ⌜PermFlows p p'⌝ ∗ read_write_cond a' p' interp) -∗
    sts_full_world W ∗ ∃ wps, ([∗ list] a;wp ∈ (region_addrs b e);wps, a ↦ₐ[wp.2] wp.1) ∗ ▷ (([∗ list] a;wp ∈ (region_addrs b e);wps, a ↦ₐ[wp.2] wp.1) -∗ region W)
                                 ∗ ⌜Forall (λ awp, W.1 !! awp.1 = Some Permanent ∨ W.1 !! awp.1 = Some (Uninitialized awp.2.1)) (zip (region_addrs b e) wps)⌝
                                 ∗ ⌜Forall (λ w, PermFlows p w.2) wps⌝.
  Proof.
    iIntros (Hcond) "[Hsts [Hr #Hrels] ]".
    iDestruct (open_stack_object_pre with "[$Hsts $Hr $Hrels]") as "[Hsts Hws]".
    apply region_addrs_NoDup.
    intros a' Hin. apply Hcond. apply elem_of_region_addrs. auto.
    iFrame. iDestruct "Hws" as (wps) "(Hws & Hcls & Hcond & %)". iExists _. iFrame. iSplit;auto.
    iDestruct (big_sepL2_alt with "Hcond") as "[% Hcond]".
    iDestruct (big_sepL_forall with "Hcond") as %Hforall. iPureIntro.
    apply Forall_forall. intros x [k Hx]%elem_of_list_lookup. eapply Hforall. eauto.
  Qed.

  Lemma uninitialize_revoke_condition W m :
    (∀ a' : Addr, is_Some (m !! a') ↔ std W !! a' = Some Monotemporary ∧ (0 <= a')%a) →
    revoke_condition (uninitialize W m).
  Proof.
    intros Hforall. intros a.
    destruct (m !! a) eqn:Hsome.
    - assert (is_Some (m !! a)) as HisSome;[eauto|]. apply Hforall in HisSome as [Hmono _].
      eapply uninitialize_std_sta_lookup_in in Hsome;eauto. rewrite Hsome. auto.
    - apply uninitialize_std_sta_None_lookup with (m:=W.1) in Hsome as Heq. rewrite Heq.
      intros Hcontr. assert (is_Some (m !! a)) as [? HisSome];[|congruence].
      apply Hforall. split;auto. solve_addr.
  Qed.

End stack_object.
