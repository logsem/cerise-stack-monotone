From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel fundamental region_invariants_batch_uninitialized.
From cap_machine Require Export iris_extra addr_reg_sample region_macros contiguous stack_macros_helpers macros.

Section lse.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          `{MonRef: MonRefG (leibnizO _) CapR_rtc Σ} {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.


  Definition lse_instrs f_a :=
    prepstackU_instrs r_stk 1 ++
    checkbelow_instrs r_t0 r_stk ++
    [pushU_r_instr r_stk r_env;
    load_r r_env r_env] ++
    assert_r_z_instrs f_a r_env 2 ++
    rclear_instrs (list_difference all_registers [PC;r_t0]) ++
    [jmp r_t0].

  Definition lse a p f_a :=
    ([∗ list] a_i;w_i ∈ a;(lse_instrs f_a), a_i ↦ₐ[p] w_i)%I.

  Definition lse_inv d : iProp Σ := d ↦ₐ[RWX] inl 2%Z.


  Lemma lse_spec W pc_p pc_p' pc_g pc_b pc_e (* PC *)
        wret (* return cap *)
        lse_addrs (* program addresses *)
        d d' (* dynamically allocated memory given by preamble, connected to invariant i *)
        a_first a_last (* special adresses *)
        f_a b_link e_link a_link a_entry fail_cap (* linking table variables *)
        wstk (* stack *)
        rmap (* registers *)
        ι1 ι2 (* invariant names *) :

    (* PC assumptions *)
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last ->
    PermFlows pc_p pc_p' ->

    (* Program adresses assumptions *)
    contiguous_between lse_addrs a_first a_last ->

    (* Linking table assumptions *)
    withinBounds (RW, Global, b_link, e_link, a_entry) = true →
    (a_link + f_a)%a = Some a_entry ->

    (* malloc'ed memory assumption *)
    (d + 1)%a = Some d' ->

    (* footprint of the register map *)
    dom (gset RegName) rmap = all_registers_s ∖ {[PC;r_stk;r_t0;r_env]} →

    (* The two invariants have different names *)
    (up_close (B:=coPset) ι2 ## ↑ι1) ->

    {{{ r_stk ↦ᵣ wstk
      ∗ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,a_first)
      ∗ r_t0 ↦ᵣ wret
      ∗ r_env ↦ᵣ inr (RWX,Global,d,d',d)
      ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
      (* invariant for d *)
      ∗ (∃ ι, inv ι (lse_inv d))
      (* stack *)
      ∗ interp W wstk
      (* token which states all non atomic invariants are closed *)
      ∗ na_own logrel_nais ⊤
      (* callback validity *)
      ∗ interp W wret
      (* trusted code *)
      ∗ na_inv logrel_nais ι1 (lse lse_addrs pc_p' f_a)
      (* linking table *)
      ∗ na_inv logrel_nais ι2 (pc_b ↦ₐ[pc_p'] inr (RO,Global,b_link,e_link,a_link) ∗ a_entry ↦ₐ[RO] fail_cap)
      (* we start out with arbitrary sts *)
      ∗ sts_full_world W
      ∗ region W
    }}}
      Seq (Instr Executable)
      {{{ v, RET v; ⌜v = HaltedV⌝ →
                    ∃ r W', full_map r ∧ registers_mapsto r
                         ∗ ⌜related_sts_priv_world W W'⌝
                         ∗ na_own logrel_nais ⊤
                         ∗ sts_full_world W'
                         ∗ region W' }}}.
  Proof.
    iIntros (Hvpc Hfl Hcont Hlt_wb Hlt_link Hdoff Hdom Hndisj φ).
    iIntros "(Hr_stk & HPC & Hr_t0 & Hr_env & Hregs & #Hdinv & #Hwstk_valid & Hown & #Hwret_valid & #Hlse_prog & #Htable & Hsts & Hr) Hφ".
    iMod (na_inv_acc with "Hlse_prog Hown") as "(>Hprog & Hown & Hcls)";auto.
    (* get some general purpose registers *)
    assert (is_Some (rmap !! r_t1)) as [w1 Hw1];[apply elem_of_gmap_dom;rewrite Hdom;set_solver+|].
    assert (is_Some (rmap !! r_t2)) as [w2 Hw2];[apply elem_of_gmap_dom;rewrite Hdom;set_solver+|].
    assert (is_Some (rmap !! r_t3)) as [w3 Hw3];[apply elem_of_gmap_dom;rewrite Hdom;set_solver+|].
    assert (is_Some (rmap !! r_t4)) as [w4 Hw4];[apply elem_of_gmap_dom;rewrite Hdom;set_solver+|].
    iDestruct (big_sepM_delete with "Hregs") as "[Hr_t1 Hregs]";[apply Hw1|].
    iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr_t2 Hregs]";[rewrite lookup_delete_ne//;eauto|].
    iDestruct (big_sepM_delete _ _ r_t3 with "Hregs") as "[Hr_t3 Hregs]";[rewrite !lookup_delete_ne//;eauto|].
    iDestruct (big_sepM_delete _ _ r_t4 with "Hregs") as "[Hr_t4 Hregs]";[rewrite !lookup_delete_ne//;eauto|].
    (* prepstack *)
    iPrologue_multi "Hprog" Hcont Hvpc link.
    iApply (prepstackU_spec with "[- $HPC $Hcode $Hr_stk]");[eauto..|].
    iSplitL "Hr_t1";[eauto|]. iSplitL "Hr_t2";[eauto|].
    iNext. destruct (isPermWord wstk URWLX) eqn:Hperm;[|(* Failure *) iApply "Hφ";iIntros (Hcontr);inversion Hcontr].
    (* cleanup of stack information *)
    destruct wstk as [| [ [ [ [p_stk l_stk] b_stk] e_stk] a_stk] ];[inversion Hperm|]. iExists l_stk,b_stk, e_stk, a_stk.
    destruct p_stk;inversion Hperm. iSplit;auto.
    destruct (1 <? e_stk - b_stk)%Z eqn:Hsize;[|(* Failure *) iApply "Hφ";iIntros (Hcontr);inversion Hcontr].
    destruct (b_stk <=? a_stk)%Z eqn:Hle;[|(* Failure *) iApply "Hφ";iIntros (Hcontr);inversion Hcontr].
    iDestruct (writeLocalAllowedU_implies_local with "Hwstk_valid") as %Hmonotone;auto. destruct l_stk;inversion Hmonotone.
    iIntros "(HPC & Hprepstack & Hr_stk & Hr_t1 & Hr_t2)".
    (* checkbelow *)
    iPrologue_multi "Hprog" Hcont Hvpc link0.
    iApply (checkbelow_spec with "[- $HPC $Hcode $Hr_stk $Hr_t0]");[eauto..|].
    iSplitL "Hr_t1";[eauto|]. iSplitL "Hr_t2";[eauto|]. iSplitL "Hr_t3";[eauto|]. iSplitL "Hr_t4";[eauto|].
    iNext.
    destruct (is_cap wret && (canReadUpTo wret <? b_stk)%a && negb (isO_word wret)) eqn:Hbelowcond;
      [|(* Failure *) iApply "Hφ";iIntros (Hcontr);inversion Hcontr].
    iIntros "(HPC & Hcheckbelow & Hr_t0 & Hr_stk & Hr_t1 & Hr_t2 & Hr_t3 & Hr_t4)".

    (* pushu r_stk r_env *)
    (* we have reached a part of the code which will require us to make a pub^b_stk change to the world *)
    (* we will therefore first uninitialize all addresses at or above b_stk *)
    iMod (uninitialize_region _ b_stk with "[$Hsts $Hr]") as (m Hmcond) "[Hsts Hr]".
    (* next we can open the region at b_stk, which we will first assert is in m *)
    iDestruct (valid_uninitialized_condition _ m with "Hwstk_valid") as %Hstk_cond;auto.
    (* next we can open the world at b_stk *)
    assert (b_stk <= b_stk < e_stk)%a as Hstk_bounds.
    { split;[clear;solve_addr|]. clear -Hsize. apply Z.ltb_lt in Hsize. lia. }
    pose proof (Hstk_cond b_stk Hstk_bounds) as [w Hw].
    iAssert (rel b_stk RWLX (λ Wv, interp Wv.1 Wv.2)) as "#Hrel".
    { rewrite fixpoint_interp1_eq /=. destruct (decide (b_stk < a_stk))%a.
      - iDestruct "Hwstk_valid" as "[Hv _]".
        iDestruct (big_sepL_elem_of _ _ b_stk with "Hv") as (p Hflp) "[Hrel _]".
        { apply elem_of_region_addrs. clear -Hstk_bounds l. solve_addr. }
        destruct p;inversion Hflp. iFrame "Hrel".
      - iDestruct "Hwstk_valid" as "[_ Hv]".
        iDestruct (big_sepL_elem_of _ _ b_stk with "Hv") as (p Hflp) "[Hrel _]".
        { apply elem_of_region_addrs. clear -Hstk_bounds n. solve_addr. }
        destruct p;inversion Hflp. iFrame "Hrel". }
    iDestruct (region_open_uninitialized with "[$Hrel $Hr $Hsts]") as "(Hr & Hsts & Hstate & Hb_stk & %)";[eauto|..].
    (* and we are ready to push a new value b_stk *)
    assert (is_Some (b_stk + 1))%a as [b_stk1 Hb_next].
    { clear -Hstk_bounds. destruct (b_stk + 1)%a eqn:Hsome;eauto. exfalso. solve_addr. }
    iPrologue_multi "Hprog" Hcont Hvpc link1.
    iDestruct (big_sepL2_length with "Hcode") as %Hlength_code1.
    prep_addr_list_full l_code1 Hcont_code1.
    iDestruct "Hcode" as "[HpushU Hcode]".
    iApply (pushU_r_spec with "[- $HPC $HpushU $Hr_stk $Hr_env $Hb_stk]");
      [iCorrectPC link0 link1|auto|auto| |iContiguous_next_a Hcont_code1|apply Hb_next|..].
    { apply andb_true_iff. split;[apply Z.leb_le|apply Z.ltb_lt];clear -Hstk_bounds;solve_addr. }
    { intros Hcontr;inversion Hcontr. }
    iNext. iIntros "(HPC & HpushU & Hr_stk & Hr_env & Hb_stk)".
    (* we can now close the world again *)
    pose proof (uninitialized_condition _ _ _ Hmcond) as Hmcond_alt.
    iMod (uninitialize_open_region_change _ _ b_stk with "[$Hb_stk $Hrel $Hsts $Hr $Hstate]") as "[Hr Hsts]";
      [clear;solve_addr|auto|auto|].

    (* and we can now finish executing the instructions without more changes to W *)
    iPrologue "Hcode".
    iDestruct "Hdinv" as (ι) "Hdinv". iInv ι as ">Hd" "Hcls'". rewrite /lse_inv.
    iAssert (⌜(d =? a)%a = false⌝)%I as %Heq_false.
    { rewrite Z.eqb_neq. iIntros (->%z_of_eq). iDestruct (address_dupl_false with "Hi Hd") as "Hbot";[auto..|done].
      eapply pc_range_nonO in Hcont_code1;[|eauto]. destruct pc_p',pc_p;auto;inversion Hfl;auto. }
    iApply (wp_load_success_same with "[$HPC $Hi $Hr_env Hd]");
      [auto|apply decode_encode_instrW_inv|apply Hfl|iCorrectPC link0 link1|..].
    { clear -Hdoff. split;auto. apply andb_true_iff. split;[apply Z.leb_le|apply Z.ltb_lt];solve_addr. }
    { eapply contiguous_between_last. apply Hcont_code1. auto. }
    { rewrite Heq_false. iFrame. auto. }
    rewrite Heq_false.
    iNext. iIntros "(HPC & Hr_env & Hprog_done & Hd)".
    iMod ("Hcls'" with "[$Hd]") as "_".
    iModIntro. iApply wp_pure_step_later;auto. iNext.
    iClear "Hcode".

    (* assert r_env 2 *)
    iPrologue_multi "Hprog" Hcont Hvpc link2.
    iMod (na_inv_acc with "Htable Hown") as "(>[Hpc_b Ha_entry] & Hown & Hcls'')";[auto|solve_ndisj|].
    iApply (assert_r_z_success with "[- $HPC $Hcode $Hr_env $Hpc_b $Ha_entry]");
      [apply Hvpc_code2|apply Hfl|apply Hcont_code2|auto..|].
    iSplitL "Hr_t1";[eauto|]. iSplitL "Hr_t2";[eauto|]. iSplitL "Hr_t3";[eauto|].
    iNext. iIntros "(Hr_t1 & Hr_t2 & Hr_t3 & Hr_env & HPC & Hassert & Hpc_b & Ha_entry)".
    iMod ("Hcls''" with "[$Hown $Hpc_b $Ha_entry]") as "Hown".

    (* rclear RegName/{PC;r_t0} *)
    iPrologue_multi "Hprog" Hcont Hvpc link3.
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t4]") as "Hregs";[apply lookup_delete|rewrite insert_delete -!delete_insert_ne//].
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t3]") as "Hregs";[apply lookup_delete|rewrite insert_delete -!delete_insert_ne//].
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t2]") as "Hregs";[apply lookup_delete|rewrite insert_delete -!delete_insert_ne//].
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t1]") as "Hregs";[apply lookup_delete|rewrite insert_delete].
    iDestruct (big_sepM_insert with "[$Hregs $Hr_stk]") as "Hregs".
    { rewrite !lookup_insert_ne//. apply not_elem_of_dom. rewrite Hdom. set_solver-. }
    iDestruct (big_sepM_insert with "[$Hregs $Hr_env]") as "Hregs".
    { rewrite !lookup_insert_ne//. apply not_elem_of_dom. rewrite Hdom. set_solver-. }
    iApply (rclear_spec_gmap with "[- $HPC $Hcode $Hregs]");[eauto..|].
    { apply not_elem_of_list. constructor. }
    { assert (length l_code2 = 31) as Hlength4. clear -Hlength2 Hlength3. rewrite app_length Hlength3 in Hlength2. lia.
      destruct l_code2;inversion Hlength4. apply contiguous_between_cons_inv_first in Hcont_code3 as ->. auto. }
    { clear -Hdom. rewrite !dom_insert_L Hdom list_to_set_difference -/all_registers_s /=. clear. set_solver. }
    iNext. iIntros "[HPC [Hdom Hrclear]]".
    iDestruct "Hdom" as (rmap') "[Hregs #Hregs_cond]". iDestruct "Hregs_cond" as %[Hdom' Hzeroes].

    (* jmp r_t0 *)
    prep_addr_list_full l_rest3 Hcont.
    iPrologue "Hprog".
    iApply (wp_jmp_success with "[$HPC $Hi $Hr_t0]");
      [apply decode_encode_instrW_inv|apply Hfl|iCorrectPC link3 a_last|].

    (* first we will update the varilidy of wret to the new world *)
    (* this will be possible because we made sure its reading bound is below b_stk *)
    set (W' := (<s[b_stk:=Uninitialized (inr (RWX, Global, d, d', d))]s>(uninitialize W m))).
    apply andb_true_iff in Hbelowcond as [ [His_cap Hlt%Z.ltb_lt]%andb_true_iff HnotO].
    assert (related_sts_a_world W W' b_stk) as Hrelated.
    { eapply related_sts_a_trans_world;[apply uninitialize_related_pub_a|];eauto.
      apply related_sts_a_uninitialized. clear -Hmcond Hmcond_alt His_cap Hlt HnotO Hw. solve_addr. eauto. }
    iDestruct (interp_monotone_a _ W' with "[] Hwret_valid") as "Hwret_valid'".
    { iPureIntro. clear -Hmcond Hmcond_alt His_cap Hlt HnotO Hw Hrelated. eapply related_sts_a_weak_world with b_stk;auto.
      destruct wret;inversion His_cap. destruct c,p,p,p. simpl in *.
      destruct (isU p) eqn:HU;destruct p;inversion Hlt;solve_addr. }
    destruct wret;inversion His_cap. destruct c as [ [ [ [p g]b]e]a'].
    iAssert (▷ interp_expression (<[PC:=inl 0%Z]> (<[r_t0:=inr (p, g, b, e, a')]> rmap')) W' (updatePcPerm (inr (p,g,b,e,a'))))%I as "Hcont".
    { destruct (decide (p = E)).
      - subst. iClear "Hwstk_valid Hwret_valid". rewrite fixpoint_interp1_eq. iSimpl in "Hwret_valid'".
        rewrite /enter_cond. iApply "Hwret_valid'". destruct g;iPureIntro.
        apply related_sts_priv_refl_world. apply related_sts_pub_plus_refl_world. apply related_sts_a_refl_world.
      - iDestruct (fundamental_from_interp (<[PC:=inl 0%Z]> (<[r_t0:=inr (p,g,b,e,a')]> rmap')) with "Hwret_valid'") as "Hcont". iNext.
        rewrite updatePcPerm_cap_non_E//. }

    (* we can now establish the continuation *)
    iEpilogue "(HPC & Hi & Hr_t0)".

    (* first we will close the program invariant *)
    iMod ("Hcls" with "[Hprepstack Hcheckbelow HpushU Hprog_done Hassert Hrclear Hi $Hown]") as "Hown".
    { iNext. iFrame. simpl. done. }

    (* next we must establish that the current register state is valid *)
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t0]") as "Hregs".
    { apply not_elem_of_dom. rewrite Hdom'. set_solver-. }
    iDestruct (big_sepM_insert with "[$Hregs $HPC]") as "Hregs".
    { rewrite lookup_insert_ne//. apply not_elem_of_dom. rewrite Hdom'. set_solver-. }
    iDestruct ("Hcont" with "[$Hown $Hr $Hsts Hregs]") as "[_ Hconf]".
    { rewrite insert_insert. iFrame "Hregs". iSplit;[iPureIntro|].
      - simpl. intros x. apply elem_of_gmap_dom. rewrite !dom_insert_L Hdom' list_to_set_difference. clear.
        pose proof (all_registers_s_correct x). set_solver.
      - iIntros (r HPC). rewrite /RegLocate. rewrite lookup_insert_ne//.
        destruct (decide (r_t0 = r));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
        rewrite Hzeroes. rewrite !fixpoint_interp1_eq. done.
        rewrite Hdom'. clear -HPC n. pose proof (all_registers_s_correct r).
        rewrite list_to_set_difference. set_solver. }
    iApply (wp_wand with "Hconf").
    iIntros (v). iIntros "Hcond". iApply "Hφ".
    iIntros (Hhalted). iDestruct ("Hcond" $! Hhalted) as (r W'') "(?&?&%&?&?&?)".
    iExists _,_;iFrame.
    iPureIntro. eapply related_sts_a_priv_trans_world;eauto.
  Qed.

End lse.
