From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules rules_LoadU_derived logrel fundamental region_invariants_revocation region_invariants_static region_invariants_batch_uninitialized stack_object_helpers.
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

  Definition r_adv := r_t29.
  Definition r_param1 := r_t16.
  Definition r_param2 := r_t17.

  Definition stack_object_passing_instrs stack_obj f_a :=
    (* we check that the function pointer is global *)
    reqglob_instrs r_adv ++
    (* prepare the stack *)
    prepstackU_instrs r_stk 12 2 ++
    (* load parameter 1 into register *)
    [loadU_r_z r_param1 r_stk (-1)] ++
    (* we must do some dynamic checks on the input object, which can be a stack object *)
    checkra_instrs r_param1 ++
    checkints_instrs r_param1 r_t1 r_t2 r_t3 ++
    (* we can begin the function *)
    (* push some local state *)
    [pushU_z_instr r_stk 2;
    (* we create a stack object *)
    pushU_z_instr r_stk stack_obj;
    move_r r_param2 r_stk;
    getb r_t1 r_stk;
    gete r_t2 r_stk;
    add_r_z r_t1 r_t1 3;
    subseg_r_r r_param2 r_t1 r_t2;
    promoteU r_param2] ++
    (* call r_adv *)
    scallU_prologue_instrs r_adv [r_param1;r_param2] ++
    (* we push the parameters onto the new restricted adversary stack *)
    [pushU_r_instr r_stk r_param1;
    pushU_r_instr r_stk r_param2;
    pushU_r_instr r_stk r_t0;
    move_z r_param1 0; (* these three cleanup steps are not necessary, but practical *)
    move_z r_param2 0;
    move_z r_t0 0;
    (* jump to the ardversary callee *)
    jmp r_adv;
    (* restore local state *)
    lea_z r_stk (-6)] ++
    (* we assert that the local state is still 2. If the return pointer has been leaked,
       then the caller can alter the local state, jump to the return pointer and make
       the following assertion fail *)
    [loadU_r_z r_t1 r_stk (-2)] ++
    assert_r_z_instrs f_a r_t1 2 ++
    [loadU_r_z r_t0 r_stk (-4)] ++
    (* we leave everything on the stack, but clear registers before returning *)
    rclear_instrs (list_difference all_registers [PC;r_t0]) ++
    [jmp r_t0].

  Definition stack_object_passing a p stack_obj f_a :=
    ([∗ list] a_i;w_i ∈ a;(stack_object_passing_instrs stack_obj f_a), a_i ↦ₐ[p] w_i)%I.


  Lemma stack_object_spec W pc_p pc_p' pc_g pc_b pc_e (* PC *)
        stack_object_passing_addrs (* program addresses *)
        a_first a_last (* special adresses *)
        f_a b_link e_link a_link a_entry fail_cap (* linking table variables *)
        stack_obj advw (* input *)
        wstk (* stack *)
        rmap (* registers *)
        ι1 ι2 (* invariant names *) :

    (* PC assumptions *)
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last ->
    PermFlows pc_p pc_p' ->

    (* Program adresses assumptions *)
    contiguous_between stack_object_passing_addrs a_first a_last ->

    (* Linking table assumptions *)
    withinBounds (RW, Global, b_link, e_link, a_entry) = true →
    (a_link + f_a)%a = Some a_entry ->

    (* the monotonicity of the PC is not monotone *)
    isMonotone pc_g = false →

    (* footprint of the register map *)
    dom (gset RegName) rmap = all_registers_s ∖ {[PC;r_stk;r_adv]} →

    (* The two invariants have different names *)
    (up_close (B:=coPset) ι2 ## ↑ι1) ->

    {{{ r_stk ↦ᵣ wstk
      ∗ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,a_first)
      ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
      (* adv *)
      ∗ r_adv ↦ᵣ advw
      ∗ interp W advw
      (* stack *)
      ∗ interp W wstk
      (* token which states all non atomic invariants are closed *)
      ∗ na_own logrel_nais ⊤
      (* trusted code *)
      ∗ na_inv logrel_nais ι1 (stack_object_passing stack_object_passing_addrs pc_p' stack_obj f_a)
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
    iIntros (Hvpc Hfl Hcont Hlt_wb Hlt_link Hpcmono Hdom Hndisj φ).
    iIntros "(Hr_stk & HPC & Hregs & Hr_adv & #Hadv_valid & #Hwstk_valid & Hown & #Hlse_prog & #Htable & Hsts & Hr) Hφ".
    iMod (na_inv_acc with "Hlse_prog Hown") as "(>Hprog & Hown & Hcls)";auto.

    (* get some general purpose registers *)
    assert (is_Some (rmap !! r_t0)) as [w0 Hw0];[apply elem_of_gmap_dom;rewrite Hdom;set_solver+|].
    assert (is_Some (rmap !! r_t1)) as [w1 Hw1];[apply elem_of_gmap_dom;rewrite Hdom;set_solver+|].
    assert (is_Some (rmap !! r_t2)) as [w2 Hw2];[apply elem_of_gmap_dom;rewrite Hdom;set_solver+|].
    assert (is_Some (rmap !! r_t3)) as [w3 Hw3];[apply elem_of_gmap_dom;rewrite Hdom;set_solver+|].
    assert (is_Some (rmap !! r_t4)) as [w4 Hw4];[apply elem_of_gmap_dom;rewrite Hdom;set_solver+|].
    assert (is_Some (rmap !! r_param1)) as [wp1 Hwp1];[apply elem_of_gmap_dom;rewrite Hdom;set_solver+|].
    assert (is_Some (rmap !! r_param2)) as [wp2 Hwp2];[apply elem_of_gmap_dom;rewrite Hdom;set_solver+|].
    iDestruct (big_sepM_delete with "Hregs") as "[Hr_t0 Hregs]";[apply Hw0|].
    iDestruct (big_sepM_delete _ _ r_t1 with "Hregs") as "[Hr_t1 Hregs]";[rewrite lookup_delete_ne//;eauto|].
    iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr_t2 Hregs]";[rewrite !lookup_delete_ne//;eauto|].
    iDestruct (big_sepM_delete _ _ r_t3 with "Hregs") as "[Hr_t3 Hregs]";[rewrite !lookup_delete_ne//;eauto|].
    iDestruct (big_sepM_delete _ _ r_t4 with "Hregs") as "[Hr_t4 Hregs]";[rewrite !lookup_delete_ne//;eauto|].
    iDestruct (big_sepM_delete _ _ r_param1 with "Hregs") as "[Hr_param1 Hregs]";[rewrite !lookup_delete_ne//;eauto|].
    iDestruct (big_sepM_delete _ _ r_param2 with "Hregs") as "[Hr_param2 Hregs]";[rewrite !lookup_delete_ne//;eauto|].

    (* reqglob  *)
    iPrologue_multi "Hprog" Hcont Hvpc link.
    iApply (reqglob_spec with "[- $HPC $Hcode $Hr_adv]");[eauto..|].
    iSplitL "Hr_t1";[eauto|]. iSplitL "Hr_t2";[eauto|].
    iNext. destruct (isGlobalWord advw) eqn:Hglob;[|(* Failure *) iApply "Hφ";iIntros (Hcontr);inversion Hcontr].
    destruct advw as [c | [ [ [ [g l] b] e] a'] ];[inversion Hglob|]. destruct l;[|inversion Hglob..].
    iExists _,_,_,_. iSplit;[eauto|].
    iIntros "(HPC & Hreqglob & Hr_adv & Hr_t1 & Hr_t2)".

    (* prepstack *)
    iPrologue_multi "Hprog" Hcont Hvpc link0.
    iApply (prepstackU_spec with "[- $HPC $Hcode $Hr_stk]");[eauto..|].
    iSplitL "Hr_t1";[eauto|]. iSplitL "Hr_t2";[eauto|].
    iNext. destruct (isPermWord wstk URWLX) eqn:Hperm;[|(* Failure *) iApply "Hφ";iIntros (Hcontr);inversion Hcontr].
    destruct wstk as [c | [ [ [ [gstk lstk] bstk] estk] astk] ];[inversion Hperm|]. destruct gstk;inversion Hperm.
    iExists _,_,_,_. iSplit;[eauto|].
    destruct ((12%nat + 2%nat <? estk - bstk)%Z) eqn:Hsize;[|(* Failure *) iApply "Hφ";iIntros (Hcontr);inversion Hcontr].
    destruct ((bstk + 2%nat <=? astk)%Z) eqn:Hbounds;[|(* Failure *) iApply "Hφ";iIntros (Hcontr);inversion Hcontr].
    iIntros "Hcont". iDestruct "Hcont" as (a_param Ha_param) "(HPC & HprepstackU & Hr_stk & Hr_t1 & Hr_t2)".
    apply Z.ltb_lt in Hsize. apply Z.leb_le in Hbounds.

    (* we can extract the validity of the parameters passed on the stack *)
    iDestruct (read_allowedU_inv _ bstk with "Hwstk_valid") as (p' Hflows) "Hcond1";[clear -Hbounds Hsize Ha_param;solve_addr|auto|].
    iDestruct (writeLocalAllowedU_valid_cap_below_implies _ _ _ _ _ _ bstk with "Hwstk_valid") as %Hmono1;
      [auto|apply le_addr_withinBounds|..];[clear -Hbounds Hsize Ha_param;solve_addr..|].
    destruct p';inversion Hflows;clear Hflows.

    destruct (bstk + 1)%a eqn:Hsome;[|exfalso;clear -Ha_param Hsome;solve_addr].
    iDestruct (read_allowedU_inv _ a with "Hwstk_valid") as (p' Hflows) "Hcond2";[clear -Hbounds Hsize Hsome;solve_addr|auto|].
    iDestruct (writeLocalAllowedU_valid_cap_below_implies _ _ _ _ _ _ a with "Hwstk_valid") as %Hmono2;
      [auto|apply le_addr_withinBounds|..];[clear -Hbounds Hsize Hsome;solve_addr..|].
    destruct p';inversion Hflows;clear Hflows.

    (* loadU r_param1 r_stk -1 *)
    iPrologue_multi "Hprog" Hcont Hvpc link1.
    iDestruct (big_sepL2_length with "Hcode") as %Hprog_length.
    destruct_addr_list l_code1.
    iDestruct (region_open_monotemp_pwl with "[$Hcond2 $Hr $Hsts]") as
        (wsecret) "(Hr & Hsts & Hstate & Ha & % & #Hmono & #Hwsecret_valid)";[auto..|].
    iPrologue "Hcode". apply contiguous_between_cons_inv_first in Hcont_code1 as Heq. subst l_code1.
    iApply (wp_loadU_success with "[$HPC $Hi $Hr_param1 $Hr_stk $Ha]");
      [apply decode_encode_instrW_inv|apply Hfl|auto|iCorrectPC link0 link1|auto..].
    { clear -Hsome Ha_param Hbounds Hsize. apply le_addr_withinBounds;solve_addr. }
    { apply Hlink1. }
    { clear -Hsome Ha_param Hbounds Hsize. solve_addr. }
    iEpilogue "(HPC & Hr_param1 & Hprog_done & Hr_stk & Ha)".
    iDestruct (region_close_monotemp_pwl with "[$Hstate $Hr $Ha $Hcond2]") as "Hr";auto. iClear "Hcode".

    (* check the passed object is RA *)
    iPrologue_multi "Hprog" Hcont Hvpc link2.
    iApply (checkra_spec with "[- $HPC $Hcode $Hr_param1 $Hr_t1 $Hr_t2 $Hr_t3 $Hr_t4]");[eauto..|].
    iNext. destruct (is_cap wsecret) eqn:Hiscap;[|(* Failure *) iApply "Hφ";iIntros (Hcontr);inversion Hcontr].
    destruct wsecret as [c | [ [ [ [l p] bsec] esec] asec] ];[inversion Hiscap|].
    iExists _,_,_,_,_;iSplit;[eauto|].
    destruct (readAllowed l) eqn:Hra;[|(* Failure *) iApply "Hφ";iIntros (Hcontr);inversion Hcontr].
    iIntros "(HPC & Hcheckra & Hr_param1 & Hr_t1 & Hr_t2 & Hr_t3 & Hr_t4)".

    (* we must now dynamically check that the object in param1 is of the correct type *)
    (* we must therefore extract the object from W *)
    (* we will thereafter need to freeze the full world, before reinstating the object after the check *)

    (* extract region information of [bsec,esec] from W *)
    iDestruct (state_unused_stack with "Hwstk_valid") as %Hstack_state;[apply Hbounds|apply Ha_param|].
    iDestruct (input_stack_disjoint _ _ a_param estk with "[$Hwsecret_valid $Hmono]") as %Hdisj;
      [clear -Hbounds Hsize Hsome Ha_param;solve_addr|auto|auto|].
    iDestruct (readAllowed_implies_region_conditions with "Hwsecret_valid") as "Hsecret_cond";auto.

    (* uninitialize the full stack *)
    iMod (uninitialize_region_keep _ addr_reg.za with "[$Hsts $Hr]") as (m Hmcond) "[Hsts [Hr #Hvalids] ]".
    (* next we can open the region at b_stk, which we will first assert is in m *)
    iDestruct (valid_uninitialized_condition_weak _ m with "Hwstk_valid") as %Hstk_cond;eauto. clear. solve_addr.
    iSimpl in "Hwsecret_valid". iDestruct (valid_readAllowed_condition_weak _ m with "Hwsecret_valid") as %Hsec_cond;eauto. clear. solve_addr.

    (* opening [bsec,esec] while remembering the words in case of uninitialized state in (uninit m W) *)
    iDestruct (open_stack_object with "[$Hsts $Hr]") as "(Hsts & Hws)";eauto.
    { iApply big_sepL_forall. iIntros (k x Hx).
      assert (x ∈ region_addrs bsec esec) as Hinx;[apply elem_of_list_lookup;eauto|].
      iApply read_allowed_inv. apply elem_of_region_addrs in Hinx. eauto. eauto.
      iFrame "Hwsecret_valid". }
    iDestruct "Hws" as (wps) "(Hbesec & Hcls' & #Hsecret_states & #Hperms)".
    iDestruct "Hsecret_states" as %Hsecret_states. iDestruct "Hperms" as %Hperm_flows.

    (* Now we are ready to apply the checkints macro *)
    iPrologue_multi "Hprog" Hcont Hvpc link3.
    iApply (wp_wand with "[- Hφ]").
    2: { iIntros (v) "Hφ'". iApply "Hφ". iExact "Hφ'". }
    iApply (wp_wand with "[-]").
    iApply (checkints_spec with "[- $HPC $Hcode $Hr_param1 $Hbesec $Hr_t1 $Hr_t2 $Hr_t3]");[eauto..|].
    2: { iSimpl. iIntros (v) "[Hφ | Hfailed]". iExact "Hφ". iIntros "Hcontr". iSimplifyEq. }
    iNext. iIntros "(HPC & Hcheckints & Hr_param1 & Hr_t1 & Hr_t2 & Hr_t3 & Hbesec & #Hints)".
    iDestruct "Hints" as %Hints.
    (* we now have enough information to close the region again *)
    iDestruct ("Hcls'" with "Hbesec") as "Hr".

    (* for the next part of the code, we will need to manipulate our local stack frame *)
    (* for that, we begin by revoking the full local stack frame from W *)
    assert (∃ frame_end, a_param + 10 = Some frame_end)%a as [frame_end Hframe_delim].
    { clear -Hbounds Ha_param Hsome Hsize. destruct (a_param + 10)%a eqn:HH;eauto. exfalso. solve_addr.}
    (* first we must know that a fully uninitialized world satisfies the revoke condition *)
    apply uninitialize_revoke_condition in Hmcond as Hrevoked.
    (* next we may revoke it *)
    iMod (uninitialize_to_revoked_cond_states (region_addrs bstk frame_end) _ _ RWLX (λ Wv, interp Wv.1 Wv.2) with "[$Hr $Hsts]") as "(Hr & Hsts & Hframe)";[apply region_addrs_NoDup|auto|..].
    { apply Forall_forall. intros x Hin%elem_of_region_addrs. apply Hstk_cond. clear -Hbounds Ha_param Hsome Hsize Hframe_delim Hin. solve_addr. }
    { iApply big_sepL_forall. iIntros (k x Hlookup).
      assert (x ∈ (region_addrs bstk frame_end)) as Hin;[apply elem_of_list_lookup;eauto|].
      apply elem_of_region_addrs in Hin.
      iDestruct (read_allowedU_inv _ x with "Hwstk_valid") as (p' Hflows) "Hcond".
      clear -Hin Hframe_delim Ha_param Hsome Hsize Hbounds. solve_addr.
      auto. destruct p';inversion Hflows. iFrame "Hcond". }

    (* finally we clean up our resources a bit *)
    iAssert (∃ ws wret w', bstk ↦ₐ[RWLX] wret ∗ a ↦ₐ[RWLX] w' ∗ [[a_param,frame_end]]↦ₐ[RWLX][[ws]])%I with "[Hframe]" as (wsstk wret w') "(Hbstk & Ha & Hframe)".
    { iDestruct (region_addrs_exists with "Hframe") as (ws) "Hframe".
      iDestruct (big_sepL2_length with "Hframe") as %Hflen. rewrite region_addrs_length in Hflen.
      assert (region_size bstk frame_end = 12) as Heq. clear -Hframe_delim Ha_param. rewrite /region_size. solve_addr.
      rewrite Heq in Hflen. destruct ws;[inversion Hflen|]. rewrite region_addrs_cons;[|clear -Hframe_delim Ha_param;solve_addr].
      rewrite Hsome /=. rewrite region_addrs_cons;[|clear -Hframe_delim Ha_param Hsome;solve_addr].
      assert ((a + 1)%a = Some a_param) as ->;[clear -Hsome Ha_param;solve_addr|]. destruct ws;[inversion Hflen|]. simpl.
      iDestruct "Hframe" as "(H1 & H2 & Hframe)".
      iExists ws,w,w5. iDestruct "H1" as "[_ $]". iDestruct "H2" as "[_ $]".
      iApply (big_sepL2_mono with "Hframe"). iIntros (k y1 y2 Hin1 Hin2) "[_ H]". iFrame. }
    iDestruct (big_sepL2_length with "Hframe") as %Hframe_length.
    rewrite region_addrs_length in Hframe_length.
    apply (incr_addr_region_size_iff _ _ 10)in Hframe_delim as Hframe_det.
    destruct Hframe_det as [Hframe_le Hframe_size]. rewrite Hframe_size in Hframe_length.

    (* we can now continue with the execution of instructions *)
    iPrologue_multi "Hprog" Hcont Hvpc link4.
    iDestruct (big_sepL2_length with "Hcode") as %Hlength_code.
    destruct_addr_list l_code3.
    iDestruct (writeLocalAllowedU_implies_local with "Hwstk_valid") as %Hmono;auto.
    destruct lstk;inversion Hmono;clear Hmono.

    (* pushU r_stk 2 *)
    assert (is_Some (a_param + 1)%a) as [af2 Haf2].
    { destruct (a_param + 1)%a eqn:Hcontr;eauto;exfalso;clear -Hframe_delim Hcontr;solve_addr. }
    destruct wsstk as [|wf1 wsstk];[inversion Hframe_length|].
    iDestruct (region_mapsto_cons with "Hframe") as "[Hf1 Hframe]";
      [apply Haf2|clear -Haf2 Hframe_delim;solve_addr|..].
    iDestruct "Hcode" as "[Hi Hcode]".
    apply contiguous_between_cons_inv_first in Hcont_code4 as Heq. subst l_code3.
    iApply (pushU_z_spec with "[- $HPC $Hf1 $Hr_stk $Hi]");
      [iCorrectPC link3 link4|apply Hfl|auto| |iContiguous_next_a Hcont_code4|apply Haf2|].
    { clear -Hbounds Ha_param Hsize Hframe_delim. apply le_addr_withinBounds; solve_addr. }
    iNext. iIntros "(HPC & Hprog_done2 & Hr_stk & Hf1)".

    (* pushU r_stk stack_obj *)
    assert (is_Some (af2 + 1)%a) as [af3 Haf3].
    { destruct (af2 + 1)%a eqn:Hcontr;eauto;exfalso;clear -Hframe_delim Hcontr Haf2;solve_addr. }
    destruct wsstk as [|wf2 wsstk];[inversion Hframe_length|].
    iDestruct (region_mapsto_cons with "Hframe") as "[Hf2 Hframe]";
      [apply Haf3|clear -Haf2 Haf3 Hframe_delim;solve_addr|..].
    iDestruct "Hcode" as "[Hi Hcode]".
    iApply (pushU_z_spec with "[- $HPC $Hf2 $Hr_stk $Hi]");
      [iCorrectPC link3 link4|apply Hfl|auto| |iContiguous_next_a Hcont_code4|apply Haf3|].
    { clear -Hbounds Ha_param Hsize Hframe_delim Haf2 Haf3.
      apply le_addr_withinBounds; solve_addr. }
    iNext. iIntros "(HPC & Hi & Hr_stk & Hf2)". iCombine "Hi" "Hprog_done2" as "Hprog_done2".

    (* move r_param2 r_stk *)
    iPrologue "Hcode".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_param2 $Hr_stk]");
      [apply decode_encode_instrW_inv|apply Hfl|iCorrectPC link3 link4|iContiguous_next_a Hcont_code4|].
    iEpilogue "(HPC & Hi & Hr_param2 & Hr_stk)"; iCombine "Hi" "Hprog_done2" as "Hprog_done2".
    (* getb r_t1 r_stk *)
    iPrologue "Hcode".
    iApply (wp_Get_success with "[$HPC $Hi $Hr_t1 $Hr_stk]");
      [apply decode_encode_instrW_inv|eauto|apply Hfl|iCorrectPC link3 link4|iContiguous_next_a Hcont_code4|auto..|].
    iEpilogue "(HPC & Hi & Hr_stk & Hr_t1)"; iCombine "Hi" "Hprog_done2" as "Hprog_done2".
    iSimpl in "Hr_t1".
    (* gete r_t2 r_stk *)
    iPrologue "Hcode".
    iApply (wp_Get_success with "[$HPC $Hi $Hr_t2 $Hr_stk]");
      [apply decode_encode_instrW_inv|eauto|apply Hfl|iCorrectPC link3 link4|iContiguous_next_a Hcont_code4|auto..|].
    iEpilogue "(HPC & Hi & Hr_stk & Hr_t2)"; iCombine "Hi" "Hprog_done2" as "Hprog_done2".
    iSimpl in "Hr_t2".
    (* add r_t1 r_t1 3 *)
    iPrologue "Hcode".
    iApply (wp_add_sub_lt_success_dst_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|eauto|iContiguous_next_a Hcont_code4|apply Hfl|iCorrectPC link3 link4|].
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done2" as "Hprog_done2".
    iSimpl in "Hr_t1".
    (* subseg r_param2 r_t1 r_t2 *)
    iPrologue "Hcode".
    iApply (wp_subseg_success _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ af2 estk with "[$HPC $Hi $Hr_param2 $Hr_t1 $Hr_t2]");
      [apply decode_encode_instrW_inv|apply Hfl|iCorrectPC link3 link4| |auto|auto| |iContiguous_next_a Hcont_code4|].
    { split;[|apply z_to_addr_z_of]. clear -Haf2 Ha_param. assert (bstk + 3 = Some af2)%a;[solve_addr|].
      apply incr_addr_of_z_i in H as Heq. rewrite Heq. apply z_to_addr_z_of. }
    { rewrite /isWithin. apply andb_true_iff. rewrite !Z.leb_le. clear -Ha_param Haf2. solve_addr. }
    iEpilogue "(HPC & Hi & Hr_t1 & Hr_t2 & Hr_param2)"; iCombine "Hi" "Hprog_done2" as "Hprog_done2".
    (* promoteU r_param2 *)
    iPrologue "Hcode".
    iApply (rules_PromoteU_derived.wp_promoteU_success with "[$HPC $Hi $Hr_param2]");
      [apply decode_encode_instrW_inv|apply Hfl|iCorrectPC link3 link4|auto|..].
    { eapply contiguous_between_last. apply Hcont_code4. auto. }
    iEpilogue "(HPC & Hi & Hr_param2)"; iCombine "Hi" "Hprog_done2" as "Hprog_done2".
    iSimpl in "Hr_param2". assert (addr_reg.min af3 estk = af3) as ->;[clear -Hbounds Hsize Ha_param Haf2 Haf3;solve_addr|].

    (* we are now ready to apply the calling convention *)
    (* split up the stack frame into activation and parameter part *)
    assert (∃ a_r_adv, (af3 + 6)%a = Some a_r_adv) as [a_r_adv Ha_r_adv];
      [clear -Hbounds Hframe_delim Haf2 Haf3;destruct (af3 + 6)%a eqn:hsome;eauto;exfalso;solve_addr|].
    assert (∃ b_r_adv, (af3 + 7)%a = Some b_r_adv) as [b_r_adv Hb_r_adv];
      [clear -Hbounds Hframe_delim Haf2 Haf3;destruct (af3 + 7)%a eqn:hsome;eauto;exfalso;solve_addr|].
    assert (∃ wact wparams, wsstk = wact ++ wparams ∧ length wact = 7) as (wact & wparams & Hframe_eqapp & Hact_size).
    { clear -Hframe_length. repeat (destruct wsstk;[by inversion Hframe_length|]). destruct wsstk;inversion Hframe_length.
      exists [w;w0;w1;w2;w3;w4;w5]. eauto. }
    rewrite Hframe_eqapp. iDestruct (region_mapsto_split _ _ b_r_adv with "Hframe") as "[Hact Hparams]";auto.
    { clear -Ha_r_adv Hframe_delim Haf2 Haf3 Hb_r_adv. solve_addr. }
    { rewrite /region_size Hact_size. clear -Hb_r_adv Hframe_delim Haf2 Haf3. solve_addr. }
    iClear "Hcode". iPrologue_multi "Hprog" Hcont Hvpc link5.
    (* reconstruct registers except r_param1 r_param2 *)
    rewrite -!(delete_commute _ r_t4).
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t4]") as "Hregs"; [apply lookup_delete|rewrite insert_delete].
    rewrite -!(delete_commute _ r_t3) -!delete_insert_ne//.
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t3]") as "Hregs"; [apply lookup_delete|rewrite insert_delete].
    rewrite -!(delete_commute _ r_t2) -!delete_insert_ne//.
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t2]") as "Hregs"; [apply lookup_delete|rewrite insert_delete].
    rewrite -!(delete_commute _ r_t1) -!delete_insert_ne//.
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t1]") as "Hregs"; [apply lookup_delete|rewrite insert_delete].

    iApply (scallU_prologue_spec with "[- $HPC $Hact $Hcode $Hregs $Hr_stk]");
      [apply Hvpc_code5| | |apply Hcont_code5|apply Hfl|auto..|apply Ha_r_adv|apply Hb_r_adv|].
    { clear -Ha_param Haf3 Hbounds Hsize Hframe_delim Haf2. apply le_addr_withinBounds;solve_addr. }
    { clear -Ha_param Haf3 Hbounds Hsize Hframe_delim Haf2 Hb_r_adv. apply le_addr_withinBounds;solve_addr. }
    { repeat (apply not_elem_of_cons; split;auto). apply not_elem_of_nil. }
    { clear. set_solver. }
    { rewrite dom_insert_L !dom_delete_L !dom_insert_L Hdom. clear. simpl. set_solver. }
    iSplitL "Hr_t0";[eauto|].
    iNext. iIntros "(HPC & Hr_stk & Hr_t0 & Hregs & Hact & HscallU_prologue)".

    (* TODO: fix the calling convention to take the instructions between jmp and prologue into account
       (this can be done as a parametrised activation record, that subsegs the expected amount)? or as a parameter to prologue *)
  Admitted. 







End stack_object.
