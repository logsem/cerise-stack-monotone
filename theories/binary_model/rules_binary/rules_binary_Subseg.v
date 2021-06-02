From cap_machine Require Export rules_Subseg rules_binary_base.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac.


Section cap_lang_spec_rules.
  Context `{cfgSG Σ, MachineParameters, invG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : cap_lang.state.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.


  Lemma step_Subseg Ep K pc_p pc_g pc_b pc_e pc_a w dst src1 src2 regs :
    decodeInstrW w = Subseg dst src1 src2 ->
    isCorrectPC (inr (pc_p, pc_g, pc_b, pc_e, pc_a)) →
    regs !! PC = Some (inr (pc_p, pc_g, pc_b, pc_e, pc_a)) →
    regs_of (Subseg dst src1 src2) ⊆ dom _ regs →

    nclose specN ⊆ Ep →

    spec_ctx ∗ ⤇ fill K (Instr Executable) ∗ ▷ pc_a ↣ₐ w ∗ ▷ ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={Ep}=∗ ∃ retv regs', ⌜ Subseg_spec regs dst src1 src2 regs' retv ⌝ ∗ ⤇ fill K (of_val retv) ∗ pc_a ↣ₐ w ∗ ([∗ map] k↦y ∈ regs', k ↣ᵣ y).
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hnclose) "(Hinv & Hj & >Hpc_a & >Hmap)".
    iDestruct "Hinv" as (ρ) "Hinv". rewrite /spec_inv.
    iInv specN as ">Hinv'" "Hclose". iDestruct "Hinv'" as (e [σr σm]) "[Hown %] /=".
    iDestruct (regspec_heap_valid_inclSepM with "Hown Hmap") as %Hregs.
    have HPC' := regs_lookup_eq _ _ _ HPC.
    have ? := lookup_weaken _ _ _ _ HPC Hregs.
    iDestruct (spec_heap_valid with "[$Hown $Hpc_a]") as %Hpc_a.
    iDestruct (spec_expr_valid with "[$Hown $Hj]") as %Heq; subst e.
    specialize (normal_always_step (σr,σm)) as [c [ σ2 Hstep]].
    eapply step_exec_inv in Hstep; eauto.

    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri.
    unfold regs_of in Hri, Dregs.
    destruct (Hri dst) as [wdst [H'dst Hdst]]. by set_solver+.
    assert (Hstep':=Hstep).
    destruct wdst as [| cdst]; [| destruct_cap cdst].
    { rewrite /= /RegLocate Hdst in Hstep. repeat case_match; inv Hstep; simplify_pair_eq.
      all: try iFailStep Subseg_fail_dst_noncap. }

    destruct (decide (cdst = E)).
    { subst cdst. rewrite /= /RegLocate Hdst in Hstep.
      repeat case_match; inv Hstep; simplify_pair_eq.
      all: iFailStep Subseg_fail_pE. }

    destruct (addr_of_argument regs src1) as [a1|] eqn:Ha1;
      pose proof Ha1 as H'a1; cycle 1.
    { destruct src1 as [| r1] eqn:?; cbn in Ha1.
      { rewrite /= /RegLocate Hdst Ha1 in Hstep.
        assert (c = Failed ∧ σ2 = (σr, σm)) as (-> & ->).
        { repeat case_match; inv Hstep; auto. }
        (* destruct src2;try iFailStep Subseg_fail_src1_nonaddr.  *)

        iMod (exprspec_mapsto_update _ _ (fill _ (Instr Failed)) with "Hown Hj") as "[Hown Hj]";
          iMod ("Hclose" with "[Hown]") as "_";
          [iNext;iExists _,_;iFrame;iPureIntro;eapply rtc_r;eauto;prim_step_from_exec|]. 
        { destruct src2; simplify_map_eq; auto. }
        iExists (FailedV),_; iFrame;iModIntro;iFailCore Subseg_fail_src1_nonaddr.
      }
      subst src1. destruct (Hri r1) as [r1v [Hr'1 Hr1]].
        by unfold regs_of_argument; set_solver+.
      rewrite /addr_of_argument /= Hr'1 in Ha1.
      assert (c = Failed ∧ σ2 = (σr, σm)) as (-> & ->).
      { repeat case_match; simplify_pair_eq.
        all: rewrite /= /RegLocate Hdst Hr1 ?Ha1 in Hstep.
        all: repeat case_match; inv Hstep; auto. }
      repeat case_match; try congruence; try rename c into c0.
      all: iFailStep Subseg_fail_src1_nonaddr.
    }
    eapply addr_of_argument_Some_inv' in Ha1 as [z1 [Hz1 Hz1']]; eauto.

    destruct (addr_of_argument regs src2) as [a2|] eqn:Ha2;
      pose proof Ha2 as H'a2; cycle 1.
    { destruct src2 as [| r2] eqn:?; cbn in Ha2.
      { rewrite /= /RegLocate Hdst Ha2 in Hstep.
        assert (c = Failed ∧ σ2 = (σr, σm)) as (-> & ->).
        { repeat case_match; inv Hstep; auto. }
        iMod (exprspec_mapsto_update _ _ (fill _ (Instr Failed)) with "Hown Hj") as "[Hown Hj]";
          iMod ("Hclose" with "[Hown]") as "_";
          [iNext;iExists _,_;iFrame;iPureIntro;eapply rtc_r;eauto;prim_step_from_exec|].
        { destruct src1; simplify_map_eq; auto. }
        iExists (FailedV),_; iFrame;iModIntro;iFailCore Subseg_fail_src2_nonaddr. }
      subst src2. destruct (Hri r2) as [r2v [Hr'2 Hr2]].
        by unfold regs_of_argument; set_solver+.
      rewrite /addr_of_argument /= Hr'2 in Ha2.
      assert (c = Failed ∧ σ2 = (σr, σm)) as (-> & ->).
      { repeat case_match; simplify_pair_eq.
        all: rewrite /= /RegLocate Hdst Hr2 ?Ha2 in Hstep.
        all: repeat case_match; inv Hstep; auto. }
      repeat case_match; try congruence; try rename c into c0.
      all: iFailStep Subseg_fail_src2_nonaddr. }
    eapply addr_of_argument_Some_inv' in Ha2 as [z2 [Hz2 Hz2']]; eauto.

    assert ((c, σ2) = if isWithin a1 a2 cdst2 cdst1 then
                        updatePC (update_reg (σr, σm) dst (inr (cdst, cdst3, a1, a2, cdst0))) else
                        (Failed, (σr, σm)))
      as Hexec.
    { rewrite -Hstep; clear Hstep.
      rewrite /= /RegLocate Hdst.
      destruct Hz1' as [ -> | [r1 (-> & Hr1 & Hr1') ] ];
        destruct Hz2' as [ -> | [r2 (-> & Hr2 & Hr2') ] ].
      all: rewrite ?Hz1 ?Hz2 ?Hr1' ?Hr2'.
      all: repeat case_match; auto; simplify_eq; auto; congruence. }

    clear Hstep.
    destruct (isWithin a1 a2 cdst2 cdst1) eqn:Hiw; cycle 1.
    { inv Hexec. iFailStep Subseg_fail_not_iswithin. }

    destruct (incrementPC (<[ dst := (inr (cdst, cdst3, a1, a2, cdst0)) ]> regs)) eqn:HX;
      pose proof HX as H'X; cycle 1.
    { apply incrementPC_fail_updatePC with (m:=σm) in HX.
      eapply updatePC_fail_incl with (m':=σm) in HX.
      2: by apply lookup_insert_is_Some'; eauto.
      2: by apply insert_mono; eauto.
      simplify_pair_eq.
      iMod ((regspec_heap_update_inSepM _ _ _ dst) with "Hown Hmap") as "[Hown Hmap]"; eauto.
      iFailStep Subseg_fail_incrPC. }

    eapply (incrementPC_success_updatePC _ σm) in HX
      as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & Hincr & HuPC & -> & ?).
    eapply updatePC_success_incl with (m':=σm) in HuPC. 2: by eapply insert_mono; eauto.
    simplify_pair_eq. iFrame.
    iMod ((regspec_heap_update_inSepM _ _ _ dst) with "Hown Hmap") as "[Hown Hmap]"; eauto.
    iMod ((regspec_heap_update_inSepM _ _ _ PC (inr (p', g', b', e', a_pc'))) with "Hown Hmap") as "[Hown Hmap]"; eauto.
    iMod (exprspec_mapsto_update _ _ (fill K (Instr NextI)) with "Hown Hj") as "[Hown Hj]".
    iExists NextIV,_. iFrame.
    iMod ("Hclose" with "[Hown]") as "_".
    { iNext. iExists _,_;iFrame. iPureIntro. eapply rtc_r;eauto.
      prim_step_from_exec.
    }
    iModIntro. iPureIntro. econstructor; eauto.
  Qed.

  Lemma step_subseg_success E K pc_p pc_g pc_b pc_e pc_a w dst r1 r2 p g b e a n1 n2 a1 a2 pc_a' :
    decodeInstrW w = Subseg dst (inr r1) (inr r2) →
    isCorrectPC (inr (pc_p,pc_g,pc_b,pc_e,pc_a)) →
    z_to_addr n1 = Some a1 ∧ z_to_addr n2 = Some a2 →
    p ≠ machine_base.E →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →
    nclose specN ⊆ E →

    spec_ctx ∗ ⤇ fill K (Instr Executable)
             ∗ ▷ PC ↣ᵣ inr (pc_p,pc_g,pc_b,pc_e,pc_a)
             ∗ ▷ pc_a ↣ₐ w
             ∗ ▷ dst ↣ᵣ inr (p,g,b,e,a)
             ∗ ▷ r1 ↣ᵣ inl n1
             ∗ ▷ r2 ↣ᵣ inl n2
    ={E}=∗ ⤇ fill K (Instr NextI)
        ∗ PC ↣ᵣ inr (pc_p,pc_g,pc_b,pc_e,pc_a')
        ∗ pc_a ↣ₐ w
        ∗ r1 ↣ᵣ inl n1
        ∗ r2 ↣ᵣ inl n2
        ∗ dst ↣ᵣ inr (p, g, a1, a2, a). 
  Proof. 
    iIntros (Hinstr Hvpc [Hn1 Hn2] Hpne Hwb Hpc_a' Hnclose) "(Hown & Hj & >HPC & >Hpc_a & >Hdst & >Hr1 & >Hr2)".
    iDestruct (map_of_regs_4 with "HPC Hr1 Hr2 Hdst") as "[Hmap (%&%&%&%&%&%)]".
    iMod (step_Subseg with "[$Hown $Hj $Hpc_a $Hmap]") as (retv regs' Hspec) "(Hj & Hpc_a & Hmap)";simplify_map_eq;eauto. 
    by unfold regs_of; rewrite !dom_insert; set_solver+.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iFrame. incrementPC_inv. unfold addr_of_argument, z_of_argument in *; simplify_map_eq_alt. 
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r2 dst) //
              (insert_commute _ r1 dst) // (insert_commute _ PC dst) // insert_insert.
      iDestruct (regs_of_map_4 with "Hmap") as "(?&?&?&?)"; eauto; by iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; unfold addr_of_argument, z_of_argument in *; simplify_map_eq_alt. congruence.
      incrementPC_inv;[|rewrite lookup_insert_ne// lookup_insert;eauto].
      destruct H13; try congruence.
      inv Hvpc; naive_solver. }
  Qed.


End cap_lang_spec_rules.
