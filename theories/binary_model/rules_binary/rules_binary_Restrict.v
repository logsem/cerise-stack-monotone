From cap_machine Require Export rules_Restrict rules_binary_base.
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

  Lemma step_Restrict Ep K pc_p pc_g pc_b pc_e pc_a w dst src regs :
    decodeInstrW w = Restrict dst src ->
    isCorrectPC (inr (pc_p, pc_g, pc_b, pc_e, pc_a)) →
    regs !! PC = Some (inr (pc_p, pc_g, pc_b, pc_e, pc_a)) →
    regs_of (Restrict dst src) ⊆ dom _ regs →

    nclose specN ⊆ Ep →

    spec_ctx ∗ ⤇ fill K (Instr Executable) ∗ pc_a ↣ₐ w ∗ ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={Ep}=∗ ∃ retv regs', ⌜ Restrict_spec regs dst src regs' retv ⌝ ∗ ⤇ fill K (of_val retv) ∗ pc_a ↣ₐ w ∗ ([∗ map] k↦y ∈ regs', k ↣ᵣ y).
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hcls) "(#Hinv & Hj & Hpc_a & Hmap)".
    iDestruct "Hinv" as (ρ) "Hinv". rewrite /spec_inv.
    iInv specN as ">Hinv'" "Hclose". iDestruct "Hinv'" as (e [σr σm]) "[Hown %] /=".
    iDestruct (regspec_heap_valid_inclSepM with "Hown Hmap") as %Hregs.
    have HPC' := regs_lookup_eq _ _ _ HPC.
    have Hx := lookup_weaken _ _ _ _ HPC Hregs.
    iDestruct (spec_heap_valid with "[$Hown $Hpc_a]") as %Hpc_a.
    iDestruct (spec_expr_valid with "[$Hown $Hj]") as %Heq; subst e.

    specialize (normal_always_step (σr,σm)) as [c [ σ2 Hstep]].
    eapply step_exec_inv in Hstep; eauto.

    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri.
    unfold regs_of in Hri, Dregs. assert (Hstep':=Hstep).
    destruct (Hri dst) as [wdst [H'dst Hdst]]. by set_solver+.
    destruct wdst as [| cdst]; [| destruct_cap cdst].
    { rewrite /= /RegLocate Hdst in Hstep.
      destruct src; inv Hstep; simplify_pair_eq.
      all: iFailStep Restrict_fail_dst_noncap. }

    destruct (z_of_argument regs src) as [wsrc|] eqn:Hwsrc;
      pose proof Hwsrc as H'wsrc; cycle 1.
    { destruct src as [| r0]; cbn in Hwsrc; [ congruence |].
      destruct (Hri r0) as [r0v [Hr'0 Hr0]]. by unfold regs_of_argument; set_solver+.
      rewrite Hr'0 in Hwsrc. destruct r0v as [| cc]; [ congruence | destruct_cap cc].
      assert (c = Failed ∧ σ2 = (σr, σm)) as (-> & ->).
      { rewrite /= /RegLocate Hdst Hr0 in Hstep. by simplify_pair_eq. }
      iFailStep Restrict_fail_src_nonz. }
    eapply z_of_argument_Some_inv' in Hwsrc; eauto.

    destruct (decide (cdst = E)).
    { subst cdst. cbn in Hstep. rewrite /RegLocate Hdst in Hstep.
      repeat case_match; inv Hstep; iFailStep Restrict_fail_pE. }

    destruct (PermPairFlowsTo (decodePermPair wsrc) (cdst,cdst3)) eqn:Hflows; cycle 1.
    { rewrite /= /RegLocate Hdst in Hstep.
      destruct Hwsrc as [ -> | (r0 & -> & Hr0 & Hr0') ].
      all: rewrite ?Hr0' Hflows in Hstep.
      all: repeat case_match; inv Hstep; iFailStep Restrict_fail_invalid_perm. }

    assert ((c, σ2) = updatePC (update_reg (σr, σm) dst (inr (decodePermPair wsrc, cdst2, cdst1, cdst0)))) as HH.
    { rewrite /= /RegLocate Hdst in Hstep.
      destruct Hwsrc as [ -> | (r0 & -> & Hr0 & Hr0') ].
      all: rewrite ?Hr0' Hflows in Hstep.
      all: repeat case_match; inv Hstep; eauto; congruence. }
    clear Hstep. rewrite /update_reg /= in HH.

    destruct (incrementPC (<[ dst := inr (decodePermPair wsrc, cdst2, cdst1, cdst0) ]> regs)) eqn:Hregs';
      pose proof Hregs' as H'regs'; cycle 1.
    { apply incrementPC_fail_updatePC with (m:=σm) in Hregs'.
      eapply updatePC_fail_incl with (m':=σm) in Hregs'.
      2: by apply lookup_insert_is_Some'; eauto.
      2: by apply insert_mono; eauto.
      simplify_pair_eq.
      iMod ((regspec_heap_update_inSepM _ _ _ dst) with "Hown Hmap") as "[Hown Hmap]"; eauto.
      iFailStep Restrict_fail_PC_overflow. }

    eapply (incrementPC_success_updatePC _ σm) in Hregs'
      as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & Hincr & HuPC & ->).
    eapply updatePC_success_incl with (m':=σm) in HuPC. 2: by eapply insert_mono; eauto.
    simplify_pair_eq. iFrame.
    iMod ((regspec_heap_update_inSepM _ _ _ dst) with "Hown Hmap") as "[Hr Hmap]"; eauto.
    iMod ((regspec_heap_update_inSepM _ _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iMod (exprspec_mapsto_update _ _ (fill K (Instr NextI)) with "Hr Hj") as "[Hown Hj]".
    iExists NextIV,_. iFrame.
    iMod ("Hclose" with "[Hown]") as "_".
    { iNext. iExists _,_;iFrame. iPureIntro. eapply rtc_r;eauto.
      prim_step_from_exec.
    }
    iModIntro. iPureIntro. econstructor; eauto. Unshelve. all: try done.
  Qed.

  Lemma step_restrict_success_z Ep K pc_p pc_g pc_b pc_e pc_a pc_a' w r1 p g b e a z :
     decodeInstrW w = Restrict r1 (inl z) →
     isCorrectPC (inr (pc_p,pc_g,pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     PermPairFlowsTo (decodePermPair z) (p,g) = true →
     p ≠ E →
     nclose specN ⊆ Ep →

     spec_ctx ∗ ⤇ fill K (Instr Executable)
              ∗ ▷ PC ↣ᵣ inr (pc_p,pc_g,pc_b,pc_e,pc_a)
              ∗ ▷ pc_a ↣ₐ w
              ∗ ▷ r1 ↣ᵣ inr (p,g,b,e,a)
     ={Ep}=∗ ⤇ fill K (Instr NextI)
         ∗ PC ↣ᵣ inr (pc_p,pc_g,pc_b,pc_e,pc_a')
         ∗ pc_a ↣ₐ w
         ∗ r1 ↣ᵣ inr (decodePermPair z,b,e,a).
  Proof.
    iIntros (Hinstr Hvpc Hpca' Hflows HpE Hnclose) "(Hown & Hj & >HPC & >Hpc_a & >Hr1)".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iMod (step_Restrict with "[$Hown $Hj $Hmap $Hpc_a]") as (retv regs' Hspec) "(Hj & Hpc_a & Hregs)";
      eauto; simplify_map_eq_alt; try rewrite lookup_insert; eauto.
      by unfold regs_of; rewrite !dom_insert; set_solver+.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iFrame. simpl in *. incrementPC_inv; simplify_map_eq_alt.
      rewrite (insert_commute _ PC r1) // insert_insert
              (insert_commute _ PC r1) // insert_insert.
      iDestruct (regs_of_map_2 with "Hregs") as "(?&?)"; eauto; by iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; simpl in *; simplify_map_eq_alt; eauto; try congruence.
      incrementPC_inv;[|rewrite lookup_insert_ne// lookup_insert;eauto]. congruence. }
  Qed.


End cap_lang_spec_rules.
