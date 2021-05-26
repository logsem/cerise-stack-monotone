From cap_machine Require Export rules_AddSubLt rules_binary_base.
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

  Tactic Notation "destruct_or" ident(H) :=
  match type of H with
  | _ ∨ _ => destruct H as [H|H]
  | Is_true (_ || _) => apply orb_True in H; destruct H as [H|H]
  end.
  Tactic Notation "destruct_or" "?" ident(H) := repeat (destruct_or H).
  Tactic Notation "destruct_or" "!" ident(H) := hnf in H; destruct_or H; destruct_or? H.

  Lemma step_AddSubLt Ep K i pc_p pc_g pc_b pc_e pc_a w dst arg1 arg2 regs :
    decodeInstrW w = i →
    is_AddSubLt i dst arg1 arg2 →
    isCorrectPC (inr (pc_p,pc_g, pc_b, pc_e, pc_a)) →
    regs !! PC = Some (inr (pc_p,pc_g, pc_b, pc_e, pc_a)) →
    regs_of i ⊆ dom _ regs →

    nclose specN ⊆ Ep →

    spec_ctx ∗ ⤇ fill K (Instr Executable) ∗ ▷ pc_a ↣ₐ w ∗ ▷ ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={Ep}=∗ ∃ retv regs', ⌜ AddSubLt_spec (decodeInstrW w) regs dst arg1 arg2 regs' retv ⌝ ∗
                            ⤇ fill K (of_val retv) ∗ pc_a ↣ₐ w ∗ [∗ map] k↦y ∈ regs', k ↣ᵣ y.
  Proof.
    iIntros (Hdecode Hinstr Hvpc HPC Dregs Hnclose) "(Hinv & Hj & >Hpc_a & >Hmap)".
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
    erewrite regs_of_is_AddSubLt in Hri, Dregs; eauto.
    destruct (Hri dst) as [wdst [H'dst Hdst]]. by set_solver+.

    destruct (z_of_argument regs arg1) as [n1|] eqn:Hn1;
      pose proof Hn1 as Hn1'; cycle 1.
    (* Failure: arg1 is not an integer *)
    { unfold z_of_argument in Hn1. destruct arg1 as [| r0]; [ congruence |].
      destruct (Hri r0) as [r0v [Hr'0 Hr0]]. by unfold regs_of_argument; set_solver+.
      rewrite Hr'0 in Hn1. destruct r0v as [| (([? ?] & ?) & ?) ]; [ congruence |].
      assert (c = Failed ∧ σ2 = (σr, σm)) as (-> & ->).
      { destruct_or! Hinstr; rewrite Hinstr /= in Hstep.
        all: rewrite /RegLocate Hr0 in Hstep. all: repeat case_match; simplify_eq; eauto. }
      iFailStep AddSubLt_fail_nonconst1.
    }

    destruct (z_of_argument regs arg2) as [n2|] eqn:Hn2;
      pose proof Hn2 as Hn2'; cycle 1.
    (* Failure: arg2 is not an integer *)
    { unfold z_of_argument in Hn2. destruct arg2 as [| r0]; [ congruence |].
      destruct (Hri r0) as [r0v [Hr'0 Hr0]]. by unfold regs_of_argument; set_solver+.
      rewrite Hr'0 in Hn2. destruct r0v as [| (([? ?] & ?) & ?) ]; [ congruence |].
      assert (c = Failed ∧ σ2 = (σr, σm)) as (-> & ->).
      { destruct_or! Hinstr; rewrite Hinstr /= in Hstep.
        all: rewrite /RegLocate Hr0 in Hstep. all: repeat case_match; simplify_eq; eauto. }
      iFailStep AddSubLt_fail_nonconst2. }

    eapply z_of_argument_Some_inv' in Hn1; eapply z_of_argument_Some_inv' in Hn2; eauto.
    assert ((c, σ2) = updatePC (update_reg (σr, σm) dst (inl (denote i n1 n2)))) as HH.
    { destruct Hn1 as [ -> | (r1 & -> & _ & Hr1) ]; destruct Hn2 as [ -> | (r2 & -> & _ & Hr2) ].
      all: destruct_or! Hinstr; rewrite Hinstr /= /RegLocate /update_reg /= in Hstep |- *; auto.
      all: rewrite ?Hr1 ?Hr2 /= in Hstep; auto. }
    rewrite /update_reg /= in HH.

    destruct (incrementPC (<[ dst := inl (denote i n1 n2) ]> regs))
      as [regs'|] eqn:Hregs'; pose proof Hregs' as H'regs'; cycle 1.
    (* Failure: Cannot increment PC *)
    { apply incrementPC_fail_updatePC with (m:=σm) in Hregs'.
      eapply updatePC_fail_incl with (m':=σm) in Hregs'.
      2: by apply lookup_insert_is_Some'; eauto.
      2: by apply insert_mono; eauto.
      simplify_pair_eq.
      iMod ((regspec_heap_update_inSepM _ _ _ dst) with "Hown Hmap") as "[Hown Hmap]"; eauto.
      iFailStep AddSubLt_fail_incrPC. }

    (* Success *)

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
      prim_step_from_exec. }
    iModIntro. iPureIntro. econstructor; eauto.
  Qed.

  Lemma step_AddSubLt_fail E K ins dst n1 r2 w wdst cap pc_p pc_g pc_b pc_e pc_a :
    decodeInstrW w = ins →
    is_AddSubLt ins dst (inl n1) (inr r2) →
    isCorrectPC (inr (pc_p,pc_g , pc_b, pc_e, pc_a)) →
    nclose specN ⊆ E →

    spec_ctx ∗ ⤇ fill K (Instr Executable) ∗ PC ↣ᵣ inr (pc_p,pc_g, pc_b, pc_e, pc_a) ∗ pc_a ↣ₐ w ∗ dst ↣ᵣ wdst ∗ r2 ↣ᵣ inr cap
    ={E}=∗ ⤇ fill K (of_val FailedV).
  Proof.
    iIntros (Hdecode Hinstr Hvpc Hnclose) "(Hown & Hj & HPC & Hpc_a & Hdst & Hr2)".
    iDestruct (map_of_regs_3 with "HPC Hdst Hr2") as "[Hmap (%&%&%)]".
    iMod (step_AddSubLt with "[$Hmap $Hown $Hj Hpc_a]") as (? ? Hspec) "(Hj & HH)"; eauto; simplify_map_eq; eauto.
      by erewrite regs_of_is_AddSubLt; eauto; rewrite !dom_insert; set_solver+.
    destruct Hspec as [* Hsucc |].
    { (* Success (contradiction) *) by rewrite /= lookup_insert_ne// lookup_insert_ne// lookup_insert in H5. }
    { (* Failure, done *) by iFrame. }
  Qed.

  Lemma step_add_sub_lt_success_z_r E K dst pc_p pc_g pc_b pc_e pc_a w wdst ins n1 r2 n2 pc_a' :
    decodeInstrW w = ins →
    is_AddSubLt ins dst (inl n1) (inr r2) →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (inr (pc_p,pc_g,pc_b,pc_e,pc_a)) ->
    nclose specN ⊆ E →

    spec_ctx ∗ ⤇ fill K (Instr Executable)
             ∗ PC ↣ᵣ inr (pc_p,pc_g,pc_b,pc_e,pc_a)
             ∗ pc_a ↣ₐ w
             ∗ r2 ↣ᵣ inl n2
             ∗ dst ↣ᵣ wdst
    ={E}=∗
             ⤇ fill K (of_val NextIV)
             ∗ PC ↣ᵣ inr (pc_p,pc_g,pc_b,pc_e,pc_a')
             ∗ pc_a ↣ₐ w
             ∗ r2 ↣ᵣ inl n2
             ∗ dst ↣ᵣ inl (denote ins n1 n2). 
  Proof.
    iIntros (Hdecode Hinstr Hpc_a Hvpc Hnlose) "(#Hown & Hj & HPC & Hpc_a & Hr2 & Hdst)".
    iDestruct (map_of_regs_3 with "HPC Hr2 Hdst") as "[Hmap (%&%&%)]".
    iMod (step_AddSubLt with "[$Hmap $Hj $Hown $Hpc_a]") as (retv regs' Hspec) "(Hj & Hpc_a & Hmap)"; simplify_map_eq; eauto.
    by erewrite regs_of_is_AddSubLt; eauto; rewrite !dom_insert; set_solver+.
    
    destruct Hspec as [| * Hfail].
    { (* Success *)
      iFrame. incrementPC_inv. simplify_map_eq. 
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r2 dst) //
              (insert_commute _ dst PC) // insert_insert.
      by iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; simplify_map_eq; eauto.
      incrementPC_inv;[|rewrite lookup_insert_ne// lookup_insert; eauto]. congruence. 
    } 
  Qed.

  Lemma step_add_sub_lt_success_dst_r E K dst pc_p pc_g pc_b pc_e pc_a w ins n1 r2 n2 pc_a' :
    decodeInstrW w = ins →
    is_AddSubLt ins dst (inr dst) (inr r2) →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (inr (pc_p,pc_g,pc_b,pc_e,pc_a)) ->

    nclose specN ⊆ E →

    spec_ctx ∗ ⤇ fill K (Instr Executable)
             ∗ PC ↣ᵣ inr (pc_p,pc_g,pc_b,pc_e,pc_a)
             ∗ pc_a ↣ₐ w
             ∗ r2 ↣ᵣ inl n2
             ∗ dst ↣ᵣ inl n1
    ={E}=∗ ⤇ fill K (Instr NextI)
        ∗ PC ↣ᵣ inr (pc_p,pc_g,pc_b,pc_e,pc_a')
        ∗ pc_a ↣ₐ w
        ∗ r2 ↣ᵣ inl n2
        ∗ dst ↣ᵣ inl (denote ins n1 n2).
  Proof.
    iIntros (Hdecode Hinstr Hpc_a Hvpc Hnclose) "(Hown & Hj & HPC & Hpc_a & Hr2 & Hdst)".
    iDestruct (map_of_regs_3 with "HPC Hr2 Hdst") as "[Hmap (%&%&%)]".
    iMod (step_AddSubLt with "[$Hmap $Hj $Hown $Hpc_a]") as (retv regs' Hspec) "(Hj & Hpc_a & Hmap)"; simplify_map_eq; eauto.
    by erewrite regs_of_is_AddSubLt; eauto; rewrite !dom_insert; set_solver+.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iFrame. incrementPC_inv; simpl in *; simplify_map_eq_alt.
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ r2 dst) //
              (insert_commute _ PC dst) // insert_insert. 
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; by iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; simpl in *; simplify_map_eq_alt. 
      incrementPC_inv;[|rewrite lookup_insert_ne// lookup_insert; eauto]. congruence. }
  Qed.

  Lemma step_add_sub_lt_success_z_dst E K dst pc_p pc_g pc_b pc_e pc_a w ins n1 n2 pc_a' :
    decodeInstrW w = ins →
    is_AddSubLt ins dst (inl n1) (inr dst) →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (inr (pc_p,pc_g,pc_b,pc_e,pc_a)) ->
    nclose specN ⊆ E →

    spec_ctx ∗ ⤇ fill K (Instr Executable)
             ∗ PC ↣ᵣ inr (pc_p,pc_g,pc_b,pc_e,pc_a)
             ∗ pc_a ↣ₐ w
             ∗ dst ↣ᵣ inl n2
    ={E}=∗ ⤇ fill K (Instr NextI)
        ∗ PC ↣ᵣ inr (pc_p,pc_g,pc_b,pc_e,pc_a')
        ∗ pc_a ↣ₐ w
        ∗ dst ↣ᵣ inl (denote ins n1 n2).
  Proof.
    iIntros (Hdecode Hinstr Hpc_a Hvpc Hnclose) "(Hown & Hj & HPC & Hpc_a & Hdst)".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iMod (step_AddSubLt with "[$Hmap $Hj $Hown $Hpc_a]") as (retv regs' Hspec) "(Hj & Hpc_a & Hmap)"; simplify_map_eq; eauto.
    by erewrite regs_of_is_AddSubLt; eauto; rewrite !dom_insert; set_solver+.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iFrame. simpl in *. incrementPC_inv; simplify_map_eq_alt.
      rewrite (insert_commute _ PC dst) // insert_insert insert_commute // insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; by iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; simpl in *; simplify_map_eq_alt.
      incrementPC_inv; [|rewrite lookup_insert_ne// lookup_insert; eauto]. congruence. }
  Qed.

  Lemma step_add_sub_lt_success_dst_z E K dst pc_p pc_g pc_b pc_e pc_a w ins n1 n2 pc_a' :
    decodeInstrW w = ins →
    is_AddSubLt ins dst (inr dst) (inl n2) →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (inr (pc_p,pc_g,pc_b,pc_e,pc_a)) ->
    nclose specN ⊆ E →

    spec_ctx ∗ ⤇ fill K (Instr Executable)
             ∗ PC ↣ᵣ inr (pc_p,pc_g,pc_b,pc_e,pc_a)
             ∗ pc_a ↣ₐ w
             ∗ dst ↣ᵣ inl n1
    ={E}=∗ ⤇ fill K (Instr NextI)
        ∗ PC ↣ᵣ inr (pc_p,pc_g,pc_b,pc_e,pc_a')
        ∗ pc_a ↣ₐ w
        ∗ dst ↣ᵣ inl (denote ins n1 n2).
  Proof.
    iIntros (Hdecode Hinstr Hpc_a Hvpc Hnclose) "(Hown & Hj & HPC & Hpc_a & Hdst)".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iMod (step_AddSubLt with "[$Hmap $Hj $Hown $Hpc_a]") as (retv regs' Hspec) "(Hj & Hpc_a & Hmap)"; simplify_map_eq; eauto.
    by erewrite regs_of_is_AddSubLt; eauto; rewrite !dom_insert; set_solver+.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iFrame. simpl in *. incrementPC_inv; simplify_map_eq_alt.
      rewrite (insert_commute _ PC dst) // insert_insert insert_commute // insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; by iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail;simpl in *;simplify_map_eq_alt; eauto.
      incrementPC_inv;[|rewrite lookup_insert_ne// lookup_insert;eauto]. congruence. }
  Qed.

End cap_lang_spec_rules.
