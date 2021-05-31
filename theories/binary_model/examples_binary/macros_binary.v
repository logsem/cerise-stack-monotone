From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel stack_macros_helpers.
From cap_machine Require Export iris_extra addr_reg_sample contiguous.
From cap_machine Require Import macros.
From cap_machine.binary_model.rules_binary Require Import rules_binary.

(** This file contains specification side specs for macros.
    The file contains push and rclear
 *)

Ltac iPrologue_s prog :=
  (try iPrologue_pre);
  iDestruct prog as "[Hi Hprog]".

Ltac iEpilogue_s :=
   iMod (do_step_pure _ [] with "[$Hspec $Hj]") as "Hj";auto;
   iSimpl in "Hj".

Section macros.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ} {cfg : cfgSG Σ}
          `{MP: MachineParameters}.


  (* --------------------------------------------------------------------------------- *)
  (* -------------------------------------- RCLEAR ----------------------------------- *)
  (* --------------------------------------------------------------------------------- *)

  Definition rclear_s (a : list Addr) (r : list RegName) : iProp Σ :=
      ([∗ list] k↦a_i;w_i ∈ a;(rclear_instrs r), a_i ↣ₐ w_i)%I.

  Lemma rclear_s_spec E (a : list Addr) (r: list RegName) (rmap : gmap RegName Word) p b e a1 an :
    contiguous_between a a1 an →
    ¬ PC ∈ r → hd_error a = Some a1 →
    isCorrectPC_range p b e a1 an →
    list_to_set r = dom (gset RegName) rmap →
     nclose specN ⊆ E →

     spec_ctx
    ∗ ⤇ Seq (Instr Executable)
    ∗ ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↣ᵣ w_i)
    ∗ ▷ PC ↣ᵣ inr (p,b,e,a1)
    ∗ ▷ rclear_s a r
     ={E}=∗ ⤇ Seq (Instr Executable)
         ∗ PC ↣ᵣ inr (p,b,e,an)
         ∗ ([∗ map] r_i↦_ ∈ rmap, r_i ↣ᵣ inl 0%Z)
         ∗ rclear_s a r.
  Proof.
    iIntros (Ha Hne Hhd Hvpc Hrdom Hnclose) "(#Hspec & Hj & >Hreg & >HPC & >Hrclear)".
    iDestruct (big_sepL2_length with "Hrclear") as %Har.
    iRevert (Hne Har Hhd Hvpc Ha Hrdom).
    iInduction (a) as [| a1'] "IH" forall (r rmap a1 an).
    { iIntros (Hne Har Hhd Hvpc Ha Hrdom). by inversion Hhd; simplify_eq. }
    iIntros (Hne Har Hhd Hvpc Ha Hrdom).
    rewrite /rclear_s /=.
    (* rewrite -(beq_nat_refl (length r)).  *)destruct r; inversion Har.
    rewrite rclear_instrs_cons.
    iDestruct (big_sepL2_cons with "Hrclear") as "[Ha1 Hrclear]".
    rewrite list_to_set_cons in Hrdom.
    assert (is_Some (rmap !! r)) as [rv ?].
    { rewrite elem_of_gmap_dom -Hrdom. set_solver. }
    iDestruct (big_sepM_delete _ _ r with "Hreg") as "[Hr Hreg]". eauto.
    pose proof (contiguous_between_cons_inv _ _ _ _ Ha) as [-> [a2 [? Hcont'] ] ].
    iMod (step_move_success_z _ [SeqCtx] with "[$Hspec $Hj $HPC $Hr $Ha1]")
      as "(Hj & HPC & Ha1 & Hr)";
      [apply decode_encode_instrW_inv|iCorrectPC a1 an|eauto|auto..].
    iEpilogue_s.
    destruct a.
    { iFrame. inversion Hcont'; subst. iFrame.
      destruct r0; inversion Har. simpl in Hrdom.
      iApply (big_sepM_delete _ _ r). eauto.
      rewrite (_: delete r rmap = ∅). rewrite !big_sepM_empty. eauto.
      apply map_empty. intro. eapply (@not_elem_of_dom _ _ (gset RegName)).
      typeclasses eauto. rewrite dom_delete_L -Hrdom. set_solver. }

    pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont') as ->.
    assert (PC ∉ r0). { apply not_elem_of_cons in Hne as [? ?]. auto. }

    destruct (decide (r ∈ r0)).
    { iDestruct (big_sepM_insert with "[$Hreg $Hr]") as "Hreg".
        by rewrite lookup_delete. rewrite insert_delete.
      (* iCombine "Ha1" "Hrclear" as "Hrclear". *) iSimpl. iFrame "Ha1".
      iMod ("IH" with "Hj Hreg HPC Hrclear [] [] [] [] [] []") as "($&$&Hregs&$)";iFrame;eauto.
      { iPureIntro. intros ? [? ?]. apply Hvpc. solve_addr. }
      { iPureIntro. rewrite dom_insert_L -Hrdom. set_solver. }
      { iApply (big_sepM_delete _ _ r). eauto.
        iDestruct (big_sepM_delete _ _ r with "Hregs") as "[? ?]".
        rewrite lookup_insert //. iFrame. rewrite delete_insert_delete //. } }
    { iMod ("IH" with "Hj Hreg HPC Hrclear [] [] [] [] [] []") as "($&$&Hregs&$)";iFrame;eauto.
      { iPureIntro. intros ? [? ?]. apply Hvpc. solve_addr. }
      { iPureIntro. rewrite dom_delete_L -Hrdom. set_solver. }
      iApply (big_sepM_delete _ _ r). eauto. iFrame. done.
    }
  Qed.




End macros.
