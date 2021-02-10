From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules.
From cap_machine Require Export addr_reg_sample region_macros contiguous stack_macros_helpers.
From cap_machine Require Export req.

Section stack_macros.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          `{MonRef: MonRefG (leibnizO _) CapR_rtc Σ}
          `{MP: MachineParameters}.

  (* TODO: move this to the rules_Lea.v file. small issue with the spec of failure: it does not actually
     require/leave a trace on dst! It would be good if req_regs of a failing get does not include dst (if possible) *)
  Lemma wp_Lea_fail_U Ep pc_p pc_g pc_b pc_e pc_a w r1 rv p g b e a z a' pc_p' :
    decodeInstrW w = Lea r1 (inr rv) →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (a + z)%a = Some a' ->
     (match p with
      | URW | URWL | URWX | URWLX => (a < a')%a
      | _ => False
      end) ->

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ[pc_p'] w
           ∗ ▷ r1 ↦ᵣ inr ((p,g),b,e,a)
           ∗ ▷ rv ↦ᵣ inl z }}}
       Instr Executable @ Ep
     {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hdecode Hfl Hvpc Hz Hp φ) "(>HPC & >Hpc_a & >Hsrc & >Hdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_lea with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
      by rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
    iDestruct "Hspec" as %Hspec.
    destruct Hspec as [* Hsucc |].
    { (* Success (contradiction) *) simplify_map_eq. destruct p0; try done; revert Hp H5;clear;solve_addr. }
    { (* Failure, done *) by iApply "Hφ". }
  Qed.

  Definition prepstackU_instrs r (minsize: Z) :=
    reqperm_instrs r (encodePerm URWLX) ++
    reqsize_instrs r minsize ++
    [getb r_t1 r;
    geta r_t2 r;
    sub_r_r r_t1 r_t1 r_t2;
    lea_r r r_t1;
    move_z r_t1 0;
    move_z r_t2 0].

  Definition prepstackU r minsize a p : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(prepstackU_instrs r minsize), a_i ↦ₐ[p] w_i)%I.

  Lemma prepstackU_spec r minsize a w pc_p pc_p' pc_g pc_b pc_e a_first a_last φ :
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last ->
    PermFlows pc_p pc_p' ->
    contiguous_between a a_first a_last ->

      ▷ prepstackU r minsize a pc_p'
    ∗ ▷ PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_first)
    ∗ ▷ r ↦ᵣ w
    ∗ ▷ (∃ w, r_t1 ↦ᵣ w)
    ∗ ▷ (∃ w, r_t2 ↦ᵣ w)
    ∗ ▷ (if isPermWord w URWLX then
           ∃ l b e a', ⌜w = inr (URWLX,l,b,e,a')⌝ ∧
           if (minsize <? e - b)%Z then
             if (b <=? a')%Z then
               (PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_last) ∗ prepstackU r minsize a pc_p' ∗
                   r ↦ᵣ inr (URWLX,l,b,e,b) ∗ r_t1 ↦ᵣ inl 0%Z ∗ r_t2 ↦ᵣ inl 0%Z
                   -∗ WP Seq (Instr Executable) {{ φ }})
             else φ FailedV
           else φ FailedV
         else φ FailedV)
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hfl Hcont) "(>Hprog & >HPC & >Hr & >Hr_t1 & >Hr_t2 & Hφ)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength. simpl in *.
    iAssert (⌜r ≠ PC⌝)%I as %Hne.
    { destruct (decide (r = PC)); auto; subst. iDestruct (regname_dupl_false with "HPC Hr") as %Hcontr. done. }
    (* reqperm *)
    iPrologue_multi "Hprog" Hcont Hvpc link.
    iApply (reqperm_spec with "[$HPC $Hcode $Hr $Hr_t1 $Hr_t2 Hφ Hprog]"); [apply Hvpc_code|apply Hfl|apply Hcont_code|].
    iNext. destruct (isPermWord w URWLX); auto.
    iDestruct "Hφ" as (l b e a' Heq) "Hφ".
    subst. iExists l,b,e,a'. iSplit; auto.
    iIntros "(HPC & Hprog_done & Hr & Hr_t1 & Hr_t2)".
    (* reqsize *)
    iPrologue_multi "Hprog" Hcont Hvpc link0.
    iApply (reqsize_spec with "[- $HPC $Hcode $Hr $Hr_t1 $Hr_t2]");
      [apply Hvpc_code0|apply Hfl|eauto|].
    iNext. destruct (minsize <? e - b)%Z; auto.
    iIntros "H". iDestruct "H" as (w1 w2) "(Hreqsize & HPC & Hr & Hr_t1 & Hr_t2)".
    (* getb r_t1 r *)
    iDestruct (big_sepL2_length with "Hprog") as %Hlength'.
    prep_addr_list_full l_rest0 Hcont.
    iPrologue "Hprog".
    iApply (wp_Get_success with "[$HPC $Hi $Hr $Hr_t1]");
      [apply decode_encode_instrW_inv|auto|apply Hfl|iCorrectPC link0 a_last|iContiguous_next Hcont 0|auto..].
    iEpilogue "(HPC & Hi & Hr & Hr_t1) /="; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* geta r_t2 r *)
    iPrologue "Hprog".
    iApply (wp_Get_success with "[$HPC $Hi $Hr $Hr_t2]");
      [apply decode_encode_instrW_inv|auto|apply Hfl|iCorrectPC link0 a_last|iContiguous_next Hcont 1|auto..].
    iEpilogue "(HPC & Hi & Hr & Hr_t2) /="; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* sub r_t1 r_t1 r_t2 *)
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_dst_r with "[$HPC $Hi $Hr_t2 $Hr_t1]");
      [apply decode_encode_instrW_inv|auto|iContiguous_next Hcont 2|apply Hfl|iCorrectPC link0 a_last|..].
    iEpilogue "(HPC & Hi & Hr_t2 & Hr_t1) /="; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* we need to distinguish between the case where the capability is stuck, or usable *)
    assert ((a' + (b - a'))%a = Some b) as Hlea;[solve_addr|].
    destruct (decide (b <= a')%a).
    2: { (* lea fail *)
      iPrologue "Hprog".
      iApply (wp_Lea_fail_U with "[$HPC $Hi $Hr_t1 $Hr]");
        [apply decode_encode_instrW_inv|apply Hfl|iCorrectPC link0 a_last|apply Hlea|..].
      { simpl. solve_addr. }
      iEpilogue "_ /=". assert (b <=? a' = false)%Z as ->;[apply Z.leb_gt;solve_addr|].
      iApply wp_value. iApply "Hφ". }
    (* lea r r_t1 *)
    iPrologue "Hprog".
    iApply (wp_lea_success_reg with "[$HPC $Hi $Hr_t1 $Hr]");
      [apply decode_encode_instrW_inv|apply Hfl|iCorrectPC link0 a_last|iContiguous_next Hcont 3|apply Hlea|auto..].
    iEpilogue "(HPC & Hi & Hr_t1 & Hr)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* move r_t1 0 *)
    iPrologue "Hprog".
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t1]"); 
      [apply decode_encode_instrW_inv|apply Hfl|iCorrectPC link0 a_last|iContiguous_next Hcont 4|auto|..].
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* move r_t2 0 *)
    iPrologue "Hprog".
    apply contiguous_between_last with (ai:=a4) in Hcont as Hlast;[|auto].
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t2]"); 
      [apply decode_encode_instrW_inv|apply Hfl|iCorrectPC link0 a_last|apply Hlast|auto|..].
    iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    assert (b <=? a' = true)%Z as ->;[apply Zle_is_le_bool;auto|].
    iApply "Hφ". iFrame.
    repeat (iDestruct "Hprog_done" as "[Hi Hprog_done]"; iFrame "Hi"). 
    iFrame "Hprog_done". done.
  Qed.

End stack_macros.
