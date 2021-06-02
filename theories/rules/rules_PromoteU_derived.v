From cap_machine Require Import rules_base.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac.
From cap_machine.rules Require Import rules_PromoteU.

Section cap_lang_rules.
  Context `{memG Σ, regG Σ}.
  Context `{MachineParameters}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : cap_lang.expr.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : cap_lang.val.
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.

  (* load from the top *)
  Lemma wp_promoteU_success Ep r1 pc_p pc_g pc_b pc_e pc_a w p g b e a pc_a' :
    decodeInstrW w = PromoteU r1 →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    p <> E ->
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r1 ↦ᵣ inr ((p,g),b,e,a) }}}
      Instr Executable @ Ep
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
             ∗ pc_a ↦ₐ w
             ∗ r1 ↦ᵣ inr (promote_perm p, g, b, addr_reg.min a e, a) }}}.
  Proof.
    iIntros (Hinstr Hvpc HE Hpca' φ)
            "(>HPC & >Hi & >Hr1) Hφ".
    (* pose proof (correctPC_nonO _ _ _ _ _ _ Hfl Hvpc) as Hpc_p'. *)
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap % ]".
    iApply (wp_PromoteU with "[$Hmap $Hi]") ;simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
       rewrite insert_commute // insert_insert insert_commute //  insert_insert.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hr1]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto.
       destruct H5; try congruence. inv Hvpc. naive_solver.
     }
  Qed.

End cap_lang_rules.
