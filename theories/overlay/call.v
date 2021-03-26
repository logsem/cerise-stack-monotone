From iris.algebra Require Import base.
From iris.program_logic Require Import language ectx_language ectxi_language.
From stdpp Require Import gmap fin_maps list finite.
From cap_machine Require Export addr_reg machine_base machine_parameters.
From cap_machine.overlay Require Import base.

(* Call r rargs implements a calling convention with arguments passed on the stack
   Assuming that r0, r1, r2 ∉ {r} ∪ rargs, and r_stk contains a stack capability, it will
   - save *all* registers on the stack except PC and r_stk
   - prepare the return capability
   - prepare the stack capability in r_stk for a new frame
   - push the return capability
   - push all arguments
   - clear all registers except PC, r and r_stk
   - jmp r *)

Section call.

  Context `{MachineParameters}.
  Definition r_stk := R 31 eq_refl.

  (* Clearing a list of registers *)
  Definition rclear_instrs (r : list RegName): list Word := map (λ r_i, inl (encodeInstr (Mov r_i (inl 0%Z)))) r.

  Lemma rclear_instrs_length:
    forall r, length (rclear_instrs r) = length r.
  Proof. induction r; simpl; auto. Qed.

  (* Push instruction *)
  Definition push_instrs ρs: list Word := map (fun ρ => inl (encodeInstr (StoreU r_stk (inl 0%Z) ρ))) ρs.

  Lemma push_instrs_length:
    forall ρs, length (push_instrs ρs) = length ρs.
  Proof. induction ρs; simpl; auto. Qed.

  (* Pop instruction *)
  Definition pop_instrs r: list Word := [inl (encodeInstr (LoadU r r_stk (inl (-1)%Z))); inl (encodeInstr (Lea r_stk (inl (-1)%Z)))].

  (* Push all registers except r_stk and PC *)
  Definition push_env_instrs: list Word :=
    push_instrs (map (fun r => inr r) (list_difference all_registers [PC; r_stk])).

  Lemma push_env_instrs_length:
    length (push_env_instrs) = 31.
  Proof. reflexivity. Qed.

  (* Pop all registers except r_stk and PC, must be reverse order from push *)
  Definition pop_env_instrs: list Word :=
    foldl (fun b r => (pop_instrs r) ++ b) [] (list_difference all_registers [PC; r_stk]).

  Lemma pop_env_instrs_length:
    length (pop_env_instrs) = 62.
  Proof. reflexivity. Qed.

  (* Code for call macro *)
  Definition call_instrs r rargs: list Word :=
    (* Save environment *)
    push_env_instrs
    (* Prepare return capability *)
    ++ push_instrs [ inl (encodeInstr (Mov (R 1 eq_refl) (inr PC)))
                   ; inl (encodeInstr (Lea (R 1 eq_refl) (inl 5%Z)))
                   ; inl (encodeInstr (Load r_stk (R 1 eq_refl)))
                   ; inl (encodeInstr (LoadU PC r_stk (inl (-1)%Z)))]
    ++ [ inl (encodeInstr (Mov (R 1 eq_refl) (inr PC)))
       ; inl (encodeInstr (Lea (R 1 eq_refl) (inl (43 + length rargs)%Z))) (* offset to beginning of environment restoration *)]
    ++ push_instrs [inr (R 1 eq_refl); inr r_stk]
    ++ [ inl (encodeInstr (Mov (R 0 eq_refl) (inr r_stk)))
       ; inl (encodeInstr (PromoteU (R 0 eq_refl)))
       ; inl (encodeInstr (Lea (R 0 eq_refl) (inl (-6)%Z)))
       ; inl (encodeInstr (Restrict (R 0 eq_refl) (inl (encodePermPair (E, Monotone)))))
       ]
    (* Prepare new stack capability for callee *)
    ++ [inl (encodeInstr (GetA (R 1 eq_refl) r_stk));
        inl (encodeInstr (GetE (R 2 eq_refl) r_stk));
        inl (encodeInstr (Subseg r_stk (inr (R 1 eq_refl)) (inr (R 2 eq_refl))))]
    (* Push return capability *)
    ++ push_instrs [inr (R 0 eq_refl)]
    (* Push all arguments *)
    ++ push_instrs (map (fun r => inr r) rargs)
    (* Clear all registers *)
    ++ rclear_instrs (list_difference all_registers [PC; r; r_stk])
    (* Jump to callee *)
    ++ [inl (encodeInstr (Jmp r))]
    (* Restore environment *)
    ++ [inl (encodeInstr (Lea r_stk (inl (-1)%Z)))] ++ pop_env_instrs.

  Lemma all_registers_list_difference_length:
    forall r, r <> PC ->
         r <> r_stk ->
         length (list_difference all_registers [PC; r; r_stk]) = 30.
  Proof.
    destruct r; try congruence.
    intros. do 32 (destruct n as [|n]; [simpl; try reflexivity|]).
    - elim H1. f_equal. eapply Eqdep_dec.eq_proofs_unicity. destruct x, y; auto.
    - simpl in fin; discriminate.
  Qed.

  Lemma call_instrs_length:
    forall r rargs,
      r <> PC ->
      r <> r_stk ->
      length (call_instrs r rargs) = 141 + length rargs.
  Proof.
    intros. rewrite /call_instrs 11!app_length push_env_instrs_length pop_env_instrs_length !push_instrs_length !map_length all_registers_list_difference_length //.
    simpl length. lia.
  Qed.

End call.
