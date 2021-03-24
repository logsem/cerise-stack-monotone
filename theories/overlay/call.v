From iris.algebra Require Import base.
From iris.program_logic Require Import language ectx_language ectxi_language.
From stdpp Require Import gmap fin_maps list finite.
From cap_machine Require Export addr_reg machine_base machine_parameters.
From cap_machine.overlay Require Import base.

(* Call r rargs implements a calling convention with arguments passed on the stack
   Assuming that r0, r1 ∉ {r, rargs}, and r_stk contains a stack capability, it will
   - save *all* registers on the stack except PC and r_stk
   - prepare the return capability
   - prepare the stack capability in r_stk for a new frame
   - push the return capability
   - push all arguments
   - clear all registers except PC, r and r_stk
   - jmp r *)

Section call.

  Context `{MachineParameters}.
  Parameter r_stk: RegName.

  (* Clearing a list of registers *)
  Definition rclear_instrs (r : list RegName): list Word := map (λ r_i, inl (encodeInstr (Mov r_i (inl 0%Z)))) r.

  (* Push instruction *)
  Definition push_instrs ρs: list Word := map (fun ρ => inl (encodeInstr (StoreU r_stk (inl 0%Z) ρ))) ρs.

  (* Pop instruction *)
  Definition pop_instrs r: list Word := [inl (encodeInstr (LoadU r r_stk (inl (-1)%Z))); inl (encodeInstr (Lea r_stk (inl (-1)%Z)))].

  (* Push all registers except r_stk and PC *)
  Definition push_env_instrs: list Word :=
    push_instrs (map (fun r => inr r) (list_difference all_registers [PC; r_stk])).

  (* Pop all registers except r_stk and PC, must be reverse order from push *)
  Definition pop_env_instrs: list Word :=
    foldl (fun b r => (pop_instrs r) ++ b) [] (list_difference all_registers [PC; r_stk]).

  (* Code for call macro *)
  Definition call_instrs r rargs: list Word :=
    push_env_instrs
    ++ [(* TODO: prepare return capability *)]
    ++ [(* TODO: prepare stack capability *)]
    ++ [(* TODO: push return capability *)]
    ++ push_instrs (map (fun r => inr r) rargs)
    ++ rclear_instrs (list_difference all_registers [PC; r; r_stk])
    ++ [inl (encodeInstr (Jmp r))]
    ++ pop_env_instrs.

End call.
