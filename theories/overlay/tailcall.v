From iris.algebra Require Import base.
From iris.program_logic Require Import language ectx_language ectxi_language.
From stdpp Require Import gmap fin_maps list finite.
From cap_machine Require Export addr_reg machine_base machine_parameters.
From cap_machine.overlay Require Import base.

(* Tailcall r rargs implements a tailcall to r *)

Section tailcall.

  Context `{MachineParameters}.
  Definition r_stk := R 31 eq_refl.

  (* TODO later *)

End tailcall.
