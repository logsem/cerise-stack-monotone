From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel fundamental region_invariants_revocation region_invariants_static region_invariants_batch_uninitialized.
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

  Definition stack_object_passing_instrs stack_obj :=
    (* we check that the function pointer is global *)
    reqglob_instrs r_adv ++
    (* we must do some dynamic checks on the input object *)
    checkra_instrs r_param1 ++
    checkints_instrs r_param1 r_t1 r_t2 r_t3 ++
    (* prepare the stack *)
    prepstackU_instrs r_stk 9 ++
    checkbelow_instrs r_t0 r_stk ++
    (* we can begin the function *)
    [pushU_z_instr r_stk stack_obj;
    move_r r_param2 r_stk;
    promoteU r_param2;
    (* push the local state *)
    pushU_r_instr r_stk r_t0] ++
    (* call r_adv *)
    scallU_prologue_instrs r_adv [r_param1;r_param2] ++
    [ jmp r_adv;
    (* restore local state *)
    lea_z r_stk (-6)] ++
    popU_instrs r_stk r_t0 ++
    (* we leave everything on the stack *)
    rclear_instrs (list_difference all_registers [PC;r_t0]) ++
    [jmp r_t0].

  Definition stack_object_passing a p f_a :=
    ([∗ list] a_i;w_i ∈ a;(stack_object_passing_instrs f_a), a_i ↦ₐ[p] w_i)%I.
  



End stack_object.
