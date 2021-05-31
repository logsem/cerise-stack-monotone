From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules.
From cap_machine.binary_model Require Import logrel_binary fundamental_binary region_invariants_batch_uninitialized_binary.
From cap_machine Require Export iris_extra addr_reg_sample contiguous stack_macros_helpers. macros.

Section lse.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.


  Definition lse_instrs f_a :=
    prepstackU_instrs r_stk 1 1 ++
    [loadU_r_z r_t0 r_stk (-1); (* since parameters are passer on the stack, no need to check that the input is below the stack bound *)
    pushU_r_instr r_stk r_env;
    load_r r_env r_env] ++
    assert_r_z_instrs f_a r_env 2 ++
    rclear_instrs (list_difference all_registers [PC;r_t0]) ++
    [jmp r_t0].

  Definition lse a f_a :=
    ([∗ list] a_i;w_i ∈ a;(lse_instrs f_a), a_i ↦ₐ w_i)%I.

  Definition lse_inv d : iProp Σ := d ↦ₐ inl 2%Z.


  Lemma lse_spec W pc_p pc_g pc_b pc_e (* PC *)
        lse_addrs (* program addresses *)
        d d' (* dynamically allocated memory given by preamble, connected to invariant i *)
        a_first a_last (* special adresses *)
        f_a b_link e_link a_link a_entry fail_cap (* linking table variables *)
        wstk (* stack *)
        rmap (* registers *)
        ι1 ι2 (* invariant names *) :

    (* PC assumptions *)
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last ->

    (* Program adresses assumptions *)
    contiguous_between lse_addrs a_first a_last ->

    (* Linking table assumptions *)
    withinBounds (RW, Global, b_link, e_link, a_entry) = true →
    (a_link + f_a)%a = Some a_entry ->

    (* malloc'ed memory assumption *)
    (d + 1)%a = Some d' ->

    (* footprint of the register map *)
    dom (gset RegName) rmap = all_registers_s ∖ {[PC;r_stk;r_env]} →

    (* The two invariants have different names *)
    (up_close (B:=coPset) ι2 ## ↑ι1) ->

    {{{ r_stk ↦ᵣ wstk
      ∗ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,a_first)
      ∗ r_env ↦ᵣ inr (RWX,Global,d,d',d)
      ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
      (* invariant for d *)
      ∗ (∃ ι, inv ι (lse_inv d))
      (* stack *)
      ∗ interp W wstk
      (* token which states all non atomic invariants are closed *)
      ∗ na_own logrel_nais ⊤
      (* trusted code *)
      ∗ na_inv logrel_nais ι1 (lse lse_addrs f_a)
      (* linking table *)
      ∗ na_inv logrel_nais ι2 (pc_b ↦ₐ inr (RO,Global,b_link,e_link,a_link) ∗ a_entry ↦ₐ fail_cap)
      (* we start out with arbitrary sts *)
      ∗ sts_full_world W
      ∗ region W
    }}}
      Seq (Instr Executable)
      {{{ v, RET v; ⌜v = HaltedV⌝ →
                    ∃ r W', full_map r ∧ registers_mapsto r
                         ∗ ⌜related_sts_priv_world W W'⌝
                         ∗ na_own logrel_nais ⊤
                         ∗ sts_full_world W'
                         ∗ region W' }}}.
  Proof.
