From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel fundamental region_invariants_batch_uninitialized region_invariants_revocation region_invariants_static.
From cap_machine Require Export iris_extra addr_reg_sample region_macros contiguous stack_macros_helpers.
From cap_machine Require Import macros.

(**
   This file contains quality of life lemmas about world manipulations, for the
   purpose of examples.
 *)

Section world.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          `{MonRef: MonRefG (leibnizO _) CapR_rtc Σ} {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.


  (* For example that use a dynamic type check to reinstate validity of a revoked world *)
  Lemma region_open_acc W W1 l p g b e a :
    ⊢ region W1 ∗ ([∗ list] a ∈ l, (∃ p φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗ ▷ monotemp_resources W φ a p ∗ rel a p φ) ∗ ⌜(std (revoke W)) !! a = Some Revoked⌝).




End world.
