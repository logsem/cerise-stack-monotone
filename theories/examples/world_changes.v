From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel fundamental region_invariants_batch_uninitialized region_invariants_revocation region_invariants_static.
From cap_machine Require Export iris_extra addr_reg_sample region_macros contiguous stack_macros_helpers.
From cap_machine Require Import macros.

(**
   This file contains quality of life lemmas about world manipulations,
   and validity in general,
   for the purpose of examples.
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

  Definition readAllowedWord (w : Word) :=
    match w with
    | inl _ => false
    | inr (p,_,_,_,_) => readAllowed p
    end.
  Definition readAllowedUWord (w : Word) :=
    match w with
    | inl _ => false
    | inr (p,_,_,_,_) => readAllowedU p
    end.

  Definition read_region (w : Word) :=
    match w with
    | inl _ => []
    | inr (p,_,b,e,a) => if readAllowed p then region_addrs b e
                        else if readAllowedU p then region_addrs b a
                             else []
    end.

  (* If the monotonicity condition holds for some w with validity as the invariant,
     we can infer certain bounds restrictions on that word *)
  Lemma interp_monotonicity_bounds W a w :
    interp W w -∗ future_pub_a_mono a interpC w -∗ ⌜(aOf w <= a)%a⌝ ∨ future_priv_mono interpC w.
  Proof.
    iIntros "#Hval #Hmono".
    destruct w as [z|c].
    { iRight. iAlways. iIntros (W1 W2 Hrelated) "#Hval' /=". rewrite !fixpoint_interp1_eq. eauto. }
    destruct c as [ [ [ [p g] b] e] a'].
    destruct (read_region (inr (p,g,b,e,a'))) eqn:Hlist.
    { destruct (readAllowedU p) eqn:HraU.
      - rewrite /read_region in Hlist.
        assert (readAllowed p = false) as Hfalse;[destruct p;auto;inversion HraU|].
        rewrite HraU Hfalse in Hlist. iSimpl.
        assert (isU p = true) as HU;[destruct p;auto;inversion HraU|].
        rewrite HU. destruct (decide (a' <= e)%a).
    (*     iRight. iAlways. iIntros (W1 W2 Hrelated) "#Hval' /=". *)
    (*     rewrite !fixpoint_interp1_eq. *)
    (*     assert (region_addrs b (addr_reg.min a' e) = []) as Hnil1. *)
    (*     { destruct (decide (addr_reg.min a' e = a'));[rewrite e0;auto|]. *)
    (*       rewrite (region_addrs_split2 _ _ a) in Hlist. *)
    (*       assert (addr_reg.min a' e = e) as ->;[solve_addr|]. *)
    (*       apply region_addrs_empty. solve_addr. } *)
    (*     assert (region_addrs (addr_reg.max b a') e = []) as Hnil2. *)
    (*     destruct p;inversion HraU;iSimpl;auto. *)

    (*     all: destruct g;simpl;try done. *)



    (*   iAlways. iIntros (W1 W2 Hrelated) "#Hval' /=". *)
    (*   simpl in Hlist. destruct (readAllowed p) eqn:Hra. *)
    (*   - rewrite !fixpoint_interp1_eq. *)
    (*     destruct p;inversion Hra;iSimpl;rewrite Hlist;auto. *)
    (*     all: destruct g;simpl;done. *)
    (*   - destruct (readAllowedU p) eqn:HraU. *)
    (*     + rewrite !fixpoint_interp1_eq. *)
    (*       destruct p;inversion HraU;iSimpl;auto. *)
    (*       all: destruct g;simpl;try done. *)

        (* } *)
  Abort.

End world.
