From iris.algebra Require Import base.
From iris.program_logic Require Import language ectx_language ectxi_language.
From stdpp Require Import gmap fin_maps list finite.
From cap_machine Require Export addr_reg machine_base machine_parameters.

Inductive Cap: Type :=
| Regular: machine_base.Cap -> Cap (* Regular capabilities *)
| Stk: nat -> Perm -> Addr -> Addr -> Addr -> Cap (* Stack derived capabilities *)
| Ret: nat -> Addr -> Addr -> Addr -> Cap. (* Return capabilities *)

Instance cap_eq_dec : EqDecision Cap.
Proof. solve_decision. Defined.
Instance word_eq_dec : EqDecision Word.
Proof. solve_decision. Defined.

Definition Word := (Z + Cap)%type.

Notation Reg := (gmap RegName Word).
Notation Mem := (gmap Addr Word).

Definition RegLocate (reg : Reg) (r : RegName) :=
  match (reg !! r) with
  | Some w => w
  | None => inl 0%Z
  end.

Definition MemLocate (mem : Mem) (a : Addr) :=
  match (mem !! a) with
  | Some w => w
  | None => inl 0%Z
  end.

Notation "mem !m! a" := (MemLocate mem a) (at level 20).
Notation "reg !r! r" := (RegLocate reg r) (at level 20).

Definition Stackframe := (Reg * Mem)%type.

Definition ExecConf := (Reg * Mem * Mem * list Stackframe)%type.

Definition reg (ϕ: ExecConf) :=
  match ϕ with
  | (r, _, _, _) => r
  end.

Definition mem (ϕ: ExecConf) :=
  match ϕ with
  | (_, m, _, _) => m
  end.

Definition stk (ϕ: ExecConf) :=
  match ϕ with
  | (_, _, stk, _) => stk
  end.

Definition callstack (ϕ: ExecConf) :=
  match ϕ with
  | (_, _, _, cs) => cs
  end.

Lemma ExecConfDestruct:
  forall ϕ,
    ϕ = (reg ϕ, mem ϕ, stk ϕ, callstack ϕ).
Proof. repeat destruct ϕ as (ϕ & ?). reflexivity. Qed.
