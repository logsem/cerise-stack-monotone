From iris.algebra Require Import base.
From iris.program_logic Require Import language ectx_language ectxi_language.
From stdpp Require Import gmap fin_maps list.
From cap_machine Require Export addr_reg machine_base machine_parameters.

Inductive Cap: Type :=
| Regular: machine_base.Cap -> Cap (* Regular capabilities *)
| Stk: nat -> Perm -> Addr -> Addr -> Addr -> Cap (* Stack derived capabilities *)
| Ret: nat -> Addr -> Addr -> Addr -> Cap. (* Return capabilities *)

Coercion Regular : machine_base.Cap >-> Cap.

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

Inductive ConfFlag : Type :=
| Executable
| Halted
| Failed
| NextI.

Definition Conf: Type := ConfFlag * ExecConf.

Definition update_reg (ϕ: ExecConf) (r: RegName) (w: Word): ExecConf := (<[r:=w]>(reg ϕ), mem ϕ, stk ϕ, callstack ϕ).
Definition update_mem (φ: ExecConf) (a: Addr) (w: Word): ExecConf := (reg φ, <[a:=w]>(mem φ), stk φ, callstack φ).
Definition update_stk (φ: ExecConf) (a: Addr) (w: Word): ExecConf := (reg φ, mem φ, <[a:=w]> (stk φ), callstack φ).
Fixpoint update_callstack (cs: list Stackframe) (d: nat) (a: Addr) (w: Word): option (list Stackframe) :=
  match cs with
  | sf::cs => if nat_eq_dec d (length cs) then Some ((fst sf, <[a := w]> (snd sf))::cs)
             else match update_callstack cs d a w with
                  | None => None
                  | Some cs => Some (sf::cs)
                  end
  | [] => None
  end.
Definition update_stack (φ: ExecConf) (d: nat) (a: Addr) (w: Word): option ExecConf :=
  match update_callstack (callstack φ) d a w with
  | None => None
  | Some cs => Some (reg φ, mem φ, stk φ, cs)
  end.

Definition updatePC (φ: ExecConf): Conf :=
  match RegLocate (reg φ) PC with
  | inr (Regular ((p, g), b, e, a)) =>
    match (a + 1)%a with
    | Some a' => let φ' := (update_reg φ PC (inr (Regular ((p, g), b, e, a')))) in
                 (NextI, φ')
    | None => (Failed, φ)
    end
  | inr (Stk d p b e a) =>
    match (a + 1)%a with
    | Some a' => let φ' := (update_reg φ PC (inr (Stk d p b e a'))) in
                 (NextI, φ')
    | None => (Failed, φ)
    end
  | _ => (Failed, φ)
  end.

Definition updatePcPerm (w: Word): Word :=
  match w with
  | inr (Regular ((E, g), b, e, a)) => inr (Regular ((RX, g), b, e, a))
  | inr (Stk d E b e a) => inr (Stk d RX b e a)
  | _ => w
  end.

Fixpoint jmp_ret (d: nat) (cs: list Stackframe) :=
  match cs with
  | sf::cs => if nat_eq_dec d (length cs) then Some (sf, cs) else jmp_ret d cs
  | [] => None
  end.

Fixpoint stack (d: nat) (cs: list Stackframe) :=
  match cs with
  | sf::cs => if nat_eq_dec d (length cs) then Some (snd sf) else stack d cs
  | [] => None
  end.

Definition nonZero (w: Word): bool :=
  match w with
  | inr _ => true
  | inl n => Zneq_bool n 0
  end.

Definition canReadUpTo (w: Word): Addr :=
  match w with
  | inl _ => za
  | inr (Regular ((p, g), b, e, a)) => match p with
                                      | O => za
                                      | RO | RW | RWL | RX | RWX | RWLX | E => e
                                      | URW | URWL | URWX | URWLX => a
                                      end
  | inr (Stk d p b e a) => match p with
                          | O => za
                          | RO | RW | RWL | RX | RWX | RWLX | E => e
                          | URW | URWL | URWX | URWLX => a
                          end
  | inr (Ret d b e a) => e
  end.

Definition canStore (p: Perm) (a: Addr) (w: Word): bool :=
  match w with
  | inl _ => true
  | inr (Regular ((_, g), _, _, _)) => match g with
                                      | Global => true
                                      | Local => pwl p
                                      | Monotone => pwl p && leb_addr (canReadUpTo w) a
                                      end
  | inr (Stk _ _ _ _ _) | inr (Ret _ _ _ _) => pwl p && leb_addr (canReadUpTo w) a
  end.

Definition canStoreU (p: Perm) (a: Addr) (w: Word): bool :=
  match w with
  | inl _ => true
  | inr (Regular ((_, g), _, _, _)) => match g with
                                      | Global => true
                                      | Local => pwlU p
                                      | Monotone => pwlU p && leb_addr (canReadUpTo w) a
                                      end
  | inr (Stk _ _ _ _ _) | inr (Ret _ _ _ _) => pwlU p && leb_addr (canReadUpTo w) a
  end.

Definition isWithin (n1 n2 b e: Addr) : bool :=
  ((b <=? n1) && (n2 <=? e))%a.

Inductive access_kind: Type :=
| LoadU_access (b e a: Addr) (offs: Z): access_kind
| StoreU_access (b e a: Addr) (offs: Z): access_kind.

Definition verify_access (a: access_kind): option Addr :=
  match a with
  | LoadU_access b e a offs =>
    match (a + offs)%a with
    | None => None
    | Some a' => if Addr_le_dec b a' then
                  if Addr_lt_dec a' a then
                    if Addr_le_dec a e then
                      Some a' else None else None else None
    end
  | StoreU_access b e a offs =>
    match (a + offs)%a with
    | None => None
    | Some a' => if Addr_le_dec b a' then
                  if Addr_le_dec a' a then
                    if Addr_lt_dec a e then
                      Some a' else None else None else None
    end
  end.

Definition z_of_argument (regs: Reg) (a: Z + RegName) : option Z :=
  match a with
  | inl z => Some z
  | inr r =>
    match regs !! r with
    | Some (inl z) => Some z
    | _ => None
    end
  end.

Inductive isCorrectPC: Word → Prop :=
| isCorrectPC_intro:
    forall p g (b e a : Addr),
      (b <= a < e)%a →
      p = RX \/ p = RWX \/ p = RWLX →
      isCorrectPC (inr (Regular ((p, g), b, e, a)))
| isCorrectPC_intro':
    forall d p (b e a : Addr),
      (b <= a < e)%a →
      p = RX \/ p = RWX \/ p = RWLX →
      isCorrectPC (inr (Stk d p b e a)).

Section opsem.
  Context `{MachineParameters}.

  Definition exec (i: instr) (φ: ExecConf): Conf :=
    match i with
    | Fail => (Failed, φ)
    | Halt => (Halted, φ)
    | Jmp r =>
      match (RegLocate (reg φ) r) with
      | inr (Ret d b e a) => match jmp_ret d (callstack φ) with
                            | None => (Failed, φ)
                            | Some ((reg', m'), cs) => (NextI, (merge (fun a b => match a with Some _ => a | _ => b end) reg' (reg φ), mem φ, m', cs))
                                                        (* TODO: this is not safe if registers are not cleared beforehands *)
                      end
      | _ => let φ' :=  (update_reg φ PC (updatePcPerm (RegLocate (reg φ) r))) in (NextI, φ')
      end
    | Jnz r1 r2 =>
      if nonZero (RegLocate (reg φ) r2) then
        match (RegLocate (reg φ) r1) with
        | inr (Ret d b e a) => match jmp_ret d (callstack φ) with
                              | None => (Failed, φ)
                              | Some ((reg', m'), cs) => (NextI, (merge (fun a b => match a with Some _ => a | _ => b end) reg' (reg φ), mem φ, m', cs))
                              end
        | _ => let φ' := (update_reg φ PC (updatePcPerm (RegLocate (reg φ) r1))) in (NextI, φ')
        end
      else updatePC φ
    | Load dst src =>
      match RegLocate (reg φ) src with
      | inl n => (Failed, φ)
      | inr (Regular ((p, g), b, e, a)) =>
        (* Fails for U cap *)
        if readAllowed p && withinBounds ((p, g), b, e, a) then updatePC (update_reg φ dst (MemLocate (mem φ) a))
        else (Failed, φ)
      | inr (Ret d b e a) => (Failed, φ)
      | inr (Stk d p b e a) =>
        if readAllowed p && withinBounds ((p, Monotone), b, e, a) then
          match stack d ((reg φ, stk φ)::(callstack φ)) with
          | None => (Failed, φ)
          | Some m => updatePC (update_reg φ dst (MemLocate m a))
          end
        else (Failed, φ)
      end
    | Store dst (inr src) =>
      match RegLocate (reg φ) dst with
      | inl n => (Failed, φ)
      | inr (Regular ((p, g), b, e, a)) =>
        (* Fails for U cap *)
        if writeAllowed p && withinBounds ((p, g), b, e, a) && canStore p a (RegLocate (reg φ) src) then
          updatePC (update_mem φ a (RegLocate (reg φ) src))
        else (Failed, φ)
      | inr (Ret d b e a) => (Failed, φ)
      | inr (Stk d p b e a) =>
        if nat_eq_dec d (length (callstack φ)) then
          updatePC (update_stk φ a (RegLocate (reg φ) src))
        else match update_stack φ d a (RegLocate (reg φ) src) with
             | None => (Failed, φ)
             | Some φ' => updatePC φ'
             end
      end
    | Store dst (inl n) =>
      match RegLocate (reg φ) dst with
      | inl n => (Failed, φ)
      | inr (Regular ((p, g), b, e, a)) =>
        (* Fails for U cap *)
        if writeAllowed p && withinBounds ((p, g), b, e, a) then updatePC (update_mem φ a (inl n)) else (Failed, φ)
      | inr (Ret d b e a) => (Failed, φ)
      | inr (Stk d p b e a) =>
        if nat_eq_dec d (length (callstack φ)) then
          updatePC (update_stk φ a (inl n))
        else match update_stack φ d a (inl n) with
             | None => (Failed, φ)
             | Some φ' => updatePC φ'
             end
      end
    | Mov dst (inl n) => updatePC (update_reg φ dst (inl n))
    | Mov dst (inr src) => updatePC (update_reg φ dst (RegLocate (reg φ) src))
    | Lea dst (inl n) =>
      match RegLocate (reg φ) dst with
      | inl _ => (Failed, φ)
      | inr (Regular ((p, g), b, e, a)) =>
        match p with
        | E => (Failed, φ)
        (* Make sure that we can only decrease pointer for uninitialized capabilities *)
        | URW | URWL | URWX | URWLX => match (a + n)%a with
                                      | Some a' => if Addr_le_dec a' a then
                                                    let c := Regular ((p, g), b, e, a') in
                                                    updatePC (update_reg φ dst (inr c))
                                                  else (Failed, φ)
                                      | None => (Failed, φ)
                                      end
        | _ => match (a + n)%a with
               | Some a' => let c := Regular ((p, g), b, e, a') in
                            updatePC (update_reg φ dst (inr c))
               | None => (Failed, φ)
               end
        end
      | inr (Ret d b e a) => (Failed, φ)
      | inr (Stk d p b e a) =>
        match p with
        | E => (Failed, φ)
        (* Make sure that we can only decrease pointer for uninitialized capabilities *)
        | URW | URWL | URWX | URWLX => match (a + n)%a with
                                      | Some a' => if Addr_le_dec a' a then
                                                    let c := Stk d p b e a' in
                                                    updatePC (update_reg φ dst (inr c))
                                                  else (Failed, φ)
                                      | None => (Failed, φ)
                                      end
        | _ => match (a + n)%a with
               | Some a' => let c := Stk d p b e a' in
                            updatePC (update_reg φ dst (inr c))
               | None => (Failed, φ)
               end
        end
      end
    | Lea dst (inr r) =>
      match RegLocate (reg φ) dst with
      | inl _ => (Failed, φ)
      | inr (Regular ((p, g), b, e, a)) =>
        match p with
        | E => (Failed, φ)
        (* Make sure that we can only decrease pointer for uninitialized capabilities *)
        | URW | URWL | URWX | URWLX => match RegLocate (reg φ) r with
                                      | inr _ => (Failed, φ)
                                      | inl n => match (a + n)%a with
                                                | Some a' => if Addr_le_dec a' a then
                                                              let c := Regular ((p, g), b, e, a') in
                                                              updatePC (update_reg φ dst (inr c))
                                                            else (Failed, φ)
                                                | None => (Failed, φ)
                                                end
                                      end
        | _ => match RegLocate (reg φ) r with
              | inr _ => (Failed, φ)
              | inl n => match (a + n)%a with
                        | Some a' => let c := Regular ((p, g), b, e, a') in
                                    updatePC (update_reg φ dst (inr c))
                        | None => (Failed, φ)
                        end
              end
        end
      | inr (Ret d b e a) => (Failed, φ)
      | inr (Stk d p b e a) =>
        match p with
        | E => (Failed, φ)
        (* Make sure that we can only decrease pointer for uninitialized capabilities *)
        | URW | URWL | URWX | URWLX => match RegLocate (reg φ) r with
                                      | inr _ => (Failed, φ)
                                      | inl n => match (a + n)%a with
                                                | Some a' => if Addr_le_dec a' a then
                                                              let c := Stk d p b e a' in
                                                              updatePC (update_reg φ dst (inr c))
                                                            else (Failed, φ)
                                                | None => (Failed, φ)
                                                end
                                      end
        | _ => match RegLocate (reg φ) r with
              | inr _ => (Failed, φ)
              | inl n => match (a + n)%a with
                        | Some a' => let c := Stk d p b e a' in
                                    updatePC (update_reg φ dst (inr c))
                        | None => (Failed, φ)
                        end
              end
        end
      end
    | Restrict dst (inl n) =>
      match RegLocate (reg φ) dst with
      | inl _ => (Failed, φ)
      | inr (Regular (permPair, b, e, a)) =>
        match permPair with
        | (E, _) => (Failed, φ)
        | _ => if PermPairFlowsTo (decodePermPair n) permPair then
                updatePC (update_reg φ dst (inr (Regular (decodePermPair n, b, e, a))))
              else (Failed, φ)
        end
      | inr (Ret _ _ _ _) => (Failed, φ)
      | inr (Stk d p b e a) =>
        match p with
        | E => (Failed, φ)
        | _ => if PermPairFlowsTo (decodePermPair n) (p, Monotone) then
                                updatePC (update_reg φ dst (inr (Stk d (fst (decodePermPair n)) b e a)))
              else (Failed, φ)
        end
      end
    | Restrict dst (inr r) =>
      match RegLocate (reg φ) dst with
      | inl _ => (Failed, φ)
      | inr (Regular (permPair, b, e, a)) =>
        match RegLocate (reg φ) r with
        | inr _ => (Failed, φ)
        | inl n =>
          match permPair with
          | (E, _) => (Failed, φ)
          | _ => if PermPairFlowsTo (decodePermPair n) permPair then
                  updatePC (update_reg φ dst (inr (Regular (decodePermPair n, b, e, a))))
                else (Failed, φ)
          end
        end
      | inr (Ret _ _ _ _) => (Failed, φ)
      | inr (Stk d p b e a) =>
        match RegLocate (reg φ) r with
        | inr _ => (Failed, φ)
        | inl n =>
          match p with
          | E => (Failed, φ)
          | _ => if PermPairFlowsTo (decodePermPair n) (p, Monotone) then
                  updatePC (update_reg φ dst (inr (Stk d (fst (decodePermPair n)) b e a)))
                else (Failed, φ)
          end
        end
      end
    | Add dst (inr r1) (inr r2) =>
      match RegLocate (reg φ) r1 with
      | inr _ => (Failed, φ)
      | inl n1 => match RegLocate (reg φ) r2 with
                 | inr _ => (Failed, φ)
                 | inl n2 => updatePC (update_reg φ dst (inl (n1 + n2)%Z))
                 end
      end
    | Add dst (inl n1) (inr r2) =>
      match RegLocate (reg φ) r2 with
      | inr _ => (Failed, φ)
      | inl n2 => updatePC (update_reg φ dst (inl (n1 + n2)%Z))
      end
    | Add dst (inr r1) (inl n2) =>
      match RegLocate (reg φ) r1 with
      | inr _ => (Failed, φ)
      | inl n1 => updatePC (update_reg φ dst (inl (n1 + n2)%Z))
      end
    | Add dst (inl n1) (inl n2) =>
      updatePC (update_reg φ dst (inl (n1 + n2)%Z))
    | Sub dst (inr r1) (inr r2) =>
      match RegLocate (reg φ) r1 with
      | inr _ => (Failed, φ)
      | inl n1 => match RegLocate (reg φ) r2 with
                 | inr _ => (Failed, φ)
                 | inl n2 => updatePC (update_reg φ dst (inl (n1 - n2)%Z))
                 end
      end
    | Sub dst (inl n1) (inr r2) =>
      match RegLocate (reg φ) r2 with
      | inr _ => (Failed, φ)
      | inl n2 => updatePC (update_reg φ dst (inl (n1 - n2)%Z))
      end
    | Sub dst (inr r1) (inl n2) =>
      match RegLocate (reg φ) r1 with
      | inr _ => (Failed, φ)
      | inl n1 => updatePC (update_reg φ dst (inl (n1 - n2)%Z))
      end
    | Sub dst (inl n1) (inl n2) =>
      updatePC (update_reg φ dst (inl (n1 - n2)%Z))
    | Lt dst (inr r1) (inr r2) =>
      match RegLocate (reg φ) r1 with
      | inr _ => (Failed, φ)
      | inl n1 => match RegLocate (reg φ) r2 with
                 | inr _ => (Failed, φ)
                 | inl n2 => updatePC (update_reg φ dst (inl (Z.b2z (Z.ltb n1 n2))))
                 end
      end
    | Lt dst (inl n1) (inr r2) =>
      match RegLocate (reg φ) r2 with
      | inr _ => (Failed, φ)
      | inl n2 => updatePC (update_reg φ dst (inl (Z.b2z (Z.ltb n1 n2))))
      end
    | Lt dst (inr r1) (inl n2) =>
      match RegLocate (reg φ) r1 with
      | inr _ => (Failed, φ)
      | inl n1 => updatePC (update_reg φ dst (inl (Z.b2z (Z.ltb n1 n2))))
      end
    | Lt dst (inl n1) (inl n2) =>
      updatePC (update_reg φ dst (inl (Z.b2z (Z.ltb n1 n2))))
    | Subseg dst (inr r1) (inr r2) =>
      match RegLocate (reg φ) dst with
      | inl _ => (Failed, φ)
      | inr (Regular ((p, g), b, e, a)) =>
        match p with
        | E => (Failed, φ)
        | _ =>
          match RegLocate (reg φ) r1 with
          | inr _ => (Failed, φ)
          | inl n1 =>
            match RegLocate (reg φ) r2 with
            | inr _ => (Failed, φ)
            | inl n2 =>
              match z_to_addr n1, z_to_addr n2 with
              | Some a1, Some a2 =>
                if isWithin a1 a2 b e then
                  updatePC (update_reg φ dst (inr (Regular ((p, g), a1, a2, a))))
                else (Failed, φ)
              | _,_ => (Failed, φ)
              end
            end
          end
        end
      | inr (Ret _ _ _ _) => (Failed, φ)
      | inr (Stk d p b e a) =>
        match p with
        | E => (Failed, φ)
        | _ =>
          match RegLocate (reg φ) r1 with
          | inr _ => (Failed, φ)
          | inl n1 =>
            match RegLocate (reg φ) r2 with
            | inr _ => (Failed, φ)
            | inl n2 =>
              match z_to_addr n1, z_to_addr n2 with
              | Some a1, Some a2 =>
                if isWithin a1 a2 b e then
                  updatePC (update_reg φ dst (inr (Stk d p a1 a2 a)))
                else (Failed, φ)
              | _,_ => (Failed, φ)
              end
            end
          end
        end
      end
    | Subseg dst (inl n1) (inr r2) =>
      match RegLocate (reg φ) dst with
      | inl _ => (Failed, φ)
      | inr (Regular ((p, g), b, e, a)) =>
        match p with
        | E => (Failed, φ)
        | _ =>
          match RegLocate (reg φ) r2 with
          | inr _ => (Failed, φ)
          | inl n2 =>
            match z_to_addr n1, z_to_addr n2 with
            | Some a1, Some a2 =>
              if isWithin a1 a2 b e then
                updatePC (update_reg φ dst (inr (Regular ((p, g), a1, a2, a))))
                     else (Failed, φ)
            | _,_ => (Failed, φ)
            end
          end
        end
      | inr (Ret _ _ _ _) => (Failed, φ)
      | inr (Stk d p b e a) =>
        match p with
        | E => (Failed, φ)
        | _ =>
          match RegLocate (reg φ) r2 with
          | inr _ => (Failed, φ)
          | inl n2 =>
            match z_to_addr n1, z_to_addr n2 with
            | Some a1, Some a2 =>
              if isWithin a1 a2 b e then
                updatePC (update_reg φ dst (inr (Stk d p a1 a2 a)))
                     else (Failed, φ)
            | _,_ => (Failed, φ)
            end
          end
        end
      end
    | Subseg dst (inr r1) (inl n2) =>
      match RegLocate (reg φ) dst with
      | inl _ => (Failed, φ)
      | inr (Regular ((p, g), b, e, a)) =>
        match p with
        | E => (Failed, φ)
        | _ =>
          match RegLocate (reg φ) r1 with
          | inr _ => (Failed, φ)
          | inl n1 =>
            match z_to_addr n1, z_to_addr n2 with
            | Some a1, Some a2 =>
              if isWithin a1 a2 b e then
                updatePC (update_reg φ dst (inr (Regular ((p, g), a1, a2, a))))
              else (Failed, φ)
            | _,_ => (Failed, φ)
            end
          end
        end
      | inr (Ret _ _ _ _) => (Failed, φ)
      | inr (Stk d p b e a) =>
        match p with
        | E => (Failed, φ)
        | _ =>
          match RegLocate (reg φ) r1 with
          | inr _ => (Failed, φ)
          | inl n1 =>
            match z_to_addr n1, z_to_addr n2 with
            | Some a1, Some a2 =>
              if isWithin a1 a2 b e then
                updatePC (update_reg φ dst (inr (Stk d p a1 a2 a)))
              else (Failed, φ)
            | _,_ => (Failed, φ)
            end
          end
        end
      end
    | Subseg dst (inl n1) (inl n2) =>
      match RegLocate (reg φ) dst with
      | inl _ => (Failed, φ)
      | inr (Regular ((p, g), b, e, a)) =>
        match p with
        | E => (Failed, φ)
        | _ =>
          match z_to_addr n1, z_to_addr n2 with
          | Some a1, Some a2 =>
            if isWithin a1 a2 b e then
              updatePC (update_reg φ dst (inr (Regular ((p, g), a1, a2, a))))
            else (Failed, φ)
          | _,_ => (Failed, φ)
          end
        end
      | inr (Ret _ _ _ _) => (Failed, φ)
      | inr (Stk d p b e a) =>
        match p with
        | E => (Failed, φ)
        | _ =>
          match z_to_addr n1, z_to_addr n2 with
          | Some a1, Some a2 =>
            if isWithin a1 a2 b e then
              updatePC (update_reg φ dst (inr (Stk d p a1 a2 a)))
            else (Failed, φ)
          | _,_ => (Failed, φ)
          end
        end
      end
    | GetA dst r =>
      match RegLocate (reg φ) r with
      | inl _ => (Failed, φ)
      | inr (Regular (_, _, _, a)) | inr (Ret _ _ _ a) | inr (Stk _ _ _ _ a) =>
        match a with
        | A a' _ _ => updatePC (update_reg φ dst (inl a'))
        end
      end
    | GetB dst r =>
      match RegLocate (reg φ) r with
      | inl _ => (Failed, φ)
      | inr (Regular (_, b, _, _)) | inr (Ret _ b _ _) | inr (Stk _ _ b _ _) =>
        match b with
        | A b' _ _ => updatePC (update_reg φ dst (inl b'))
        end
      end
    | GetE dst r =>
      match RegLocate (reg φ) r with
      | inl _ => (Failed, φ)
      | inr (Regular (_, _, e, _)) | inr (Ret _ _ e _) | inr (Stk _ _ _ e _) =>
        match e with
        | A e' _ _ => updatePC (update_reg φ dst (inl e'))
        end
      end
    | GetP dst r =>
      match RegLocate (reg φ) r with
      | inl _ => (Failed, φ)
      | inr (Regular ((p, _), _, _, _))
      | inr (Stk _ p _ _ _) =>
        updatePC (update_reg φ dst (inl (encodePerm p)))
      | inr (Ret _ _ _ _) =>
        updatePC (update_reg φ dst (inl (encodePerm E)))
      end
    | GetL dst r =>
      match RegLocate (reg φ) r with
      | inl _ => (Failed, φ)
      | inr (Regular ((_, g), _, _, _)) => updatePC (update_reg φ dst (inl (encodeLoc g)))
      | inr (Stk _ _ _ _ _)
      | inr (Ret _ _ _ _) =>
        updatePC (update_reg φ dst (inl (encodeLoc Monotone)))
      end
    | IsPtr dst r =>
      match RegLocate (reg φ) r with
      | inl _ => updatePC (update_reg φ dst (inl 0%Z))
      | inr _ => updatePC (update_reg φ dst (inl 1%Z))
      end
    | LoadU rdst rsrc offs =>
      match RegLocate (reg φ) rsrc with
      | inl _ => (Failed, φ)
      | inr (Regular ((p, g), b, e, a)) =>
        if isU p then
          match z_of_argument (reg φ) offs with
          | None => (Failed, φ)
          | Some noffs => match verify_access (LoadU_access b e a noffs) with
                         | None => (Failed, φ)
                         | Some a' => updatePC (update_reg φ rdst (MemLocate (mem φ) a'))
                         end
          end
        else (Failed, φ)
      | inr (Ret _ _ _ _) => (Failed, φ)
      | inr (Stk d p b e a) =>
        if isU p then
          match z_of_argument (reg φ) offs with
          | None => (Failed, φ)
          | Some noffs => match verify_access (LoadU_access b e a noffs) with
                         | None => (Failed, φ)
                         | Some a' => match stack d ((reg φ, stk φ)::(callstack φ)) with
                                     | None => (Failed, φ)
                                     | Some m => updatePC (update_reg φ rdst (MemLocate m a'))
                                     end
                         end
          end
        else (Failed, φ)
      end
    | StoreU dst offs src =>
      let w := match src with
               | inl n => inl n
               | inr rsrc => (RegLocate (reg φ) rsrc)
               end in
      match RegLocate (reg φ) dst with
      | inl _ => (Failed, φ)
      | inr (Regular ((p, g), b, e, a)) =>
        match z_of_argument (reg φ) offs with
        | None => (Failed, φ)
        | Some noffs => match verify_access (StoreU_access b e a noffs) with
                       | None => (Failed, φ)
                       | Some a' => if isU p && canStoreU p a' w then
                                     if addr_eq_dec a a' then
                                       match (a + 1)%a with
                                       | Some a => updatePC (update_reg (update_mem φ a' w) dst (inr (Regular ((p, g), b, e, a))))
                                       | None => (Failed, φ)
                                       end
                                     else updatePC (update_mem φ a' w)
                                   else (Failed, φ)
                       end
        end
      | inr (Ret _ _ _ _) => (Failed, φ)
      | inr (Stk d p b e a) =>
        match z_of_argument (reg φ) offs with
        | None => (Failed, φ)
        | Some noffs => match verify_access (StoreU_access b e a noffs) with
                       | None => (Failed, φ)
                       | Some a' => if isU p && canStoreU p a' w then
                                     if addr_eq_dec a a' then
                                       match (a + 1)%a with
                                       | Some a =>
                                         if nat_eq_dec d (length (callstack φ)) then
                                           updatePC (update_reg (update_stk φ a' w) dst (inr (Stk d p b e a)))
                                         else match update_stack φ d a' w with
                                              | None => (Failed, φ)
                                              | Some φ' => updatePC (update_reg φ' dst (inr (Stk d p b e a)))
                                              end
                                       | None => (Failed, φ)
                                       end
                                     else updatePC (update_mem φ a' w)
                                   else (Failed, φ)
                       end
        end
      end
    | PromoteU dst =>
      match RegLocate (reg φ) dst with
      | inr (Regular ((p, g), b, e, a)) =>
        if perm_eq_dec p E then (Failed, φ)
        else updatePC (update_reg φ dst (inr (Regular ((promote_perm p, g), b, min a e, a))))
      | inr (Ret _ _ _ _) => (Failed, φ)
      | inr (Stk d p b e a) =>
        if perm_eq_dec p E then (Failed, φ)
        else updatePC (update_reg φ dst (inr (Stk d (promote_perm p) b e a)))
      | inl _ => (Failed, φ)
      end
    end.

  Inductive step: Conf → Conf → Prop :=
  | step_exec_fail:
      forall φ,
        not (isCorrectPC ((reg φ) !r! PC)) →
        step (Executable, φ) (Failed, φ)
  | step_exec_instr:
      forall φ p g b e a i c,
        RegLocate (reg φ) PC = inr (Regular ((p, g), b, e, a)) ->
        isCorrectPC ((reg φ) !r! PC) →
        decodeInstrW ((mem φ) !m! a) = i →
        exec i φ = c →
        step (Executable, φ) (c.1, c.2).





