From iris.algebra Require Import base.
From iris.program_logic Require Import language ectx_language ectxi_language.
From stdpp Require Import gmap fin_maps list finite.
From cap_machine Require Export addr_reg machine_base machine_parameters.

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

Lemma isCorrectPC_dec:
  forall w, { isCorrectPC w } + { not (isCorrectPC w) }.
Proof.
  destruct w.
  - right. red; intros H. inversion H.
  - destruct c.
    + destruct c as ((((p & g) & b) & e) & a).
      case_eq (match p with RX | RWX | RWLX => true | _ => false end); intros.
      * destruct (Addr_le_dec b a).
        { destruct (Addr_lt_dec a e).
          { left. econstructor; simpl; eauto. by auto.
            destruct p; naive_solver. }
          { right. red; intro HH. inversion HH; subst. solve_addr. } }
        { right. red; intros HH; inversion HH; subst. solve_addr. }
      * right. red; intros HH; inversion HH; subst. naive_solver.
    + case_eq (match p with RX | RWX | RWLX => true | _ => false end); intros.
      * destruct (Addr_le_dec a a1).
        { destruct (Addr_lt_dec a1 a0).
          { left. econstructor; simpl; eauto. by auto.
            destruct p; naive_solver. }
          { right. red; intro HH. inversion HH; subst. solve_addr. } }
        { right. red; intros HH; inversion HH; subst. solve_addr. }
      * right. red; intros HH; inversion HH; subst. naive_solver.
    + right. red; intros H. inversion H.
Qed.

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
                            | Some ((reg', m'), cs) => (NextI, (reg', mem φ, m', cs))
                            end
      | _ => let φ' :=  (update_reg φ PC (updatePcPerm (RegLocate (reg φ) r))) in (NextI, φ')
      end
    | Jnz r1 r2 =>
      if nonZero (RegLocate (reg φ) r2) then
        match (RegLocate (reg φ) r1) with
        | inr (Ret d b e a) => match jmp_ret d (callstack φ) with
                              | None => (Failed, φ)
                              | Some ((reg', m'), cs) => (NextI, (reg', mem φ, m', cs))
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

  Definition decodeInstrW' (w: Word) :=
    match w with
    | inl n => decodeInstrW (inl n)
    | inr _ => Fail
    end.

  (* Definition rclear_instrs (r : list RegName): list Word := map (λ r_i, inl (encodeInstr (Mov r_i (inl 0%Z)))) r. *)

  (* Definition return_instrs r := rclear_instrs (list_difference all_registers [PC; r]) ++ [inl (encodeInstr (Jmp r))]. *)

  (* Lemma rclear_instrs_length: *)
  (*   forall r, r <> PC -> length (rclear_instrs (list_difference all_registers [PC; r])) = RegNum. *)
  (* Proof. *)
  (*   destruct r; try congruence. *)
  (*   intros. rewrite /rclear_instrs. *)
  (*   do 32 (destruct n as [|n]; [simpl; reflexivity|]). *)
  (*   simpl in fin. discriminate. *)
  (* Qed. *)

  (* Lemma return_instrs_length: *)
  (*   forall r, r <> PC -> length (return_instrs r) = RegNum + 1. *)
  (* Proof. *)
  (*   intros. rewrite /return_instrs app_length rclear_instrs_length //. *)
  (* Qed. *)

  (* Lemma return_instrs_last: *)
  (*   forall r, *)
  (*     r <> PC -> *)
  (*     return_instrs r !! RegNum = Some (inl (encodeInstr (Jmp r))). *)
  (* Proof. *)
  (*   intros. rewrite lookup_app_r rclear_instrs_length //. *)
  (* Qed. *)

  (* Lemma return_instrs_ext_eq: *)
  (*   forall r1 r2, *)
  (*     r1 <> PC -> *)
  (*     r2 <> PC -> *)
  (*     return_instrs r1 !! RegNum = return_instrs r2 !! RegNum -> *)
  (*     r1 = r2. *)
  (* Proof. *)
  (*   intros. rewrite !return_instrs_last // in H2. *)
  (*   inversion H2; clear H2; subst. *)
  (*   eapply encode_instr_inj in H4. *)
  (*   inversion H4; auto. *)
  (* Qed. *)









  Inductive step: Conf → Conf → Prop :=
  | step_exec_fail:
      forall φ,
        not (isCorrectPC ((reg φ) !r! PC)) →
        step (Executable, φ) (Failed, φ)
  | step_exec_instr:
      forall φ p g b e a i c,
        RegLocate (reg φ) PC = inr (Regular ((p, g), b, e, a)) ->
        isCorrectPC ((reg φ) !r! PC) →
        decodeInstrW' ((mem φ) !m! a) = i →
        exec i φ = c →
        (~ (exists r rd rb re ra, r <> PC /\ (reg φ !r! r = inr (Ret rd rb re ra)) /\
                forall i, (i <= RegNum)%nat ->
                     exists a_i, (a + i)%a = Some a_i /\ (return_instrs r) !! i = Some ((mem φ) !m! a_i)) \/
        exists a', (a + RegNum)%a = Some a' /\ ~ (a' < e)%a) ->
        step (Executable, φ) (c.1, c.2)
  | step_exec_instr':
      forall φ d p b e a i c m,
        RegLocate (reg φ) PC = inr (Stk d p b e a) ->
        isCorrectPC ((reg φ) !r! PC) →
        stack d ((reg φ, stk φ)::(callstack φ)) = Some m ->
        decodeInstrW' (m !m! a) = i →
        exec i φ = c →
        step (Executable, φ) (c.1, c.2).
  (* | step_exec_return: *)
  (*     forall φ p g b e a a' c rd rb re ra, *)
  (*       RegLocate (reg φ) PC = inr (Regular ((p, g), b, e, a)) -> *)
  (*       isCorrectPC ((reg φ) !r! PC) → *)
  (*       (a + RegNum)%a = Some a' -> *)
  (*       (a' < e)%a -> *)
  (*       (exists r, r <> PC /\ (reg φ !r! r = inr (Ret rd rb re ra)) /\ *)
  (*            forall i, (i <= RegNum)%nat -> *)
  (*                 exists a_i, (a + i)%a = Some a_i /\ (return_instrs r) !! i = Some ((mem φ) !m! a_i)) -> *)
  (*       c = match jmp_ret rd (callstack φ) with *)
  (*           | None => (Failed, φ) (* Should never happen ? *) *)
  (*           | Some ((reg', m'), cs) => (NextI, (merge (fun a b => match a with Some _ => a | _ => Some (inl 0%Z) end) reg' (reg φ), mem φ, m', cs)) *)
  (*           end -> *)
  (*       step (Executable, φ) (c.1, c.2). *)
  (* TODO: add call, tailcall semantics and PC = Stk capability version *)

  (* Lemma is_return_dec: *)
  (*   forall reg mem a, *)
  (*     {exists r rd rb re ra, r <> PC /\ (reg !r! r = inr (Ret rd rb re ra)) /\ *)
  (*                            forall i, (i <= RegNum)%nat -> *)
  (*                                 exists a_i, (a + i)%a = Some a_i /\ (return_instrs r) !! i = Some ((mem) !m! a_i)} + *)
  (*     {~ exists r rd rb re ra, r <> PC /\ (reg !r! r = inr (Ret rd rb re ra)) /\ *)
  (*                              forall i, (i <= RegNum)%nat -> *)
  (*                                   exists a_i, (a + i)%a = Some a_i /\ (return_instrs r) !! i = Some ((mem) !m! a_i)}. *)
  (* Proof. *)
  (*   intros. eapply exists_dec. intros. *)
  (*   destruct (reg_eq_dec x PC). *)
  (*   - right. red; intros (rd & rb & re & ra & A & B & C). congruence. *)
  (*   - assert ({exists rd rb re ra, reg0 !r! x = inr (Ret rd rb re ra)} + {~ exists rd rb re ra, reg0 !r! x = inr (Ret rd rb re ra)}). *)
  (*     { destruct (reg0 !r! x). *)
  (*       - right. red; intros. destruct H0 as (? & ? & ? & ? & ?). congruence. *)
  (*       - destruct c. *)
  (*         + right. red; intros. destruct H0 as (? & ? & ? & ? & ?). congruence. *)
  (*         + right. red; intros. destruct H0 as (? & ? & ? & ? & ?). congruence. *)
  (*         + left. eauto. } *)
  (*     destruct H0. *)
  (*     + assert ({∀ i : nat, i ≤ RegNum → ∃ a_i : Addr, (a + i)%a = Some a_i ∧ return_instrs x !! i = Some (mem0 !m! a_i)} + {~∀ i : nat, i ≤ RegNum → ∃ a_i : Addr, (a + i)%a = Some a_i ∧ return_instrs x !! i = Some (mem0 !m! a_i)}). *)
  (*       { assert ((∀ i : nat, i ≤ RegNum → ∃ a_i : Addr, (a + i)%a = Some a_i ∧ return_instrs x !! i = Some (mem0 !m! a_i)) <-> (forall i: fin (S RegNum), ∃ a_i : Addr, (a + (fin_to_nat i))%a = Some a_i ∧ return_instrs x !! (fin_to_nat i) = Some (mem0 !m! a_i))). *)
  (*       { split; intros. *)
  (*         - eapply H0. generalize (fin_to_nat_lt i). lia. *)
  (*         - assert (i < S RegNum) by lia. *)
  (*           generalize (H0 (nat_to_fin H2)). *)
  (*           rewrite fin_to_nat_to_fin. auto. } *)
  (*       assert ({forall i: fin (S RegNum), ∃ a_i : Addr, (a + (fin_to_nat i))%a = Some a_i ∧ return_instrs x !! (fin_to_nat i) = Some (mem0 !m! a_i)} + {~ forall i: fin (S RegNum), ∃ a_i : Addr, (a + (fin_to_nat i))%a = Some a_i ∧ return_instrs x !! (fin_to_nat i) = Some (mem0 !m! a_i)}). *)
  (*       { eapply forall_dec. intros. *)
  (*         case_eq (a + x0)%a; intros. *)
  (*         - assert ({return_instrs x !! (fin_to_nat x0) = Some (mem0 !m! a0)} + {~ return_instrs x !! (fin_to_nat x0) = Some (mem0 !m! a0)}). decide equality. decide equality. apply Z_eq_dec. apply cap_eq_dec. *)
  (*           destruct H2. *)
  (*           + left; eauto. *)
  (*           + right. red; intros. *)
  (*             destruct H2 as [y [A B]]. congruence. *)
  (*         - right. red; intros. destruct H2 as [y [A B]]. congruence. } *)
  (*       destruct H1. *)
  (*         - left. intros. assert (i < S RegNum) by lia. *)
  (*           generalize (e0 (nat_to_fin H2)). rewrite fin_to_nat_to_fin. eauto. *)
  (*         - right. red; intros. eapply n0. intros. eapply H1. generalize (fin_to_nat_lt i). lia. } *)
  (*       destruct H0. *)
  (*       * left. destruct e as [rd [rb [re [ra A]]]]. *)
  (*         exists rd, rb, re, ra. auto. *)
  (*       * right. red; intros (rd & rb & re & ra & A & B & C). congruence. *)
  (*     + right. red; intros (rd & rb & re & ra & A & B & C). *)
  (*       eapply n0. eauto. *)
  (* Qed. *)

  Lemma normal_always_step:
    forall φ, exists cf φ', step (Executable, φ) (cf, φ').
  Proof.
    intros. destruct (isCorrectPC_dec (RegLocate (reg φ) PC)).
    - inversion i; subst.
      + destruct (is_return_dec (reg φ) (mem φ) a).
        * destruct e0 as [r [rd [rb [re [ra [A [B C]]]]]]].
          destruct (C RegNum ltac:(clear; solve_addr)) as [a_RegNum [HA HB]].
          destruct (Addr_lt_dec (a_RegNum) e).
          { do 2 eexists; eapply step_exec_return; eauto. }
          { do 2 eexists; eapply step_exec_instr; eauto. }
        * do 2 eexists; eapply step_exec_instr; eauto.
      + admit.
    - exists Failed, φ. constructor 1; eauto.
  Admitted.

  Lemma step_deterministic:
    forall c1 c2 c2' σ1 σ2 σ2',
      step (c1, σ1) (c2, σ2) →
      step (c1, σ1) (c2', σ2') →
      c2 = c2' ∧ σ2 = σ2'.
  Proof.
    Ltac inv H := inversion H; clear H; subst.
    intros * H1 H2; split; inv H1; inv H2; auto; try congruence.
    - destruct H10.
      + elim H0. rewrite H6 in H4; inv H4.
        destruct H11. exists x, rd, rb, re, ra.
        destruct H1 as [A [B C]]. repeat split; eauto.
      + rewrite H6 in H4; inv H4.
        destruct H0 as [a'' [A B]].
        rewrite A in H8; inv H8. elim B; auto.
    - destruct H13.
      + elim H0. rewrite H6 in H4; inv H4.
        destruct H10. exists x, rd, rb, re, ra.
        destruct H1 as [A [B C]]. repeat split; eauto.
      + rewrite H6 in H4; inv H4.
        destruct H0 as [a'' [A B]].
        rewrite A in H8; inv H8. elim B; auto.
    - rewrite H4 in H6; inv H6.
      rewrite H11 in H8; inv H8.
      destruct H10 as [r1 [A [B C]]].
      destruct H13 as [r2 [A' [B' C']]].
      destruct (C RegNum ltac:(clear; solve_addr)) as [aa [X1 X2]].
      destruct (C' RegNum ltac:(clear; solve_addr)) as [bb [Y1 Y2]].
      rewrite X1 in H11; inv H11. rewrite Y1 in X1; inv X1.
      rewrite -Y2 in X2. eapply return_instrs_ext_eq in X2; auto. subst r2.
      rewrite B' in B; inv B. reflexivity.
    - destruct H10.
      + elim H0. rewrite H6 in H4; inv H4.
        destruct H11. exists x, rd, rb, re, ra.
        destruct H1 as [A [B C]]. repeat split; eauto.
      + rewrite H6 in H4; inv H4.
        destruct H0 as [a'' [A B]].
        rewrite A in H8; inv H8. elim B; auto.
    - destruct H13.
      + elim H0. rewrite H6 in H4; inv H4.
        destruct H10. exists x, rd, rb, re, ra.
        destruct H1 as [A [B C]]. repeat split; eauto.
      + rewrite H6 in H4; inv H4.
        destruct H0 as [a'' [A B]].
        rewrite A in H8; inv H8. elim B; auto.
    - rewrite H4 in H6; inv H6.
      rewrite H11 in H8; inv H8.
      destruct H10 as [r1 [A [B C]]].
      destruct H13 as [r2 [A' [B' C']]].
      destruct (C RegNum ltac:(clear; solve_addr)) as [aa [X1 X2]].
      destruct (C' RegNum ltac:(clear; solve_addr)) as [bb [Y1 Y2]].
      rewrite X1 in H11; inv H11. rewrite Y1 in X1; inv X1.
      rewrite -Y2 in X2. eapply return_instrs_ext_eq in X2; auto. subst r2.
      rewrite B' in B; inv B. reflexivity.
  Qed.

  Inductive val: Type :=
  | HaltedV: val
  | FailedV: val
  | NextIV: val.

  Inductive expr: Type :=
  | Instr (c : ConfFlag)
  | Seq (e : expr).
  Definition state : Type := ExecConf.

  Definition of_val (v: val): expr :=
    match v with
    | HaltedV => Instr Halted
    | FailedV => Instr Failed
    | NextIV => Instr NextI
    end.

  Fixpoint to_val (e: expr): option val :=
    match e with
    | Instr c =>
      match c with
      | Executable => None
      | Halted => Some HaltedV
      | Failed => Some FailedV
      | NextI => Some NextIV
      end
    | Seq _ => None
    end.

  Lemma of_to_val:
    forall e v, to_val e = Some v →
           of_val v = e.
  Proof.
    intros * HH. destruct e; try destruct c; simpl in HH; inv HH; auto.
  Qed.

  Lemma to_of_val:
    forall v, to_val (of_val v) = Some v.
  Proof. destruct v; reflexivity. Qed.

  (** Evaluation context *)
  Inductive ectx_item :=
  | SeqCtx.

  Notation ectx := (list ectx_item).

  Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
    match Ki with
    | SeqCtx => Seq e
    end.

  Inductive prim_step: expr → state → list Empty_set → expr → state → list expr → Prop :=
  | PS_no_fork_instr σ e' σ' :
      step (Executable, σ) (e', σ') → prim_step (Instr Executable) σ [] (Instr e') σ' []
  | PS_no_fork_seq σ : prim_step (Seq (Instr NextI)) σ [] (Seq (Instr Executable)) σ []
  | PS_no_fork_halt σ : prim_step (Seq (Instr Halted)) σ [] (Instr Halted) σ []
  | PS_no_fork_fail σ : prim_step (Seq (Instr Failed)) σ [] (Instr Failed) σ [].

  Lemma val_stuck:
    forall e σ o e' σ' efs,
      prim_step e σ o e' σ' efs →
      to_val e = None.
  Proof. intros * HH. by inversion HH. Qed.

  Lemma prim_step_exec_inv σ1 l1 e2 σ2 efs :
    prim_step (Instr Executable) σ1 l1 e2 σ2 efs →
    l1 = [] ∧ efs = [] ∧
    exists (c: ConfFlag),
      e2 = Instr c ∧
      step (Executable, σ1) (c, σ2).
  Proof. inversion 1; subst; split; eauto. Qed.

  Lemma prim_step_and_step_exec σ1 e2 σ2 l1 e2' σ2' efs :
    step (Executable, σ1) (e2, σ2) →
    prim_step (Instr Executable) σ1 l1 e2' σ2' efs →
    l1 = [] ∧ e2' = (Instr e2) ∧ σ2' = σ2 ∧ efs = [].
  Proof.
    intros* Hstep Hpstep. inversion Hpstep as [? ? ? Hstep' | | |]; subst.
    generalize (step_deterministic _ _ _ _ _ _ Hstep Hstep'). intros [-> ->].
    auto.
  Qed.

  Lemma overlay_lang_determ e1 σ1 κ κ' e2 e2' σ2 σ2' efs efs' :
    prim_step e1 σ1 κ e2 σ2 efs →
    prim_step e1 σ1 κ' e2' σ2' efs' →
    κ = κ' ∧ e2 = e2' ∧ σ2 = σ2' ∧ efs = efs'.
  Proof.
    intros Hs1 Hs2. inv Hs1; inv Hs2. all: auto.
    generalize (step_deterministic _ _ _ _ _ _ H0 H1).
    intros [? ?]; subst. auto.
  Qed.

  Lemma fill_item_val Ki e :
    is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
  Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto. Qed.

  Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
  Proof. destruct Ki; intros ???; simplify_eq; auto with f_equal. Qed.

  Lemma head_ctx_step_val Ki e σ1 κ e2 σ2 ef :
    prim_step (fill_item Ki e) σ1 κ e2 σ2 ef → is_Some (to_val e).
  Proof. destruct Ki; inversion_clear 1; simplify_option_eq; eauto. Qed.

  Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
    to_val e1 = None → to_val e2 = None →
    fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
  Proof.
    destruct Ki1, Ki2; intros; try discriminate; simplify_eq;
    repeat match goal with
           | HH : to_val (of_val _) = None |- _ => by rewrite to_of_val in HH
           end; auto.
  Qed.

  Lemma overlay_lang_mixin : EctxiLanguageMixin of_val to_val fill_item prim_step.
  Proof.
    constructor;
    apply _ || eauto using to_of_val, of_to_val, val_stuck,
           fill_item_val, fill_item_no_val_inj, head_ctx_step_val.
  Qed.

  Definition is_atomic (e : expr) : Prop :=
    match e with
    | Instr _ => True
    | _ => False
    end.

  Lemma updatePC_atomic φ :
    ∃ φ', updatePC φ = (Failed,φ') ∨ (updatePC φ = (NextI,φ')) ∨
          (updatePC φ = (Halted,φ')).
  Proof.
    rewrite /updatePC; repeat case_match; eauto.
  Qed.

  Lemma instr_atomic i φ :
    ∃ φ', (exec i φ = (Failed, φ')) ∨ (exec i φ = (NextI, φ')) ∨
          (exec i φ = (Halted, φ')).
  Proof.
    unfold exec; repeat case_match; eauto; try (eapply updatePC_atomic; eauto).
  Qed.

End opsem.

Canonical Structure overlay_ectxi_lang `{MachineParameters} := EctxiLanguage overlay_lang_mixin.
Canonical Structure overlay_ectx_lang `{MachineParameters} := EctxLanguageOfEctxi overlay_ectxi_lang.
Canonical Structure overlay_lang `{MachineParameters} := LanguageOfEctx overlay_ectx_lang.

Hint Extern 20 (PureExec _ _ _) => progress simpl : typeclass_instances.

Hint Extern 5 (IntoVal _ _) => eapply of_to_val; fast_done : typeclass_instances.
Hint Extern 10 (IntoVal _ _) =>
  rewrite /IntoVal; eapply of_to_val; rewrite /= !to_of_val /=; solve [ eauto ] : typeclass_instances.

Hint Extern 5 (AsVal _) => eexists; eapply of_to_val; fast_done : typeclass_instances.
Hint Extern 10 (AsVal _) =>
eexists; rewrite /IntoVal; eapply of_to_val; rewrite /= !to_of_val /=; solve [ eauto ] : typeclass_instances.

Local Hint Resolve language.val_irreducible.
Local Hint Resolve to_of_val.
Local Hint Unfold language.irreducible.

