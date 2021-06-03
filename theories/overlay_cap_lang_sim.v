From cap_machine.overlay Require Import base lang.
From cap_machine Require Import cap_lang simulation linking region machine_run.
From cap_machine.rules Require rules_base.
From stdpp Require Import base gmap fin_maps list.
From Coq Require Import Eqdep_dec ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section overlay_to_cap_lang.

  Lemma all_registers_correct:
    forall r, r ∈ all_registers.
  Proof.
    rewrite /all_registers.
    destruct r.
    - do 32 (apply elem_of_cons; right).
        by apply elem_of_list_singleton.
    - induction n.
      + apply elem_of_cons; left.
        apply f_equal. apply eq_proofs_unicity. decide equality.
      + apply elem_of_list_lookup_2 with (S n).
        repeat (destruct n;
                first (simpl;do 2 f_equal;apply eq_proofs_unicity;decide equality)).
        simpl in *. inversion fin.
  Qed.

  Lemma all_registers_s_correct:
    forall r, r ∈ (@list_to_set _ (gset RegName) _ _ _ all_registers).
  Proof.
    intros; rewrite elem_of_list_to_set.
    apply all_registers_correct.
  Qed.

  Definition translate_word (w: base.Word): Word :=
    match w with
    | inl n => inl n
    | inr c => match c with
              | Regular c => inr c
              | Stk d p b e a => inr (p, Monotone, b, e, a)
              | Ret b e a => inr (E, Monotone, b, e, a)
              end
    end.

  Lemma isCorrectPC_translate_word:
    forall w,
      lang.isCorrectPC w ->
      isCorrectPC (translate_word w).
  Proof.
    intros; inv H; simpl; econstructor; eauto.
  Qed.

  Lemma decodeInstrW_translate_word `{MachineParameters}:
    forall w,
      decodeInstrW' w = decodeInstrW (translate_word w).
  Proof.
    destruct w; simpl; auto.
    destruct c; simpl; auto.
  Qed.

  Definition compile (c: overlay_component): machine_component :=
    match c with
    | Lib _ _ _ _ (ms, imp, exp) => Lib _ _ _ _ (@fmap (gmap Addr) _ base.Word Word translate_word ms, imp, fmap translate_word exp)
    | Main _ _ _ _ (ms, imp, exp) c_main => Main _ _ _ _ (@fmap (gmap Addr) _ base.Word Word translate_word ms, imp, fmap translate_word exp) (translate_word c_main)
    end.

  Variables b_stk e_stk: Addr.
  Variable stk_pos: (b_stk < e_stk)%a.
  Context `{MachineParameters}.

  Inductive sim_flag: lang.ConfFlag -> ConfFlag -> Prop :=
  | sim_flag_exec:
      sim_flag lang.Executable Executable
  | sim_flag_halted:
      sim_flag lang.Halted Halted
  | sim_flag_failed:
      sim_flag lang.Failed Failed
  | sim_flag_next:
      sim_flag lang.NextI NextI.

  Lemma sim_flag_determ:
    forall f1 f2 f2',
      sim_flag f1 f2 ->
      sim_flag f1 f2' ->
      f2 = f2'.
  Proof.
    intros; inv H0; inv H1; auto.
  Qed.

  Inductive sim_expr: lang.expr -> expr -> Prop :=
  | sim_expr_instr:
      forall f1 f2,
        sim_flag f1 f2 ->
        sim_expr (lang.Instr f1) (Instr f2)
  | sim_expr_seq:
      forall e1 e2,
        sim_expr e1 e2 ->
        sim_expr (lang.Seq e1) (Seq e2).

  Lemma sim_expr_determ:
    forall e1 e2 e2',
      sim_expr e1 e2 ->
      sim_expr e1 e2' ->
      e2 = e2'.
  Proof.
    induction e1; intros.
    - inv H0; inv H1. f_equal. eapply sim_flag_determ; eauto.
    - inv H0; inv H1. f_equal. eapply IHe1; eauto.
  Qed.

  Lemma sim_expr_fill:
    forall K e1 e2,
      sim_expr e1 e2 ->
      sim_expr (ectx_language.fill K e1) (@ectx_language.fill cap_ectx_lang (map (fun _ => SeqCtx) K) e2).
  Proof.
    induction K; intros.
    - simpl; auto.
    - destruct a; simpl. eapply IHK; eauto.
      econstructor; eauto.
  Qed.

  Lemma sim_expr_fill_inv:
    forall K e1 e2,
      sim_expr (ectx_language.fill K e1) e2 ->
      exists e2', sim_expr (ectx_language.fill K e1) (@ectx_language.fill cap_ectx_lang (map (fun _ => SeqCtx) K) e2') /\ sim_expr e1 e2'.
  Proof.
    induction K.
    - simpl; intros. eauto.
    - destruct a; simpl; intros.
      eapply IHK in H0; auto.
      destruct H0 as [e2' [A B] ].
      inv B. exists e3; split; auto.
  Qed.

  Definition incrementPC (regs: base.Reg) : option base.Reg :=
    match regs !! PC with
    | Some (inr (Regular ((p, g), b, e, a))) =>
      match (a + 1)%a with
      | Some a' => 
        match p with
        | E | URWLX | URWX | URWL | URW => None
        | _ => Some (<[ PC := inr (Regular ((p, g), b, e, a')) ]> regs)
        end
      | None => None
      end
    | Some (inr (Stk d p b e a)) =>
      match (a + 1)%a with
      | Some a' => 
        match p with
        | E | URWLX | URWX | URWL | URW => None
        | _ => Some (<[ PC := inr (Stk d p b e a') ]> regs)
        end
      | None => None
      end
    | _ => None
    end.

  Lemma incrementPC_is_Some:
    forall r1 r2,
      incrementPC r1 = Some r2 ->
      forall x, is_Some (r1 !! x) <-> is_Some (r2 !! x).
  Proof.
    rewrite /incrementPC. intros.
    destruct (r1 !! PC) eqn:X; [|inv H0].
    destruct s; inv H0.
    destruct c; inv H2.
    - destruct c as [ [ [ [p' g'] b'] e'] a'].
      destruct (a' + 1)%a; inv H1.
      destruct (reg_eq_dec x PC).
      + subst x. destruct p'; try congruence; inv H2; rewrite lookup_insert X; split; intro; eauto.
      + destruct p'; try congruence; inv H2; rewrite lookup_insert_ne; auto.
    - destruct (a1 + 1)%a; inv H1.
      destruct (reg_eq_dec x PC).
      + subst x. destruct p; try congruence; inv H2; rewrite lookup_insert X; split; intro; eauto.
      + destruct p; try congruence; inv H2; rewrite lookup_insert_ne; auto.
  Qed.

  Lemma incrementPC_inv_Some:
    forall r1 r2,
      incrementPC r1 = Some r2 ->
      match r1 !! PC with
      | Some (inr (Regular (p, g, b, e, a))) => exists a', (a + 1)%a = Some a' /\ r2 = <[PC := inr (Regular (p, g, b, e, a'))]> r1 /\ (p <> E /\ p <> URWLX /\ p <> URWX /\ p <> URWL /\ p <> URW)
      | Some (inr (Stk d p b e a)) => exists a', (a + 1)%a = Some a' /\ r2 = <[PC := inr (Stk d p b e a')]> r1  /\ (p <> E /\ p <> URWLX /\ p <> URWX /\ p <> URWL /\ p <> URW)
      | _ => False
      end.
  Proof.
    intros. rewrite /incrementPC in H0.
    destruct (r1 !! PC) as [wpc|] eqn:HPC; [|congruence].
    destruct wpc; [congruence|].
    destruct c.
    - destruct c as [ [ [ [p g] b] e] a].
      destruct (a + 1)%a; [|congruence].
      destruct p; inv H0; eexists; repeat split; eauto.
    - destruct (a1 + 1)%a; [|congruence].
      destruct p; inv H0; eexists; repeat split; eauto.
    - congruence.
  Qed.

  Lemma incrementPC_fail_updatePC regs h stk cs :
   incrementPC regs = None ->
   lang.updatePC (regs, h, stk, cs) = (lang.Failed, (regs, h, stk, cs)).
  Proof.
   rewrite /incrementPC /lang.updatePC /base.RegLocate /=.
   destruct (regs !! PC) as [X|]; auto.
   destruct X; auto. destruct c as [ [ [ [ [p g] b] e] a] | ? | ?]; auto.
   destruct (a + 1)%a; auto; destruct p; try congruence; auto.
   destruct (a1 + 1)%a; auto; destruct p; try congruence; auto.
  Qed.

  Lemma incrementPC_success_updatePC regs regs' h stk cs :
    incrementPC regs = Some regs' ->
    lang.updatePC (regs, h, stk, cs) = (lang.NextI, (regs', h, stk, cs)).
  Proof.
    rewrite /incrementPC /lang.updatePC /update_reg /base.RegLocate /=.
    destruct (regs !! PC) as [X|] eqn:?; auto; try congruence; [].
    destruct X; try congruence. destruct c as [ [ [ [ [p g] b] e] a] | ? | ?]; try congruence.
    destruct (a + 1)%a eqn:?; [| congruence]. destruct p; try congruence; inversion 1; subst regs';
    do 6 eexists; repeat split; auto.
    destruct (a1 + 1)%a eqn:?; [| congruence]. destruct p; try congruence; inversion 1; subst regs';
    do 6 eexists; repeat split; auto.
  Qed.

  Notation incrementPC' := rules_base.incrementPC.

  Lemma incrementPC_success_incrementPC' regs1 regs1' regs2 w:
    regs1 !! PC = Some w ->
    regs2 !! PC = Some (translate_word w) ->
    incrementPC regs1 = Some regs1' ->
    exists regs2', incrementPC' regs2 = Some regs2'.
  Proof.
    intros Hw Hw'. rewrite /incrementPC /incrementPC' Hw Hw'.
    destruct w; try congruence.
    destruct c as [ [ [ [ [p g] b] e] a] | ? | ?]; try congruence.
    - simpl; destruct (a + 1)%a eqn:?; [| congruence]. destruct p; try congruence; eauto.
    - simpl; destruct (a1 + 1)%a eqn:?; [| congruence]. destruct p; try congruence; eauto.
  Qed.

  Lemma incrementPC_fail_incrementPC' regs1 regs2 w:
    regs1 !! PC = Some w ->
    regs2 !! PC = Some (translate_word w) ->
    incrementPC regs1 = None ->
    incrementPC' regs2 = None.
  Proof.
    intros Hw Hw'. rewrite /incrementPC /incrementPC' Hw Hw'.
    destruct w; simpl; auto.
    destruct c as [ [ [ [ [p g] b] e] a1] | ? | ?]; simpl; auto;
    destruct (a1 + 1)%a; try congruence; auto; destruct p; try congruence; auto.
  Qed.

  Definition word_of_argument (regs: base.Reg) (a: Z + RegName): base.Word :=
    match a with
    | inl n => inl n
    | inr r => base.RegLocate regs r
    end.

  Fixpoint flag_of_expr (e: lang.expr) :=
    match e with
    | lang.Instr f => f
    | lang.Seq e => flag_of_expr e
    end.

  Definition can_step (e: lang.expr): Prop :=
    flag_of_expr e = lang.Executable \/ flag_of_expr e = lang.NextI.
  
  Lemma can_step_fill:
    forall K e, can_step (fill K e) = can_step e.
  Proof.
    induction K; simpl; auto.
    intros. destruct a. simpl.
    rewrite IHK. rewrite /can_step /=. reflexivity.
  Qed.

  Definition interp (w: base.Word) (h: base.Mem) (stk: base.Mem) (cs: list Stackframe): Prop :=
    match w with
    | inl n => True
    | inr (Regular _) => lang.pwlW w = false /\ lang.can_address_only w (dom _ h)
    | inr (Stk d p b e a) => d = length cs /\ forall x, (b <= x < lang.canReadUpTo w)%a (* min e canReadUpTo ? *) -> exists w, stk !! x = Some w
    | inr (Ret b e a) => match cs with
                         | [] => False
                         | (reg', stk')::cs' => exists b_stk e_stk a_stk, reg' !! call.r_stk = Some (inr (Stk (length cs') URWLX b_stk e_stk a_stk)) /\ a = ^(a_stk + 31)%a /\ True (* TODO describe return capability shape *)
                         end
    end.

  (* w is legally stored at address a *)
  Definition canBeStored (w: base.Word) (a: Addr): Prop :=
    match w with
    | inl _ => True
    | inr (Regular (p, g, b, e, a)) => match g with
                                       | Monotone => (lang.canReadUpTo w <= a)%a
                                       | _ => True
                                       end
    | inr _ => (lang.canReadUpTo w <= a)%a
    end.

  Inductive sim_cs: bool -> base.Mem -> list Stackframe -> machine_base.Mem -> Prop :=
  | sim_cs_nil:
      forall b h m,
        sim_cs b h [] m
  | sim_cs_cons_true:
      forall reg stk cs h m
        (Hregsdef: forall r, exists w, reg !! r = Some w /\ interp w h stk cs)
        (Hstkdisjheap: forall a, is_Some (stk !! a) -> is_Some (h !! a) -> False)
        (Hstksim: forall a w, stk !! a = Some w -> m !! a = Some (translate_word w) /\ interp w h stk cs /\ canBeStored w a)
        (Hcontiguous: exists b_stk e_stk a_stk, reg !! call.r_stk = Some (inr (Stk (length cs) URWLX b_stk e_stk a_stk)) /\ dom (gset _) stk = list_to_set (region_addrs b_stk ^(a_stk + 37)%a) /\ forall (i: nat) r, ((list_difference all_registers [PC; call.r_stk]) !! i) = Some r -> stk !! ^(a_stk + i)%a = reg !! r)
        (Hcs: sim_cs true h cs m),
        sim_cs true h ((reg, stk)::cs) m
 | sim_cs_cons_false:
      (* false indicates topmost frame *)
      forall reg stk cs h m
        (Hregsdef: forall r, exists w, reg !! r = Some w /\ interp w h stk cs)
        (Hstkdisjheap: forall a, is_Some (stk !! a) -> is_Some (h !! a) -> False)
        (Hstksim: forall a w, stk !! a = Some w -> m !! a = Some (translate_word w) /\ interp w h stk cs /\ canBeStored w a)
        (* This is the only difference, for the topmost frame, the shape of the stack is not frozen yet *)
        (Hcontiguous: exists b_stk e_stk, dom (gset _) stk = list_to_set (region_addrs b_stk e_stk))
        (Hcs: sim_cs true h cs m),
        sim_cs false h ((reg, stk)::cs) m.

  Inductive invariants: language.cfg overlay_lang -> language.cfg cap_lang -> Prop :=
  | invariants_intro:
      forall e1 e2 reg1 reg2 h stk cs mem2
        (Hstkdisj: forall d1 d2, d1 < d2 -> forall stk1 stk2, stack d1 ((reg1, stk)::cs) = Some stk1 -> stack d2 ((reg1, stk)::cs) = Some stk2 -> forall a1 a2, is_Some (stk1 !! a1) -> is_Some (stk2 !! a2) -> (a1 < a2)%a)
        (Hcswf: sim_cs false h ((reg1, stk)::cs) mem2)
        (Hsregs: forall r w, reg1 !! r = Some w -> reg2 !! r = Some (translate_word w))
        (Hsh: forall a w, h !! a = Some w -> mem2 !! a = Some (translate_word w) /\ lang.pwlW w = false /\ lang.is_global w = true /\ lang.can_address_only w (dom _ h))
        (Hdisj: forall a, a ∈ dom (gset _) h -> (e_stk <= a)%a),
      invariants ([e1], (reg1, h, stk, cs)) ([e2], (reg2, mem2)).

  Inductive sim: language.cfg overlay_lang -> language.cfg cap_lang -> Prop :=
  | sim_intro:
      forall e1 e2 reg1 reg2 h stk cs mem2
        (Hsexpr: sim_expr e1 e2)
        (Hinvs: can_step e1 -> invariants ([e1], (reg1, h, stk, cs)) ([e2], (reg2, mem2))),
        sim ([e1], (reg1, h, stk, cs)) ([e2], (reg2, mem2)).

  Lemma Hregsdef_preserve_word_of_arg reg h stk cs
    (Hregsdef: forall r, exists w, reg !! r = Some w /\ interp w h stk cs):
    forall src dst r,
      exists w, <[dst := word_of_argument reg src]> reg !! r = Some w /\ interp w h stk cs.
  Proof.
    intros. destruct (reg_eq_dec dst r); [|rewrite lookup_insert_ne; eauto].
    subst r. rewrite lookup_insert. eexists; split; eauto.
    destruct src; simpl; auto. rewrite /base.RegLocate.
    destruct (Hregsdef r) as [wr [A B] ]. rewrite A; auto.
  Qed.

  Lemma Hsregs_preserve_word_of_arg (reg1: base.Reg) (reg2: Reg) dst src
    (Hsregs: forall (r: RegName) w, reg1 !! r = Some w -> reg2 !! r = Some (translate_word w)):
    forall r w, (<[dst:=word_of_argument reg1 src]> reg1) !! r = Some w -> (<[dst:=translate_word (word_of_argument reg1 src)]> reg2 )!! r = Some (translate_word w).
  Proof.
    intros. destruct (reg_eq_dec dst r); [|rewrite lookup_insert_ne; rewrite lookup_insert_ne in H0; auto].
    subst r; rewrite lookup_insert; rewrite lookup_insert in H0.
    inv H0; auto.
  Qed.

  Lemma exec_sim:
    forall K reg1 reg1' reg2 reg2' h h' stk stk' cs cs' mem2 mem2' p g b e a c1 c2
      (Hsexpr: sim_expr (fill K (lang.Instr lang.Executable)) (@ectx_language.fill cap_ectx_lang (map (fun _ => SeqCtx) K) (Instr Executable)))
      (Hstkdisj: forall d1 d2, d1 < d2 -> forall stk1 stk2, stack d1 ((reg1, stk)::cs) = Some stk1 -> stack d2 ((reg1, stk)::cs) = Some stk2 -> forall a1 a2, is_Some (stk1 !! a1) -> is_Some (stk2 !! a2) -> (a1 < a2)%a)
      (Hcswf: sim_cs false h ((reg1, stk)::cs) mem2)
      (Hsregs: forall r w, reg1 !! r = Some w -> reg2 !! r = Some (translate_word w))
      (Hsh: forall a w, h !! a = Some w -> mem2 !! a = Some (translate_word w) /\ lang.pwlW w = false /\ lang.is_global w = true /\ lang.can_address_only w (dom _ h))
      (Hdisj: forall a, a ∈ dom (gset _) h -> (e_stk <= a)%a)
      (HnisJmp: ∀ r : RegName, decodeInstrW' (base.MemLocate h a) ≠ Jmp r)
      (HnisJnz: ∀ r1 r2 : RegName, decodeInstrW' (base.MemLocate h a) ≠ Jnz r1 r2)
      (HisCorrectPC: lang.isCorrectPC (inr (Regular (p, g, b, e, a)))),
      reg1 !! PC = Some (inr (Regular (p, g, b, e, a))) ->
      lang.exec (decodeInstrW' (base.MemLocate h a)) (reg1, h, stk, cs) = (c1, (reg1', h', stk', cs')) ->
      exec (decodeInstrW (mem2 !m! a)) (reg2, mem2) = (c2, (reg2', mem2')) ->
      sim ([ectxi_language.fill K (lang.Instr c1)], (reg1', h', stk', cs')) ([ectxi_language.fill (map (fun=> SeqCtx) K) (Instr c2)], (reg2', mem2')).
  Proof.
    rewrite /MemLocate /base.MemLocate. intros.
    inv Hcswf. generalize (Hregsdef PC).
    intros [wpc [HPC HinterpPC] ].
    rewrite HPC in H0; inv H0. simpl in HinterpPC.
    destruct HinterpPC as [HnpwlPC Hisdef].
    inv HisCorrectPC. generalize (Hisdef _ H4); intros Hha.
    eapply elem_of_dom in Hha. destruct Hha as [wa Ha].
    rewrite Ha in H1. generalize (Hsh _ _ Ha).
    intros [Ha' [HnpwlW [Hisglobal Hcan_address] ] ].
    rewrite Ha' in H2. rewrite -decodeInstrW_translate_word in H2.
    rewrite Ha in HnisJmp, HnisJnz.
    destruct (decodeInstrW' wa) eqn:Hinstr.
    - (* Jmp *)
      exfalso; eapply HnisJmp; reflexivity.
    - (* Jnz *)
      exfalso; eapply HnisJnz; reflexivity.
    - (* Mov *)
      simpl in H1, H2.
      assert (match incrementPC (<[dst := word_of_argument reg1 src]> reg1) with Some r => c1 = lang.NextI /\ c2 = NextI /\ reg1' = r /\ h' = h /\ stk' = stk /\ cs' = cs /\ mem2' = mem2 /\ incrementPC' (<[dst := translate_word (word_of_argument reg1 src)]> reg2) = Some reg2' | _ => c1 = lang.Failed /\ c2 = Failed end).
      { destruct (incrementPC (<[dst:=word_of_argument reg1 src]> reg1)) as [reg1''|] eqn:Hincrement1.
        - generalize (@incrementPC_success_updatePC _ _ h stk cs Hincrement1).
          intro A. assert (X: (c1, (reg1', h', stk', cs')) = (lang.NextI, (reg1'', h, stk, cs))).
          { rewrite -A -H1. destruct src; simpl in A; rewrite A; auto. }
          inv X. assert (Hww: exists ww, <[dst:=word_of_argument reg1 src]> reg1 !! PC = Some ww).
          { destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert; eauto|].
            rewrite lookup_insert_ne; auto. rewrite HPC; eauto. }
          destruct Hww as [ww Hww].
          assert (Hww': (<[dst:=translate_word (word_of_argument reg1 src)]> reg2) !! PC = Some (translate_word ww)).
          { destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hww; inv Hww; rewrite lookup_insert //|].
            rewrite lookup_insert_ne; auto.
            rewrite lookup_insert_ne in Hww; auto. }
          generalize (@incrementPC_success_incrementPC' _ _ _ _ Hww Hww' Hincrement1).
          intros [regs2'' Y].
          generalize (@rules_base.incrementPC_success_updatePC _ mem2 _ Y).
          intros [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
          assert (XX: (c2, (reg2', mem2')) = (NextI, (regs2'', mem2))).
          { rewrite Z4 -Z3 - H2. destruct src; simpl; auto.
            replace (reg2 !r! r) with (translate_word (base.RegLocate reg1 r)); auto.
            rewrite /base.RegLocate /RegLocate.
            destruct (Hregsdef r) as [rw [X1 X2] ].
            rewrite X1. rewrite (Hsregs _ _ X1) //. }
          inv XX. repeat split; auto.
        - generalize (@incrementPC_fail_updatePC _ h stk cs Hincrement1).
          intro X. split.
          + destruct src; simpl in H1; rewrite H1 in X; inv X; auto.
          + assert (Hww: exists ww, <[dst:=word_of_argument reg1 src]> reg1 !! PC = Some ww).
            { destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert; eauto|].
              rewrite lookup_insert_ne; auto. rewrite HPC; eauto. }
            destruct Hww as [ww Hww].
            assert (Hww': (<[dst:=translate_word (word_of_argument reg1 src)]> reg2) !! PC = Some (translate_word ww)).
            { destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in Hww; inv Hww; rewrite lookup_insert //|].
              rewrite lookup_insert_ne; auto.
              rewrite lookup_insert_ne in Hww; auto. }
            generalize (@incrementPC_fail_incrementPC' _ _ _ Hww Hww' Hincrement1). intro Y.
            generalize (rules_base.incrementPC_fail_updatePC _ mem2 Y).
            intro Z. destruct src; simpl in H2; simpl in Z; [rewrite H2 in Z; inv Z; auto|].
            replace (reg2 !r! r) with (translate_word (base.RegLocate reg1 r)) in H2; [rewrite H2 in Z; inv Z; auto|].
            rewrite /base.RegLocate /RegLocate.
            destruct (Hregsdef r) as [rw [X1 X2] ].
            rewrite X1. rewrite (Hsregs _ _ X1) //. }
      destruct (incrementPC (<[dst:=word_of_argument reg1 src]> reg1)) as [reg1''|] eqn:Hincrement; cycle 1.
      + destruct H0 as [-> ->].
        econstructor.
        * eapply sim_expr_fill. repeat econstructor.
        * rewrite can_step_fill /can_step /=; intros [A | A]; discriminate.
      + destruct H0 as [-> [-> [-> [<- [<- [<- [<- Hincrement'] ] ] ]  ] ] ].
        econstructor.
        * eapply sim_expr_fill. repeat econstructor.
        * intros _. econstructor; eauto.
          -- econstructor; eauto.
             generalize (Hregsdef_preserve_word_of_arg Hregsdef src dst). intros AA.
             generalize (incrementPC_inv_Some Hincrement). intro X1.
             generalize (rules_base.incrementPC_Some_inv _ _ Hincrement').
             intros [p'' [g'' [b'' [e'' [a'' [a''' [Y1 [Y2 [Y3 Y4] ] ] ] ] ] ] ] ].
             destruct (<[dst:=word_of_argument reg1 src]> reg1 !! PC) as [wpc|] eqn:X2; [|elim X1].
             destruct wpc as [?|cap]; [elim X1|].
             destruct cap as [ [ [ [ [p1 g1] b1] e1] a1] | ? | ?]; [| | elim X1].
             ** destruct X1 as [a1' [Ha1' [X1 X1'] ] ].
                rewrite X1. intro. destruct (reg_eq_dec PC r).
                { subst r; rewrite lookup_insert; eexists; split; eauto.
                  simpl. destruct (AA PC) as [wpc [ZA ZB] ].
                  rewrite X2 in ZA; inv ZA. apply ZB. }
                { rewrite lookup_insert_ne; auto. }
             ** destruct X1 as [a2' [Ha2' [X1 X1'] ] ].
                rewrite X1. intro. destruct (reg_eq_dec PC r).
                { subst r; rewrite lookup_insert; eexists; split; eauto.
                  simpl. destruct (AA PC) as [wpc [ZA ZB] ].
                  rewrite X2 in ZA; inv ZA. simpl in ZB.
                  destruct ZB as [ZB1 ZB2]; split; auto.
                  intros. apply ZB2. destruct X1' as [? [? [? [? ?] ] ] ].
                  destruct p0; auto; congruence. }
                { rewrite lookup_insert_ne; auto. }
          -- generalize (@Hsregs_preserve_word_of_arg _ _ dst src Hsregs). intros Hsregs'.
             generalize (incrementPC_inv_Some Hincrement). intro X1.
             generalize (rules_base.incrementPC_Some_inv _ _ Hincrement').
             intros [p'' [g'' [b'' [e'' [a'' [a''' [Y1 [Y2 [Y3 Y4] ] ] ] ] ] ] ] ].
             destruct (<[dst:=word_of_argument reg1 src]> reg1 !! PC) as [wpc|] eqn:X2; [|elim X1].
             destruct wpc as [?|cap]; [elim X1|].
             destruct cap as [ [ [ [ [p1 g1] b1] e1] a1] | ? | ?]; [| | elim X1].
             ++ destruct X1 as [a1' [Ha1' [X1 X1'] ] ].
                rewrite X1. intro. destruct (reg_eq_dec PC r).
                { subst r; rewrite lookup_insert.
                  subst reg2'. rewrite lookup_insert.
                  inversion 1. simpl.
                  generalize (Hsregs' _ _ X2). rewrite Y1. simpl. inversion 1; subst.
                  rewrite Y2 in Ha1'; inv Ha1'; auto. }
                { subst reg2'. rewrite !(lookup_insert_ne _ PC); auto. }
             ++ destruct X1 as [a1' [Ha1' [X1 X1'] ] ].
                rewrite X1. intro. destruct (reg_eq_dec PC r).
                { subst r; rewrite lookup_insert.
                  subst reg2'. rewrite lookup_insert.
                  inversion 1. simpl.
                  generalize (Hsregs' _ _ X2). rewrite Y1. simpl. inversion 1; subst.
                  rewrite Y2 in Ha1'; inv Ha1'; auto. }
                { subst reg2'. rewrite !(lookup_insert_ne _ PC); auto. }
    - (* Load *) admit.
    - (* Store *) admit.
    - (* Lt *) admit.
    - (* Add *) admit.
    - (* Sub *) admit.
    - (* Lea *) admit.
    - (* Restrict *) admit.
    - (* Subseg *) admit.
    - (* IsPtr *) admit.
    - (* GetL *) admit.
    - (* GetP *) admit.
    - (* GetB *) admit.
    - (* GetE *) admit.
    - (* GetA *) admit.
    - (* Fail *)
      simpl in H1, H2. inv H1; inv H2.
      econstructor.
      + eapply sim_expr_fill. repeat econstructor.
      + rewrite can_step_fill /can_step /=; intros [A | A]; discriminate.
    - (* Halt *)
      simpl in H1, H2. inv H1; inv H2.
      econstructor.
      + eapply sim_expr_fill. repeat econstructor.
      + rewrite can_step_fill /can_step /=; intros [A | A]; discriminate.
    - (* LoadU *) admit.
    - (* StoreU *) admit.
    - (* PromoteU *) admit.
  
(*
    - (* Lt *)
      assert ((c1 = lang.Failed /\ ((reg1' = reg1 /\ reg2' = reg2) \/ (exists n, reg1' = (<[dst := inl n]> reg1) /\ reg2' = (<[dst := inl n]> reg2))) /\ h' = h /\ stk' = stk /\ cs' = cs /\ c2 = Failed /\ mem2' = mem2) \/ (exists n, c1 = lang.NextI /\ incrementPC (<[dst := inl n]> reg1) = Some reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ c2 = NextI /\ incrementPC' (<[dst := inl n]> reg2) = Some reg2' /\ mem2' = mem2)).
      { simpl in H2, H3. destruct r1.
        - destruct r2.
          + rewrite /base.update_reg /lang.updatePC /= in H2.
            destruct (base.RegLocate (<[dst:=inl (Z.b2z (z <? z0)%Z)]> reg1) PC) eqn:XX; rewrite XX in H2.
            * left. inv H2. rewrite /update_reg /updatePC /= in H3.
              destruct (<[dst:=inl (Z.b2z (z <? z0)%Z)]> reg2 !r! PC) eqn:YY; rewrite YY in H3; [inv H3; repeat split; eauto|].
              destruct (reg_eq_dec dst PC); [subst dst; rewrite /RegLocate lookup_insert /= in YY; inv YY|].
              rewrite /RegLocate lookup_insert_ne in YY; auto.
              rewrite /base.RegLocate lookup_insert_ne in XX; auto.
              rewrite H1 in XX. inv XX.
            * destruct (reg_eq_dec dst PC); [subst dst; rewrite /base.RegLocate lookup_insert in XX; inv XX|].
              rewrite /base.RegLocate lookup_insert_ne in XX; auto.
              rewrite H1 in XX; inv XX. destruct (a + 1)%a eqn:ZZ.
              { inv H2. right. rewrite /updatePC /update_reg /= in H3.
                rewrite /RegLocate lookup_insert_ne in H3; auto.
                generalize (Hsregs _ _ H1); intros XX. rewrite XX /= ZZ in H3. inv H3.
                eexists. repeat split; eauto.
                rewrite /incrementPC lookup_insert_ne // H1 ZZ //.
                rewrite /incrementPC' lookup_insert_ne // XX /= ZZ //. }
              { left. inv H2. rewrite /updatePC /update_reg /= in H3.
                rewrite /RegLocate lookup_insert_ne in H3; auto.
                generalize (Hsregs _ _ H1); intros XX. rewrite XX /= ZZ in H3. inv H3.
                repeat split; eauto. }
          + destruct (Hregsdef r) as [wr Hwr].
            rewrite /base.RegLocate Hwr in H2.
            generalize (Hsregs _ _ Hwr). intros Hwr'.
            rewrite /RegLocate Hwr' in H3. destruct wr.
            * simpl in H3. rewrite /base.update_reg /lang.updatePC /= in H2.
              destruct (base.RegLocate (<[dst:=inl (Z.b2z (z <? z0)%Z)]> reg1) PC) eqn:XX; rewrite XX in H2.
              { left. inv H2. rewrite /update_reg /updatePC /= in H3.
                destruct (<[dst:=inl (Z.b2z (z <? z0)%Z)]> reg2 !r! PC) eqn:YY; rewrite YY in H3; [inv H3; repeat split; eauto|].
                destruct (reg_eq_dec dst PC); [subst dst; rewrite /RegLocate lookup_insert /= in YY; inv YY|].
                rewrite /RegLocate lookup_insert_ne in YY; auto.
                rewrite /base.RegLocate lookup_insert_ne in XX; auto.
                rewrite H1 in XX. inv XX. }
              { destruct (reg_eq_dec dst PC); [subst dst; rewrite /base.RegLocate lookup_insert in XX; inv XX|].
                rewrite /base.RegLocate lookup_insert_ne in XX; auto.
                rewrite H1 in XX; inv XX. destruct (a + 1)%a eqn:ZZ.
                - inv H2. right. rewrite /updatePC /update_reg /= in H3.
                  rewrite /RegLocate lookup_insert_ne in H3; auto.
                  generalize (Hsregs _ _ H1); intros XX. rewrite XX /= ZZ in H3. inv H3.
                  eexists. repeat split; eauto.
                  rewrite /incrementPC lookup_insert_ne // H1 ZZ //.
                  rewrite /incrementPC' lookup_insert_ne // XX /= ZZ //.
                - left. inv H2. rewrite /updatePC /update_reg /= in H3.
                  rewrite /RegLocate lookup_insert_ne in H3; auto.
                  generalize (Hsregs _ _ H1); intros XX. rewrite XX /= ZZ in H3. inv H3.
                  repeat split; eauto. }
            * inv H2. assert (exists c', translate_word (inr c) = inr c').
              { destruct c; simpl; eauto. }
              destruct H0 as [c' Hc']. rewrite Hc' in H3. inv H3.
              left. repeat split; eauto.
        - destruct r2.
          + destruct (Hregsdef r) as [wr Hwr].
            rewrite /base.RegLocate Hwr in H2.
            generalize (Hsregs _ _ Hwr). intros Hwr'.
            rewrite /RegLocate Hwr' in H3. destruct wr.
            * simpl in H3. rewrite /base.update_reg /lang.updatePC /= in H2.
              destruct (base.RegLocate (<[dst:=inl (Z.b2z (z0 <? z)%Z)]> reg1) PC) eqn:XX; rewrite XX in H2.
              { left. inv H2. rewrite /update_reg /updatePC /= in H3.
                destruct (<[dst:=inl (Z.b2z (z0 <? z)%Z)]> reg2 !r! PC) eqn:YY; rewrite YY in H3; [inv H3; repeat   split; eauto|].
                destruct (reg_eq_dec dst PC); [subst dst; rewrite /RegLocate lookup_insert /= in YY; inv YY|].
                rewrite /RegLocate lookup_insert_ne in YY; auto.
                rewrite /base.RegLocate lookup_insert_ne in XX; auto.
                rewrite H1 in XX. inv XX. }
              { destruct (reg_eq_dec dst PC); [subst dst; rewrite /base.RegLocate lookup_insert in XX; inv XX|].
                rewrite /base.RegLocate lookup_insert_ne in XX; auto.
                rewrite H1 in XX; inv XX. destruct (a + 1)%a eqn:ZZ.
                - inv H2. right. rewrite /updatePC /update_reg /= in H3.
                  rewrite /RegLocate lookup_insert_ne in H3; auto.
                  generalize (Hsregs _ _ H1); intros XX. rewrite XX /= ZZ in H3. inv H3.
                  eexists. repeat split; eauto.
                  rewrite /incrementPC lookup_insert_ne // H1 ZZ //.
                  rewrite /incrementPC' lookup_insert_ne // XX /= ZZ //.
                - left. inv H2. rewrite /updatePC /update_reg /= in H3.
                  rewrite /RegLocate lookup_insert_ne in H3; auto.
                  generalize (Hsregs _ _ H1); intros XX. rewrite XX /= ZZ in H3. inv H3.
                  repeat split; eauto. }
            * inv H2. assert (exists c', translate_word (inr c) = inr c').
              { destruct c; simpl; eauto. }
              destruct H0 as [c' Hc']. rewrite Hc' in H3. inv H3.
              left. repeat split; eauto.
          + destruct (Hregsdef r) as [wr Hwr].
            rewrite /base.RegLocate Hwr in H2.
            destruct (Hregsdef r0) as [wr0 Hwr0].
            rewrite /base.RegLocate Hwr0 in H2.
            generalize (Hsregs _ _ Hwr). intros Hwr'.
            rewrite /RegLocate Hwr' in H3.
            generalize (Hsregs _ _ Hwr0). intros Hwr0'.
            rewrite /RegLocate Hwr0' in H3. destruct wr.
            * destruct wr0.
              { simpl in H3. rewrite /base.update_reg /lang.updatePC /= in H2.
                destruct (base.RegLocate (<[dst:=inl (Z.b2z (z <? z0)%Z)]> reg1) PC) eqn:XX; rewrite XX in H2.
                - left. inv H2. rewrite /update_reg /updatePC /= in H3.
                  destruct (<[dst:=inl (Z.b2z (z <? z0)%Z)]> reg2 !r! PC) eqn:YY; rewrite YY in H3; [inv H3; repeat split; eauto|].
                  destruct (reg_eq_dec dst PC); [subst dst; rewrite /RegLocate lookup_insert /= in YY; inv YY|].
                  rewrite /RegLocate lookup_insert_ne in YY; auto.
                  rewrite /base.RegLocate lookup_insert_ne in XX; auto.
                  rewrite H1 in XX. inv XX.
                - destruct (reg_eq_dec dst PC); [subst dst; rewrite /base.RegLocate lookup_insert in XX; inv XX|].
                  rewrite /base.RegLocate lookup_insert_ne in XX; auto.
                  rewrite H1 in XX; inv XX. destruct (a + 1)%a eqn:ZZ.
                  + inv H2. right. rewrite /updatePC /update_reg /= in H3.
                    rewrite /RegLocate lookup_insert_ne in H3; auto.
                    generalize (Hsregs _ _ H1); intros XX. rewrite XX /= ZZ in H3. inv H3.
                    eexists. repeat split; eauto.
                    rewrite /incrementPC lookup_insert_ne // H1 ZZ //.
                   rewrite /incrementPC' lookup_insert_ne // XX /= ZZ //.
                  + left. inv H2. rewrite /updatePC /update_reg /= in H3.
                    rewrite /RegLocate lookup_insert_ne in H3; auto.
                    generalize (Hsregs _ _ H1); intros XX. rewrite XX /= ZZ in H3. inv H3.
                    repeat split; eauto. }
              { inv H2. assert (exists c', translate_word (inr c) = inr c').
                { destruct c; simpl; eauto. }
                destruct H0 as [c' Hc']. rewrite Hc' in H3. inv H3.
                left. repeat split; eauto. } }
      destruct H0 as [AA|AA].
      + destruct AA as [-> [AA [-> [-> [-> [-> ->]]]]]].
        split; [econstructor |]. destruct AA as [[-> ->] | AA]; [split; [|split; [|split; [|split; [|split]]]]; auto|].
        destruct AA as [n [-> ->]]. split; [|split; [|split; [|split; [|split]]]]; auto.
        * intro r; destruct (reg_eq_dec r dst); [subst r; rewrite lookup_insert; eauto|rewrite lookup_insert_ne; auto].
        * intro r. destruct (reg_eq_dec r dst); [subst r; rewrite lookup_insert; inversion 1|].
          rewrite lookup_insert_ne; auto. intros. eapply Hregstk in H0; auto.
        * intro; destruct (reg_eq_dec r dst); [subst r; rewrite !lookup_insert /=; inversion 1; reflexivity|].
          rewrite !lookup_insert_ne; auto.
      + destruct AA as [n [-> [XX [-> [-> [-> [-> [YY ->]]]]]]]].
        split; [econstructor|]. split; [|split; [|split; [|split; [|split]]]]; auto.
        * intros; eapply (incrementPC_is_Some XX).
          destruct (reg_eq_dec r dst); [subst r; rewrite lookup_insert; eauto|rewrite lookup_insert_ne //; auto].
        * intros. rewrite /incrementPC in XX. destruct (reg_eq_dec PC dst); [subst dst; rewrite lookup_insert in XX; inv XX|rewrite lookup_insert_ne in XX; auto].
          rewrite H1 in XX. destruct (a + 1)%a; inv XX.
          destruct (reg_eq_dec r PC); [subst r; rewrite lookup_insert in H0; inv H0|].
          rewrite lookup_insert_ne in H0; auto.
          destruct (reg_eq_dec r dst); [subst r; rewrite lookup_insert in H0; inv H0|].
          rewrite lookup_insert_ne in H0; auto.
          eapply Hregstk in H0; eauto.
        * intros. rewrite /incrementPC in XX. destruct (reg_eq_dec PC dst); [subst dst; rewrite lookup_insert in XX; inv XX|rewrite lookup_insert_ne in XX; auto].
          rewrite H1 in XX. destruct (a + 1)%a eqn:AA; inv XX.
          rewrite /incrementPC' in YY. rewrite lookup_insert_ne in YY; auto.
          generalize (Hsregs _ _ H1). simpl; intro ZZ. rewrite ZZ in YY. rewrite AA in YY; inv YY.
          destruct (reg_eq_dec r PC); [subst r; rewrite lookup_insert in H0; rewrite lookup_insert; inv H0; simpl; auto|].
          rewrite lookup_insert_ne in H0; auto.
          rewrite lookup_insert_ne; auto. destruct (reg_eq_dec r dst); [subst r; rewrite lookup_insert; rewrite lookup_insert in H0; inv H0; reflexivity|].
          rewrite lookup_insert_ne in H0; auto.
          rewrite lookup_insert_ne; auto.
    - (* Add *)
      assert ((c1 = lang.Failed /\ ((reg1' = reg1 /\ reg2' = reg2) \/ (exists n, reg1' = (<[dst := inl n]> reg1) /\ reg2' = (<[dst := inl n]> reg2))) /\ h' = h /\ stk' = stk /\ cs' = cs /\ c2 = Failed /\ mem2' = mem2) \/ (exists n, c1 = lang.NextI /\ incrementPC (<[dst := inl n]> reg1) = Some reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ c2 = NextI /\ incrementPC' (<[dst := inl n]> reg2) = Some reg2' /\ mem2' = mem2)).
      { simpl in H2, H3. destruct r1.
        - destruct r2.
          + rewrite /base.update_reg /lang.updatePC /= in H2.
            destruct (base.RegLocate (<[dst:=inl (z + z0)%Z]> reg1) PC) eqn:XX; rewrite XX in H2.
            * left. inv H2. rewrite /update_reg /updatePC /= in H3.
              destruct (<[dst:=inl (z + z0)%Z]> reg2 !r! PC) eqn:YY; rewrite YY in H3; [inv H3; repeat split; eauto|].
              destruct (reg_eq_dec dst PC); [subst dst; rewrite /RegLocate lookup_insert /= in YY; inv YY|].
              rewrite /RegLocate lookup_insert_ne in YY; auto.
              rewrite /base.RegLocate lookup_insert_ne in XX; auto.
              rewrite H1 in XX. inv XX.
            * destruct (reg_eq_dec dst PC); [subst dst; rewrite /base.RegLocate lookup_insert in XX; inv XX|].
              rewrite /base.RegLocate lookup_insert_ne in XX; auto.
              rewrite H1 in XX; inv XX. destruct (a + 1)%a eqn:ZZ.
              { inv H2. right. rewrite /updatePC /update_reg /= in H3.
                rewrite /RegLocate lookup_insert_ne in H3; auto.
                generalize (Hsregs _ _ H1); intros XX. rewrite XX /= ZZ in H3. inv H3.
                eexists. repeat split; eauto.
                rewrite /incrementPC lookup_insert_ne // H1 ZZ //.
                rewrite /incrementPC' lookup_insert_ne // XX /= ZZ //. }
              { left. inv H2. rewrite /updatePC /update_reg /= in H3.
                rewrite /RegLocate lookup_insert_ne in H3; auto.
                generalize (Hsregs _ _ H1); intros XX. rewrite XX /= ZZ in H3. inv H3.
                repeat split; eauto. }
          + destruct (Hregsdef r) as [wr Hwr].
            rewrite /base.RegLocate Hwr in H2.
            generalize (Hsregs _ _ Hwr). intros Hwr'.
            rewrite /RegLocate Hwr' in H3. destruct wr.
            * simpl in H3. rewrite /base.update_reg /lang.updatePC /= in H2.
              destruct (base.RegLocate (<[dst:=inl (z + z0)%Z]> reg1) PC) eqn:XX; rewrite XX in H2.
              { left. inv H2. rewrite /update_reg /updatePC /= in H3.
                destruct (<[dst:=inl (z + z0)%Z]> reg2 !r! PC) eqn:YY; rewrite YY in H3; [inv H3; repeat   split; eauto|].
                destruct (reg_eq_dec dst PC); [subst dst; rewrite /RegLocate lookup_insert /= in YY; inv YY|].
                rewrite /RegLocate lookup_insert_ne in YY; auto.
                rewrite /base.RegLocate lookup_insert_ne in XX; auto.
                rewrite H1 in XX. inv XX. }
              { destruct (reg_eq_dec dst PC); [subst dst; rewrite /base.RegLocate lookup_insert in XX; inv XX|].
                rewrite /base.RegLocate lookup_insert_ne in XX; auto.
                rewrite H1 in XX; inv XX. destruct (a + 1)%a eqn:ZZ.
                - inv H2. right. rewrite /updatePC /update_reg /= in H3.
                  rewrite /RegLocate lookup_insert_ne in H3; auto.
                  generalize (Hsregs _ _ H1); intros XX. rewrite XX /= ZZ in H3. inv H3.
                  eexists. repeat split; eauto.
                  rewrite /incrementPC lookup_insert_ne // H1 ZZ //.
                  rewrite /incrementPC' lookup_insert_ne // XX /= ZZ //.
                - left. inv H2. rewrite /updatePC /update_reg /= in H3.
                  rewrite /RegLocate lookup_insert_ne in H3; auto.
                  generalize (Hsregs _ _ H1); intros XX. rewrite XX /= ZZ in H3. inv H3.
                  repeat split; eauto. }
            * inv H2. assert (exists c', translate_word (inr c) = inr c').
              { destruct c; simpl; eauto. }
              destruct H0 as [c' Hc']. rewrite Hc' in H3. inv H3.
              left. repeat split; eauto.
        - destruct r2.
          + destruct (Hregsdef r) as [wr Hwr].
            rewrite /base.RegLocate Hwr in H2.
            generalize (Hsregs _ _ Hwr). intros Hwr'.
            rewrite /RegLocate Hwr' in H3. destruct wr.
            * simpl in H3. rewrite /base.update_reg /lang.updatePC /= in H2.
              destruct (base.RegLocate (<[dst:=inl (z0 + z)%Z]> reg1) PC) eqn:XX; rewrite XX in H2.
              { left. inv H2. rewrite /update_reg /updatePC /= in H3.
                destruct (<[dst:=inl (z0 + z)%Z]> reg2 !r! PC) eqn:YY; rewrite YY in H3; [inv H3; repeat   split; eauto|].
                destruct (reg_eq_dec dst PC); [subst dst; rewrite /RegLocate lookup_insert /= in YY; inv YY|].
                rewrite /RegLocate lookup_insert_ne in YY; auto.
                rewrite /base.RegLocate lookup_insert_ne in XX; auto.
                rewrite H1 in XX. inv XX. }
              { destruct (reg_eq_dec dst PC); [subst dst; rewrite /base.RegLocate lookup_insert in XX; inv XX|].
                rewrite /base.RegLocate lookup_insert_ne in XX; auto.
                rewrite H1 in XX; inv XX. destruct (a + 1)%a eqn:ZZ.
                - inv H2. right. rewrite /updatePC /update_reg /= in H3.
                  rewrite /RegLocate lookup_insert_ne in H3; auto.
                  generalize (Hsregs _ _ H1); intros XX. rewrite XX /= ZZ in H3. inv H3.
                  eexists. repeat split; eauto.
                  rewrite /incrementPC lookup_insert_ne // H1 ZZ //.
                  rewrite /incrementPC' lookup_insert_ne // XX /= ZZ //.
                - left. inv H2. rewrite /updatePC /update_reg /= in H3.
                  rewrite /RegLocate lookup_insert_ne in H3; auto.
                  generalize (Hsregs _ _ H1); intros XX. rewrite XX /= ZZ in H3. inv H3.
                  repeat split; eauto. }
            * inv H2. assert (exists c', translate_word (inr c) = inr c').
              { destruct c; simpl; eauto. }
              destruct H0 as [c' Hc']. rewrite Hc' in H3. inv H3.
              left. repeat split; eauto.
          + destruct (Hregsdef r) as [wr Hwr].
            rewrite /base.RegLocate Hwr in H2.
            destruct (Hregsdef r0) as [wr0 Hwr0].
            rewrite /base.RegLocate Hwr0 in H2.
            generalize (Hsregs _ _ Hwr). intros Hwr'.
            rewrite /RegLocate Hwr' in H3.
            generalize (Hsregs _ _ Hwr0). intros Hwr0'.
            rewrite /RegLocate Hwr0' in H3. destruct wr.
            * destruct wr0.
              { simpl in H3. rewrite /base.update_reg /lang.updatePC /= in H2.
                destruct (base.RegLocate (<[dst:=inl (z + z0)%Z]> reg1) PC) eqn:XX; rewrite XX in H2.
                - left. inv H2. rewrite /update_reg /updatePC /= in H3.
                  destruct (<[dst:=inl (z + z0)%Z]> reg2 !r! PC) eqn:YY; rewrite YY in H3; [inv H3; repeat split; eauto|].
                  destruct (reg_eq_dec dst PC); [subst dst; rewrite /RegLocate lookup_insert /= in YY; inv YY|].
                  rewrite /RegLocate lookup_insert_ne in YY; auto.
                  rewrite /base.RegLocate lookup_insert_ne in XX; auto.
                  rewrite H1 in XX. inv XX.
                - destruct (reg_eq_dec dst PC); [subst dst; rewrite /base.RegLocate lookup_insert in XX; inv XX|].
                  rewrite /base.RegLocate lookup_insert_ne in XX; auto.
                  rewrite H1 in XX; inv XX. destruct (a + 1)%a eqn:ZZ.
                  + inv H2. right. rewrite /updatePC /update_reg /= in H3.
                    rewrite /RegLocate lookup_insert_ne in H3; auto.
                    generalize (Hsregs _ _ H1); intros XX. rewrite XX /= ZZ in H3. inv H3.
                    eexists. repeat split; eauto.
                    rewrite /incrementPC lookup_insert_ne // H1 ZZ //.
                  rewrite /incrementPC' lookup_insert_ne // XX /= ZZ //.
                  + left. inv H2. rewrite /updatePC /update_reg /= in H3.
                    rewrite /RegLocate lookup_insert_ne in H3; auto.
                    generalize (Hsregs _ _ H1); intros XX. rewrite XX /= ZZ in H3. inv H3.
                    repeat split; eauto. }
              { inv H2. assert (exists c', translate_word (inr c) = inr c').
                { destruct c; simpl; eauto. }
                destruct H0 as [c' Hc']. rewrite Hc' in H3. inv H3.
                left. repeat split; eauto. } }
      destruct H0 as [AA|AA].
      + destruct AA as [-> [AA [-> [-> [-> [-> ->]]]]]].
        split; [econstructor |]. destruct AA as [[-> ->] | AA]; [split; [|split; [|split; [|split; [|split]]]]; auto|].
        destruct AA as [n [-> ->]]. split; [|split; [|split; [|split; [|split]]]]; auto.
        * intro r; destruct (reg_eq_dec r dst); [subst r; rewrite lookup_insert; eauto|rewrite lookup_insert_ne; auto].
        * intro r. destruct (reg_eq_dec r dst); [subst r; rewrite lookup_insert; inversion 1|].
          rewrite lookup_insert_ne; auto. intros. eapply Hregstk in H0; auto.
        * intro; destruct (reg_eq_dec r dst); [subst r; rewrite !lookup_insert /=; inversion 1; reflexivity|].
          rewrite !lookup_insert_ne; auto.
      + destruct AA as [n [-> [XX [-> [-> [-> [-> [YY ->]]]]]]]].
        split; [econstructor|]. split; [|split; [|split; [|split; [|split]]]]; auto.
        * intros; eapply (incrementPC_is_Some XX).
          destruct (reg_eq_dec r dst); [subst r; rewrite lookup_insert; eauto|rewrite lookup_insert_ne //; auto].
        * intros. rewrite /incrementPC in XX. destruct (reg_eq_dec PC dst); [subst dst; rewrite lookup_insert in XX; inv XX|rewrite lookup_insert_ne in XX; auto].
          rewrite H1 in XX. destruct (a + 1)%a; inv XX.
          destruct (reg_eq_dec r PC); [subst r; rewrite lookup_insert in H0; inv H0|].
          rewrite lookup_insert_ne in H0; auto.
          destruct (reg_eq_dec r dst); [subst r; rewrite lookup_insert in H0; inv H0|].
          rewrite lookup_insert_ne in H0; auto.
          eapply Hregstk in H0; eauto.
        * intros. rewrite /incrementPC in XX. destruct (reg_eq_dec PC dst); [subst dst; rewrite lookup_insert in XX; inv XX|rewrite lookup_insert_ne in XX; auto].
          rewrite H1 in XX. destruct (a + 1)%a eqn:AA; inv XX.
          rewrite /incrementPC' in YY. rewrite lookup_insert_ne in YY; auto.
          generalize (Hsregs _ _ H1). simpl; intro ZZ. rewrite ZZ in YY. rewrite AA in YY; inv YY.
          destruct (reg_eq_dec r PC); [subst r; rewrite lookup_insert in H0; rewrite lookup_insert; inv H0; simpl; auto|].
          rewrite lookup_insert_ne in H0; auto.
          rewrite lookup_insert_ne; auto. destruct (reg_eq_dec r dst); [subst r; rewrite lookup_insert; rewrite lookup_insert in H0; inv H0; reflexivity|].
          rewrite lookup_insert_ne in H0; auto.
          rewrite lookup_insert_ne; auto.

    - (* Sub *) admit.
    - (* Lea *) admit.
    - (* Restrict *) admit.
    - (* Subseg *) admit.
    - (* IsPtr *) admit.
    - (* GetL *) admit.
    - (* GetP *) admit.
    - (* GetB *) admit.
    - (* GetE *) admit.
    - (* GetA *) admit.
    - (* Fail *)
      simpl in H2, H3. inv H2; inv H3.
      split; [|split; [|split; [|split; [|split; [|split]]]]]; auto.
      econstructor.
    - (* Halt *)
      simpl in H2, H3. inv H2; inv H3.
      split; [|split; [|split; [|split; [|split; [|split]]]]]; auto.
      econstructor.
    - (* LoadU *) admit.
    - (* StoreU *) admit.
    - (* PromoteU *) admit.

*)



  Admitted.







  Inductive sim_val: lang.val -> val -> Prop :=
  | sim_val_halted:
      sim_val lang.HaltedV HaltedV
  | sim_val_failed:
      sim_val lang.FailedV FailedV
  | sim_val_next:
      sim_val lang.NextIV NextIV.

  Lemma overlay_to_cap_lang_fsim:
    forall (c: overlay_component),
      is_program e_stk _ _ _ _ lang.can_address_only lang.pwlW lang.is_global c ->
      @forward_simulation_tc overlay_lang cap_lang (lang.initial_state b_stk e_stk c) (initial_state call.r_stk b_stk e_stk (compile c)) sim sim_val.
  Proof.
    intros. econstructor.
    - inv H0. cbn -[list_to_set].
      econstructor.
      + repeat econstructor.
      + intros. econstructor.
        { intros; destruct d1.
          * simpl in H2. inv H2.
            rewrite lookup_empty in H4. inv H4. congruence.
          * simpl in H2. congruence. }
        { intros. econstructor.
          * intros. destruct (reg_eq_dec r call.r_stk).
            { subst r. rewrite lookup_insert. eauto.
              eexists; split; eauto. simpl. split; auto.
              intros. solve_addr. }
            { rewrite lookup_insert_ne; auto.
              destruct (reg_eq_dec r PC).
              - subst r. rewrite lookup_insert.
                eexists; split; eauto. inv Hwfcomp.
                destruct Hw_main as [A [B C] ]. simpl in A.
                destruct w_main; simpl; auto.
                destruct c; simpl in A.
                + destruct c as [ [ [ [p g] b] e] a].
                  simpl in B. auto.
                + elim A.
                + elim A.
              - rewrite lookup_insert_ne; auto.
                exists (inl 0%Z). split; [|simpl; auto].
                rewrite lookup_gset_to_gmap_Some. split; auto.
                eapply all_registers_s_correct. }
          * intros. rewrite lookup_empty in H1; inv H1; congruence.
          * intros. rewrite lookup_empty in H1; inv H1.
          * exists b_stk, b_stk. rewrite region_addrs_empty; [|clear; solve_addr].
            simpl. rewrite dom_empty_L. reflexivity.
          * econstructor. }
        { intros. destruct (reg_eq_dec r call.r_stk).
          * subst r. rewrite lookup_insert in H1.
            inv H1. rewrite lookup_insert. reflexivity.
          * rewrite lookup_insert_ne in H1; auto.
            rewrite lookup_insert_ne; auto.
            destruct (reg_eq_dec r PC).
            { subst r. rewrite lookup_insert in H1.
              rewrite lookup_insert. inv H1. reflexivity. }
            { rewrite lookup_insert_ne in H1; auto.
              rewrite lookup_insert_ne; auto.
              rewrite lookup_gset_to_gmap_Some.
              eapply lookup_gset_to_gmap_Some in H1.
              destruct H1 as [A B]; inv B.
              split; auto. } }
        { intros. rewrite lookup_fmap H1 /=. split; auto.
          inv Hwfcomp. inv Hwf_pre. generalize (Hnpwl _ _ H1).
          intros [A [B C] ]; repeat split; auto. }
        { intros. inv Hwfcomp. inv Hwf_pre. eapply Hdisjstk; auto. }
    - intros. inv H1. inv H2. inv H1.
      assert (e0 = e1 /\ t1 = [] /\ t2 = []).
      { destruct t1, t2; simpl in H2; inv H2; auto.
        - symmetry in H5. apply app_eq_nil in H5.
          destruct H5 as [A B]; inv B.
        - symmetry in H5. apply app_eq_nil in H5.
          destruct H5 as [A B]; inv B. }
      destruct H1 as [A [B C] ]; subst e0; subst t1; subst t2.
      inv H2. rewrite !app_nil_l.
      inv H4. destruct (sim_expr_fill_inv Hsexpr) as [e22 [A B] ].
      generalize (sim_expr_determ Hsexpr A). intros; subst e2. inv H3.
      + (* General exec case*)
        inv B. inv H3.
        specialize (Hinvs ltac:(rewrite can_step_fill /can_step /=; auto)).
        inv Hinvs. inv H1.
        * (* not correct PC *)
          simpl in H4. eexists. split.
          { eapply tc_once. exists []. econstructor; eauto.
            { f_equal; eauto. instantiate (1 := []).
              instantiate (2 := []). reflexivity. }
            econstructor; eauto. econstructor.
            eapply step_exec_fail. simpl; intro HA.
            rewrite /RegLocate in HA.
            inv HA. destruct (reg2 !! PC) as [pcw2|] eqn:X; try congruence.
            subst pcw2. rewrite /base.RegLocate in H4. inv Hcswf.
            destruct (Hregsdef PC) as [pcw1 [Y Y'] ]. rewrite Y in H4.
            generalize (Hsregs PC _ Y). rewrite X; intros Z; inv Z.
            destruct pcw1; simpl in H5; try congruence.
            destruct c0.
            + inv H5. eapply H4. econstructor; eauto.
            + inv H5. eapply H4. econstructor; eauto.
            + inv H5. destruct H3 as [? | [? | ?] ]; congruence. }
          { simpl. econstructor; eauto.
            - eapply sim_expr_fill.
              do 2 econstructor.
            - rewrite can_step_fill /can_step /=. intros [?|?]; discriminate. }
        * (* not correct PC stack *)
          simpl in H5. rewrite /base.RegLocate in H5.
          destruct (reg1 !! PC) as [pcw1|] eqn:X; try congruence. subst pcw1.
          inv Hcswf. destruct (Hregsdef PC) as [pcw1 [HA HB] ].
          rewrite X in HA; inv HA. simpl in HB. destruct HB.
          simpl in H6. destruct (nat_eq_dec d (@length Stackframe cs)); try congruence.
        * (* Regular exec *)
          simpl in H5, H6. rewrite H5 in H6. simpl.
          assert ((exists r, decodeInstrW' (base.MemLocate h a) = Jmp r) \/ (forall r, decodeInstrW' (base.MemLocate h a) <> Jmp r)).
          { clear. destruct (decodeInstrW' (base.MemLocate h a)); eauto. }
          destruct H1 as [HisJmp | HnisJmp].
          { (* Jmp case *)
            destruct HisJmp as [rjmp HisJmp].
            inv Hcswf. destruct (Hregsdef rjmp) as [wrjmp [HA Hinterp] ].
            assert (Hne: (exists br er ar, wrjmp = inr (Ret br er ar)) \/ (forall br er ar, wrjmp <> inr (Ret br er ar))).
            { destruct wrjmp; auto. destruct c0; eauto. }
            destruct Hne as [ [br [er [ar ->] ] ] |Hne]; cycle 1.
            - (* Regular jmp *)
              set res := exec (decodeInstrW (mem2 !m! a)) (reg2, mem2).
              exists ([@ectx_language.fill cap_ectx_lang (map (fun _ => SeqCtx) K) (Instr res.1)], res.2).
              split.
              + eapply tc_once. econstructor. econstructor; eauto.
                * f_equal; eauto. instantiate (1 := []).
                instantiate (2 := []). reflexivity.
                * instantiate (1 := res.2).
                  instantiate (1 := []). reflexivity.
                * econstructor; eauto. econstructor.
                  rewrite /base.RegLocate in H5.
                  destruct (reg1 !! PC) eqn:HPC; [|congruence].
                  subst s. generalize (Hsregs _ _ HPC); simpl.
                  intros HPC'. econstructor; simpl; eauto.
                  { rewrite /RegLocate HPC'. reflexivity. }
                  { rewrite /RegLocate HPC'. generalize (isCorrectPC_translate_word H6).
                    simpl; auto. }
              + rewrite HisJmp. rewrite /base.MemLocate in HisJmp.
                destruct (Hregsdef PC) as [wpc [HPC HinterpPC] ].
                rewrite /base.RegLocate HPC in H5. inv H5.
                generalize (Hsregs _ _ HPC). intro HPC'.
                simpl in HinterpPC. destruct HinterpPC as [HnpwlU Hdom].
                generalize (Hdom a ltac:(inv H6; auto)); intros Haa.
                eapply elem_of_dom in Haa. destruct Haa as [wa Hha].
                rewrite Hha in HisJmp. generalize (Hsh _ _ Hha).
                intros [Hma [HnpwlW [Hisglob Hcan_address] ] ].
                subst res. rewrite /MemLocate Hma -decodeInstrW_translate_word // HisJmp.
                generalize (Hsregs _ _ HA). intros HB.
                rewrite /= /RegLocate /base.RegLocate HA HB /=.
                destruct wrjmp as [njmp | cap] eqn:Hwrjmp; simpl.
                * econstructor.
                  { eapply sim_expr_fill; repeat econstructor. }
                  { intros. econstructor; eauto.
                    - econstructor; eauto.
                      replace (inl njmp) with (word_of_argument reg1 (inr rjmp)) by (simpl; rewrite /base.RegLocate HA //).
                      eapply Hregsdef_preserve_word_of_arg; eauto.
                    - replace (inl njmp) with (word_of_argument reg1 (inr rjmp)) by (simpl; rewrite /base.RegLocate HA //).
                      replace (inl njmp) with (translate_word (word_of_argument reg1 (inr rjmp))) by (simpl; rewrite /base.RegLocate HA //).
                      eapply Hsregs_preserve_word_of_arg; eauto. }
                * destruct cap; [| | congruence].
                  { destruct c0 as [ [ [ [p1 g1] b1] e1] a1].
                    destruct (perm_eq_dec p1 E).
                    - subst p1; simpl. econstructor; eauto.
                      + eapply sim_expr_fill; repeat econstructor.
                      + intros. econstructor; eauto.
                        * econstructor; eauto.
                          simpl. intros. destruct (reg_eq_dec PC r).
                          { subst r; rewrite lookup_insert.
                            eexists; split; eauto. }
                          { rewrite lookup_insert_ne; auto. }
                        * simpl. intros r w. destruct (reg_eq_dec PC r).
                          { subst r; rewrite !lookup_insert; inversion 1; simpl; auto. }
                          { rewrite !lookup_insert_ne //. auto. }
                    - rewrite updatePcPerm_cap_non_E; auto. simpl.
                      econstructor; eauto.
                      + eapply sim_expr_fill; repeat econstructor.
                      + intros. econstructor; eauto.
                        * econstructor; eauto.
                          simpl. intros. destruct (reg_eq_dec PC r).
                          { subst r; rewrite lookup_insert.
                            destruct p1; try congruence; eexists; split; eauto. }
                          { rewrite lookup_insert_ne; auto. }
                        * simpl. intros r w. destruct (reg_eq_dec PC r).
                          { destruct p1; try congruence; subst r; rewrite !lookup_insert; inversion 1; simpl; auto. }
                          { rewrite !lookup_insert_ne //. auto. } }
                  { destruct (perm_eq_dec p0 E).
                    - subst p0; simpl. econstructor; eauto.
                      + eapply sim_expr_fill; repeat econstructor.
                      + intros. econstructor; eauto.
                        * econstructor; eauto.
                          simpl. intros. destruct (reg_eq_dec PC r).
                          { subst r; rewrite lookup_insert.
                            eexists; split; eauto. }
                          { rewrite lookup_insert_ne; auto. }
                        * simpl. intros r w. destruct (reg_eq_dec PC r).
                          { subst r; rewrite !lookup_insert; inversion 1; simpl; auto. }
                          { rewrite !lookup_insert_ne //. auto. }
                    - rewrite updatePcPerm_cap_non_E; auto. simpl.
                      econstructor; eauto.
                      + eapply sim_expr_fill; repeat econstructor.
                      + intros. econstructor; eauto.
                        * econstructor; eauto.
                          simpl. intros. destruct (reg_eq_dec PC r).
                          { subst r; rewrite lookup_insert.
                            destruct p0; try congruence; eexists; split; eauto. }
                          { rewrite lookup_insert_ne; auto. }
                        * simpl. intros r w. destruct (reg_eq_dec PC r).
                          { destruct p0; try congruence; subst r; rewrite !lookup_insert; inversion 1; simpl; auto. }
                          { rewrite !lookup_insert_ne //. auto. } }
            - (* Return jump *)
              admit. }
          assert ((exists r1 r2, decodeInstrW' (base.MemLocate h a) = Jnz r1 r2) \/ (forall r1 r2, decodeInstrW' (base.MemLocate h a) <> Jnz r1 r2)).
          { clear. destruct (decodeInstrW' (base.MemLocate h a)); eauto. }
          destruct H1 as [HisJnz | HnisJnz].
          { destruct HisJnz as [rjnz [rcond HisJnz] ].
            inv Hcswf. destruct (Hregsdef rjnz) as [wrjnz [HA Hinterp] ].
            destruct (Hregsdef rcond) as [wcond [HA' Hinterp_cond] ].
            assert (Hne: (exists br er ar, wrjnz = inr (Ret br er ar)) \/ (forall br er ar, wrjnz <> inr (Ret br er ar))).
            { destruct wrjnz; auto. destruct c0; eauto. }
            destruct Hne as [ [br [er [ar ->] ] ] |Hne]; cycle 1.
            - (* Regular jnz *)
              set res := exec (decodeInstrW (mem2 !m! a)) (reg2, mem2).
              exists ([@ectx_language.fill cap_ectx_lang (map (fun _ => SeqCtx) K) (Instr res.1)], res.2).
              split.
              + eapply tc_once. econstructor. econstructor; eauto.
                * f_equal; eauto. instantiate (1 := []).
                instantiate (2 := []). reflexivity.
                * instantiate (1 := res.2).
                  instantiate (1 := []). reflexivity.
                * econstructor; eauto. econstructor.
                  rewrite /base.RegLocate in H5.
                  destruct (reg1 !! PC) eqn:HPC; [|congruence].
                  subst s. generalize (Hsregs _ _ HPC); simpl.
                  intros HPC'. econstructor; simpl; eauto.
                  { rewrite /RegLocate HPC'. reflexivity. }
                  { rewrite /RegLocate HPC'. generalize (isCorrectPC_translate_word H6).
                    simpl; auto. }
              + rewrite HisJnz. rewrite /base.MemLocate in HisJnz.
                destruct (Hregsdef PC) as [wpc [HPC HinterpPC] ].
                rewrite /base.RegLocate HPC in H5. inv H5.
                generalize (Hsregs _ _ HPC). intro HPC'.
                generalize (Hsregs _ _ HA'). intro HA''.
                simpl in HinterpPC. destruct HinterpPC as [HnpwlU Hdom].
                generalize (Hdom a ltac:(inv H6; auto)); intros Haa.
                eapply elem_of_dom in Haa. destruct Haa as [wa Hha].
                rewrite Hha in HisJnz. generalize (Hsh _ _ Hha).
                intros [Hma [HnpwlW [Hisglob Hcan_address] ] ].
                subst res. rewrite /MemLocate Hma -decodeInstrW_translate_word // HisJnz.
                generalize (Hsregs _ _ HA). intros HB.
                rewrite /= /RegLocate /base.RegLocate HA HA' HA'' HB /=.
                replace (nonZero (translate_word wcond)) with (lang.nonZero wcond); cycle 1.
                { destruct wcond; [reflexivity|]. destruct c0; reflexivity. }
                destruct (lang.nonZero wcond); simpl.
                * destruct wrjnz as [njmp | cap] eqn:Hwrjmp; simpl.
                  { econstructor.
                    { eapply sim_expr_fill; repeat econstructor. }
                    { intros. econstructor; eauto.
                      - econstructor; eauto.
                        replace (inl njmp) with (word_of_argument reg1 (inr rjnz)) by (simpl; rewrite /base.RegLocate HA //).
                        eapply Hregsdef_preserve_word_of_arg; eauto.
                      - replace (inl njmp) with (word_of_argument reg1 (inr rjnz)) by (simpl; rewrite /base.RegLocate HA //).
                        replace (inl njmp) with (translate_word (word_of_argument reg1 (inr rjnz))) by (simpl; rewrite /base.RegLocate HA //).
                        eapply Hsregs_preserve_word_of_arg; eauto. } }
                  { destruct cap; [| | congruence].
                    { destruct c0 as [ [ [ [p1 g1] b1] e1] a1].
                      destruct (perm_eq_dec p1 E).
                      - subst p1; simpl. econstructor; eauto.
                        + eapply sim_expr_fill; repeat econstructor.
                        + intros. econstructor; eauto.
                          * econstructor; eauto.
                            simpl. intros. destruct (reg_eq_dec PC r).
                            { subst r; rewrite lookup_insert.
                              eexists; split; eauto. }
                            { rewrite lookup_insert_ne; auto. }
                          * simpl. intros r w. destruct (reg_eq_dec PC r).
                            { subst r; rewrite !lookup_insert; inversion 1; simpl; auto. }
                            { rewrite !lookup_insert_ne //. auto. }
                      - rewrite updatePcPerm_cap_non_E; auto. simpl.
                        econstructor; eauto.
                        + eapply sim_expr_fill; repeat econstructor.
                        + intros. econstructor; eauto.
                          * econstructor; eauto.
                            simpl. intros. destruct (reg_eq_dec PC r).
                            { subst r; rewrite lookup_insert.
                              destruct p1; try congruence; eexists; split; eauto. }
                            { rewrite lookup_insert_ne; auto. }
                          * simpl. intros r w. destruct (reg_eq_dec PC r).
                            { destruct p1; try congruence; subst r; rewrite !lookup_insert; inversion 1; simpl; auto. }
                            { rewrite !lookup_insert_ne //. auto. } }
                    { destruct (perm_eq_dec p0 E).
                      - subst p0; simpl. econstructor; eauto.
                        + eapply sim_expr_fill; repeat econstructor.
                        + intros. econstructor; eauto.
                          * econstructor; eauto.
                            simpl. intros. destruct (reg_eq_dec PC r).
                            { subst r; rewrite lookup_insert.
                              eexists; split; eauto. }
                            { rewrite lookup_insert_ne; auto. }
                          * simpl. intros r w. destruct (reg_eq_dec PC r).
                            { subst r; rewrite !lookup_insert; inversion 1; simpl; auto. }
                            { rewrite !lookup_insert_ne //. auto. }
                      - rewrite updatePcPerm_cap_non_E; auto. simpl.
                        econstructor; eauto.
                        + eapply sim_expr_fill; repeat econstructor.
                        + intros. econstructor; eauto.
                          * econstructor; eauto.
                            simpl. intros. destruct (reg_eq_dec PC r).
                            { subst r; rewrite lookup_insert.
                              destruct p0; try congruence; eexists; split; eauto. }
                            { rewrite lookup_insert_ne; auto. }
                          * simpl. intros r w. destruct (reg_eq_dec PC r).
                            { destruct p0; try congruence; subst r; rewrite !lookup_insert; inversion 1; simpl; auto. }
                            { rewrite !lookup_insert_ne //. auto. } } }
                * destruct (a + 1)%a eqn:Hap1.
                  { assert (lang.updatePC (reg1, h, stk, cs) = (lang.NextI, (<[PC := inr (Regular (p, g, b, e, a0))]>reg1, h, stk, cs))) as ->.
                    { rewrite /lang.updatePC /= /base.RegLocate HPC /= Hap1 /=.
                      inv H6; destruct p; simpl; naive_solver. }
                    assert (updatePC (reg2, mem2) = (NextI, (<[PC := inr (p, g, b, e, a0)]> reg2, mem2))) as ->.
                    { rewrite /updatePC /= /RegLocate HPC' /= Hap1 /=. 
                      inv H6; destruct p; simpl; naive_solver. }
                    simpl. econstructor.
                    - eapply sim_expr_fill; repeat econstructor.
                    - intros. econstructor; eauto.
                      + econstructor; eauto.
                        intros r; destruct (reg_eq_dec r PC).
                        * subst r; rewrite lookup_insert; eexists; split; auto.
                          simpl. auto.
                        * rewrite lookup_insert_ne; auto.
                      + intros r w. destruct (reg_eq_dec r PC).
                        * subst r; rewrite !lookup_insert; auto.
                          inversion 1; simpl; auto.
                        * rewrite !lookup_insert_ne; auto. }
                  { rewrite /lang.updatePC /updatePC /= /base.RegLocate /RegLocate HPC HPC' /= Hap1 /=.
                    simpl. econstructor.
                    - eapply sim_expr_fill; repeat econstructor.
                    - rewrite can_step_fill /can_step /=. intros [X | X]; discriminate. }
            - (* Return jump *)
              rewrite HisJnz. rewrite /base.MemLocate in HisJnz.
              destruct (Hregsdef PC) as [wpc [HPC HinterpPC] ].
              rewrite /base.RegLocate HPC in H5. inv H5.
              generalize (Hsregs _ _ HPC). intro HPC'.
              generalize (Hsregs _ _ HA'). intro HA''.
              simpl in HinterpPC. destruct HinterpPC as [HnpwlU Hdom].
              generalize (Hdom a ltac:(inv H6; auto)); intros Haa.
              eapply elem_of_dom in Haa. destruct Haa as [wa Hha].
              rewrite Hha in HisJnz. generalize (Hsh _ _ Hha).                
              intros [Hma [HnpwlW [Hisglob Hcan_address] ] ].
              generalize (Hsregs _ _ HA). intros HB.
              assert (Hnz: nonZero (translate_word wcond) = lang.nonZero wcond).
              { destruct wcond; simpl; auto. destruct c0; simpl; auto. }
              destruct (lang.nonZero wcond) eqn:Hnzcond; cycle 1.
              + set res := exec (decodeInstrW (mem2 !m! a)) (reg2, mem2).
                exists ([@ectx_language.fill cap_ectx_lang (map (fun _ => SeqCtx) K) (Instr res.1)], res.2). split.
                * eapply tc_once. econstructor. econstructor; eauto.
                  -- f_equal; eauto. instantiate (1 := []).
                     instantiate (2 := []). reflexivity.
                  -- instantiate (1 := res.2).
                     instantiate (1 := []). reflexivity.
                  -- econstructor; eauto. econstructor.
                     econstructor; simpl; eauto.
                     ++ rewrite /RegLocate HPC'; eauto.
                     ++ rewrite /RegLocate HPC'. generalize (isCorrectPC_translate_word H6).
                        simpl; auto.
                * subst res. rewrite /MemLocate Hma -decodeInstrW_translate_word HisJnz.
                  rewrite /= /base.RegLocate /RegLocate HA' HA'' Hnzcond Hnz /=.
                  destruct (a + 1)%a eqn:Hap1.
                  { assert (lang.updatePC (reg1, h, stk, cs) = (lang.NextI, (<[PC := inr (Regular (p, g, b, e, a0))]>reg1, h, stk, cs))) as ->.
                    { rewrite /lang.updatePC /= /base.RegLocate HPC /= Hap1 /=.
                      inv H6; destruct p; simpl; naive_solver. }
                    assert (updatePC (reg2, mem2) = (NextI, (<[PC := inr (p, g, b, e, a0)]> reg2, mem2))) as ->.
                    { rewrite /updatePC /= /RegLocate HPC' /= Hap1 /=. 
                      inv H6; destruct p; simpl; naive_solver. }
                    simpl. econstructor.
                    - eapply sim_expr_fill; repeat econstructor.
                    - intros. econstructor; eauto.
                      + econstructor; eauto.
                        intros r; destruct (reg_eq_dec r PC).
                        * subst r; rewrite lookup_insert; eexists; split; auto.
                          simpl. auto.
                        * rewrite lookup_insert_ne; auto.
                      + intros r w. destruct (reg_eq_dec r PC).
                        * subst r; rewrite !lookup_insert; auto.
                          inversion 1; simpl; auto.
                        * rewrite !lookup_insert_ne; auto. }
                  { rewrite /lang.updatePC /updatePC /= /base.RegLocate /RegLocate HPC HPC' /= Hap1 /=.
                    simpl. econstructor.
                    - eapply sim_expr_fill; repeat econstructor.
                    - rewrite can_step_fill /can_step /=. intros [X | X]; discriminate. }
              + (* Actual return case *)
                admit. }
          (* Not Jmp nor Jnz so we know we only need one step *)
          set res := exec (decodeInstrW (mem2 !m! a)) (reg2, mem2).
          exists ([@ectx_language.fill cap_ectx_lang (map (fun _ => SeqCtx) K) (Instr res.1)], res.2).
          split.
          { eapply tc_once. econstructor. econstructor; eauto.
            - f_equal; eauto. instantiate (1 := []).
            instantiate (2 := []). reflexivity.
            - instantiate (1 := res.2).
              instantiate (1 := []). reflexivity.
            - econstructor; eauto. econstructor.
              rewrite /base.RegLocate in H5.
              destruct (reg1 !! PC) eqn:HPC; [|congruence].
              subst s. generalize (Hsregs _ _ HPC); simpl.
              intros HPC'. econstructor; simpl; eauto.
              + rewrite /RegLocate HPC'. reflexivity.
              + rewrite /RegLocate HPC'. generalize (isCorrectPC_translate_word H6).
                simpl; auto. }
          { destruct (lang.exec (decodeInstrW' (base.MemLocate h a)) (reg1, h, stk, cs)) as [c1 [ [ [reg1' h'] stk'] cs'] ] eqn:Hexec. simpl.
            destruct res as [c2 [reg2' mem2'] ] eqn:Hexec'. subst res. simpl.
            rewrite /base.RegLocate in H5.
            destruct (reg1 !! PC) eqn:HPC; [|congruence]. subst s.
            eapply exec_sim; eauto. }
        * (* Regular stack exec *) admit.
        * (* Regular call *)
          simpl in H5, H6. rewrite H5 in H6. simpl.
          eexists. split.
          { (* TODO: change machine_run_conf *) admit. } 
          admit.
        * (* Stack call *) admit.
      + (* NextI case *)
        inv B. inv H2. inv H3.
        exists ([@ectx_language.fill cap_ectx_lang (map (fun _ => SeqCtx) K) (Seq (Instr Executable))], (reg2, mem2)). split.
        * eapply tc_once. econstructor. econstructor; eauto.
          { f_equal; eauto. instantiate (1 := []).
            instantiate (2 := []). reflexivity. }
          { instantiate (1 := (reg2, mem2)).
            instantiate (1 := []). reflexivity. }
          { econstructor; eauto.
            econstructor. }
        * specialize (Hinvs ltac:(rewrite can_step_fill /can_step /=; auto)).
          inv Hinvs. econstructor; eauto.
          { eapply sim_expr_fill; eauto.
            repeat econstructor. }
          { intros. econstructor; eauto. } 
      + (* Halted case *)
        inv B. inv H2. inv H3.
        exists ([@ectx_language.fill cap_ectx_lang (map (fun _ => SeqCtx) K) (Instr Halted)], (reg2, mem2)). split.
        * eapply tc_once. econstructor. econstructor; eauto.
          { f_equal; eauto. instantiate (1 := []).
            instantiate (2 := []). reflexivity. }
          { instantiate (1 := (reg2, mem2)).
            instantiate (1 := []). reflexivity. }
          { econstructor; eauto.
            econstructor. }
        * econstructor; eauto.
          { eapply sim_expr_fill; eauto.
            do 3 econstructor. }
          { rewrite can_step_fill /can_step /=. intros [? | ?]; discriminate. }
      + (* Failed case *)
        inv B. inv H2. inv H3.
        exists ([@ectx_language.fill cap_ectx_lang (map (fun _ => SeqCtx) K) (Instr Failed)], (reg2, mem2)). split.
        * eapply tc_once. econstructor. econstructor; eauto.
          { f_equal; eauto. instantiate (1 := []).
            instantiate (2 := []). reflexivity. }
          { instantiate (1 := (reg2, mem2)).
            instantiate (1 := []). reflexivity. }
          { econstructor; eauto.
            econstructor. }
        * econstructor; eauto.
          { eapply sim_expr_fill; eauto.
            do 3 econstructor. }
          { rewrite can_step_fill /can_step /=; intros [? | ?]; discriminate. }
    - intros. inv H1. destruct H3 as [A B].
      inv H2. simpl in A. inv A. destruct x; simpl in B; [|congruence].
      inv Hsexpr. inv H2; [congruence| | |]; inv B; eexists; split; econstructor; simpl; split; reflexivity.
  Admitted.

End overlay_to_cap_lang.
