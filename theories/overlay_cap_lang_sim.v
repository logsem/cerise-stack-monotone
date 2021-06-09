From cap_machine.overlay Require Import base lang.
From cap_machine Require Import cap_lang simulation linking region machine_run.
From cap_machine.rules Require rules_base.
From stdpp Require Import base gmap fin_maps list.
From Coq Require Import Eqdep_dec ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section overlay_to_cap_lang.

  (* TODO: update solve_addr *)
  Lemma ltb_addr_spec:
    forall a1 a2,
      ltb_addr a1 a2 = true <-> (a1 < a2)%a.
  Proof.
    intros; unfold ltb_addr, lt_addr. eapply Z.ltb_lt.
  Qed.

  Lemma leb_addr_spec:
    forall a1 a2,
      leb_addr a1 a2 = true <-> (a1 <= a2)%a.
  Proof.
    intros; unfold leb_addr, le_addr. eapply Z.leb_le.
  Qed.

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

  Lemma translate_word_cap:
    forall c,
      exists c', translate_word (inr c) = inr c'.
  Proof.
    simpl; destruct c; eauto.
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
  | sim_expr_instr_failed:
      sim_expr (lang.Instr lang.Failed) (Instr Failed)
  | sim_expr_instr_halted:
      sim_expr (lang.Instr lang.Halted) (Instr Halted)
  | sim_expr_seq:
      forall f1 f2,
        sim_flag f1 f2 ->
        sim_expr (lang.Seq (lang.Instr f1)) (Seq (Instr f2)).

  Lemma sim_expr_determ:
    forall e1 e2 e2',
      sim_expr e1 e2 ->
      sim_expr e1 e2' ->
      e2 = e2'.
  Proof.
    intros e1 e2 e2' A B; inv A; inv B; auto.
    f_equal. f_equal. eapply sim_flag_determ; eauto.
  Qed.

  Lemma cons_is_app:
    forall K (a: lang.ectx_item), a :: K = K ++ [a].
  Proof.
    induction K.
    - reflexivity.
    - simpl. intros; destruct a, a0.
      rewrite IHK. reflexivity.
  Qed.

  Lemma sim_expr_exec_inv:
    forall K,
      sim_expr (fill K (lang.Instr lang.Executable)) (@ectx_language.fill cap_ectx_lang (map (fun=> SeqCtx) K) (Instr Executable)) ->
      K = [lang.SeqCtx].
  Proof.
    destruct K.
    - simpl; inversion 1.
    - rewrite (cons_is_app K e) /fill /= map_app !ectxi_language.fill_app.
      destruct e; simpl. inversion 1.
      destruct K; [reflexivity|].
      exfalso. rewrite (cons_is_app K e) /fill /= ectxi_language.fill_app in H1.
      destruct e; simpl in H1. inv H1.
  Qed.

  Lemma sim_expr_next_inv:
    forall K,
      sim_expr (fill K (lang.Instr lang.NextI)) (@ectx_language.fill cap_ectx_lang (map (fun=> SeqCtx) K) (Instr NextI)) ->
      K = [lang.SeqCtx].
  Proof.
    destruct K.
    - simpl; inversion 1.
    - rewrite (cons_is_app K e) /fill /= map_app !ectxi_language.fill_app.
      destruct e; simpl. inversion 1.
      destruct K; [reflexivity|].
      exfalso. rewrite (cons_is_app K e) /fill /= ectxi_language.fill_app in H1.
      destruct e; simpl in H1. inv H1.
  Qed.

  Lemma fill_inv_instr:
    forall K cf e1,
      ectxi_language.fill K e1 = lang.Instr cf ->
      K = [] /\ e1 = lang.Instr cf.
  Proof.
    destruct K; [simpl; auto|].
    rewrite (cons_is_app K e) /fill /=.
    intros. rewrite ectxi_language.fill_app in H0.
    destruct e; simpl in H0; inv H0.
  Qed.

(*  Lemma sim_expr_fill:
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
  Qed.*)

  Lemma z_of_argument_inv_Some:
    forall reg arg n,
      lang.z_of_argument reg arg = Some n ->
      (arg = inl n) \/ (exists r, arg = inr r /\ reg !! r = Some (inl n)).
  Proof.
    destruct arg; simpl; intros.
    - inv H0; left; auto.
    - right; exists r; split; auto.
      destruct (reg !! r); inv H0; auto.
      destruct s; inv H2; auto.
  Qed.

  Lemma z_of_argument_inv_None:
    forall reg arg,
      (forall r, is_Some (reg !! r)) ->
      lang.z_of_argument reg arg = None ->
      (exists r c, arg = inr r /\ reg !! r = Some (inr c)).
  Proof.
    destruct arg; simpl; intros; try congruence.
    exists r. generalize (H0 r); intro A.
    destruct (reg !! r); inv H1.
    destruct s; inv H3; eauto.
    inv A; congruence.
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

  Definition activation_code: list base.Word :=
    [ inl (encodeInstr (Mov (R 1 eq_refl) (inr PC)))
    ; inl (encodeInstr (Lea (R 1 eq_refl) (inl (-1)%Z)))
    ; inl (encodeInstr (Load call.r_stk (R 1 eq_refl)))]
    ++ List.map inl call.pop_env_instrs
    ++ [ inl (encodeInstr (LoadU PC call.r_stk (inl (- 1)%Z)))].

  Lemma activation_code_length:
    length activation_code = 66.
  Proof.
    rewrite /activation_code !app_length map_length call.pop_env_instrs_length /=.
    reflexivity.
  Qed.

  Definition is_return (stk: base.Mem) a e: Prop :=
    forall i,
      i < 66 ->
      exists ai, (a + i)%a = Some ai /\ 
                 (ai < e)%a /\
                 activation_code !! i = stk !! ai.

  Definition interp (w: base.Word) (h: base.Mem) (stk: base.Mem) (cs: list Stackframe): Prop :=
    match w with
    | inl n => True
    | inr (Regular _) => lang.pwlW w = false /\ lang.can_address_only w (dom _ h)
    | inr (Stk d p b e a) => d = length cs /\ forall x, (b <= x < lang.canReadUpTo w)%a (* min e canReadUpTo ? *) -> exists w, stk !! x = Some w
    | inr (Ret b e a) => match cs with
                         | [] => False
                         | (reg', stk')::cs' =>
                            exists e_stk a_stk,
                              reg' !! call.r_stk = Some (inr (Stk (length cs') URWLX b e_stk ^(a_stk + 1)%a)) /\
                              (a_stk + 33)%a = Some a /\
                              (exists pcp pcg pcb pce pca, reg' !! PC = Some (inr (Regular (pcp, pcg, pcb, pce, pca))) /\ (pcp = RX \/ pcp = RWX \/ pcp = RWLX) /\
                              exists pcam1, stk' !! a_stk = Some (inr (Regular (pcp, pcg, pcb, pce, pcam1))) /\ (pcam1 + 1)%a = Some pca) /\
                              (b <= a_stk < e)%a /\
                              (e <= e_stk)%a /\
                              (forall i, i < 31 -> exists ri, ((list_difference all_registers [PC; call.r_stk]) !! i) = Some ri /\ stk' !! ^(a_stk + (S i))%a = reg' !! ri) /\
                              stk' !! ^(a_stk + 32)%a = Some (inr (Stk (length cs') URWLX b e_stk ^(a_stk + 32)%a)) /\
                              is_return stk' a e
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
        (Hcontiguous: exists b_stk e_stk a_stk, reg !! call.r_stk = Some (inr (Stk (length cs) URWLX b_stk e_stk a_stk)) /\ dom (gset _) stk = list_to_set (region_addrs b_stk ^(a_stk + 98)%a))
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
        * eapply sim_expr_exec_inv in Hsexpr. subst K.
          simpl. repeat econstructor.
        * rewrite can_step_fill /can_step /=; intros [A | A]; discriminate.
      + destruct H0 as [-> [-> [-> [<- [<- [<- [<- Hincrement'] ] ] ]  ] ] ].
        econstructor.
        * eapply sim_expr_exec_inv in Hsexpr. subst K.
          simpl. repeat econstructor.
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
    - (* Lt *)
      assert (match (lang.z_of_argument reg1 r1, lang.z_of_argument reg1 r2) with
              | (Some n1, Some n2) => 
                match incrementPC (<[dst:=inl (Z.b2z (n1 <? n2)%Z)]> reg1) with
                | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inl (Z.b2z (n1 <? n2)%Z)]> reg2) = Some reg2' /\ mem2' = mem2
                | None => c1 = lang.Failed /\ c2 = Failed
                end
              | (_, _) => c1 = lang.Failed /\ c2 = Failed
      end).
      { assert (Hregsome1: forall r, is_Some (reg1 !!r)).
        { intros. destruct (Hregsdef r) as [rw [-> _] ]. eauto. }
        destruct (lang.z_of_argument reg1 r1) as [n1|] eqn:Hr1.
        - destruct (lang.z_of_argument reg1 r2) as [n2|] eqn:Hr2.
          + eapply z_of_argument_inv_Some in Hr1.
            eapply z_of_argument_inv_Some in Hr2.
            assert (XX: lang.exec (Lt dst r1 r2) (reg1, h, stk, cs) = lang.updatePC (<[dst:=inl (Z.b2z (n1 <? n2)%Z)]> reg1, h, stk, cs)).
            { rewrite /lang.exec /=. destruct Hr1 as [-> | [r1' [-> Hr1eq] ] ].
              - destruct Hr2 as [-> | [r2' [-> Hr2eq] ] ].
                + reflexivity.
                + rewrite /base.RegLocate Hr2eq //.
              - rewrite /base.RegLocate Hr1eq.
                destruct Hr2 as [-> | [r2' [-> Hr2eq] ] ]; [reflexivity| rewrite Hr2eq //]. }
            rewrite XX in H1; clear XX.
            assert (XX: exec (Lt dst r1 r2) (reg2, mem2) = updatePC (<[dst:=inl (Z.b2z (n1 <? n2)%Z)]> reg2, mem2)).
            { rewrite /exec /=. destruct Hr1 as [-> | [r1' [-> Hr1eq] ] ].
              - destruct Hr2 as [-> | [r2' [-> Hr2eq] ] ]; [reflexivity|].
                rewrite /RegLocate (Hsregs _ _ Hr2eq) //.
              - rewrite /RegLocate (Hsregs _ _ Hr1eq) /=.
                destruct Hr2 as [-> | [r2' [-> Hr2eq] ] ]; [reflexivity|].
                rewrite (Hsregs _ _ Hr2eq) //. }
            rewrite XX in H2; clear XX.
            rewrite /base.update_reg /= in H1.
            assert (exists w, (<[dst:=inl (Z.b2z (n1 <? n2)%Z)]> reg1) !! PC = Some w /\ (<[dst:=inl (Z.b2z (n1 <? n2)%Z)]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
            { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert /=; eauto|].
              rewrite !lookup_insert_ne //.
              eexists; rewrite HPC; split; auto. }
            destruct (incrementPC (<[dst:=inl (Z.b2z (n1 <? n2)%Z)]> reg1)) as [reg1''|] eqn:HX.
            * erewrite incrementPC_success_updatePC in H1; eauto.
              eapply incrementPC_success_incrementPC' in HX; eauto.
              destruct HX as [reg2'' HX].
              rewrite HX.
              eapply rules_base.incrementPC_success_updatePC in HX.
              destruct HX as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
              rewrite Z3 -Z4 in H2. inv H1; inv H2; repeat split; auto.
            * erewrite incrementPC_fail_updatePC in H1; eauto.
              inv H1; split; auto.
              eapply incrementPC_fail_incrementPC' in HX; eauto.
              erewrite rules_base.incrementPC_fail_updatePC in H2; eauto.
              inv H2; auto.
          + simpl in H1, H2.
            eapply z_of_argument_inv_None in Hr2; eauto.
            destruct Hr2 as [r2' [cap2 [-> Hr2eq] ] ].
            rewrite /base.RegLocate Hr2eq in H1.
            destruct (translate_word_cap cap2) as [cap2' Hcap2'].
            generalize (Hsregs _ _ Hr2eq). rewrite Hcap2'; intros Hr2eq'.
            rewrite /RegLocate Hr2eq' in H2.
            destruct r1; [inv H1; inv H2; split; auto|].
            destruct (reg1 !! r) as [w1|]; destruct (reg2 !! r) as [w2|]; try (destruct w1); try (destruct w2); inv H1; inv H2; split; auto.
        - simpl in H1, H2.
          eapply z_of_argument_inv_None in Hr1; eauto.
          destruct Hr1 as [r1' [cap1 [-> Hr1eq] ] ].
          rewrite /base.RegLocate Hr1eq in H1.
          destruct (translate_word_cap cap1) as [cap1' Hcap1'].
          generalize (Hsregs _ _ Hr1eq). rewrite Hcap1'; intros Hr1eq'.
          rewrite /RegLocate Hr1eq' in H2.
          destruct r2; inv H1; inv H2; auto. }
      destruct (lang.z_of_argument reg1 r1) as [n1|] eqn:Hn1; cycle 1.
      + destruct H0 as [-> ->]. econstructor.
        * eapply sim_expr_exec_inv in Hsexpr. subst K.
          simpl. repeat econstructor.
        * rewrite can_step_fill /can_step /=; intros [A | A]; discriminate.
      + destruct (lang.z_of_argument reg1 r2) as [n2|] eqn:Hn2; cycle 1.
        * destruct H0 as [-> ->]. econstructor.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            simpl. repeat econstructor. }
          { rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
        * destruct (incrementPC (<[dst:=inl (Z.b2z (n1 <? n2)%Z)]> reg1)) as [reg1''|] eqn:Hincrement; cycle 1.
          { destruct H0 as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              simpl. repeat econstructor.
            - rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
          { destruct H0 as [-> [-> [-> [-> [-> [-> [Hincrement' ->] ] ] ] ] ] ].
            econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              simpl. repeat econstructor.
            - intros _. eapply incrementPC_inv_Some in Hincrement.
              destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in  Hincrement; elim Hincrement|].
              rewrite lookup_insert_ne // in Hincrement.
              rewrite HPC in Hincrement. destruct Hincrement as [ap1 [Hap1 [-> XX] ] ] .
              eapply rules_base.incrementPC_Some_inv in Hincrement'.
              rewrite lookup_insert_ne // in Hincrement'.
              rewrite (Hsregs _ _ HPC) /= in Hincrement'.
              destruct Hincrement' as [? [? [? [? [? [? [XXX [Hap1' [-> XY] ] ] ] ] ] ] ] ]; inv XXX.
              rewrite Hap1 in Hap1'; inv Hap1'.
              econstructor; eauto.
              + econstructor; eauto. intros.
                destruct (reg_eq_dec PC r).
                * subst r; rewrite lookup_insert. eexists; split; eauto.
                  simpl; auto.
                * rewrite lookup_insert_ne //. destruct (reg_eq_dec dst r).
                  { subst r; rewrite lookup_insert. eexists; split; eauto.
                    simpl; auto. }
                  { rewrite lookup_insert_ne //. }
              + intros r; destruct (reg_eq_dec PC r); [subst r|].
                * rewrite !lookup_insert; inversion 1; simpl; auto.
                * rewrite !(lookup_insert_ne _ PC) //. destruct (reg_eq_dec dst r); [subst r|].
                  { rewrite !lookup_insert; inversion 1; simpl; auto. }
                  { rewrite !lookup_insert_ne //. auto. } }
    - (* Add *)
      assert (match (lang.z_of_argument reg1 r1, lang.z_of_argument reg1 r2) with
              | (Some n1, Some n2) => 
                match incrementPC (<[dst:=inl (n1 + n2)%Z]> reg1) with
                | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inl (n1 + n2)%Z]> reg2) = Some reg2' /\ mem2' = mem2
                | None => c1 = lang.Failed /\ c2 = Failed
                end
              | (_, _) => c1 = lang.Failed /\ c2 = Failed
      end).
      { assert (Hregsome1: forall r, is_Some (reg1 !!r)).
        { intros. destruct (Hregsdef r) as [rw [-> _] ]. eauto. }
        destruct (lang.z_of_argument reg1 r1) as [n1|] eqn:Hr1.
        - destruct (lang.z_of_argument reg1 r2) as [n2|] eqn:Hr2.
          + eapply z_of_argument_inv_Some in Hr1.
            eapply z_of_argument_inv_Some in Hr2.
            assert (XX: lang.exec (machine_base.Add dst r1 r2) (reg1, h, stk, cs) = lang.updatePC (<[dst:=inl ((n1 + n2)%Z)]> reg1, h, stk, cs)).
            { rewrite /lang.exec /=. destruct Hr1 as [-> | [r1' [-> Hr1eq] ] ].
              - destruct Hr2 as [-> | [r2' [-> Hr2eq] ] ].
                + reflexivity.
                + rewrite /base.RegLocate Hr2eq //.
              - rewrite /base.RegLocate Hr1eq.
                destruct Hr2 as [-> | [r2' [-> Hr2eq] ] ]; [reflexivity| rewrite Hr2eq //]. }
            rewrite XX in H1; clear XX.
            assert (XX: exec (machine_base.Add dst r1 r2) (reg2, mem2) = updatePC (<[dst:=inl ((n1 + n2)%Z)]> reg2, mem2)).
            { rewrite /exec /=. destruct Hr1 as [-> | [r1' [-> Hr1eq] ] ].
              - destruct Hr2 as [-> | [r2' [-> Hr2eq] ] ]; [reflexivity|].
                rewrite /RegLocate (Hsregs _ _ Hr2eq) //.
              - rewrite /RegLocate (Hsregs _ _ Hr1eq) /=.
                destruct Hr2 as [-> | [r2' [-> Hr2eq] ] ]; [reflexivity|].
                rewrite (Hsregs _ _ Hr2eq) //. }
            rewrite XX in H2; clear XX.
            rewrite /base.update_reg /= in H1.
            assert (exists w, (<[dst:=inl ((n1 + n2)%Z)]> reg1) !! PC = Some w /\ (<[dst:=inl ((n1 + n2)%Z)]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
            { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert /=; eauto|].
              rewrite !lookup_insert_ne //.
              eexists; rewrite HPC; split; auto. }
            destruct (incrementPC (<[dst:=inl ((n1 + n2)%Z)]> reg1)) as [reg1''|] eqn:HX.
            * erewrite incrementPC_success_updatePC in H1; eauto.
              eapply incrementPC_success_incrementPC' in HX; eauto.
              destruct HX as [reg2'' HX].
              rewrite HX.
              eapply rules_base.incrementPC_success_updatePC in HX.
              destruct HX as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
              rewrite Z3 -Z4 in H2. inv H1; inv H2; repeat split; auto.
            * erewrite incrementPC_fail_updatePC in H1; eauto.
              inv H1; split; auto.
              eapply incrementPC_fail_incrementPC' in HX; eauto.
              erewrite rules_base.incrementPC_fail_updatePC in H2; eauto.
              inv H2; auto.
          + simpl in H1, H2.
            eapply z_of_argument_inv_None in Hr2; eauto.
            destruct Hr2 as [r2' [cap2 [-> Hr2eq] ] ].
            rewrite /base.RegLocate Hr2eq in H1.
            destruct (translate_word_cap cap2) as [cap2' Hcap2'].
            generalize (Hsregs _ _ Hr2eq). rewrite Hcap2'; intros Hr2eq'.
            rewrite /RegLocate Hr2eq' in H2.
            destruct r1; [inv H1; inv H2; split; auto|].
            destruct (reg1 !! r) as [w1|]; destruct (reg2 !! r) as [w2|]; try (destruct w1); try (destruct w2); inv H1; inv H2; split; auto.
        - simpl in H1, H2.
          eapply z_of_argument_inv_None in Hr1; eauto.
          destruct Hr1 as [r1' [cap1 [-> Hr1eq] ] ].
          rewrite /base.RegLocate Hr1eq in H1.
          destruct (translate_word_cap cap1) as [cap1' Hcap1'].
          generalize (Hsregs _ _ Hr1eq). rewrite Hcap1'; intros Hr1eq'.
          rewrite /RegLocate Hr1eq' in H2.
          destruct r2; inv H1; inv H2; auto. }
      destruct (lang.z_of_argument reg1 r1) as [n1|] eqn:Hn1; cycle 1.
      + destruct H0 as [-> ->]. econstructor.
        * eapply sim_expr_exec_inv in Hsexpr. subst K.
          simpl. repeat econstructor.
        * rewrite can_step_fill /can_step /=; intros [A | A]; discriminate.
      + destruct (lang.z_of_argument reg1 r2) as [n2|] eqn:Hn2; cycle 1.
        * destruct H0 as [-> ->]. econstructor.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            simpl. repeat econstructor. }
          { rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
        * destruct (incrementPC (<[dst:=inl ((n1 + n2)%Z)]> reg1)) as [reg1''|] eqn:Hincrement; cycle 1.
          { destruct H0 as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              simpl. repeat econstructor.
            - rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
          { destruct H0 as [-> [-> [-> [-> [-> [-> [Hincrement' ->] ] ] ] ] ] ].
            econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              simpl. repeat econstructor.
            - intros _. eapply incrementPC_inv_Some in Hincrement.
              destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in  Hincrement; elim Hincrement|].
              rewrite lookup_insert_ne // in Hincrement.
              rewrite HPC in Hincrement. destruct Hincrement as [ap1 [Hap1 [-> XX] ] ] .
              eapply rules_base.incrementPC_Some_inv in Hincrement'.
              rewrite lookup_insert_ne // in Hincrement'.
              rewrite (Hsregs _ _ HPC) /= in Hincrement'.
              destruct Hincrement' as [? [? [? [? [? [? [XXX [Hap1' [-> XY] ] ] ] ] ] ] ] ]; inv XXX.
              rewrite Hap1 in Hap1'; inv Hap1'.
              econstructor; eauto.
              + econstructor; eauto. intros.
                destruct (reg_eq_dec PC r).
                * subst r; rewrite lookup_insert. eexists; split; eauto.
                  simpl; auto.
                * rewrite lookup_insert_ne //. destruct (reg_eq_dec dst r).
                  { subst r; rewrite lookup_insert. eexists; split; eauto.
                    simpl; auto. }
                  { rewrite lookup_insert_ne //. }
              + intros r; destruct (reg_eq_dec PC r); [subst r|].
                * rewrite !lookup_insert; inversion 1; simpl; auto.
                * rewrite !(lookup_insert_ne _ PC) //. destruct (reg_eq_dec dst r); [subst r|].
                  { rewrite !lookup_insert; inversion 1; simpl; auto. }
                  { rewrite !lookup_insert_ne //. auto. } }
    - (* Sub *)
      assert (match (lang.z_of_argument reg1 r1, lang.z_of_argument reg1 r2) with
              | (Some n1, Some n2) => 
                match incrementPC (<[dst:=inl ((n1 - n2)%Z)]> reg1) with
                | Some reg1'' => c1 = lang.NextI /\ c2 = NextI /\ reg1'' = reg1' /\ h' = h /\ stk' = stk /\ cs' = cs /\ incrementPC' (<[dst:=inl ((n1 - n2)%Z)]> reg2) = Some reg2' /\ mem2' = mem2
                | None => c1 = lang.Failed /\ c2 = Failed
                end
              | (_, _) => c1 = lang.Failed /\ c2 = Failed
      end).
      { assert (Hregsome1: forall r, is_Some (reg1 !!r)).
        { intros. destruct (Hregsdef r) as [rw [-> _] ]. eauto. }
        destruct (lang.z_of_argument reg1 r1) as [n1|] eqn:Hr1.
        - destruct (lang.z_of_argument reg1 r2) as [n2|] eqn:Hr2.
          + eapply z_of_argument_inv_Some in Hr1.
            eapply z_of_argument_inv_Some in Hr2.
            assert (XX: lang.exec (Sub dst r1 r2) (reg1, h, stk, cs) = lang.updatePC (<[dst:=inl ((n1 - n2)%Z)]> reg1, h, stk, cs)).
            { rewrite /lang.exec /=. destruct Hr1 as [-> | [r1' [-> Hr1eq] ] ].
              - destruct Hr2 as [-> | [r2' [-> Hr2eq] ] ].
                + reflexivity.
                + rewrite /base.RegLocate Hr2eq //.
              - rewrite /base.RegLocate Hr1eq.
                destruct Hr2 as [-> | [r2' [-> Hr2eq] ] ]; [reflexivity| rewrite Hr2eq //]. }
            rewrite XX in H1; clear XX.
            assert (XX: exec (Sub dst r1 r2) (reg2, mem2) = updatePC (<[dst:=inl ((n1 - n2)%Z)]> reg2, mem2)).
            { rewrite /exec /=. destruct Hr1 as [-> | [r1' [-> Hr1eq] ] ].
              - destruct Hr2 as [-> | [r2' [-> Hr2eq] ] ]; [reflexivity|].
                rewrite /RegLocate (Hsregs _ _ Hr2eq) //.
              - rewrite /RegLocate (Hsregs _ _ Hr1eq) /=.
                destruct Hr2 as [-> | [r2' [-> Hr2eq] ] ]; [reflexivity|].
                rewrite (Hsregs _ _ Hr2eq) //. }
            rewrite XX in H2; clear XX.
            rewrite /base.update_reg /= in H1.
            assert (exists w, (<[dst:=inl ((n1 - n2)%Z)]> reg1) !! PC = Some w /\ (<[dst:=inl ((n1 - n2)%Z)]> reg2) !! PC = Some (translate_word w)) as [wpc [HY HZ] ].
            { destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert /=; eauto|].
              rewrite !lookup_insert_ne //.
              eexists; rewrite HPC; split; auto. }
            destruct (incrementPC (<[dst:=inl ((n1 - n2)%Z)]> reg1)) as [reg1''|] eqn:HX.
            * erewrite incrementPC_success_updatePC in H1; eauto.
              eapply incrementPC_success_incrementPC' in HX; eauto.
              destruct HX as [reg2'' HX].
              rewrite HX.
              eapply rules_base.incrementPC_success_updatePC in HX.
              destruct HX as [p' [g' [b' [e' [a' [a'' [Z1 [Z2 [Z3 [Z4 Z5] ] ] ] ] ] ] ] ] ].
              rewrite Z3 -Z4 in H2. inv H1; inv H2; repeat split; auto.
            * erewrite incrementPC_fail_updatePC in H1; eauto.
              inv H1; split; auto.
              eapply incrementPC_fail_incrementPC' in HX; eauto.
              erewrite rules_base.incrementPC_fail_updatePC in H2; eauto.
              inv H2; auto.
          + simpl in H1, H2.
            eapply z_of_argument_inv_None in Hr2; eauto.
            destruct Hr2 as [r2' [cap2 [-> Hr2eq] ] ].
            rewrite /base.RegLocate Hr2eq in H1.
            destruct (translate_word_cap cap2) as [cap2' Hcap2'].
            generalize (Hsregs _ _ Hr2eq). rewrite Hcap2'; intros Hr2eq'.
            rewrite /RegLocate Hr2eq' in H2.
            destruct r1; [inv H1; inv H2; split; auto|].
            destruct (reg1 !! r) as [w1|]; destruct (reg2 !! r) as [w2|]; try (destruct w1); try (destruct w2); inv H1; inv H2; split; auto.
        - simpl in H1, H2.
          eapply z_of_argument_inv_None in Hr1; eauto.
          destruct Hr1 as [r1' [cap1 [-> Hr1eq] ] ].
          rewrite /base.RegLocate Hr1eq in H1.
          destruct (translate_word_cap cap1) as [cap1' Hcap1'].
          generalize (Hsregs _ _ Hr1eq). rewrite Hcap1'; intros Hr1eq'.
          rewrite /RegLocate Hr1eq' in H2.
          destruct r2; inv H1; inv H2; auto. }
      destruct (lang.z_of_argument reg1 r1) as [n1|] eqn:Hn1; cycle 1.
      + destruct H0 as [-> ->]. econstructor.
        * eapply sim_expr_exec_inv in Hsexpr. subst K.
          simpl. repeat econstructor.
        * rewrite can_step_fill /can_step /=; intros [A | A]; discriminate.
      + destruct (lang.z_of_argument reg1 r2) as [n2|] eqn:Hn2; cycle 1.
        * destruct H0 as [-> ->]. econstructor.
          { eapply sim_expr_exec_inv in Hsexpr. subst K.
            simpl. repeat econstructor. }
          { rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
        * destruct (incrementPC (<[dst:=inl ((n1 - n2)%Z)]> reg1)) as [reg1''|] eqn:Hincrement; cycle 1.
          { destruct H0 as [-> ->]. econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              simpl. repeat econstructor.
            - rewrite can_step_fill /can_step /=; intros [A | A]; discriminate. }
          { destruct H0 as [-> [-> [-> [-> [-> [-> [Hincrement' ->] ] ] ] ] ] ].
            econstructor.
            - eapply sim_expr_exec_inv in Hsexpr. subst K.
              simpl. repeat econstructor.
            - intros _. eapply incrementPC_inv_Some in Hincrement.
              destruct (reg_eq_dec dst PC); [subst dst; rewrite lookup_insert in  Hincrement; elim Hincrement|].
              rewrite lookup_insert_ne // in Hincrement.
              rewrite HPC in Hincrement. destruct Hincrement as [ap1 [Hap1 [-> XX] ] ] .
              eapply rules_base.incrementPC_Some_inv in Hincrement'.
              rewrite lookup_insert_ne // in Hincrement'.
              rewrite (Hsregs _ _ HPC) /= in Hincrement'.
              destruct Hincrement' as [? [? [? [? [? [? [XXX [Hap1' [-> XY] ] ] ] ] ] ] ] ]; inv XXX.
              rewrite Hap1 in Hap1'; inv Hap1'.
              econstructor; eauto.
              + econstructor; eauto. intros.
                destruct (reg_eq_dec PC r).
                * subst r; rewrite lookup_insert. eexists; split; eauto.
                  simpl; auto.
                * rewrite lookup_insert_ne //. destruct (reg_eq_dec dst r).
                  { subst r; rewrite lookup_insert. eexists; split; eauto.
                    simpl; auto. }
                  { rewrite lookup_insert_ne //. }
              + intros r; destruct (reg_eq_dec PC r); [subst r|].
                * rewrite !lookup_insert; inversion 1; simpl; auto.
                * rewrite !(lookup_insert_ne _ PC) //. destruct (reg_eq_dec dst r); [subst r|].
                  { rewrite !lookup_insert; inversion 1; simpl; auto. }
                  { rewrite !lookup_insert_ne //. auto. } }
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
      + eapply sim_expr_exec_inv in Hsexpr. subst K.
        simpl. repeat econstructor.
      + rewrite can_step_fill /can_step /=; intros [A | A]; discriminate.
    - (* Halt *)
      simpl in H1, H2. inv H1; inv H2.
      econstructor.
      + eapply sim_expr_exec_inv in Hsexpr. subst K.
        simpl. repeat econstructor.
      + rewrite can_step_fill /can_step /=; intros [A | A]; discriminate.
    - (* LoadU *) admit.
    - (* StoreU *) admit.
    - (* PromoteU *) admit.
  Admitted.

  Lemma stack_is_Some:
    forall cs d,
      is_Some (stack d cs) <-> d < length cs.
  Proof.
    induction cs; intros.
    - simpl. split; [inversion 1; discriminate|lia].
    - simpl. destruct (nat_eq_dec d (length cs)).
      + subst d. split; [lia|eauto].
      + rewrite IHcs. lia.
  Qed.

  Lemma foldl_pop_instrs_acc:
    forall rlist acc,
      foldl (λ (b : list Z) (r : RegName), call.pop_instrs r ++ b) acc rlist =
      (foldl (λ (b : list Z) (r : RegName), call.pop_instrs r ++ b) [] rlist) ++ acc.
  Proof.
    induction rlist; intros.
    - reflexivity.
    - simpl in IHrlist. simpl foldl. rewrite IHrlist.
      rewrite (IHrlist ([encodeInstr (LoadU a call.r_stk (inl (-1)%Z)); encodeInstr (Lea call.r_stk (inl (-1)%Z))])).
      rewrite -app_assoc /=. reflexivity.
  Qed.

  Lemma foldl_pop_instrs_cons:
    forall rlist r,
      foldl (λ (b : list Z) (r : RegName), call.pop_instrs r ++ b) [] (r :: rlist) =
      (foldl (λ (b : list Z) (r : RegName), call.pop_instrs r ++ b) [] rlist) ++ (call.pop_instrs r).
  Proof.
    intros. simpl foldl. rewrite foldl_pop_instrs_acc. reflexivity.
  Qed.

  Lemma foldl_pop_instrs_length:
    forall rlist,
      length (foldl (λ (b : list Z) (r : RegName), call.pop_instrs r ++ b) [] rlist) = 2 * length rlist.
  Proof.
    induction rlist.
    - reflexivity.
    - rewrite foldl_pop_instrs_cons app_length IHrlist.
      simpl. lia.
  Qed.

  Lemma all_registers_NoDup :
    NoDup all_registers.
  Proof.
    rewrite /all_registers.
    repeat (
      apply NoDup_cons_2;
      first (repeat (rewrite not_elem_of_cons; split; [done|]); apply not_elem_of_nil)
    ).
    by apply NoDup_nil.
  Qed.

  Lemma pop_env_instrs_spec:
    forall rlist br er ar ar_final bstk estk astk astk_final reg mem (reg': base.Reg)
    (Hstkfinal: (astk + (- (length rlist)))%a = Some (astk_final))
    (Hlowstk: (bstk <= astk_final)%a)
    (Hhistk: (astk < estk)%a)
    (Harfinal: (ar + (2 * (length rlist)))%a = Some (ar_final))
    (Hlowar: (br <= ar)%a)
    (Hhiar: (ar_final < er)%a)
    (Hnotin: PC ∉ rlist /\ call.r_stk ∉ rlist)
    (Hinstrs: forall i, 
                i < 2 * (length rlist) -> 
                exists ai, (ar + i)%a = Some ai /\ 
                mem !! ai = (translate_word <$> (inl <$> (foldl (fun b r => (call.pop_instrs r) ++ b) [] rlist))) !! i)
    (Hcontents: forall i,
                  i < length rlist ->
                  exists ai, (astk + - (S i))%a = Some ai /\
                  exists r, rlist !! (length rlist - S i) = Some r /\
                  exists rwi, mem !! ai = Some (translate_word rwi) /\
                  reg' !! r = Some rwi),
    rtc erased_step 
      ([Seq (Instr Executable)], (<[PC:=inr (RX, Monotone, br, er, ar)]> (<[call.r_stk:=inr (URWLX, Monotone, bstk, estk, astk)]> reg), mem))
      ([Seq (Instr Executable)], (<[PC:=inr (RX, Monotone, br, er, ar_final)]> (<[call.r_stk:=inr (URWLX, Monotone, bstk, estk, astk_final)]> (foldr (fun r reg => <[r:= translate_word (base.RegLocate reg' r)]> reg) reg rlist)), mem)).
  Proof.
    induction rlist; intros.
    - simpl. simpl in Hstkfinal. assert (astk = astk_final) as <- by (clear -Hstkfinal; solve_addr).
      simpl in Harfinal. assert (ar = ar_final) as <- by (clear -Harfinal; solve_addr).
      apply rtc_refl.
    - eapply rtc_transitive.
      + eapply IHrlist; auto.
        * instantiate (1 := ^(astk + - length rlist)%a).
          clear -Hstkfinal. solve_addr.
        * clear -Hstkfinal Hlowstk; solve_addr.
        * instantiate (1 := ^(ar + 2 * length rlist)%a).
          clear -Harfinal. solve_addr.
        * clear -Harfinal Hhiar; solve_addr.
        * destruct Hnotin as [Hnotin1 Hnotin2].
          eapply not_elem_of_cons in Hnotin1.
          eapply not_elem_of_cons in Hnotin2.
          destruct Hnotin1, Hnotin2. split; auto.
        * rewrite foldl_pop_instrs_cons in Hinstrs.
          intros. generalize (Hinstrs i ltac:(clear -H0; simpl; lia)).
          intros [ai [Hai HA] ]. exists ai; split; auto.
          rewrite !fmap_app in HA.
          rewrite lookup_app_l in HA; auto.
          rewrite !fmap_length. rewrite foldl_pop_instrs_length; auto.
        * intros. generalize (Hcontents i ltac:(clear -H0; simpl; lia)).
          intros [ai [Hai [r [HA [rwi HB] ] ] ] ]. exists ai; split; auto.
          exists r. rewrite lookup_cons_ne_0 in HA; [|simpl; lia].
          replace (length (a :: rlist) - S i) with (S (length rlist - S i)) in HA by (simpl; lia).
          simpl in HA. split; auto.
          exists rwi; eauto.
      + destruct (Hinstrs (2 * length rlist) ltac:(simpl; lia)) as [ar' [Har' Hinstr0] ].
        destruct (Hinstrs (2 * length rlist + 1) ltac:(simpl; lia)) as [arp1 [Harp1 Hinstr1] ].
        destruct (Hcontents (length rlist) ltac:(simpl; lia)) as [astkm1 [Hastkm1 [r0 [Hr0 [rw0 [Hrw0 Hrw0'] ] ] ] ] ].
        simpl. replace (length (a :: rlist) - S (length rlist)) with 0 in Hr0 by (simpl; lia).
        simpl in Hr0; inv Hr0.
        rewrite /(base.RegLocate _ r0) Hrw0'.
        eapply rtc_l.
        * econstructor. econstructor; eauto.
          { f_equal; eauto. instantiate (1 := []).
            instantiate (2 := []). reflexivity. }
          { instantiate (1 := []). econstructor; try reflexivity.
            instantiate (2 := [SeqCtx]). reflexivity.
            econstructor. eapply step_exec_instr; simpl; auto.
            rewrite /RegLocate lookup_insert; reflexivity.
            rewrite /RegLocate lookup_insert. econstructor; eauto.
            clear -Hlowar Hhiar Harfinal. solve_addr. }
        * simpl. assert (^(ar + 2 * length rlist)%a = ar') as -> by (clear -Har'; solve_addr).
          rewrite foldl_pop_instrs_cons !fmap_app in Hinstr0.
          rewrite lookup_app_r in Hinstr0; [|rewrite !fmap_length foldl_pop_instrs_length; lia].
          rewrite !fmap_length foldl_pop_instrs_length in Hinstr0.
          replace (2 * length rlist - 2 * length rlist) with 0 in Hinstr0 by lia.
          simpl in Hinstr0.
          rewrite /MemLocate Hinstr0 /= decode_encode_instr_inv /=.
          rewrite /RegLocate lookup_insert_ne //.
          rewrite lookup_insert /=.
          assert ((^(astk + - length rlist) + -1)%a = Some astkm1) as -> by (clear -Hastkm1; solve_addr).
          destruct (Addr_le_dec bstk astkm1) as [_|X]; [|clear -X Hastkm1 Hstkfinal Hlowstk; solve_addr].
          destruct (Addr_lt_dec astkm1 ^(astk + - length rlist)%a) as [_|X]; [|clear -X Hastkm1; solve_addr].
          destruct (Addr_le_dec ^(astk + - length rlist)%a estk) as [_|X]; [|clear -X Hhistk Hastkm1; solve_addr].
          rewrite /update_reg /= /MemLocate Hrw0.
          assert (HnPCr0: r0 <> PC).
          { destruct Hnotin as [Hnotin1 _]. apply not_elem_of_cons in Hnotin1.
            destruct Hnotin1; auto. }
          assert (Hnrstkr0: r0 <> call.r_stk).
          { destruct Hnotin as [_ Hnotin1]. apply not_elem_of_cons in Hnotin1.
            destruct Hnotin1; auto. }
          rewrite /updatePC /= /RegLocate (lookup_insert_ne _ r0 PC) //.
          rewrite lookup_insert.
          assert ((ar' + 1)%a = Some arp1) as -> by (clear -Har' Harp1; solve_addr).
          rewrite /update_reg /=.
          eapply rtc_l. 
          { econstructor. econstructor; eauto.
            { f_equal; eauto. instantiate (1 := []).
              instantiate (2 := []). reflexivity. }
            { instantiate (1 := []). econstructor; try reflexivity.
              instantiate (2 := []). reflexivity. econstructor. } }
          simpl. eapply rtc_l.
          { econstructor. econstructor; eauto.
            { f_equal; eauto. instantiate (1 := []).
              instantiate (2 := []). reflexivity. }
            { instantiate (1 := []). econstructor; try reflexivity.
              instantiate (2 := [SeqCtx]). reflexivity.
              econstructor. eapply step_exec_instr; simpl; auto.
              rewrite /RegLocate lookup_insert; reflexivity.
              rewrite /RegLocate lookup_insert. econstructor; eauto.
              clear -Hlowar Hhiar Harfinal Harp1. solve_addr. } }
          simpl. rewrite foldl_pop_instrs_cons !fmap_app in Hinstr1.
          rewrite lookup_app_r in Hinstr1; [|rewrite !fmap_length foldl_pop_instrs_length; lia].
          rewrite !fmap_length foldl_pop_instrs_length in Hinstr1.
          replace (2 * length rlist + 1 - 2 * length rlist) with 1 in Hinstr1 by lia.
          simpl in Hinstr1.
          rewrite /MemLocate Hinstr1 /= decode_encode_instr_inv /=.
          rewrite /RegLocate (lookup_insert_ne _ PC call.r_stk) //.
          rewrite (lookup_insert_ne _ r0 call.r_stk) //.
          rewrite (lookup_insert_ne _ PC call.r_stk) //.
          rewrite lookup_insert. assert ((^(astk + - length rlist) + -1)%a = Some astkm1) as -> by (clear -Hastkm1; solve_addr).
          destruct (Addr_le_dec astkm1 ^(astk + - length rlist)%a) as [_|X]; [|clear -X Hstkfinal Hlowstk Hastkm1; solve_addr].
          rewrite /update_reg /= /updatePC /= /RegLocate (lookup_insert_ne _ call.r_stk PC) //.
          rewrite lookup_insert.
          assert ((arp1 + 1)%a = Some ar_final) as -> by (clear -Harp1 Harfinal; solve_addr).
          rewrite /update_reg /=.
          rewrite (insert_commute _ call.r_stk PC) //.
          rewrite insert_insert.
          rewrite (insert_commute _ r0 PC) //.
          rewrite (insert_commute _ call.r_stk PC) //.
          rewrite insert_insert.
          rewrite (insert_commute _ r0 call.r_stk) //.
          rewrite insert_insert.
          replace astkm1 with astk_final by (clear -Hastkm1 Hstkfinal; solve_addr).
          eapply rtc_once. econstructor. econstructor; eauto.
          { f_equal; eauto. instantiate (1 := []).
            instantiate (2 := []). reflexivity. }
          { reflexivity. }
          econstructor. instantiate (2:=[]); auto.
          reflexivity. econstructor.
  Qed.

  Lemma foldr_insert_spec:
    forall rlist nregs reg r,
      NoDup rlist ->
      (In r rlist -> 
      (foldr (λ (r : RegName) (reg : Reg), <[r:=translate_word (base.RegLocate nregs r)]> reg) reg rlist) !! r = Some (translate_word (base.RegLocate nregs r))) /\
      (~ In r rlist ->
      (foldr (λ (r : RegName) (reg : Reg), <[r:=translate_word (base.RegLocate nregs r)]> reg) reg rlist) !! r = reg !! r).
  Proof.
    induction rlist; intros.
    - split; [inversion 1|intro; reflexivity].
    - split.
      + intro X; inv X.
        * simpl. rewrite lookup_insert //.
        * simpl. inv H0. eapply elem_of_list_In in H1.
          rewrite lookup_insert_ne; [|intro; subst a; apply H4; auto].
          destruct (IHrlist nregs reg r H5) as [A B].
          eapply A; eapply elem_of_list_In; auto.
      + intros. simpl. rewrite lookup_insert_ne; [|intro; subst r; eapply H1; left; auto].
        inv H0. destruct (IHrlist nregs reg r H5) as [A B].
        eapply B. intro; eapply H1; right; auto.
  Qed.      

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
      inv H4. inv Hsexpr.
      { symmetry in H2; eapply fill_inv_instr in H2.
        destruct H2; subst K; subst e1'.
        inv H3. }
      { symmetry in H2; eapply fill_inv_instr in H2.
        destruct H2; subst K; subst e1'.
        inv H3. }
      inv H3.
      + (* General exec case*)
        assert (K = [lang.SeqCtx] /\ f1 = lang.Executable) as [-> ->].
        { destruct K; [simpl in H1; inv H1|]. rewrite cons_is_app in H1.
          destruct e; rewrite ectxi_language.fill_app /= in H1.
          inv H1. symmetry in H5; eapply fill_inv_instr in H5.
          destruct H5 as [-> ?]. inv H1; auto. }
        specialize (Hinvs ltac:(rewrite can_step_fill /can_step /=; auto)).
        inv Hinvs. clear H1. inv H2. inv H4.
        * (* not correct PC *)
          simpl in H3. eexists. split.
          { eapply tc_once. exists []. econstructor; eauto.
            { f_equal; eauto. instantiate (1 := []).
              instantiate (2 := []). reflexivity. }
            econstructor; eauto. instantiate (2 := [SeqCtx]).
            reflexivity. econstructor.
            eapply step_exec_fail. simpl; intro HA.
            rewrite /RegLocate in HA.
            inv HA. destruct (reg2 !! PC) as [pcw2|] eqn:X; try congruence.
            subst pcw2. rewrite /base.RegLocate in H3. inv Hcswf.
            destruct (Hregsdef PC) as [pcw1 [Y Y'] ]. rewrite Y in H3.
            generalize (Hsregs PC _ Y). rewrite X; intros Z; inv Z.
            destruct pcw1; simpl in H5; try congruence.
            destruct c0.
            + inv H5. eapply H3. econstructor; eauto.
            + inv H5. eapply H3. econstructor; eauto.
            + inv H5. destruct H4 as [? | [? | ?] ]; congruence. }
          { simpl. econstructor; eauto.
            - repeat econstructor.
            - rewrite /can_step /=. intros [?|?]; discriminate. }
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
              exists ([Seq (Instr res.1)], res.2).
              split.
              + eapply tc_once. econstructor. econstructor; eauto.
                * f_equal; eauto. instantiate (1 := []).
                  instantiate (2 := []). reflexivity.
                * instantiate (1 := res.2).
                  instantiate (1 := []). reflexivity.
                * econstructor; eauto. instantiate (2 := [SeqCtx]).
                  reflexivity. reflexivity.
                  rewrite /base.RegLocate in H5.
                  destruct (reg1 !! PC) eqn:HPC; [|congruence].
                  subst s. generalize (Hsregs _ _ HPC); simpl.
                  intros HPC'. econstructor; simpl; eauto.
                  econstructor; simpl; eauto.
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
                  { repeat econstructor. }
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
                      + repeat econstructor.
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
                      + repeat econstructor.
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
                      + repeat econstructor.
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
                      + repeat econstructor.
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
              rewrite /base.RegLocate in H5.
              destruct (Hregsdef PC) as [wpc [HPC HinterpPC] ].
              rewrite HPC in H5; inv H5. generalize (Hsregs _ _ HPC); simpl.
              intros HPC'. simpl in Hinterp; destruct cs as [| [nregs nstk] cs']; [elim Hinterp|].
              destruct Hinterp as [ne_stk [na_stk [Hr_stk [Haris [ (pcp & pcg & pcb & pce & pca & HnewPC & Hcanexec & pcam1 & HnewPC' & Hpcam1eq) [Hrange [Hrange' [XA [XB XC] ] ] ] ] ] ] ] ].
              simpl in HinterpPC. destruct HinterpPC as [HnpwlU Hdom].
              eexists ([Seq (Instr NextI)], (fmap translate_word nregs, mem2)).
              rewrite HisJmp. rewrite /lang.exec /base.RegLocate HA /=.
              split.
              + eapply tc_rtc_r.
                * eapply tc_once. econstructor. econstructor; eauto.
                  { f_equal; eauto. instantiate (1 := []).
                    instantiate (2 := []). reflexivity. }
                  { instantiate (1 := []). econstructor; try reflexivity.
                    instantiate (2 := [SeqCtx]). reflexivity.
                    econstructor. eapply step_exec_instr; simpl; auto.
                    rewrite /RegLocate HPC'; reflexivity.
                    rewrite /RegLocate HPC'. inv H6; econstructor; eauto. }
                * simpl. generalize (Hdom a ltac:(inv H6; auto)); intros Haa.
                  eapply elem_of_dom in Haa. destruct Haa as [wa Hha].
                  rewrite /base.MemLocate Hha in HisJmp. generalize (Hsh _ _ Hha).
                  intros [Hma [HnpwlW [Hisglob Hcan_address] ] ].
                  rewrite /MemLocate Hma -decodeInstrW_translate_word // HisJmp.
                  rewrite /= /RegLocate. generalize (Hsregs _ _ HA).
                  intros HA'. rewrite HA'. simpl. eapply rtc_l.
                  { exists []. eapply step_atomic with (t1:=[]). 
                    1,2: reflexivity. cbn.
                    eapply ectx_language.Ectx_step with (K:=[]).
                    1,2: reflexivity. cbn. econstructor. }
                  simpl. rewrite /is_return in XC.
                  rewrite /update_reg /=.
                  assert (XD: forall i, i < 66 -> is_Some (activation_code !! i)).
                  { intros. apply lookup_lt_is_Some.
                    rewrite activation_code_length //. }
                  assert (XC': forall i, i < 66 -> exists ai, (ar + i)%a = Some ai /\ (ai < er)%a /\ (translate_word <$> activation_code) !! i = mem2 !! ai).
                  { intros. generalize (XC i H1). intros [ai [A [B C] ] ].
                    exists ai. split; auto. split; auto.
                    rewrite list_lookup_fmap C.
                    assert (exists wai, nstk !! ai = Some wai) as [wai Hwai].
                    { destruct (XD _ H1) as [wai Hwai].
                      rewrite Hwai in C; eauto. }
                    inv Hcs. generalize (Hstksim0 _ _ Hwai). rewrite Hwai.
                    simpl. intros [? [? ?] ]. congruence. }
                  eapply rtc_l.
                  { exists []. eapply step_atomic with (t1:=[]).
                    1,2: reflexivity. cbn.
                    eapply ectx_language.Ectx_step with (K:=[SeqCtx]).
                    1,2: reflexivity. econstructor. eapply step_exec_instr; eauto.
                    - rewrite /= /RegLocate lookup_insert; eauto.
                    - rewrite /= /RegLocate lookup_insert. econstructor; auto.
                      destruct (XC 0 ltac:(lia)) as [ar' [Har' [XX _] ] ].
                      clear -Hrange Haris Har' XX. solve_addr. }
                  simpl. generalize (XC' 0 ltac:(lia)). intros [ar' [XX [_ XY] ] ].
                  assert (ar = ar') by (clear -XX; solve_addr). subst ar'; clear XX.
                  rewrite list_lookup_fmap in XY. rewrite /activation_code /= in XY.
                  rewrite /MemLocate -XY /=. clear XY.
                  destruct (XC' 1 ltac:(lia)) as [arp1 [Harp1 [Hlow1 Hcode1] ] ].
                  rewrite decode_encode_instr_inv /= /RegLocate lookup_insert /update_reg /updatePC /RegLocate !(lookup_insert_ne _ (R 1 _) PC) // /= !lookup_insert Harp1 /update_reg /=.
                  eapply rtc_l.
                  { exists []. eapply step_atomic with (t1:=[]). 
                    1,2: reflexivity. cbn.
                    eapply ectx_language.Ectx_step with (K:=[]).
                    1,2: reflexivity. cbn. econstructor. }
                  simpl. eapply rtc_l.
                  { exists []. eapply step_atomic with (t1:=[]).
                    1,2: reflexivity. cbn.
                    eapply ectx_language.Ectx_step with (K:=[SeqCtx]).
                    1,2: reflexivity. econstructor. eapply step_exec_instr; eauto.
                    - rewrite /= /RegLocate lookup_insert; eauto.
                    - rewrite /= /RegLocate lookup_insert. econstructor; auto.
                      clear -Hlow1 Hrange Harp1 Hlow1 Haris. solve_addr. }
                  simpl. rewrite list_lookup_fmap /= in Hcode1.
                  rewrite /MemLocate -Hcode1 /= decode_encode_instr_inv /= /RegLocate !(lookup_insert_ne _ PC (R 1 _)) // !lookup_insert.
                  assert (Harm1eq: (ar + -1)%a = Some (^(na_stk + 32)%a)).
                  { clear -Haris Hrange. solve_addr. }
                  rewrite Harm1eq /update_reg /=.
                  destruct (XC' 2 ltac:(lia)) as [arp2 [Harp2 [Hlow2 Hcode2] ] ].
                  assert ((arp1 + 1)%a = Some arp2) by (clear -Harp1 Harp2; solve_addr).
                  rewrite /updatePC /RegLocate /= (lookup_insert_ne _ (R 1 _) PC) // lookup_insert H1 /update_reg /=. clear H1.
                  eapply rtc_l.
                  { exists []. eapply step_atomic with (t1:=[]). 
                    1,2: reflexivity. cbn.
                    eapply ectx_language.Ectx_step with (K:=[]).
                    1,2: reflexivity. cbn. econstructor. }
                  simpl. eapply rtc_l.
                  { exists []. eapply step_atomic with (t1:=[]).
                    1,2: reflexivity. cbn.
                    eapply ectx_language.Ectx_step with (K:=[SeqCtx]).
                    1,2: reflexivity. econstructor. eapply step_exec_instr; eauto.
                    - rewrite /= /RegLocate lookup_insert; eauto.
                    - rewrite /= /RegLocate lookup_insert. econstructor; auto.
                      clear -Hlow2 Hrange Harp2 Haris. solve_addr. }
                  simpl. rewrite list_lookup_fmap /= in Hcode2.
                  rewrite /MemLocate -Hcode2 /= decode_encode_instr_inv /= /RegLocate !(lookup_insert_ne _ PC (R 1 _)) // !lookup_insert.
                  rewrite andb_true_l.
                  assert ((br <=? ^(na_stk + 32))%a && (^(na_stk + 32) <? er)%a = true) as ->.
                  { clear -Hrange Harm1eq Haris Harp1 Hlow1. apply andb_true_iff.
                    split. apply leb_addr_spec. solve_addr.
                    apply ltb_addr_spec. solve_addr. }
                  rewrite /update_reg /=. inv Hcs.
                  generalize (Hstksim0 _ _ XB). simpl. intros [YA [ [_ YB] _] ].
                  rewrite /MemLocate YA /=.
                  destruct (XC' 3 ltac:(lia)) as [arp3 [Harp3 [Hlow3 Hcode3] ] ].
                  assert ((arp2 + 1)%a = Some arp3) by (clear -Harp2 Harp3; solve_addr).
                  rewrite /updatePC /RegLocate /= (lookup_insert_ne _ call.r_stk) // lookup_insert /= H1 /update_reg /=. clear H1.
                  eapply rtc_l.
                  { exists []. eapply step_atomic with (t1:=[]). 
                    1,2: reflexivity. cbn.
                    eapply ectx_language.Ectx_step with (K:=[]).
                    1,2: reflexivity. cbn. econstructor. }
                  simpl. rewrite -!(insert_commute _ PC (R 1 _)) //.
                  rewrite -!(insert_commute _ PC call.r_stk) //.
                  rewrite !insert_insert. eapply rtc_transitive.
                  { eapply pop_env_instrs_spec with (rlist := list_difference all_registers [PC; call.r_stk]).
                    - replace (length (list_difference all_registers [PC; call.r_stk])) with 31 by reflexivity.
                      instantiate (1 := ^(na_stk + 1)%a).
                      clear -Haris. solve_addr.
                    - clear -Hrange. solve_addr.
                    - clear -Hrange Hrange' Harm1eq Harp1 Hlow1. solve_addr.
                    - instantiate (1 := ^(ar + 65)%a).
                      simpl length. destruct (XC 65 ltac:(lia)) as [arp65 [? _] ].
                      clear -H1 Harp3. solve_addr.
                    - clear -Hrange Harp3 Haris. solve_addr.
                    - destruct (XC 65 ltac:(lia)) as [arp65 [X [Y _] ] ].
                      clear -X Y; solve_addr.
                    - split; eapply not_elem_of_list; [left|right;left].
                    - simpl length. simpl Nat.mul.
                      intros i Hilt. generalize (XC' (3 + i) ltac:(lia)).
                      intros [ai [Hai [Hailt Hcodei] ] ].
                      exists ai. split; [clear -Harp3 Hai; solve_addr|].
                      rewrite /activation_code in Hcodei.
                      rewrite fmap_app lookup_app_r in Hcodei; [|simpl; lia].
                      rewrite fmap_app lookup_app_l in Hcodei; [|rewrite !fmap_length map_length call.pop_env_instrs_length /=; lia].
                      simpl length in Hcodei. replace (3 + i - 3) with i in Hcodei by lia.
                      rewrite -Hcodei. reflexivity.
                    - simpl length. intros i Hilt.
                      generalize (XA (31 - S i) ltac:(clear -Hilt; lia)).
                      intros [ri [Hri Hstkri] ].
                      exists (^(na_stk + S (31 - S i))%a).
                      split; [clear -Haris Hrange Hilt; solve_addr|].
                      exists ri; split; auto.
                      destruct (Hregsdef0 ri) as [rwi [Hrwi Hinterprwi] ].
                      exists rwi. split; eauto.
                      rewrite Hrwi in Hstkri.
                      generalize (Hstksim0 _ _ Hstkri). intros [? ?]; auto. }
                  eapply rtc_l.
                  { econstructor. econstructor; eauto.
                    - instantiate (2 := []). instantiate (3 := []).
                      reflexivity.
                    - econstructor. 
                      + instantiate (2 := [SeqCtx]). reflexivity.
                      + reflexivity.
                      + econstructor. eapply step_exec_instr; eauto.
                        * rewrite /RegLocate lookup_insert //.
                        * rewrite /RegLocate lookup_insert.
                          econstructor; auto. destruct (XC' 65 ltac:(lia)) as [arp65 [Harp65 [Hlt65 ?] ] ].
                          clear -Hrange Harp65 Hlt65 Haris. solve_addr. }
                  rewrite !app_nil_l. 
                  set (rlist := list_difference all_registers [PC; call.r_stk]).
                  rewrite /cap_lang.mem /MemLocate.
                  destruct (XC' 65 ltac:(lia)) as [arp65 [Harp65 [Hlt65 Hcode65] ] ].
                  replace (^(ar + 65)%a) with arp65 by (clear -Harp65; solve_addr).
                  rewrite /activation_code !fmap_app in Hcode65.
                  rewrite lookup_app_r in Hcode65; [|simpl; lia].
                  rewrite lookup_app_r in Hcode65; [|simpl; lia].
                  simpl in Hcode65. rewrite -Hcode65.
                  rewrite /decodeInstrW decode_encode_instr_inv.
                  rewrite /exec /reg /RegLocate.
                  rewrite (lookup_insert_ne _ PC) //.
                  rewrite lookup_insert. rewrite /isU /z_of_argument.
                  rewrite /verify_access.
                  assert ((^(na_stk + 1) + -1)%a = Some na_stk) as -> by (clear -Hrange; solve_addr).
                  destruct (Addr_le_dec br na_stk) as [_|X]; [|exfalso; clear -X Hrange; solve_addr].
                  destruct (Addr_lt_dec na_stk ^(na_stk + 1)%a) as [_|X]; [|exfalso; clear -X Hrange; solve_addr].
                  destruct (Addr_le_dec ^(na_stk + 1)%a ne_stk) as [_|X]; [|exfalso; clear -X Hrange Hrange'; solve_addr].
                  rewrite /update_reg /cap_lang.mem /reg /MemLocate.
                  generalize (Hstksim0 _ _ HnewPC'). intros [AA [AB AC] ].
                  rewrite AA.
                  assert (ZZ: (foldr (λ (r : RegName) (reg : Reg), <[r:=translate_word (base.RegLocate nregs r)]> reg) (<[R 1 (erefl true):=inr (RX, Monotone, br, er, ^(na_stk + 32)%a)]> reg2) rlist) = <[PC := reg2 !r! PC]> (<[call.r_stk := reg2 !r! call.r_stk]> (translate_word <$> nregs))).
                  { eapply map_eq. intros.
                    assert (Hdup: NoDup rlist).
                    { subst rlist. apply NoDup_list_difference.
                      apply all_registers_NoDup. }
                    destruct (in_dec reg_eq_dec i rlist).
                    - rewrite (proj1 (foldr_insert_spec _ _ i Hdup) i0).
                      eapply elem_of_list_In in i0.
                      eapply elem_of_list_difference in i0.
                      destruct i0 as [Hin Hnin].
                      rewrite lookup_insert_ne; [|intro; subst i; eapply Hnin; left].
                      rewrite lookup_insert_ne; [|intro; subst i; eapply Hnin; right; left].
                      destruct (Hregsdef0 i) as [wi [Hwi _] ].
                      rewrite lookup_fmap /base.RegLocate Hwi; reflexivity.
                    - rewrite (proj2 (foldr_insert_spec _ _ i Hdup) n).
                      destruct (reg_eq_dec PC i); [subst i; rewrite lookup_insert lookup_insert_ne /RegLocate // HPC' //|].
                      rewrite (lookup_insert_ne _ PC) //.
                      destruct (reg_eq_dec call.r_stk i); [subst i; rewrite lookup_insert lookup_insert_ne /RegLocate //|].
                      destruct (Hregsdef call.r_stk) as [ww [XX _] ].
                      rewrite (Hsregs _ _ XX); auto.
                      exfalso. eapply n. eapply elem_of_list_In.
                      eapply elem_of_list_difference.
                      split. apply all_registers_correct.
                      intro. eapply elem_of_cons in H1.
                      destruct H1; [apply n0; auto|].
                      eapply elem_of_cons in H1. destruct H1; [apply n1; auto|].
                      eapply not_elem_of_nil; eauto. }
                  rewrite ZZ. rewrite insert_insert.
                  rewrite (insert_commute _ call.r_stk PC) //.
                  rewrite !insert_insert /=.
                  assert (YY: updatePC (<[PC:=inr (pcp, pcg, pcb, pce, pcam1)]> (<[call.r_stk:=inr (URWLX, Monotone, br, ne_stk, ^(na_stk + 1)%a)]> (translate_word <$> nregs)), mem2) = (NextI, update_reg (<[PC:=inr (pcp, pcg, pcb, pce, pcam1)]> (<[call.r_stk:=inr (URWLX, Monotone, br, ne_stk, ^(na_stk + 1)%a)]> (translate_word <$> nregs)), mem2) PC (inr (pcp, pcg, pcb, pce, pca)))).
                  { rewrite /updatePC /RegLocate lookup_insert /= Hpcam1eq.
                    destruct Hcanexec as [-> | [-> | ->] ]; auto. }
                  rewrite YY /update_reg /=.
                  rewrite insert_insert.
                  assert (XX: <[PC:=inr (pcp, pcg, pcb, pce, pca)]> (<[call.r_stk:=inr (URWLX, Monotone, br, ne_stk, ^(na_stk + 1)%a)]> (translate_word <$> nregs)) = translate_word <$> nregs).
                  { eapply map_eq. intros.
                    destruct (reg_eq_dec i PC); [subst i|].
                    - rewrite lookup_insert lookup_fmap HnewPC /= //.
                    - rewrite lookup_insert_ne; auto.
                      destruct (reg_eq_dec i call.r_stk); [subst i|].
                      + rewrite lookup_insert lookup_fmap Hr_stk /= //.
                      + rewrite lookup_insert_ne; auto. }
                  rewrite XX. econstructor.
            + econstructor.
              * repeat econstructor.
              * intros _. econstructor; eauto.
                { intros. eapply Hstkdisj; eauto.
                  - generalize (proj1 (stack_is_Some _ _) ltac:(eexists; exact H2)); simpl; intros Hd1.
                    destruct (nat_eq_dec d1 (S (length cs'))); [lia|].
                    exact H2.
                  - generalize (proj1 (stack_is_Some _ _) ltac:(eexists; exact H3)); simpl; intros Hd2.
                    destruct (nat_eq_dec d2 (S (length cs'))); [lia|].
                    exact H3. }
                { inv Hcs; econstructor; eauto.
                  destruct Hcontiguous0 as [? [? [? [? ?] ] ] ].
                  eexists; eexists; eauto. }
                { intros r w X; rewrite lookup_fmap X /= //. } }
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
              exists ([@ectx_language.fill cap_ectx_lang [SeqCtx] (Instr res.1)], res.2).
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
                  econstructor; simpl; eauto.
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
                    { repeat econstructor. }
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
                        + repeat econstructor.
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
                        + repeat econstructor.
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
                        + repeat econstructor.
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
                        + repeat econstructor.
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
                    - repeat econstructor.
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
                    - repeat econstructor.
                    - rewrite /can_step /=. intros [X | X]; discriminate. }
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
                exists ([@ectx_language.fill cap_ectx_lang [SeqCtx] (Instr res.1)], res.2). split.
                * eapply tc_once. econstructor. econstructor; eauto.
                  -- f_equal; eauto. instantiate (1 := []).
                     instantiate (2 := []). reflexivity.
                  -- instantiate (1 := res.2).
                     instantiate (1 := []). reflexivity.
                  -- econstructor; eauto. econstructor.
                     econstructor; simpl; eauto.
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
                    - repeat econstructor.
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
                    - repeat econstructor.
                    - rewrite /can_step /=. intros [X | X]; discriminate. }
              + (* Actual return case *)
                admit. }
          (* Not Jmp nor Jnz so we know we only need one step *)
          set res := exec (decodeInstrW (mem2 !m! a)) (reg2, mem2).
          exists ([@ectx_language.fill cap_ectx_lang [SeqCtx] (Instr res.1)], res.2).
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
              econstructor; simpl; eauto.
              + rewrite /RegLocate HPC'. reflexivity.
              + rewrite /RegLocate HPC'. generalize (isCorrectPC_translate_word H6).
                simpl; auto. }
          { destruct (lang.exec (decodeInstrW' (base.MemLocate h a)) (reg1, h, stk, cs)) as [c1 [ [ [reg1' h'] stk'] cs'] ] eqn:Hexec. simpl.
            destruct res as [c2 [reg2' mem2'] ] eqn:Hexec'. subst res. simpl.
            rewrite /base.RegLocate in H5.
            destruct (reg1 !! PC) eqn:HPC; [|congruence]. subst s.
            eapply exec_sim with (K := [lang.SeqCtx]); eauto.
            repeat econstructor. }
        * (* Regular stack exec *) admit.
        * (* Regular call *)
          simpl in H5, H6. rewrite H5 in H6. simpl.
          eexists. split.
          { (* TODO: change machine_run_conf *) admit. } 
          admit.
      + (* NextI case *)
        assert (K = [] /\ f1 = lang.NextI) as [-> ->].
        { destruct K; [simpl in H1; inv H1; auto|]. rewrite cons_is_app in H1.
          destruct e; rewrite ectxi_language.fill_app /= in H1.
          inv H1. symmetry in H4; eapply fill_inv_instr in H4.
          destruct H4 as [-> ?]. inv H1; auto. }
        inv H2. clear H1.
        exists ([@ectx_language.fill cap_ectx_lang [] (Seq (Instr Executable))], (reg2, mem2)). split.
        * eapply tc_once. econstructor. econstructor; eauto.
          { f_equal; eauto. instantiate (1 := []).
            instantiate (2 := []). reflexivity. }
          { instantiate (1 := (reg2, mem2)).
            instantiate (1 := []). reflexivity. }
          { econstructor; eauto.
            econstructor. econstructor. }
        * specialize (Hinvs ltac:(rewrite can_step_fill /can_step /=; auto)).
          inv Hinvs. econstructor; eauto.
          { repeat econstructor. }
          { intros. econstructor; eauto. } 
      + (* Halted case *)
        assert (K = [] /\ f1 = lang.Halted) as [-> ->].
        { destruct K; [simpl in H1; inv H1; auto|]. rewrite cons_is_app in H1.
          destruct e; rewrite ectxi_language.fill_app /= in H1.
          inv H1. symmetry in H4; eapply fill_inv_instr in H4.
          destruct H4 as [-> ?]. inv H1; auto. }
        inv H2. clear H1.
        exists ([@ectx_language.fill cap_ectx_lang [] (Instr Halted)], (reg2, mem2)). split.
        * eapply tc_once. econstructor. econstructor; eauto.
          { f_equal; eauto. instantiate (1 := []).
            instantiate (2 := []). reflexivity. }
          { instantiate (1 := (reg2, mem2)).
            instantiate (1 := []). reflexivity. }
          { econstructor; eauto.
            econstructor. econstructor. }
        * econstructor; eauto.
          { repeat econstructor. }
          { rewrite can_step_fill /can_step /=. intros [? | ?]; discriminate. }
      + (* Failed case *)
        assert (K = [] /\ f1 = lang.Failed) as [-> ->].
        { destruct K; [simpl in H1; inv H1; auto|]. rewrite cons_is_app in H1.
          destruct e; rewrite ectxi_language.fill_app /= in H1.
          inv H1. symmetry in H4; eapply fill_inv_instr in H4.
          destruct H4 as [-> ?]. inv H1; auto. }
        inv H2. clear H1.
        exists ([@ectx_language.fill cap_ectx_lang [] (Instr Failed)], (reg2, mem2)). split.
        * eapply tc_once. econstructor. econstructor; eauto.
          { f_equal; eauto. instantiate (1 := []).
            instantiate (2 := []). reflexivity. }
          { instantiate (1 := (reg2, mem2)).
            instantiate (1 := []). reflexivity. }
          { econstructor; eauto.
            econstructor. econstructor. }
        * econstructor; eauto.
          { repeat econstructor. }
          { rewrite can_step_fill /can_step /=; intros [? | ?]; discriminate. }
    - intros. inv H1. destruct H3 as [A B].
      inv H2. simpl in A. inv A. destruct x; simpl in B; [|congruence].
      inv Hsexpr; inv B; eexists; split; econstructor; simpl; split; reflexivity.
  Admitted.

End overlay_to_cap_lang.
