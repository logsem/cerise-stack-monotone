From cap_machine.overlay Require Import base lang.
From cap_machine Require Import cap_lang simulation linking.
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
      destruct H0 as [e2' [A B]].
      inv B. exists e3; split; auto.
  Qed.

  Definition incrementPC (regs: base.Reg) : option base.Reg :=
    match regs !! PC with
    | Some (inr (Regular ((p, g), b, e, a))) =>
      match (a + 1)%a with
      | Some a' => Some (<[ PC := inr (Regular ((p, g), b, e, a')) ]> regs)
      | None => None
      end
    | Some (inr (Stk d p b e a)) =>
      match (a + 1)%a with
      | Some a' => Some (<[ PC := inr (Stk d p b e a') ]> regs)
      | None => None
      end
    | Some (inr (Ret b e a)) =>
      match (a + 1)%a with
      | Some a' => Some (<[ PC := inr (Ret b e a') ]> regs)
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
    - destruct c as [[[[p' g'] b'] e'] a'].
      destruct (a' + 1)%a; inv H1.
      destruct (reg_eq_dec x PC).
      + subst x. rewrite lookup_insert X; split; intro; eauto.
      + rewrite lookup_insert_ne; auto.
    - destruct (a1 + 1)%a; inv H1.
      destruct (reg_eq_dec x PC).
      + subst x. rewrite lookup_insert X; split; intro; eauto.
      + rewrite lookup_insert_ne; auto.
    - destruct (a1 + 1)%a; inv H1.
      destruct (reg_eq_dec x PC).
      + subst x. rewrite lookup_insert X; split; intro; eauto.
      + rewrite lookup_insert_ne; auto.
  Qed.

  Definition incrementPC' (regs: Reg) : option Reg :=
    match regs !! PC with
    | Some (inr ((p, g), b, e, a)) =>
      match (a + 1)%a with
      | Some a' => Some (<[ PC := inr ((p, g), b, e, a') ]> regs)
      | None => None
      end
    | _ => None
    end.

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

  Inductive sim_cs: base.Mem -> list Stackframe -> machine_base.Mem -> Prop :=
  | sim_cs_nil:
      forall h m,
        sim_cs h [] m
  | sim_cs_cons:
      forall reg stk cs h m
        (Hregsdef: forall r, is_Some (reg !! r))
        (Hregstk: forall r d p b e a, reg !! r = Some (inr (Stk d p b e a)) -> exists s, stack d ((reg, stk)::cs) = Some s /\ forall x, (b <= x < e)%a -> exists w, s !! x = Some w /\ m !! x = Some (translate_word w))
        (Hregret: forall r d b e a, reg !! r = Some (inr (Ret d b e a)) -> exists s, stack d ((reg, stk)::cs) = Some s /\ forall x, (b <= x < e)%a -> exists w, s !! x = Some w /\ m !! x = Some (translate_word w))
        (* TODO: need to describe return pointer code *)
        (Hregh: forall r p g b e a, reg !! r = Some (inr (Regular (p, g, b, e, a))) -> forall x, (b <= x < e)%a -> exists w, h !! x = Some w /\ m !! x = Some (translate_word w))
        (Hstkstk: forall y d p b e a, stk !! y = Some (inr (Stk d p b e a)) -> exists s, stack d ((reg, stk)::cs) = Some s /\ forall x, (b <= x < e)%a -> exists w, s !! x = Some w /\ m !! x = Some (translate_word w))
        (Hstlret: forall y d b e a, stk !! y = Some (inr (Ret d b e a)) -> exists s, stack d ((reg, stk)::cs) = Some s /\ forall x, (b <= x < e)%a -> exists w, s !! x = Some w /\ m !! x = Some (translate_word w))
        (* TODO: need to describe return pointer code *)
        (Hstkh: forall y p g b e a, stk !! y = Some (inr (Regular (p, g, b, e, a))) -> forall x, (b <= x < e)%a -> exists w, h !! x = Some w /\ m !! x = Some (translate_word w))
        (Hsstk: forall a w, stk !! a = Some w -> m !! a = Some (translate_word w))
        (Hcs: sim_cs h cs m),
        sim_cs h ((reg, stk)::cs) m.

  Inductive sim: language.cfg overlay_lang -> language.cfg cap_lang -> Prop :=
  | sim_intro:
      forall e1 e2 reg1 reg2 h stk cs mem2
        (Hsexpr: sim_expr e1 e2)
        (Hcswf: sim_cs h ((reg1, stk)::cs) mem2)
        (Hsregs: forall r w, reg1 !! r = Some w -> reg2 !! r = Some (translate_word w))
        (Hsh: forall a w, h !! a = Some w -> mem2 !! a = Some (translate_word w) /\ lang.is_global w /\ lang.can_address_only w (dom _ h))
        (*(Hdisj: forall a, a ∈ dom (gset _) h -> (e_stk <= a)%a)*),
        sim ([e1], (reg1, h, stk, cs)) ([e2], (reg2, mem2)).

  Lemma exec_sim:
    forall reg1 reg1' reg2 reg2' h h' stk stk' cs cs' mem2 mem2' p g b e a c1 c2
      (Hregsdef: forall r, is_Some (reg1 !! r))
      (Hregstk: forall r d p b e a, reg1 !! r = Some (inr (Stk d p b e a)) -> is_Some (stack d ((reg1,stk)::cs)))
      (Hsregs: forall r w, reg1 !! r = Some w -> reg2 !! r = Some (translate_word w))
      (Hsh: forall a w, h !! a = Some w -> mem2 !! a = Some (translate_word w) /\ lang.is_global w /\ lang.can_address_only w (dom _ h))
      (Hsstk: forall a w, stk !! a = Some w -> mem2 !! a = Some (translate_word w))
      (Hdisj: h ##ₘ stk),
      is_Some (h !! a) ->
      reg1 !! PC = Some (inr (Regular (p, g, b, e, a))) ->
      lang.exec (decodeInstrW' (base.MemLocate h a)) (reg1, h, stk, cs) = (c1, (reg1', h', stk', cs')) ->
      exec (decodeInstrW (mem2 !m! a)) (reg2, mem2) = (c2, (reg2', mem2')) ->
      sim_flag c1 c2 /\
      (forall r, is_Some (reg1' !! r)) /\
      (forall r d p b e a, reg1' !! r = Some (inr (Stk d p b e a)) -> is_Some (stack d ((reg1',stk')::cs'))) /\
      (forall r w, reg1' !! r = Some w -> reg2' !! r = Some (translate_word w)) /\
      (forall a w, h' !! a = Some w -> (mem2' !! a = Some (translate_word w) /\ lang.is_global w /\ lang.can_address_only w (dom _ h'))) /\
      (forall a w, stk' !! a = Some w -> mem2' !! a = Some (translate_word w)) /\
      (h' ##ₘ stk').
  Proof.
    rewrite /MemLocate /base.MemLocate. intros.
    destruct H0 as [w Hw].
    rewrite Hw in H2. generalize (Hsh _ _ Hw). intros [Hw' [Hwisglobal Hwcanaddress]].
    rewrite Hw' in H3. rewrite <- decodeInstrW_translate_word in H3.
    destruct (decodeInstrW' w) eqn:Hinstr.
    - (* Jmp *)
      simpl in H2. destruct (Hregsdef r) as [wr Hwr].
      rewrite /base.RegLocate Hwr in H2.
      admit.
    - (* Jnz *) admit.
    - (* Mov *)
      assert (c1 = match incrementPC (<[dst := word_of_argument reg1 src]> reg1) with Some _ => lang.NextI | _ => lang.Failed end /\ reg1' = match incrementPC (<[dst := word_of_argument reg1 src]> reg1) with Some r => r | _ => <[dst := word_of_argument reg1 src]> reg1 end /\ h' = h /\ stk' = stk /\ cs' = cs /\ c2 = match incrementPC (<[dst := word_of_argument reg1 src]> reg1) with Some _ => NextI | _ => Failed end /\ reg2' = match incrementPC' (<[dst := translate_word (word_of_argument reg1 src)]> reg2) with Some r => r | _ => <[dst := translate_word (word_of_argument reg1 src)]> reg2 end /\ mem2' = mem2).
      { simpl in H2. destruct src; simpl.
        - rewrite /base.update_reg /= /lang.updatePC /= /base.RegLocate in H2.
          rewrite /incrementPC. destruct (reg_eq_dec dst PC).
          + subst dst. rewrite !lookup_insert.
            rewrite lookup_insert in H2. inv H2; repeat split; auto.
            rewrite /= /update_reg /= /updatePC /= /RegLocate lookup_insert in H3; inv H3; auto.
            rewrite /= /update_reg /= /updatePC /= /RegLocate lookup_insert in H3; inv H3; auto.
            rewrite /incrementPC' /= lookup_insert //.
            rewrite /= /update_reg /= /updatePC /= /RegLocate lookup_insert in H3; inv H3; auto.
          + rewrite lookup_insert_ne in H2; auto.
            rewrite lookup_insert_ne; auto. rewrite H1.
            rewrite H1 in H2. rewrite /= /update_reg /= /updatePC /= /RegLocate lookup_insert_ne // in H3.
            rewrite /incrementPC'. generalize (Hsregs _ _ H1). intro Y.
            rewrite lookup_insert_ne // Y /=. rewrite Y /= in H3.
            destruct (a + 1)%a.
            * inv H2. inv H3. repeat split; auto.
            * inv H2. inv H3. repeat split; auto.
        - rewrite /base.update_reg /= /lang.updatePC /= in H2.
          rewrite /update_reg /= /updatePC /= in H3.
          rewrite /incrementPC /incrementPC'. destruct (reg_eq_dec dst PC).
          + subst dst. rewrite !lookup_insert.
            rewrite /base.RegLocate !lookup_insert in H2.
            rewrite /RegLocate !lookup_insert in H3.
            rewrite /base.RegLocate. destruct (reg1 !! r) eqn:X.
            * generalize (Hsregs _ _ X). intro Y. rewrite Y in H3.
              destruct s; [inv H2; inv H3; simpl; repeat split; auto|].
              destruct c.
              { destruct c as [[[[p' g'] b'] e'] a']. simpl in *.
                destruct (a' + 1)%a; inv H2; inv H3; repeat split; auto. }
              { simpl in *. destruct (a2 + 1)%a; inv H2; inv H3; repeat split; auto. }
              { simpl in *. destruct (a2 + 1)%a; inv H2; inv H3; repeat split; auto. }
            * destruct (Hregsdef r). rewrite H0 in X; inv X.
          + rewrite !(lookup_insert_ne _ dst PC) //.
            rewrite /base.RegLocate (lookup_insert_ne _ dst PC) // H1 in H2.
            generalize (Hsregs _ _ H1). intro Y.
            rewrite /RegLocate (lookup_insert_ne _ dst PC) // Y /= in H3.
            rewrite Y H1 /=.
            destruct (a + 1)%a; inv H2; inv H3; repeat split; auto.
            destruct (Hregsdef r) as [wr Hwr].
            generalize (Hsregs _ _ Hwr). intro Hwr'.
            rewrite /base.RegLocate Hwr Hwr'; auto.
            destruct (Hregsdef r) as [wr Hwr].
            generalize (Hsregs _ _ Hwr). intro Hwr'.
            rewrite /base.RegLocate Hwr Hwr'; auto. }
      destruct H0 as [HA [HB [HC [HD [HE [HF [HG HH]]]]]]].
      subst. split; [|split; [|split; [|split; [|split; [|split]]]]]; auto.
      + destruct (incrementPC (<[dst:=word_of_argument reg1 src]> reg1)); econstructor.
      + destruct (incrementPC (<[dst:=word_of_argument reg1 src]> reg1)) eqn:XX.
        * intro. rewrite -incrementPC_is_Some; [|eapply XX].
          destruct (reg_eq_dec dst r).
          { subst dst; rewrite lookup_insert; eauto. }
          { rewrite lookup_insert_ne; eauto. }
        * intros. destruct (reg_eq_dec dst r).
          { subst dst; rewrite lookup_insert; eauto. }
          { rewrite lookup_insert_ne; eauto. }
      + intros. rewrite /incrementPC in H0.
        destruct (reg_eq_dec dst PC).
        * subst dst; rewrite !lookup_insert in H0.
          destruct (word_of_argument reg1 src) eqn:XX.
          { destruct (reg_eq_dec r PC); [subst r; rewrite lookup_insert in H0; inv H0 |].
            rewrite lookup_insert_ne in H0; auto. eapply Hregstk in H0.
            rewrite /stack in H0. rewrite /stack.
            destruct (nat_eq_dec d (length cs)); eauto. }
          { destruct c.
            - destruct c as [[[[p' g'] b'] e'] a'].
              destruct (a' + 1)%a.
              + destruct (reg_eq_dec r PC); [subst r; rewrite lookup_insert in H0; inv H0|].
                rewrite !lookup_insert_ne in H0; auto. eapply Hregstk in H0.
                rewrite /stack in H0. rewrite /stack.
                destruct (nat_eq_dec d (length cs)); eauto.
              + destruct (reg_eq_dec r PC); [subst r; rewrite lookup_insert in H0; inv H0|].
                rewrite lookup_insert_ne in H0; auto. eapply Hregstk in H0.
                rewrite /stack in H0. rewrite /stack.
                destruct (nat_eq_dec d (length cs)); eauto.
            - destruct (a3 + 1)%a.
              + rewrite insert_insert in H0. destruct (reg_eq_dec r PC).
                * subst r. rewrite lookup_insert in H0. inv H0.
                  rewrite /word_of_argument in XX. destruct src; inv XX.
                  rewrite /base.RegLocate in H4. destruct (reg1 !! r) eqn:XX; [subst s| inv H4].
                  eapply Hregstk in XX. rewrite /stack in XX. rewrite /stack.
                  destruct (nat_eq_dec d (length cs)); eauto.
                * rewrite lookup_insert_ne in H0; auto.
                  eapply Hregstk in H0. rewrite /stack in H0. rewrite /stack.
                  destruct (nat_eq_dec d (length cs)); eauto.
              + destruct (reg_eq_dec r PC).
                * subst r. rewrite lookup_insert in H0. inv H0.
                  rewrite /word_of_argument in XX. destruct src; inv XX.
                  rewrite /base.RegLocate in H4. destruct (reg1 !! r) eqn:XX; [subst s| inv H4].
                  eapply Hregstk in XX. rewrite /stack in XX. rewrite /stack.
                  destruct (nat_eq_dec d (length cs)); eauto.
                * rewrite lookup_insert_ne in H0; auto.
                  eapply Hregstk in H0. rewrite /stack in H0. rewrite /stack.
                  destruct (nat_eq_dec d (length cs)); eauto.
            - destruct (a3 + 1)%a.
              + rewrite insert_insert in H0. destruct (reg_eq_dec r PC); [subst r; rewrite lookup_insert in H0; inv H0|].
                rewrite lookup_insert_ne in H0; auto. eapply Hregstk in H0.
                rewrite /stack in H0. rewrite /stack.
                destruct (nat_eq_dec d (length cs)); eauto.
              + destruct (reg_eq_dec r PC); [subst r; rewrite lookup_insert in H0; inv H0|].
                rewrite lookup_insert_ne in H0; auto. eapply Hregstk in H0.
                rewrite /stack in H0. rewrite /stack.
                destruct (nat_eq_dec d (length cs)); eauto. }
        * rewrite lookup_insert_ne in H0; auto.
          rewrite H1 in H0. destruct (a + 1)%a.
          { destruct (reg_eq_dec PC r); [subst r; rewrite lookup_insert in H0; inv H0|].
            rewrite lookup_insert_ne in H0; auto.
            destruct (reg_eq_dec r dst); [subst r; rewrite lookup_insert in H0; inv H0|].
            - rewrite /word_of_argument in H5. destruct src; inv H5.
              rewrite /base.RegLocate in H4. destruct (reg1 !! r) eqn:XX; [subst s|inv H4].
              eapply Hregstk in XX. rewrite /stack in XX. rewrite /stack.
              destruct (nat_eq_dec d (length cs)); eauto.
            - rewrite lookup_insert_ne in H0; auto.
              eapply Hregstk in H0. rewrite /stack in H0. rewrite /stack.
              destruct (nat_eq_dec d (length cs)); eauto. }
          { destruct (reg_eq_dec r dst); [subst r; rewrite lookup_insert in H0; inv H0|].
            - rewrite /word_of_argument in H5. destruct src; inv H5.
              rewrite /base.RegLocate in H4. destruct (reg1 !! r) eqn:XX; [subst s|inv H4].
              eapply Hregstk in XX. rewrite /stack in XX. rewrite /stack.
              destruct (nat_eq_dec d (length cs)); eauto.
            - rewrite lookup_insert_ne in H0; auto.
              eapply Hregstk in H0. rewrite /stack in H0. rewrite /stack.
              destruct (nat_eq_dec d (length cs)); eauto. }
      + rewrite /incrementPC /incrementPC'; destruct (reg_eq_dec dst PC); [subst dst; rewrite !lookup_insert|]; intros.
        * destruct (word_of_argument reg1 src) eqn:XX; simpl.
          { destruct (reg_eq_dec r PC); [subst r; rewrite lookup_insert; rewrite lookup_insert in H0; inv H0; auto|].
            rewrite lookup_insert_ne in H0; auto.
            rewrite lookup_insert_ne; auto. }
          { destruct c.
            - destruct c as [[[[p' g'] b'] e'] a'].
              destruct ((a' + 1)%a).
              + destruct (reg_eq_dec PC r); [subst r; rewrite lookup_insert in H0; rewrite lookup_insert; inv H0; reflexivity|].
                rewrite !lookup_insert_ne; auto.
                rewrite !lookup_insert_ne in H0; auto.
              + destruct (reg_eq_dec PC r); [subst r; rewrite lookup_insert in H0; rewrite lookup_insert; inv H0; reflexivity|].
                rewrite lookup_insert_ne; auto.
                rewrite lookup_insert_ne in H0; auto.
            - destruct ((a2 + 1)%a).
              + destruct (reg_eq_dec PC r); [subst r; rewrite lookup_insert in H0; rewrite lookup_insert; inv H0; reflexivity|].
                rewrite !lookup_insert_ne; auto.
                rewrite !lookup_insert_ne in H0; auto.
              + destruct (reg_eq_dec PC r); [subst r; rewrite lookup_insert in H0; rewrite lookup_insert; inv H0; reflexivity|].
                rewrite lookup_insert_ne; auto.
                rewrite lookup_insert_ne in H0; auto.
            - destruct ((a2 + 1)%a).
              + destruct (reg_eq_dec PC r); [subst r; rewrite lookup_insert in H0; rewrite lookup_insert; inv H0; reflexivity|].
                rewrite !lookup_insert_ne; auto.
                rewrite !lookup_insert_ne in H0; auto.
              + destruct (reg_eq_dec PC r); [subst r; rewrite lookup_insert in H0; rewrite lookup_insert; inv H0; reflexivity|].
                rewrite lookup_insert_ne; auto.
                rewrite lookup_insert_ne in H0; auto. }
        * rewrite lookup_insert_ne in H0; auto.
          rewrite lookup_insert_ne; auto.
          rewrite H1 in H0. generalize (Hsregs _ _ H1); intros Y.
          rewrite Y /=. destruct ((a + 1)%a).
          { destruct (reg_eq_dec r PC); [subst r; rewrite lookup_insert in H0; rewrite lookup_insert; inv H0; auto|].
            rewrite lookup_insert_ne in H0; auto.
            rewrite lookup_insert_ne; auto.
            destruct (reg_eq_dec r dst); [subst r; rewrite lookup_insert in H0; rewrite lookup_insert; inv H0; auto|].
            rewrite lookup_insert_ne in H0; auto.
            rewrite lookup_insert_ne; auto. }
          { destruct (reg_eq_dec r dst); [subst r; rewrite lookup_insert in H0; rewrite lookup_insert; inv H0; auto|].
            rewrite lookup_insert_ne in H0; auto.
            rewrite lookup_insert_ne; auto. }
    - (* Load *) admit.
    - (* Store *) admit.
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
      is_program e_stk _ _ _ _ lang.can_address_only lang.pwl lang.is_global c ->
      @forward_simulation overlay_lang cap_lang (lang.initial_state b_stk e_stk c) (initial_state call.r_stk b_stk e_stk (compile c)) sim sim_val.
  Proof.
    intros. econstructor.
    - inv H0. cbn -[list_to_set].
      econstructor.
      + repeat econstructor.
      + intros. destruct (reg_eq_dec r call.r_stk).
        * subst r. rewrite lookup_insert. eauto.
        * destruct (reg_eq_dec r PC).
          { subst r. rewrite lookup_insert_ne; auto.
            rewrite lookup_insert. eauto. }
          { do 2 (rewrite lookup_insert_ne; auto).
            exists (inl 0%Z). erewrite lookup_gset_to_gmap_Some.
            split; auto. eapply all_registers_s_correct. }
      + intros. inv Hwfcomp. destruct (reg_eq_dec r call.r_stk).
        * subst r. rewrite lookup_insert in H0. inv H0. simpl. eauto.
        * destruct (reg_eq_dec r PC).
          { subst r. rewrite lookup_insert_ne in H0; auto.
            rewrite lookup_insert in H0. inv H0.
            destruct Hw_main as [A B]. inv B. }
          { do 2 (rewrite lookup_insert_ne in H0; auto).
            erewrite lookup_gset_to_gmap_Some in H0. destruct H0 as [A B].
            inv B. }
      + intros. destruct (reg_eq_dec r call.r_stk).
        * subst r. rewrite lookup_insert in H0.
          rewrite lookup_insert. inv H0; reflexivity.
        * destruct (reg_eq_dec r PC).
          { subst r.
            rewrite lookup_insert_ne in H0; auto.
            rewrite lookup_insert in H0.
            rewrite lookup_insert_ne; auto.
            rewrite lookup_insert. inv H0; eauto. }
          { do 2 (rewrite lookup_insert_ne in H0; auto).
            do 2 (rewrite lookup_insert_ne; auto).
            erewrite lookup_gset_to_gmap_Some in H0. destruct H0 as [A B].
            inv B. simpl translate_word. rewrite lookup_gset_to_gmap_Some.
            split; auto. }
      + intros. rewrite lookup_fmap H0 /= //.
      + intros. rewrite lookup_empty in H0; inv H0.
      + eapply map_disjoint_empty_r.
    - intros. inv H2; inv H1.
      inv H3. inv H1. assert (e0 = e1 /\ t1 = [] /\ t2 = []).
      { destruct t1, t2; simpl in H3; inv H3; auto.
        + symmetry in H5. apply app_eq_nil in H5.
          destruct H5 as [A B]; inv B.
        + symmetry in H5. apply app_eq_nil in H5.
          destruct H5 as [A B]; inv B. }
      destruct H1 as [A [B C]]; subst e0; subst t1; subst t2.
      clear H3. simpl. inv H4. destruct (sim_expr_fill_inv Hsexpr) as [e22 [A B]].
      generalize (sim_expr_determ Hsexpr A). intros; subst e2. inv H3.
      + inv B. inv H3. inv H1.
        * simpl in H4. eexists. split.
          { eapply rtc_once. exists []. econstructor; eauto.
            { f_equal; eauto. instantiate (1 := []).
              instantiate (2 := []). reflexivity. }
            econstructor; eauto. econstructor.
            eapply step_exec_fail. simpl; intro HA.
            rewrite /RegLocate in HA.
            inv HA. destruct (reg2 !! PC) as [pcw2|] eqn:X; try congruence.
            subst pcw2. rewrite /base.RegLocate in H4.
            destruct (Hregsdef PC) as [pcw1 Y]. rewrite Y in H4.
            generalize (Hsregs PC _ Y). rewrite X; intros Z; inv Z.
            destruct pcw1; simpl in H5; try congruence.
            destruct c0.
            + inv H5. eapply H4. econstructor; eauto.
            + inv H5. eapply H4. econstructor; eauto.
            + inv H5. destruct H3 as [? | [? | ?]]; congruence. }
          { simpl. econstructor; eauto. eapply sim_expr_fill.
            do 2 econstructor. }
        * simpl in H5. rewrite /base.RegLocate in H5.
          destruct (reg1 !! PC) as [pcw1|] eqn:X; try congruence. subst pcw1.
          eapply Hregstk in X. simpl in X, H6; destruct X; congruence.
        * eexists. split.
          { eapply rtc_once. exists []. econstructor; eauto.
            - f_equal; eauto. instantiate (1 := []).
              instantiate (2 := []). reflexivity.
            - econstructor; eauto. econstructor.
              rewrite /base.RegLocate /= in H5.
              destruct (reg1 !! PC) as [pcw1|] eqn:X; try congruence; subst pcw1.
              simpl in H6. rewrite /base.RegLocate X in H6.
              generalize (isCorrectPC_translate_word H6). simpl; intro Y.
              generalize (Hsregs _ _ X). simpl; intro Z.
              eapply step_exec_instr; eauto; simpl; rewrite /RegLocate Z; eauto. }
          { simpl. destruct (lang.exec (decodeInstrW' (base.MemLocate h a)) (reg1, h, stk, cs)) eqn:XX.
            destruct (exec (decodeInstrW (mem2 !m! a)) (reg2, mem2)) eqn:YY. simpl.
            destruct e1 as [r'' m'']. destruct e0 as [[[r' h'] stk'] cs'].
            econstructor; eauto.
            - eapply sim_expr_fill; eauto.
              rewrite /base.RegLocate /= in H5.
              destruct (reg1 !! PC) as [pcw1|] eqn:X; try congruence; subst pcw1.
              generalize (Hsregs _ _ X). simpl; intro Y.
              




              admit.
            - admit.
            - admit.
            - admit.
            - admit.
            - admit.
            - admit. }
        * admit.
        * (* call global *)
          admit.
        * (* call stack *)
          admit.
      + inv B. inv H2. inv H3.
        exists ([@ectx_language.fill cap_ectx_lang (map (fun _ => SeqCtx) K) (Seq (Instr Executable))], (reg2, mem2)). split.
        * eapply rtc_once. econstructor. econstructor; eauto.
          { f_equal; eauto. instantiate (1 := []).
            instantiate (2 := []). reflexivity. }
          { instantiate (1 := (reg2, mem2)).
            instantiate (1 := []). reflexivity. }
          { econstructor; eauto.
            econstructor. }
        * econstructor; eauto.
          eapply sim_expr_fill; eauto.
          do 3 econstructor.
      + inv B. inv H2. inv H3.
        exists ([@ectx_language.fill cap_ectx_lang (map (fun _ => SeqCtx) K) (Instr Halted)], (reg2, mem2)). split.
        * eapply rtc_once. econstructor. econstructor; eauto.
          { f_equal; eauto. instantiate (1 := []).
            instantiate (2 := []). reflexivity. }
          { instantiate (1 := (reg2, mem2)).
            instantiate (1 := []). reflexivity. }
          { econstructor; eauto.
            econstructor. }
        * econstructor; eauto.
          eapply sim_expr_fill; eauto.
          do 2 econstructor.
      + inv B. inv H2. inv H3.
        exists ([@ectx_language.fill cap_ectx_lang (map (fun _ => SeqCtx) K) (Instr Failed)], (reg2, mem2)). split.
        * eapply rtc_once. econstructor. econstructor; eauto.
          { f_equal; eauto. instantiate (1 := []).
            instantiate (2 := []). reflexivity. }
          { instantiate (1 := (reg2, mem2)).
            instantiate (1 := []). reflexivity. }
          { econstructor; eauto.
            econstructor. }
        * econstructor; eauto.
          eapply sim_expr_fill; eauto.
          do 2 econstructor.
    - intros. inv H1. inv H2.
      destruct H3 as [A B].
      simpl in A; inv A.
      destruct x; simpl in B; try congruence.
      inv Hsexpr.
      destruct c0; simpl in B; try congruence; inv H2; inv B; eexists; split; econstructor; eauto.
  Admitted.

End overlay_to_cap_lang.
