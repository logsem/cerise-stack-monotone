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
              | Ret d b e a => inr (E, Monotone, b, e, a)
              end
    end.

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

  Inductive sim_expr: lang.expr -> expr -> Prop :=
  | sim_expr_instr:
      forall f1 f2,
        sim_flag f1 f2 ->
        sim_expr (lang.Instr f1) (Instr f2)
  | sim_expr_seq:
      forall e1 e2,
        sim_expr e1 e2 ->
        sim_expr (lang.Seq e1) (Seq e2).

  Inductive sim: language.cfg overlay_lang' -> language.cfg cap_lang' -> Prop :=
  | sim_intro:
      forall e1 e2 reg1 reg2 h stk cs mem2
        (Hsexpr: sim_expr e1 e2)
        (Hsregs: forall r w, reg1 !! r = Some w -> reg2 !! r = Some (translate_word w))
        (Hsh: forall a w, h !! a = Some w -> mem2 !! a = Some (translate_word w))
        (Hsstk: forall a w, stk !! a = Some w -> mem2 !! a = Some (translate_word w))
        (Hdisj: h ##ₘ stk),
        sim ([e1], (reg1, h, stk, cs)) ([e2], (reg2, mem2)).

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
      forward_simulation (lang.initial_state b_stk e_stk c) (initial_state call.r_stk b_stk e_stk (compile c)) sim sim_val.
  Proof.
    intros. econstructor.
    - inv H0. cbn -[list_to_set].
      econstructor.
      + repeat econstructor.
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
      clear H3. simpl. inv H4.
      + inv Hsexpr. inv H3.
        admit.
      + inv Hsexpr. inv H2. inv H3.
        exists ([Seq (Instr Executable)], (reg2, mem2)). split.
        * eapply rtc_once. econstructor. econstructor; eauto.
          { f_equal; eauto. instantiate (1 := []).
            instantiate (1 := Seq (Instr NextI)).
            instantiate (1 := []). reflexivity. }
          { instantiate (1 := (reg2, mem2)).
            instantiate (1 := []).
            instantiate (1 := Seq (Instr Executable)). reflexivity. }
          { econstructor. }
        * econstructor; eauto.
          do 2 econstructor.
      + inv Hsexpr. inv H2. inv H3.
        exists ([Instr Halted], (reg2, mem2)). split.
        * eapply rtc_once. econstructor. econstructor; eauto.
          { f_equal; eauto. instantiate (1 := []).
            instantiate (1 := Seq (Instr Halted)).
            instantiate (1 := []). reflexivity. }
          { instantiate (1 := (reg2, mem2)).
            instantiate (1 := []).
            instantiate (1 := Instr Halted). reflexivity. }
          { econstructor. }
        * econstructor; eauto.
          do 2 econstructor.
      + inv Hsexpr. inv H2. inv H3.
        exists ([Instr Failed], (reg2, mem2)). split.
        * eapply rtc_once. econstructor. econstructor; eauto.
          { f_equal; eauto. instantiate (1 := []).
            instantiate (1 := Seq (Instr Failed)).
            instantiate (1 := []). reflexivity. }
          { instantiate (1 := (reg2, mem2)).
            instantiate (1 := []).
            instantiate (1 := Instr Failed). reflexivity. }
          { econstructor. }
        * econstructor; eauto.
          do 2 econstructor.
    - intros. inv H1. inv H2.
      destruct H3 as [A B].
      simpl in A; inv A.
      destruct x; simpl in B; try congruence.
      destruct c0; simpl in B; try congruence; inv H1; inv H3; inv B; eexists; split; econstructor; eauto.
  Admitted.

End overlay_to_cap_lang.
