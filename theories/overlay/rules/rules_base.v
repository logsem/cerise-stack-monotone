From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac auth.
From cap_machine Require Export mono_ref sts iris_extra.
From cap_machine.overlay Require Export base lang.

(* CMRΑ for heap memory *)
Class memG Σ := MemG {
  mem_invG : invG Σ;
  mem_gen_memG :> gen_heapG Addr base.Word Σ}.

(* CMRΑ for stack memory *)
Class stackG Σ := StackG {
  stack_invG : invG Σ;
  stack_gen_stackG :> gen_heapG (nat * Addr) base.Word Σ}.

(* CMRA for registers *)
Class regG Σ := RegG {
  reg_invG : invG Σ;
  reg_gen_regG :> gen_heapG RegName base.Word Σ; }.

Fixpoint make_stack_map (ss: list (base.Mem)): gmap (nat * Addr) base.Word :=
  match ss with
  | nil => empty
  | s::ss => map_fold (fun a w m => <[(length ss, a):=w]> m) (make_stack_map ss) s
  end.

(* invariants for memory, and a state interpretation for (mem,reg) *)
Instance memG_irisG `{MachineParameters} `{memG Σ, regG Σ, stackG Σ} : irisG overlay_lang Σ := {
  iris_invG := mem_invG;
  state_interp σ κs _ := ((gen_heap_ctx (reg σ)) ∗ (gen_heap_ctx (mem σ)) ∗ (gen_heap_ctx (make_stack_map ((stk σ)::(map snd (callstack σ))))))%I;
  fork_post _ := True%I;
}.
Global Opaque iris_invG.

Lemma make_stack_map_length_none ss d a:
  d >= length ss ->
  make_stack_map ss !! (d, a) = None.
Proof.
  induction ss; intros.
  - simpl. apply lookup_empty.
  - simpl. apply (map_fold_ind (λ m1 m2, m1 !! (d, a) = None) (λ (a : Addr) (w : base.Word) (m : gmap (nat * Addr) base.Word), <[(length ss, a):=w]> m) (make_stack_map ss)).
    + eapply IHss. simpl in H; lia.
    + intros. simpl in H.
      rewrite lookup_insert_ne; auto.
      intro. inversion H2; lia.
Qed.

Lemma make_stack_map_cons_eq:
  forall ss s d a, d <> length ss ->
              make_stack_map (s::ss) !! (d, a) = make_stack_map ss !! (d, a).
Proof.
  intros. simpl.
  apply (map_fold_ind (λ m1 m2, m1 !! (d, a) = (make_stack_map ss) !! (d, a))); auto.
  intros. rewrite lookup_insert_ne; auto.
  intro X; inversion X; congruence.
Qed.

Lemma make_stack_map_convert ss d a w:
  make_stack_map (map snd ss) !! (d, a) = Some w ->
  exists s, stack d ss = Some s /\ s !! a = Some w.
Proof.
  induction ss.
  - simpl. rewrite lookup_empty. congruence.
  - simpl. intros. destruct (nat_eq_dec d (@Datatypes.length Stackframe ss)).
    + subst d. eexists; split; eauto.
      clear IHss. rewrite map_length in H.
      apply (map_fold_ind (λ m1 m2, forall i x, m1 !! (length ss, i) = Some x -> m2 !! i = Some x) (λ (a : Addr) (w : base.Word) (m : gmap (nat * Addr) base.Word), <[(length ss, a):=w]> m) (make_stack_map (map snd ss))); auto.
      * intros. rewrite make_stack_map_length_none in H0. congruence.
        rewrite map_length. lia.
      * intros. destruct (decide (i = i0)).
        { subst i0. rewrite lookup_insert. rewrite lookup_insert in H2. auto. }
        { rewrite lookup_insert_ne; auto.
          rewrite lookup_insert_ne in H2; auto.
          intro X; inversion X; congruence. }
    + eapply IHss. rewrite -H.
      rewrite make_stack_map_cons_eq; auto.
      rewrite map_length; auto.
Qed.

(* Points to predicates for registers *)
Notation "r ↣ᵣ{ q } w" := (mapsto (L:=RegName) (V:=base.Word) r q w)
  (at level 20, q at level 50, format "r  ↣ᵣ{ q }  w") : bi_scope.
Notation "r ↣ᵣ w" := (mapsto (L:=RegName) (V:=base.Word) r 1 w)%I (at level 20) : bi_scope.

(* Points to predicates for stack memory *)
(* Notation "a { n } ↣ₐ { q } w" := (mapsto (L:=(nat * Addr)) (V:=base.Word) (n, a) q w) *)
(*   (at level 20, q at level 50, format "a { n } ↣ₐ { q }  w") : bi_scope. *)
Notation "a ↣ₐ [ n ] w" := (mapsto (L:=nat * Addr) (V:=base.Word) (n, a) 1 w) (at level 20) : bi_scope.

(* Points to predicates for heap memory *)
(* Notation "a ↣ₐ { q } w" := (mapsto (L:=Addr) (V:=base.Word) a q w) *)
(*   (at level 20, q at level 50, format "a  ↣ₐ { q }  w") : bi_scope. *)
Notation "a ↣ₐ w" := (mapsto (L:=Addr) (V:=base.Word) a 1 w) (at level 20) : bi_scope.

Section overlay_lang_rules.
  Context `{MachineParameters}.
  Context `{memG Σ, regG Σ, stackG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : base.ExecConf.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types w : base.Word.
  Implicit Types reg : gmap RegName base.Word.
  Implicit Types ms : gmap Addr base.Word.

  (* ----------------------------- LOCATΕ LEMMAS ----------------------------------- *)

  Lemma locate_ne_reg reg r1 r2 w w' :
    r1 ≠ r2 → reg !r! r1 = w → <[r2:=w']> reg !r! r1 = w.
  Proof.
    intros. rewrite /RegLocate.
    rewrite lookup_partial_alter_ne; eauto.
  Qed.

  Lemma locate_eq_reg reg r1 w w' :
    reg !r! r1 = w → <[r1:=w']> reg !r! r1 = w'.
  Proof.
    intros. rewrite /RegLocate.
    rewrite lookup_partial_alter; eauto.
  Qed.

  Lemma locate_ne_mem mem a1 a2 w w' :
    a1 ≠ a2 → mem !m! a1 = w → <[a2:=w']> mem !m! a1 = w.
  Proof.
    intros. rewrite /MemLocate.
    rewrite lookup_partial_alter_ne; eauto.
  Qed.

  (* ------------------------- registers points-to --------------------------------- *)

  Lemma regname_dupl_false r w1 w2 :
    r ↣ᵣ w1 -∗ r ↣ᵣ w2 -∗ False.
  Proof.
    iIntros "Hr1 Hr2".
    iDestruct (mapsto_valid_2 with "Hr1 Hr2") as %?.
    contradiction.
  Qed.

  Lemma regname_neq r1 r2 w1 w2 :
    r1 ↣ᵣ w1 -∗ r2 ↣ᵣ w2 -∗ ⌜ r1 ≠ r2 ⌝.
  Proof.
    iIntros "H1 H2" (?). subst r1. iApply (regname_dupl_false with "H1 H2").
  Qed.

  Lemma map_of_regs_1 (r1: RegName) (w1: base.Word) :
    r1 ↣ᵣ w1 -∗
    ([∗ map] k↦y ∈ {[r1 := w1]}, k ↣ᵣ y).
  Proof. by rewrite big_sepM_singleton. Qed.

  Lemma regs_of_map_1 (r1: RegName) (w1: base.Word) :
    ([∗ map] k↦y ∈ {[r1 := w1]}, (k ↣ᵣ y)) -∗
    r1 ↣ᵣ w1.
  Proof. by rewrite big_sepM_singleton. Qed.

  Lemma map_of_regs_2 (r1 r2: RegName) (w1 w2: base.Word) :
    r1 ↣ᵣ w1 -∗ r2 ↣ᵣ w2 -∗
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> ∅)), k ↣ᵣ y) ∗ ⌜ r1 ≠ r2 ⌝.
  Proof.
    iIntros "H1 H2". iPoseProof (regname_neq with "H1 H2") as "%".
    rewrite !big_sepM_insert ?big_sepM_empty; eauto.
    2: by apply lookup_insert_None; split; eauto.
    iFrame. eauto.
  Qed.

  Lemma regs_of_map_2 (r1 r2: RegName) (w1 w2: base.Word) :
    r1 ≠ r2 →
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> ∅)), k ↣ᵣ y) -∗
    r1 ↣ᵣ w1 ∗ r2 ↣ᵣ w2.
  Proof.
    iIntros (?) "Hmap". rewrite !big_sepM_insert ?big_sepM_empty; eauto.
    by iDestruct "Hmap" as "(? & ? & _)"; iFrame.
    apply lookup_insert_None; split; eauto.
  Qed.

  Lemma map_of_regs_3 (r1 r2 r3: RegName) (w1 w2 w3: base.Word) :
    r1 ↣ᵣ w1 -∗ r2 ↣ᵣ w2 -∗ r3 ↣ᵣ w3 -∗
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> (<[r3:=w3]> ∅))), k ↣ᵣ y) ∗
     ⌜ r1 ≠ r2 ∧ r1 ≠ r3 ∧ r2 ≠ r3 ⌝.
  Proof.
    iIntros "H1 H2 H3".
    iPoseProof (regname_neq with "H1 H2") as "%".
    iPoseProof (regname_neq with "H1 H3") as "%".
    iPoseProof (regname_neq with "H2 H3") as "%".
    rewrite !big_sepM_insert ?big_sepM_empty; simplify_map_eq; eauto.
    iFrame. eauto.
  Qed.

  Lemma regs_of_map_3 (r1 r2 r3: RegName) (w1 w2 w3: base.Word) :
    r1 ≠ r2 → r1 ≠ r3 → r2 ≠ r3 →
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> (<[r3:=w3]> ∅))), k ↣ᵣ y) -∗
    r1 ↣ᵣ w1 ∗ r2 ↣ᵣ w2 ∗ r3 ↣ᵣ w3.
  Proof.
    iIntros (? ? ?) "Hmap". rewrite !big_sepM_insert ?big_sepM_empty; simplify_map_eq; eauto.
    iDestruct "Hmap" as "(? & ? & ? & _)"; iFrame.
  Qed.

  Lemma map_of_regs_4 (r1 r2 r3 r4: RegName) (w1 w2 w3 w4: base.Word) :
    r1 ↣ᵣ w1 -∗ r2 ↣ᵣ w2 -∗ r3 ↣ᵣ w3 -∗ r4 ↣ᵣ w4 -∗
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> (<[r3:=w3]> (<[r4:=w4]> ∅)))), k ↣ᵣ y) ∗
     ⌜ r1 ≠ r2 ∧ r1 ≠ r3 ∧ r1 ≠ r4 ∧ r2 ≠ r3 ∧ r2 ≠ r4 ∧ r3 ≠ r4 ⌝.
  Proof.
    iIntros "H1 H2 H3 H4".
    iPoseProof (regname_neq with "H1 H2") as "%".
    iPoseProof (regname_neq with "H1 H3") as "%".
    iPoseProof (regname_neq with "H1 H4") as "%".
    iPoseProof (regname_neq with "H2 H3") as "%".
    iPoseProof (regname_neq with "H2 H4") as "%".
    iPoseProof (regname_neq with "H3 H4") as "%".
    rewrite !big_sepM_insert ?big_sepM_empty; simplify_map_eq; eauto.
    iFrame. eauto.
  Qed.

  Lemma regs_of_map_4 (r1 r2 r3 r4: RegName) (w1 w2 w3 w4: base.Word) :
    r1 ≠ r2 → r1 ≠ r3 → r1 ≠ r4 → r2 ≠ r3 → r2 ≠ r4 → r3 ≠ r4 →
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> (<[r3:=w3]> (<[r4:=w4]> ∅)))), k ↣ᵣ y) -∗
    r1 ↣ᵣ w1 ∗ r2 ↣ᵣ w2 ∗ r3 ↣ᵣ w3 ∗ r4 ↣ᵣ w4.
  Proof.
    intros. iIntros "Hmap". rewrite !big_sepM_insert ?big_sepM_empty; simplify_map_eq; eauto.
    iDestruct "Hmap" as "(? & ? & ? & ? & _)"; iFrame.
  Qed.

  (* ----------------------------------- FAIL RULES ---------------------------------- *)

  Lemma step_fail_inv c (σ σ': base.ExecConf) :
    ¬ isCorrectPC (reg σ !r! PC) →
    step (Executable, σ) (c, σ') →
    c = Failed ∧ σ' = σ.
  Proof.
    intros HPC Hs. inversion Hs; subst; auto; done.
  Qed.

  Lemma step_exec_inv φ p g b e a w instr (c: ConfFlag) (σ: ExecConf) :
    reg φ !! PC = Some (inr (Regular ((p, g), b, e, a))) →
    isCorrectPC (inr (Regular ((p, g), b, e, a))) →
    mem φ !! a = Some w →
    decodeInstrW' w = instr →
    ~ (∃ (rf : RegName) (rargs : list RegName), is_call rf rargs (mem φ) a e) ->
    step (Executable, φ) (c, σ) →
    exec instr φ = (c, σ).
  Proof.
    intros HPC Hpc Hm Hinstr Hnotcall. inversion 1.
    { exfalso. subst. rewrite /RegLocate HPC in H6. auto. }
    { exfalso. subst. rewrite /RegLocate HPC in H7. congruence. }
    { subst. rewrite /RegLocate HPC in H7; inversion H7; subst.
      rewrite /MemLocate Hm. eapply injective_projections; auto. }
    { subst. rewrite /RegLocate HPC in H7. congruence. }
    { subst. rewrite /RegLocate HPC in H7. inversion H7; subst.
      elim Hnotcall; eauto. }
    { subst. rewrite /RegLocate HPC in H7. congruence. }
  Qed.

  Lemma step_exec_inv' φ d p b e m a w instr (c: ConfFlag) (σ: ExecConf) :
    reg φ !! PC = Some (inr (Stk d p b e a)) →
    isCorrectPC (inr (Stk d p b e a)) →
    stack d ((reg φ, stk φ) :: callstack φ) = Some m ->
    m !! a = Some w →
    decodeInstrW' w = instr →
    ~ (∃ (rf : RegName) (rargs : list RegName), is_call rf rargs m a e) ->
    step (Executable, φ) (c, σ) →
    exec instr φ = (c, σ).
  Proof.
    intros HPC Hpc Hms Hm Hinstr Hnotcall. inversion 1.
    { exfalso. subst. rewrite /RegLocate HPC in H6. auto. }
    { exfalso. subst. rewrite /RegLocate HPC in H7. inversion H7; subst. congruence. }
    { subst. rewrite /RegLocate HPC in H7. congruence. }
    { subst. rewrite /RegLocate HPC in H7; inversion H7; subst.
      inversion H7; subst. rewrite Hms in H9; inversion H9; subst.
      rewrite /MemLocate Hm. eapply injective_projections; auto. }
    { subst. rewrite /RegLocate HPC in H7. congruence. }
    { subst. rewrite /RegLocate HPC in H7. inversion H7; subst.
      rewrite Hms in H9. inversion H9; subst.
      elim Hnotcall; eauto. }
  Qed.

  Lemma wp_notCorrectPC:
    forall E w,
      ~ isCorrectPC w ->
      {{{ PC ↣ᵣ w }}}
        Instr Executable @ E
      {{{ RET FailedV; PC ↣ᵣ w }}}.
  Proof.
    intros *. intros Hnpc.
    iIntros (ϕ) "HPC Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1 as [[[r m] stk] sfs]; simpl.
    iDestruct "Hσ1" as "[Hr [Hm Hstk]]".
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iApply fupd_frame_l.
    iSplit. by iPureIntro; apply normal_always_head_reducible.
    iModIntro. iIntros (e1 σ2 efs Hstep).
    apply prim_step_exec_inv in Hstep as (-> & -> & (c & -> & Hstep)).
    eapply step_fail_inv in Hstep as [-> ->]; eauto.
    iNext. iModIntro. iSplitR; auto. iFrame. cbn. by iApply "Hϕ".
    simpl. rewrite /RegLocate H3. eauto.
  Qed.

  (* Subcases for respecitvely permissions and bounds *)

  Lemma wp_notCorrectPC_perm E pc_p pc_g pc_b pc_e pc_a :
      pc_p ≠ RX ∧ pc_p ≠ RWX ∧ pc_p ≠ RWLX →
      {{{ PC ↣ᵣ inr (Regular ((pc_p,pc_g),pc_b,pc_e,pc_a))}}}
      Instr Executable @ E
      {{{ RET FailedV; True }}}.
  Proof.
    iIntros ([HnRX [HnRWX HnRWLX]] φ) "HPC Hwp".
    iApply (wp_notCorrectPC with "[HPC]");[|iFrame|].
    intro X; inversion X. destruct H9 as [Y | [Y | Y]]; congruence.
    iNext. iIntros "HPC /=".
    by iApply "Hwp".
  Qed.

  Lemma wp_notCorrectPC_perm' E d pc_p pc_b pc_e pc_a :
      pc_p ≠ RX ∧ pc_p ≠ RWX ∧ pc_p ≠ RWLX →
      {{{ PC ↣ᵣ inr (Stk d pc_p pc_b pc_e pc_a)}}}
      Instr Executable @ E
      {{{ RET FailedV; True }}}.
  Proof.
    iIntros ([HnRX [HnRWX HnRWLX]] φ) "HPC Hwp".
    iApply (wp_notCorrectPC with "[HPC]");[|iFrame|].
    intro X; inversion X. destruct H9 as [Y | [Y | Y]]; congruence.
    iNext. iIntros "HPC /=".
    by iApply "Hwp".
  Qed.

  (* ----------------------------------- ATOMIC RULES -------------------------------- *)

  Lemma wp_halt E pc_p pc_g pc_b pc_e pc_a w pc_p' :
    decodeInstrW' w = Halt →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr (Regular ((pc_p,pc_g),pc_b,pc_e,pc_a))) →

    {{{ PC ↣ᵣ inr (Regular ((pc_p,pc_g),pc_b,pc_e,pc_a)) ∗ pc_a ↣ₐ w }}}
      Instr Executable @ E
    {{{ RET HaltedV; PC ↣ᵣ inr (Regular (pc_p, pc_g, pc_b, pc_e, pc_a)) ∗ pc_a ↣ₐ w }}}.
  Proof.
    intros Hinstr Hfl Hvpc.
    iIntros (φ) "[Hpc Hpca] Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1 as [[[r m] stk] sf]; simpl.
    iDestruct "Hσ1" as "[Hr [Hm Hstk]]".
    iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
    iDestruct (@gen_heap_valid with "Hm Hpca") as %?.
    iModIntro.
    iSplitR. by iPureIntro; apply normal_always_head_reducible.
    iIntros (e2 σ2 efs Hstep).
    eapply prim_step_exec_inv in Hstep as (-> & -> & (c & -> & Hstep)).
    eapply step_exec_inv in Hstep; eauto. cbn in Hstep. simplify_eq.
    iNext. iModIntro. iSplitR; eauto. iFrame. iApply "Hφ". by iFrame.
    intro X. destruct X as [rf [rargs Hiscall]].
    destruct Hiscall as [a' [_ [_ [_ [_ [_ [_ [_ X]]]]]]]].
    destruct (X 0 ltac:(lia)) as [a'' [A B]].
    simpl in B. inversion B.
    assert ((pc_a + 0%nat)%a = Some pc_a) by (clear; solve_addr).
    rewrite A in H5; inversion H5; subst.
    rewrite /MemLocate H4 in B. inversion B; subst.
    rewrite /decodeInstrW' in Hinstr.
    rewrite decode_encode_instrW_inv in Hinstr.
    congruence.
  Qed.

  Lemma wp_halt' E d pc_p pc_b pc_e pc_a w pc_p' :
    decodeInstrW' w = Halt →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr (Stk d pc_p pc_b pc_e pc_a)) →

    {{{ PC ↣ᵣ inr (Stk d pc_p pc_b pc_e pc_a) ∗ pc_a ↣ₐ [d] w }}}
      Instr Executable @ E
    {{{ RET HaltedV; PC ↣ᵣ inr (Stk d pc_p pc_b pc_e pc_a) ∗ pc_a ↣ₐ [d] w }}}.
  Proof.
    intros Hinstr Hfl Hvpc.
    iIntros (φ) "[Hpc Hpca] Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1 as [[[r m] stk] sf]; simpl.
    iDestruct "Hσ1" as "[Hr [Hm Hstk]]".
    iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
    iDestruct (@gen_heap_valid with "Hstk Hpca") as %?.
    assert (XY: map_fold (λ a w (m : gmap (nat * Addr) base.Word), <[(length (map snd sf), a):=w]> m) (make_stack_map (map snd sf)) stk = make_stack_map (map snd ((r, stk)::sf))) by reflexivity.
    rewrite XY in H4. eapply make_stack_map_convert in H4.
    destruct H4 as [ms [HA HB]].
    iModIntro.
    iSplitR. by iPureIntro; apply normal_always_head_reducible.
    iIntros (e2 σ2 efs Hstep).
    eapply prim_step_exec_inv in Hstep as (-> & -> & (c & -> & Hstep)).
    eapply step_exec_inv' in Hstep; eauto. cbn in Hstep. simplify_eq.
    iNext. iModIntro. iSplitR; eauto. iFrame. iApply "Hφ". by iFrame.
    intro X. destruct X as [rf [rargs Hiscall]].
    destruct Hiscall as [a' [_ [_ [_ [_ [_ [_ [_ X]]]]]]]].
    destruct (X 0 ltac:(lia)) as [a'' [A B]].
    simpl in B. inversion B.
    assert ((pc_a + 0%nat)%a = Some pc_a) by (clear; solve_addr).
    rewrite A in H4; inversion H4; subst.
    rewrite /MemLocate HB in H5.
    rewrite -H5 /decodeInstrW' in Hinstr.
    rewrite decode_encode_instrW_inv in Hinstr.
    congruence.
  Qed.

  Lemma wp_fail E pc_p pc_g pc_b pc_e pc_a w pc_p' :
    decodeInstrW' w = Fail →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr (Regular ((pc_p,pc_g),pc_b,pc_e,pc_a))) →

    {{{ PC ↣ᵣ inr (Regular ((pc_p,pc_g),pc_b,pc_e,pc_a)) ∗ pc_a ↣ₐ w }}}
      Instr Executable @ E
    {{{ RET FailedV; PC ↣ᵣ inr (Regular ((pc_p,pc_g),pc_b,pc_e,pc_a)) ∗ pc_a ↣ₐ w }}}.
  Proof.
    intros Hinstr Hfl Hvpc.
    iIntros (φ) "[Hpc Hpca] Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1 as [[[r m] stk] sf]; simpl.
    iDestruct "Hσ1" as "[Hr [Hm Hstk]]".
    iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
    iDestruct (@gen_heap_valid with "Hm Hpca") as %?.
    iModIntro.
    iSplitR. by iPureIntro; apply normal_always_head_reducible.
    iIntros (e2 σ2 efs Hstep).
    eapply prim_step_exec_inv in Hstep as (-> & -> & (c & -> & Hstep)).
    eapply step_exec_inv in Hstep; eauto. cbn in Hstep. simplify_eq.
    iNext. iModIntro. iSplitR; eauto. iFrame. iApply "Hφ". by iFrame.
    intro X. destruct X as [rf [rargs Hiscall]].
    destruct Hiscall as [a' [_ [_ [_ [_ [_ [_ [_ X]]]]]]]].
    destruct (X 0 ltac:(lia)) as [a'' [A B]].
    simpl in B. inversion B.
    assert ((pc_a + 0%nat)%a = Some pc_a) by (clear; solve_addr).
    rewrite A in H5; inversion H5; subst.
    rewrite /MemLocate H4 in B. inversion B; subst.
    rewrite /decodeInstrW' in Hinstr.
    rewrite decode_encode_instrW_inv in Hinstr.
    congruence.
  Qed.

  Lemma wp_fail' E d pc_p pc_b pc_e pc_a w pc_p' :
    decodeInstrW' w = Fail →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr (Stk d pc_p pc_b pc_e pc_a)) →

    {{{ PC ↣ᵣ inr (Stk d pc_p pc_b pc_e pc_a) ∗ pc_a ↣ₐ [d] w }}}
      Instr Executable @ E
    {{{ RET FailedV; PC ↣ᵣ inr (Stk d pc_p pc_b pc_e pc_a) ∗ pc_a ↣ₐ [d] w }}}.
  Proof.
    intros Hinstr Hfl Hvpc.
    iIntros (φ) "[Hpc Hpca] Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1 as [[[r m] stk] sf]; simpl.
    iDestruct "Hσ1" as "[Hr [Hm Hstk]]".
    iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
    iDestruct (@gen_heap_valid with "Hstk Hpca") as %?.
    assert (XY: map_fold (λ a w (m : gmap (nat * Addr) base.Word), <[(length (map snd sf), a):=w]> m) (make_stack_map (map snd sf)) stk = make_stack_map (map snd ((r, stk)::sf))) by reflexivity.
    rewrite XY in H4. eapply make_stack_map_convert in H4.
    destruct H4 as [ms [HA HB]].
    iModIntro.
    iSplitR. by iPureIntro; apply normal_always_head_reducible.
    iIntros (e2 σ2 efs Hstep).
    eapply prim_step_exec_inv in Hstep as (-> & -> & (c & -> & Hstep)).
    eapply step_exec_inv' in Hstep; eauto. cbn in Hstep. simplify_eq.
    iNext. iModIntro. iSplitR; eauto. iFrame. iApply "Hφ". by iFrame.
    intro X. destruct X as [rf [rargs Hiscall]].
    destruct Hiscall as [a' [_ [_ [_ [_ [_ [_ [_ X]]]]]]]].
    destruct (X 0 ltac:(lia)) as [a'' [A B]].
    simpl in B. inversion B.
    assert ((pc_a + 0%nat)%a = Some pc_a) by (clear; solve_addr).
    rewrite A in H4; inversion H4; subst.
    rewrite /MemLocate HB in H5.
    rewrite -H5 /decodeInstrW' in Hinstr.
    rewrite decode_encode_instrW_inv in Hinstr.
    congruence.
  Qed.

End overlay_lang_rules.
