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

(* Points to predicates for registers *)
Notation "r ↣ᵣ{ q } w" := (mapsto (L:=RegName) (V:=base.Word) r q w)
  (at level 20, q at level 50, format "r  ↣ᵣ{ q }  w") : bi_scope.
Notation "r ↣ᵣ w" := (mapsto (L:=RegName) (V:=base.Word) r 1 w)%I (at level 20) : bi_scope.

(* Points to predicates for stack memory *)
(* Notation "a { n } ↣ₐ { q } w" := (mapsto (L:=(nat * Addr)) (V:=base.Word) (n, a) q w) *)
(*   (at level 20, q at level 50, format "a { n } ↣ₐ { q }  w") : bi_scope. *)
Notation "a ↣ₐ { n } w" := (mapsto (L:=nat * Addr) (V:=base.Word) (n, a) 1 w) (at level 20) : bi_scope.

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

End overlay_lang_rules.
