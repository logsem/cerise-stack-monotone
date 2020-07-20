From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac auth.
From cap_machine Require Export cap_lang mono_ref sts iris_extra.

(* CMRΑ for memory *)
Class memG Σ := MemG {
  mem_invG : invG Σ;
  mem_gen_memG :> gen_heapG Addr Word Σ}.

(* CMRA for registers *)
Class regG Σ := RegG {
  reg_invG : invG Σ;
  reg_gen_regG :> gen_heapG RegName Word Σ; }.


(* invariants for memory, and a state interpretation for (mem,reg) *)
Instance memG_irisG `{MachineParameters} `{memG Σ, regG Σ} : irisG cap_lang Σ := {
  iris_invG := mem_invG;
  state_interp σ κs _ := ((gen_heap_ctx σ.1) ∗ (gen_heap_ctx σ.2))%I;
  fork_post _ := True%I;
}.
Global Opaque iris_invG.

(* Points to predicates for registers *)
Notation "r ↦ᵣ{ q } w" := (mapsto (L:=RegName) (V:=Word) r q w)
  (at level 20, q at level 50, format "r  ↦ᵣ{ q }  w") : bi_scope.
Notation "r ↦ᵣ w" := (mapsto (L:=RegName) (V:=Word) r 1 w) (at level 20) : bi_scope.

(* Points to predicates for memory *)
Notation "a ↦ₐ { q } w" := (mapsto (L:=Addr) (V:=Word) a q w)
  (at level 20, q at level 50, format "a  ↦ₐ { q }  w") : bi_scope.
Notation "a ↦ₐ w" := (mapsto (L:=Addr) (V:=Word) a 1 w) (at level 20) : bi_scope.

(* capabilities. We use the monotone monoid to construct a pointer which may only
   update according to its permission *)
Section Capabilities.

  Definition LeastPermUpd (w : Word) : Perm :=
    match w with
    | inl _ => URW
    | inr ((_,Global),_,_,_) => URW
    | _ => URWL
    end.

  (* It could have been better to define the second in terms of the first here *)
  Lemma isLocal_RWL w:
    isLocalWord w = true → LeastPermUpd w = URWL.
  Proof.
    intros HiLW. destruct w.
    - cbv in HiLW. by exfalso.
    - destruct_cap c. cbv in HiLW.
      destruct c3; by cbv.
  Qed.

  Lemma not_isLocal_WL w:
    isLocalWord w = false → LeastPermUpd w = URW.
  Proof.
    intros HiLW. destruct w.
    - auto.
    - destruct_cap c. cbv in HiLW.
      destruct c3; by cbv.
  Qed.

  Lemma LeastPermUpd_atleast w:
    PermFlows URW (LeastPermUpd w).
  Proof.
    destruct w as [|c]; cbn. constructor.
    destruct_cap c. case_match; constructor.
  Qed.

  Inductive CapR : relation (Word * Perm) :=
  | P_res w p1 p2 : PermFlows p1 p2 → CapR (w,p2) (w,p1)
  | W_upd w1 w2 p : PermFlows (LeastPermUpd w2) p → CapR (w1,p) (w2,p).

  Definition PerP := λ p1 p2, PermFlows p2 p1.
  Lemma PerP_refl : ∀ p, PerP p p.
  Proof. apply PermFlows_refl. Qed.
  Lemma PerP_trans : ∀ P1 P2 P3, PerP P1 P2 → PerP P2 P3 → PerP P1 P3.
  Proof.
    intros p1 p2 p3. rewrite /PerP /PermFlows /PermFlowsTo;
    intros Hp1 Hp2.
    destruct p1,p2,p3; simpl; auto.
  Qed.

  Definition CapR_rtc := rtc CapR.

  Instance WordPerm_Equiv : Equiv (leibnizO (Word * Perm)).
  Proof. apply _. Defined.

  Instance WordPerm_Dist : Dist (leibnizO (Word * Perm)).
  Proof. apply _. Defined.

  Global Instance CapR_rtc_ProperPreOrder : monocmra.ProperPreOrder CapR_rtc.
  Proof. split; apply _. Defined.

  Instance PermFlows_Equiv : Equiv (leibnizO Perm).
  Proof. apply _. Defined.

  Instance PermFlows_Dist : Dist (leibnizO Perm).
  Proof. apply _. Defined.

  Global Instance PerP_ProperPreOrder : monocmra.ProperPreOrder PerP.
  Proof.
    split; [|apply _].
    split; intro;[rewrite /Reflexive;apply PerP_refl|rewrite /Transitive;apply PerP_trans].
  Defined.

  Global Instance PermFlows_ProperPreOrder : monocmra.ProperPreOrder PermFlows.
  Proof.
    split; [|apply _].
    split; intro;[rewrite /Reflexive;apply PerP_refl|rewrite /Transitive;apply PermFlows_trans].
  Defined.

  Context `{MonRefG (leibnizO _) CapR_rtc Σ, !memG Σ}.
  Notation A := (leibnizO (Word * Perm)).

  Definition MonRefMapsto_def l γ (v : A) :=
    (Exact (A:=A) CapR_rtc γ v ∗ atleast (A:=A) CapR_rtc γ v
           ∗ (l ↦ₐ v.1 ∨ ⌜v.2 = O⌝))%I.
  (* if the permission is O, we do not have ownership of the location *)
  Definition MonRefMapsto_aux l γ v : seal (MonRefMapsto_def l γ v).
  Proof. by eexists. Qed.
  Definition MonRefMapsto l γ v : iProp Σ := (MonRefMapsto_aux l γ v).(unseal).
  Definition MonRefMapsto_eq l γ v :
    MonRefMapsto l γ v = MonRefMapsto_def l γ v :=
    (MonRefMapsto_aux l γ v).(seal_eq).

  Notation "a ↦ₐ [ p ] w" := (∃ cap_γ, MonRefMapsto a cap_γ (w,p))%I
              (at level 20, p at level 50, format "a  ↦ₐ [ p ]  w") : bi_scope.

  Lemma MonRefAlloc l v p :
    l ↦ₐ v ==∗ l ↦ₐ[p] v.
  Proof.
    iIntros "Hl".
    iMod (MonRef_alloc (A:=A)) as (γ) "[HE Hal]"; eauto.
    iModIntro. iExists _.
    rewrite MonRefMapsto_eq /MonRefMapsto_def. iFrame.
  Qed.

  Lemma MonRefAlloc_sepL2 (p:Perm) (l1: list Addr) (l2: list Word) :
    ([∗ list] k;v ∈ l1;l2, k ↦ₐ v) ==∗ ([∗ list] k;v ∈ l1;l2, k ↦ₐ[p] v).
  Proof.
    iIntros "H".
    iDestruct (big_sepL2_mono with "H") as "H".
    { intros. apply MonRefAlloc. }
    iDestruct (big_sepL2_bupd with "H") as "H". eauto.
  Qed.

  Lemma MonRefAlloc_sepM (p:Perm) (m: gmap Addr Word) :
    ([∗ map] k↦v ∈ m, k ↦ₐ v) ==∗ ([∗ map] k↦v ∈ m, k ↦ₐ[p] v).
  Proof.
    iIntros "H".
    iDestruct (big_sepM_mono with "H") as "H".
    { intros. apply MonRefAlloc. }
    iDestruct (big_sepM_bupd with "H") as "H". eauto.
  Qed.

  Lemma MonRefDealloc l γ v p :
    MonRefMapsto l γ (v,p) -∗
                 (l ↦ₐ v ∨ ⌜p = O⌝) ∗
       ∃ P, P ∗ (P -∗ ∀ w, ⌜CapR_rtc (v,p) w⌝ -∗
                       (l ↦ₐ w.1 ∨ ⌜w.2 = O⌝) ==∗ MonRefMapsto l γ w).
  Proof.
    rewrite MonRefMapsto_eq /MonRefMapsto_def.
    iIntros "(HE & Ha & Hl)".
    iFrame.
    iDestruct (MonRef_related (A:=A) with "HE Ha") as %Hab.
    iExists (Exact (A:=A) CapR_rtc γ (v,p) ∗
                   atleast (A:=A) CapR_rtc γ (v,p))%I; iFrame.
    iIntros "[HE Ha]". iIntros ([w p'] Hcap) "Hl /=".
    rewrite MonRefMapsto_eq /MonRefMapsto_def; iFrame.
    iMod (MonRef_update (A:=A) CapR_rtc γ (v,p) with "HE") as "[$ $]"; eauto.
  Qed.

  Lemma snap_shot l γ v : MonRefMapsto l γ v ==∗ atleast (A:=A) CapR_rtc γ v.
  Proof.
    rewrite MonRefMapsto_eq /MonRefMapsto_def atleast_eq /atleast_def.
    iIntros "(HE & Hal & Hl)"; eauto.
  Qed.

  Lemma recall l γ v w :
    atleast (A:=A) CapR_rtc γ w -∗ MonRefMapsto l γ v -∗ ⌜CapR_rtc w v⌝.
  Proof.
    rewrite MonRefMapsto_eq /MonRefMapsto_def.
    iIntros "Hal (HE & Hal' & Hl)".
    iDestruct (MonRef_related with "HE Hal") as "?"; eauto.
  Qed.

  Instance Exact_Timeless : Timeless (Exact (A:=A) CapR_rtc γ v).
  Proof. apply _. Qed.

  Instance atleast_Timeless : Timeless (atleast (A:=A) CapR_rtc γ v).
  Proof.
    intros. rewrite (atleast_eq (A:=A) CapR_rtc γ v). apply _. Qed.

  Global Instance MonRefMapsto_Timeless : Timeless (MonRefMapsto l γ v).
  Proof.
    intros.
    rewrite MonRefMapsto_eq /MonRefMapsto_def.
    apply _.
  Qed.

End Capabilities.

Section World.
  Local Definition STS : Type := (STS_states * STS_rels).

  Inductive RelW : (STS * bool) → (STS * bool) -> Prop :=
  | RelW_pr (W1 W2 : STS) : related_sts_priv W1.1 W2.1 W1.2 W2.2
                            -> RelW (W1,true) (W2,true)
  | RelW_pu (W1 W2 : STS) : related_sts_pub W1.1 W2.1 W1.2 W2.2
                            -> RelW (W1,false) (W2,false)
  | RelW_pu_to_pr (W1 W2 : STS) : related_sts_priv W1.1 W2.1 W1.2 W2.2
                              → RelW (W1,false) (W2,true).

  Instance PrivRelW_Equiv : Equiv (leibnizO (STS * bool)).
  Proof. apply _. Defined.

  Instance PrivRelW_Dist : Dist (leibnizO (STS * bool)).
  Proof. apply _. Defined.

  Global Instance PrivRelW_ProperPreOrder : monocmra.ProperPreOrder RelW.
  Proof.
    split; [|apply _].
    split; intro.
    - destruct x. destruct b.
      + apply RelW_pr. apply related_sts_priv_refl.
      + apply RelW_pu. apply related_sts_pub_refl.
    - intros y z. destruct x,y,z; inversion 1; inversion 1.
      + constructor. apply related_sts_priv_trans with s0.1 s0.2; auto.
      + constructor. apply related_sts_pub_trans with s0.1 s0.2; auto.
      + subst. constructor. apply related_sts_pub_priv_trans with s0.1 s0.2; auto.
      + subst. constructor. apply related_sts_priv_trans with s0.1 s0.2; auto.
  Defined.

End World.

Definition logN : namespace := nroot .@ "logN".

(* --------------------------- LTAC DEFINITIONS ----------------------------------- *)

Ltac inv_head_step :=
  repeat match goal with
         | _ => progress simplify_map_eq/= (* simplify memory stuff *)
         | H : to_val _ = Some _ |- _ => apply of_to_val in H
         | H : _ = of_val ?v |- _ =>
           is_var v; destruct v; first[discriminate H|injection H as H]
         | H : cap_lang.prim_step ?e _ _ _ _ _ |- _ =>
           try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable *)
           (*    and can thus better be avoided. *)
           let φ := fresh "φ" in
           inversion H as [| φ]; subst φ; clear H
         end.

Ltac option_locate_m_once m :=
  match goal with
  | H : m !! ?a = Some ?w |- _ => let Htmp := fresh in
                                rename H into Htmp ;
                                let Ha := fresh "H" m a in
                                pose proof (mem_lookup_eq _ _ _ Htmp) as Ha; clear Htmp
  end.
Ltac option_locate_r_once r :=
  match goal with
  | H : r !! ?a = Some ?w |- _ => let Htmp := fresh in
                                rename H into Htmp ;
                                let Ha := fresh "H" r a in
                                pose proof (regs_lookup_eq _ _ _ Htmp) as Ha; clear Htmp
  end.
Ltac option_locate_mr_once m r :=
  first [ option_locate_m_once m | option_locate_r_once r ].
Ltac option_locate_mr m r :=
  repeat option_locate_mr_once m r.
Ltac option_locate_m m :=
  repeat option_locate_m_once m.
Ltac option_locate_r m :=
  repeat option_locate_r_once m.

(* Permission-carrying memory type, used to describe maps of locations and permissions in the load and store cases *)
Notation PermMem := (gmap Addr (Perm * Word)).

Section cap_lang_rules.
  Context `{MachineParameters}.
  Context `{memG Σ, regG Σ, MonRefG (leibnizO _) CapR_rtc Σ,
            World: MonRefG (leibnizO _) RelW Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : cap_lang.expr.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : cap_lang.val.
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.
  Notation A := (leibnizO (Word * Perm)).
  Notation P := (leibnizO Perm).
  Notation WORLD_S := (leibnizO ((STS_states * STS_rels) * bool)).
  Implicit Types M : WORLD_S.
  Implicit Types W : (STS_states * STS_rels).

  (* Definition atleast_p γ p := atleast (A:=P) PermFlows γ p. *)
  (* Definition Exact_p γ p := Exact (A:=P) PermFlows γ p. *)

  (* --------------------------- WORLD REL MONOID ----------------------------------- *)
  Definition atleast_w γ M := atleast (A:=WORLD_S) RelW γ M.
  Definition Exact_w γ M := Exact (A:=WORLD_S) RelW γ M.

  Lemma RelW_private M W γ :
    atleast_w γ M -∗ Exact_w γ (W,true) -∗ ⌜related_sts_priv M.1.1 W.1 M.1.2 W.2⌝.
  Proof.
    rewrite /atleast_w /Exact_w.
    iIntros "#HM HW".
    iDestruct (MonRef_related (A:=WORLD_S) with "HW HM") as %Hrel.
      by inversion Hrel; subst.
  Qed.

  Lemma RelW_public M W γ :
    atleast_w γ M -∗ Exact_w γ (W,false) -∗ ⌜related_sts_pub M.1.1 W.1 M.1.2 W.2⌝.
  Proof.
    rewrite /atleast_w /Exact_w.
    iIntros "#HM HW".
    iDestruct (MonRef_related (A:=WORLD_S) with "HW HM") as %Hrel.
      by inversion Hrel; subst.
  Qed.

  Lemma RelW_public_to_private W γ :
    Exact_w γ (W,false) ==∗ Exact_w γ (W,true) ∗ atleast_w γ (W,true).
  Proof.
    iIntros "HW".
    iMod (MonRef_update (A:=WORLD_S) with "HW"); auto.
    constructor. apply related_sts_priv_refl.
  Qed.

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

  (* Conditionally unify on the read register value *)
  Definition read_reg_inr  (regs : Reg) (r : RegName) p g b e a :=
    regs !! r = Some (inr ((p, g), b, e, a)) ∨ ∃ z, regs !! r = Some(inl z).


  (* ------------------------- registers points-to --------------------------------- *)

  Lemma regname_dupl_false r w1 w2 :
    r ↦ᵣ w1 -∗ r ↦ᵣ w2 -∗ False.
  Proof.
    iIntros "Hr1 Hr2".
    iDestruct (mapsto_valid_2 with "Hr1 Hr2") as %?.
    contradiction.
  Qed.

  Lemma regname_neq r1 r2 w1 w2 :
    r1 ↦ᵣ w1 -∗ r2 ↦ᵣ w2 -∗ ⌜ r1 ≠ r2 ⌝.
  Proof.
    iIntros "H1 H2" (?). subst r1. iApply (regname_dupl_false with "H1 H2").
  Qed.

  Lemma map_of_regs_1 (r1: RegName) (w1: Word) :
    r1 ↦ᵣ w1 -∗
    ([∗ map] k↦y ∈ {[r1 := w1]}, k ↦ᵣ y).
  Proof. by rewrite big_sepM_singleton. Qed.

  Lemma regs_of_map_1 (r1: RegName) (w1: Word) :
    ([∗ map] k↦y ∈ {[r1 := w1]}, k ↦ᵣ y) -∗
    r1 ↦ᵣ w1.
  Proof. by rewrite big_sepM_singleton. Qed.

  Lemma map_of_regs_2 (r1 r2: RegName) (w1 w2: Word) :
    r1 ↦ᵣ w1 -∗ r2 ↦ᵣ w2 -∗
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> ∅)), k ↦ᵣ y) ∗ ⌜ r1 ≠ r2 ⌝.
  Proof.
    iIntros "H1 H2". iPoseProof (regname_neq with "H1 H2") as "%".
    rewrite !big_sepM_insert ?big_sepM_empty; eauto.
    2: by apply lookup_insert_None; split; eauto.
    iFrame. eauto.
  Qed.

  Lemma regs_of_map_2 (r1 r2: RegName) (w1 w2: Word) :
    r1 ≠ r2 →
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> ∅)), k ↦ᵣ y) -∗
    r1 ↦ᵣ w1 ∗ r2 ↦ᵣ w2.
  Proof.
    iIntros (?) "Hmap". rewrite !big_sepM_insert ?big_sepM_empty; eauto.
    by iDestruct "Hmap" as "(? & ? & _)"; iFrame.
    apply lookup_insert_None; split; eauto.
  Qed.

  Lemma map_of_regs_3 (r1 r2 r3: RegName) (w1 w2 w3: Word) :
    r1 ↦ᵣ w1 -∗ r2 ↦ᵣ w2 -∗ r3 ↦ᵣ w3 -∗
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> (<[r3:=w3]> ∅))), k ↦ᵣ y) ∗
     ⌜ r1 ≠ r2 ∧ r1 ≠ r3 ∧ r2 ≠ r3 ⌝.
  Proof.
    iIntros "H1 H2 H3".
    iPoseProof (regname_neq with "H1 H2") as "%".
    iPoseProof (regname_neq with "H1 H3") as "%".
    iPoseProof (regname_neq with "H2 H3") as "%".
    rewrite !big_sepM_insert ?big_sepM_empty; simplify_map_eq; eauto.
    iFrame. eauto.
  Qed.

  Lemma regs_of_map_3 (r1 r2 r3: RegName) (w1 w2 w3: Word) :
    r1 ≠ r2 → r1 ≠ r3 → r2 ≠ r3 →
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> (<[r3:=w3]> ∅))), k ↦ᵣ y) -∗
    r1 ↦ᵣ w1 ∗ r2 ↦ᵣ w2 ∗ r3 ↦ᵣ w3.
  Proof.
    iIntros (? ? ?) "Hmap". rewrite !big_sepM_insert ?big_sepM_empty; simplify_map_eq; eauto.
    iDestruct "Hmap" as "(? & ? & ? & _)"; iFrame.
  Qed.

  Lemma map_of_regs_4 (r1 r2 r3 r4: RegName) (w1 w2 w3 w4: Word) :
    r1 ↦ᵣ w1 -∗ r2 ↦ᵣ w2 -∗ r3 ↦ᵣ w3 -∗ r4 ↦ᵣ w4 -∗
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> (<[r3:=w3]> (<[r4:=w4]> ∅)))), k ↦ᵣ y) ∗
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

  Lemma regs_of_map_4 (r1 r2 r3 r4: RegName) (w1 w2 w3 w4: Word) :
    r1 ≠ r2 → r1 ≠ r3 → r1 ≠ r4 → r2 ≠ r3 → r2 ≠ r4 → r3 ≠ r4 →
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> (<[r3:=w3]> (<[r4:=w4]> ∅)))), k ↦ᵣ y) -∗
    r1 ↦ᵣ w1 ∗ r2 ↦ᵣ w2 ∗ r3 ↦ᵣ w3 ∗ r4 ↦ᵣ w4.
  Proof.
    intros. iIntros "Hmap". rewrite !big_sepM_insert ?big_sepM_empty; simplify_map_eq; eauto.
    iDestruct "Hmap" as "(? & ? & ? & ? & _)"; iFrame.
  Qed.

  (* -------------- semantic heap + a map of pointsto -------------------------- *)

  Lemma gen_heap_valid_inSepM:
    ∀ (L V : Type) (EqDecision0 : EqDecision L) (H : Countable L)
      (Σ : gFunctors) (gen_heapG0 : gen_heapG L V Σ)
      (σ σ' : gmap L V) (l : L) (q : Qp) (v : V),
      σ' !! l = Some v →
      gen_heap_ctx σ -∗
      ([∗ map] k↦y ∈ σ', mapsto k q y) -∗
      ⌜σ !! l = Some v⌝.
  Proof.
    intros * Hσ'.
    rewrite (big_sepM_delete _ σ' l) //. iIntros "? [? ?]".
    iApply (gen_heap_valid with "[$]"). eauto.
  Qed.

  Lemma gen_heap_valid_inSepM':
    ∀ (L V : Type) (EqDecision0 : EqDecision L) (H : Countable L)
      (Σ : gFunctors) (gen_heapG0 : gen_heapG L V Σ)
      (σ σ' : gmap L V) (q : Qp),
      gen_heap_ctx σ -∗
      ([∗ map] k↦y ∈ σ', mapsto k q y) -∗
      ⌜forall (l: L) (v: V), σ' !! l = Some v → σ !! l = Some v⌝.
  Proof.
    intros *. iIntros "? Hmap" (l v Hσ').
    rewrite (big_sepM_delete _ σ' l) //. iDestruct "Hmap" as "[? ?]".
    iApply (gen_heap_valid with "[$]"). eauto.
  Qed.

  Lemma gen_heap_valid_inclSepM:
    ∀ (L V : Type) (EqDecision0 : EqDecision L) (H : Countable L)
      (Σ : gFunctors) (gen_heapG0 : gen_heapG L V Σ)
      (σ σ' : gmap L V) (q : Qp),
      gen_heap_ctx σ -∗
      ([∗ map] k↦y ∈ σ', mapsto k q y) -∗
      ⌜σ' ⊆ σ⌝.
  Proof.
    intros *. iIntros "Hσ Hmap".
    iDestruct (gen_heap_valid_inSepM' with "Hσ Hmap") as "#H".
    iDestruct "H" as %Hincl. iPureIntro. intro l.
    unfold option_relation.
    destruct (σ' !! l) eqn:HH'; destruct (σ !! l) eqn:HH; naive_solver.
  Qed.

  Lemma gen_heap_valid_allSepM:
    ∀ (L V : Type) (EqDecision0 : EqDecision L) (H : Countable L)
      (EV: Equiv V) (REV: Reflexive EV) (LEV: @LeibnizEquiv V EV)
      (Σ : gFunctors) (gen_heapG0 : gen_heapG L V Σ)
      (σ σ' : gmap L V) (q : Qp),
      (forall (l:L), is_Some (σ' !! l)) →
      gen_heap_ctx σ -∗
      ([∗ map] k↦y ∈ σ', mapsto k q y) -∗
      ⌜ σ = σ' ⌝.
  Proof.
    intros * ? ? * Hσ'. iIntros "A B".
    iAssert (⌜ forall l, σ !! l = σ' !! l ⌝)%I with "[A B]" as %HH.
    { iIntros (l).
      specialize (Hσ' l). unfold is_Some in Hσ'. destruct Hσ' as [v Hσ'].
      rewrite Hσ'.
      eapply (gen_heap_valid_inSepM _ _ _ _ _ _ σ σ') in Hσ'.
      iApply (Hσ' with "[$]"). eauto. }
    iPureIntro. eapply map_leibniz. intro.
    eapply leibniz_equiv_iff. auto.
    Unshelve.
    unfold equiv. unfold Reflexive. intros [ x |].
    { unfold option_equiv. constructor. apply REV. } constructor.
  Qed.

  Lemma gen_heap_update_inSepM :
    ∀ {L V : Type} {EqDecision0 : EqDecision L}
      {H : Countable L} {Σ : gFunctors}
      {gen_heapG0 : gen_heapG L V Σ}
      (σ σ' : gmap L V) (l : L) (v : V),
      is_Some (σ' !! l) →
      gen_heap_ctx σ
      -∗ ([∗ map] k↦y ∈ σ', mapsto k 1 y)
      ==∗ gen_heap_ctx (<[l:=v]> σ)
          ∗ [∗ map] k↦y ∈ (<[l:=v]> σ'), mapsto k 1 y.
  Proof.
    intros * Hσ'. destruct Hσ'.
    rewrite (big_sepM_delete _ σ' l) //. iIntros "Hh [Hl Hmap]".
    iMod (gen_heap_update with "Hh Hl") as "[Hh Hl]". iModIntro.
    iSplitL "Hh"; eauto.
    rewrite (big_sepM_delete _ (<[l:=v]> σ') l).
    { rewrite delete_insert_delete. iFrame. }
    rewrite lookup_insert //.
  Qed.

  (* --------------------------- CAPABILITY PREDICATE ------------------------------- *)
  (* Points to predicates for memory *)
  Notation "a ↦ₐ [ p ] w" := (∃ cap_γ, MonRefMapsto a cap_γ (w,p))%I
              (at level 20, p at level 50, format "a  ↦ₐ [ p ]  w") : bi_scope.
  Definition mapsto_nO (a: Addr) (p: Perm) (w: Word) := (a ↦ₐ[p] w ∗ ⌜p ≠ O⌝)%I.

  Lemma gen_heap_valid_cap
        (σ : gmap Addr Word) (a : Addr) (w : Word) (p : Perm) :
    p ≠ O →
    gen_heap_ctx σ -∗ a ↦ₐ[p] w -∗ ⌜σ !! a = Some w⌝.
  Proof.
    iIntros (Hne) "Hσ Ha".
    iDestruct "Ha" as (γ_cap) "Ha".
    rewrite MonRefMapsto_eq /MonRefMapsto_def /=.
    iDestruct "Ha" as "(Hex & Hal & [Ha | %])"; [|contradiction].
    iApply (gen_heap_valid with "Hσ Ha").
  Qed.

  Lemma cap_duplicate_false a p p' w w' :
    p ≠ O ∧ p' ≠ O →
    a ↦ₐ[p] w ∗ a ↦ₐ[p'] w' -∗ False.
  Proof.
    iIntros ([Hne1 Hne2]) "[Ha1 Ha2]".
    iDestruct "Ha1" as (γ1) "Ha1".
    iDestruct "Ha2" as (γ2) "Ha2".
    do 2 rewrite MonRefMapsto_eq /MonRefMapsto_def /=.
    iDestruct "Ha1" as "(_ & _ & [Ha | %])"; [|contradiction].
    iDestruct "Ha2" as "(_ & _ & [Ha' | %])"; [|contradiction].
    iDestruct (mapsto_valid_2 with "Ha Ha'") as %Hcontr. done.
  Qed.

  Lemma cap_restrict (a : Addr) (w : Word) (p p' : Perm) :
    PermFlows p' p →
    a ↦ₐ[p] w ==∗ a ↦ₐ[p'] w.
  Proof.
    iIntros (Hfl) "Ha".
    iDestruct "Ha" as (γ_cap) "Ha". iExists (γ_cap).
    do 2 rewrite MonRefMapsto_eq /MonRefMapsto_def /=.
    iDestruct "Ha" as "(Hex & Hal & Ha)".
    iMod (MonRef_update (A:=A) with "Hex") as "[HE HFr']"; eauto.
    right with (w,p');[|left].
    constructor; auto.
    iFrame.
    iDestruct "Ha" as "[Ha | %]".
    - iLeft. by iFrame.
    - subst. destruct p'; inversion Hfl. by iRight.
  Qed.

  Lemma gen_heap_update_cap (σ : gmap Addr Word) (a : Addr) (p : Perm) (w w' : Word) :
    PermFlows (LeastPermUpd w') p →
    gen_heap_ctx σ -∗ a ↦ₐ[p] w ==∗ gen_heap_ctx (<[a:=w']> σ) ∗ a ↦ₐ[p] w'.
  Proof.
    iIntros (Hf) "Hσ Ha".
    iDestruct "Ha" as (γ_cap) "Ha". iApply bi.sep_exist_l. iExists γ_cap.
    do 2 rewrite MonRefMapsto_eq /MonRefMapsto_def /=.
    assert (p ≠ O) as Ho.
    { assert (PermFlows URW p) as Hflp.
      by etransitivity; eauto using LeastPermUpd_atleast.
      inversion Hflp; destruct p; eauto. }
    iDestruct "Ha" as "(Hex & Hal & [Ha | %])"; [|contradiction].
    iMod (MonRef_update (A:=A) with "Hex") as "[$ $]"; eauto.
    { right with (w',p); [|left]. by constructor. }
    by iMod (gen_heap_update with "Hσ Ha") as "[$ $]".
  Qed.

  Lemma wp_lift_atomic_head_step_no_fork_determ {s E Φ} e1 :
    to_val e1 = None →
    (∀ (σ1:cap_lang.state) κ κs n, state_interp σ1 (κ ++ κs) n ={E}=∗
     ∃ κ e2 (σ2:cap_lang.state) efs, ⌜cap_lang.prim_step e1 σ1 κ e2 σ2 efs⌝ ∗
      (▷ |==> (state_interp σ2 κs n ∗ from_option Φ False (to_val e2))))
      ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (?) "H". iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 κ κs n)  "Hσ1 /=".
    iMod ("H" $! σ1 κ κs n with "[Hσ1]") as "H"; auto.
    iDestruct "H" as (κ' e2 σ2 efs) "[H1 H2]".
    iModIntro. iSplit.
    - rewrite /head_reducible /=.
      iExists κ', e2, σ2, efs. auto.
    - iNext. iIntros (? ? ?) "H".
      iDestruct "H" as %Hs1.
      iDestruct "H1" as %Hs2.
      destruct (cap_lang_determ _ _ _ _ _ _ _ _ _ _ Hs1 Hs2) as [Heq1 [Heq2 [Heq3 Heq4]]].
      subst a; subst a0; subst a1.
      iMod "H2". iModIntro. iFrame. inv Hs1; auto.
  Qed.

  (* -------------- predicates on memory maps -------------------------- *)

  Lemma resource_exists a p' w:
    a ↦ₐ[p'] w ⊣⊢ (∃ (p : Perm) (w0 : Word), ⌜(p', w) = (p, w0)⌝ ∗ a ↦ₐ[p] w0).
  Proof.
    iSplit; first by auto.
    iIntros "HH"; iDestruct "HH" as (p w0 Heq) "HH"; by inversion Heq.
  Qed.

  Lemma address_dupl_false a w1 w2 p1 p2 :
    p1 ≠ O → p2 ≠ O → a ↦ₐ[p1] w1 -∗ a ↦ₐ[p2] w2 -∗ False.
  Proof.
    iIntros (p1ne p2ne) "Hr1 Hr2".
    iDestruct "Hr1" as (g1) "Hr1".
    iDestruct "Hr2" as (g2) "Hr2".
    iDestruct (MonRefDealloc with "[$Hr1]") as "[[Hr1 | %] _]"; last congruence.
    iDestruct (MonRefDealloc with "[$Hr2]") as "[[Hr2 | %] _]"; last congruence.
    iDestruct (mapsto_valid_2 with "Hr1 Hr2") as %?.
    contradiction.
  Qed.

  Lemma extract_sep_if_split a pc_a P Q R:
     (if (a =? pc_a)%a then P else Q ∗ R)%I ≡
     ((if (a =? pc_a)%a then P else Q) ∗
     if (a =? pc_a)%a then emp else R)%I.
  Proof.
    destruct (a =? pc_a)%a; auto.
    iSplit; auto. iIntros "[H1 H2]"; auto.
  Qed.

  Lemma address_neq a1 a2 w1 w2 p1 p2  :
    p1 ≠ O → p2 ≠ O → a1 ↦ₐ[p1] w1 -∗ a2 ↦ₐ[p2] w2 -∗ ⌜ a1 ≠ a2 ⌝.
  Proof.
    iIntros (p1ne p2ne) "H1 H2". iIntros (contr). subst a1. iApply (address_dupl_false with "H1 H2");auto.
  Qed.

  Lemma memMap_resource_0  :
        True ⊣⊢ ([∗ map] a↦pw ∈ ∅, ∃ p w, ⌜pw = (p,w)⌝ ∗ a ↦ₐ[p] w).
  Proof.
    by rewrite big_sepM_empty.
  Qed.


  Lemma memMap_resource_1 (a : Addr) (p' : Perm) (w : Word)  :
        a ↦ₐ[p'] w  ⊣⊢ ([∗ map] a↦pw ∈ <[a:=(p',w)]> ∅, ∃ p w, ⌜pw = (p,w)⌝ ∗ a ↦ₐ[p] w)%I.
  Proof.
    rewrite big_sepM_delete; last by apply lookup_insert.
    rewrite delete_insert; last by auto. rewrite -memMap_resource_0.
    iSplit; iIntros "HH".
    - rewrite resource_exists. by iSplitL.
    - rewrite resource_exists. by iDestruct "HH" as "[HH _]".
  Qed.

  Lemma memMap_resource_2ne (a1 a2 : Addr) (p1' p2' : Perm) (w1 w2 : Word)  :
    a1 ≠ a2 → ([∗ map] a↦pw ∈  <[a1:=(p1',w1)]> (<[a2:=(p2',w2)]> ∅), ∃ p w, ⌜pw = (p,w)⌝ ∗ a ↦ₐ[p] w)%I ⊣⊢ a1 ↦ₐ[p1'] w1 ∗ a2 ↦ₐ[p2'] w2.
  Proof.
    intros.
    rewrite big_sepM_delete; last by apply lookup_insert.
    rewrite (big_sepM_delete _ _ a2 (p2',w2)); rewrite delete_insert; try by rewrite lookup_insert_ne. 2: by rewrite lookup_insert.
    rewrite delete_insert; auto.
    rewrite -memMap_resource_0.
    iSplit; iIntros "HH".
    - iDestruct "HH" as "[H1 [H2 _ ] ]".  iSplitL "H1"; by rewrite -resource_exists.
    - iDestruct "HH" as "[H1 H2]". iSplitL "H1"; auto.
  Qed.

  Lemma memMap_resource_2ne_apply (a1 a2 : Addr) (p1' p2' : Perm) (w1 w2 : Word)  :
    p1' ≠ O → p2' ≠ O → a1 ↦ₐ[p1'] w1 -∗ a2 ↦ₐ[p2'] w2 -∗ ([∗ map] a↦pw ∈  <[a1:=(p1',w1)]> (<[a2:=(p2',w2)]> ∅), ∃ p w, ⌜pw = (p,w)⌝ ∗ a ↦ₐ[p] w) ∗ ⌜a1 ≠ a2⌝.
  Proof.
    iIntros (Hne1 Hne2) "Hi Hr2a".
    iDestruct (address_neq  with "Hi Hr2a") as %Hne; auto.
    iSplitL; last by auto.
    iApply memMap_resource_2ne; auto. iSplitL "Hi"; auto.
  Qed.

  Lemma memMap_resource_2gen (a1 a2 : Addr) (p1' p2' : Perm) (w1 w2 : Word)  :
    ( ∃ mem, ([∗ map] a↦pw ∈ mem, ∃ p w, ⌜pw = (p,w)⌝ ∗ a ↦ₐ[p] w) ∧
       ⌜ if  (a2 =? a1)%a
       then mem =  (<[a1:=(p1',w1)]> ∅)
       else mem = <[a1:=(p1',w1)]> (<[a2:=(p2',w2)]> ∅)⌝
    )%I ⊣⊢ (a1 ↦ₐ[p1'] w1 ∗ if (a2 =? a1)%a then emp else a2 ↦ₐ[p2'] w2) .
  Proof.
    destruct (a2 =? a1)%a eqn:Heq.
    - apply Z.eqb_eq, z_of_eq in Heq. rewrite memMap_resource_1.
      iSplit.
      * iDestruct 1 as (mem) "[HH ->]".  by iSplit.
      * iDestruct 1 as "[Hmap _]". iExists (<[a1:=(p1', w1)]> ∅); iSplitL; auto.
    - apply Z.eqb_neq in Heq.
      rewrite -memMap_resource_2ne; auto. 2 : congruence.
      iSplit.
      * iDestruct 1 as (mem) "[HH ->]". done.
      * iDestruct 1 as "Hmap". iExists (<[a1:=(p1', w1)]> (<[a2:=(p2', w2)]> ∅)); iSplitL; auto.
  Qed.

  Lemma memMap_resource_2gen_d (a1 a2 : Addr) (p1' p2' : Perm) (w1 w2 : Word)  :
    ( ∃ mem, ([∗ map] a↦pw ∈ mem, ∃ p w, ⌜pw = (p,w)⌝ ∗ a ↦ₐ[p] w) ∧
       ⌜ if  (a2 =? a1)%a
       then mem =  (<[a1:=(p1',w1)]> ∅)
       else mem = <[a1:=(p1',w1)]> (<[a2:=(p2',w2)]> ∅)⌝
    ) -∗ (a1 ↦ₐ[p1'] w1 ∗ if (a2 =? a1)%a then emp else a2 ↦ₐ[p2'] w2) .
  Proof.
    iIntros. by rewrite memMap_resource_2gen.
  Qed.

  (* Not the world's most beautiful lemma, but it does avoid us having to fiddle around with a later under an if in proofs *)
  Lemma memMap_resource_2gen_clater (a1 a2 : Addr) (p1' p2' : Perm) (w1 w2 : Word)  :
    (▷ a1 ↦ₐ[p1'] w1) -∗
    (if (a2 =? a1)%a then emp else ▷ a2 ↦ₐ[p2'] w2) -∗
    (∃ mem, ▷ ([∗ map] a↦pw ∈ mem, ∃ p w, ⌜pw = (p,w)⌝ ∗ a ↦ₐ[p] w) ∗
       ⌜if  (a2 =? a1)%a
       then mem =  (<[a1:=(p1',w1)]> ∅)
       else mem = <[a1:=(p1',w1)]> (<[a2:=(p2',w2)]> ∅)⌝
    )%I.
  Proof.
    iIntros "Hc1 Hc2".
    destruct (a2 =? a1)%a eqn:Heq.
    - iExists (<[a1:=(p1', w1)]> ∅); iSplitL; auto. iNext. by rewrite memMap_resource_1.
    - iExists (<[a1:=(p1', w1)]> (<[a2:=(p2', w2)]> ∅)); iSplitL; auto.
      iNext. iDestruct (memMap_resource_2ne with "[$Hc1 $Hc2]") as "Hmem".
      {apply Z.eqb_neq in Heq. congruence. }
      done.
  Qed.

  Lemma memMap_delete:
    ∀(a : Addr) (p' : Perm) (w : Word) (mem0 : PermMem),
      mem0 !! a = Some (p', w) →
      ([∗ map] a↦pw ∈ mem0, ∃ (p : Perm) (w0 : Word), ⌜pw = (p, w0)⌝ ∗ a ↦ₐ[p] w0)
      ⊣⊢ (a ↦ₐ[p'] w
         ∗ ([∗ map] k↦y ∈ delete a mem0, ∃ (p : Perm) (w0 : Word),
               ⌜y = (p, w0)⌝ ∗ k ↦ₐ[p] w0)).
  Proof.
    intros a p' w mem0 Hmem0a.
    rewrite resource_exists.
    rewrite -(big_sepM_delete _ _ a); auto.
  Qed.

  Lemma gen_mem_valid_inSepM:
    ∀ (a : Addr) (p' : Perm) (r1 r2 : RegName) (w : Word) (mem0 : PermMem) (r : Reg) (m : Mem),
      p' ≠ O →
      mem0 !! a = Some (p', w) →
      gen_heap_ctx m
                   -∗ ([∗ map] a↦pw ∈ mem0, ∃ (p : Perm) (w0 : Word), ⌜pw = (p, w0)⌝ ∗ a ↦ₐ[p] w0)
                   -∗ ⌜m !! a = Some w⌝.
  Proof.
    iIntros (a p' r1 r2 w mem0 r m Hpnz Hmem_pc) "Hm Hmem".
    iDestruct (memMap_delete a with "Hmem") as "[Hpc_a Hmem]"; eauto.
    iDestruct (gen_heap_valid_cap with "Hm Hpc_a") as %?; auto.
  Qed.

  Lemma mem_v_implies_m_v:
    ∀ (mem0 : PermMem) (m : Mem) (p : Perm) (g : Locality) (b e a : Addr) (p' : Perm) (v : Word),
      mem0 !! a = Some (p', v)
      → p' ≠ O
      → ([∗ map] a0↦pw ∈ mem0, ∃ (p0 : Perm) (w : Word),
            ⌜pw = (p0, w)⌝ ∗ a0 ↦ₐ[p0] w)
          -∗ gen_heap_ctx m -∗ ⌜m !m! a = v⌝.
  Proof.
    iIntros (mem0 m p g b e a p' v Hmema HPFp) "Hmem Hm".
    iDestruct (memMap_delete a with "Hmem") as "[H_a Hmem]"; eauto.
    iDestruct (gen_heap_valid_cap with "Hm H_a") as %?; auto.
    by option_locate_mr_once m r.
  Qed.

  Lemma gen_mem_update_inSepM :
    ∀ {Σ : gFunctors} {gen_heapG0 : gen_heapG Addr Word Σ}
      (σ : gmap Addr Word) (mem : PermMem) (l : Addr) (p : Perm) (v' v : Word),
      mem !! l = Some (p,v') → PermFlows (LeastPermUpd v) p →
      gen_heap_ctx σ
      -∗ ([∗ map] a0↦pw ∈ mem, ∃ (p0 : Perm) (w0 : Word),
             ⌜pw = (p0, w0)⌝ ∗ a0 ↦ₐ[p0] w0)
      ==∗ gen_heap_ctx (<[l:=v]> σ)
          ∗ ([∗ map] a0↦pw ∈ <[l:=(p,v)]> mem, ∃ (p0 : Perm) (w0 : Word),
             ⌜pw = (p0, w0)⌝ ∗ a0 ↦ₐ[p0] w0).
  Proof.
    intros.
    rewrite (memMap_delete l) //. iIntros "Hh [Hl Hmap]".
    iMod (gen_heap_update_cap with "Hh Hl") as "[Hh Hl]"; eauto.
    iModIntro.
    iSplitL "Hh"; eauto.
    iApply (memMap_delete l); first by rewrite lookup_insert.
    rewrite delete_insert_delete. iFrame.
  Qed.

  (* ----------------------------------- FAIL RULES ---------------------------------- *)

  Lemma wp_notCorrectPC:
    forall E w,
      ~ isCorrectPC w ->
      {{{ PC ↦ᵣ w }}}
        Instr Executable @ E
        {{{ RET FailedV; PC ↦ᵣ w }}}.
  Proof.
    intros *. intros Hnpc.
    iIntros (ϕ) "HPC Hϕ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /="; destruct σ1 as [r m]; simpl;
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    option_locate_mr m r.
    rewrite -HrPC in Hnpc.
    iApply fupd_frame_l.
    iSplit. by iPureIntro; apply normal_always_head_reducible.
    iModIntro. iIntros (e1 σ2 efs Hstep).
    apply prim_step_exec_inv in Hstep as (-> & -> & (c & -> & Hstep)).
    eapply step_fail_inv in Hstep as [-> ->]; eauto.
    iNext. iModIntro. iSplitR; auto. iFrame. cbn. by iApply "Hϕ".
  Qed.

  (* Subcases for respecitvely permissions and bounds *)

  Lemma wp_notCorrectPC_perm E pc_p pc_g pc_b pc_e pc_a :
      pc_p ≠ RX ∧ pc_p ≠ RWX ∧ pc_p ≠ RWLX →
      {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)}}}
      Instr Executable @ E
      {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hperm φ) "HPC Hwp".
    iApply (wp_notCorrectPC with "[HPC]");
      [apply not_isCorrectPC_perm;eauto|iFrame|].
    iNext. iIntros "HPC /=".
    by iApply "Hwp".
  Qed.

  Lemma wp_notCorrectPC_range E pc_p pc_g pc_b pc_e pc_a :
       ¬ (pc_b <= pc_a < pc_e)%a →
      {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)}}}
      Instr Executable @ E
      {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hperm φ) "HPC Hwp".
    iApply (wp_notCorrectPC with "[HPC]");
      [apply not_isCorrectPC_bounds;eauto|iFrame|].
    iNext. iIntros "HPC /=".
    by iApply "Hwp".
  Qed.

  (* ----------------------------------- ATOMIC RULES -------------------------------- *)

  Lemma wp_halt E pc_p pc_g pc_b pc_e pc_a w pc_p' :
    decodeInstrW w = Halt →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a) ∗ pc_a ↦ₐ[pc_p'] w }}}
      Instr Executable @ E
    {{{ RET HaltedV; PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a) ∗ pc_a ↦ₐ[pc_p'] w }}}.
  Proof.
    intros Hinstr Hfl Hvpc.
    iIntros (φ) "[Hpc Hpca] Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1 as [r m]; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hpca") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst. naive_solver. }
    iModIntro.
    iSplitR. by iPureIntro; apply normal_always_head_reducible.
    iIntros (e2 σ2 efs Hstep).
    eapply prim_step_exec_inv in Hstep as (-> & -> & (c & -> & Hstep)).
    eapply step_exec_inv in Hstep; eauto. cbn in Hstep. simplify_eq.
    iNext. iModIntro. iSplitR; eauto. iFrame. iApply "Hφ". by iFrame.
  Qed.

  Lemma wp_fail E pc_p pc_g pc_b pc_e pc_a w pc_p' :
    decodeInstrW w = Fail →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a) ∗ pc_a ↦ₐ[pc_p'] w }}}
      Instr Executable @ E
    {{{ RET FailedV; PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a) ∗ pc_a ↦ₐ[pc_p'] w }}}.
  Proof.
    intros Hinstr Hfl Hvpc.
    iIntros (φ) "[Hpc Hpca] Hφ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1 as [r m]; simpl.
    iDestruct "Hσ1" as "[Hr Hm]".
    iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
    iDestruct (@gen_heap_valid_cap with "Hm Hpca") as %?.
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      inversion Hvpc; subst. naive_solver. }
    iModIntro.
    iSplitR. by iPureIntro; apply normal_always_head_reducible.
    iIntros (e2 σ2 efs Hstep).
    eapply prim_step_exec_inv in Hstep as (-> & -> & (c & -> & Hstep)).
    eapply step_exec_inv in Hstep; eauto. cbn in Hstep. simplify_eq.
    iNext. iModIntro. iSplitR; eauto. iFrame. iApply "Hφ". by iFrame.
   Qed.

  (* ----------------------------------- PURE RULES ---------------------------------- *)

  Local Ltac solve_exec_safe := intros; subst; do 3 eexists; econstructor; eauto.
  Local Ltac solve_exec_puredet := simpl; intros; by inv_head_step.
  Local Ltac solve_exec_pure := intros ?; apply nsteps_once, pure_head_step_pure_step;
                                constructor; [solve_exec_safe|]; intros;
                                (match goal with
                                | H : head_step _ _ _ _ _ _ |- _ => inversion H end).

  Global Instance pure_seq_failed :
    PureExec True 1 (Seq (Instr Failed)) (Instr Failed).
  Proof. by solve_exec_pure. Qed.

  Global Instance pure_seq_halted :
    PureExec True 1 (Seq (Instr Halted)) (Instr Halted).
  Proof. by solve_exec_pure. Qed.

  Global Instance pure_seq_done :
    PureExec True 1 (Seq (Instr NextI)) (Seq (Instr Executable)).
  Proof. by solve_exec_pure. Qed.

End cap_lang_rules.

(* Points to predicates for memory *)
Notation "a ↦ₐ [ p ] w" := (∃ cap_γ, MonRefMapsto a cap_γ (w,p))%I
  (at level 20, p at level 50, format "a  ↦ₐ [ p ]  w") : bi_scope.
Notation "a ↦ₐ < p > w" := (mapsto_nO a p w)
    (at level 20, p at level 50, format "a  ↦ₐ < p >  w") : bi_scope.

(* Used to close the failing cases of the ftlr.
  - Hcont is the (iris) name of the closing hypothesis (usually "Hφ")
  - fail_case_name is one constructor of the spec_name,
    indicating the appropriate error case
 *)
Ltac iFailCore fail_case_name :=
      iPureIntro;
      econstructor; eauto;
      eapply fail_case_name ; eauto.

Ltac iFailWP Hcont fail_case_name :=
  by (cbn; iFrame; iApply Hcont; iFrame; iFailCore fail_case_name).

(* ----------------- useful definitions to factor out the wp specs ---------------- *)

(*--- register equality ---*)
  Lemma addr_ne_reg_ne {regs : leibnizO Reg} {r1 r2 : RegName}
        {p0 g0 b0 e0 a0 p g b e a}:
    regs !! r1 = Some (inr (p0, g0, b0, e0, a0))
    → regs !! r2 = Some (inr (p, g, b, e, a))
    → a0 ≠ a → r1 ≠ r2.
  Proof.
    intros Hr1 Hr2 Hne.
    destruct (decide (r1 = r2)); simplify_eq; auto.
  Qed.

(*--- word_of_argument ---*)

Definition word_of_argument (regs: Reg) (a: Z + RegName): option Word :=
  match a with
  | inl n => Some (inl n)
  | inr r => regs !! r
  end.

Lemma word_of_argument_Some_inv (regs: Reg) (arg: Z + RegName) (w:Word) :
  word_of_argument regs arg = Some w →
  ((∃ z, arg = inl z ∧ w = inl z) ∨
   (∃ r, arg = inr r ∧ regs !! r = Some w)).
Proof.
  unfold word_of_argument. intro. repeat case_match; simplify_eq/=; eauto.
Qed.

Lemma word_of_argument_Some_inv' (regs regs': Reg) (arg: Z + RegName) (w:Word) :
  word_of_argument regs arg = Some w →
  regs ⊆ regs' →
  ((∃ z, arg = inl z ∧ w = inl z) ∨
   (∃ r, arg = inr r ∧ regs !! r = Some w ∧ regs' !! r = Some w)).
Proof.
  unfold word_of_argument. intro. repeat case_match; simplify_eq/=; eauto.
  intros HH. unshelve epose proof (lookup_weaken _ _ _ _ _ HH); eauto.
Qed.

(*--- addr_of_argument ---*)

Definition addr_of_argument regs src :=
  match z_of_argument regs src with
  | Some n => z_to_addr n
  | None => None
  end.

Lemma addr_of_argument_Some_inv (regs: Reg) (arg: Z + RegName) (a:Addr) :
  addr_of_argument regs arg = Some a →
  ∃ z, z_to_addr z = Some a ∧
       (arg = inl z ∨ ∃ r, arg = inr r ∧ regs !! r = Some (inl z)).
Proof.
  unfold addr_of_argument, z_of_argument.
  intro. repeat case_match; simplify_eq/=; eauto. eexists. eauto.
Qed.

Lemma addr_of_argument_Some_inv' (regs regs': Reg) (arg: Z + RegName) (a:Addr) :
  addr_of_argument regs arg = Some a →
  regs ⊆ regs' →
  ∃ z, z_to_addr z = Some a ∧
       (arg = inl z ∨ ∃ r, arg = inr r ∧ regs !! r = Some (inl z) ∧ regs' !! r = Some (inl z)).
Proof.
  unfold addr_of_argument, z_of_argument.
  intros ? HH. repeat case_match; simplify_eq/=; eauto. eexists. split; eauto.
  unshelve epose proof (lookup_weaken _ _ _ _ _ HH); eauto.
Qed.

(*--- regs_of ---*)

Definition regs_of_argument (arg: Z + RegName): gset RegName :=
  match arg with
  | inl _ => ∅
  | inr r => {[ r ]}
  end.

Definition regs_of (i: instr): gset RegName :=
  match i with
  | Lea r1 arg => {[ r1 ]} ∪ regs_of_argument arg
  | GetP r1 r2 => {[ r1; r2 ]}
  | GetL r1 r2 => {[ r1; r2 ]}
  | GetB r1 r2 => {[ r1; r2 ]}
  | GetE r1 r2 => {[ r1; r2 ]}
  | GetA r1 r2 => {[ r1; r2 ]}
  | machine_base.Add r arg1 arg2 => {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2
  | Sub r arg1 arg2 => {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2
  | Lt r arg1 arg2 => {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2
  | IsPtr dst src => {[ dst; src ]}
  | Mov r arg => {[ r ]} ∪ regs_of_argument arg
  | Restrict r1 arg => {[ r1 ]} ∪ regs_of_argument arg
  | Subseg r arg1 arg2 => {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2
  | Load r1 r2 => {[ r1; r2 ]}
  | Store r1 arg => {[ r1 ]} ∪ regs_of_argument arg
  | Jnz r1 r2 => {[ r1; r2 ]}
  | LoadU dst src offs => {[ dst; src ]} ∪ regs_of_argument offs
  | StoreU dst offs src => {[ dst ]} ∪ regs_of_argument offs  ∪ regs_of_argument src
  | PromoteU dst => {[ dst ]}
  | _ => ∅
  end.

Lemma indom_regs_incl D (regs regs': Reg) :
  D ⊆ dom (gset RegName) regs →
  regs ⊆ regs' →
  ∀ r, r ∈ D →
       ∃ (w:Word), (regs !! r = Some w) ∧ (regs' !! r = Some w).
Proof.
  intros * HD Hincl rr Hr.
  assert (is_Some (regs !! rr)) as [w Hw].
  { eapply @elem_of_dom with (D := gset RegName). typeclasses eauto.
    eapply elem_of_subseteq; eauto. }
  exists w. split; auto. eapply lookup_weaken; eauto.
Qed.

(*--- incrementPC ---*)

Definition incrementPC (regs: Reg) : option Reg :=
  match regs !! PC with
  | Some (inr ((p, g), b, e, a)) =>
    match (a + 1)%a with
    | Some a' => Some (<[ PC := inr ((p, g), b, e, a') ]> regs)
    | None => None
    end
  | _ => None
  end.

Lemma incrementPC_Some_inv regs regs' :
  incrementPC regs = Some regs' ->
  exists p g b e a a',
    regs !! PC = Some (inr ((p, g), b, e, a)) ∧
    (a + 1)%a = Some a' ∧
    regs' = <[ PC := inr ((p, g), b, e, a') ]> regs.
Proof.
  unfold incrementPC.
  destruct (regs !! PC) as [ [| [ [ [ [? ?] ?] ?] u] ] |];
    try congruence.
  case_eq (u+1)%a; try congruence. intros ? ?. inversion 1.
  do 6 eexists. split; eauto.
Qed.

Lemma incrementPC_None_inv regs pg b e a :
  incrementPC regs = None ->
  regs !! PC = Some (inr (pg, b, e, a)) ->
  (a + 1)%a = None.
Proof.
  unfold incrementPC.
  destruct (regs !! PC) as [ [| [ [ [ [? ?] ?] ?] u] ] |];
    try congruence.
  case_eq (u+1)%a; congruence.
Qed.

Lemma incrementPC_overflow_mono regs regs' :
  incrementPC regs = None →
  is_Some (regs !! PC) →
  regs ⊆ regs' →
  incrementPC regs' = None.
Proof.
  intros Hi HPC Hincl. unfold incrementPC in *. destruct HPC as [c HPC].
  pose proof (lookup_weaken _ _ _ _ HPC Hincl) as HPC'.
  rewrite HPC HPC' in Hi |- *.
  destruct c as [| ((((?&?)&?)&?)&aa)]; first by auto.
  destruct (aa+1)%a; last by auto. congruence.
Qed.

(* todo: instead, define updatePC on top of incrementPC *)
Lemma incrementPC_fail_updatePC regs m :
   incrementPC regs = None ->
   updatePC (regs, m) = (Failed, (regs, m)).
Proof.
   rewrite /incrementPC /updatePC /RegLocate /=.
   destruct (regs !! PC) as [X|]; auto.
   destruct X as [| [[[[? ?] ?] ?] a']]; auto.
   destruct (a' + 1)%a; auto. congruence.
Qed.

Lemma incrementPC_success_updatePC regs m regs' :
  incrementPC regs = Some regs' ->
  ∃ p g b e a a',
    regs !! PC = Some (inr ((p, g, b, e, a))) ∧
    (a + 1)%a = Some a' ∧
    updatePC (regs, m) = (NextI, (<[ PC := inr ((p, g), b, e, a') ]> regs, m)) ∧
    regs' = <[ PC := inr ((p, g), b, e, a') ]> regs.
Proof.
  rewrite /incrementPC /updatePC /update_reg /RegLocate /=.
  destruct (regs !! PC) as [X|] eqn:?; auto; try congruence; [].
  destruct X as [| [[[[? ?] ?] ?] a']] eqn:?; try congruence; [].
  destruct (a' + 1)%a eqn:?; [| congruence]. inversion 1; subst regs'.
  do 6 eexists. repeat split; auto.
Qed.

Lemma updatePC_success_incl m m' regs regs' w :
  regs ⊆ regs' →
  updatePC (regs, m) = (NextI, (<[ PC := w ]> regs, m)) →
  updatePC (regs', m') = (NextI, (<[ PC := w ]> regs', m')).
Proof.
  intros * Hincl Hu. rewrite /updatePC /= in Hu |- *.
  destruct (regs !! PC) as [ w1 |] eqn:Hrr.
  { pose proof (regs_lookup_eq _ _ _ Hrr) as Hrr2. rewrite Hrr2 in Hu.
    pose proof (lookup_weaken _ _ _ _ Hrr Hincl) as ->%regs_lookup_eq.
    destruct w1 as [|((((?&?)&?)&?)&a1)]; simplify_eq.
    destruct (a1 + 1)%a eqn:Ha1; simplify_eq. rewrite /update_reg /=.
    f_equal. f_equal.
    assert (HH: forall (reg1 reg2:Reg), reg1 = reg2 -> reg1 !! PC = reg2 !! PC)
      by (intros * ->; auto).
    apply HH in Hu. rewrite !lookup_insert in Hu. by simplify_eq. }
  { unfold RegLocate in Hu. rewrite Hrr in Hu. inversion Hu. }
Qed.

Lemma updatePC_fail_incl m m' regs regs' :
  is_Some (regs !! PC) →
  regs ⊆ regs' →
  updatePC (regs, m) = (Failed, (regs, m)) →
  updatePC (regs', m') = (Failed, (regs', m')).
Proof.
  intros [w HPC] Hincl Hfail. rewrite /updatePC /RegLocate /= in Hfail |- *.
  rewrite !HPC in Hfail. have -> := lookup_weaken _ _ _ _ HPC Hincl.
  destruct w as [|((((?&?)&?)&?)&a1)]; simplify_eq; auto;[].
  destruct (a1 + 1)%a; simplify_eq; auto.
Qed.

Ltac incrementPC_inv :=
  match goal with
  | H : incrementPC _ = Some _ |- _ =>
    apply incrementPC_Some_inv in H as (?&?&?&?&?&?&?&?&?)
  | H : incrementPC _ = None |- _ =>
    eapply incrementPC_None_inv in H
  end; simplify_eq.

Lemma pair_eq_inv {A B} {y u : A} {z t : B} {x} :
    x = (y, z) -> x = (u, t) ->
    y = u ∧ z = t.
Proof. intros ->. inversion 1. auto. Qed.

(* TODO: integrate into stdpp? *)
Tactic Notation "simplify_pair_eq" :=
  repeat
    lazymatch goal with
    | H1 : ?x = (?y, ?z), H2 : ?x = (?u, ?t) |- _ =>
      assert (y = u ∧ z = t) as [? ?] by (exact (pair_eq_inv H1 H2)); clear H2
    | H1 : (?y, ?z) = ?x, H2 : ?x = (?u, ?t) |- _ =>
      assert (y = u ∧ z = t) as [? ?] by (exact (pair_eq_inv (eq_sym H1) H2)); clear H2
    | H1 : ?x = (?y, ?z), H2 : (?u, ?t) = ?x |- _ =>
      assert (y = u ∧ z = t) as [? ?] by (exact (pair_eq_inv H1 (eq_sym H2))); clear H2
    | H1 : (?y, ?z) = ?x, H2 : (?u, ?t) = ?x |- _ =>
      assert (y = u ∧ z = t) as [? ?] by (exact (pair_eq_inv (eq_sym H1) (eq_sym H2))); clear H2
    | |- _ => progress simplify_eq
    end.

(*----------------------- FIXME TEMPORARY ------------------------------------*)
(* This is a copy-paste from stdpp (fin_maps.v), plus a fix to avoid using
   "rewrite .. by .." that is not available when using ssreflect's rewrite. *)
(* TODO: upstream the fix into stdpp, and remove the code below whenever we
   upgrade to a version of stdpp that includes it *)

Tactic Notation "simpl_map" "by" tactic3(tac) := repeat
  match goal with
  | H : context[ ∅ !! _ ] |- _ => rewrite lookup_empty in H
  | H : context[ (<[_:=_]>_) !! _ ] |- _ =>
    rewrite lookup_insert in H || (rewrite lookup_insert_ne in H; [| by tac])
  | H : context[ (alter _ _ _) !! _] |- _ =>
    rewrite lookup_alter in H || (rewrite lookup_alter_ne in H; [| by tac])
  | H : context[ (delete _ _) !! _] |- _ =>
    rewrite lookup_delete in H || (rewrite lookup_delete_ne in H; [| by tac])
  | H : context[ {[ _ := _ ]} !! _ ] |- _ =>
    rewrite lookup_singleton in H || (rewrite lookup_singleton_ne in H; [| by tac])
  | H : context[ (_ <$> _) !! _ ] |- _ => rewrite lookup_fmap in H
  | H : context[ (omap _ _) !! _ ] |- _ => rewrite lookup_omap in H
  | H : context[ lookup (A:=?A) ?i (?m1 ∪ ?m2) ] |- _ =>
    let x := fresh in evar (x:A);
    let x' := eval unfold x in x in clear x;
    let E := fresh in
    assert ((m1 ∪ m2) !! i = Some x') as E by (clear H; by tac);
    rewrite E in H; clear E
  | |- context[ ∅ !! _ ] => rewrite lookup_empty
  | |- context[ (<[_:=_]>_) !! _ ] =>
    rewrite lookup_insert || (rewrite lookup_insert_ne; [| by tac])
  | |- context[ (alter _ _ _) !! _ ] =>
    rewrite lookup_alter || (rewrite lookup_alter_ne; [| by tac])
  | |- context[ (delete _ _) !! _ ] =>
    rewrite lookup_delete || (rewrite lookup_delete_ne; [| by tac])
  | |- context[ {[ _ := _ ]} !! _ ] =>
    rewrite lookup_singleton || (rewrite lookup_singleton_ne; [| by tac])
  | |- context[ (_ <$> _) !! _ ] => rewrite lookup_fmap
  | |- context[ (omap _ _) !! _ ] => rewrite lookup_omap
  | |- context [ lookup (A:=?A) ?i ?m ] =>
    let x := fresh in evar (x:A);
    let x' := eval unfold x in x in clear x;
    let E := fresh in
    assert (m !! i = Some x') as E by tac;
    rewrite E; clear E
  end.

Tactic Notation "simpl_map" := simpl_map by eauto with simpl_map map_disjoint.

Tactic Notation "simplify_map_eq" "by" tactic3(tac) :=
  decompose_map_disjoint;
  repeat match goal with
  | _ => progress simpl_map by tac
  | _ => progress simplify_eq/=
  | _ => progress simpl_option by tac
  | H : {[ _ := _ ]} !! _ = None |- _ => rewrite lookup_singleton_None in H
  | H : {[ _ := _ ]} !! _ = Some _ |- _ =>
    rewrite lookup_singleton_Some in H; destruct H
  | H1 : ?m1 !! ?i = Some ?x, H2 : ?m2 !! ?i = Some ?y |- _ =>
    let H3 := fresh in
    feed pose proof (lookup_weaken_inv m1 m2 i x y) as H3; [done|by tac|done|];
    clear H2; symmetry in H3
  | H1 : ?m1 !! ?i = Some ?x, H2 : ?m2 !! ?i = None |- _ =>
    let H3 := fresh in
    apply (lookup_weaken _ m2) in H1; [congruence|by tac]
  | H : ?m ∪ _ = ?m ∪ _ |- _ =>
    apply map_union_cancel_l in H; [|by tac|by tac]
  | H : _ ∪ ?m = _ ∪ ?m |- _ =>
    apply map_union_cancel_r in H; [|by tac|by tac]
  | H : {[?i := ?x]} = ∅ |- _ => by destruct (map_non_empty_singleton i x)
  | H : ∅ = {[?i := ?x]} |- _ => by destruct (map_non_empty_singleton i x)
  | H : ?m !! ?i = Some _, H2 : ?m !! ?j = None |- _ =>
     unless (i ≠ j) by done;
     assert (i ≠ j) by (by intros ?; simplify_eq)
  end.
Tactic Notation "simplify_map_eq" "/=" "by" tactic3(tac) :=
  repeat (progress csimpl in * || simplify_map_eq by tac).
Tactic Notation "simplify_map_eq" :=
  simplify_map_eq by eauto with simpl_map map_disjoint.
Tactic Notation "simplify_map_eq" "/=" :=
  simplify_map_eq/= by eauto with simpl_map map_disjoint.
