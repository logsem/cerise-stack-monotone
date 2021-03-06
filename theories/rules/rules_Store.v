From cap_machine Require Import region_invariants rules_base.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac.

Section cap_lang_rules.
  Context `{memG Σ, regG Σ}.
  Context `{MachineParameters}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : cap_lang.expr.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : cap_lang.val.
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.

  Definition word_of_argument (regs: Reg) (a: Z + RegName) : option Word :=
    match a with
    | inl z => Some (inl z)
    | inr r =>
      match regs !! r with
      | Some w => Some w
      | _ => None
      end
    end.

  Lemma word_of_argument_inr (regs: Reg) (arg: Z + RegName) (c0 : Cap):
    word_of_argument regs arg = Some(inr(c0)) →
    (∃ r : RegName, arg = inr r ∧ regs !! r = Some(inr(c0))).
  Proof.
    intros HStoreV.
    unfold word_of_argument in HStoreV.
    destruct arg.
       - by inversion HStoreV.
       - exists r. destruct (regs !! r) eqn:Hvr0; last by inversion HStoreV.
         split; auto.
  Qed.

  Definition reg_allows_store (regs : Reg) (r : RegName) p g b e a (storev : Word) :=
    regs !! r = Some (inr ((p, g), b, e, a)) ∧
    writeAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true ∧
    (canStore p a storev = true).

  Inductive Store_failure (regs: Reg) (r1 : RegName)(r2 : Z + RegName) (mem : Mem):=
  | Store_fail_const z:
      regs !! r1 = Some(inl z) ->
      Store_failure regs r1 r2 mem
  | Store_fail_bounds p g b e a:
      regs !! r1 = Some(inr ((p, g), b, e, a)) ->
      (writeAllowed p = false ∨ withinBounds ((p, g), b, e, a) = false) →
      Store_failure regs r1 r2 mem
  | Store_fail_invalid_locality p g b e a storev:
      regs !! r1 = Some(inr ((p, g), b, e, a)) ->
      word_of_argument regs r2 = Some storev ->
      canStore p a storev = false ->
      (* isLocalWord storev = true → *)
      (* pwl p = false → *)
      Store_failure regs r1 r2 mem
  | Store_fail_invalid_PC:
      incrementPC (regs) = None ->
      Store_failure regs r1 r2 mem
  .

  Inductive Store_spec
    (regs: Reg) (r1 : RegName) (r2 : Z + RegName)
    (regs': Reg) (mem mem' : Mem) : cap_lang.val → Prop
  :=
  | Store_spec_success p g b e a storev oldv :
    word_of_argument regs r2 = Some storev ->
    reg_allows_store regs r1 p g b e a storev  →
    mem !! a = Some oldv →
    mem' = (<[a := storev]> mem) →
    incrementPC(regs) = Some regs' ->
    Store_spec regs r1 r2 regs' mem mem' NextIV
  | Store_spec_failure :
    Store_failure regs r1 r2 mem ->
    Store_spec regs r1 r2 regs' mem mem' FailedV.


  Definition allow_store_map_or_true (r1 : RegName) (r2 : Z + RegName) (regs : Reg) (mem : Mem):=
    ∃ p g b e a storev,
      read_reg_inr regs r1 p g b e a ∧ word_of_argument regs r2 = Some storev ∧
      if decide (reg_allows_store regs r1 p g b e a storev) then
        ∃ w, mem !! a = Some w
      else True.

  Lemma allow_store_implies_storev:
    ∀ (r1 : RegName)(r2 : Z + RegName) (mem0 : Mem) (r : Reg) (p : Perm) (g : Locality) (b e a : Addr) storev,
      allow_store_map_or_true r1 r2 r mem0
      → r !r! r1 = inr (p, g, b, e, a)
      → word_of_argument r r2 = Some storev
      → writeAllowed p = true
      → withinBounds (p, g, b, e, a) = true
      → (canStore  p a storev = true)
      → ∃ (storev : Word),
          mem0 !! a = Some  storev.
  Proof.
    intros r1 r2 mem0 r p g b e a storev HaStore Hr2v Hwoa Hwa Hwb HLocal.
    unfold allow_store_map_or_true in HaStore.
    destruct HaStore as (?&?&?&?&?&?&[Hrr | Hrl]&Hwo&Hmem).
    - assert (Hrr' := Hrr). option_locate_mr_once m r.
      rewrite Hrr1 in Hr2v; inversion Hr2v; subst.
      case_decide as HAL.
      * auto.
      * unfold reg_allows_store in HAL.
        destruct HAL. rewrite Hwo in Hwoa; inversion Hwoa. auto.
    - destruct Hrl as [z Hrl]. option_locate_mr m r. by congruence.
  Qed.

  Lemma mem_eq_implies_allow_store_map:
    ∀ (regs : Reg)(mem : Mem)(r1 : RegName)(r2 : Z + RegName)(w storev : Word) p g b e a,
      mem = <[a:=w]> ∅
      → regs !! r1 = Some (inr (p,g,b,e,a))
      → word_of_argument regs r2 = Some storev
      → allow_store_map_or_true r1 r2 regs mem.
  Proof.
    intros regs mem r1 r2 w storev p g b e a Hmem Hrr2 Hwoa.
    exists p,g,b,e,a,storev; split.
    - left. by simplify_map_eq.
    - case_decide; last done.
      split; auto. exists w. simplify_map_eq. auto.
  Qed.

  Lemma mem_neq_implies_allow_store_map:
    ∀ (regs : Reg)(mem : Mem)(r1 : RegName)(r2 : Z + RegName)(pc_a : Addr)
      (w w' storev : Word) p g b e a,
      a ≠ pc_a
      → mem = <[pc_a:= w]> (<[a:= w']> ∅)
      → regs !! r1 = Some (inr (p,g,b,e,a))
      → word_of_argument regs r2 = Some storev
      → allow_store_map_or_true r1 r2 regs mem.
  Proof.
    intros regs mem r1 r2 pc_a w w' storev p g b e a H4 Hrr2 Hwoa.
    exists p,g,b,e,a,storev; split.
    - left. by simplify_map_eq.
    - case_decide; last done.
      split; auto. exists w'. simplify_map_eq. split; auto.
  Qed.

  Lemma mem_implies_allow_store_map:
    ∀ (regs : Reg)(mem : Mem)(r1 : RegName)(r2 : Z + RegName)(pc_a : Addr)
      (w w' storev : Word) p g b e a,
      (if (a =? pc_a)%a
       then mem = <[pc_a:= w]> ∅
       else mem = <[pc_a:= w]> (<[a:= w']> ∅))
      → regs !! r1 = Some (inr (p,g,b,e,a))
      → word_of_argument regs r2 = Some storev
      → allow_store_map_or_true r1 r2 regs mem.
  Proof.
    intros regs mem r1 r2 pc_a w w' storev p g b e a H4 Hrr2 Hwoa.
    destruct (a =? pc_a)%a eqn:Heq.
      + apply Z.eqb_eq, z_of_eq in Heq. subst a. eapply mem_eq_implies_allow_store_map; eauto.
      + apply Z.eqb_neq in Heq.  eapply mem_neq_implies_allow_store_map; eauto. congruence.
  Qed.

   Lemma wp_store Ep
     pc_p pc_g pc_b pc_e pc_a
     r1 (r2 : Z + RegName) w mem regs :
   decodeInstrW w = Store r1 r2 →
   isCorrectPC (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
   regs !! PC = Some (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
   regs_of (Store r1 r2) ⊆ dom _ regs →
   mem !! pc_a = Some w →
   allow_store_map_or_true r1 r2 regs mem →

   {{{ (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ regs' mem' retv, RET retv;
       ⌜ Store_spec regs r1 r2 regs' mem mem' retv⌝ ∗
         ([∗ map] a↦w ∈ mem', a ↦ₐ w) ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
   Proof.
     iIntros (Hinstr Hvpc HPC Dregs Hmem_pc HaStore φ) "(>Hmem & >Hmap) Hφ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "[Hr Hm] /=". destruct σ1 as [r m]; simpl.
     iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.

     (* Derive necessary register values in r *)
     pose proof (lookup_weaken _ _ _ _ HPC Hregs).
     specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.
     feed destruct (Hri r1) as [r1v [Hr'1 Hr1]]. by set_solver+.
     pose proof (regs_lookup_eq _ _ _ Hr'1) as Hr''1.
     iDestruct (gen_mem_valid_inSepM pc_a _ _ _ mem _ m with "Hm Hmem") as %Hma; eauto.

     iModIntro.
     iSplitR. by iPureIntro; apply normal_always_head_reducible.
     iNext. iIntros (e2 σ2 efs Hpstep).
     apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
     iSplitR; auto. eapply step_exec_inv in Hstep; eauto.

     option_locate_mr m r.
     cbn in Hstep. rewrite Hrr1 in Hstep.

     (* Now we start splitting on the different cases in the Load spec, and prove them one at a time *)
     destruct r1v as  [| (([[p g] b] & e) & a) ] eqn:Hr1v.
     { (* Failure: r1 is not a capability *)
       assert (c = Failed ∧ σ2 = (r, m)) as (-> & ->)
         by (destruct r2; inversion Hstep; auto).
       iFailWP "Hφ" Store_fail_const.
     }

     destruct (writeAllowed p && withinBounds ((p, g), b, e, a)) eqn:HWA; rewrite HWA in Hstep.
     2 : { (* Failure: r2 is either not within bounds or doesnt allow reading *)
        assert (c = Failed ∧ σ2 = (r, m)) as (-> & ->)
         by (destruct r2; inversion Hstep; auto).
       apply andb_false_iff in HWA.
       iFailWP "Hφ" Store_fail_bounds.
     }
     apply andb_true_iff in HWA; destruct HWA as (Hwa & Hwb).

     destruct (word_of_argument regs r2) as [ storev | ] eqn:HSV.
     2: {
       destruct r2 as [z | r2].
       - cbn in HSV; inversion HSV.
       - destruct (Hri r2) as [r0v [Hr0 _] ]. by set_solver+.
         cbn in HSV. rewrite Hr0 in HSV. inversion HSV.
     }
     assert (word_of_argument r r2 = Some(storev)) as HSVr.
     { destruct r2; cbn in HSV. inversion HSV; by rewrite H3.
       destruct (Hri r0) as [r0v [Hregs0 Hr0] ].  by set_solver+.
       rewrite -Hr0 in Hregs0; rewrite Hregs0 in HSV. exact HSV.
     }

     case_eq (canStore p a storev); intro HcanStore.
     2:{ destruct r2.
         - simpl in HSV; inv HSV. simpl in HcanStore; congruence.
         - assert (c = Failed ∧ σ2 = (r, m)) as (-> & ->).
           { simpl in HSV; inv HSV. rewrite /= in HSVr.
             rewrite /= /RegLocate in Hstep.
             destruct (r !! r0); try congruence. inv HSVr.
             rewrite HcanStore in Hstep. inv Hstep; auto. }
           iFailWP "Hφ" Store_fail_invalid_locality.
     }


     (* destruct (decide (isLocalWord storev = true ∧ pwl p = false)). *)
     (* {  (* Failure: trying to write a local value to a non-WL cap *) *)
     (*        destruct a0 as [HLW Hpwl]. *)
     (*   assert (c = Failed ∧ σ2 = (r, m)) as (-> & ->). *)
     (*  { destruct storev. *)
     (*   - cbv in HLW; by exfalso. *)
     (*   - destruct (word_of_argument_inr _ _ _ HSVr) as (r0 & -> & Hr0s). *)
     (*     destruct (isLocalWord_cap_isLocal _ HLW) as (p' & g' & b' & e' & a' & -> & HIL). *)
     (*     option_locate_mr m r. rewrite /canStore  Hrr0 /= Hpwl in Hstep. *)
     (*     destruct g'; simpl in HIL; try congruence; inversion Hstep; auto. } *)
     (*  iFailWP "Hφ" Store_fail_invalid_locality. *)
     (* } *)

     assert (isLocalWord storev = false ∨ machine_base.pwl p = true) as HLocal.
     { rewrite /canStore in HcanStore. destruct storev; simpl; auto.
       destruct_cap c0. destruct c4; auto.
       eapply andb_true_iff in HcanStore. destruct HcanStore; auto. }
     (* apply (not_and_r) in n0. *)
     (* destruct n0 as [Hlw | Hpwl]. *)
     (* destruct (isLocalWord storev); first by exfalso. by left. *)
     (* destruct (pwl p); last by exfalso. by right. *)
     (* } clear n0. *)

     (* Prove that a is in the memory map now, otherwise we cannot continue *)
     pose proof (allow_store_implies_storev r1 r2 mem regs p g b e a storev) as (oldv & Hmema); auto.

     (* Given this, prove that a is also present in the memory itself *)
     iDestruct (mem_v_implies_m_v mem m  with "Hmem Hm" ) as %Hma ; auto. eauto.

     (* Regardless of whether we increment the PC, the memory will change: destruct on the PC later *)
     assert (updatePC (update_mem (r, m) a storev) = (c, σ2)) as HH.
      { destruct r2.
       - cbv in HSVr; inversion HSVr; subst storev. done.
       - destruct (r !r! r0) eqn:Hr0.
         * destruct (Hri r0) as [r0v [Hregs01 Hr01] ]. by set_solver+.
           assert(is_Some( r !! r0 )) as Hrr0. by exists r0v.
           pose proof (regs_lookup_inl_eq r r0 z Hrr0 Hr0) as Hr0'.
           simpl in HSVr; rewrite Hr0' in HSVr.
           inversion HSVr; subst storev. done.
         * destruct_cap c0.
           epose proof (regs_lookup_inr_eq r r0 _ _ _ _ _ Hr0) as Hr0'.
           simpl in HSVr; rewrite Hr0' in HSVr; inversion HSVr.
           subst storev; clear HSVr.
           rewrite HcanStore /= in Hstep.
           auto.
       }
      iMod ((gen_mem_update_inSepM _ _ a) with "Hm Hmem") as "[Hm Hmem]"; eauto.

      destruct (incrementPC regs ) as [ regs' |] eqn:Hregs'.
      2: { (* Failure: the PC could not be incremented correctly *)
        assert (incrementPC r = None).
        { eapply incrementPC_overflow_mono; first eapply Hregs'; eauto. }
        rewrite incrementPC_fail_updatePC /= in HH; auto.
        inversion HH.
        iFailWP "Hφ" Store_fail_invalid_PC.
      }

     (* Success *)
      clear Hstep. rewrite /update_mem /= in HH.
      eapply (incrementPC_success_updatePC _ (<[a:=storev]> m)) in Hregs'
        as (p1 & g1 & b1 & e1 & a1 & a_pc1 & HPC'' & Ha_pc' & HuPC & -> & X).
      eapply (updatePC_success_incl _ (<[a:=storev]> m)) in HuPC. 2: by eauto.
      rewrite HuPC in HH; clear HuPC; inversion HH; clear HH; subst c σ2. cbn.

      iFrame.
      iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      iFrame. iModIntro. iApply "Hφ". iFrame.
      iPureIntro. eapply Store_spec_success; eauto.
        * split; auto. exact Hr'1. all: auto.
        * unfold incrementPC. rewrite HPC'' Ha_pc'.
          destruct X as [? [? [? [? ?]]]]; destruct p1; auto; congruence.
      Unshelve. all: auto.
   Qed.

  Lemma wp_store_success_z_PC E pc_p pc_g pc_b pc_e pc_a pc_a' w z :
     decodeInstrW w = Store PC (inl z) →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ w }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
              ∗ pc_a ↦ₐ (inl z) }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Hwa φ)
            "(>HPC & >Hi) Hφ".
    iDestruct (map_of_regs_1 with "HPC") as "Hmap".
    iDestruct (memMap_resource_1 with "Hi") as "Hmem".

    iApply (wp_store with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_eq_implies_allow_store_map; eauto. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ".
       destruct H3 as [Hrr2 _]. simplify_map_eq.
       rewrite memMap_resource_1.
       incrementPC_inv.
       simplify_map_eq.
       rewrite !insert_insert.
       iDestruct (regs_of_map_1 with "[$Hmap]") as "HPC"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto.
       apply isCorrectPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [_ Hwb].
       destruct o; last apply Is_true_false in H2. all:try congruence.
       destruct e; try congruence.
       inv Hvpc. destruct H2 as [? | [? | [? | [? | ?]]]]; destruct H9 as [? | [? | ?]]; congruence.
     }
   Qed.

   (* Lemma wp_store_success_reg_PC E src wsrc pc_p pc_p' pc_g pc_b pc_e pc_a pc_a' w : *)
   (*   decodeInstrW w = Store PC (inr src) → *)
   (*   PermFlows pc_p pc_p' → *)
   (*   isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) → *)
   (*   (pc_a + 1)%a = Some pc_a' → *)
   (*   writeAllowed pc_p = true → *)
   (*   (isLocalWord wsrc = false ∨ (pc_p = RWL ∨ pc_p = RWLX)) -> *)

   (*   {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a) *)
   (*         ∗ ▷ pc_a ↦ₐ[pc_p'] w *)
   (*         ∗ ▷ src ↦ᵣ wsrc }}} *)
   (*     Instr Executable @ E *)
   (*     {{{ RET NextIV; *)
   (*         PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a') *)
   (*            ∗ pc_a ↦ₐ[pc_p'] wsrc *)
   (*            ∗ src ↦ᵣ wsrc }}}. *)
   (* Proof. *)
   (*   iIntros (Hinstr Hfl Hvpc Hpca' Hwa Hloc φ) *)
   (*          "(>HPC & >Hi & >Hsrc) Hφ". *)
   (*   iDestruct (map_of_regs_2 with "HPC Hsrc") as "[Hmap %]". *)
   (*   iDestruct (memMap_resource_1 with "Hi") as "Hmem". *)

   (*  iApply (wp_store with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto. *)
   (*  { by rewrite !dom_insert; set_solver+. } *)
   (*  { eapply mem_eq_implies_allow_store_map; eauto. *)
   (*    all: by simplify_map_eq. } *)
   (*  iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)". *)
   (*  iDestruct "Hspec" as %Hspec. *)

   (*  destruct Hspec as [ | * Hfail ]. *)
   (*   { (* Success *) *)
   (*     iApply "Hφ". *)
   (*     destruct H4 as [Hrr2 _]. simplify_map_eq. *)
   (*     rewrite memMap_resource_1. *)
   (*     incrementPC_inv. *)
   (*     simplify_map_eq. *)
   (*     do 2 rewrite insert_insert. *)
   (*     iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto. iFrame. } *)
   (*   { (* Failure (contradiction) *) *)
   (*     destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. *)
   (*     - apply isCorrectPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [_ Hwb]. *)
   (*       destruct o; last apply Is_true_false in H3; congruence. *)
   (*     - destruct Hloc; first congruence. naive_solver. *)
   (*     - congruence. *)
   (*   } *)
   (*  Qed. *)

   (* Lemma wp_store_success_reg_PC_same E pc_p pc_g pc_b pc_e pc_a pc_a' w w' pc_p' : *)
   (*   decodeInstrW w = Store PC (inr PC) → *)
   (*   PermFlows pc_p pc_p' → *)
   (*   isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) → *)
   (*   (pc_a + 1)%a = Some pc_a' → *)
   (*   writeAllowed pc_p = true → *)
   (*   (isLocal pc_g = false ∨ (pc_p = RWLX ∨ pc_p = RWL)) → *)

   (*   {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a) *)
   (*         ∗ ▷ pc_a ↦ₐ[pc_p'] w }}} *)
   (*     Instr Executable @ E *)
   (*     {{{ RET NextIV; *)
   (*         PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a') *)
   (*            ∗ pc_a ↦ₐ[pc_p'] inr ((pc_p,pc_g),pc_b,pc_e,pc_a) }}}. *)
   (* Proof. *)
   (*   iIntros (Hinstr Hfl Hvpc Hpca' Hwa Hloc φ) *)
   (*          "(>HPC & >Hi) Hφ". *)
   (*   iDestruct (map_of_regs_1 with "HPC") as "Hmap". *)
   (*   iDestruct (memMap_resource_1 with "Hi") as "Hmem". *)

   (*  iApply (wp_store with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto. *)
   (*  { by rewrite !dom_insert; set_solver+. } *)
   (*  { eapply mem_eq_implies_allow_store_map; eauto. *)
   (*    all: by simplify_map_eq. } *)
   (*  iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)". *)
   (*  iDestruct "Hspec" as %Hspec. *)

   (*  destruct Hspec as [ | * Hfail ]. *)
   (*   { (* Success *) *)
   (*     iApply "Hφ". *)
   (*     destruct H3 as [Hrr2 _]. simplify_map_eq. *)
   (*     rewrite memMap_resource_1. *)
   (*     incrementPC_inv. *)
   (*     simplify_map_eq. *)
   (*     do 2 rewrite insert_insert. *)
   (*     iDestruct (regs_of_map_1 with "[$Hmap]") as "HPC"; eauto. iFrame. } *)
   (*   { (* Failure (contradiction) *) *)
   (*     destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. destruct o . all: try congruence. *)
   (*     - apply isCorrectPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [_ Hwb]. *)
   (*       apply Is_true_false in H2; congruence. *)
   (*     - destruct Hloc; first congruence. naive_solver. *)
   (*   } *)
   (*  Qed. *)

   Lemma wp_store_success_same E pc_p pc_g pc_b pc_e pc_a pc_a' w dst z w'
         p g b e :
     decodeInstrW w = Store dst (inl z) →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true ∧ withinBounds ((p, g), b, e, pc_a) = true →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,pc_a) }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
              ∗ pc_a ↦ₐ (inl z)
              ∗ dst ↦ᵣ inr ((p,g),b,e,pc_a) }}}.
    Proof.
     iIntros (Hinstr Hvpc Hpca' [Hwa Hwb] φ)
            "(>HPC & >Hi & >Hdst) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
     iDestruct (memMap_resource_1 with "Hi") as "Hmem".

    iApply (wp_store _ pc_p with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_eq_implies_allow_store_map; eauto.
      all: by simplify_map_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ".
       destruct H4 as [Hrr2 _]. simplify_map_eq.
       rewrite memMap_resource_1.
       incrementPC_inv.
       simplify_map_eq.
       do 2 rewrite insert_insert.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto.
       destruct o. all: try congruence.
       destruct e0; try congruence.
       inv Hvpc. destruct H3 as [? | [? | [? | [? | ?]]]]; destruct H10 as [? | [? | ?]]; congruence.
     }
    Qed.

   (* Lemma wp_store_success_reg' E pc_p pc_g pc_b pc_e pc_a pc_a' w dst w' *)
   (*       p g b e a pc_p' p' : *)
   (*    decodeInstrW w = Store dst (inr PC) → *)
   (*    PermFlows pc_p pc_p' → *)
   (*   isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) → *)
   (*   (pc_a + 1)%a = Some pc_a' → *)
   (*   writeAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true → *)
   (*   (isLocal pc_g = false ∨ (p = RWLX ∨ p = RWL)) → *)

   (*   {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a) *)
   (*         ∗ ▷ pc_a ↦ₐ[pc_p'] w *)
   (*         ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,a) *)
   (*         ∗ if (a =? pc_a)%a *)
   (*           then ⌜PermFlows p pc_p'⌝ *)
   (*           else ⌜PermFlows p p'⌝ ∗ ▷ a ↦ₐ[p'] w' }}} *)
   (*     Instr Executable @ E *)
   (*     {{{ RET NextIV; *)
   (*         PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a') *)
   (*            ∗ pc_a ↦ₐ[pc_p'] (if (a =? pc_a)%a *)
   (*                             then (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) *)
   (*                             else w) *)
   (*            ∗ dst ↦ᵣ inr ((p,g),b,e,a) *)
   (*            ∗ if (a =? pc_a)%a *)
   (*              then emp *)
   (*              else a ↦ₐ[p'] (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) }}}. *)
   (* Proof. *)
   (*   iIntros (Hinstr Hfl Hvpc Hpca' [Hwa Hwb] Hloc φ) *)
   (*          "(>HPC & >Hi & >Hdst & Ha) Hφ". *)
   (*   iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]". *)
   (*   iDestruct (extract_sep_if_split with "Ha") as "[Hflt Hr1a]". *)
   (*   iAssert (⌜if (a =? pc_a)%a then PermFlows p pc_p' else PermFlows p p'⌝)%I with "[Hflt]" as %Hfl'. *)
   (*   { iRevert "Hflt". destruct (a =? pc_a)%a; auto. } *)
   (*   iDestruct (memMap_resource_2gen_clater with "Hi Hr1a") as (mem) "[>Hmem %]". *)

   (*  iApply (wp_store with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto. *)
   (*  { by rewrite !dom_insert; set_solver+. } *)
   (*  { destruct (a =? pc_a)%a; by simplify_map_eq. } *)
   (*  { eapply mem_implies_allow_store_map; eauto. all: by simplify_map_eq. } *)

   (*  iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)". *)
   (*  iDestruct "Hspec" as %Hspec. *)

   (*  destruct Hspec as [ | * Hfail ]. *)
   (*   { (* Success *) *)
   (*     iApply "Hφ". *)
   (*     destruct H5 as [Hrr2 _]. simplify_map_eq. *)
   (*     destruct (a0 =? pc_a)%a eqn:Heq; subst mem. *)
   (*     -  apply Z.eqb_eq, z_of_eq in Heq. subst a0. *)
   (*        rewrite insert_insert. *)
   (*        rewrite memMap_resource_1. *)
   (*        incrementPC_inv. *)
   (*        simplify_map_eq. rewrite insert_insert. *)
   (*        iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto. iFrame. *)

   (*     - apply Z.eqb_neq in Heq. *)
   (*       rewrite insert_commute; last congruence. rewrite insert_insert. *)
   (*       iDestruct (memMap_resource_2ne with "Hmem") as "[Ha0 Hpc_a]"; first congruence. *)
   (*       incrementPC_inv. *)
   (*       rewrite lookup_insert_ne in H6; last congruence. simplify_map_eq. rewrite insert_insert. *)
   (*       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto. iFrame. *)
   (*   } *)
   (*   { (* Failure (contradiction) *) *)
   (*     destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. *)
   (*     destruct o. all: try congruence. *)
   (*     destruct Hloc; first congruence. naive_solver. *)
   (*   } *)
   (*   Qed. *)

   (* Lemma wp_store_success_reg_same' E pc_p pc_g pc_b pc_e pc_a pc_a' w dst *)
   (*       p g b e pc_p' : *)
   (*   decodeInstrW w = Store dst (inr dst) → *)
   (*   PermFlows pc_p pc_p' → *)
   (*   PermFlows p pc_p' → *)
   (*   isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) → *)
   (*   (pc_a + 1)%a = Some pc_a' → *)
   (*   writeAllowed p = true ∧ withinBounds ((p, g), b, e, pc_a) = true → *)
   (*   (isLocal g = false ∨ (p = RWLX ∨ p = RWL)) → *)

   (*   {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a) *)
   (*         ∗ ▷ pc_a ↦ₐ[pc_p'] w *)
   (*         ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,pc_a) }}} *)
   (*     Instr Executable @ E *)
   (*     {{{ RET NextIV; *)
   (*         PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a') *)
   (*            ∗ pc_a ↦ₐ[pc_p'] inr (p, g, b, e, pc_a) *)
   (*            ∗ dst ↦ᵣ inr ((p,g),b,e,pc_a) }}}. *)
   (* Proof. *)
   (*   iIntros (Hinstr Hfl Hfl' Hvpc Hpca' [Hwa Hwb] Hloc φ) *)
   (*          "(>HPC & >Hi & >Hdst) Hφ". *)
   (*   iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]". *)
   (*   iDestruct (memMap_resource_1 with "Hi") as "Hmem". *)

   (*  iApply (wp_store _ pc_p with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto. *)
   (*  { by rewrite !dom_insert; set_solver+. } *)
   (*  { eapply mem_eq_implies_allow_store_map; eauto. *)
   (*    all: by simplify_map_eq. } *)
   (*  iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)". *)
   (*  iDestruct "Hspec" as %Hspec. *)

   (*  destruct Hspec as [ | * Hfail ]. *)
   (*   { (* Success *) *)
   (*     iApply "Hφ". *)
   (*     destruct H4 as [Hrr2 _]. simplify_map_eq. *)
   (*     rewrite memMap_resource_1. *)
   (*     incrementPC_inv. *)
   (*     simplify_map_eq. *)
   (*     do 2 rewrite insert_insert. *)
   (*     iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto. iFrame. } *)
   (*   { (* Failure (contradiction) *) *)
   (*     destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. *)
   (*     destruct o. all: try congruence. *)
   (*     destruct Hloc; first congruence. naive_solver. *)
   (*   } *)
   (* Qed. *)

   (* Lemma wp_store_success_reg_same_a E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src *)
   (*       p g b e pc_p' w'' : *)
   (*    decodeInstrW w = Store dst (inr src) → *)
   (*    PermFlows pc_p pc_p' → *)
   (*    PermFlows p pc_p' → *)
   (*   isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) → *)
   (*   (pc_a + 1)%a = Some pc_a' → *)
   (*   writeAllowed p = true ∧ withinBounds ((p, g), b, e, pc_a) = true → *)
   (*   (isLocalWord w'' = false ∨ (p = RWLX ∨ p = RWL)) → *)

   (*   {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a) *)
   (*         ∗ ▷ pc_a ↦ₐ[pc_p'] w *)
   (*         ∗ ▷ src ↦ᵣ w'' *)
   (*         ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,pc_a) }}} *)
   (*     Instr Executable @ E *)
   (*     {{{ RET NextIV; *)
   (*         PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a') *)
   (*            ∗ pc_a ↦ₐ[pc_p'] w'' *)
   (*            ∗ src ↦ᵣ w'' *)
   (*            ∗ dst ↦ᵣ inr ((p,g),b,e,pc_a)}}}. *)
   (* Proof. *)
   (*   iIntros (Hinstr Hfl Hfl' Hvpc Hpca' [Hwa Hwb] Hloc φ) *)
   (*           "(>HPC & >Hi & >Hsrc & >Hdst) Hφ". *)
   (*   iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]". *)
   (*   iDestruct (memMap_resource_1 with "Hi") as "Hmem". *)

   (*  iApply (wp_store _ pc_p with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto. *)
   (*  { by rewrite !dom_insert; set_solver+. } *)
   (*  { eapply mem_eq_implies_allow_store_map; eauto. *)
   (*    all: by simplify_map_eq. } *)
   (*  iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)". *)
   (*  iDestruct "Hspec" as %Hspec. *)

   (*  destruct Hspec as [ | * Hfail ]. *)
   (*   { (* Success *) *)
   (*     iApply "Hφ". *)
   (*     destruct H6 as [Hrr2 _]. simplify_map_eq. *)
   (*     rewrite memMap_resource_1. *)
   (*     incrementPC_inv. *)
   (*     simplify_map_eq. *)
   (*     do 2 rewrite insert_insert. *)
   (*     iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hsrc Hdst] ]"; eauto. iFrame. } *)
   (*   { (* Failure (contradiction) *) *)
   (*     destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. *)
   (*     destruct o. all: try congruence. *)
   (*     destruct Hloc; first congruence. naive_solver. *)
   (*   } *)
   (* Qed. *)

  (* Lemma wp_store_success_local_reg E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src w' *)
  (*        p g b e a p' g' b' e' a' pc_p' p'' : *)
  (*   decodeInstrW w = Store dst (inr src) → *)
  (*   PermFlows pc_p pc_p' → *)
  (*   PermFlows p p'' → *)
  (*    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) → *)
  (*    (pc_a + 1)%a = Some pc_a' → *)
  (*    writeAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true → *)
  (*    isLocal g' = true ∧ (p = RWLX ∨ p = RWL) → *)

  (*    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a) *)
  (*          ∗ ▷ pc_a ↦ₐ[pc_p'] w *)
  (*          ∗ ▷ src ↦ᵣ inr ((p',g'),b',e',a') *)
  (*          ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,a) *)
  (*          ∗ ▷ a ↦ₐ[p''] w' }}} *)
  (*      Instr Executable @ E *)
  (*      {{{ RET NextIV; *)
  (*          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a') *)
  (*             ∗ pc_a ↦ₐ[pc_p'] w *)
  (*             ∗ src ↦ᵣ inr ((p',g'),b',e',a') *)
  (*             ∗ dst ↦ᵣ inr ((p,g),b,e,a) *)
  (*             ∗ a ↦ₐ[p''] inr ((p',g'),b',e',a') }}}. *)
  (* Proof. *)
  (*   iIntros (Hinstr Hfl Hfl' Hvpc Hpca' [Hwa Hwb] Hloc φ) *)
  (*            "(>HPC & >Hi & >Hsrc & >Hdst & >Hsrca) Hφ". *)
  (*   iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]". *)
  (*   pose proof (writeAllowed_nonO _ _ Hfl' Hwa) as Hp''. *)
  (*   pose proof (correctPC_nonO _ _ _ _ _ _ Hfl Hvpc) as Hpc_p'. *)
  (*   iDestruct (memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto. *)

  (*   iApply (wp_store _ pc_p with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto. *)
  (*   { by rewrite !dom_insert; set_solver+. } *)
  (*   { eapply mem_neq_implies_allow_store_map with (a := a) (p' := p''); eauto. *)
  (*     all: by simplify_map_eq. } *)
  (*   iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)". *)
  (*   iDestruct "Hspec" as %Hspec. *)

  (*   destruct Hspec as [ | * Hfail ]. *)
  (*    { (* Success *) *)
  (*      iApply "Hφ". *)
  (*      destruct H7 as [Hrr2 _]. simplify_map_eq. *)
  (*      rewrite insert_commute // insert_insert. *)
  (*      iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto. *)
  (*      incrementPC_inv. *)
  (*      simplify_map_eq. *)
  (*      rewrite insert_insert. *)
  (*      iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hsrc Hdst] ]"; eauto. iFrame. } *)
  (*    { (* Failure (contradiction) *) *)
  (*      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. *)
  (*      destruct o. all: try congruence. *)
  (*      destruct Hloc as [_ Hpwl]. naive_solver. *)
  (*    } *)
  (* Qed. *)

  (*  Lemma wp_store_success_z_reg E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src w' *)
  (*        p g b e a z pc_p' p' : *)
  (*    decodeInstrW w = Store dst (inr src) → *)
  (*    PermFlows pc_p pc_p' → *)
  (*    PermFlows p p' → *)
  (*    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) → *)
  (*    (pc_a + 1)%a = Some pc_a' → *)
  (*    writeAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true → *)

  (*    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a) *)
  (*          ∗ ▷ pc_a ↦ₐ[pc_p'] w *)
  (*          ∗ ▷ src ↦ᵣ inl z *)
  (*          ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,a) *)
  (*          ∗ ▷ a ↦ₐ[p'] w' }}} *)
  (*      Instr Executable @ E *)
  (*      {{{ RET NextIV; *)
  (*          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a') *)
  (*             ∗ pc_a ↦ₐ[pc_p'] w *)
  (*             ∗ src ↦ᵣ inl z *)
  (*             ∗ dst ↦ᵣ inr ((p,g),b,e,a) *)
  (*             ∗ a ↦ₐ[p'] inl z }}}. *)
  (*  Proof. *)
  (*    iIntros (Hinstr Hfl Hfl' Hvpc Hpca' [Hwa Hwb] φ) *)
  (*            "(>HPC & >Hi & >Hsrc & >Hdst & >Hsrca) Hφ". *)
  (*   iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]". *)
  (*   pose proof (writeAllowed_nonO _ _ Hfl' Hwa) as Hp''. *)
  (*   pose proof (correctPC_nonO _ _ _ _ _ _ Hfl Hvpc) as Hpc_p'. *)
  (*   iDestruct (memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto. *)

  (*   iApply (wp_store _ pc_p with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto. *)
  (*   { by rewrite !dom_insert; set_solver+. } *)
  (*   { eapply mem_neq_implies_allow_store_map with (a := a) (p' := p'); eauto. *)
  (*     all: by simplify_map_eq. } *)
  (*   iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)". *)
  (*   iDestruct "Hspec" as %Hspec. *)

  (*   destruct Hspec as [ | * Hfail ]. *)
  (*    { (* Success *) *)
  (*      iApply "Hφ". *)
  (*      destruct H7 as [Hrr2 _]. simplify_map_eq. *)
  (*      rewrite insert_commute // insert_insert. *)
  (*      iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto. *)
  (*      incrementPC_inv. *)
  (*      simplify_map_eq. *)
  (*      rewrite insert_insert. *)
  (*      iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hsrc Hdst] ]"; eauto. iFrame. } *)
  (*    { (* Failure (contradiction) *) *)
  (*      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. *)
  (*      destruct o. all: congruence. *)
  (*    } *)
  (*  Qed. *)

    Lemma wp_store_success_reg E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src w'
         p g b e a w'' :
      decodeInstrW w = Store dst (inr src) →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true →
     canStore p a w'' = true ->
     (* (isLocalWord w'' = false ∨ (p = RWLX ∨ p = RWL)) → *)

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ src ↦ᵣ w''
           ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,a)
           ∗ ▷ a ↦ₐ w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
              ∗ pc_a ↦ₐ w
              ∗ src ↦ᵣ w''
              ∗ dst ↦ᵣ inr ((p,g),b,e,a)
              ∗ a ↦ₐ w'' }}}.
    Proof.
      iIntros (Hinstr Hvpc Hpca' [Hwa Hwb] Hloc φ)
             "(>HPC & >Hi & >Hsrc & >Hdst & >Hsrca) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iDestruct (memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iApply (wp_store _ pc_p with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_neq_implies_allow_store_map with (a := a); eauto.
      all: by simplify_map_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ".
       destruct H7 as [Hrr2 _]. simplify_map_eq.
       rewrite insert_commute // insert_insert.
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq.
       rewrite insert_insert.
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hsrc Hdst] ]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto.
       destruct o. all: try try congruence.
       destruct e0; try congruence.
       inv Hvpc. destruct H6 as [? | [? | [? | [? | ?]]]]; destruct H13 as [? | [? | ?]]; congruence.
     }
    Qed.

   Lemma wp_store_success_reg_same E pc_p pc_g pc_b pc_e pc_a pc_a' w dst w'
         p g b e a :
     decodeInstrW w = Store dst (inr dst) →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true →
     canStore p a (inr ((p,g),b,e,a)) = true ->
     (* (isLocal g = false ∨ (p = RWLX ∨ p = RWL)) → *)

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,a)
           ∗ ▷ a ↦ₐ w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
              ∗ pc_a ↦ₐ w
              ∗ dst ↦ᵣ inr ((p,g),b,e,a)
              ∗ a ↦ₐ inr ((p,g),b,e,a) }}}.
   Proof.
    iIntros (Hinstr Hvpc Hpca' [Hwa Hwb] Hloc φ)
             "(>HPC & >Hi & >Hdst & >Hsrca) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iApply (wp_store _ pc_p with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_neq_implies_allow_store_map with (a := a); eauto.
      all: by simplify_map_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ".
       destruct H5 as [Hrr2 _]. simplify_map_eq.
       rewrite insert_commute // insert_insert.
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq.
       rewrite insert_insert.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hdst]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto.
       destruct o. all: try congruence.
       destruct e0; try congruence.
       inv Hvpc. destruct H4 as [? | [? | [? | [? | ?]]]]; destruct H11 as [? | [? | ?]]; congruence.
     }
    Qed.

   Lemma wp_store_success_z E pc_p pc_g pc_b pc_e pc_a pc_a' w dst z w'
         p g b e a :
     decodeInstrW w = Store dst (inl z) →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ dst ↦ᵣ inr ((p,g),b,e,a)
           ∗ ▷ a ↦ₐ w' }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
              ∗ pc_a ↦ₐ w
              ∗ dst ↦ᵣ inr ((p,g),b,e,a)
              ∗ a ↦ₐ inl z }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' [Hwa Hwb] φ)
             "(>HPC & >Hi & >Hdst & >Hsrca) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iApply (wp_store _ pc_p with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_neq_implies_allow_store_map with (a := a); eauto.
      all: by simplify_map_eq. }
    iNext. iIntros (regs' mem' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ".
       destruct H5 as [Hrr2 _]. simplify_map_eq.
       rewrite insert_commute // insert_insert.
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq.
       rewrite insert_insert.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hdst]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto.
       destruct o. all: try congruence.
       destruct e0; try congruence.
       inv Hvpc. destruct H4 as [? | [? | [? | [? | ?]]]]; destruct H11 as [? | [? | ?]]; congruence.
     }
   Qed.

 End cap_lang_rules.
