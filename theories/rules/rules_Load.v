From cap_machine Require Import rules_base.
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

  Definition reg_allows_load (regs : Reg) (r : RegName) p g b e a  :=
    regs !! r = Some (inr ((p, g), b, e, a)) ∧
    readAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true.

  Inductive Load_failure (regs: Reg) (r1 r2: RegName) (mem: Mem) :=
  | Load_fail_const z:
      regs !! r2 = Some (inl z) ->
      Load_failure regs r1 r2 mem
  | Load_fail_bounds p g b e a:
      regs !! r2 = Some (inr ((p, g), b, e, a)) ->
      (readAllowed p = false ∨ withinBounds ((p, g), b, e, a) = false) →
      Load_failure regs r1 r2 mem
  (* Notice how the None below also includes all cases where we read an inl value into the PC, because then incrementing it will fail *)
  | Load_fail_invalid_PC p g b e a loadv:
      regs !! r2 = Some (inr ((p, g), b, e, a)) ->
      mem !! a = Some loadv →
      incrementPC (<[ r1 := loadv ]> regs) = None ->
      Load_failure regs r1 r2 mem
  .

  Inductive Load_spec
    (regs: Reg) (r1 r2: RegName)
    (regs': Reg) (mem : Mem) : cap_lang.val → Prop
  :=
  | Load_spec_success p g b e a loadv :
    reg_allows_load regs r2 p g b e a →
    mem !! a = Some loadv →
    incrementPC
      (<[ r1 := loadv ]> regs) = Some regs' ->
    Load_spec regs r1 r2 regs' mem NextIV

  | Load_spec_failure :
    Load_failure regs r1 r2 mem ->
    Load_spec regs r1 r2 regs' mem FailedV.

  Definition allow_load_map_or_true r (regs : Reg) (mem : Mem):=
    ∃ p g b e a, read_reg_inr regs r p g b e a ∧
      if decide (reg_allows_load regs r p g b e a) then
        ∃ w, mem !! a = Some w
      else True.

  Lemma allow_load_implies_loadv:
    ∀ (r2 : RegName) (mem0 : Mem) (r : Reg) (p : Perm) (g : Locality) (b e a : Addr),
      allow_load_map_or_true r2 r mem0
      → r !r! r2 = inr (p, g, b, e, a)
      → readAllowed p = true
      → withinBounds (p, g, b, e, a) = true
      → ∃  (loadv : Word),
          mem0 !! a = Some loadv.
  Proof.
    intros r2 mem0 r p g b e a HaLoad Hr2v Hra Hwb.
    unfold allow_load_map_or_true in HaLoad.
    destruct HaLoad as (?&?&?&?&?&[Hrr | Hrl]&Hmem).
    - assert (Hrr' := Hrr). option_locate_r_once r. rewrite Hrr2 in Hr2v; inversion Hr2v; subst.
      case_decide as HAL.
      * auto.
      * unfold reg_allows_load in HAL.
        destruct HAL; auto.
    - destruct Hrl as [z Hrl]. option_locate_mr m r. by congruence.
  Qed.

  Lemma mem_eq_implies_allow_load_map:
    ∀ (regs : Reg)(mem : Mem)(r2 : RegName) (w : Word) p g b e a,
      mem = <[a:= w]> ∅
      → regs !! r2 = Some (inr (p,g,b,e,a))
      → allow_load_map_or_true r2 regs mem.
  Proof.
    intros regs mem r2 w p g b e a Hmem Hrr2.
    exists p,g,b,e,a; split.
    - left. by simplify_map_eq.
    - case_decide; last done.
      exists  w. simplify_map_eq. auto.
  Qed.

  Lemma mem_neq_implies_allow_load_map:
    ∀ (regs : Reg)(mem : Mem)(r2 : RegName) (pc_a : Addr)
      (w w' : Word) p g b e a,
      a ≠ pc_a
      → mem = <[pc_a:= w]> (<[a:= w']> ∅)
      → regs !! r2 = Some (inr (p,g,b,e,a))
      → allow_load_map_or_true r2 regs mem.
  Proof.
    intros regs mem r2 pc_a w w' p g b e a H4 Hrr2.
    exists p,g,b,e,a; split.
    - left. by simplify_map_eq.
    - case_decide; last done.
      exists w'. simplify_map_eq. split; auto.
  Qed.

  Lemma mem_implies_allow_load_map:
    ∀ (regs : Reg)(mem : Mem)(r2 : RegName) (pc_a : Addr)
      (w w' : Word) p g b e a,
      (if (a =? pc_a)%a
       then mem = <[pc_a:= w]> ∅
       else mem = <[pc_a:= w]> (<[a:= w']> ∅))
      → regs !! r2 = Some (inr (p,g,b,e,a))
      → allow_load_map_or_true r2 regs mem.
  Proof.
    intros regs mem r2 pc_a w w' p g b e a H4 Hrr2.
    destruct (a =? pc_a)%a eqn:Heq.
      + apply Z.eqb_eq, z_of_eq in Heq. subst a. eapply mem_eq_implies_allow_load_map; eauto.
      + apply Z.eqb_neq in Heq.  eapply mem_neq_implies_allow_load_map; eauto. congruence.
  Qed.

  Lemma mem_implies_loadv:
    ∀ (pc_a : Addr) (w w' : Word) (a0 : Addr)
      (mem0 : gmap Addr (Word)) (loadv : Word),
      (if (a0 =? pc_a)%a
       then mem0 = <[pc_a:= w]> ∅
       else mem0 = <[pc_a:= w]> (<[a0:= w']> ∅))→
      mem0 !! a0 = Some loadv →
      loadv = (if (a0 =? pc_a)%a then w else w').
  Proof.
    intros pc_a w w' a0 mem0 loadv H4 H6.
    destruct (a0 =? pc_a)%a eqn:Heq; rewrite H4 in H6.
    + apply Z.eqb_eq, z_of_eq in Heq; subst a0. by simplify_map_eq.
    + apply Z.eqb_neq in Heq. rewrite lookup_insert_ne in H6; last congruence. by simplify_map_eq.
  Qed.

   Lemma wp_load Ep
     pc_p pc_g pc_b pc_e pc_a
     r1 r2 w mem regs :
   decodeInstrW w = Load r1 r2 →
   isCorrectPC (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
   regs !! PC = Some (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
   regs_of (Load r1 r2) ⊆ dom _ regs →
   mem !! pc_a = Some w →
   allow_load_map_or_true r2 regs mem →

   {{{ (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ regs' retv, RET retv;
       ⌜ Load_spec regs r1 r2 regs' mem retv⌝ ∗
         ([∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
   Proof.
     iIntros (Hinstr Hvpc HPC Dregs Hmem_pc HaLoad φ) "(>Hmem & >Hmap) Hφ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "[Hr Hm] /=". destruct σ1 as [r m]; simpl.
     iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.

     (* Derive necessary register values in r *)
     pose proof (lookup_weaken _ _ _ _ HPC Hregs).
     specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.
     feed destruct (Hri r2) as [r2v [Hr'2 Hr2]]. by set_solver+.
     feed destruct (Hri r1) as [r1v [Hr'1 _]]. by set_solver+. clear Hri.
     pose proof (regs_lookup_eq _ _ _ Hr'1) as Hr''1.
     pose proof (regs_lookup_eq _ _ _ Hr'2) as Hr''2.
     (* Derive the PC in memory *)
     iDestruct (gen_mem_valid_inSepM pc_a _ _ _ mem _ m with "Hm Hmem") as %Hma; eauto.

     iModIntro.
     iSplitR. by iPureIntro; apply normal_always_head_reducible.
     iNext. iIntros (e2 σ2 efs Hpstep).
     apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
     iSplitR; auto. eapply step_exec_inv in Hstep; eauto.

     option_locate_mr m r.
     cbn in Hstep. rewrite Hrr2 in Hstep.

     (* Now we start splitting on the different cases in the Load spec, and prove them one at a time *)
     destruct r2v as  [| (([[p g] b] & e) & a) ] eqn:Hr2v.
     { (* Failure: r2 is not a capability *)
       symmetry in Hstep; inversion Hstep; clear Hstep. subst c σ2.
        iFailWP "Hφ" Load_fail_const.
     }

     destruct (readAllowed p && withinBounds ((p, g), b, e, a)) eqn:HRA; rewrite HRA in Hstep.
     2 : { (* Failure: r2 is either not within bounds or doesnt allow reading *)
       symmetry in Hstep; inversion Hstep; clear Hstep. subst c σ2.
       apply andb_false_iff in HRA.
       iFailWP "Hφ" Load_fail_bounds.
     }
     apply andb_true_iff in HRA; destruct HRA as (Hra & Hwb).

     (* Prove that a is in the memory map now, otherwise we cannot continue *)
     pose proof (allow_load_implies_loadv r2 mem regs p g b e a) as (loadv & Hmema); auto.

     iDestruct (mem_v_implies_m_v mem _ _ _ _ loadv with "Hmem Hm" ) as %Hma ; eauto.

     rewrite Hma in Hstep.
     destruct (incrementPC (<[ r1 := loadv ]> regs)) as  [ regs' |] eqn:Hregs'.
     2: { (* Failure: the PC could not be incremented correctly *)
       assert (incrementPC (<[ r1 := loadv]> r) = None).
       { eapply incrementPC_overflow_mono; first eapply Hregs'.
         by rewrite lookup_insert_is_Some'; eauto.
         by apply insert_mono; eauto. }

       rewrite incrementPC_fail_updatePC /= in Hstep; auto.
       symmetry in Hstep; inversion Hstep; clear Hstep. subst c σ2.
       (* Update the heap resource, using the resource for r2 *)
       iMod ((gen_heap_update_inSepM _ _ r1) with "Hr Hmap") as "[Hr Hmap]"; eauto.
       iFailWP "Hφ" Load_fail_invalid_PC.
     }

     (* Success *)
     rewrite /update_reg /= in Hstep.
     eapply (incrementPC_success_updatePC _ m) in Hregs'
       as (p1 & g1 & b1 & e1 & a1 & a_pc1 & HPC'' & Ha_pc' & HuPC & ->).
     eapply updatePC_success_incl in HuPC. 2: by eapply insert_mono.
     rewrite HuPC in Hstep; clear HuPC; inversion Hstep; clear Hstep; subst c σ2. cbn.
     iFrame.
     iMod ((gen_heap_update_inSepM _ _ r1) with "Hr Hmap") as "[Hr Hmap]"; eauto.
     iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
     iFrame. iModIntro. iApply "Hφ". iFrame.
     iPureIntro. eapply Load_spec_success; auto.
       * split; auto. apply (regs_lookup_inr_eq regs r2).
         exact Hr''2.
         auto.
       * exact Hmema.
       * unfold incrementPC. by rewrite HPC'' Ha_pc'.
     Unshelve. all: auto.
   Qed.

   Lemma wp_load_success E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a pc_a' :
    decodeInstrW w = Load r1 r2 →
    isCorrectPC (inr (pc_p,pc_g,pc_b,pc_e,pc_a)) →
    readAllowed p = true ∧ withinBounds (p, g, b, e, a) = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r1 ↦ᵣ w''  
          ∗ ▷ r2 ↦ᵣ inr (p,g,b,e,a)
          ∗ (if (eqb_addr a pc_a) then emp else ▷ a ↦ₐ w') }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,pc_a')
             ∗ r1 ↦ᵣ (if (eqb_addr a pc_a) then w else w')
             ∗ pc_a ↦ₐ w
             ∗ r2 ↦ᵣ inr (p,g,b,e,a)
             ∗ (if (eqb_addr a pc_a) then emp else a ↦ₐ w') }}}. 
  Proof.
    iIntros (Hinstr Hvpc [Hra Hwb] Hpca' φ)
            "(>HPC & >Hi & >Hr1 & >Hr2 & Hr2a) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iDestruct (memMap_resource_2gen_clater _ _ _ _ (λ a w, a ↦ₐ w)%I with "Hi Hr2a") as (mem) "[>Hmem Hmem']".
    iDestruct "Hmem'" as %Hmem.

    iApply (wp_load with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { destruct (a =? pc_a)%a; by simplify_map_eq. }
    { eapply mem_implies_allow_load_map; eauto. by simplify_map_eq. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       (* FIXME: fragile *)
       destruct H5 as [Hrr2 _]. simplify_map_eq.
       iDestruct (memMap_resource_2gen_d with "[Hmem]") as "[Hpc_a Ha]".
       {iExists mem; iSplitL; auto. }
       incrementPC_inv.
       pose proof (mem_implies_loadv _ _ _ _ _ _ Hmem H6) as Hloadv; eauto.
       simplify_map_eq.
       rewrite (insert_commute _ PC r1) // insert_insert (insert_commute _ r1 PC) // insert_insert.
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto.
       iApply "Hφ". iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto.
       destruct o. all: congruence. }
  Qed.

  Lemma wp_load_success_notinstr E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a pc_a' :
    decodeInstrW w = Load r1 r2 →
    isCorrectPC (inr (pc_p,pc_g,pc_b,pc_e,pc_a)) →
    readAllowed p = true ∧ withinBounds (p, g, b, e, a) = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ inr (p,g,b,e,a)
          ∗ ▷ a ↦ₐ w' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,pc_a')
             ∗ r1 ↦ᵣ w'
             ∗ pc_a ↦ₐ w
             ∗ r2 ↦ᵣ inr (p,g,b,e,a)
             ∗ a ↦ₐ w' }}}.
  Proof.
    intros. iIntros "(>HPC & >Hpc_a & >Hr1 & >Hr2 & >Ha)".
    destruct (a =? pc_a)%a eqn:Ha.
    { rewrite (_: a = pc_a); cycle 1.
      { unfold eqb_addr in Ha. apply Z.eqb_eq in Ha. solve_addr. }
      by iDestruct (addr_dupl_false with "Ha Hpc_a") as "?". }
    iIntros "Hφ". iApply (wp_load_success with "[$HPC $Hpc_a $Hr1 $Hr2 Ha]"); eauto.
    rewrite Ha. iFrame. iNext. iIntros "(? & ? & ? & ? & ?)". rewrite Ha.
    iApply "Hφ". iFrame.
  Qed.

  Lemma wp_load_success_frominstr E r1 r2 pc_p pc_g pc_b pc_e pc_a w w'' p g b e pc_a' :
    decodeInstrW w = Load r1 r2 →
    isCorrectPC (inr (pc_p,pc_g,pc_b,pc_e,pc_a)) →
    readAllowed p = true ∧ withinBounds (p, g, b, e, pc_a) = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ inr (p,g,b,e,pc_a) }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,pc_a')
             ∗ r1 ↦ᵣ w
             ∗ pc_a ↦ₐ w
             ∗ r2 ↦ᵣ inr (p,g,b,e,pc_a) }}}.
  Proof.
    intros. iIntros "(>HPC & >Hpc_a & >Hr1 & >Hr2)".
    iIntros "Hφ". iApply (wp_load_success with "[$HPC $Hpc_a $Hr1 $Hr2]"); eauto.
    { unfold eqb_addr. rewrite Z.eqb_refl. eauto. }
    iNext. iIntros "(? & ? & ? & ? & ?)". unfold eqb_addr. rewrite Z.eqb_refl.
    iApply "Hφ". iFrame. Unshelve. eauto.
  Qed.

  Lemma wp_load_success_same E r1 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a pc_a' :
    decodeInstrW w = Load r1 r1 →
    isCorrectPC (inr (pc_p,pc_g,pc_b,pc_e,pc_a)) →
    readAllowed p = true →
    withinBounds (p, g, b, e, a) = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ inr (pc_p,pc_g, pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r1 ↦ᵣ inr (p,g,b,e,a)
          ∗ (if (a =? pc_a)%a then emp else ▷ a ↦ₐ w') }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,pc_a')
             ∗ r1 ↦ᵣ (if (a =? pc_a)%a then w else w')
             ∗ pc_a ↦ₐ w
             ∗ (if (a =? pc_a)%a then emp else a ↦ₐ w') }}}. 
  Proof.
    iIntros (Hinstr Hvpc Hra Hwb Hpca' φ)
            "(>HPC & >Hi & >Hr1 & Hr1a) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iDestruct (memMap_resource_2gen_clater _ _ _ _ (λ a w, a ↦ₐ w)%I with "Hi Hr1a") as (mem) "[>Hmem Hmem']".
    iDestruct "Hmem'" as %Hmem.

    iApply (wp_load with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { destruct (a =? pc_a)%a; by simplify_map_eq. }
    { eapply mem_implies_allow_load_map; eauto. by simplify_map_eq. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ".
       destruct H3 as [Hrr2 _]. simplify_map_eq.
       iDestruct (memMap_resource_2gen_d with "[Hmem]") as "[Hpc_a Ha]".
       {iExists mem; iSplitL; auto. }
       incrementPC_inv.
       pose proof (mem_implies_loadv _ _ _ _ _ _ Hmem H4) as Hloadv; eauto.
       simplify_map_eq.
       rewrite (insert_commute _ PC r1) // insert_insert (insert_commute _ r1 PC) // insert_insert.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hr1]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto.
       destruct o. all: congruence. }
    Qed.

  (* If a points to a capability, the load into PC success if its address can be incr *)
  Lemma wp_load_success_PC E r2 pc_p pc_g pc_b pc_e pc_a w
        p g b e a p' g' b' e' a' a'' :
    decodeInstrW w = Load PC r2 →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    readAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true →
    (a' + 1)%a = Some a'' →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r2 ↦ᵣ inr ((p,g),b,e,a)
          ∗ ▷ a ↦ₐ inr ((p',g'),b',e',a') }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((p',g'),b',e',a'')
             ∗ pc_a ↦ₐ w
             ∗ r2 ↦ᵣ inr ((p,g),b,e,a)
             ∗ a ↦ₐ inr ((p',g'),b',e',a') }}}.
  Proof.
    iIntros (Hinstr Hvpc [Hra Hwb] Hpca' φ)
            "(>HPC & >Hi & >Hr2 & >Hr2a) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr2") as "[Hmap %]".
    iDestruct (memMap_resource_2ne_apply with "Hi Hr2a") as "[Hmem %]"; auto.
    iApply (wp_load with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_neq_implies_allow_load_map with (a := a); eauto.
      by simplify_map_eq. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ".
       destruct H4 as [Hrr2 _]. simplify_map_eq.
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq.
       rewrite insert_insert insert_insert.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hr2]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto.
       destruct o. all: congruence. }
  Qed.

  Lemma wp_load_success_fromPC E r1 pc_p pc_g pc_b pc_e pc_a pc_a' w w'' :
    decodeInstrW w = Load r1 PC →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r1 ↦ᵣ w'' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
             ∗ pc_a ↦ₐ w
             ∗ r1 ↦ᵣ w }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' φ)
            "(>HPC & >Hi & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    rewrite memMap_resource_1.
    iApply (wp_load with "[$Hmap $Hi]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_eq_implies_allow_load_map with (a := pc_a); eauto.
      by simplify_map_eq. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ".
       destruct H3 as [Hrr2 _]. simplify_map_eq.
       rewrite -memMap_resource_1.
       incrementPC_inv. simplify_map_eq.
       rewrite insert_commute //= insert_insert insert_insert insert_commute //=.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hr1]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto.
       apply isCorrectPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [Hra Hwb].
       destruct o; apply Is_true_false in H3. all:congruence.
     }
  Qed.

End cap_lang_rules.
