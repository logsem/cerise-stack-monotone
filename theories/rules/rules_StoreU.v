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

  Inductive StoreU_failure (regs : Reg) (dst: RegName) (offs src: Z + RegName) :=
  | StoreU_fail_const z:
      regs !! dst = Some (inl z) ->
      StoreU_failure regs dst offs src
  | StoreU_fail_perm1 p g b e a:
      regs !! dst = Some (inr ((p, g), b, e, a)) ->
      isU p = false ->
      StoreU_failure regs dst offs src
  | StoreU_fail_perm2 p g b e a a' w zoffs :
      regs !! dst = Some (inr ((p, g), b, e, a)) ->
      word_of_argument regs src = Some w ->
      z_of_argument regs offs = Some zoffs ->
      verify_access (StoreU_access b e a zoffs) = Some a' ->
      canStoreU p a' w = false ->
      StoreU_failure regs dst offs src
  | StoreU_fail_offs_arg p g b e a w:
      regs !! dst = Some (inr ((p, g), b, e, a)) ->
      word_of_argument regs src = Some w ->
      z_of_argument regs offs = None ->
      StoreU_failure regs dst offs src
  | StoreU_fail_verify_access p g b e a w zoffs:
      regs !! dst = Some (inr ((p, g), b, e, a)) ->
      word_of_argument regs src = Some w ->
      z_of_argument regs offs = Some zoffs ->
      verify_access (StoreU_access b e a zoffs) = None ->
      StoreU_failure regs dst offs src
  | StoreU_fail_incrPC1 p g b e a a' w zoffs:
      regs !! dst = Some (inr ((p, g), b, e, a)) ->
      word_of_argument regs src = Some w ->
      isU p = true ->
      canStoreU p a w = true ->
      z_of_argument regs offs = Some zoffs ->
      verify_access (StoreU_access b e a zoffs) = Some a' ->
      (a + 1)%a = None ->
      StoreU_failure regs dst offs src
  | StoreU_fail_incrPC2 p g b e a w zoffs a'' a':
      regs !! dst = Some (inr ((p, g), b, e, a)) ->
      word_of_argument regs src = Some w ->
      isU p = true ->
      canStoreU p a'' w = true ->
      z_of_argument regs offs = Some zoffs ->
      verify_access (StoreU_access b e a zoffs) = Some a'' ->
      (a'' + 1)%a = Some a' ->
      incrementPC (<[dst := (inr ((p, g), b, e, a'))]> regs) = None ->
      StoreU_failure regs dst offs src
  | StoreU_fail_incrPC3 p g b e a w zoffs a' :
      regs !! dst = Some (inr ((p, g), b, e, a)) ->
      word_of_argument regs src = Some w ->
      isU p = true ->
      canStoreU p a' w = true ->
      z_of_argument regs offs = Some zoffs ->
      verify_access (StoreU_access b e a zoffs) = Some a' ->
      a <> a' ->
      incrementPC regs = None ->
      StoreU_failure regs dst offs src.

  Definition reg_allows_storeU (regs : Reg) (r : RegName) p g b e a a' (storev : Word) :=
    regs !! r = Some (inr ((p, g), b, e, a)) ∧
    isU p = true ∧ (b <= a')%a ∧ (a' <= a)%a ∧ (a < e)%a ∧
    (canStoreU p a' storev = true).

  Inductive StoreU_spec (regs: Reg) (rdst: RegName) (offs rsrc: Z + RegName) (regs': Reg) (mem mem': Mem) : cap_lang.val → Prop :=
  | StoreU_spec_success p g b e a w zoffs a' old:
      (* regs !! rdst = Some (inr ((p, g), b, e, a)) -> *)
      word_of_argument regs rsrc = Some w ->
      (* isU p = true -> *)
      (* canStoreU p a w = true -> *)
      z_of_argument regs offs = Some zoffs →
      (a + zoffs)%a = Some a' →
      reg_allows_storeU regs rdst p g b e a a' w →
      (* verify_access (StoreU_acCAPcess b e a zoffs) = Some a' -> *)
      mem !! a' = Some old ->
      mem' = (<[ a' := w ]> mem) ->
      (if addr_eq_dec a a' then
         match (a + 1)%a with
         | Some a'' => incrementPC (<[ rdst := inr ((p, g), b, e, a'') ]> regs) = Some regs'
         | None => False
         end
       else incrementPC regs = Some regs') ->
      StoreU_spec regs rdst offs rsrc regs' mem mem' NextIV
  | StoreU_spec_failure:
      StoreU_failure regs rdst offs rsrc ->
      StoreU_spec regs rdst offs rsrc regs' mem mem' FailedV.

  Definition allow_storeU_map_or_true (r1 : RegName) (r2 : Z + RegName) (offs : Z + RegName) (regs : Reg) (mem : Mem):=
    ∃ p g b e a storev,
      read_reg_inr regs r1 p g b e a ∧ word_of_argument regs r2 = Some storev ∧
      match z_of_argument regs offs with
      | None => True
      | Some zoffs =>
        match (a + zoffs)%a with
        | Some a' => if decide (reg_allows_storeU regs r1 p g b e a a' storev) then
                      ∃ w, mem !! a' = Some w
                    else True
        | None => True
        end
      end.


  Lemma allow_storeU_map_or_true_match rdst rsrc offs regs mem :
    allow_storeU_map_or_true rdst rsrc offs regs mem →
    ∃ wsr, word_of_argument regs rsrc = Some wsr ∧
    match regs !! rdst with
   | None => True
   | Some (inl _) => True
   | Some (inr (p, g, b, e, a)) =>
       match z_of_argument regs offs with
       | None => True
       | Some zoffs => match verify_access (StoreU_access b e a zoffs) with
                      | None => True
                      | Some a' => if isU p && canStoreU p a' wsr then
                                    match mem !! a' with
                                    | None => False
                                    | Some w => True
                                    end
                                  else True
                      end
       end
    end.
  Proof.
    intros Hallow.
    destruct Hallow as (p & g & b & e & a & storev & Hreg & Hwoa & Hcond).
    exists storev.
    split;auto.
    destruct Hreg as [Hreg | [z Hreg] ];rewrite Hreg;auto.
    destruct (z_of_argument regs offs);auto.
    destruct (verify_access (StoreU_access b e a z)) eqn:Hverify;auto.
    destruct (isU p && canStoreU p a0 storev) eqn:Hstore;[|auto].
    apply verify_access_spec in Hverify as (Haz & Hconds).
    rewrite Haz in Hcond.
    case_decide.
    - destruct Hcond as (w & ->);auto.
    - exfalso. apply H2.
      apply andb_prop in Hstore as [? ?].
      destruct Hconds as (?&?&?). 
      repeat split;auto.
  Qed.

  Lemma wp_storeU Ep
     pc_p pc_g pc_b pc_e pc_a
     rdst rsrc offs w wsrc mem regs :
   decodeInstrW w = StoreU rdst offs rsrc →
   isCorrectPC (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
   regs !! PC = Some (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
   regs_of (StoreU rdst offs rsrc) ⊆ dom _ regs →
   mem !! pc_a = Some w →
   word_of_argument regs rsrc = Some wsrc ->
   match regs !! rdst with
   | None => True
   | Some (inl _) => True
   | Some (inr (p, g, b, e, a)) =>
     match z_of_argument regs offs with
       | None => True
       | Some zoffs => match verify_access (StoreU_access b e a zoffs) with
                      | None => True
                      | Some a' => if isU p && canStoreU p a' wsrc then
                                    match mem !! a' with
                                    | None => False
                                    | Some w => True
                                    end
                                  else True
                      end
       end
   end ->

   {{{ (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ regs' mem' retv, RET retv;
       ⌜ StoreU_spec regs rdst offs rsrc regs' mem mem' retv⌝ ∗
         ([∗ map] a↦w ∈ mem', a ↦ₐ w) ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
   Proof.
     iIntros (Hinstr Hvpc HPC Dregs Hmem_pc Hwsrc HaStore φ) "(>Hmem & >Hmap) Hφ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "[Hr Hm] /=". destruct σ1 as [r m]; simpl.
     iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.

     (* Derive necessary register values in r *)
     pose proof (lookup_weaken _ _ _ _ HPC Hregs).
     specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.
     feed destruct (Hri rdst) as [rdstv [Hrdst' Hrdst'']]. by set_solver+.
     pose proof (regs_lookup_eq _ _ _ Hrdst') as Hrdst'''.
     (* Derive the PC in memory *)
     iDestruct (gen_mem_valid_inSepM pc_a _ _ _ mem _ m with "Hm Hmem") as %Hma; eauto.

     iModIntro.
     iSplitR. by iPureIntro; apply normal_always_head_reducible.
     iNext. iIntros (e2 σ2 efs Hpstep).
     apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
     iSplitR; auto. eapply step_exec_inv in Hstep; eauto.

     rewrite /exec /RegLocate in Hstep. rewrite Hrdst'' in Hstep.
     destruct rdstv as [zdst| [[[[p g] b] e] a] ].
     { inv Hstep. iFailWP "Hφ" StoreU_fail_const. }

     (* destruct (isU p) eqn:HisU; cycle 1. *)
     (* { simpl in Hstep. inv Hstep. iFailWP "Hφ" StoreU_fail_perm1. } *)

     assert (Hwsrc': match rsrc with
                     | inl n => inl n
                     | inr rsrc =>
                       match reg (r, m) !! rsrc with
                       | Some w => w
                       | None => inl 0%Z
                       end
                     end = wsrc).
     { destruct rsrc; simpl in Hwsrc; inv Hwsrc; auto.
       simpl. feed destruct (Hri r0) as [aa [HA HB]]. by set_solver+.
       rewrite HB; congruence. }
     rewrite Hwsrc' in Hstep.

     (* destruct (canStoreU p a wsrc) eqn:HcanStoreU; cycle 1. *)
     (* { simpl in Hstep. inversion Hstep. *)
     (*   iFailWP "Hφ" StoreU_fail_perm2. } *)

     assert (Hzofargeq: z_of_argument r offs = z_of_argument regs offs).
     { rewrite /z_of_argument; destruct offs; auto.
       feed destruct (Hri r0) as [? [?]]. by set_solver+.
       rewrite H3 H4; auto. }
     rewrite Hzofargeq in Hstep.

     Local Opaque verify_access.
     simpl in Hstep. destruct (z_of_argument regs offs) as [zoffs|] eqn:Hoffs; cycle 1.
     { inv Hstep. iFailWP "Hφ" StoreU_fail_offs_arg. }

     destruct (verify_access (StoreU_access b e a zoffs)) as [a'|] eqn:Hverify; cycle 1.
     { inv Hstep. iFailWP "Hφ" StoreU_fail_verify_access. }

     destruct (isU p) eqn:HisU; cycle 1.
     { simpl in Hstep. inv Hstep. iFailWP "Hφ" StoreU_fail_perm1. }

     destruct (canStoreU p a' wsrc) eqn:HcanStoreU; cycle 1.
     { simpl in Hstep. inversion Hstep. iFailWP "Hφ" StoreU_fail_perm2. }

     rewrite Hrdst' HisU Hverify HcanStoreU /= in HaStore.
     destruct (mem !! a') as [wa|]eqn:Ha; try (inv HaStore; fail).

     destruct (addr_eq_dec a a').
     { subst a'. destruct (a + 1)%a as [a'|] eqn:Hap1; cycle 1.
       { inv Hstep. iFailWP "Hφ" StoreU_fail_incrPC1. }

       iMod ((gen_mem_update_inSepM _ _ a) with "Hm Hmem") as "[Hm Hmem]"; eauto.

       destruct (incrementPC (<[rdst:=inr (p, g, b, e, a')]> regs)) eqn:Hincr; cycle 1.
       { assert _ as Hincr' by (eapply (incrementPC_overflow_mono (<[rdst:=_]> regs) (<[rdst:=_]> r) Hincr _ _)).
         rewrite incrementPC_fail_updatePC in Hstep; eauto.
         inv Hstep. simpl.
         iMod ((gen_heap_update_inSepM _ _ rdst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
         iFailWP "Hφ" StoreU_fail_incrPC2. }

       destruct (incrementPC_success_updatePC _ m _ Hincr) as (p1 & g1 & b1 & e1 & a1 & a_pc1 & HPC'' & Ha_pc' & HuPC & ->).
       eapply updatePC_success_incl in HuPC. 2: by eapply insert_mono.
       instantiate (1 := <[a:=wsrc]> m) in HuPC.
       rewrite HuPC in Hstep. inversion Hstep; clear Hstep; subst c σ2. cbn.
       iMod ((gen_heap_update_inSepM _ _ rdst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
       iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
       rewrite <- Hwsrc'. iFrame. iModIntro; iApply "Hφ".
       iFrame. iPureIntro. apply verify_access_spec in Hverify as (? & ? & ? & ?). econstructor; eauto.
       - repeat split;eauto.
       - rewrite Hwsrc'. auto.
       - destruct (addr_eq_dec a a); try congruence.
         rewrite Hap1. auto. }

     iMod ((gen_mem_update_inSepM _ _ a') with "Hm Hmem") as "[Hm Hmem]"; eauto.

     destruct (incrementPC regs) eqn:Hincr; cycle 1.
     { assert _ as Hincr' by (eapply (incrementPC_overflow_mono regs r Hincr _ _)).
       rewrite incrementPC_fail_updatePC in Hstep; eauto.
       inv Hstep. simpl.
       iFailWP "Hφ" StoreU_fail_incrPC3. }

     destruct (incrementPC_success_updatePC regs (<[a':=wsrc]> m) _ Hincr) as (p1 & g1 & b1 & e1 & a1 & a_pc1 & HPC'' & Ha_pc' & HuPC & ->).
     eapply updatePC_success_incl in HuPC; eauto.
     instantiate (1 := <[a':=wsrc]> m) in HuPC.
     rewrite HuPC in Hstep.
     inversion Hstep; clear Hstep; subst c σ2. cbn.
     iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
     rewrite <- Hwsrc'. iFrame. iModIntro; iApply "Hφ".
     iFrame. iPureIntro. apply verify_access_spec in Hverify as (? & ? & ? & ?). econstructor; eauto.
     { repeat split;eauto. }
     { rewrite Hwsrc'. reflexivity. }
     { destruct (addr_eq_dec a a'); try congruence; auto. }

     Unshelve. all: eauto.
     { destruct (reg_eq_dec PC rdst).
       - subst rdst. rewrite lookup_insert. eauto.
       - rewrite lookup_insert_ne; eauto. }
     { eapply insert_mono; eauto. }
   Qed.


  Lemma wp_storeU_alt Ep
     pc_p pc_g pc_b pc_e pc_a
     rdst rsrc offs w mem regs :
   decodeInstrW w = StoreU rdst offs rsrc →
   isCorrectPC (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
   regs !! PC = Some (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
   regs_of (StoreU rdst offs rsrc) ⊆ dom _ regs →
   mem !! pc_a = Some w →
   allow_storeU_map_or_true rdst rsrc offs regs mem  ->

   {{{ (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ regs' mem' retv, RET retv;
       ⌜ StoreU_spec regs rdst offs rsrc regs' mem mem' retv⌝ ∗
         ([∗ map] a↦w ∈ mem', a ↦ₐ w) ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
   Proof.
     iIntros (Hinstr Hvpc HPC Dregs Hmem_pc HaStore φ) "(>Hmem & >Hmap) Hφ".
     apply allow_storeU_map_or_true_match in HaStore as (wsrc & Hwsrc & HaStore).
     iApply (wp_storeU with "[$Hmem $Hmap]");eauto.
   Qed.

End cap_lang_rules.
