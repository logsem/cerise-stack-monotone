From cap_machine.ftlr Require Export Jmp Store StoreU. (*Jnz Get AddSubLt IsPtr Lea Load Mov Restrict Subseg LoadU PromoteU. *)
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel region_invariants.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          `{MonRef: MonRefG (leibnizO _) CapR_rtc Σ} {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (leibnizO Word) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma extract_r_ex r (reg : RegName) :
    (∃ w, r !! reg = Some w) →
    ⊢ (([∗ map] r0↦w ∈ r, r0 ↦ᵣ w) → ∃ w, reg ↦ᵣ w).
  Proof.
    intros [w Hw].
    iIntros "Hmap". iExists w.
    iApply (big_sepM_lookup (λ reg' i, reg' ↦ᵣ i)%I r reg w); eauto.
  Qed.

  Lemma extract_r reg (r : RegName) w :
    reg !! r = Some w →
    ⊢ (([∗ map] r0↦w ∈ reg, r0 ↦ᵣ w) →
      (r ↦ᵣ w ∗ (∀ x', r ↦ᵣ x' -∗ [∗ map] k↦y ∈ <[r := x']> reg, k ↦ᵣ y))).
  Proof.
    iIntros (Hw) "Hmap".
    iDestruct (big_sepM_lookup_acc (λ (r : RegName) i, r ↦ᵣ i)%I reg r w) as "Hr"; eauto.
    iSpecialize ("Hr" with "[Hmap]"); eauto. iDestruct "Hr" as "[Hw Hmap]".
    iDestruct (big_sepM_insert_acc (λ (r : RegName) i, r ↦ᵣ i)%I reg r w) as "Hupdate"; eauto.
    iSpecialize ("Hmap" with "[Hw]"); eauto.
    iSpecialize ("Hupdate" with "[Hmap]"); eauto.
  Qed.

  Instance addr_inhabited: Inhabited Addr := populate (A 0%Z eq_refl eq_refl).

  (*TODO: change to region_conditions *)
  Theorem fundamental W r p g b e (a : Addr) :
    ⊢ ((⌜p = RX⌝ ∨ ⌜p = RWX⌝ ∨ ⌜p = RWLX ∧ g = Monotone⌝) →
      ([∗ list] a ∈ (region_addrs b e), ∃ p', ⌜PermFlows p p'⌝ ∗ (read_write_cond a p' interp)
                                             ∧ ⌜if pwl p then region_state_pwl_mono W a else region_state_nwl W a g⌝) →
      interp_expression r W (inr ((p,g),b,e,a))).
  Proof.
    iIntros (Hp) "#Hinv /=".
    iIntros "[[Hfull Hreg] [Hmreg [Hr [Hsts Hown]]]]".
    iSplit; eauto; simpl.
    iRevert (Hp) "Hinv".
    iLöb as "IH" forall (W r p g b e a).
    iIntros (Hp) "#Hinv".
    iDestruct "Hfull" as "%". iDestruct "Hreg" as "#Hreg".
    iApply (wp_bind (fill [SeqCtx])).
    destruct (decide (isCorrectPC (inr ((p,g),b,e,a)))).
    - (* Correct PC *)
      assert ((b <= a)%a ∧ (a < e)%a) as Hbae.
      { eapply in_range_is_correctPC; eauto.
        unfold le_addr; lia. }
      iDestruct (extract_from_region_inv _ _ a with "Hinv") as (p' Hfp) "(Hinva & Hstate_a)"; auto.
      iDestruct "Hstate_a" as %Hstate_a.
      assert (∃ (ρ : region_type), (std W) !! a = Some ρ ∧ ρ ≠ Revoked ∧ (∀ g, ρ ≠ Static g)
                                   ∧ (∀ g, ρ ≠ Monostatic g) ∧ (∀ w, ρ ≠ Uninitialized w))
        as [ρ [Hρ [Hne_rev [Hne_sta [Hne_mono Hne_uninit] ] ] ] ].
      { destruct (pwl p); [rewrite Hstate_a;eexists;eauto|].
        destruct g; [rewrite Hstate_a|destruct Hstate_a as [-> | ->]|destruct Hstate_a as [-> | [-> | ->] ] ];eexists;eauto. }
      iDestruct (region_open W a p' with "[$Hinva $Hr $Hsts]")
        as (w) "(Hr & Hsts & Hstate & Ha & % & Hmono & #Hw) /=";[|apply Hρ|].
      { destruct ρ;auto;[done|by specialize (Hne_sta g0)|by specialize (Hne_mono g0)|by specialize (Hne_uninit w)]. }
      iDestruct ((big_sepM_delete _ _ PC) with "Hmreg") as "[HPC Hmap]";
        first apply (lookup_insert _ _ (inr (p, g, b, e, a))).
      destruct (decodeInstrW w) eqn:Hi. (* proof by cases on each instruction *)
      + (* Jmp *)
        iApply (jmp_case with "[] [] [] [] [Hmono] [] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* Jnz *)
        (* iApply (jnz_case with "[] [] [] [] [Hmono] [] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmap]"); *)
        (*   try iAssumption; eauto. *) admit.
      + (* Mov *)
        (* iApply (mov_case with "[] [] [] [] [Hmono] [] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmap]"); *)
        (*   try iAssumption; eauto. *) admit.
      + (* Load *)
        (* iApply (load_case with "[] [] [] [] [Hmono] [] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmap]"); *)
        (*   try iAssumption; eauto.a *) admit. 
      + (* Store *)
        iApply (store_case with "[] [] [] [] [Hmono] [] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmap]");
          try iAssumption; eauto.
      + (* Lt *)
        (* iApply (add_sub_lt_case with "[] [] [] [] [Hmono] [] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmap]"); *)
        (*   try iAssumption; eauto. *) admit. 
      + (* Add *)
        (* iApply (add_sub_lt_case with "[] [] [] [] [Hmono] [] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmap]"); *)
        (*   try iAssumption; eauto. *) admit. 
      + (* Sub *)
        (* iApply (add_sub_lt_case with "[] [] [] [] [Hmono] [] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmap]"); *)
        (*   try iAssumption; eauto. *) admit. 
      + (* Lea *)
        (* iApply (lea_case with "[] [] [] [] [Hmono] [] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmap]"); *)
        (*   try iAssumption; eauto. *) admit. 
      + (* Restrict *)
        (* iApply (restrict_case with "[] [] [] [] [Hmono] [] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmap]"); *)
        (*   try iAssumption; eauto. *) admit. 
      + (* Subseg *)
        (* iApply (subseg_case with "[] [] [] [] [Hmono] [] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmap]"); *)
        (*   try iAssumption; eauto. *) admit. 
      + (* IsPtr *)
        (* iApply (isptr_case with "[] [] [] [] [Hmono] [] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmap]"); *)
        (*   try iAssumption; eauto. *) admit. 
      + (* GetL *)
        (* iApply (get_case _ _ _ _ _ _ _ _ _ _ _ _ (GetL _ _) with "[] [] [] [] [Hmono] [] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmap]"); *)
        (*   try iAssumption; eauto. *) admit. 
      + (* GetP *)
        (* iApply (get_case _ _ _ _ _ _ _ _ _ _ _ _ (GetP _ _) with "[] [] [] [] [Hmono] [] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmap]"); *)
        (*   try iAssumption; eauto. *) admit. 
      + (* GetB *)
        (* iApply (get_case _ _ _ _ _ _ _ _ _ _ _ _ (GetB _ _) with "[] [] [] [] [Hmono] [] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmap]"); *)
        (*   try iAssumption; eauto. *) admit. 
      + (* GetE *)
        (* iApply (get_case _ _ _ _ _ _ _ _ _ _ _ _ (GetE _ _) with "[] [] [] [] [Hmono] [] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmap]"); *)
        (*   try iAssumption; eauto. *) admit. 
      + (* GetA *)
        (* iApply (get_case _ _ _ _ _ _ _ _ _ _ _ _ (GetA _ _) with "[] [] [] [] [Hmono] [] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmap]"); *)
        (*   try iAssumption; eauto. *) admit. 
      + (* Fail *)
        iApply (wp_fail with "[HPC Ha]"); eauto; iFrame.
        iNext. iIntros "[HPC Ha] /=".
        iApply wp_pure_step_later; auto.
        iApply wp_value.
        iNext. iIntros (Hcontr); inversion Hcontr.
      + (* Halt *)
        iApply (wp_halt with "[HPC Ha]"); eauto; iFrame.
        iNext. iIntros "[HPC Ha] /=".
        iDestruct (region_close _ _ _ _ _ ρ with "[$Hr $Ha $Hstate $Hmono]") as "Hr";[auto|iFrame "#"; auto|].
        { destruct ρ;auto;[|specialize (Hne_sta g0)|specialize (Hne_mono g0)|specialize (Hne_uninit w0)]; contradiction. }
        iApply wp_pure_step_later; auto.
        iApply wp_value.
        iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
        apply lookup_insert. rewrite delete_insert_delete. iFrame.
        rewrite insert_insert. iNext. iIntros (_).
        iExists (<[PC:=inr (p, g, b, e, a)]> r),W. iFrame.
        iAssert (⌜related_sts_priv_world W W⌝)%I as "#Hrefl".
        { iPureIntro. apply related_sts_priv_refl_world. }
        iFrame "#".
        iAssert (∀ r0 : RegName, ⌜is_Some (<[PC:=inr (p, g, b, e, a)]> r !! r0)⌝)%I as "HA".
        { iIntros. destruct (reg_eq_dec PC r0).
          - subst r0; rewrite lookup_insert; eauto.
          - rewrite lookup_insert_ne; auto. }
        iExact "HA".
      + (* LoadU *)
      (* iApply (loadU_case with "[] [] [] [] [Hmono] [] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmap]"); try iAssumption; eauto. *)
        admit. 
      + (* StoreU *)
        iApply (storeU_case with "[] [] [] [] [Hmono] [] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmap]"); try iAssumption; eauto.
      + (* PromoteU *)
    (* iApply (promoteU_case with "[] [] [] [] [Hmono] [] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmap]"); try iAssumption; eauto. *)
        admit. 
   - (* Not correct PC *)
     iDestruct ((big_sepM_delete _ _ PC) with "Hmreg") as "[HPC Hmap]";
       first apply (lookup_insert _ _ (inr (p, g, b, e, a))).
     iApply (wp_notCorrectPC with "HPC"); eauto.
     iNext. iIntros "HPC /=".
     iApply wp_pure_step_later; auto.
     iApply wp_value.
     iNext. iIntros (Hcontr); inversion Hcontr.
     Unshelve. apply _.
     (* Qed. *)
  Admitted. 

  (* the execute condition can be regained using the FTLR on read allowed permissions *)
  Lemma interp_exec_cond W p g b e a :
    p = RX ∨ p = RWX ∨ p = RWLX ->
    interp W (inr (p,g,b,e,a)) -∗ exec_cond W b e g p interp.
  Proof.
    iIntros (Hra) "#Hw".
    iIntros (a0 r W' Hin) "#Hfuture". iModIntro.
    destruct g.
    + iDestruct (interp_monotone_nm_nl with "Hfuture [] Hw") as "Hw'";[auto|].
      iDestruct (readAllowed_implies_region_conditions with "Hw'") as "Hread_cond";[destruct Hra as [-> | [-> | ->] ];auto|].
      iApply fundamental;[|eauto]. destruct Hra as [-> | [-> | ->] ];auto.
      rewrite fixpoint_interp1_eq /=. done.
    + iDestruct (interp_monotone_nm with "Hfuture [] Hw") as "Hw'";[auto|].
      iDestruct (readAllowed_implies_region_conditions with "Hw'") as "Hread_cond";[destruct Hra as [-> | [-> | ->] ];auto|].
      iApply fundamental;[|eauto]. destruct Hra as [-> | [-> | ->] ];auto.
      rewrite fixpoint_interp1_eq /=. done.
    + iDestruct (interp_monotone_a with "[Hfuture] Hw") as "Hw'";[auto|].
      2: iDestruct (readAllowed_implies_region_conditions with "Hw'") as "Hread_cond";[destruct Hra as [-> | [-> | ->] ];auto|].
      2: iApply fundamental;[|eauto];destruct Hra as [-> | [-> | ->] ];auto.
      simpl. destruct Hra as [-> | [-> | ->] ];auto.
  Qed.

  Lemma fundamental_from_interp W p g b e a r :
    p = RX ∨ p = RWX ∨ (p = RWLX ∧ g = Monotone) →
    ⊢ interp W (inr (p, g, b, e, a)) →
      interp_expression r W (inr (p,g,b,e,a)).
  Proof.
    iIntros (Hp) "HV". iApply fundamental; auto.
    rewrite fixpoint_interp1_eq.
    destruct Hp as [-> | [-> | [ -> -> ] ] ]; eauto.
  Qed.

End fundamental.
