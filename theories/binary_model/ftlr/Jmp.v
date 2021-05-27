From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.binary_model Require Export logrel_binary.
From cap_machine.binary_model Require Import ftlr_base monotone.
From cap_machine.rules Require Import rules_Jmp.
From cap_machine.binary_model.rules_binary Require Import rules_binary_Jmp.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          {nainv: logrel_na_invs Σ} {cfgg : cfgSG Σ}
          `{MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (prodO (leibnizO Word) (leibnizO Word)) -n> iPropO Σ).
  Notation R := (WORLD -n> (prodO (leibnizO Reg) (leibnizO Reg)) -n> iPropO Σ).
  Implicit Types v : (prodO (leibnizO Word) (leibnizO Word)).
  Implicit Types interp : (D).

  Lemma jmp_case (W : WORLD) (r : prodO (leibnizO Reg) (leibnizO Reg)) (p : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (r0 : RegName) (P:D):
    ftlr_instr W r p g b e a w (Jmp r0) ρ P.
  Proof.
    intros Heqregs Hp Hsome i Hbae Hpers Hpwl Hregion Hnotrevoked Hnotmonostatic Hnotuninitialized Hi.
    iIntros "#Hspec #IH #Hinv #Hreg #Hinva #Hrcond #Hwcond Hmono Hw Hsts Hown".
    iIntros "Hr Hstate Ha Ha' HPC Hmap HsPC Hsmap Hj".
    rewrite !delete_insert_delete.
    destruct (reg_eq_dec PC r0).
    * subst r0.
      iApply (wp_jmp_successPC with "[HPC Ha]"); eauto; first iFrame.
      iNext. iIntros "[HPC Ha] /=".
      iApply wp_pure_step_later; auto.
      (* specification steps *)
      iNext.
      iMod (step_jmp_successPC _ [SeqCtx] with "[$Ha' $HsPC $Hspec $Hj]") as "(Hs & HsPC & Ha') /=";eauto.
      iMod (do_step_pure _ [] with "[$Hs]") as "Hs /=";auto.
      (* reconstruct regions *)
      iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
      iDestruct ((big_sepM_delete _ _ PC) with "[HsPC Hsmap]") as "Hsmap /=";
        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
      (* close region *)
      iDestruct (region_close with "[$Hstate $Hr Hw $Ha $Hmono $Ha']") as "Hr"; eauto.
      { destruct ρ;auto;[|specialize (Hnotmonostatic g0)|specialize (Hnotuninitialized p0)];contradiction. }
      (* apply IH *)
      iApply ("IH" $! _ _ _ g _ _ a with "[] [Hmap] [Hsmap] [$Hr] [$Hsts] [$Hown] [$Hs]"); eauto.
      { iSplit;auto. iPureIntro. apply Hsome. }
      destruct p; iFrame.
      destruct Hp as [Hp | [Hp | [Hp Hg] ] ]; congruence.
      rewrite -Heqregs. destruct p; iFrame.
      destruct Hp as [Hp | [Hp | [Hp Hg] ] ]; congruence.
    * specialize Hsome with r0 as Hr0.
      destruct Hr0 as [ [wsrc Hsomesrc] [wsrc' Hsomesrc'] ].
      iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hsrc Hmap]"; eauto.
      rewrite (lookup_delete_ne r.1 PC r0); eauto.
      iDestruct ((big_sepM_delete _ _ r0) with "Hsmap") as "[Hsrc' Hsmap]"; eauto.
      rewrite (lookup_delete_ne r.1 PC r0); eauto.
      iApply (wp_jmp_success with "[$HPC $Ha $Hsrc]"); eauto.
      iNext. iIntros "[HPC [Ha Hsrc]] /=".
      iMod (step_jmp_success _ [SeqCtx] with "[$Ha' $HsPC $Hspec $Hj $Hsrc']")
        as "(Hs & HsPC & Ha' & Hsrc') /=";eauto.
      iMod (do_step_pure _ [] with "[$Hs]") as "Hs /=";auto.
      iApply wp_pure_step_later; auto.
      (* reconstruct regions *)
      iDestruct ((big_sepM_delete _ _ r0) with "[Hsrc Hmap]") as "Hmap /=";
        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
      iDestruct ((big_sepM_delete _ _ r0) with "[Hsrc' Hsmap]") as "Hsmap /=";
        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
      rewrite -delete_insert_ne; auto.
      destruct (updatePcPerm wsrc) eqn:Heq.
      { iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_notCorrectPC with "HPC"); [intro; match goal with H: isCorrectPC (inl _) |- _ => inv H end|].
        iNext. iNext. iIntros "HPC /=".
        iApply wp_pure_step_later; auto. iNext.
        iApply wp_value. iIntros. discriminate. }
      { destruct c,p0,p0,p0.
        destruct p0.
        - iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext. iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto. iNext.
          iApply wp_value. iIntros. discriminate.
        - iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext. iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto. iNext.
          iApply wp_value. iIntros. discriminate.
        - iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext. iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto. iNext.
          iApply wp_value. iIntros. discriminate.
        - iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext. iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto. iNext.
          iApply wp_value. iIntros. discriminate.
        - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
          apply lookup_insert. rewrite delete_insert_delete. iFrame.
          iDestruct ((big_sepM_delete _ _ PC) with "[HsPC Hsmap]") as "Hsmap /=".
          apply lookup_insert. rewrite delete_insert_delete. iFrame.
          rewrite (insert_id r.1 r0); auto.
          iDestruct ("Hreg" $! r0 ltac:(auto)) as "Hwsrc".
          rewrite /RegLocate Hsomesrc.
          assert (r.2 !! r0 = Some wsrc) as Hsrc.
          { rewrite -(lookup_insert_ne _ PC _ (inl 0%Z))// -Heqregs lookup_insert_ne//. }
          rewrite Hsrc.
          destruct wsrc; simpl in Heq; try congruence.
          destruct c,p0,p0,p0,p0; try congruence.
          + inv Heq. rewrite (fixpoint_interp1_eq _ (inr _,inr _)).
            simpl. rewrite /read_write_cond.
            (* iDestruct "Hwsrc" as (q) "[% H1]". *)
            iDestruct (region_close with "[$Hstate $Hr Hw $Ha $Hmono $Ha']") as "Hr"; eauto.
            { destruct ρ;auto;[|specialize (Hnotmonostatic g0)|specialize (Hnotuninitialized p0)];contradiction. }
            iApply ("IH" with "[] [$Hmap] [Hsmap] [$Hr] [$Hsts] [$Hown] [$Hs]"); eauto.
            rewrite -Heqregs. auto.
            rewrite /region_conditions. iSimpl.
            iModIntro. iDestruct "Hwsrc" as "[_ Hwsrc]". iApply (big_sepL_mono with "Hwsrc").
            intros. iIntros "H". iDestruct "H" as (P' Hpers') "(((?&?)&?)&?)".
            iFrame. iExists P';iFrame. auto.
          + inv Heq. rewrite (fixpoint_interp1_eq _ (inr _,inr _)).
            simpl. rewrite /enter_cond.
            rewrite /interp_expr /=.
            iDestruct "Hwsrc" as "#H".
            iAssert (future_world l a1 W W) as "Hfuture".
            { destruct l; iPureIntro.
              - apply related_sts_priv_refl_world.
              - apply related_sts_priv_refl_world.
              - apply related_sts_a_refl_world. }
            iDestruct "H" as "[_ H]".
            iSpecialize ("H" $! _ _ with "Hfuture").
            iDestruct (region_close with "[$Hstate $Hr Hw $Ha $Ha' $Hmono]") as "Hr"; eauto.
            { destruct ρ;auto;[|specialize (Hnotmonostatic g0)|specialize (Hnotuninitialized p0)];contradiction. }
            iNext.
            iDestruct ("H" with "[$Hmap Hsmap $Hr $Hsts $Hown $Hs]") as "[_ HA]"; auto.
            rewrite -Heqregs. iFrame. iSplit;auto.
        - iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext. iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros. discriminate.
        - iNext.
          iDestruct (region_close with "[$Hstate $Hr Hw $Ha $Ha' $Hmono]") as "Hr"; eauto.
          { destruct ρ;auto;[|specialize (Hnotmonostatic g0)|specialize (Hnotuninitialized p0)];contradiction. }
          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
          apply lookup_insert. rewrite delete_insert_delete. iFrame.
          iDestruct ((big_sepM_delete _ _ PC) with "[HsPC Hsmap]") as "Hsmap /=".
          apply lookup_insert. rewrite delete_insert_delete. iFrame.
          rewrite (insert_id r.1 r0); auto.
          assert (r.2 !! r0 = Some wsrc) as Hsrc.
          { rewrite -(lookup_insert_ne _ PC _ (inl 0%Z))// -Heqregs lookup_insert_ne//. }
          destruct wsrc; simpl in Heq; try congruence.
          destruct c,p0,p0,p0,p0; try congruence. inv Heq.
          iDestruct ("Hreg" $! r0 ltac:(auto)) as "Hwsrc".
          rewrite /RegLocate Hsomesrc Hsrc.
          rewrite (fixpoint_interp1_eq _ (inr _,inr _)).
          simpl.
          (* iDestruct "Hwsrc" as (p'') "[% H1]". *)
          iClear "Hinv".
          iApply ("IH" with "[] [Hmap] [Hsmap] [$Hr] [$Hsts] [$Hown] [$Hs]"); iFrame "#"; eauto.
          rewrite -Heqregs;auto. iDestruct "Hwsrc" as "[_ Hwsrc]". auto.
        - iNext.
          iDestruct (region_close with "[$Hstate $Hr Hw $Ha $Ha' $Hmono]") as "Hr"; eauto.
          { destruct ρ;auto;[|specialize (Hnotmonostatic g0)|specialize (Hnotuninitialized p0)];contradiction. }
          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
          apply lookup_insert. rewrite delete_insert_delete. iFrame.
          iDestruct ((big_sepM_delete _ _ PC) with "[HsPC Hsmap]") as "Hsmap /=".
          apply lookup_insert. rewrite delete_insert_delete. iFrame.
          rewrite (insert_id r.1 r0); auto.
          assert (r.2 !! r0 = Some wsrc) as Hsrc.
          { rewrite -(lookup_insert_ne _ PC _ (inl 0%Z))// -Heqregs lookup_insert_ne//. }
          destruct wsrc; simpl in Heq; try congruence.
          destruct c,p0,p0,p0,p0; try congruence. inv Heq.
          iDestruct ("Hreg" $! r0 ltac:(auto)) as "Hwsrc".
          rewrite /RegLocate Hsomesrc Hsrc.
          rewrite (fixpoint_interp1_eq _ (inr _,inr _)).
          simpl. destruct l; auto. (* iDestruct "Hwsrc" as (p'') "[% H1]". *) iClear "Hinv".
          iDestruct "Hwsrc" as "[_ Hwsrc]".
          iApply ("IH" with "[] [Hmap] [Hsmap] [$Hr] [$Hsts] [$Hown] [$Hs]"); iFrame "#"; eauto.
          rewrite -Heqregs;auto.
        - iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext. iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros. discriminate.
        - iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext. iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros. discriminate.
        - iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext. iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros. discriminate.
        - iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext. iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros. discriminate.
      }
      Unshelve. all: auto.
  Qed.

End fundamental.
