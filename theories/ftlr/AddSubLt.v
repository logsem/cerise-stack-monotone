From cap_machine Require Export logrel.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base. 

Section fundamental.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            World: MonRefG (leibnizO _) RelW Σ}.
  Notation D := ((leibnizO Word) -n> iProp Σ).
  Notation R := ((leibnizO Reg) -n> iProp Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types r : (leibnizO Reg). 
  Implicit Types interp : D.
  Notation WORLD_S := (leibnizO ((STS_states * STS_rels) * bool)).
  Implicit Types M : WORLD_S. 

  Lemma RX_Add_Sub_Lt_case:
    ∀ r a g M fs fr b e p' w dst (r1 r2: Z + RegName)
      (H3 : ∀ x : RegName, (λ x0 : RegName, is_Some (r !! x0)) x)
      (i : isCorrectPC (inr (RX, g, b, e, a)))
      (Hbae : (b <= a)%a ∧ (a <= e)%a)
      (Hfp : PermFlows RX p')
      (Hi : cap_lang.decode w = cap_lang.Add dst r1 r2 \/ cap_lang.decode w = Sub dst r1 r2 \/ cap_lang.decode w = Lt dst r1 r2)
      (Heq : fs = M.1.1 ∧ fr = M.1.2),
      □ ▷ (∀ a0 a1 a2 a3 a4 a5 a6 a7,
            full_map a0
         -∗ (∀ r0 : RegName, ⌜r0 ≠ PC⌝ → (fixpoint interp1) (a0 !r! r0))
         -∗ registers_mapsto (<[PC:=inr (RX, a2, a5, a6, a1)]> a0)
         -∗ Exact_w wγ a7
         -∗ sts_full a3 a4
         -∗ na_own logrel_nais ⊤
         -∗ ⌜a7.1.1 = a3⌝
         → ⌜a7.1.2 = a4⌝
         → □ (∃ p : Perm, ⌜PermFlows RX p⌝
                           ∧ ([∗ list] a8 ∈ region_addrs a5 a6, 
                              na_inv logrel_nais (logN.@a8)
                                     (∃ w0 : leibnizO Word, a8 ↦ₐ[p] w0 ∗ ▷ interp w0)))
         -∗ ⟦ [a3, a4] ⟧ₒ)
        -∗ □ ([∗ list] a0 ∈ region_addrs b e, na_inv logrel_nais (logN.@a0)
                    (∃ w0, a0 ↦ₐ[p'] w0 ∗ ▷ interp w0))
        -∗ □ (∀ r0 : RegName, ⌜r0 ≠ PC⌝ → (fixpoint interp1) (r !r! r0))
        -∗ □ na_inv logrel_nais (logN.@a)
              (∃ w0 : leibnizO Word, a ↦ₐ[p'] w0 ∗ ▷ interp w0)
        -∗ □ ▷ ▷ interp w
        -∗ Exact_w wγ M
        -∗ sts_full fs fr
        -∗ a ↦ₐ[p'] w
        -∗ na_own logrel_nais (⊤ ∖ ↑logN.@a)
        -∗ (▷ (∃ w0, a ↦ₐ[p'] w0 ∗ ▷ interp w0)
              ∗ na_own logrel_nais (⊤ ∖ ↑logN.@a)
            ={⊤}=∗ na_own logrel_nais ⊤)
        -∗ PC ↦ᵣ inr (RX, g, b, e, a)
        -∗ ([∗ map] k↦y ∈ delete PC
                    (<[PC:=inr (RX, g, b, e, a)]> r), 
            k ↦ᵣ y)
        -∗ WP Instr Executable
           {{ v, WP fill [SeqCtx] (of_val v)
                    {{ v0, ⌜v0 = HaltedV⌝ → ∃ r0 fs' fr',
                           full_map r0 ∧ registers_mapsto r0
                           ∗ ⌜related_sts_priv fs fs' fr fr'⌝
                           ∗ na_own logrel_nais ⊤
                           ∗ sts_full fs' fr' }} }}.
  Proof.
    intros r a g M fs fr b e p' w. intros.
    iIntros "#IH #Hinv #Hreg #Hinva #Hval". 
    iIntros "HM Hsts Ha Hown Hcls HPC Hmap".
    destruct Heq as [Heq1 Heq2].
    rewrite delete_insert_delete.
    destruct (reg_eq_dec dst PC).
    * subst dst.
      destruct r1; destruct r2.
      { iApply (wp_add_sub_lt_success with "[Ha HPC]"); eauto.
        - destruct (reg_eq_dec PC PC); auto; try congruence. iFrame. eauto.
        - iNext. destruct (reg_eq_dec PC PC); try congruence.
          iIntros "(_ & Ha & _ & _ & HPC)".
          iApply wp_pure_step_later; auto.
          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
          iApply wp_value. iNext. iIntros. congruence. }
      { destruct (reg_eq_dec PC r0).
        - subst r0. iApply (wp_add_sub_lt_PC_fail2 with "[Ha HPC]"); eauto.
          + iFrame.
          + iNext. iIntros "(HPC & Ha)".
            iApply wp_pure_step_later; auto.
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
            iApply wp_value. iNext. iIntros. discriminate a0.
        - destruct (H3 r0) as [wr0 Hsomer0].
          iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
          rewrite lookup_delete_ne; eauto.
          destruct wr0.
          + iApply (wp_add_sub_lt_success with "[Ha HPC Hr0]"); eauto.
            * destruct (reg_eq_dec PC PC); auto; try congruence.
              destruct (reg_eq_dec r0 PC); iFrame; eauto.
            * iNext. destruct (reg_eq_dec PC PC); try congruence.
              destruct (reg_eq_dec r0 PC); try congruence.
              iIntros "(_ & Ha & _ & Hr0 & HPC)".
              iApply wp_pure_step_later; auto.
              iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
              rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
              iApply wp_value. iNext. iIntros. discriminate a0.
          + iApply (wp_add_sub_lt_fail2 with "[Ha HPC Hr0]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha & Hr0)".
            iApply wp_pure_step_later; auto.
            iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
            rewrite -delete_insert_ne; auto.
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
            iApply wp_value. iNext. iIntros. discriminate. }
      { destruct (reg_eq_dec PC r0).
        - subst r0. iApply (wp_add_sub_lt_PC_fail1 with "[Ha HPC]"); eauto.
          + iFrame.
          + iNext. iIntros "(HPC & Ha)".
            iApply wp_pure_step_later; auto.
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
            iApply wp_value. iNext. iIntros. discriminate.
        - destruct (H3 r0) as [wr0 Hsomer0].
          iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
          rewrite lookup_delete_ne; eauto.
          destruct wr0.
          + iApply (wp_add_sub_lt_success with "[Ha HPC Hr0]"); eauto.
            * destruct (reg_eq_dec PC PC); auto; try congruence.
              destruct (reg_eq_dec r0 PC); iFrame; eauto.
            * iNext. destruct (reg_eq_dec PC PC); try congruence.
              destruct (reg_eq_dec r0 PC); try congruence.
              iIntros "(_ & Ha & Hr0 & _ & HPC)".
              iApply wp_pure_step_later; auto.
              iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
              rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
              iApply wp_value. iNext; iIntros; discriminate.
          + iApply (wp_add_sub_lt_fail1 with "[Ha HPC Hr0]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha & Hr0)".
            iApply wp_pure_step_later; auto.
            iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
            rewrite -delete_insert_ne; auto.
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
            iApply wp_value. iNext; iIntros; discriminate. }
      { destruct (reg_eq_dec PC r0).
        - subst r0. iApply (wp_add_sub_lt_PC_fail1 with "[Ha HPC]"); eauto.
          + iFrame.
          + iNext. iIntros "(HPC & Ha)".
            iApply wp_pure_step_later; auto.
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
            iApply wp_value. iNext; iIntros; discriminate.
        - destruct (reg_eq_dec PC r1).
          + subst r1. iApply (wp_add_sub_lt_PC_fail2 with "[Ha HPC]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha)".
            iApply wp_pure_step_later; auto.
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
            iApply wp_value. iNext; iIntros; discriminate.
          + destruct (H3 r0) as [wr0 Hsomer0].
            destruct (H3 r1) as [wr1 Hsomer1].
            iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
            rewrite lookup_delete_ne; eauto.
            destruct (reg_eq_dec r0 r1).
            * subst r1. destruct wr0.
              { iApply (wp_add_sub_lt_success_same with "[Ha HPC Hr0]"); eauto.
                - destruct (reg_eq_dec PC PC); auto; try congruence.
                  destruct (reg_eq_dec r0 PC); iFrame; eauto.
                - iNext. destruct (reg_eq_dec r0 PC); try congruence.
                  destruct (reg_eq_dec PC PC); try congruence.
                  iIntros "(_ & Ha & Hr0 & HPC)".
                  iApply wp_pure_step_later; auto.
                  iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                    [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                  repeat rewrite -delete_insert_ne; auto.
                  iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                    [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                  iApply wp_value. iNext; iIntros; discriminate. } 
              { iApply (wp_add_sub_lt_fail1 with "[Ha HPC Hr0]"); eauto; iFrame.
                iNext. iIntros "(HPC & Ha & Hr0)".
                iApply wp_pure_step_later; auto.
                iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                repeat rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                iApply wp_value. iNext; iIntros; discriminate. } 
            * iDestruct ((big_sepM_delete _ _ r1) with "Hmap") as "[Hr1 Hmap]".
              repeat rewrite lookup_delete_ne; eauto.
              destruct wr0.
              { destruct wr1.
                - iApply (wp_add_sub_lt_success with "[Ha HPC Hr0 Hr1]"); eauto.
                  + destruct (reg_eq_dec PC PC); auto; try congruence.
                    destruct (reg_eq_dec r0 PC); iFrame; eauto.
                    destruct (reg_eq_dec r1 PC); auto.
                  + simpl. destruct (reg_eq_dec r0 PC); try congruence.
                    destruct (reg_eq_dec r1 PC); try congruence.
                    destruct (reg_eq_dec PC PC); try congruence.
                    iNext. iIntros "(_ & Ha & Hr0 & Hr1 & HPC)".
                    iApply wp_pure_step_later; auto.
                    iDestruct ((big_sepM_delete _ _ r1) with "[Hr1 Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    rewrite -delete_insert_ne; auto.
                    iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    repeat rewrite -delete_insert_ne; auto.
                    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    iApply wp_value. iNext; iIntros; discriminate.
                - iApply (wp_add_sub_lt_fail2 with "[Ha HPC Hr1]"); eauto; iFrame.
                  iNext. iIntros "(HPC & Ha & Hr1)".
                  iApply wp_pure_step_later; auto.
                  iDestruct ((big_sepM_delete _ _ r1) with "[Hr1 Hmap]") as "Hmap /=";
                    [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                  rewrite -delete_insert_ne; auto.
                  iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                    [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                  repeat rewrite -delete_insert_ne; auto.
                  iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                    [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                  iApply wp_value. iNext; iIntros; discriminate. }
              { iApply (wp_add_sub_lt_fail1 with "[Ha HPC Hr0]"); eauto; iFrame.
                iNext. iIntros "(HPC & Ha & Hr0)".
                iApply wp_pure_step_later; auto.
                iDestruct ((big_sepM_delete _ _ r1) with "[Hr1 Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                repeat rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                iApply wp_value. iNext; iIntros; discriminate. } }
    * destruct (H3 dst) as [wdst Hsomedst].
      iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]".
      rewrite lookup_delete_ne; eauto.
      destruct r1; destruct r2.
      { iApply (wp_add_sub_lt_success with "[Ha Hdst HPC]"); eauto.
        - destruct (reg_eq_dec dst PC); eauto; iFrame; eauto.
        - iNext. destruct (reg_eq_dec dst PC); try congruence.
          iIntros "(HPC & Ha & _ & _ & Hdst)".
          iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
          rewrite -delete_insert_ne; auto.
          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
          assert (PureExec True 1 (Seq (cap_lang.of_val match (a + 1)%a with | Some _ => NextIV | None => FailedV end)) match (a + 1)%a with | Some _ => Seq (Instr Executable) | None => Instr Failed end).
          { destruct (a+1)%a; auto. apply pure_seq_done. apply pure_seq_failed. }
          iApply (wp_pure_step_later); auto. iNext.
          iAssert ((interp_registers (<[dst:=match cap_lang.decode w with
                                             | Lt _ _ _ => inl (Z.b2z (z <? z0)%Z)
                                             | cap_lang.Add _ _ _ => inl (z + z0)%Z
                                             | Sub _ _ _ => inl (z - z0)%Z
                                             | _ => inl 0%Z
                                             end]> r)))%I
            as "[Hfull' Hreg']".
          { iSplitR.
            - iIntros (r0). 
              destruct (H3 r0) as [c Hsome].
              iPureIntro.
              destruct (decide (dst = r0)); simplify_eq;
                [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
            - iIntros (r0 Hnepc) "/=".
              destruct (H3 r0) as [c Hsome].
              destruct (decide (dst = r0)); simplify_eq.
              + rewrite /RegLocate lookup_insert. repeat rewrite (fixpoint_interp1_eq).
                destruct (cap_lang.decode w); simpl; eauto.
              + rewrite /RegLocate lookup_insert_ne; auto.
                iDestruct ("Hreg" $! (r0)) as "Hv". iApply "Hv". auto. }
          destruct (a+1)%a.
          -- iMod ("Hcls" with "[Hown Ha]") as "Hcls'".
             { iFrame. iNext. iExists w. iFrame. iNext. auto. }
             simpl. 
             iApply ("IH" with "[Hfull'] [Hreg'] [Hmap] [HM] [Hsts] [Hcls']"); eauto.
          -- iApply wp_value. iIntros. discriminate. }
      { destruct (reg_eq_dec PC r0).
        - subst r0. iApply (wp_add_sub_lt_PC_fail2 with "[Ha HPC]"); eauto.
          + iFrame.
          + iNext. iIntros "(HPC & Ha)".
            iApply wp_pure_step_later; auto.
            iApply wp_value. iNext; iIntros; discriminate.
        - destruct (H3 r0) as [wr0 Hsomer0].
          destruct (reg_eq_dec dst r0).
          + subst r0. destruct wdst.
            * iApply (wp_add_sub_lt_success with "[Ha HPC Hdst]"); eauto.
              -- destruct (reg_eq_dec dst PC); eauto; try congruence.
                 iFrame. destruct (reg_eq_dec dst dst); eauto; try congruence.
              -- simpl. iNext. destruct (reg_eq_dec dst PC); try congruence.
                 iIntros "(HPC & Ha & _ & _ & Hdst)".
                 case_eq (a+1)%a; intros.
                 ++ iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    rewrite -delete_insert_ne; auto.
                    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    iApply wp_pure_step_later; auto. iNext.
                    iMod ("Hcls" with "[Hown Ha]") as "Hcls'".
                    { iFrame. iNext. iExists w. iFrame. auto. } 
                    iAssert ((interp_registers (<[dst:=match cap_lang.decode w with
                                                       | Lt _ _ _ => inl (Z.b2z (z <? z0)%Z)
                                                       | cap_lang.Add _ _ _ => inl (z + z0)%Z
                                                       | Sub _ _ _ => inl (z - z0)%Z
                                                       | _ => inl 0%Z
                                                       end]> r)))%I
                      as "[Hfull' Hreg']".
                    { iSplitR.
                      - iIntros (r0). 
                        destruct (H3 r0) as [c Hsome].
                        iPureIntro.
                        destruct (decide (dst = r0)); simplify_eq;
                          [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
                      - iIntros (r0 Hnepc) "/=".
                        destruct (H3 r0) as [c Hsome].
                        destruct (decide (dst = r0)); simplify_eq.
                        + rewrite /RegLocate lookup_insert. repeat rewrite (fixpoint_interp1_eq).
                          destruct (cap_lang.decode w); simpl; eauto.
                        + rewrite /RegLocate lookup_insert_ne; auto.
                          iDestruct ("Hreg" $! (r0)) as "Hv". iApply "Hv". auto. }
                    iApply ("IH" with "[Hfull'] [Hreg'] [Hmap] [HM] [Hsts] [Hcls']"); eauto.
                 ++ iApply wp_pure_step_later; auto.
                    iApply wp_value; eauto. iNext. iIntros. discriminate.
            * iApply (wp_add_sub_lt_fail2 with "[Ha HPC Hdst]"); eauto; iFrame.
              iNext. iIntros "(HPC & Ha & Hdst)". iApply wp_pure_step_later; auto.
              iNext. iApply wp_value. iIntros; discriminate.
          + iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
            repeat rewrite lookup_delete_ne; eauto.
            destruct wr0.
            * iApply (wp_add_sub_lt_success with "[Ha HPC Hdst Hr0]"); eauto.
              -- destruct (reg_eq_dec dst PC); eauto; try congruence.
                 iFrame. destruct (reg_eq_dec r0 dst); eauto; try congruence.
              -- simpl. iNext. destruct (reg_eq_dec dst PC); try congruence.
                 destruct (reg_eq_dec r0 dst); try congruence.
                 iIntros "(HPC & Ha & _ & Hr0 & Hdst)".
                 case_eq (a+1)%a; intros.
                 ++ iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    rewrite -delete_insert_ne; auto.
                    iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    repeat rewrite -delete_insert_ne; auto.
                    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    iApply wp_pure_step_later; auto. iNext.
                    iMod ("Hcls" with "[Hown Ha]") as "Hcls'".
                    { iFrame. iNext. iExists w. iFrame; auto. }
                    iAssert ((interp_registers (<[dst:=match cap_lang.decode w with
                                                       | Lt _ _ _ => inl (Z.b2z (z <? z0)%Z)
                                                       | cap_lang.Add _ _ _ => inl (z + z0)%Z
                                                       | Sub _ _ _ => inl (z - z0)%Z
                                                       | _ => inl 0%Z
                                                       end]> (<[r0:=inl z0]> r))))%I
                      as "[Hfull' Hreg']".
                    { iSplitR.
                      - iIntros (r1).
                        destruct (H3 r1) as [c Hsome].
                        iPureIntro.
                        destruct (decide (dst = r1)); simplify_eq;
                          [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
                        destruct (reg_eq_dec r0 r1); simplify_eq;
                          [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
                      - iIntros (r1 Hnepc) "/=".
                        destruct (H3 r1) as [c Hsome].
                        destruct (decide (dst = r1)); simplify_eq.
                        + rewrite /RegLocate lookup_insert. repeat rewrite (fixpoint_interp1_eq).
                          destruct (cap_lang.decode w); simpl; eauto.
                        + rewrite /RegLocate lookup_insert_ne; auto.
                          destruct (reg_eq_dec r0 r1); simplify_eq.
                          * rewrite lookup_insert. repeat rewrite (fixpoint_interp1_eq). simpl; eauto.
                          * rewrite lookup_insert_ne; auto. iApply "Hreg". auto. }
                    iApply ("IH" with "[Hfull'] [Hreg'] [Hmap] [HM] [Hsts] [Hcls']"); eauto.
                 ++ iApply wp_pure_step_later; auto.
                    iApply wp_value; eauto. iNext. iIntros. discriminate.
            * iApply (wp_add_sub_lt_fail2 with "[Ha HPC Hdst Hr0]"); eauto; iFrame.
              iNext. iIntros "(HPC & Ha & Hr0)". iApply wp_pure_step_later; auto.
              iNext. iApply wp_value. iIntros; discriminate. }
      { destruct (reg_eq_dec PC r0).
        - subst r0. iApply (wp_add_sub_lt_PC_fail1 with "[Ha HPC]"); eauto.
          + iFrame.
          + iNext. iIntros "(HPC & Ha)".
            iApply wp_pure_step_later; auto.
            iApply wp_value. iNext; iIntros; discriminate.
        - destruct (H3 r0) as [wr0 Hsomer0].
          destruct (reg_eq_dec dst r0).
          + subst r0. destruct wdst.
            * iApply (wp_add_sub_lt_success with "[Ha HPC Hdst]"); eauto.
              -- destruct (reg_eq_dec dst PC); eauto; try congruence.
                 iFrame. destruct (reg_eq_dec dst dst); eauto; try congruence.
              -- simpl. iNext. destruct (reg_eq_dec dst PC); try congruence.
                 iIntros "(HPC & Ha & _ & _ & Hdst)".
                 case_eq (a+1)%a; intros.
                 ++ iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    repeat rewrite -delete_insert_ne; auto.
                    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    iApply wp_pure_step_later; auto. iNext.
                    iMod ("Hcls" with "[Hown Ha]") as "Hcls'".
                    { iFrame. iNext. iExists w; iFrame; auto. }
                    iAssert ((interp_registers (<[dst:=match cap_lang.decode w with
                                                       | Lt _ _ _ => inl (Z.b2z (z0 <? z)%Z)
                                                       | cap_lang.Add _ _ _ => inl (z0 + z)%Z
                                                       | Sub _ _ _ => inl (z0 - z)%Z
                                                       | _ => inl 0%Z
                                                       end]> r)))%I
                      as "[Hfull' Hreg']".
                    { iSplitR.
                      - iIntros (r0). 
                        destruct (H3 r0) as [c Hsome].
                        iPureIntro.
                        destruct (decide (dst = r0)); simplify_eq;
                          [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
                      - iIntros (r0 Hnepc) "/=".
                        destruct (H3 r0) as [c Hsome].
                        destruct (decide (dst = r0)); simplify_eq.
                        + rewrite /RegLocate lookup_insert. repeat rewrite (fixpoint_interp1_eq).
                          destruct (cap_lang.decode w); simpl; eauto.
                        + rewrite /RegLocate lookup_insert_ne; auto.
                          iApply "Hreg". auto. }
                    iApply ("IH" with "[Hfull'] [Hreg'] [Hmap] [HM] [Hsts] [Hcls']"); eauto.
                 ++ iApply wp_pure_step_later; auto.
                    iApply wp_value; eauto. iNext. iIntros. discriminate.
            * iApply (wp_add_sub_lt_fail1 with "[Ha HPC Hdst]"); eauto; iFrame.
              iNext. iIntros "(HPC & Ha & Hdst)". iApply wp_pure_step_later; auto.
              iNext. iApply wp_value. iIntros; discriminate.
          + iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
            repeat rewrite lookup_delete_ne; eauto.
            destruct wr0.
            * iApply (wp_add_sub_lt_success with "[Ha HPC Hdst Hr0]"); eauto.
              -- destruct (reg_eq_dec dst PC); eauto; try congruence.
                 iFrame. destruct (reg_eq_dec r0 dst); eauto; try congruence.
              -- simpl. iNext. destruct (reg_eq_dec dst PC); try congruence.
                 destruct (reg_eq_dec r0 dst); try congruence.
                 iIntros "(HPC & Ha & Hr0 & _ & Hdst)".
                 case_eq (a+1)%a; intros.
                 ++ iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    rewrite -delete_insert_ne; auto.
                    iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    repeat rewrite -delete_insert_ne; auto.
                    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    iApply wp_pure_step_later; auto. iNext.
                    iMod ("Hcls" with "[Hown Ha]") as "Hcls'".
                    { iFrame. iNext. iExists w. iFrame. auto. }
                    iAssert ((interp_registers (<[dst:=match cap_lang.decode w with
                                                       | Lt _ _ _ => inl (Z.b2z (z0 <? z)%Z)
                                                       | cap_lang.Add _ _ _ => inl (z0 + z)%Z
                                                       | Sub _ _ _ => inl (z0 - z)%Z
                                                       | _ => inl 0%Z
                                                       end]> (<[r0:=inl z0]> r))))%I
                      as "[Hfull' Hreg']".
                    { iSplitR.
                      - iIntros (r1).
                        destruct (H3 r1) as [c Hsome].
                        iPureIntro.
                        destruct (decide (dst = r1)); simplify_eq;
                          [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
                        destruct (reg_eq_dec r0 r1); simplify_eq;
                          [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
                      - iIntros (r1 Hnepc) "/=".
                        destruct (H3 r1) as [c Hsome].
                        destruct (decide (dst = r1)); simplify_eq.
                        + rewrite /RegLocate lookup_insert. repeat rewrite (fixpoint_interp1_eq).
                          destruct (cap_lang.decode w); simpl; eauto.
                        + rewrite /RegLocate lookup_insert_ne; auto.
                          destruct (reg_eq_dec r0 r1); simplify_eq.
                          * rewrite lookup_insert. repeat rewrite (fixpoint_interp1_eq). simpl; eauto.
                          * rewrite lookup_insert_ne; auto. iApply "Hreg". auto. }
                    iApply ("IH" with "[Hfull'] [Hreg'] [Hmap] [HM] [Hsts] [Hcls']"); eauto.
                 ++ iApply wp_pure_step_later; auto.
                    iApply wp_value; eauto. iNext. iIntros. discriminate.
            * iApply (wp_add_sub_lt_fail1 with "[Ha HPC Hdst Hr0]"); eauto; iFrame.
              iNext. iIntros "(HPC & Ha & Hr0)". iApply wp_pure_step_later; auto.
              iNext. iApply wp_value. iIntros; discriminate. }
      { destruct (reg_eq_dec PC r0).
        - subst r0. iApply (wp_add_sub_lt_PC_fail1 with "[Ha HPC]"); eauto.
          + iFrame.
          + iNext. iIntros "(HPC & Ha)".
            iApply wp_pure_step_later; auto.
            iApply wp_value. iNext; iIntros; discriminate.
        - destruct (reg_eq_dec PC r1).
          + subst r1. iApply (wp_add_sub_lt_PC_fail2 with "[Ha HPC]"); eauto.
            * iFrame.
            * iNext. iIntros "(HPC & Ha)".
              iApply wp_pure_step_later; auto.
              iApply wp_value. iNext; iIntros; discriminate.
          + destruct (H3 r0) as [wr0 Hsomer0].
            destruct (H3 r1) as [wr1 Hsomer1].
            destruct (reg_eq_dec dst r0).
            * subst r0. destruct (reg_eq_dec dst r1).
              { subst r1. destruct wdst.
                - iApply (wp_add_sub_lt_success_same with "[Ha HPC Hdst]"); eauto.
                  + simpl; iFrame. destruct (reg_eq_dec dst dst); auto; congruence.
                  + iNext. destruct (reg_eq_dec dst PC); try congruence.
                    iIntros "(HPC & Ha & _ & Hdst)".
                    case_eq (a+1)%a; intros.
                    * iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                      repeat rewrite -delete_insert_ne; auto.
                      iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                      iApply wp_pure_step_later; auto. iNext.
                      iMod ("Hcls" with "[Hown Ha]") as "Hcls'".
                      { iFrame. iNext. iExists w. iFrame. auto. }
                      iAssert ((interp_registers (<[dst:=match cap_lang.decode w with
                                                         | Lt _ _ _ => inl (Z.b2z (z <? z)%Z)
                                                         | cap_lang.Add _ _ _ => inl (z + z)%Z
                                                         | Sub _ _ _ => inl (z - z)%Z
                                                         | _ => inl 0%Z
                                                         end]> r)))%I
                        as "[Hfull' Hreg']".
                      { iSplitR.
                        - iIntros (r1).
                          destruct (H3 r1) as [c Hsome].
                          iPureIntro.
                          destruct (decide (dst = r1)); simplify_eq;
                            [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
                        - iIntros (r1 Hnepc) "/=".
                          destruct (H3 r1) as [c Hsome].
                          destruct (decide (dst = r1)); simplify_eq.
                          + rewrite /RegLocate lookup_insert. repeat rewrite (fixpoint_interp1_eq).
                            destruct (cap_lang.decode w); simpl; eauto.
                          + rewrite /RegLocate lookup_insert_ne; auto.
                            iApply "Hreg". auto. }
                      iApply ("IH" with "[Hfull'] [Hreg'] [Hmap] [HM] [Hsts] [Hcls']"); eauto.
                    * iApply wp_pure_step_later; auto.
                      iNext. iApply wp_value; auto. iIntros; discriminate.
                - iApply (wp_add_sub_lt_fail1 with "[Ha HPC Hdst]"); eauto; iFrame.
                  iNext. iIntros "(HPC & Ha & Hdst)". iApply wp_pure_step_later; auto.
                  iApply wp_value; eauto. iNext; iIntros; discriminate. }
              { iDestruct ((big_sepM_delete _ _ r1) with "Hmap") as "[Hr1 Hmap]".
                repeat rewrite lookup_delete_ne; eauto.
                destruct wdst.
                - destruct wr1.
                  + iApply (wp_add_sub_lt_success with "[Ha HPC Hdst Hr1]"); eauto.
                    * iFrame. destruct (reg_eq_dec dst dst); try congruence; auto.
                    * iNext. destruct (reg_eq_dec dst PC); try congruence.
                      destruct (reg_eq_dec r1 dst); try congruence.
                      iIntros "(HPC & Ha & _ & Hr1 & Hdst)".
                      case_eq (a+1)%a; intros.
                      { iDestruct ((big_sepM_delete _ _ r1) with "[Hr1 Hmap]") as "Hmap /=";
                          [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                        rewrite -delete_insert_ne; auto.
                        iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                          [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                        repeat rewrite -delete_insert_ne; auto.
                        iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                          [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                        iApply wp_pure_step_later; auto. iNext.
                        iMod ("Hcls" with "[Hown Ha]") as "Hcls'".
                        { iFrame. iNext. iExists w. iFrame. auto. }
                        iAssert ((interp_registers (<[dst:=match cap_lang.decode w with
                                                           | Lt _ _ _ => inl (Z.b2z (z <? z0)%Z)
                                                           | cap_lang.Add _ _ _ => inl (z + z0)%Z
                                                           | Sub _ _ _ => inl (z - z0)%Z
                                                           | _ => inl 0%Z
                                                           end]> (<[r1:=inl z0]> r))))%I
                          as "[Hfull' Hreg']".
                        { iSplitR.
                          - iIntros (r2).
                            destruct (H3 r2) as [c Hsome].
                            iPureIntro.
                            destruct (decide (dst = r2)); simplify_eq;
                              [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
                            destruct (reg_eq_dec r1 r2); simplify_eq;
                              [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
                          - iIntros (r2 Hnepc) "/=".
                            destruct (H3 r2) as [c Hsome].
                            destruct (decide (dst = r2)); simplify_eq.
                            + rewrite /RegLocate lookup_insert. repeat rewrite (fixpoint_interp1_eq).
                              destruct (cap_lang.decode w); simpl; eauto.
                            + rewrite /RegLocate lookup_insert_ne; auto.
                              destruct (reg_eq_dec r1 r2); simplify_eq.
                              * rewrite lookup_insert. repeat rewrite (fixpoint_interp1_eq). simpl; eauto.
                              * rewrite lookup_insert_ne; auto. iApply "Hreg". auto. }
                        iApply ("IH" with "[Hfull'] [Hreg'] [Hmap] [HM] [Hsts] [Hcls']"); eauto. }
                      { iApply wp_pure_step_later; auto.
                        iApply wp_value; auto. iNext; iIntros; discriminate. }
                  + iApply (wp_add_sub_lt_fail2 with "[Ha HPC Hr1]"); eauto; iFrame.
                    iNext. iIntros "(HPC & Ha & Hr1)". iApply wp_pure_step_later; auto.
                    iApply wp_value; eauto. iNext; iIntros; discriminate.
                - iApply (wp_add_sub_lt_fail1 with "[Ha HPC Hdst]"); eauto; iFrame.
                  iNext. iIntros "(HPC & Ha & Hdst)". iApply wp_pure_step_later; auto.
                  iApply wp_value; eauto. iNext; iIntros; discriminate. }
            * iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
              repeat rewrite lookup_delete_ne; eauto.
              destruct (reg_eq_dec dst r1).
              { subst r1. destruct wdst.
                - destruct wr0.
                  + iApply (wp_add_sub_lt_success with "[Ha HPC Hdst Hr0]"); eauto.
                    * simpl; iFrame. destruct (reg_eq_dec r0 dst); auto; try congruence.
                      destruct (reg_eq_dec dst dst); auto; congruence.
                    * iNext. destruct (reg_eq_dec dst PC); try congruence.
                      destruct (reg_eq_dec r0 dst); try congruence.
                      iIntros "(HPC & Ha & Hr0 & _ & Hdst)".
                      case_eq (a+1)%a; intros.
                      { iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                          [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                        rewrite -delete_insert_ne; auto.
                        iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                          [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                        repeat rewrite -delete_insert_ne; auto.
                        iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                          [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                        iApply wp_pure_step_later; auto. iNext.
                        iMod ("Hcls" with "[Hown Ha]") as "Hcls'".
                        { iFrame. iNext. iExists w. iFrame. auto. }
                        iAssert ((interp_registers (<[dst:=match cap_lang.decode w with
                                                           | Lt _ _ _ => inl (Z.b2z (z0 <? z)%Z)
                                                           | cap_lang.Add _ _ _ => inl (z0 + z)%Z
                                                           | Sub _ _ _ => inl (z0 - z)%Z
                                                           | _ => inl 0%Z
                                                           end]> (<[r0:=inl z0]> r))))%I
                          as "[Hfull' Hreg']".
                        { iSplitR.
                          - iIntros (r1).
                            destruct (H3 r1) as [c Hsome].
                            iPureIntro.
                            destruct (decide (dst = r1)); simplify_eq;
                              [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
                            destruct (reg_eq_dec r0 r1); simplify_eq;
                              [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
                          - iIntros (r1 Hnepc) "/=".
                            destruct (H3 r1) as [c Hsome].
                            destruct (decide (dst = r1)); simplify_eq.
                            + rewrite /RegLocate lookup_insert. repeat rewrite (fixpoint_interp1_eq).
                              destruct (cap_lang.decode w); simpl; eauto.
                            + rewrite /RegLocate lookup_insert_ne; auto.
                              destruct (reg_eq_dec r0 r1); simplify_eq.
                              * rewrite lookup_insert. repeat rewrite (fixpoint_interp1_eq). simpl; eauto.
                              * rewrite lookup_insert_ne; auto. iApply "Hreg". auto. }
                        iApply ("IH" with "[Hfull'] [Hreg'] [Hmap] [HM] [Hsts] [Hcls']"); eauto. }
                      { iApply wp_pure_step_later; auto.
                        iNext. iApply wp_value; auto. iIntros; discriminate. }
                  + iApply (wp_add_sub_lt_fail1 with "[Ha HPC Hr0]"); eauto; iFrame.
                    iNext. iIntros "(HPC & Ha & Hr0)". iApply wp_pure_step_later; auto.
                    iApply wp_value; eauto. iNext; iIntros; discriminate.
                - iApply (wp_add_sub_lt_fail2 with "[Ha HPC Hdst]"); eauto; iFrame.
                  iNext. iIntros "(HPC & Ha & Hdst)". iApply wp_pure_step_later; auto.
                  iApply wp_value; eauto. iNext; iIntros; discriminate. }
              { destruct (reg_eq_dec r0 r1).
                - subst r1. destruct wr0.
                  + iApply (wp_add_sub_lt_success_same with "[Ha HPC Hdst Hr0]"); eauto.
                    * simpl; iFrame. destruct (reg_eq_dec r0 dst); auto; try congruence.
                      destruct (reg_eq_dec dst PC); auto; congruence.
                    * iNext. destruct (reg_eq_dec dst PC); try congruence.
                      destruct (reg_eq_dec r0 dst); try congruence.
                      iIntros "(HPC & Ha & Hr0 & Hdst)".
                      case_eq (a+1)%a; intros.
                      { iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                          [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                        rewrite -delete_insert_ne; auto.
                        iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                          [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                        repeat rewrite -delete_insert_ne; auto.
                        iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                          [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                        iApply wp_pure_step_later; auto. iNext.
                        iMod ("Hcls" with "[Hown Ha]") as "Hcls'".
                        { iFrame. iNext. iExists w. iFrame. auto. }
                        iAssert ((interp_registers (<[dst:= match cap_lang.decode w with
                                                            | Lt _ _ _ => inl (Z.b2z (z <? z)%Z)
                                                            | cap_lang.Add _ _ _ => inl (z + z)%Z
                                                            | Sub _ _ _ => inl (z - z)%Z
                                                            | _ => inl 0%Z
                                                            end]> (<[r0:=inl z]> r))))%I
                          as "[Hfull' Hreg']".
                        { iSplitR.
                          - iIntros (r1).
                            destruct (H3 r1) as [c Hsome].
                            iPureIntro.
                            destruct (decide (dst = r1)); simplify_eq;
                              [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
                            destruct (reg_eq_dec r0 r1); simplify_eq;
                              [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
                          - iIntros (r1 Hnepc) "/=".
                            destruct (H3 r1) as [c Hsome].
                            destruct (decide (dst = r1)); simplify_eq.
                            + rewrite /RegLocate lookup_insert. repeat rewrite (fixpoint_interp1_eq).
                              destruct (cap_lang.decode w); simpl; eauto.
                            + rewrite /RegLocate lookup_insert_ne; auto.
                              destruct (reg_eq_dec r0 r1); simplify_eq.
                              * rewrite lookup_insert. repeat rewrite (fixpoint_interp1_eq). simpl; eauto.
                              * rewrite lookup_insert_ne; auto. iApply "Hreg". auto. }
                        iApply ("IH" with "[Hfull'] [Hreg'] [Hmap] [HM] [Hsts] [Hcls']"); eauto. }
                      { iApply wp_pure_step_later; auto.
                        iNext. iApply wp_value; auto. iIntros; discriminate. }
                  + iApply (wp_add_sub_lt_fail1 with "[Ha HPC Hr0]"); eauto; iFrame.
                    iNext. iIntros "(HPC & Ha & Hr0)". iApply wp_pure_step_later; auto.
                    iApply wp_value; eauto. iNext; iIntros; discriminate.
                - iDestruct ((big_sepM_delete _ _ r1) with "Hmap") as "[Hr1 Hmap]".
                  repeat rewrite lookup_delete_ne; eauto.
                  destruct wr0.
                  + destruct wr1.
                    * iApply (wp_add_sub_lt_success with "[Ha HPC Hdst Hr0 Hr1]"); eauto.
                      { simpl; iFrame. destruct (reg_eq_dec r0 dst); auto; try congruence.
                        destruct (reg_eq_dec r1 dst); destruct (reg_eq_dec dst PC); try congruence; auto. }
                      { iNext. destruct (reg_eq_dec dst PC); try congruence.
                        destruct (reg_eq_dec r0 dst); try congruence.
                        destruct (reg_eq_dec r1 dst); try congruence.
                        iIntros "(HPC & Ha & Hr0 & Hr1 & Hdst)".
                        case_eq (a+1)%a; intros.
                        - iDestruct ((big_sepM_delete _ _ r1) with "[Hr1 Hmap]") as "Hmap /=";
                            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                          repeat rewrite -delete_insert_ne; auto.
                          iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                          repeat rewrite -delete_insert_ne; auto.
                          iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                          repeat rewrite -delete_insert_ne; auto.
                          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                          iApply wp_pure_step_later; auto. iNext.
                          iMod ("Hcls" with "[Hown Ha]") as "Hcls'".
                          { iFrame. iNext. iExists w. iFrame. auto. }
                          iAssert ((interp_registers (<[dst:=match cap_lang.decode w with
                                                             | Lt _ _ _ => inl (Z.b2z (z <? z0)%Z)
                                                             | cap_lang.Add _ _ _ => inl (z + z0)%Z
                                                             | Sub _ _ _ => inl (z - z0)%Z
                                                             | _ => inl 0%Z
                                                             end]> (<[r0:=inl z]> (<[r1:=inl z0]> r)))))%I
                            as "[Hfull' Hreg']".
                          { iSplitR.
                            - iIntros (r2).
                              destruct (H3 r2) as [c Hsome].
                              iPureIntro.
                              destruct (decide (dst = r2)); simplify_eq;
                                [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
                              destruct (reg_eq_dec r0 r2); simplify_eq;
                                [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
                              destruct (reg_eq_dec r1 r2); simplify_eq;
                                [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
                            - iIntros (r2 Hnepc) "/=".
                              destruct (H3 r2) as [c Hsome].
                              destruct (decide (dst = r2)); simplify_eq.
                              + rewrite /RegLocate lookup_insert. repeat rewrite (fixpoint_interp1_eq).
                                destruct (cap_lang.decode w); simpl; eauto.
                              + rewrite /RegLocate lookup_insert_ne; auto.
                                destruct (reg_eq_dec r0 r2); simplify_eq.
                                * rewrite lookup_insert. repeat rewrite (fixpoint_interp1_eq). simpl; eauto.
                                * rewrite lookup_insert_ne; auto. destruct (reg_eq_dec r1 r2); simplify_eq.
                                  -- rewrite lookup_insert. repeat rewrite (fixpoint_interp1_eq). simpl; eauto.
                                  -- rewrite lookup_insert_ne; auto. iApply "Hreg". auto. }
                          iApply ("IH" with "[Hfull'] [Hreg'] [Hmap] [HM] [Hsts] [Hcls']"); eauto.
                        - iApply wp_pure_step_later; auto.
                          iNext. iApply wp_value; auto. iIntros; discriminate. }
                    * iApply (wp_add_sub_lt_fail2 with "[Ha HPC Hr1]"); eauto; iFrame.
                      iNext. iIntros "(HPC & Ha & Hr1)". iApply wp_pure_step_later; auto.
                      iApply wp_value; eauto. iNext; iIntros; discriminate.
                  + iApply (wp_add_sub_lt_fail1 with "[Ha HPC Hr0]"); eauto; iFrame.
                    iNext. iIntros "(HPC & Ha & Hr0)". iApply wp_pure_step_later; auto.
                    iApply wp_value; eauto. iNext; iIntros; discriminate. } }
      Unshelve. exact (inl 0%Z). exact (inl 0%Z). exact (inl 0%Z). exact (inl 0%Z). exact (inl 0%Z). exact (inl 0%Z).
      exact (inl 0%Z). exact (inl 0%Z). exact (inl 0%Z). exact (inl 0%Z).
  Qed.

End fundamental.