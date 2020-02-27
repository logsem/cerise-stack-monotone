From cap_machine Require Export logrel.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Import ftlr_base monotone.
From cap_machine Require Import addr_reg.
From cap_machine.rules Require Import rules_Subseg.

(* TODO: Move into logrel.v *)
Instance future_world_persistent (Σ: gFunctors) g W W': Persistent (@future_world Σ g W W').
Proof.
  unfold future_world. destruct g; apply bi.pure_persistent.
Qed.

Section fundamental.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            Heap: heapG Σ}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation WORLD := (leibnizO (STS * STS)). 
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (leibnizO Word) -n> iProp Σ).
  Notation R := (WORLD -n> (leibnizO Reg) -n> iProp Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma leb_addr_spec:
    forall a1 a2,
      reflect (le_addr a1 a2) (leb_addr a1 a2).
  Proof.
    intros. rewrite /leb_addr /le_addr.
    apply Z.leb_spec0.
  Qed.    

  Lemma isWithin_implies a0 a1 b e:
    isWithin a0 a1 b e = true ->
    (b <= a0 /\ a1 <= e)%a.
  Proof.
    rewrite /isWithin.
    intros. repeat (apply andb_true_iff in H3; destruct H3).
    generalize (proj2 (reflect_iff _ _ (leb_addr_spec _ _)) H6).
    generalize (proj2 (reflect_iff _ _ (leb_addr_spec _ _)) H4).
    auto.
  Qed.

  (* TODO: This should be move to region.v *)
  Lemma region_split b a e :
    (b <= a /\ a <= e)%a ->
    region_addrs b e = region_addrs b a ++ region_addrs a e.
  Proof.
    intros [? ?].
    rewrite /region_addrs.
    rewrite (region_addrs_aux_decomposition (region_size b e) b (region_size b a)).
    2: unfold region_size; solve_addr.
    do 2 f_equal; unfold region_size; solve_addr.
  Qed.

  (* TODO: This should be move to region.v *)
  Lemma isWithin_region_addrs_decomposition a0 a1 b e:
    (b <= a0 /\ a1 <= e /\ a0 <= a1)%a ->
    region_addrs b e = region_addrs b a0 ++
                       region_addrs a0 a1 ++
                       region_addrs a1 e.
  Proof with try (unfold region_size; solve_addr).
    intros (Hba0 & Ha1e & Ha0a1).
    rewrite (region_split b a0 e)... f_equal.
    rewrite (region_split a0 a1 e)...
  Qed.

  Lemma within_in_range:
    forall a b b' e e',
      (b <= b')%a ->
      (e' <= e)%a ->
      in_range a b' e' ->
      in_range a b e.
  Proof.
    intros. destruct H5. unfold in_range.
    unfold le_addr in *. unfold lt_addr in *.
    lia.
  Qed.

  (* TODO: Someone clever should factorize *)
  Lemma subseg_interp_preserved W p l b b' e e' a :
      p <> E ->
      (b <= b')%a ->
      (e' <= e)%a ->
      □ ▷ (∀ (a7 : leibnizO (STS * STS)) (a8 : Reg) (a9 : Perm) (a10 : Locality) 
             (a11 a12 a13 : Addr),
              full_map a8
                       -∗ (∀ r1 : RegName,
                              ⌜r1 ≠ PC⌝
                              → ((fixpoint interp1) a7)
                                  match a8 !! r1 with
                                  | Some w0 => w0
                                  | None => inl 0%Z
                                  end)
                       -∗ registers_mapsto (<[PC:=inr (a9, a10, a11, a12, a13)]> a8)
                       -∗ region a7
                       -∗ sts_full_world sts_std a7
                       -∗ na_own logrel_nais ⊤
                       -∗ ⌜a9 = RX ∨ a9 = RWX ∨ a9 = RWLX ∧ a10 = Local⌝
              → □ (∃ p'0 : Perm,
                      ⌜PermFlows a9 p'0⌝
                      ∧ ([∗ list] a14 ∈ region_addrs a11 a12, 
                         read_write_cond a14 p'0 interp
                         ∧ ⌜if pwl a9
                            then region_state_pwl a7 a14
                            else region_state_nwl a7 a14 a10⌝
                                 ∧ ⌜region_std a7 a14⌝)) -∗ 
                  interp_conf a7) -∗
      (fixpoint interp1) W (inr (p, l, b, e, a)) -∗
      (fixpoint interp1) W (inr (p, l, b', e', a)).
  Proof.
    intros Hne Hb He. iIntros "#IH Hinterp".
    repeat (rewrite fixpoint_interp1_eq).
    destruct p; simpl; auto; try congruence.
    - iDestruct "Hinterp" as (p Hfl) "H".
      iExists p. iSplitR; auto.
      destruct (Z_le_dec b' e').
      + rewrite (isWithin_region_addrs_decomposition b' e'); eauto.
        iDestruct (big_sepL_app with "H") as "[H1 H2]".
        iDestruct (big_sepL_app with "H2") as "[H2 H3]".
        auto.
      + replace (region_addrs b' e') with (nil: list Addr).
        rewrite big_sepL_nil. auto.
        unfold region_addrs, region_size. rewrite Z_to_nat_nonpos //; lia.
    - iDestruct "Hinterp" as (p) "[% H]".
      iExists p. iSplitR; auto.
      destruct (Z_le_dec b' e').
      + rewrite (isWithin_region_addrs_decomposition b' e'); eauto.
        iDestruct (big_sepL_app with "H") as "[H1 H2]".
        iDestruct (big_sepL_app with "H2") as "[H2 H3]".
        auto.
      + replace (region_addrs b' e') with (nil: list Addr).
        rewrite big_sepL_nil. auto.
        unfold region_addrs, region_size. rewrite Z_to_nat_nonpos //; lia.
    - destruct l; auto.
      iDestruct "Hinterp" as (p) "[% H]".
      iExists p. iSplitR; auto.
      destruct (Z_le_dec b' e').
      + rewrite (isWithin_region_addrs_decomposition b' e'); eauto.
        iDestruct (big_sepL_app with "H") as "[H1 H2]".
        iDestruct (big_sepL_app with "H2") as "[H2 H3]".
        auto.
      + replace (region_addrs b' e') with (nil: list Addr).
        rewrite big_sepL_nil. auto.
        unfold region_addrs, region_size. rewrite Z_to_nat_nonpos //; lia.
    - iDestruct "Hinterp" as (p) "[% [H H']]".
      iExists p. iSplitR; auto.
      iDestruct "H" as "#H".
      iDestruct "H'" as "#H'".
      iSplitL.
      + destruct (Z_le_dec b' e').
        * rewrite (isWithin_region_addrs_decomposition b' e'); eauto.
          iDestruct (big_sepL_app with "H") as "[H1 H2]".
          iDestruct (big_sepL_app with "H2") as "[H3 H4]".
          auto.
        * replace (region_addrs b' e') with (nil: list Addr).
          rewrite big_sepL_nil. auto.
          unfold region_addrs, region_size. rewrite Z_to_nat_nonpos //; lia.
      + iModIntro.
        rewrite /exec_cond.
        iIntros (a0 r W') "#Hbe' #Hfuture". iNext. rewrite /interp_expr /=.
        iIntros "[[Hfull Hreg] [Hmap [Hregion [Hsts Hown]]]]".
        iSplitR; auto.
        iApply ("IH" with "[Hfull] [Hreg] [Hmap] [Hregion] [Hsts] [Hown]"); eauto.
        rewrite /read_write_cond. iAlways.
        iExists p. iSplitR; auto.
        destruct (Z_le_dec b' e').
        * rewrite (isWithin_region_addrs_decomposition b' e'); eauto.
          iDestruct (big_sepL_app with "H") as "[H1 H2]".
          iDestruct (big_sepL_app with "H2") as "[H3 H4]".
          simpl. destruct l; simpl; iDestruct "Hfuture" as %Hfuture.
          { iApply (big_sepL_mono with "H3"). intros.
            simpl. iIntros "[HA [% %]]". iSplitL "HA"; auto.
            iPureIntro. split.
            - eelim (region_state_nwl_monotone_nl _ _ y _ Hfuture H5). auto.
            - eapply related_sts_rel_std; eauto. }
          { iApply (big_sepL_mono with "H3"). intros.
            simpl. iIntros "[HA [% %]]". iSplitL "HA"; auto.
            iPureIntro. split.
            - eapply (region_state_nwl_monotone _ _ _ Local _ Hfuture H5); eauto.
            - eapply rel_is_std_i_monotone; eauto. }
        * replace (region_addrs b' e') with (nil: list Addr).
          rewrite big_sepL_nil. auto.
          unfold region_addrs, region_size. rewrite Z_to_nat_nonpos //; lia.
    - iDestruct "Hinterp" as (p) "[% [H H']]".
      iExists p. iSplitR; auto.
      iDestruct "H" as "#H".
      iDestruct "H'" as "#H'".
      iSplitL.
      + destruct (Z_le_dec b' e').
        * rewrite (isWithin_region_addrs_decomposition b' e'); eauto.
          iDestruct (big_sepL_app with "H") as "[H1 H2]".
          iDestruct (big_sepL_app with "H2") as "[H4 H3]".
          auto.
        * replace (region_addrs b' e') with (nil: list Addr).
          rewrite big_sepL_nil. auto.
          unfold region_addrs, region_size. rewrite Z_to_nat_nonpos //; lia.
      + iModIntro. rewrite /exec_cond.
        iIntros (a0 r W') "#Hbe' #Hfuture". iNext. rewrite /interp_expr /=.
        iIntros "[[Hfull Hreg] [Hmap [Hex [Hsts Hown]]]]".
        iSplitR; auto.
        iApply ("IH" with "[Hfull] [Hreg] [Hmap] [Hex] [Hsts] [Hown]"); eauto.
        iAlways. iExists p; iSplitR; auto.
        destruct (Z_le_dec b' e').
        * rewrite (isWithin_region_addrs_decomposition b' e'); eauto.
          iDestruct (big_sepL_app with "H") as "[H1 H2]".
          iDestruct (big_sepL_app with "H2") as "[H4 H3]".
          simpl. destruct l; simpl; iDestruct "Hfuture" as %Hfuture.
          { iApply (big_sepL_mono with "H4"). intros.
            simpl. iIntros "[HA [% %]]". iSplitL "HA"; auto.
            iPureIntro. split.
            - eelim (region_state_nwl_monotone_nl _ _ y _ Hfuture H5). auto.
            - eapply related_sts_rel_std; eauto. }
          { iApply (big_sepL_mono with "H4"). intros.
            simpl. iIntros "[HA [% %]]". iSplitL "HA"; auto.
            iPureIntro. split.
            - eapply (region_state_nwl_monotone _ _ _ Local _ Hfuture H5); eauto.
            - eapply rel_is_std_i_monotone; eauto. }
        * replace (region_addrs b' e') with (nil: list Addr).
          rewrite big_sepL_nil. auto.
          unfold region_addrs, region_size. rewrite Z_to_nat_nonpos //; lia.
    - destruct l; auto. iDestruct "Hinterp" as (p) "[% [H H']]".
      iExists p. iSplitR; auto.
      iDestruct "H" as "#H".
      iDestruct "H'" as "#H'".
      iSplitL.
      + destruct (Z_le_dec b' e').
        * rewrite (isWithin_region_addrs_decomposition b' e'); eauto.
          iDestruct (big_sepL_app with "H") as "[H1 H2]".
          iDestruct (big_sepL_app with "H2") as "[H4 H3]".
          auto.
        * replace (region_addrs b' e') with (nil: list Addr).
          rewrite big_sepL_nil. auto.
          unfold region_addrs, region_size. rewrite Z_to_nat_nonpos //; lia.
      + iModIntro. rewrite /exec_cond.
        iIntros (a0 r W') "#Hbe' #Hfuture". iNext. rewrite /interp_expr /=.
        iIntros "[[Hfull Hreg] [Hmap [Hex [Hsts Hown]]]]".
        iSplitR; auto.
        iApply ("IH" with "[Hfull] [Hreg] [Hmap] [Hex] [Hsts] [Hown]"); eauto.
        iExists p. iSplitR; auto.
        destruct (Z_le_dec b' e').
        * rewrite (isWithin_region_addrs_decomposition b' e'); eauto.
          iDestruct (big_sepL_app with "H") as "[H1 H2]".
          iDestruct (big_sepL_app with "H2") as "[H4 H3]".
          simpl. iDestruct "Hfuture" as %Hfuture.
          iApply (big_sepL_mono with "H4"). intros.
          simpl. iIntros "[HA [% %]]". iSplitL "HA"; auto.
          iPureIntro. split.
          { eapply region_state_pwl_monotone; eauto. }
          { eapply rel_is_std_i_monotone; eauto. }
        * replace (region_addrs b' e') with (nil: list Addr).
          rewrite big_sepL_nil. auto.
          unfold region_addrs, region_size. rewrite Z_to_nat_nonpos //; lia.
          Unshelve. assumption. assumption. assumption. assumption.
  Qed.

  Lemma subseg_case (W : WORLD) (r : leibnizO Reg) (p p' : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (dst : RegName) (r1 r2 : Z + RegName):
    ftlr_instr W r p p' g b e a w (Subseg dst r1 r2) ρ.
  Proof.
    intros Hp Hsome i Hbae Hfp Hpwl Hregion Hstd Hnotrevoked HO Hi.
    iIntros "#IH #Hinv #Hreg #Hinva Hmono #Hw Hsts Hown".
    iIntros "Hr Hstate Ha HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_Subseg with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { (* todo: tactic *) intro ri. rewrite lookup_insert_is_Some.
      destruct (decide (PC = ri)); eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec.
    { iApply wp_pure_step_later; auto. iNext.
      iApply wp_value; auto. iIntros; discriminate. }
    { match goal with
      | H: incrementPC _ = Some _ |- _ => apply incrementPC_Some_inv in H as (p''&g''&b''&e''&a''& ? & HPC & Z & Hregs')
      end. simplify_map_eq.
      iApply wp_pure_step_later; auto. iNext.

      destruct (reg_eq_dec PC dst).
      { subst dst. repeat rewrite insert_insert in HPC |- *.
        rewrite !lookup_insert in HPC H3; inv HPC; inv H3.
        iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
        iApply ("IH" $! _ r with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hown]"); try iClear "IH"; eauto.
        iAlways. iExists p'. iSplitR; auto.
        generalize (isWithin_implies _ _ _ _ H7). intros [A B].
        destruct (Z_le_dec b'' e'').
        + rewrite (isWithin_region_addrs_decomposition b'' e'' b0 e0); auto.
          iDestruct (big_sepL_app with "Hinv") as "[Hinv1 Hinv2]".
          iDestruct (big_sepL_app with "Hinv2") as "[Hinv3 Hinv4]".
          iFrame "#".
        + replace (region_addrs b'' e'') with (nil: list Addr).
          rewrite big_sepL_nil. auto.
          unfold region_addrs, region_size. rewrite Z_to_nat_nonpos //; lia. }
      { rewrite lookup_insert_ne in HPC; auto.
        rewrite lookup_insert in HPC.
        rewrite lookup_insert_ne in H3; auto. inv HPC.
        iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
        iApply ("IH" $! _ (<[dst:=_]> _) with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
        - intros; simpl.
          rewrite lookup_insert_is_Some.
          destruct (reg_eq_dec dst x0); auto; right; split; auto.
          rewrite lookup_insert_is_Some.
          destruct (reg_eq_dec PC x0); auto; right; split; auto.
        - iIntros (ri Hri). rewrite /RegLocate.
          destruct (reg_eq_dec ri dst).
          + subst ri. rewrite lookup_insert.
            iDestruct ("Hreg" $! dst Hri) as "Hdst".
            generalize (isWithin_implies _ _ _ _ H7). intros [A B].
            rewrite H3. iApply subseg_interp_preserved; eauto.
          + repeat rewrite lookup_insert_ne; auto.
            iApply "Hreg"; auto. } }
  Qed.

End fundamental.
