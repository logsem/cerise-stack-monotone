From stdpp Require Import base.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From cap_machine Require Export logrel monotone.
From cap_machine Require Import ftlr_base.
From cap_machine.rules Require Import rules_StoreU.
From cap_machine Require Import stdpp_extra.
Import uPred.

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

  Lemma isU_inv:
    ∀ (W : leibnizO WORLD) (a' a b e : Addr) (p : Perm) (g : Locality),
      (b ≤ a' < addr_reg.min a e)%Z
      → isU p = true
      → ⊢ (interp W) (inr (p, g, b, e, a))
      → ∃ p' : Perm, ⌜PermFlows (promote_perm p) p'⌝ ∗ read_write_cond a' p' interp
                     ∧ ⌜(∃ ρ : region_type, std W !! a' = Some ρ
                                            ∧ ρ ≠ Revoked /\ (∀ g, ρ ≠ Static g) ∧ (∀ g, ρ ≠ Monostatic g) ∧ (∀ w, ρ ≠ Uninitialized w))⌝.
  Proof.
    intros. rewrite /interp fixpoint_interp1_eq /=. iIntros "H".
    assert (p = URW \/ p = URWL \/ p = URWX \/ p = URWLX) as [-> | [-> | [-> | ->] ] ] by (destruct p; simpl in H0; auto; congruence); simpl.
    - destruct g.
      + iDestruct (extract_from_region_inv with "H") as (p' ?) "[C %]";try (iExists p'; iFrame; auto);[solve_addr|].
        iSplit;auto. iPureIntro; auto. rewrite H2. eexists;eauto.
      + iDestruct "H" as "[B C]".
        iDestruct (extract_from_region_inv with "B") as (p' ?) "[D %]"; try (iExists p'; iFrame); auto.
        iSplit;auto. iPureIntro; auto. destruct H2; eexists;eauto.
      + iDestruct "H" as "[B C]".
        iDestruct (extract_from_region_inv with "B") as (p' ?) "[D %]"; try (iExists p'; iFrame); auto.
        iSplit;auto. iPureIntro; auto. destruct H2 as [? | [? | ?] ]; eexists;eauto.
    - destruct g; auto.
      iDestruct "H" as "[B C]".
      iDestruct (extract_from_region_inv with "B") as (p' ?) "[D %]"; try (iExists p'; iFrame); auto.
      iPureIntro; split;eauto. eexists;eauto.
    - destruct g.
      + iDestruct (extract_from_region_inv with "H") as (p' Hfl) "[D %]"; try (iExists p'; iFrame); auto; [solve_addr|].
        iSplit;auto. iPureIntro; auto. eexists; eauto.
      + iDestruct "H" as "[B C]".
        iDestruct (extract_from_region_inv with "B") as (p' Hfl) "[E %]"; try (iExists p'; iFrame); auto.
        iSplit;auto. iPureIntro; auto. destruct H1; eexists;eauto.
      + iDestruct "H" as "[B C]".
        iDestruct (extract_from_region_inv with "B") as (p' Hfl) "[E %]"; try (iExists p'; iFrame); auto.
        iSplit;auto. iPureIntro; auto. destruct H1 as [? | [? | ?] ]; eexists;eauto.
    - destruct g; auto.
      iDestruct "H" as "[B C]".
      iDestruct (extract_from_region_inv with "B") as (p' Hfl) "[D %]"; try (iExists p'; iFrame); auto.
      iSplit;auto. iPureIntro; simpl in H1; eexists;eauto.
  Qed.

  Lemma isU_inv_all :
    ∀ (W : leibnizO WORLD) (a' a b e : Addr) (p : Perm) (g : Locality),
      (b ≤ a' < e)%Z
      → isU p = true
      → ⊢ (interp W) (inr (p, g, b, e, a))
      → ∃ p' : Perm, ⌜PermFlows (promote_perm p) p'⌝ ∗ read_write_cond a' p' interp
                     ∧ ⌜(∃ ρ : region_type, std W !! a' = Some ρ
                                            ∧ ρ ≠ Revoked ∧ (∀ g, ρ ≠ Monostatic g) ∧ (forall g, ρ = Static g -> ∃ w, g = {[a':=w]}))⌝.
  Proof.
    intros. iIntros "H". 
    destruct (decide (a' < addr_reg.min a e))%a.
    { iDestruct (isU_inv _ a' with "H") as (p') "(?&?&H)";[solve_addr|auto|]. iDestruct "H" as %(?&?&?&?&?&?).
      iExists p'. iFrame. iPureIntro;eauto. eexists;split;eauto. repeat split;auto.
      intros g0 Hcontr. congruence. }
    assert (addr_reg.min a e <= a' < e)%a;[solve_addr|]. 
    rewrite /interp fixpoint_interp1_eq /=.
    assert (p = URW \/ p = URWL \/ p = URWX \/ p = URWLX) as [-> | [-> | [-> | ->] ] ] by (destruct p; simpl in H0; auto; congruence); simpl.
    - destruct g.
      + iDestruct (extract_from_region_inv with "H") as (p' ?) "[C %]";try (iExists p'; iFrame; auto);[solve_addr|].
        iSplit;auto. iPureIntro; auto. eexists;repeat split;eauto. intros. congruence. 
      + iDestruct "H" as "[B C]".
        iDestruct (extract_from_region_inv with "C") as (p' ?) "[D %]"; try (iExists p'; iFrame);[solve_addr|].
        iSplit;auto. iPureIntro; auto. destruct H3 as [-> |[-> | [? ->] ] ]; eexists;repeat split;eauto;intros ? Hcontr;inversion Hcontr;eauto.
      + iDestruct "H" as "[B C]".
        iDestruct (extract_from_region_inv with "C") as (p' ?) "[D %]"; try (iExists p'; iFrame); [solve_addr|].
        iSplit;auto. iPureIntro; auto. destruct H3 as [? | [? | [? | [ [? ?] | [? ?] ] ] ] ];
                                         eexists;repeat split;eauto;intros ? Hcontr;inversion Hcontr;eauto.
    - destruct g; auto.
      iDestruct "H" as "[B C]".
      iDestruct (extract_from_region_inv with "C") as (p' ?) "[D %]"; try (iExists p'; iFrame); [solve_addr|].
      iPureIntro; split;eauto. destruct H3 as [? | [? ?] ]; eexists;repeat split;eauto;intros ? Hcontr;inversion Hcontr;eauto.
    - destruct g.
      + iDestruct (extract_from_region_inv with "H") as (p' Hfl) "[D %]"; try (iExists p'; iFrame); auto. 
        iSplit;auto. iPureIntro; auto. eexists;repeat split;eauto;intros ? Hcontr;inversion Hcontr;eauto.
      + iDestruct "H" as "[B C]".
        iDestruct (extract_from_region_inv with "C") as (p' Hfl) "[E %]"; try (iExists p'; iFrame);[solve_addr|].
        iSplit;auto. iPureIntro; auto. destruct H2 as [? | [? | [? ?] ] ];
                                         eexists;repeat split;eauto;intros ? Hcontr;inversion Hcontr;eauto.
      + iDestruct "H" as "[B C]".
        iDestruct (extract_from_region_inv with "C") as (p' Hfl) "[E %]"; try (iExists p'; iFrame); [solve_addr|].
        iSplit;auto. iPureIntro; auto. destruct H2 as [? | [? | [? | [ [? ?] | [? ?] ] ] ] ];
                                         eexists;repeat split;eauto;intros ? Hcontr;inversion Hcontr;eauto.
    - destruct g; auto.
      iDestruct "H" as "[B C]".
      iDestruct (extract_from_region_inv with "C") as (p' Hfl) "[D %]"; try (iExists p'; iFrame); [solve_addr|].
      iSplit;auto. iPureIntro; destruct H2 as [? | [? ?] ]; eexists;repeat split;eauto;intros ? Hcontr;inversion Hcontr;eauto.
  Qed.

  Lemma isU_inv_boundary :
    ∀ (W : leibnizO WORLD) (a' a b e : Addr) (p : Perm) (g : Locality),
      (b <= a' < e)%Z → (a' ≤ addr_reg.min a e)%Z
      → isU p = true
      → ⊢ (interp W) (inr (p, g, b, e, a))
      → ∃ p' : Perm, ⌜PermFlows (promote_perm p) p'⌝ ∗ read_write_cond a' p' interp
                     ∧ ⌜(∃ ρ : region_type, std W !! a' = Some ρ
                                            ∧ ρ ≠ Revoked ∧ (∀ g, ρ ≠ Monostatic g) ∧ (forall g, ρ = Static g -> ∃ w, g = {[a':=w]}) ∧
                                            if (a' =? addr_reg.min a e)%Z
                                            then True
                                            else (∀ g, ρ ≠ Static g) ∧ (∀ w, ρ ≠ Uninitialized w))⌝.
  Proof.
    intros. iIntros "H". 
    destruct (a' =? addr_reg.min a e)%Z eqn:Heq.
    - iDestruct (isU_inv_all _ a' with "H") as (p') "(?&?&H)";[solve_addr|auto|]. iDestruct "H" as %(?&?&?&?&?).
      iExists p'. iFrame. iPureIntro;eexists;eauto.
    - apply Z.eqb_neq in Heq. iDestruct (isU_inv _ a' with "H") as (p') "(?&?&H)";[solve_addr|auto|]. iDestruct "H" as %(?&?&?&?&?&?).
      iExists p'. iFrame. iPureIntro;eexists;repeat split;eauto. intros. congruence. 
  Qed.

  Lemma execcPC_implies_interp W p g b e a0:
    p = RX ∨ p = RWX ∨ p = RWLX ∧ g = Monotone →
    ([∗ list] a ∈ region_addrs b e,
     ∃ p', ⌜PermFlows p p'⌝ ∗
       read_write_cond a p' interp
       ∧ ⌜if pwl p
          then region_state_pwl_mono W a
          else region_state_nwl W a g⌝) -∗
      ((fixpoint interp1) W) (inr (p, g, b, e, a0)).
  Proof.
    iIntros (Hp) "#HR".
    rewrite (fixpoint_interp1_eq _ (inr _)).
    (do 2 try destruct Hp as [ | Hp]). 3:destruct Hp.
    all:subst; auto. 
  Qed.

  (* The necessary resources to close the region again, except for the points to predicate, which we will store separately *)
  Definition region_open_resources W l ls p φ (v : Word) (condb : bool): iProp Σ :=
    (∃ ρ,
        sts_state_std l ρ
    ∗ ⌜std W !! l = Some ρ⌝
    ∗ ⌜ρ ≠ Revoked⌝
    ∗ ⌜(∀ g, ρ ≠ Monostatic g)⌝
    ∗ ⌜(∀ g, ρ = Static g → ∃ w, g = {[l:=w]})⌝
    ∗ ⌜if condb then True else (forall g, ρ ≠ Static g) ∧ (forall w, ρ ≠ Uninitialized w)⌝
    ∗ open_region_many (l :: ls) W
    ∗ ⌜p ≠ O⌝
    ∗ rel l p φ)%I.

  Lemma store_inr_eq {regs r p0 g0 b0 e0 a0 a' p1 g1 b1 e1 a1 storev}:
    reg_allows_storeU regs r p0 g0 b0 e0 a0 a' storev →
    read_reg_inr regs r p1 g1 b1 e1 a1 →
    p0 = p1 ∧ g0 = g1 ∧ b0 = b1 ∧ e0 = e1 ∧ a0 = a1.
  Proof.
      intros Hrar H3.
      pose (Hrar' := Hrar).
      destruct Hrar' as (Hinr0 & _). destruct H3 as [Hinr1 | Hinl1].
      * rewrite Hinr0 in Hinr1. inversion Hinr1.
        subst;auto.
      * destruct Hinl1 as [z Hinl1]. rewrite Hinl1 in Hinr0. by exfalso.
  Qed.

  (* Description of what the resources are supposed to look like after opening the region if we need to, but before closing the region up again*)
  Definition allow_store_res W r1 r2 offs (regs : Reg) pc_a (pc_p : Perm) :=
    (∃ p g b e a storev, ⌜read_reg_inr regs r1 p g b e a⌝ ∗ ⌜word_of_argument regs r2 = Some storev⌝ ∗
      match z_of_argument regs offs with
      | None => open_region pc_a W
      | Some zoffs =>
        match (a + zoffs)%a with
        | Some a' => (if decide (reg_allows_storeU regs r1 p g b e a a' storev) then
                       (if decide (a' ≠ pc_a) then
                          ∃ p' w, a' ↦ₐ [p'] w  ∗ ⌜PermFlows (promote_perm p) p'⌝ ∗ (region_open_resources W a' [pc_a] p' interpC w (a' =? a)%Z)
                        else open_region pc_a W ∗ ⌜PermFlows (promote_perm p) pc_p⌝ )
                     else open_region pc_a W)
        | None => open_region pc_a W
        end
      end)%I.

  Definition allow_store_mem W r1 r2 offs (regs : Reg) pc_a pc_p pc_w (mem : PermMem):=
    (∃ p g b e a storev, ⌜read_reg_inr regs r1 p g b e a⌝ ∗ ⌜word_of_argument regs r2 = Some storev⌝ ∗
      match z_of_argument regs offs with
      | None => ⌜mem = <[pc_a:=(pc_p,pc_w)]> ∅⌝ ∗ open_region pc_a W
      | Some zoffs =>
        match (a + zoffs)%a with
        | Some a' => (if decide (reg_allows_storeU regs r1 p g b e a a' storev) then
                       (if decide (a' ≠ pc_a) then
                          ∃ p' w, ⌜mem = <[a':=(p',w)]> (<[pc_a:=(pc_p,pc_w)]> ∅)⌝ ∗ ⌜PermFlows (promote_perm p) p'⌝
                                                                                 ∗ (region_open_resources W a' [pc_a] p' interpC w (a' =? a)%Z)
                        else ⌜mem = <[pc_a:=(pc_p,pc_w)]> ∅⌝ ∗ open_region pc_a W ∗ ⌜PermFlows (promote_perm p) pc_p⌝ )
                     else ⌜mem = <[pc_a:=(pc_p,pc_w)]> ∅⌝ ∗ open_region pc_a W)
        | None => ⌜mem = <[pc_a:=(pc_p,pc_w)]> ∅⌝ ∗ open_region pc_a W
        end
      end)%I.

  Lemma interp_hpf_eq (W : WORLD) (r : leibnizO Reg) (r1 : RegName)
        p g b e a a' pc_p pc_g pc_b pc_e pc_p' w storev:
    reg_allows_storeU (<[PC:=inr (pc_p, pc_g, pc_b, pc_e, a')]> r) r1 p g b e a a' storev
    → isU pc_p = false
    → PermFlows pc_p pc_p'
    → (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → ((fixpoint interp1) W) (r !r! r1))
        -∗ read_write_cond a' pc_p' interp
        -∗ ⌜PermFlows (promote_perm p) pc_p'⌝.
  Proof.
    destruct (decide (r1 = PC)).
    - subst r1. iIntros ([? ?] ? ?). simplify_map_eq; auto. destruct H0 as [? _]. congruence. 
    - iIntros ((Hsomer1 & Hwa & Hwb1 & Hwb2 & Hwb3 & Hloc) Hu Hfl) "Hreg Hinva".
      iDestruct ("Hreg" $! r1 n) as "Hr1". simplify_map_eq. rewrite /RegLocate Hsomer1.
      iDestruct (isU_inv_all _ a' with "Hr1") as (p'' Hfl') "#[Harel' _]"; auto.
      { solve_addr. }
      rewrite /read_write_cond. 
      iDestruct (rel_agree a' p'' pc_p' with "[$Hinva $Harel']") as "[% _]";subst;auto.
  Qed.

  Lemma create_store_res:
    ∀ (W : WORLD) (r : leibnizO Reg) (p p' : Perm)
      (g : Locality) (b e a : Addr) (r1 : RegName) (offs r2 : Z + RegName) (p0 : Perm)
      (g0 : Locality) (b0 e0 a0 : Addr)(storev : Word),
      read_reg_inr (<[PC:=inr (p, g, b, e, a)]> r) r1 p0 g0 b0 e0 a0
      → isU p = false
      → PermFlows (promote_perm p) p'
      → word_of_argument (<[PC:=inr (p, g, b, e, a)]> r) r2 = Some storev
      → (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → ((fixpoint interp1) W) (r !r! r1))
          -∗ read_write_cond a p' interp
          -∗ open_region a W
          -∗ sts_full_world W
          -∗ allow_store_res W r1 r2 offs (<[PC:=inr (p, g, b, e, a)]> r) a p'
          ∗ sts_full_world W.
  Proof.
    intros W r p p' g b e a r1 r2 offs p0 g0 b0 e0 a0 storev HVr1 Hnu Hfl Hwoa.
    iIntros "#Hreg #Hinva Hr Hsts".
    do 6 (iApply sep_exist_r; iExists _). iFrame "%".
    destruct (z_of_argument (<[PC:=inr (p, g, b, e, a)]> r) r2);[|iFrame]. 
    destruct (a0 + z)%a;[|iFrame]. 
    case_decide as Hallows.
    - case_decide as Haeq.
      + destruct Hallows as (Hrinr & Hra & Hwb1 & Hwb2 & Hwb3 & HLoc).
        assert (r1 ≠ PC) as n.
        { intros Heq;subst. destruct HVr1 as [?|[? ?] ]; simplify_map_eq;congruence. }
        simplify_map_eq.

        iDestruct ("Hreg" $! r1 n) as "Hvsrc".
        rewrite /RegLocate Hrinr.
        iDestruct (isU_inv_boundary _ a1 with "Hvsrc") as (p0' Hfl') "[Hrel' %]";[solve_addr|solve_addr|auto|].
        rewrite /read_write_cond.
        iDestruct (region_open_prepare with "Hr") as "Hr".

        destruct H as (ρ & Hρ & Hnotrevoked & Hnotmonostatic & Hstatic & Hdec).
        assert (addr_reg.min a0 e0 = a0) as Heq;[solve_addr|]. rewrite Heq in Hdec. 
        destruct ρ; try congruence.
        * iDestruct (region_open_next _ _ _ a1 p0' Temporary with "[$Hrel' $Hr $Hsts]") as (w0) "($ & Hstate' & Hr & Ha0 & % & Hfuture & #Hval)";
            auto;[intros [g1 Hcontr];done..| |].
          { apply not_elem_of_cons. split; auto. apply not_elem_of_nil. }
          iExists _,_. iFrame. iSplitR; auto. iExists Temporary. iFrame "∗ % #".
        * iDestruct (region_open_next _ _ _ a1 p0' Monotemporary with "[$Hrel' $Hr $Hsts]") as (w0) "($ & Hstate' & Hr & Ha0 & % & Hfuture & #Hval)";
            auto;[intros [g1 Hcontr];done..| |].
          { apply not_elem_of_cons. split; auto. apply not_elem_of_nil. }
          iExists _,_. iFrame. iSplitR; auto. iExists Monotemporary. iFrame "∗ % #". 
        * iDestruct (region_open_next _ _ _ a1 p0' Permanent with "[$Hrel' $Hr $Hsts]") as (w0) "($ & Hstate' & Hr & Ha0 & % & Hfuture & #Hval)";
            auto;[intros [g1 Hcontr];done..| |].
          { apply not_elem_of_cons. split; auto. apply not_elem_of_nil. }
          iExists _,_. iFrame. iSplitR; auto. iExists Permanent. iFrame "∗ % #". 
        * destruct Hstatic with g1 as [w Hw];auto.
          iDestruct (region_open_next_uninit _ w _ a1 with "[$Hrel' $Hr $Hsts]") as "($ & $ & Hstate & Ha & %)";eauto.
          { apply not_elem_of_cons. split; auto. apply not_elem_of_nil. }
          { rewrite Hρ Hw;eauto. }
          iExists _,_. iFrame. iSplitR; auto. subst. iExists _. iFrame "∗ % #". 
        * iDestruct (region_open_next_monouninit_w _ w _ a1 with "[$Hrel' $Hr $Hsts]") as "($ & $ & Hstate & Ha & %)";eauto.
          { apply not_elem_of_cons. split; auto. apply not_elem_of_nil. }
          iExists _,_;iFrame. iSplit;auto. iExists _;iFrame. iFrame "% #".
      + subst a1. iFrame. iApply (interp_hpf_eq W r r1 p0 g0 b0 e0 a0 a p g b e p' storev storev with "Hreg");eauto.
        eapply PermFlows_trans;eauto. destruct p;simpl;inversion Hnu;apply PermFlows_refl. 
    - iFrame. 
  Qed.

  Lemma store_res_implies_mem_map:
    ∀ (W : WORLD) (r : leibnizO Reg) (p' : Perm)
       (a : Addr) (w : Word) (r1 : RegName) (offs r2 : Z + RegName),
      allow_store_res W r1 r2 offs r a p'
      -∗ a ↦ₐ[p'] w
      -∗ ∃ mem0 : PermMem,
          allow_store_mem W r1 r2 offs r a p' w mem0
            ∗ ▷ ([∗ map] a0↦pw ∈ mem0, ∃ (p0 : Perm) (w0 : leibnizO Word),
                ⌜pw = (p0, w0)⌝ ∗ a0 ↦ₐ[p0] w0).
  Proof.
    intros W r p' a w r1 r2 offs.
    iIntros "HStoreRes Ha".
    iDestruct "HStoreRes" as (p1 g1 b1 e1 a1 storev) "(% & % & HStoreRes)".
    destruct (z_of_argument r r2) eqn:Hz.
    2: { iExists _. iSplitL "HStoreRes".
         + iExists p1,g1,b1,e1,a1,storev. iFrame "%".
           rewrite Hz. iFrame. eauto. 
         + iNext. by iApply memMap_resource_1. }
    destruct (a1 + z)%a eqn:Hnext. 
    2: { iExists _. iSplitL "HStoreRes".
         + iExists p1,g1,b1,e1,a1,storev. iFrame "%".
           rewrite Hz Hnext. iFrame. eauto. 
         + iNext. by iApply memMap_resource_1. }

    case_decide as Hallows.
    - case_decide as Haeq.
      ++ pose(Hallows' := Hallows). destruct Hallows as (Hrinr & Hra & Hwb & HLoc).
         iDestruct "HStoreRes" as (p'0 w0) "[HStoreCh HStoreRest]".
         iExists _.
         iSplitL "HStoreRest".
        + iExists p1,g1,b1,e1,a1,storev. iFrame "%". rewrite Hz Hnext.
          case_decide; last by exfalso. case_decide; last by exfalso.
          iExists p'0,w0. iSplitR; auto.
        + iNext.
          iApply memMap_resource_2ne; auto; iFrame.
      ++ iExists _.
         iSplitL "HStoreRes".
        + iExists p1,g1,b1,e1,a1,storev. iFrame "%". rewrite Hz Hnext.
          case_decide; last by exfalso. case_decide; first by exfalso.
          iFrame. auto.
        + iNext. by iApply memMap_resource_1.
    - iExists _.
      iSplitL "HStoreRes".
      + iExists p1,g1,b1,e1,a1,storev. iFrame "%". rewrite Hz Hnext.
        case_decide; first by exfalso. iFrame. auto.
      + iNext. by iApply memMap_resource_1.
    Qed.

  Lemma mem_map_implies_pure_conds:
    ∀ (W : WORLD) (r : leibnizO Reg) (p p' : Perm)
      (g : Locality) (b e a : Addr) (w : Word) (r1 : RegName) (offs r2 : Z + RegName)
      (mem0 : PermMem),
        p' ≠ O →
        allow_store_mem W r1 r2 offs r a p' w mem0
        -∗ ⌜mem0 !! a = Some (p', w)⌝
          ∗ ⌜allow_storeU_map_or_true r1 r2 offs r mem0⌝.
  Proof.
    iIntros (W r p p' g b e a w r1 r2 offs mem0 Hp'O) "HStoreMem".
    iDestruct "HStoreMem" as (p1 g1 b1 e1 a1 storev) "(% & % & HStoreRes)".
    rewrite /allow_storeU_map_or_true.
    destruct (z_of_argument r r2) eqn:Hz.
    2: { iDestruct "HStoreRes" as "[-> HStoreRes ]".
         iSplitR. by rewrite lookup_insert.
         iExists p1,g1,b1,e1,a1,storev. repeat iSplitR; auto. }
    destruct (a1 + z)%a eqn:Hnext.
    2: { iDestruct "HStoreRes" as "[-> HStoreRes ]".
         iSplitR. by rewrite lookup_insert.
         iExists p1,g1,b1,e1,a1,storev. repeat iSplitR; auto.
         rewrite Hnext. auto. }

    case_decide as Hallows.
    - case_decide as Haeq.
      + pose(Hallows' := Hallows). destruct Hallows' as (Hrinr & Hra & Hwb & HLoc).
        (* case_decide as Haeq. *)
        iDestruct "HStoreRes" as (p'0 w0 ->) "[% _]".
        iSplitR. rewrite lookup_insert_ne; auto. by rewrite lookup_insert.
        iExists p1,g1,b1,e1,a1,storev.
        iPureIntro. repeat split; auto. rewrite Hnext. 
        case_decide; last by exfalso.
        exists p'0,w0. simplify_map_eq. split;auto.
        eapply PermFlows_trans;eauto. destruct p1;simpl;auto;apply PermFlows_refl. 
      + subst a. iDestruct "HStoreRes" as "[-> [HStoreRes % ] ]".
        iSplitR. by rewrite lookup_insert.
        iExists p1,g1,b1,e1,a1,storev. repeat iSplitR; auto. rewrite Hnext.
        case_decide as Hdec1; last by done.
        iExists p',w. rewrite lookup_insert. iSplit;auto. iPureIntro.
        eapply PermFlows_trans;eauto. destruct p1;simpl;try apply PermFlows_refl;done.
    - iDestruct "HStoreRes" as "[-> HStoreRes ]".
      iSplitR. by rewrite lookup_insert.
      iExists p1,g1,b1,e1,a1,storev. repeat iSplitR; auto.
      rewrite Hnext. 
      case_decide as Hdec1; last by done. by exfalso.
  Qed.

  Lemma isU_weak_addrs W p g b e a a' :
    isU p -> (a' <= a)%a →
    interp W (inr (p,g,b,e,a)) -∗ interp W (inr (p,g,b,e,a')).
  Proof.
    iIntros (Hu Hle) "#Hv".
    rewrite !fixpoint_interp1_eq.
  Admitted. 
    (* destruct p;inversion Hu. *)
    (* - destruct g;try done. *)
    (*   + simpl. admit. *)
    (*     admit.  *)

  Lemma storev_interp_mono W (r : Reg) (r1 : RegName) (r2 : Z + RegName) p g b e a a' p' ρ storev:
     PermFlows (promote_perm p) p'
     → word_of_argument r r2 = Some storev
     → reg_allows_storeU r r1 p g b e a a' storev
     → std W !! a' = Some ρ
     → ((fixpoint interp1) W) (inr (p,g,b,e,a))
       -∗ monotonicity_guarantees_region ρ a' storev p' interpC.
   Proof.
     iIntros (Hpf Hwoa Hras Hststd) "HInt".
     destruct Hras as (Hrir & Hwa & Hwb & Hwb1 & Hwb2 & Hloc).
     destruct storev as [z | cap].
     - iDestruct (isU_weak_addrs with "HInt") as "HInt";eauto.
       iApply (interp_monotone_generalZ with "HInt" );auto.
       { apply andb_true_iff. split;[apply Z.leb_le|apply Z.ltb_lt];solve_addr. }
       eapply PermFlows_trans;eauto. destruct p;inversion Hwa;simpl;auto.
     - iDestruct (isU_weak_addrs with "HInt") as "HInt";eauto.
       destruct r2. cbn in Hwoa; inversion Hwoa; by exfalso.
       destruct_cap cap. cbn in Hwoa.
       destruct (r !! r0); inversion Hwoa; clear Hwoa; subst w.
       iApply (interp_monotone_generalUW with "HInt" ); eauto.
       apply andb_true_iff. split;[apply Z.leb_le|apply Z.ltb_lt];solve_addr. 
   Qed.


   Definition new_worldU W (a0 : Addr) pc_p pc_g pc_b pc_e pc_a r offs :=
     match z_of_argument (<[PC:=inr (pc_p, pc_g, pc_b, pc_e, pc_a)]> r) offs with
     | Some z =>
       match (a0 + z)%a with
       | Some a1 =>
         if (a1 =? a0)%Z
         then match std W !! a1 with
              | Some (Uninitialized _) => (<[a0:=Monotemporary]> W.1,W.2)
              | Some (Static _) => (<[a0:=Temporary]> W.1,W.2)
              | _ => W
              end
         else W
       | None => W
       end
     | None => W
     end.

  (* Note that we turn in all information that we might have on the monotonicity of the current PC value, so that in the proof of the ftlr case itself, we do not have to worry about whether the PC was written to or not when we close the last location pc_a in the region *)
   Lemma mem_map_recover_res:
    ∀ (W : WORLD) (r : Reg) (p' : Perm)
       (pc_w : Word) (r1 : RegName) (r2 offs : Z + RegName) (offz : Z) (p0 p'0 pc_p pc_p' : Perm)
       (g0 pc_g : Locality) (b0 e0 a0 a1 pc_b pc_e pc_a : Addr) (mem0 : PermMem) (oldv storev : Word) (ρ : region_type),
      word_of_argument (<[PC:=inr (pc_p, pc_g, pc_b, pc_e, pc_a)]> r) r2 = Some storev
      → z_of_argument (<[PC:=inr (pc_p, pc_g, pc_b, pc_e, pc_a)]> r) offs = Some offz (* necessary for successful store *)
      → (a0 + offz)%a = Some a1 (* necessary for successful store *)
      → (pc_p = RX ∨ pc_p = RWX ∨ pc_p = RWLX)
      → reg_allows_storeU (<[PC:=inr (pc_p, pc_g, pc_b, pc_e, pc_a)]> r) r1 p0 g0 b0 e0 a0 a1 storev
      → std W !! pc_a = Some ρ
      → mem0 !! a1 = Some (p'0, oldv) (*?*)
      → allow_store_mem W r1 r2 offs (<[PC:=inr (pc_p, pc_g, pc_b, pc_e, pc_a)]> r) pc_a pc_p' pc_w mem0
        -∗ (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → ((fixpoint interp1) W) (r !r! r1))
        -∗ ((fixpoint interp1) W) (inr(pc_p, pc_g, pc_b, pc_e, pc_a))
        -∗ ((fixpoint interp1) W) pc_w
        -∗ monotonicity_guarantees_region ρ pc_a pc_w pc_p' interpC
        -∗ ([∗ map] a0↦pw ∈ <[a1 := (p'0, storev)]> mem0, ∃ (p0 : Perm) (w0 : Word),
               ⌜pw = (p0, w0)⌝ ∗ a0 ↦ₐ[p0] w0)
        -∗ sts_full_world W
        -∗ ∃ v, open_region pc_a (new_worldU W a0 pc_p pc_g pc_b pc_e pc_a r offs)
                            ∗ sts_full_world (new_worldU W a0 pc_p pc_g pc_b pc_e pc_a r offs)
                            ∗ pc_a ↦ₐ[pc_p'] v
                            ∗ ((fixpoint interp1) (new_worldU W a0 pc_p pc_g pc_b pc_e pc_a r offs)) v
                            ∗ monotonicity_guarantees_region ρ pc_a v pc_p' interpC.
   Proof.
    intros W r p' pc_w r1 r2 offs offz p0 p'0 pc_p pc_p' g0 pc_g b0 e0 a0 a1 pc_b pc_e pc_a mem0 oldv storev ρ Hwoa Hz Hnext Hpcperm Hras Hstdst Ha0.
    iIntros "HStoreMem #Hreg #HVPCr #Hpc_w Hpcmono Hmem Hsts".
    iDestruct "HStoreMem" as (p1 g1 b1 e1 a1' storev1) "[% [% HStoreRes] ]".
    destruct (store_inr_eq Hras H) as (<- & <- &<- &<- &<-).
    rewrite Hwoa in H0; inversion H0; simplify_eq.
    rewrite /new_worldU !Hz !Hnext.

    case_decide as Hallows.
    - iAssert (((fixpoint interp1) W) (inr (p0,g0,b0,e0,a0)))%I with "[HVPCr Hreg]" as "#HVr1".
      { destruct Hras as [Hreg _]. destruct (decide (r1 = PC)).
        - subst r1. rewrite lookup_insert in Hreg. inversion Hreg. subst. 
          destruct Hallows as (_ & Hallows & _). destruct Hpcperm as [-> | [-> | -> ] ];inversion Hallows.
        - iSpecialize ("Hreg" $! r1 n). rewrite lookup_insert_ne in Hreg; last congruence. rewrite /RegLocate Hreg.
          auto. 
      }
      iAssert (((fixpoint interp1) W) storev1)%I with "[HVPCr Hreg]" as "#HVstorev1".
      { destruct storev1.
        - repeat rewrite fixpoint_interp1_eq. by cbn.
        - destruct r2. cbn in Hwoa; inversion Hwoa; by exfalso.
          destruct_cap c. cbn in Hwoa.
          destruct (<[PC:=inr (pc_p, pc_g, pc_b, pc_e, pc_a)]> r !! r0) eqn:Hrr0; inversion Hwoa; clear Hwoa; subst w.
          destruct (decide (r0 = PC)).
          + subst r0. rewrite lookup_insert in Hrr0. by inversion Hrr0.
          + iSpecialize ("Hreg" $! r0 n).  rewrite lookup_insert_ne in Hrr0; last congruence. by rewrite /RegLocate Hrr0.
      }
      case_decide as Haeq.
      + iExists pc_w.
        destruct Hallows as [Hrinr [Hwa [Hwb Hloc] ] ].
        iDestruct "HStoreRes" as (p'1 w') "[-> [% HLoadRes] ]".
        rewrite lookup_insert in Ha0; inversion Ha0; clear Ha0; subst.
        iDestruct "HLoadRes" as (ρ1) "(Hstate' & % & % & % & % & % & Hr & % & Hrel')".
        rewrite insert_insert memMap_resource_2ne; last auto. iDestruct "Hmem" as  "[Ha1 $]".
        iDestruct (storev_interp_mono with "HVr1") as "Hr1Mono";eauto.
        destruct ((a1 =? a0)%Z) eqn:Heqa. apply Z.eqb_eq,z_of_eq in Heqa as ->.
        * rewrite H1. admit. 
        * destruct H5 as [? ?].
          iDestruct (region_close_next with "[$Hr $Ha1 $Hrel' $Hstate' $HVstorev1 $Hr1Mono]") as "Hr"; eauto.
          { intros [g Hcontr]. specialize (H5 g). done. }
          { intros [g Hcontr]. specialize (H3 g). done. }
          { intros [g Hcontr]. specialize (H7 g). done. }
          { apply not_elem_of_cons; split; [auto|apply not_elem_of_nil]. }
          iDestruct (region_open_prepare with "Hr") as "$". by iFrame.
      + subst a1. iDestruct "HStoreRes" as "[-> [HStoreRes % ] ]".
        rewrite insert_insert -memMap_resource_1.
        rewrite lookup_insert in Ha0; inversion Ha0; simplify_eq.
        iExists storev1. iFrame.
        iDestruct (storev_interp_mono with "HVr1") as "Hr1Mono"; eauto.
    - by exfalso.
   Qed.














  (* TODO: move somewhere *)
  Lemma isU_inv:
    ∀ (W : leibnizO WORLD) (a' a b e : Addr) (p : Perm) (g : Locality),
      (b ≤ a' < addr_reg.min a e)%Z
      → isU p = true
      → ⊢ (interp W) (inr (p, g, b, e, a))
      → ∃ p' : Perm, ⌜PermFlows (promote_perm p) p'⌝ ∗ read_write_cond a' p' interp
                     ∧ ⌜(∃ ρ : region_type, std W !! a' = Some ρ
                                            ∧ ρ ≠ Revoked /\ (∀ g, ρ ≠ Static g) ∧ (∀ g, ρ ≠ Monostatic g) ∧ (∀ w, ρ ≠ Uninitialized w))⌝.
  Proof.
    intros. rewrite /interp fixpoint_interp1_eq /=. iIntros "H".
    assert (p = URW \/ p = URWL \/ p = URWX \/ p = URWLX) as [-> | [-> | [-> | ->] ] ] by (destruct p; simpl in H0; auto; congruence); simpl.
    - destruct g.
      + iDestruct (extract_from_region_inv with "H") as (p' ?) "[C %]";try (iExists p'; iFrame; auto);[solve_addr|].
        iSplit;auto. iPureIntro; auto. rewrite H2. eexists;eauto.
      + iDestruct "H" as "[B C]".
        iDestruct (extract_from_region_inv with "B") as (p' ?) "[D %]"; try (iExists p'; iFrame); auto.
        iSplit;auto. iPureIntro; auto. destruct H2; eexists;eauto.
      + iDestruct "H" as "[B C]".
        iDestruct (extract_from_region_inv with "B") as (p' ?) "[D %]"; try (iExists p'; iFrame); auto.
        iSplit;auto. iPureIntro; auto. destruct H2 as [? | [? | ?] ]; eexists;eauto.
    - destruct g; auto.
      iDestruct "H" as "[B C]".
      iDestruct (extract_from_region_inv with "B") as (p' ?) "[D %]"; try (iExists p'; iFrame); auto.
      iPureIntro; split;eauto. eexists;eauto.
    - destruct g.
      + iDestruct (extract_from_region_inv with "H") as (p' Hfl) "[D %]"; try (iExists p'; iFrame); auto; [solve_addr|].
        iSplit;auto. iPureIntro; auto. eexists; eauto.
      + iDestruct "H" as "[B C]".
        iDestruct (extract_from_region_inv with "B") as (p' Hfl) "[E %]"; try (iExists p'; iFrame); auto.
        iSplit;auto. iPureIntro; auto. destruct H1; eexists;eauto.
      + iDestruct "H" as "[B C]".
        iDestruct (extract_from_region_inv with "B") as (p' Hfl) "[E %]"; try (iExists p'; iFrame); auto.
        iSplit;auto. iPureIntro; auto. destruct H1 as [? | [? | ?] ]; eexists;eauto.
    - destruct g; auto.
      iDestruct "H" as "[B C]".
      iDestruct (extract_from_region_inv with "B") as (p' Hfl) "[D %]"; try (iExists p'; iFrame); auto.
      iSplit;auto. iPureIntro; simpl in H1; eexists;eauto.
  Qed.

  



















  (* Lemma region_open_next_perm' W ls l p : *)
  (*   l ∉ ls → (std_sta W) !! (countable.encode l) = Some (countable.encode Permanent) ->  *)
  (*   open_region_many ls W ∗ sts_full_world sts_std W ∗ uninitialized_cond l p -∗ *)
  (*                    ∃ v, sts_full_world sts_std W *)
  (*                         ∗ sts_state_std (countable.encode l) Permanent *)
  (*                         ∗ open_region_many (l :: ls) W *)
  (*                         ∗ l ↦ₐ[p] v *)
  (*                         ∗ ⌜p ≠ O⌝. *)
  (* Proof. *)
  (*   rewrite open_region_many_eq .  *)
  (*   iIntros (Hnin Htemp) "(Hopen & Hfull & Hun)". *)
  (*   rewrite /open_region_many_def /= /region_map_def. *)
  (*   rewrite /region_def /region. *)
  (*   iDestruct "Hopen" as (M) "(HM & % & Hpreds)". *)
  (*   destruct (proj1 (H3 (countable.encode l)) ltac:(eauto)) as [l' [X1 X2] ]. *)
  (*   eapply encode_inj in X1; subst l'. destruct X2 as [γp HX]. *)
  (*   iDestruct "Hun" as (γrel) "Hγpred". rewrite RELS_eq /RELS_def REL_eq /REL_def. *)
  (*   iDestruct (reg_in with "[$HM $Hγpred]") as %HMeq. *)
  (*   rewrite HMeq delete_list_insert; auto. *)
  (*   rewrite delete_list_delete; auto. *)
  (*   rewrite big_sepM_insert; [|by rewrite lookup_delete]. *)
  (*   iDestruct "Hpreds" as "[Hl Hpreds]". *)
  (*   iDestruct "Hl" as (ρ) "[Hstate Hl]". destruct ρ. *)
  (*   1,3,4: iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr. *)
  (*   1,2,3: rewrite Htemp in Hcontr; inversion Hcontr; apply countable.encode_inj in H5; done.     iDestruct "Hl" as (γpred' v p' ϕ) "(% & % & Hl & HX & HY & HZ)". *)
  (*   inversion H4; subst. *)
  (*   iExists v. iFrame. *)
  (*   iSplitL; auto. *)
  (*   iExists _. iFrame "∗ #". rewrite <- HMeq. auto. *)
  (* Qed. *)

  (* Lemma region_open_next_temp' W ls l p : *)
  (*   l ∉ ls → (std_sta W) !! (countable.encode l) = Some (countable.encode Temporary) ->  *)
  (*   open_region_many ls W ∗ sts_full_world sts_std W ∗ uninitialized_cond l p -∗ *)
  (*                    ∃ v, sts_full_world sts_std W *)
  (*                         ∗ sts_state_std (countable.encode l) Temporary *)
  (*                         ∗ open_region_many (l :: ls) W *)
  (*                         ∗ l ↦ₐ[p] v *)
  (*                         ∗ ⌜p ≠ O⌝. *)
  (* Proof. *)
  (*   rewrite open_region_many_eq .  *)
  (*   iIntros (Hnin Htemp) "(Hopen & Hfull & Hun)". *)
  (*   rewrite /open_region_many_def /= /region_map_def. *)
  (*   rewrite /region_def /region. *)
  (*   iDestruct "Hopen" as (M) "(HM & % & Hpreds)". *)
  (*   destruct (proj1 (H3 (countable.encode l)) ltac:(eauto)) as [l' [X1 X2] ]. *)
  (*   eapply encode_inj in X1; subst l'. destruct X2 as [γp HX]. *)
  (*   iDestruct "Hun" as (γrel) "Hγpred". rewrite RELS_eq /RELS_def REL_eq /REL_def. *)
  (*   iDestruct (reg_in with "[$HM $Hγpred]") as %HMeq. *)
  (*   rewrite HMeq delete_list_insert; auto. *)
  (*   rewrite delete_list_delete; auto. *)
  (*   rewrite big_sepM_insert; [|by rewrite lookup_delete]. *)
  (*   iDestruct "Hpreds" as "[Hl Hpreds]". *)
  (*   iDestruct "Hl" as (ρ) "[Hstate Hl]". destruct ρ. *)
  (*   2,3,4: iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr. *)
  (*   2,3,4: rewrite Htemp in Hcontr; inversion Hcontr; apply countable.encode_inj in H5; done.     iDestruct "Hl" as (γpred' v p' ϕ) "(% & % & Hl & HX & HY & HZ)". *)
  (*   inversion H4; subst. *)
  (*   iExists v. iFrame. *)
  (*   iSplitL; auto. *)
  (*   iExists _. iFrame "∗ #". rewrite <- HMeq. auto. *)
  (* Qed. *)

  Lemma region_open_next_uninit' W ls l p w :
    l ∉ ls → (std W) !! l = Some (Static {[l:=w]}) ->
    open_region_many ls W ∗ sts_full_world W ∗ read_write_cond l p interp -∗
                            sts_full_world W
                          ∗ sts_state_std l (Static {[l:=w]})
                          ∗ open_region_many (l :: ls) W
                          ∗ l ↦ₐ[p] w
                          ∗ ⌜p ≠ O⌝.
  Proof.
    rewrite open_region_many_eq .
    iIntros (Hnin Htemp) "(Hopen & Hfull & Hun)".
    rewrite /open_region_many_def /= /region_map_def.
    rewrite /region_def /region.
    iDestruct "Hopen" as (M Mρ) "(HM & % & % & Hpreds)".
    assert (is_Some (M !! l)) as [γp HX].
    { apply elem_of_gmap_dom. rewrite -H. apply elem_of_gmap_dom. eauto. }
    rewrite /read_write_cond rel_eq /rel_def.
    iDestruct "Hun" as (γrel) "[Hγpred BB]". rewrite RELS_eq /RELS_def REL_eq /REL_def.
    iDestruct (reg_in with "[$HM $Hγpred]") as %HMeq.
    rewrite HMeq delete_list_insert; auto.
    rewrite delete_list_delete; auto.
    rewrite big_sepM_insert; [|by rewrite lookup_delete].
    iDestruct "Hpreds" as "[Hl Hpreds]".
    iDestruct "Hl" as (ρ) "[ % [Hstate Hl] ]". destruct ρ.
    1,2,3,4: iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
    1,2,3,4: try (rewrite Htemp in Hcontr; by inversion Hcontr).
    iDestruct "Hl" as (γpred p0 φ Heq Hpers) "[#Hsaved Hl]". inversion Heq.
    iDestruct "Hl" as (v Hlookup Hneq) "[Hl _]". rewrite Htemp in Hcontr. inversion Hcontr. subst g.
    rewrite lookup_insert in Hlookup. inversion Hlookup.
    iFrame.
    repeat iSplitL; auto.
    iExists _,Mρ. iFrame "∗ #". subst. rewrite -HMeq.
    repeat iSplit;auto.
    iApply (region_map_delete_singleton with "Hpreds");eauto.
  Qed.

  Lemma region_open_next' W ls l ρ p:
    ρ <> Revoked ∧ (forall m, ρ = Static m -> (∃ w, m = {[l:=w]})) ->
    l ∉ ls → (std W) !! l = Some ρ ->
    open_region_many ls W ∗ sts_full_world W ∗ read_write_cond l p interp -∗
                     ∃ v, sts_full_world W
                          ∗ sts_state_std l ρ
                          ∗ open_region_many (l :: ls) W
                          ∗ l ↦ₐ[p] v
                          ∗ ⌜p ≠ O⌝.
  Proof.
    iIntros ([Hnotrevoked Hnotstatic] Hnotin Hstd) "[A [B C]]". destruct ρ; try congruence.
    - destruct (pwl p) eqn:Hpwl.
      + iDestruct (region_open_next_temp_pwl with "[$A $B $C]") as "X"; auto.
        iDestruct "X" as (v) "[A [B [C [D [E F]]]]]".
        iExists v. iFrame.
      + iDestruct (region_open_next_temp_nwl with "[$A $B $C]") as "X"; auto.
        iDestruct "X" as (v) "[A [B [C [D [E F]]]]]".
        iExists v. iFrame.
    - iDestruct (region_open_next_perm with "[$A $B $C]") as "X"; auto.
      iDestruct "X" as (v) "[A [B [C [D [E F]]]]]".
      iExists v. iFrame.
    - destruct Hnotstatic with g as [w Hw];auto. subst g. iExists w.
      iApply region_open_next_uninit'; eauto; iFrame.
  Qed.

  Lemma isU_limit_inv:
    ∀ (W : leibnizO WORLD) (a b e : Addr) (p : Perm) (g : Locality),
      (b ≤ a < e)%Z ->
      isU p = true ->
      (interp W) (inr (p, g, b, e, a)) -∗
      ∃ p' : Perm,
        ⌜PermFlows (promote_perm p) p'⌝ ∗
         read_write_cond a p' interp ∧
        ⌜(∃ ρ : region_type, std W !! a = Some ρ
                             ∧ ρ ≠ Revoked ∧ (forall m, ρ = Static m -> (∃ w, m = {[a:=w]})))⌝.
  Proof.
    intros. rewrite /interp fixpoint_interp1_eq /=. iIntros "H".
    assert (p = URW \/ p = URWL \/ p = URWX \/ p = URWLX) as [-> | [-> | [-> | ->] ] ] by (destruct p; simpl in H0; auto; congruence); simpl.
    - destruct g.
      + iDestruct (extract_from_region_inv with "H") as (p' ?) "[C %]"; eauto.
        iExists p'. iSplit;auto. simpl. iFrame. iPureIntro. eexists. repeat split;eauto. done.
      + iDestruct "H" as "[B C]".
        iDestruct (extract_from_region_inv with "C") as (p' ?) "[D %]"; try (iExists p'; iSplit;auto;iFrame); eauto.
        split;auto;solve_addr.
        iPureIntro; destruct H2 as [-> | [-> | [ ? -> ] ] ]; eexists;repeat split;eauto; try done.
        intros m Hm. inversion Hm. exists x. auto.
    - destruct g; auto.
      iDestruct "H" as "[B C]".
      iDestruct (extract_from_region_inv with "C") as (p' ?) "[D %]"; try (iExists p'; iSplit;auto;iFrame); eauto.
      split; eauto; solve_addr.
      iPureIntro; eauto. destruct H2 as [-> | [? ->] ]; eexists;repeat split;eauto;try done.
      intros m Hm; inversion Hm. eauto.
    - destruct g.
      + iDestruct (extract_from_region_inv with "H") as (p' ?) "[D %]"; try (iExists p'; iSplit;auto;iFrame);auto.
        iPureIntro. eexists;repeat split;eauto; try done.
      + iDestruct "H" as "[B C]".
        iDestruct (extract_from_region_inv with "C") as (p' ?) "[E %]"; try (iExists p'; iSplit;auto;iFrame);auto.
        split; eauto; solve_addr.
        iPureIntro; auto. destruct H2 as [-> | [-> | [? ->] ] ]; eexists;repeat split;eauto; try done.
        intros m Hm; inversion Hm;eauto.
    - destruct g; auto.
      iDestruct "H" as "[B D]".
      iDestruct (extract_from_region_inv with "D") as (p' ?) "[E %]"; try (iExists p'; iSplit;auto;iFrame); eauto.
      split; eauto; solve_addr.
      iPureIntro; auto. destruct H2 as [-> | [? ->] ]; eexists;repeat split;eauto; try done.
      intros m Hm; inversion Hm;eauto.
  Qed.

  Definition region_open_resources W l ls p φ v (bl : bool): iProp Σ :=
    (∃ ρ,
     sts_state_std l ρ
    ∗ ⌜ρ ≠ Revoked ∧ (forall m, ρ ≠ Static m)⌝
    ∗ open_region_many (l :: ls) W
    ∗ ⌜p ≠ O⌝
    ∗ (if bl then monotonicity_guarantees_region ρ v p φ ∗ φ (W, v)
       else ▷ monotonicity_guarantees_region ρ v p φ ∗  ▷ φ (W, v) )
    ∗ rel l p φ)%I.

  Definition region_open_resources_uninit W l ls p (bl : bool): iProp Σ :=
    (∃ ρ,
     sts_state_std l ρ
    ∗ ⌜ρ ≠ Revoked ∧ (forall m, ρ = Static m -> (∃ w, m = {[l:=w]}))⌝
    ∗ open_region_many (l :: ls) W
    ∗ ⌜p ≠ O⌝
    ∗ read_write_cond l p interp)%I.

  (* TODO: move upstream to Iris ?*)
  Instance if_persistent {PROP:bi} P Q (b: bool):
    Persistent P ->
    Persistent Q ->
    Persistent (PROP := PROP) (if b then P else Q).
  Proof.
    intros; destruct b; auto.
  Qed.

  (* TODO: move into logrel.v *)
  (* Quality of life lemma *)
  Global Instance future_world_pure g W W':
    IntoPure (@future_world Σ g W W')
             (match g with Global => related_sts_priv_world W W' | Local => related_sts_pub_world W W' end).
  Proof. red; intros. destruct g; auto. Qed.

  Lemma region_close_next_uninit_pwl W ls l φ p w v `{forall Wv, Persistent (φ Wv)}:
    l ∉ ls ->
    pwl p = true →
    sts_state_std l (Static {[l:=w]})
    ∗ open_region_many (l::ls) W
    ∗ l ↦ₐ[p] v
    ∗ ⌜p ≠ O⌝
    ∗ future_pub_mono φ v
    ∗ ▷ φ (W,v) (* Maybe φ (<l[ l := Temporary, (Rpub, Rpriv) ]l> W, v) *)
    ∗ rel l p φ
    ∗ sts_full_world W
    ==∗ open_region_many ls (<s[ l := Temporary ]s> W) ∗ sts_full_world (<s[ l := Temporary ]s> W).
  Proof.
    rewrite open_region_many_eq rel_eq /open_region_many_def /rel_def /region_def
            REL_eq RELS_eq /RELS_def /REL_def.
    iIntros (Hnin Hpwl) "(Hstate & Hreg_open & Hl & % & #Hmono & Hφ & #Hrel & Hfull)".
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M Mρ) "(HM & % & % & Hpreds)".
    iDestruct (sts_full_state_std with "Hfull Hstate") as "%".
    iDestruct (sts_update_std with "Hfull Hstate") as ">[Hfull Hstate]".
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    iModIntro. iSplitR "Hfull".
    { iDestruct (big_sepM_insert _ (delete l (delete_list ls M)) l with "[-HM]") as "Hmap_def";
        first by rewrite lookup_delete.
      { simpl.
        iDestruct (region_map_insert_nonstatic Temporary with "Hpreds") as "Hpreds";auto.
        iFrame. iExists Temporary. iFrame.
        iSplit;[iPureIntro;apply lookup_insert|].
        iExists γpred, p, _. iFrame "∗ #". repeat iSplitR; auto.
        iExists v. rewrite Hpwl. auto. }
      assert (Hpub: related_sts_pub_world W (<s[l:=Temporary]s>W)).
      { eapply (uninitialized_related_sts_pub_world l W); eauto. }
      iDestruct (region_map_monotone _ _ _ _ Hpub with "Hmap_def") as "HMdef"; eauto.
      iExists M,(<[l:=Temporary]>Mρ); iFrame.
      assert (l ∈ dom (gset Addr) M) as Hin.
      { rewrite -H1. apply elem_of_gmap_dom. eauto. }
      repeat rewrite dom_insert_L.
      repeat iSplit;[iPureIntro..|];[rewrite H1;set_solver|rewrite H2;set_solver|].
      rewrite -delete_list_delete;auto. rewrite -delete_list_insert; auto. rewrite -HMeq.
      rewrite delete_list_insert; auto. }
    iFrame.
  Qed.

  Lemma region_close_next_uninit_nwl W ls l φ p w v `{forall Wv, Persistent (φ Wv)}:
    l ∉ ls ->
    pwl p = false →
    sts_state_std l (Static {[l:=w]})
    ∗ open_region_many (l::ls) W
    ∗ l ↦ₐ[p] v
    ∗ ⌜p ≠ O⌝
    ∗ future_priv_mono φ v
    ∗ ▷ φ (W,v) (* Maybe φ (<l[ l := Temporary, (Rpub, Rpriv) ]l> W, v) *)
    ∗ rel l p φ
    ∗ sts_full_world W
    ==∗ open_region_many ls (<s[ l := Temporary ]s> W) ∗ sts_full_world (<s[ l := Temporary ]s> W).
  Proof.
    rewrite open_region_many_eq rel_eq /open_region_many_def /rel_def /region_def
            REL_eq RELS_eq /RELS_def /REL_def.
    iIntros (Hnin Hpwl) "(Hstate & Hreg_open & Hl & % & #Hmono & Hφ & #Hrel & Hfull)".
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M Mρ) "(HM & % & % & Hpreds)".
    iDestruct (sts_full_state_std with "Hfull Hstate") as "%".
    iDestruct (sts_update_std with "Hfull Hstate") as ">[Hfull Hstate]".
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    iModIntro. iSplitR "Hfull".
    { iDestruct (big_sepM_insert _ (delete l (delete_list ls M)) l with "[-HM]") as "Hmap_def";
        first by rewrite lookup_delete.
      { simpl.
        iDestruct (region_map_insert_nonstatic Temporary with "Hpreds") as "Hpreds";auto.
        iFrame. iExists Temporary. iFrame.
        iSplit;[iPureIntro;apply lookup_insert|].
        iExists γpred, p, _. iFrame "∗ #". repeat iSplitR; auto.
        iExists v. rewrite Hpwl. auto. }
      assert (Hpub: related_sts_pub_world W (<s[l:=Temporary]s>W)).
      { eapply (uninitialized_related_sts_pub_world l W); eauto. }
      iDestruct (region_map_monotone _ _ _ _ Hpub with "Hmap_def") as "HMdef"; eauto.
      iExists M,(<[l:=Temporary]>Mρ); iFrame.
      assert (l ∈ dom (gset Addr) M) as Hin.
      { rewrite -H1. apply elem_of_gmap_dom. eauto. }
      repeat rewrite dom_insert_L.
      repeat iSplit;[iPureIntro..|];[rewrite H1;set_solver|rewrite H2;set_solver|].
      rewrite -delete_list_delete;auto. rewrite -delete_list_insert; auto. rewrite -HMeq.
      rewrite delete_list_insert; auto. }
    iFrame.
  Qed.

  Lemma region_close_next_uninit W ls l φ p w v `{forall Wv, Persistent (φ Wv)}:
    l ∉ ls ->
    sts_state_std l (Static {[l:=w]})
    ∗ open_region_many (l::ls) W
    ∗ l ↦ₐ[p] v
    ∗ ⌜p ≠ O⌝
    ∗ (if pwl p then future_pub_mono else future_priv_mono) φ v
    ∗ ▷ φ (W,v) (* Maybe φ (<l[ l := Temporary, (Rpub, Rpriv) ]l> W, v) *)
    ∗ rel l p φ
    ∗ sts_full_world W
    ==∗ open_region_many ls (<s[ l := Temporary ]s> W) ∗ sts_full_world (<s[ l := Temporary ]s> W).
  Proof.
    intros Hnotin. destruct (pwl p) eqn:Hpwl.
    - iApply region_close_next_uninit_pwl; auto.
    - iApply region_close_next_uninit_nwl; auto.
  Qed.

  Global Instance exi_uninit_eqdec l : Decision (∃ w : leibnizO Word, ρ' = Static {[l:=w]}).
  Proof.
    intros ρ; destruct ρ;[right|right|right|];[intros [? ?];done..|].
    destruct (g !! l) eqn:Hsome;[|right];[|intros [? ?];simplify_map_eq].
    destruct (decide (g = {[l:=w]}));[left|right];subst;eauto. intros [? ?]. simplify_map_eq.
  Qed.

  Lemma storeU_case (W : WORLD) (r : leibnizO Reg) (p p' : Perm) (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (rdst : RegName) (offs rsrc : Z + RegName):
    ftlr_instr W r p p' g b e a w (StoreU rdst offs rsrc) ρ.
  Proof.
    intros Hp Hsome i Hbae Hfp Hpwl Hregion [Hnotrevoked Hnotstatic] HO Hi.
    iIntros "#IH #Hinv #Hreg #Hinva Hmono #Hw Hsts Hown".
    iIntros "Hr Hstate Ha HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.

    assert (Hsome': forall x, is_Some (<[PC:=inr (p, g, b, e, a)]> r !! x)).
    { intros. destruct (reg_eq_dec x PC).
      - subst x. rewrite lookup_insert; eauto.
      - rewrite lookup_insert_ne; auto. }
    destruct (Hsome' rdst) as [wdst Hrdst].
    iDestruct (region_open_prepare with "Hr") as "Hr".
    assert (Hwsrc: exists wsrc, word_of_argument (<[PC:=inr (p, g, b, e, a)]> r) rsrc = Some wsrc).
    { destruct rsrc; eauto.
      simpl; eapply Hsome'. }
    destruct Hwsrc as [wsrc Hwsrc].

    iAssert (∃ (mem: gmap Addr (Perm * Word)),
                ⌜let wx := <[PC:=inr (p, g, b, e, a)]> r !! rdst in
                match wx with
                | Some (inr (px, gx, bx, ex, ax)) =>
                  if isU px && canStoreU px wsrc
                  then let moffs := z_of_argument (<[PC:=inr (p, g, b, e, a)]> r) offs in
                       match moffs with
                       | Some zoffs =>
                         let ma' := verify_access (StoreU_access bx ex ax zoffs) in
                         match ma' with
                         | Some a' =>
                           let mpw := mem !! a' in
                           match mpw with
                           | Some (p'', w') => PermFlows (promote_perm px) p''
                           | None => False
                           end
                         | None => True
                         end
                       | None => True
                       end
                  else True
                | _ => True
                end⌝ ∗
                (▷ let wx := <[PC:=inr (p, g, b, e, a)]> r !! rdst in
                match wx with
                | Some (inr (px, gx, bx, ex, ax)) =>
                  if isU px && canStoreU px wsrc
                  then let moffs := z_of_argument (<[PC:=inr (p, g, b, e, a)]> r) offs in
                       match moffs with
                       | Some zoffs =>
                         let ma' := verify_access (StoreU_access bx ex ax zoffs) in
                         match ma' with
                         | Some a' =>
                           if addr_eq_dec ax a' then
                             let mpw := mem !! a' in
                             match mpw with
                             | Some (p'', w') =>
                               ⌜mem = if addr_eq_dec a a' then (<[a:=(p'',w)]> ∅) else <[a:=(p',w)]> (<[a':=(p'',w')]> ∅)⌝ ∗ sts_full_world W ∗ if addr_eq_dec a a' then open_region_many [a] W else region_open_resources_uninit W a' [a] p'' true
                             | None => ⌜False⌝
                             end
                           else
                             let mpw := mem !! a' in
                             match mpw with
                             | Some (p'', w') =>
                               ⌜mem = if addr_eq_dec a a' then (<[a:=(p'',w)]> ∅) else <[a:=(p',w)]> (<[a':=(p'',w')]> ∅)⌝ ∗ sts_full_world W ∗ if addr_eq_dec a a' then open_region_many [a] W else region_open_resources W a' [a] p'' interpC w' true
                             | None => ⌜False⌝
                             end
                         | None => True
                         end
                       | None => True
                       end
                  else True
                | _ => True
                end) ∗ ([∗ map] a↦pw ∈ mem, ∃ p w, ⌜pw = (p,w)⌝ ∗ a ↦ₐ[p] w) ∗ ⌜mem !! a = Some (p', w)⌝)%I
        with "[Ha Hsts Hr]" as "H".
    { rewrite Hrdst. destruct wdst; auto.
      - iDestruct (memMap_resource_1 with "Ha") as "H".
        iExists _; iFrame; auto. rewrite lookup_insert; auto.
      - destruct_cap c. destruct (isU c && canStoreU c wsrc) eqn:HisU.
        + destruct (z_of_argument (<[PC:=inr (p, g, b, e, a)]> r) offs) eqn:Hzof.
          * destruct (verify_access (StoreU_access c2 c1 c0 z)) eqn:Hver.
            -- apply andb_true_iff in HisU. destruct HisU as [HisU Hcan].
               assert (Hdstne: rdst <> PC).
               { red; intros; subst rdst.
                 rewrite lookup_insert in Hrdst. inv Hrdst.
                 destruct Hp as [-> | [-> | [-> ->] ] ]; simpl in HisU; inv HisU. }
               iDestruct ("Hreg" $! rdst Hdstne) as "Hinvdst"; auto.
               rewrite lookup_insert_ne in Hrdst; auto.
               rewrite /RegLocate Hrdst.
               eapply verify_access_spec in Hver.
               destruct Hver as [HA [HB [HC HD] ] ].
               destruct (addr_eq_dec c0 a0).
               ++ (* Uninitialized stuff, HERE BE DRAGONS *)
                  subst c0. destruct (addr_eq_dec a a0).
                  ** subst a0. iDestruct (memMap_resource_1 with "Ha") as "H".
                     iExists _; iFrame; auto.
                     rewrite lookup_insert; auto.
                     iSplitR; iFrame; auto.
                     iDestruct (isU_limit_inv _ a with "Hinvdst") as "H"; auto.
                     iDestruct "H" as (p'') "[% [Hun %]]".
                     iAssert (⌜p' = p''⌝%I) as "%".
                     { iDestruct (rel_agree with "[Hinva Hun]") as "[% A]".
                       iSplit; [iExact "Hinva"| iExact "Hun"]. auto. }
                     subst p'. iPureIntro. auto.
                  ** iDestruct (isU_limit_inv _ a0 with "Hinvdst") as "H"; auto.
                     iDestruct "H" as (p'') "[% [Hun %]]".
                     destruct H0 as [ρ' [X [Y Z] ] ].
                     iDestruct (region_open_next' with "[$Hsts $Hr]") as "HH"; eauto.
                     { apply not_elem_of_cons. split; eauto.
                       apply not_elem_of_nil. }
                     iDestruct "HH" as (wa0) "(Hsts & Hstate & Hr & Ha0 & %)".
                     iDestruct (memMap_resource_2ne with "[$Ha $Ha0]") as "H"; auto.
                     iExists (<[a:=(p', w)]> (<[a0:=(_, wa0)]> ∅)).
                     rewrite lookup_insert_ne; auto. rewrite lookup_insert.

                     iFrame. iSplitR; auto.
                     iSplitL; [iSplitR;auto|].
                     iExists _. iFrame. repeat iSplit;auto.
                     iFrame "∗ #"; auto. rewrite lookup_insert; auto.
               ++ iDestruct (isU_inv _ a0 with "Hinvdst") as "H"; auto.
                  { split; solve_addr. }
                  iDestruct "H" as (p'') "[% [X %]]".
                  destruct (addr_eq_dec a a0).
                  ** subst a0. iDestruct (memMap_resource_1 with "Ha") as "H".
                     iExists _; iFrame; auto.
                     rewrite lookup_insert; auto.
                     iFrame. iSplitR; auto.
                     iAssert (⌜p' = p''⌝)%I as %Hpeq.
                     { rewrite /read_write_cond.
                       iDestruct (rel_agree a p' p'' with "[$Hinva $X]") as "[$ A]". }
                     subst p'. iPureIntro. auto.
                  ** destruct H0 as [ρ' [X [Y Z ] ] ].
                     iDestruct (region_open_next with "[$Hsts $Hr]") as "HH"; eauto.
                     { intros [g' Hcontr]. subst. specialize (Z g'). contradiction. }
                     { apply not_elem_of_cons. split; auto.
                       apply not_elem_of_nil. }
                     iDestruct "HH" as (w') "(Hsts & Hstate & Hr & Ha' & % & Hmono & HX)".
                     iDestruct (memMap_resource_2ne with "[$Ha $Ha']") as "H"; auto.
                     iExists (<[a:=(p', w)]> (<[a0:=(p'', w')]> ∅)).
                     rewrite lookup_insert_ne; auto. rewrite lookup_insert.
                     iFrame. iSplitR; auto.
                     iSplitL; auto. iNext. iSplitR; auto.
                     iExists ρ'. iFrame; auto. rewrite lookup_insert; auto.
            -- iDestruct (memMap_resource_1 with "Ha") as "H".
               iExists _; iFrame; auto. rewrite lookup_insert; auto.
          * iDestruct (memMap_resource_1 with "Ha") as "H".
            iExists _; iFrame; auto. rewrite lookup_insert; auto.
        + iDestruct (memMap_resource_1 with "Ha") as "H".
          iExists _; iFrame; auto. rewrite lookup_insert; auto. }

    iDestruct "H" as (mem) "[% [A [B %]]]".
    iApply (wp_storeU with "[Hmap B]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq. intros rr _.
      apply elem_of_gmap_dom. rewrite lookup_insert_is_Some'; eauto. }
    { rewrite Hrdst. rewrite Hrdst in H. destruct wdst; auto.
      destruct_cap c. destruct (isU c && canStoreU c wsrc); auto.
      destruct (z_of_argument (<[PC:=inr (p, g, b, e, a)]> r) offs); auto.
      destruct (verify_access (StoreU_access c2 c1 c0 z)); auto.
      destruct (mem !! a0); auto. destruct p0.
      eapply PermFlows_trans; eauto. destruct c; econstructor. }
    { iFrame. }
    iNext. iIntros (r' mem' v) "[% [B C]]".
    inv H1.

    { rewrite Hrdst in H2. inv H2. rewrite Hwsrc in H3; inv H3.
      rewrite Hrdst H4 H5 H6 H7 /=.
      rewrite Hrdst H4 H5 H6 H7 /= in H.
      iAssert (((fixpoint interp1) W) w0) as "#Hw0".
      { rewrite /word_of_argument in Hwsrc.
        destruct rsrc; inv Hwsrc.
        - rewrite !fixpoint_interp1_eq /=; auto.
        - destruct (reg_eq_dec PC r0).
          + subst r0. rewrite lookup_insert in H2; inv H2.
            rewrite (fixpoint_interp1_eq W (inr _)) /=.
            iAssert (□ exec_cond W b e g p (fixpoint interp1))%I as "HinvPC".
            { iModIntro. rewrite /exec_cond.
              iIntros (a'' r'' W'' Hin) "#Hfuture".
              iNext. rewrite /interp_expr /=.
              iIntros "[[Hmap Hreg'] [Hfull [Hx [Hsts Hown]]]]".
              iSplitR; eauto.
              iApply ("IH" with "[Hmap] [Hreg'] [Hfull] [Hx] [Hsts] [Hown]"); iFrame "#"; eauto.
              iModIntro. (* iExists p'. iSplitR; auto. *) simpl.
              iDestruct "Hfuture" as %Hfuture.
              iApply (big_sepL_mono with "Hinv"); intros; simpl.
              iIntros "H". iDestruct "H" as (? ?) "[HA %]". iExists _; iSplit;eauto. iFrame. iPureIntro.
              destruct (pwl p) eqn:Hpwlp.
              - eapply region_state_pwl_monotone; eauto.
                destruct Hp as [-> | [-> | [-> ->] ] ]; simpl in Hpwlp; try congruence.
              - destruct g; [eapply region_state_nwl_monotone_nl; eauto| eapply region_state_nwl_monotone; eauto].
            }
            destruct Hp as [-> | [-> | [-> ->] ] ]; iFrame "#"; auto.
          + rewrite lookup_insert_ne in H2; auto.
            iDestruct ("Hreg" $! r0 ltac:(auto)) as "HX"; auto.
            rewrite /RegLocate H2. auto. }
      assert (Hnedst: rdst <> PC).
      { red; intro; subst rdst. rewrite lookup_insert in Hrdst.
        inv Hrdst. destruct Hp as [-> | [-> | [-> ->] ] ]; simpl in H4; inv H4. }
      iDestruct ("Hreg" $! rdst Hnedst) as "Hwdst".
      rewrite lookup_insert_ne in Hrdst; auto.
      rewrite /RegLocate Hrdst.
      iAssert (|==> ∃ W', region W' ∗ ⌜related_sts_pub_world W W'⌝ ∗ sts_full_world W' ∗ if addr_eq_dec a0 a' then match (a0 + 1)%a with | Some a'' => ((fixpoint interp1) W') (inr (p0, g0, b0, e0, a'')) | None => True end else True)%I with "[A B Hmono Hstate]" as ">HW".
      { destruct (addr_eq_dec a0 a').
        - subst a0. destruct (a' + 1)%a as [a''|] eqn:Hap1; try tauto.
          destruct (mem !! a') as [(p'', w'')|]; auto.
          iDestruct "A" as "[% [Hsts A]]".
          destruct (addr_eq_dec a a').
          + iModIntro; subst a'; subst mem.
            iDestruct (region_open_prepare with "A") as "A".
            rewrite insert_insert.
            iDestruct (memMap_resource_1 with "B") as "B".
            inv H8. rewrite lookup_insert in H0; inv H0.
            iDestruct (region_close _ _ (λ Wv : (WORLD * Word), interp Wv.1 Wv.2)
                         with "[$A $B $Hstate Hmono]") as "B"; eauto.
            { destruct ρ; auto; congruence. }
            { iFrame "#". iSplitR; auto.
              destruct (decide (ρ = Temporary ∧ pwl p' = true)).
              - rewrite /future_pub_mono /=. iModIntro.
                iIntros (W1 W2) "% #A".
                iApply interp_monotone; auto.
              - rewrite /future_priv_mono /=. iModIntro.
                iIntros (W1 W2) "% #A". iApply (interp_monotone_nl with "[] [] A"); auto.
                destruct w0; auto.
                eapply not_and_r in n. destruct_cap c.
                simpl. destruct c3; auto. simpl in H5.
                destruct (pwlU p0) eqn:HwplU; intros; try congruence.
                destruct n.
                * iAssert (⌜g0 = Local⌝)%I as %->.
                  { rewrite (fixpoint_interp1_eq W (inr (p0, _, _, _, _))).
                    destruct p0; simpl in HwplU; try congruence; destruct g0; simpl; auto. }
                  rewrite (fixpoint_interp1_eq W (inr (p0, _, _, _, _))).
                  iAssert (⌜region_state_U_pwl W a⌝)%I as %Hρ.
                  { destruct p0; simpl in H,H4,H5,H6,HwplU; try congruence.
                    - simpl. iDestruct "Hwdst" as "[YA YB]".
                      destruct (proj1 (verify_access_spec _ _) H7) as (A & B & C & D).
                      iDestruct (extract_from_region_inv with "YB") as (pp ?) "[E %]"; auto.
                      split; try solve_addr.
                    - simpl. iDestruct "Hwdst" as "[YA YC]".
                      destruct (proj1 (verify_access_spec _ _) H7) as (A & B & C & D).
                      iDestruct (extract_from_region_inv with "YC") as (pp ?) "[E %]"; auto.
                      split; try solve_addr. }
                  destruct Hρ as [Hρ | Hρ]; rewrite Hregion in Hρ; inversion Hρ; try subst ρ; congruence.
                * assert (HpwlU2: pwlU p' = true).
                  { destruct p0; simpl in H6; simpl in HwplU; try congruence; destruct p'; rewrite /PermFlows in H; inv H; simpl in H0; try congruence; reflexivity. }
                  destruct Hp as [-> | [-> | [-> ->] ] ]; destruct p'; simpl in HpwlU2; simpl in H0; try congruence; inv Hfp. }
            iExists W. iFrame. iSplitR.
            * iPureIntro.
              rewrite /related_sts_pub_world; eapply related_sts_pub_refl_world.
            * rewrite !(fixpoint_interp1_eq W (inr (p0,_,_,_,_))) !interp1_eq.
              destruct (perm_eq_dec p0 O); [subst p0; simpl in H4; congruence|].
              destruct (perm_eq_dec p0 E); [subst p0; simpl in H4; congruence|].
              iDestruct "Hwdst" as "[A1 [% A4]]".
              rewrite H4. iFrame "%".
              destruct g0; simpl; iFrame "#". eapply verify_access_spec in H7.
              destruct H7 as [A1 [A2 [A3 A4] ] ].
              replace (addr_reg.max b0 a) with a by solve_addr.
              replace (addr_reg.min a e0) with a by solve_addr.
              replace (addr_reg.min a'' e0) with a'' by solve_addr.
              iSplit.
              { rewrite (isWithin_region_addrs_decomposition a a'' b0 a''); [|solve_addr].
                iApply big_sepL_app. iFrame "#".
                iApply big_sepL_app.
                replace (region_addrs a'' a'') with (@nil Addr) by (rewrite /region_addrs region_size_0 /=; auto; solve_addr).
                iSplitL.
                - replace (region_addrs a a'') with (a::nil).
                  + iApply big_sepL_cons. iSplitL; [|iApply big_sepL_nil; auto].
                    iDestruct (extract_from_region_inv a e0 a with "A4") as (pp ?) "[X1 %]"; [solve_addr|].
                    iExists pp. iSplit;auto. iSplitL; auto.
                    iPureIntro; auto.
                    destruct (pwlU p0) eqn:Hp0.
                    { rewrite /region_state_U_pwl in H2. destruct H2; auto.
                      destruct H2.
                      eelim Hnotstatic. congruence. }
                    { rewrite /region_state_U_pwl in H2. destruct H2; auto.
                      destruct H2; auto. destruct H2. eelim Hnotstatic. congruence. }
                  + rewrite /region_addrs /region_size /=.
                    replace (a'' - a)%Z with 1%Z by solve_addr.
                    simpl. auto.
                - iApply big_sepL_nil; auto. }
              { replace (addr_reg.max b0 a'') with a'' by solve_addr.
                iApply (big_sepL_submseteq with "A4").
                rewrite (region_addrs_decomposition a a e0); [|solve_addr].
                replace ^(a + 1)%a with a'' by solve_addr.
                eapply submseteq_inserts_l.
                eapply submseteq_cons. auto. }
          + subst mem. iDestruct "A" as (ρ') "[A1 [ [% %] [A2 [% #A3]]]]".
            iDestruct (sts_full_state_std with "[$Hsts] [$A1]") as "%".
            (* destruct (region_type_EqDecision ρ' Uninitialized). *)
            destruct (decide (exists w, ρ' = Static {[a':=w]})).
            * destruct e1 as [? e1]. subst ρ'. rewrite -(insert_delete _ a' (p'0, w0)).
              rewrite delete_insert_ne; auto. rewrite delete_insert; auto.
              iDestruct (memMap_resource_2ne with "B") as "[B1 B2]"; auto. inv H8.
              iDestruct (region_close_next_uninit with "[$A1 $A2 $B1 $A3 $Hw0 $Hsts]") as "HX".
              { eapply not_elem_of_cons; split; auto.
                eapply not_elem_of_nil. }
              { iSplitR; auto. simpl. destruct (pwl p'0) eqn:Hpwl'.
                - rewrite /future_pub_mono /=. iModIntro.
                  iIntros (W1 W2) "% #A".
                  iApply interp_monotone; auto.
                - rewrite /future_priv_mono /=. iModIntro.
                  iIntros (W1 W2) "% #A". iApply interp_monotone_nl; auto.
                  destruct w0; auto.
                  destruct_cap c. simpl. destruct c3; auto.
                  simpl in H5. destruct (pwlU p0) eqn:HpwlU; try congruence.
                  exfalso. destruct p0; simpl in H,H4,HpwlU; try congruence;
                  destruct p'0; simpl in *; inv H; congruence. }
              iDestruct "HX" as ">[Hregion Hfull]".
              iDestruct (region_open_prepare with "Hregion") as "Hregion".
              assert (related_sts_pub_world W (<s[a':=Temporary]s>W)).
              { eapply (uninitialized_related_sts_pub_world); eauto. }
              iDestruct (region_close with "[$Hregion $B2 $Hstate $Hmono]") as "HH"; eauto.
              { destruct ρ;auto; congruence. }
              { iSplitR; auto. iFrame "∗ #". iNext.
                iApply interp_monotone; auto. }
              iModIntro. iExists _. iFrame "∗ %".
              iDestruct (interp_monotone with "[] [$Hwdst]") as "#Hwdst'"; [iPureIntro; eauto|].
              rewrite !(fixpoint_interp1_eq (<s[a':=_]s> W)) !interp1_eq.
              destruct (perm_eq_dec p0 O); [subst p0; simpl in H8; discriminate|].
              destruct (perm_eq_dec p0 E); [subst p0; simpl in H8; discriminate|].
              iDestruct "Hwdst'" as "[A1 [% A4]]".
              rewrite H4. iFrame "%".
              destruct g0; simpl; iFrame "#". eapply verify_access_spec in H7.
              destruct H7 as [A1 [A2 [A3 A4] ] ].
              replace (addr_reg.max b0 a') with a' by solve_addr.
              replace (addr_reg.min a' e0) with a' by solve_addr.
              replace (addr_reg.min a'' e0) with a'' by solve_addr.
              iSplit.
              { rewrite (isWithin_region_addrs_decomposition a' a'' b0 a''); [|solve_addr].
                iApply big_sepL_app. iFrame "#".
                iApply big_sepL_app.
                replace (region_addrs a'' a'') with (@nil Addr) by (rewrite /region_addrs region_size_0 /=; auto; solve_addr).
                iSplitL.
                - replace (region_addrs a' a'') with (a'::nil).
                  + iApply big_sepL_cons. iSplitL; [|iApply big_sepL_nil; auto].
                    iDestruct (extract_from_region_inv a' e0 a' with "A4") as (pp ?) "[X1 %]"; [solve_addr|].
                    iExists pp; iSplit;auto. iSplitL; auto.
                    iPureIntro; auto.
                    destruct (pwlU p0) eqn:Hp0; auto.
                    { rewrite /region_state_pwl /std_update /std /=.
                      rewrite lookup_insert. reflexivity. }
                    { rewrite /region_state_pwl /std_update /std /=.
                      rewrite lookup_insert. auto. }
                  + rewrite /region_addrs /region_size /=.
                    replace (a'' - a')%Z with 1%Z by solve_addr.
                    simpl. auto.
                - iApply big_sepL_nil; auto. }
              { replace (addr_reg.max b0 a'') with a'' by solve_addr.
                iApply (big_sepL_submseteq with "A4").
                rewrite (region_addrs_decomposition a' a' e0); [|solve_addr].
                replace ^(a' + 1)%a with a'' by solve_addr.
                eapply submseteq_inserts_l.
                eapply submseteq_cons. auto. }
            * rewrite -(insert_delete _ a' (p'0, w0)).
              rewrite delete_insert_ne; auto. rewrite delete_insert; auto.
              iDestruct (memMap_resource_2ne with "B") as "[B1 B2]"; auto. inv H8.
              iDestruct (region_close_next with "[$A1 $A2 $B1 $A3 $Hw0]") as "HX"; auto.
              { intros [g' Hcontr]. specialize (H2 g'). apply H2 in Hcontr as Hcontr'. destruct Hcontr'. subst g'.
                simplify_map_eq.
                assert (∃ w : leibnizO Word, Static {[a' := x]} = Static {[a' := w]});eauto. }
              { eapply not_elem_of_cons; split; auto.
                eapply not_elem_of_nil. }
              { iSplitR; auto. rewrite /monotonicity_guarantees_region.
                destruct ρ'; auto.
                - destruct (pwl p'0) eqn:Hpwl'.
                  + rewrite /future_pub_mono /=. iModIntro.
                    iIntros (W1 W2) "% #A".
                    iApply interp_monotone; auto.
                  + rewrite /future_priv_mono /=. iModIntro.
                    iIntros (W1 W2) "% #A". iApply interp_monotone_nl; auto.
                    destruct w0; auto.
                    destruct_cap c. simpl. destruct c3; auto.
                    simpl in H7. destruct (pwlU p0) eqn:HpwlU; try congruence; exfalso;
                    destruct p0; simpl in H,H4,HpwlU; try congruence;
                      destruct p'0; simpl in *; inv H; congruence.
                - simpl. rewrite /future_priv_mono /=. iModIntro.
                  iIntros (W1 W2) "% #A". iApply interp_monotone_nl; auto.
                  destruct w0; auto. destruct_cap c. simpl. destruct c3; auto.
                  simpl in H5. destruct p0; simpl in H4, H5; try (inv H4; inv H5; fail).
                  + rewrite (fixpoint_interp1_eq W (inr (URWL,_,_,_,_))) /=.
                    destruct g0; auto. iDestruct "Hwdst" as "[Y1 Y2]".
                    iDestruct (extract_from_region_inv _ _ a' with "Y2") as (pp ?) "[Y3 %]".
                    { eapply verify_access_spec in H7.
                      destruct H7 as [X1 [X2 [X3 X4] ] ].
                      solve_addr. }
                    destruct H11;[|destruct H11]; rewrite H11 in H9; discriminate.
                  + rewrite (fixpoint_interp1_eq W (inr (URWLX,_,_,_,_))) /=.
                    destruct g0; auto. iDestruct "Hwdst" as "[Y1 Y3]".
                    iDestruct (extract_from_region_inv _ _ a' with "Y3") as (pp ?) "[Y4 %]".
                    { eapply verify_access_spec in H7.
                      destruct H7 as [X1 [X2 [X3 X4] ] ].
                      solve_addr. }
                    destruct H11;[|destruct H11]; rewrite H11 in H9; discriminate. }
              iDestruct (region_open_prepare with "HX") as "Hregion".
              iDestruct (region_close with "[$Hregion $B2 $Hstate $Hmono]") as "HH"; eauto.
              { destruct ρ;auto;congruence. }
              iModIntro. iExists _. iFrame "∗ %". iSplit.
              { iPureIntro. rewrite /related_sts_pub_world; eapply related_sts_pub_refl_world. }
              { rewrite !(fixpoint_interp1_eq W (inr (p0,_,_,_,_))) !interp1_eq.
                destruct (perm_eq_dec p0 O); [subst p0; simpl in *; congruence|].
                destruct (perm_eq_dec p0 E); [subst p0; simpl in *; congruence|].
                iDestruct "Hwdst" as "[A1 [% A4]]".
                rewrite H4. iFrame "%".
                destruct g0; simpl; iFrame "#". eapply verify_access_spec in H7.
                destruct H7 as [A1 [A2 [A3 A4] ] ].
                replace (addr_reg.max b0 a') with a' by solve_addr.
                replace (addr_reg.min a' e0) with a' by solve_addr.
                replace (addr_reg.min a'' e0) with a'' by solve_addr.
                iSplit.
                { rewrite (isWithin_region_addrs_decomposition a' a'' b0 a''); [|solve_addr].
                  iApply big_sepL_app. iFrame "#".
                  iApply big_sepL_app.
                  replace (region_addrs a'' a'') with (@nil Addr) by (rewrite /region_addrs region_size_0 /=; auto; solve_addr).
                  iSplitL.
                  - replace (region_addrs a' a'') with (a'::nil).
                    + iApply big_sepL_cons. iSplitL; [|iApply big_sepL_nil; auto].
                      iDestruct (extract_from_region_inv a' e0 a' with "A4") as (pp Hflowspp) "[X1 %]"; [solve_addr|].
                      iExists pp; iSplit;auto. iSplitL; auto.
                      iPureIntro;auto.
                      destruct (pwlU p0) eqn:Hp0; auto.
                      { destruct H7; auto. elim n0.
                        rewrite H9 in H7; inv H7. exists x. inversion H11. eauto. }
                      { destruct H7; auto. destruct H7; auto. elim n0. destruct H7.
                        rewrite H7 in H9; inv H9. eauto. }
                    + rewrite /region_addrs /region_size /=.
                      replace (a'' - a')%Z with 1%Z by solve_addr.
                      simpl. auto.
                  - iApply big_sepL_nil; auto. }
                { replace (addr_reg.max b0 a'') with a'' by solve_addr.
                  iApply (big_sepL_submseteq with "A4").
                  rewrite (region_addrs_decomposition a' a' e0); [|solve_addr].
                  replace ^(a' + 1)%a with a'' by solve_addr.
                  eapply submseteq_inserts_l.
                  eapply submseteq_cons. auto. } }
        - iModIntro. destruct (mem !! a') as [(p'', w'')|]; auto.
          iDestruct "A" as "[% [Hsts A]]".
          destruct (addr_eq_dec a a').
          + subst a'. subst mem.
            iDestruct (region_open_prepare with "A") as "A".
            rewrite insert_insert.
            iDestruct (memMap_resource_1 with "B") as "B".
            rewrite lookup_insert in H0.
            inversion H8; inversion H0. subst p'' w'' p'0.
            iDestruct (region_close _ _ (λ Wv : WORLD * Word, interp Wv.1 Wv.2) with "[$A $B $Hstate Hmono]") as "B"; eauto.
            { destruct ρ;auto;congruence. }
            { iSplitR;auto. iFrame "#". simpl.
              destruct (decide (ρ = Temporary ∧ pwl p' = true)).
              - rewrite /future_pub_mono /=. iModIntro.
                 iIntros (W1 W2) "% #A".
                 iApply interp_monotone; auto.
              - rewrite /future_priv_mono /=. iModIntro.
                 iIntros (W1 W2) "% #A". iApply interp_monotone_nl; auto.
                 destruct w0; auto.
                 eapply not_and_r in n0. destruct_cap c.
                 simpl. destruct c3; auto. simpl in H5.
                 destruct (pwlU p0) eqn:HwplU; intros; try congruence.
                 destruct n0.
                 * iAssert (⌜g0 = Local⌝)%I as %->.
                    { rewrite (fixpoint_interp1_eq W (inr (p0, _, _, _, _))).
                      destruct p0; simpl in HwplU; try congruence; destruct g0; simpl; auto. }
                    rewrite (fixpoint_interp1_eq W (inr (p0, _, _, _, _))).
                    iAssert (⌜region_state_U_pwl W a⌝)%I as %Hρ.
                    { destruct p0; simpl in H4; simpl in HwplU; try congruence.
                      - simpl. iDestruct "Hwdst" as "[YA YB]".
                        destruct (proj1 (verify_access_spec _ _) H7) as (A & B & C & D).
                        iDestruct (extract_from_region_inv _ _ a with "YA") as (pp ?) "[E %]"; auto.
                        split; try solve_addr. rewrite /addr_reg.min; destruct (Addr_le_dec a0 e0); solve_addr.
                      - simpl. iDestruct "Hwdst" as "[YA YB]".
                        destruct (proj1 (verify_access_spec _ _) H7) as (A & B & C & D).
                        iDestruct (extract_from_region_inv _ _ a with "YA") as (pp ?) "[E %]"; auto.
                        split; try solve_addr. rewrite /addr_reg.min; destruct (Addr_le_dec a0 e0); solve_addr. }
                    destruct Hρ as [Hρ | Hρ]; rewrite Hregion in Hρ; inversion Hρ; try subst ρ; congruence.
                  * assert (HpwlU2: pwlU p' = true).
                    { destruct p0; simpl in H5; simpl in HwplU; try congruence; destruct p'; rewrite /PermFlows in H; inv H; simpl in H0; try congruence; reflexivity. }
                    exfalso. destruct Hp as [-> | [-> | [-> ->] ] ]; destruct p'; simpl in HpwlU2; simpl in *; try congruence; inv Hfp. }

            iExists W. iFrame. iPureIntro. apply related_sts_pub_refl_world.
          + subst mem. rewrite insert_commute; auto.
            rewrite insert_insert.
            iDestruct (memMap_resource_2ne with "B") as "[B C]"; auto.
            rewrite /region_open_resources.
            iDestruct "A" as (ρ') "[A1 [ [% %] [A2 [% [[A3 #Hw'] #A4]]]]]". inv H8.
            iDestruct (sts_full_state_std with "[$Hsts] [$A1]") as "%".
            iDestruct (region_close_next with "[$A1 $A2 A3 $A4 $C]") as "A"; auto.
            { intros [g' Hcontr]. specialize (H2 g'). congruence. }
            { eapply not_elem_of_cons; split; auto. eapply not_elem_of_nil. }
            { iSplitR; auto. simpl. iSplit; auto.
              rewrite !switch_monotonicity_formulation; auto.
              rewrite /monotonicity_guarantees_decide.
              destruct (decide (ρ' = Temporary ∧ pwl p'0 = true)).
              + rewrite /future_pub_mono /=. iModIntro.
                iIntros (W1 W2) "% #A".
                iApply interp_monotone; auto.
              + rewrite /future_priv_mono /=. iModIntro.
                iIntros (W1 W2) "% #A". iApply interp_monotone_nl; auto.
                destruct w0; auto.
                eapply not_and_r in n1. destruct_cap c.
                simpl. destruct c3; auto. simpl in H4,H5.
                destruct (pwlU p0) eqn:HwplU; intros; try congruence.
                destruct n1.
                * iAssert (⌜g0 = Local⌝)%I as %->.
                  { rewrite (fixpoint_interp1_eq W (inr (p0, _, _, _, _))).
                    destruct p0; simpl in HwplU; try congruence; destruct g0; simpl; auto. }
                  rewrite (fixpoint_interp1_eq W (inr (p0, _, _, _, _))).
                  iAssert (⌜region_state_U_pwl W a'⌝)%I as %Hρ.
                  { destruct p0; simpl in H4; simpl in HwplU; try congruence.
                    - simpl. iDestruct "Hwdst" as "[YA YB]".
                      destruct (proj1 (verify_access_spec _ _) H7) as (A & B & C & D).
                      iDestruct (extract_from_region_inv b0 _ a' with "YA") as (pp ?) "[E %]"; auto.
                      split; try solve_addr. iPureIntro. left; auto.
                    - simpl. iDestruct "Hwdst" as "[YA YC]".
                      destruct (proj1 (verify_access_spec _ _) H7) as (A & B & C & D).
                      iDestruct (extract_from_region_inv b0 _ a' with "YA") as (pp ?) "[E %]"; auto.
                      split; try solve_addr. iPureIntro. left; auto. }
                  destruct Hρ as [Hρ | Hρ]; rewrite H8 in Hρ; inversion Hρ; try subst ρ'; congruence.
                * assert (HpwlU2: pwlU p'0 = true).
                  { destruct p0; simpl in H5; simpl in HwplU; try congruence; destruct p'0; rewrite /PermFlows in H; inv H; simpl in H0; try congruence; reflexivity. }
                  exfalso. destruct p0; destruct p'0; simpl in H5, HwplU, HpwlU2, H10; try congruence; inv H; auto. }
            iDestruct (region_open_prepare with "A") as "A".
            iDestruct (region_close with "[$A $B $Hmono $Hstate]") as "B"; auto.
            { destruct ρ;auto;congruence. }
            iExists W. iFrame. iPureIntro. apply related_sts_pub_refl_world. }
      iDestruct "HW" as (W') "[Hregion [% [Hfull HX]]]".
      iDestruct ("IH" $! W' r' with "[] [HX] [C] [$Hregion] [$Hfull] [$Hown] [] []") as "H"; auto.
      { iPureIntro. simpl; intros.
        destruct (addr_eq_dec a0 a').
        - subst a0. destruct (a' + 1)%a as [a''|] eqn:Ha'; try tauto.
          eapply incrementPC_Some_inv in H10.
          destruct H10 as (?&?&?&?&?&?&?&?&?).
          subst r'. destruct (reg_eq_dec PC x).
          * subst x; rewrite lookup_insert; eauto.
          * rewrite lookup_insert_ne; auto.
            destruct (reg_eq_dec rdst x).
            { subst x. rewrite lookup_insert; eauto. }
            { rewrite !lookup_insert_ne; auto. }
        - eapply incrementPC_Some_inv in H10.
          destruct H10 as (?&?&?&?&?&?&?&?&?).
          subst r'. destruct (reg_eq_dec PC x).
          + subst x; rewrite lookup_insert; eauto.
          + rewrite !lookup_insert_ne; auto. }
      { iIntros (x) "%".
        destruct (addr_eq_dec a0 a').
        - subst a0. destruct (a' + 1)%a as [a''|] eqn:Ha'; try tauto.
          eapply incrementPC_Some_inv in H10.
          destruct H10 as (?&?&?&?&?&?&?&?&?).
          subst r'. rewrite lookup_insert_ne; auto.
          destruct (reg_eq_dec rdst x).
          * subst x. rewrite lookup_insert. auto.
          * rewrite !lookup_insert_ne; auto.
            iApply interp_monotone; auto.
            iApply "Hreg"; auto.
        - eapply incrementPC_Some_inv in H10.
          destruct H10 as (?&?&?&?&?&?&?&?&?).
          subst r'. rewrite !lookup_insert_ne; auto.
          iApply interp_monotone; auto.
          iApply "Hreg"; auto. }
      { instantiate (3 := b).
        instantiate (2 := e).
        instantiate (1 := match (a + 1)%a with Some a' => a' | None => a end).
        destruct (addr_eq_dec a0 a').
        - subst a0. destruct (a' + 1)%a as [a''|] eqn:Ha'; try tauto.
          eapply incrementPC_Some_inv in H10.
          destruct H10 as (?&?&?&?&?&?&?&?&?).
          subst r'. rewrite insert_insert.
          simplify_map_eq. auto.
        - eapply incrementPC_Some_inv in H10.
          destruct H10 as (?&?&?&?&?&?&?&?&?).
          subst r'. rewrite insert_insert.
          simplify_map_eq. rewrite insert_insert;auto. }
      { iModIntro. (* iExists p'; iSplitR; auto. *)
        iApply (big_sepL_mono with "Hinv"); auto.
        intros. simpl. iIntros "Hw". iDestruct "Hw" as (pp ?) "Hw".
        iExists pp; iSplit;auto.
        iDestruct "Hw" as "[$ %]".
        destruct (pwl p);iPureIntro.
        + eapply region_state_pwl_monotone; eauto.
        + eapply region_state_nwl_monotone; eauto.
      }
      iApply wp_pure_step_later; auto. iNext.
      iApply (wp_mono with "H"). simpl.
      iIntros (v) "H %". iDestruct ("H" $! a1) as (rx Wx) "[A [B [% [C [D E]]]]]".
      iExists rx, Wx; iFrame.
      iPureIntro. eapply related_sts_priv_trans_world; eauto.
      eapply related_sts_pub_priv_world; auto. }
    { iApply wp_pure_step_later; auto. iNext. iApply wp_value; auto. iIntros; discriminate. }
    Unshelve. all: eauto; try exact {[a:=x]}.
  Qed.

End fundamental.
