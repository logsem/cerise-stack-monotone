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
                                            ∧ ρ ≠ Revoked ∧ (∀ g, ρ ≠ Monostatic g) ∧ (∀ w, ρ ≠ Uninitialized w))⌝.
  Proof.
    intros. rewrite /interp fixpoint_interp1_eq /=. iIntros "H".
    assert (p = URW \/ p = URWL \/ p = URWX \/ p = URWLX) as [-> | [-> | [-> | ->] ] ] by (destruct p; simpl in H0; auto; congruence); simpl.
    - destruct g.
      + iDestruct (extract_from_region_inv with "H") as (p' ?) "[C %]";try (iExists p'; iFrame; auto);[solve_addr|].
        iSplit;auto. iPureIntro; auto. rewrite H2. eexists;eauto.
      + iDestruct "H" as "[B C]".
        iDestruct (extract_from_region_inv with "B") as (p' ?) "[D %]"; try (iExists p'; iFrame); auto.
        iSplit;auto. iPureIntro; eauto.
      + iDestruct "H" as "[B C]".
        iDestruct (extract_from_region_inv with "B") as (p' ?) "[D %]"; try (iExists p'; iFrame); auto.
        iSplit;auto. iPureIntro; auto. destruct H2 as [? | ?]; eexists;eauto.
    - destruct g; auto.
      iDestruct "H" as "[B C]".
      iDestruct (extract_from_region_inv with "B") as (p' ?) "[D %]"; try (iExists p'; iFrame); auto.
      iPureIntro; split;eauto.
    - destruct g.
      + iDestruct (extract_from_region_inv with "H") as (p' Hfl) "[D %]"; try (iExists p'; iFrame); auto; [solve_addr|].
        iSplit;auto. iPureIntro; auto. eexists; eauto.
      + iDestruct "H" as "[B C]".
        iDestruct (extract_from_region_inv with "B") as (p' Hfl) "[E %]"; try (iExists p'; iFrame); auto.
        iSplit;auto. iPureIntro; eauto.
      + iDestruct "H" as "[B C]".
        iDestruct (extract_from_region_inv with "B") as (p' Hfl) "[E %]"; try (iExists p'; iFrame); auto.
        iSplit;auto. iPureIntro; auto. destruct H1 as [? | ?]; eexists;eauto.
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
                                            ∧ ρ ≠ Revoked ∧ (∀ g, ρ ≠ Monostatic g))⌝.
  Proof.
    intros. iIntros "H".
    destruct (decide (a' < addr_reg.min a e))%a.
    { iDestruct (isU_inv _ a' with "H") as (p') "(?&?&H)";[solve_addr|auto|]. iDestruct "H" as %(?&?&?&?&?).
      iExists p'. iFrame. iPureIntro;eauto. }
    assert (addr_reg.min a e <= a' < e)%a;[solve_addr|].
    rewrite /interp fixpoint_interp1_eq /=.
    assert (p = URW \/ p = URWL \/ p = URWX \/ p = URWLX) as [-> | [-> | [-> | ->] ] ] by (destruct p; simpl in H0; auto; congruence); simpl.
    - destruct g.
      + iDestruct (extract_from_region_inv with "H") as (p' ?) "[C %]";try (iExists p'; iFrame; auto);[solve_addr|].
        iSplit;auto. iPureIntro; auto. eexists;repeat split;eauto.
      + iDestruct "H" as "[B C]".
        iDestruct (extract_from_region_inv with "C") as (p' ?) "[D %]"; try (iExists p'; iFrame);[solve_addr|].
        iSplit;auto. iPureIntro; eauto.
      + iDestruct "H" as "[B C]".
        iDestruct (extract_from_region_inv with "C") as (p' ?) "[D %]"; try (iExists p'; iFrame); [solve_addr|].
        iSplit;auto. iPureIntro; auto. destruct H3 as [? | [? | [? ?] ] ];
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
        iSplit;auto. iPureIntro; eauto.
      + iDestruct "H" as "[B C]".
        iDestruct (extract_from_region_inv with "C") as (p' Hfl) "[E %]"; try (iExists p'; iFrame); [solve_addr|].
        iSplit;auto. iPureIntro; auto. destruct H2 as [? | [? | [? ?] ] ];
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
                                            ∧ ρ ≠ Revoked ∧ (∀ g, ρ ≠ Monostatic g) ∧
                                            if (a' =? addr_reg.min a e)%Z
                                            then True
                                            else (∀ w, ρ ≠ Uninitialized w))⌝.
  Proof.
    intros. iIntros "H". 
    destruct (a' =? addr_reg.min a e)%Z eqn:Heq.
    - iDestruct (isU_inv_all _ a' with "H") as (p') "(?&?&H)";[solve_addr|auto|]. iDestruct "H" as %(?&?&?&?).
      iExists p'. iFrame. iPureIntro;eexists;eauto.
    - apply Z.eqb_neq in Heq. iDestruct (isU_inv _ a' with "H") as (p') "(?&?&H)";[solve_addr|auto|]. iDestruct "H" as %(?&?&?&?&?).
      iExists p'. iFrame. iPureIntro;eexists;repeat split;eauto. 
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
    ∗ ⌜if condb then True else (forall w, ρ ≠ Uninitialized w)⌝
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

        destruct H as (ρ & Hρ & Hnotrevoked & Hnotmonostatic & Hdec).
        assert (addr_reg.min a0 e0 = a0) as Heq;[solve_addr|]. rewrite Heq in Hdec. 
        destruct ρ; try congruence.
        * iDestruct (region_open_next _ _ _ a1 p0' Monotemporary with "[$Hrel' $Hr $Hsts]") as (w0) "($ & Hstate' & Hr & Ha0 & % & Hfuture & #Hval)";
            auto;[intros [g1 Hcontr];done..| |].
          { apply not_elem_of_cons. split; auto. apply not_elem_of_nil. }
          iExists _,_. iFrame. iSplitR; auto. iExists Monotemporary. iFrame "∗ % #". 
        * iDestruct (region_open_next _ _ _ a1 p0' Permanent with "[$Hrel' $Hr $Hsts]") as (w0) "($ & Hstate' & Hr & Ha0 & % & Hfuture & #Hval)";
            auto;[intros [g1 Hcontr];done..| |].
          { apply not_elem_of_cons. split; auto. apply not_elem_of_nil. }
          iExists _,_. iFrame. iSplitR; auto. iExists Permanent. iFrame "∗ % #".
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

  (* TODO: prove this using interp_weakening *)
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
              | Some (Uninitialized _) => (<[a1:=Monotemporary]> W.1,W.2)
              | _ => W
              end
         else W
       | None => W
       end
     | None => W
     end.

   Lemma new_worldU_pub W a0 pc_p pc_g pc_b pc_e pc_a r offs :
     related_sts_pub_world W (new_worldU W a0 pc_p pc_g pc_b pc_e pc_a r offs).
   Proof.
     unfold new_worldU.
     destruct (z_of_argument (<[PC:=inr (pc_p, pc_g, pc_b, pc_e, pc_a)]> r) offs);
       [|apply related_sts_pub_refl_world].
     destruct (a0 + z)%a eqn:Hnext;[|apply related_sts_pub_refl_world].
     destruct (a =? a0)%Z;[|apply related_sts_pub_refl_world].
     destruct (std W !! a) eqn:Hsome;[|apply related_sts_pub_refl_world].
     destruct r0;try apply related_sts_pub_refl_world. 
     apply uninitialized_w_mono_related_sts_pub_world in Hsome;auto. 
   Qed.

   Definition new_state ρ :=
     match ρ with
     | Uninitialized _ => Monotemporary
     | _ => ρ
     end. 

   Lemma new_worldU_lookup W a0 pc_p pc_g pc_b pc_e pc_a r offs z a1 ρ :
     z_of_argument (<[PC:=inr (pc_p, pc_g, pc_b, pc_e, pc_a)]> r) offs = Some z →
     (a0 + z)%a = Some a1 →
     W.1 !! a1 = Some ρ →
     (a1 =? a0)%Z = true →
     std (new_worldU W a0 pc_p pc_g pc_b pc_e pc_a r offs) !! a1 = Some (new_state ρ).
   Proof.
     intros Hzoff Hnext Hρ Hfalse.
     unfold new_worldU. rewrite Hzoff Hnext Hfalse Hρ.
     unfold new_state. destruct ρ;auto;
     simplify_map_eq;auto. 
   Qed.

  (* Note that we turn in all information that we might have on the monotonicity of the current PC value, so that in the proof of the ftlr case itself, we do not have to worry about whether the PC was written to or not when we close the last location pc_a in the region *)
   Lemma mem_map_recover_res:
    ∀ (W : WORLD) (r : Reg) (p' : Perm)
       (pc_w : Word) (r1 : RegName) (r2 offs : Z + RegName) (offz : Z) (p0 p'0 pc_p pc_p' : Perm)
       (g0 pc_g : Locality) (b0 e0 a0 a1 pc_b pc_e pc_a : Addr) (mem0 : PermMem) (oldv storev : Word) (ρ : region_type)
       (Hnotuninitialized : ∀ w, ρ ≠ Uninitialized w), 
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
        ={⊤}=∗ ∃ v, open_region pc_a (new_worldU W a0 pc_p pc_g pc_b pc_e pc_a r offs)
                            ∗ sts_full_world (new_worldU W a0 pc_p pc_g pc_b pc_e pc_a r offs)
                            ∗ pc_a ↦ₐ[pc_p'] v
                            ∗ ((fixpoint interp1) (new_worldU W a0 pc_p pc_g pc_b pc_e pc_a r offs)) v
                            ∗ monotonicity_guarantees_region ρ pc_a v pc_p' interpC
                            ∗ ⌜related_sts_pub_world W (new_worldU W a0 pc_p pc_g pc_b pc_e pc_a r offs)⌝.
   Proof.
     intros W r p' pc_w r1 r2 offs offz p0 p'0 pc_p pc_p' g0 pc_g b0 e0 a0 a1 pc_b pc_e pc_a mem0 oldv storev ρ Hnotuninitialized
            Hwoa Hz Hnext Hpcperm Hras Hstdst Ha0.
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
          + iSpecialize ("Hreg" $! r0 n). rewrite lookup_insert_ne in Hrr0; last congruence. by rewrite /RegLocate Hrr0.
      }
      case_decide as Haeq.
      + iExists pc_w.
        destruct Hallows as [Hrinr [Hwa [Hwb Hloc] ] ].
        iDestruct "HStoreRes" as (p'1 w') "[-> [% HLoadRes] ]".
        rewrite lookup_insert in Ha0; inversion Ha0; clear Ha0; subst.
        iDestruct "HLoadRes" as (ρ1) "(Hstate' & % & % & % & % & Hr & % & Hrel')".
        rewrite insert_insert memMap_resource_2ne; last auto. iDestruct "Hmem" as  "[Ha1 $]".
        iDestruct (storev_interp_mono with "HVr1") as "Hr1Mono"; eauto.
        destruct ((a1 =? a0)%Z) eqn:Heqa.
        assert (related_sts_pub_world W (new_worldU W a0 pc_p pc_g pc_b pc_e pc_a r offs)) as Hpub.
        { apply new_worldU_pub. }
        iDestruct (storev_interp_mono (new_worldU W a0 pc_p pc_g pc_b pc_e pc_a r offs) with "[HVr1]") as "Hr1Mono2";
          [eauto..|eapply new_worldU_lookup;eauto| |].
        { iApply interp_monotone;[|iFrame "#"]. iPureIntro. auto. }
        iDestruct (interp_monotone with "[] Hpc_w") as "Hpc_w'";[iPureIntro;apply Hpub|]. 
        apply Z.eqb_eq,z_of_eq in Heqa as ->.
        * rewrite H1. iFrame.
          destruct (decide (ρ1 = Monotemporary ∨ ρ1 = Permanent)). 
          ** iDestruct (region_close_next with "[$Hr $Ha1 $Hrel' $Hstate' $HVstorev1 $Hr1Mono]") as "Hr"; eauto;
               [intros [g Hcontr];destruct o as [o | o]; subst;try done..| |].
             { apply not_elem_of_cons; split; [auto|apply not_elem_of_nil]. }
             destruct o as [-> | ->]; iDestruct (region_open_prepare with "Hr") as "$"; iFrame; iFrame "Hpc_w";
             iPureIntro;apply related_sts_pub_refl_world. 
          ** apply Decidable.not_or in n as [Hne1 n].
             destruct ρ1;try congruence.
             (* ρ1 = Uninitialized w *)
             unfold monotonicity_guarantees_region.
             iSimpl in "Hr1Mono2". 
             destruct (pwl p'0) eqn:Hpwl. 
             *** iMod (region_close_next_mono_uninit_w_pwl with "[$Hr $Hsts $Ha1 $Hrel' $Hstate' $HVstorev1 $Hr1Mono2]") as "[Hr Hsts]";eauto.
                 { apply not_elem_of_cons; split; [auto|apply not_elem_of_nil]. }
                 iModIntro. iDestruct (region_open_prepare with "Hr") as "$". iFrame. unfold new_worldU.
                 rewrite Hz Hnext H1 Z.eqb_refl. iFrame "Hpc_w'".
                 rewrite /new_worldU Hz Hnext H1 Z.eqb_refl in Hpub. auto.
             *** iMod (region_close_next_mono_uninit_w_nwl with "[$Hr $Hsts $Ha1 $Hrel' $Hstate' $HVstorev1 $Hr1Mono2]") as "[Hr Hsts]";eauto.
                 { apply not_elem_of_cons; split; [auto|apply not_elem_of_nil]. }
                 iModIntro. iDestruct (region_open_prepare with "Hr") as "$". iFrame. unfold new_worldU.
                 rewrite Hz Hnext H1 Z.eqb_refl. iFrame "Hpc_w'".
                 rewrite /new_worldU Hz Hnext H1 Z.eqb_refl in Hpub. auto.
        * iDestruct (region_close_next with "[$Hr $Ha1 $Hrel' $Hstate' $HVstorev1 $Hr1Mono]") as "Hr"; eauto.
          { intros [g Hcontr]. specialize (H3 g). done. }
          { intros [g Hcontr]. specialize (H4 g). done. }
          { apply not_elem_of_cons; split; [auto|apply not_elem_of_nil]. }
          iDestruct (region_open_prepare with "Hr") as "$". iFrame. iFrame "Hpc_w".
          iPureIntro. apply related_sts_pub_refl_world. 
      + subst a1. iDestruct "HStoreRes" as "[-> [HStoreRes % ] ]".
        rewrite insert_insert -memMap_resource_1.
        rewrite lookup_insert in Ha0; inversion Ha0; simplify_eq.
        iExists storev1. iFrame.
        rewrite Hstdst. 
        iDestruct (storev_interp_mono with "HVr1") as "Hr1Mono"; eauto.
        destruct (pc_a =? a0)%Z eqn:Heqa0.
        * destruct ρ; iFrame "∗ #"; try by (iPureIntro;apply related_sts_pub_refl_world).
          exfalso. specialize (Hnotuninitialized w);done. 
        * iModIntro. iFrame "∗ #". iPureIntro. apply related_sts_pub_refl_world. 
    - by exfalso.
   Qed.

   (* core lemma which will state that incrementing the address remains valid if world is initialized *)
   Lemma interp_initialize_limit W a' x x0 x1 x2 x3 r offs p0 g0 b0 e0 a0 zoffs w0 r1:
     related_sts_pub_world W (new_worldU W a' x x0 x1 x2 x3 r offs) →
     z_of_argument (<[PC:=inr (x, x0, x1, x2, x3)]> r) offs = Some zoffs →
     reg_allows_storeU (<[PC:=inr (x, x0, x1, x2, x3)]> r) r1 p0 g0 b0 e0 a' a' w0 →
     (a' + zoffs)%a = Some a' →
     (a' + 1)%a = Some a0 →
     fixpoint interp1 W (inr (p0, g0, b0, e0, a')) -∗
     fixpoint interp1 (new_worldU W a' x x0 x1 x2 x3 r offs) (inr (p0, g0, b0, e0, a0)).
   Proof.
     iIntros (Hpub Hzoff Hallows Ha' Hnext) "#Hvalid".
     destruct Hallows as [Hlookup [Hu (Hle1 & Hle2 & Hle3 & Hallows)] ].
     iDestruct (interp_monotone with "[] Hvalid") as "Hvalid'";[eauto|].
     iClear "Hvalid".
     destruct p0;inversion Hu;rewrite !fixpoint_interp1_eq /=;eauto.
     - destruct g0;try done.
       + iDestruct "Hvalid'" as "[Hval1 Hval2]".
         assert (addr_reg.min a' e0 <= addr_reg.min a0 e0)%Z;[solve_addr|].
         assert (b0 <= (addr_reg.min a' e0))%Z;[solve_addr|].
         rewrite (region_addrs_split b0 (addr_reg.min a' e0) (addr_reg.min a0 e0));[|solve_addr].
         rewrite big_sepL_app. rewrite bi.sep_comm. iFrame "Hval1".
         assert (addr_reg.max b0 a0 <= e0)%a;[solve_addr|].
         rewrite (region_addrs_split (addr_reg.max b0 a') (addr_reg.max b0 a0) e0);[|solve_addr].
         iDestruct (big_sepL_app with "Hval2") as "[Hval21 Hval22]". iFrame "Hval22".
         assert (addr_reg.min a' e0 = a') as ->;[solve_addr|].
         assert (addr_reg.min a0 e0 = a0) as ->;[solve_addr|].
         assert (addr_reg.max b0 a' = a') as ->;[solve_addr|].
         assert (addr_reg.max b0 a0 = a0) as ->;[solve_addr|].
         rewrite (region_addrs_single a' a0);auto. 
       + iDestruct "Hvalid'" as "[Hval1 Hval2]".
         assert (addr_reg.min a' e0 <= addr_reg.min a0 e0)%Z;[solve_addr|].
         assert (b0 <= (addr_reg.min a' e0))%Z;[solve_addr|].
         rewrite (region_addrs_split b0 (addr_reg.min a' e0) (addr_reg.min a0 e0));[|solve_addr].
         rewrite big_sepL_app. rewrite bi.sep_comm. iFrame "Hval1".
         assert (addr_reg.max b0 a0 <= e0)%a;[solve_addr|].
         rewrite (region_addrs_split (addr_reg.max b0 a') (addr_reg.max b0 a0) e0);[|solve_addr].
         iDestruct (big_sepL_app with "Hval2") as "[Hval21 Hval22]". iFrame "Hval22".
         assert (addr_reg.min a' e0 = a') as ->;[solve_addr|].
         assert (addr_reg.min a0 e0 = a0) as ->;[solve_addr|].
         assert (addr_reg.max b0 a' = a') as ->;[solve_addr|].
         assert (addr_reg.max b0 a0 = a0) as ->;[solve_addr|].
         rewrite (region_addrs_single a' a0);auto. simpl.
         iDestruct "Hval21" as "[Hval21 _]".
         iDestruct "Hval21" as (p0 Hflows) "[Hrel %]".
         iSplit;auto. iExists p0. repeat iSplit;auto. iPureIntro.

         unfold region_state_U in H0. destruct H2 as [-> | [ -> | [w Hstatic] ] ];auto.
         all: unfold new_worldU in Hstatic;rewrite Hzoff Ha' Z.eqb_refl in Hstatic.
         all: unfold new_worldU;rewrite Hzoff Ha' Z.eqb_refl.
         all: destruct (std W !! a') eqn:Hsome;[|congruence]. 
         all: destruct r0;inversion Hstatic; try congruence.
         all: simplify_map_eq. 
     - destruct g0;try done.
       iDestruct "Hvalid'" as "[Hval1 Hval2]".
       assert (addr_reg.min a' e0 <= addr_reg.min a0 e0)%Z;[solve_addr|].
       assert (b0 <= (addr_reg.min a' e0))%Z;[solve_addr|].
       rewrite (region_addrs_split b0 (addr_reg.min a' e0) (addr_reg.min a0 e0));[|solve_addr].
       rewrite big_sepL_app. rewrite bi.sep_comm. iFrame "Hval1".
       assert (addr_reg.max b0 a0 <= e0)%a;[solve_addr|].
       rewrite (region_addrs_split (addr_reg.max b0 a') (addr_reg.max b0 a0) e0);[|solve_addr].
       iDestruct (big_sepL_app with "Hval2") as "[Hval21 Hval22]". iFrame "Hval22".
       assert (addr_reg.min a' e0 = a') as ->;[solve_addr|].
       assert (addr_reg.min a0 e0 = a0) as ->;[solve_addr|].
       assert (addr_reg.max b0 a' = a') as ->;[solve_addr|].
       assert (addr_reg.max b0 a0 = a0) as ->;[solve_addr|].
       rewrite (region_addrs_single a' a0);auto. simpl.
       iDestruct "Hval21" as "[Hval21 _]".
       iDestruct "Hval21" as (p0 Hflows) "[Hrel %]".
       iSplit;auto. iExists p0. repeat iSplit;auto. iPureIntro.

       unfold region_state_U in H0. destruct H2 as [Hw | [w Hstatic] ];auto.
       unfold new_worldU in Hstatic. rewrite Hzoff Ha' Z.eqb_refl in Hstatic.
       unfold new_worldU. rewrite Hzoff Ha' Z.eqb_refl.
       destruct (std W !! a') eqn:Hsome;[|congruence]. 
       destruct r0;inversion Hstatic; try congruence.
       simplify_map_eq. 
     - destruct g0;try done.
       + iDestruct "Hvalid'" as "[Hval1 Hval2]".
         assert (addr_reg.min a' e0 <= addr_reg.min a0 e0)%Z;[solve_addr|].
         assert (b0 <= (addr_reg.min a' e0))%Z;[solve_addr|].
         rewrite (region_addrs_split b0 (addr_reg.min a' e0) (addr_reg.min a0 e0));[|solve_addr].
         rewrite big_sepL_app. rewrite bi.sep_comm. iFrame "Hval1".
         assert (addr_reg.max b0 a0 <= e0)%a;[solve_addr|].
         rewrite (region_addrs_split (addr_reg.max b0 a') (addr_reg.max b0 a0) e0);[|solve_addr].
         iDestruct (big_sepL_app with "Hval2") as "[Hval21 Hval22]". iFrame "Hval22".
         assert (addr_reg.min a' e0 = a') as ->;[solve_addr|].
         assert (addr_reg.min a0 e0 = a0) as ->;[solve_addr|].
         assert (addr_reg.max b0 a' = a') as ->;[solve_addr|].
         assert (addr_reg.max b0 a0 = a0) as ->;[solve_addr|].
         rewrite (region_addrs_single a' a0);auto. 
       + iDestruct "Hvalid'" as "[Hval1 Hval2]".
         assert (addr_reg.min a' e0 <= addr_reg.min a0 e0)%Z;[solve_addr|].
         assert (b0 <= (addr_reg.min a' e0))%Z;[solve_addr|].
         rewrite (region_addrs_split b0 (addr_reg.min a' e0) (addr_reg.min a0 e0));[|solve_addr].
         rewrite big_sepL_app. rewrite bi.sep_comm. iFrame "Hval1".
         assert (addr_reg.max b0 a0 <= e0)%a;[solve_addr|].
         rewrite (region_addrs_split (addr_reg.max b0 a') (addr_reg.max b0 a0) e0);[|solve_addr].
         iDestruct (big_sepL_app with "Hval2") as "[Hval21 Hval22]". iFrame "Hval22".
         assert (addr_reg.min a' e0 = a') as ->;[solve_addr|].
         assert (addr_reg.min a0 e0 = a0) as ->;[solve_addr|].
         assert (addr_reg.max b0 a' = a') as ->;[solve_addr|].
         assert (addr_reg.max b0 a0 = a0) as ->;[solve_addr|].
         rewrite (region_addrs_single a' a0);auto. simpl.
         iDestruct "Hval21" as "[Hval21 _]".
         iDestruct "Hval21" as (p0 Hflows) "[Hrel %]".
         iSplit;auto. iExists p0. repeat iSplit;auto. iPureIntro.

         unfold region_state_U in H0. destruct H2 as [-> | [ -> | [w Hstatic] ] ];auto.
         all: unfold new_worldU in Hstatic;rewrite Hzoff Ha' Z.eqb_refl in Hstatic.
         all: unfold new_worldU;rewrite Hzoff Ha' Z.eqb_refl.
         all: destruct (std W !! a') eqn:Hsome;[|congruence]. 
         all: destruct r0;inversion Hstatic; try congruence.
         all: simplify_map_eq.
     - destruct g0;try done.
       iDestruct "Hvalid'" as "[Hval1 Hval2]".
       assert (addr_reg.min a' e0 <= addr_reg.min a0 e0)%Z;[solve_addr|].
       assert (b0 <= (addr_reg.min a' e0))%Z;[solve_addr|].
       rewrite (region_addrs_split b0 (addr_reg.min a' e0) (addr_reg.min a0 e0));[|solve_addr].
       rewrite big_sepL_app. rewrite bi.sep_comm. iFrame "Hval1".
       assert (addr_reg.max b0 a0 <= e0)%a;[solve_addr|].
       rewrite (region_addrs_split (addr_reg.max b0 a') (addr_reg.max b0 a0) e0);[|solve_addr].
       iDestruct (big_sepL_app with "Hval2") as "[Hval21 Hval22]". iFrame "Hval22".
       assert (addr_reg.min a' e0 = a') as ->;[solve_addr|].
       assert (addr_reg.min a0 e0 = a0) as ->;[solve_addr|].
       assert (addr_reg.max b0 a' = a') as ->;[solve_addr|].
       assert (addr_reg.max b0 a0 = a0) as ->;[solve_addr|].
       rewrite (region_addrs_single a' a0);auto. simpl.
       iDestruct "Hval21" as "[Hval21 _]".
       iDestruct "Hval21" as (p0 Hflows) "[Hrel %]".
       iSplit;auto. iExists p0. repeat iSplit;auto. iPureIntro.

       unfold region_state_U in H0. destruct H2 as [Hw | [w Hstatic] ];auto.
       unfold new_worldU in Hstatic. rewrite Hzoff Ha' Z.eqb_refl in Hstatic.
       unfold new_worldU. rewrite Hzoff Ha' Z.eqb_refl.
       destruct (std W !! a') eqn:Hsome;[|congruence]. 
       destruct r0;inversion Hstatic; try congruence.
       simplify_map_eq. 
   Qed. 

   Lemma storeU_case (W : WORLD) (r : leibnizO Reg) (p p' : Perm) (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (rdst : RegName) (offs rsrc : Z + RegName):
    ftlr_instr W r p p' g b e a w (StoreU rdst offs rsrc) ρ.
  Proof.
    intros Hp Hsome i Hbae Hfp Hpwl Hregion Hnotrevoked Hnotmonostatic Hnotuninitialized HO Hi.
    iIntros "#IH #Hinv #Hreg #Hinva Hmono #Hw Hsts Hown".
    iIntros "Hr Hstate Ha HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.

    (* To read out PC's name later, and needed when calling wp_load *)
    assert(∀ x : RegName, is_Some (<[PC:=inr (p, g, b, e, a)]> r !! x)) as Hsome'.
    {
      intros. destruct (decide (x = PC)).
      rewrite e0 lookup_insert; unfold is_Some. by eexists.
        by rewrite lookup_insert_ne.
    }

    (* Initializing the names for the values of Hsrc now, to instantiate the existentials in step 1 *)
    assert (∃ p0 g0 b0 e0 a0 , read_reg_inr (<[PC:=inr (p, g, b, e, a)]> r) rdst p0 g0 b0 e0 a0) as [p0 [g0 [b0 [e0 [a0 HVdst] ] ] ] ].
    {
      specialize Hsome' with rdst as Hdst.
      destruct Hdst as [wdst Hsomedst].
      unfold read_reg_inr. destruct wdst. 2: destruct_cap c. all: repeat eexists.
      right. by exists z. by left.
    }

     assert (∃ storev, word_of_argument (<[PC:=inr (p, g, b, e, a)]> r) rsrc = Some storev) as [storev Hwoa].
    { destruct rsrc; cbn.
      - by exists (inl z).
      - specialize Hsome' with r0 as Hr0.
        destruct Hr0 as [wsrc Hsomer0].
        exists wsrc. by rewrite Hsomer0.
    }

    (* Step 1: open the region, if necessary, and store all the resources obtained from the region in allow_load_res *)
    iDestruct (create_store_res with "Hreg Hinva Hr Hsts") as "[HStoreRes Hsts]"; eauto.
    { destruct Hp as [-> | [-> | [-> _] ] ];auto. }
    { destruct Hp as [-> | [-> | [-> _] ] ];auto. }
    (* Clear helper values; they exist in the existential now *)
    clear HVdst p0 g0 b0 e0 a0 Hwoa storev.

    (* Step2: derive the concrete map of memory we need, and any spatial predicates holding over it *)
    iDestruct (store_res_implies_mem_map W  with "HStoreRes Ha") as (mem) "[HStoreMem HMemRes]".

    (* Step 3:  derive the non-spatial conditions over the memory map*)
    iDestruct (mem_map_implies_pure_conds _ _ _ _ _ _ _ _ _ _ offs with "HStoreMem") as %(HReadPC & HStoreAP); auto.

    iApply (wp_storeU_alt with "[$Hmap $HMemRes]");[apply Hi|apply HO|eauto|auto..].
    { by rewrite lookup_insert. }
    { rewrite /subseteq /map_subseteq /set_subseteq. intros rr _.
      apply elem_of_gmap_dom. rewrite lookup_insert_is_Some'; eauto. }
    iNext. iIntros (regs' mem' retv). iDestruct 1 as (HSpec) "[Hmem Hmap]".

    destruct HSpec as [* ? ? ? ? ? -> Hincr|].
    { destruct (addr_eq_dec a0 a').
      - subst. destruct (a' + 1)%a eqn:Hincr';inversion Hincr. 
        apply incrementPC_Some_inv in Hincr.

        destruct Hincr as (?&?&?&?&?&?&?&?&?).
        iApply wp_pure_step_later; auto. iNext.

        (* From this, derive value relation for the current PC*)
        iDestruct (execcPC_implies_interp _ _ _ _ _ a  with "Hinv") as "HVPC"; eauto.

        iDestruct (switch_monotonicity_formulation with "Hmono") as "Hmono"; [eauto..|].

        (* Step 4: return all the resources we had in order to close the second location in the region, in the cases where we need to *)
        iMod (mem_map_recover_res with "HStoreMem Hreg HVPC Hw Hmono Hmem Hsts") as (w') "(Hr & Hsts & Ha & #HSVInterp & Hmono & %)";eauto.
        { destruct Hp as [-> | [-> | [-> _] ] ];auto. }

        iDestruct (switch_monotonicity_formulation with "Hmono") as "Hmono"; auto.

        iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
        { destruct ρ;auto;[|specialize (Hnotmonostatic g1)|specialize (Hnotuninitialized w1)];try contradiction. }
        simplify_map_eq.

        iApply wp_wand_r.
        iSplitL. iApply ("IH" $! (new_worldU W a' p g b e a r offs) with "[%] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); auto.
        { cbn. intros x'. destruct (decide (rdst = x'));simplify_map_eq;eauto. }
        { iIntros (r1 Hne). destruct (decide (rdst = r1)).
          { subst. rewrite /RegLocate. assert (Hval:=H2).
            destruct H2 as [Hdst H2]. simplify_map_eq.
            iSpecialize ("Hreg" $! r1 Hne). rewrite Hdst.
            iApply (interp_initialize_limit with "Hreg");eauto. }
          { rewrite /RegLocate. simplify_map_eq. iSpecialize ("Hreg" $! r1 Hne).
            destruct (r !! r1) eqn:Hsomer;rewrite Hsomer.
            iApply (interp_monotone with "[] Hreg"). auto.
            rewrite !fixpoint_interp1_eq. done. 
          }
        }
        { iPureIntro. destruct (decide (rdst = PC));subst;[|simplify_map_eq;auto].
          unfold reg_allows_storeU in H2. 
          rewrite /incrementPC in H5. simplify_map_eq. destruct H2 as [H2 _]. inversion H2;subst;auto. }
        { destruct (decide (rdst = PC));subst;simplify_map_eq;auto.
          - unfold reg_allows_storeU in H2. 
            rewrite /incrementPC in H5. simplify_map_eq.
            destruct H2 as [H2 _]. inversion H2;subst;auto.
            iDestruct (interp_monotone with "[] HVPC") as "HVPC'";[iPureIntro;apply H8|].
            iClear "Hw HSVInterp HVPC".
            rewrite fixpoint_interp1_eq /=.
            destruct Hp as [-> | [-> | [-> _] ] ]; try iFrame "HVPC'". destruct x0; try done; iFrame "HVPC'". 
          - iDestruct (interp_monotone with "[] HVPC") as "HVPC'";[iPureIntro;apply H8|].
            iClear "Hw HSVInterp HVPC".
            rewrite fixpoint_interp1_eq /=.
            destruct Hp as [-> | [-> | [-> _] ] ]; try iFrame "HVPC'". destruct x0; try done; iFrame "HVPC'". 
        }
        iIntros (v) "Hv". iIntros (Hhalted).
        iDestruct ("Hv" $! Hhalted) as (r0 W') "(Hfull & Hregs & % & Hown & sts & Hr)".
        iExists _,_. iFrame. iPureIntro. eapply related_sts_pub_priv_trans_world;eauto.
      - apply incrementPC_Some_inv in Hincr.

        destruct Hincr as (?&?&?&?&?&?&?&?&?).
        iApply wp_pure_step_later; auto. iNext.

        (* From this, derive value relation for the current PC*)
        iDestruct (execcPC_implies_interp _ _ _ _ _ a  with "Hinv") as "HVPC"; eauto.

        iDestruct (switch_monotonicity_formulation with "Hmono") as "Hmono"; [eauto..|].

        (* Step 4: return all the resources we had in order to close the second location in the region, in the cases where we need to *)
        iMod (mem_map_recover_res with "HStoreMem Hreg HVPC Hw Hmono Hmem Hsts") as (w') "(Hr & Hsts & Ha & #HSVInterp & Hmono & %)";eauto.
        { destruct Hp as [-> | [-> | [-> _] ] ];auto. }

        iDestruct (switch_monotonicity_formulation with "Hmono") as "Hmono"; auto.

        iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
        { destruct ρ;auto;[|specialize (Hnotmonostatic g1)|specialize (Hnotuninitialized w1)];try contradiction. }
        simplify_map_eq.

        iApply wp_wand_r.
        iSplitL. iApply ("IH" $! (new_worldU W a0 x x0 x1 x2 x3 r offs) with "[%] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); auto.
        { iIntros (r1 Hne). destruct (decide (rdst = r1)).
          { subst. rewrite /RegLocate. assert (Hval:=H2).
            destruct H2 as [Hdst H2]. simplify_map_eq.
            iSpecialize ("Hreg" $! r1 Hne). rewrite Hdst.
            iApply (interp_monotone with "[] Hreg"). auto. }
          { rewrite /RegLocate. simplify_map_eq. iSpecialize ("Hreg" $! r1 Hne).
            destruct (r !! r1) eqn:Hsomer;rewrite Hsomer.
            iApply (interp_monotone with "[] Hreg"). auto.
            rewrite !fixpoint_interp1_eq. done. 
          }
        }
        { destruct (decide (rdst = PC));subst;simplify_map_eq;auto.
          - unfold reg_allows_storeU in H2. 
            rewrite /incrementPC in H5. simplify_map_eq.
            destruct H2 as [H2 _]. inversion H2;subst;auto.
            iDestruct (interp_monotone with "[] HVPC") as "HVPC'";[iPureIntro;apply H7|].
            iClear "Hw HSVInterp HVPC".
            rewrite fixpoint_interp1_eq /=.
            destruct Hp as [-> | [-> | [-> _] ] ]; try iFrame "HVPC'". destruct g0; try done; iFrame "HVPC'". 
          - iDestruct (interp_monotone with "[] HVPC") as "HVPC'";[iPureIntro;apply H7|].
            iClear "Hw HSVInterp HVPC".
            rewrite fixpoint_interp1_eq /=.
            destruct Hp as [-> | [-> | [-> _] ] ]; try iFrame "HVPC'". destruct x0; try done; iFrame "HVPC'". 
        }
        iIntros (v) "Hv". iIntros (Hhalted).
        iDestruct ("Hv" $! Hhalted) as (r0 W') "(Hfull & Hregs & % & Hown & sts & Hr)".
        iExists _,_. iFrame. iPureIntro. eapply related_sts_pub_priv_trans_world;eauto.
    }
    { iApply wp_pure_step_later; auto. iNext. iApply wp_value; auto. iIntros; discriminate. }
    Unshelve. all: auto.
  Qed.

End fundamental.
