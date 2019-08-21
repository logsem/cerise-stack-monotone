From cap_machine Require Export logrel monotone.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base. 

Section fundamental.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ}.
  Notation D := ((leibnizC Word) -n> iProp Σ).
  Notation R := ((leibnizC Reg) -n> iProp Σ).
  Implicit Types w : (leibnizC Word).
  Implicit Types interp : D.

  Lemma extract_r_ex reg (r : RegName) :
    (∃ w, reg !! r = Some w) →
    (([∗ map] r0↦w ∈ reg, r0 ↦ᵣ w) → ∃ w, r ↦ᵣ w)%I. 
  Proof.
    intros [w Hw].
    iIntros "Hmap". iExists w. 
    iApply (big_sepM_lookup (λ r i, r ↦ᵣ i)%I reg r w); eauto. 
  Qed.

  Lemma extract_r reg (r : RegName) w :
    reg !! r = Some w →
    (([∗ map] r0↦w ∈ reg, r0 ↦ᵣ w) →
     (r ↦ᵣ w ∗ (∀ x', r ↦ᵣ x' -∗ [∗ map] k↦y ∈ <[r := x']> reg, k ↦ᵣ y)))%I.
  Proof.
    iIntros (Hw) "Hmap". 
    iDestruct (big_sepM_lookup_acc (λ r i, r ↦ᵣ i)%I reg r w) as "Hr"; eauto.
    iSpecialize ("Hr" with "[Hmap]"); eauto. iDestruct "Hr" as "[Hw Hmap]".
    iDestruct (big_sepM_insert_acc (λ r i, r ↦ᵣ i)%I reg r w) as "Hupdate"; eauto.
    iSpecialize ("Hmap" with "[Hw]"); eauto. 
    iSpecialize ("Hupdate" with "[Hmap]"); eauto.
  Qed.

  Lemma interp_cap_preserved E fs fr p l a2 a1 a0 a3 (Hne: p <> cap_lang.E):
    (((fixpoint interp1) E) (fs, fr)) (inr (p, l, a2, a1, a0)) -∗
    (((fixpoint interp1) E) (fs, fr)) (inr (p, l, a2, a1, a3)).
  Proof.
    repeat rewrite fixpoint_interp1_eq. simpl. iIntros "HA".
    destruct p; auto.
    - iDestruct "HA" as (g b e a ws) "(HA & HB & HC)".
      iDestruct "HA" as %?. inv H3.
      iExists g, b, e, a3, ws. iFrame; auto.
    - iDestruct "HA" as (p g b e a) "(HA & HB & HC)".
      iDestruct "HA" as %?. inv H3.
      iExists RW, g, b, e, a3. iFrame; auto.
    - iDestruct "HA" as (p g b e a) "(HA & HB & HC)".
      iDestruct "HA" as %?. inv H3.
      iExists RWL, g, b, e, a3. iFrame; auto.
    - iDestruct "HA" as (p g b e a ws) "(HA & HB & HC)".
      iDestruct "HA" as %?. inv H3.
      iExists RX, g, b, e, a3, ws. iFrame; auto.
    - elim Hne; reflexivity.
    - iDestruct "HA" as (p g b e a) "(HA & HB & HC)".
      iDestruct "HA" as %?. inv H3.
      iExists RWX, g, b, e, a3. iFrame; auto.
    - iDestruct "HA" as (p g b e a) "(HA & HB & HC)".
      iDestruct "HA" as %?. inv H3.
      iExists RWLX, g, b, e, a3. iFrame; auto.
  Qed.

  Lemma PermPairFlows_interp_preserved E fs fr p p' l l' a2 a1 a0:
    PermPairFlowsTo (p', l') (p, l) = true ->
    na_own logrel_nais E -∗
    (((fixpoint interp1) E) (fs, fr)) (inr (p, l, a2, a1, a0)) ={⊤}=∗
    (((fixpoint interp1) E) (fs, fr)) (inr (p', l', a2, a1, a0)).
  Proof.
    intros. iIntros "Hown HA".
    destruct (andb_true_eq _ _ ltac:(symmetry in H3; exact H3)).
    simpl in H4. repeat rewrite fixpoint_interp1_eq.
    destruct p; destruct p'; simpl in H4; try congruence; simpl; match goal with | H: PermPairFlowsTo (O, _) (_, _) = _ |- _ => auto | _ => idtac end.
    - iDestruct "HA" as (g b e a ws) "[% [HB HC]]".
      inv H6. iExists l', b, e, a, ws. iFrame. auto.
    - iDestruct "HA" as (p g b e a) "[% [% #Hinv]]".
      inv H6. iExists l', b, e, a.
      iMod (na_inv_open _ _ _ (logN.@(b, e)) with "Hinv Hown") as "(Hregion & Hown & Hcls)"; auto.
      iDestruct "Hregion" as (ws) "Hregion".
      iExists ws. iAssert (⌜↑logN.@(b, e) ⊆ E⌝)%I as "HA". iPureIntro; auto.
      iFrame. iAssert (|={⊤}=> na_inv logrel_nais (logN.@(b, e)) (read_only_cond b e ws (fixpoint interp1)))%I with "[Hregion Hown Hcls]" as "HA".
      { iApply (na_inv_alloc). iNext. rewrite /read_only_cond.
        iDestruct "Hregion" as "(Hbe & Hstsf)".
        iFrame. iIntros. iDestruct ("Hstsf" $! stsf E0) as "Hstsf".
        iDestruct (big_sepL_later with "Hstsf") as "Hstsf".
        iApply big_sepL_later. iNext.
        iDestruct (big_sepL_sepL with "Hstsf") as "[Hstsf1 Hstsf2]".
        iFrame. }
      iMod "HA" as "HA". iModIntro. iFrame. auto.
    - iDestruct "HA" as (p g b e a) "[% [HB HC]]".
      inv H6. iExists RW,l',b,e,a.
      iFrame. auto.
    - iDestruct "HA" as (p g b e a) "[% [% #Hinv]]".
      inv H6. iExists l', b, e, a.
      iMod (na_inv_open _ _ _ (logN.@(b, e)) with "Hinv Hown") as "(Hregion & Hown & Hcls)"; auto.
      iDestruct "Hregion" as (ws) "Hregion".
      iExists ws. iAssert (⌜↑logN.@(b, e) ⊆ E⌝)%I as "HA". iPureIntro; auto.
      iFrame. iAssert (|={⊤}=> na_inv logrel_nais (logN.@(b, e)) (read_only_cond b e ws (fixpoint interp1)))%I with "[Hregion Hown Hcls]" as "HA".
      { iApply (na_inv_alloc). iNext. rewrite /read_only_cond.
        iDestruct "Hregion" as "(Hbe & Hstsf)".
        iFrame. }
      iMod "HA" as "HA". iModIntro. iFrame. auto.
    - (* PermPairFlowsTo (RW, l') (RWL, l) = true *)
      iDestruct "HA" as (p g b e a) "[% [% #Hinv]]".
      inv H6. iExists RW, l', b, e, a.
      iMod (na_inv_open _ _ _ (logN.@(b, e)) with "Hinv Hown") as "(Hregion & Hown & Hcls)"; auto.
      iDestruct "Hregion" as (ws) "Hregion".
      iAssert (⌜↑logN.@(b, e) ⊆ E⌝)%I as "HA". iPureIntro; auto.
      iFrame. iAssert (|={⊤}=> na_inv logrel_nais (logN.@(b, e)) (read_write_cond b e (fixpoint interp1)))%I with "[Hregion Hown Hcls]" as "HA".
      { iApply (na_inv_alloc). iNext. rewrite /read_write_cond.
        iExists ws. iDestruct "Hregion" as "(Hbe & Hstsf)". iFrame.
        iIntros. iDestruct ("Hstsf" $! stsf E0) as "Hstsf".
        iDestruct (big_sepL_later with "Hstsf") as "Hstsf".
        iApply big_sepL_later.
        iNext. iApply big_sepL_sepL. iSplitL "Hstsf"; auto.
        
        (* Not proveable *) admit. }
      admit.
    - iDestruct "HA" as (p g b e a) "[% [% #Hinv]]".
      inv H6. iExists RWL, l', b, e, a. auto.
    - iDestruct "HA" as (p g b e a ws) "[% [% [#Hinv Hexec]]]".
      inv H6. iExists l', b, e, a, ws.
      iModIntro. iSplitR; auto.
    - iDestruct "HA" as (p g b e a ws) "[% [HA [Hinv HB]]]".
      inv H6. iExists RX,l',b,e,a,ws.
      iModIntro. iFrame.
  Admitted.
  
  Instance addr_inhabited: Inhabited Addr := populate (A 0%Z eq_refl).

  Lemma RX_Jmp_case:
    ∀ (E0 : coPset) (r : leibnizC Reg) (a : Addr) (g : Locality) (fs : leibnizC STS_states) (fr : leibnizC STS_rels) 
      (b e : Addr) (ws : list Word) (w : Word) (r0 : RegName)
      (fundamental_RWX : ∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) (E : coPset) (r : leibnizC Reg) 
                      (b e : Addr) (g : Locality) (a : Addr), (na_inv logrel_nais (logN.@(b, e))
                                                                 (read_write_cond b e interp)
                                                               → (λ (stsf0 : prodC (leibnizC STS_states) (leibnizC STS_rels)) 
                                                                    (E0 : coPset) (r0 : leibnizC Reg), 
                                                                  ((interp_expression E0 r0) stsf0) 
                                                                    (inr (RWX, g, b, e, a))) stsf E r)%I)
      (fundamental_RWLX : ∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) (E : coPset) (r : leibnizC Reg) 
                       (b e : Addr) (g : Locality) (a : Addr), (na_inv logrel_nais (logN.@(b, e))
                                                                  (read_write_local_cond b e interp)
                                                                → (λ (stsf0 : prodC (leibnizC STS_states)
                                                                                (leibnizC STS_rels)) 
                                                                     (E0 : coPset) (r0 : leibnizC Reg), 
                                                                   ((interp_expression E0 r0) stsf0)
                                                                     (inr (RWLX, g, b, e, a))) stsf E r)%I)
      (Hreach : ∀ ns : namespace, Some (logN.@(b, e)) = Some ns → ↑ns ⊆ E0)
      (H3 : ∀ x : RegName, (λ x0 : RegName, is_Some (r !! x0)) x)
      (i : isCorrectPC (inr (RX, g, b, e, a)))
      (Hbae : (b <= a)%a ∧ (a <= e)%a)
      (Hbe : ↑logN.@(b, e) ⊆ E0)
      (Hi : cap_lang.decode w = Jmp r0),
      □ ▷ ▷ ((interp E0) (fs, fr)) w
        -∗ □ ▷ ([∗ list] w0 ∈ ws, ▷ ((interp E0) (fs, fr)) w0)
        -∗ □ ▷ (∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) (E1 : leibnizC coPset), [∗ list] w0 ∈ ws, ▷ 
                                                                                                                       ((interp E1) stsf) w0)
        -∗ □ (∀ r0 : RegName, ⌜r0 ≠ PC⌝ → (((fixpoint interp1) E0) (fs, fr)) (r !r! r0))
        -∗ □ na_inv logrel_nais (logN.@(b, e))
        ([[b,e]]↦ₐ[[ws]]
                ∗ (∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) (E1 : leibnizC coPset), [∗ list] w0 ∈ ws, ▷ 
                                                                                                                          ((interp E1) stsf) w0))
        -∗ □ ▷ (∀ (a0 : leibnizC Reg) (a1 : Addr) (a2 : Locality) (a3 : leibnizC STS_states) 
                  (a4 : leibnizC STS_rels) (a5 a6 : Addr) (a7 : list Word), full_map a0
                                                                                     -∗ (∀ r0 : RegName, 
                                                                                            ⌜r0 ≠ PC⌝
                                                                                            → (((fixpoint interp1) E0) (a3, a4))
                                                                                                (a0 !r! r0))
                                                                                     -∗ registers_mapsto
                                                                                     (<[PC:=
                                                                                          inr (RX, a2, a5, a6, a1)]> a0)
                                                                                     -∗ sts_full a3 a4
                                                                                     -∗ na_own logrel_nais E0
                                                                                     -∗ 
                                                                                     □ 
                                                                                     na_inv logrel_nais
                                                                                     (logN.@(a5, a6))
                                                                                     ([[a5,a6]]↦ₐ[[a7]]
                                                                                               ∗ 
                                                                                               (∀ (stsf : 
                                                                                                     prodC 
                                                                                                       (leibnizC STS_states)
                                                                                                       (leibnizC STS_rels)) 
                                                                                                  (E1 : 
                                                                                                     leibnizC coPset), [∗ list] w0 ∈ a7, ▷ 
                                                                                                                                           ((interp E1) stsf) w0))
                                                                                     -∗ 
                                                                                     □ ⌜
                                                                                     ∀ ns : namespace, 
                                                                                       Some (logN.@(a5, a6)) =
                                                                                       Some ns → 
                                                                                       ↑ns ⊆ E0⌝ -∗ 
                                                                                        ⟦ [a3, a4, E0] ⟧ₒ)
        -∗ ([∗ map] k↦y ∈ delete PC (<[PC:=inr (RX, g, b, e, a)]> r), k ↦ᵣ y)
        -∗ PC ↦ᵣ inr (RX, g, b, e, a)
        -∗ ▷ match (a + 1)%a with
             | Some ah =>
               [[ah,e]]↦ₐ[[drop (S (length (region_addrs b (get_addr_from_option_addr (a + -1)%a)))) ws]]
             | None => ⌜drop (S (length (region_addrs b (get_addr_from_option_addr (a + -1)%a)))) ws = []⌝
             end
        -∗ a ↦ₐ w
        -∗ ▷ ([[b,get_addr_from_option_addr (a + -1)%a]]↦ₐ[[take
                                                              (length
                                                                 (region_addrs b
                                                                               (get_addr_from_option_addr
                                                                                  (a + -1)%a))) ws]])
        -∗ ▷ ⌜ws =
      take (length (region_addrs b (get_addr_from_option_addr (a + -1)%a))) ws ++
           w :: drop (S (length (region_addrs b (get_addr_from_option_addr (a + -1)%a)))) ws⌝
           -∗ (▷ ([[b,e]]↦ₐ[[ws]]
                         ∗ (∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) 
                              (E1 : leibnizC coPset), [∗ list] w0 ∈ ws, ▷ ((interp E1) stsf) w0))
                 ∗ na_own logrel_nais (E0 ∖ ↑logN.@(b, e)) ={⊤}=∗ na_own logrel_nais E0)
           -∗ na_own logrel_nais (E0 ∖ ↑logN.@(b, e))
           -∗ sts_full fs fr
           -∗ WP Instr Executable
           {{ v, WP fill [SeqCtx] (of_val v)
                    {{ v0, ⌜v0 = HaltedV⌝
                           → ∃ (r0 : Reg) (fs' : STS_states) (fr' : STS_rels), 
                           full_map r0
                           ∧ registers_mapsto r0
                                              ∗ ⌜related_sts_priv fs fs' fr fr'⌝
                                              ∗ na_own logrel_nais E0 ∗ sts_full fs' fr' }} }}.
  Proof.
    intros E0 r a g fs fr b e ws w. intros.
    iIntros "#Hva #Hval' #Hval #Hreg #Hinv #IH".
    iIntros "Hmap HPC Hh Ha Hregionl Heqws Hcls Hown Hsts".
    rewrite delete_insert_delete.
    destruct (reg_eq_dec PC r0).
    * subst r0.
      iApply (wp_jmp_successPC with "[HPC Ha]"); eauto; iFrame.
      iNext. iIntros "[HPC Ha] /=".
      iApply wp_pure_step_later; auto.
      (* reconstruct regions *)
      iNext. 
      iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E0) (fs, fr)) with
                     "[Heqws Hregionl Hh Ha]") as "[Hbe Hbev]"; eauto.
      { iExists w. iFrame. iFrame "#". }
      iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
      (* reestablish invariant *)
      iMod ("Hcls" with "[$Hbe Hbev $Hown]") as "Hown".
      { iNext. iIntros (stsf' E'). rewrite -big_sepL_later. iNext. auto. }
      (* apply IH *)
      iApply ("IH" $! _ _ _ _ _ _ _ ws with "[] Hreg Hmap Hsts Hown");
        iFrame "#"; [iPureIntro;eauto|iAlways;iPureIntro;eauto]. 
    * specialize H3 with r0 as Hr0.
      destruct Hr0 as [wsrc Hsomesrc].
      iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hsrc Hmap]"; eauto.
      rewrite (lookup_delete_ne r PC r0); eauto.
      iApply (wp_jmp_success with "[HPC Ha Hsrc]"); eauto; iFrame.
      iNext. iIntros "[HPC [Ha Hsrc]] /=".
      iApply wp_pure_step_later; auto. iNext. 
      (* reconstruct regions *)
      iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E0) (fs, fr)) with
                     "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto.
      { iExists w. iFrame. auto. }
      iDestruct ((big_sepM_delete _ _ r0) with "[Hsrc Hmap]") as "Hmap /=";
        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
      rewrite -delete_insert_ne; auto.
      iMod ("Hcls" with "[Hregion $Hown]") as "Hcls'".
      { iNext. iDestruct "Hregion" as "[$ _]". 
        iIntros (stsf' E'). rewrite -big_sepL_later. auto. }
      destruct (updatePcPerm wsrc) eqn:Heq.
      { iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_notCorrectPC with "HPC"); [intro; match goal with H: isCorrectPC (inl _) |- _ => inv H end|].
        iNext. iIntros "HPC /=".
        iApply wp_pure_step_later; auto.
        iApply wp_value.
        iNext. iIntros. discriminate. }
      { destruct c,p,p,p.
        destruct p.
        - iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros. discriminate.
        - iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros. discriminate.
        - iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros. discriminate.
        - iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros. discriminate.
        - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
          apply lookup_insert. rewrite delete_insert_delete. iFrame.
          rewrite (insert_id r r0); auto.
          iApply ("IH" with "[] [] [Hmap] [Hsts] [Hcls']"); eauto; admit.
        - iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros. discriminate.
        - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
          apply lookup_insert. rewrite delete_insert_delete. iFrame.
          rewrite (insert_id r r0); auto.
          (* use fundamental_RWX in some way ? *) admit.
        - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
          apply lookup_insert. rewrite delete_insert_delete. iFrame.
          rewrite (insert_id r r0); auto.
          (* use fundamental_RWLX in some way ? *) admit. }
  Admitted.




  Lemma RX_Jnz_case:
    ∀ (E0 : coPset) (r : leibnizC Reg) (a : Addr) (g : Locality) (fs : leibnizC STS_states) (fr : leibnizC STS_rels) 
      (b e : Addr) (ws : list Word) (w : Word) (r1 r2: RegName)
      (fundamental_RWX : ∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) (E : coPset) (r : leibnizC Reg) 
                           (b e : Addr) (g : Locality) (a : Addr), (na_inv logrel_nais (logN.@(b, e))
                                                                           (read_write_cond b e interp)
                                                                    → (λ (stsf0 : prodC (leibnizC STS_states) (leibnizC STS_rels)) 
                                                                         (E0 : coPset) (r0 : leibnizC Reg), 
                                                                       ((interp_expression E0 r0) stsf0) 
                                                                         (inr (RWX, g, b, e, a))) stsf E r)%I)
      (fundamental_RWLX : ∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) (E : coPset) (r : leibnizC Reg) 
                            (b e : Addr) (g : Locality) (a : Addr), (na_inv logrel_nais (logN.@(b, e))
                                                                            (read_write_local_cond b e interp)
                                                                     → (λ (stsf0 : prodC (leibnizC STS_states)
                                                                                         (leibnizC STS_rels)) 
                                                                          (E0 : coPset) (r0 : leibnizC Reg), 
                                                                        ((interp_expression E0 r0) stsf0)
                                                                          (inr (RWLX, g, b, e, a))) stsf E r)%I)
      (Hreach : ∀ ns : namespace, Some (logN.@(b, e)) = Some ns → ↑ns ⊆ E0)
      (H3 : ∀ x : RegName, (λ x0 : RegName, is_Some (r !! x0)) x)
      (i : isCorrectPC (inr (RX, g, b, e, a)))
      (Hbae : (b <= a)%a ∧ (a <= e)%a)
      (Hbe : ↑logN.@(b, e) ⊆ E0)
      (Hi : cap_lang.decode w = Jnz r1 r2),
      □ ▷ ▷ ((interp E0) (fs, fr)) w
        -∗ □ ▷ ([∗ list] w0 ∈ ws, ▷ ((interp E0) (fs, fr)) w0)
        -∗ □ ▷ (∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) (E1 : leibnizC coPset), [∗ list] w0 ∈ ws, ▷ 
                                                                                                                       ((interp E1) stsf) w0)
        -∗ □ (∀ r0 : RegName, ⌜r0 ≠ PC⌝ → (((fixpoint interp1) E0) (fs, fr)) (r !r! r0))
        -∗ □ na_inv logrel_nais (logN.@(b, e))
        ([[b,e]]↦ₐ[[ws]]
                ∗ (∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) (E1 : leibnizC coPset), [∗ list] w0 ∈ ws, ▷ 
                                                                                                                          ((interp E1) stsf) w0))
        -∗ □ ▷ (∀ (a0 : leibnizC Reg) (a1 : Addr) (a2 : Locality) (a3 : leibnizC STS_states) 
                  (a4 : leibnizC STS_rels) (a5 a6 : Addr) (a7 : list Word), full_map a0
                                                                                     -∗ (∀ r0 : RegName, 
                                                                                            ⌜r0 ≠ PC⌝
                                                                                            → (((fixpoint interp1) E0) (a3, a4))
                                                                                                (a0 !r! r0))
                                                                                     -∗ registers_mapsto
                                                                                     (<[PC:=
                                                                                          inr (RX, a2, a5, a6, a1)]> a0)
                                                                                     -∗ sts_full a3 a4
                                                                                     -∗ na_own logrel_nais E0
                                                                                     -∗ 
                                                                                     □ 
                                                                                     na_inv logrel_nais
                                                                                     (logN.@(a5, a6))
                                                                                     ([[a5,a6]]↦ₐ[[a7]]
                                                                                               ∗ 
                                                                                               (∀ (stsf : 
                                                                                                     prodC 
                                                                                                       (leibnizC STS_states)
                                                                                                       (leibnizC STS_rels)) 
                                                                                                  (E1 : 
                                                                                                     leibnizC coPset), [∗ list] w0 ∈ a7, ▷ 
                                                                                                                                           ((interp E1) stsf) w0))
                                                                                     -∗ 
                                                                                     □ ⌜
                                                                                     ∀ ns : namespace, 
                                                                                       Some (logN.@(a5, a6)) =
                                                                                       Some ns → 
                                                                                       ↑ns ⊆ E0⌝ -∗ 
                                                                                        ⟦ [a3, a4, E0] ⟧ₒ)
        -∗ ([∗ map] k↦y ∈ delete PC (<[PC:=inr (RX, g, b, e, a)]> r), k ↦ᵣ y)
        -∗ PC ↦ᵣ inr (RX, g, b, e, a)
        -∗ ▷ match (a + 1)%a with
             | Some ah =>
               [[ah,e]]↦ₐ[[drop (S (length (region_addrs b (get_addr_from_option_addr (a + -1)%a)))) ws]]
             | None => ⌜drop (S (length (region_addrs b (get_addr_from_option_addr (a + -1)%a)))) ws = []⌝
             end
        -∗ a ↦ₐ w
        -∗ ▷ ([[b,get_addr_from_option_addr (a + -1)%a]]↦ₐ[[take
                                                              (length
                                                                 (region_addrs b
                                                                               (get_addr_from_option_addr
                                                                                  (a + -1)%a))) ws]])
        -∗ ▷ ⌜ws =
      take (length (region_addrs b (get_addr_from_option_addr (a + -1)%a))) ws ++
           w :: drop (S (length (region_addrs b (get_addr_from_option_addr (a + -1)%a)))) ws⌝
           -∗ (▷ ([[b,e]]↦ₐ[[ws]]
                         ∗ (∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) 
                              (E1 : leibnizC coPset), [∗ list] w0 ∈ ws, ▷ ((interp E1) stsf) w0))
                 ∗ na_own logrel_nais (E0 ∖ ↑logN.@(b, e)) ={⊤}=∗ na_own logrel_nais E0)
           -∗ na_own logrel_nais (E0 ∖ ↑logN.@(b, e))
           -∗ sts_full fs fr
           -∗ WP Instr Executable
           {{ v, WP fill [SeqCtx] (of_val v)
                    {{ v0, ⌜v0 = HaltedV⌝
                           → ∃ (r0 : Reg) (fs' : STS_states) (fr' : STS_rels), 
                           full_map r0
                           ∧ registers_mapsto r0
                                              ∗ ⌜related_sts_priv fs fs' fr fr'⌝
                                              ∗ na_own logrel_nais E0 ∗ sts_full fs' fr' }} }}.
  Proof.
    intros E r a g fs fr b e ws w. intros.
    iIntros "#Hva #Hval' #Hval #Hreg #Hinv #IH".
    iIntros "Hmap HPC Hh Ha Hregionl Heqws Hcls Hown Hsts".
    rewrite delete_insert_delete.
    destruct (reg_eq_dec PC r2).
    * subst r2.
      destruct (reg_eq_dec PC r1).
      { subst r1. iApply (wp_jnz_success_jmpPC with "[HPC Ha]"); eauto; iFrame.
        iNext. iIntros "(HPC & Ha)".
        simpl. iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
        apply lookup_insert. rewrite delete_insert_delete. iFrame.
        iApply wp_pure_step_later; auto. iNext.
        iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr)) with
                       "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto.
        { iExists w. iFrame. iFrame "#". }
        iMod ("Hcls" with "[Hregion $Hown]") as "Hcls'".
        { iNext. iDestruct "Hregion" as "[$ _]". 
          iIntros (stsf' E'). rewrite -big_sepL_later. auto. }
        iApply ("IH" with "[] [] [Hmap] [Hsts] [Hcls']"); eauto. }
      { destruct (H3 r1) as [wr1 Hsomer1].
        iDestruct ((big_sepM_delete _ _ r1) with "Hmap") as "[Hr1 Hmap]".
        { rewrite lookup_delete_ne; eauto. }
        iApply (wp_jnz_success_jmpPC2 with "[HPC Hr1 Ha]"); eauto; iFrame.
        iNext. iIntros "(HPC & Ha & Hr1)".
        iApply wp_pure_step_later; auto. iNext.
        iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr)) with
                       "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto.
        { iExists w. iFrame. auto. }
        iDestruct ((big_sepM_delete _ _ r1) with "[Hr1 Hmap]") as "Hmap /=";
          [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
        rewrite -delete_insert_ne; auto.
        iMod ("Hcls" with "[Hregion $Hown]") as "Hcls'".
        { iNext. iDestruct "Hregion" as "[$ _]". 
          iIntros (stsf' E'). rewrite -big_sepL_later. auto. }
        destruct (updatePcPerm wr1) eqn:Heq.
        { iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [intro; match goal with H: isCorrectPC (inl _) |- _ => inv H end|].
          iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros. discriminate. }
        { destruct c,p,p,p.
          destruct p.
          - iApply (wp_bind (fill [SeqCtx])).
            iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
            iNext. iIntros "HPC /=".
            iApply wp_pure_step_later; auto.
            iApply wp_value.
            iNext. iIntros. discriminate.
          - iApply (wp_bind (fill [SeqCtx])).
            iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
            iNext. iIntros "HPC /=".
            iApply wp_pure_step_later; auto.
            iApply wp_value.
            iNext. iIntros. discriminate.
          - iApply (wp_bind (fill [SeqCtx])).
            iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
            iNext. iIntros "HPC /=".
            iApply wp_pure_step_later; auto.
            iApply wp_value.
            iNext. iIntros. discriminate.
          - iApply (wp_bind (fill [SeqCtx])).
            iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
            iNext. iIntros "HPC /=".
            iApply wp_pure_step_later; auto.
            iApply wp_value.
            iNext. iIntros. discriminate.
          - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
            apply lookup_insert. rewrite delete_insert_delete. iFrame.
            rewrite (insert_id r r1); auto.
            iApply ("IH" with "[] [] [Hmap] [Hsts] [Hcls']"); eauto; admit.
          - iApply (wp_bind (fill [SeqCtx])).
            iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
            iNext. iIntros "HPC /=".
            iApply wp_pure_step_later; auto.
            iApply wp_value.
            iNext. iIntros. discriminate.
          - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
            apply lookup_insert. rewrite delete_insert_delete. iFrame.
            rewrite (insert_id r r1); auto.
            (* use fundamental_RWX in some way ? *) admit.
          - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
            apply lookup_insert. rewrite delete_insert_delete. iFrame.
            rewrite (insert_id r r1); auto.
            (* use fundamental_RWLX in some way ? *) admit. } }
    * destruct (H3 r2) as [wr2 Hsomer2].
      iDestruct ((big_sepM_delete _ _ r2) with "Hmap") as "[Hr2 Hmap]".
      { rewrite lookup_delete_ne; eauto. }
      case_eq (nonZero wr2); intros.
      { assert (wr2 <> inl 0%Z) by (intro; subst wr2; cbv in H4; congruence).
        destruct (reg_eq_dec PC r1).
        - subst r1. iApply (wp_jnz_success_jmpPC1 with "[HPC Hr2 Ha]"); eauto; iFrame.
          iNext. iIntros "(HPC & Ha & Hr2)".
          iApply wp_pure_step_later; auto. iNext.
          simpl. iDestruct ((big_sepM_delete _ _ r2) with "[Hr2 Hmap]") as "Hmap /=";
                   [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
          rewrite -delete_insert_ne; auto.
          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
          apply lookup_insert. rewrite delete_insert_delete. iFrame.
          rewrite (insert_id r r2); auto.
          iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr)) with
                         "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto.
          { iExists w. iFrame. iFrame "#". }
          iMod ("Hcls" with "[Hregion $Hown]") as "Hcls'".
          { iNext. iDestruct "Hregion" as "[$ _]". 
            iIntros (stsf' E'). rewrite -big_sepL_later. auto. }
          iApply ("IH" with "[] [] [Hmap] [Hsts] [Hcls']"); eauto.
        - destruct (reg_eq_dec r2 r1).
          + subst r1. iApply (wp_jnz_success_jmp2 with "[HPC Hr2 Ha]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha & Hr2)".
            iApply wp_pure_step_later; auto. iNext.
            simpl. iDestruct ((big_sepM_delete _ _ r2) with "[Hr2 Hmap]") as "Hmap /=";
                     [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
            rewrite -delete_insert_ne; auto.
            rewrite (insert_id r r2); auto.
            iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr)) with
                           "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto.
            { iExists w. iFrame. iFrame "#". }
            iMod ("Hcls" with "[Hregion $Hown]") as "Hcls'".
            { iNext. iDestruct "Hregion" as "[$ _]". 
              iIntros (stsf' E'). rewrite -big_sepL_later. auto. }
            destruct (updatePcPerm wr2) eqn:Heq.
            { iApply (wp_bind (fill [SeqCtx])).
              iApply (wp_notCorrectPC with "HPC"); [intro; match goal with H: isCorrectPC (inl _) |- _ => inv H end|].
              iNext. iIntros "HPC /=".
              iApply wp_pure_step_later; auto.
              iApply wp_value.
              iNext. iIntros. discriminate. }
            { destruct c,p,p,p.
              destruct p.
              - iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate.
              - iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate.
              - iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate.
              - iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate.
              - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
                apply lookup_insert. rewrite delete_insert_delete. iFrame.
                iApply ("IH" with "[] [] [Hmap] [Hsts] [Hcls']"); eauto; admit.
              - iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate.
              - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
                apply lookup_insert. rewrite delete_insert_delete. iFrame.
                (* use fundamental_RWX in some way ? *) admit.
              - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
                apply lookup_insert. rewrite delete_insert_delete. iFrame.
                (* use fundamental_RWLX in some way ? *) admit. }
          + destruct (H3 r1) as [wr1 Hsomer1].
            iDestruct ((big_sepM_delete _ _ r1) with "Hmap") as "[Hr1 Hmap]".
            { repeat rewrite lookup_delete_ne; eauto. }
            iApply (wp_jnz_success_jmp with "[HPC Hr1 Hr2 Ha]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha & Hr1 & Hr2)".
            iApply wp_pure_step_later; auto. iNext.
            simpl. iDestruct ((big_sepM_delete _ _ r1) with "[Hr1 Hmap]") as "Hmap /=";
                     [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
            repeat rewrite -delete_insert_ne; auto.
            rewrite (insert_id r r1); auto.
            iDestruct ((big_sepM_delete _ _ r2) with "[Hr2 Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
            rewrite -delete_insert_ne; auto. rewrite (insert_id r r2); auto.
            iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr)) with
                           "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto.
            { iExists w. iFrame. iFrame "#". }
            iMod ("Hcls" with "[Hregion $Hown]") as "Hcls'".
            { iNext. iDestruct "Hregion" as "[$ _]". 
              iIntros (stsf' E'). rewrite -big_sepL_later. auto. }
            destruct (updatePcPerm wr1) eqn:Heq.
            { iApply (wp_bind (fill [SeqCtx])).
              iApply (wp_notCorrectPC with "HPC"); [intro; match goal with H: isCorrectPC (inl _) |- _ => inv H end|].
              iNext. iIntros "HPC /=".
              iApply wp_pure_step_later; auto.
              iApply wp_value.
              iNext. iIntros. discriminate. }
            { destruct c,p,p,p.
              destruct p.
              - iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate.
              - iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate.
              - iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate.
              - iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate.
              - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
                apply lookup_insert. rewrite delete_insert_delete. iFrame.
                iApply ("IH" with "[] [] [Hmap] [Hsts] [Hcls']"); eauto; admit.
              - iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate.
              - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
                apply lookup_insert. rewrite delete_insert_delete. iFrame.
                (* use fundamental_RWX in some way ? *) admit.
              - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
                apply lookup_insert. rewrite delete_insert_delete. iFrame.
                (* use fundamental_RWLX in some way ? *) admit. } }
      { assert (wr2 = inl 0%Z) by (destruct wr2; cbv in H4; try congruence; destruct z; try congruence).
        subst wr2. case_eq (a+1)%a; intros.
        - iApply (wp_jnz_success_next with "[HPC Ha Hr2]"); eauto; iFrame.
          iNext. iIntros "(HPC & Ha & Hr2)".
          iApply wp_pure_step_later; auto. iNext.
          iDestruct ((big_sepM_delete _ _ r2) with "[Hr2 Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
          rewrite -delete_insert_ne; auto. rewrite (insert_id r r2); auto.
          iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr)) with
                         "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto.
          { iExists w. rewrite H5. iFrame. iFrame "#". }
          iMod ("Hcls" with "[Hregion $Hown]") as "Hcls'".
          { iNext. iDestruct "Hregion" as "[$ _]". 
            iIntros (stsf' E'). rewrite -big_sepL_later. auto. }
          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
          iApply ("IH" with "[] [] [Hmap] [Hsts] [Hcls']"); eauto.
        - iApply (wp_jnz_fail_next with "[HPC Ha Hr2]"); eauto; iFrame.
          iNext. iIntros "(HPC & Ha & Hr2)".
          iApply wp_pure_step_later; auto. iNext.
          iApply wp_value. iIntros. discriminate. }
  Admitted.

  Lemma RX_Mov_case:
    ∀ (E0 : coPset) (r : leibnizC Reg) (a : Addr) (g : Locality) (fs : leibnizC STS_states) (fr : leibnizC STS_rels) 
      (b e : Addr) (ws : list Word) (w : Word) (dst : RegName) (src: Z + RegName)
      (fundamental_RWX : ∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) (E : coPset) (r : leibnizC Reg) 
                           (b e : Addr) (g : Locality) (a : Addr), (na_inv logrel_nais (logN.@(b, e))
                                                                           (read_write_cond b e interp)
                                                                    → (λ (stsf0 : prodC (leibnizC STS_states) (leibnizC STS_rels)) 
                                                                         (E0 : coPset) (r0 : leibnizC Reg), 
                                                                       ((interp_expression E0 r0) stsf0) 
                                                                         (inr (RWX, g, b, e, a))) stsf E r)%I)
      (fundamental_RWLX : ∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) (E : coPset) (r : leibnizC Reg) 
                            (b e : Addr) (g : Locality) (a : Addr), (na_inv logrel_nais (logN.@(b, e))
                                                                            (read_write_local_cond b e interp)
                                                                     → (λ (stsf0 : prodC (leibnizC STS_states)
                                                                                         (leibnizC STS_rels)) 
                                                                          (E0 : coPset) (r0 : leibnizC Reg), 
                                                                        ((interp_expression E0 r0) stsf0)
                                                                          (inr (RWLX, g, b, e, a))) stsf E r)%I)
      (Hreach : ∀ ns : namespace, Some (logN.@(b, e)) = Some ns → ↑ns ⊆ E0)
      (H3 : ∀ x : RegName, (λ x0 : RegName, is_Some (r !! x0)) x)
      (i : isCorrectPC (inr (RX, g, b, e, a)))
      (Hbae : (b <= a)%a ∧ (a <= e)%a)
      (Hbe : ↑logN.@(b, e) ⊆ E0)
      (Hi : cap_lang.decode w = Mov dst src),
      □ ▷ ▷ ((interp E0) (fs, fr)) w
        -∗ □ ▷ ([∗ list] w0 ∈ ws, ▷ ((interp E0) (fs, fr)) w0)
        -∗ □ ▷ (∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) (E1 : leibnizC coPset), [∗ list] w0 ∈ ws, ▷ 
                                                                                                                       ((interp E1) stsf) w0)
        -∗ □ (∀ r0 : RegName, ⌜r0 ≠ PC⌝ → (((fixpoint interp1) E0) (fs, fr)) (r !r! r0))
        -∗ □ na_inv logrel_nais (logN.@(b, e))
        ([[b,e]]↦ₐ[[ws]]
                ∗ (∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) (E1 : leibnizC coPset), [∗ list] w0 ∈ ws, ▷ 
                                                                                                                          ((interp E1) stsf) w0))
        -∗ □ ▷ (∀ (a0 : leibnizC Reg) (a1 : Addr) (a2 : Locality) (a3 : leibnizC STS_states) 
                  (a4 : leibnizC STS_rels) (a5 a6 : Addr) (a7 : list Word), full_map a0
                                                                                     -∗ (∀ r0 : RegName, 
                                                                                            ⌜r0 ≠ PC⌝
                                                                                            → (((fixpoint interp1) E0) (a3, a4))
                                                                                                (a0 !r! r0))
                                                                                     -∗ registers_mapsto
                                                                                     (<[PC:=
                                                                                          inr (RX, a2, a5, a6, a1)]> a0)
                                                                                     -∗ sts_full a3 a4
                                                                                     -∗ na_own logrel_nais E0
                                                                                     -∗ 
                                                                                     □ 
                                                                                     na_inv logrel_nais
                                                                                     (logN.@(a5, a6))
                                                                                     ([[a5,a6]]↦ₐ[[a7]]
                                                                                               ∗ 
                                                                                               (∀ (stsf : 
                                                                                                     prodC 
                                                                                                       (leibnizC STS_states)
                                                                                                       (leibnizC STS_rels)) 
                                                                                                  (E1 : 
                                                                                                     leibnizC coPset), [∗ list] w0 ∈ a7, ▷ 
                                                                                                                                           ((interp E1) stsf) w0))
                                                                                     -∗ 
                                                                                     □ ⌜
                                                                                     ∀ ns : namespace, 
                                                                                       Some (logN.@(a5, a6)) =
                                                                                       Some ns → 
                                                                                       ↑ns ⊆ E0⌝ -∗ 
                                                                                        ⟦ [a3, a4, E0] ⟧ₒ)
        -∗ ([∗ map] k↦y ∈ delete PC (<[PC:=inr (RX, g, b, e, a)]> r), k ↦ᵣ y)
        -∗ PC ↦ᵣ inr (RX, g, b, e, a)
        -∗ ▷ match (a + 1)%a with
             | Some ah =>
               [[ah,e]]↦ₐ[[drop (S (length (region_addrs b (get_addr_from_option_addr (a + -1)%a)))) ws]]
             | None => ⌜drop (S (length (region_addrs b (get_addr_from_option_addr (a + -1)%a)))) ws = []⌝
             end
        -∗ a ↦ₐ w
        -∗ ▷ ([[b,get_addr_from_option_addr (a + -1)%a]]↦ₐ[[take
                                                              (length
                                                                 (region_addrs b
                                                                               (get_addr_from_option_addr
                                                                                  (a + -1)%a))) ws]])
        -∗ ▷ ⌜ws =
      take (length (region_addrs b (get_addr_from_option_addr (a + -1)%a))) ws ++
           w :: drop (S (length (region_addrs b (get_addr_from_option_addr (a + -1)%a)))) ws⌝
           -∗ (▷ ([[b,e]]↦ₐ[[ws]]
                         ∗ (∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) 
                              (E1 : leibnizC coPset), [∗ list] w0 ∈ ws, ▷ ((interp E1) stsf) w0))
                 ∗ na_own logrel_nais (E0 ∖ ↑logN.@(b, e)) ={⊤}=∗ na_own logrel_nais E0)
           -∗ na_own logrel_nais (E0 ∖ ↑logN.@(b, e))
           -∗ sts_full fs fr
           -∗ WP Instr Executable
           {{ v, WP fill [SeqCtx] (of_val v)
                    {{ v0, ⌜v0 = HaltedV⌝
                           → ∃ (r0 : Reg) (fs' : STS_states) (fr' : STS_rels), 
                           full_map r0
                           ∧ registers_mapsto r0
                                              ∗ ⌜related_sts_priv fs fs' fr fr'⌝
                                              ∗ na_own logrel_nais E0 ∗ sts_full fs' fr' }} }}.
  Proof.
    intros E r a g fs fr b e ws w. intros.
    iIntros "#Hva #Hval' #Hval #Hreg #Hinv #IH".
    iIntros "Hmap HPC Hh Ha Hregionl Heqws Hcls Hown Hsts".
    rewrite delete_insert_delete.
    destruct (reg_eq_dec PC dst).
    * subst dst. destruct src.
      { iApply (wp_move_fail_reg_toPC2 with "[HPC Ha]"); eauto; iFrame; auto.
        iNext. iIntros "(HPC & Ha & _)".
        iApply wp_pure_step_later; auto.
        iApply wp_value. iNext; iIntros; discriminate. }
      { destruct (reg_eq_dec PC r0).
        - subst r0. case_eq (a+1)%a; intros.
          + iApply (wp_move_success_reg_samePC with "[HPC Ha]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha)".
            (* iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr)) with *)
            (*                "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto. *)
            (* { iExists w. rewrite H4. iFrame. auto. } *)
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
            apply lookup_insert. rewrite delete_insert_delete. iFrame.
            iMod ("Hcls" with "[Heqws Hregionl Hh Ha $Hown]") as "Hcls'".
            { iNext.
              iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr)) with
                             "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto. 
              { iExists w. rewrite H4. iFrame. auto. }
              iDestruct "Hregion" as "[$ _]". 
              iIntros (stsf' E'). rewrite -big_sepL_later. auto. 
            }
            iApply wp_pure_step_later; auto.
            iApply ("IH" with "[] [] [Hmap] [Hsts] [Hcls']"); eauto.
          + iApply (wp_move_fail_reg_samePC with "[HPC Ha]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha)".
            iApply wp_pure_step_later; auto.
            iApply wp_value. iNext; iIntros; discriminate.
        - destruct (H3 r0) as [wr0 Hsomer0].
          iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
          { rewrite lookup_delete_ne; eauto. }
          destruct wr0.
          + iApply (wp_move_fail_reg_toPC2 with "[HPC Ha Hr0]"); eauto; iFrame; auto.
            simpl. iNext. iIntros "(HPC & Ha & Hr0)".
            iApply wp_pure_step_later; auto.
            iApply wp_value. iNext; iIntros; discriminate. 
          + destruct c, p, p, p. case_eq (a0 + 1)%a; intros.
            * iApply (wp_move_success_reg_toPC with "[HPC Ha Hr0]"); eauto; iFrame.
              iNext. iIntros "(HPC & Ha & Hr0)".
              (* iDestruct (extract_from_region _ _ a with *)
              (*              "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto. *)
              (* { iExists w. iFrame. iExact "Hva". } *)
              iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=".
              apply lookup_insert. rewrite delete_insert_delete. iFrame.
              rewrite -delete_insert_ne; auto.
              iMod ("Hcls" with "[Heqws Hregionl Hh Ha $Hown]") as "Hcls'".
              { iNext.
                iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr)) with
                               "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto. 
                { iExists w. iFrame. auto. }
                iDestruct "Hregion" as "[$ _]". 
                iIntros (stsf' E'). rewrite -big_sepL_later. auto. 
              }
              iApply wp_pure_step_later; auto.
              destruct p.
              { iNext. iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate. }
              { iNext. iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate. }
              { iNext. iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate. }
              { iNext. iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate. }
              { iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
                apply lookup_insert. rewrite delete_insert_delete. iFrame.
                rewrite (insert_id r r0); auto.
                iApply ("IH" with "[] [] [Hmap] [Hsts] [Hcls']"); eauto; admit. }
              { iNext. iApply (wp_bind (fill [SeqCtx])).
                iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                iNext. iIntros "HPC /=".
                iApply wp_pure_step_later; auto.
                iApply wp_value.
                iNext. iIntros. discriminate. }
              { iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
                apply lookup_insert. rewrite delete_insert_delete. iFrame.
                rewrite (insert_id r r0); auto.
                iNext. (* use fundamental_RWX in some way ? *) admit. }
              { iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
                apply lookup_insert. rewrite delete_insert_delete. iFrame.
                rewrite (insert_id r r0); auto.
                iNext. (* use fundamental_RWLX in some way ? *) admit. }
            * iApply (wp_move_fail_reg_toPC with "[HPC Ha Hr0]"); eauto; iFrame.
              iNext. iIntros "(HPC & Ha & Hr0)".
              iApply wp_pure_step_later; auto.
              iApply wp_value. iNext; iIntros; discriminate. }
    * destruct (H3 dst) as [wdst Hsomedst].
      iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]".
      { rewrite lookup_delete_ne; eauto. }
      destruct src.
      { case_eq (a+1)%a; intros.
        - iApply (wp_move_success_z with "[HPC Ha Hdst]"); eauto; iFrame.
          iNext. iIntros "(HPC & Ha & Hdst)".
          (* iDestruct (extract_from_region' _ _ a _ ((interp E) (fs, fr)) with *)
          (*            "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto. *)
          (* { iExists w. rewrite H4. iFrame. iExact "Hva". } *)
          iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=".
          apply lookup_insert. rewrite delete_insert_delete. iFrame.
          rewrite -delete_insert_ne; auto.
          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
          apply lookup_insert. rewrite delete_insert_delete. iFrame.
          iMod ("Hcls" with "[Heqws Hregionl Hh Ha $Hown]") as "Hcls'".
          { iNext.
            iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr)) with
                           "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto. 
            { iExists w. rewrite H4. iFrame. auto. }
            iDestruct "Hregion" as "[$ _]". 
            iIntros (stsf' E'). rewrite -big_sepL_later. auto. 
          }
          iApply wp_pure_step_later; auto.
          iApply ("IH" with "[] [] [Hmap] [Hsts] [Hcls']").
          { iIntros (r2). iPureIntro.
            destruct (reg_eq_dec dst r2).
            - subst r2. exists (inl z). eapply lookup_insert.
            - destruct (H3 r2) as [wr2 Hsomer2].
              exists wr2. rewrite -Hsomer2. apply (lookup_insert_ne r dst r2 (inl z) n0). }
          { iIntros (r2 HnePC). destruct (reg_eq_dec dst r2).
            - subst r2. rewrite /RegLocate lookup_insert.
              repeat rewrite (fixpoint_interp1_eq); simpl; eauto.
            - rewrite /RegLocate lookup_insert_ne.
              iApply "Hreg"; auto. auto. }
          { eauto. }
          { eauto. }
          { eauto. }
          { eauto. }
          { eauto. }
        - iApply (wp_move_fail_z with "[HPC Ha Hdst]"); eauto; iFrame.
          iNext. iIntros "(HPC & Ha & Hdst)".
          iApply wp_pure_step_later; auto.
          iApply wp_value. iNext; iIntros; discriminate. }
      { destruct (reg_eq_dec PC r0).
        - subst r0. case_eq (a+1)%a; intros.
          + iApply (wp_move_success_reg_fromPC with "[HPC Ha Hdst]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha & Hdst)".
            (* iDestruct (extract_from_region _ _ a with *)
            (*                "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto. *)
            (* { iExists w. rewrite H4. iFrame. iExact "Hva". } *)
            iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=".
            apply lookup_insert. rewrite delete_insert_delete. iFrame.
            rewrite -delete_insert_ne; auto.
            iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
            apply lookup_insert. rewrite delete_insert_delete. iFrame.
            iMod ("Hcls" with "[Heqws Hregionl Hh Ha $Hown]") as "Hcls'".
            { iNext.
              iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr)) with
                             "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto. 
              { iExists w. rewrite H4. iFrame. auto. }
              iDestruct "Hregion" as "[$ _]". 
              iIntros (stsf' E'). rewrite -big_sepL_later. auto. 
            }
            iApply wp_pure_step_later; auto.
            iApply ("IH" with "[] [] [Hmap] [Hsts] [Hcls']").
            { iIntros (r2). iPureIntro.
              destruct (reg_eq_dec dst r2).
              - subst r2. exists (inr (RX, g, b, e, a)). eapply lookup_insert.
              - destruct (H3 r2) as [wr2 Hsomer2].
                exists wr2. rewrite -Hsomer2. eapply (lookup_insert_ne r); eauto. }
            { iIntros (r2 HnePC). destruct (reg_eq_dec dst r2).
              - subst r2. rewrite /RegLocate lookup_insert.
                rewrite (fixpoint_interp1_eq _ _ (inr (RX, g, b, e, a))) /=.
                iExists RX,g,b,e,a,ws. do 2 (iSplitR; auto).
                iFrame "#". iIntros. iModIntro.
                (* PC is in the logical relation, not sure how to prove *) admit.
              - rewrite /RegLocate lookup_insert_ne.
                iApply "Hreg"; auto. auto. }
            { eauto. }
            { eauto. }
            { eauto. }
            { eauto. }
            { eauto. }
          + iApply (wp_move_fail_reg_fromPC with "[HPC Ha Hdst]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha & Hdst)".
            iApply wp_pure_step_later; auto.
            iApply wp_value. iNext; iIntros; discriminate.
        - case_eq (a+1)%a; intros.
          + destruct (reg_eq_dec dst r0).
            * subst r0. iApply (wp_move_success_reg_same with "[HPC Ha Hdst]"); eauto; iFrame.
              iNext. iIntros "(HPC & Ha & Hdst)".
              (* iDestruct (extract_from_region _ _ a with *)
              (*                "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto. *)
              (* { iExists w. rewrite H4. iFrame. iExact "Hva". } *)
              iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=".
              apply lookup_insert. rewrite delete_insert_delete. iFrame.
              repeat rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
              apply lookup_insert. rewrite delete_insert_delete. iFrame.
              iMod ("Hcls" with "[Heqws Hregionl Hh Ha $Hown]") as "Hcls'".
              { iNext.
                iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr)) with
                               "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto. 
                { iExists w. rewrite H4. iFrame. auto. }
                iDestruct "Hregion" as "[$ _]". 
                iIntros (stsf' E'). rewrite -big_sepL_later. auto. 
              }
              iApply wp_pure_step_later; auto.
              iApply ("IH" with "[] [] [Hmap] [Hsts] [Hcls']").
              { iIntros (r2). iPureIntro.
                destruct (reg_eq_dec dst r2).
                - subst r2. exists (wdst). eapply lookup_insert.
                - destruct (H3 r2) as [wr2 Hsomer2].
                  exists wr2. rewrite -Hsomer2. eapply (lookup_insert_ne r); eauto. }
              { iIntros (r2 HnePC). destruct (reg_eq_dec dst r2).
                - subst r2. rewrite /RegLocate lookup_insert.
                  iSpecialize ("Hreg" $! dst). rewrite Hsomedst.
                  iApply "Hreg"; auto.
                - rewrite /RegLocate lookup_insert_ne.
                  iApply "Hreg"; auto. auto. }
              { eauto. }
              { eauto. }
              { eauto. }
              { eauto. }
              { eauto. }
            * destruct (H3 r0) as [wr0 Hsomer0].
              iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
              { repeat rewrite lookup_delete_ne; eauto. }
              iApply (wp_move_success_reg with "[Hdst Hr0 HPC Ha]"); eauto; iFrame.
              iNext. iIntros "(HPC & Ha & Hdst & Hr0)".
              (* iDestruct (extract_from_region _ _ a with *)
              (*                "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto. *)
              (* { iExists w. rewrite H4. iFrame. iExact "Hva". } *)
              iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=".
              apply lookup_insert. rewrite delete_insert_delete. iFrame.
              rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=".
              apply lookup_insert. rewrite delete_insert_delete. iFrame.
              repeat rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
              apply lookup_insert. rewrite delete_insert_delete. iFrame.
              iMod ("Hcls" with "[Heqws Hregionl Hh Ha $Hown]") as "Hcls'".
              { iNext.
                iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr)) with
                               "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto. 
                { iExists w. rewrite H4. iFrame. auto. }
                iDestruct "Hregion" as "[$ _]". 
                iIntros (stsf' E'). rewrite -big_sepL_later. auto. 
              }
              iApply wp_pure_step_later; auto.
              iApply ("IH" with "[] [] [Hmap] [Hsts] [Hcls']").
              { iIntros (r2). iPureIntro.
                destruct (reg_eq_dec dst r2).
                - subst r2. exists wr0. eapply lookup_insert.
                - destruct (reg_eq_dec r0 r2).
                  + subst r0. exists wr0. rewrite lookup_insert_ne; auto.
                    eapply lookup_insert.
                  + destruct (H3 r2) as [wr2 Hsomer2].
                    exists wr2. rewrite -Hsomer2. repeat rewrite lookup_insert_ne; eauto. }
              { iIntros (r2 HnePC). destruct (reg_eq_dec dst r2).
                - subst r2. rewrite /RegLocate lookup_insert.
                  iDestruct ("Hreg" $! r0) as "Hr0".
                  rewrite Hsomer0. iApply "Hr0"; auto.
                - rewrite /RegLocate lookup_insert_ne; auto.
                  destruct (reg_eq_dec r0 r2).
                  + subst r2. rewrite lookup_insert.
                    iDestruct ("Hreg" $! r0) as "Hr0".
                    rewrite Hsomer0. iApply "Hr0"; auto.
                  + rewrite lookup_insert_ne; auto. iApply "Hreg"; auto. }
              { eauto. }
              { eauto. }
              { eauto. }
              { eauto. }
              { eauto. }
          + destruct (reg_eq_dec dst r0).
            * subst r0. iApply (wp_move_fail_reg_same with "[HPC Ha Hdst]"); eauto; iFrame.
              iNext. iIntros "(HPC & Ha & Hdst)".
              iApply wp_pure_step_later; auto.
              iApply wp_value. iNext; iIntros; discriminate.
            * destruct (H3 r0) as [wr0 Hsomer0].
              iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
              { repeat rewrite lookup_delete_ne; eauto. }
              iApply (wp_move_fail_reg with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
              iNext. iIntros "(HPC & Ha & Hdst & Hr0)".
              iApply wp_pure_step_later; auto.
              iApply wp_value. iNext; iIntros; discriminate. }
  Admitted.
    

  Lemma RX_Load_case:
    ∀ (E0 : coPset) (r : leibnizC Reg) (a : Addr) (g : Locality) (fs : leibnizC STS_states) (fr : leibnizC STS_rels) 
      (b e : Addr) (ws : list Word) (w : Word) (dst : RegName) (src: RegName)
      (fundamental_RWX : ∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) (E : coPset) (r : leibnizC Reg) 
                           (b e : Addr) (g : Locality) (a : Addr), (na_inv logrel_nais (logN.@(b, e))
                                                                           (read_write_cond b e interp)
                                                                    → (λ (stsf0 : prodC (leibnizC STS_states) (leibnizC STS_rels)) 
                                                                         (E0 : coPset) (r0 : leibnizC Reg), 
                                                                       ((interp_expression E0 r0) stsf0) 
                                                                         (inr (RWX, g, b, e, a))) stsf E r)%I)
      (fundamental_RWLX : ∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) (E : coPset) (r : leibnizC Reg) 
                            (b e : Addr) (g : Locality) (a : Addr), (na_inv logrel_nais (logN.@(b, e))
                                                                            (read_write_local_cond b e interp)
                                                                     → (λ (stsf0 : prodC (leibnizC STS_states)
                                                                                         (leibnizC STS_rels)) 
                                                                          (E0 : coPset) (r0 : leibnizC Reg), 
                                                                        ((interp_expression E0 r0) stsf0)
                                                                          (inr (RWLX, g, b, e, a))) stsf E r)%I)
      (Hreach : ∀ ns : namespace, Some (logN.@(b, e)) = Some ns → ↑ns ⊆ E0)
      (H3 : ∀ x : RegName, (λ x0 : RegName, is_Some (r !! x0)) x)
      (i : isCorrectPC (inr (RX, g, b, e, a)))
      (Hbae : (b <= a)%a ∧ (a <= e)%a)
      (Hbe : ↑logN.@(b, e) ⊆ E0)
      (Hi : cap_lang.decode w = Load dst src),
      □ ▷ ▷ ((interp E0) (fs, fr)) w
        -∗ □ ▷ ([∗ list] w0 ∈ ws, ▷ ((interp E0) (fs, fr)) w0)
        -∗ □ ▷ (∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) (E1 : leibnizC coPset), [∗ list] w0 ∈ ws, ▷ 
                                                                                                                       ((interp E1) stsf) w0)
        -∗ □ (∀ r0 : RegName, ⌜r0 ≠ PC⌝ → (((fixpoint interp1) E0) (fs, fr)) (r !r! r0))
        -∗ □ na_inv logrel_nais (logN.@(b, e))
        ([[b,e]]↦ₐ[[ws]]
                ∗ (∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) (E1 : leibnizC coPset), [∗ list] w0 ∈ ws, ▷ 
                                                                                                                          ((interp E1) stsf) w0))
        -∗ □ ▷ (∀ (a0 : leibnizC Reg) (a1 : Addr) (a2 : Locality) (a3 : leibnizC STS_states) 
                  (a4 : leibnizC STS_rels) (a5 a6 : Addr) (a7 : list Word), full_map a0
                                                                                     -∗ (∀ r0 : RegName, 
                                                                                            ⌜r0 ≠ PC⌝
                                                                                            → (((fixpoint interp1) E0) (a3, a4))
                                                                                                (a0 !r! r0))
                                                                                     -∗ registers_mapsto
                                                                                     (<[PC:=
                                                                                          inr (RX, a2, a5, a6, a1)]> a0)
                                                                                     -∗ sts_full a3 a4
                                                                                     -∗ na_own logrel_nais E0
                                                                                     -∗ 
                                                                                     □ 
                                                                                     na_inv logrel_nais
                                                                                     (logN.@(a5, a6))
                                                                                     ([[a5,a6]]↦ₐ[[a7]]
                                                                                               ∗ 
                                                                                               (∀ (stsf : 
                                                                                                     prodC 
                                                                                                       (leibnizC STS_states)
                                                                                                       (leibnizC STS_rels)) 
                                                                                                  (E1 : 
                                                                                                     leibnizC coPset), [∗ list] w0 ∈ a7, ▷ 
                                                                                                                                           ((interp E1) stsf) w0))
                                                                                     -∗ 
                                                                                     □ ⌜
                                                                                     ∀ ns : namespace, 
                                                                                       Some (logN.@(a5, a6)) =
                                                                                       Some ns → 
                                                                                       ↑ns ⊆ E0⌝ -∗ 
                                                                                        ⟦ [a3, a4, E0] ⟧ₒ)
        -∗ ([∗ map] k↦y ∈ delete PC (<[PC:=inr (RX, g, b, e, a)]> r), k ↦ᵣ y)
        -∗ PC ↦ᵣ inr (RX, g, b, e, a)
        -∗ ▷ match (a + 1)%a with
             | Some ah =>
               [[ah,e]]↦ₐ[[drop (S (length (region_addrs b (get_addr_from_option_addr (a + -1)%a)))) ws]]
             | None => ⌜drop (S (length (region_addrs b (get_addr_from_option_addr (a + -1)%a)))) ws = []⌝
             end
        -∗ a ↦ₐ w
        -∗ ▷ ([[b,get_addr_from_option_addr (a + -1)%a]]↦ₐ[[take
                                                              (length
                                                                 (region_addrs b
                                                                               (get_addr_from_option_addr
                                                                                  (a + -1)%a))) ws]])
        -∗ ▷ ⌜ws =
      take (length (region_addrs b (get_addr_from_option_addr (a + -1)%a))) ws ++
           w :: drop (S (length (region_addrs b (get_addr_from_option_addr (a + -1)%a)))) ws⌝
           -∗ (▷ ([[b,e]]↦ₐ[[ws]]
                         ∗ (∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) 
                              (E1 : leibnizC coPset), [∗ list] w0 ∈ ws, ▷ ((interp E1) stsf) w0))
                 ∗ na_own logrel_nais (E0 ∖ ↑logN.@(b, e)) ={⊤}=∗ na_own logrel_nais E0)
           -∗ na_own logrel_nais (E0 ∖ ↑logN.@(b, e))
           -∗ sts_full fs fr
           -∗ WP Instr Executable
           {{ v, WP fill [SeqCtx] (of_val v)
                    {{ v0, ⌜v0 = HaltedV⌝
                           → ∃ (r0 : Reg) (fs' : STS_states) (fr' : STS_rels), 
                           full_map r0
                           ∧ registers_mapsto r0
                                              ∗ ⌜related_sts_priv fs fs' fr fr'⌝
                                              ∗ na_own logrel_nais E0 ∗ sts_full fs' fr' }} }}.
  Proof.
    intros E r a g fs fr b e ws w. intros.
    iIntros "#Hva #Hval' #Hval #Hreg #Hinv #IH".
    iIntros "Hmap HPC Hh Ha Hregionl Heqws Hcls Hown Hsts".
    destruct (decide (PC = dst)),(decide (PC = src)); simplify_eq. 
    * (* Load PC PC ==> fail *)
      iApply (wp_load_fail3 with "[HPC Ha]"); eauto; iFrame. 
      iNext. iIntros "[HPC Ha] /=".
      iApply wp_pure_step_later; auto.
      iApply wp_value.
      iNext. iIntros "%"; inversion a0.
    * (* Load PC src ==> success if src ↦ inr, fail o/w *)
      simpl in H3. 
      specialize H3 with src as Hsrc. 
      destruct Hsrc as [wsrc Hsomesrc]. 
      assert ((delete PC r !! src) = Some wsrc) as Hsomesrc'.
      { rewrite -Hsomesrc. apply (lookup_delete_ne r PC src). eauto. }
      rewrite delete_insert_delete.
      iDestruct ((big_sepM_delete _ _ src) with "Hmap") as "[Hsrc Hmap]"; eauto.
      destruct wsrc.
      { (* src ↦ inl z ==> fail *)
        iApply (wp_load_fail2 with "[HPC Ha Hsrc]"); eauto; iFrame.
        iNext. iIntros "[HPC [Ha Hsrc]] /=".
        iApply wp_pure_step_later; auto. iApply wp_value.
        iNext. iIntros "%"; inversion a0.  
      } 
      (* src ↦ inr c ==> need to open invariant *)
      destruct c. do 3 destruct p.
      (* if p is not ra or a0 is not within bounds: fail *)
      destruct (decide ((readAllowed p && withinBounds ((p,l),a2,a1,a0)) = false)).
      { (* Capability fail *)
        iApply (wp_load_fail1 with "[HPC Ha Hsrc]"); eauto.
        - split; eauto. apply andb_false_iff. eauto.
        - iFrame.
        - iNext. iIntros "[HPC [Ha Hsrc]] /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros "%"; inversion a3. 
      }
      (* readAllowed p && withinBounds ((p,l),a2,a1,a0) *)
      apply (not_false_is_true (_ && _)),Is_true_eq_left,andb_prop_elim in n0
        as [Hra Hwb]. apply andb_prop_elim in Hwb as [Hle Hge]. 
      (* get validity of capability in src from Hreg *)
      apply reg_eq_sym in n. 
      iDestruct ("Hreg" $! src n) as "Hvsrc". 
      rewrite /RegLocate Hsomesrc.
      iDestruct (read_allowed_inv with "Hvsrc") as "Hconds"; eauto.
      (* Each condition in Hconds take a step in similar fashion *)
      rewrite /read_write_cond. 
      iAssert ((∃ w', ▷ (a0 ↦ₐ w' ∗ a ↦ₐ w
                         ={⊤}=∗ na_own logrel_nais E)
                        ∗ ▷ a0 ↦ₐ w' ∗ ▷ ▷ ⟦ w' ⟧ E (fs,fr)
               (* ∗ (∃ E', ⌜get_namespace w' = Some E'⌝ ∧ ⌜↑E' ⊆ E⌝)*))
                 ∗ sts_full fs fr
                 -∗ WP Instr Executable
                 {{ v, WP fill [SeqCtx] (of_val v)
                          {{ v0, ⌜v0 = HaltedV⌝
                                 → ∃ (r0 : Reg) (fs' : STS_states) (fr' : STS_rels),
                                 full_map r0
                                 ∧ registers_mapsto r0
                                                    ∗ ⌜related_sts_priv fs fs' fr fr'⌝
                                                    ∗ na_own logrel_nais E
                                                    ∗ sts_full fs' fr' }} }} )%I
                                                               with "[Ha HPC Hsrc Hmap]" as "Hstep".
      {
        iIntros "(Hw0 & Hsts)".
        iDestruct "Hw0" as (w0) "(Hcls' & Ha0 & #Hw0)".
        (* iDestruct "Hsub" as (E') "#[Hns Hsub]".  *)
        iAssert (∀ w1 w2, full_map (<[PC:=w1]> (<[src:=w2]> r)))%I as "#Hfull".
        { iIntros (w1 w2 r0).
          iPureIntro.
          destruct (decide (PC = r0)); [simplify_eq; rewrite lookup_insert; eauto|].
          rewrite lookup_insert_ne.
          destruct (decide (src = r0)); [simplify_eq; rewrite lookup_insert; eauto|].
          rewrite lookup_insert_ne. apply H3. done. done.
        }
        destruct w0.
        { iApply (wp_load_fail5 with "[HPC Ha Hsrc Ha0]"); eauto.
          - split; apply Is_true_eq_true; eauto.
            apply andb_prop_intro. split; [apply Hle|apply Hge].
          - iFrame.
          - iNext. iIntros "[HPC [Ha [Hsrc Ha0]]] /=".
            iApply wp_pure_step_later; auto.
            iApply wp_value.
            iNext. iIntros "%"; inversion a3. 
        }
        destruct c,p0,p0,p0.
        destruct ((a3 + 1)%a) eqn:Ha0.
        2: { (* If src points to top address, load crashes *)
          iApply (wp_load_fail4 with "[HPC Hsrc Ha Ha0]"); eauto.
          - split; apply Is_true_eq_true; eauto.
            apply andb_prop_intro. split; [apply Hle|apply Hge].
          - iFrame.
          - iNext. iIntros "[HPC [Ha [Hsrc Ha0]]] /=".
            iApply wp_pure_step_later; auto.
            iApply wp_value.
            iNext. iIntros "%"; inversion a6. 
        }
        (* successful load into PC *)
        iApply (wp_load_success_PC with "[HPC Ha Hsrc Ha0]"); eauto.
        - split; apply Is_true_eq_true; eauto.
          apply andb_prop_intro. split; [apply Hle|apply Hge].
        - iFrame.
        - iNext. iIntros "[HPC [Ha [Hsrc Ha0]]] /=".
          iApply wp_pure_step_later; auto.
          iAssert (⌜p0 ≠ RX⌝ ∧ ⌜p0 ≠ RWX⌝ ∧ ⌜p0 ≠ RWLX⌝ →
                   PC ↦ᵣ inr (p0, l0, a5, a4, a6) -∗
                      WP Seq (Instr Executable) {{ w, ⌜w = FailedV⌝
                                                                  ∗ PC ↦ᵣ inr (p0, l0, a5, a4, a6) }})%I
            as "Hfail".
          { iIntros "(% & % & %) HPC".
            iApply (wp_bind (fill [SeqCtx])).
            iApply (wp_notCorrectPC with "[HPC]");
              [apply not_isCorrectPC_perm; eauto|iFrame|].
            iNext. iIntros "HPC /=".
            iApply wp_pure_step_later; auto.
            iNext. iApply wp_value. iFrame. done.
          }
          (* The new register state is valid *)
          iAssert (interp_registers _ _ (<[src:=inr (p, l, a2, a1, a0)]> r)) as "[Hfull' Hreg']".
          { iSplitL.
            { iIntros (r0). iPureIntro.
              destruct (decide (src = r0)); simplify_eq;
                [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto. }
            iIntros (r0) "%".
            destruct (decide (src = r0)); simplify_eq.
            + by rewrite /RegLocate lookup_insert.
            + rewrite /RegLocate lookup_insert_ne; auto.
              iDestruct ("Hreg" $! (r0) a7) as "Hr0".
              specialize H3 with r0.
              destruct H3 as [c Hsome].
              rewrite Hsome. iApply "Hr0"; auto.
          }
          destruct p0;
            [iAssert (⌜O ≠ RX⌝ ∧ ⌜O ≠ RWX⌝ ∧ ⌜O ≠ RWLX⌝)%I as "Htrivial";
             first (iSplit; iPureIntro; auto)|
             iAssert (⌜RO ≠ RX⌝ ∧ ⌜RO ≠ RWX⌝ ∧ ⌜RO ≠ RWLX⌝)%I as "Htrivial";
             first (iSplit; iPureIntro; auto)|
             iAssert (⌜RW ≠ RX⌝ ∧ ⌜RW ≠ RWX⌝ ∧ ⌜RW ≠ RWLX⌝)%I as "Htrivial";
             first (iSplit; iPureIntro; auto)|
             iAssert (⌜RWL ≠ RX⌝ ∧ ⌜RWL ≠ RWX⌝ ∧ ⌜RWL ≠ RWLX⌝)%I as "Htrivial";
             first (iSplit; iPureIntro; auto)| |
             iAssert (⌜cap_lang.E ≠ RX⌝ ∧ ⌜cap_lang.E ≠ RWX⌝ ∧ ⌜cap_lang.E ≠ RWLX⌝)%I as "Htrivial";
             first (iSplit; iPureIntro; auto)| | ];
            try ( iDestruct ("Hfail" with "Htrivial HPC") as "Hfail";
                  iApply (wp_wand with "Hfail");
                  iAssert ((∀ v : val cap_lang, ⌜v = FailedV⌝
                                                            ∗ PC ↦ᵣ inr (_, l0, a5, a4, a6)
                                                            -∗ ⌜v = HaltedV⌝
                                                → ∃ (r0 : Reg) fs' fr',
                                 full_map r0 ∧ registers_mapsto r0 ∗ ⌜related_sts_priv fs fs' fr fr'⌝
                                                                ∗ na_own logrel_nais E
                                                                ∗ sts_full fs' fr'))%I
                    with "[Hmap Hsrc Hsts]" as "Hfailed";
                  [ iIntros (v) "[-> HPC]";
                    iDestruct ((big_sepM_delete _ _ src)
                                 with "[Hsrc Hmap]") as "Hmap /=";
                    [apply lookup_insert|rewrite delete_insert_delete;iFrame|];
                    rewrite -delete_insert_ne; auto;
                    iDestruct ((big_sepM_delete _ _ PC)
                                 with "[HPC Hmap]") as "Hmap /=";
                    [apply lookup_insert|rewrite delete_insert_delete;iFrame|];
                    iIntros "%"; inversion a7
                   |];iFrame);
            try (iNext;iDestruct ("Hfail" with "Htrivial HPC") as "Hfail"; 
                 iApply wp_wand_l;iFrame;iIntros (v) "[-> HPC] %";inversion a7).
          { (* new PC is RX ==> apply IH*)
            iClear "Hfail".
            iDestruct ((big_sepM_delete _ _ src) with "[Hsrc Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|];
              rewrite -delete_insert_ne; auto;
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|].
            (* apply IH *)
            iNext.
            rewrite (fixpoint_interp1_eq _ _ (inr (RX, l0, a5, a4, a3))) /=.
            iDestruct "Hw0" as (p0 g0 b0 e0 a7 ws1) "(% & % & Hb0e0 & Hexec)".
            inversion H4;subst.
            iMod ("Hcls'" with "[$Ha0 $Ha]") as "Hown". 
            iApply ("IH" $! _ _ _ _ _ _ _ ws1
                      with "[Hfull'] [Hreg'] [Hmap] [Hsts] [Hown]");
              iFrame; iFrame "#".
            iAlways. iPureIntro. by intros ns Hns; inversion Hns.  
          } 
          { (* new PC is RWX, apply fundamental_RWX *)
            iClear "Hfail".
            iDestruct ((big_sepM_delete _ _ src) with "[Hsrc Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|];
              rewrite -delete_insert_ne; auto;
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|].
            iNext.
            rewrite (fixpoint_interp1_eq _ _ (inr (RWX, l0, a5, a4, a3))) /=.
            iDestruct "Hw0" as (p0 g0 b0 e0 a7) "(% & % & Hb0e0 & Hexec)".
            inversion H4;subst.
            iMod ("Hcls'" with "[$Ha0 $Ha]") as "Hown". 
            iDestruct (fundamental_RWX _ _ (<[src:=inr (p, l, a2, a1, a0)]> r)
                         with "Hb0e0") as "Hexpr"; eauto.
            iDestruct "Hexpr" as (fs0 fr0) "(% & % & Hexpr)";
              simplify_eq.
            iDestruct ("Hexpr" 
                         with "[Hfull' Hreg' Hmap Hsts Hown]")
              as (p0 g1 b1 e1 a3) "[% Ho]"; simplify_eq; iFrame.
            iFrame. 
            iPureIntro. by intros ns Hns; inversion Hns.  
          }
          { (* new PC is RWLX, apply fundamental_RWLX *)
            iClear "Hfail".
            iDestruct ((big_sepM_delete _ _ src) with "[Hsrc Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|];
              rewrite -delete_insert_ne; auto;
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|].
            rewrite (fixpoint_interp1_eq _ _ (inr (RWLX, l0, a5, a4, a3))).
            iNext.
            iDestruct "Hw0" as (p0 g0 b0 e0 a7) "(% & % & Hb0e0 & Hexec)".
            inversion H4;subst.
            iMod ("Hcls'" with "[$Ha0 $Ha]") as "Hown". 
            iDestruct (fundamental_RWLX _ _ (<[src:=inr (p, l, a2, a1, a0)]> r)
                         with "Hb0e0") as "Hexpr"; eauto.
            iDestruct "Hexpr" as (fs0 fr0) "(% & % & Hexpr)";
              simplify_eq.
            iDestruct ("Hexpr" 
                         with "[Hfull' Hreg' Hmap Hsts Hown]")
              as (p0 g1 b1 e1 a3) "[% Ho]"; simplify_eq; iFrame.
            iFrame. 
            iPureIntro. by intros ns Hns; inversion Hns.  
          }
      }

      destruct (decide ((b,e) = (a2,a1))).
      {
        inversion e0; subst.
        (* no need to open any invariant, in this case we need to do cases on 
               a = a0. if a = a0, then the program should crash, since we will not 
               be able to increment w once loaded into PC. Otherwise we just do as 
               below, except we don't need to open the invariant, we just destruct the 
               region a0 is in (either in Hregionl or Hregionh). *)
        admit. 
      }
      iDestruct "Hconds" as "[[#Hro|#[Hrw|Hrwl]] %]".
      (* each condition is similar, but with some subtle differences for closing *)
      { iDestruct "Hro" as (ws0) "#Hinv0".
        (* open the invariant to access a0 ↦ₐ _ *)
        assert (↑logN.@(a2, a1) ⊆ (E ∖ ↑logN.@(b, e))) as Ha2a1.
        { apply namespace_subseteq_difference; auto.
          rewrite /namespace_subseteq_difference.
            by apply ndot_ne_disjoint.
        }
        iMod (na_inv_open with "Hinv0 Hown") as "[Hro_cond [Hown' Hcls']]"; auto. 
        rewrite /read_only_cond.
        iDestruct "Hro_cond" as "[Ha2a1 #Hro_cond]".
        iDestruct ("Hro_cond" $! (fs,fr) E) as "Hro_cond'".
        iCombine "Ha2a1 Hro_cond'" as "Hregion". 
        iDestruct (extract_from_region' _ _ a0 with "Hregion") as (w0) "(Heqws' & Hregion0l & _ & >Ha0 & #Hva0 & Hh0)"; first (split; by apply Z.leb_le,Is_true_eq_true).
        iApply "Hstep". iFrame "Hsts".
        iExists w0. iFrame "Ha0 Hva0". 
        iNext. iIntros "[Ha0 Ha]".
        iMod ("Hcls'" with "[Hown' Heqws' Hregion0l Ha0 Hh0]") as "Hown".
        { iFrame. iNext.
          iDestruct (extract_from_region' _ _ a0 _
                                          (((fixpoint interp1) E) (fs, fr))
                       with "[Heqws' Hregion0l Ha0 Hh0]")
            as "Hregion";
            first (split; by apply Z.leb_le,Is_true_eq_true).
          { iFrame. iExists _. iFrame "∗ #". }
          iDestruct "Hregion" as "[$ _]".
          iIntros (stsf E0). iApply big_sepL_later. iNext. auto. 
        }
        iMod ("Hcls" with "[$Hown Hregionl Hh Ha Heqws]") as "Hown".
        { iNext. 
          iDestruct (extract_from_region' _ _ a _
                                          (((fixpoint interp1) E) (fs, fr))
                       with "[Hregionl Hh Ha Heqws]")
            as "Hregion"; eauto.
          { iExists _. iFrame. iFrame "∗ #". }
          iDestruct "Hregion" as "[$ _]".
          iIntros (stsf E0). iApply big_sepL_later. iNext. auto. 
        } 
        iModIntro. iFrame. 
      }
      { (* open the invariant to access a0 ↦ₐ _ *)
        assert (↑logN.@(a2, a1) ⊆ (E ∖ ↑logN.@(b, e))) as Ha2a1.
        { apply namespace_subseteq_difference; auto.
          rewrite /namespace_subseteq_difference.
            by apply ndot_ne_disjoint.
        }
        iMod (na_inv_open with "Hrw Hown") as "[Hrw_cond [Hown Hcls']]"; auto. 
        iDestruct "Hrw_cond" as (ws0) "Hrw_cond".
        iDestruct "Hrw_cond" as "[Ha2a1 #Hrw_cond]".
        iDestruct ("Hrw_cond" $! (fs,fr) E) as "Hrw_cond'".
        iCombine "Ha2a1 Hrw_cond'" as "Hregion".
        iDestruct (extract_from_region' _ _ a0 with "Hregion") as (w0) "(Heqws' & Hregion0l & _ & >Ha0 & #[Hva0 Hnl] & Hh0)"; first (split; by apply Z.leb_le,Is_true_eq_true).
        iApply "Hstep". iFrame "Hsts".
        iExists w0. iFrame "Ha0 #".
        iNext. iIntros "[Ha0 Ha]". 
        iMod ("Hcls'" with "[Hown Heqws' Hregion0l Ha0 Hh0]") as "Hown".
        { iFrame. iNext.
          iDestruct (extract_from_region' _ _ a0 _
                                          (((fixpoint interp1) E) (fs, fr))
                       with "[Heqws' Hregion0l Ha0 Hh0]")
            as "Hregion";
            first (split; by apply Z.leb_le,Is_true_eq_true).
          { iFrame. iExists _. iFrame "∗ #".
            iDestruct (big_sepL_sepL with "Hrw_cond") as "[$ _]". 
          }
          iExists _. iDestruct "Hregion" as "[$ _]".
          iIntros (stsf E0). iApply big_sepL_later. iNext. auto. 
        }
        iMod ("Hcls" with "[$Hown Hregionl Hh Ha Heqws]") as "Hown".
        { iNext. 
          iDestruct (extract_from_region' _ _ a _
                                          (((fixpoint interp1) E) (fs, fr))
                       with "[Hregionl Hh Ha Heqws]")
            as "Hregion"; eauto.
          { iExists _. iFrame. iFrame "∗ #". }
          iDestruct "Hregion" as "[$ _]".
          iIntros (stsf E0). iApply big_sepL_later. iNext. auto. 
        } 
        iModIntro. iFrame.
      }
      { (* open the invariant to access a0 ↦ₐ _ *)
        assert (↑logN.@(a2, a1) ⊆ (E ∖ ↑logN.@(b, e))) as Ha2a1.
        { apply namespace_subseteq_difference; auto.
          rewrite /namespace_subseteq_difference.
            by apply ndot_ne_disjoint.
        }
        iMod (na_inv_open with "Hrwl Hown") as "[Hrw_cond [Hown Hcls']]"; auto. 
        iDestruct "Hrw_cond" as (ws0) "Hrw_cond".
        iDestruct "Hrw_cond" as "[Ha2a1 #Hrw_cond]".
        iDestruct ("Hrw_cond" $! (fs,fr) E) as "Hrw_cond'".
        iCombine "Ha2a1 Hrw_cond'" as "Hregion".
        iDestruct (extract_from_region' _ _ a0 with "Hregion") as (w0) "(Heqws' & Hregion0l & _ & >Ha0 & #Hva0 & Hh0)"; first (split; by apply Z.leb_le,Is_true_eq_true).
        iApply "Hstep". iFrame "Hsts".
        iExists w0. iFrame "Ha0 #".
        iNext. iIntros "[Ha0 Ha]". 
        iMod ("Hcls'" with "[Hown Heqws' Hregion0l Ha0 Hh0]") as "Hown".
        { iFrame. iNext.
          iDestruct (extract_from_region' _ _ a0 _
                                          (((fixpoint interp1) E) (fs, fr))
                       with "[Heqws' Hregion0l Ha0 Hh0]")
            as "Hregion";
            first (split; by apply Z.leb_le,Is_true_eq_true).
          { iFrame. iExists _. iFrame "∗ #". }
          iExists _. iDestruct "Hregion" as "[$ _]".
          iIntros (stsf E0). iApply big_sepL_later. iNext. auto. 
        }
        iMod ("Hcls" with "[$Hown Hregionl Hh Ha Heqws]") as "Hown".
        { iNext. 
          iDestruct (extract_from_region' _ _ a _
                                          (((fixpoint interp1) E) (fs, fr))
                       with "[Hregionl Hh Ha Heqws]")
            as "Hregion"; eauto.
          { iExists _. iFrame. iFrame "∗ #". }
          iDestruct "Hregion" as "[$ _]".
          iIntros (stsf E0). iApply big_sepL_later. iNext. auto. 
        } 
        iModIntro. iFrame.
      }
    * destruct (H3 dst) as [wdst Hsomedst].
      rewrite delete_insert_delete.
      assert ((delete PC r !! dst) = Some wdst) as Hsomedst'.
      { rewrite -Hsomedst. apply (lookup_delete_ne r PC dst). eauto. }
      iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]"; eauto. 
      destruct (a + 1)%a eqn:Ha'. 
      2: { (* if PC cannot be incremented ==> dst is updated, then program crashes *)
        iApply (wp_load_fail6 with "[HPC Hdst Ha]"); eauto.
        iFrame. iNext. iIntros "[HPC [Ha Hdst]] /=".
        iApply wp_pure_step_later; auto.
        iApply wp_value; auto.
        iNext. 
        iIntros (Hcontr); inversion Hcontr. 
      }
      (* if PC can be incremented, load succeeds ==> apply IH *)
      iApply (wp_load_success_fromPC with "[HPC Hdst Ha]"); eauto.
      iFrame.
      iNext. iIntros "[HPC [Ha Hdst]] /=".
      iApply wp_pure_step_later; auto.
      (* we want to apply IH on the updated register state *)
      iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
        [apply lookup_insert|rewrite delete_insert_delete;iFrame|];
        rewrite -delete_insert_ne; auto;
          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
          [apply lookup_insert|rewrite delete_insert_delete;iFrame|].
      (* apply IH *)
      iAssert (▷ interp_registers _ (fs, fr) (<[dst:=w]> r))%I
        as "[Hfull Hreg']".
      { iNext. iSplitL.
        { iIntros (r0). iPureIntro.
          destruct (decide (dst = r0)); simplify_eq;
            [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto. }
        iIntros (r0) "%".
        destruct (decide (dst = r0)); simplify_eq.
        + by rewrite /RegLocate lookup_insert.
        + rewrite /RegLocate lookup_insert_ne; auto.
          iDestruct ("Hreg" $! (r0) a1) as "Hr0".
          specialize H3 with r0. 
          destruct H3 as [c Hsome].
          rewrite Hsome. iApply "Hr0"; auto.
      }
      iNext.
      iMod ("Hcls" with "[Heqws Hregionl Hh Ha $Hown]") as "Hown".
      { iNext.
        iDestruct (extract_from_region' _ _ a _
                                        (((fixpoint interp1) E) (fs, fr))
                     with "[Heqws Hregionl Hh Ha]") as "[Hbe Hregion]"; eauto.
        { iExists _. iFrame. rewrite Ha'. iFrame "∗ #". }
        iFrame. iIntros (stsf E0). iApply big_sepL_later. iNext. auto. }
      iApply ("IH" with "Hfull Hreg' Hmap Hsts Hown").
      iExact "Hinv". auto. 
    * destruct (H3 src) as [wsrc Hsomesrc].
      assert ((delete PC r !! src) = Some wsrc) as Hsomesrc'.
      { rewrite -Hsomesrc. apply (lookup_delete_ne r PC src). eauto. }
      rewrite delete_insert_delete. 
      iDestruct ((big_sepM_delete _ _ src) with "Hmap") as "[Hsrc Hmap]"; eauto.
      destruct wsrc.
      { (* src ↦ inl z ==> fail *)
        iApply (wp_load_fail2 with "[HPC Ha Hsrc]"); eauto; iFrame.
        iNext. iIntros "[HPC [Ha Hsrc]] /=".
        iApply wp_pure_step_later; auto. iApply wp_value.
        iNext. iIntros (Hcontr); inversion Hcontr. 
      } 
      (* src ↦ inr c ==> need to open invariant *)
      destruct c. do 3 destruct p.
      (* if p is not ra or a0 is not within bounds: fail *)
      destruct (decide ((readAllowed p && withinBounds ((p,l),a2,a1,a0)) = false)).
      { (* Capability fail *)
        iApply (wp_load_fail1 with "[HPC Ha Hsrc]"); eauto.
        - split; eauto. apply andb_false_iff. eauto.
        - iFrame.
        - iNext. iIntros "[HPC [Ha Hsrc]] /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value. iNext.
          iIntros (Hcontr); inversion Hcontr. 
      }
      (* readAllowed p && withinBounds ((p,l),a2,a1,a0) *)
      apply (not_false_is_true (_ && _)),Is_true_eq_left,andb_prop_elim in n1
        as [Hra Hwb]. apply andb_prop_elim in Hwb as [Hle Hge].
      (* the contents of src is valid *)
      iAssert ((fixpoint interp1) _ _ (inr (p, l, a2, a1, a0))) as "#Hvsrc".
      { apply reg_eq_sym in n0. iDestruct ("Hreg" $! src n0) as "Hvsrc".
        rewrite /RegLocate Hsomesrc /=. by iApply "Hvsrc". }
      iDestruct (read_allowed_inv with "Hvsrc") as "Hconds"; eauto.
      (* Each condition in Hconds take a step in similar fashion *)
      iAssert ((∃ w', ▷ (a0 ↦ₐ w' ∗ a ↦ₐ w
                         ={⊤}=∗ na_own logrel_nais E)
                        ∗ ▷ a0 ↦ₐ w' ∗ ▷ ▷ ⟦ w' ⟧ E (fs,fr)
               (* ∗ (∃ E', ⌜get_namespace w' = Some E'⌝ ∧ ⌜↑E' ⊆ E⌝)*))
                 ∗ sts_full fs fr
                 -∗ WP Instr Executable
                 {{ v, WP fill [SeqCtx] (of_val v)
                          {{ v0, ⌜v0 = HaltedV⌝
                                 → ∃ (r0 : Reg) (fs' : STS_states) (fr' : STS_rels),
                                 full_map r0
                                 ∧ registers_mapsto r0
                                                    ∗ ⌜related_sts_priv fs fs' fr fr'⌝
                                                    ∗ na_own logrel_nais E
                                                    ∗ sts_full fs' fr' }} }} )%I
                                                               with "[Ha HPC Hsrc Hmap]" as "Hstep".
      { iIntros "[Hcls' Hsts]". iDestruct "Hcls'" as (w0) "[Hcls' [Ha0 #Hw0]]". 
        (* if PC cannot be incremented ==> dst is updated, then program crashes *)
        destruct (a + 1)%a eqn:Ha'; simplify_eq.
        2: { destruct (decide (src = dst)); simplify_eq. 
             - iApply (wp_load_fail8 with "[HPC Hsrc Ha Ha0]"); eauto.
               { split; apply Is_true_eq_true; eauto. apply andb_prop_intro. eauto. }
               iFrame. iNext. iIntros "[HPC [Ha [Hdst Ha0]]] /=".
               iApply wp_pure_step_later; auto.
               iApply wp_value. iNext.
               iIntros (Hcontr); inversion Hcontr. 
             - destruct (H3 dst) as [wdst Hsomedst].
               assert (delete PC r !! dst = Some wdst) as Hsomedst'.
               { rewrite -Hsomedst. apply (lookup_delete_ne r PC dst). eauto. }
               assert (delete src (delete PC r) !! dst = Some wdst) as Hsomedst''.
               { rewrite -Hsomedst'. apply (lookup_delete_ne (delete PC r) src dst).
                 eauto. }
               iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]";
                 eauto.
               iApply (wp_load_fail7 with "[HPC Hsrc Hdst Ha Ha0]"); eauto.
               { split; apply Is_true_eq_true; eauto. apply andb_prop_intro. eauto. }
               iFrame. iNext. iIntros "(HPC & Ha & Hsrc & Ha0 & Hdst) /=".
               iApply wp_pure_step_later; auto.
               iApply wp_value. iNext.
               iIntros (Hcontr); inversion Hcontr. 
        }
        (* two successful steps: loading to a fresh dst, and loading to src *)
        destruct (decide (src = dst)); simplify_eq.
        - iApply (wp_load_success_same with "[HPC Hsrc Ha Ha0]"); eauto.
          { split; apply Is_true_eq_true; eauto. apply andb_prop_intro. eauto. }
          iFrame. iNext. iIntros "(HPC & Hdst & Ha & Ha0) /=".
          iApply wp_pure_step_later; auto. 
          iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|];
            rewrite -delete_insert_ne; auto;
              iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|].
          (* apply IH *)
          (* we will apply the IH on an updated register state *)
          (* we can only prove the following once we have taken a step *)
          iAssert (▷ interp_registers _ _ (<[dst:=w0]> r))%I as "[Hfull' Hreg']".
          { iNext. iSplitR.
            - iIntros (r0).
              iPureIntro.
              destruct (H3 r0) as [c Hsome]. 
              destruct (decide (dst = r0)); simplify_eq;
                [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
            - iIntros (r0) "% /=".
              iDestruct ("Hreg" $! (r0)) as "Hv".
              destruct (H3 r0) as [c Hsome]. 
              destruct (decide (dst = r0)); simplify_eq.
              + rewrite /RegLocate lookup_insert. iApply "Hw0". 
              + rewrite /RegLocate lookup_insert_ne; auto. 
                rewrite Hsome. iApply "Hv"; auto.  
          }
          iNext.
          iMod ("Hcls'" with "[$Ha0 $Ha]") as "Hown". 
          iApply ("IH" with "Hfull' Hreg' Hmap Hsts Hown"); auto. 
        - destruct (H3 dst) as [wdst Hsomedst].
          assert (delete PC r !! dst = Some wdst) as Hsomedst'.
          { rewrite -Hsomedst. apply (lookup_delete_ne r PC dst). eauto. }
          assert (delete src (delete PC r) !! dst = Some wdst) as Hsomedst''.
          { rewrite -Hsomedst'. apply (lookup_delete_ne (delete PC r) src dst).
            eauto. }
          iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]";
            eauto.
          iApply (wp_load_success with "[HPC Hsrc Hdst Ha Ha0]"); eauto.
          { split; apply Is_true_eq_true; eauto. apply andb_prop_intro. eauto. }
          iFrame. iNext. iIntros "(HPC & Hdst & Ha & Hsrc & Ha0) /=".
          iApply wp_pure_step_later; auto. 
          iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|];
            rewrite -delete_insert_ne; auto;
              iDestruct ((big_sepM_delete _ _ src) with "[Hsrc Hmap]") as "Hmap /=";
              [apply lookup_insert|rewrite delete_insert_delete;iFrame|];
              rewrite -delete_insert_ne; auto;
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete|].
          rewrite -delete_insert_ne; auto. iFrame. 
          (* apply IH *)
          (* we will apply the IH on an updated register state *)
          (* we can only prove the following once we have taken a step *)
          iAssert (▷ interp_registers _ _ (<[src:=inr (p, l, a2, a1, a0)]> (<[dst:=w0]> r)))%I
            as "[Hfull' Hreg']".
          { iNext. iSplitR.
            - iIntros (r0).
              destruct (H3 r0) as [c Hsome].
              iPureIntro.
              destruct (decide (src = r0)); simplify_eq;
                [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
              destruct (decide (dst = r0)); simplify_eq;
                [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
            - iIntros (r0) "%".
              destruct (H3 r0) as [c Hsome].
              iDestruct ("Hreg" $! (r0)) as "Hv".
              destruct (decide (src = r0)); simplify_eq.
              + rewrite /RegLocate lookup_insert. iApply "Hvsrc". 
              + rewrite /RegLocate lookup_insert_ne; auto. 
                rewrite Hsome. destruct (decide (dst = r0)); simplify_eq.
                * by rewrite lookup_insert.
                * rewrite lookup_insert_ne. rewrite Hsome. iApply "Hv"; auto.
                  auto. 
          }
          iNext.
          iMod ("Hcls'" with "[$Ha0 $Ha]") as "Hown". 
          iApply ("IH" with "Hfull' Hreg' Hmap Hsts Hown"); auto. 
      }
      destruct (decide ((b,e) = (a2,a1))).
      {
        inversion e0; subst. 
        (* no need to open any invariant *)
        admit. 
      }
      iDestruct "Hconds" as "[[#Hro|#[Hrw|Hrwl]] %]".
      (* each condition is similar, but with some subtle differences for closing *)
      { iDestruct "Hro" as (ws0) "#Hinv0".
        (* open the invariant to access a0 ↦ₐ _ *)
        assert (↑logN.@(a2, a1) ⊆ (E ∖ ↑logN.@(b, e))) as Ha2a1.
        { apply namespace_subseteq_difference; auto.
          rewrite /namespace_subseteq_difference.
            by apply ndot_ne_disjoint.
        }
        iMod (na_inv_open with "Hinv0 Hown") as "[Hro_cond [Hown' Hcls']]"; auto. 
        rewrite /read_only_cond.
        iDestruct "Hro_cond" as "[Ha2a1 #Hro_cond]".
        iDestruct ("Hro_cond" $! (fs,fr) E) as "Hro_cond'".
        iCombine "Ha2a1 Hro_cond'" as "Hregion". 
        iDestruct (extract_from_region' _ _ a0 with "Hregion") as (w0) "(Heqws' & Hregion0l & _ & >Ha0 & #Hva0 & Hh0)"; first (split; by apply Z.leb_le,Is_true_eq_true).
        iApply "Hstep". iFrame "Hsts".
        iExists w0. iFrame "Ha0 Hva0". 
        iNext. iIntros "[Ha0 Ha]".
        iMod ("Hcls'" with "[Hown' Heqws' Hregion0l Ha0 Hh0]") as "Hown".
        { iFrame. iNext.
          iDestruct (extract_from_region' _ _ a0 _
                                          (((fixpoint interp1) E) (fs, fr))
                       with "[Heqws' Hregion0l Ha0 Hh0]")
            as "Hregion";
            first (split; by apply Z.leb_le,Is_true_eq_true).
          { iFrame. iExists _. iFrame "∗ #". }
          iDestruct "Hregion" as "[$ _]".
          iIntros (stsf E0). iApply big_sepL_later. iNext. auto. 
        }
        iMod ("Hcls" with "[$Hown Hregionl Hh Ha Heqws]") as "Hown".
        { iNext. 
          iDestruct (extract_from_region' _ _ a _
                                          (((fixpoint interp1) E) (fs, fr))
                       with "[Hregionl Hh Ha Heqws]")
            as "Hregion"; eauto.
          { iExists _. iFrame. iFrame "∗ #". }
          iDestruct "Hregion" as "[$ _]".
          iIntros (stsf E0). iApply big_sepL_later. iNext. auto. 
        } 
        iModIntro. iFrame. 
      }
      { (* open the invariant to access a0 ↦ₐ _ *)
        assert (↑logN.@(a2, a1) ⊆ (E ∖ ↑logN.@(b, e))) as Ha2a1.
        { apply namespace_subseteq_difference; auto.
          rewrite /namespace_subseteq_difference.
            by apply ndot_ne_disjoint.
        }
        iMod (na_inv_open with "Hrw Hown") as "[Hrw_cond [Hown Hcls']]"; auto. 
        iDestruct "Hrw_cond" as (ws0) "Hrw_cond".
        iDestruct "Hrw_cond" as "[Ha2a1 #Hrw_cond]".
        iDestruct ("Hrw_cond" $! (fs,fr) E) as "Hrw_cond'".
        iCombine "Ha2a1 Hrw_cond'" as "Hregion".
        iDestruct (extract_from_region' _ _ a0 with "Hregion") as (w0) "(Heqws' & Hregion0l & _ & >Ha0 & #[Hva0 Hnl] & Hh0)"; first (split; by apply Z.leb_le,Is_true_eq_true).
        iApply "Hstep". iFrame "Hsts".
        iExists w0. iFrame "Ha0 #".
        iNext. iIntros "[Ha0 Ha]". 
        iMod ("Hcls'" with "[Hown Heqws' Hregion0l Ha0 Hh0]") as "Hown".
        { iFrame. iNext.
          iDestruct (extract_from_region' _ _ a0 _
                                          (((fixpoint interp1) E) (fs, fr))
                       with "[Heqws' Hregion0l Ha0 Hh0]")
            as "Hregion";
            first (split; by apply Z.leb_le,Is_true_eq_true).
          { iFrame. iExists _. iFrame "∗ #".
            iDestruct (big_sepL_sepL with "Hrw_cond") as "[$ _]". 
          }
          iExists _. iDestruct "Hregion" as "[$ _]".
          iIntros (stsf E0). iApply big_sepL_later. iNext. auto. 
        }
        iMod ("Hcls" with "[$Hown Hregionl Hh Ha Heqws]") as "Hown".
        { iNext. 
          iDestruct (extract_from_region' _ _ a _
                                          (((fixpoint interp1) E) (fs, fr))
                       with "[Hregionl Hh Ha Heqws]")
            as "Hregion"; eauto.
          { iExists _. iFrame. iFrame "∗ #". }
          iDestruct "Hregion" as "[$ _]".
          iIntros (stsf E0). iApply big_sepL_later. iNext. auto. 
        } 
        iModIntro. iFrame.
      }
      { (* open the invariant to access a0 ↦ₐ _ *)
        assert (↑logN.@(a2, a1) ⊆ (E ∖ ↑logN.@(b, e))) as Ha2a1.
        { apply namespace_subseteq_difference; auto.
          rewrite /namespace_subseteq_difference.
            by apply ndot_ne_disjoint.
        }
        iMod (na_inv_open with "Hrwl Hown") as "[Hrw_cond [Hown Hcls']]"; auto. 
        iDestruct "Hrw_cond" as (ws0) "Hrw_cond".
        iDestruct "Hrw_cond" as "[Ha2a1 #Hrw_cond]".
        iDestruct ("Hrw_cond" $! (fs,fr) E) as "Hrw_cond'".
        iCombine "Ha2a1 Hrw_cond'" as "Hregion".
        iDestruct (extract_from_region' _ _ a0 with "Hregion") as (w0) "(Heqws' & Hregion0l & _ & >Ha0 & #Hva0 & Hh0)"; first (split; by apply Z.leb_le,Is_true_eq_true).
        iApply "Hstep". iFrame "Hsts".
        iExists w0. iFrame "Ha0 #".
        iNext. iIntros "[Ha0 Ha]". 
        iMod ("Hcls'" with "[Hown Heqws' Hregion0l Ha0 Hh0]") as "Hown".
        { iFrame. iNext.
          iDestruct (extract_from_region' _ _ a0 _
                                          (((fixpoint interp1) E) (fs, fr))
                       with "[Heqws' Hregion0l Ha0 Hh0]")
            as "Hregion";
            first (split; by apply Z.leb_le,Is_true_eq_true).
          { iFrame. iExists _. iFrame "∗ #". }
          iExists _. iDestruct "Hregion" as "[$ _]".
          iIntros (stsf E0). iApply big_sepL_later. iNext. auto. 
        }
        iMod ("Hcls" with "[$Hown Hregionl Hh Ha Heqws]") as "Hown".
        { iNext. 
          iDestruct (extract_from_region' _ _ a _
                                          (((fixpoint interp1) E) (fs, fr))
                       with "[Hregionl Hh Ha Heqws]")
            as "Hregion"; eauto.
          { iExists _. iFrame. iFrame "∗ #". }
          iDestruct "Hregion" as "[$ _]".
          iIntros (stsf E0). iApply big_sepL_later. iNext. auto. 
        } 
        iModIntro. iFrame.
      }
  Admitted.

  Lemma RX_Store_case:
    ∀ (E0 : coPset) (r : leibnizC Reg) (a : Addr) (g : Locality) (fs : leibnizC STS_states) (fr : leibnizC STS_rels) 
      (b e : Addr) (ws : list Word) (w : Word) (dst : RegName) (src: Z + RegName)
      (fundamental_RWX : ∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) (E : coPset) (r : leibnizC Reg) 
                           (b e : Addr) (g : Locality) (a : Addr), (na_inv logrel_nais (logN.@(b, e))
                                                                           (read_write_cond b e interp)
                                                                    → (λ (stsf0 : prodC (leibnizC STS_states) (leibnizC STS_rels)) 
                                                                         (E0 : coPset) (r0 : leibnizC Reg), 
                                                                       ((interp_expression E0 r0) stsf0) 
                                                                         (inr (RWX, g, b, e, a))) stsf E r)%I)
      (fundamental_RWLX : ∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) (E : coPset) (r : leibnizC Reg) 
                            (b e : Addr) (g : Locality) (a : Addr), (na_inv logrel_nais (logN.@(b, e))
                                                                            (read_write_local_cond b e interp)
                                                                     → (λ (stsf0 : prodC (leibnizC STS_states)
                                                                                         (leibnizC STS_rels)) 
                                                                          (E0 : coPset) (r0 : leibnizC Reg), 
                                                                        ((interp_expression E0 r0) stsf0)
                                                                          (inr (RWLX, g, b, e, a))) stsf E r)%I)
      (Hreach : ∀ ns : namespace, Some (logN.@(b, e)) = Some ns → ↑ns ⊆ E0)
      (H3 : ∀ x : RegName, (λ x0 : RegName, is_Some (r !! x0)) x)
      (i : isCorrectPC (inr (RX, g, b, e, a)))
      (Hbae : (b <= a)%a ∧ (a <= e)%a)
      (Hbe : ↑logN.@(b, e) ⊆ E0)
      (Hi : cap_lang.decode w = Store dst src),
      □ ▷ ▷ ((interp E0) (fs, fr)) w
        -∗ □ ▷ ([∗ list] w0 ∈ ws, ▷ ((interp E0) (fs, fr)) w0)
        -∗ □ ▷ (∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) (E1 : leibnizC coPset), [∗ list] w0 ∈ ws, ▷ 
                                                                                                                       ((interp E1) stsf) w0)
        -∗ □ (∀ r0 : RegName, ⌜r0 ≠ PC⌝ → (((fixpoint interp1) E0) (fs, fr)) (r !r! r0))
        -∗ □ na_inv logrel_nais (logN.@(b, e))
        ([[b,e]]↦ₐ[[ws]]
                ∗ (∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) (E1 : leibnizC coPset), [∗ list] w0 ∈ ws, ▷ 
                                                                                                                          ((interp E1) stsf) w0))
        -∗ □ ▷ (∀ (a0 : leibnizC Reg) (a1 : Addr) (a2 : Locality) (a3 : leibnizC STS_states) 
                  (a4 : leibnizC STS_rels) (a5 a6 : Addr) (a7 : list Word), full_map a0
                                                                                     -∗ (∀ r0 : RegName, 
                                                                                            ⌜r0 ≠ PC⌝
                                                                                            → (((fixpoint interp1) E0) (a3, a4))
                                                                                                (a0 !r! r0))
                                                                                     -∗ registers_mapsto
                                                                                     (<[PC:=
                                                                                          inr (RX, a2, a5, a6, a1)]> a0)
                                                                                     -∗ sts_full a3 a4
                                                                                     -∗ na_own logrel_nais E0
                                                                                     -∗ 
                                                                                     □ 
                                                                                     na_inv logrel_nais
                                                                                     (logN.@(a5, a6))
                                                                                     ([[a5,a6]]↦ₐ[[a7]]
                                                                                               ∗ 
                                                                                               (∀ (stsf : 
                                                                                                     prodC 
                                                                                                       (leibnizC STS_states)
                                                                                                       (leibnizC STS_rels)) 
                                                                                                  (E1 : 
                                                                                                     leibnizC coPset), [∗ list] w0 ∈ a7, ▷ 
                                                                                                                                           ((interp E1) stsf) w0))
                                                                                     -∗ 
                                                                                     □ ⌜
                                                                                     ∀ ns : namespace, 
                                                                                       Some (logN.@(a5, a6)) =
                                                                                       Some ns → 
                                                                                       ↑ns ⊆ E0⌝ -∗ 
                                                                                        ⟦ [a3, a4, E0] ⟧ₒ)
        -∗ ([∗ map] k↦y ∈ delete PC (<[PC:=inr (RX, g, b, e, a)]> r), k ↦ᵣ y)
        -∗ PC ↦ᵣ inr (RX, g, b, e, a)
        -∗ ▷ match (a + 1)%a with
             | Some ah =>
               [[ah,e]]↦ₐ[[drop (S (length (region_addrs b (get_addr_from_option_addr (a + -1)%a)))) ws]]
             | None => ⌜drop (S (length (region_addrs b (get_addr_from_option_addr (a + -1)%a)))) ws = []⌝
             end
        -∗ a ↦ₐ w
        -∗ ▷ ([[b,get_addr_from_option_addr (a + -1)%a]]↦ₐ[[take
                                                              (length
                                                                 (region_addrs b
                                                                               (get_addr_from_option_addr
                                                                                  (a + -1)%a))) ws]])
        -∗ ▷ ⌜ws =
      take (length (region_addrs b (get_addr_from_option_addr (a + -1)%a))) ws ++
           w :: drop (S (length (region_addrs b (get_addr_from_option_addr (a + -1)%a)))) ws⌝
           -∗ (▷ ([[b,e]]↦ₐ[[ws]]
                         ∗ (∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) 
                              (E1 : leibnizC coPset), [∗ list] w0 ∈ ws, ▷ ((interp E1) stsf) w0))
                 ∗ na_own logrel_nais (E0 ∖ ↑logN.@(b, e)) ={⊤}=∗ na_own logrel_nais E0)
           -∗ na_own logrel_nais (E0 ∖ ↑logN.@(b, e))
           -∗ sts_full fs fr
           -∗ WP Instr Executable
           {{ v, WP fill [SeqCtx] (of_val v)
                    {{ v0, ⌜v0 = HaltedV⌝
                           → ∃ (r0 : Reg) (fs' : STS_states) (fr' : STS_rels), 
                           full_map r0
                           ∧ registers_mapsto r0
                                              ∗ ⌜related_sts_priv fs fs' fr fr'⌝
                                              ∗ na_own logrel_nais E0 ∗ sts_full fs' fr' }} }}.
  Proof.
    intros E r a g fs fr b e ws w. intros.
    iIntros "#Hva #Hval' #Hval #Hreg #Hinv #IH".
    iIntros "Hmap HPC Hh Ha Hregionl Heqws Hcls Hown Hsts".
    rewrite delete_insert_delete.
    destruct (reg_eq_dec dst PC).
    * subst dst. assert (writeAllowed RX = false) by reflexivity.
      iApply (wp_store_fail1' with "[HPC Ha]"); eauto; iFrame.
      iNext. iIntros. iApply wp_pure_step_later; auto.
      iNext. iApply wp_value. iIntros. discriminate.
    * destruct (H3 dst) as [wdst Hsomedst].
      iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]"; [rewrite lookup_delete_ne; eauto|].
      destruct wdst.
      { iApply (wp_store_fail2 with "[HPC Hdst Ha]"); eauto; iFrame.
        iNext. iIntros. iApply wp_pure_step_later; auto.
        iNext. iApply wp_value. iIntros. discriminate. }
      { destruct c,p,p,p. 
        case_eq (writeAllowed p); intros.
        - case_eq (withinBounds (p, l, a2, a1, a0)); intros.
          + destruct src.
            * (* need to get a0 ↦ₐ _ and stuff, todo later *)
              (* take the points to earlier, to factorize *)
              admit.
            * destruct (reg_eq_dec r0 PC).
              { subst r0. (* need to get a0 ↦ₐ _, todo later *) admit. }
              { destruct (reg_eq_dec dst r0).
                - subst r0. (* same thing *) admit.
                - destruct (H3 r0) as [wr0 Hsomer0].
                  iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]"; [repeat rewrite lookup_delete_ne; eauto|].
                  (* same thing, todo *) admit. }
          + iApply (wp_store_fail1 with "[HPC Hdst Ha]"); eauto; iFrame.
            iNext. iIntros. iApply wp_pure_step_later; auto.
            iNext. iApply wp_value. iIntros. discriminate.
        - iApply (wp_store_fail1 with "[HPC Hdst Ha]"); eauto; iFrame.
          iNext. iIntros. iApply wp_pure_step_later; auto.
          iNext. iApply wp_value. iIntros. discriminate. }
  Admitted.
    

   Lemma RX_Add_Sub_Lt_case:
    ∀ (E0 : coPset) (r : leibnizC Reg) (a : Addr) (g : Locality) (fs : leibnizC STS_states) (fr : leibnizC STS_rels) 
      (b e : Addr) (ws : list Word) (w : Word) (dst : RegName) (r1 r2: Z + RegName)
      (fundamental_RWX : ∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) (E : coPset) (r : leibnizC Reg) 
                           (b e : Addr) (g : Locality) (a : Addr), (na_inv logrel_nais (logN.@(b, e))
                                                                           (read_write_cond b e interp)
                                                                    → (λ (stsf0 : prodC (leibnizC STS_states) (leibnizC STS_rels)) 
                                                                         (E0 : coPset) (r0 : leibnizC Reg), 
                                                                       ((interp_expression E0 r0) stsf0) 
                                                                         (inr (RWX, g, b, e, a))) stsf E r)%I)
      (fundamental_RWLX : ∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) (E : coPset) (r : leibnizC Reg) 
                            (b e : Addr) (g : Locality) (a : Addr), (na_inv logrel_nais (logN.@(b, e))
                                                                            (read_write_local_cond b e interp)
                                                                     → (λ (stsf0 : prodC (leibnizC STS_states)
                                                                                         (leibnizC STS_rels)) 
                                                                          (E0 : coPset) (r0 : leibnizC Reg), 
                                                                        ((interp_expression E0 r0) stsf0)
                                                                          (inr (RWLX, g, b, e, a))) stsf E r)%I)
      (Hreach : ∀ ns : namespace, Some (logN.@(b, e)) = Some ns → ↑ns ⊆ E0)
      (H3 : ∀ x : RegName, (λ x0 : RegName, is_Some (r !! x0)) x)
      (i : isCorrectPC (inr (RX, g, b, e, a)))
      (Hbae : (b <= a)%a ∧ (a <= e)%a)
      (Hbe : ↑logN.@(b, e) ⊆ E0)
      (Hi : cap_lang.decode w = cap_lang.Add dst r1 r2 \/ cap_lang.decode w = Sub dst r1 r2 \/ cap_lang.decode w = Lt dst r1 r2),
      □ ▷ ▷ ((interp E0) (fs, fr)) w
        -∗ □ ▷ ([∗ list] w0 ∈ ws, ▷ ((interp E0) (fs, fr)) w0)
        -∗ □ ▷ (∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) (E1 : leibnizC coPset), [∗ list] w0 ∈ ws, ▷ 
                                                                                                                       ((interp E1) stsf) w0)
        -∗ □ (∀ r0 : RegName, ⌜r0 ≠ PC⌝ → (((fixpoint interp1) E0) (fs, fr)) (r !r! r0))
        -∗ □ na_inv logrel_nais (logN.@(b, e))
        ([[b,e]]↦ₐ[[ws]]
                ∗ (∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) (E1 : leibnizC coPset), [∗ list] w0 ∈ ws, ▷ 
                                                                                                                          ((interp E1) stsf) w0))
        -∗ □ ▷ (∀ (a0 : leibnizC Reg) (a1 : Addr) (a2 : Locality) (a3 : leibnizC STS_states) 
                  (a4 : leibnizC STS_rels) (a5 a6 : Addr) (a7 : list Word), full_map a0
                                                                                     -∗ (∀ r0 : RegName, 
                                                                                            ⌜r0 ≠ PC⌝
                                                                                            → (((fixpoint interp1) E0) (a3, a4))
                                                                                                (a0 !r! r0))
                                                                                     -∗ registers_mapsto
                                                                                     (<[PC:=
                                                                                          inr (RX, a2, a5, a6, a1)]> a0)
                                                                                     -∗ sts_full a3 a4
                                                                                     -∗ na_own logrel_nais E0
                                                                                     -∗ 
                                                                                     □ 
                                                                                     na_inv logrel_nais
                                                                                     (logN.@(a5, a6))
                                                                                     ([[a5,a6]]↦ₐ[[a7]]
                                                                                               ∗ 
                                                                                               (∀ (stsf : 
                                                                                                     prodC 
                                                                                                       (leibnizC STS_states)
                                                                                                       (leibnizC STS_rels)) 
                                                                                                  (E1 : 
                                                                                                     leibnizC coPset), [∗ list] w0 ∈ a7, ▷ 
                                                                                                                                           ((interp E1) stsf) w0))
                                                                                     -∗ 
                                                                                     □ ⌜
                                                                                     ∀ ns : namespace, 
                                                                                       Some (logN.@(a5, a6)) =
                                                                                       Some ns → 
                                                                                       ↑ns ⊆ E0⌝ -∗ 
                                                                                        ⟦ [a3, a4, E0] ⟧ₒ)
        -∗ ([∗ map] k↦y ∈ delete PC (<[PC:=inr (RX, g, b, e, a)]> r), k ↦ᵣ y)
        -∗ PC ↦ᵣ inr (RX, g, b, e, a)
        -∗ ▷ match (a + 1)%a with
             | Some ah =>
               [[ah,e]]↦ₐ[[drop (S (length (region_addrs b (get_addr_from_option_addr (a + -1)%a)))) ws]]
             | None => ⌜drop (S (length (region_addrs b (get_addr_from_option_addr (a + -1)%a)))) ws = []⌝
             end
        -∗ a ↦ₐ w
        -∗ ▷ ([[b,get_addr_from_option_addr (a + -1)%a]]↦ₐ[[take
                                                              (length
                                                                 (region_addrs b
                                                                               (get_addr_from_option_addr
                                                                                  (a + -1)%a))) ws]])
        -∗ ▷ ⌜ws =
      take (length (region_addrs b (get_addr_from_option_addr (a + -1)%a))) ws ++
           w :: drop (S (length (region_addrs b (get_addr_from_option_addr (a + -1)%a)))) ws⌝
           -∗ (▷ ([[b,e]]↦ₐ[[ws]]
                         ∗ (∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) 
                              (E1 : leibnizC coPset), [∗ list] w0 ∈ ws, ▷ ((interp E1) stsf) w0))
                 ∗ na_own logrel_nais (E0 ∖ ↑logN.@(b, e)) ={⊤}=∗ na_own logrel_nais E0)
           -∗ na_own logrel_nais (E0 ∖ ↑logN.@(b, e))
           -∗ sts_full fs fr
           -∗ WP Instr Executable
           {{ v, WP fill [SeqCtx] (of_val v)
                    {{ v0, ⌜v0 = HaltedV⌝
                           → ∃ (r0 : Reg) (fs' : STS_states) (fr' : STS_rels), 
                           full_map r0
                           ∧ registers_mapsto r0
                                              ∗ ⌜related_sts_priv fs fs' fr fr'⌝
                                              ∗ na_own logrel_nais E0 ∗ sts_full fs' fr' }} }}.
   Proof.
     intros E r a g fs fr b e ws w. intros.
     iIntros "#Hva #Hval' #Hval #Hreg #Hinv #IH".
     iIntros "Hmap HPC Hh Ha Hregionl Heqws Hcls Hown Hsts".
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
     * rewrite -big_sepL_later.
       destruct (H3 dst) as [wdst Hsomedst].
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
           iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr)) with
                          "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto.
           { iExists _. iFrame. iFrame "∗ #". }
           iAssert ((interp_registers _ _ (<[dst:=match cap_lang.decode w with
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
           -- iMod ("Hcls" with "[Hown Hregion]") as "Hcls'".
              { iFrame. iNext. iDestruct "Hregion" as "[H1 H2]".
                iFrame. iIntros. rewrite -big_sepL_later. iNext.
                iApply "Hval". }
              simpl. 
              iApply ("IH" with "[Hfull'] [Hreg'] [Hmap] [Hsts] [Hcls']"); eauto.
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
                     iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr))with
                                    "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto.
                     { iExists _. rewrite H4; iFrame "∗ #". }
                     iMod ("Hcls" with "[Hown Hregion]") as "Hcls'".
                     { iFrame. iDestruct "Hregion" as "[H1 H2]".
                       iNext. iFrame. iIntros. rewrite -big_sepL_later. iNext. auto. }
                     iAssert ((interp_registers _ _ (<[dst:=match cap_lang.decode w with
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
                     iApply ("IH" with "[Hfull'] [Hreg'] [Hmap] [Hsts] [Hcls']"); eauto.
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
                     iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr)) with
                                    "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto.
                     { iExists _. rewrite H4; iFrame "∗ #". }
                     iMod ("Hcls" with "[Hown Hregion]") as "Hcls'".
                     { iFrame. iDestruct "Hregion" as "[H1 H2]".
                       iNext. iFrame. iIntros. rewrite -big_sepL_later. iNext. auto. }
                     iAssert ((interp_registers _ _ (<[dst:=match cap_lang.decode w with
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
                     iApply ("IH" with "[Hfull'] [Hreg'] [Hmap] [Hsts] [Hcls']"); eauto.
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
                     iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr))with
                                    "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto.
                     { iExists _. rewrite H4; iFrame "∗ #". }
                     iMod ("Hcls" with "[Hown Hregion]") as "Hcls'".
                     { iFrame. iDestruct "Hregion" as "[H1 H2]".
                       iNext. iFrame. iIntros. rewrite -big_sepL_later. iNext. auto. }
                     iAssert ((interp_registers _ _ (<[dst:=match cap_lang.decode w with
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
                     iApply ("IH" with "[Hfull'] [Hreg'] [Hmap] [Hsts] [Hcls']"); eauto.
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
                     iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr))with
                                    "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto.
                     { iExists _. rewrite H4; iFrame "∗ #". }
                     iMod ("Hcls" with "[Hown Hregion]") as "Hcls'".
                     { iFrame. iDestruct "Hregion" as "[H1 H2]".
                       iNext. iFrame. iIntros. rewrite -big_sepL_later. iNext. auto. }
                     iAssert ((interp_registers _ _ (<[dst:=match cap_lang.decode w with
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
                     iApply ("IH" with "[Hfull'] [Hreg'] [Hmap] [Hsts] [Hcls']"); eauto.
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
                       iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr))with
                                      "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto.
                       { iExists _. rewrite H4; iFrame "∗ #". }
                       iMod ("Hcls" with "[Hown Hregion]") as "Hcls'".
                       { iFrame. iDestruct "Hregion" as "[H1 H2]".
                         iNext. iFrame. iIntros. rewrite -big_sepL_later. iNext. auto. }
                       iAssert ((interp_registers _ _ (<[dst:=match cap_lang.decode w with
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
                       iApply ("IH" with "[Hfull'] [Hreg'] [Hmap] [Hsts] [Hcls']"); eauto.
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
                         iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr))with
                                        "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto.
                         { iExists _. rewrite H4; iFrame "∗ #". }
                         iMod ("Hcls" with "[Hown Hregion]") as "Hcls'".
                         { iFrame. iDestruct "Hregion" as "[H1 H2]".
                           iNext. iFrame. iIntros. rewrite -big_sepL_later. iNext. auto. }
                         iAssert ((interp_registers _ _ (<[dst:=match cap_lang.decode w with
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
                         iApply ("IH" with "[Hfull'] [Hreg'] [Hmap] [Hsts] [Hcls']"); eauto. }
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
                         iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr))with
                                        "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto.
                         { iExists _. rewrite H4; iFrame "∗ #". }
                         iMod ("Hcls" with "[Hown Hregion]") as "Hcls'".
                         { iFrame. iDestruct "Hregion" as "[H1 H2]".
                           iNext. iFrame. iIntros. rewrite -big_sepL_later. iNext. auto. }
                         iAssert ((interp_registers _ _ (<[dst:=match cap_lang.decode w with
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
                         iApply ("IH" with "[Hfull'] [Hreg'] [Hmap] [Hsts] [Hcls']"); eauto. }
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
                         iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr))with
                                        "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto.
                         { iExists _. rewrite H4; iFrame "∗ #". }
                         iMod ("Hcls" with "[Hown Hregion]") as "Hcls'".
                         { iFrame. iDestruct "Hregion" as "[H1 H2]".
                           iNext. iFrame. iIntros. rewrite -big_sepL_later. iNext. auto. }
                         iAssert ((interp_registers _ _ (<[dst:= match cap_lang.decode w with
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
                         iApply ("IH" with "[Hfull'] [Hreg'] [Hmap] [Hsts] [Hcls']"); eauto. }
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
                           iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr))with
                                          "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto.
                           { iExists _. rewrite H4; iFrame "∗ #". }
                           iMod ("Hcls" with "[Hown Hregion]") as "Hcls'".
                           { iFrame. iDestruct "Hregion" as "[H1 H2]".
                             iNext. iFrame. iIntros. rewrite -big_sepL_later. iNext. auto. }
                           iAssert ((interp_registers _ _ (<[dst:=match cap_lang.decode w with
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
                           iApply ("IH" with "[Hfull'] [Hreg'] [Hmap] [Hsts] [Hcls']"); eauto.
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

   Lemma RX_Lea_case:
    ∀ (E0 : coPset) (r : leibnizC Reg) (a : Addr) (g : Locality) (fs : leibnizC STS_states) (fr : leibnizC STS_rels) 
      (b e : Addr) (ws : list Word) (w : Word) (dst : RegName) (r0: Z + RegName)
      (fundamental_RWX : ∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) (E : coPset) (r : leibnizC Reg) 
                           (b e : Addr) (g : Locality) (a : Addr), (na_inv logrel_nais (logN.@(b, e))
                                                                           (read_write_cond b e interp)
                                                                    → (λ (stsf0 : prodC (leibnizC STS_states) (leibnizC STS_rels)) 
                                                                         (E0 : coPset) (r0 : leibnizC Reg), 
                                                                       ((interp_expression E0 r0) stsf0) 
                                                                         (inr (RWX, g, b, e, a))) stsf E r)%I)
      (fundamental_RWLX : ∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) (E : coPset) (r : leibnizC Reg) 
                            (b e : Addr) (g : Locality) (a : Addr), (na_inv logrel_nais (logN.@(b, e))
                                                                            (read_write_local_cond b e interp)
                                                                     → (λ (stsf0 : prodC (leibnizC STS_states)
                                                                                         (leibnizC STS_rels)) 
                                                                          (E0 : coPset) (r0 : leibnizC Reg), 
                                                                        ((interp_expression E0 r0) stsf0)
                                                                          (inr (RWLX, g, b, e, a))) stsf E r)%I)
      (Hreach : ∀ ns : namespace, Some (logN.@(b, e)) = Some ns → ↑ns ⊆ E0)
      (H3 : ∀ x : RegName, (λ x0 : RegName, is_Some (r !! x0)) x)
      (i : isCorrectPC (inr (RX, g, b, e, a)))
      (Hbae : (b <= a)%a ∧ (a <= e)%a)
      (Hbe : ↑logN.@(b, e) ⊆ E0)
      (Hi : cap_lang.decode w = Lea dst r0),
      □ ▷ ▷ ((interp E0) (fs, fr)) w
        -∗ □ ▷ ([∗ list] w0 ∈ ws, ▷ ((interp E0) (fs, fr)) w0)
        -∗ □ ▷ (∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) (E1 : leibnizC coPset), [∗ list] w0 ∈ ws, ▷ 
                                                                                                                       ((interp E1) stsf) w0)
        -∗ □ (∀ r0 : RegName, ⌜r0 ≠ PC⌝ → (((fixpoint interp1) E0) (fs, fr)) (r !r! r0))
        -∗ □ na_inv logrel_nais (logN.@(b, e))
        ([[b,e]]↦ₐ[[ws]]
                ∗ (∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) (E1 : leibnizC coPset), [∗ list] w0 ∈ ws, ▷ 
                                                                                                                          ((interp E1) stsf) w0))
        -∗ □ ▷ (∀ (a0 : leibnizC Reg) (a1 : Addr) (a2 : Locality) (a3 : leibnizC STS_states) 
                  (a4 : leibnizC STS_rels) (a5 a6 : Addr) (a7 : list Word), full_map a0
                                                                                     -∗ (∀ r0 : RegName, 
                                                                                            ⌜r0 ≠ PC⌝
                                                                                            → (((fixpoint interp1) E0) (a3, a4))
                                                                                                (a0 !r! r0))
                                                                                     -∗ registers_mapsto
                                                                                     (<[PC:=
                                                                                          inr (RX, a2, a5, a6, a1)]> a0)
                                                                                     -∗ sts_full a3 a4
                                                                                     -∗ na_own logrel_nais E0
                                                                                     -∗ 
                                                                                     □ 
                                                                                     na_inv logrel_nais
                                                                                     (logN.@(a5, a6))
                                                                                     ([[a5,a6]]↦ₐ[[a7]]
                                                                                               ∗ 
                                                                                               (∀ (stsf : 
                                                                                                     prodC 
                                                                                                       (leibnizC STS_states)
                                                                                                       (leibnizC STS_rels)) 
                                                                                                  (E1 : 
                                                                                                     leibnizC coPset), [∗ list] w0 ∈ a7, ▷ 
                                                                                                                                           ((interp E1) stsf) w0))
                                                                                     -∗ 
                                                                                     □ ⌜
                                                                                     ∀ ns : namespace, 
                                                                                       Some (logN.@(a5, a6)) =
                                                                                       Some ns → 
                                                                                       ↑ns ⊆ E0⌝ -∗ 
                                                                                        ⟦ [a3, a4, E0] ⟧ₒ)
        -∗ ([∗ map] k↦y ∈ delete PC (<[PC:=inr (RX, g, b, e, a)]> r), k ↦ᵣ y)
        -∗ PC ↦ᵣ inr (RX, g, b, e, a)
        -∗ ▷ match (a + 1)%a with
             | Some ah =>
               [[ah,e]]↦ₐ[[drop (S (length (region_addrs b (get_addr_from_option_addr (a + -1)%a)))) ws]]
             | None => ⌜drop (S (length (region_addrs b (get_addr_from_option_addr (a + -1)%a)))) ws = []⌝
             end
        -∗ a ↦ₐ w
        -∗ ▷ ([[b,get_addr_from_option_addr (a + -1)%a]]↦ₐ[[take
                                                              (length
                                                                 (region_addrs b
                                                                               (get_addr_from_option_addr
                                                                                  (a + -1)%a))) ws]])
        -∗ ▷ ⌜ws =
      take (length (region_addrs b (get_addr_from_option_addr (a + -1)%a))) ws ++
           w :: drop (S (length (region_addrs b (get_addr_from_option_addr (a + -1)%a)))) ws⌝
           -∗ (▷ ([[b,e]]↦ₐ[[ws]]
                         ∗ (∀ (stsf : prodC (leibnizC STS_states) (leibnizC STS_rels)) 
                              (E1 : leibnizC coPset), [∗ list] w0 ∈ ws, ▷ ((interp E1) stsf) w0))
                 ∗ na_own logrel_nais (E0 ∖ ↑logN.@(b, e)) ={⊤}=∗ na_own logrel_nais E0)
           -∗ na_own logrel_nais (E0 ∖ ↑logN.@(b, e))
           -∗ sts_full fs fr
           -∗ WP Instr Executable
           {{ v, WP fill [SeqCtx] (of_val v)
                    {{ v0, ⌜v0 = HaltedV⌝
                           → ∃ (r0 : Reg) (fs' : STS_states) (fr' : STS_rels), 
                           full_map r0
                           ∧ registers_mapsto r0
                                              ∗ ⌜related_sts_priv fs fs' fr fr'⌝
                                              ∗ na_own logrel_nais E0 ∗ sts_full fs' fr' }} }}.
   Proof.
     intros E r a g fs fr b e ws w. intros.
     iIntros "#Hva #Hval' #Hval #Hreg #Hinv #IH".
     iIntros "Hmap HPC Hh Ha Hregionl Heqws Hcls Hown Hsts".
     rewrite delete_insert_delete.
     destruct (reg_eq_dec PC dst).
     * subst dst. destruct r0.
       { case_eq (a + z)%a; intros.
         * case_eq (a0 + 1)%a; intros.
           { iApply (wp_lea_success_z_PC with "[HPC Ha]"); eauto; iFrame.
             iNext. iIntros "(HPC & Ha)".
             iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
               [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
             (* iDestruct (extract_from_region' _ _ a with *)
             (*                "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto. *)
             (* { iExists _. iFrame "∗ #". } *)
             iMod ("Hcls" with "[Heqws Hregionl Hh Ha $Hown]") as "Hcls'".
             { iNext.
               iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr)) with
                              "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto. 
               { iExists w. iFrame "∗ #". }
               iDestruct "Hregion" as "[$ _]". 
               iIntros (stsf' E'). rewrite -big_sepL_later. auto. 
             }
             iApply wp_pure_step_later; auto.
             iApply ("IH" with "[] [] [Hmap] [Hsts] [Hcls']"); auto. }
           { iApply (wp_lea_failPC1' with "[HPC Ha]"); eauto; iFrame.
             iNext. iIntros.  iApply wp_pure_step_later; auto.
             iNext. iApply wp_value; auto. iIntros; discriminate. }
         * iApply (wp_lea_failPC1 with "[HPC Ha]"); eauto; iFrame.
           iNext. iIntros. iApply wp_pure_step_later; auto.
           iNext. iApply wp_value; auto. iIntros; discriminate. }
       { destruct (H3 r0) as [wr0 Hsomer0].
         destruct (reg_eq_dec PC r0).
         - subst r0. iApply (wp_lea_fail6 with "[HPC Ha]"); eauto; iFrame.
           iNext. iIntros. iApply wp_pure_step_later; auto.
           iNext. iApply wp_value; auto. iIntros; discriminate.
         - iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
           repeat rewrite lookup_delete_ne; eauto.
           destruct wr0.
           + case_eq (a + z)%a; intros.
             * case_eq (a0 + 1)%a; intros.
               { iApply (wp_lea_success_reg_PC with "[HPC Ha Hr0]"); eauto; iFrame.
                 iNext. iIntros "(HPC & Ha & Hr0)".
                 iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                   [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                 rewrite -delete_insert_ne; auto.
                 iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                   [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                 iMod ("Hcls" with "[Heqws Hregionl Hh Ha $Hown]") as "Hcls'".
                 { iNext.
                   iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr)) with
                                  "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto. 
                   { iExists w. iFrame "∗ #". }
                   iDestruct "Hregion" as "[$ _]". 
                   iIntros (stsf' E'). rewrite -big_sepL_later. auto. 
                 }
                 iApply wp_pure_step_later; auto. rewrite (insert_id _ r0); auto.
                 iApply ("IH" with "[] [] [Hmap] [Hsts] [Hcls']"); auto. }
               { iApply (wp_lea_failPCreg1' with "[HPC Ha Hr0]"); eauto; iFrame.
                 iNext. iIntros.  iApply wp_pure_step_later; auto.
                 iNext. iApply wp_value; auto. iIntros; discriminate. }
             * iApply (wp_lea_failPCreg1 with "[HPC Ha Hr0]"); eauto; iFrame.
               iNext. iIntros. iApply wp_pure_step_later; auto.
               iNext. iApply wp_value; auto. iIntros; discriminate.
           + iApply (wp_lea_failPC5 with "[HPC Ha Hr0]"); eauto; iFrame.
             iNext. iIntros. iApply wp_pure_step_later; auto.
             iNext. iApply wp_value; auto. iIntros; discriminate. }
     * destruct (H3 dst) as [wdst Hsomedst].
       iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]"; eauto.
       rewrite lookup_delete_ne; eauto.
       destruct wdst.
       { iApply (wp_lea_fail2 with "[HPC Ha Hdst]"); eauto; iFrame.
         iNext. iIntros. iApply wp_pure_step_later; auto.
         iNext. iApply wp_value; auto. iIntros; discriminate. }
       { destruct c, p, p, p.
         destruct (perm_eq_dec p cap_lang.E).
         - subst p. destruct r0.
           + iApply (wp_lea_fail1 with "[HPC Ha Hdst]"); eauto; iFrame.
             iNext. iIntros. iApply wp_pure_step_later; auto.
             iNext. iApply wp_value; auto. iIntros; discriminate.
           + iApply (wp_lea_fail3 with "[HPC Ha Hdst]"); eauto; iFrame.
             iNext. iIntros. iApply wp_pure_step_later; auto.
             iNext. iApply wp_value; auto. iIntros; discriminate.
         - destruct r0.
           + case_eq (a0 + z)%a; intros.
             * case_eq (a + 1)%a; intros.
               { iApply (wp_lea_success_z with "[HPC Ha Hdst]"); eauto; iFrame.
                 iNext. iIntros "(HPC & Ha & Hdst)".
                 iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                   [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                 repeat rewrite -delete_insert_ne; auto.
                 iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                   [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                 iMod ("Hcls" with "[Heqws Hregionl Hh Ha $Hown]") as "Hcls'".
                 { iNext.
                   iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr)) with
                                  "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto. 
                   { iExists _. rewrite H5; iFrame "∗ #". }
                   iDestruct "Hregion" as "[$ _]". 
                   iIntros (stsf' E'). rewrite -big_sepL_later. auto. 
                 }
                 iApply wp_pure_step_later; auto.
                 iAssert ((interp_registers _ _ (<[dst:=inr (p, l, a2, a1, a3)]> r)))%I
                   as "[Hfull' Hreg']".
                 { iSplitL.
                   - iIntros (r2). destruct (reg_eq_dec dst r2); [subst r2; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto].
                   - iIntros (r2 Hnepc). destruct (reg_eq_dec dst r2).
                     + subst r2. rewrite /RegLocate lookup_insert.
                       iDestruct ("Hreg" $! dst Hnepc) as "HA". rewrite Hsomedst.
                       simpl. iApply (interp_cap_preserved with "HA"); auto.
                     + rewrite /RegLocate lookup_insert_ne; auto.
                       iApply "Hreg"; auto. }
                 iApply ("IH" with "[Hfull'] [Hreg'] [Hmap] [Hsts] [Hcls']"); auto. }
               { iApply (wp_lea_fail1' with "[HPC Ha Hdst]"); eauto; iFrame.
                 iNext. iIntros. iApply wp_pure_step_later; auto.
                 iNext. iApply wp_value; auto. iIntros; discriminate. }
             * iApply (wp_lea_fail1 with "[HPC Ha Hdst]"); eauto; iFrame.
               iNext. iIntros. iApply wp_pure_step_later; auto.
               iNext. iApply wp_value; auto. iIntros; discriminate.
           + destruct (H3 r0) as [wr0 Hsomer0].
             destruct (reg_eq_dec PC r0).
             * subst r0. iApply (wp_lea_fail6 with "[HPC Ha]"); eauto; iFrame.
               iNext. iIntros. iApply wp_pure_step_later; auto.
               iNext. iApply wp_value; auto. iIntros; discriminate.
             * destruct (reg_eq_dec dst r0).
               { subst r0. iApply (wp_lea_fail7 with "[HPC Ha Hdst]"); eauto; iFrame.
                 iNext. iIntros. iApply wp_pure_step_later; auto.
                 iNext. iApply wp_value; auto. iIntros; discriminate. }
               { iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
                 repeat rewrite lookup_delete_ne; eauto.
                 destruct wr0.
                 - case_eq (a0 + z)%a; intros.
                   * case_eq (a + 1)%a; intros.
                     { revert H4; intro H4.
                       iApply (wp_lea_success_reg with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
                       iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
                       iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                         [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                       repeat rewrite -delete_insert_ne; auto.
                       iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                         [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                       repeat rewrite -delete_insert_ne; auto.
                       iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                         [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                       iMod ("Hcls" with "[Heqws Hregionl Hh Ha $Hown]") as "Hcls'".
                       { iNext.
                         iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr)) with
                                        "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto. 
                         { iExists _. rewrite H5; iFrame "∗ #". }
                         iDestruct "Hregion" as "[$ _]". 
                         iIntros (stsf' E'). rewrite -big_sepL_later. auto. 
                       }
                       iApply wp_pure_step_later; auto.
                       iAssert ((interp_registers _ _ (<[dst:=inr (p, l, a2, a1, a3)]> (<[r0:=inl z]> r))))%I
                         as "[Hfull' Hreg']".
                       { iSplitL.
                         - iIntros (r2). destruct (reg_eq_dec dst r2); [subst r2; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto].
                           destruct (reg_eq_dec r0 r2); [subst r2; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto].
                         - iIntros (r2 Hnepc). destruct (reg_eq_dec dst r2).
                           + subst r2. rewrite /RegLocate lookup_insert.
                             iDestruct ("Hreg" $! dst Hnepc) as "HA". rewrite Hsomedst.
                             simpl. iApply (interp_cap_preserved with "HA"); auto.
                           + rewrite /RegLocate lookup_insert_ne; auto.
                             destruct (reg_eq_dec r0 r2).
                             * subst r2; rewrite lookup_insert. simpl.
                               repeat rewrite fixpoint_interp1_eq. simpl. eauto.
                             * rewrite lookup_insert_ne; auto.
                               iApply "Hreg"; auto. }
                       iApply ("IH" with "[Hfull'] [Hreg'] [Hmap] [Hsts] [Hcls']"); auto. }
                     { iApply (wp_lea_fail4' with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
                       iNext. iIntros. iApply wp_pure_step_later; auto.
                       iNext. iApply wp_value; auto. iIntros; discriminate. }
                   * iApply (wp_lea_fail4 with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
                     iNext. iIntros. iApply wp_pure_step_later; auto.
                     iNext. iApply wp_value; auto. iIntros; discriminate.
                 - iApply (wp_lea_fail5 with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
                   iNext. iIntros. iApply wp_pure_step_later; auto.
                   iNext. iApply wp_value; auto. iIntros; discriminate. } }
   Qed.
   
  Lemma fundamental_RX stsf E r b e g (a : Addr) ws :
    (na_inv logrel_nais (logN .@ (b,e)) (read_only_cond b e ws interp) →
     ⟦ inr ((RX,g),b,e,a) ⟧ₑ stsf E r)%I
  with fundamental_RWX stsf E r b e g (a : Addr) :
    (na_inv logrel_nais (logN .@ (b,e)) (read_write_cond b e interp) →
     ⟦ inr ((RWX,g),b,e,a) ⟧ₑ stsf E r)%I
  with fundamental_RWLX stsf E r b e g (a : Addr) :
    (na_inv logrel_nais (logN .@ (b,e)) (read_write_local_cond b e interp) →
     ⟦ inr ((RWLX,g),b,e,a) ⟧ₑ stsf E r)%I. 
  Proof.
  { clear fundamental_RX.
    destruct stsf as [fs fr].
    iIntros "#Hinv /=". iExists fs,fr.
    repeat (iSplit;auto). 
    iIntros "[[Hfull Hreg] [Hmreg [Hsts [Hown #Hreach]]]]".
    iExists _,_,_,_,_; iSplit; eauto; simpl.
    iRevert "Hinv Hreach". iLöb as "IH" forall (r a g fs fr b e ws).
    iIntros "#Hinv %". rename a0 into Hreach. 
    iDestruct "Hfull" as "%". iDestruct "Hreg" as "#Hreg". 
    iApply (wp_bind (fill [SeqCtx])).
    destruct (decide (isCorrectPC (inr ((RX,g),b,e,a)))). 
    - (* Correct PC *)
      assert ((b <= a)%a ∧ (a <= e)%a) as Hbae.
      { eapply in_range_is_correctPC; eauto.
        unfold le_addr; omega. }
      iAssert (⌜↑logN.@(b, e) ⊆ E⌝)%I as %Hbe.
      { iPureIntro. by apply Hreach. }
      (* iMod ("Hinv" $! ⊤ E _ Hbe with "Hown") as "[[Hregion Hown] Hcls]".  *)
      iMod (na_inv_open _ _ _ (logN.@(b, e)) with "Hinv Hown") as "(Hregion & Hown & Hcls)"; auto. 
      (* iDestruct (extract_from_region _ _ a with "Hregion") *)
      (*   as (al w ah) "(Hal & Hah & Hregionl & Hvalidl & >Ha & #Hva & Hregionh & Hvalidh)"; *)
      (*   auto. *)
(* ======= *)
      (*       iInv (logN.@(b, e)) as "Hregion" "Hcls".       *)
      rewrite /read_only_cond.
      iDestruct "Hregion" as "[Hbe #Hval]".
      iDestruct ("Hval" $! (fs,fr) E) as "Hval'".
      iCombine "Hbe Hval'" as "Hregion". 
      iDestruct (extract_from_region' _ _ a with "Hregion") as (w) "(Heqws & Hregionl & _ & >Ha & #Hva & Hh)"; auto.
      iDestruct ((big_sepM_delete _ _ PC) with "Hmreg") as "[HPC Hmap]"; 
        first apply (lookup_insert _ _ (inr (RX, g, b, e, a))).
      destruct (cap_lang.decode w) eqn:Hi. (* proof by cases on each instruction *)
      + (* Jmp *)
        iApply (RX_Jmp_case with "[] [] [] [] [] [] [Hmap] [HPC] [Hh] [Ha] [Hregionl] [Heqws] [Hcls] [Hown] [Hsts]"); eauto.
      + (* Jnz *)
        iApply (RX_Jnz_case with "[] [] [] [] [] [] [Hmap] [HPC] [Hh] [Ha] [Hregionl] [Heqws] [Hcls] [Hown] [Hsts]"); eauto.
      + (* Mov *)
        iApply (RX_Mov_case with "[] [] [] [] [] [] [Hmap] [HPC] [Hh] [Ha] [Hregionl] [Heqws] [Hcls] [Hown] [Hsts]"); eauto.
      + (* Load *)
        iApply (RX_Load_case with "[] [] [] [] [] [] [Hmap] [HPC] [Hh] [Ha] [Hregionl] [Heqws] [Hcls] [Hown] [Hsts]"); eauto.
      + (* Store *)
        iApply (RX_Store_case with "[] [] [] [] [] [] [Hmap] [HPC] [Hh] [Ha] [Hregionl] [Heqws] [Hcls] [Hown] [Hsts]"); eauto.
      + (* Lt *)
        iApply (RX_Add_Sub_Lt_case with "[] [] [] [] [] [] [Hmap] [HPC] [Hh] [Ha] [Hregionl] [Heqws] [Hcls] [Hown] [Hsts]"); eauto.
      + (* Add *)
        iApply (RX_Add_Sub_Lt_case with "[] [] [] [] [] [] [Hmap] [HPC] [Hh] [Ha] [Hregionl] [Heqws] [Hcls] [Hown] [Hsts]"); eauto.
      + (* Sub *)
        iApply (RX_Add_Sub_Lt_case with "[] [] [] [] [] [] [Hmap] [HPC] [Hh] [Ha] [Hregionl] [Heqws] [Hcls] [Hown] [Hsts]"); eauto.
      + (* Lea *)
        iApply (RX_Lea_case with "[] [] [] [] [] [] [Hmap] [HPC] [Hh] [Ha] [Hregionl] [Heqws] [Hcls] [Hown] [Hsts]"); eauto.
      + (* Restrict *)
        iRevert "Hmap HPC Hh Ha Hregionl Heqws Hcls Hown Hsts".
        iRevert "Hva Hval' Hval Hreg Hinv IH".

        
        
        (* rewrite delete_insert_delete.
        destruct (reg_eq_dec PC dst).
        * subst dst. destruct r0.
          { case_eq (PermPairFlowsTo (decodePermPair z) (RX, g)); intros.
            * case_eq (a + 1)%a; intros.
              { iApply (wp_restrict_success_z_PC with "[HPC Ha]"); eauto; iFrame.
                iNext. iIntros "(HPC & Ha)".
                iMod ("Hcls" with "[Hown Heqws Hregionl Hh Ha]") as "Hcls'".
                { iFrame. iNext.  
                  iDestruct (extract_from_region' _ _ a _
                                                  (((fixpoint interp1) E) (fs, fr)) with
                                 "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto. 
                  { iExists _. rewrite H5; iFrame "∗ #". }
                  iDestruct "Hregion" as "[Hregion _]". iFrame. 
                  iIntros (stsf E0). iApply big_sepL_later. iNext. auto. 
                }
                iApply wp_pure_step_later; auto.
                case_eq (decodePermPair z); intros. rewrite H6 in H4.
                destruct (andb_true_eq _ _ ltac:(symmetry in H4; exact H4)).
                simpl in H7. destruct p; simpl in H7; try congruence.
                - iNext. iApply (wp_bind (fill [SeqCtx])).
                  iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                  iNext. iIntros "HPC /=".
                  iApply wp_pure_step_later; auto.
                  iApply wp_value.
                  iNext. iIntros. discriminate.
                - iNext. iApply (wp_bind (fill [SeqCtx])).
                  iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                  iNext. iIntros "HPC /=".
                  iApply wp_pure_step_later; auto.
                  iApply wp_value.
                  iNext. iIntros. discriminate.
                - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                  iApply ("IH" with "[] [] [Hmap] [Hsts] [Hcls']"); auto.
                - iNext. iApply (wp_bind (fill [SeqCtx])).
                  iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
                  iNext. iIntros "HPC /=".
                  iApply wp_pure_step_later; auto.
                  iApply wp_value.
                  iNext. iIntros. discriminate. }
              { iApply (wp_restrict_failPC1' with "[HPC Ha]"); eauto; iFrame.
                iNext. iIntros. iApply wp_pure_step_later; auto.
                iNext. iApply wp_value; auto. iIntros; discriminate. }
            * iApply (wp_restrict_failPC1 with "[HPC Ha]"); eauto; iFrame.
              iNext. iIntros. iApply wp_pure_step_later; auto.
              iNext. iApply wp_value; auto. iIntros; discriminate. }
          { destruct (H3 r0) as [wr0 Hsomer0].
            destruct (reg_eq_dec PC r0).
            - subst r0. iApply (wp_restrict_fail6 with "[HPC Ha]"); eauto; iFrame.
              iNext. iIntros. iApply wp_pure_step_later; auto.
              iNext. iApply wp_value; auto. iIntros; discriminate.
            - iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
              repeat rewrite lookup_delete_ne; eauto.
              destruct wr0.
              + case_eq (PermPairFlowsTo (decodePermPair z) (RX, g)); intros.
                * case_eq (a + 1)%a; intros.
                  { iApply (wp_restrict_success_reg_PC with "[HPC Ha Hr0]"); eauto; iFrame.
                    iNext. iIntros "(HPC & Ha & Hr0)".
                    iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    rewrite -delete_insert_ne; auto.
                    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    iMod ("Hcls" with "[Hown Heqws Hregionl Hh Ha]") as "Hcls'".
                    { iFrame. iNext.  
                      iDestruct (extract_from_region' _ _ a _
                                                      (((fixpoint interp1) E) (fs, fr)) with
                                     "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto. 
                      { iExists _. rewrite H5; iFrame "∗ #". }
                      iDestruct "Hregion" as "[Hregion _]". iFrame. 
                      iIntros (stsf E0). iApply big_sepL_later. iNext. auto. 
                    }
                    iApply wp_pure_step_later; auto. rewrite (insert_id _ r0); auto.
                    case_eq (decodePermPair z); intros.
                    destruct p; admit.
                    (* case analysis on the kind of permission, fail if not RX/RWX/RWLX *)
                    (* iApply ("IH" with "[] [] [Hmap] [Hsts] [Hcls']"); auto.*) }
                  { iApply (wp_restrict_failPCreg1' with "[HPC Ha Hr0]"); eauto; iFrame.
                    iNext. iIntros.  iApply wp_pure_step_later; auto.
                    iNext. iApply wp_value; auto. iIntros; discriminate. }
                * iApply (wp_restrict_failPCreg1 with "[HPC Ha Hr0]"); eauto; iFrame.
                  iNext. iIntros. iApply wp_pure_step_later; auto.
                  iNext. iApply wp_value; auto. iIntros; discriminate.
              + iApply (wp_restrict_failPC5 with "[HPC Ha Hr0]"); eauto; iFrame.
                iNext. iIntros. iApply wp_pure_step_later; auto.
                iNext. iApply wp_value; auto. iIntros; discriminate. }
        * destruct (H3 dst) as [wdst Hsomedst].
          iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]"; eauto.
          rewrite lookup_delete_ne; eauto.
          destruct wdst.
          { iApply (wp_restrict_fail2 with "[HPC Ha Hdst]"); eauto; iFrame.
            iNext. iIntros. iApply wp_pure_step_later; auto.
            iNext. iApply wp_value; auto. iIntros; discriminate. }
          { destruct c, p, p, p.
            - destruct r0.
              + case_eq (PermPairFlowsTo (decodePermPair z) (p, l)); intros.
                * case_eq (a + 1)%a; intros.
                  { iApply (wp_restrict_success_z with "[HPC Ha Hdst]"); eauto; iFrame.
                    iNext. iIntros "(HPC & Ha & Hdst)".
                    iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    repeat rewrite -delete_insert_ne; auto.
                    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    iMod ("Hcls" with "[Hown Heqws Hregionl Hh Ha]") as "Hcls'".
                    { iFrame. iNext.  
                      iDestruct (extract_from_region' _ _ a _
                                                      (((fixpoint interp1) E) (fs, fr)) with
                                     "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto. 
                      { iExists _. rewrite H5; iFrame "∗ #". }
                      iDestruct "Hregion" as "[Hregion _]". iFrame. 
                      iIntros (stsf E0). iApply big_sepL_later. iNext. auto. 
                    }
                    iApply wp_pure_step_later; auto.
                    iAssert ((interp_registers _ _ (<[dst:=inr (decodePermPair z, a2, a1, a0)]> r)))%I
                      as "[Hfull' Hreg']".
                    { iSplitL.
                      - iIntros (r2). destruct (reg_eq_dec dst r2); [subst r2; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto].
                      - iIntros (r2 Hnepc). destruct (reg_eq_dec dst r2).
                        + subst r2. rewrite /RegLocate lookup_insert.
                          iDestruct ("Hreg" $! dst Hnepc) as "HA". rewrite Hsomedst.
                          simpl. rewrite (fixpoint_interp1_eq _ _ (inr (decodePermPair z, a2, a1, a0))) /=.
                          admit. (* need to do a case analysis *)
                        + rewrite /RegLocate lookup_insert_ne; auto.
                          iApply "Hreg"; auto. }
                    iApply ("IH" with "[Hfull'] [Hreg'] [Hmap] [Hsts] [Hcls']"); auto. }
                  { iApply (wp_restrict_fail1' with "[HPC Ha Hdst]"); eauto; iFrame.
                    iNext. iIntros. iApply wp_pure_step_later; auto.
                    iNext. iApply wp_value; auto. iIntros; discriminate. }
                * iApply (wp_restrict_fail1 with "[HPC Ha Hdst]"); eauto; iFrame.
                  iNext. iIntros. iApply wp_pure_step_later; auto.
                  iNext. iApply wp_value; auto. iIntros; discriminate.
              + destruct (H3 r0) as [wr0 Hsomer0].
                destruct (reg_eq_dec PC r0).
                * subst r0. iApply (wp_restrict_fail6 with "[HPC Ha]"); eauto; iFrame.
                  iNext. iIntros. iApply wp_pure_step_later; auto.
                  iNext. iApply wp_value; auto. iIntros; discriminate.
                * destruct (reg_eq_dec dst r0).
                  { subst r0. iApply (wp_restrict_fail7 with "[HPC Ha Hdst]"); eauto; iFrame.
                    iNext. iIntros. iApply wp_pure_step_later; auto.
                    iNext. iApply wp_value; auto. iIntros; discriminate. }
                  { iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
                    repeat rewrite lookup_delete_ne; eauto.
                    destruct wr0.
                    - case_eq (PermPairFlowsTo (decodePermPair z) (p, l)); intros.
                      * case_eq (a + 1)%a; intros.
                        { revert H4; intro H4.
                          iApply (wp_restrict_success_reg with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
                          iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
                          iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                          repeat rewrite -delete_insert_ne; auto.
                          iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                          repeat rewrite -delete_insert_ne; auto.
                          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                         iMod ("Hcls" with "[Hown Heqws Hregionl Hh Ha]") as "Hcls'".
                         { iFrame. iNext.  
                           iDestruct (extract_from_region' _ _ a _
                              (((fixpoint interp1) E) (fs, fr)) with
                                 "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto. 
                           { iExists _. rewrite H5; iFrame "∗ #". }
                           iDestruct "Hregion" as "[Hregion _]". iFrame. 
                           iIntros (stsf E0). iApply big_sepL_later. iNext. auto. 
                         }
                          iApply wp_pure_step_later; auto.
                          iAssert ((interp_registers _ _ (<[dst:=inr (decodePermPair z, a2, a1, a0)]> (<[r0:=inl z]> r))))%I
                            as "[Hfull' Hreg']".
                          { iSplitL.
                            - iIntros (r2). destruct (reg_eq_dec dst r2); [subst r2; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto].
                              destruct (reg_eq_dec r0 r2); [subst r2; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto].
                            - iIntros (r2 Hnepc). destruct (reg_eq_dec dst r2).
                              + subst r2. rewrite /RegLocate lookup_insert.
                                iDestruct ("Hreg" $! dst Hnepc) as "HA". rewrite Hsomedst.
                                simpl. admit. (* case analysis again *)
                              + rewrite /RegLocate lookup_insert_ne; auto.
                                destruct (reg_eq_dec r0 r2).
                                * subst r2; rewrite lookup_insert. simpl.
                                  repeat rewrite fixpoint_interp1_eq. simpl. eauto.
                                * rewrite lookup_insert_ne; auto.
                                  iApply "Hreg"; auto. }
                          iApply ("IH" with "[Hfull'] [Hreg'] [Hmap] [Hsts] [Hcls']"); auto. }
                        { iApply (wp_restrict_fail4' with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
                          iNext. iIntros. iApply wp_pure_step_later; auto.
                          iNext. iApply wp_value; auto. iIntros; discriminate. }
                      * iApply (wp_restrict_fail4 with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
                        iNext. iIntros. iApply wp_pure_step_later; auto.
                        iNext. iApply wp_value; auto. iIntros; discriminate.
                    - iApply (wp_restrict_fail5 with "[HPC Ha Hdst Hr0]"); eauto; iFrame.
                      iNext. iIntros. iApply wp_pure_step_later; auto.
                      iNext. iApply wp_value; auto. iIntros; discriminate. } } *)
      + (* Subseg *)
        rewrite delete_insert_delete.
        destruct (reg_eq_dec PC dst).
        * subst dst. destruct r1.
          { case_eq (z_to_addr z); intros.
            - destruct r2.
              + case_eq (z_to_addr z0); intros.
                * case_eq (isWithin a0 a1 b e); intros.
                  { case_eq (a+1)%a; intros.
                    - (* success case *) admit.
                    - (* fail, can't increase PC *) admit. }
                  { iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi i H4 H5 H6 with "[HPC Ha]"); iFrame; try (iSplitR; auto).
                    iNext. iIntros. iApply wp_pure_step_later; auto.
                    iNext. iApply wp_value; auto. iIntros; discriminate. }
                * iApply (wp_subseg_fail_convert2 _ _ _ _ _ _ _ _ _ _ _ Hi i H5 with "[HPC Ha]"); iFrame; auto.
                  iNext. iIntros. iApply wp_pure_step_later; auto.
                  iNext. iApply wp_value; auto. iIntros; discriminate.
              + destruct (reg_eq_dec PC r0).
                * subst r0.
                  iApply (wp_subseg_fail_pc2 _ _ _ _ _ _ _ _ _ Hi i with "[HPC Ha]"); iFrame.
                  iNext. iIntros. iApply wp_pure_step_later; auto.
                  iNext. iApply wp_value; auto. iIntros; discriminate.
                * destruct (H3 r0) as [wr0 Hsomer0].
                  iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]"; eauto; [rewrite (lookup_delete_ne _ PC r0); eauto|].
                  destruct wr0.
                  { case_eq (z_to_addr z0); intros.
                    - case_eq (isWithin a0 a1 b e); intros.
                      + case_eq (a+1)%a; intros.
                        * (* success case *) admit.
                        * (* fail, can't increase PC *) admit.
                      + iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi i H4 H5 H6 with "[HPC Ha Hr0]"); iFrame; try (iSplitR; auto).
                        iNext. iIntros. iApply wp_pure_step_later; auto.
                        iNext. iApply wp_value; auto. iIntros; discriminate.
                    - iApply (wp_subseg_fail_convert2 _ _ _ _ _ _ _ _ _ _ _ Hi i H5 with "[HPC Ha Hr0]"); iFrame; auto.
                      iNext. iIntros. iApply wp_pure_step_later; auto.
                      iNext. iApply wp_value; auto. iIntros; discriminate. }
                  { iApply (wp_subseg_fail_reg2_cap _ _ _ _ _ _ _ _ _ _ _ Hi i with "[HPC Ha Hr0]"); iFrame; auto.
                    iNext. iIntros. iApply wp_pure_step_later; auto.
                    iNext. iApply wp_value; auto. iIntros; discriminate. }
            - iApply (wp_subseg_fail_convert1 _ _ _ _ _ _ _ _ _ _ _ Hi i H4 with "[HPC Ha]"); iFrame; auto.
              iNext. iIntros. iApply wp_pure_step_later; auto.
              iNext. iApply wp_value; auto. iIntros; discriminate. }
          { destruct (reg_eq_dec PC r0).
            - subst r0. iApply (wp_subseg_fail_pc1 _ _ _ _ _ _ _ _ _ Hi i with "[HPC Ha]"); iFrame.
              iNext. iIntros. iApply wp_pure_step_later; auto.
              iNext. iApply wp_value; auto. iIntros; discriminate.
            - destruct (H3 r0) as [wr0 Hsomer0].
              iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]"; eauto; [rewrite (lookup_delete_ne _ PC r0); eauto|].
              destruct wr0.
              + case_eq (z_to_addr z); intros.
                * destruct r2.
                  { case_eq (z_to_addr z0); intros.
                    - case_eq (isWithin a0 a1 b e); intros.
                      + case_eq (a+1)%a; intros.
                        * (* success case *) admit.
                        * (* fail, can't increase PC *) admit.
                      + iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi i H4 H5 H6 with "[HPC Ha Hr0]"); iFrame; try (iSplitR; auto).
                        iNext. iIntros. iApply wp_pure_step_later; auto.
                        iNext. iApply wp_value; auto. iIntros; discriminate.
                    - iApply (wp_subseg_fail_convert2 _ _ _ _ _ _ _ _ _ _ _ Hi i H5 with "[HPC Ha Hr0]"); iFrame; auto.
                      iNext. iIntros. iApply wp_pure_step_later; auto.
                      iNext. iApply wp_value; auto. iIntros; discriminate. }
                  { destruct (reg_eq_dec PC r1).
                    - subst r1. iApply (wp_subseg_fail_pc2 _ _ _ _ _ _ _ _ _ Hi i with "[HPC Ha]"); iFrame.
                      iNext. iIntros. iApply wp_pure_step_later; auto.
                      iNext. iApply wp_value; auto. iIntros; discriminate.
                    - destruct (reg_eq_dec r0 r1).
                      + subst r1. case_eq (isWithin a0 a0 b e); intros.
                        * case_eq (a+1)%a; intros.
                          { (* success case *) admit. }
                          { (* fail, can't increment PC *) admit. }
                        * iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi i H4 H4 H5 with "[HPC Ha Hr0]"); iFrame; try (iSplitR; auto). destruct (reg_eq_dec r0 r0); try congruence. auto.
                          iNext. iIntros. iApply wp_pure_step_later; auto.
                          iNext. iApply wp_value; auto. iIntros; discriminate.
                      + destruct (H3 r1) as [wr1 Hsomer1].
                        iDestruct ((big_sepM_delete _ _ r1) with "Hmap") as "[Hr1 Hmap]"; eauto; [repeat rewrite lookup_delete_ne; eauto|].
                        destruct wr1.
                        * case_eq (z_to_addr z0); intros.
                          { case_eq (isWithin a0 a1 b e); intros.
                            - case_eq (a+1)%a; intros.
                              + (* success case *) admit.
                              + (* fail, can't increment PC *) admit.
                            - iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi i H4 H5 H6 with "[HPC Ha Hr0 Hr1]"); iFrame; try (iSplitL; auto). destruct (reg_eq_dec r0 r1); try congruence; auto.
                              iNext. iIntros. iApply wp_pure_step_later; auto.
                              iNext. iApply wp_value; auto. iIntros; discriminate. }
                          { iApply (wp_subseg_fail_convert2 _ _ _ _ _ _ _ _ _ _ _ Hi i H5 with "[HPC Ha Hr1]"); iFrame; auto.
                            iNext. iIntros. iApply wp_pure_step_later; auto.
                            iNext. iApply wp_value; auto. iIntros; discriminate. }
                        * iApply (wp_subseg_fail_reg2_cap _ _ _ _ _ _ _ _ _ _ _ Hi i with "[HPC Ha Hr1]"); iFrame; auto.
                          iNext. iIntros. iApply wp_pure_step_later; auto.
                          iNext. iApply wp_value; auto. iIntros; discriminate. }
                * iApply (wp_subseg_fail_convert1 _ _ _ _ _ _ _ _ _ _ _ Hi i H4 with "[HPC Ha Hr0]"); iFrame; auto.
                  iNext. iIntros. iApply wp_pure_step_later; auto.
                  iNext. iApply wp_value; auto. iIntros; discriminate.
              + iApply (wp_subseg_fail_reg1_cap _ _ _ _ _ _ _ _ _ _ _ Hi i with "[HPC Ha Hr0]"); iFrame; auto.
                iNext. iIntros. iApply wp_pure_step_later; auto.
                iNext. iApply wp_value; auto. iIntros; discriminate. }
        * destruct (H3 dst) as [wdst Hsomedst].
          iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]"; eauto; [rewrite (lookup_delete_ne _ PC dst); eauto|].
          destruct wdst.
          { iApply (wp_subseg_fail_dst_z _ _ _ _ _ _ _ _ _ _ _ Hi i with "[HPC Ha Hdst]"); iFrame.
            iNext. iIntros. iApply wp_pure_step_later; auto.
            iNext. iApply wp_value; auto. iIntros; discriminate. }
          { destruct c,p,p,p. destruct r1.
            - case_eq (z_to_addr z); intros.
              + destruct r2.
                * case_eq (z_to_addr z0); intros.
                  { case_eq (isWithin a3 a4 a2 a1); intros.
                    - case_eq (a+1)%a; intros.
                      + (* success case *) admit.
                      + (* fail case, can't increment PC *) admit.
                    - iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi i H4 H5 H6 with "[HPC Ha Hdst]"); iFrame; try (repeat iSplitR; auto). destruct (reg_eq_dec PC dst); try congruence; auto.
                      iNext. iIntros. iApply wp_pure_step_later; auto.
                      iNext. iApply wp_value; auto. iIntros; discriminate. }
                  { iApply (wp_subseg_fail_convert2 _ _ _ _ _ _ _ _ _ _ _ Hi i H5 with "[HPC Ha]"); iFrame; auto.
                    iNext. iIntros. iApply wp_pure_step_later; auto.
                    iNext. iApply wp_value; auto. iIntros; discriminate. }
                * destruct (reg_eq_dec PC r0).
                  { subst r0. iApply (wp_subseg_fail_pc2 _ _ _ _ _ _ _ _ _ Hi i with "[HPC Ha]"); iFrame.
                    iNext. iIntros. iApply wp_pure_step_later; auto.
                    iNext. iApply wp_value; auto. iIntros; discriminate. }
                  { destruct (reg_eq_dec dst r0).
                    - subst r0. iApply (wp_subseg_fail_reg2_cap _ _ _ _ _ _ _ _ _ _ _ Hi i with "[HPC Ha Hdst]"); iFrame; auto.
                      iNext. iIntros. iApply wp_pure_step_later; auto.
                      iNext. iApply wp_value; auto. iIntros; discriminate.
                    - destruct (H3 r0) as [wr0 Hsomer0].
                      iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]"; eauto; [repeat rewrite lookup_delete_ne; eauto|].
                      destruct wr0.
                      + case_eq (z_to_addr z0); intros.
                        * case_eq (isWithin a3 a4 a2 a1); intros.
                          { case_eq (a+1)%a; intros.
                            - (* success case *) admit.
                            - (* fail case, can't increment PC *) admit. }
                          { iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi i H4 H5 H6 with "[HPC Ha Hr0 Hdst]"); iFrame; try (repeat iSplitR; auto). destruct (reg_eq_dec PC dst); try congruence; auto.
                            iNext. iIntros. iApply wp_pure_step_later; auto.
                            iNext. iApply wp_value; auto. iIntros; discriminate. }
                        * iApply (wp_subseg_fail_convert2 _ _ _ _ _ _ _ _ _ _ _ Hi i H5 with "[HPC Ha Hr0]"); iFrame; auto.
                          iNext. iIntros. iApply wp_pure_step_later; auto.
                          iNext. iApply wp_value; auto. iIntros; discriminate.
                      + iApply (wp_subseg_fail_reg2_cap _ _ _ _ _ _ _ _ _ _ _ Hi i with "[HPC Ha Hr0]"); iFrame; auto.
                        iNext. iIntros. iApply wp_pure_step_later; auto.
                        iNext. iApply wp_value; auto. iIntros; discriminate. }
              + (* fail case, can't convert z *) admit.
            - destruct (reg_eq_dec PC r0).
              + subst r0. iApply (wp_subseg_fail_pc1 _ _ _ _ _ _ _ _ _ Hi i with "[HPC Ha]"); iFrame.
                iNext. iIntros. iApply wp_pure_step_later; auto.
                iNext. iApply wp_value; auto. iIntros; discriminate.
              + destruct (reg_eq_dec dst r0).
                * subst r0. iApply (wp_subseg_fail_reg1_cap _ _ _ _ _ _ _ _ _ _ _ Hi i with "[HPC Ha Hdst]"); iFrame; auto.
                  iNext. iIntros. iApply wp_pure_step_later; auto.
                  iNext. iApply wp_value; auto. iIntros; discriminate.
                * destruct (H3 r0) as [wr0 Hsomer0].
                  iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]"; eauto; [repeat rewrite lookup_delete_ne; eauto|].
                  destruct wr0.
                  { case_eq (z_to_addr z); intros.
                    - destruct r2.
                      + case_eq (z_to_addr z0); intros.
                        * case_eq (isWithin a3 a4 a2 a1); intros.
                          { case_eq (a+1)%a; intros.
                            - (* success case *) admit.
                            - (* fail case, can't increment PC *) admit. }
                          { iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi i H4 H5 H6 with "[HPC Ha Hr0 Hdst]"); iFrame; try (repeat iSplitR; auto). destruct (reg_eq_dec PC dst); try congruence; auto.
                            iNext. iIntros. iApply wp_pure_step_later; auto.
                            iNext. iApply wp_value; auto. iIntros; discriminate. }
                        * iApply (wp_subseg_fail_convert2 _ _ _ _ _ _ _ _ _ _ _ Hi i H5 with "[HPC Ha Hr0]"); iFrame; auto.
                          iNext. iIntros. iApply wp_pure_step_later; auto.
                          iNext. iApply wp_value; auto. iIntros; discriminate.
                      + destruct (reg_eq_dec PC r1).
                        * subst r1. iApply (wp_subseg_fail_pc2 _ _ _ _ _ _ _ _ _ Hi i with "[HPC Ha]"); iFrame.
                          iNext. iIntros. iApply wp_pure_step_later; auto.
                          iNext. iApply wp_value; auto. iIntros; discriminate.
                        * destruct (reg_eq_dec dst r1).
                          { subst r1. iApply (wp_subseg_fail_reg2_cap _ _ _ _ _ _ _ _ _ _ _ Hi i with "[HPC Ha Hdst]"); iFrame; auto.
                            iNext. iIntros. iApply wp_pure_step_later; auto.
                            iNext. iApply wp_value; auto. iIntros; discriminate. }
                          { destruct (reg_eq_dec r0 r1).
                            - subst r1. case_eq (isWithin a3 a3 a2 a1); intros.
                              + case_eq (a+1)%a; intros.
                                * (* success case *) admit.
                                * (* fail case, can't increment PC *) admit.
                              + iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi i H4 H4 H5 with "[HPC Ha Hr0 Hdst]"); iFrame; try (repeat iSplitR; auto). destruct (reg_eq_dec r0 r0); try congruence; auto.
                                destruct (reg_eq_dec PC dst); try congruence; auto.
                                iNext. iIntros. iApply wp_pure_step_later; auto.
                                iNext. iApply wp_value; auto. iIntros; discriminate.
                            - destruct (H3 r1) as [wr1 Hsomer1].
                              iDestruct ((big_sepM_delete _ _ r1) with "Hmap") as "[Hr1 Hmap]"; eauto; [repeat rewrite lookup_delete_ne; eauto|].
                              destruct wr1.
                              + case_eq (z_to_addr z0); intros.
                                * case_eq (isWithin a3 a4 a2 a1); intros.
                                  { case_eq (a+1)%a; intros.
                                    - (* success case *) admit.
                                    - (* fail case, can't increment PC *) admit. }
                                  { iApply (wp_subseg_fail_notwithin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi i H4 H5 H6 with "[HPC Ha Hr0 Hr1 Hdst]"); iFrame. iSplitL "Hr1". destruct (reg_eq_dec r0 r1); try congruence; auto.
                                    destruct (reg_eq_dec PC dst); try congruence; auto.
                                    iNext. iIntros. iApply wp_pure_step_later; auto.
                                    iNext. iApply wp_value; auto. iIntros; discriminate. }
                                * iApply (wp_subseg_fail_convert2 _ _ _ _ _ _ _ _ _ _ _ Hi i H5 with "[HPC Ha Hr0 Hr1]"); iFrame; auto.
                                  iNext. iIntros. iApply wp_pure_step_later; auto.
                                  iNext. iApply wp_value; auto. iIntros; discriminate.
                              + iApply (wp_subseg_fail_reg2_cap _ _ _ _ _ _ _ _ _ _ _ Hi i with "[HPC Ha Hr1]"); iFrame; auto.
                                iNext. iIntros. iApply wp_pure_step_later; auto.
                                iNext. iApply wp_value; auto. iIntros; discriminate. }
                    - iApply (wp_subseg_fail_convert1 _ _ _ _ _ _ _ _ _ _ _ Hi i H4 with "[HPC Ha Hr0]"); iFrame; auto.
                      iNext. iIntros. iApply wp_pure_step_later; auto.
                      iNext. iApply wp_value; auto. iIntros; discriminate. }
                  { iApply (wp_subseg_fail_reg1_cap _ _ _ _ _ _ _ _ _ _ _ Hi i with "[HPC Ha Hr0]"); iFrame; auto.
                    iNext. iIntros. iApply wp_pure_step_later; auto.
                    iNext. iApply wp_value; auto. iIntros; discriminate. } }
      + (* IsPtr *) admit.
        (* rewrite delete_insert_delete.
        destruct (reg_eq_dec PC dst).
        * subst dst.
          specialize H3 with r0 as Hr0. 
          destruct Hr0 as [wr0 Hsomesr0]. 
          iAssert ((if reg_eq_dec PC r0 then ▷ PC ↦ᵣ inr (RX, g, b, e, a) else ▷ PC ↦ᵣ inr (RX, g, b, e, a) ∗ ▷ r0 ↦ᵣ wr0) ∗ (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y))%I with "[HPC Hmap]" as "[H Hmap]".
          { destruct (reg_eq_dec PC r0); iFrame.
            iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]"; eauto.
            rewrite (lookup_delete_ne _ PC r0); eauto. iFrame. }
          iApply (wp_IsPtr_fail_PC with "[Ha H]"); eauto; iFrame.
          iNext. iIntros "(H & Ha)".
          iApply wp_pure_step_later; auto.
          iAssert ([∗ map] k↦y ∈ <[PC:=inl (if reg_eq_dec PC r0 then 1%Z else match wr0 with inl _ => 0%Z | _ => 1%Z end)]> (if reg_eq_dec PC r0 then r else (<[r0:=wr0]> r)), k ↦ᵣ y)%I with "[H Hmap]" as "Hmap".
          { destruct (reg_eq_dec PC r0).
            - iDestruct ((big_sepM_delete _ _ PC) with "[H Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. iFrame.
            - iDestruct "H" as "[H1 H2]".
              iDestruct ((big_sepM_delete _ _ r0) with "[H2 Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
              rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_delete _ _ PC) with "[H1 Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. iFrame. }
          iApply wp_value.
          iNext. iIntros (Hcontr). inversion Hcontr. 
        * case_eq (a + 1)%a; intros.
          { destruct (reg_eq_dec PC r0).
            - subst r0.
              specialize H3 with dst as Hdst. 
              destruct Hdst as [wdst Hsomesdst]. 
              iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]"; eauto.
              rewrite (lookup_delete_ne _ PC dst); eauto.
              iApply (wp_IsPtr_successPC with "[HPC Ha Hdst]"); eauto; iFrame.
              iNext. iIntros "(HPC & Ha & Hdst)".
              iApply wp_pure_step_later; auto.
              (* reconstruct regions *)
              (* iDestruct (extract_from_region _ _ a with *)
              (*                "[Heqws Hregionl Hvalidl Hh Ha]") as "[Hbe Hregion]"; eauto. *)
              (* { iExists w. iFrame. rewrite H4. iFrame. iExact "Hva". } *)
              iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
              rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
              iAssert (interp_registers _ _ (<[dst:=inl 1%Z]> r))
                        as "[% Hreg']".
              { iSplitL.
                { iIntros (r0). iPureIntro.
                  destruct (decide (dst = r0)); simplify_eq;
                    [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto. }
                iIntros (r0). iDestruct ("Hreg" $! (r0)) as "Hv".
                destruct H3 with r0 as [c Hsome].
                iIntros (Hnepc) "/=".
                rewrite /RegLocate.
                rewrite Hsome. destruct (decide (dst = r0)); simplify_eq.
                * rewrite lookup_insert.
                  repeat rewrite fixpoint_interp1_eq. simpl; eauto.
                * rewrite lookup_insert_ne. rewrite Hsome. iApply "Hv"; auto.
                  auto. }
              (* reestablish invariant *)
              iNext. iMod ("Hcls" with "[Heqws Hregionl Hh Ha $Hown]") as "Hown".
              { iNext.
                iDestruct (extract_from_region' _ _ a _
                              (((fixpoint interp1) E) (fs, fr)) with 
                             "[Heqws Hregionl Hh Ha]") as "[Hbe Hregion]"; eauto.
                { iExists w. iFrame. rewrite H4. iFrame "∗ #". }
                iFrame. iIntros (stsf E0). iApply big_sepL_later. iNext. auto. }
              (* apply IH *)
              iApply ("IH" $! _ _ _ _ _ _ _ ws with "[] Hreg' Hmap Hsts Hown");
                iFrame "#"; [iPureIntro;eauto|iAlways;iPureIntro;eauto].
            - specialize H3 with dst as Hdst. 
              destruct Hdst as [wdst Hsomesdst].
              specialize H3 with r0 as Hr0. 
              destruct Hr0 as [wr0 Hsomer0]. 
              iAssert ((if reg_eq_dec r0 dst then ▷ r0 ↦ᵣ wr0 else ▷ r0 ↦ᵣ wr0 ∗ ▷ dst ↦ᵣ wdst) ∗ (if reg_eq_dec r0 dst then [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y else [∗ map] k↦y ∈ delete dst (delete r0 (delete PC r)), k ↦ᵣ y))%I with "[Hmap]" as "[Hr0dst Hmap]".
              { destruct (reg_eq_dec r0 dst).
                - subst dst. iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]"; eauto.
                  rewrite (lookup_delete_ne _ PC r0); eauto. iFrame.
                - iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]"; eauto.
                  rewrite (lookup_delete_ne _ PC r0); eauto.
                  iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]"; eauto.
                  rewrite (lookup_delete_ne _ r0 dst); eauto.
                  rewrite (lookup_delete_ne _ PC dst); eauto. iFrame. }
              iApply (wp_IsPtr_success with "[HPC Ha Hr0dst]"); eauto; iFrame.
              iNext. iIntros "(HPC & Ha & Hr0dst)".
              iApply wp_pure_step_later; auto.
              (* reconstruct regions *)
              (* iDestruct (extract_from_region _ _ a with *)
              (*                "[Heqws Hregionl Hvalidl Hh Ha]") as "[Hbe Hregion]"; eauto. *)
              (* { iExists w. iFrame. rewrite H4. iFrame. iExact "Hva". } *)
              iAssert ([∗ map] k↦y ∈ <[PC:=inr (RX, g, b, e, a0)]> (if reg_eq_dec r0 dst then <[r0:=inl match wr0 with | inl _ => 0%Z | inr _ => 1%Z end]> r else (<[r0:=wr0]> (<[dst:=inl match wr0 with | inl _ => 0%Z | inr _ => 1%Z end]> r))), k ↦ᵣ y)%I with "[Hr0dst HPC Hmap]" as "Hmap".
              { destruct (reg_eq_dec r0 dst).
                - iDestruct ((big_sepM_delete _ _ r0) with "[Hr0dst Hmap]") as "Hmap /=";
                    [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                  rewrite -delete_insert_ne; auto.
                  iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                    [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                  auto.
                - iDestruct "Hr0dst" as "[Hr0 Hdst]".
                  iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                    [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                  rewrite -delete_insert_ne; auto.
                  iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                    [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                  rewrite -delete_insert_ne; auto. rewrite -delete_insert_ne; auto.
                  iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                    [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                  auto. }
              iAssert (interp_registers _ _ (if reg_eq_dec r0 dst
                            then <[r0:=inl match wr0 with
                                           | inl _ => 0%Z
                                           | inr _ => 1%Z
                                           end]> r
                            else <[r0:=wr0]> (<[dst:=inl match wr0 with
                                                         | inl _ => 0%Z
                                                         | inr _ => 1%Z
                                                         end]> r)))
                        as "[% Hreg']".
              { iSplit.
                - iPureIntro.
                  destruct (reg_eq_dec r0 dst); simpl.
                  + subst r0. intros r1. destruct (reg_eq_dec dst r1).
                    * subst r1. rewrite lookup_insert; eauto.
                    * rewrite lookup_insert_ne; auto; rewrite Hsome; eauto.
                  + intros r1. destruct (reg_eq_dec r0 r1).
                    * subst r1. rewrite lookup_insert; eauto.
                    * rewrite lookup_insert_ne; auto.
                      destruct (reg_eq_dec r1 dst); [subst; rewrite lookup_insert; eauto| rewrite lookup_insert_ne; auto; rewrite Hsome; eauto].
                - iIntros (r1).
                  specialize H3 with r1 as Hr1. 
                  destruct Hr1 as [c Hsome].
                  iIntros (Hnepc) "/=".
                  iSpecialize ("Hreg" $! r1 Hnepc).  
                  rewrite /RegLocate Hsome.
                  destruct (reg_eq_dec r0 dst).
                  + destruct (reg_eq_dec r0 r1).
                    * subst r1. rewrite lookup_insert.
                      repeat rewrite fixpoint_interp1_eq. simpl. eauto.
                    * rewrite lookup_insert_ne; eauto. rewrite Hsome. iApply "Hreg"; auto.
                  + destruct (reg_eq_dec r0 r1).
                    * subst r1. rewrite lookup_insert.
                      rewrite Hsome in Hsomer0; inv Hsomer0.
                      iApply "Hreg"; auto.
                    * rewrite lookup_insert_ne; eauto.
                      destruct (reg_eq_dec r1 dst).
                      ** subst r1. rewrite lookup_insert.
                         repeat rewrite fixpoint_interp1_eq; simpl; eauto.
                      ** rewrite lookup_insert_ne; auto. rewrite Hsome. iApply "Hreg"; auto. }

              (* reestablish invariant *)
              iNext. iMod ("Hcls" with "[Heqws Hregionl Hh Ha $Hown]") as "Hown".
              { iNext.
                iDestruct (extract_from_region' _ _ a _
                              (((fixpoint interp1) E) (fs, fr)) with 
                             "[Heqws Hregionl Hh Ha]") as "[Hbe Hregion]"; eauto.
                { iExists w. iFrame. rewrite H4. iFrame "∗ #". }
                iFrame. iIntros (stsf E0). iApply big_sepL_later. iNext. auto. }
              (* apply IH *)
              iApply ("IH" $! _ _ _ _ _ _ _ ws with "[] Hreg' Hmap Hsts Hown");
                iFrame "#"; [iPureIntro;eauto|iAlways;iPureIntro;eauto].
          } 
          { specialize H3 with dst as Hdst. 
            destruct Hdst as [wdst Hsomesdst].
            specialize H3 with r0 as Hr0. 
            destruct Hr0 as [wr0 Hsomer0]. 
            iAssert ((if reg_eq_dec r0 dst then ▷ r0 ↦ᵣ wr0 else if reg_eq_dec r0 PC then ▷ dst ↦ᵣ wdst else ▷ r0 ↦ᵣ wr0 ∗ ▷ dst ↦ᵣ wdst) ∗ (if reg_eq_dec r0 dst then [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y else if reg_eq_dec r0 PC then [∗ map] k↦y ∈ delete dst (delete PC r), k ↦ᵣ y else [∗ map] k↦y ∈ delete dst (delete r0 (delete PC r)), k ↦ᵣ y))%I with "[Hmap]" as "[H Hmap]".
          { destruct (reg_eq_dec r0 dst).
            - subst r0. iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hr0 Hmap]"; eauto.
              rewrite (lookup_delete_ne _ PC dst); eauto. iFrame.
            - destruct (reg_eq_dec r0 PC).
              + subst r0. iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hr0 Hmap]"; eauto.
                rewrite (lookup_delete_ne _ PC dst); eauto. iFrame.
              + iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]"; eauto.
                rewrite (lookup_delete_ne _ PC r0); eauto. iFrame.
                iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]"; eauto.
                rewrite (lookup_delete_ne _ r0 dst); eauto. rewrite (lookup_delete_ne _ PC dst); eauto. iFrame. }
          iApply (wp_IsPtr_fail with "[Ha HPC H]"); eauto; iFrame.
          iNext. iIntros "(HPC & Ha & H)".
          iApply wp_pure_step_later; auto.
          iAssert ([∗ map] k↦y ∈ (<[PC:=inr (RX, g, b, e, a)]> (if reg_eq_dec r0 dst then <[r0:=inl match wr0 with inl _ => 0%Z | inr _ => 1%Z end]> r else (if reg_eq_dec r0 PC then <[dst:=inl 1%Z]> r else <[r0:= wr0]> (<[dst:=inl match wr0 with inl _ => 0%Z | inr _ => 1%Z end]> r)))), k ↦ᵣ y)%I with "[H HPC Hmap]" as "Hmap".
          { destruct (reg_eq_dec r0 dst).
            - subst dst. iDestruct ((big_sepM_delete _ _ r0) with "[H Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. 
              rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto.
            - destruct (reg_eq_dec r0 PC).
              + subst r0. iDestruct ((big_sepM_delete _ _ dst) with "[H Hmap]") as "Hmap /=";
                            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto.
              + iDestruct "H" as "[H1 H2]".
                iDestruct ((big_sepM_delete _ _ dst) with "[H2 Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                repeat rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ r0) with "[H1 Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. 
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto. }
          iApply wp_value.
          iNext. iIntros (Hcontr); inversion Hcontr. 
          } *)
      + (* GetL *) admit.
        (* rewrite delete_insert_delete.
        specialize H3 with dst as Hdst. 
        destruct Hdst as [wdst Hsomesdst].
        specialize H3 with r0 as Hr0. 
        destruct Hr0 as [wr0 Hsomer0]. 
        iAssert ((if reg_eq_dec PC r0 then emp else r0 ↦ᵣ wr0) ∗ (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y))%I with "[Hmap]" as "[Hr0 Hmap]".
        { destruct (reg_eq_dec PC r0); iFrame.
          iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
          rewrite (lookup_delete_ne _ PC r0); eauto. iFrame. }
        iAssert ((if reg_eq_dec PC dst then emp else if reg_eq_dec r0 dst then emp else dst ↦ᵣ wdst) ∗ (if reg_eq_dec PC dst then (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y) else if reg_eq_dec r0 dst then (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y) else (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete dst (delete PC r), k ↦ᵣ y else [∗ map] k↦y ∈ delete dst (delete r0 (delete PC r)), k ↦ᵣ y)))%I with "[Hmap]" as "[Hdst Hmap]".
        { destruct (reg_eq_dec PC dst); iFrame.
          destruct (reg_eq_dec r0 dst); iFrame.
          destruct (reg_eq_dec PC r0).
          - iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]".
            rewrite (lookup_delete_ne _ PC dst); eauto. iFrame.
          - iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]".
            rewrite (lookup_delete_ne _ r0 dst); eauto.
            rewrite (lookup_delete_ne _ PC dst); eauto. iFrame. }
        destruct (reg_eq_dec PC dst).
        { subst dst. iApply (wp_GetL_failPC with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
          iNext. iIntros "(HPC & Ha & Hr0)".
          (* iDestruct (extract_from_region _ _ a with *)
          (*                "[Heqws Hregionl Hvalidl Hh Ha]") as "Hregion"; eauto. *)
          (* { iExists w. iFrame. iExact "Hva". } *)
          iAssert ([∗ map] k↦y ∈ <[PC:=(if reg_eq_dec PC r0 then inl (encodeLoc g) else match wr0 with | inl _ => inr (RX, g, b, e, a) | inr (_, g', _, _, _) => inl (encodeLoc g') end)]> (if reg_eq_dec PC r0 then r else <[r0:= wr0]> r), k ↦ᵣ y)%I with "[Hr0 HPC Hmap]" as "Hmap".
          { destruct (reg_eq_dec PC r0).
            - iDestruct ((big_sepM_delete _ _ ) with "[HPC Hmap]") as "Hmap /=".
              eapply lookup_insert.
              erewrite (delete_insert_delete r PC _). iFrame. simpl. auto.
            - iDestruct ((big_sepM_delete _ _ ) with "[Hr0 Hmap]") as "Hmap /=";
                [eapply lookup_insert|erewrite (delete_insert_delete (delete PC r) r0 _);iFrame|]. simpl.
              rewrite -delete_insert_ne; auto.
              iDestruct ((big_sepM_delete _ _ ) with "[HPC Hmap]") as "Hmap /=";
                [eapply lookup_insert|erewrite (delete_insert_delete (<[r0:=wr0]> r) PC _);iFrame|]. simpl. auto. }
          iAssert (interp_registers _ _ (if reg_eq_dec PC r0 then r else <[r0:=wr0]> r)) as "Hreg'".
          { iSplit.
            - iIntros (r1).
              iPureIntro. destruct (reg_eq_dec PC r0); auto.
              destruct (reg_eq_dec r0 r1); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
            - iIntros (r1 Hnepc).
              iDestruct ("Hreg" $! r1 Hnepc) as "#Hv".
              specialize H3 with r1 as [wr1 Hr1]. 
              destruct (reg_eq_dec PC r0); eauto.
              destruct (reg_eq_dec r0 r1).
              + subst r1. rewrite /RegLocate lookup_insert Hsomer0.
                iApply "Hv"; auto.
              + rewrite /RegLocate lookup_insert_ne; auto. }
          iApply wp_pure_step_later; auto. iApply wp_value.
          iNext. iIntros (Hcontr); inversion Hcontr. 
        } 
        { case_eq (a + 1)%a; intros.
          - iApply (wp_GetL_success with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
            (* iDestruct (extract_from_region _ _ a with *)
            (*                "[Heqws Hregionl Hvalidl Hh Ha]") as "[Hbe Hregion]"; eauto. *)
            (* { iExists w. iFrame. rewrite H4. iFrame. iExact "Hva". } *)
            destruct (reg_eq_dec PC r0).
            + subst r0. destruct (reg_eq_dec PC dst); try congruence.
              iApply wp_pure_step_later; auto.
              iAssert ([∗ map] k↦y ∈ <[PC:=inr (RX, g, b, e, a0)]> (<[dst:=inl (encodeLoc g)]> r), k ↦ᵣ y)%I with "[Hdst HPC Hmap]" as "Hmap".
              { iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. 
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto. }
              simpl.
              iAssert (interp_registers _ _ (<[dst:=inl (encodeLoc g)]> r)) as "[% Hreg']".
              { iSplit.
                - iIntros (r1).
                  iPureIntro. destruct (reg_eq_dec r1 dst); simpl.
                  + subst r1. rewrite lookup_insert; eauto.
                  + rewrite lookup_insert_ne; auto.
                - iIntros (r1 Hnepc) "/=".
                  iDestruct ("Hreg" $! r1 Hnepc) as "#Hv".
                  specialize H3 with r1 as [wr1 Hr1]. 
                  rewrite /RegLocate.
                  destruct (reg_eq_dec r1 dst); simpl.
                  + subst r1. rewrite lookup_insert; eauto.
                    repeat rewrite fixpoint_interp1_eq. simpl. eauto.
                  + rewrite lookup_insert_ne; auto. }
              (* reestablish invariant *)
              iNext. iMod ("Hcls" with "[Heqws Hregionl Hh Ha $Hown]") as "Hown".
              { iNext.
                iDestruct (extract_from_region' _ _ a _
                              (((fixpoint interp1) E) (fs, fr)) with 
                             "[Heqws Hregionl Hh Ha]") as "[Hbe Hregion]"; eauto.
                { iExists w. iFrame. rewrite H4. iFrame "∗ #". }
                iFrame. iIntros (stsf E0). iApply big_sepL_later. iNext. auto. }
              (* apply IH *)
              iApply ("IH" $! _ _ _ _ _ _ _ ws with "[] Hreg' Hmap Hsts Hown");
                iFrame "#"; [iPureIntro;eauto|iAlways;iPureIntro;eauto].
            + destruct wr0.
              * simpl. iApply wp_pure_step_later; auto.
                iNext. iApply wp_value. iIntros (Hcontr); inversion Hcontr. 
              * destruct c, p, p, p. iApply wp_pure_step_later; auto.
                iAssert ([∗ map] k↦y ∈ <[PC:=inr (RX, g, b, e, a0)]> (if reg_eq_dec r0 dst then <[dst:=inl (encodeLoc l)]> r else <[r0:=inr (p, l, a3, a2, a1)]> (<[dst:=inl (encodeLoc l)]> r)), k ↦ᵣ y)%I with "[Hr0 Hdst HPC Hmap]" as "Hmap".
                { destruct (reg_eq_dec r0 dst).
                  - subst r0. iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    rewrite -delete_insert_ne; auto.
                    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto.
                  - iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    rewrite -delete_insert_ne; auto.
                    iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    do 2 (rewrite -delete_insert_ne; auto).
                    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto. }
                iAssert (interp_registers _ _ (if reg_eq_dec r0 dst then <[dst:=inl _]> r else <[r0:=inr (p, l, a3, a2, a1)]> (<[dst:=inl _]> r))) as "[% Hreg']".
                { iSplit.
                  - iIntros (r1).
                    iPureIntro. destruct (reg_eq_dec r0 dst).
                    + subst r0. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
                    + destruct (reg_eq_dec r1 r0); eapply (proj2 (lookup_insert_is_Some _ r0 r1 (inr _))); eauto.
                      right; split; auto. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
                  - iIntros (r1 Hnepc) "/=".
                  iDestruct ("Hreg" $! r1 Hnepc) as "#Hv".
                  specialize H3 with r1 as [w0 Hsome]. 
                  rewrite /RegLocate.
                  rewrite Hsome. destruct (reg_eq_dec r0 dst).
                    + subst r0. destruct (reg_eq_dec dst r1).
                      * subst r1. rewrite lookup_insert !fixpoint_interp1_eq /=; eauto.
                      * rewrite lookup_insert_ne; eauto. rewrite Hsome; eauto.
                    + destruct (reg_eq_dec r0 r1).
                      * subst r1. rewrite lookup_insert /=.
                        rewrite Hsome in Hsomer0; inv Hsomer0.
                        iApply "Hv"; auto.
                      * rewrite lookup_insert_ne; auto. destruct (reg_eq_dec dst r1).
                        { subst r1; rewrite lookup_insert !fixpoint_interp1_eq /=; eauto. }
                        { rewrite lookup_insert_ne; auto. rewrite Hsome.
                          iApply "Hv"; auto. } }
                (* reestablish invariant *)
                iNext. iMod ("Hcls" with "[Heqws Hregionl Hh Ha $Hown]") as "Hown".
              { iNext.
                iDestruct (extract_from_region' _ _ a _
                              (((fixpoint interp1) E) (fs, fr)) with 
                             "[Heqws Hregionl Hh Ha]") as "[Hbe Hregion]"; eauto.
                { iExists w. iFrame. rewrite H4. iFrame "∗ #". }
                iFrame. iIntros (stsf E0). iApply big_sepL_later. iNext. auto. }
                (* apply IH *)
                iApply ("IH" $! _ _ _ _ _ _ _ ws with "[] Hreg' Hmap Hsts Hown");
                  iFrame "#"; [iPureIntro;eauto|iAlways;iPureIntro;eauto].
          - iApply (wp_GetL_fail with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
            (* iDestruct (extract_from_region _ _ a with *)
            (*                "[Heqws Hregionl Hvalidl Hh Ha]") as "[Hbe Hregion]"; eauto. *)
            (* { iExists w. iFrame. rewrite H4. iFrame. iExact "Hva". } *)
            iApply wp_pure_step_later; auto.
            iApply wp_value. iNext. iIntros (Hcontr); inversion Hcontr.
        } *)
      + (* GetP *) admit.
        (* rewrite delete_insert_delete.
        specialize H3 with dst as Hdst. 
        destruct Hdst as [wdst Hsomesdst].
        specialize H3 with r0 as Hr0. 
        destruct Hr0 as [wr0 Hsomer0]. 
        iAssert ((if reg_eq_dec PC r0 then emp else r0 ↦ᵣ wr0) ∗ (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y))%I with "[Hmap]" as "[Hr0 Hmap]".
        { destruct (reg_eq_dec PC r0); iFrame.
          iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
          rewrite (lookup_delete_ne _ PC r0); eauto. iFrame. }
        iAssert ((if reg_eq_dec PC dst then emp else if reg_eq_dec r0 dst then emp else dst ↦ᵣ wdst) ∗ (if reg_eq_dec PC dst then (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y) else if reg_eq_dec r0 dst then (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y) else (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete dst (delete PC r), k ↦ᵣ y else [∗ map] k↦y ∈ delete dst (delete r0 (delete PC r)), k ↦ᵣ y)))%I with "[Hmap]" as "[Hdst Hmap]".
        { destruct (reg_eq_dec PC dst); iFrame.
          destruct (reg_eq_dec r0 dst); iFrame.
          destruct (reg_eq_dec PC r0).
          - iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]".
            rewrite (lookup_delete_ne _ PC dst); eauto. iFrame.
          - iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]".
            rewrite (lookup_delete_ne _ r0 dst); eauto.
            rewrite (lookup_delete_ne _ PC dst); eauto. iFrame. }
        destruct (reg_eq_dec PC dst).
        { subst dst. iApply (wp_GetP_failPC with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
          iNext. iIntros "(HPC & Ha & Hr0) /=".
          iApply wp_pure_step_later; auto. iApply wp_value.
          iNext. iIntros (Hcontr); inversion Hcontr.
        } 
        { case_eq (a + 1)%a; intros.
          - iApply (wp_GetP_success with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
            destruct (reg_eq_dec PC r0).
            + subst r0. destruct (reg_eq_dec PC dst); try congruence.
              iApply wp_pure_step_later; auto.
              iAssert ([∗ map] k↦y ∈ <[PC:=inr (RX, g, b, e, a0)]> (<[dst:=inl (encodePerm RX)]> r), k ↦ᵣ y)%I with "[Hdst HPC Hmap]" as "Hmap".
              { iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. 
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto. }
              simpl. iAssert (interp_registers _ _ (<[dst:=inl (encodePerm RX)]> r)) as "[% Hreg']".
              { iSplit.
                - iIntros (r1).
                  iPureIntro. destruct (reg_eq_dec r1 dst); simpl.
                  + subst r1. rewrite lookup_insert; eauto.
                  + rewrite lookup_insert_ne; auto. 
                - iIntros (r1 Hnepc) "/=".
                  iDestruct ("Hreg" $! r1 Hnepc) as "#Hv". 
                  rewrite /RegLocate.
                  destruct (reg_eq_dec r1 dst); simpl.
                  + subst r1. rewrite lookup_insert; eauto.
                    repeat rewrite fixpoint_interp1_eq. simpl. eauto.
                  + rewrite lookup_insert_ne; auto.
              }
              (* reestablish invariant *)
                iNext. iMod ("Hcls" with "[Heqws Hregionl Hh Ha $Hown]") as "Hown".
              { iNext.
                iDestruct (extract_from_region' _ _ a _
                              (((fixpoint interp1) E) (fs, fr)) with 
                             "[Heqws Hregionl Hh Ha]") as "[Hbe Hregion]"; eauto.
                { iExists w. iFrame. rewrite H4. iFrame "∗ #". }
                iFrame. iIntros (stsf E0). iApply big_sepL_later. iNext. auto. }
                (* apply IH *)
                iApply ("IH" $! _ _ _ _ _ _ _ ws with "[] Hreg' Hmap Hsts Hown");
                  iFrame "#"; [iPureIntro;eauto|iAlways;iPureIntro;eauto].
            + destruct wr0.
              * simpl. iApply wp_pure_step_later; auto.
                iApply wp_value. iNext.
                iIntros (Hcontr); inversion Hcontr. 
              * destruct c, p, p, p. iApply wp_pure_step_later; auto.
                iAssert ([∗ map] k↦y ∈ <[PC:=inr (RX, g, b, e, a0)]> (if reg_eq_dec r0 dst then <[dst:=inl (encodePerm p)]> r else <[r0:=inr (p, l, a3, a2, a1)]> (<[dst:=inl (encodePerm p)]> r)), k ↦ᵣ y)%I with "[Hr0 Hdst HPC Hmap]" as "Hmap".
                { destruct (reg_eq_dec r0 dst).
                  - subst r0. iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    rewrite -delete_insert_ne; auto.
                    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto.
                  - iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    rewrite -delete_insert_ne; auto.
                    iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    do 2 (rewrite -delete_insert_ne; auto).
                    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto. }
                iAssert (interp_registers _ _ (if reg_eq_dec r0 dst then <[dst:=inl _]> r else <[r0:=inr (p, l, a3, a2, a1)]> (<[dst:=inl _]> r))) as "[% Hreg']".
                { iSplit.
                  - iIntros (r1). 
                    iPureIntro. destruct (reg_eq_dec r0 dst).
                    + subst r0. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
                    + destruct (reg_eq_dec r1 r0); eapply (proj2 (lookup_insert_is_Some _ r0 r1 (inr _))); eauto.
                      right; split; auto. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
                  - iIntros (r1 Hnepc) "/=".
                    iDestruct ("Hreg" $! r1 Hnepc) as "#Hv". 
                    rewrite /RegLocate.
                    destruct H3 with r1 as [w0 Hsome].
                    rewrite Hsome. destruct (reg_eq_dec r0 dst).
                    + subst r0. destruct (reg_eq_dec dst r1).
                      * subst r1. rewrite lookup_insert !fixpoint_interp1_eq /=; eauto.
                      * rewrite lookup_insert_ne; eauto. rewrite Hsome; eauto.
                    + destruct (reg_eq_dec r0 r1).
                      * subst r1. rewrite lookup_insert /=.
                        rewrite Hsome in Hsomer0; inv Hsomer0.
                        iApply "Hv"; auto.
                      * rewrite lookup_insert_ne; auto. destruct (reg_eq_dec dst r1).
                        { subst r1; rewrite lookup_insert !fixpoint_interp1_eq /=; eauto. }
                        { rewrite lookup_insert_ne; auto. rewrite Hsome.
                          iApply "Hv"; auto. } }
                (* reestablish invariant *)
                iNext. iMod ("Hcls" with "[Heqws Hregionl Hh Ha $Hown]") as "Hown".
              { iNext.
                iDestruct (extract_from_region' _ _ a _
                              (((fixpoint interp1) E) (fs, fr)) with 
                             "[Heqws Hregionl Hh Ha]") as "[Hbe Hregion]"; eauto.
                { iExists w. iFrame. rewrite H4. iFrame "∗ #". }
                iFrame. iIntros (stsf E0). iApply big_sepL_later. iNext. auto. }
                (* apply IH *)
                iApply ("IH" $! _ _ _ _ _ _ _ ws with "[] Hreg' Hmap Hsts Hown");
                  iFrame "#"; [iPureIntro;eauto|iAlways;iPureIntro;eauto].
          - iApply (wp_GetP_fail with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha & Hr0 & Hdst) /=".
            iApply wp_pure_step_later; auto. iApply wp_value.
            iNext. iIntros (Hcontr); inversion Hcontr.
        } *)
      + (* GetB *) admit.
        (* rewrite delete_insert_delete.
        specialize H3 with dst as Hdst. 
        destruct Hdst as [wdst Hsomesdst].
        specialize H3 with r0 as Hr0. 
        destruct Hr0 as [wr0 Hsomer0]. 
        iAssert ((if reg_eq_dec PC r0 then emp else r0 ↦ᵣ wr0) ∗ (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y))%I with "[Hmap]" as "[Hr0 Hmap]".
        { destruct (reg_eq_dec PC r0); iFrame.
          iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
          rewrite (lookup_delete_ne _ PC r0); eauto. iFrame. }
        iAssert ((if reg_eq_dec PC dst then emp else if reg_eq_dec r0 dst then emp else dst ↦ᵣ wdst) ∗ (if reg_eq_dec PC dst then (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y) else if reg_eq_dec r0 dst then (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y) else (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete dst (delete PC r), k ↦ᵣ y else [∗ map] k↦y ∈ delete dst (delete r0 (delete PC r)), k ↦ᵣ y)))%I with "[Hmap]" as "[Hdst Hmap]".
        { destruct (reg_eq_dec PC dst); iFrame.
          destruct (reg_eq_dec r0 dst); iFrame.
          destruct (reg_eq_dec PC r0).
          - iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]".
            rewrite (lookup_delete_ne _ PC dst); eauto. iFrame.
          - iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]".
            rewrite (lookup_delete_ne _ r0 dst); eauto.
            rewrite (lookup_delete_ne _ PC dst); eauto. iFrame. }
        destruct (reg_eq_dec PC dst).
        { subst dst. iApply (wp_GetB_failPC with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
          iNext. iIntros "(HPC & Ha & Hr0) /=".
          iApply wp_pure_step_later; auto. iApply wp_value.
          iNext. iIntros (Hcontr); inversion Hcontr.
        }
        { case_eq (a + 1)%a; intros.
          - iApply (wp_GetB_success with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
            destruct (reg_eq_dec PC r0).
            + subst r0. destruct (reg_eq_dec PC dst); try congruence.
              iApply wp_pure_step_later; auto.
              iAssert ([∗ map] k↦y ∈ <[PC:=inr (RX, g, b, e, a0)]> (<[dst:=inl (z_of b)]> r), k ↦ᵣ y)%I with "[Hdst HPC Hmap]" as "Hmap".
              { iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. 
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto. }
              simpl. iAssert (interp_registers _ _ (<[dst:=inl (z_of b)]> r)) as "[% Hreg']".
              { iSplit.
                - iIntros (r1).
                  iPureIntro. destruct (reg_eq_dec r1 dst); simpl.
                  + subst r1. rewrite lookup_insert; eauto.
                  + rewrite lookup_insert_ne; auto.
                - iIntros (r1 Hnepc) "/=".
                  iDestruct ("Hreg" $! r1 Hnepc) as "#Hv".
                  rewrite /RegLocate.
                  destruct (reg_eq_dec r1 dst); simpl.
                  + subst r1. rewrite lookup_insert; eauto.
                    repeat rewrite fixpoint_interp1_eq. simpl. eauto.
                  + rewrite lookup_insert_ne; auto. }
              (* reestablish invariant *)
              iNext. iMod ("Hcls" with "[Heqws Hregionl Hh Ha $Hown]") as "Hown".
              { iNext.
                iDestruct (extract_from_region' _ _ a _
                              (((fixpoint interp1) E) (fs, fr)) with 
                             "[Heqws Hregionl Hh Ha]") as "[Hbe Hregion]"; eauto.
                { iExists w. iFrame. rewrite H4. iFrame "∗ #". }
                iFrame. iIntros (stsf E0). iApply big_sepL_later. iNext. auto. }
              (* apply IH *)
              iApply ("IH" $! _ _ _ _ _ _ _ ws with "[] Hreg' Hmap Hsts Hown");
                iFrame "#"; [iPureIntro;eauto|iAlways;iPureIntro;eauto].
            + destruct wr0.
              * simpl. iApply wp_pure_step_later; auto.
                iApply wp_value. iNext. iIntros (Hcontr); inversion Hcontr. 
              * destruct c, p, p, p. iApply wp_pure_step_later; auto.
                iAssert ([∗ map] k↦y ∈ <[PC:=inr (RX, g, b, e, a0)]> (if reg_eq_dec r0 dst then <[dst:=inl (z_of a3)]> r else <[r0:=inr (p, l, a3, a2, a1)]> (<[dst:=inl (z_of a3)]> r)), k ↦ᵣ y)%I with "[Hr0 Hdst HPC Hmap]" as "Hmap".
                { destruct (reg_eq_dec r0 dst).
                  - subst r0. iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    rewrite -delete_insert_ne; auto.
                    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto.
                    destruct a3; auto.
                  - iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    rewrite -delete_insert_ne; auto.
                    iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    do 2 (rewrite -delete_insert_ne; auto).
                    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto.
                    destruct a3; auto.
                }
                iAssert (interp_registers _ _ (if reg_eq_dec r0 dst then <[dst:=inl _]> r else <[r0:=inr (p, l, a3, a2, a1)]> (<[dst:=inl _]> r))) as "[% Hreg']".
                { iSplit.
                  - iIntros (r1).
                    iPureIntro. destruct (reg_eq_dec r0 dst).
                    + subst r0. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
                    + destruct (reg_eq_dec r1 r0); eapply (proj2 (lookup_insert_is_Some _ r0 r1 (inr _))); eauto.
                      right; split; auto. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
                  - iIntros (r1 Hnepc) "/=".
                    iDestruct ("Hreg" $! r1 Hnepc) as "#Hv".
                    rewrite /RegLocate.
                    destruct H3 with r1 as [w0 Hsome].
                    rewrite Hsome. destruct (reg_eq_dec r0 dst).
                    + subst r0. destruct (reg_eq_dec dst r1).
                      * subst r1. rewrite lookup_insert !fixpoint_interp1_eq /=; eauto.
                      * rewrite lookup_insert_ne; eauto. rewrite Hsome; eauto.
                    + destruct (reg_eq_dec r0 r1).
                      * subst r1. rewrite lookup_insert /=.
                        rewrite Hsome in Hsomer0; inv Hsomer0.
                        iApply "Hv"; auto.
                      * rewrite lookup_insert_ne; auto. destruct (reg_eq_dec dst r1).
                        { subst r1; rewrite lookup_insert !fixpoint_interp1_eq /=; eauto. }
                        { rewrite lookup_insert_ne; auto. rewrite Hsome.
                          iApply "Hv"; auto. } }
                (* reestablish invariant *)
                iNext. iMod ("Hcls" with "[Heqws Hregionl Hh Ha $Hown]") as "Hown".
                { iNext.
                iDestruct (extract_from_region' _ _ a _
                              (((fixpoint interp1) E) (fs, fr)) with 
                             "[Heqws Hregionl Hh Ha]") as "[Hbe Hregion]"; eauto.
                { iExists w. iFrame. rewrite H4. iFrame "∗ #". }
                iFrame. iIntros (stsf E0). iApply big_sepL_later. iNext. auto. }
                (* apply IH *)
                iApply ("IH" $! _ _ _ _ _ _ _ ws with "[] Hreg' Hmap Hsts Hown");
                  iFrame "#"; [iPureIntro;eauto|iAlways;iPureIntro;eauto].
          - iApply (wp_GetB_fail with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha & Hr0 & Hdst) /=".
            iApply wp_pure_step_later;auto. iApply wp_value. 
            iNext. iIntros (Hcontr); inversion Hcontr.    
        } *) 
      + (* GetE *) admit.
        (* rewrite delete_insert_delete.
        specialize H3 with dst as Hdst. 
        destruct Hdst as [wdst Hsomesdst].
        specialize H3 with r0 as Hr0. 
        destruct Hr0 as [wr0 Hsomer0]. 
        iAssert ((if reg_eq_dec PC r0 then emp else r0 ↦ᵣ wr0) ∗ (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y))%I with "[Hmap]" as "[Hr0 Hmap]".
        { destruct (reg_eq_dec PC r0); iFrame.
          iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
          rewrite (lookup_delete_ne _ PC r0); eauto. iFrame. }
        iAssert ((if reg_eq_dec PC dst then emp else if reg_eq_dec r0 dst then emp else dst ↦ᵣ wdst) ∗ (if reg_eq_dec PC dst then (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y) else if reg_eq_dec r0 dst then (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y) else (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete dst (delete PC r), k ↦ᵣ y else [∗ map] k↦y ∈ delete dst (delete r0 (delete PC r)), k ↦ᵣ y)))%I with "[Hmap]" as "[Hdst Hmap]".
        { destruct (reg_eq_dec PC dst); iFrame.
          destruct (reg_eq_dec r0 dst); iFrame.
          destruct (reg_eq_dec PC r0).
          - iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]".
            rewrite (lookup_delete_ne _ PC dst); eauto. iFrame.
          - iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]".
            rewrite (lookup_delete_ne _ r0 dst); eauto.
            rewrite (lookup_delete_ne _ PC dst); eauto. iFrame. }
        destruct (reg_eq_dec PC dst).
        { subst dst. iApply (wp_GetE_failPC with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
          iNext. iIntros "(HPC & Ha & Hr0) /=".
          iApply wp_pure_step_later;auto. iApply wp_value.
          iNext. iIntros (Hcontr); inversion Hcontr. 
        }
        { case_eq (a + 1)%a; intros.
          - iApply (wp_GetE_success with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
            destruct (reg_eq_dec PC r0).
            + subst r0. destruct (reg_eq_dec PC dst); try congruence.
              iApply wp_pure_step_later; auto.
              iAssert ([∗ map] k↦y ∈ <[PC:=inr (RX, g, b, e, a0)]> (<[dst:=inl (z_of e)]> r), k ↦ᵣ y)%I with "[Hdst HPC Hmap]" as "Hmap".
              { iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. 
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto. }
              simpl. iAssert (interp_registers _ _ (<[dst:=inl (z_of e)]> r)) as "[% Hreg']".
              { iSplit.
                - iIntros (r1).
                  iPureIntro. destruct (reg_eq_dec r1 dst); simpl.
                  + subst r1. rewrite lookup_insert; eauto.
                  + rewrite lookup_insert_ne; auto.
                - iIntros (r1 Hnepc) "/=".
                  iDestruct ("Hreg" $! r1 Hnepc) as "#Hv".
                  rewrite /RegLocate.
                  destruct (reg_eq_dec r1 dst); simpl.
                  + subst r1. rewrite lookup_insert; eauto.
                    repeat rewrite fixpoint_interp1_eq. simpl. eauto.
                  + rewrite lookup_insert_ne; auto. }
              (* reestablish invariant *)
              iNext. iMod ("Hcls" with "[Heqws Hregionl Hh Ha $Hown]") as "Hown".
              { iNext.
                iDestruct (extract_from_region' _ _ a _
                              (((fixpoint interp1) E) (fs, fr)) with 
                             "[Heqws Hregionl Hh Ha]") as "[Hbe Hregion]"; eauto.
                { iExists w. iFrame. rewrite H4. iFrame "∗ #". }
                iFrame. iIntros (stsf E0). iApply big_sepL_later. iNext. auto. }
              (* apply IH *)
              iApply ("IH" $! _ _ _ _ _ _ _ ws with "[] Hreg' Hmap Hsts Hown");
                iFrame "#"; [iPureIntro;eauto|iAlways;iPureIntro;eauto].
            + destruct wr0.
              * simpl. iApply wp_pure_step_later; auto.
                iApply wp_value. iNext. iIntros (Hcontr); inversion Hcontr. 
              * destruct c, p, p, p. iApply wp_pure_step_later; auto.
                iAssert ([∗ map] k↦y ∈ <[PC:=inr (RX, g, b, e, a0)]> (if reg_eq_dec r0 dst then <[dst:=inl (z_of a2)]> r else <[r0:=inr (p, l, a3, a2, a1)]> (<[dst:=inl (z_of a2)]> r)), k ↦ᵣ y)%I with "[Hr0 Hdst HPC Hmap]" as "Hmap".
                { destruct (reg_eq_dec r0 dst).
                  - subst r0. iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    rewrite -delete_insert_ne; auto.
                    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto.
                  - iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    rewrite -delete_insert_ne; auto.
                    iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    do 2 (rewrite -delete_insert_ne; auto).
                    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto. }
                iAssert (interp_registers _ _ (if reg_eq_dec r0 dst then <[dst:=inl _]> r else <[r0:=inr (p, l, a3, a2, a1)]> (<[dst:=inl _]> r))) as "[% Hreg']".
                { iSplit.
                  - iIntros (r1).
                    iPureIntro. destruct (reg_eq_dec r0 dst).
                    + subst r0. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
                    + destruct (reg_eq_dec r1 r0); eapply (proj2 (lookup_insert_is_Some _ r0 r1 (inr _))); eauto.
                      right; split; auto. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
                  - iIntros (r1 Hnepc) "/=". 
                    iDestruct ("Hreg" $! r1 Hnepc) as "#Hv".
                    rewrite /RegLocate.
                    destruct H3 with r1 as [w0 Hsome]. rewrite Hsome. destruct (reg_eq_dec r0 dst).
                    + subst r0. destruct (reg_eq_dec dst r1).
                      * subst r1. rewrite lookup_insert !fixpoint_interp1_eq /=; eauto.
                      * rewrite lookup_insert_ne; eauto. rewrite Hsome; eauto.
                    + destruct (reg_eq_dec r0 r1).
                      * subst r1. rewrite lookup_insert /=.
                        rewrite Hsome in Hsomer0; inv Hsomer0.
                        iApply "Hv"; auto.
                      * rewrite lookup_insert_ne; auto. destruct (reg_eq_dec dst r1).
                        { subst r1; rewrite lookup_insert !fixpoint_interp1_eq /=; eauto. }
                        { rewrite lookup_insert_ne; auto. rewrite Hsome.
                          iApply "Hv"; auto. } }
               (* reestablish invariant *)
              iNext. iMod ("Hcls" with "[Heqws Hregionl Hh Ha $Hown]") as "Hown".
              { iNext.
                iDestruct (extract_from_region' _ _ a _
                              (((fixpoint interp1) E) (fs, fr)) with 
                             "[Heqws Hregionl Hh Ha]") as "[Hbe Hregion]"; eauto.
                { iExists w. iFrame. rewrite H4. iFrame "∗ #". }
                iFrame. iIntros (stsf E0). iApply big_sepL_later. iNext. auto. }
              (* apply IH *)
              iApply ("IH" $! _ _ _ _ _ _ _ ws with "[] Hreg' Hmap Hsts Hown");
                iFrame "#"; [iPureIntro;eauto|iAlways;iPureIntro;eauto].
          - iApply (wp_GetE_fail with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha & Hr0 & Hdst) /=".
            iApply wp_pure_step_later;auto. iApply wp_value.
            iNext. iIntros (Hcontr); inversion Hcontr. 
        } *)
      + (* GetA *) admit.
        (*rewrite delete_insert_delete.
         specialize H3 with dst as Hdst. 
        destruct Hdst as [wdst Hsomesdst].
        specialize H3 with r0 as Hr0. 
        destruct Hr0 as [wr0 Hsomer0]. 
        iAssert ((if reg_eq_dec PC r0 then emp else r0 ↦ᵣ wr0) ∗ (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y))%I with "[Hmap]" as "[Hr0 Hmap]".
        { destruct (reg_eq_dec PC r0); iFrame.
          iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]".
          rewrite (lookup_delete_ne _ PC r0); eauto. iFrame. }
        iAssert ((if reg_eq_dec PC dst then emp else if reg_eq_dec r0 dst then emp else dst ↦ᵣ wdst) ∗ (if reg_eq_dec PC dst then (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y) else if reg_eq_dec r0 dst then (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete PC r, k ↦ᵣ y else [∗ map] k↦y ∈ delete r0 (delete PC r), k ↦ᵣ y) else (if reg_eq_dec PC r0 then [∗ map] k↦y ∈ delete dst (delete PC r), k ↦ᵣ y else [∗ map] k↦y ∈ delete dst (delete r0 (delete PC r)), k ↦ᵣ y)))%I with "[Hmap]" as "[Hdst Hmap]".
        { destruct (reg_eq_dec PC dst); iFrame.
          destruct (reg_eq_dec r0 dst); iFrame.
          destruct (reg_eq_dec PC r0).
          - iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]".
            rewrite (lookup_delete_ne _ PC dst); eauto. iFrame.
          - iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]".
            rewrite (lookup_delete_ne _ r0 dst); eauto.
            rewrite (lookup_delete_ne _ PC dst); eauto. iFrame. }
        destruct (reg_eq_dec PC dst).
        { subst dst. iApply (wp_GetA_failPC with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
          iNext. iIntros "(HPC & Ha & Hr0)".
          iApply wp_pure_step_later; auto. iApply wp_value.
          iNext. iIntros (Hcontr); inversion Hcontr. 
        } 
        { case_eq (a + 1)%a; intros.
          - iApply (wp_GetA_success with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
            destruct (reg_eq_dec PC r0).
            + subst r0. destruct (reg_eq_dec PC dst); try congruence.
              iApply wp_pure_step_later; auto.
              iAssert ([∗ map] k↦y ∈ <[PC:=inr (RX, g, b, e, a0)]> (<[dst:=inl (z_of a)]> r), k ↦ᵣ y)%I with "[Hdst HPC Hmap]" as "Hmap".
              { iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. 
                rewrite -delete_insert_ne; auto.
                iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                  [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto. }
              simpl. iAssert (interp_registers _ _ (<[dst:=inl (z_of a)]> r)) as "[% Hreg']".
              { iSplit.
                - iIntros (r1).
                  iPureIntro. destruct (reg_eq_dec r1 dst); simpl.
                  + subst r1. rewrite lookup_insert; eauto.
                  + rewrite lookup_insert_ne; auto. 
                - iIntros (r1 Hnepc).
                  iDestruct ("Hreg" $! r1 Hnepc) as "Hv".
                  rewrite /RegLocate.
                  destruct (reg_eq_dec r1 dst); simpl.
                  + subst r1. rewrite lookup_insert; eauto.
                    repeat rewrite fixpoint_interp1_eq. simpl. eauto.
                  + rewrite lookup_insert_ne; auto. }
              (* reestablish invariant *)
              iNext. iMod ("Hcls" with "[Heqws Hregionl Hh Ha $Hown]") as "Hown".
              { iNext.
                iDestruct (extract_from_region' _ _ a _
                              (((fixpoint interp1) E) (fs, fr)) with 
                             "[Heqws Hregionl Hh Ha]") as "[Hbe Hregion]"; eauto.
                { iExists w. iFrame. rewrite H4. iFrame "∗ #". }
                iFrame. iIntros (stsf E0). iApply big_sepL_later. iNext. auto. }
              (* apply IH *)
              iApply ("IH" $! _ _ _ _ _ _ _ ws with "[] Hreg' Hmap Hsts Hown");
                iFrame "#"; [iPureIntro;eauto|iAlways;iPureIntro;eauto].
            + destruct wr0.
              * iApply wp_pure_step_later; auto. iApply wp_value.
                iNext. iIntros (Hcontr); inversion Hcontr. 
              * destruct c, p, p, p. iApply wp_pure_step_later; auto.
                iAssert ([∗ map] k↦y ∈ <[PC:=inr (RX, g, b, e, a0)]> (if reg_eq_dec r0 dst then <[dst:=inl (z_of a1)]> r else <[r0:=inr (p, l, a3, a2, a1)]> (<[dst:=inl (z_of a1)]> r)), k ↦ᵣ y)%I with "[Hr0 Hdst HPC Hmap]" as "Hmap".
                { destruct (reg_eq_dec r0 dst).
                  - subst r0. iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                                [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    rewrite -delete_insert_ne; auto.
                    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto.
                  - iDestruct ((big_sepM_delete _ _ dst) with "[Hdst Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    rewrite -delete_insert_ne; auto.
                    iDestruct ((big_sepM_delete _ _ r0) with "[Hr0 Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
                    do 2 (rewrite -delete_insert_ne; auto).
                    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
                      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl. auto. }
                iAssert (interp_registers _ _ (if reg_eq_dec r0 dst then <[dst:=inl _]> r else <[r0:=inr (p, l, a3, a2, a1)]> (<[dst:=inl _]> r))) as "[% Hreg']".
                { iSplit.
                  - iIntros (r1).
                    iPureIntro. destruct (reg_eq_dec r0 dst).
                    + subst r0. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
                    + destruct (reg_eq_dec r1 r0); eapply (proj2 (lookup_insert_is_Some _ r0 r1 (inr _))); eauto.
                      right; split; auto. destruct (reg_eq_dec r1 dst); eapply (proj2 (lookup_insert_is_Some r _ _ _)); eauto.
                  - iIntros (r1 Hnepc).
                    iDestruct ("Hreg" $! r1 Hnepc) as "Hv".
                    rewrite /RegLocate.
                    destruct H3 with r1 as [w0 Hsome].
                    rewrite Hsome. destruct (reg_eq_dec r0 dst).
                    + subst r0. destruct (reg_eq_dec dst r1).
                      * subst r1. rewrite lookup_insert !fixpoint_interp1_eq /=; eauto.
                      * rewrite lookup_insert_ne; eauto. rewrite Hsome; eauto.
                    + destruct (reg_eq_dec r0 r1).
                      * subst r1. rewrite lookup_insert /=.
                        rewrite Hsome in Hsomer0; inv Hsomer0.
                        iApply "Hv"; auto.
                      * rewrite lookup_insert_ne; auto. destruct (reg_eq_dec dst r1).
                        { subst r1; rewrite lookup_insert !fixpoint_interp1_eq /=; eauto. }
                        { rewrite lookup_insert_ne; auto. rewrite Hsome.
                          iApply "Hv"; auto. } }
                (* reestablish invariant *)
              iNext. iMod ("Hcls" with "[Heqws Hregionl Hh Ha $Hown]") as "Hown".
              { iNext.
                iDestruct (extract_from_region' _ _ a _
                              (((fixpoint interp1) E) (fs, fr)) with 
                             "[Heqws Hregionl Hh Ha]") as "[Hbe Hregion]"; eauto.
                { iExists w. iFrame. rewrite H4. iFrame "∗ #". }
                iFrame. iIntros (stsf E0). iApply big_sepL_later. iNext. auto. }
              (* apply IH *)
              iApply ("IH" $! _ _ _ _ _ _ _ ws with "[] Hreg' Hmap Hsts Hown");
                iFrame "#"; [iPureIntro;eauto|iAlways;iPureIntro;eauto].
          - iApply (wp_GetA_fail with "[Hr0 HPC Hdst Ha]"); eauto; iFrame.
            iNext. iIntros "(HPC & Ha & Hr0 & Hdst)".
            iApply wp_pure_step_later; auto. iApply wp_value.
            iNext. iIntros (Hcontr); inversion Hcontr. 
        } *)
      + (* Fail *)
        iApply (wp_fail with "[HPC Ha]"); eauto; iFrame.
        iNext. iIntros "[HPC Ha] /=".
        iApply wp_pure_step_later; auto.
        iApply wp_value.
        iNext. iIntros (Hcontr); inversion Hcontr. 
      + (* Halt *)
        iApply (wp_halt with "[HPC Ha]"); eauto; iFrame.
        iNext. iIntros "[HPC Ha] /=". 
        iMod ("Hcls" with "[Heqws Hregionl Hh Ha $Hown]") as "Hown".
        { iNext.
          iDestruct (extract_from_region' _ _ a _
                     (((fixpoint interp1) E) (fs, fr)) with 
                         "[Heqws Hregionl Hh Ha]") as "[Hbe Hregion]"; eauto.
          { iExists w. iFrame "∗ #". }
          iFrame. iIntros (stsf E0). iApply big_sepL_later. iNext. auto. }
        iApply wp_pure_step_later; auto.
        iApply wp_value.
        iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
        apply lookup_insert. rewrite delete_insert_delete. iFrame.
        rewrite insert_insert. iNext. iIntros (_). 
        iExists (<[PC:=inr (RX, g, b, e, a)]> r),fs,_. iFrame.
        iAssert (⌜related_sts_priv fs fs fr fr⌝)%I as "#Hrefl". 
        { iPureIntro. apply related_sts_priv_refl. }
        iFrame "#".
        iAssert (∀ r0 : RegName, ⌜is_Some (<[PC:=inr (RX, g, b, e, a)]> r !! r0)⌝)%I as "HA".
        { iIntros. destruct (reg_eq_dec PC r0).
          - subst r0; rewrite lookup_insert; eauto.
          - rewrite lookup_insert_ne; auto. }            
        iFrame. 
   - (* Not correct PC *)
     iDestruct ((big_sepM_delete _ _ PC) with "Hmreg") as "[HPC Hmap]";
       first apply (lookup_insert _ _ (inr (RX, g, b, e, a))). 
     iApply (wp_notCorrectPC with "HPC"); eauto.
     iNext. iIntros "HPC /=".
     iApply wp_pure_step_later; auto.
     iApply wp_value.
     iNext. iIntros (Hcontr); inversion Hcontr.
  }
  { destruct stsf as [fs fr].
    iIntros "#Hinv /=". iExists fs,fr.
    repeat (iSplit;auto). 
    iIntros "[[Hfull Hreg] [Hmreg [Hsts [Hown #Hreach]]]]".
    iExists _,_,_,_,_; iSplit; eauto; simpl.
    iRevert "Hinv Hreach". iLöb as "IH" forall (r a g fs fr b e).
    iIntros "#Hinv %". rename a0 into Hreach. 
    iDestruct "Hfull" as "%". iDestruct "Hreg" as "#Hreg". 
    iApply (wp_bind (fill [SeqCtx])).
    destruct (decide (isCorrectPC (inr ((RWX,g),b,e,a)))). 
    - (* Correct PC *)
      assert ((b <= a)%a ∧ (a <= e)%a) as Hbae.
      { eapply in_range_is_correctPC; eauto.
        unfold le_addr; omega. }
      iAssert (⌜↑logN.@(b, e) ⊆ E⌝)%I as %Hbe.
      { iPureIntro. by apply Hreach. }
      (* iMod ("Hinv" $! ⊤ E _ Hbe with "Hown") as "[[Hregion Hown] Hcls]".  *)
      iMod (na_inv_open _ _ _ (logN.@(b, e)) with "Hinv Hown") as "(Hregion & Hown & Hcls)"; auto. 
      (* iDestruct (extract_from_region _ _ a with "Hregion") *)
      (*   as (al w ah) "(Hal & Hah & Hregionl & Hvalidl & >Ha & #Hva & Hregionh & Hvalidh)"; *)
      (*   auto. *)
(* ======= *)
      (*       iInv (logN.@(b, e)) as "Hregion" "Hcls".       *)
      rewrite /read_write_cond.
      iDestruct "Hregion" as (ws) "[Hbe #Hval]".
      iDestruct ("Hval" $! (fs,fr) E) as "Hval'".
      iCombine "Hbe Hval'" as "Hregion".
      iAssert ((▷ ▷ (([∗ list] w ∈ ws, (((interp E) (fs, fr)) w)) ∗ ([∗ list] w ∈ ws, ⌜isLocalWord w = false⌝)))%I) as "[#Hval1 #Hval2]".
      { iNext. iNext. iApply (big_sepL_sepL with "Hval'"). }
      iDestruct (extract_from_region' _ _ a with "Hregion") as (w) "(Heqws & Hregionl & _ & >Ha & #[Hva1 Hva2] & Hh)"; auto.
      iDestruct ((big_sepM_delete _ _ PC) with "Hmreg") as "[HPC Hmap]"; 
        first apply (lookup_insert _ _ (inr (RWX, g, b, e, a))).
      destruct (cap_lang.decode w) eqn:Hi. (* proof by cases on each instruction *)
      + (* Jmp *)
        rewrite delete_insert_delete.
        destruct (reg_eq_dec PC r0).
        * subst r0.
          iApply (wp_jmp_successPC with "[HPC Ha]"); eauto; iFrame.
          iNext. iIntros "[HPC Ha] /=".
          iApply wp_pure_step_later; auto.
          (* reconstruct regions *)
          iNext.
          iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr)) with
                         "[Heqws Hregionl Hh Ha]") as "[Hbe Hbev]"; eauto.
          { iExists w. iFrame. iFrame "#". }
          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
          [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
          (* reestablish invariant *)
          iMod ("Hcls" with "[Hbe Hbev $Hown]") as "Hown".
          { iNext. iExists ws. iFrame. iIntros (stsf' E'). rewrite -big_sepL_later. iNext. auto. }
          (* apply IH *)
          iApply ("IH" $! _ _ _ _ _ _ _ with "[] Hreg Hmap Hsts Hown");
            iFrame "#"; [iPureIntro;eauto|iAlways;iPureIntro;eauto]. 
        * destruct (H3 r0) as [wsrc Hsomesrc].
          iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hsrc Hmap]"; eauto.
          rewrite (lookup_delete_ne r PC r0); eauto.
          iApply (wp_jmp_success with "[HPC Ha Hsrc]"); eauto; iFrame.
          iNext. iIntros "[HPC [Ha Hsrc]] /=".
          iApply wp_pure_step_later; auto. iNext. 
          (* reconstruct regions *)
          iDestruct (extract_from_region' _ _ a _ (((fixpoint interp1) E) (fs, fr)) with
                         "[Heqws Hregionl Hh Ha]") as "Hregion"; eauto.
          { iExists w. iFrame. auto. }
          iDestruct ((big_sepM_delete _ _ r0) with "[Hsrc Hmap]") as "Hmap /=";
            [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
          rewrite -delete_insert_ne; auto.
          iMod ("Hcls" with "[Hregion $Hown]") as "Hcls'".
          { iNext. iExists ws. iDestruct "Hregion" as "[$ _]". 
            iIntros (stsf' E'). rewrite -big_sepL_later. auto. }
          destruct (updatePcPerm wsrc) eqn:Heq.
          { iApply (wp_bind (fill [SeqCtx])).
            iApply (wp_notCorrectPC with "HPC"); [intro; match goal with H: isCorrectPC (inl _) |- _ => inv H end|].
            iNext. iIntros "HPC /=".
            iApply wp_pure_step_later; auto.
            iApply wp_value.
            iNext. iIntros. discriminate. }
          { destruct c,p,p,p.
            destruct p.
            - iApply (wp_bind (fill [SeqCtx])).
              iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
              iNext. iIntros "HPC /=".
              iApply wp_pure_step_later; auto.
              iApply wp_value.
              iNext. iIntros. discriminate.
            - iApply (wp_bind (fill [SeqCtx])).
              iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
              iNext. iIntros "HPC /=".
              iApply wp_pure_step_later; auto.
              iApply wp_value.
              iNext. iIntros. discriminate.
            - iApply (wp_bind (fill [SeqCtx])).
              iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
              iNext. iIntros "HPC /=".
              iApply wp_pure_step_later; auto.
              iApply wp_value.
              iNext. iIntros. discriminate.
            - iApply (wp_bind (fill [SeqCtx])).
              iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
              iNext. iIntros "HPC /=".
              iApply wp_pure_step_later; auto.
              iApply wp_value.
              iNext. iIntros. discriminate.
            - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
              apply lookup_insert. rewrite delete_insert_delete. iFrame.
              rewrite (insert_id r r0); auto.
              (* use fundamental_RX in some way ? *) admit.
            - iApply (wp_bind (fill [SeqCtx])).
              iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
              iNext. iIntros "HPC /=".
              iApply wp_pure_step_later; auto.
              iApply wp_value.
              iNext. iIntros. discriminate.
            - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
              apply lookup_insert. rewrite delete_insert_delete. iFrame.
              rewrite (insert_id r r0); auto.
              iApply ("IH" with "[] [] [Hmap] [Hsts] [Hcls']"); eauto; admit.
            - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
              apply lookup_insert. rewrite delete_insert_delete. iFrame.
              rewrite (insert_id r r0); auto.
              (* use fundamental_RWLX in some way ? *) admit. }
      + (* Jnz *) admit.
      + (* Mov *) admit.
      + (* Load *) admit.
      + (* Store *) admit.
      + (* Lt *) admit.
      + (* Add *) admit.
      + (* Sub *) admit.
      + (* Lea *) admit.
      + (* Restrict *) admit.
      + (* Subseg *) admit.
      + (* IsPtr *) admit.
      + (* GetL *) admit.
      + (* GetP *) admit.
      + (* GetB *) admit.
      + (* GetE *) admit.
      + (* GetA *) admit.
      + (* Fail *) 
        iApply (wp_fail with "[HPC Ha]"); eauto; iFrame.
        iNext. iIntros "[HPC Ha] /=".
        iApply wp_pure_step_later; auto.
        iApply wp_value. 
        iNext. iIntros (Hcontr); inversion Hcontr.
      + (* Halt *)
        iApply (wp_halt with "[HPC Ha]"); eauto; iFrame.
        iNext. iIntros "[HPC Ha] /=". 
        iMod ("Hcls" with "[Heqws Hregionl Hh Ha $Hown]") as "Hown".
        { iNext. iExists ws.
          iDestruct (extract_from_region' _ _ a _
                     (((fixpoint interp1) E) (fs, fr)) with 
                         "[Heqws Hregionl Hh Ha]") as "[Hbe Hregion]"; eauto.
          { iExists w. iFrame "∗ #". }
          iFrame. iIntros (stsf E0). iApply big_sepL_later. iNext. auto. }
        iApply wp_pure_step_later; auto.
        iApply wp_value.
        iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
        apply lookup_insert. rewrite delete_insert_delete. iFrame.
        rewrite insert_insert. iNext. iIntros (_). 
        iExists (<[PC:=inr (RWX, g, b, e, a)]> r),fs,_. iFrame.
        iAssert (⌜related_sts_priv fs fs fr fr⌝)%I as "#Hrefl". 
        { iPureIntro. apply related_sts_priv_refl. }
        iFrame "#".
        iAssert (∀ r0 : RegName, ⌜is_Some (<[PC:=inr (RWX, g, b, e, a)]> r !! r0)⌝)%I as "HA".
        { iIntros. destruct (reg_eq_dec PC r0).
          - subst r0; rewrite lookup_insert; eauto.
          - rewrite lookup_insert_ne; auto. }
        iFrame.
    - (* Not correct PC *)
     iDestruct ((big_sepM_delete _ _ PC) with "Hmreg") as "[HPC Hmap]";
       first apply (lookup_insert _ _ (inr (RWX, g, b, e, a))). 
     iApply (wp_notCorrectPC with "HPC"); eauto.
     iNext. iIntros "HPC /=".
     iApply wp_pure_step_later; auto.
     iApply wp_value.
     iNext. iIntros (Hcontr); inversion Hcontr. }
  { admit. }
  Admitted.
  

  Theorem fundamental (perm : Perm) b e g (a : Addr) stsf E r :
    (⌜perm = RX⌝ ∧ ∃ ws, (na_inv logrel_nais (logN .@ (b,e))
                                 (read_only_cond b e ws interp)%I)) ∨
    (⌜perm = RWX⌝ ∧ (na_inv logrel_nais (logN .@ (b,e))
                                 (read_write_cond b e interp)%I)) ∨
    (⌜perm = RWLX⌝ ∧ (na_inv logrel_nais (logN .@ (b,e))
                                 (read_write_local_cond b e interp)%I)) -∗
    ⟦ inr ((perm,g),b,e,a) ⟧ₑ stsf E r.
  Proof. 
    iIntros "[#[-> Hinv] | [#[-> Hinv] | #[-> Hinv]]]".
    - iDestruct "Hinv" as (ws) "Hinv". by iApply fundamental_RX. 
    - by iApply fundamental_RWX. 
    - by iApply fundamental_RWLX.
  Qed.  

    
      
End fundamental. 