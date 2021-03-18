From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules.
From cap_machine Require Export addr_reg_sample region_macros contiguous stack_macros_helpers.
From cap_machine.rules Require Import rules_StoreU_derived rules_LoadU_derived.

Section stack_macros.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          `{MonRef: MonRefG (leibnizO _) CapR_rtc Σ}
          `{MP: MachineParameters}.

  (* -------------------------------------- PUSHU ------------------------------------- *)
  Definition pushU_r_instr r_stk r := storeU_z_r r_stk 0 r.

  Definition pushU_r a1 p r_stk r : iProp Σ := (a1 ↦ₐ[p] pushU_r_instr r_stk r)%I.

  Definition isMonotone_word (w:Word) :=
    match w with
    | inl _ => false
    | inr (_,l,_,_,_) => match l with
                        | Monotone => true
                        | _ => false
                        end
    end.

  Lemma pushU_r_spec a1 a2 w w' r p p' p_a g b e stk_b stk_e stk_a stk_a' φ :
    isCorrectPC (inr ((p,g),b,e,a1)) →
    PermFlows p p' ->
    PermFlows URWLX p_a ->
    withinBounds ((URWLX,Monotone),stk_b,stk_e,stk_a) = true →
    (a1 + 1)%a = Some a2 →
    (stk_a + 1)%a = Some stk_a' →
    (isMonotone_word w' = true → (canReadUpTo w' <=? stk_a)%a = true) →

      ▷ pushU_r a1 p' r_stk r
    ∗ ▷ PC ↦ᵣ inr ((p,g),b,e,a1)
    ∗ ▷ r_stk ↦ᵣ inr ((URWLX,Monotone),stk_b,stk_e,stk_a)
    ∗ ▷ r ↦ᵣ w'
    ∗ ▷ stk_a ↦ₐ[p_a] w
    ∗ ▷ (PC ↦ᵣ inr ((p,g),b,e,a2) ∗ pushU_r a1 p' r_stk r ∗
            r_stk ↦ᵣ inr ((URWLX,Monotone),stk_b,stk_e,stk_a') ∗ r ↦ᵣ w' ∗ stk_a ↦ₐ[p_a] w'
            -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc1 Hfl Hfl' Hwb Hsuc Hstk Hcanread)
            "(Ha1 & HPC & Hr_stk & Hr & Hstk_a' & Hφ)".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_storeU_success_0_reg with "[$HPC $Ha1 $Hr $Hr_stk $Hstk_a']");
      [apply decode_encode_instrW_inv|auto|auto|auto |apply Hsuc|auto| |eauto..].
    { rewrite /canStoreU. destruct w'; auto. destruct c,p0,p0,p0,l;auto. }
    iFrame.
    iEpilogue "(HPC & Ha1 & Hr & Hr_stk & Hstk_a)".
    iApply "Hφ". iFrame.
  Qed.

  Lemma pushU_r_spec_same a1 a2 w p p' p_a g b e stk_b stk_e stk_a stk_a' φ :
    isCorrectPC (inr ((p,g),b,e,a1)) →
    PermFlows p p' ->
    PermFlows URWLX p_a ->
    withinBounds ((URWLX,Monotone),stk_b,stk_e,stk_a) = true →
    (a1 + 1)%a = Some a2 →
    (stk_a + 1)%a = Some stk_a' →

      ▷ pushU_r a1 p' r_stk r_stk
    ∗ ▷ PC ↦ᵣ inr ((p,g),b,e,a1)
    ∗ ▷ r_stk ↦ᵣ inr ((URWLX,Monotone),stk_b,stk_e,stk_a)
    ∗ ▷ stk_a ↦ₐ[p_a] w
    ∗ ▷ (PC ↦ᵣ inr ((p,g),b,e,a2) ∗ pushU_r a1 p' r_stk r_stk ∗
            r_stk ↦ᵣ inr ((URWLX,Monotone),stk_b,stk_e,stk_a') ∗ stk_a ↦ₐ[p_a] inr ((URWLX,Monotone),stk_b,stk_e,stk_a)
            -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc1 Hfl Hfl' Hwb Hsuc Hstk)
            "(Ha1 & HPC & Hr_stk & Hstk_a' & Hφ)".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_storeU_success_0_reg_same with "[$HPC $Ha1 $Hr_stk $Hstk_a']");
      [apply decode_encode_instrW_inv|auto|auto|auto|apply Hsuc|auto| |eauto..].
    { rewrite /canStoreU. simpl. apply Z.leb_le. solve_addr. }
    iEpilogue "(HPC & Ha1 & Hr_stk & Hstk_a)".
    iApply "Hφ". iFrame.
  Qed.

  Definition pushU_z_instr r_stk z := storeU_z_z r_stk 0 z.

  Definition pushU_z a1 p r_stk z : iProp Σ := (a1 ↦ₐ[p] pushU_z_instr r_stk z)%I.

  Lemma pushU_z_spec a1 a2 w z p p' p_a g b e stk_b stk_e stk_a stk_a' φ :
    isCorrectPC (inr ((p,g),b,e,a1)) →
    PermFlows p p' ->
    PermFlows URWLX p_a ->
    withinBounds ((URWLX,Monotone),stk_b,stk_e,stk_a) = true →
    (a1 + 1)%a = Some a2 →
    (stk_a + 1)%a = Some stk_a' →

      ▷ pushU_z a1 p' r_stk z
    ∗ ▷ PC ↦ᵣ inr ((p,g),b,e,a1)
    ∗ ▷ r_stk ↦ᵣ inr ((URWLX,Monotone),stk_b,stk_e,stk_a)
    ∗ ▷ stk_a ↦ₐ[p_a] w
    ∗ ▷ (PC ↦ᵣ inr ((p,g),b,e,a2) ∗ pushU_z a1 p' r_stk z ∗
            r_stk ↦ᵣ inr ((URWLX,Monotone),stk_b,stk_e,stk_a') ∗ stk_a ↦ₐ[p_a] inl z
            -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc1 Hf Hfl' Hwb Hsuc Hstk)
            "(Ha1 & HPC & Hr_stk & Hstk_a' & Hφ)".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_storeU_success_0_z with "[$HPC $Ha1 $Hr_stk $Hstk_a']");
      [apply decode_encode_instrW_inv|auto| auto |auto|apply Hsuc|eauto..].
    iEpilogue "(HPC & Ha1 & Hr_stk & Hstk_a)".
    iApply "Hφ". iFrame.
  Qed.


  (* -------------------------------------- POPU -------------------------------------- *)
  Definition popU_instrs r_stk r :=
    [loadU_r_z r r_stk (-1); sub_z_z r_t1 0 1; lea_r r_stk r_t1].

  Definition popU (a1 a2 a3 : Addr) (p : Perm) (r_stk r : RegName) : iProp Σ :=
    ([∗ list] a;i ∈ [a1;a2;a3];(popU_instrs r_stk r), a ↦ₐ[p] i)%I.

  Lemma popU_spec a1 a2 a3 a4 r w w' wt1 p p' p_a g b e stk_b stk_e stk_a stk_a' φ :
    isCorrectPC (inr ((p,g),b,e,a1)) ∧ isCorrectPC (inr ((p,g),b,e,a2)) ∧
    isCorrectPC (inr ((p,g),b,e,a3)) →
    PermFlows p p' ->
    PermFlows URWLX p_a ->
    withinBounds ((URWLX,Monotone),stk_b,stk_e,stk_a') = true →
    r ≠ PC →
    (a1 + 1)%a = Some a2 →
    (a2 + 1)%a = Some a3 →
    (a3 + 1)%a = Some a4 →
    (stk_a' + 1)%a = Some stk_a →

      ▷ popU a1 a2 a3 p' r_stk r
    ∗ ▷ PC ↦ᵣ inr ((p,g),b,e,a1)
    ∗ ▷ r_stk ↦ᵣ inr ((URWLX,Monotone),stk_b,stk_e,stk_a)
    ∗ ▷ stk_a' ↦ₐ[p_a] w
    ∗ ▷ r_t1 ↦ᵣ wt1
    ∗ ▷ r ↦ᵣ w'
    ∗ ▷ (PC ↦ᵣ inr ((p,g),b,e,a4)
            ∗ popU a1 a2 a3 p' r_stk r
            ∗ r ↦ᵣ w
            ∗ stk_a' ↦ₐ[p_a] w
            ∗ r_stk ↦ᵣ inr ((URWLX,Monotone),stk_b,stk_e,stk_a')
            ∗ r_t1 ↦ᵣ (inl (-1)%Z)
            -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
    WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros ((Hvpc1 & Hvpc2 & Hvpc3) Hfl Hfl' Hwb Hne Ha1' Ha2' Ha3' Hstk_a')
            "((>Ha1 & >Ha2 & >Ha3 & _) & >HPC & >Hr_stk & >Hstk_a & >Hr_t1 & >Hr & Hφ)".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_loadU_success with "[$HPC $Ha1 $Hr $Hr_stk $Hstk_a]");
      [apply decode_encode_instrW_inv|eauto..].
    iEpilogue "(HPC & Hr & Ha1 & Hr_stk & Hstk_a) /=".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_add_sub_lt_success_z_z with "[$HPC $Ha2 $Hr_t1]");
      [apply decode_encode_instrW_inv|eauto..].
    iEpilogue "(HPC & Ha2 & Hr_t1) /=".
    iApply (wp_bind (fill [SeqCtx])).
    assert ((stk_a + (-1)%Z)%a = Some stk_a') as Hlea;
      [revert Hstk_a';clear;solve_addr|].
    iApply (wp_lea_success_reg with "[$HPC $Ha3 $Hr_stk $Hr_t1]");
      [apply decode_encode_instrW_inv|eauto..].
    { simpl. solve_addr. }
    iEpilogue "(HPC & Ha3 & Hr_t1 & Hr_stk) /=".
    iApply "Hφ". iFrame. done.
  Qed.

End stack_macros.
