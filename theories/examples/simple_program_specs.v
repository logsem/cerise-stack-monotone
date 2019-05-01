From cap_machine Require Import rules.
From iris.proofmode Require Import tactics.

Section examples.
  Context `{memG Σ, regG Σ}.

  Lemma load_halt_1 pc_p pc_g pc_b pc_e pc_a wl wh w1 w2 r1 r2 p g b e a :
    cap_lang.decode wl = Load r1 r2 → cap_lang.decode wh = Halt →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,(pc_a + 1)%Z)) → (* these are annoying *)
    readAllowed p = true ∧ withinBounds ((p, g), b, e, a) = true →
    r1 ≠ PC →
    
    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ pc_a ↦ₐ wl
           ∗ (pc_a + 1)%Z ↦ₐ wh
           ∗ r1 ↦ᵣ w1
           ∗ r2 ↦ᵣ inr (p, g, b, e, a)
           ∗ a ↦ₐ w2 }}}
      (Executable : cap_lang.expr)
      {{{ RET HaltedV; r1 ↦ᵣ w2 }}}.
  Proof.
    intros Hil Hih Hvpc Hvpc' [Hra Hwb] Hne.
    iIntros (φ) "(Hpc & Hpca & Hpca' & Hr1 & Hr2) Hφ".
    iApply (wp_load_success _ _ _ _ _ _ pc_a); eauto. iFrame.
    iNext. iIntros "[Hpc Hr1]".
    iApply (wp_halt _ _ _ _ (pc_a + 1)%Z with "[Hpc Hpca']"); eauto; first iFrame.
    iNext. iIntros "[Hpc Hpca']".
    iApply "Hφ". iFrame. 
  Qed.

End examples. 