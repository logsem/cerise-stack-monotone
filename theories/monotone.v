From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From cap_machine Require Export logrel region_invariants_transitions.
From iris.base_logic Require Export invariants na_invariants saved_prop.
Import uPred.

Section monotone.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          `{MonRef: MonRefG (leibnizO _) CapR_rtc Σ} {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  Lemma region_state_nwl_monotone W W' a l :
    related_sts_pub_world W W' →
    region_state_nwl W a l -> region_state_nwl W' a l.
  Proof.
    rewrite /region_state_nwl /std.
    intros Hrelated Hstate.
    destruct l.
    - destruct Hrelated as [ [Hdom_sta Hrelated ] _]. simpl in *.
      assert (is_Some (W'.1 !! a)) as [y Hy].
      { apply elem_of_gmap_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. apply elem_of_gmap_dom;eauto. }
      specialize (Hrelated a Permanent y Hstate Hy).
      apply std_rel_pub_rtc_Permanent in Hrelated; subst; auto.
    - destruct Hrelated as [ [Hdom_sta Hrelated] _]. simpl in *.
      assert (is_Some (W'.1 !! a)) as [y Hy].
      { apply elem_of_gmap_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. apply elem_of_gmap_dom.
        destruct Hstate; eauto. }
      destruct Hstate as [HTemp | HPerm].
      + left.
        specialize (Hrelated _ Temporary y HTemp Hy).
        apply std_rel_pub_rtc_Temporary in Hrelated; subst;auto.
      + right.
        specialize (Hrelated _ Permanent y HPerm Hy).
        apply std_rel_pub_rtc_Permanent in Hrelated; subst; auto.
    - destruct Hrelated as [ [Hdom_sta Hrelated] _]. simpl in *.
      assert (is_Some (W'.1 !! a)) as [y Hy].
      { apply elem_of_gmap_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. apply elem_of_gmap_dom.
        destruct Hstate; eauto. destruct H0;eauto. }
      destruct Hstate as [Hmono | [Htemp | Hperm] ].
      + left. specialize (Hrelated _ Monotemporary y Hmono Hy).
        apply std_rel_pub_rtc_Monotemporary in Hrelated; subst;auto.
      + right. left.
        specialize (Hrelated _ Temporary y Htemp Hy).
        apply std_rel_pub_rtc_Temporary in Hrelated; subst;auto.
      + right. right.
        specialize (Hrelated _ Permanent y Hperm Hy).
        apply std_rel_pub_rtc_Permanent in Hrelated; subst; auto.
  Qed.

  Lemma region_state_nwl_monotone_a W W' (a a' : Addr) l :
    (a <= a')%a →
    related_sts_a_world W W' a' →
    region_state_nwl W a l -> region_state_nwl W' a l.
  Proof.
    rewrite /region_state_nwl /std.
    intros Hlt Hrelated Hstate.
    destruct l.
    - destruct Hrelated as [ [Hdom_sta Hrelated ] _]. simpl in *.
      assert (is_Some (W'.1 !! a)) as [y Hy].
      { apply elem_of_gmap_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. apply elem_of_gmap_dom;eauto. }
      specialize (Hrelated a Permanent y Hstate Hy).
      eapply rtc_implies in Hrelated.
      apply std_rel_pub_plus_rtc_Permanent in Hrelated; subst; auto.
      intros r q. destruct (decide (a <= a')%a);auto. 
    - destruct Hrelated as [ [Hdom_sta Hrelated] _]. simpl in *.
      assert (is_Some (W'.1 !! a)) as [y Hy].
      { apply elem_of_gmap_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. apply elem_of_gmap_dom.
        destruct Hstate; eauto. }
      destruct Hstate as [HTemp | HPerm].
      + left.
        specialize (Hrelated _ Temporary y HTemp Hy).
        eapply rtc_implies in Hrelated.
        apply std_rel_pub_plus_rtc_Temporary in Hrelated; subst;auto.
        intros r q. destruct (decide (a <= a')%a);auto. 
      + right.
        specialize (Hrelated _ Permanent y HPerm Hy).
        eapply rtc_implies in Hrelated.
        apply std_rel_pub_plus_rtc_Permanent in Hrelated; subst; auto.
        intros r q. destruct (decide (a <= a')%a);auto.  
    - destruct Hrelated as [ [Hdom_sta Hrelated] _]. simpl in *.
      assert (is_Some (W'.1 !! a)) as [y Hy].
      { apply elem_of_gmap_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. apply elem_of_gmap_dom.
        destruct Hstate; eauto. destruct H0;eauto. }
      destruct Hstate as [Hmono | [Htemp | Hperm] ].
      + specialize (Hrelated _ Monotemporary y Hmono Hy).
        eapply rtc_implies in Hrelated.
        apply std_rel_pub_rtc_Monotemporary in Hrelated; subst;auto.
        intros r q. rewrite decide_True;auto.
      + right. left.
        specialize (Hrelated _ Temporary y Htemp Hy).
        eapply rtc_implies in Hrelated.
        apply std_rel_pub_rtc_Temporary in Hrelated; subst;auto.
        intros r q. rewrite decide_True;auto.
      + right. right.
        specialize (Hrelated _ Permanent y Hperm Hy).
        eapply rtc_implies in Hrelated.
        apply std_rel_pub_rtc_Permanent in Hrelated; subst; auto.
        intros r q. rewrite decide_True;auto.
  Qed.

  Lemma region_state_nwl_monotone_nm W W' a :
    related_sts_pub_plus_world W W' →
    region_state_nwl W a Local -> region_state_nwl W' a Local.
  Proof.
    rewrite /region_state_nwl /std.
    intros Hrelated Hstate.
    destruct Hrelated as [ [Hdom_sta Hrelated ] _].
    assert (is_Some (W'.1 !! a)) as [y Hy].
    { apply elem_of_gmap_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. apply elem_of_gmap_dom;eauto. destruct Hstate;eauto. }
    destruct Hstate as [Htemp | Hperm].
    - left.
      specialize (Hrelated _ Temporary y Htemp Hy).
      apply std_rel_pub_plus_rtc_Temporary in Hrelated; subst;auto.
    - right.
      specialize (Hrelated _ Permanent y Hperm Hy).
      apply std_rel_pub_plus_rtc_Permanent in Hrelated; subst; auto.
  Qed.

  Lemma region_state_nwl_monotone_nm_nl W W' a :
    related_sts_priv_world W W' →
    region_state_nwl W a Global -> region_state_nwl W' a Global.
  Proof.
    rewrite /region_state_nwl /std.
    intros Hrelated Hstate.
    destruct Hrelated as [ [Hdom_sta Hrelated ] _].
    assert (is_Some (W'.1 !! a)) as [y Hy].
    { apply elem_of_gmap_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. apply elem_of_gmap_dom;eauto. }
    specialize (Hrelated _ Permanent y Hstate Hy).
    apply std_rel_rtc_Permanent in Hrelated; subst; auto.
  Qed.

  (* Lemma region_state_pwl_monotone W W' a : *)
  (*   related_sts_pub_plus_world W W' → *)
  (*   region_state_pwl W a -> region_state_pwl W' a. *)
  (* Proof. *)
  (*   rewrite /region_state_pwl /std. *)
  (*   intros Hrelated Hstate. *)
  (*   destruct Hrelated as [ [Hdom_sta Hrelated ] _]. simpl in *. *)
  (*   assert (is_Some (W'.1 !! a)) as [y Hy]. *)
  (*   { apply elem_of_gmap_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. apply elem_of_gmap_dom;eauto. } *)
  (*   specialize (Hrelated _ Temporary y Hstate Hy). *)
  (*   apply std_rel_pub_plus_rtc_Temporary in Hrelated; subst; auto. *)
  (* Qed. *)

  Lemma region_state_pwl_monotone_mono W W' a :
    related_sts_pub_world W W' →
    region_state_pwl_mono W a -> region_state_pwl_mono W' a.
  Proof.
    rewrite /region_state_pwl_mono /std.
    intros Hrelated Hstate.
    destruct Hrelated as [ [Hdom_sta Hrelated ] _]. simpl in *.
    assert (is_Some (W'.1 !! a)) as [y Hy].
    { apply elem_of_gmap_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. apply elem_of_gmap_dom;eauto. }
    specialize (Hrelated _ Monotemporary y Hstate Hy).
    apply std_rel_pub_rtc_Monotemporary in Hrelated; subst; auto.
  Qed.

  Lemma region_state_pwl_monotone_a W W' a a' :
    (a <= a')%a →
    related_sts_a_world W W' a' →
    region_state_pwl_mono W a -> region_state_pwl_mono W' a.
  Proof.
    rewrite /region_state_pwl_mono /std.
    intros Hle Hrelated Hstate.
    destruct Hrelated as [ [Hdom_sta Hrelated ] _]. simpl in *.
    assert (is_Some (W'.1 !! a)) as [y Hy].
    { apply elem_of_gmap_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. apply elem_of_gmap_dom;eauto. }
    specialize (Hrelated _ Monotemporary y Hstate Hy).
    eapply rtc_implies in Hrelated. 
    apply std_rel_pub_rtc_Monotemporary in Hrelated; subst; auto.
    intros r q. rewrite decide_True;auto. 
  Qed.

  Lemma region_state_U_monotone W W' a :
    related_sts_pub_plus_world W W' →
    region_state_U W a -> region_state_U W' a.
  Proof.
    rewrite /region_state_U /std.
    intros Hrelated Hstate.
    destruct Hrelated as [ [Hdom_sta Hrelated ] _]. simpl in *.
    assert (is_Some (W'.1 !! a)) as [y Hy].
    { apply elem_of_gmap_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. apply elem_of_gmap_dom;eauto.
      destruct Hstate as [Hstate | [Hstate | [w Hstate] ] ];eauto.
    }
    destruct Hstate as [Hstate|[Hstate|[w Hstate] ] ].
    - specialize (Hrelated _ Temporary y Hstate Hy).
      destruct (decide (y = Temporary)); subst; auto.
      apply std_rel_pub_plus_rtc_Temporary in Hrelated; auto. contradiction.
    - specialize (Hrelated _ Permanent y Hstate Hy).
      apply std_rel_pub_plus_rtc_Permanent in Hrelated; auto. subst y; auto.
    - specialize (Hrelated _ (Static {[a:=w]}) y Hstate Hy).
      eapply std_rel_pub_plus_rtc_Static in Hrelated; eauto. destruct Hrelated; subst y; eauto.
  Qed.

  Lemma region_state_U_monotone_mono W W' a :
    related_sts_pub_plus_world W W' →
    region_state_U_mono W a -> region_state_U_mono W' a.
  Proof.
    rewrite /region_state_U_mono /std.
    intros Hrelated Hstate.
    destruct Hrelated as [ [Hdom_sta Hrelated ] _]. simpl in *.
    assert (is_Some (W'.1 !! a)) as [y Hy].
    { apply elem_of_gmap_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. apply elem_of_gmap_dom;eauto.
      destruct Hstate as [Hstate | [Hstate | [Hstate | [ [w state] |  [w Hstate] ] ] ] ];eauto. }
    destruct Hstate as [Hstate | [Hstate | [Hstate | [ [w Hstate] |  [w Hstate] ] ] ] ].
    - specialize (Hrelated _ _ y Hstate Hy).
      apply std_rel_pub_plus_rtc_Monotemporary in Hrelated;eauto.
      destruct Hrelated as [-> | [? ->] ];subst;rewrite Hy;eauto. repeat right. eauto. 
    - specialize (Hrelated _ Temporary y Hstate Hy).
      destruct (decide (y = Temporary)); subst; auto.
      apply std_rel_pub_plus_rtc_Temporary in Hrelated; auto. contradiction.
    - specialize (Hrelated _ Permanent y Hstate Hy).
      apply std_rel_pub_plus_rtc_Permanent in Hrelated; auto. subst y; auto.
    - specialize (Hrelated _ (Static {[a:=w]}) y Hstate Hy).
      eapply std_rel_pub_plus_rtc_Static in Hrelated; eauto. destruct Hrelated; subst y; eauto.
      right;right;right;left. eauto. 
    - specialize (Hrelated _ _ y Hstate Hy).
      eapply std_rel_pub_plus_rtc_Uninitialized in Hrelated; eauto.
      destruct Hrelated as [-> | [? ->] ]; eauto. repeat right;eauto. 
  Qed.

  (* Lemma region_state_U_pwl_monotone W W' a : *)
  (*   related_sts_pub_plus_world W W' → *)
  (*   region_state_U_pwl W a -> region_state_U_pwl W' a. *)
  (* Proof. *)
  (*   rewrite /region_state_U /std. *)
  (*   intros Hrelated Hstate. *)
  (*   destruct Hrelated as [ [Hdom_sta Hrelated ] _]. simpl in *. *)
  (*   assert (is_Some (W'.1 !! a)) as [y Hy]. *)
  (*   { apply elem_of_gmap_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. apply elem_of_gmap_dom;eauto. *)
  (*     destruct Hstate as [? | [? ?] ]; eauto. } *)
  (*   destruct Hstate as [Hstate|[? Hstate] ]. *)
  (*   - specialize (Hrelated _ Temporary y Hstate Hy). *)
  (*     destruct (decide (y = Temporary)); subst; left; auto. *)
  (*     apply std_rel_pub_plus_rtc_Temporary in Hrelated; auto. contradiction. *)
  (*   - specialize (Hrelated _ (Static {[a:=x]}) y Hstate Hy). *)
  (*     eapply std_rel_pub_plus_rtc_Static in Hrelated; eauto. destruct Hrelated; subst y; [left | right]; eauto. *)
  (* Qed. *)

  Lemma region_state_U_pwl_monotone_mono W W' a :
    related_sts_pub_world W W' →
    region_state_U_pwl_mono W a -> region_state_U_pwl_mono W' a.
  Proof.
    rewrite /region_state_U /std.
    intros Hrelated Hstate.
    destruct Hrelated as [ [Hdom_sta Hrelated ] _]. simpl in *.
    assert (is_Some (W'.1 !! a)) as [y Hy].
    { apply elem_of_gmap_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. apply elem_of_gmap_dom;eauto.
      destruct Hstate as [? | [? ?] ]; eauto. }
    destruct Hstate as [Hstate|[? Hstate] ].
    - specialize (Hrelated _ Monotemporary y Hstate Hy).
      destruct (decide (y = Monotemporary)); subst; left; auto.
      apply std_rel_pub_rtc_Monotemporary in Hrelated; auto. contradiction.
    - specialize (Hrelated _ (Uninitialized x) y Hstate Hy).
      eapply std_rel_pub_rtc_Uninitialized in Hrelated; eauto. destruct Hrelated;subst y; [left | right]; eauto.
  Qed.

  Lemma region_state_U_pwl_monotone_mono_a W W' a a' :
    related_sts_a_world W W' a' →
    region_state_U_pwl_mono W a -> region_state_U_pwl_mono W' a.
  Proof.
    rewrite /region_state_U /std.
    intros Hrelated Hstate.
    destruct Hrelated as [ [Hdom_sta Hrelated ] _]. simpl in *.
    assert (is_Some (W'.1 !! a)) as [y Hy].
    { apply elem_of_gmap_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. apply elem_of_gmap_dom;eauto.
      destruct Hstate as [? | [? ?] ]; eauto. }
    destruct Hstate as [Hstate|[? Hstate] ].
    - specialize (Hrelated _ Monotemporary y Hstate Hy).
      destruct (decide (y = Monotemporary)); subst; auto. left;auto. 
      destruct (decide (a <= a')%a). 
      + apply std_rel_pub_rtc_Monotemporary in Hrelated; subst;auto. contradiction.
      + apply std_rel_pub_plus_rtc_Monotemporary in Hrelated; subst;auto. 
        destruct Hrelated as [-> | [? ->] ];
        rewrite /region_state_U_pwl_mono;eauto.
    - specialize (Hrelated _ (Uninitialized x) y Hstate Hy).
      destruct (decide (a <= a')%a). 
      + eapply std_rel_pub_rtc_Uninitialized in Hrelated; eauto.
        destruct Hrelated; subst y; [left | right]; eauto.
      + eapply std_rel_pub_plus_rtc_Uninitialized in Hrelated; eauto.
        destruct Hrelated as [Hy' | [w' Hy'] ]; subst y; [left | right]; eauto.
  Qed.

  (* The following lemma is not required for monotonicity, but is interesting for use in examples *)
  Lemma region_state_U_pwl_monotone_same W W' a w :
    related_sts_pub_world W W' →
    (std W) !! a = Some (Static {[a:=w]}) -> (std W') !! a = Some Temporary ∨ (std W') !! a = Some (Static {[a:=w]}).
  Proof.
    rewrite /region_state_U /std.
    intros Hrelated Hstate.
    destruct Hrelated as [ [Hdom_sta Hrelated ] _]. simpl in *.
    assert (is_Some (W'.1 !! a)) as [y Hy].
    { apply elem_of_gmap_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. apply elem_of_gmap_dom;eauto. }
    specialize (Hrelated _ (Static {[a:=w]}) y Hstate Hy).
    eapply std_rel_pub_rtc_Static in Hrelated; eauto. destruct Hrelated; subst y; [left | right]; eauto.
  Qed.

  Lemma region_state_Revoked_monotone (W W' : WORLD) (a : Addr) :
    related_sts_pub_world W W' →
    (std W) !! a = Some Revoked ->
    (std W') !! a = Some Revoked ∨
    (std W') !! a = Some Temporary ∨
    (std W') !! a = Some Monotemporary ∨
    (std W') !! a = Some Permanent.
  Proof.
    rewrite /region_state_pwl_mono /std.
    intros Hrelated Hstate.
    destruct Hrelated as [ [Hdom_sta Hrelated ] _]. simpl in *.
    assert (is_Some (W'.1 !! a)) as [y Hy].
    { apply elem_of_gmap_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. apply elem_of_gmap_dom;eauto. }
    specialize (Hrelated _ Revoked y Hstate Hy).
    apply std_rel_pub_rtc_Revoked in Hrelated; auto.
    destruct Hrelated as [Htemp | [Hperm | [Hmono | Hrev] ] ]; subst; auto.
  Qed.

  Lemma interp_monotone W W' w :
    ⌜related_sts_pub_world W W'⌝ -∗
    interp W w -∗ interp W' w.
  Proof.
    iIntros (Hrelated) "#Hw".
    rewrite /interp /= fixpoint_interp1_eq /=.
    destruct w; rewrite fixpoint_interp1_eq /=; auto.
    destruct c,p,p,p,p; auto.
    - iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p Hfl) "#[Hrw Hrel]".
      iExists _. iSplit;eauto. iFrame "#".
      iDestruct "Hrel" as %Hrel.
      iPureIntro. apply region_state_nwl_monotone with W;auto.
    - iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p Hfl) "#[Hrw Hrel]".
      iExists _. iSplit;eauto. iFrame "#".
      iDestruct "Hrel" as %Hrel.
      iPureIntro. apply region_state_nwl_monotone with W;auto.
    - destruct l; auto.
      iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p Hfl) "#[Hrw Hrel]".
      iExists _. iSplit;eauto. iFrame "#".
      iDestruct "Hrel" as %Hrel.
      iPureIntro.
      apply region_state_pwl_monotone_mono with W;auto.
    - iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p Hfl) "#[Hrw Hrel]".
      iExists _. iSplit;eauto. iFrame "#".
      iDestruct "Hrel" as %Hrel.
      iPureIntro. apply region_state_nwl_monotone with W;auto.
    - iModIntro. iIntros (r W'').
      destruct l; simpl.
      + iIntros (Hrelated').
        iAssert (future_world Global a W W'')%I as "Hrelated".
        { iPureIntro. apply related_sts_pub_priv_trans_world with W'; auto. }
        iSpecialize ("Hw" $! r W'' with "Hrelated").
        iApply "Hw".
      + iIntros (Hrelated').
        iAssert (future_world Local a W W'')%I as "Hrelated".
        { iPureIntro. apply related_sts_pub_pub_plus_trans_world with W'; auto. }
        iSpecialize ("Hw" $! r W'' with "Hrelated").
        iApply "Hw".
      + iIntros (Hrelated').
        iAssert (future_world Monotone a0 W W'')%I as "Hrelated".
        { iPureIntro. apply related_sts_pub_a_trans_world with W'; auto. }
        iSpecialize ("Hw" $! r W'' with "Hrelated").
        iApply "Hw".
    - iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p Hfl) "#[Hrw Hrel]".
      iExists _. iSplit;eauto. iFrame "#".
      iDestruct "Hrel" as %Hrel.
      iPureIntro. apply region_state_nwl_monotone with W;auto.
    - destruct l; auto.
      iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p Hfl) "#[Hrw Hrel]".
      iExists _. iSplit;eauto. iFrame "#".
      iDestruct "Hrel" as %Hrel.
      iPureIntro. apply region_state_pwl_monotone_mono with W;auto.
    - destruct l; simpl.
      + iApply (big_sepL_mono with "Hw").
        iIntros (n y Hsome) "Hw".
        iDestruct "Hw" as (p Hfl) "#[Hrw Hst]".
        iExists _. iSplit;eauto. iFrame "#".
        iDestruct "Hst" as %Hst.
        iPureIntro. eapply (region_state_nwl_monotone W W' _ Global); auto.
      + iDestruct "Hw" as "[Hw1 Hw2]".
        iSplitL "Hw1".
        * iApply (big_sepL_mono with "Hw1").
          iIntros (n y Hsome) "Hw".
          iDestruct "Hw" as (p Hfl) "#[Hrw Hst ]".
          iExists _. iSplit;eauto. iFrame "#".
          iDestruct "Hst" as %Hstd.
          iPureIntro. eapply (region_state_nwl_monotone W W' _ Local); auto.
        * iApply (big_sepL_mono with "Hw2").
          iIntros (n y Hsome) "Hw".
          iDestruct "Hw" as (p Hfl) "#[Hrw Hst ]".
          iExists _. iSplit;eauto. iFrame "#".
          iDestruct "Hst" as %Hst.
          iPureIntro.
          eapply region_state_U_monotone; eauto.
          apply related_sts_pub_pub_plus_world;auto.
      + iDestruct "Hw" as "[Hw1 Hw2]".
        iSplitL "Hw1".
        * iApply (big_sepL_mono with "Hw1").
          iIntros (n y Hsome) "Hw".
          iDestruct "Hw" as (p Hfl) "#[Hrw Hst ]".
          iExists _. iSplit;eauto. iFrame "#".
          iDestruct "Hst" as %Hstd.
          iPureIntro. eapply (region_state_nwl_monotone W W' _ Monotone); auto.
        * iApply (big_sepL_mono with "Hw2").
          iIntros (n y Hsome) "Hw".
          iDestruct "Hw" as (p Hfl) "#[Hrw Hst ]".
          iExists _. iSplit;eauto. iFrame "#".
          iDestruct "Hst" as %Hst.
          iPureIntro.
          eapply region_state_U_monotone_mono; eauto.
          apply related_sts_pub_pub_plus_world;auto. 
    - destruct l; auto.
      iDestruct "Hw" as "[Hbe Hexec]".
      iSplit.
      { iApply (big_sepL_mono with "Hbe").
        iIntros (n y Hsome) "Hw".
        iDestruct "Hw" as (p Hfl) "#[Hrw Hrel ]".
        iExists _. iSplit;eauto. iFrame "#".
        iDestruct "Hrel" as %Hrel.
        iPureIntro. apply region_state_pwl_monotone_mono with W;auto. }
      { iApply (big_sepL_mono with "Hexec").
        iIntros (n y Hsome) "Hw".
        iDestruct "Hw" as (p Hfl) "#[Hrw Hrel ]".
        iExists _. iSplit;eauto. iFrame "#".
        iDestruct "Hrel" as %Hrel.
        iPureIntro. apply region_state_U_pwl_monotone_mono with W;auto. }
    - destruct l; simpl.
      + iApply (big_sepL_mono with "Hw").
        iIntros (n y Hsome) "Hw".
        iDestruct "Hw" as (p Hfl) "#[Hrw Hst ]".
        iExists _. iSplit;eauto. iFrame "#".
        iDestruct "Hst" as %Hst.
        iPureIntro. eapply (region_state_nwl_monotone W W' _ Global); auto.
      + iDestruct "Hw" as "[Hw1 Hw2]".
        iSplitL "Hw1".
        * iApply (big_sepL_mono with "Hw1").
          iIntros (n y Hsome) "Hw".
          iDestruct "Hw" as (p Hfl) "#[Hrw Hst ]".
          iExists _. iSplit;eauto. iFrame "#".
          iDestruct "Hst" as %Hstd.
          iPureIntro. eapply (region_state_nwl_monotone W W' _ Local); auto.
        * iApply (big_sepL_mono with "Hw2").
          iIntros (n y Hsome) "Hw".
          iDestruct "Hw" as (p Hfl) "#[Hrw Hst ]".
          iExists _. iSplit;eauto. iFrame "#".
          iDestruct "Hst" as %Hst.
          iPureIntro.
          eapply region_state_U_monotone; eauto.
          apply related_sts_pub_pub_plus_world;auto.
      + iDestruct "Hw" as "[Hw1 Hw2]".
        iSplitL "Hw1".
        * iApply (big_sepL_mono with "Hw1").
          iIntros (n y Hsome) "Hw".
          iDestruct "Hw" as (p Hfl) "#[Hrw Hst ]".
          iExists _. iSplit;eauto. iFrame "#".
          iDestruct "Hst" as %Hstd.
          iPureIntro. eapply (region_state_nwl_monotone W W' _ Monotone); auto.
        * iApply (big_sepL_mono with "Hw2").
          iIntros (n y Hsome) "Hw".
          iDestruct "Hw" as (p Hfl) "#[Hrw Hst ]".
          iExists _. iSplit;eauto. iFrame "#".
          iDestruct "Hst" as %Hst.
          iPureIntro.
          eapply region_state_U_monotone_mono; eauto.
          apply related_sts_pub_pub_plus_world;auto.
    - destruct l; auto.
      iDestruct "Hw" as "[Hbe Hexec]".
      iSplit.
      { iApply (big_sepL_mono with "Hbe").
        iIntros (n y Hsome) "Hw".
        iDestruct "Hw" as (p Hfl) "#[Hrw Hrel ]".
        iExists _. iSplit;eauto. iFrame "#".
        iDestruct "Hrel" as %Hrel.
        iPureIntro. apply region_state_pwl_monotone_mono with W;auto. }
      { iApply (big_sepL_mono with "Hexec").
        iIntros (n y Hsome) "Hw".
        iDestruct "Hw" as (p Hfl) "#[Hrw Hrel ]".
        iExists _. iSplit;eauto. iFrame "#".
        iDestruct "Hrel" as %Hrel.
        iPureIntro. apply region_state_U_pwl_monotone_mono with W;auto. }
  Qed.

  Definition aOf (w : Word) : Addr :=
    match w with
    | inl _ => addr_reg.top
    | inr (p,_,_,e,a) => if isU p then a else e
    end.

  Lemma region_addrs_lookup_le b e a n :
    region_addrs b e !! n = Some a →
    (a <= e)%a.
  Proof.
    intros Hlookup.
    assert (a ∈ (region_addrs b e)) as Hin.
    { apply elem_of_list_lookup. eauto. }
    apply elem_of_region_addrs in Hin as [? ?].
    solve_addr.
  Qed. 

  Lemma interp_monotone_a W W' w :
    ⌜related_sts_a_world W W' (aOf w)⌝ -∗
    interp W w -∗ interp W' w.
  Proof.
    iIntros (Hrelated) "#Hw".
    rewrite /interp /= fixpoint_interp1_eq /=.
    destruct w; rewrite fixpoint_interp1_eq /=; auto.
    destruct c,p,p,p,p; auto; simpl in Hrelated.
    - iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p Hfl) "#[Hrw Hrel]".
      iExists _. iSplit;eauto. iFrame "#".
      iDestruct "Hrel" as %Hrel.
      iPureIntro. apply region_state_nwl_monotone_a with W a0;auto.
      eapply region_addrs_lookup_le;eauto. 
    - iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p Hfl) "#[Hrw Hrel]".
      iExists _. iSplit;eauto. iFrame "#".
      iDestruct "Hrel" as %Hrel.
      iPureIntro. apply region_state_nwl_monotone_a with W a0;auto. eapply region_addrs_lookup_le;eauto. 
    - destruct l; auto.
      iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p Hfl) "#[Hrw Hrel]".
      iExists _. iSplit;eauto. iFrame "#".
      iDestruct "Hrel" as %Hrel.
      iPureIntro.
      apply region_state_pwl_monotone_a with W a0;auto. eapply region_addrs_lookup_le;eauto. 
    - iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p Hfl) "#[Hrw Hrel]".
      iExists _. iSplit;eauto. iFrame "#".
      iDestruct "Hrel" as %Hrel.
      iPureIntro. apply region_state_nwl_monotone_a with W a0;auto. eapply region_addrs_lookup_le;eauto. 
    - iModIntro. iIntros (r W'').
      destruct l; simpl.
      + iIntros (Hrelated').
        iAssert (future_world Global a W W'')%I as "Hrelated".
        { iPureIntro. apply related_sts_a_priv_trans_world with W' a0; auto. }
        iSpecialize ("Hw" $! r W'' with "Hrelated").
        iApply "Hw".
      + iIntros (Hrelated').
        iAssert (future_world Local a W W'')%I as "Hrelated".
        { iPureIntro. apply related_sts_a_pub_plus_trans_world with W' a0; auto. }
        iSpecialize ("Hw" $! r W'' with "Hrelated").
        iApply "Hw".
      + iIntros (Hrelated').
        iAssert (future_world Monotone a0 W W'')%I as "Hrelated".
        { iPureIntro. apply related_sts_a_trans_world with W';auto. }
        iSpecialize ("Hw" $! r W'' with "Hrelated").
        iApply "Hw".
    - iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p Hfl) "#[Hrw Hrel]".
      iExists _. iSplit;eauto. iFrame "#".
      iDestruct "Hrel" as %Hrel.
      iPureIntro. apply region_state_nwl_monotone_a with W a0;auto. eapply region_addrs_lookup_le;eauto. 
    - destruct l; auto.
      iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p Hfl) "#[Hrw Hrel]".
      iExists _. iSplit;eauto. iFrame "#".
      iDestruct "Hrel" as %Hrel.
      iPureIntro. apply region_state_pwl_monotone_a with W a0;auto. eapply region_addrs_lookup_le;eauto. 
    - destruct l; simpl.
      + iApply (big_sepL_mono with "Hw").
        iIntros (n y Hsome) "Hw".
        iDestruct "Hw" as (p Hfl) "#[Hrw Hst]".
        iExists _. iSplit;eauto. iFrame "#".
        iDestruct "Hst" as %Hst.
        iPureIntro. apply region_state_nwl_monotone_nm_nl with W;auto.
        apply related_sts_pub_plus_priv_world, related_sts_a_pub_plus_world with a;auto. 
      + iDestruct "Hw" as "[Hw1 Hw2]".
        iSplitL "Hw1".
        * iApply (big_sepL_mono with "Hw1").
          iIntros (n y Hsome) "Hw".
          iDestruct "Hw" as (p Hfl) "#[Hrw Hst ]".
          iExists _. iSplit;eauto. iFrame "#".
          iDestruct "Hst" as %Hstd.
          iPureIntro. eapply (region_state_nwl_monotone_a W W' _ (addr_reg.min a a0) Local); auto.
          eapply region_addrs_lookup_le;eauto.  apply related_sts_a_weak_world with a;auto. solve_addr. 
        * iApply (big_sepL_mono with "Hw2").
          iIntros (n y Hsome) "Hw".
          iDestruct "Hw" as (p Hfl) "#[Hrw Hst ]".
          iExists _. iSplit;eauto. iFrame "#".
          iDestruct "Hst" as %Hst.
          iPureIntro.
          eapply region_state_U_monotone; eauto.
          apply related_sts_a_pub_plus_world with a;auto.
      + iDestruct "Hw" as "[Hw1 Hw2]".
        iSplitL "Hw1".
        * iApply (big_sepL_mono with "Hw1").
          iIntros (n y Hsome) "Hw".
          iDestruct "Hw" as (p Hfl) "#[Hrw Hst ]".
          iExists _. iSplit;eauto. iFrame "#".
          iDestruct "Hst" as %Hstd.
          iPureIntro. eapply (region_state_nwl_monotone_a W W' _ (addr_reg.min a a0) Monotone); auto.
          eapply region_addrs_lookup_le;eauto.  apply related_sts_a_weak_world with a;auto. solve_addr.
        * iApply (big_sepL_mono with "Hw2").
          iIntros (n y Hsome) "Hw".
          iDestruct "Hw" as (p Hfl) "#[Hrw Hst ]".
          iExists _. iSplit;eauto. iFrame "#".
          iDestruct "Hst" as %Hst.
          iPureIntro.
          eapply region_state_U_monotone_mono; eauto.
          apply related_sts_a_pub_plus_world with a;auto.
    - destruct l; auto.
      iDestruct "Hw" as "[Hbe Hexec]".
      iSplit.
      { iApply (big_sepL_mono with "Hbe").
        iIntros (n y Hsome) "Hw".
        iDestruct "Hw" as (p Hfl) "#[Hrw Hrel ]".
        iExists _. iSplit;eauto. iFrame "#".
        iDestruct "Hrel" as %Hrel.
        iPureIntro. apply region_state_pwl_monotone_a with W (addr_reg.min a a0);auto.
        eapply region_addrs_lookup_le;eauto. apply related_sts_a_weak_world with a;auto. solve_addr.
      }
      { iApply (big_sepL_mono with "Hexec").
        iIntros (n y Hsome) "Hw".
        iDestruct "Hw" as (p Hfl) "#[Hrw Hrel ]".
        iExists _. iSplit;eauto. iFrame "#".
        iDestruct "Hrel" as %Hrel.
        iPureIntro. apply region_state_U_pwl_monotone_mono_a with W (addr_reg.min a a0);auto.
        apply related_sts_a_weak_world with a;auto. solve_addr. }
    - destruct l; simpl.
      + iApply (big_sepL_mono with "Hw").
        iIntros (n y Hsome) "Hw".
        iDestruct "Hw" as (p Hfl) "#[Hrw Hst ]".
        iExists _. iSplit;eauto. iFrame "#".
        iDestruct "Hst" as %Hst.
        iPureIntro. apply region_state_nwl_monotone_nm_nl with W;auto.
        apply related_sts_pub_plus_priv_world, related_sts_a_pub_plus_world with a;auto.
      + iDestruct "Hw" as "[Hw1 Hw2]".
        iSplitL "Hw1".
        * iApply (big_sepL_mono with "Hw1").
          iIntros (n y Hsome) "Hw".
          iDestruct "Hw" as (p Hfl) "#[Hrw Hst ]".
          iExists _. iSplit;eauto. iFrame "#".
          iDestruct "Hst" as %Hstd.
          iPureIntro. eapply (region_state_nwl_monotone_a W W' _ (addr_reg.min a a0) Local); auto.
          eapply region_addrs_lookup_le;eauto. apply related_sts_a_weak_world with a;auto. solve_addr.
        * iApply (big_sepL_mono with "Hw2").
          iIntros (n y Hsome) "Hw".
          iDestruct "Hw" as (p Hfl) "#[Hrw Hst ]".
          iExists _. iSplit;eauto. iFrame "#".
          iDestruct "Hst" as %Hst.
          iPureIntro.
          eapply region_state_U_monotone; eauto.
          apply related_sts_a_pub_plus_world with a;auto.
      + iDestruct "Hw" as "[Hw1 Hw2]".
        iSplitL "Hw1".
        * iApply (big_sepL_mono with "Hw1").
          iIntros (n y Hsome) "Hw".
          iDestruct "Hw" as (p Hfl) "#[Hrw Hst ]".
          iExists _. iSplit;eauto. iFrame "#".
          iDestruct "Hst" as %Hstd.
          iPureIntro. eapply (region_state_nwl_monotone_a W W' _ (addr_reg.min a a0)  Monotone); auto.
          eapply region_addrs_lookup_le;eauto. apply related_sts_a_weak_world with a;auto. solve_addr.
         * iApply (big_sepL_mono with "Hw2").
          iIntros (n y Hsome) "Hw".
          iDestruct "Hw" as (p Hfl) "#[Hrw Hst ]".
          iExists _. iSplit;eauto. iFrame "#".
          iDestruct "Hst" as %Hst.
          iPureIntro.
          eapply region_state_U_monotone_mono; eauto.
          apply related_sts_a_pub_plus_world with a;auto.
    - destruct l; auto.
      iDestruct "Hw" as "[Hbe Hexec]".
      iSplit.
      { iApply (big_sepL_mono with "Hbe").
        iIntros (n y Hsome) "Hw".
        iDestruct "Hw" as (p Hfl) "#[Hrw Hrel ]".
        iExists _. iSplit;eauto. iFrame "#".
        iDestruct "Hrel" as %Hrel.
        iPureIntro. apply region_state_pwl_monotone_a with W (addr_reg.min a a0);auto.
        eapply region_addrs_lookup_le;eauto. apply related_sts_a_weak_world with a;auto. solve_addr.
      }
      { iApply (big_sepL_mono with "Hexec").
        iIntros (n y Hsome) "Hw".
        iDestruct "Hw" as (p Hfl) "#[Hrw Hrel ]".
        iExists _. iSplit;eauto. iFrame "#".
        iDestruct "Hrel" as %Hrel.
        iPureIntro. apply region_state_U_pwl_monotone_mono_a with W a;auto. }
  Qed.

  Definition isMonotoneWord (w : Word) :=
    match w with
    | inl _ => false
    | inr (_,l,_,_,_) => isMonotone l
    end.

  Lemma interp_monotone_nm W W' w :
    ⌜related_sts_pub_plus_world W W'⌝ -∗ ⌜isMonotoneWord w = false⌝ -∗
    interp W w -∗ interp W' w.
  Proof.
    iIntros (Hrelated Hnl) "#Hw".
    rewrite /interp /= fixpoint_interp1_eq /=.
    destruct w; rewrite fixpoint_interp1_eq /=; auto.
    destruct c,p,p,p,p; auto.
    - iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p Hfl) "#[Hrw Hrel ]".
      iExists _. iSplit;eauto. iFrame "#".
      iDestruct "Hrel" as %Hrel.
      iPureIntro. destruct l; try discriminate.
      apply region_state_nwl_monotone_nm_nl with W;auto.
      apply related_sts_pub_plus_priv_world;auto.
      apply region_state_nwl_monotone_nm with W;auto.
    - iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p Hfl) "#[Hrw Hrel ]".
      iExists _. iSplit;eauto. iFrame "#".
      iDestruct "Hrel" as %Hrel.
      iPureIntro. destruct l; try discriminate.
      apply region_state_nwl_monotone_nm_nl with W;auto.
      apply related_sts_pub_plus_priv_world;auto.
      apply region_state_nwl_monotone_nm with W;auto.
    - destruct l; auto. discriminate.
    - iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p Hfl) "#[Hrw Hrel ]".
      iExists _. iSplit;eauto. iFrame "#".
      iDestruct "Hrel" as %Hrel.
      iPureIntro. destruct l; try discriminate.
      apply region_state_nwl_monotone_nm_nl with W;auto.
      apply related_sts_pub_plus_priv_world;auto.
      apply region_state_nwl_monotone_nm with W;auto.
    - iModIntro. iIntros (r W'').
      destruct l; simpl; try discriminate.
      + iIntros (Hrelated').
        iAssert (future_world Global a W W'')%I as "Hrelated".
        { iPureIntro. apply related_sts_pub_plus_priv_trans_world with W'; auto. }
        iSpecialize ("Hw" $! r W'' with "Hrelated").
        iApply "Hw".
      + iIntros (Hrelated').
        iAssert (future_world Local a W W'')%I as "Hrelated".
        { iPureIntro. apply related_sts_pub_plus_trans_world with W'; auto. }
        iSpecialize ("Hw" $! r W'' with "Hrelated").
        iApply "Hw".
    - iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p Hfl) "#[Hrw Hrel ]".
      iExists _. iSplit;eauto. iFrame "#".
      iDestruct "Hrel" as %Hrel.
      iPureIntro. destruct l; try discriminate.
      apply region_state_nwl_monotone_nm_nl with W;auto.
      apply related_sts_pub_plus_priv_world;auto.
      apply region_state_nwl_monotone_nm with W;auto.
    - destruct l; try discriminate. done. done.
    - destruct l; simpl in Hnl; try discriminate.
      + iApply (big_sepL_mono with "Hw").
        iIntros (n y Hsome) "Hw".
        iDestruct "Hw" as (p Hfl) "#[Hrw Hst ]".
        iExists _. iSplit;eauto. iFrame "#".
        iDestruct "Hst" as %Hst.
        iPureIntro.
        apply region_state_nwl_monotone_nm_nl with W;auto.
        apply related_sts_pub_plus_priv_world;auto.
      + iDestruct "Hw" as "[Hw1 Hw2]".
        iSplit.
        { iApply (big_sepL_mono with "Hw1").
          iIntros (n y Hsome) "Hw".
          iDestruct "Hw" as (p Hfl) "#[Hrw Hst ]".
          iExists _. iSplit;eauto. iFrame "#".
          iDestruct "Hst" as %Hst.
          iPureIntro.
          apply region_state_nwl_monotone_nm with W;auto. }
        { iApply (big_sepL_mono with "Hw2").
          iIntros (n y Hsome) "Hw".
          iDestruct "Hw" as (p Hfl) "#[Hrw Hst ]".
          iExists _. iSplit;eauto. iFrame "#".
          iDestruct "Hst" as %Hst.
          iPureIntro.
          apply region_state_U_monotone with W;auto. }
    - destruct l; auto. discriminate.
    - destruct l; simpl in Hnl; try discriminate.
      + iApply (big_sepL_mono with "Hw").
        iIntros (n y Hsome) "Hw".
        iDestruct "Hw" as (p Hfl) "#[Hrw Hst ]".
        iExists _. iSplit;eauto. iFrame "#".
        iDestruct "Hst" as %Hst.
        iPureIntro.
        apply region_state_nwl_monotone_nm_nl with W; auto.
        apply related_sts_pub_plus_priv_world;auto.
      + iDestruct "Hw" as "[Hw1 Hw2]".
        iSplit.
        { iApply (big_sepL_mono with "Hw1").
          iIntros (n y Hsome) "Hw".
          iDestruct "Hw" as (p Hfl) "#[Hrw Hst ]".
          iExists _. iSplit;eauto. iFrame "#".
          iDestruct "Hst" as %Hst.
          iPureIntro.
          apply region_state_nwl_monotone_nm with W;auto. }
        { iApply (big_sepL_mono with "Hw2").
          iIntros (n y Hsome) "Hw".
          iDestruct "Hw" as (p Hfl) "#[Hrw Hst ]".
          iExists _. iSplit;eauto. iFrame "#".
          iDestruct "Hst" as %Hst.
          iPureIntro.
          apply region_state_U_monotone with W;auto. }
    - destruct l; try discriminate. done. done.
  Qed. 

  Lemma interp_monotone_nm_nl W W' w :
    ⌜related_sts_priv_world W W'⌝ -∗ ⌜isLocalWord w = false⌝ -∗
    interp W w -∗ interp W' w.
  Proof.
    iIntros (Hrelated Hnl) "#Hw".
    rewrite /interp /= fixpoint_interp1_eq /=.
    destruct w; rewrite fixpoint_interp1_eq /=; auto.
    destruct c,p,p,p,p; auto.
    - iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p Hfl) "#[Hrw Hrel ]".
      iExists _. iSplit;eauto. iFrame "#".
      iDestruct "Hrel" as %Hrel.
      iPureIntro. destruct l; try discriminate.
      apply region_state_nwl_monotone_nm_nl with W;auto.
    - iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p Hfl) "#[Hrw Hrel ]".
      iExists _. iSplit;eauto. iFrame "#".
      iDestruct "Hrel" as %Hrel.
      iPureIntro. destruct l; try discriminate.
      apply region_state_nwl_monotone_nm_nl with W;auto.
    - destruct l; auto. discriminate.
    - iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p Hfl) "#[Hrw Hrel ]".
      iExists _. iSplit;eauto. iFrame "#".
      iDestruct "Hrel" as %Hrel.
      iPureIntro. destruct l; try discriminate.
      apply region_state_nwl_monotone_nm_nl with W;auto.
    - iModIntro. iIntros (r W'').
      destruct l; simpl; try discriminate.
      iIntros (Hrelated').
      iAssert (future_world Global a0 W W'')%I as "Hrelated".
      { iPureIntro. apply related_sts_priv_trans_world with W'; auto. }
      iSpecialize ("Hw" $! r W'' with "Hrelated").
      iApply "Hw".
    - iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p Hfl) "#[Hrw Hrel ]".
      iExists _. iSplit;eauto. iFrame "#".
      iDestruct "Hrel" as %Hrel.
      iPureIntro. destruct l; try discriminate.
      apply region_state_nwl_monotone_nm_nl with W;auto.
    - destruct l; try discriminate. done.
    - destruct l; simpl in Hnl; try discriminate.
      iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p Hfl) "#[Hrw Hst ]".
      iExists _. iSplit;eauto. iFrame "#".
      iDestruct "Hst" as %Hst.
      iPureIntro.
      apply region_state_nwl_monotone_nm_nl with W; auto.
    - destruct l; auto. discriminate.
    - destruct l; simpl in Hnl; try discriminate.
      iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p Hfl) "#[Hrw Hst ]".
      iExists _. iSplit;eauto. iFrame "#".
      iDestruct "Hst" as %Hst.
      iPureIntro.
      apply region_state_nwl_monotone_nm_nl with W; auto.
    - destruct l; try discriminate. done.
  Qed.

  (*Lemma that allows switching between the two different formulations of monotonicity, to alleviate the effects of inconsistencies*)
  Lemma switch_monotonicity_formulation ρ l w p φ:
      ρ ≠ Revoked → (∀ m, ρ ≠ Static m) -> (∀ m, ρ ≠ Monostatic m) -> (∀ w, ρ ≠ Uninitialized w) ->
      monotonicity_guarantees_region ρ l w p φ ≡ monotonicity_guarantees_decide (Σ := Σ) ρ l w p φ.
  Proof.
    intros Hrev Hsta Hmono Huninit.
    unfold monotonicity_guarantees_region, monotonicity_guarantees_decide.
    iSplit; iIntros "HH".
    - destruct ρ;simpl;auto.
      * simpl. destruct (pwl p) ; intros.
        destruct (decide (Temporary = Temporary ∧ true = true)). auto. assert (Temporary = Temporary ∧ true = true); auto. by congruence.
        destruct (decide (Temporary = Temporary ∧ false = true)). destruct a; by exfalso. auto.
      * destruct (pwl p).
        destruct (decide (Monotemporary = Monotemporary ∧ true = true)). auto. exfalso;auto.
        simpl. auto.
      * by intros.
      * specialize (Hsta g). done.
      * specialize (Hmono g). done.
      * specialize (Huninit w0). done.
    - intros. destruct ρ;simpl;auto.
      * destruct (pwl p);simpl;auto.
      * destruct (pwl p);simpl;auto.
  Qed.

  (* The validity of regions are monotone wrt private/public future worlds *)
  Lemma adv_monotone W W' b e :
    related_sts_priv_world W W' →
    ([∗ list] a ∈ region_addrs b e, read_write_cond a RX interp
                      ∧ ⌜std W !! a = Some Permanent⌝)
    -∗ ([∗ list] a ∈ region_addrs b e, read_write_cond a RX interp
                      ∧ ⌜std W' !! a = Some Permanent⌝).
  Proof.
    iIntros (Hrelated) "Hr".
    iApply (big_sepL_mono with "Hr").
    iIntros (k y Hsome) "(Hy & Hperm)".
    iFrame.
    iDestruct "Hperm" as %Hperm.
    iPureIntro.
    apply (region_state_nwl_monotone_nm_nl _ W') in Hperm; auto.
  Qed.

  Lemma adv_stack_monotone W W' b e :
    related_sts_pub_world W W' ->
    ([∗ list] a ∈ region_addrs b e, read_write_cond a RWLX interp
                                     ∧ ⌜region_state_pwl_mono W a⌝)
    -∗ ([∗ list] a ∈ region_addrs b e, read_write_cond a RWLX interp
                                       ∧ ⌜region_state_pwl_mono W' a⌝).
  Proof.
    iIntros (Hrelated) "Hstack_adv".
    iApply (big_sepL_mono with "Hstack_adv").
    iIntros (k y Hsome) "(Hr & Htemp)".
    iDestruct "Htemp" as %Htemp.
    iFrame. iPureIntro.
    apply (region_state_pwl_monotone_mono _ W') in Htemp; auto.
  Qed.

  Global Instance interp_ne n :
    Proper (dist n ==> dist n) (λ Wv : WORLD * (leibnizO Word), (interp Wv.1) Wv.2).
  Proof.
    solve_proper.
  Qed.
  
  (* The general monotonicity statement that interp gives you when writing a word into a
     pointer (p0, l, a2, a1, a0) ; simply a bundling of all individual monotonicity statements *)
Lemma interp_monotone_generalW (W : WORLD)  (ρ : region_type) (p p0 p1 : Perm) (l g : Locality)(b e a a2 a1 a0 : Addr):
  std W !! a0 = Some ρ →
  withinBounds (p0, l, a2, a1, a0) = true →
  PermFlows p0 p1 →
  canStore p0 a0 (inr (p,g,b,e,a)) = true →
  ((fixpoint interp1) W) (inr (p0, l, a2, a1, a0)) -∗
  monotonicity_guarantees_region ρ a0 (inr (p, g, b, e, a)) p1  (λne Wv : WORLD * (leibnizO Word), (interp Wv.1) Wv.2).
Proof.
  unfold monotonicity_guarantees_region.
  iIntros (Hstd Hwb Hfl' Hconds) "#Hvdst".
  destruct ρ;auto.
  - destruct (pwl p1) eqn: HpwlP1 ; iModIntro; simpl;auto.
    * iIntros (W0 W1) "% HIW0".
      iApply (interp_monotone_nm with "[] [] HIW0");[done|].
      destruct p0 ; try (simpl in Hconds; by exfalso).
      all: destruct g;auto. 
      all: iDestruct (writeLocalAllowed_valid_cap_implies with "Hvdst" ) as %Ha;eauto;rewrite Ha in Hstd;done.
    * iIntros (W0 W1) "% HIW0".
      iApply (interp_monotone_nm_nl with "[] [] HIW0");[done|].
      destruct g;auto.
      ** destruct p0;inversion Hconds;destruct p1;inversion Hfl';done.
      ** apply andb_prop in Hconds as [Hconds ?]. destruct p0;inversion Hconds;destruct p1;inversion Hfl';done.
  - destruct (pwl p1) eqn: HpwlP1 ; iModIntro; simpl;auto.
    + iIntros (W0 W1) "% HIW0".
      destruct g.
      * iApply (interp_monotone_nm_nl with "[] [] HIW0");auto.
        iPureIntro. apply related_sts_a_pub_plus_world in a3. apply related_sts_pub_plus_priv_world;auto. 
      * iApply (interp_monotone_nm with "[] [] HIW0");auto.
        iPureIntro. apply related_sts_a_pub_plus_world with a0;auto.
      * destruct (decide (p = O)). 
        { subst. rewrite !fixpoint_interp1_eq. done. }
        iApply (interp_monotone_a with "[] HIW0");auto.
        apply andb_prop in Hconds as [Hp0 Hleb].
        simpl. destruct (isU p) eqn:Hu.
        ** assert (a <= a0)%a as Hle.
           { destruct p; inversion Hu;simpl in Hleb;apply Z.leb_le in Hleb;solve_addr. }
           iPureIntro. apply related_sts_a_weak_world with a0;auto. 
        ** assert (e <= a0)%a as Hle.
           { destruct p; inversion Hu;simpl in Hleb;apply Z.leb_le in Hleb; try solve_addr. }
           iPureIntro. apply related_sts_a_weak_world with a0;auto.
    + assert (pwl p0 = false) as Hpwl.
      { destruct p0;auto; destruct p1;inversion HpwlP1;inversion Hfl'. }
      simpl in Hconds. rewrite Hpwl andb_false_l in Hconds. destruct g;inversion Hconds.
      iIntros (W0 W1) "% HIW0".
      iApply (interp_monotone_nm_nl with "[] [] HIW0");auto.
  - iModIntro. simpl. iIntros (W0 W1) "% HIW0".
    destruct g.
    + by iApply interp_monotone_nm_nl.
    + (*Trick here: value relation leads to a contradiction if p0 is WL, since then its region cannot be permanent*)
      iDestruct ( writeLocalAllowed_valid_cap_implies with "Hvdst" ) as %Ha; eauto.
      rewrite Hstd in Ha. inversion Ha.
    + apply andb_prop in Hconds as [Hp0 Hleb].
      iDestruct ( writeLocalAllowed_valid_cap_implies with "Hvdst" ) as %Ha; eauto.
      rewrite Hstd in Ha. inversion Ha.
Qed.

(* Analogous, but now we have the general monotonicity statement in case an integer z is written *)
Lemma interp_monotone_generalZ (W : WORLD)  (ρ : region_type) (p0 p1 : Perm) (l : Locality)(a2 a1 a0 : Addr) z:
  std W !! a0 = Some ρ →
  withinBounds (p0, l, a2, a1, a0) = true →
  PermFlows p0 p1 →
  ((fixpoint interp1) W) (inr (p0, l, a2, a1, a0)) -∗
  monotonicity_guarantees_region ρ a0 (inl z) p1  (λne Wv : WORLD * (leibnizO Word), (interp Wv.1) Wv.2).
Proof.
  unfold monotonicity_guarantees_region.
  iIntros (Hstd Hwb Hfl') "#Hvdst".
  destruct ρ;auto.
  - destruct (pwl p1) eqn: HpwlP1 ; iModIntro; simpl.
    all: iIntros (W0 W1) "% HIW0".
    all: rewrite !fixpoint_interp1_eq;done. 
  - destruct (pwl p1) eqn: HpwlP1 ; iModIntro; simpl.
    all: iIntros (W0 W1) "% HIW0".
    all: rewrite !fixpoint_interp1_eq;done. 
  - iModIntro. iIntros (W0 W1) "% HIW0".
    iSimpl. rewrite !fixpoint_interp1_eq;done. 
Qed.

End monotone.
