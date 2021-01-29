From iris.algebra Require Import gmap agree auth.
From iris.proofmode Require Import tactics.
From cap_machine Require Export stdpp_extra iris_extra region_invariants region_invariants_transitions.
Import uPred.

Section heap.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          `{MonRef: MonRefG (leibnizO _) CapR_rtc Σ}
          `{MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  (* --------------------------------------------------------------------------------------------------------- *)
  (* --------------------------------------------- REVOCATION ------------------------------------------------ *)
  (* --------------------------------------------------------------------------------------------------------- *)

  (*
     Revocation turns every temporary/monotemporary location state to revoked.
     Revocation is crucial to privately update state: in general,
     region states are only monotone with regards to public future
     world. To do a private update, we must thus revoke all temp
     regions, after which we only have regions that are indeed
     monotone wrt private future world.
   *)


  (* Revocation only changes the states of the standard STS collection *)
  Definition revoke_std_sta : STS_STD → STS_STD :=
    fmap (λ v, match v with
               | Temporary => Revoked
               | Monotemporary => Revoked
               | _ => v
               end).
  Definition revoke W : WORLD := (revoke_std_sta (std W), loc W).

  (* A weaker revocation which only revokes elements from a list *)
  Fixpoint revoke_list_std_sta (l : list Addr) (fs : STS_STD) : STS_STD :=
    match l with
    | [] => fs
    | i :: l' => match fs !! i with
               | Some j => match j with
                          | Temporary => <[i := Revoked]> (revoke_list_std_sta l' fs)
                          | Monotemporary => <[i := Revoked]> (revoke_list_std_sta l' fs)
                          | _ => (revoke_list_std_sta l' fs)
                          end
               | None => (revoke_list_std_sta l' fs)
               end
    end.
  Definition revoke_list l W : WORLD := ((revoke_list_std_sta l (std W)), loc W).

  Lemma related_sts_pub_world_fresh W a ρ :
    a ∉ dom (gset Addr) (std W) →
    related_sts_pub_world W (<s[a:=ρ]s> W).
  Proof.
    rewrite /std. intros Hdom_sta.
    rewrite /related_sts_pub_world /=.
    split;[|apply related_sts_pub_refl].
    rewrite /related_sts_pub. split.
    - rewrite dom_insert_L. set_solver.
    - apply (not_elem_of_dom (D:=gset Addr) W.1 a) in Hdom_sta.
      intros i x y Hx Hy.
      destruct (decide (a = i)).
      + subst. rewrite Hdom_sta in Hx. inversion Hx.
      + rewrite lookup_insert_ne in Hy;auto.
        rewrite Hx in Hy.
        inversion Hy; subst.
        left.
  Qed.

  Lemma related_sts_pub_fresh (W : STS) a ρ i:
    i ∉ dom (gset positive) W.1 →
    i ∉ dom (gset positive) W.2 →
    related_sts_pub W.1 (<[i:=a]> W.1) W.2 (<[i:=ρ]> W.2).
  Proof.
    intros Hdom_sta Hdom_rel.
    rewrite /related_sts_pub. split;[|split;[auto|] ].
    - apply dom_insert_subseteq.
    - apply dom_insert_subseteq.
    - apply not_elem_of_dom in Hdom_sta.
       apply not_elem_of_dom in Hdom_rel.
       intros j r1 r2 r1' r2' r3 r3' Hr Hr'.
       destruct (decide (j = i)).
      + subst. rewrite Hr in Hdom_rel. done.
      + rewrite lookup_insert_ne in Hr'; auto.
        rewrite Hr in Hr'. inversion Hr'. repeat (split;auto).
        intros x y Hx Hy.
        rewrite lookup_insert_ne in Hy;auto.
        rewrite Hx in Hy.
        inversion Hy; inversion Hr'; subst.
        left.
  Qed.

  Lemma related_sts_pub_world_fresh_loc W (i x : positive) r1 r2 :
    i ∉ dom (gset positive) (loc W).1 →
    i ∉ dom (gset positive) (loc W).2 →
    related_sts_pub_world W (W.1,(<[i:=x]> W.2.1, <[i:= (r1,r2)]> W.2.2)).
  Proof.
    rewrite /loc. intros Hdom_sta Hdom_rel.
    rewrite /related_sts_pub_world /=.
    split;[apply related_sts_std_pub_refl|].
    rewrite /related_sts_pub. split;[|split].
    - rewrite dom_insert_L. set_solver.
    - rewrite dom_insert_L. set_solver.
    - apply (not_elem_of_dom (D:=gset positive) W.2.1 i) in Hdom_sta.
      apply (not_elem_of_dom (D:=gset positive) W.2.2 i) in Hdom_rel.
      intros j r1' r2' r1'' r2'' r3' r3''  Hr' Hr''.
      destruct (decide (j = i)).
      + subst. rewrite Hdom_rel in Hr'. inversion Hr'.
      + simplify_map_eq. repeat split;auto.
        intros x' y Hx' Hy. simplify_map_eq. left.
  Qed.

  Lemma related_sts_pub_world_revoked_temp W a :
    (std W) !! a = Some Revoked ∨
    (std W) !! a = Some Temporary →
    related_sts_pub_world W (<s[a:=Temporary]s>W).
  Proof.
    intros Ha.
    rewrite /related_sts_pub_world /=.
    split;[|apply related_sts_pub_refl].
    rewrite /related_sts_pub. split.
    - rewrite dom_insert_L. set_solver.
    - intros i x y Hx Hy.
      destruct (decide (a = i)).
      + subst.
        rewrite Hx in Ha.
        destruct Ha as [Ha | Ha]; inversion Ha.
        ++ rewrite lookup_insert in Hy. inversion Hy.
           right with (Temporary);[|left]. constructor.
        ++ rewrite lookup_insert in Hy. inversion Hy. left.
      + rewrite lookup_insert_ne in Hy;auto.
        rewrite Hx in Hy.
        inversion Hy; subst.
        left.
  Qed.

  Lemma related_sts_pub_world_revoked_monotemp W a :
    (std W) !! a = Some Revoked ∨
    (std W) !! a = Some Monotemporary →
    related_sts_pub_world W (<s[a:=Monotemporary]s>W).
  Proof.
    intros Ha.
    rewrite /related_sts_pub_world /=.
    split;[|apply related_sts_pub_refl].
    rewrite /related_sts_pub. split.
    - rewrite dom_insert_L. set_solver.
    - intros i x y Hx Hy.
      destruct (decide (a = i)).
      + subst.
        rewrite Hx in Ha.
        destruct Ha as [Ha | Ha]; inversion Ha.
        ++ rewrite lookup_insert in Hy. inversion Hy.
           right with (Monotemporary);[|left]. constructor.
        ++ rewrite lookup_insert in Hy. inversion Hy. left.
      + rewrite lookup_insert_ne in Hy;auto.
        rewrite Hx in Hy.
        inversion Hy; subst.
        left.
  Qed.

  (* The following lemma takes a revoked region and makes it Temporary. *)

  Lemma update_region_revoked_temp_pwl E W l p v φ `{∀ Wv, Persistent (φ Wv)} :
    (std W) !! l = Some Revoked →
    p ≠ O → pwl p = true →
    future_pub_plus_mono φ v -∗
    sts_full_world W -∗
    region W -∗
    l ↦ₐ[p] v -∗ φ (W,v) -∗ rel l p φ ={E}=∗ region (<s[l := Temporary ]s>W)
                             ∗ sts_full_world (<s[l := Temporary ]s>W).
  Proof.
    iIntros (Hrev HO Hpwl) "#Hmono Hsts Hreg Hl #Hφ #Hrel".
    rewrite region_eq /region_def.
    iDestruct "Hreg" as (M Mρ) "(Hγrel & #Hdom & #Hdom' & Hpreds)".
    iDestruct "Hdom" as %Hdom. iDestruct "Hdom'" as %Hdom'.
    rewrite RELS_eq /RELS_def.
    rewrite rel_eq /rel_def REL_eq /REL_def. iDestruct "Hrel" as (γ) "[HREL Hsaved]".
    iDestruct (reg_in γrel (M) with "[$Hγrel $HREL]") as %HMeq.
    rewrite /region_map_def HMeq big_sepM_insert; [|by rewrite lookup_delete].
    iDestruct "Hpreds" as "[Hl' Hr]".
    iDestruct "Hl'" as (ρ Hl) "[Hstate Hresources]".
    iDestruct (sts_full_state_std with "Hsts Hstate") as %Hρ.
    rewrite Hrev in Hρ. inversion Hρ as [Hρrev]. subst.
    iMod (sts_update_std _ _ _ Temporary with "Hsts Hstate") as "[Hsts Hstate]".
    assert (related_sts_pub_world W (<s[l := Temporary ]s> W)) as Hrelated.
    { apply related_sts_pub_world_revoked_temp; auto. }
    assert (related_sts_pub_plus_world W (<s[l := Temporary ]s> W)) as Hrelated'.
    { apply related_sts_pub_pub_plus_world;auto. }
    iDestruct (region_map_monotone _ _ _ _ Hrelated with "Hr") as "Hr".
    iDestruct ("Hmono" $! _ _ Hrelated' with "Hφ") as "Hφ'".
    assert (is_Some (M !! l)) as [x Hsome].
    { apply elem_of_gmap_dom. rewrite -Hdom. apply elem_of_gmap_dom. eauto. }
    iDestruct (region_map_delete_nonstatic with "Hr") as "Hr";[intros m;split;intros Hcontr;congruence|].
    iDestruct (region_map_insert_nonstatic Temporary with "Hr") as "Hr";auto.
    iDestruct (big_sepM_delete _ _ l _ Hsome with "[Hl Hstate $Hr]") as "Hr".
    { iExists Temporary. iFrame. iSplitR;[iPureIntro;apply lookup_insert|].
      iExists γ, p, φ. rewrite HMeq lookup_insert in Hsome.
      inversion Hsome. repeat (iSplit; auto). iExists _. iFrame.
      iSplit;auto. rewrite Hpwl. iFrame "#". }
    rewrite /std_update /=. iFrame "Hsts".
    iExists M. iFrame. rewrite -HMeq. iFrame.
    iModIntro. iExists _. iFrame. iPureIntro.
    apply insert_id in Hsome. apply insert_id in Hl. rewrite -Hsome -Hl. split.
    - repeat rewrite dom_insert_L;rewrite Hdom;set_solver.
    - repeat rewrite dom_insert_L;rewrite Hdom';set_solver.
  Qed.

   Lemma update_region_revoked_temp_nwl E W l p v φ `{∀ Wv, Persistent (φ Wv)} :
    (std W) !! l = Some Revoked →
    p ≠ O →
    future_priv_mono φ v -∗
    sts_full_world W -∗
    region W -∗
    l ↦ₐ[p] v -∗ φ (W,v) -∗ rel l p φ ={E}=∗ region (<s[l := Temporary ]s>W)
                             ∗ sts_full_world (<s[l := Temporary ]s>W).
  Proof.
    iIntros (Hrev HO) "#Hmono Hsts Hreg Hl #Hφ #Hrel".
    rewrite region_eq /region_def.
    iDestruct "Hreg" as (M Mρ) "(Hγrel & #Hdom & #Hdom' & Hpreds)".
    iDestruct "Hdom" as %Hdom. iDestruct "Hdom'" as %Hdom'.
    rewrite RELS_eq /RELS_def.
    rewrite rel_eq /rel_def REL_eq /REL_def. iDestruct "Hrel" as (γ) "[HREL Hsaved]".
    iDestruct (reg_in γrel (M) with "[$Hγrel $HREL]") as %HMeq.
    rewrite /region_map_def HMeq big_sepM_insert; [|by rewrite lookup_delete].
    iDestruct "Hpreds" as "[Hl' Hr]".
    iDestruct "Hl'" as (ρ Hl) "[Hstate Hresources]".
    iDestruct (sts_full_state_std with "Hsts Hstate") as %Hρ.
    rewrite Hrev in Hρ. inversion Hρ as [Hρrev]. subst.
    iMod (sts_update_std _ _ _ Temporary with "Hsts Hstate") as "[Hsts Hstate]".
    assert (related_sts_pub_world W (<s[l := Temporary ]s> W)) as Hrelated.
    { apply related_sts_pub_world_revoked_temp; auto. }
    assert (related_sts_priv_world W (<s[l := Temporary ]s> W)) as Hrelated'.
    { apply related_sts_pub_priv_world. auto. }
    iDestruct (region_map_monotone _ _ _ _ Hrelated with "Hr") as "Hr".
    iDestruct (region_map_delete_nonstatic with "Hr") as "Hr"; [intros m;split;intros Hcontr;congruence|].
    iDestruct (region_map_insert_nonstatic Temporary with "Hr") as "Hr";auto.
    iDestruct ("Hmono" $! _ _ Hrelated' with "Hφ") as "Hφ'".
    assert (is_Some (M !! l)) as [x Hsome].
    { apply elem_of_gmap_dom. rewrite -Hdom. apply elem_of_gmap_dom. eauto. }
    iDestruct (big_sepM_delete _ _ l _ Hsome with "[Hl Hstate $Hr]") as "Hr".
    { iExists Temporary. iFrame. iSplitR;[iPureIntro;apply lookup_insert|].
      iExists γ, p, φ. rewrite HMeq lookup_insert in Hsome.
      inversion Hsome. repeat (iSplit; auto). iExists _. iFrame. iSplit;auto.
      destruct (pwl p); iFrame "#".
      iIntros (W' W'' Hrelated''). iModIntro. iIntros "HφW'".
      iApply ("Hmono" with "[] HφW'").
      iPureIntro. apply related_sts_pub_plus_priv_world; auto.
    }
    rewrite /std_update /=. iFrame "Hsts".
    iExists M. iFrame. rewrite -HMeq. iFrame.
    iModIntro. iExists _. iFrame. iPureIntro.
    apply insert_id in Hsome. apply insert_id in Hl. rewrite -Hsome -Hl. split.
    - repeat rewrite dom_insert_L;rewrite Hdom;set_solver.
    - repeat rewrite dom_insert_L;rewrite Hdom';set_solver.
  Qed.

  Lemma update_region_revoked_monotemp_pwl E W l p v φ `{∀ Wv, Persistent (φ Wv)} :
    (std W) !! l = Some Revoked →
    p ≠ O → pwl p = true →
    future_pub_a_mono l φ v -∗
    sts_full_world W -∗
    region W -∗
    l ↦ₐ[p] v -∗ φ (W,v) -∗ rel l p φ ={E}=∗ region (<s[l := Monotemporary ]s>W)
                             ∗ sts_full_world (<s[l := Monotemporary ]s>W).
  Proof.
    iIntros (Hrev HO Hpwl) "#Hmono Hsts Hreg Hl #Hφ #Hrel".
    rewrite region_eq /region_def.
    iDestruct "Hreg" as (M Mρ) "(Hγrel & #Hdom & #Hdom' & Hpreds)".
    iDestruct "Hdom" as %Hdom. iDestruct "Hdom'" as %Hdom'.
    rewrite RELS_eq /RELS_def.
    rewrite rel_eq /rel_def REL_eq /REL_def. iDestruct "Hrel" as (γ) "[HREL Hsaved]".
    iDestruct (reg_in γrel (M) with "[$Hγrel $HREL]") as %HMeq.
    rewrite /region_map_def HMeq big_sepM_insert; [|by rewrite lookup_delete].
    iDestruct "Hpreds" as "[Hl' Hr]".
    iDestruct "Hl'" as (ρ Hl) "[Hstate Hresources]".
    iDestruct (sts_full_state_std with "Hsts Hstate") as %Hρ.
    rewrite Hrev in Hρ. inversion Hρ as [Hρrev]. subst.
    iMod (sts_update_std _ _ _ Monotemporary with "Hsts Hstate") as "[Hsts Hstate]".
    assert (related_sts_pub_world W (<s[l := Monotemporary ]s> W)) as Hrelated.
    { apply related_sts_pub_world_revoked_monotemp; auto. }
    assert (related_sts_a_world W (<s[l := Monotemporary ]s> W) l) as Hrelated'.
    { apply related_sts_pub_a_world; auto. }
    iDestruct (region_map_monotone _ _ _ _ Hrelated with "Hr") as "Hr".
    iDestruct ("Hmono" $! _ _ Hrelated' with "Hφ") as "Hφ'".
    assert (is_Some (M !! l)) as [x Hsome].
    { apply elem_of_gmap_dom. rewrite -Hdom. apply elem_of_gmap_dom. eauto. }
    iDestruct (region_map_delete_nonstatic with "Hr") as "Hr"; [intros m;split;intros Hcontr;congruence|].
    iDestruct (region_map_insert_nonstatic Monotemporary with "Hr") as "Hr";auto.
    iDestruct (big_sepM_delete _ _ l _ Hsome with "[Hl Hstate $Hr]") as "Hr".
    { iExists Monotemporary. iFrame. iSplitR;[iPureIntro;apply lookup_insert|].
      iExists γ, p, φ. rewrite HMeq lookup_insert in Hsome.
      inversion Hsome. repeat (iSplit; auto). iExists _. iFrame.
      iSplit;auto. rewrite Hpwl. iFrame "#". }
    rewrite /std_update /=. iFrame "Hsts".
    iExists M. iFrame. rewrite -HMeq. iFrame.
    iModIntro. iExists _. iFrame. iPureIntro.
    apply insert_id in Hsome. apply insert_id in Hl. rewrite -Hsome -Hl. split.
    - repeat rewrite dom_insert_L;rewrite Hdom;set_solver.
    - repeat rewrite dom_insert_L;rewrite Hdom';set_solver.
  Qed.

   Lemma update_region_revoked_monotemp_nwl E W l p v φ `{∀ Wv, Persistent (φ Wv)} :
    (std W) !! l = Some Revoked →
    p ≠ O →
    future_priv_mono φ v -∗
    sts_full_world W -∗
    region W -∗
    l ↦ₐ[p] v -∗ φ (W,v) -∗ rel l p φ ={E}=∗ region (<s[l := Monotemporary ]s>W)
                             ∗ sts_full_world (<s[l := Monotemporary ]s>W).
  Proof.
    iIntros (Hrev HO) "#Hmono Hsts Hreg Hl #Hφ #Hrel".
    rewrite region_eq /region_def.
    iDestruct "Hreg" as (M Mρ) "(Hγrel & #Hdom & #Hdom' & Hpreds)".
    iDestruct "Hdom" as %Hdom. iDestruct "Hdom'" as %Hdom'.
    rewrite RELS_eq /RELS_def.
    rewrite rel_eq /rel_def REL_eq /REL_def. iDestruct "Hrel" as (γ) "[HREL Hsaved]".
    iDestruct (reg_in γrel (M) with "[$Hγrel $HREL]") as %HMeq.
    rewrite /region_map_def HMeq big_sepM_insert; [|by rewrite lookup_delete].
    iDestruct "Hpreds" as "[Hl' Hr]".
    iDestruct "Hl'" as (ρ Hl) "[Hstate Hresources]".
    iDestruct (sts_full_state_std with "Hsts Hstate") as %Hρ.
    rewrite Hrev in Hρ. inversion Hρ as [Hρrev]. subst.
    iMod (sts_update_std _ _ _ Monotemporary with "Hsts Hstate") as "[Hsts Hstate]".
    assert (related_sts_pub_world W (<s[l := Monotemporary ]s> W)) as Hrelated.
    { apply related_sts_pub_world_revoked_monotemp; auto. }
    assert (related_sts_priv_world W (<s[l := Monotemporary ]s> W)) as Hrelated'.
    { apply related_sts_pub_priv_world. auto. }
    iDestruct (region_map_monotone _ _ _ _ Hrelated with "Hr") as "Hr".
    iDestruct (region_map_delete_nonstatic with "Hr") as "Hr"; [intros m;split;intros Hcontr;congruence|].
    iDestruct (region_map_insert_nonstatic Monotemporary with "Hr") as "Hr";auto.
    iDestruct ("Hmono" $! _ _ Hrelated' with "Hφ") as "Hφ'".
    assert (is_Some (M !! l)) as [x Hsome].
    { apply elem_of_gmap_dom. rewrite -Hdom. apply elem_of_gmap_dom. eauto. }
    iDestruct (big_sepM_delete _ _ l _ Hsome with "[Hl Hstate $Hr]") as "Hr".
    { iExists Monotemporary. iFrame. iSplitR;[iPureIntro;apply lookup_insert|].
      iExists γ, p, φ. rewrite HMeq lookup_insert in Hsome.
      inversion Hsome. repeat (iSplit; auto). iExists _. iFrame. iSplit;auto.
      destruct (pwl p); iFrame "#".
      iIntros (W' W'' Hrelated''). iModIntro. iIntros "HφW'".
      iApply ("Hmono" with "[] HφW'").
      iPureIntro. apply related_sts_pub_plus_priv_world.
      eapply related_sts_a_pub_plus_world;eauto.
    }
    rewrite /std_update /=. iFrame "Hsts".
    iExists M. iFrame. rewrite -HMeq. iFrame.
    iModIntro. iExists _. iFrame. iPureIntro.
    apply insert_id in Hsome. apply insert_id in Hl. rewrite -Hsome -Hl. split.
    - repeat rewrite dom_insert_L;rewrite Hdom;set_solver.
    - repeat rewrite dom_insert_L;rewrite Hdom';set_solver.
  Qed.

  (* -------------------------------------------------------------------------- *)
  (* ------------------------- LEMMAS ABOUT REVOKE ---------------------------- *)

  Definition revoke_i i :=
    match i with
    | Temporary => Revoked
    | Monotemporary => Revoked
    | _ => i
    end.

  Lemma revoke_list_std_sta_spec (l : list Addr) :
    forall (Wstd_sta : STS_STD) (i : Addr),
      (revoke_list_std_sta l Wstd_sta) !! i = match Wstd_sta !! i with
                                              | None => None
                                              | Some j => Some (if List.In_dec addr_eq_dec i l then revoke_i j else j)
                                              end.
  Proof.
    induction l; intros.
    - simpl. destruct (Wstd_sta !! i); auto.
    - case_eq (Wstd_sta !! i); [intros j H3 | intros H3].
      { destruct (in_dec addr_eq_dec i (a :: l)).
        + destruct i0 as [A | A].
          * subst i. simpl. rewrite H3.
            destruct j;[rewrite lookup_insert;auto|rewrite lookup_insert;auto|rewrite IHl H3; destruct (in_dec addr_eq_dec a l);auto..].
          * simpl.
            case_eq (Wstd_sta !! a); intros.
            { destruct (decide (Temporary = r)).
              - subst. destruct (decide (i = a)).
                { subst;rewrite lookup_insert. by simplify_map_eq. }
                { rewrite lookup_insert_ne;auto. rewrite IHl H3.
                  destruct (in_dec addr_eq_dec i l);[auto|contradiction]. }
              - destruct (decide (Monotemporary = r)). 
                { subst. destruct (decide (i = a)).
                  - subst. rewrite lookup_insert. by simplify_map_eq.
                  - rewrite lookup_insert_ne//. rewrite IHl H3.
                    destruct (in_dec addr_eq_dec i l);[auto|contradiction]. }
                destruct r; try contradiction; rewrite IHl H3;
                destruct (in_dec addr_eq_dec i l); tauto. }
            { rewrite IHl H3.
              destruct (in_dec addr_eq_dec i l); tauto. }
        + simpl. case_eq (Wstd_sta !! a); intros.
          * destruct (decide (Temporary = r)).
            { subst. rewrite lookup_insert_ne.
              - rewrite IHl H3.
                destruct (in_dec addr_eq_dec i l); auto.
                elim n. right; auto.
              - red; intro. elim n; left; auto. }
            { destruct (decide (Monotemporary = r)). 
              { subst. rewrite lookup_insert_ne.
                rewrite IHl H3. destruct (in_dec addr_eq_dec i l); auto.
                elim n. right; auto. red; intro. elim n; left; auto. }
              destruct r; try contradiction; rewrite IHl H3;
              destruct (in_dec addr_eq_dec i l); auto;
              elim n; right; auto. }
          * rewrite IHl H3.
            destruct (in_dec addr_eq_dec i l); auto.
            elim n; right; auto. }
      { simpl. case_eq (Wstd_sta !! a); intros.
        - destruct (addr_eq_dec i a); try congruence.
          destruct (decide (Temporary = r)); intros.
          + subst. rewrite lookup_insert_ne; auto.
            rewrite IHl H3; auto.
          + destruct (decide (Monotemporary = r)); intros.
            subst. rewrite lookup_insert_ne;auto.
            rewrite IHl H3;auto.
            destruct r; try contradiction; rewrite IHl H3; auto.
        - rewrite IHl H3; auto. }
  Qed.

  Lemma revoke_list_not_elem_of_lookup i l m :
    i ∉ l →
    (revoke_list_std_sta l m) !! i = m !! i.
  Proof.
    rewrite revoke_list_std_sta_spec.
    intros; destruct (m !! i) as [x|] eqn:Hm; auto.
    destruct (in_dec addr_eq_dec i l); auto.
    eapply elem_of_list_In in i0. by simplify_map_eq.
  Qed.

  Lemma revoke_list_dom_std_sta (Wstd_sta : gmap Addr region_type) :
    revoke_std_sta Wstd_sta = revoke_list_std_sta (map_to_list Wstd_sta).*1 Wstd_sta.
  Proof.
    eapply (map_leibniz (M:=gmap Addr)). red. red. intros.
    rewrite revoke_list_std_sta_spec /revoke_std_sta lookup_fmap /revoke_i /=.
    destruct (Wstd_sta !! i) as [x|] eqn:Hwstd; rewrite Hwstd /=; auto.
    destruct (decide (Temporary = x)).
    - subst x.
      eapply elem_of_map_to_list in Hwstd as Hx.
      destruct (in_dec addr_eq_dec i (map_to_list Wstd_sta).*1); auto.
      apply leibniz_equiv_iff. auto.
      elim n. eapply elem_of_list_In.
      eapply elem_of_list_fmap. exists (i, Temporary).
      split; auto.
    - destruct (decide (Monotemporary = x)).
      + subst x. eapply elem_of_map_to_list in Hwstd as Hx.
        destruct (in_dec addr_eq_dec i (map_to_list Wstd_sta).*1); auto.
        apply leibniz_equiv_iff. 
        elim n0. eapply elem_of_list_In.
        eapply elem_of_list_fmap. exists (i, Monotemporary).
        split; auto.
      + destruct (in_dec addr_eq_dec i (map_to_list Wstd_sta).*1); auto.
        destruct x;auto; try contradiction.
    - apply leibniz_equiv_iff. auto.
      Unshelve. apply _.
  Qed.

  Lemma revoke_list_dom W :
    revoke W = revoke_list (map_to_list W.1).*1 W.
  Proof.
    by rewrite /revoke_list /= -revoke_list_dom_std_sta /revoke.
  Qed.

  Lemma revoke_list_lookup_Some Wstd_sta l (a : Addr) :
    is_Some (Wstd_sta !! a) ↔ is_Some ((revoke_list_std_sta l Wstd_sta) !! a).
  Proof.
    rewrite revoke_list_std_sta_spec.
    destruct (Wstd_sta !! a); split; eauto.
  Qed.

  Lemma revoke_lookup_Some W (i : Addr) :
    is_Some ((std W) !! i) ↔ is_Some ((std (revoke W)) !! i).
  Proof.
    rewrite revoke_list_dom /revoke_list /=.
    rewrite revoke_list_std_sta_spec.
    destruct (std W !! i); eauto.
    rewrite !is_Some_alt; auto.
  Qed.

  Lemma revoke_lookup_None W (i : Addr) :
    (std W) !! i = None ↔ (std (revoke W)) !! i = None.
  Proof.
    split.
    - intros Hnone. apply eq_None_not_Some.
      intros Hcontr. apply revoke_lookup_Some in Hcontr.
      apply eq_None_not_Some in Hcontr; auto.
    - intros Hnone. apply eq_None_not_Some.
      intros Hcontr. apply revoke_lookup_Some in Hcontr.
      apply eq_None_not_Some in Hcontr; auto.
  Qed.

  Lemma revoke_std_sta_lookup_Some Wstd_sta (i : Addr) :
    is_Some (Wstd_sta !! i) ↔ is_Some (revoke_std_sta Wstd_sta !! i).
  Proof.
    split; intros Hi.
    - assert (std (Wstd_sta, (∅,∅)) = Wstd_sta) as Heq;auto.
      rewrite -Heq in Hi.
      apply (revoke_lookup_Some ((Wstd_sta),∅) i) in Hi.
      auto.
    - assert (std (Wstd_sta, (∅,∅)) = Wstd_sta) as <-;auto.
      apply (revoke_lookup_Some ((Wstd_sta),∅) i).
      auto.
  Qed.

  Lemma revoke_lookup_Temp Wstd_sta i :
    (Wstd_sta !! i = Some Temporary) →
    (revoke_std_sta Wstd_sta) !! i = Some Revoked.
  Proof.
    rewrite revoke_list_dom_std_sta. intros Hsome.
    rewrite revoke_list_std_sta_spec Hsome.
    destruct (in_dec addr_eq_dec i (map_to_list Wstd_sta).*1) eqn:HH.
    - rewrite /revoke_i HH. auto.
    - elim n. eapply elem_of_list_In.
      eapply map_to_list_fst. eexists; by apply elem_of_map_to_list.
  Qed.

  Lemma revoke_lookup_Monotemp Wstd_sta i :
    (Wstd_sta !! i = Some Monotemporary) →
    (revoke_std_sta Wstd_sta) !! i = Some Revoked.
  Proof.
    rewrite revoke_list_dom_std_sta. intros Hsome.
    rewrite revoke_list_std_sta_spec Hsome.
    destruct (in_dec addr_eq_dec i (map_to_list Wstd_sta).*1) eqn:HH.
    - rewrite /revoke_i HH. auto.
    - elim n. eapply elem_of_list_In.
      eapply map_to_list_fst. eexists; by apply elem_of_map_to_list.
  Qed.

  Lemma revoke_lookup_Revoked Wstd_sta i :
    (Wstd_sta !! i = Some Revoked) →
    (revoke_std_sta Wstd_sta) !! i = Some Revoked.
  Proof.
    rewrite revoke_list_dom_std_sta. intros Hsome.
    rewrite revoke_list_std_sta_spec Hsome.
    destruct (in_dec addr_eq_dec i (map_to_list Wstd_sta).*1) eqn:HH.
    - rewrite /revoke_i HH. auto.
    - elim n. eapply elem_of_list_In.
      eapply map_to_list_fst. eexists; by apply elem_of_map_to_list.
  Qed.

  Lemma revoke_lookup_Perm Wstd_sta i :
    (Wstd_sta !! i = Some Permanent) →
    (revoke_std_sta Wstd_sta) !! i = Some Permanent.
  Proof.
    rewrite revoke_list_dom_std_sta. intros Hsome.
    rewrite revoke_list_std_sta_spec Hsome.
    destruct (in_dec addr_eq_dec i (map_to_list Wstd_sta).*1) eqn:HH.
    - rewrite /revoke_i HH. auto.
    - elim n. eapply elem_of_list_In.
      eapply map_to_list_fst. eexists; by apply elem_of_map_to_list.
  Qed.

  Lemma revoke_lookup_Static Wstd_sta i m :
    (Wstd_sta !! i = Some (Static m)) →
    (revoke_std_sta Wstd_sta) !! i = Some (Static m).
  Proof.
    rewrite revoke_list_dom_std_sta. intros Hsome.
    rewrite revoke_list_std_sta_spec Hsome.
    destruct (in_dec addr_eq_dec i (map_to_list Wstd_sta).*1) eqn:HH.
    - rewrite /revoke_i HH. auto.
    - elim n. eapply elem_of_list_In.
      eapply map_to_list_fst. eexists; by apply elem_of_map_to_list.
  Qed.

  Lemma revoke_lookup_Monostatic Wstd_sta i m :
    (Wstd_sta !! i = Some (Monostatic m)) →
    (revoke_std_sta Wstd_sta) !! i = Some (Monostatic m).
  Proof.
    rewrite revoke_list_dom_std_sta. intros Hsome.
    rewrite revoke_list_std_sta_spec Hsome.
    destruct (in_dec addr_eq_dec i (map_to_list Wstd_sta).*1) eqn:HH.
    - rewrite /revoke_i HH. auto.
    - elim n. eapply elem_of_list_In.
      eapply map_to_list_fst. eexists; by apply elem_of_map_to_list.
  Qed.

  Lemma revoke_lookup_Uninitialized Wstd_sta i w :
    (Wstd_sta !! i = Some (Uninitialized w)) →
    (revoke_std_sta Wstd_sta) !! i = Some (Uninitialized w).
  Proof.
    rewrite revoke_list_dom_std_sta. intros Hsome.
    rewrite revoke_list_std_sta_spec Hsome.
    destruct (in_dec addr_eq_dec i (map_to_list Wstd_sta).*1) eqn:HH.
    - rewrite /revoke_i HH. auto.
    - elim n. eapply elem_of_list_In.
      eapply map_to_list_fst. eexists; by apply elem_of_map_to_list.
  Qed.

  Lemma revoke_list_lookup_non_temp (Wstd_sta : STS_STD) (l : list Addr) (i : Addr) (ρ : region_type) :
    i ∈ l →
    (revoke_list_std_sta l Wstd_sta) !! i = Some ρ → ρ ≠ Temporary ∧ ρ ≠ Monotemporary.
  Proof.
    intros Hin Hsome.
    rewrite revoke_list_std_sta_spec in Hsome.
    destruct (Wstd_sta !! i); try congruence.
    eapply elem_of_list_In in Hin.
    destruct (in_dec addr_eq_dec i l); try tauto.
    inv Hsome. rewrite /revoke_i.
    destruct (decide (Temporary = r)).
    - destruct r;auto;contradiction.
    - destruct (decide (Monotemporary = r)).
      + destruct r;auto;contradiction.
      + destruct r;[contradiction|auto..].
  Qed.

  Lemma revoke_std_sta_lookup_non_temp Wstd_sta (i : Addr) (ρ : region_type) :
    (revoke_std_sta Wstd_sta) !! i = Some ρ → ρ ≠ Temporary ∧ ρ ≠ Monotemporary.
  Proof.
    intros Hin.
    rewrite revoke_list_dom_std_sta in Hin.
    apply revoke_list_lookup_non_temp with Wstd_sta ((map_to_list Wstd_sta).*1) i; auto.
    rewrite /std /= in Hin.
    assert (is_Some (Wstd_sta !! i)) as [x Hsome].
    { rewrite revoke_list_std_sta_spec in Hin.
      destruct (Wstd_sta !! i); eauto. }
    apply map_to_list_fst. exists x.
    apply elem_of_map_to_list. done.
  Qed.

  Lemma revoke_lookup_non_temp W (i : Addr) (ρ : region_type) :
    (std (revoke W)) !! i = Some ρ → ρ ≠ Temporary ∧ ρ ≠ Monotemporary.
  Proof.
    intros Hin.
    rewrite revoke_list_dom in Hin.
    apply revoke_list_lookup_non_temp with W.1 ((map_to_list W.1).*1) i; auto.
    rewrite /std /= in Hin.
    assert (is_Some (W.1 !! i)) as [x Hsome].
    { rewrite revoke_list_lookup_Some. eauto. }
    apply map_to_list_fst. exists x.
    apply elem_of_map_to_list. done.
  Qed.

  Lemma revoke_monotone_dom (Wstd_sta Wstd_sta' : gmap Addr region_type) :
    dom (gset Addr) Wstd_sta ⊆ dom (gset Addr) Wstd_sta' →
    dom (gset Addr) (revoke_std_sta Wstd_sta) ⊆ dom (gset Addr) (revoke_std_sta Wstd_sta').
  Proof.
    intros Hdom.
    induction Wstd_sta using map_ind.
    - rewrite /revoke_std_sta fmap_empty dom_empty.
      apply empty_subseteq.
    - apply elem_of_subseteq in Hdom.
      assert (is_Some (Wstd_sta' !! i)) as Hsome.
      { apply elem_of_gmap_dom;apply Hdom.
        apply elem_of_gmap_dom. rewrite lookup_insert. eauto. }
      apply elem_of_subseteq. intros j Hj.
      apply elem_of_gmap_dom in Hj; apply elem_of_gmap_dom.
      destruct (decide (i=j));subst.
      { by apply (revoke_std_sta_lookup_Some Wstd_sta'). }
      { rewrite -revoke_std_sta_lookup_Some.
        apply elem_of_gmap_dom. apply elem_of_subseteq in Hdom. apply Hdom.
        apply elem_of_gmap_dom. rewrite lookup_insert_ne;auto.
        apply (revoke_std_sta_lookup_Some) in Hj. rewrite lookup_insert_ne in Hj;auto.
      }
  Qed.

  Lemma revoke_monotone_lookup (Wstd_sta Wstd_sta' : gmap Addr region_type) i :
    Wstd_sta !! i = Wstd_sta' !! i →
    revoke_std_sta Wstd_sta !! i = revoke_std_sta Wstd_sta' !! i.
  Proof.
    intros Heq.
    induction Wstd_sta using map_ind.
    - rewrite lookup_empty in Heq.
      rewrite /revoke_std_sta fmap_empty lookup_empty lookup_fmap.
      destruct (Wstd_sta' !! i) eqn:Hnone; inversion Heq.
      done.
    - destruct (decide (i0 = i)).
      + subst. rewrite lookup_insert in Heq.
        rewrite /revoke_std_sta fmap_insert lookup_fmap lookup_insert -Heq /=.
        done.
      + rewrite lookup_insert_ne in Heq;auto.
        specialize (IHWstd_sta Heq).
        rewrite /revoke_std_sta fmap_insert lookup_insert_ne;auto.
  Qed.

  Lemma revoke_monotone_lookup_same (Wstd_sta : gmap Addr region_type) i :
    Wstd_sta !! i ≠ Some Temporary ->
    Wstd_sta !! i ≠ Some Monotemporary →
    revoke_std_sta Wstd_sta !! i = Wstd_sta !! i.
  Proof.
    intros Hneq Hneq'.
    induction Wstd_sta using map_ind.
    - rewrite /revoke_std_sta lookup_empty lookup_fmap. eauto.
    - destruct (decide (i0 = i)).
      + subst. rewrite lookup_insert in Hneq.
        rewrite /revoke_std_sta fmap_insert lookup_insert lookup_insert /=.
        f_equiv.
        destruct x eqn:Hcontr; auto.
        contradiction. simplify_map_eq. 
      + simplify_map_eq. 
        rewrite /revoke_std_sta fmap_insert lookup_insert_ne;auto.
  Qed.

  Lemma revoke_monotone_lookup_same' (W:WORLD) (i: Addr) :
    std W !! i ≠ Some Temporary ->
    std W !! i ≠ Some Monotemporary ->
    std (revoke W) !! i = std W !! i.
  Proof. cbn. eauto using revoke_monotone_lookup_same. Qed.

  Lemma anti_revoke_lookup_Revoked Wstd_sta i :
    (revoke_std_sta Wstd_sta) !! i = Some Revoked ->
    (Wstd_sta !! i = Some Revoked) ∨ (Wstd_sta !! i = Some Temporary) ∨ (Wstd_sta !! i = Some Monotemporary).
  Proof.
    intros Hrev.
    assert (is_Some (Wstd_sta !! i)) as [x Hx];[apply revoke_std_sta_lookup_Some;eauto|].
    destruct x;subst;auto;
      rewrite revoke_monotone_lookup_same in Hrev;auto;rewrite Hx;auto.
  Qed.

  Lemma revoke_dom_eq Wstd_sta :
    dom (gset Addr) Wstd_sta = dom (gset Addr) (revoke_std_sta Wstd_sta).
  Proof.
    apply gset_leibniz. split.
    - intros Hin.
      apply elem_of_gmap_dom. apply elem_of_gmap_dom in Hin.
      rewrite -revoke_std_sta_lookup_Some.
      eauto.
    - intros Hin.
      apply elem_of_gmap_dom. apply elem_of_gmap_dom in Hin.
      rewrite revoke_std_sta_lookup_Some.
      eauto.
  Qed.

  (* --------------------------------------------------------------------------------- *)
  (* ----------- A REVOKED REGION IS MONOTONE WRT PRIVATE FUTURΕ WORLDS -------------- *)

  Lemma std_rel_priv_Static x g :
    std_rel_priv (Static g) x → x = Static g.
  Proof.
    intros Hrel.
    inversion Hrel; done.
  Qed.

  Lemma std_rel_priv_rtc_Static x y g :
    x = Static g →
    rtc std_rel_priv x y → y = Static g.
  Proof.
    intros Hx Hrtc.
    induction Hrtc ;auto.
    subst. apply IHHrtc. apply std_rel_priv_Static; eauto.
  Qed.

  Lemma std_rel_priv_monotone x y x' y' Wstd_sta Wstd_sta' i :
    Wstd_sta !! i = Some x -> Wstd_sta' !! i = Some y ->
    (revoke_std_sta Wstd_sta) !! i = Some x' → (revoke_std_sta Wstd_sta') !! i = Some y' →
    rtc (std_rel_priv) x y →
    rtc (λ x0 y0 : region_type, std_rel_pub x0 y0 ∨ std_rel_pub_plus x0 y0 ∨ std_rel_priv x0 y0) x' y'.
  Proof.
    intros Hx Hy Hx' Hy' Hrtc.
    induction Hrtc as [Hrefl | j k h Hjk].
    - simplify_eq. rewrite -Hx in Hy.
      apply revoke_monotone_lookup in Hy.
      rewrite Hx' Hy' in Hy. inversion Hy. left.
    - destruct j,k; inversion Hjk; try discriminate; auto.
      + apply std_rel_priv_rtc_Permanent in Hrtc; auto; subst.
        apply revoke_lookup_Temp in Hx as Hxtemp.
        apply revoke_lookup_Perm in Hy as Hyperm.
        rewrite Hxtemp in Hx'. rewrite Hyperm in Hy'.
        inversion Hx'; inversion Hy'; simplify_eq.
        right with Permanent; [|left]. left. constructor.
      + subst.
        apply revoke_lookup_Temp in Hx as Hxtemp.
        rewrite Hxtemp in Hx'. inversion Hx'; simplify_eq.
        destruct h.
        * apply revoke_lookup_Temp in Hy as Hytemp.
          rewrite Hytemp in Hy'. inversion Hy'; simplify_eq.
          left.
        * apply revoke_lookup_Monotemp in Hy as Hytemp.
          rewrite Hytemp in Hy'. inversion Hy'; simplify_eq.
          left.
        * apply revoke_lookup_Perm in Hy as Hytemp.
          rewrite Hytemp in Hy'. inversion Hy'; simplify_eq.
          right with Permanent; [|left].
          left. constructor.
        * apply revoke_lookup_Revoked in Hy as Hytemp.
          rewrite Hytemp in Hy'. inversion Hy'; simplify_eq.
          left.
        * apply revoke_lookup_Static in Hy as Hytemp.
          rewrite Hytemp in Hy'. inversion Hy'; simplify_eq.
          apply rtc_or_intro_l. apply rtc_or_intro_l. auto.
        * apply revoke_lookup_Monostatic in Hy as Hytemp.
          rewrite Hytemp in Hy'. inversion Hy'; simplify_eq.
          apply rtc_or_intro_l. apply rtc_or_intro_l. auto.
        * apply revoke_lookup_Uninitialized in Hy as Hytemp.
          rewrite Hytemp in Hy'. inversion Hy'; simplify_eq.
          apply rtc_or_intro_l. apply rtc_or_intro_l. auto.
      + subst.
        apply revoke_lookup_Temp in Hx as Hxtemp.
        rewrite Hxtemp in Hx'. inversion Hx'; simplify_eq.
        destruct h.
        * apply revoke_lookup_Temp in Hy as Hytemp.
          rewrite Hytemp in Hy'. inversion Hy'; simplify_eq.
          left.
        * apply revoke_lookup_Monotemp in Hy as Hytemp.
          rewrite Hytemp in Hy'. inversion Hy'; simplify_eq.
          left.
        * apply revoke_lookup_Perm in Hy as Hytemp.
          rewrite Hytemp in Hy'. inversion Hy'; simplify_eq.
          right with Permanent; [|left]. left. constructor.
        * apply revoke_lookup_Revoked in Hy as Hytemp.
          rewrite Hytemp in Hy'. inversion Hy'; simplify_eq.
          left.
        * apply revoke_lookup_Static in Hy as Hytemp.
          rewrite Hytemp in Hy'. inversion Hy'; simplify_eq.
          right with Temporary.
          { left. constructor. }
          right with (Static g0);[|by left].
          right. right. constructor.
        * apply revoke_lookup_Monostatic in Hy as Hytemp.
          rewrite Hytemp in Hy'. inversion Hy'; simplify_eq.
          right with Monotemporary.
          { left. constructor. }
          right with (Monostatic g0);[|by left].
          right. right. constructor.
        * apply revoke_lookup_Uninitialized in Hy as Hytemp.
          rewrite Hytemp in Hy'. inversion Hy'; simplify_eq.
          right with Monotemporary.
          { left. constructor. }
          right with (Uninitialized w);[|by left].
          right. left. constructor.
      + apply std_rel_priv_rtc_Temporary in Hrtc as [-> | [-> | [-> | [? ->] ] ] ]; auto; subst.
        * apply revoke_lookup_Monotemp in Hx as Hxtemp.
          apply revoke_lookup_Temp in Hy as Hytemp.
          simplify_eq. left.
        * apply revoke_lookup_Monotemp in Hx as Hxtemp.
          apply revoke_lookup_Perm in Hy as Hytemp.
          simplify_eq. right with Permanent.
          left. constructor. left.
        * apply revoke_lookup_Monotemp in Hx as Hxtemp.
          apply revoke_lookup_Revoked in Hy as Hytemp.
          simplify_eq. left.
        * apply revoke_lookup_Monotemp in Hx as Hxtemp.
          apply revoke_lookup_Static in Hy as Hytemp.
          simplify_eq. right with Temporary.
          left;constructor. eright;[|left]. right;right;constructor.
      + apply std_rel_priv_rtc_Revoked in Hrtc;auto;subst.
        apply revoke_lookup_Monotemp in Hx as Hxtemp.
        apply revoke_lookup_Revoked in Hy as Hyperm.
        simplify_eq. left.
      + subst. eapply std_rel_priv_rtc_Monostatic in Hrtc;auto;subst.
        apply revoke_lookup_Monotemp in Hx as Hxtemp.
        apply revoke_lookup_Monostatic in Hy as Hyperm.
        simplify_eq. right with Monotemporary.
        left. constructor. eright;[|left].
        right. right. constructor.
  Qed.

  Lemma std_rel_pub_monotone x y x' y' Wstd_sta Wstd_sta' i :
    Wstd_sta !! i = Some x -> Wstd_sta' !! i = Some y ->
    (revoke_std_sta Wstd_sta) !! i = Some x' → (revoke_std_sta Wstd_sta') !! i = Some y' →
    rtc std_rel_pub x y →
    rtc (λ x0 y0 : region_type, std_rel_pub x0 y0 ∨ std_rel_pub_plus x0 y0 ∨ std_rel_priv x0 y0) x' y'.
  Proof.
    intros Hx Hy Hx' Hy' Hrtc.
    induction Hrtc as [Hrefl | j k h Hjk].
    - simplify_eq. rewrite -Hx in Hy.
      apply revoke_monotone_lookup in Hy.
      rewrite Hx' Hy' in Hy. inversion Hy. left.
    - destruct j,k; inversion Hjk; try discriminate; auto.
      + apply std_rel_pub_rtc_Temporary in Hrtc; auto. subst.
        apply revoke_lookup_Revoked in Hx as Hxtemp.
        apply revoke_lookup_Temp in Hy as Hyperm.
        rewrite Hxtemp in Hx'. rewrite Hyperm in Hy'.
        inversion Hx'; inversion Hy'; simplify_eq.
        left.
      + apply std_rel_pub_rtc_Monotemporary in Hrtc; auto. subst.
        apply revoke_lookup_Revoked in Hx as Hxtemp.
        apply revoke_lookup_Monotemp in Hy as Hyperm.
        simplify_eq. left.
      + apply std_rel_pub_rtc_Permanent in Hrtc; auto. subst.
        apply revoke_lookup_Revoked in Hx as Hxtemp.
        apply revoke_lookup_Perm in Hy as Hyperm.
        simplify_eq. eright;[|left]. left. constructor.
      + apply std_rel_pub_rtc_Temporary in Hrtc; auto. subst.
        apply revoke_lookup_Static in Hx as Hxtemp.
        apply revoke_lookup_Temp in Hy as Hyperm.
        simplify_eq. right with Temporary. left;constructor.
        eright;[|left]. right. right. constructor.
      + subst. apply std_rel_pub_rtc_Monotemporary in Hrtc; auto. subst.
        apply revoke_lookup_Monostatic in Hx as Hxtemp.
        apply revoke_lookup_Monotemp in Hy as Hyperm.
        simplify_eq. right with Monotemporary. left;constructor.
        eright;[|left]. right. right. constructor.
      + subst. apply std_rel_pub_rtc_Monotemporary in Hrtc; auto. subst.
        apply revoke_lookup_Uninitialized in Hx as Hxtemp.
        apply revoke_lookup_Monotemp in Hy as Hyperm.
        simplify_eq. right with Monotemporary. left;constructor.
        eright;[|left]. right. right. constructor.
  Qed.

  Ltac revoke_i W1 W2 i :=
    (match goal with
     | H : W1 !! i = Some _
           , H' : W2 !! i = Some _ |- _ =>
       let Hxtemp := fresh "Hxtemp" in
       let Hytemp := fresh "Hytemp" in
       try (apply revoke_lookup_Temp in H as Hxtemp);
       try (apply revoke_lookup_Monotemp in H as Hxtemp);
       try (apply revoke_lookup_Perm in H as Hxtemp);
       try (apply revoke_lookup_Revoked in H as Hxtemp);
       try (eapply revoke_lookup_Static in H as Hxtemp);
       try (eapply revoke_lookup_Uninitialized in H as Hxtemp);
       try (eapply revoke_lookup_Monostatic in H as Hxtemp);
       try (apply revoke_lookup_Temp in H' as Hytemp);
       try (apply revoke_lookup_Monotemp in H' as Hytemp);
       try (apply revoke_lookup_Perm in H' as Hytemp);
       try (eapply revoke_lookup_Static in H' as Hytemp);
       try (eapply revoke_lookup_Uninitialized in H' as Hytemp);
       try (eapply revoke_lookup_Monostatic in H' as Hytemp);
       try (apply revoke_lookup_Revoked in H' as Hytemp);simplify_eq
     end).

  Lemma std_rel_monotone x y x' y' Wstd_sta Wstd_sta' i :
    Wstd_sta !! i = Some x -> Wstd_sta' !! i = Some y ->
    (revoke_std_sta Wstd_sta) !! i = Some x' → (revoke_std_sta Wstd_sta') !! i = Some y' →
    rtc (λ x0 y0 : region_type, std_rel_pub x0 y0 ∨ std_rel_pub_plus x0 y0 ∨ std_rel_priv x0 y0) x y →
    rtc (λ x0 y0 : region_type, std_rel_pub x0 y0 ∨ std_rel_pub_plus x0 y0 ∨ std_rel_priv x0 y0) x' y'.
  Proof.
    intros Hx Hy Hx' Hy' Hrtc.
    induction Hrtc as [Hrefl | j k h Hjk].
    - simplify_eq. rewrite -Hx in Hy.
      apply revoke_monotone_lookup in Hy.
      rewrite Hx' Hy' in Hy. inversion Hy. left.
    - destruct Hjk as [Hjk | [Hjk | Hjk] ].
      + destruct j,k; inversion Hjk; try discriminate; auto.
        * destruct h;revoke_i Wstd_sta Wstd_sta' i;try left.
          eright;[left;constructor|left].
          right with Temporary. left;constructor.
          eright;[right;right;constructor|left].
          right with Temporary. left;constructor.
          right with Revoked. right;right;constructor.
          right with Monotemporary. left;constructor.
          eright;[right;right;constructor|left].
          right with Monotemporary. left;constructor.
          eright;[right;left;constructor|left].
        * destruct h;revoke_i Wstd_sta Wstd_sta' i;try left.
          eright;[left;constructor|left].
          right with Temporary. left;constructor.
          eright;[right;right;constructor|left].
          right with Monotemporary. left;constructor.
          eright;[right;right;constructor|left].
          right with Monotemporary. left;constructor.
          eright;[right;left;constructor|left].
        * apply std_rel_rtc_Permanent in Hrtc;auto. subst.
          apply revoke_lookup_Revoked in Hx as Hxtemp.
          apply revoke_lookup_Perm in Hy as Hytemp.
          simplify_eq. eright;[left;constructor|left].
        * destruct h;revoke_i Wstd_sta Wstd_sta' i;try left;
            try (right with Temporary;[left;constructor|eright;[right;right;constructor|left]]).
          right with Temporary;[left;constructor|]. right with Revoked;[right;right;constructor|].
          right with Monotemporary;[left;constructor|]. eright;[|left]. right;right;constructor.
          right with Temporary;[left;constructor|]. right with Revoked;[right;right;constructor|].
          right with Monotemporary;[left;constructor|]. eright;[|left]. right;left;constructor.
        * subst. destruct h;revoke_i Wstd_sta Wstd_sta' i;try left;
            try (right with Monotemporary;[left;constructor|eright;[right;right;constructor|left]]).
          1,2: (right with Monotemporary;[left;constructor|right with Temporary;[right;right;constructor|]]).
          eright;[right;right;constructor|left].
          eright;[right;right;constructor|left].
          right with Monotemporary;[left;constructor|].
          eright;[|left]. right;left;constructor.
        * subst. destruct h;revoke_i Wstd_sta Wstd_sta' i;try left;
            try (right with Monotemporary;[left;constructor|eright;[right;right;constructor|left]]).
          1,2: (right with Monotemporary;[left;constructor|right with Temporary;[right;right;constructor|]]).
          eright;[right;right;constructor|left]. eright;[right;right;constructor|left].
          right with Monotemporary;[left;constructor|].
          eright;[|left]. right;left;constructor.
      + destruct j,k,h; inversion Hjk; try discriminate; auto;
          revoke_i Wstd_sta Wstd_sta' i; try left.
        eright;[left;constructor|left].
        right with Temporary;[left;constructor|eright;[right;right;constructor|left]].
        right with Monotemporary;[left;constructor|eright;[right;right;constructor|left]].
        right with Monotemporary;[left;constructor|eright;[right;left;constructor|left]].
      + destruct j,k,h; inversion Hjk; try discriminate; auto;
          revoke_i Wstd_sta Wstd_sta' i; try left;
            try (right with Temporary;[left;constructor|eright;[right;right;constructor|left]]);
            try (right with Monotemporary;[left;constructor|eright;[right;right;constructor|left]]);
            try (right with Monotemporary;[left;constructor|eright;[right;left;constructor|left]]).
  Qed.

  Lemma revoke_monotone W W' :
    related_sts_priv_world W W' → related_sts_priv_world (revoke W) (revoke W').
  Proof.
    destruct W as [ Wstd_sta [Wloc_sta Wloc_rel] ].
    destruct W' as [ Wstd_sta' [Wloc_sta' Wloc_rel'] ];
    rewrite /revoke /std /=.
    intros [(Hdom_sta & Htransition) Hrelated_loc].
    apply revoke_monotone_dom in Hdom_sta.
    split;[split;[auto|]|auto].
    intros i x' y' Hx' Hy'.
    simpl in *.
    assert (is_Some (Wstd_sta !! i)) as [x Hx]; [apply revoke_std_sta_lookup_Some; eauto|].
    assert (is_Some (Wstd_sta' !! i)) as [y Hy]; [apply revoke_std_sta_lookup_Some; eauto|].
    apply std_rel_monotone with x y Wstd_sta Wstd_sta' i; auto. apply Htransition with i;auto.
  Qed.

  (* --------------------------------------------------------------------------------- *)
  (* ----------------- REVOKED W IS A PRIVATE FUTURE WORLD TO W ---------------------- *)

  Lemma revoke_list_related_sts_priv_cons W l i :
    related_sts_priv_world W (revoke_list l W) → related_sts_priv_world W (revoke_list (i :: l) W).
  Proof.
    intros Hpriv.
    rewrite /revoke_list /=.
    destruct (std W !! i) eqn:Hsome; auto.
    destruct r eqn:Htemp; auto.
    - destruct W as [ Wstd_sta Wloc].
      destruct Hpriv as [(Hdoms & Ha) Hloc]; auto.
      split;simpl;auto.
      rewrite /related_sts_std_priv.
      simpl in *.
      split.
      + rewrite dom_insert_L. set_solver.
      + intros j x y Hx Hy.
        destruct (decide (i = j)).
        { subst.
          rewrite lookup_insert in Hy. inversion Hy.
          rewrite Hsome in Hx;inversion Hx;subst.
          right with Revoked;[|left].
          right. right. constructor.
        }
        rewrite lookup_insert_ne in Hy;auto.
        apply Ha with j;auto.
    - destruct W as [ Wstd_sta Wloc].
      destruct Hpriv as [(Hdoms & Ha) Hloc]; auto.
      split;simpl;auto.
      rewrite /related_sts_std_priv.
      simpl in *.
      split.
      + rewrite dom_insert_L. set_solver.
      + intros j x y Hx Hy.
        destruct (decide (i = j)).
        { subst.
          rewrite lookup_insert in Hy. inversion Hy.
          rewrite Hsome in Hx;inversion Hx;subst.
          right with Revoked;[|left].
          right. right. constructor.
        }
        rewrite lookup_insert_ne in Hy;auto.
        apply Ha with j;auto.
  Qed.

  Lemma revoke_list_related_sts_priv W l :
    related_sts_priv_world W (revoke_list l W).
  Proof.
    induction l.
    - destruct W. rewrite /revoke_list /=. apply related_sts_priv_refl_world.
    - split;[|apply related_sts_priv_refl].
      apply revoke_list_related_sts_priv_cons; auto.
  Qed.

  Lemma revoke_related_sts_priv W :
    related_sts_priv_world W (revoke W).
  Proof.
    rewrite revoke_list_dom. apply revoke_list_related_sts_priv.
  Qed.

  (* Helper lemmas for reasoning about a revoked domain *)

  Lemma dom_equal_revoke_list (W : WORLD) (M : relT) l :
    dom (gset Addr) W.1 = dom (gset Addr) M →
    dom (gset Addr) (revoke_list l W).1 = dom (gset Addr) M.
  Proof.
    intros Hdom.
    induction l.
    - done.
    - rewrite /revoke_list /=.
      destruct (std W !! a) eqn:Hsome; auto.
      destruct r eqn:Htemp;auto.
      all: rewrite dom_insert_L;rewrite IHl.
      all: assert (a ∈ dom (gset Addr) M) as Hin;[rewrite -Hdom;apply elem_of_gmap_dom;eauto|].
      all: try set_solver.
  Qed.

  (* ---------------------------------------------------------------------------------------- *)
  (* ------------------- IF THΕ FULL STS IS REVOKED, WΕ CAN REVOKE REGION ------------------- *)

  (* Note that Mρ by definition matches up with the full sts. Mρ starts out by being indirectly revoked *)
  Lemma monotone_revoke_region_def M Mρ W :
    ⌜dom (gset Addr) (std W) = dom (gset Addr) M⌝ -∗
     sts_full_world (revoke W) -∗ region_map_def M Mρ W -∗
     sts_full_world (revoke W) ∗ region_map_def M Mρ (revoke W).
  Proof.
    destruct W as [Wstd_sta Wloc].
    iIntros (Hdom) "Hfull Hr".
    iDestruct (big_sepM_exists with "Hr") as (m') "Hr".
    iDestruct (big_sepM2_sep with "Hr") as "[HMρ Hr]".
    iDestruct (big_sepM2_sep with "Hr") as "[Hstates Hr]".
    iAssert (∀ a ρ, ⌜m' !! a = Some ρ⌝ → ⌜ρ ≠ Temporary⌝)%I as %Htemp.
    { iIntros (a ρ Hsome).
      iDestruct (big_sepM2_lookup_1 _ _ _ a with "Hstates") as (γp) "[Hl Hstate]"; eauto.
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hρ.
      iPureIntro.
      eapply revoke_lookup_non_temp; eauto.
    }
    iAssert (∀ a ρ, ⌜m' !! a = Some ρ⌝ → ⌜ρ ≠ Monotemporary⌝)%I as %Hmonotemp.
    { iIntros (a ρ Hsome).
      iDestruct (big_sepM2_lookup_1 _ _ _ a with "Hstates") as (γp) "[Hl Hstate]"; eauto.
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hρ.
      iPureIntro.
      eapply revoke_lookup_non_temp; eauto.
    }
    iFrame.
    iApply big_sepM_exists. iExists m'.
    iApply big_sepM2_sep. iFrame.
    iDestruct (big_sepM2_sep with "[$Hstates $Hr]") as "Hr".
    iApply (big_sepM2_mono with "Hr").
    iIntros (a ρ γp Hm' HM) "/= [Hstate Ha]".
    specialize (Htemp a ρ Hm').
    specialize (Hmonotemp a ρ Hm').
    destruct ρ;iFrame;[contradiction|contradiction|].
    iDestruct "Ha" as (γpred p φ) "(Hγp & % & Hpred & Ha)".
    iDestruct "Ha" as (v) "(Hne & Ha & #Hmono & #Hφ)".
    iExists _,_,_;iFrame "∗ #"; iSplit;auto; iExists _; iFrame "∗ #".
    iNext. iApply ("Hmono" with "[] Hφ").
    iPureIntro. apply revoke_related_sts_priv.
    Unshelve. apply _.
  Qed.

  (* ---------------------------------------------------------------------------------------- *)
  (* ------------------- A REVOKED W IS MONOTONE WRT PRIVATE FUTURE WORLD ------------------- *)

  Lemma monotone_revoke_list_region_def_mono M Mρ W W1 W2 :
    ⌜related_sts_priv_world W1 W2⌝ -∗
     sts_full_world (revoke W) -∗ region_map_def M Mρ W1 -∗
     sts_full_world (revoke W) ∗ region_map_def M Mρ W2.
  Proof.
    iIntros (Hrelated) "Hfull Hr".
    iDestruct (big_sepM_exists with "Hr") as (m') "Hr".
    iDestruct (big_sepM2_sep with "Hr") as "[HMρ Hr]".
    iAssert (∀ a ρ, ⌜m' !! a = Some ρ⌝ → ⌜ρ ≠ Temporary⌝)%I as %Htemp.
    { iIntros (a ρ Hsome).
      iDestruct (big_sepM2_sep with "Hr") as "[Hstates Hr]".
      iDestruct (big_sepM2_lookup_1 _ _ _ a with "Hstates") as (γp) "[_ Hstate]"; eauto.
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hρ.
      iPureIntro. eapply revoke_lookup_non_temp; eauto.
    }
    iAssert (∀ a ρ, ⌜m' !! a = Some ρ⌝ → ⌜ρ ≠ Monotemporary⌝)%I as %Hmonotemp.
    { iIntros (a ρ Hsome).
      iDestruct (big_sepM2_sep with "Hr") as "[Hstates Hr]".
      iDestruct (big_sepM2_lookup_1 _ _ _ a with "Hstates") as (γp) "[_ Hstate]"; eauto.
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hρ.
      iPureIntro. eapply revoke_lookup_non_temp; eauto.
    }
    iFrame.
    iApply big_sepM_exists. iExists m'.
    iApply big_sepM2_sep. iFrame.
    iApply (big_sepM2_mono with "Hr").
    iIntros (a ρ γp Hsomeρ Hsomeγp) "[Hstate Ha] /=".
    specialize (Htemp a ρ Hsomeρ).
    specialize (Hmonotemp a ρ Hsomeρ).
    destruct ρ;try contradiction;iFrame.
    iDestruct "Ha" as (γpred p φ) "(Hγp & % & Hpred & Ha)".
    iDestruct "Ha" as (v) "(Hne & Ha & #Hmono & #Hφ)".
    iFrame.
    iExists _,_,_; iFrame "∗ #". iSplit;auto.
    iExists _; iFrame "∗ #".
    iNext. iApply "Hmono";[|iFrame "#"]. auto.
    Unshelve. apply _.
  Qed.

  Lemma monotone_revoke_list_region_def_mono_same M Mρ W W' :
    ⌜related_sts_priv_world W W'⌝ -∗
     sts_full_world (revoke W) -∗ region_map_def M Mρ (revoke W) -∗
     sts_full_world (revoke W) ∗ region_map_def M Mρ (revoke W').
  Proof.
    iIntros (Hrelated) "Hfull Hr".
    iApply (monotone_revoke_list_region_def_mono with "[] Hfull Hr").
    iPureIntro. apply revoke_monotone; auto.
  Qed.

  (* ---------------------------------------------------------------------------------------- *)
  (* ---------------- IF WΕ HAVE THE REGION, THEN WE CAN REVOKE THE FULL STS ---------------- *)

  (* This matches the temprary resources in the map *)
  Definition temp_resources (W : WORLD) φ (a : Addr) (p : Perm) : iProp Σ :=
    (∃ (v : Word),
           ⌜p ≠ O⌝
          ∗ a ↦ₐ[p] v
          ∗ (if pwl p
             then future_pub_plus_mono φ v
             else future_priv_mono φ v)
          ∗ φ (W,v))%I.

  Definition monotemp_resources (W : WORLD) φ (a : Addr) (p : Perm) : iProp Σ :=
    (∃ (v : Word),
           ⌜p ≠ O⌝
          ∗ a ↦ₐ[p] v
          ∗ (if pwl p
             then future_pub_a_mono a φ v
             else future_priv_mono φ v)
          ∗ φ (W,v))%I.


  Lemma reg_get (γ : gname) (R : relT) (n : Addr) (r : leibnizO (gname * Perm)) :
    own γ (● (to_agree <$> R : relUR)) ∧ ⌜R !! n = Some r⌝ ==∗
    (own γ (● (to_agree <$> R : relUR)) ∗ own γ (◯ {[n := to_agree r]})).
  Proof.
    iIntros "[HR #Hlookup]".
    iDestruct "Hlookup" as %Hlookup.
    iApply own_op.
    iApply (own_update with "HR").
    apply auth_update_core_id; auto. apply gmap_core_id,agree_core_id.
    apply singleton_included_l. exists (to_agree r). split; auto.
    (* apply leibniz_equiv_iff in Hlookup.  *)
    rewrite lookup_fmap. apply fmap_Some_equiv.
    exists r. split; auto.
  Qed.

  Lemma region_rel_get (W : WORLD) (a : Addr) :
    (std W) !! a = Some Temporary ∨ (std W) !! a = Some Monotemporary ->
    region W ∗ sts_full_world W ==∗
     region W ∗ sts_full_world W ∗ ∃ p φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗ rel a p φ.
  Proof.
    iIntros (Hlookup) "[Hr Hsts]".
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M Mρ) "(HM & #Hdom & #Hdom' & Hr)".
    iDestruct "Hdom" as %Hdom. iDestruct "Hdom'" as %Hdom'.
    assert (is_Some (M !! a)) as [γp Hγp].
    { apply elem_of_gmap_dom. rewrite -Hdom. apply elem_of_gmap_dom. destruct Hlookup; eauto. }
    rewrite RELS_eq /RELS_def.
    iMod (reg_get with "[$HM]") as "[HM Hrel]";[eauto|].
    (* rewrite /region_map_def. iDestruct (reg_in with "[$HM $Hrel]") as %HMeq. *)
    iDestruct (big_sepM_delete _ _ a with "Hr") as "[Hstate Hr]";[eauto|].
    iDestruct "Hstate" as (ρ Ha) "[Hρ Hstate]".
    iDestruct (sts_full_state_std with "Hsts Hρ") as %Hx''.
    destruct Hlookup as [Hlookup | Hlookup].
    all: rewrite Hlookup in Hx'';inversion Hx'';subst.
    all: iDestruct "Hstate" as (γpred p φ Heq Hpers) "(#Hsaved & Ha)".
    all: iDestruct "Ha" as (v Hne) "(Ha & Hmono & #Hφ)".
    all: destruct γp as [γpred' p']; inversion Heq; subst.
    all: iDestruct (big_sepM_delete _ _ a with "[Hρ Ha Hmono Hφ $Hr]") as "Hr";[eauto| |].
    1: { iExists Temporary. iFrame. iSplit;auto. iExists γpred, p, φ. iFrame "∗ #". repeat iSplit; auto.
         iExists _. iFrame "∗ #". auto. }
    2: { iExists Monotemporary. iFrame. iSplit;auto. iExists γpred, p, φ. iFrame "∗ #". repeat iSplit; auto.
         iExists _. iFrame "∗ #". auto. }
    all: iModIntro.
    all: iSplitL "HM Hr".
    1: { iExists M. iFrame. auto. }
    2: { iExists M. iFrame. auto. }
    all: iFrame; iExists p,φ; iSplit;auto; rewrite rel_eq /rel_def REL_eq /REL_def; iExists γpred.
    all: iFrame "Hsaved Hrel".
  Qed.

  Lemma submseteq_NoDup {A : Type} (l l' : list A) : l' ⊆+ l → NoDup l -> NoDup l'.
  Proof.
    intros Hsub Hdup.
    apply submseteq_Permutation in Hsub as [k Heq].
    revert Hdup; rewrite Heq =>Hdup.
    by apply NoDup_app in Hdup as (? & _ & _).
  Qed.

  Lemma monotone_revoke_list_sts_full_world_keep W (l : list Addr) (l' k' : list Addr) :
    ⊢ ⌜NoDup (l)⌝ → ⌜l' ⊆+ l⌝ → ⌜k' ⊆+ l⌝  →
    ([∗ list] a ∈ l', ⌜(std W) !! a = Some Temporary⌝ (* ∧ rel a p φ *))
    ∗ ([∗ list] a ∈ k', ⌜(std W) !! a = Some Monotemporary⌝ (* ∧ rel a p φ *))
    ∗ sts_full_world W ∗ region W
    ==∗ (sts_full_world (revoke_list l W) ∗ region W
                        ∗ ([∗ list] a ∈ l', ∃ p φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗ ▷ temp_resources W φ a p ∗ rel a p φ)
                        ∗ ([∗ list] a ∈ k', ∃ p φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗ ▷ monotemp_resources W φ a p ∗ rel a p φ)).
  Proof.
    (* destruct W as [ [Wstd_sta Wstd_rel] Wloc].  *)
    rewrite /std region_eq /region_def /=.
    iInduction (l) as [|x l] "IH" forall (l' k');
    iIntros (Hdup Hsub Hsubk) "(#Hrel & #Hrel' & Hfull & Hr)".
    - apply submseteq_nil_r in Hsub as ->.
      apply submseteq_nil_r in Hsubk as ->.
      repeat rewrite big_sepL_nil. iFrame. done.
    - destruct (decide (x ∈ l' ++ k')).
      + iAssert (⌜∀ x0, (x0 ∈ l' → x0 ∉ k') ∧ (x0 ∈ k' → x0 ∉ l')⌝)%I as %Hdisj. 
        { iIntros (x0). iSplit; iIntros (Hin Hcontr).
          all: iDestruct (big_sepL_elem_of with "Hrel") as %Htemp;eauto.
          all: iDestruct (big_sepL_elem_of with "Hrel'") as %Htemp';eauto.
          all: congruence. }
        iAssert (∃ l2' k2',
                    ⌜NoDup l2' ∧ l2' ⊆+ l ∧ NoDup k2' ∧ k2' ⊆+ l ∧
                    match W.1 !! x with
                    | Some Temporary => l' ≡ₚx :: l2' ∧ k' ≡ₚk2'
                    | Some Monotemporary => l' ≡ₚl2' ∧ k' ≡ₚx :: k2'
                    | _ => False
                    end⌝ ∧
                    ([∗ list] a ∈ l2', ⌜W.1 !! a = Some Temporary⌝) ∗ ([∗ list] a ∈ k2', ⌜W.1 !! a = Some Monotemporary⌝))%I
          as (l2' k2') "#[Hpure [Hrel2 Hrel2']]";[|iDestruct "Hpure" as %(Hdup2' & Hsub2 & Hdupk2' & Hdupk2 & Hmatch)].
        { apply elem_of_app in e as [Hin | Hin].
          - destruct Hdisj with x as [Hnin _]. specialize (Hnin Hin).
            apply elem_of_Permutation in Hin as [l2' Heql2].
            iExists l2',k'. iAssert ([∗ list] a ∈ (x :: l2'), ⌜W.1 !! a = Some Temporary⌝)%I as "#Hrel2";[rewrite Heql2;iFrame "Hrel"|].
            simpl. iDestruct "Hrel2" as "[% $]". rewrite H0. iFrame "Hrel'". iPureIntro. apply NoDup_cons in Hdup as [Hninx Hdup].
            apply submseteq_cons_r in Hsubk as [Hsubk | [k2' [Hk2' Hsubk2']]].
            2: { exfalso. apply Hnin. rewrite Hk2'. apply elem_of_cons. by left. }
            assert (l2' ⊆+ l).
            { apply submseteq_cons_r in Hsub as [Hsub | [l'' [Hl'' Heql'']]].
              + trans l';auto. rewrite Heql2. apply submseteq_cons;auto.
              + trans l'';auto. apply Permutation_cons_inv in Heql2 as [l1 [l2 [Heq Hl']]].
                subst. apply Permutation_sym,Permutation_cons_app_inv in Hl''. rewrite Hl' Hl''. done. }
            repeat split;auto;eapply submseteq_NoDup;eauto.
          - destruct Hdisj with x as [_ Hnin]. specialize (Hnin Hin).
            apply elem_of_Permutation in Hin as [l2' Heql2].
            iExists l',l2'. iAssert ([∗ list] a ∈ (x :: l2'), ⌜W.1 !! a = Some Monotemporary⌝)%I as "#Hrel2";[rewrite Heql2;iFrame "Hrel'"|].
            simpl. iDestruct "Hrel2" as "[% $]". rewrite H0. iFrame "Hrel". iPureIntro. apply NoDup_cons in Hdup as [Hninx Hdup].
            apply submseteq_cons_r in Hsub as [Hsub | [k2' [Hk2' Hsubk2']]].
            2: { exfalso. apply Hnin. rewrite Hk2'. apply elem_of_cons. by left. }
            assert (l2' ⊆+ l).
            { apply submseteq_cons_r in Hsubk as [Hsubk | [l'' [Hl'' Heql'']]].
              + trans k';auto. rewrite Heql2. apply submseteq_cons;auto.
              + trans l'';auto. apply Permutation_cons_inv in Heql2 as [l1 [l2 [Heq Hl']]].
                subst. apply Permutation_sym,Permutation_cons_app_inv in Hl''. rewrite Hl' Hl''. done. }
            repeat split;auto;eapply submseteq_NoDup;eauto.
        }
        apply NoDup_cons in Hdup as [Hnin Hdup]. 
        simpl.
        iAssert (⌜W.1 !! x = Some Temporary ∨ W.1 !! x = Some Monotemporary⌝)%I as %Htemp.
        { apply elem_of_app in e as [Hin | Hin].
          - iDestruct (big_sepL_elem_of with "Hrel") as "Htemp";eauto. iLeft. auto.
          - iDestruct (big_sepL_elem_of with "Hrel'") as "Htemp";eauto. iRight. auto. }
        iMod (region_rel_get with "[$Hfull Hr]") as "(Hfull & Hr & #Hx)";[apply Htemp|..].
        { rewrite region_eq /region_def. iFrame. }
        rewrite region_eq /region_def.
        iMod ("IH" $! l2' k2' with "[] [] [] [$Hrel2 $Hrel2' $Hfull $Hr]") as "(Hfull & Hr & Hl & Hk)"; auto.
        rewrite /revoke_list /= /std /=.
        rewrite rel_eq /rel_def REL_eq RELS_eq /REL_def /RELS_def.
        iDestruct "Hr" as (M Mρ) "(HM & % & #Hdom & Hpreds)".
        iDestruct "Hdom" as %Hdom.
        iDestruct "Hx" as (p' φ' Hpers) "Hx".
        iDestruct "Hx" as (γpred) "#(Hγpred & Hφ)".

        (* assert that γrel = γrel' *)
        iDestruct (reg_in γrel (M) with "[$HM $Hγpred]") as %HMeq.
        rewrite /region_map_def.
        rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete].
        iDestruct "Hpreds" as "[Ha Hpreds]".
        iDestruct "Ha" as (ρ Ha) "[Hstate Ha]".
        iDestruct (sts_full_state_std with "Hfull Hstate") as %Hlookup.
        simpl in Hlookup.
        simpl in Hlookup. subst. rewrite revoke_list_not_elem_of_lookup in Hlookup; auto.
        iMod (sts_update_std _ _ _ (Revoked) with "Hfull Hstate") as "[Hfull Hstate]".
        iDestruct (region_map_delete_nonstatic with "Hpreds") as "Hpreds".
        { intros m. destruct Htemp as [Htemp | Htemp]; rewrite Htemp in Hlookup;inversion Hlookup.
          all: subst ρ; rewrite Ha;auto. }
        iDestruct (region_map_insert_nonstatic Revoked with "Hpreds") as "Hpreds";auto.
        iClear "IH".
        iSplitL "Hfull";[destruct Htemp as [-> | ->]; by iFrame|].
        iDestruct (big_sepM_insert _ _ x (γpred, p') with "[$Hpreds Hstate]") as "Hpreds"; [apply lookup_delete|..].
        iExists Revoked. iFrame. iSplitR. iPureIntro; apply lookup_insert.
        iExists _,_,_. iFrame "#". iSplit;auto.
        rewrite -HMeq.
        iModIntro. iSplitL "Hpreds HM".
        ++ iExists M,_. iFrame. iSplit; auto.
           iPureIntro. rewrite dom_insert_L.
           assert (x ∈ dom (gset Addr) M) as Hin.
           { rewrite -Hdom. apply elem_of_gmap_dom. eauto. }
           revert Hin Hdom. clear; intros Hin Hdom. rewrite Hdom. set_solver.
        ++
          iAssert (∃ (p : Perm) (φ : WORLD * Word → iPropI Σ),
                      ⌜∀ Wv : WORLD * Word, Persistent (φ Wv)⌝
                      ∗ match W.1 !! x with
                        | Some Temporary => ▷ temp_resources W φ x p
                        | Some Monotemporary => ▷ monotemp_resources W φ x p
                        | _ => False
                        end
                      ∗ (∃ γpred0 : gnameO, own γrel (◯ {[x := to_agree (γpred0, p)]}) ∗ saved_pred_own γpred0 φ))%I with "[Ha]" as "Ha".
          { iExists p', φ'. iSplitR;auto. iSplitL.
            - iDestruct "Ha" as (γpred0 p0 φ0 Heq0 Hpers0) "(#Hsaved & Ha)".
              destruct Htemp as [Htemp | Htemp]; rewrite Htemp.
              all: rewrite Htemp in Hlookup;inversion Hlookup.
              all: iDestruct "Ha" as (v Hne0) "(Hx & Hmono & #Hφ0)"; simplify_eq.
              all: iExists v;destruct W as [ Wstd_sta Wloc].
              all: iDestruct (saved_pred_agree _ _ _ (Wstd_sta, Wloc, v) with "Hφ Hsaved") as "#Hφeq";iFrame.
              all: iSplitR; auto.
              all: iDestruct (internal_eq_iff with "Hφeq") as "Hφeq'".
              all: iSplitL "Hmono";[|by iNext; iApply "Hφeq'"].
              all: destruct (pwl p0).
              all: iDestruct "Hmono" as "#Hmono".
              all: iApply later_intuitionistically_2; iModIntro.
              all: repeat (iApply later_forall_2; iIntros (W W')).
              all: iDestruct (saved_pred_agree _ _ _ (W', v) with "Hφ Hsaved") as "#HφWeq'".
              all: iDestruct (internal_eq_iff with "HφWeq'") as "HφWeq''".
              all: iDestruct (saved_pred_agree _ _ _ (W, v) with "Hφ Hsaved") as "#HφWeq".
              all: iDestruct (internal_eq_iff with "HφWeq") as "HφWeq'''".
              all: iModIntro; iIntros (Hrelated) "HφW";iApply "HφWeq''"; iApply "Hmono"; eauto.
              all: iApply "HφWeq'''"; auto.
            - iExists γpred. iFrame "#". }
          destruct Htemp as [Htemp | Htemp];rewrite Htemp in Hmatch.
          all: destruct Hmatch as [-> ->];iFrame.
          all: rewrite Htemp;iFrame.
      + (* assert (Hdup_copy:=Hdup). *)
        (* rewrite Heqlk in Hdup. *)
        apply NoDup_cons in Hdup as [Hnin Hdup].
        apply not_elem_of_app in n as [Hn1 Hn2].
        iAssert (⌜l' ⊆+ l ∧ k' ⊆+ l ∧ NoDup l⌝)%I
          as "#Hpure";[|iDestruct "Hpure" as %(Hsub2 & Hsubk2 & Hdup2)].
        { iPureIntro. repeat split;auto.
          - apply submseteq_cons_r in Hsub as [Hsubl | [k'' [Hperm Hk'']]];auto.
            revert Hn1; rewrite Hperm =>Hn1. apply not_elem_of_cons in Hn1 as [Hcontr Hn1];contradiction.
          - apply submseteq_cons_r in Hsubk as [Hsubl | [k'' [Hperm Hk'']]];auto.
            revert Hn2; rewrite Hperm =>Hn2. apply not_elem_of_cons in Hn2 as [Hcontr Hn2];contradiction.
        }
        iMod ("IH" $! l' k' with "[] [] [] [$Hrel $Hrel' $Hfull $Hr]") as "(Hfull & Hr & $ & $)"; auto.
        iDestruct "Hr" as (M Mρ) "(HM & #Hdom & #Hdom' & Hr)".
        iDestruct "Hdom" as %Hdom. iDestruct "Hdom'" as %Hdom'. iClear "IH".
        rewrite /revoke_list /std /=. destruct W as [ Wstd_sta Wloc].
        destruct (Wstd_sta !! x) eqn:Hsome.
        2: { iFrame. iModIntro. rewrite Hsome. iFrame. iExists M. iFrame. auto. }
        rewrite Hsome.
        destruct (decide (r = Temporary ∨ r = Monotemporary)).
        2: { apply Decidable.not_or in n as [Hne Hne']. destruct r; try contradiction; iFrame; iModIntro; iExists M; iFrame; auto. }
        assert (is_Some (M !! x)) as [γp Hsomea].
        { apply elem_of_gmap_dom. rewrite -Hdom. apply elem_of_gmap_dom. eauto. }
        iDestruct (big_sepM_delete _ _ x with "Hr") as "[Hx Hr]"; eauto.
        iDestruct "Hx" as (ρ Ha) "[Hstate Hρ]".
        iDestruct (sts_full_state_std with "Hfull Hstate") as %Hlookup.
        iMod (sts_update_std _ _ _ (Revoked) with "Hfull Hstate") as "[Hfull Hstate]". iFrame.
        simpl in *. rewrite revoke_list_not_elem_of_lookup in Hlookup;auto.
        rewrite Hlookup in Hsome. inversion Hsome. subst.
        iDestruct (region_map_delete_nonstatic with "Hr") as "Hpreds";[intros m; destruct o as [-> | ->]; rewrite Ha; auto|].
        iDestruct (region_map_insert_nonstatic Revoked with "Hpreds") as "Hpreds";auto.
        iDestruct (big_sepM_delete _ _ x with "[Hstate $Hpreds Hρ]") as "Hr"; eauto.
        iExists Revoked; iFrame. iSplitR. iPureIntro. apply lookup_insert.
        iDestruct "Hρ" as (? ? ? ? ?) "[? _]". iExists _,_,_. repeat iSplit;eauto.
        iModIntro. destruct o as [-> | ->]; iFrame;iExists M, _;iFrame.
        all: iSplit; auto.
        all:iPureIntro; rewrite dom_insert_L.
        all: assert (x ∈ dom (gset Addr) M) as Hin.
        1,3: rewrite -Hdom'; apply elem_of_gmap_dom; eauto.
        all: revert Hin Hdom'. all: clear; intros Hin Hdom. all: rewrite Hdom. all: set_solver.
  Qed.

  Lemma monotone_revoke_list_sts_full_world_keep_alt W (l : list Addr) (l' k' : list Addr) p φ :
    ⊢ ⌜NoDup l⌝ → ⌜l' ⊆+ l⌝ → ⌜k' ⊆+ l⌝ →
      ([∗ list] a ∈ l', ⌜(std W) !! a = Some Temporary⌝ ∗ rel a p φ)
    ∗ ([∗ list] a ∈ k', ⌜(std W) !! a = Some Monotemporary⌝ ∗ rel a p φ)
    ∗ sts_full_world W ∗ region W
    ==∗ (sts_full_world (revoke_list l W) ∗ region W
                        ∗ ([∗ list] a ∈ l', ▷ temp_resources W φ a p ∗ rel a p φ)
                        ∗ ([∗ list] a ∈ k', ▷ monotemp_resources W φ a p ∗ rel a p φ)).
  Proof.
    (* destruct W as [ [Wstd_sta Wstd_rel] Wloc].  *)
    iIntros (Hdupl Hsub Hsubk) "(Htemp & Hmonotemp & Hsts & Hr)".
    iDestruct (big_sepL_sep with "Htemp") as "[Htemp Hrel]".
    iDestruct (big_sepL_sep with "Hmonotemp") as "[Hmonotemp Hmonorel]".
    iMod (monotone_revoke_list_sts_full_world_keep with "[] [] [] [$Hsts $Hr $Htemp $Hmonotemp]") as "(Hsts & Hr & Htemp & Hmonotemp)";auto.
    iFrame. iSplitL "Htemp Hrel".
    all: iApply big_sepL_bupd.
    1: iDestruct (big_sepL_sep with "[$Hrel $Htemp]") as "Htemp".
    2: iDestruct (big_sepL_sep with "[$Hmonorel $Hmonotemp]") as "Htemp".
    all: iApply (big_sepL_mono with "Htemp").
    all: iIntros (k0 y Hsome) "(#Hr & Htemp)".
    all: iDestruct "Htemp" as (p' φ' Hpers) "[Htemp #Hrel]".
    all: iModIntro;rewrite /temp_resources /monotemp_resources.
    all: iDestruct (rel_agree _ p p' with "[$Hrel $Hr]") as "(% & #Hφeq')".
    all: subst.
    all: iDestruct "Htemp" as (v) "(Hne & Ha & Hmono & Hφ)".
    all: iFrame "Hr".
    all: iExists v; iFrame "#"; iFrame. all: iSplitL "Hmono". 
    1,3: destruct (pwl p').
    5,6: iNext; iSpecialize ("Hφeq'" $! (W,v)); iRewrite "Hφeq'"; iFrame.
    all: iIntros (W' W'' Hrelated); iDestruct "Hmono" as "#Hmono".
    all: iDestruct (rel_agree _ _ _ φ φ' with "[$Hrel $Hr]") as "(% & #Hφeq'')".
    all: iSpecialize ("Hφeq'" $! (W',v)) .
    all: iSpecialize ("Hφeq''" $! (W'',v)) .
    all: iNext; iModIntro.
    all: iRewrite "Hφeq''"; iRewrite "Hφeq'".
    all: iIntros "Hφ"; iApply "Hmono"; eauto.
  Qed.

  Lemma monotone_revoke_sts_full_world_keep W (l k : list Addr) :
    ⌜NoDup (l ++ k)⌝ -∗
     ([∗ list] a ∈ l, ⌜(std W) !! a = Some Temporary⌝) ∗
     ([∗ list] a ∈ k, ⌜(std W) !! a = Some Monotemporary⌝)
     ∗ sts_full_world W ∗ region W
    ==∗ (sts_full_world (revoke W) ∗ region W ∗
                          ([∗ list] a ∈ l, ∃ p φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗ ▷ temp_resources W φ a p ∗ rel a p φ)
                        ∗ ([∗ list] a ∈ k, ∃ p φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗ ▷ monotemp_resources W φ a p ∗ rel a p φ)).
  Proof.
    iIntros (Hdup) "(Hl & Hk & Hfull & Hr)".
    rewrite revoke_list_dom.
    iAssert (⌜l ⊆+ (map_to_list W.1).*1 ∧ k ⊆+ (map_to_list W.1).*1⌝)%I as %[Hsub Hsubk].
    { iClear "Hfull Hr". iSplit.
      1: iClear "Hk"; iInduction l as [| x l] "IH".
      3: iClear "Hl"; iInduction k as [| x k] "IH".
      1,3: iPureIntro;apply submseteq_nil_l.
      1: iDestruct "Hl" as "[ Hin Hl]".
      2: iDestruct "Hk" as "[ Hin Hl]".
      all: iDestruct "Hin" as %Hin; simpl in *. 
      2: revert Hdup; rewrite -Permutation_middle =>Hdup.
      all: apply NoDup_cons in Hdup as [Hnin Hdup].
      all: iDestruct ("IH" with "[] Hl") as %Hsub; auto.
      all: iPureIntro.
      all: assert (x ∈ (map_to_list W.1).*1) as Helem.
      1,3: apply map_to_list_fst; eexists; by apply elem_of_map_to_list. 
      all: apply elem_of_Permutation in Helem as [l' Hl']; rewrite Hl'.
      all: apply submseteq_skip;revert Hsub; rewrite Hl'; intros Hsub.
      all: apply submseteq_cons_r in Hsub as [Hsub | [l'' [Heq _] ] ]; auto.
      1: assert (countable.encode x ∈ countable.encode <$> l) as Hcontr.
      3: assert (countable.encode x ∈ countable.encode <$> k) as Hcontr.
      1,3: rewrite Heq; apply elem_of_list_here.
      all: apply elem_of_list_fmap_2 in Hcontr as [y [Hxy Hy] ].
      all: apply encode_inj in Hxy; subst; apply not_elem_of_app in Hnin as [? ?];contradiction.
    }
    iMod (monotone_revoke_list_sts_full_world_keep _ (map_to_list W.1).*1
            with "[] [] [] [$Hl $Hfull $Hr $Hk]") as "(Hfull & Hr & Hi)"; auto.
    { iPureIntro. apply (NoDup_fst_map_to_list (M:=gmap Addr) (A:=region_type)). }
    iFrame. done.
  Qed.

  Lemma monotone_revoke_sts_full_world_keep_alt W (l k : list Addr) p φ :
    ⌜NoDup (l ++ k)⌝ -∗
     ([∗ list] a ∈ l, ⌜(std W) !! a = Some Temporary⌝ ∗ rel a p φ)
     ∗ ([∗ list] a ∈ k, ⌜(std W) !! a = Some Monotemporary⌝ ∗ rel a p φ)
     ∗ sts_full_world W ∗ region W
    ==∗ (sts_full_world (revoke W) ∗ region W ∗
                        ([∗ list] a ∈ l, ▷ temp_resources W φ a p ∗ rel a p φ)
                        ∗ ([∗ list] a ∈ k, ▷ monotemp_resources W φ a p ∗ rel a p φ)).
  Proof.
    iIntros (Hdup) "(Hl & Hk & Hfull & Hr)".
    rewrite revoke_list_dom.
    iAssert (⌜l ⊆+ (map_to_list W.1).*1 ∧ k ⊆+ (map_to_list W.1).*1⌝)%I as %[Hsub Hsubk].
    { iClear "Hfull Hr". iSplit.
      1: iClear "Hk"; iInduction l as [| x l] "IH".
      3: iClear "Hl"; iInduction k as [| x k] "IH".
      1,3: iPureIntro;apply submseteq_nil_l.
      1: iDestruct "Hl" as "[ [Hin Hrel] Hl]".
      2: iDestruct "Hk" as "[ [Hin Hrel] Hl]".
      all: iDestruct "Hin" as %Hin; simpl in *. 
      2: revert Hdup; rewrite -Permutation_middle =>Hdup.
      all: apply NoDup_cons in Hdup as [Hnin Hdup].
      all: iDestruct ("IH" with "[] Hl") as %Hsub; auto.
      all: iPureIntro.
      all: assert (x ∈ (map_to_list W.1).*1) as Helem.
      1,3: apply map_to_list_fst; eexists; by apply elem_of_map_to_list. 
      all: apply elem_of_Permutation in Helem as [l' Hl']; rewrite Hl'.
      all: apply submseteq_skip;revert Hsub; rewrite Hl'; intros Hsub.
      all: apply submseteq_cons_r in Hsub as [Hsub | [l'' [Heq _] ] ]; auto.
      1: assert (countable.encode x ∈ countable.encode <$> l) as Hcontr.
      3: assert (countable.encode x ∈ countable.encode <$> k) as Hcontr.
      1,3: rewrite Heq; apply elem_of_list_here.
      all: apply elem_of_list_fmap_2 in Hcontr as [y [Hxy Hy] ].
      all: apply encode_inj in Hxy; subst; apply not_elem_of_app in Hnin as [? ?];contradiction.
    }
    iMod (monotone_revoke_list_sts_full_world_keep_alt _ (map_to_list W.1).*1 l
            with "[] [] [] [$Hl $Hk $Hfull $Hr]") as "(Hfull & Hr & Hi)"; auto.
    { iPureIntro. apply (NoDup_fst_map_to_list (M:=gmap Addr) (A:=region_type)). }
    iFrame. done.
  Qed.

  (* The following statement discards all the resources of temporary regions *)
  Lemma monotone_revoke_list_sts_full_world M Mρ W l :
    ⌜∀ (a : Addr), a ∈ l → is_Some (M !! a)⌝ -∗
    ⌜dom (gset Addr) Mρ = dom (gset Addr) M⌝ -∗
    ⌜NoDup l⌝ -∗
    sts_full_world W ∗ region_map_def M Mρ W
    ==∗ ∃ Mρ, ⌜dom (gset Addr) Mρ = dom (gset Addr) M⌝
              ∧ (sts_full_world (revoke_list l W) ∗ region_map_def M Mρ W).
  Proof.
    destruct W as [Wstd_sta Wloc].
    rewrite /std /=.
    iIntros (Hin Hdom Hdup) "[Hfull Hr]".
    iInduction (l) as [|x l] "IH".
    - iExists _. iFrame. done.
    - apply NoDup_cons in Hdup as [Hnin Hdup].
      iMod ("IH" with "[] [] Hfull Hr") as (Mρ' Hdom_new) "[Hfull Hr]"; auto.
      { iPureIntro. intros a Ha. apply Hin. apply elem_of_cons. by right. }
      rewrite /revoke_list /= /std /=.
      destruct (Wstd_sta !! x) eqn:Hsome;[|iExists _; by iFrame].
      destruct r;[| |iExists _; by iFrame..].
      all: destruct Hin with x as [γp Hsomea];[apply elem_of_list_here|].
      all: iDestruct (big_sepM_delete _ _ x with "Hr") as "[Hρ Hr]"; eauto.
      all: iDestruct "Hρ" as (ρ' Hρ') "(Hstate & Ha)".
      all: iDestruct (sts_full_state_std with "Hfull Hstate") as %Hlookup.
      all: simpl in Hlookup; subst; rewrite revoke_list_not_elem_of_lookup in Hlookup; auto.
      all: rewrite Hsome in Hlookup; inversion Hlookup as [Heq]; subst ρ'.
      all: iMod (sts_update_std _ _ _ (Revoked) with "Hfull Hstate") as "[Hfull Hstate]".
      all: iFrame.
      all: iDestruct (region_map_delete_nonstatic with "Hr") as "Hr";[intros m;by rewrite Hρ'|].
      all: iDestruct (region_map_insert_nonstatic Revoked with "Hr") as "Hr";auto.
      all: iExists _.
      all: iDestruct "Ha" as (γpred p0 φ Heq Hpers) "[#Hsaved Ha]".
      all: iDestruct (big_sepM_delete _ _ x with "[$Hr Hstate]") as "$"; eauto.
      1,3: iExists Revoked; iFrame; iSplitR.
      all: try (iPureIntro; apply lookup_insert).
      1,2: iExists _,_,_; iFrame "#"; iSplit;auto.
      all: iPureIntro; rewrite -Hdom_new dom_insert_L.
      all: assert (x ∈ dom (gset Addr) Mρ') as Hin'.
      1,3: apply elem_of_gmap_dom;eauto. 
      all: set_solver.
  Qed.

  (* The following statement discards all the resources of temporary regions *)
  Lemma monotone_revoke_sts_full_world W :
    sts_full_world W ∗ region W
    ==∗ (sts_full_world (revoke W) ∗ region W).
  Proof.
    iIntros "[Hfull Hr]".
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M Mρ) "(HM & #Hdom & #Hdom' & Hr)".
    iDestruct "Hdom" as %Hdom. iDestruct "Hdom'" as %Hdom'.
    rewrite revoke_list_dom.
    iMod (monotone_revoke_list_sts_full_world _ _ _ (map_to_list W.1).*1
            with "[] [] [] [$Hfull $Hr]") as (Mρ' Hin) "[Hfull Hr]";auto.
    { iPureIntro. intros i Hin. apply map_to_list_fst in Hin as [x Hin].
      apply elem_of_gmap_dom. rewrite -Hdom. apply elem_of_map_to_list in Hin.
      apply elem_of_gmap_dom. eauto.
    }
    { iPureIntro. apply (NoDup_fst_map_to_list (M:=gmap Addr) (A:=region_type)). }
    iFrame.
    iModIntro. iExists M,Mρ'.
    rewrite /region_map_def.
    iFrame. done.
  Qed.

  Lemma submseteq_dom (l : list Addr) (Wstd_sta : gmap Addr region_type) :
    Forall (λ i : Addr, Wstd_sta !! i = Some Temporary ∨ Wstd_sta !! i = Some Monotemporary) l
    → NoDup l → l ⊆+ (map_to_list Wstd_sta).*1.
  Proof.
    generalize l.
    induction Wstd_sta using map_ind.
    + intros l' Htemps Hdup. destruct l'; auto. inversion Htemps. destruct H2; subst; discriminate.
    + intros l' Htemps Hdup. rewrite map_to_list_insert; auto.
      cbn.
      (* destruct on i being an element of l'! *)
      destruct (decide (i ∈ l')).
      ++ apply elem_of_list_split in e as [l1 [l2 Heq] ].
         rewrite Heq -Permutation_middle.
         apply submseteq_skip.
         rewrite Heq in Hdup.
         apply NoDup_app in Hdup as [Hdup1 [Hdisj Hdup2] ].
         apply NoDup_cons in Hdup2 as [Helem2 Hdup2].
         assert (i ∉ l1) as Helem1.
         { intros Hin. specialize (Hdisj i Hin). apply not_elem_of_cons in Hdisj as [Hcontr _]. done. }
         apply IHWstd_sta.
         +++ revert Htemps. repeat rewrite Forall_forall. intros Htemps.
             intros j Hin.
             assert (j ≠ i) as Hne.
             { intros Hcontr; subst. apply elem_of_app in Hin as [Hcontr | Hcontr]; congruence. }
             destruct Htemps with j as [Htemp | Htemp]. 
             2,3: rewrite -(Htemp);rewrite lookup_insert_ne;auto.
             subst. apply elem_of_app. apply elem_of_app in Hin as [Hin | Hin]; [left;auto|right].
             apply elem_of_cons;by right.
         +++ apply NoDup_app; repeat (split;auto).
             intros j Hj. specialize (Hdisj j Hj). apply not_elem_of_cons in Hdisj as [_ Hl2];auto.
      ++ apply submseteq_cons. apply IHWstd_sta; auto.
         revert Htemps. repeat rewrite Forall_forall. intros Htemps j Hin.
         specialize (Htemps j Hin).
         assert (i ≠ j) as Hneq; [intros Hcontr; subst; congruence|].
         rewrite lookup_insert_ne in Htemps;auto.
  Qed.


  (* ---------------------------------------------------------------------------------------- *)
  (* ------------------ WE CAN REVOKΕ A REGION AND STS COLLECTION PAIR ---------------------- *)
  (* ---------------------------------------------------------------------------------------- *)

  (* revoke and discards temp regions *)
  Lemma monotone_revoke W :
    sts_full_world W ∗ region W ==∗ sts_full_world (revoke W) ∗ region (revoke W).
  Proof.
    iIntros "[HW Hr]".
    iMod (monotone_revoke_sts_full_world with "[$HW $Hr]") as "[HW Hr]".
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M Mρ) "(HM & % & % & Hpreds)".
    iDestruct (monotone_revoke_region_def with "[] [$HW] [$Hpreds]") as "[Hpreds HW]"; auto.
    iModIntro. iFrame. iExists _,_. iFrame.
    iPureIntro. split;auto. rewrite /revoke -revoke_dom_eq /=. auto.
  Qed.

  (* revoke and keep temp resources in list l, with unknown p and φ *)
  Lemma monotone_revoke_keep W l k :
    NoDup (l ++ k) ->
    ([∗ list] a ∈ l, ⌜(std W) !! a = Some Temporary⌝)
      ∗ ([∗ list] a ∈ k, ⌜(std W) !! a = Some Monotemporary⌝)
      ∗ sts_full_world W ∗ region W ==∗ sts_full_world (revoke W) ∗ region (revoke W)
      ∗ ([∗ list] a ∈ l, (∃ p φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗ ▷ temp_resources W φ a p ∗ rel a p φ)
                           ∗ ⌜(std (revoke W)) !! a = Some Revoked⌝)
      ∗ ([∗ list] a ∈ k, (∃ p φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗ ▷ monotemp_resources W φ a p ∗ rel a p φ)
                           ∗ ⌜(std (revoke W)) !! a = Some Revoked⌝).
  Proof.
    iIntros (Hdup) "(Hl & Hk & HW & Hr)".
    iAssert (⌜Forall (λ a, std W !! a = Some Temporary) l⌝)%I as %Htemps.
    { iDestruct (big_sepL_forall with "Hl") as %Htemps.
      iPureIntro. apply Forall_lookup. done. }
    iAssert (⌜Forall (λ a, std W !! a = Some Monotemporary) k⌝)%I as %Hmonotemps.
    { iDestruct (big_sepL_forall with "Hk") as %Hmonotemps.
      iPureIntro. apply Forall_lookup. done. }
    iMod (monotone_revoke_sts_full_world_keep with "[] [$HW $Hr $Hl $Hk]") as "(HW & Hr & Hl & Hk)"; eauto.
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M Mρ) "(HM & % & % & Hpreds)".
    iDestruct (monotone_revoke_region_def with "[] [$HW] [$Hpreds]") as "[Hpreds HW]"; auto.
    iModIntro. iFrame. iSplitL "HW HM".
    - iExists _,_. iFrame. iPureIntro. split;auto. rewrite /revoke -revoke_dom_eq /=. auto.
    - iSplitL "Hl".
      all: iApply big_sepL_sep; iFrame; iApply big_sepL_forall; iPureIntro.
      1: revert Htemps. 2: revert Hmonotemps. 1: rewrite (Forall_lookup _ l). 2: rewrite (Forall_lookup _ k).
      all: intros Hl i a Ha; auto.
      all: specialize (Hl i a Ha). all: rewrite /revoke. by apply revoke_lookup_Temp. by apply revoke_lookup_Monotemp.
      Unshelve. apply _.
  Qed.

  (* revoke and keep temp resources in list l, with know p and φ *)
  Lemma monotone_revoke_keep_alt W l k p φ :
    NoDup (l ++ k) ->
    ([∗ list] a ∈ l, ⌜(std W) !! a = Some Temporary⌝ ∗ rel a p φ)
      ∗ ([∗ list] a ∈ k, ⌜(std W) !! a = Some Monotemporary⌝ ∗ rel a p φ)
      ∗ sts_full_world W ∗ region W ==∗ sts_full_world (revoke W) ∗ region (revoke W)
      ∗ ([∗ list] a ∈ l, (▷ temp_resources W φ a p ∗ rel a p φ)
                           ∗ ⌜(std (revoke W)) !! a = Some Revoked⌝)
      ∗ ([∗ list] a ∈ k, (▷ monotemp_resources W φ a p ∗ rel a p φ)
                           ∗ ⌜(std (revoke W)) !! a = Some Revoked⌝).
  Proof.
    iIntros (Hdup) "(Hl & Hk & HW & Hr)".
    iAssert (⌜Forall (λ a, std W !! a = Some Temporary) l⌝)%I as %Htemps.
    { iDestruct (big_sepL_sep with "Hl") as "[Htemps Hrel]".
      iDestruct (big_sepL_forall with "Htemps") as %Htemps.
      iPureIntro. apply Forall_lookup. done. }
    iAssert (⌜Forall (λ a, std W !! a = Some Monotemporary) k⌝)%I as %Hmonotemps.
    { iDestruct (big_sepL_sep with "Hk") as "[Htemps Hrel]".
      iDestruct (big_sepL_forall with "Htemps") as %Hmonotemps.
      iPureIntro. apply Forall_lookup. done. }
    iMod (monotone_revoke_sts_full_world_keep_alt with "[] [$HW $Hr $Hl $Hk]") as "(HW & Hr & Hl & Hk)"; eauto.
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M Mρ) "(HM & % & % & Hpreds)".
    iDestruct (monotone_revoke_region_def with "[] [$HW] [$Hpreds]") as "[Hpreds HW]"; auto.
    iModIntro. iFrame. iSplitL "HW HM".
    - iExists _,_. iFrame. iPureIntro. split;auto. rewrite /revoke -revoke_dom_eq /=. auto.
    - iSplitL "Hl".
      all: iApply big_sepL_sep. all: iFrame. all: iApply big_sepL_forall. all: iPureIntro.
      1: revert Htemps. 2: revert Hmonotemps. 1: rewrite (Forall_lookup _ l). 2: rewrite (Forall_lookup _ k).
      all: intros Hl i a Ha; auto.
      all: specialize (Hl i a Ha). all: rewrite /revoke. by apply revoke_lookup_Temp. by apply revoke_lookup_Monotemp.
      Unshelve. apply _. 
  Qed.

  (* For practical reasons, it will be convenient to have a version of revoking where you only know what some of the
     temp/monotemp regions are *)
  Lemma monotone_revoke_keep_some W l1 l2 k1 k2 p φ :
    NoDup (l1 ++ l2 ++ k1 ++ k2) ->
    ([∗ list] a ∈ l1, ⌜(std W) !! a = Some Temporary⌝) ∗
    ([∗ list] a ∈ l2, ⌜(std W) !! a = Some Temporary⌝ ∗ rel a p φ) ∗
    ([∗ list] a ∈ k1, ⌜(std W) !! a = Some Monotemporary⌝) ∗
    ([∗ list] a ∈ k2, ⌜(std W) !! a = Some Monotemporary⌝ ∗ rel a p φ)
    ∗ sts_full_world W ∗ region W ==∗ sts_full_world (revoke W) ∗ region (revoke W)
    ∗ ([∗ list] a ∈ l1, (∃ p φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗ ▷ temp_resources W φ a p ∗ rel a p φ)
                          ∗ ⌜(std (revoke W)) !! a = Some Revoked⌝)
    ∗ ([∗ list] a ∈ l2, (▷ temp_resources W φ a p ∗ rel a p φ)
                          ∗ ⌜(std (revoke W)) !! a = Some Revoked⌝)
    ∗ ([∗ list] a ∈ k1, (∃ p φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗ ▷ monotemp_resources W φ a p ∗ rel a p φ)
                          ∗ ⌜(std (revoke W)) !! a = Some Revoked⌝)
    ∗ ([∗ list] a ∈ k2, (▷ monotemp_resources W φ a p ∗ rel a p φ)
                          ∗ ⌜(std (revoke W)) !! a = Some Revoked⌝).
  Proof.
    iIntros (Hdup) "(Hl1 & Hl2 & Hk1 & Hk2 & HW & Hr)".
    iDestruct (big_sepL_sep with "Hl2") as "[Hl2 #Hrels]".
    iDestruct (big_sepL_sep with "Hk2") as "[Hk2 #Hrelsk]".
    iDestruct (big_sepL_app with "[$Hl1 $Hl2]") as "Hl".
    iDestruct (big_sepL_app with "[$Hk1 $Hk2]") as "Hk".
    iMod (monotone_revoke_keep with "[$HW $Hr $Hl $Hk]") as "(HW & Hr & Hl & Hk)";[rewrite -app_assoc; auto|].
    iDestruct (big_sepL_app with "Hl") as "[Hl1 Hl2]".
    iDestruct (big_sepL_sep with "Hl2") as "[Hl2 Hrev]".
    iDestruct (big_sepL_app with "Hk") as "[Hk1 Hk2]".
    iDestruct (big_sepL_sep with "Hk2") as "[Hk2 Hrevk]".
    iFrame. iSplitL "Hl2 Hrev".
    all: iApply big_sepL_sep; iFrame.
    all: iModIntro.
    1: iDestruct (big_sepL_sep with "[Hrels $Hl2]") as "Hl2";[iFrame "Hrels"|].
    2: iDestruct (big_sepL_sep with "[Hrelsk $Hk2]") as "Hk2";[iFrame "Hrelsk"|].
    1: iApply (big_sepL_mono with "Hl2").
    2: iApply (big_sepL_mono with "Hk2").
    all: iIntros (k y Hlookup) "[Htemp #Hrel]".
    all: iDestruct "Htemp" as (p' φ' Hpers) "(Htemp & #Hrel')".
    all: rewrite /temp_resources /monotemp_resources.
    all: iDestruct (later_exist with "Htemp") as (v) "(Hne & Hy & Hmono & Hφ')".
    all: iDestruct (rel_agree _ p p' with "[$Hrel $Hrel']") as (Heq) "#Hφeq"; subst.
    all: iFrame "Hrel"; iApply later_exist_2; iExists (v); iFrame.
    all: iSplitR "Hφ'".
    1,3: destruct (pwl p').
    5,6: iNext; iSpecialize ("Hφeq" $! (W,v)); iRewrite "Hφeq"; iFrame.
    all: iIntros (W' W'' Hrelated); iDestruct "Hmono" as "#Hmono".
    all: iDestruct (rel_agree _ _ _ φ φ' with "[$Hrel $Hrel']") as "(% & #Hφeq')".
    all: iSpecialize ("Hφeq'" $! (W',v)) .
    all: iSpecialize ("Hφeq" $! (W'',v)) .
    all: iNext; iModIntro.
    all: iRewrite "Hφeq'"; iRewrite "Hφeq".
    all: iIntros "Hφ"; iApply "Hmono"; eauto.
    Unshelve. apply _.
  Qed.

  (* ---------------------------------------------------------------------------------------- *)
  (* ----------------- REVOKING ALL TEMPORARY REGIONS, KNOWN AND UNKNOWN  ------------------- *)
  (* ---------------------------------------------------------------------------------------- *)

  (* The following helper lemmas are for revoking all temporary regions in the world *)

  (* First we must assert that there exists a list of distinct addresses whose state is temporary,
     and no other address is temp*)

  Lemma extract_temps W :
    ∃ l k, NoDup (l ++ k)
           ∧ (forall (a : Addr), (std W) !! a = Some Temporary <-> a ∈ l)
           ∧ (forall (a : Addr), (std W) !! a = Some Monotemporary <-> a ∈ k).
  Proof.
    destruct W as [Wstd_sta Wloc ].
    rewrite /std /=.
    induction Wstd_sta using (map_ind (M:=gmap Addr) (A:=region_type)).
    - exists [],[]. split;[by apply NoDup_nil|]. split; intros a; split; intros Hcontr; inversion Hcontr.
    - destruct IHWstd_sta as [l [k [Hdup [Hiff Hiffk] ] ] ].
      assert (i ∈ dom (gset Addr) (<[i:=x]> m)) as Hin.
      { apply elem_of_dom. rewrite lookup_insert; eauto. }
      assert (i ∉ l) as Hnin.
      { intros Hcontr. apply Hiff in Hcontr. simplify_map_eq. }
      assert (i ∉ k) as Hnin'.
      { intros Hcontr. apply Hiffk in Hcontr. simplify_map_eq. }
      assert (Hdup_copy:=Hdup).
      apply NoDup_app in Hdup_copy as [Hdupl [Hdisj Hdupk] ].
      destruct (decide (x = Temporary)); subst.
      + exists (i :: l),k. simpl. split;[apply NoDup_cons;split;auto;apply not_elem_of_app;auto|].
        split;intros a0; destruct (decide (i = a0)); subst;simplify_map_eq.
        1,3: rewrite lookup_insert.
        { split;auto. intros _. apply elem_of_cons; by left. }
        { split;intros Hcontr;[inversion Hcontr|]. congruence. }
        1,2: rewrite lookup_insert_ne;[|intros Hcontr;congruence].
        split; intros Htemp.
        { apply elem_of_cons; right. by apply Hiff. }
        { apply elem_of_cons in Htemp as [Hcontr | Hin'];[congruence|]. apply Hiff; auto. }
        split;intros Htemp; by apply Hiffk. 
      + destruct (decide (x = Monotemporary)); subst.
        * exists l,(i::k). simpl. rewrite -Permutation_middle. split;[apply NoDup_cons;split;auto;apply not_elem_of_app;auto|].
          split;intros a0; destruct (decide (i = a0)); subst;simplify_map_eq.
          1,3: rewrite lookup_insert.
          { split;intros Hcontr;[inversion Hcontr|]. congruence. }
          { split;auto. intros _. apply elem_of_cons; by left. }
          1,2: rewrite lookup_insert_ne;[|intros Hcontr;congruence].
          split; intros Htemp; by apply Hiff.
          split; intros Htemp.
          { apply elem_of_cons; right. by apply Hiffk. }
          { apply elem_of_cons in Htemp as [Hcontr | Hin'];[congruence|]. apply Hiffk; auto. }
        * exists l,k. split; auto. split;intros a0. all: split.
          1,3: destruct (decide (i = a0));subst.
          1,3: rewrite lookup_insert; intros Hcontr; congruence.
          1: rewrite lookup_insert_ne;[apply Hiff|]; auto.
          1: rewrite lookup_insert_ne;[apply Hiffk|]; auto.
          all: intros Hin'; destruct (decide (i = a0));[congruence|].
          all: rewrite lookup_insert_ne;[|intros Hcontr;congruence].
          apply Hiff; auto. apply Hiffk;auto.
  Qed.

  (* We also want to be able to split the extracted temporary regions into known and unknown *)
  Lemma extract_temps_split W l k :
    NoDup (l ++ k) ->
    Forall (λ (a : Addr), (std W) !! a = Some Temporary) l ->
    Forall (λ (a : Addr), (std W) !! a = Some Monotemporary) k ->
    ∃ l' k', NoDup (l' ++ l ++ k' ++ k)
             ∧ (forall (a : Addr), (std W) !! a = Some Temporary <-> a ∈ (l' ++ l))
             ∧ (forall (a : Addr), (std W) !! a = Some Monotemporary <-> a ∈ (k' ++ k)).
  Proof.
    intros Hdup HForall HForallk.
    pose proof (extract_temps W) as [l' [k' [Hdup' [Hl' Hk'] ]] ].
    revert HForall HForallk; rewrite !Forall_forall =>HForall HForallk.
    exists (list_difference l' l),(list_difference k' k). split;[|split].
    - rewrite app_assoc. apply NoDup_app. split;[|split].
      + apply NoDup_app. split;[|split].
        * apply NoDup_list_difference. apply NoDup_app in Hdup' as [? ?]; auto.
        * intros a Ha. apply elem_of_list_difference in Ha as [_ Ha]; auto.
        * apply NoDup_app in Hdup as [? ?]; auto.
      + intros a Ha. apply elem_of_app in Ha as [Ha | Ha].
        * intros Hcontr. apply elem_of_app in Hcontr as [Hcontr | Hcontr].
          ** apply elem_of_list_difference in Ha as [Ha _]; auto.
             apply elem_of_list_difference in Hcontr as [Hcontr _]; auto.
             apply NoDup_app in Hdup' as [_ [Hdup' _] ]. apply Hdup' in Ha. done.
          ** apply elem_of_list_difference in Ha as [Ha' Ha]; auto.
             apply HForallk in Hcontr. apply Hl' in Ha'.  congruence.
        * intros Hcontr. apply elem_of_app in Hcontr as [Hcontr | Hcontr].
          ** apply elem_of_list_difference in Hcontr as [Hcontr _]; auto.
             apply HForall in Ha. apply Hk' in Hcontr. congruence.
          ** apply NoDup_app in Hdup as [_ [Hdup _] ]. apply Hdup in Ha. done.
      + apply NoDup_app. split;[|split].
        * apply NoDup_list_difference. apply NoDup_app in Hdup' as [? [? ?] ]; auto.
        * intros a Ha. apply elem_of_list_difference in Ha as [_ Ha]; auto.
        * apply NoDup_app in Hdup as [? [? ?] ]; auto.
    - intros a. split.
      + intros Htemp.
        destruct (decide (a ∈ list_difference l' l));[by apply elem_of_app;left|].
        apply elem_of_app;right. apply Hl' in Htemp.
        assert (not (a ∈ l' ∧ a ∉ l)) as Hnot.
        { intros Hcontr. apply elem_of_list_difference in Hcontr. contradiction. }
        destruct (decide (a ∈ l)); auto.
        assert (a ∈ l' ∧ a ∉ l) as Hcontr; auto. apply Hnot in Hcontr. done.
      + intros Hin. apply elem_of_app in Hin as [Hin | Hin].
        ++ apply elem_of_list_difference in Hin as [Hinl Hninl'].
           by apply Hl'.
        ++ by apply HForall.
    - intros a. split.
      + intros Htemp.
        destruct (decide (a ∈ list_difference k' k));[by apply elem_of_app;left|].
        apply elem_of_app;right. apply Hk' in Htemp.
        assert (not (a ∈ k' ∧ a ∉ k)) as Hnot.
        { intros Hcontr. apply elem_of_list_difference in Hcontr. contradiction. }
        destruct (decide (a ∈ k)); auto.
        assert (a ∈ k' ∧ a ∉ k) as Hcontr; auto. apply Hnot in Hcontr. done.
      + intros Hin. apply elem_of_app in Hin as [Hin | Hin].
        ++ apply elem_of_list_difference in Hin as [Hinl Hninl'].
           by apply Hk'.
        ++ by apply HForallk.
  Qed.


  (* ---------------------------------------------------------------------------------------- *)
  (* ------------------ WE CAN UPDATE A REVOKED WORLD BACK TO TEMPORARY  -------------------- *)
  (* ---------------------------------------------------------------------------------------- *)

  (* closing will take every revoked element of l and reinstate it as Temporary,
     and every revoked element of k and reinstate it as Monotemporary. l and k
     are assumed to be disjoint *)
  Fixpoint close_list_std_sta_temp (l : list Addr) (fs : STS_STD) : STS_STD :=
    match l with
    | [] => fs
    | i :: l' => match fs !! i with
               | Some j => match j with
                          | Revoked => <[i := Temporary]> (close_list_std_sta_temp l' fs)
                          | _ => (close_list_std_sta_temp l' fs)
                          end
               | None => (close_list_std_sta_temp l' fs)
                 end
    end.
  Fixpoint close_list_std_sta_monotemp (l : list Addr) (fs : STS_STD) : STS_STD :=
    match l with
    | [] => fs
    | i :: l' => match fs !! i with
               | Some j => match j with
                          | Revoked => <[i := Monotemporary]> (close_list_std_sta_monotemp l' fs)
                          | _ => (close_list_std_sta_monotemp l' fs)
                          end
               | None => (close_list_std_sta_monotemp l' fs)
                 end
    end.
  Definition close_list l k W : WORLD := (close_list_std_sta_temp l (close_list_std_sta_monotemp k (std W)), loc W).

  Lemma close_list_std_sta_temp_is_Some Wstd_sta l i :
    is_Some (Wstd_sta !! i) <-> is_Some (close_list_std_sta_temp l Wstd_sta !! i).
  Proof.
    split.
    - induction l.
      + done.
      + intros [x Hx].
      simpl.
      destruct (Wstd_sta !! a);[|apply IHl;eauto].
      destruct r;try (apply IHl;eauto).
      destruct (decide (a = i)).
        * subst. rewrite lookup_insert. eauto.
        * rewrite lookup_insert_ne;eauto.
    - induction l.
      + done.
      + intros [x Hx].
        simpl in Hx.
        destruct (Wstd_sta !! a) eqn:Hsome;eauto.
        destruct r;try by (apply IHl;eauto).
        destruct (decide (a = i)).
        * subst. eauto.
        * rewrite lookup_insert_ne in Hx;eauto.
  Qed.

  Lemma close_list_std_sta_monotemp_is_Some Wstd_sta l i :
    is_Some (Wstd_sta !! i) <-> is_Some (close_list_std_sta_monotemp l Wstd_sta !! i).
  Proof.
    split.
    - induction l.
      + done.
      + intros [x Hx].
      simpl.
      destruct (Wstd_sta !! a);[|apply IHl;eauto].
      destruct r;try (apply IHl;eauto).
      destruct (decide (a = i)).
        * subst. rewrite lookup_insert. eauto.
        * rewrite lookup_insert_ne;eauto.
    - induction l.
      + done.
      + intros [x Hx].
        simpl in Hx.
        destruct (Wstd_sta !! a) eqn:Hsome;eauto.
        destruct r;try by (apply IHl;eauto).
        destruct (decide (a = i)).
        * subst. eauto.
        * rewrite lookup_insert_ne in Hx;eauto.
  Qed.

  Lemma close_list_std_sta_temp_None Wstd_sta l i :
    Wstd_sta !! i = None <-> close_list_std_sta_temp l Wstd_sta !! i = None.
  Proof.
    split.
    - intros Hnone. apply eq_None_not_Some.
      intros Hcontr. apply close_list_std_sta_temp_is_Some in Hcontr.
      apply eq_None_not_Some in Hcontr; auto.
    - intros Hnone. apply eq_None_not_Some.
      intros Hcontr. revert Hcontr. rewrite close_list_std_sta_temp_is_Some =>Hcontr.
      apply eq_None_not_Some in Hcontr; eauto.
  Qed.

  Lemma close_list_std_sta_monotemp_None Wstd_sta l i :
    Wstd_sta !! i = None <-> close_list_std_sta_monotemp l Wstd_sta !! i = None.
  Proof.
    split.
    - intros Hnone. apply eq_None_not_Some.
      intros Hcontr. apply close_list_std_sta_monotemp_is_Some in Hcontr.
      apply eq_None_not_Some in Hcontr; auto.
    - intros Hnone. apply eq_None_not_Some.
      intros Hcontr. revert Hcontr. rewrite close_list_std_sta_monotemp_is_Some =>Hcontr.
      apply eq_None_not_Some in Hcontr; eauto.
  Qed.

  Lemma close_list_dom_eq_temp Wstd_sta l :
    dom (gset Addr) Wstd_sta = dom (gset Addr) (close_list_std_sta_temp l Wstd_sta).
  Proof.
    apply gset_leibniz. split.
    - intros Hin.
      apply elem_of_gmap_dom. apply elem_of_gmap_dom in Hin.
      rewrite -close_list_std_sta_temp_is_Some.
      eauto.
    - intros Hin.
      apply elem_of_gmap_dom. apply elem_of_gmap_dom in Hin.
      rewrite close_list_std_sta_temp_is_Some.
      eauto.
  Qed.

  Lemma close_list_dom_eq_monotemp Wstd_sta l :
    dom (gset Addr) Wstd_sta = dom (gset Addr) (close_list_std_sta_monotemp l Wstd_sta).
  Proof.
    apply gset_leibniz. split.
    - intros Hin.
      apply elem_of_gmap_dom. apply elem_of_gmap_dom in Hin.
      rewrite -close_list_std_sta_monotemp_is_Some.
      eauto.
    - intros Hin.
      apply elem_of_gmap_dom. apply elem_of_gmap_dom in Hin.
      rewrite close_list_std_sta_monotemp_is_Some.
      eauto.
  Qed.

  Lemma close_list_std_sta_same_temp Wstd_sta l i :
    i ∉ l → Wstd_sta !! i = close_list_std_sta_temp l Wstd_sta !! i.
  Proof.
    intros Hnin. induction l.
    - done.
    - simpl. apply not_elem_of_cons in Hnin as [Hne Hnin].
      destruct (Wstd_sta !! a); auto.
      destruct r; auto.
      rewrite lookup_insert_ne; auto.
  Qed.

  Lemma close_list_std_sta_same_monotemp Wstd_sta l i :
    i ∉ l → Wstd_sta !! i = close_list_std_sta_monotemp l Wstd_sta !! i.
  Proof.
    intros Hnin. induction l.
    - done.
    - simpl. apply not_elem_of_cons in Hnin as [Hne Hnin].
      destruct (Wstd_sta !! a); auto.
      destruct r; auto.
      rewrite lookup_insert_ne; auto.
  Qed.

  Lemma close_list_std_sta_same_alt_temp Wstd_sta l i :
    Wstd_sta !! i ≠ Some Revoked ->
    Wstd_sta !! i = close_list_std_sta_temp l Wstd_sta !! i.
  Proof.
    intros Hnin. induction l.
    - done.
    - simpl. (* apply not_elem_of_cons in Hnin as [Hne Hnin].  *)
      destruct (Wstd_sta !! a) eqn:some; auto.
      destruct r; auto.
      destruct (decide (a = i)).
      + subst. contradiction.
      + rewrite lookup_insert_ne; auto.
  Qed.

  Lemma close_list_std_sta_same_alt_monotemp Wstd_sta l i :
    Wstd_sta !! i ≠ Some Revoked ->
    Wstd_sta !! i = close_list_std_sta_monotemp l Wstd_sta !! i.
  Proof.
    intros Hnin. induction l.
    - done.
    - simpl. (* apply not_elem_of_cons in Hnin as [Hne Hnin].  *)
      destruct (Wstd_sta !! a) eqn:some; auto.
      destruct r; auto.
      destruct (decide (a = i)).
      + subst. contradiction.
      + rewrite lookup_insert_ne; auto.
  Qed.

  Lemma close_list_std_sta_temp_revoked Wstd_sta l i :
    i ∈ l -> Wstd_sta !! i = Some Revoked →
    close_list_std_sta_temp l Wstd_sta !! i = Some Temporary.
  Proof.
    intros Hin Hrev. induction l.
    - inversion Hin.
    - apply elem_of_cons in Hin as [Heq | Hin].
      + subst. simpl. rewrite Hrev.
        rewrite lookup_insert. auto.
      + simpl. destruct (Wstd_sta !! a); auto.
        destruct r; auto.
        destruct (decide (i = a)); subst.
        * rewrite lookup_insert; auto.
        * rewrite lookup_insert_ne;auto.
  Qed.

  Lemma close_list_std_sta_monotemp_revoked Wstd_sta l i :
    i ∈ l -> Wstd_sta !! i = Some Revoked →
    close_list_std_sta_monotemp l Wstd_sta !! i = Some Monotemporary.
  Proof.
    intros Hin Hrev. induction l.
    - inversion Hin.
    - apply elem_of_cons in Hin as [Heq | Hin].
      + subst. simpl. rewrite Hrev.
        rewrite lookup_insert. auto.
      + simpl. destruct (Wstd_sta !! a); auto.
        destruct r; auto.
        destruct (decide (i = a)); subst.
        * rewrite lookup_insert; auto.
        * rewrite lookup_insert_ne;auto.
  Qed.


  Lemma close_list_related_sts_pub_cons_temp W a l :
    related_sts_pub_world W (close_list_std_sta_temp l (std W), loc W) →
    related_sts_pub_world W (close_list_std_sta_temp (a :: l) (std W), loc W).
  Proof.
    rewrite /close_list /=. intros IHl.
    destruct (std W !! a) eqn:Hsome; auto.
    destruct r;auto.
    apply related_sts_pub_trans_world with (close_list_std_sta_temp l (std W),loc W); auto.
    split;[|apply related_sts_pub_refl].
    split.
    + simpl. rewrite dom_insert /close_list /=.
      apply union_subseteq_r.
    + rewrite /close_list /=.
      intros i x y Hx Hy.
      destruct (decide (i = a)); subst.
      ++ rewrite lookup_insert in Hy. inversion Hy.
         subst.
         destruct (decide (a ∈ l)).
         +++ apply close_list_std_sta_temp_revoked with _ l _ in Hsome;auto.
             rewrite Hsome in Hx. inversion Hx. left.
         +++ rewrite (close_list_std_sta_same_temp _ l) in Hsome;auto.
             rewrite Hsome in Hx. inversion Hx. right with Temporary;[|left].
             constructor.
      ++ rewrite lookup_insert_ne in Hy; auto.
         rewrite Hx in Hy. inversion Hy. left.
  Qed.

  Lemma close_list_related_sts_pub_cons_monotemp W a l :
    related_sts_pub_world W (close_list_std_sta_monotemp l (std W), loc W) →
    related_sts_pub_world W (close_list_std_sta_monotemp (a :: l) (std W), loc W).
  Proof.
    rewrite /close_list /=. intros IHl.
    destruct (std W !! a) eqn:Hsome; auto.
    destruct r;auto.
    apply related_sts_pub_trans_world with (close_list_std_sta_monotemp l (std W),loc W); auto.
    split;[|apply related_sts_pub_refl].
    split.
    + simpl. rewrite dom_insert /close_list /=.
      apply union_subseteq_r.
    + rewrite /close_list /=.
      intros i x y Hx Hy.
      destruct (decide (i = a)); subst.
      ++ rewrite lookup_insert in Hy. inversion Hy.
         subst.
         destruct (decide (a ∈ l)).
         +++ apply close_list_std_sta_monotemp_revoked with _ l _ in Hsome;auto.
             rewrite Hsome in Hx. inversion Hx. left.
         +++ rewrite (close_list_std_sta_same_monotemp _ l) in Hsome;auto.
             rewrite Hsome in Hx. inversion Hx. right with Monotemporary;[|left].
             constructor.
      ++ rewrite lookup_insert_ne in Hy; auto.
         rewrite Hx in Hy. inversion Hy. left.
  Qed.

  (*
  Lemma close_list_related_sts_pub_cons_nested W a a0 l k :
    related_sts_pub_world W (close_list l (a0 :: k) W) →
    related_sts_pub_world W (close_list (a :: l) (a0 :: k) W).
  Proof.
    rewrite /close_list /=. intros IHl.
    destruct (std W !! a) eqn:Hsome; auto.
    destruct r;auto.
    apply related_sts_pub_trans_world with (close_list_std_sta_monotemp l (std W),loc W); auto.
    split;[|apply related_sts_pub_refl].
    split.
    + simpl. rewrite dom_insert /close_list /=.
      apply union_subseteq_r.
    + rewrite /close_list /=.
      intros i x y Hx Hy.
      destruct (decide (i = a)); subst.
      ++ rewrite lookup_insert in Hy. inversion Hy.
         subst.
         destruct (decide (a ∈ l)).
         +++ apply close_list_std_sta_monotemp_revoked with _ l _ in Hsome;auto.
             rewrite Hsome in Hx. inversion Hx. left.
         +++ rewrite (close_list_std_sta_same_monotemp _ l) in Hsome;auto.
             rewrite Hsome in Hx. inversion Hx. right with Monotemporary;[|left].
             constructor.
      ++ rewrite lookup_insert_ne in Hy; auto.
         rewrite Hx in Hy. inversion Hy. left.
  Qed.


  Lemma close_list_related_sts_pub_temp W l :
    related_sts_pub_world W (close_list_std_sta_temp l W.1,loc W).
  Proof.
    induction l.
    - rewrite /close_list /=. destruct W. apply related_sts_pub_refl_world.
    - apply close_list_related_sts_pub_cons_temp; auto. 
  Qed.
  Lemma close_list_related_sts_pub_monotemp W l :
    related_sts_pub_world W (close_list_std_sta_monotemp l W.1,loc W).
  Proof.
    induction l.
    - rewrite /close_list /=. destruct W. apply related_sts_pub_refl_world.
    - apply close_list_related_sts_pub_cons_monotemp; auto. 
  Qed.

  Lemma close_list_related_sts_pub W l k :
    related_sts_pub_world W (close_list l k W).
  Proof.
    induction l,k.
    - rewrite /close_list /=. destruct W; apply related_sts_pub_refl_world.
    - apply close_list_related_sts_pub_monotemp; auto.
    - apply close_list_related_sts_pub_temp.
    - 
    - intros k'. eapply related_sts_pub_trans_world;eauto.
      rewrite /close_list. 
      apply close_list_related_sts_pub_cons_temp; eauto.
      rewrite -/close_list. 
      apply close_list_related_sts_pub_cons_temp; auto.
    - 
      apply close_list_related_sts_pub_cons_monotemp; eauto.
      apply close_list_related_sts_pub_monotemp; eauto.
      eapply related_sts_pub_trans_world;eauto. 
      apply close_list_related_sts_pub_cons_temp; eauto.
      apply close_list_related_sts_pub_temp; eauto.
  Qed.

  Lemma close_list_related_sts_pub_insert' Wstd_sta Wloc i l :
    i ∉ l → Wstd_sta !! i = Some Revoked ->
    related_sts_pub_world
      (close_list_std_sta l ((std (Wstd_sta,Wloc))), Wloc)
      (<[i:=Temporary]> (close_list_std_sta l Wstd_sta), Wloc).
  Proof.
    intros Hnin Hlookup.
    split;[|apply related_sts_pub_refl]; simpl.
    split;auto.
    + apply elem_of_subseteq. intros j Hj.
      rewrite dom_insert_L. apply elem_of_union. right.
      apply elem_of_dom. apply elem_of_gmap_dom in Hj. done.
    + intros j x y Hx Hy.
      destruct (decide (i = j)); subst.
      * rewrite lookup_insert in Hy. rewrite -(close_list_std_sta_same _ l) in Hx; auto.
        rewrite Hlookup in Hx. inversion Hx; inversion Hy; subst.
        right with Temporary;[|left]. constructor.
      * rewrite lookup_insert_ne in Hy; auto. rewrite Hx in Hy. inversion Hy. left.
  Qed.

  Lemma close_list_related_sts_pub_insert Wstd_sta Wloc i l :
    i ∉ l → Wstd_sta !! i = Some Revoked ->
    related_sts_pub_world
      (Wstd_sta, Wloc)
      (<[i:= Temporary]> (close_list_std_sta l Wstd_sta), Wloc).
  Proof.
    intros Hnin Hlookup.
    apply related_sts_pub_trans_world with (close_list_std_sta l ((std (Wstd_sta, Wloc))), Wloc).
    - apply close_list_related_sts_pub.
    - apply close_list_related_sts_pub_insert'; auto.
  Qed.

  Lemma close_revoke_iff Wstd_sta (l : list Addr) :
     (forall (i : Addr), Wstd_sta !! i = Some Temporary <-> i ∈ l) ->
     ∀ i, (close_list_std_sta l (revoke_std_sta Wstd_sta)) !! i =
          Wstd_sta !! i.
  Proof.
    intros Hiff.
    intros i. destruct (decide (i ∈ l)).
    + apply Hiff in e as Htemp. rewrite Htemp.
      apply close_list_std_sta_revoked;[auto|].
      apply revoke_lookup_Temp; auto.
    + apply (close_list_std_sta_same (revoke_std_sta Wstd_sta)) in n as Heq. rewrite -Heq.
      apply revoke_monotone_lookup_same.
      intros Hcontr. apply Hiff in Hcontr. contradiction.
  Qed.

  Lemma close_revoke_eq Wstd_sta (l : list Addr) :
    (forall (i : Addr), Wstd_sta !! i = Some Temporary <-> i ∈ l) ->
    (close_list_std_sta l (revoke_std_sta Wstd_sta)) = Wstd_sta.
  Proof.
    intros Hiff.
    eapply (map_leibniz (M:=gmap Addr) (A:=region_type)). Unshelve. intros i. apply leibniz_equiv_iff.
    apply close_revoke_iff. auto. apply _.
  Qed.

  Lemma close_list_std_sta_idemp Wstd_sta (l1 l2 : list Addr) :
    close_list_std_sta l1 (close_list_std_sta l2 Wstd_sta) = close_list_std_sta (l1 ++ l2) Wstd_sta.
  Proof.
    induction l1;[done|].
    simpl. rewrite IHl1.
    destruct (Wstd_sta !! a) eqn:Hsome.
    - destruct (decide (Revoked = r)).
      + subst.
        destruct (decide (a ∈ l2)).
        ++ apply close_list_std_sta_revoked with (l:=l2) in Hsome as Hsome'; auto.
           rewrite Hsome'.
           rewrite insert_id;auto.
           apply close_list_std_sta_revoked;auto.
           apply elem_of_app;by right.
        ++ rewrite (close_list_std_sta_same _ l2) in Hsome;auto.
           rewrite Hsome. auto.
      + assert (Wstd_sta !! a ≠ Some Revoked) as Hnrev.
        { intros Hcontr. congruence. }
        rewrite (close_list_std_sta_same_alt _ l2) in Hsome;auto.
        by rewrite Hsome.
    - apply (close_list_std_sta_None _ l2) in Hsome. rewrite Hsome. done.
  Qed.

  (* The following closes resources that are valid in the current world *)
  Lemma monotone_close W l p φ `{forall Wv, Persistent (φ Wv)} :
    ([∗ list] a ∈ l, temp_resources W φ a p ∗ rel a p φ
                                    ∗ ⌜(std W) !! a = Some Revoked⌝)
    ∗ sts_full_world W ∗ region W ==∗
    sts_full_world (close_list l W)
    ∗ region (close_list l W).
  Proof.
    iIntros "(Hl & Hfull & Hr)".
    iAssert (⌜NoDup l⌝)%I as %Hdup.
    { iClear "Hfull Hr".
      iInduction (l) as [|x l] "IH".
      - iPureIntro. by apply NoDup_nil.
      - iDestruct "Hl" as "[Ha Hl]".
        iDestruct ("IH" with "Hl") as %Hdup.
        iAssert (⌜x ∉ l⌝)%I as %Hnin.
        { iIntros (Hcontr). iDestruct (big_sepL_elem_of _ _ x with "Hl") as "[Ha' Hcontr]"; auto.
          rewrite /temp_resources /=.
          iDestruct "Ha" as "(Ha & _)".
          iDestruct "Ha" as (v) "(% & Ha & _)".
          iDestruct "Ha'" as (v') "(% & Ha' & _)".
          iApply (cap_duplicate_false with "[$Ha $Ha']"); auto.
        } iPureIntro. apply NoDup_cons. split; auto.
    }
    iInduction (l) as [|x l] "IH".
    - iFrame. destruct W as [ Wstd_sta Wloc]; done.
    - apply NoDup_cons in Hdup as [Hdup Hnin].
      iDestruct "Hl" as "[ [Hx #[Hrel Hrev] ] Hl]".
      rewrite /close_list region_eq /region_def /std /=.
      iMod ("IH" $! Hnin with "Hl Hfull Hr") as "(Hfull & Hr)"; auto.
      iClear "IH".
      destruct W as [ Wstd_sta Wloc].
      iDestruct "Hx" as (a HO) "(Hx & Hmono & Hφ)".
      iDestruct "Hr" as (M Mρ) "(HM & #Hdom & #Hdom' & Hr)". iDestruct "Hdom" as %Hdom. iDestruct "Hdom'" as %Hdom'.
      rewrite rel_eq /rel_def REL_eq RELS_eq. iDestruct "Hrel" as (γpred) "[HREL Hpred]".
      iDestruct (reg_in γrel M with "[$HM $HREL]") as %HMeq. rewrite HMeq.
      iDestruct (big_sepM_delete _ _ x with "Hr") as "[Hstate Hr]"; [apply lookup_insert|].
      iDestruct "Hstate" as (ρ Mx) "[Hρ Hstate]".
      iDestruct (sts_full_state_std with "Hfull Hρ") as %Hx''.
      rewrite -(close_list_std_sta_same _ l _) in Hx''; auto.
      rewrite  Hx''. iFrame.
      iDestruct "Hrev" as %Hrev. inversion Hrev as [Heq]. subst ρ.
      iMod (sts_update_std _ _ _ Temporary with "Hfull Hρ") as "[Hfull Hρ] /=". iFrame.
      iModIntro. iExists M,(<[x:=Temporary]> Mρ). rewrite HMeq.
      iDestruct (region_map_delete_nonstatic with "Hr") as "Hr";[intros m; by rewrite Mx|].
      iDestruct (region_map_insert_nonstatic Temporary with "Hr") as "Hr";auto.
      rewrite /region_map_def.
      iDestruct (big_sepM_delete _ _ x with "[Hρ Hr Hx Hmono Hφ]") as "$"; [apply lookup_insert|..].
      { do 2 (rewrite delete_insert;[|apply lookup_delete]).
        iSplitR "Hr".
        - iExists Temporary. iFrame. iSplit;[iPureIntro;apply lookup_insert|].
          rewrite /future_pub_mono. iExists γpred,p,φ.
          repeat (iSplit; auto). iExists a. iSplit;auto.
          iAssert (future_pub_mono φ a) as "#Hmono'".
          { destruct (pwl p); iDestruct "Hmono" as "#Hmono"; iModIntro.
            - iIntros (W' W'' Hrelated) "Hφ". iApply ("Hmono" with "[] Hφ"). auto.
            - iIntros (W' W'' Hrelated) "Hφ". iApply ("Hmono" with "[] Hφ"). iPureIntro. apply related_sts_pub_priv_world. auto.
          }
          iFrame "# ∗".
          iNext. iApply "Hmono'"; iFrame.
          iPureIntro. apply close_list_related_sts_pub_insert; auto.
        - iApply (big_sepM_mono with "Hr").
          iIntros (a' γp Hsome) "Hρ /=". iDestruct "Hρ" as (ρ Ha) "[Hstate Hρ]".
          iExists ρ. iFrame. destruct ρ; auto.
          + iDestruct "Hρ" as (γpred' p' φ0 Heq Hpers) "(#Hpred & Hρ)".
            iDestruct "Hρ" as (v) "(HO & Ha' & Hmono & Hφ0)".
            iSplit;auto. iExists _,_,_.
            iAssert (future_pub_mono φ0 v) as "#Hmono'".
            { destruct (pwl p'); iDestruct "Hmono" as "#Hmono"; iModIntro.
              - iIntros (W' W'' Hrelated) "Hφ". iApply ("Hmono" with "[] Hφ"). auto.
              - iIntros (W' W'' Hrelated) "Hφ". iApply ("Hmono" with "[] Hφ"). iPureIntro. apply related_sts_pub_priv_world. auto.
            } iFrame. repeat (iSplit;eauto). iExists _. iFrame.
            iNext. iApply ("Hmono'" with "[] Hφ0"). iPureIntro.
            apply close_list_related_sts_pub_insert'; auto.
          + iDestruct "Hρ" as (γpred' p' φ0 Heq' Hpers) "(#Hpred & Hρ)".
            iDestruct "Hρ" as (v) "(HO & Ha' & #Hmono & Hφ0)".
            iSplit;auto. iExists _,_,_. iFrame "∗ #". repeat iSplit;auto.
            iExists _; iFrame "∗ #". iNext. iApply ("Hmono" with "[] Hφ0"). iPureIntro.
            apply related_sts_pub_priv_world.
            apply close_list_related_sts_pub_insert'; auto.
      }
      do 2 (rewrite -HMeq). iFrame. iPureIntro.
      (* The domains remain equal *)
      split.
      { rewrite -Hdom. rewrite dom_insert_L.
        assert (x ∈ dom (gset Addr) M) as Hin.
        { apply elem_of_gmap_dom. rewrite HMeq. rewrite lookup_insert. eauto. }
        rewrite Hdom. set_solver.
      }
      rewrite dom_insert_L. assert (x ∈ dom (gset Addr) Mρ) as Hin;[apply elem_of_gmap_dom;eauto|].
      rewrite -Hdom'. set_solver.
  Qed.

  Lemma monotone_revoked_close_sub W l p φ `{forall Wv, Persistent (φ Wv)} :
    ([∗ list] a ∈ l, temp_resources (revoke W) φ a p ∗ rel a p φ
                                    ∗ ⌜(std (revoke W)) !! a = Some Revoked⌝)
    ∗ sts_full_world (revoke W) ∗ region (revoke W) ==∗
    sts_full_world (close_list l (revoke W))
    ∗ region (close_list l (revoke W)).
  Proof.
    iIntros "(Hl & Hfull & Hr)".
    iApply monotone_close; eauto.
    iFrame.
  Qed.

  (* However, we also want to be able to close regions that were valid in some world W, and which will be valid again
     in a public future world close l W' ! This is slightly more tricky: we must first update the region monotonically,
     after which it will be possible to consolidate the full_sts and region *)

  Lemma close_list_consolidate W W' (l' l : list Addr) :
    ⊢ ⌜l' ⊆+ l⌝ →
     ⌜related_sts_pub_world W (close_list_std_sta l (std W'), loc W')⌝ →
     (region (close_list l W') ∗ sts_full_world W'
            ∗ ([∗ list] a ∈ l', ∃ p φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗ temp_resources W φ a p ∗ rel a p φ))
       ==∗ (sts_full_world (close_list l' W') ∗ region (close_list l W')).
  Proof.
    iIntros (Hsub Hrelated) "(Hr & Hsts & Htemps)".
    iInduction l' as [|x l'] "IH".
    - simpl. iFrame. done.
    - iDestruct "Htemps" as "[Hx Htemps]".
      assert (l' ⊆+ l) as Hsub'.
      { apply submseteq_cons_l in Hsub as [k [Hperm Hsub] ]. rewrite Hperm.
        apply submseteq_cons_r. left. auto. }
      iMod ("IH" $! Hsub' with "Hr Hsts Htemps") as "[Hsts Hr]".
      iClear "IH".
      rewrite /close_list /=.
      iDestruct "Hx" as (p φ Hpers) "(Htemp & Hrel)".
      iDestruct "Htemp" as (v) "(Hne & Hx' & Hmono & Hφ)".
      destruct (std W' !! x) eqn:Hsome;[|iFrame;done].
      destruct (decide (Revoked = r)).
      + subst.
        assert (x ∈ l) as Hinl.
        { apply elem_of_submseteq with (x0:=x) in Hsub;[auto|apply elem_of_cons;by left]. }
        rewrite region_eq /region_def /region_map_def.
        iDestruct "Hr" as (M Mρ) "(HM & #Hdom & #Hdom' & Hr)".
        iDestruct "Hdom" as %Hdom. iDestruct "Hdom'" as %Hdom'.
        rewrite RELS_eq rel_eq /RELS_def /rel_def REL_eq /REL_def.
        iDestruct "Hrel" as (γpred) "#[Hrel Hsaved]".
        iDestruct (reg_in with "[$HM $Hrel]") as %HMeq. rewrite HMeq.
        iDestruct (big_sepM_delete _ _ x with "Hr") as "[Hx Hr]";[apply lookup_insert|].
        rewrite delete_insert;[|apply lookup_delete].
        iDestruct "Hx" as (ρ Hx) "[Hstate Hx]".
        destruct ρ.
        { iDestruct "Hx" as (γpred' p' φ' Heq Hpers') "(_ & Hx)".
          iDestruct "Hx" as (v' Hne) "(Hx & _)".
          inversion Heq; subst.
          iApply bi.False_elim. iApply (cap_duplicate_false with "[$Hx' $Hx]"); auto. }
        { iDestruct "Hx" as (γpred' p' φ' Heq Hpers') "(_ & Hx)".
          iDestruct "Hx" as (v' Hne) "(Hx & _)".
          inversion Heq; subst.
          iApply bi.False_elim. iApply (cap_duplicate_false with "[$Hx' $Hx]"); auto. }
        2 : {
          iDestruct "Hx" as (γpred' p' φ' Heq Hpers') "(_ & Hx)".
          iDestruct "Hx" as (v' Hge Hne') "(Hx & _)". iDestruct "Hne" as %Hne.
          iApply bi.False_elim. iApply (cap_duplicate_false with "[$Hx' $Hx]"); split; auto. }
        iMod (sts_update_std _ _ _ Temporary with "Hsts Hstate") as "[Hsts Hstate]". rewrite HMeq.
        iDestruct (region_map_delete_nonstatic with "Hr") as "Hr";[intros m;by rewrite Hx|].
        iDestruct (region_map_insert_nonstatic Temporary with "Hr") as "Hr"; auto.
        iDestruct (big_sepM_delete _ _ x with "[Hne Hx' Hmono Hφ Hstate $Hr]") as "Hr";[apply lookup_insert|..].
        { iExists Temporary. iFrame. rewrite lookup_insert. iSplit;auto. iExists γpred,p,φ. repeat (iSplit;auto).
          destruct (pwl p).
          - iDestruct "Hmono" as "#Hmono". iExists _. iFrame "∗#".
            iApply ("Hmono" with "[] Hφ"). auto.
          - iDestruct "Hmono" as "#Hmono". iExists _. iFrame "∗#".
            iApply ("Hmono" with "[] Hφ"). iPureIntro.
            apply related_sts_pub_priv_world; auto.
        }
        iFrame. iExists M,_. rewrite -HMeq. iFrame. rewrite -HMeq. iFrame. iModIntro. iSplit; auto.
        iPureIntro. rewrite dom_insert_L. rewrite -Hdom'.
        assert (x ∈ dom (gset Addr) Mρ);[apply elem_of_gmap_dom;eauto|]. set_solver.
      + iFrame. destruct r; done.
  Qed.

  Lemma monotone_close_list_region W W' (l : list Addr) :
    ⊢ ⌜related_sts_pub_world W (close_list l W')⌝ -∗
      sts_full_world W' ∗ region W'
      ∗ ([∗ list] a ∈ l, ∃ p φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗ temp_resources W φ a p ∗ rel a p φ)
       ==∗ (sts_full_world (close_list l W') ∗ region (close_list l W')).
  Proof.
    iIntros (Hrelated) "(Hsts & Hr & Htemp)".
    assert (related_sts_pub_world W' (close_list l W')) as Hrelated'.
    { apply close_list_related_sts_pub; auto. }
    assert (dom (gset Addr) (std W') = dom (gset Addr) (std (close_list l W'))) as Heq.
    { apply close_list_dom_eq. }
    iDestruct (region_monotone _ _ Heq Hrelated' with "Hr") as "Hr". clear Hrelated'.
    iMod (close_list_consolidate _ _ l with "[] [] [$Hr $Hsts $Htemp]") as "[Hsts Hr]";[auto|eauto|iFrame;done].
  Qed.*)

End heap.
