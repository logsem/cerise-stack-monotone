From iris.algebra Require Import gmap agree auth.
From iris.proofmode Require Import tactics.
From cap_machine Require Export region_invariants.
Import uPred. 

Section heap.
  Context `{heapG Σ, memG Σ, regG Σ, STSG Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ}.
  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation WORLD := (prodO STS STS). 
  Implicit Types W : WORLD.

  (* --------------------------------------------------------------------------------------------------------- *)
  (* --------------------------------------------- REVOCATION ------------------------------------------------ *)
  (* --------------------------------------------------------------------------------------------------------- *)

  (* 
     Revocation turns every temporary location state to revoked. 
     Revocation is crucial to privately update state: in general, 
     region states are only monotone with regards to public future 
     world. To do a private update, we must thus revoke all temp 
     regions, after which we only have regions that are indeed 
     monotone wrt private future world.
   *)
  

  (* Revocation only changes the states of the standard STS collection *)
  Definition revoke_std_sta : STS_states → STS_states :=
    fmap (λ v, if ((countable.encode Temporary) =? v)%positive then countable.encode Revoked else v). 
  Definition revoke W : WORLD := ((revoke_std_sta (std_sta W),std_rel W), loc W).

  (* A weaker revocation which only revokes elements from a list *)
  Fixpoint revoke_list_std_sta (l : list positive) (fs : STS_states) : STS_states :=
    match l with
    | [] => fs
    | i :: l' => match fs !! i with
               | Some j => if ((countable.encode Temporary) =? j)%positive
                          then <[i := countable.encode Revoked]> (revoke_list_std_sta l' fs)
                          else (revoke_list_std_sta l' fs)
               | None => (revoke_list_std_sta l' fs)
               end
    end.
  Definition revoke_list l W : WORLD := ((revoke_list_std_sta l (std_sta W),std_rel W), loc W).


  (* ------------------------------------------------------------------- *)
  (* region_map is monotone with regards to public future world relation *)
  
  Lemma region_map_monotone W W' M :
    (⌜related_sts_pub_world W W'⌝ →
     region_map_def M W -∗ region_map_def M W')%I.
  Proof.
    iIntros (Hrelated) "Hr".
    iApply big_sepM_mono; iFrame. 
    iIntros (a γ Hsome) "Hm".
    iDestruct "Hm" as (ρ) "[Hstate Hm]".
    iExists ρ. iFrame. 
    destruct ρ.
    - iDestruct "Hm" as (γpred v p φ Heq HO) "(Hl & Hmono & #Hsavedφ & Hφ)".
      iExists _,_,_,_. do 2 (iSplitR;[eauto|]).
      destruct (pwl p);
      (iDestruct "Hmono" as "#Hmono"; iFrame "∗ #";
        iApply "Hmono"; iFrame; auto); 
      try (iPureIntro; by apply related_sts_pub_priv_world).      
    - iDestruct "Hm" as (γpred v p φ Heq HO) "(Hl & #Hmono & #Hsavedφ & Hφ)".
      iExists _,_,_,_. do 2 (iSplitR;[eauto|]).
      iFrame "∗ #".
      iApply "Hmono"; iFrame; auto. 
      iPureIntro. 
      by apply related_sts_pub_priv_world. 
    - done.
  Qed. 
    
  Lemma region_monotone W W' :
    (⌜dom (gset positive) (std_sta W) = dom (gset positive) (std_sta W')⌝ →
     ⌜related_sts_pub_world W W'⌝ → region W -∗ region W')%I.
  Proof.
    iIntros (Hdomeq Hrelated) "HW". rewrite region_eq.
    iDestruct "HW" as (M) "(HM & % & Hmap)". 
    iExists (M). iFrame.
    iApply (wand_frame_r _ emp%I).
    { iIntros (_).
      iPureIntro.
      intros a. split; intros [x Hx].
      - destruct H3 with a as [Hstd _].
        apply Hstd. apply elem_of_gmap_dom.
        rewrite Hdomeq. apply elem_of_gmap_dom. eauto.
      - destruct H3 with a as [_ Hstd].
        apply elem_of_gmap_dom. rewrite -Hdomeq.
        apply elem_of_gmap_dom. eauto.
    } iSplitR;[auto|].
    iApply region_map_monotone; eauto. 
  Qed.    
    
  Lemma related_sts_pub_world_fresh W a ρ :
    (countable.encode a) ∉ dom (gset positive) (std_sta W) →
    (countable.encode a) ∉ dom (gset positive) (std_rel W) →
    related_sts_pub_world W (<s[a:=ρ,(Rpub,Rpriv)]s> W).
  Proof.
    rewrite /std_sta /std_rel. intros Hdom_sta Hdom_rel.
    rewrite /related_sts_pub_world /=.
    split;[|apply related_sts_pub_refl].
    rewrite /related_sts_pub. split;[|split;[auto|] ]. 
    - apply dom_insert_subseteq.
    - apply dom_insert_subseteq. 
    - apply not_elem_of_dom in Hdom_sta.
      apply not_elem_of_dom in Hdom_rel.
      intros i r1 r2 r1' r2' Hr Hr'. 
      destruct (decide (countable.encode a = i)).
      + subst. rewrite Hr in Hdom_rel. done. 
      + rewrite lookup_insert_ne in Hr'; auto.
        rewrite Hr in Hr'. inversion Hr'. repeat (split;auto).
        intros x y Hx Hy. 
        rewrite lookup_insert_ne in Hy;auto.
        rewrite Hx in Hy. 
        inversion Hy; inversion Hr'; subst.
        left.
  Qed.

   Lemma related_sts_pub_world_fresh_state W a ρ :
    (countable.encode a) ∉ dom (gset positive) (std_sta W) →
    rel_is_std_i W (countable.encode a) →
    related_sts_pub_world W (<s[a:=ρ,(Rpub,Rpriv)]s> W).
  Proof.
    rewrite /std_sta /std_rel. intros Hdom_sta Hdom_rel.
    rewrite /related_sts_pub_world /=.
    split;[|apply related_sts_pub_refl].
    rewrite /related_sts_pub. split;[|split;[auto|] ]. 
    - apply dom_insert_subseteq.
    - apply dom_insert_subseteq. 
    - apply not_elem_of_dom in Hdom_sta.
      intros i r1 r2 r1' r2' Hr Hr'. 
      destruct (decide (countable.encode a = i)).
      + subst. rewrite /rel_is_std_i Hr in Hdom_rel. rewrite lookup_insert in Hr'. simplify_eq.
        repeat (split;auto). intros x y Hcontr. rewrite Hcontr in Hdom_sta. done. 
      + rewrite lookup_insert_ne in Hr'; auto.
        rewrite Hr in Hr'. inversion Hr'. repeat (split;auto).
        intros x y Hx Hy. 
        rewrite lookup_insert_ne in Hy;auto.
        rewrite Hx in Hy. 
        inversion Hy; inversion Hr'; subst.
        left.
  Qed.

  Lemma related_sts_pub_world_revoked_temp W a :
    (std_sta W) !! (countable.encode a) = Some (countable.encode Revoked) ∨
    (std_sta W) !! (countable.encode a) = Some (countable.encode Temporary) →
    rel_is_std_i W (countable.encode a) →
    related_sts_pub_world W (<s[a:=Temporary,(Rpub, Rpriv)]s>W).
  Proof.
    intros Ha Hstd.
    rewrite /related_sts_pub_world /=.
    split;[|apply related_sts_pub_refl].
    rewrite /related_sts_pub. split;[|split;[auto|] ]. 
    - apply dom_insert_subseteq.
    - apply dom_insert_subseteq. 
    - intros i r1 r2 r1' r2' Hr Hr'. 
      destruct (decide (countable.encode a = i)).
      + subst. rewrite /rel_is_std_i Hr in Hstd. rewrite lookup_insert in Hr'. simplify_eq.
        repeat (split;auto). intros x y Hx Hy.
        rewrite Hx in Ha.
        destruct Ha as [Ha | Ha]; inversion Ha.
        ++ rewrite lookup_insert in Hy. inversion Hy.
           right with (countable.encode Temporary);[|left].
           exists Revoked,Temporary. repeat (split;auto).
        ++ rewrite lookup_insert in Hy. inversion Hy. left. 
      + rewrite lookup_insert_ne in Hr'; auto.
        rewrite Hr in Hr'. inversion Hr'. repeat (split;auto).
        intros x y Hx Hy. 
        rewrite lookup_insert_ne in Hy;auto.
        rewrite Hx in Hy. 
        inversion Hy; inversion Hr'; subst.
        left.
  Qed.

  (* ----------------------------------------------------------------------------------------------- *)
  (* ----------------------- LEMMAS FOR EXTENDING THE REGION MAP ----------------------------------- *)
  
  Lemma extend_region_temp_pwl E W l p v φ `{∀ W v, Persistent (φ (W,v))}:
     p ≠ O →
     (countable.encode l) ∉ dom (gset positive) (std_sta W) →
     (countable.encode l) ∉ dom (gset positive) (std_rel W) →
     (pwl p) = true →
     (future_pub_mono φ v →
     sts_full_world sts_std W -∗ region W -∗ l ↦ₐ[p] v -∗ φ (W,v) ={E}=∗ region (<s[l := Temporary, (Rpub,Rpriv) ]s>W)
                                                              ∗ rel l p φ
                                                              ∗ sts_full_world sts_std (<s[l := Temporary, (Rpub,Rpriv)]s>W))%I.
  Proof.
    iIntros (Hpne Hnone1 Hnone2 Hpwl) "#Hmono Hfull Hreg Hl #Hφ".
    rewrite region_eq rel_eq /region_def /rel_def.
    iDestruct "Hreg" as (M) "(Hγrel & % & Hpreds)".
    rewrite RELS_eq /RELS_def. 
    (* destruct on M !! l *)
    destruct (M !! l) eqn:HRl.
    { (* The location is not in the map *)
      iDestruct (big_sepM_delete _ _ _ _ HRl with "Hpreds") as "[Hl' _]".
      iDestruct "Hl'" as (ρ') "[Hstate Hl']". 
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
      apply not_elem_of_dom in Hnone1. 
      rewrite Hcontr in Hnone1. done.
    }
    (* if not, we need to allocate a new saved pred using φ, 
       and extend R with l := pred *)
    iMod (saved_pred_alloc φ) as (γpred) "#Hφ'".
    iMod (own_update _ _ (● (<[l:=to_agree (γpred,_)]> (to_agree <$> M : relUR)) ⋅ ◯ ({[l:=to_agree (γpred,_)]}))
            with "Hγrel") as "[HR #Hγrel]". 
    { apply auth_update_alloc.
      apply (alloc_singleton_local_update (to_agree <$> M)); last done.
      rewrite lookup_fmap. rewrite HRl. done. 
    }
    (* we also need to extend the World with a new temporary region *)
    iMod (sts_alloc_std_i W (countable.encode l) Temporary
            with "[] Hfull") as "(Hfull & Hstate)"; auto.     
    apply (related_sts_pub_world_fresh W l Temporary) in Hnone1 as Hrelated; auto.
    iDestruct (region_map_monotone $! Hrelated with "Hpreds") as "Hpreds'".
    iModIntro. rewrite bi.sep_exist_r. iExists _.
    rewrite -fmap_insert. 
    iFrame "HR". iFrame.
    iSplitL;[iSplitR|].
    - iPureIntro. apply dom_equal_insert; auto. 
    - iApply big_sepM_insert; auto.
      iFrame. iExists Temporary.
      iFrame. iExists γpred,v,_,φ. iSplitR;[auto|]. iFrame "∗ #".
      iSplitR;[done|].
      rewrite Hpwl. iFrame "#".
      iNext. iApply "Hmono"; eauto.
    - iExists γpred. iFrame "#".
      rewrite REL_eq /REL_def. 
      done. 
  Qed.

  Lemma extend_region_temp_nwl E W l p v φ `{∀ W v, Persistent (φ (W,v))}:
     p ≠ O →
     (countable.encode l) ∉ dom (gset positive) (std_sta W) →
     (countable.encode l) ∉ dom (gset positive) (std_rel W) →
     (pwl p) = false →
     (future_priv_mono φ v →
     sts_full_world sts_std W -∗ region W -∗ l ↦ₐ[p] v -∗ φ (W,v) ={E}=∗ region (<s[l := Temporary, (Rpub,Rpriv) ]s>W)
                                                              ∗ rel l p φ
                                                              ∗ sts_full_world sts_std (<s[l := Temporary, (Rpub,Rpriv)]s>W))%I.
  Proof.
    iIntros (Hpne Hnone1 Hnone2 Hpwl) "#Hmono Hfull Hreg Hl #Hφ".
    rewrite region_eq rel_eq /region_def /rel_def.
    iDestruct "Hreg" as (M) "(Hγrel & % & Hpreds)".
    rewrite RELS_eq /RELS_def. 
    (* destruct on M !! l *)
    destruct (M !! l) eqn:HRl.
    { (* The location is not in the map *)
      iDestruct (big_sepM_delete _ _ _ _ HRl with "Hpreds") as "[Hl' _]".
      iDestruct "Hl'" as (ρ') "[Hstate Hl']". 
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
      apply not_elem_of_dom in Hnone1. 
      rewrite Hcontr in Hnone1. done.
    }
    (* if not, we need to allocate a new saved pred using φ, 
       and extend R with l := pred *)
    iMod (saved_pred_alloc φ) as (γpred) "#Hφ'".
    iMod (own_update _ _ (● (<[l:=to_agree (γpred,_)]> (to_agree <$> M : relUR)) ⋅ ◯ ({[l:=to_agree (γpred,_)]}))
            with "Hγrel") as "[HR #Hγrel]". 
    { apply auth_update_alloc.
      apply (alloc_singleton_local_update (to_agree <$> M)); last done.
      rewrite lookup_fmap. rewrite HRl. done. 
    }
    (* we also need to extend the World with a new temporary region *)
    iMod (sts_alloc_std_i W (countable.encode l) Temporary
            with "[] Hfull") as "(Hfull & Hstate)"; auto.     
    apply (related_sts_pub_world_fresh W l Temporary) in Hnone1 as Hrelated; auto. 
    iDestruct (region_map_monotone $! Hrelated with "Hpreds") as "Hpreds'".
    iModIntro. rewrite bi.sep_exist_r. iExists _.
    rewrite -fmap_insert. 
    iFrame "HR". iFrame.
    iSplitL;[iSplitR|].
    - iPureIntro. apply dom_equal_insert; auto. 
    - iApply big_sepM_insert; auto.
      iFrame. iExists Temporary.
      iFrame. iExists γpred,v,_,φ. iSplitR;[auto|]. iFrame "∗ #".
      iSplitR;[done|].
      rewrite Hpwl. iFrame "#".
      iNext. iApply "Hmono"; eauto.
      iPureIntro. by apply related_sts_pub_priv_world. 
    - iExists γpred. iFrame "#".
      rewrite REL_eq /REL_def. 
      done. 
  Qed.

  Lemma extend_region_perm E W l p v φ `{∀ W v, Persistent (φ (W,v))}:
     p ≠ O →
     (countable.encode l) ∉ dom (gset positive) (std_sta W) →
     (countable.encode l) ∉ dom (gset positive) (std_rel W) →
     (future_priv_mono φ v →
     sts_full_world sts_std W -∗ region W -∗ l ↦ₐ[p] v -∗ φ (W,v) ={E}=∗ region (<s[l := Permanent, (Rpub,Rpriv) ]s>W)
                                                              ∗ rel l p φ
                                                              ∗ sts_full_world sts_std (<s[l := Permanent, (Rpub,Rpriv)]s>W))%I.
  Proof.
    iIntros (Hpne Hnone1 Hnone2) "#Hmono Hfull Hreg Hl #Hφ".
    rewrite region_eq rel_eq /region_def /rel_def.
    iDestruct "Hreg" as (M) "(Hγrel & % & Hpreds)".
    rewrite RELS_eq /RELS_def. 
    (* destruct on M !! l *)
    destruct (M !! l) eqn:HRl.
    { (* The location is not in the map *)
      iDestruct (big_sepM_delete _ _ _ _ HRl with "Hpreds") as "[Hl' _]".
      iDestruct "Hl'" as (ρ') "[Hstate Hl']". 
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
      apply not_elem_of_dom in Hnone1. 
      rewrite Hcontr in Hnone1. done.
    }
    (* if not, we need to allocate a new saved pred using φ, 
       and extend R with l := pred *)
    iMod (saved_pred_alloc φ) as (γpred) "#Hφ'".
    iMod (own_update _ _ (● (<[l:=to_agree (γpred,_)]> (to_agree <$> M : relUR)) ⋅ ◯ ({[l:=to_agree (γpred,_)]}))
            with "Hγrel") as "[HR #Hγrel]". 
    { apply auth_update_alloc.
      apply (alloc_singleton_local_update (to_agree <$> M)); last done.
      rewrite lookup_fmap. rewrite HRl. done. 
    }
    (* we also need to extend the World with a new temporary region *)
    iMod (sts_alloc_std_i W (countable.encode l) Permanent
            with "[] Hfull") as "(Hfull & Hstate)"; auto.     
    apply (related_sts_pub_world_fresh W l Permanent) in Hnone1 as Hrelated; auto. 
    iDestruct (region_map_monotone $! Hrelated with "Hpreds") as "Hpreds'".
    iModIntro. rewrite bi.sep_exist_r. iExists _.
    rewrite -fmap_insert. 
    iFrame "HR". iFrame.
    iSplitL;[iSplitR|].
    - iPureIntro. apply dom_equal_insert; auto. 
    - iApply big_sepM_insert; auto.
      iFrame. iExists Permanent.
      iFrame. iExists γpred,v,_,φ. iSplitR;[auto|]. iFrame "∗ #".
      iSplitR;[done|].
      iNext. iApply "Hmono"; eauto.
      iPureIntro. by apply related_sts_pub_priv_world. 
    - iExists γpred. iFrame "#".
      rewrite REL_eq /REL_def. 
      done. 
  Qed.

  (* The following allocates a Revoked region. This allocates the saved predicate and the region state, *)
  (* but since a revoked region is empty, there is no need to assume any resources for that region *)

  Lemma extend_region_revoked E W l p φ :
     (countable.encode l) ∉ dom (gset positive) (std_sta W) →
     (countable.encode l) ∉ dom (gset positive) (std_rel W) →
     (sts_full_world sts_std W -∗ region W ={E}=∗ region (<s[l := Revoked, (Rpub,Rpriv) ]s>W)
                                               ∗ rel l p φ
                                               ∗ sts_full_world sts_std (<s[l := Revoked, (Rpub,Rpriv)]s>W))%I.
  Proof.
    iIntros (Hnone1 Hnone2) "Hfull Hreg".
    rewrite region_eq rel_eq /region_def /rel_def.
    iDestruct "Hreg" as (M) "(Hγrel & % & Hpreds)".
    rewrite RELS_eq /RELS_def. 
    (* destruct on M !! l *)
    destruct (M !! l) eqn:HRl.
    { (* The location is not in the map *)
      iDestruct (big_sepM_delete _ _ _ _ HRl with "Hpreds") as "[Hl' _]".
      iDestruct "Hl'" as (ρ') "[Hstate Hl']". 
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
      apply not_elem_of_dom in Hnone1. 
      rewrite Hcontr in Hnone1. done.
    }
    (* if not, we need to allocate a new saved pred using φ, 
       and extend R with l := pred *)
    iMod (saved_pred_alloc φ) as (γpred) "#Hφ'".
    iMod (own_update _ _ (● (<[l:=to_agree (γpred,p)]> (to_agree <$> M : relUR)) ⋅ ◯ ({[l:=to_agree (γpred,p)]}))
            with "Hγrel") as "[HR #Hγrel]". 
    { apply auth_update_alloc.
      apply (alloc_singleton_local_update (to_agree <$> M)); last done.
      rewrite lookup_fmap. rewrite HRl. done. 
    }
    (* we also need to extend the World with a new temporary region *)
    iMod (sts_alloc_std_i W (countable.encode l) Revoked
            with "[] Hfull") as "(Hfull & Hstate)"; auto.     
    apply (related_sts_pub_world_fresh W l Revoked) in Hnone1 as Hrelated; auto. 
    iDestruct (region_map_monotone $! Hrelated with "Hpreds") as "Hpreds'".
    iModIntro. rewrite bi.sep_exist_r. iExists _.
    rewrite -fmap_insert. 
    iFrame "HR". iFrame.
    iSplitL;[iSplitR|].
    - iPureIntro. apply dom_equal_insert; auto. 
    - iApply big_sepM_insert; auto.
      iFrame. iExists Revoked. iFrame. 
    - iExists γpred. iFrame "#".
      rewrite REL_eq /REL_def. 
      done.
  Qed.

  (* As a followup of above, the following lemma takes a revoked region and makes it Temporary. *)

  Lemma update_region_revoked_temp_pwl E W l p v φ `{∀ W v, Persistent (φ (W,v))} :
    (std_sta W) !! (countable.encode l) = Some (countable.encode Revoked) →
    p ≠ O → pwl p = true →
    (future_pub_mono φ v -∗
    sts_full_world sts_std W -∗
    region W -∗
    l ↦ₐ[p] v -∗ φ (W,v) -∗ rel l p φ ={E}=∗ region (<s[l := Temporary, (Rpub,Rpriv) ]s>W)
                             ∗ sts_full_world sts_std (<s[l := Temporary, (Rpub,Rpriv)]s>W))%I.
  Proof.
    iIntros (Hrev HO Hpwl) "#Hmono Hsts Hreg Hl #Hφ #Hrel".
    rewrite region_eq /region_def.
    iDestruct "Hreg" as (M) "(Hγrel & Hdom & Hpreds)".
    iDestruct "Hdom" as %Hdom. 
    rewrite RELS_eq /RELS_def. 
    rewrite rel_eq /rel_def REL_eq /REL_def. iDestruct "Hrel" as (γ) "[HREL Hsaved]". 
    iDestruct (reg_in γrel (M) with "[$Hγrel $HREL]") as %HMeq.
    rewrite /region_map_def HMeq big_sepM_insert; [|by rewrite lookup_delete].
    iDestruct "Hpreds" as "[Hl' Hr]".     
    iDestruct "Hl'" as (ρ) "[Hstate Hresources]".
    iDestruct (sts_full_state_std with "Hsts Hstate") as %Hρ.
    iDestruct (sts_full_rel_state_std with "Hsts Hstate") as %Hstd. 
    rewrite Hrev in Hρ. inversion Hρ as [Hρrev]. apply encode_inj in Hρrev. subst. 
    iMod (sts_update_std _ _ _ Temporary with "Hsts Hstate") as "[Hsts Hstate]".
    assert (related_sts_pub_world W (<s[l := Temporary,(Rpub, Rpriv)]s> W)) as Hrelated.
    { apply related_sts_pub_world_revoked_temp; auto. }
    iDestruct (region_map_monotone $! Hrelated with "Hr") as "Hr".
    iDestruct ("Hmono" $! _ _ Hrelated with "Hφ") as "Hφ'".
    assert (is_Some (M !! l)) as [x Hsome].
    { specialize (Hdom (countable.encode l)).
      destruct Hdom as [ [a [Heq [x Hsome] ] ] _];[eauto|].
      apply encode_inj in Heq; subst. eauto. }
    iDestruct (big_sepM_delete _ _ l _ Hsome with "[Hl Hstate $Hr]") as "Hr".
    { iExists Temporary. iFrame.
      iExists γ, v, p, φ. rewrite HMeq lookup_insert in Hsome.
      inversion Hsome. repeat (iSplit; auto). iFrame.
      rewrite Hpwl. iFrame "#". }
    apply insert_id in Hstd.
    rewrite /std_update /= Hstd. iFrame "Hsts".
    iExists M. iFrame. rewrite -HMeq. iFrame.
    iModIntro. iPureIntro. 
    apply insert_id in Hsome. rewrite -Hsome.
    by apply dom_equal_insert. 
  Qed.

   Lemma update_region_revoked_temp_nwl E W l p v φ `{∀ W v, Persistent (φ (W,v))} :
    (std_sta W) !! (countable.encode l) = Some (countable.encode Revoked) →
    p ≠ O →
    (future_priv_mono φ v -∗
    sts_full_world sts_std W -∗
    region W -∗
    l ↦ₐ[p] v -∗ φ (W,v) -∗ rel l p φ ={E}=∗ region (<s[l := Temporary, (Rpub,Rpriv) ]s>W)
                             ∗ sts_full_world sts_std (<s[l := Temporary, (Rpub,Rpriv)]s>W))%I.
  Proof.
    iIntros (Hrev HO) "#Hmono Hsts Hreg Hl #Hφ #Hrel".
    rewrite region_eq /region_def.
    iDestruct "Hreg" as (M) "(Hγrel & Hdom & Hpreds)".
    iDestruct "Hdom" as %Hdom. 
    rewrite RELS_eq /RELS_def. 
    rewrite rel_eq /rel_def REL_eq /REL_def. iDestruct "Hrel" as (γ) "[HREL Hsaved]". 
    iDestruct (reg_in γrel (M) with "[$Hγrel $HREL]") as %HMeq.
    rewrite /region_map_def HMeq big_sepM_insert; [|by rewrite lookup_delete].
    iDestruct "Hpreds" as "[Hl' Hr]".     
    iDestruct "Hl'" as (ρ) "[Hstate Hresources]".
    iDestruct (sts_full_state_std with "Hsts Hstate") as %Hρ.
    iDestruct (sts_full_rel_state_std with "Hsts Hstate") as %Hstd. 
    rewrite Hrev in Hρ. inversion Hρ as [Hρrev]. apply encode_inj in Hρrev. subst. 
    iMod (sts_update_std _ _ _ Temporary with "Hsts Hstate") as "[Hsts Hstate]".
    assert (related_sts_pub_world W (<s[l := Temporary,(Rpub, Rpriv)]s> W)) as Hrelated.
    { apply related_sts_pub_world_revoked_temp; auto. }
    assert (related_sts_priv_world W (<s[l := Temporary,(Rpub, Rpriv)]s> W)) as Hrelated'.
    { apply related_sts_pub_priv_world. auto. }
    iDestruct (region_map_monotone $! Hrelated with "Hr") as "Hr".
    iDestruct ("Hmono" $! _ _ Hrelated' with "Hφ") as "Hφ'".
    assert (is_Some (M !! l)) as [x Hsome].
    { specialize (Hdom (countable.encode l)).
      destruct Hdom as [ [a [Heq [x Hsome] ] ] _];[eauto|].
      apply encode_inj in Heq; subst. eauto. }
    iDestruct (big_sepM_delete _ _ l _ Hsome with "[Hl Hstate $Hr]") as "Hr".
    { iExists Temporary. iFrame.
      iExists γ, v, p, φ. rewrite HMeq lookup_insert in Hsome.
      inversion Hsome. repeat (iSplit; auto). iFrame.
      destruct (pwl p); iFrame "#".
      iIntros (W' W'' Hrelated''). iAlways. iIntros "HφW'".
      iApply ("Hmono" with "[] HφW'").
      iPureIntro. apply related_sts_pub_priv_world; auto. 
    } 
    apply insert_id in Hstd.
    rewrite /std_update /= Hstd. iFrame "Hsts".
    iExists M. iFrame. rewrite -HMeq. iFrame.
    iModIntro. iPureIntro. 
    apply insert_id in Hsome. rewrite -Hsome.
    by apply dom_equal_insert. 
  Qed. 

  (* -------------------------------------------------------------------------- *)
  (* ------------------------- LEMMAS ABOUT REVOKE ---------------------------- *)
  
  Lemma revoke_list_swap Wstd_sta l a b :
    revoke_list_std_sta (a :: b :: l) Wstd_sta = revoke_list_std_sta (b :: a :: l) Wstd_sta.
  Proof.
    destruct (decide (a = b)).
    - subst. done.
    - simpl. destruct (Wstd_sta !! b) eqn:Hb,(Wstd_sta !! a) eqn:Ha; try reflexivity.
      destruct (countable.encode Temporary =? p0)%positive eqn:Hp0,
               (countable.encode Temporary =? p)%positive eqn:Hp; try reflexivity. 
      rewrite insert_commute; auto.
  Qed.

  Lemma revoke_list_swap_middle Wstd_sta l1 l2 a :
    revoke_list_std_sta (l1 ++ a :: l2) Wstd_sta = revoke_list_std_sta (a :: l1 ++ l2) Wstd_sta.
  Proof.
    induction l1.
    - done.
    - assert (a :: (a0 :: l1) ++ l2 = a :: a0 :: l1 ++ l2) as -> ; auto.
      assert ((a0 :: l1) ++ a :: l2 = a0 :: l1 ++ a :: l2) as ->; auto. 
      rewrite revoke_list_swap. simpl. rewrite IHl1. done.
  Qed.

  Lemma revoke_list_permutation Wstd_sta l1 l2 :
    l1 ≡ₚ l2 →
    revoke_list_std_sta l1 Wstd_sta = revoke_list_std_sta l2 Wstd_sta.
  Proof.
    intros Hperm. 
    induction Hperm using Permutation_ind.
    - done.
    - simpl. destruct (Wstd_sta !! x); auto.
      destruct (countable.encode Temporary =? p)%positive; auto.
      f_equiv. done.
    - by rewrite revoke_list_swap.
    - by rewrite IHHperm1 IHHperm2.
  Qed.

  Lemma revoke_list_insert_insert i x y l m :
    <[i:=x]> (revoke_list_std_sta l (<[i:=y]> m)) = <[i:=x]> (revoke_list_std_sta l m).
  Proof.
    induction l. 
    - simpl. rewrite insert_insert. done.
    - simpl. destruct (m !! a) eqn:Hsome.
      + destruct (decide (a = i)).
        * subst. rewrite lookup_insert. 
          destruct (countable.encode Temporary =? y)%positive,(countable.encode Temporary =? p)%positive;
            try rewrite insert_insert; auto.
          rewrite IHl. rewrite insert_insert;auto.
        * rewrite lookup_insert_ne;auto. rewrite Hsome.
          destruct (countable.encode Temporary =? p)%positive;auto.
          do 2 (rewrite (insert_commute _ i a);auto). 
          f_equiv. done.
      + destruct (decide (a = i)).
        * subst. rewrite lookup_insert.
          destruct (countable.encode Temporary =? y)%positive; auto.
          rewrite insert_insert. done.
        * rewrite lookup_insert_ne;auto. rewrite Hsome.
          done. 
  Qed.

  Lemma revoke_list_not_elem_of i x l m :
    i ∉ l →
    <[i:=x]> (revoke_list_std_sta l m) = revoke_list_std_sta l (<[i:=x]> m).
  Proof.
    induction l;intros Hnin.
    - done.
    - apply not_elem_of_cons in Hnin as [Hneq Hnin]. 
      simpl. destruct (m !! a) eqn:Hsome.
      + rewrite lookup_insert_ne;auto. rewrite Hsome.
        destruct (countable.encode Temporary =? p)%positive; auto.
        rewrite insert_commute;auto. f_equiv. auto.
      + rewrite lookup_insert_ne;auto. rewrite Hsome.
        auto.
  Qed.

  Lemma revoke_list_not_elem_of_lookup i l m :
    i ∉ l →
    (revoke_list_std_sta l m) !! i = m !! i.
  Proof.
    induction l; intros Hnin. 
    - done.
    - apply not_elem_of_cons in Hnin as [Hneq Hnin]. 
      simpl. destruct (m !! a) eqn:Hsome.
      + destruct (countable.encode Temporary =? p)%positive; auto.
        rewrite lookup_insert_ne; auto. 
      + auto.
  Qed.

  Lemma revoke_list_dom_std_sta (Wstd_sta : STS_states) :
    revoke_std_sta Wstd_sta = revoke_list_std_sta (map_to_list Wstd_sta).*1 Wstd_sta.
  Proof.
    induction Wstd_sta using map_ind.
    - rewrite /revoke /revoke_std_sta /=. 
        by rewrite fmap_empty map_to_list_empty /revoke_list /std_sta /std_rel /=.
    - rewrite /revoke /revoke_std_sta /=.
      rewrite fmap_insert.
      apply map_to_list_insert with m i x in H3 as Hperm.
      apply (fmap_Permutation fst) in Hperm. 
      rewrite /revoke_list (revoke_list_permutation _ _ ((i, x) :: map_to_list m).*1); auto.
      rewrite /= lookup_insert.
      destruct (countable.encode Temporary =? x)%positive; auto.
      + rewrite /revoke_std_sta in IHWstd_sta. rewrite IHWstd_sta. 
        rewrite revoke_list_insert_insert. repeat f_equiv. 
      + rewrite /revoke_std_sta in IHWstd_sta. rewrite IHWstd_sta. 
        apply revoke_list_not_elem_of.
        intros Hcontr. apply (elem_of_list_fmap_2 fst) in Hcontr.
        destruct Hcontr as [ [y1 y2] [Hy Hyin] ]. subst.
        apply elem_of_map_to_list in Hyin. simpl in *. congruence.
  Qed. 
  
  Lemma revoke_list_dom W :
    revoke W = revoke_list (map_to_list W.1.1).*1 W.
  Proof.
    by rewrite /revoke_list /= -revoke_list_dom_std_sta /revoke /std_sta. 
  Qed.

  Lemma map_to_list_fst {A B : Type} `{EqDecision A, Countable A} (m : gmap A B) i :
    i ∈ (map_to_list m).*1 ↔ (∃ x, (i,x) ∈ (map_to_list m)).
  Proof.
    split.
    - intros Hi.
      destruct (m !! i) eqn:Hsome.
      + exists b. by apply elem_of_map_to_list.
      + rewrite -(list_to_map_to_list m) in Hsome.
        eapply not_elem_of_list_to_map in Hsome. done. 
    - intros [x Hix].
      apply elem_of_list_fmap.
      exists (i,x). auto. 
  Qed.       

  Lemma revoke_list_lookup_Some Wstd_sta l (i : positive) :
    is_Some (Wstd_sta !! i) ↔ is_Some ((revoke_list_std_sta l Wstd_sta) !! i). 
  Proof.
    split.
    - induction l.
      + done.
      + intros [x Hx]. 
      simpl.
      destruct (Wstd_sta !! a);[|apply IHl;eauto].
      destruct (countable.encode Temporary =? p)%positive;[|apply IHl;eauto].
      destruct (decide (a = i)).
        * subst. rewrite lookup_insert. eauto.
        * rewrite lookup_insert_ne;eauto. 
    - induction l.
      + done.
      + intros [x Hx].
        simpl in Hx.
        destruct (Wstd_sta !! a) eqn:Hsome;eauto. 
        destruct (countable.encode Temporary =? p)%positive;[|apply IHl;eauto].
        destruct (decide (a = i)).
        * subst. eauto. 
        * rewrite lookup_insert_ne in Hx;eauto. 
  Qed.
  
  Lemma revoke_lookup_Some W (i : positive) :
    is_Some ((std_sta W) !! i) ↔ is_Some ((std_sta (revoke W)) !! i).
  Proof.
    rewrite revoke_list_dom.
    apply revoke_list_lookup_Some. 
  Qed.

  Lemma revoke_lookup_None W (i : positive) :
    (std_sta W) !! i = None <-> (std_sta (revoke W)) !! i = None.
  Proof.
    split.
    - intros Hnone. apply eq_None_not_Some.
      intros Hcontr. apply revoke_lookup_Some in Hcontr.
      apply eq_None_not_Some in Hcontr; auto.
    - intros Hnone. apply eq_None_not_Some.
      intros Hcontr. apply revoke_lookup_Some in Hcontr.
      apply eq_None_not_Some in Hcontr; auto.
  Qed. 

  Lemma revoke_std_sta_lookup_Some Wstd_sta (i : positive) :
    is_Some (Wstd_sta !! i) ↔ is_Some (revoke_std_sta Wstd_sta !! i).
  Proof.
    split; intros Hi. 
    - assert (std_sta (Wstd_sta, ∅ : STS_rels, (∅,∅)) = Wstd_sta) as Heq;auto.
      rewrite -Heq in Hi. 
      apply (revoke_lookup_Some ((Wstd_sta,∅),∅) i) in Hi. 
      auto.
    - assert (std_sta (Wstd_sta, ∅ : STS_rels, (∅,∅)) = Wstd_sta) as <-;auto.
      apply (revoke_lookup_Some ((Wstd_sta,∅),∅) i). 
      auto.
  Qed. 

  Lemma revoke_list_nin Wstd_sta (l : list positive) (i : positive) :
    i ∉ l → (revoke_list_std_sta l Wstd_sta) !! i = Wstd_sta !! i.
  Proof.
    intros Hnin.
    induction l.
    - done.
    - apply not_elem_of_cons in Hnin as [Hneq Hnin].
      simpl. destruct (Wstd_sta !! a); auto.
      destruct  (countable.encode Temporary =? p)%positive;auto. 
      rewrite lookup_insert_ne; auto.
  Qed. 
      
  Lemma revoke_list_lookup_Temp (Wstd_sta : STS_states) (l : list positive) (i : positive) :
    (Wstd_sta !! i = Some (countable.encode Temporary)) →
    (revoke_list_std_sta (i :: l) Wstd_sta) !! i = Some (countable.encode Revoked). 
  Proof.
    intros Hp.
    rewrite /= Hp Positive_as_OT.eqb_refl. 
    apply lookup_insert. 
  Qed.

  Lemma revoke_list_lookup_middle_Temp (Wstd_sta : STS_states) (l : list positive) (i : positive) :
    i ∈ l →
    (Wstd_sta !! i = Some (countable.encode Temporary)) →
    (revoke_list_std_sta l Wstd_sta) !! i = Some (countable.encode Revoked). 
  Proof.
    intros Hin Hp.
    apply elem_of_list_split in Hin as [l1 [l2 ->] ].
    rewrite revoke_list_swap_middle.
    by apply revoke_list_lookup_Temp. 
  Qed.

  Lemma revoke_lookup_Temp Wstd_sta i :
    (Wstd_sta !! i = Some (countable.encode Temporary)) →
    (revoke_std_sta Wstd_sta) !! i = Some (countable.encode Revoked).
  Proof.
    rewrite revoke_list_dom_std_sta. intros Hsome.
    apply revoke_list_lookup_middle_Temp; auto.
    apply map_to_list_fst. exists (countable.encode Temporary).
      by apply elem_of_map_to_list.
  Qed. 

  Lemma revoke_list_lookup_Revoked (Wstd_sta : STS_states) (l : list positive) (i : positive) :
    (Wstd_sta !! i = Some (countable.encode Revoked)) →
    (revoke_list_std_sta (i :: l) Wstd_sta) !! i = Some (countable.encode Revoked). 
  Proof.
    intros Hp.
    induction l.
    - rewrite /= Hp.
      destruct (countable.encode Temporary =? countable.encode Revoked)%positive; [|done]. apply lookup_insert. 
    - rewrite revoke_list_swap /=.
      destruct (Wstd_sta !! a); auto.
      destruct (countable.encode Temporary =? p)%positive; auto. 
      rewrite Hp.
      destruct (decide (a = i)).
      + subst. apply lookup_insert.
      + rewrite lookup_insert_ne;auto.
        rewrite /= Hp in IHl.
        destruct (countable.encode Temporary =? countable.encode Revoked)%positive; auto. 
  Qed.

  Lemma revoke_list_lookup_middle_Revoked (Wstd_sta : STS_states) (l : list positive) (i : positive) :
    i ∈ l →
    (Wstd_sta !! i = Some (countable.encode Revoked)) →
    (revoke_list_std_sta l Wstd_sta) !! i = Some (countable.encode Revoked). 
  Proof.
    intros Hin Hp.
    apply elem_of_list_split in Hin as [l1 [l2 ->] ].
    rewrite revoke_list_swap_middle.
    by apply revoke_list_lookup_Revoked. 
  Qed.

  Lemma revoke_lookup_Revoked Wstd_sta i :
    (Wstd_sta !! i = Some (countable.encode Revoked)) →
    (revoke_std_sta Wstd_sta) !! i = Some (countable.encode Revoked).
  Proof.
    rewrite revoke_list_dom_std_sta. intros Hsome.
    apply revoke_list_lookup_middle_Revoked; auto.
    apply map_to_list_fst. exists (countable.encode Revoked).
      by apply elem_of_map_to_list.
  Qed. 

  Lemma revoke_list_lookup_Perm (Wstd_sta : STS_states) (l : list positive) (i : positive) :
    (Wstd_sta !! i = Some (countable.encode Permanent)) →
    (revoke_list_std_sta (i :: l) Wstd_sta) !! i = Some (countable.encode Permanent). 
  Proof.
    induction l.
    - intros Hp.
      rewrite /= Hp. 
      destruct (countable.encode Temporary =? countable.encode Permanent)%positive eqn:Hcontr; [|done].
      apply Positive_as_OT.eqb_eq,encode_inj in Hcontr; inversion Hcontr. 
    - intros Hp.
      (* apply not_elem_of_cons in Hin as [Hneq Hin].  *)
      rewrite revoke_list_swap.
      rewrite /=.
      destruct (decide (i = a)).
      + subst. rewrite Hp. 
        destruct (countable.encode Temporary =? countable.encode Permanent)%positive eqn:Hcontr.
        * apply Positive_as_DT.eqb_eq,encode_inj in Hcontr. inversion Hcontr.
        * specialize (IHl Hp).
          by rewrite /= Hp Hcontr in IHl. 
      + destruct (Wstd_sta !! a).
        * rewrite Hp. destruct (countable.encode Temporary =? p)%positive.
          ** destruct (countable.encode Temporary =? countable.encode Permanent)%positive eqn:Hcontr; [|].
             apply Positive_as_OT.eqb_eq,encode_inj in Hcontr; inversion Hcontr.
             rewrite lookup_insert_ne;auto.
             specialize (IHl Hp). 
               by rewrite /= Hp Hcontr in IHl. 
          ** destruct (countable.encode Temporary =? countable.encode Permanent)%positive eqn:Hcontr; [|].
             apply Positive_as_OT.eqb_eq,encode_inj in Hcontr; inversion Hcontr.
             specialize (IHl Hp). 
               by rewrite /= Hp Hcontr in IHl. 
        * rewrite Hp. 
          destruct (countable.encode Temporary =? countable.encode Permanent)%positive eqn:Hcontr; [|].
          apply Positive_as_OT.eqb_eq,encode_inj in Hcontr; inversion Hcontr.
          specialize (IHl Hp). 
            by rewrite /= Hp Hcontr in IHl. 
  Qed.

  Lemma revoke_list_lookup_middle_Perm (Wstd_sta : STS_states) (l : list positive) (i : positive) :
    i ∈ l →
    (Wstd_sta !! i = Some (countable.encode Permanent)) →
    (revoke_list_std_sta l Wstd_sta) !! i = Some (countable.encode Permanent). 
  Proof.
    intros Hin Hp.
    apply elem_of_list_split in Hin as [l1 [l2 ->] ].
    rewrite revoke_list_swap_middle.
    by apply revoke_list_lookup_Perm. 
  Qed.

  Lemma revoke_lookup_Perm Wstd_sta i :
    (Wstd_sta !! i = Some (countable.encode Permanent)) →
    (revoke_std_sta Wstd_sta) !! i = Some (countable.encode Permanent).
  Proof.
    rewrite revoke_list_dom_std_sta. intros Hsome.
    apply revoke_list_lookup_middle_Perm; auto.
    apply map_to_list_fst. exists (countable.encode Permanent).
      by apply elem_of_map_to_list.
  Qed. 

  Lemma revoke_list_lookup_None (Wstd_sta : STS_states) (l : list positive) (i : positive) :
    i ∉ l →
    (Wstd_sta !! i = None →
     (revoke_list_std_sta (i :: l) Wstd_sta) !! i = None).
  Proof.
    intros Hin Hnone.
    induction l. 
    - by rewrite /= Hnone. 
    - rewrite revoke_list_swap.
      apply not_elem_of_cons in Hin as [Hneq Hin]. 
      rewrite /= Hnone in IHl.
      rewrite /= Hnone.
      destruct (Wstd_sta !! a); auto.
      destruct (countable.encode Temporary =? p)%positive; auto. 
      rewrite lookup_insert_ne;auto.
  Qed.

  
  Lemma revoke_list_lookup_non_temp (Wstd_sta : STS_states) (l : list positive) (i : positive) (ρ : region_type) :
    i ∈ l →
    (revoke_list_std_sta l Wstd_sta) !! i = Some (countable.encode ρ) → ρ ≠ Temporary.
  Proof.
    intros Hin Hsome Hcontr.
    subst. induction l.
    - inversion Hin.
    - apply elem_of_cons in Hin as [Heq | Hin].
      + subst. simpl in *.
        destruct (Wstd_sta !! a) eqn:Ha.
        * destruct (countable.encode Temporary =? p)%positive eqn:Htemp.
          ** rewrite lookup_insert in Hsome. inversion Hsome as [Hcontr].
             apply encode_inj in Hcontr. done.
          ** destruct (decide (a ∈ l));[apply IHl; auto|]. 
             rewrite revoke_list_nin in Hsome; auto. rewrite Ha in Hsome.
             inversion Hsome as [Hcontr]. subst.
             apply Positive_as_OT.eqb_neq in Htemp. done. 
        * destruct (decide (a ∈ l));[apply IHl; auto|]. 
          rewrite revoke_list_nin in Hsome; auto. congruence.
      + simpl in *.
        destruct (Wstd_sta !! a) eqn:Ha.
        * destruct (countable.encode Temporary =? p)%positive eqn:Htemp.
          ** apply IHl; auto.
             destruct (decide (i = a)); subst.
             { rewrite lookup_insert in Hsome. inversion Hsome as [Hcontr].
               apply encode_inj in Hcontr. done. }
             rewrite lookup_insert_ne in Hsome; auto.
          ** apply IHl; auto. 
        * apply IHl; auto.
  Qed.

  Lemma revoke_std_sta_lookup_non_temp Wstd_sta (i : positive) (ρ : region_type) :
    (revoke_std_sta Wstd_sta) !! i = Some (countable.encode ρ) → ρ ≠ Temporary.
  Proof.
    intros Hin. 
    rewrite revoke_list_dom_std_sta in Hin.
    apply revoke_list_lookup_non_temp with Wstd_sta ((map_to_list Wstd_sta).*1) i; auto.
    rewrite /std_sta /= in Hin.
    assert (is_Some (Wstd_sta !! i)) as [x Hsome].
    { rewrite revoke_list_lookup_Some. eauto. }
    apply map_to_list_fst. exists x. 
    apply elem_of_map_to_list. done. 
  Qed.   

  Lemma revoke_lookup_non_temp W (i : positive) (ρ : region_type) :
    (std_sta (revoke W)) !! i = Some (countable.encode ρ) → ρ ≠ Temporary.
  Proof.
    intros Hin. 
    rewrite revoke_list_dom in Hin.
    apply revoke_list_lookup_non_temp with W.1.1 ((map_to_list W.1.1).*1) i; auto.
    rewrite /std_sta /= in Hin.
    assert (is_Some (W.1.1 !! i)) as [x Hsome].
    { rewrite revoke_list_lookup_Some. eauto. }
    apply map_to_list_fst. exists x. 
    apply elem_of_map_to_list. done. 
  Qed.    

  Lemma revoke_monotone_dom Wstd_sta Wstd_sta' :
    dom (gset positive) Wstd_sta ⊆ dom (gset positive) Wstd_sta' →
    dom (gset positive) (revoke_std_sta Wstd_sta) ⊆ dom (gset positive) (revoke_std_sta Wstd_sta').
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

  Lemma revoke_monotone_lookup Wstd_sta Wstd_sta' i :
    Wstd_sta !! i = Wstd_sta' !! i →
    revoke_std_sta Wstd_sta !! i = revoke_std_sta Wstd_sta' !! i.
  Proof.
    intros Heq.
    induction Wstd_sta using map_ind.
    - rewrite lookup_empty in Heq.
      rewrite /revoke_std_sta fmap_empty lookup_empty lookup_fmap.
      destruct (Wstd_sta' !! i) eqn:Hnone; inversion Heq.
      rewrite Hnone. done.
    - destruct (decide (i0 = i)).
      + subst. rewrite lookup_insert in Heq.
        rewrite /revoke_std_sta fmap_insert lookup_fmap lookup_insert -Heq /=.
        done.
      + rewrite lookup_insert_ne in Heq;auto.
        specialize (IHWstd_sta Heq). 
        rewrite /revoke_std_sta fmap_insert lookup_insert_ne;auto.
  Qed.

  (* --------------------------------------------------------------------------------- *)
  (* ----------- A REVOKED REGION IS MONOTONE WRT PRIVATE FUTURΕ WORLDS -------------- *)

  Lemma std_rel_priv_monotone x y x' y' Wstd_sta Wstd_sta' i :
    Wstd_sta !! i = Some x -> Wstd_sta' !! i = Some y ->
    (revoke_std_sta Wstd_sta) !! i = Some x' → (revoke_std_sta Wstd_sta') !! i = Some y' →
    rtc (convert_rel std_rel_priv) x y → rtc (convert_rel (std_rel_priv)) x' y'.
  Proof.
    intros Hx Hy Hx' Hy' Hrtc.
    induction Hrtc as [Hrefl | j k h Hjk].
    - simplify_eq. rewrite -Hx in Hy.
      apply revoke_monotone_lookup in Hy.
      rewrite Hx' Hy' in Hy. inversion Hy. left.
    - inversion Hjk as [ρ Hρ].
      destruct Hρ as [ρ' [Hjρ [Hkρ' Hρρ'] ] ].
      subst. destruct ρ,ρ'; inversion Hρρ'; try discriminate; auto.
      + apply std_rel_priv_rtc_Permanent in Hrtc; auto; subst.
        apply revoke_lookup_Temp in Hx as Hxtemp.
        apply revoke_lookup_Perm in Hy as Hyperm.
        rewrite Hxtemp in Hx'. rewrite Hyperm in Hy'.
        inversion Hx'; inversion Hy'; simplify_eq. 
        right with (countable.encode Permanent); [|left]. 
        exists Revoked, Permanent. repeat (split;auto). by right.
      + apply std_rel_priv_rtc_Permanent in Hrtc; auto; subst.
        apply revoke_lookup_Temp in Hx as Hxtemp.
        apply revoke_lookup_Perm in Hy as Hyperm.
        rewrite Hxtemp in Hx'. rewrite Hyperm in Hy'.
        inversion Hx'; inversion Hy'; simplify_eq. 
        right with (countable.encode Permanent); [|left]. 
        exists Revoked, Permanent. repeat (split;auto). by right.
      + assert (∃ (ρ : region_type), h = countable.encode ρ) as [ρ Hρ]. 
        { apply std_rel_exist with (countable.encode Revoked); eauto.
          apply rtc_or_intro_l. auto. }
        apply revoke_lookup_Temp in Hx as Hxtemp.
        rewrite Hxtemp in Hx'. inversion Hx'; simplify_eq.
        destruct ρ.
        * apply revoke_lookup_Temp in Hy as Hytemp.
          rewrite Hytemp in Hy'. inversion Hy'; simplify_eq.
          left.
        * apply revoke_lookup_Perm in Hy as Hytemp.
          rewrite Hytemp in Hy'. inversion Hy'; simplify_eq.
          right with (countable.encode Permanent); [|left]. 
          exists Revoked, Permanent. repeat (split;auto). by right.
        * apply revoke_lookup_Revoked in Hy as Hytemp.
          rewrite Hytemp in Hy'. inversion Hy'; simplify_eq.
          left.         
      + apply std_rel_priv_rtc_Permanent in Hrtc; auto; subst.
        apply revoke_lookup_Revoked in Hx as Hxtemp.
        apply revoke_lookup_Perm in Hy as Hyperm.
        rewrite Hxtemp in Hx'. rewrite Hyperm in Hy'.
        inversion Hx'; inversion Hy'; simplify_eq. 
        right with (countable.encode Permanent); [|left]. 
        exists Revoked, Permanent. repeat (split;auto).
  Qed.

  Lemma std_rel_pub_monotone x y x' y' Wstd_sta Wstd_sta' i :
    Wstd_sta !! i = Some x -> Wstd_sta' !! i = Some y ->
    (revoke_std_sta Wstd_sta) !! i = Some x' → (revoke_std_sta Wstd_sta') !! i = Some y' →
    rtc (convert_rel std_rel_pub) x y → rtc (convert_rel (std_rel_pub)) x' y'.
  Proof.
    intros Hx Hy Hx' Hy' Hrtc.
    induction Hrtc as [Hrefl | j k h Hjk].
    - simplify_eq. rewrite -Hx in Hy.
      apply revoke_monotone_lookup in Hy.
      rewrite Hx' Hy' in Hy. inversion Hy. left.
    - inversion Hjk as [ρ Hρ].
      destruct Hρ as [ρ' [Hjρ [Hkρ' Hρρ'] ] ].
      subst. destruct ρ,ρ'; inversion Hρρ'; try discriminate; auto.
      apply std_rel_pub_rtc_Temporary in Hrtc; auto. subst. 
      apply revoke_lookup_Revoked in Hx as Hxtemp.
      apply revoke_lookup_Temp in Hy as Hyperm.
      rewrite Hxtemp in Hx'. rewrite Hyperm in Hy'.
      inversion Hx'; inversion Hy'; simplify_eq. 
      left. 
  Qed.

  Ltac revoke_i W1 W2 i :=
    (match goal with
     | H : W1 !! i = Some (countable.encode _)
           , H' : W2 !! i = Some (countable.encode _) |- _ =>
       let Hxtemp := fresh "Hxtemp" in
       let Hytemp := fresh "Hytemp" in 
      try (apply revoke_lookup_Temp in H as Hxtemp);
      try (apply revoke_lookup_Perm in H as Hxtemp);
      try (apply revoke_lookup_Revoked in H as Hxtemp);
      try (apply revoke_lookup_Temp in H' as Hytemp);
      try (apply revoke_lookup_Perm in H' as Hytemp);
      try (apply revoke_lookup_Revoked in H' as Hytemp);simplify_eq
    end).

  Lemma std_rel_monotone x y x' y' Wstd_sta Wstd_sta' i :
    Wstd_sta !! i = Some x -> Wstd_sta' !! i = Some y ->
    (revoke_std_sta Wstd_sta) !! i = Some x' → (revoke_std_sta Wstd_sta') !! i = Some y' →
    rtc (λ x0 y0 : positive, convert_rel std_rel_pub x0 y0 ∨ convert_rel std_rel_priv x0 y0) x y →
    rtc (λ x0 y0 : positive, convert_rel std_rel_pub x0 y0 ∨ convert_rel std_rel_priv x0 y0) x' y'.
  Proof.
    intros Hx Hy Hx' Hy' Hrtc. 
    induction Hrtc as [Hrefl | j k h Hjk].
    - simplify_eq. rewrite -Hx in Hy.
      apply revoke_monotone_lookup in Hy.
      rewrite Hx' Hy' in Hy. inversion Hy. left.
    - destruct Hjk as [Hjk | Hjk]. 
      + inversion Hjk as [ρ Hρ].
        destruct Hρ as [ρ' [Hjρ [Hkρ' Hρρ'] ] ].
        subst. destruct ρ,ρ'; inversion Hρρ'; try discriminate; auto.
        apply std_rel_exist in Hrtc as [ρ Hρ]; eauto. subst.
        destruct ρ; revoke_i Wstd_sta Wstd_sta' i; try left.
        right with (countable.encode Permanent); [|left]. right. 
        exists Revoked, Permanent. repeat (split;auto). by right.
      + inversion Hjk as [ρ Hρ].
        destruct Hρ as [ρ' [Hjρ [Hkρ' Hρρ'] ] ].
        subst. apply std_rel_exist in Hrtc as [ρ'' Hρ'']; eauto. subst.
        destruct ρ,ρ',ρ''; inversion Hρρ'; try discriminate; auto;
          revoke_i Wstd_sta Wstd_sta' i; try left;
        (right with (countable.encode Permanent); [|left]; right; 
          exists Revoked, Permanent; repeat (split;auto); by right).
  Qed.
  
  Lemma revoke_monotone W W' :
    rel_is_std W ->
    related_sts_priv_world W W' → related_sts_priv_world (revoke W) (revoke W').
  Proof.
    destruct W as [ [Wstd_sta Wstd_rel] [Wloc_sta Wloc_rel] ].
    destruct W' as [ [Wstd_sta' Wstd_rel'] [Wloc_sta' Wloc_rel'] ];
    rewrite /revoke /std_sta /std_rel /=. 
    intros Hstd [(Hdom_sta & Hdom_rel & Htransition) Hrelated_loc]. 
    apply revoke_monotone_dom in Hdom_sta.
    split;[split;[auto|split;[auto|] ]|auto].
    intros i r1 r2 r1' r2' Hr Hr'.
    simpl in *.
    assert ((r1,r2) = (convert_rel std_rel_pub, convert_rel std_rel_priv)) as Heq.
    { apply Some_inj. rewrite -Hr. apply Hstd. eauto. }
    simplify_eq. 
    specialize (Htransition i _ _ r1' r2' Hr Hr') as [<- [<- Htransition] ]. 
    split;[auto|split;[auto|] ]. 
    intros x' y' Hx' Hy'.
    assert (is_Some (Wstd_sta !! i)) as [x Hx]; [apply revoke_std_sta_lookup_Some; eauto|]. 
    assert (is_Some (Wstd_sta' !! i)) as [y Hy]; [apply revoke_std_sta_lookup_Some; eauto|].
    apply std_rel_monotone with x y Wstd_sta Wstd_sta' i; auto. 
  Qed.

  (* --------------------------------------------------------------------------------- *)
  (* ----------------- REVOKED W IS A PRIVATE FUTURE WORLD TO W ---------------------- *)
  
  Lemma revoke_list_related_sts_priv_cons W l i :
    (is_Some ((std_rel W) !! i) → rel_is_std_i W i) →
    related_sts_priv_world W (revoke_list l W) → related_sts_priv_world W (revoke_list (i :: l) W).
  Proof.
    intros Hstd Hpriv.
    rewrite /revoke_list /=.
    destruct (std_sta W !! i) eqn:Hsome; auto.
    destruct (countable.encode Temporary =? p)%positive eqn:Htemp; auto.
    destruct W as [ [Wstd_sta Wstd_rel] Wloc]. 
    destruct Hpriv as [(Hdoms & Hdomr & Ha) Hloc]; auto.
    split;simpl;auto.
    rewrite /related_sts_priv.
    apply Positive_as_OT.eqb_eq in Htemp. 
    simpl in *. 
    split;[|split].
    - etrans;[|apply dom_insert_subseteq];auto.
    - auto.
    - intros j r1 r2 r1' r2' Hr Hr'.
      rewrite Hr in Hr'. inversion Hr'. repeat (split;auto).
      intros x y Hx Hy. 
      destruct (decide (i = j)).
      { subst. assert (is_Some (Wstd_rel !! j)) as Hasome; eauto.
        rewrite Hstd in Hr; eauto. inversion Hr. 
        rewrite Hsome in Hx. inversion Hx.
        rewrite lookup_insert in Hy. inversion Hy.
        right with (countable.encode Revoked);[|left].
        right. cbv. exists Temporary, Revoked. 
        split;[auto|split;[auto|] ].
          by left. 
      }
      rewrite lookup_insert_ne in Hy;auto.
      specialize (Ha j r1 r2 r1 r2 Hr Hr) as (_ & _ & Ha). 
      subst. apply Ha; auto.
  Qed. 

  Lemma revoke_list_related_sts_priv W l :
    rel_is_std W →
    related_sts_priv_world W (revoke_list l W).
  Proof.
    induction l.
    - split; apply related_sts_priv_refl.
    - split;[|apply related_sts_priv_refl].
      apply revoke_list_related_sts_priv_cons; auto. 
  Qed.

  Lemma revoke_related_sts_priv W :
    rel_is_std W →
    related_sts_priv_world W (revoke W).
  Proof.
    intros Hstd.
    rewrite revoke_list_dom. apply revoke_list_related_sts_priv.
    done. 
  Qed.
    
  (* If a full private future world of W is standard, then W is standard *)
  Lemma sts_full_world_std W W' :
    (⌜related_sts_priv_world W W'⌝
      -∗ sts_full_world sts_std W'
    → ⌜rel_is_std W⌝)%I. 
  Proof.
    iIntros (Hrelated) "Hfull".
    iDestruct "Hfull" as "[[% [% _] ] _]".
    iPureIntro.
    intros i Hx.
    destruct Hrelated as [ (Hdom_std & Hdom_rel & Htransition) _].
    assert ((∀ x : positive, x ∈ (dom (gset positive) W.1.2) → x ∈ (dom (gset positive) W'.1.2))) as H_std_elem_rel;
      [by apply elem_of_subseteq|].
    assert (i ∈ dom (gset positive) W.1.2) as H_i_rel; [by apply elem_of_dom|].
    specialize (H_std_elem_rel i H_i_rel).
    apply elem_of_dom in H_std_elem_rel as [ [r1' r2'] Hr'].
    apply elem_of_dom in H_i_rel as [ [r1 r2] Hr].
    specialize (Htransition i r1 r2 r1' r2' Hr Hr') as (Heq1 & Heq2 & _).
    assert (is_Some (W'.1.2 !! i)) as Hsome'; eauto.    
    rewrite H4 in Hr'; auto.
    by inversion Hr'; subst. 
  Qed.

  (* Helper lemmas for reasoning about a revoked domain *)

  Lemma dom_equal_empty_inv_r Wstd_sta :
    dom_equal Wstd_sta ∅ → Wstd_sta = ∅.
  Proof.
    intros Hdom. 
    apply map_empty.
    intros i.
    destruct Hdom with i as [Hdom1 Hdom2]. 
    apply eq_None_not_Some.
    intros Hsome. specialize (Hdom1 Hsome) as [a [_ [x Hcontr] ] ].
    inversion Hcontr.
  Qed.

  Lemma dom_equal_empty_inv_l M :
    dom_equal ∅ M → M = ∅.
  Proof.
    intros Hdom. 
    apply map_empty.
    intros i.
    destruct Hdom with (countable.encode i) as [Hdom1 Hdom2]. 
    apply eq_None_not_Some.
    intros Hsome.
    assert (∃ a : Addr, countable.encode a = countable.encode i ∧ is_Some (M !! a)) as Ha; eauto.
    specialize (Hdom2 Ha) as [x Hcontr].
    inversion Hcontr.
  Qed.

  Lemma dom_equal_revoke_list W M l : 
    dom_equal (std_sta W) M →
    dom_equal (std_sta (revoke_list l W)) M.
  Proof.
    intros Hdom.
    induction l.
    - done.
    - rewrite /revoke_list /=.
      destruct (std_sta W !! a) eqn:Hsome; auto.
      destruct Hdom with a as [Hdom1 Hdom2].
      destruct (countable.encode Temporary =? p)%positive eqn:Htemp;auto.
      rewrite /std_sta /=. 
      split.
      + intros [x Hi].
        destruct (decide (a = i));subst; eauto.
        rewrite lookup_insert_ne in Hi;auto. 
        destruct IHl with i as [Hdomi1 Hdomi2].
        apply Hdomi1. eauto.
      + intros [a' [Heq [x Hx] ] ]; simplify_eq.
        destruct (decide (a = (countable.encode a')));subst; eauto.
        * rewrite lookup_insert;eauto.
        * rewrite lookup_insert_ne;auto.
          apply IHl. eauto.
  Qed.

  Lemma dom_equal_revoke_list' W M l : 
    dom_equal (std_sta (revoke_list l W)) M →
    dom_equal (std_sta W) M.
  Proof.
    intros Hdom.
    induction l.
    - done.
    - rewrite /revoke_list /= in Hdom.
      destruct (std_sta W !! a) eqn:Hsome; auto.
      destruct Hdom with a as [Hdom1 Hdom2].
      destruct (countable.encode Temporary =? p)%positive eqn:Htemp;auto.
      rewrite /std_sta /=. 
      split.
      + intros [x Hi].
        destruct (decide (a = i));subst.
        * apply Hdom1. rewrite /revoke_list /std_sta /= lookup_insert.
          eauto. 
        * rewrite /revoke_list /std_sta /= in Hdom. 
          destruct Hdom with i as [Hdomi1 _].
          apply Hdomi1. rewrite lookup_insert_ne; auto.
          apply revoke_list_lookup_Some. eauto. 
      + intros [a' [Heq [x Hx] ] ]; simplify_eq.
        rewrite /revoke_list /std_sta /= in Hdom.
        destruct Hdom with (countable.encode a') as [Hdom1i Hdom2i]. 
        destruct (decide (a = (countable.encode a')));subst; eauto.
        rewrite lookup_insert_ne in Hdom2i; auto.
        rewrite revoke_list_lookup_Some. apply Hdom2i.
        exists a'. split; eauto.
  Qed.

  Lemma dom_equal_revoke W M :
    dom_equal (std_sta W) M <->
    dom_equal (std_sta (revoke W)) M.
  Proof.
    rewrite revoke_list_dom. split; [apply dom_equal_revoke_list|apply dom_equal_revoke_list'].
  Qed. 

  Lemma related_sts_priv_weaken fs fr gs gr i x :
    i ∉ dom (gset positive) fs →
    related_sts_priv fs (<[i:=x]> gs) fr gr →
    related_sts_priv fs gs fr gr.
  Proof.
    intros Hnin [Hdom_std [Hdom_loc Hrelated] ].
    split;[|split;auto].
    - rewrite dom_insert_L in Hdom_std.
      apply elem_of_subseteq.
      apply elem_of_subseteq in Hdom_std.
      intros x' Hx'. specialize (Hdom_std x' Hx').
      destruct (decide (x' = i)); [subst;contradiction|].
      apply elem_of_union in Hdom_std as [Hcontr | Hgs]; auto.
      apply elem_of_singleton_1 in Hcontr. contradiction. 
    - intros i' r1 r2 r1' r2' Hr Hr'.
      edestruct Hrelated as (Heq & Heq' & Hstate); eauto; subst.
      repeat (split;auto).
      intros x' y Hx' Hy.
      destruct (decide (i = i')); subst.
      + exfalso. apply Hnin. apply elem_of_gmap_dom. 
        eauto.
      + apply Hstate; auto.
        rewrite lookup_insert_ne;auto. 
  Qed.

  (* Helper lemma for reasoning about the current state of a region map *)
  Lemma big_sepM_exists {A B C : Type} `{EqDecision A, Countable A} (m : gmap A B) (φ : A → C -> B → iProp Σ) :
    (([∗ map] a↦b ∈ m, ∃ c, φ a c b) ∗-∗ (∃ (m' : gmap A C), [∗ map] a↦c;b ∈ m';m, φ a c b))%I.
  Proof.
    iSplit. 
    - iIntros "Hmap".
      iInduction (m) as [| a x m Hnone] "IH" using map_ind.
      + iExists empty. done.
      + iDestruct (big_sepM_insert with "Hmap") as "[Hc Hmap]"; auto.
        iDestruct "Hc" as (c) "Hc".
        iDestruct ("IH" with "Hmap") as (m') "Hmap".
        iExists (<[a:=c]> m').
        iApply (big_sepM2_insert_2 with "Hc").
        iFrame.
    - iIntros "Hmap".
      iDestruct "Hmap" as (m') "Hmap". 
      iInduction (m) as [| a x m Hnone] "IH" using map_ind forall (m').
      + done.
      + iDestruct (big_sepM2_dom with "Hmap") as %Hdom. 
        assert (is_Some (m' !! a)) as [ρ Hρ].
        { apply elem_of_gmap_dom. rewrite Hdom dom_insert_L.
          apply elem_of_union_l, elem_of_singleton; auto. }    
        rewrite -(insert_id m' a ρ); auto.
        rewrite -insert_delete. 
        iDestruct (big_sepM2_insert with "Hmap") as "[Hφ Hmap]";[apply lookup_delete|auto|].
        iApply big_sepM_insert;auto.
        iDestruct ("IH" with "Hmap") as "Hmap". iFrame.
        iExists ρ. iFrame. 
  Qed.

  (* ---------------------------------------------------------------------------------------- *)
  (* ------------------- IF THΕ FULL STS IS REVOKED, WΕ CAN REVOKE REGION ------------------- *)

  Lemma monotone_revoke_region_def M W :
    ⌜dom_equal (std_sta W) M⌝ -∗ ⌜rel_is_std W⌝ -∗
     sts_full_world sts_std (revoke W) -∗ region_map_def M W -∗
     sts_full_world sts_std (revoke W) ∗ region_map_def M (revoke W).
  Proof.
    destruct W as [ [Wstd_sta Wstd_rel] Wloc].
    iIntros (Hdom Hstd) "Hfull Hr".
    iDestruct (big_sepM_exists with "Hr") as (m') "Hr".
    iDestruct (big_sepM2_sep with "Hr") as "[Hstates Hr]".
    iAssert (∀ a ρ, ⌜m' !! a = Some ρ⌝ → ⌜ρ ≠ Temporary⌝)%I as %Htemp.
    { iIntros (a ρ Hsome).
      iDestruct (big_sepM2_lookup_1 _ _ _ a with "Hstates") as (γp) "[_ Hstate]"; eauto.
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hρ.
      iPureIntro.
      eapply revoke_lookup_non_temp; eauto. 
    }
    iFrame.
    iApply big_sepM_exists. iExists m'.
    iApply big_sepM2_sep. iFrame.
    iApply (big_sepM2_mono with "Hr"). 
    iIntros (a ρ γp Hm' HM) "/= Ha". 
    specialize (Htemp a ρ Hm').
    destruct ρ;[contradiction| |done]. 
    iDestruct "Ha" as (γpred v p φ) "(Hγp & Hne & Ha & #Hmono & Hpred & Hφ)".
    iExists _,_,_,_. iFrame "∗ #".
    iNext. iApply ("Hmono" with "[] Hφ"). 
    iPureIntro. apply revoke_related_sts_priv. auto.
    Unshelve. apply _. 
  Qed.

  (* ---------------------------------------------------------------------------------------- *)
  (* ------------------- A REVOKED W IS MONOTONE WRT PRIVATE FUTURE WORLD ------------------- *)
  
  Lemma monotone_revoke_list_region_def_mono M W W' :
    ⌜related_sts_priv_world W W'⌝ -∗ ⌜dom_equal (std_sta W') M⌝ -∗
     sts_full_world sts_std (revoke W) -∗ region_map_def M (revoke W) -∗
     sts_full_world sts_std (revoke W) ∗ region_map_def M (revoke W').
  Proof.
    iIntros (Hrelated Hdom) "Hfull Hr".
    iDestruct (big_sepM_exists with "Hr") as (m') "Hr".
    iDestruct (big_sepM2_sep with "Hr") as "[Hstates Hr]".
    iAssert (∀ a ρ, ⌜m' !! a = Some ρ⌝ → ⌜ρ ≠ Temporary⌝)%I as %Htemp.
    { iIntros (a ρ Hsome).
      iDestruct (big_sepM2_lookup_1 _ _ _ a with "Hstates") as (γp) "[_ Hstate]"; eauto.
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hρ.
      iPureIntro. eapply revoke_lookup_non_temp; eauto. 
    }
    iDestruct (sts_full_world_std (revoke W) with "[] [$Hfull]") as %Hstd.
    { iPureIntro. split;apply related_sts_priv_refl. }
    iFrame. 
    iApply big_sepM_exists. iExists m'.
    iApply big_sepM2_sep. iFrame. 
    iApply (big_sepM2_mono with "Hr").
    iIntros (a ρ γp Hsomeρ Hsomeγp) "Ha /=".
    specialize (Htemp a ρ Hsomeρ). 
    destruct ρ;[contradiction| |done].
    iDestruct "Ha" as (γpred v p φ) "(Heq & HpO & Ha & #Hmono & Hpred & Hφ)". 
    iExists _,_,_,_; iFrame "∗ #".
    iNext. iApply "Hmono";[|iFrame].
    iPureIntro. apply revoke_monotone; auto.
    Unshelve. apply _. 
  Qed.

  (* ---------------------------------------------------------------------------------------- *)
  (* ---------------- IF WΕ HAVE THE REGION, THEN WE CAN REVOKE THE FULL STS ---------------- *)

  (* This matches the temprary resources in the map *)
  Definition temp_resources (W : WORLD) φ (a : Addr) (p : Perm) : iProp Σ :=
    (∃ (v : Word),
           ⌜p ≠ O⌝
          ∗ a ↦ₐ[p] v
          ∗ (if pwl p
             then future_pub_mono φ v
             else future_priv_mono φ v)
          ∗ φ (W,v))%I. 
  
  Lemma monotone_revoke_list_sts_full_world_keep W (l : list positive) (l' : list Addr) p φ :
    (⌜NoDup l'⌝ → ⌜NoDup l⌝ → ⌜countable.encode <$> l' ⊆+ l⌝ →
    ([∗ list] a ∈ l', ⌜(std_sta W) !! (countable.encode a) = Some (countable.encode Temporary)⌝ ∧ rel a p φ)
    ∗ sts_full_world sts_std W ∗ region W
    ==∗ (sts_full_world sts_std (revoke_list l W) ∗ region W
                        ∗ [∗ list] a ∈ l', ▷ temp_resources W φ a p ∗ rel a p φ))%I.
  Proof.
    destruct W as [ [Wstd_sta Wstd_rel] Wloc]. 
    rewrite /std_sta region_eq /region_def /=.
    iInduction (l) as [|x l] "IH" forall (l'); 
    iIntros (Hdup' Hdup Hsub) "(#Hrel & Hfull & Hr)".
    - iFrame. apply submseteq_nil_r,fmap_nil_inv in Hsub as ->. repeat rewrite big_sepL_nil. done. 
    - destruct (decide (x ∈ (countable.encode <$> l'))). 
      + apply elem_of_list_split in e as [l1 [l2 Heq] ].
        rewrite Heq in Hsub.
        iRevert (Hsub Hdup Hdup'). rewrite -(NoDup_fmap countable.encode l') Heq -Permutation_middle. iIntros (Hsub Hdup Hdup').
        apply NoDup_cons in Hdup as [Hnin Hdup]. 
        apply NoDup_cons in Hdup' as [Hnin' Hdup'].
        assert (∃ a : Addr, x = countable.encode a ∧ a ∈ l') as [a [Hxa Ha] ].
        { apply elem_of_list_fmap_2. rewrite Heq. apply elem_of_app. right. apply elem_of_list_here. }
        apply elem_of_Permutation in Ha as [l'' Hleq]. rewrite Hleq /=. 
        iDestruct "Hrel" as "[ [Htemp Hx] Hrel]".
        iDestruct "Htemp" as %Htemp. 
        iMod ("IH" with "[] [] [] [$Hrel $Hfull $Hr]") as "(Hfull & Hr & Hl)"; auto.
        { iPureIntro. apply submseteq_cons_l in Hsub as [k' [Hperm Hsub] ].
          apply Permutation.Permutation_cons_inv in Hperm.
          apply NoDup_cons_12 with a. rewrite -Hleq. apply NoDup_fmap_1 with countable.encode.
          rewrite Heq -Permutation_middle. apply NoDup_cons; auto. }
        { iPureIntro. apply fmap_Permutation with countable.encode in Hleq.
          revert Hleq. rewrite Heq -Permutation_middle fmap_cons Hxa. intros Hleq.
          apply Permutation.Permutation_cons_inv in Hleq. rewrite -Hleq.
          apply submseteq_cons_l in Hsub as [k' [Hperm Hsub] ].
          apply Permutation.Permutation_cons_inv in Hperm.
          rewrite Hperm. done. }
        rewrite /revoke_list /= /std_sta /=.
        rewrite Hxa Htemp Positive_as_OT.eqb_refl.
        rewrite rel_eq /rel_def REL_eq RELS_eq /REL_def /RELS_def /region_map_def. 
        iDestruct "Hx" as (γpred) "#(Hγpred & Hφ)".
        iDestruct "Hr" as (M) "(HM & % & Hpreds)". 
        (* assert that γrel = γrel' *)
        iDestruct (reg_in γrel (M) with "[$HM $Hγpred]") as %HMeq.
        rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete].
        iDestruct "Hpreds" as "[Ha Hpreds]".
        iDestruct "Ha" as (ρ) "[Hstate Ha]". 
        iDestruct (sts_full_state_std with "Hfull Hstate") as %Hlookup.
        simpl in Hlookup. 
        simpl in Hlookup. subst. rewrite revoke_list_not_elem_of_lookup in Hlookup; auto.
        rewrite Htemp in Hlookup. inversion Hlookup; simplify_eq.
        iMod (sts_update_std _ _ _ (Revoked) with "Hfull Hstate") as "[Hfull Hstate]".
        iFrame "∗ #". iClear "IH". 
        iDestruct (big_sepM_insert _ _ a (γpred, p) with "[$Hpreds Hstate]") as "Hpreds"; [apply lookup_delete|..].
        iExists Revoked. iFrame. rewrite -HMeq.
        iModIntro. iSplitL "Hpreds HM".
        ++ iExists M. iFrame. auto. 
        ++ iSplitL.
           +++ iDestruct "Ha" as (γpred0 v p0 φ0 Heq0 Hp0) "(Hx & Hmono & #Hsaved & Hφ0)"; simplify_eq.
               iExists v.
               iDestruct (saved_pred_agree _ _ _ (Wstd_sta, Wstd_rel, Wloc, v) with "Hφ Hsaved") as "#Hφeq". iFrame.
               iSplitR; auto.
               iDestruct (internal_eq_iff with "Hφeq") as "Hφeq'". 
               iSplitL "Hmono";[|by iNext; iApply "Hφeq'"].
               destruct (pwl p0).
               { iDestruct "Hmono" as "#Hmono".
                 iApply later_intuitionistically_2. iAlways.
                 repeat (iApply later_forall_2; iIntros (W W')).
                 iDestruct (saved_pred_agree _ _ _ (W', v) with "Hφ Hsaved") as "#HφWeq'".
                 iDestruct (internal_eq_iff with "HφWeq'") as "HφWeq''".
                 iDestruct (saved_pred_agree _ _ _ (W, v) with "Hφ Hsaved") as "#HφWeq".
                 iDestruct (internal_eq_iff with "HφWeq") as "HφWeq'''". 
                 iAlways. iIntros (Hrelated) "HφW". iApply "HφWeq''". iApply "Hmono"; eauto.
                 iApply "HφWeq'''"; auto. }
               { iDestruct "Hmono" as "#Hmono".
                 iApply later_intuitionistically_2. iAlways.
                 repeat (iApply later_forall_2; iIntros (W W')).
                 iDestruct (saved_pred_agree _ _ _ (W', v) with "Hφ Hsaved") as "#HφWeq'".
                 iDestruct (internal_eq_iff with "HφWeq'") as "HφWeq''".
                 iDestruct (saved_pred_agree _ _ _ (W, v) with "Hφ Hsaved") as "#HφWeq".
                 iDestruct (internal_eq_iff with "HφWeq") as "HφWeq'''". 
                 iAlways. iIntros (Hrelated) "HφW". iApply "HφWeq''". iApply "Hmono"; eauto.
                 iApply "HφWeq'''"; auto. }
           +++ iExists γpred. iFrame "#".
      + apply NoDup_cons in Hdup as [Hnin Hdup].
        apply submseteq_cons_r in Hsub as [Hsub | [l'' [Hcontr _] ] ].
        2: { exfalso. apply n. rewrite Hcontr. apply elem_of_list_here. }
        iMod ("IH" with "[] [] [] [$Hrel $Hfull $Hr]") as "(Hfull & Hr & Hl)"; auto.
        iDestruct "Hr" as (M) "(HM & #Hdom & Hr)". iDestruct "Hdom" as %Hdom. iClear "IH". 
        rewrite /revoke_list /std_sta /=.
        destruct (Wstd_sta !! x) eqn:Hsome.
        2: { iFrame. iModIntro. iExists M. iFrame. auto. }
        destruct (countable.encode Temporary =? p0)%positive eqn:Htemp.
        2: { iFrame. iModIntro. iExists M. iFrame. auto. }
        assert (∃ a:Addr, countable.encode a = x ∧ is_Some (M !! a)) as [a [Heqa [γp Hsomea] ] ].
        { destruct Hdom with (countable.encode x) as [ [a [Heq Ha] ] _]; eauto. }
        iDestruct (big_sepM_delete _ _ a with "Hr") as "[Hx Hr]"; eauto.
        iDestruct "Hx" as (ρ) "[Hstate Hρ]".
        iMod (sts_update_std _ _ _ (Revoked) with "Hfull Hstate") as "[Hfull Hstate]". rewrite Heqa. iFrame. 
        iDestruct (big_sepM_delete _ _ a with "[Hstate $Hr Hρ]") as "Hr"; eauto.
        iExists Revoked; rewrite Heqa; iFrame.
        iModIntro. iFrame. iExists M. iFrame. auto. 
  Qed.
            
  Lemma monotone_revoke_sts_full_world_keep W (l : list Addr) p φ :
    ⌜NoDup l⌝ -∗
    ([∗ list] a ∈ l, ⌜(std_sta W) !! (countable.encode a) = Some (countable.encode Temporary)⌝ ∧ rel a p φ)
    ∗ sts_full_world sts_std W ∗ region W
    ==∗ (sts_full_world sts_std (revoke W) ∗ region W ∗
                        ([∗ list] a ∈ l, ▷ temp_resources W φ a p ∗ rel a p φ)).
  Proof.
    iIntros (Hdup) "(Hl & Hfull & Hr)".
    rewrite revoke_list_dom.
    iAssert (⌜countable.encode <$> l ⊆+ (map_to_list W.1.1).*1⌝)%I as %Hsub.
    { iClear "Hfull Hr". iInduction l as [| x l] "IH".
      - rewrite fmap_nil. iPureIntro. apply submseteq_nil_l.
      - rewrite fmap_cons /=. iDestruct "Hl" as "[ [Hin _] Hl]".
        iDestruct "Hin" as %Hin. apply NoDup_cons in Hdup as [Hnin Hdup].
        iDestruct ("IH" with "[] Hl") as %Hsub; auto. 
        iPureIntro.
        assert (countable.encode x ∈ (map_to_list W.1.1).*1) as Helem.
        { apply map_to_list_fst. exists (countable.encode Temporary). by apply elem_of_map_to_list. }
        apply elem_of_Permutation in Helem as [l' Hl']. rewrite Hl'.
        apply submseteq_skip. revert Hsub. rewrite Hl'; intros Hsub.
        apply submseteq_cons_r in Hsub as [Hsub | [l'' [Heq _] ] ]; auto. 
        assert (countable.encode x ∈ countable.encode <$> l) as Hcontr. 
        { rewrite Heq. apply elem_of_list_here. }
        apply elem_of_list_fmap_2 in Hcontr as [y [Hxy Hy] ]. 
        apply encode_inj in Hxy. subst. contradiction. 
    }
    iMod (monotone_revoke_list_sts_full_world_keep _ (map_to_list W.1.1).*1 l 
            with "[] [] [] [$Hl $Hfull $Hr]") as "(Hfull & Hr & Hi)"; auto. 
    { iPureIntro. apply NoDup_fst_map_to_list. }
    iFrame. done. 
  Qed.

  
  (* The following statement discards all the resources of temporary regions *)
  Lemma monotone_revoke_list_sts_full_world M W l :
    ⌜∀ (i : positive), i ∈ l → ∃ (a : Addr), countable.encode a = i ∧ is_Some (M !! a)⌝ -∗
    ⌜NoDup l⌝ -∗
    sts_full_world sts_std W ∗ region_map_def M W
    ==∗ (sts_full_world sts_std (revoke_list l W) ∗ region_map_def M W).
  Proof.
    destruct W as [ [Wstd_sta Wstd_rel] Wloc]. 
    rewrite /std_sta /=. 
    iIntros (Hin Hdup) "[Hfull Hr]".
    iInduction (l) as [|x l] "IH". 
    - iFrame. done. 
    - apply NoDup_cons in Hdup as [Hnin Hdup]. 
      iMod ("IH" with "[] [] Hfull Hr") as "[Hfull Hr]"; auto.
      { iPureIntro. intros a Ha. apply Hin. apply elem_of_cons. by right. }
      rewrite /revoke_list /= /std_sta /=. 
      destruct (Wstd_sta !! x) eqn:Hsome;[|by iFrame]. 
      destruct (countable.encode Temporary =? p)%positive eqn:Htemp;[|by iFrame]. 
      destruct Hin with x as [a [Heq [γp Hsomea] ] ];[apply elem_of_list_here|].
      iDestruct (big_sepM_delete _ _ a with "Hr") as "[Hρ Hr]"; eauto.
      iDestruct "Hρ" as (ρ') "(Hstate & Ha)".
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hlookup. 
      simpl in Hlookup. subst. rewrite revoke_list_not_elem_of_lookup in Hlookup; auto.
      apply base.positive_beq_true in Htemp. 
      rewrite Hsome -Htemp in Hlookup. inversion Hlookup; simplify_eq.
      iMod (sts_update_std _ _ _ (Revoked) with "Hfull Hstate") as "[Hfull Hstate]".
      iFrame.
      iDestruct (big_sepM_delete _ _ a with "[$Hr Hstate]") as "$"; eauto.
      iExists Revoked. iFrame.
  Qed.

  (* The following statement discards all the resources of temporary regions *)
  Lemma monotone_revoke_sts_full_world W :
    sts_full_world sts_std W ∗ region W
    ==∗ (sts_full_world sts_std (revoke W) ∗ region W).
  Proof.
    iIntros "[Hfull Hr]".
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M) "(HM & #Hdom & Hr)".
    iDestruct "Hdom" as %Hdom. 
    rewrite revoke_list_dom.
    iMod (monotone_revoke_list_sts_full_world _ _ (map_to_list W.1.1).*1
            with "[] [] [$Hfull $Hr]") as "[Hfull Hr]".
    { iPureIntro. intros i Hin. apply map_to_list_fst in Hin as [x Hin].
      destruct Hdom with i as [Hdom1 _].
      apply Hdom1. exists x. by apply elem_of_map_to_list. 
    }
    { iPureIntro. apply NoDup_fst_map_to_list. }
    iFrame.
    iModIntro. iExists M. iFrame. done. 
  Qed.


  Lemma submseteq_dom (l : list positive) (Wstd_sta : STS_states) :
    Forall (λ i : positive, Wstd_sta !! i = Some (countable.encode Temporary)) l
    → NoDup l → l ⊆+ (map_to_list Wstd_sta).*1.
  Proof.
    generalize l. 
    induction Wstd_sta using map_ind.
    + intros l' Htemps Hdup. destruct l'; auto. inversion Htemps. subst. discriminate. 
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
             rewrite -(Htemps j);[rewrite lookup_insert_ne;auto|].
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
  
  Lemma monotone_revoke W :
    sts_full_world sts_std W ∗ region W ==∗ sts_full_world sts_std (revoke W) ∗ region (revoke W).
  Proof.
    iIntros "[HW Hr]".
    iDestruct (sts_full_world_std W W with "[] HW") as %Hstd;[iPureIntro;split;apply related_sts_priv_refl|]. 
    iMod (monotone_revoke_sts_full_world with "[$HW $Hr]") as "[HW Hr]".
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M) "(HM & % & Hpreds)". 
    iDestruct (monotone_revoke_region_def with "[] [] [$HW] [$Hpreds]") as "[Hpreds HW]"; auto.
    iModIntro. iFrame. iExists _. iFrame.
    iPureIntro. by apply (dom_equal_revoke W M).
  Qed.

  Lemma monotone_revoke_keep W l p φ :
    NoDup l ->
    ([∗ list] a ∈ l, ⌜(std_sta W) !! (countable.encode a) = Some (countable.encode Temporary)⌝ ∧ rel a p φ)
      ∗ sts_full_world sts_std W ∗ region W ==∗ sts_full_world sts_std (revoke W) ∗ region (revoke W)
      ∗ [∗ list] a ∈ l, (▷ temp_resources W φ a p ∗ rel a p φ)
                     ∗ ⌜(std_sta (revoke W)) !! (countable.encode a) = Some (countable.encode Revoked)⌝.
  Proof.
    iIntros (Hdup) "(Hl & HW & Hr)".
    iDestruct (sts_full_world_std W W with "[] HW") as %Hstd;[iPureIntro;split;apply related_sts_priv_refl|].
    iAssert (⌜Forall (λ a, std_sta W !! countable.encode a = Some (countable.encode Temporary)) l⌝)%I as %Htemps.
    { iDestruct (big_sepL_and with "Hl") as "[Htemps Hrel]".
      iDestruct (big_sepL_forall with "Htemps") as %Htemps.
      iPureIntro. apply Forall_lookup. done. }
    iMod (monotone_revoke_sts_full_world_keep with "[] [$HW $Hr $Hl]") as "(HW & Hr & Hl)"; eauto.
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M) "(HM & % & Hpreds)".
    iDestruct (monotone_revoke_region_def with "[] [] [$HW] [$Hpreds]") as "[Hpreds HW]"; auto.
    iModIntro. iFrame. iSplitL "HW HM".
    - iExists _. iFrame. iPureIntro. by apply (dom_equal_revoke W M).
    - iApply big_sepL_sep. iFrame. iApply big_sepL_forall. iPureIntro.
      revert Htemps. rewrite (Forall_lookup _ l). intros Hl i a Ha; auto.
      specialize (Hl i a Ha). rewrite /revoke. apply revoke_lookup_Temp. done. 
  Qed.

  
  (* ---------------------------------------------------------------------------------------- *)
  (* ------------------ WE CAN UPDATE A REVOKED WORLD BACK TO TEMPORARY  -------------------- *)
  (* ---------------------------------------------------------------------------------------- *)

  (* closing will take every revoked element of l and reinstate it as temporary *)
  Fixpoint close_list_std_sta (l : list positive) (fs : STS_states) : STS_states :=
    match l with
    | [] => fs
    | i :: l' => match fs !! i with
               | Some j => if ((countable.encode Revoked) =? j)%positive
                          then <[i := countable.encode Temporary]> (close_list_std_sta l' fs)
                          else (close_list_std_sta l' fs)
               | None => (close_list_std_sta l' fs)
               end
    end.
  Definition close_list l W : WORLD := ((close_list_std_sta l (std_sta W),std_rel W), loc W).

  Lemma close_list_std_sta_is_Some Wstd_sta l i :
    is_Some (Wstd_sta !! i) <-> is_Some (close_list_std_sta l Wstd_sta !! i).
  Proof.
    split.
    - induction l.
      + done.
      + intros [x Hx]. 
      simpl.
      destruct (Wstd_sta !! a);[|apply IHl;eauto].
      destruct (countable.encode Revoked =? p)%positive;[|apply IHl;eauto].
      destruct (decide (a = i)).
        * subst. rewrite lookup_insert. eauto.
        * rewrite lookup_insert_ne;eauto. 
    - induction l.
      + done.
      + intros [x Hx].
        simpl in Hx.
        destruct (Wstd_sta !! a) eqn:Hsome;eauto. 
        destruct (countable.encode Revoked =? p)%positive;[|apply IHl;eauto].
        destruct (decide (a = i)).
        * subst. eauto. 
        * rewrite lookup_insert_ne in Hx;eauto. 
  Qed.

  Lemma close_list_std_sta_None Wstd_sta l i :
    Wstd_sta !! i = None <-> close_list_std_sta l Wstd_sta !! i = None.
  Proof.
    split.
    - intros Hnone. apply eq_None_not_Some.
      intros Hcontr. apply close_list_std_sta_is_Some in Hcontr.
      apply eq_None_not_Some in Hcontr; auto.
    - intros Hnone. apply eq_None_not_Some.
      intros Hcontr. revert Hcontr. rewrite close_list_std_sta_is_Some =>Hcontr.
      apply eq_None_not_Some in Hcontr; eauto.
  Qed. 

  Lemma close_list_std_sta_same Wstd_sta l i :
    i ∉ l → Wstd_sta !! i = close_list_std_sta l Wstd_sta !! i.
  Proof.
    intros Hnin. induction l.
    - done.
    - simpl. apply not_elem_of_cons in Hnin as [Hne Hnin]. 
      destruct (Wstd_sta !! a); auto.
      destruct (countable.encode Revoked =? p)%positive; auto.
      rewrite lookup_insert_ne; auto.
  Qed.

  Lemma close_list_std_sta_revoked Wstd_sta l i :
    i ∈ l -> Wstd_sta !! i = Some (countable.encode Revoked) →
    close_list_std_sta l Wstd_sta !! i = Some (countable.encode Temporary).
  Proof.
    intros Hin Hrev. induction l.
    - inversion Hin.
    - apply elem_of_cons in Hin as [Heq | Hin].
      + subst. simpl. rewrite Hrev.
        destruct (countable.encode Revoked =? countable.encode Revoked)%positive eqn:Hcontr. 
        * rewrite lookup_insert; auto.
        * apply Positive_as_DT.eqb_neq in Hcontr. 
          contradiction.
      + simpl. destruct (Wstd_sta !! a); auto.
        destruct (countable.encode Revoked =? p)%positive; auto.
        destruct (decide (i = a)); subst.
        * rewrite lookup_insert; auto.
        * rewrite lookup_insert_ne;auto.
  Qed.
          
  Lemma close_list_related_sts_pub_cons W a l :
    rel_is_std W →
    related_sts_pub_world W (close_list l W) →
    related_sts_pub_world W (close_list_std_sta (a :: l) (std_sta W), std_rel W, loc W).
  Proof.
    rewrite /close_list /=. intros Hstd IHl.
    destruct (std_sta W !! a) eqn:Hsome; auto.
    destruct (countable.encode Revoked =? p)%positive eqn:Hrev;auto.
    apply related_sts_pub_trans_world with (close_list l W); auto.
    split;[|apply related_sts_pub_refl].
    split;[|split].
    + simpl. rewrite dom_insert /close_list /=.
      apply union_subseteq_r.
    + by rewrite /close_list /=.
    + rewrite /close_list /=. intros i r1 r2 r1' r2' Hr Hr'.
      rewrite Hr in Hr'. inversion Hr'.
      repeat (split;auto).
      intros x y Hx Hy.
      destruct (decide (i = a)); subst.
      ++ rewrite lookup_insert in Hy. inversion Hy.
         apply Positive_as_DT.eqb_eq in Hrev. subst.
         destruct (decide (a ∈ l)).
         +++ apply close_list_std_sta_revoked with _ l _ in Hsome;auto.
             rewrite Hsome in Hx. inversion Hx. left.
         +++ rewrite (close_list_std_sta_same _ l) in Hsome;auto.
             rewrite Hsome in Hx. inversion Hx. right with (countable.encode Temporary);[|left].
             assert (is_Some (std_rel W !! a)) as Hstda; eauto.
             specialize (Hstd a Hstda). rewrite Hstd in Hr. inversion Hr.
             exists Revoked,Temporary. repeat (split;auto).
      ++ rewrite lookup_insert_ne in Hy; auto.
         rewrite Hx in Hy. inversion Hy. left.
  Qed. 
         
  Lemma close_list_related_sts_pub W l :
    rel_is_std W → 
    related_sts_pub_world W (close_list l W).
  Proof.
    intros Hstd.
    induction l.
    - rewrite /close_list /=. split; apply related_sts_pub_refl.
    - apply close_list_related_sts_pub_cons; auto. 
  Qed.

  Lemma close_list_related_sts_pub_insert' Wstd_sta Wstd_rel Wloc i l :
    rel_is_std (Wstd_sta,Wstd_rel,Wloc) → 
    i ∉ l → Wstd_sta !! i = Some (countable.encode Revoked) ->
    related_sts_pub_world
      (close_list_std_sta l ((std_sta (Wstd_sta, Wstd_rel, Wloc))), Wstd_rel, Wloc)
      (<[i:=countable.encode Temporary]> (close_list_std_sta l Wstd_sta), Wstd_rel, Wloc).
  Proof.
    intros Hstd Hnin Hlookup.
    split;[|apply related_sts_pub_refl]; simpl.
    split;[|split]; auto.
    + apply elem_of_subseteq. intros j Hj.
      rewrite dom_insert_L. apply elem_of_union. right.
      apply elem_of_dom. apply elem_of_dom in Hj. done. 
    + intros j r1 r2 r1' r2' Hr Hr'.
      assert (is_Some (Wstd_rel !! j)) as Hsome; eauto.
      rewrite Hstd in Hr; auto. rewrite Hstd in Hr'; auto. inversion Hr; inversion Hr'; subst.
      repeat (split;auto). intros x y Hx Hy.
      destruct (decide (i = j)); subst.
      * rewrite lookup_insert in Hy. rewrite -(close_list_std_sta_same _ l) in Hx; auto. 
        rewrite Hlookup in Hx. inversion Hx; inversion Hy; subst.
        right with (countable.encode Temporary);[|left].
        exists Revoked, Temporary. repeat (split;auto).
      * rewrite lookup_insert_ne in Hy; auto. rewrite Hx in Hy. inversion Hy. left.
  Qed.

  Lemma close_list_related_sts_pub_insert Wstd_sta Wstd_rel Wloc i l :
    rel_is_std (Wstd_sta,Wstd_rel,Wloc) → 
    i ∉ l → Wstd_sta !! i = Some (countable.encode Revoked) ->
    related_sts_pub_world
      (Wstd_sta, Wstd_rel, Wloc)
      (<[i:=countable.encode Temporary]> (close_list_std_sta l Wstd_sta), Wstd_rel, Wloc).
  Proof.
    intros Hstd Hnin Hlookup.
    apply related_sts_pub_trans_world with (close_list_std_sta l ((std_sta (Wstd_sta, Wstd_rel, Wloc))),
                                            std_rel (Wstd_sta, Wstd_rel, Wloc), Wloc).
    - apply close_list_related_sts_pub with _ l in Hstd. apply Hstd.
    - apply close_list_related_sts_pub_insert'; auto. 
  Qed.
  
  Lemma monotone_close W l p φ :
    ([∗ list] a ∈ l, temp_resources W φ a p ∗ rel a p φ
                                    ∗ ⌜(std_sta W) !! (countable.encode a) = Some (countable.encode Revoked)⌝)
    ∗ sts_full_world sts_std W ∗ region W ==∗
    sts_full_world sts_std (close_list (countable.encode <$> l) W)
    ∗ region (close_list (countable.encode <$> l) W).
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
    - iFrame. destruct W as [ [Wstd_sta Wstd_rel] Wloc]; done. 
    - apply NoDup_cons in Hdup as [Hdup Hnin]. 
      iDestruct "Hl" as "[ [Hx #[Hrel Hrev] ] Hl]". rewrite fmap_cons /=. 
      rewrite /close_list region_eq /region_def /std_sta /std_rel /=.
      iMod ("IH" $! Hnin with "Hl Hfull Hr") as "(Hfull & Hr)"; auto.
      iClear "IH".
      destruct W as [ [Wstd_sta Wstd_rel] Wloc].
      iDestruct (sts_full_world_std with "[] Hfull") as %Hstd;[iPureIntro;split;apply related_sts_priv_refl|].
      iDestruct "Hx" as (a HO) "(Hx & Hmono & Hφ)".
      iDestruct "Hr" as (M) "(HM & #Hdom & Hr)". iDestruct "Hdom" as %Hdom.
      rewrite rel_eq /rel_def REL_eq RELS_eq. iDestruct "Hrel" as (γpred) "[HREL Hpred]".
      iDestruct (reg_in γrel M with "[$HM $HREL]") as %HMeq. rewrite HMeq. 
      iDestruct (big_sepM_delete _ _ x with "Hr") as "[Hstate Hr]"; [apply lookup_insert|].
      iDestruct "Hstate" as (ρ) "[Hρ Hstate]". 
      iDestruct (sts_full_state_std with "Hfull Hρ") as %Hx''.      
      rewrite -(close_list_std_sta_same _ (countable.encode <$> l) _) in Hx''.
      2: { intros Hcontr. apply elem_of_list_fmap_2 in Hcontr as [y [Hxy Hcontr] ].
           apply encode_inj in Hxy; subst. contradiction. }
      rewrite  Hx''. iFrame. iSimplifyEq. rewrite Positive_as_OT.eqb_refl.
      iMod (sts_update_std _ _ _ Temporary with "Hfull Hρ") as "[Hfull Hρ] /=". iFrame. 
      iModIntro. iExists M. rewrite HMeq.
      iDestruct (big_sepM_delete _ _ x with "[Hρ Hr Hx Hmono Hφ]") as "$"; [apply lookup_insert|..].
      { do 2 (rewrite delete_insert;[|apply lookup_delete]).
        iSplitR "Hr".
        - iExists Temporary. iFrame. rewrite /future_pub_mono. iExists γpred,a,p,φ.
          repeat (iSplit; auto).
          iAssert (future_pub_mono φ a) as "#Hmono'".
          { destruct (pwl p); iDestruct "Hmono" as "#Hmono"; iAlways.
            - iIntros (W' W'' Hrelated) "Hφ". iApply ("Hmono" with "[] Hφ"). auto.
            - iIntros (W' W'' Hrelated) "Hφ". iApply ("Hmono" with "[] Hφ"). iPureIntro. apply related_sts_pub_priv_world. auto.
          }
          iFrame "# ∗".
          iNext. iApply "Hmono'"; iFrame.
          iPureIntro. apply close_list_related_sts_pub_insert; auto.
          intros Hcontr. apply elem_of_list_fmap in Hcontr as [y [Heq Hy] ].
          apply encode_inj in Heq; subst. contradiction. 
        - iApply (big_sepM_mono with "Hr").
          iIntros (a' γp Hsome) "Hρ /=". iDestruct "Hρ" as (ρ) "[Hstate Hρ]".
          iExists ρ. iFrame. destruct ρ; auto.
          + iDestruct "Hρ" as (γpred' v p' φ0) "(Heq & HO & Ha' & Hmono & Hpred & Hφ0)".
            iExists _,_,_,_.
            iAssert (future_pub_mono φ0 v) as "#Hmono'".
            { destruct (pwl p'); iDestruct "Hmono" as "#Hmono"; iAlways.
              - iIntros (W' W'' Hrelated) "Hφ". iApply ("Hmono" with "[] Hφ"). auto.
              - iIntros (W' W'' Hrelated) "Hφ". iApply ("Hmono" with "[] Hφ"). iPureIntro. apply related_sts_pub_priv_world. auto.
            } iFrame. 
            iNext. iApply ("Hmono'" with "[] Hφ0"). iPureIntro.
            apply close_list_related_sts_pub_insert'; auto.
            intros Hcontr. apply elem_of_list_fmap in Hcontr as [y [Heq Hy] ].
            apply encode_inj in Heq; subst. contradiction. 
          + iDestruct "Hρ" as (γpred' v p' φ0) "(Heq & HO & Ha' & #Hmono & Hpred & Hφ0)".
            iExists _,_,_,_. iFrame "∗ #". 
            iNext. iApply ("Hmono" with "[] Hφ0"). iPureIntro.
            apply related_sts_pub_priv_world.
            apply close_list_related_sts_pub_insert'; auto.
            intros Hcontr. apply elem_of_list_fmap in Hcontr as [y [Heq Hy] ].
            apply encode_inj in Heq; subst. contradiction. 
      }
      do 2 (rewrite -HMeq). iFrame. iPureIntro.
      (* The domains remain equal *)
      intros i. destruct Hdom with i as [Hdom1 Hdom2].
      destruct Hdom with (countable.encode x) as [Hdomx1 Hdomx2]. 
      split.
      + intros Hsome. destruct (decide (i = countable.encode x)); subst. 
        ++ apply Hdomx1. 
           apply close_list_std_sta_is_Some. eauto.
        ++ rewrite lookup_insert_ne in Hsome; auto.
      + intros [a0 [Heq Hsome] ]. destruct (decide (i = countable.encode x)); subst. 
        ++ rewrite e. rewrite lookup_insert. eauto. 
        ++ rewrite lookup_insert_ne; auto. destruct Hdom2 as [xa0 Ha0]; eauto.
  Qed. 
    

  Lemma monotone_revoked_close_sub W l p φ :
    ([∗ list] a ∈ l, temp_resources (revoke W) φ a p ∗ rel a p φ
                                    ∗ ⌜(std_sta (revoke W)) !! (countable.encode a) = Some (countable.encode Revoked)⌝)
    ∗ sts_full_world sts_std (revoke W) ∗ region (revoke W) ==∗
    sts_full_world sts_std (close_list (countable.encode <$> l) (revoke W))
    ∗ region (close_list (countable.encode <$> l) (revoke W)).
  Proof.
    iIntros "(Hl & Hfull & Hr)".
    iApply monotone_close. 
    iFrame. 
  Qed. 


End heap. 
