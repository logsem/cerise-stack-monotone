From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules rules_LoadU_derived logrel fundamental region_invariants_revocation region_invariants_static region_invariants_batch_uninitialized.
From cap_machine Require Export iris_extra addr_reg_sample region_macros contiguous stack_macros_helpers macros.

(* TODO:move this to stdpp_extra *)
Lemma elements_dom_list_to_map :
      ∀ K V : Type,
        EqDecision K → ∀ (EqDecision1 : EqDecision K) (H : Countable K) (l : list (K*V)),
          NoDup (l.*1) →
          elements (dom (gset K) (list_to_map l : gmap K V)) ≡ₚl.*1.
Proof.
  intros K V ? ? ? l Hdup. induction l.
  - simpl. auto.
  - destruct a as [k v]. simpl in *.
    apply NoDup_cons in Hdup as [Hin Hdup].
    rewrite dom_insert_L elements_union_singleton.
    constructor. auto.
    apply not_elem_of_dom.
    apply not_elem_of_list_to_map_1. auto.
Qed.

Lemma elements_dom_list_to_map_zip :
      ∀ K V : Type,
        EqDecision K → ∀ (EqDecision1 : EqDecision K) (H : Countable K) (l1 : list K) (l2 : list V),
          length l1 <= length l2 →
          NoDup l1 →
          elements (dom (gset K) (list_to_map (zip l1 l2) : gmap K V)) ≡ₚl1.
Proof.
  intros K V ? ? ? l1. induction l1.
  - simpl. auto.
  - intros l2 Hlen Hdup. destruct l2; [simpl in *; inversion Hlen|]. simpl in *.
    apply NoDup_cons in Hdup as [Hin Hdup].
    rewrite dom_insert_L elements_union_singleton.
    constructor. apply IHl1; auto. lia.
    apply not_elem_of_dom.
    apply not_elem_of_list_to_map_1. rewrite fst_zip;auto. lia.
Qed.

Lemma Permutation_disjoint {A : Type} {eq1 : EqDecision A} {a : A} (l1 l2 l3 : list A) :
  l1 ≡ₚl2 → l1 ## l3 -> l2 ## l3.
Proof.
  intros Hperm Hdisj.
  apply elem_of_disjoint.
  intros x Hx Hx'. revert Hx; rewrite -Hperm =>Hx.
  apply elem_of_disjoint in Hdisj. apply Hdisj in Hx. done.
Qed.

Section stack_object.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          `{MonRef: MonRefG (leibnizO _) CapR_rtc Σ} {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  (* TODO:move this to multiple_updates *)
  Lemma std_update_multiple_disjoint W l1 l2 ρ1 ρ2 :
    l1 ## l2 →
    std_update_multiple (std_update_multiple W l2 ρ2) l1 ρ1 =
    std_update_multiple (std_update_multiple W l1 ρ1) l2 ρ2.
  Proof.
    induction l1; intros Hdisj.
    - simpl. auto.
    - simpl. apply disjoint_cons in Hdisj as Hnin.
      apply disjoint_weak in Hdisj.
      apply IHl1 in Hdisj. rewrite Hdisj.
      rewrite std_update_multiple_insert_commute;auto.
  Qed.

  Lemma region_addrs_disjoint_skip_middle b a2 a3 aend e :
    (a2 + 1)%a = Some a3 → (a3 <= aend)%a →
    region_addrs b a2 ++ region_addrs a3 aend ## [a2] ++ region_addrs aend e.
  Proof.
    intros Hsome Hle.
    simpl. apply elem_of_disjoint.
    intros x Hx Hx'.
    apply elem_of_cons in Hx' as [-> | Hx'].
    - apply elem_of_app in Hx as [Hx%elem_of_region_addrs | Hx%elem_of_region_addrs];solve_addr.
    - apply elem_of_region_addrs in Hx'.
      apply elem_of_app in Hx as [Hx%elem_of_region_addrs | Hx%elem_of_region_addrs];try solve_addr.
  Qed.

  (* The following lemma will be used to make sure that any object passed as a parameter *)
  (* on the stack, will be disjoint from the current stack *)
  Lemma input_stack_disjoint W a0 a1 a2 p l b e a :
    (a0 + 1)%a = Some a1 →
    readAllowed p = true →
    Forall (λ a, W.1 !! a = Some Monotemporary ∨ (∃ w, W.1 !! a = Some (Uninitialized w))) (region_addrs a1 a2) →
    interp W (inr (p,l,b,e,a)) ∗ future_pub_a_mono a0 (λ Wv, interp Wv.1 Wv.2) (inr (p,l,b,e,a)) -∗
    ⌜(region_addrs b e) ## (region_addrs a1 a2)⌝.
  Proof.
    iIntros (Hincr Hra Hforall) "[#Hvalid #Hmono] /=".
    rewrite elem_of_disjoint. iIntros (i Hin1 Hin2).
    iDestruct (readAllowed_implies_region_conditions with "Hvalid") as "Hcond";auto.
    iDestruct (big_sepL_elem_of with "Hcond") as (p' Hflows) "[Hrwcond %]";eauto.
    assert (W.1 !! i = Some Monotemporary ∨ W.1 !! i = Some Permanent) as Hi.
    { destruct (pwl p);auto. destruct l;auto. }
    revert Hforall; rewrite Forall_forall =>Hforall. apply Hforall in Hin2 as Ha.
    destruct Ha as [Ha | [w Ha] ]; destruct Hi as [Hi | Hi];try congruence.
    apply elem_of_region_addrs in Hin1 as Hlelt1. destruct Hlelt1 as [Hle1 Hlt1].
    apply elem_of_region_addrs in Hin2 as Hlelt2. destruct Hlelt2 as [Hle2 Hlt2].
    assert (related_sts_a_world W (<s[i:=Uninitialized (inl 0%Z)]s> W) a0) as Hpub.
    { split;[|apply related_sts_pub_plus_refl]. simpl.
      split;[rewrite dom_insert_L;set_solver|].
      intros i0 x y Hx Hy. destruct (decide (i = i0));simplify_map_eq.
      - rewrite lookup_insert in Hy. inversion Hy. eright;[|left].
        rewrite decide_True;[|solve_addr]. right. constructor.
      - rewrite lookup_insert_ne// Hx in Hy. inversion Hy. left. }
    iSpecialize ("Hmono" $! W _ Hpub with "Hvalid").
    iDestruct (readAllowed_implies_region_conditions with "Hmono") as "Hcond'";auto.
    iDestruct (big_sepL_elem_of with "Hcond'") as (p'' Hflows') "[_ %]";eauto.
    iPureIntro.
    destruct (pwl p).
    - rewrite /region_state_pwl_mono /= lookup_insert in H1. done.
    - rewrite /region_state_nwl /= lookup_insert in H1. destruct l; try done.
      destruct H1;done.
  Qed.


  (* Useful lemma to extract the states of all the unused part of the stack *)
  Lemma state_unused_stack (i : nat) W lstk (bstk estk astk a : Addr) :
      (bstk + i ≤ astk)%Z →
      (bstk + i)%a = Some a →
      interp W (inr (URWLX, lstk, bstk, estk, astk)) -∗
      ⌜Forall (λ a0 : Addr, W.1 !! a0 = Some Monotemporary ∨ (∃ w : Word, W.1 !! a0 = Some (Uninitialized w))) (region_addrs a estk)⌝.
  Proof.
    iIntros (Hbounds Hsome) "Hvalid".
    rewrite Forall_forall. iIntros (x Hx).
    rewrite fixpoint_interp1_eq /=. destruct lstk;try done.
    iDestruct "Hvalid" as "[Hlo Hhi]".
    apply elem_of_region_addrs in Hx as Hconds. destruct Hconds as [Hle Hlt].
    destruct (decide (astk <= estk)%Z).
    - assert (addr_reg.min astk estk = astk) as ->;[solve_addr|].
      assert (addr_reg.max bstk astk = astk) as ->;[solve_addr|].
      destruct (decide (x < astk)%Z).
      + iDestruct (big_sepL_elem_of _ _ x with "Hlo") as (p Hflows) "[Hcond Hpure]".
        { apply elem_of_region_addrs. solve_addr. }
        iDestruct "Hpure" as %Hcond. auto.
      + iDestruct (big_sepL_elem_of _ _ x with "Hhi") as (p Hflows) "[Hcond Hpure]".
        { apply elem_of_region_addrs. solve_addr. }
        iDestruct "Hpure" as %Hcond. auto.
    - assert (addr_reg.min astk estk = estk) as ->;[solve_addr|].
      iDestruct (big_sepL_elem_of _ _ x with "Hlo") as (p Hflows) "[Hcond Hpure]".
      { apply elem_of_region_addrs. solve_addr. }
      iDestruct "Hpure" as %Hcond. auto.
  Qed.

  (* lemma for opening a stack object from region, which may be either a heap object or an uninitialized stack object *)
  Lemma open_stack_object_pre_mid l l' W p :
    NoDup l → l ## l' → (∀ a', a' ∈ l → (W.1 !! a' = Some Permanent ∨ (∃ w, W.1 !! a' = Some (Uninitialized w)))) →
    sts_full_world W ∗ open_region_many l' W ∗ ([∗ list] a' ∈ l, ∃ p' : Perm, ⌜PermFlows p p'⌝ ∗ read_write_cond a' p' interp) -∗
    sts_full_world W ∗ ∃ wps, ([∗ list] a;wp ∈ l;wps, a ↦ₐ[wp.2] wp.1) ∗ ▷ (([∗ list] a;wp ∈ l;wps, a ↦ₐ[wp.2] wp.1) -∗ open_region_many l' W)
                                                                       ∗ ([∗ list] a;wp ∈ l;wps, ⌜W.1 !! a = Some Permanent ∨ W.1 !! a = Some (Uninitialized wp.1)⌝)
                                                                       ∗ ⌜Forall (λ w, PermFlows p w.2) wps⌝.
  Proof.
    iIntros (Hdup Hdisj Hcond) "[Hsts [Hr #Hrels] ]".
    iInduction l as [|x l] "IH" forall (l' Hdisj).
    - iFrame. iExists []. auto.
    - apply NoDup_cons in Hdup as [Hnin Hdup].
      apply disjoint_cons in Hdisj as Hnin'.
      apply disjoint_swap in Hdisj;auto.
      iSimpl in "Hrels". iDestruct "Hrels" as "[Hx Hrels]".
      iDestruct "Hx" as (p' Hflows) "Hrel".
      destruct Hcond with x as [Hperm | [w Huninit] ];[constructor|..].
      + iDestruct (region_open_next_perm with "[$Hrel $Hsts $Hr]") as (v) "(Hsts & Hstate & Hr & Hx & % & #Hmono & #Hvalid)";auto.
        iDestruct ("IH" with "[] [] [] Hrels Hsts Hr") as "[Hsts Hws]";auto.
        { iPureIntro. intros a Ha. apply Hcond. constructor. auto. }
        iFrame. iDestruct "Hws" as (wps) "(Hws & Hcls & Hcond & %)". iExists ((v,p') :: wps).
        iFrame. iSplit;auto. iNext.
        iIntros "[Hx Hxs]". simpl.
        iDestruct ("Hcls" with "Hxs") as "Hr".
        iDestruct (region_close_next_perm with "[$Hstate $Hr $Hx]") as "Hr";auto. apply _.
      + iDestruct (region_open_next_monouninit_w with "[$Hrel $Hsts $Hr]") as "(Hr & Hsts & Hstate & Hx & %)";eauto.
        iDestruct ("IH" with "[] [] [] Hrels Hsts Hr") as "[Hsts Hws]";auto.
        { iPureIntro. intros a Ha. apply Hcond. constructor. auto. }
        iFrame. iDestruct "Hws" as (wps) "(Hws & Hcls & Hcond & %)". iExists ((w,p') :: wps).
        iFrame. iSplit;auto. iNext.
        iIntros "[Hx Hxs]". simpl.
        iDestruct ("Hcls" with "Hxs") as "Hr".
        iDestruct (region_close_next_uninit with "[$Hstate $Hr $Hx]") as "Hr";auto. apply _.
  Qed.

  Lemma open_stack_object_pre l W p :
    NoDup l → (∀ a', a' ∈ l → (W.1 !! a' = Some Permanent ∨ (∃ w, W.1 !! a' = Some (Uninitialized w)))) →
    sts_full_world W ∗ region W ∗ ([∗ list] a' ∈ l, ∃ p' : Perm, ⌜PermFlows p p'⌝ ∗ read_write_cond a' p' interp) -∗
    sts_full_world W ∗ ∃ wps, ([∗ list] a;wp ∈ l;wps, a ↦ₐ[wp.2] wp.1) ∗ ▷ (([∗ list] a;wp ∈ l;wps, a ↦ₐ[wp.2] wp.1) -∗ region W)
                                                                       ∗ ([∗ list] a;wp ∈ l;wps, ⌜W.1 !! a = Some Permanent ∨ W.1 !! a = Some (Uninitialized wp.1)⌝)
                                                                       ∗ ⌜Forall (λ w, PermFlows p w.2) wps⌝.
  Proof.
    iIntros (Hdup Hcond) "[Hsts [Hr #Hrels] ]".
    iDestruct (region_open_nil with "Hr") as "Hr".
    iDestruct (open_stack_object_pre_mid with "[$Hsts $Hr]") as "[Hsts Hws]";eauto. apply disjoint_nil_r. exact (addr_reg.top). (*??*)
    iFrame. iDestruct "Hws" as (ws) "(?&HH&?)". iExists ws. iFrame. iNext. iIntros "H".
    iApply region_open_nil. iApply "HH". iFrame.
  Qed.

  Lemma open_stack_object W p b e :
    (∀ a', (b <= a' < e)%a → (W.1 !! a' = Some Permanent ∨ (∃ w, W.1 !! a' = Some (Uninitialized w)))) →
    sts_full_world W ∗ region W ∗ ([∗ list] a' ∈ (region_addrs b e), ∃ p' : Perm, ⌜PermFlows p p'⌝ ∗ read_write_cond a' p' interp) -∗
    sts_full_world W ∗ ∃ wps, ([∗ list] a;wp ∈ (region_addrs b e);wps, a ↦ₐ[wp.2] wp.1) ∗ ▷ (([∗ list] a;wp ∈ (region_addrs b e);wps, a ↦ₐ[wp.2] wp.1) -∗ region W)
                                 ∗ ⌜Forall (λ awp, W.1 !! awp.1 = Some Permanent ∨ W.1 !! awp.1 = Some (Uninitialized awp.2.1)) (zip (region_addrs b e) wps)⌝
                                 ∗ ⌜Forall (λ w, PermFlows p w.2) wps⌝.
  Proof.
    iIntros (Hcond) "[Hsts [Hr #Hrels] ]".
    iDestruct (open_stack_object_pre with "[$Hsts $Hr $Hrels]") as "[Hsts Hws]".
    apply region_addrs_NoDup.
    intros a' Hin. apply Hcond. apply elem_of_region_addrs. auto.
    iFrame. iDestruct "Hws" as (wps) "(Hws & Hcls & Hcond & %)". iExists _. iFrame. iSplit;auto.
    iDestruct (big_sepL2_alt with "Hcond") as "[% Hcond]".
    iDestruct (big_sepL_forall with "Hcond") as %Hforall. iPureIntro.
    apply Forall_forall. intros x [k Hx]%elem_of_list_lookup. eapply Hforall. eauto.
  Qed.

  (* After checking that the input stack object is all ints, we may need to re initialize it *)
  (* For this purpose we will need to define a merge operation for "conditionally" closing the world *)
  Fixpoint initialize_list l := λ W,
    match l with
    | [] => W
    | a :: l' => match W.1 !! a with
               | Some (Uninitialized _) => <s[a:=Monotemporary]s>(initialize_list l' W)
               | _ => initialize_list l' W
               end
    end.

  Lemma initialize_list_nin W l a :
    a ∉ l → (initialize_list l W).1 !! a = W.1 !! a.
  Proof.
    intros Hnin.
    induction l.
    - simpl;auto.
    - simpl. apply not_elem_of_cons in Hnin as [Hne Hnin].
      rewrite -IHl;auto. destruct (W.1 !! a0);auto.
      destruct r;auto. rewrite lookup_insert_ne//.
  Qed.

  Lemma initialize_list_perm W l a :
    W.1 !! a = Some Permanent → (initialize_list l W).1 !! a = W.1 !! a.
  Proof.
    intros Hnin.
    induction l.
    - simpl;auto.
    - simpl. destruct (decide (a0 = a));subst.
      + rewrite Hnin;auto. rewrite IHl. auto.
      + destruct (W.1 !! a0);auto. destruct r;auto. rewrite lookup_insert_ne//.
  Qed.

  Lemma initialize_list_in W l a w :
    a ∈ l → W.1 !! a = Some (Uninitialized w) → (initialize_list l W).1 !! a = Some Monotemporary.
  Proof.
    intros Hin Huninit.
    induction l;[inversion Hin|].
    simpl. apply elem_of_cons in Hin as [-> | Hin].
    - rewrite Huninit lookup_insert. auto.
    - destruct (W.1 !! a0);auto. destruct r;auto.
      destruct (decide (a = a0));subst;[rewrite lookup_insert|rewrite lookup_insert_ne//];auto.
  Qed.



  Lemma close_stack_object_mid W E m la1 la2 ρ wps l p bsec esec asec lsec :
    (bsec <= asec)%a →
    lsec = region_addrs asec esec →
    length (region_addrs bsec esec) = length wps →
    Forall (λ w : (Z + Cap) * Perm, ∃ z : Z, w.1 = inl z) wps →
    Forall (λ awp : Addr * (Word * Perm),
                    (uninitialize W m).1 !! awp.1 = Some Permanent ∨ (uninitialize W m).1 !! awp.1 = Some (Uninitialized awp.2.1))
           (zip (region_addrs bsec esec) wps) →

    region_addrs bsec esec ## (la1 ++ la2) →

    region_conditions W l p bsec esec -∗
    sts_full_world (std_update_multiple (std_update_multiple (uninitialize W m) la1 ρ) la2 Revoked) -∗
    region (std_update_multiple (std_update_multiple (uninitialize W m) la1 ρ) la2 Revoked) ={E}=∗

    sts_full_world (initialize_list lsec (std_update_multiple (std_update_multiple (uninitialize W m) la1 ρ) la2 Revoked)) ∗
    region (initialize_list lsec (std_update_multiple (std_update_multiple (uninitialize W m) la1 ρ) la2 Revoked)).
  Proof.
    iIntros (Hle Heq Hlen Hints Hwps Hdisj) "#Hcond Hsts Hr".
    iInduction (lsec) as [|a lsec] "IH" forall (asec Heq Hle).
    - iModIntro. iSimpl. iFrame.
    - assert (asec < esec)%a as Hlt.
      { destruct (decide (esec <= asec))%a;[|solve_addr]. apply region_addrs_empty in l0. rewrite l0 in Heq. inversion Heq. }
      rewrite region_addrs_cons // in Heq.
      destruct (asec + 1)%a eqn:Hasec;[|exfalso;solve_addr].
      simpl in Heq. assert (a = asec) as Heqa;[inversion Heq;auto|subst a].
      assert (asec ∈ region_addrs bsec esec) as Hin.
      { apply elem_of_region_addrs. solve_addr. }
      apply elem_of_disjoint in Hdisj as Hlookup.
      apply Hlookup in Hin as Hnin. apply not_elem_of_app in Hnin as [Hnin1 Hnin2].
      rewrite /= std_sta_update_multiple_lookup_same_i// std_sta_update_multiple_lookup_same_i//.
      assert (∃ wp, (asec,wp) ∈ zip (region_addrs bsec esec) wps) as [wp Hinwp].
      { apply elem_of_list_lookup in Hin as [k Hk].
        assert ((zip (region_addrs bsec esec) wps).*1 !! k = Some asec).
        { rewrite fst_zip;[|lia]. auto. }
        apply list_lookup_fmap_inv in H0 as [ [a' wp] [Hsubst Hy] ]. inversion Hsubst;subst.
        exists wp. apply elem_of_list_lookup;eauto. }
      revert Hwps; rewrite Forall_forall =>Hwps. apply Hwps in Hinwp as Hstate. simpl in Hstate.
      destruct Hstate as [Hperm | Huninit].
      + (* If the address is permanent, the world will not change *)
        rewrite Hperm. iMod ("IH" $! a0 with "[] [] Hsts Hr") as "[$ $]". inversion Heq;auto. iPureIntro;solve_addr. auto.
      + (* If the address is uninitialized, we need to reinitialise it using the ints assumption *)
        rewrite Huninit. iMod ("IH" $! a0 with "[] [] Hsts Hr") as "[Hsts Hr]". inversion Heq;auto. iPureIntro;solve_addr.
        (* get the read_write condition for asec *)
        iDestruct (big_sepL_elem_of with "Hcond") as (p' Hflows) "[Hrel Hasec]";[apply Hin|].
        assert (asec ∉ lsec) as Hnin.
        { inversion Heq. intros Hcontr%elem_of_region_addrs. solve_addr. }
        (* open the world to get the resource *)
        iDestruct (region_open_uninitialized with "[$Hr $Hsts $Hrel]") as "(Hr & Hsts & Hstate & Hl & %)".
        { rewrite initialize_list_nin// std_sta_update_multiple_lookup_same_i// std_sta_update_multiple_lookup_same_i//. }
        (* assert that wp.1 is an int *)
        apply elem_of_zip_r in Hinwp.
        revert Hints;rewrite Forall_forall =>Hints. apply Hints in Hinwp as [z Hz].
        destruct wp as [w p0]. simpl in Hz. subst w. simpl.
        (* we can now close the world again and update its state to temp *)
        destruct (pwl p') eqn:Hpwl.
        * iMod (region_close_mono_uninit_w_pwl with "[$Hr $Hsts $Hstate $Hl $Hrel]") as "[$ $]";auto.
          iSplit;auto. iSimpl. iSplit.
          iModIntro. iIntros (W0 W' Hrelated) "_ /=". rewrite fixpoint_interp1_eq. eauto.
          iNext. rewrite fixpoint_interp1_eq;eauto.
        * iMod (region_close_mono_uninit_w_nwl with "[$Hr $Hsts $Hstate $Hl $Hrel]") as "[$ $]";auto.
          iSplit;auto. iSimpl. iSplit.
          iModIntro. iIntros (W0 W' Hrelated) "_ /=". rewrite fixpoint_interp1_eq. eauto.
          iNext. rewrite fixpoint_interp1_eq;eauto.
  Qed.

  Lemma uninitialize_std_sta_lookup_perm :
    ∀ (i : Addr) (m : Mem) (fs : STS_STD), fs !! i = Some Permanent <-> uninitialize_std_sta m fs !! i = Some Permanent.
  Proof.
    intros i m fs. split;intros Hperm.
    - rewrite uninitialize_std_sta_spec Hperm.
      destruct (m !! i);auto.
    - rewrite uninitialize_std_sta_spec in Hperm.
      destruct (fs !! i);auto. destruct (m !! i); auto.
      inversion Hperm. destruct r;inversion H1. auto.
  Qed.

  Lemma close_stack_object W E m la1 la2 ρ wps l p bsec esec asec :
    (if pwl l then p = Monotone else True) →
    readAllowed l →
    length (region_addrs bsec esec) = length wps →
    Forall (λ w : (Z + Cap) * Perm, ∃ z : Z, w.1 = inl z) wps →
    Forall (λ awp : Addr * (Word * Perm),
                    (uninitialize W m).1 !! awp.1 = Some Permanent ∨ (uninitialize W m).1 !! awp.1 = Some (Uninitialized awp.2.1))
           (zip (region_addrs bsec esec) wps) →

    region_addrs bsec esec ## (la1 ++ la2) →

    region_conditions W l p bsec esec -∗
    sts_full_world (std_update_multiple (std_update_multiple (uninitialize W m) la1 ρ) la2 Revoked) -∗
    region (std_update_multiple (std_update_multiple (uninitialize W m) la1 ρ) la2 Revoked) ={E}=∗

    sts_full_world (initialize_list (region_addrs bsec esec) (std_update_multiple (std_update_multiple (uninitialize W m) la1 ρ) la2 Revoked)) ∗
    region (initialize_list (region_addrs bsec esec) (std_update_multiple (std_update_multiple (uninitialize W m) la1 ρ) la2 Revoked)) ∗
    interp (initialize_list (region_addrs bsec esec) (std_update_multiple (std_update_multiple (uninitialize W m) la1 ρ) la2 Revoked)) (inr (l, p, bsec, esec, asec)).
  Proof.
    iIntros (Hmono Hra Hlen Hints Hwps Hdisj) "#Hcond Hsts Hr".
    iMod (close_stack_object_mid with "Hcond Hsts Hr") as "[$ $]";eauto. solve_addr.
    iModIntro. rewrite fixpoint_interp1_eq /=.
    assert (forall k y, region_addrs bsec esec !! k = Some y → ∃ wp, (y,wp) ∈ zip (region_addrs bsec esec) wps) as Hinwp.
    { intros k y Hlook.
      assert ((zip (region_addrs bsec esec) wps).*1 !! k = Some y).
      { rewrite fst_zip;[|lia]. auto. }
      apply list_lookup_fmap_inv in H0 as [ [a' wp] [Hsubst Hy] ]. inversion Hsubst;subst.
      exists wp. apply elem_of_list_lookup;eauto. }
    destruct l;inversion Hra.
    3,6: destruct p;inversion Hmono.
    all: try iApply (big_sepL_mono with "Hcond").
    all: iIntros (k y Hk) "Hres /=".
    all: iDestruct "Hres" as (p' Hflows) "(Hrel & %)".
    all: iExists p';iFrame;iSplit;auto.
    all: revert Hwps;rewrite Forall_forall =>Hwps.
    all: assert (y ∈ region_addrs bsec esec) as Hy;[apply elem_of_list_lookup;eauto|].
    all: apply Hinwp in Hk as [ [w p0] Hiny].
    all: apply Hwps in Hiny; simpl in Hiny.
    all: apply elem_of_disjoint in Hdisj.
    all: apply Hdisj in Hy as Hny;apply not_elem_of_app in Hny as [Hy1 Hy2].
    all: rewrite /region_state_nwl /region_state_pwl_mono.
    1,2,5,6: destruct p;simpl in *.
    all: try (apply uninitialize_std_sta_lookup_perm with (m:=m) in H0).
    all: try (rewrite initialize_list_perm;by rewrite std_sta_update_multiple_lookup_same_i// std_sta_update_multiple_lookup_same_i//).
    5,6: destruct Hiny as [Hiny | Hiny];
      [apply uninitialize_std_sta_lookup_perm in Hiny; congruence
      |rewrite (initialize_list_in _ _ _ w)// std_sta_update_multiple_lookup_same_i// std_sta_update_multiple_lookup_same_i//].
    all: destruct Hiny as [Hiny | Hiny];
      [iRight;rewrite initialize_list_perm// std_sta_update_multiple_lookup_same_i// std_sta_update_multiple_lookup_same_i//
      |iLeft;rewrite (initialize_list_in _ _ _ w)// std_sta_update_multiple_lookup_same_i// std_sta_update_multiple_lookup_same_i//].
  Qed.

  Lemma uninitialize_revoke_condition W m :
    (∀ a' : Addr, is_Some (m !! a') ↔ std W !! a' = Some Monotemporary ∧ (0 <= a')%a) →
    revoke_condition (uninitialize W m).
  Proof.
    intros Hforall. intros a.
    destruct (m !! a) eqn:Hsome.
    - assert (is_Some (m !! a)) as HisSome;[eauto|]. apply Hforall in HisSome as [Hmono _].
      eapply uninitialize_std_sta_lookup_in in Hsome;eauto. rewrite Hsome. auto.
    - apply uninitialize_std_sta_None_lookup with (m:=W.1) in Hsome as Heq. rewrite Heq.
      intros Hcontr. assert (is_Some (m !! a)) as [? HisSome];[|congruence].
      apply Hforall. split;auto. solve_addr.
  Qed.

  Lemma read_allowedU_inv_range W p g b e a b' e' :
    (b <= b' ∧ e' < e)%a → readAllowedU p = true →
    interp W (inr (p,g,b,e,a)) -∗
    [∗ list] a ∈ region_addrs b' e', ∃ p', ⌜PermFlows (promote_perm p) p'⌝ ∗ read_write_cond a p' interp.
  Proof.
    iIntros ([Hle Hlt] HraU) "Hv".
    iApply big_sepL_forall. iIntros (k x Hin).
    assert (x ∈ region_addrs b' e') as [Hle' Hlt']%elem_of_region_addrs.
    { apply elem_of_list_lookup;eauto. }
    iDestruct (read_allowedU_inv _ x with "Hv") as "Hcond";auto. solve_addr.
  Qed.


End stack_object.
