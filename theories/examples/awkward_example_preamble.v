From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
Require Import Eqdep_dec.
From cap_machine Require Import
     rules logrel fundamental region_invariants
     region_invariants_revocation region_invariants_static.
From cap_machine.examples Require Import region_macros stack_macros scall malloc awkward_example_helpers awkward_example.
From stdpp Require Import countable.

Lemma big_sepM_to_big_sepL2 {Σ : gFunctors} {A B : Type} `{EqDecision A} `{Countable A}
      (r : gmap A B) (lr : list A) (φ : A → B → iProp Σ) :
  NoDup lr →
  (∀ r0, r0 ∈ lr → is_Some (r !! r0)) →
  ([∗ map] k↦y ∈ r, φ k y) -∗ ∃ ys, ([∗ list] k;y ∈ lr;ys, φ k y).
Proof.
  iInduction (lr) as [ | r0 ] "IHl" forall (r); iIntros (Hdup Hlookup) "Hmap".
  - iExists []. done.
  - assert (is_Some (r !! r0)) as Hr0.
    { apply Hlookup. constructor. }
    destruct Hr0 as [v0 ?].
    iDestruct (big_sepM_delete _ _ r0 with "Hmap") as "(H & Hmap)"; eauto.
    iSpecialize ("IHl" with "[] [] Hmap").
    { iPureIntro. by eapply NoDup_cons_12. }
    { iPureIntro. intros rr Hrr. rewrite lookup_delete_ne.
      { apply Hlookup. by constructor. }
      intros ->. eapply NoDup_cons_11; eauto. }
    iDestruct "IHl" as (ys) "IHl". iExists (v0 :: ys). cbn. iFrame.
Qed.

Lemma big_sepL2_split_at {Σ : gFunctors} {A B: Type} `{EqDecision A} `{Countable A}
      (k: nat) (l1: list A) (l2: list B) (φ : A → B → iProp Σ):
  ([∗ list] a;b ∈ l1;l2, φ a b) -∗
  ([∗ list] a;b ∈ (take k l1);(take k l2), φ a b) ∗ ([∗ list] a;b ∈ (drop k l1);(drop k l2), φ a b).
Proof.
  iIntros "H".
  iDestruct (big_sepL2_length with "H") as %?.
  rewrite -{1}(take_drop k l1) -{1}(take_drop k l2).
  iDestruct (big_sepL2_app' with "H") as "[? ?]".
  { rewrite !take_length. lia. }
  iFrame.
Qed.

Lemma regmap_full_dom (r: gmap RegName Word):
  (∀ x, is_Some (r !! x)) →
  dom (gset RegName) r = all_registers_s.
Proof.
  intros Hfull. apply (anti_symm _); rewrite elem_of_subseteq.
  - intros rr _. apply all_registers_s_correct.
  - intros rr _. rewrite -elem_of_gmap_dom. apply Hfull.
Qed.

(* TODO: move to lang.v *)
Lemma le_addr_withinBounds p l b e a:
  (b <= a)%a → (a < e)%a →
  withinBounds (p, l, b, e, a) = true .
Proof.
  intros. eapply andb_true_iff. unfold ltb_addr, leb_addr.
  unfold le_addr, lt_addr in *. rewrite Z.leb_le Z.ltb_lt. lia.
Qed.

Section awkward_example_preamble.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          `{MonRef: MonRefG (leibnizO _) CapR_rtc Σ} {nainv: logrel_na_invs Σ}.

  Ltac iPrologue prog :=
    iDestruct prog as "[Hi Hprog]";
    iApply (wp_bind (fill [SeqCtx])).

  Ltac iEpilogue prog :=
    iNext; iIntros prog; iSimpl;
    iApply wp_pure_step_later;auto;iNext.

  Ltac middle_lt prev index :=
    match goal with
    | Ha_first : ?a !! 0 = Some ?a_first |- _
    => apply Z.lt_trans with prev; auto; apply incr_list_lt_succ with a index; auto
    end.

  Ltac iCorrectPC i j :=
    eapply isCorrectPC_contiguous_range with (a0 := i) (an := j); eauto; [];
    cbn; solve [ repeat constructor ].

  Ltac iContiguous_next Ha index :=
    apply contiguous_of_contiguous_between in Ha;
    generalize (contiguous_spec _ Ha index); auto.

  (**************)

  Lemma region_addrs_single b e:
    (b+1)%a = Some e →
    region_addrs b e = [b].
  Proof.
    intros. rewrite /region_addrs.
    rewrite (_: region_size b e = 1) //= /region_size.
    solve_addr.
  Qed.

  Lemma region_mapsto_single b e p l:
    (b+1)%a = Some e →
    [[b,e]] ↦ₐ[p] [[l]] -∗
    ∃ v, b ↦ₐ[p] v ∗ ⌜l = [v]⌝.
  Proof.
    iIntros (Hbe) "H". rewrite /region_mapsto region_addrs_single //.
    iDestruct (big_sepL2_length with "H") as %Hlen.
    cbn in Hlen. destruct l as [|x l']; [by inversion Hlen|].
    destruct l'; [| by inversion Hlen]. iExists x. cbn.
    iDestruct "H" as "(H & _)". eauto.
  Qed.

  (* [f_m] is the offset of the malloc capability *)
  (* [offset_to_awkward] is the offset between the [move_r r_t1 PC] instruction
  and the code of the awkward example *)
  Definition awkward_preamble_instrs (f_m offset_to_awkward: Z) :=
    malloc_instrs f_m 1 ++
    [store_z r_t1 0;
     move_r r_t2 r_t1;
     move_r r_t1 PC;
     lea_z r_t1 offset_to_awkward] ++
    crtcls_instrs f_m ++
    rclear_instrs (list_difference all_registers [PC; r_t0; r_t1]) ++
    [jmp r_t0].

  Definition awkward_preamble f_m offset_to_awkward ai p :=
    ([∗ list] a_i;w_i ∈ ai;(awkward_preamble_instrs f_m offset_to_awkward), a_i ↦ₐ[p] w_i)%I.

  (* Compute the offset from the start of the program to the move_r r_t1 PC
     instruction. Will be used later to compute [offset_to_awkward]. *)
  (* This is somewhat overengineered, but could be easily generalized to compute
     offsets for other programs if needed. *)
  Definition awkward_preamble_move_offset : Z.
  Proof.
    unshelve notypeclasses refine (let x := _ : Z in _). {
      set instrs := awkward_preamble_instrs 0 0.
      assert (sig (λ l1, ∃ l2, instrs = l1 ++ l2)) as [l1 _]; [do 2 eexists | exact (length l1)].

      assert (forall A (l1 l2 l3 l4: list A), l2 = l3 ++ l4 → l1 ++ l2 = (l1 ++ l3) ++ l4) as step_app.
      { intros * ->. by rewrite app_assoc. }
      assert (forall A (l1 l2 l3: list A) x, l1 = l2 ++ l3 → x :: l1 = (x :: l2) ++ l3) as step_cons.
      { intros * ->. reflexivity. }
      assert (forall A (l1 l2: list A) x, x :: l1 = l2 → x :: l1 = l2) as prepare_cons.
      { auto. }
      assert (forall A (l: list A), l = [] ++ l) as stop.
      { reflexivity. }

      unfold instrs, awkward_preamble_instrs.
      (* Program-specific part *)
      eapply step_app.
      repeat (eapply prepare_cons;
              lazymatch goal with
              | |- move_r r_t1 PC :: _ = _ => fail
              | _ => eapply step_cons end).
      eapply stop.
    }
    cbv in x. exact x.
  Defined.

  Definition awkN : namespace := nroot .@ "awkN".
  Definition awk_invN : namespace := awkN .@ "inv".
  Definition awk_codeN : namespace := awkN .@ "code".
  Definition awk_clsN : namespace := awkN .@ "cls".

  Lemma awkward_preamble_spec (f_m offset_to_awkward: Z) (r: Reg) W pc_p pc_g pc_b pc_e
        ai pc_p' a_first a_end b_link e_link a_link a_entry ai_awk awk_first awk_end
        a_move:

    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_end →
    PermFlows pc_p pc_p' →
    contiguous_between ai a_first a_end →
    withinBounds (RW, Global, b_link, e_link, a_entry) = true →
    (a_link + f_m)%a = Some a_entry →
    (a_first + awkward_preamble_move_offset)%a = Some a_move →
    (a_move + offset_to_awkward)%a = Some awk_first →
    contiguous_between ai_awk awk_first awk_end →

    (* Code of the preamble *)
    awkward_preamble f_m offset_to_awkward ai pc_p'

    (* Code of the awkward example itself *)
    ∗ awkward_example ai_awk pc_p r_adv 65

    (*** Resources for malloc ***)
    (* assume that a pointer to the linking table (where the malloc capa is) is at offset 0 of PC *)
    ∗ inv malloc_γ ([[b_m,e_m]] ↦ₐ[p_m] [[malloc_subroutine]])
    ∗ pc_b ↦ₐ[pc_p'] (inr (RW, Global, b_link, e_link, a_link))
    ∗ a_entry ↦ₐ[RW] (inr (E, Global, b_m, e_m, a_m))

    -∗
    interp_expr interp r W (inr (pc_p, pc_g, pc_b, pc_e, a_first)).
  Proof.
    rewrite /interp_expr /=.
    iIntros (Hvpc Hfl Hcont Hwb_malloc Ha_entry Ha_lea H_awk_offset Hcont_awk)
            "(Hprog & Hawk & #Hinv_malloc & Hpc_b & Ha_entry)
             ([#Hr_full #Hr_valid] & Hregs & Hr & Hsts & HnaI)".
    iDestruct "Hr_full" as %Hr_full.
    rewrite /full_map.
    iSplitR; auto. rewrite /interp_conf.

    (* put the code for the awkward example in an invariant *)
    iDestruct (na_inv_alloc logrel_nais _ awk_codeN with "Hawk") as ">#Hawk".

    rewrite /registers_mapsto.
    iDestruct (big_sepM_delete _ _ PC with "Hregs") as "[HPC Hregs]".
      by rewrite lookup_insert //. rewrite delete_insert_delete //.
    destruct (Hr_full r_t0) as [r0 Hr0].
    iDestruct (big_sepM_delete _ _ r_t0 with "Hregs") as "[Hr0 Hregs]". by rewrite !lookup_delete_ne//.
    pose proof (regmap_full_dom _ Hr_full) as Hdom_r.
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.

    (* malloc 1 *)
    iDestruct (contiguous_between_program_split with "Hprog") as
        (ai_malloc ai_rest a_malloc_end) "(Hmalloc & Hprog & #Hcont)"; [apply Hcont|].
    iDestruct "Hcont" as %(Hcont_malloc & Hcont_rest & Heqapp & Hlink).
    iApply (malloc_spec with "[- $HPC $Hmalloc $Hpc_b $Ha_entry $Hr0 $Hregs $Hr $Hsts]");
      [|apply Hfl|eapply Hcont_malloc|eapply Hwb_malloc|eapply Ha_entry|..].
    { admit. }
    { rewrite !dom_delete_L Hdom_r difference_difference_L //. }
    iSplitR. iApply "Hinv_malloc". iNext.
    iIntros "(HPC & Hmalloc & Hpc_b & Ha_entry & HH)".
    iDestruct "HH" as (b_cell e_cell Hbe_cell)
                      "(Hr1 & Hcell & Hr0 & Hregs & #Hcell_fresh & Hr & Hsts)".
    iDestruct "Hcell_fresh" as %Hcell_fresh.
    (* TODO: change the postcondition of malloc to produce (b+size = Some e) instead of a subtraction? *)
    iDestruct (region_mapsto_single with "Hcell") as (cellv) "(Hcell & _)". revert Hbe_cell; clear; solve_addr.
    rewrite region_addrs_single in Hcell_fresh. 2: revert Hbe_cell; clear; solve_addr.
    rewrite ->Forall_singleton in Hcell_fresh.
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_rest.

    destruct ai_rest as [| a l]; [by inversion Hlength|].
    assert (a_malloc_end = a) as ->. admit.
    (* store_z r_t1 0 *)
    destruct l as [| ? l]; [by inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_store_success_z with "[$HPC $Hr1 $Hi $Hcell]");
      [eapply store_z_i|apply Hfl|constructor| |iContiguous_next Hcont_rest 0|..].
    { admit. }
    { split; auto. apply le_addr_withinBounds; revert Hbe_cell; clear; solve_addr. }
    iEpilogue "(HPC & Hprog_done & Hr1 & Hb_cell)". iCombine "Hprog_done" "Hmalloc" as "Hprog_done".
    (* move_r r_t2 r_t1 *)
    iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr2 Hregs]".
      by rewrite lookup_insert. rewrite delete_insert_delete.
    destruct l as [| a_move' l]; [by inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg _ _ _ _ _ _ _ _ r_t2 _ r_t1 with "[$HPC $Hi $Hr1 $Hr2]");
      [eapply move_r_i|apply Hfl| |iContiguous_next Hcont_rest 1|done|..].
    { admit. }
    iEpilogue "(HPC & Hi & Hr2 & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move_r r_t1 PC *)
    destruct l as [| ? l]; [by inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr1]");
      [eapply move_r_i|apply Hfl| |iContiguous_next Hcont_rest 2|done|..].
    { admit. }
    iEpilogue "(HPC & Hi & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea_z r_t1 offset_to_awkward *)
    assert (a_move' = a_move) as ->.
    { admit. }
    destruct l as [| ? l]; [by inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_lea_success_z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ awk_first with "[$HPC $Hi $Hr1]");
      [eapply lea_z_i|apply Hfl| |iContiguous_next Hcont_rest 3|assumption|done|..].
    { admit. }
    { admit. }
    iEpilogue "(HPC & Hi & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* crtcls *)
    iDestruct (contiguous_between_program_split with "Hprog") as
        (ai_crtcls ai_rest a_crtcls_end) "(Hcrtcls & Hprog & #Hcont)".
    { epose proof (contiguous_between_incr_addr _ 4%nat _ _ _ Hcont_rest eq_refl).
      eapply contiguous_between_app with (a1:=[_;_;_;_]). 2: eapply Hcont_rest.
      all: eauto. }
    iDestruct "Hcont" as %(Hcont_crtcls & Hcont_rest' & Heqapp' & Hlink').
    iApply (crtcls_spec with "[- $HPC $Hcrtcls $Hpc_b $Ha_entry $Hr0 $Hregs $Hr1 $Hr2 $Hr $Hsts]");
      [|apply Hfl|apply Hcont_crtcls|apply Hwb_malloc|apply Ha_entry|..].
    { admit. }
    { rewrite dom_delete_L dom_insert_L !dom_delete_L Hdom_r.
      rewrite !difference_difference_L singleton_union_difference_L all_registers_union_l.
      clear. set_solver. }
    { admit. }
    { admit. }
    iSplitR. iApply "Hinv_malloc". iNext.
    iIntros "(HPC & Hcrtcls & Hpc_b & Ha_entry & HH)".
    iDestruct "HH" as (b_cls e_cls Hbe_cls) "(Hr1 & Hbe_cls & Hr0 & Hr2 & Hregs & #Hcls_fresh & Hr & Hsts)".
    iDestruct "Hcls_fresh" as %Hcls_fresh.
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_rest'.
    iDestruct (na_inv_alloc logrel_nais _ awk_clsN with "Hbe_cls") as ">#Hcls_inv".
    (* rclear *)
    iDestruct (contiguous_between_program_split with "Hprog") as
        (ai_rclear ai_rest' a_rclear_end) "(Hrclear & Hprog & #Hcont)"; eauto.
    iDestruct "Hcont" as %(Hcont_rclear & Hcont_rest'' & Heqapp'' & Hlink'').
    iDestruct (big_sepL2_length with "Hrclear") as %Hrclear_len.
    destruct ai_rclear; [by inversion Hrclear_len|].
    pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont_rclear) as ->.
    iDestruct (big_sepM_insert _ _ r_t2 with "[$Hregs $Hr2]") as "Hregs".
      by rewrite !lookup_insert_ne // lookup_delete.
    iApply (rclear_spec with "[- $HPC $Hrclear $Hregs]");
      [apply Hcont_rclear| | | |apply Hfl|..].
    { apply not_elem_of_list; repeat constructor. }
    { reflexivity. }
    { admit. }
    { rewrite list_to_set_difference -/all_registers_s.
      repeat rewrite ?dom_insert_L ?dom_delete_L. rewrite Hdom_r.
      rewrite !singleton_union_difference_L !all_registers_union_l !difference_difference_L.
      f_equal. clear. set_solver. }
    iNext. iIntros "(HPC & Hregs & Hrclear)". iCombine "Hrclear" "Hprog_done" as "Hprog_done".
    iDestruct (big_sepL2_length with "Hprog") as %Hlen'.
    destruct ai_rest'; [by inversion Hlen'|].
    (* in preparation of jumping, we allocate the new awkward invariant and sts *)
    iDestruct (sts_alloc_loc _ false awk_rel_pub awk_rel_priv with "Hsts") as ">HH".
    iDestruct "HH" as (i) "(Hsts & % & % & Hst_i & #Hrel_i)".
    iDestruct (inv_alloc awkN _ (awk_inv i b_cell) with "[Hb_cell Hst_i]") as ">#Hawk_inv".
    { iNext. rewrite /awk_inv. iExists false. iFrame. }
    (* call the resulting world W2 *)
    match goal with |- context [ sts_full_world ?W ] => set W2 := W end.
    (* jmp *)
    iPrologue "Hprog".
    pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont_rest'') as ->.
    assert (ai_rest' = []) as -> by (inversion Hlen'; eauto using nil_length_inv).
    iApply (wp_jmp_success with "[$HPC $Hi $Hr0]");
      [apply jmp_i|apply Hfl|..].
    { admit. }
    (* TODO: We need to allocate all the relevant non atomic invariants *)

    (* the current state of registers is valid *)
    iAssert (interp W2 (inr (E, Global, b_cls, e_cls, b_cls)))%I as "#Hvalid_cls".
    { rewrite /interp fixpoint_interp1_eq /= /enter_cond. iModIntro.
      iIntros (r' W3 HW3) "". iNext. rewrite /interp_expr /=.
      iIntros "([Hr'_full #Hr'_valid] & Hregs' & Hr & Hsts & HnaI)". iDestruct "Hr'_full" as %Hr'_full.
      pose proof (regmap_full_dom _ Hr'_full) as Hdom_r'.
      iSplitR; [auto|]. rewrite /interp_conf.

      iDestruct (na_inv_open with "Hcls_inv HnaI") as ">(>Hcls & Hna & Hcls_close)";
        [auto..|].

      rewrite /registers_mapsto.
      rewrite -insert_delete.
      iDestruct (big_sepM_insert with "Hregs'") as "[HPC Hregs']". by apply lookup_delete. 
      destruct (Hr'_full r_t1) as [r1v ?].
      iDestruct (big_sepM_delete _ _ r_t1 with "Hregs'") as "[Hr1 Hregs']".
        by rewrite lookup_delete_ne //.
      destruct (Hr'_full r_env) as [renvv ?].
      iDestruct (big_sepM_delete _ _ r_env with "Hregs'") as "[Hrenv Hregs']".
        by rewrite !lookup_delete_ne //.
      (* Step through the closure code *)
      (* TODO: the part where we step through the closure initialization code
         should be moved to a separate lemma in stack_macros *)
      iDestruct (big_sepL2_length with "Hcls") as %Hcls_len. simpl in Hcls_len.
      rewrite /region_mapsto.
      assert (b_cls + 8 = Some e_cls)%a as Hbe.
      { rewrite region_addrs_length /region_size in Hcls_len.
        revert Hcls_len; clear; solve_addr. }
      assert (contiguous_between (region_addrs b_cls e_cls) b_cls e_cls) as Hcont_cls.
      { apply contiguous_between_of_region_addrs; auto. revert Hbe; clear; solve_addr. }
      pose proof (region_addrs_NoDup b_cls e_cls) as Hcls_nodup.
      iDestruct (big_sepL2_split_at 6 with "Hcls") as "[Hcls_code Hcls_data]".
      cbn [take drop].
      destruct (region_addrs b_cls e_cls) as [| ? ll]; [by inversion Hcls_len|].
      pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont_cls). subst.
      assert (isCorrectPC_range RX Global b_cls e_cls b_cls e_cls).
      { unfold isCorrectPC_range. intros ? [? ?]. constructor; try split; auto. }
      do 7 (destruct ll as [| ? ll]; [by inversion Hcls_len|]).
      destruct ll;[| by inversion Hcls_len]. cbn [take drop].
      iDestruct "Hcls_data" as "(Hcls_ptr & Hcls_env & _)".
      (* move r_t1 PC *)
      iPrologue "Hcls_code". rewrite -j_1.
      iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr1]");
        [rewrite decode_encode_inv // | done | iCorrectPC b_cls e_cls |
         iContiguous_next Hcont_cls 0 | done | ..].
      iEpilogue "(HPC & Hprog_done & Hr1)".
      (* lea r_t1 7 *)
      iPrologue "Hprog". rewrite -j_2.
      iApply (wp_lea_success_z with "[$HPC $Hi $Hr1]");
        [rewrite decode_encode_inv // | done | iCorrectPC b_cls e_cls |
         iContiguous_next Hcont_cls 1 | | done | done | ..].
      { eapply contiguous_between_incr_addr_middle' with (i:=0); eauto.
        cbn. clear. lia. }
      iEpilogue "(HPC & Hi & Hr1)". iCombine "Hi Hprog_done" as "Hprog_done".
      (* load r_env r_t1 *)
      apply NoDup_ListNoDup in Hcls_nodup.
      iPrologue "Hprog". rewrite -j_3.
      (* FIXME: tedious & fragile *)
      assert ((a9 =? a4)%a = false) as H_4_9.
      { apply Z.eqb_neq. intros Heqb. assert (a9 = a4) as ->. revert Heqb; clear; solve_addr.
        exfalso. by pose proof (NoDup_lookup _ 2 7 _ Hcls_nodup eq_refl eq_refl). }
      iApply (wp_load_success with "[$HPC $Hi $Hrenv $Hr1 Hcls_env]");
        [rewrite decode_encode_inv // | done | iCorrectPC b_cls e_cls |
         split;[done|] | iContiguous_next Hcont_cls 2 | ..].
      { eapply contiguous_between_middle_bounds' in Hcont_cls as [? ?].
        by eapply le_addr_withinBounds; eauto. repeat constructor. }
      { rewrite H_4_9. iFrame. eauto. }
      iEpilogue "(HPC & Hrenv & Hi & Hr1 & Hcls_env)". rewrite H_4_9.
      iCombine "Hi Hprog_done" as "Hprog_done".
      (* lea r_t1 (-1) *)
      iPrologue "Hprog". rewrite -j_4.
      iApply (wp_lea_success_z with "[$HPC $Hi $Hr1]");
        [rewrite decode_encode_inv // | done | iCorrectPC b_cls e_cls |
         iContiguous_next Hcont_cls 3 | | done | done | ..].
      { assert ((a8 + 1)%a = Some a9) as HH. by iContiguous_next Hcont_cls 6.
        instantiate (1 := a8). revert HH. clear; solve_addr. }
      iEpilogue "(HPC & Hi & Hr1)". iCombine "Hi Hprog_done" as "Hprog_done".
      (* load r_t1 r_t1 *)
      iPrologue "Hprog". rewrite -j_5.
      (* FIXME: tedious & fragile *)
      assert ((a8 =? a6)%a = false) as H_8_6.
      { apply Z.eqb_neq. intros Heqb. assert (a8 = a6) as ->. revert Heqb; clear; solve_addr.
        exfalso. by pose proof (NoDup_lookup _ 4 6 _ Hcls_nodup eq_refl eq_refl). }
      iApply (wp_load_success_same with "[$HPC $Hi $Hr1 Hcls_ptr]");
        [(* FIXME *) auto | rewrite decode_encode_inv // | done | iCorrectPC b_cls e_cls |
         split;[done|] | iContiguous_next Hcont_cls 4 | ..].
      { eapply contiguous_between_middle_bounds' in Hcont_cls as [? ?].
        by eapply le_addr_withinBounds; eauto. repeat constructor. }
      { rewrite H_8_6. iFrame. eauto. }
      iEpilogue "(HPC & Hr1 & Hi & Hcls_ptr)". rewrite H_8_6.
      iCombine "Hi Hprog_done" as "Hprog_done".
      (* jmp r_t1 *)
      iPrologue "Hprog". rewrite -j_6.
      iApply (wp_jmp_success with "[$HPC $Hi $Hr1]");
        [rewrite decode_encode_inv // | done | iCorrectPC b_cls e_cls | .. ].
      iEpilogue "(HPC & Hi & Hr1)".
      rewrite updatePcPerm_cap_non_E. 2: admit.

      (* close the invariant for the closure *)
      iDestruct ("Hcls_close" with "[Hprog_done $Hna Hi Hcls_env Hcls_ptr]") as ">Hna".
      { repeat iDestruct "Hprog_done" as "(?&Hprog_done)". iNext. iFrame. eauto. }

      iDestruct (big_sepM_insert with "[$Hregs' $Hr1]") as "Hregs'".
        by rewrite lookup_delete_ne // lookup_delete //.
        rewrite -delete_insert_ne // insert_delete.
      destruct (Hr'_full r_t0) as [r0v Hr0v].
      iDestruct (big_sepM_delete _ _ r_t0 with "Hregs'") as "[Hr0 Hregs']".
        by rewrite lookup_delete_ne // lookup_insert_ne // lookup_delete_ne //.
      destruct (Hr'_full r_adv) as [radvv Hradvv].
      iDestruct (big_sepM_delete _ _ r_adv with "Hregs'") as "[Hradv Hregs']".
        by rewrite !lookup_delete_ne // lookup_insert_ne // lookup_delete_ne //.
      destruct (Hr'_full r_stk) as [rstkv Hrstkv].
      iDestruct (big_sepM_delete _ _ r_stk with "Hregs'") as "[Hrstk Hregs']".
        by rewrite !lookup_delete_ne // lookup_insert_ne // lookup_delete_ne //.

      iApply (f4_spec with "[$HPC $Hr0 $Hradv $Hrenv $Hrstk $Hregs' $Hrel_i $Hna $Hsts $Hr]").
      { admit. }
      { admit. }
      { revert Hbe_cell; clear; solve_addr. }
      { rewrite !dom_delete_L !dom_insert_L !dom_delete_L Hdom_r'.
        rewrite !singleton_union_difference_L !all_registers_union_l !difference_difference_L.
        f_equal. clear. set_solver. }
      iSplitL. iExists awkN; iApply "Hawk_inv".
      iSplitL.
      { unshelve iSpecialize ("Hr'_valid" $! r_stk _); [done|].
        rewrite /(RegLocate r' r_stk) Hrstkv. iApply "Hr'_valid". }
      iSplitL.
      { unshelve iSpecialize ("Hr'_valid" $! r_adv _); [done|].
        rewrite /(RegLocate r' r_adv) Hradvv. iApply "Hr'_valid". }
      iSplitL.
      { unshelve iSpecialize ("Hr'_valid" $! r_t0 _); [done|].
        rewrite /(RegLocate r' r_t0) Hr0v. iApply "Hr'_valid". }
      { iExists _; iApply "Hawk". }
      { iNext. iIntros (?) "HH". iIntros (->). iApply "HH". eauto. }
    }

    unshelve iSpecialize ("Hr_valid" $! r_t0 _). done.
    rewrite /(RegLocate _ r_t0) Hr0.

    iAssert (((fixpoint interp1) W2) r0) as "#Hr_valid2". 
    { iApply (interp_monotone with "[] Hr_valid"). iPureIntro. apply related_sts_pub_world_fresh_loc; auto. }
    set r' : gmap RegName Word :=
      <[r_t0  := r0]>
      (<[r_t1 := inr (E, Global, b_cls, e_cls, b_cls)]>
       (create_gmap_default (list_difference all_registers [r_t0;r_t1]) (inl 0%Z))).

    (* either we fail, or we use the continuation in rt0 *)
    iDestruct (jmp_or_fail_spec with "Hr_valid2") as "Hcont".
    destruct (decide (isCorrectPC (updatePcPerm r0))). 
    2 : { iEpilogue "(HPC & Hi & Hr0)". iApply "Hcont". iFrame "HPC". iIntros (Hcontr);done. }
    iDestruct "Hcont" as (p g b e a3 Heq) "#Hcont". 
    simplify_eq. 

    iAssert (future_world g W2 W2) as "Hfuture".
    { destruct g; iPureIntro. apply related_sts_priv_refl_world. apply related_sts_pub_refl_world. }
    iSpecialize ("Hcont" $! r W2 with "Hfuture"). 

    (* prepare the continuation *)
    iEpilogue "(HPC & Hi & Hr0)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    iSpecialize ("Hcont" with "[Hsts Hr Hregs HPC Hr0 Hr1 HnaI]").
    { iFrame. iDestruct (region_monotone with "[] [] Hr") as "$";
                [auto|iPureIntro;apply related_sts_pub_world_fresh_loc; auto|].
      (* register manipulation *)
      admit. }

    (* apply the continuation *)
    iDestruct "Hcont" as "[_ Hcallback_now]".
    iApply wp_wand_l. iFrame "Hcallback_now". 
    iIntros (v) "Hφ".
    iIntros (Hne).
    iDestruct ("Hφ" $! Hne) as (r0 W') "(Hfull & Hregs & #Hrelated & Hna & Hsts & Hr)". 
    iExists r0,W'. iFrame.
    iDestruct "Hrelated" as %Hrelated. iPureIntro.
    eapply related_sts_pub_priv_trans_world;[|eauto]. 
    apply related_sts_pub_world_fresh_loc; auto.

  Admitted.

End awkward_example_preamble.
