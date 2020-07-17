From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
Require Import Eqdep_dec. 
From cap_machine Require Import
     rules logrel fundamental region_invariants
     region_invariants_revocation region_invariants_static.
From cap_machine.examples Require Import region_macros stack_macros scall malloc awkward_example_helpers.
From stdpp Require Import countable.
    
Section awkward_example.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          `{MonRef: MonRefG (leibnizO _) CapR_rtc Σ} {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS). 
  Implicit Types W : WORLD.

  (* choose a special register for the environment and adv pointer *)
  (* note that we are here simplifying the environment to simply point to one location *)      
   Definition r_env : RegName := r_t30.
   Definition r_adv : RegName := r_t28.

   Definition awkward_epilogue_off := 65%Z.

   (* r1 contains an executable pointer to adversarial code *)
   (* f_a is the offset to the failure subroutine in the environment table *)
   (* by convention a pointer to the linking table is at the bottom address of the PC *)
   Definition awkward_instrs f_a (r1 : RegName) :=
     reqglob_instrs r1 ++
     prepstack_instrs r_stk 11 ++
     [store_z r_env 0] ++
     push_r_instrs r_stk r_env ++
     push_r_instrs r_stk r_t0 ++
     push_r_instrs r_stk r1 ++
     scall_prologue_instrs awkward_epilogue_off r1 ++
     [jmp r1;
     sub_z_z r_t1 0 7;
     lea_r r_stk r_t1] ++
     pop_instrs r_stk r1 ++
     pop_instrs r_stk r_t0 ++
     pop_instrs r_stk r_env ++
     [store_z r_env 1] ++
     push_r_instrs r_stk r_env ++
     push_r_instrs r_stk r_t0 ++ 
     scall_prologue_instrs awkward_epilogue_off r1 ++
     [jmp r1;
     sub_z_z r_t1 0 7;
     lea_r r_stk r_t1] ++
     pop_instrs r_stk r_t0 ++
     pop_instrs r_stk r_env ++
     (* assert that the cap in r_env points to 1 *)
     [load_r r1 r_env] ++
     assert_r_z_instrs f_a r1 1 ++
     (* in this version, we clear only the local stack frame before returning *)
     (* first we prepare the stack to only point to the local stack frame *)
     [getb r_t1 r_stk;
     add_r_z r_t2 r_t1 10;
     subseg_r_r r_stk r_t1 r_t2] ++ 
     mclear_instrs r_stk ++
     rclear_instrs (list_difference all_registers [PC;r_t0]) ++
     [jmp r_t0].

   Definition awkward_instrs_length : Z :=
     Eval cbv in (length (awkward_instrs 0 r_adv)).

   Definition awkward_example (a : list Addr) (p : Perm) f_a (r1 : RegName) : iProp Σ :=
     ([∗ list] a_i;w_i ∈ a;(awkward_instrs f_a r1), a_i ↦ₐ[p] w_i)%I.

   
  Ltac middle_lt prev index :=
    match goal with
    | Ha_first : ?a !! 0 = Some ?a_first |- _ 
    => apply Z.lt_trans with prev; auto; apply incr_list_lt_succ with a index; auto
    end. 

  Ltac iContiguous_bounds i j :=
    eapply contiguous_between_middle_bounds' with (a0 := i) (an := j);
    [ eauto | cbn; solve [ repeat constructor ] ].

  Ltac iCorrectPC i j :=
    eapply isCorrectPC_contiguous_range with (a0 := i) (an := j); eauto; [];
    cbn; solve [ repeat constructor ].

  Ltac iContiguous_bounds_withinBounds a0 an :=
    apply isWithinBounds_bounds_alt' with a0 an; auto; [];
    iContiguous_bounds a0 an.

  Lemma isCorrectPC_range_npE p g b e a0 an :
    isCorrectPC_range p g b e a0 an →
    (a0 < an)%a →
    p ≠ E.
  Proof.
    intros HH1 HH2. 
    destruct (isCorrectPC_range_perm _ _ _ _ _ _ HH1 HH2) as [?| [?|?] ]; 
      congruence.
  Qed.

  Ltac isWithinBounds := rewrite /withinBounds; apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; simpl; auto.

  Ltac iNotElemOfList :=
    repeat (apply not_elem_of_cons; split;[auto|]); apply not_elem_of_nil.  

  Ltac addr_succ :=
    match goal with
    | H : _ |- (?a1 + ?z)%a = Some ?a2 =>
      rewrite /incr_addr /=; do 2 f_equal; apply eq_proofs_unicity; decide equality
    end.

  (* The following ltac gets out the next general purpuse register *)
  Ltac get_genpur_reg Hr_gen wsr ptr :=
    let w := fresh "wr" in 
    destruct wsr as [? | w wsr]; first (by iApply bi.False_elim);
    iDestruct Hr_gen as ptr.
  
  Ltac iDestructList Hlength l :=
    (repeat (let a := fresh "a" in destruct l as [|a l];[by inversion Hlength|]));
    destruct l;[|by inversion l].
  
  Ltac iContiguous_next Ha index :=
    apply contiguous_of_contiguous_between in Ha;
    generalize (contiguous_spec _ Ha index); auto.
  
  Ltac iPrologue_pre l Hl :=
    destruct l; [inversion Hl|]; iApply (wp_bind (fill [SeqCtx])).
  
  Ltac iPrologue l Hl prog := 
    iPrologue_pre l Hl;
    iDestruct prog as "[Hinstr Hprog]".     
  
  Ltac iEpilogue intro_ptrn :=
    iNext; iIntros intro_ptrn; iSimpl;
    iApply wp_pure_step_later;auto;iNext.

  Ltac iLookupR Hl :=
    rewrite /= lookup_app_r;rewrite Hl /=;auto.
  
  Ltac iPush_z prog :=
    let cont := fresh "cont" in
    let a_rest := fresh "a_rest" in
    let push2 := fresh "push2" in
    let Ha1 := fresh "Ha1" in
    let Ha2 := fresh "Ha2" in
    let Ha := fresh "Ha" in
    iDestruct (push_z_instrs_extract with prog) as (a_rest push2 cont)
      "((Hpush & Hprog) & #Hcont)"; eauto;
    iDestruct "Hcont" as %(-> & Ha1 & Ha2 & Ha);
    iApply (push_z_spec with "[-]"); last iFrame "Hpush HPC Hr_stk Ha"; eauto;
    clear Ha1 Ha2; last iRename "Hprog" into prog.

  Ltac iPush_r prog :=
    let cont := fresh "cont" in
    let a_rest := fresh "a_rest" in
    let push2 := fresh "push2" in
    let Ha1 := fresh "Ha1" in
    let Ha2 := fresh "Ha2" in
    let Ha := fresh "Ha" in
    iDestruct (push_r_instrs_extract with prog) as (a_rest push2 cont)
      "((Hpush & Hprog) & #Hcont)"; eauto;
    iDestruct "Hcont" as %(-> & Ha1 & Ha2 & Ha);
    iApply (push_r_spec with "[-]"); last iFrame "Hpush HPC Hr_stk Ha Hreg";
    last iRename "Hprog" into prog.
  
  Ltac iGet_genpur_reg Hr_gen Hwsr wsr ptr :=
    let w := fresh "wr" in 
    destruct wsr as [? | w wsr]; first (by inversion Hwsr);
    iDestruct Hr_gen as ptr.
  
  Ltac iGet_genpur_reg_map r' reg Hgen_reg Hfull Hgen_ptrn :=
    let w := fresh "w" in
    let Hw := fresh "Hw" in 
    iAssert (⌜∃ w, r' !! reg = Some w⌝)%I as %[w Hw];
    first iApply Hfull;
    iDestruct (big_sepM_delete _ _ reg with Hgen_reg) as Hgen_ptrn;
    [repeat (rewrite lookup_delete_ne; auto; (try by (rewrite lookup_insert_ne; eauto)))|].
  
  Ltac iClose_genpur_reg_map reg Hgen_ptrn Hgen :=
    repeat (rewrite -(delete_insert_ne _ reg); [|auto]);
    iDestruct (big_sepM_insert _ _ reg with Hgen_ptrn) as Hgen;[apply lookup_delete|iFrame|rewrite insert_delete].

  (* ---------------------------------------------------------------------------------------------- *)
  (* --------------------------------------- Register Map Lemmas ---------------------------------- *)
  (* ---------------------------------------------------------------------------------------------- *)

   Lemma registers_mapsto_resources pc_w stk_w rt0_w adv_w pc_w' (rmap: gmap RegName Word) :
    dom (gset RegName) rmap = all_registers_s ∖ {[PC; r_stk; r_t0; r_adv]} →
    ([∗ map] r_i↦_ ∈ rmap, r_i ↦ᵣ inl 0%Z)
    -∗ r_stk ↦ᵣ stk_w
    -∗ r_t0 ↦ᵣ rt0_w
    -∗ r_adv ↦ᵣ adv_w
    -∗ PC ↦ᵣ pc_w'
    -∗
    registers_mapsto (<[PC:=pc_w']> (<[PC:=pc_w]> (<[r_stk:=stk_w]> (<[r_t0:=rt0_w]> (<[r_adv:=adv_w]>
      (create_gmap_default (list_difference all_registers [PC; r_stk; r_t0; r_adv]) (inl 0%Z))))))).
  Proof.
    iIntros (Hdom) "Hregs Hr_stk Hr_t0 Hr_adv HPC".
    rewrite /registers_mapsto insert_insert.
    do 4 (rewrite big_sepM_insert; [iFrame|done]).
    iDestruct (big_sepM_dom with "Hregs") as "Hregs".
    iApply (big_sepM_mono (λ k _, k ↦ᵣ inl 0%Z))%I.
    { intros * [? ->]%create_gmap_default_lookup_is_Some. auto. }
    iApply big_sepM_dom. rewrite big_opS_proper'. iFrame. done.
    rewrite Hdom.
    rewrite create_gmap_default_dom list_to_set_difference -/all_registers_s.
    f_equal. clear. set_solver.
  Qed.

  Lemma r_full (pc_w stk_w rt0_w adv_w : Word) :
    full_map (Σ:=Σ) (<[PC:=pc_w]> (<[r_stk:=stk_w]> (<[r_t0:=rt0_w]> (<[r_adv:=adv_w]>
           (create_gmap_default (list_difference all_registers [PC; r_stk; r_t0; r_adv]) (inl 0%Z)))))).
  Proof.
    rewrite /full_map. iPureIntro. intros rr. cbn beta.
    rewrite elem_of_gmap_dom 4!dom_insert_L create_gmap_default_dom list_to_set_difference.
    rewrite -/all_registers_s. generalize (all_registers_s_correct rr). clear. set_solver.
  Qed.

  Lemma r_zero (pc_w stk_w rt0_w adv_w : Word) r1 :
    r1 ≠ r_stk → r1 ≠ PC → r1 ≠ r_t0 → r1 ≠ r_adv →
    (<[PC:=pc_w]> (<[r_stk:=stk_w]> (<[r_t0:=rt0_w]> (<[r_adv:=adv_w]>
           (create_gmap_default (list_difference all_registers [PC; r_stk; r_t0; r_adv]) (inl 0%Z)))))) !r! r1 = inl 0%Z.
  Proof.
    intros Hr_stk HPC Hr_t0 Hr_t30. rewrite /RegLocate.
    destruct (<[PC:=pc_w]>
              (<[r_stk:=stk_w]>
               (<[r_t0:=rt0_w]>
                (<[r_adv:=adv_w]> (create_gmap_default (list_difference all_registers [PC; r_stk; r_t0; r_adv])
                                                       (inl 0%Z)))))
                !! r1) eqn:Hsome; rewrite Hsome; last done.
    do 4 (rewrite lookup_insert_ne in Hsome;auto).
    assert (Some s = Some (inl 0%Z)) as Heq.
    { rewrite -Hsome. apply create_gmap_default_lookup.
      apply elem_of_list_difference. split; first apply all_registers_correct.
      repeat (apply not_elem_of_cons;split;auto).
      apply not_elem_of_nil. 
    } by inversion Heq. 
  Qed.

  (* ---------------------------------------------------------------------------------------------- *)
  (* --------------------------------------- World Related Lemmas --------------------------------- *)
  (* ---------------------------------------------------------------------------------------------- *)
  
   (* The following lemmas asserts that the world upon return is indeed a public future world of W and W3 *)
   (* As the first step we want to show that if we assert that the closed region corresponds to ALL the 
      temporary region, then closing a revoked W equals W *)
   
   Lemma related_pub_local_3 W W' W3 W6 b e l l' l1 l2 m1 m2 i c c' :
     W' = ((revoke_std_sta W.1),(<[i:=encode false]> W.2.1,W.2.2))
     -> (b <= c < e)%a ∧ (b <= c' < e)%a
     (* l is the list of all revoked resources in W *)
     -> (forall a : Addr, W.1 !! a = Some Temporary <-> a ∈ l)
     (* l' is the list of all addition revoked resources in W3 (other than [c,e)) *)
     -> (forall a : Addr, W3.1 !! a = Some Temporary <-> a ∈ l')
     (* m1 and m2 are the maps containing the local frame and the rest of the temporary resources *)
     -> (l ≡ₚl1 ++ (region_addrs b e) ∧ l' ≡ₚl2 ++ (region_addrs c e) ∧
        elements (dom (gset Addr) m1) ≡ₚl1 ++ (region_addrs b c)
        ∧ elements (dom (gset Addr) m2) ≡ₚl1 ++ l2 ++ (region_addrs b c'))
     (* i is the awkward invariant *)
     → W.2.2 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv)
     -> (∃ (b : bool), W.2.1 !! i = Some (encode b))
     (* relations between intermediary worlds *)
     → related_sts_pub_world
         (close_list (region_addrs c e)
                     (std_update_multiple
                        (revoke (W.1,((<[i:=encode false]> W.2.1), W.2.2)))
                     (elements (dom (gset Addr) m1))
                     (Static m1))) W3
     → related_sts_pub_world
         (close_list (region_addrs c' e)
                     (std_update_multiple
                        (std_update_multiple
                           (revoke (W3.1, ((<[i:=encode true]> W3.2.1), W3.2.2)))
                           (elements (dom (gset Addr) m1))
                           Revoked)
                     (elements (dom (gset Addr) m2))
                     (Static m2))) W6
     → related_sts_pub_world W (std_update_temp_multiple W6 (elements (dom (gset Addr) m2))).
   Proof.
     intros Heq [Hbounds1 Hbounds2] Hiff1 Hiff2 Happ Hawk [x Hawki] Hrelated1 Hrelated2. 
     subst W'.
     simpl in *.
     split; simpl. 
     - (* standard resources *)
       destruct Hrelated1 as [Hstd_related1 _]. 
       destruct Hrelated2 as [Hstd_related2 _]. simpl in *. 
       destruct Hstd_related2 as [Hstd_sta_dom2 Hstd_related2].
       destruct Hstd_related1 as [Hstd_sta_dom1 Hstd_related1].
       assert (dom (gset Addr) (std W) ⊆ dom (gset Addr) (std W6)) as Hsub.
       { rewrite -close_list_dom_eq in Hstd_sta_dom1.
         trans (dom (gset Addr) (std W3)).
         - etrans;[|apply Hstd_sta_dom1]. etrans;[|apply std_update_multiple_sta_dom_subseteq].
           rewrite -revoke_dom_eq. done.
         - etrans;[|apply Hstd_sta_dom2].
           rewrite -close_list_dom_eq. 
           repeat (etrans;[|apply std_update_multiple_sta_dom_subseteq]).
           rewrite -revoke_dom_eq. done. 
       }
       split.
       + etrans;[|apply std_update_multiple_sta_dom_subseteq]. auto. 
       + intros k x0 y Hx0 Hy.
         destruct W as [ Wstd_sta [Wloc_sta Wloc_rel] ].
         destruct W3 as [ Wstd_sta3 [Wloc_sta3 Wloc_rel3] ].
         destruct W6 as [ Wstd_sta6 [Wloc_sta6 Wloc_rel6] ].
         simpl in *.
         destruct (decide (k ∈ l1 ++ l2 ++ (region_addrs b c'))).
         * (* k is a revoked element, which is updated to static at the end *)
           destruct Happ as (Heq1' & Heq2' & Heq3' & Heq4'). 
           rewrite std_sta_update_multiple_lookup_in_i in Hy;auto.
           2: { rewrite Heq4'. auto. }
           inversion Hy; subst.
           (* apply elem_of_list_fmap in e0 as [a [Heqa e0] ]. subst. *)
           apply elem_of_app in e0 as [Hl1 | Hl']. 
           ** (* k is a revoked element in l1 *)
             assert (Wstd_sta !! k = Some Temporary) as Htemp. 
             { apply Hiff1. rewrite Heq1'. apply elem_of_app. by left. }
             rewrite Htemp in Hx0; inversion Hx0; subst. left.
           ** (* k is a either revoked element in l2 or [b,c'] *)
             apply elem_of_app in Hl' as [Hl2 | Hbc']. 
             *** (* k is a revoked element in l2 *)
               assert (Wstd_sta3 !! k = Some Temporary) as Htemp.
               { apply Hiff2. rewrite Heq2'. apply elem_of_app. by left. }
               (* if x0 is temp we are done *)
               destruct (decide (x0 = Temporary));[subst;left|].
               (* o/w it cannot be an element of either l1 or [b,e], which means it will not get set to static *)
               apply Hstd_related1 with k; auto. 
               assert (k ∉ l1 ++ region_addrs b e) as Hnin.
               { rewrite -Heq1'. intros Hin. apply Hiff1 in Hin. rewrite Hx0 in Hin. inversion Hin. contradiction. }
               apply not_elem_of_app in Hnin as [Hl1 Hbe].
               rewrite (region_addrs_split _ c) in Hbe;[|revert Hbounds1;clear;solve_addr].
               apply not_elem_of_app in Hbe as [Hbc Hce].
               rewrite -close_list_std_sta_same.
               rewrite std_sta_update_multiple_lookup_same_i.
               rewrite revoke_monotone_lookup_same;auto.
               rewrite Hx0. intros Hcontr; inversion Hcontr; contradiction.
               rewrite Heq3'. apply not_elem_of_app. split;auto.
               revert Hce. clear. set_solver.
             *** (* k is a revoked element in [b,c'] *)
               assert (Wstd_sta !! k = Some Temporary) as Htemp.
               { apply Hiff1. rewrite Heq1'. apply elem_of_app. right.
                 rewrite (region_addrs_split _ c');[|revert Hbounds2;clear;solve_addr].
                 apply elem_of_app. by left. }
               rewrite Hx0 in Htemp. inversion Htemp. left. 
         * destruct Happ as [Heq1' [Heq2' [Heq3' Heq4'] ] ]. repeat rewrite fmap_app in n.
           apply not_elem_of_app in n as [Hl1 Hn1].
           apply not_elem_of_app in Hn1 as [Hl2 Hbc'].
           subst. 
           (* we have two more cases, either k is an element of the stack passed on to adv call 2, 
              or k was never a revoked element *)
           destruct (decide (k ∈ region_addrs c' e)). 
           ** (* k is an element of the stack and was revoked in W *)
             assert (Wstd_sta !! k = Some Temporary) as Htemp.
             { subst. 
               apply Hiff1. rewrite Heq1'. apply elem_of_app. right.
               rewrite (region_addrs_split _ c');[|revert Hbounds2;clear;solve_addr]. 
               apply elem_of_app. right. revert e0. clear. set_solver. 
             }
             rewrite std_sta_update_multiple_lookup_same_i in Hy.
             2: { rewrite Heq4'. repeat (apply not_elem_of_app;split;auto). }
             destruct (decide (k ∈ region_addrs c e)) as [Hce | Hce]. 
             *** (* if k is in [c,e], we know its temporary by Hiff2 *)
               assert (Wstd_sta3 !! k = Some Temporary) as Htemp3.
               { apply Hiff2. rewrite Heq2'. apply elem_of_app. right. revert Hce;clear;set_solver. }
               subst. rewrite Htemp in Hx0. inversion Hx0; subst. apply Hstd_related2 with k; auto.
               apply close_list_std_sta_revoked;auto. 
               rewrite std_sta_update_multiple_lookup_same_i;auto. 
               2: { rewrite Heq4'. revert Hl1 Hl2 Hbc'. clear. set_solver. }
               (* if a is in [c,e] and [c',e],it cannot also be in [b,c] *)
               assert (k ∉ region_addrs b c) as Hbc.
               { destruct (decide (c < c')%a). 
                 - rewrite (region_addrs_split _ c) in Hbc';[|revert Hbounds1 l0;clear;solve_addr].
                   revert Hbc'; clear; set_solver.
                 - assert (c' ≤ c)%Z as Hle;[revert n;clear;solve_addr|].
                   destruct (decide (c = c'));[subst;revert Hbc';clear;set_solver|].
                   apply region_addrs_xor_elem_of with (c:=c) in e0;[|revert Hbounds1 Hle;clear;solve_addr]. 
                   rewrite (region_addrs_split _ c');[|revert Hbounds2 Hle;clear;solve_addr].
                   apply not_elem_of_app;split;[revert Hbc';clear;set_solver|].
                   revert Hce e0;clear. set_solver. 
               } 
               rewrite std_sta_update_multiple_lookup_same_i;auto.
               2: { rewrite Heq3'. revert Hl1 Hbc. clear. set_solver. }
               rewrite /revoke /std /=. apply revoke_lookup_Temp; auto.
             *** (* otherwise we must assert that it could have been revoked, then closed before the second call *)
               (* apply Hrelated2; auto. *)
               assert (Wstd_sta3 !! k ≠ Some Temporary) as Htemp3.
               { intros Hcontr. apply Hiff2 in Hcontr. subst. 
                 revert Hcontr. rewrite Heq2'. revert Hce Hl2. clear; intros. set_solver. }
               assert (k ∈ dom (gset Addr) Wstd_sta3) as Hin3.
               { apply elem_of_subseteq in Hstd_sta_dom1. apply Hstd_sta_dom1. apply elem_of_gmap_dom.
                 apply close_list_std_sta_is_Some.
                 apply std_sta_update_multiple_is_Some. 
                 rewrite -revoke_std_sta_lookup_Some. eauto. }
               apply elem_of_gmap_dom in Hin3 as [y3 Hy3].
               rewrite Hx0 in Htemp. inversion Htemp. subst.
               (* if a is in [c,e],it must also be in [b,c] *)
               assert (k ∈ region_addrs b c) as Hbc.
               { destruct (decide (c < c')%a). 
                 - rewrite (region_addrs_split _ c') in Hce;[|revert Hbounds2 l0;clear;solve_addr].
                   revert Hce e0; clear; set_solver.
                 - assert (c' ≤ c)%Z as Hle;[revert n;clear;solve_addr|].
                   rewrite (region_addrs_split _ c) in e0;[|revert Hbounds1 Hle;clear;solve_addr].
                   apply elem_of_app in e0 as [Hc'c | Hcontr];[|contradiction].
                   rewrite (region_addrs_split _ c');[|revert Hbounds2 Hle;clear;solve_addr].
                   apply elem_of_app. by right. 
               }
               (* before the first call, the resource is set of Static *)
               assert (rtc std_rel_pub (Static m1) y3) as Hrelated.
               { apply Hstd_related1 with k;auto. 
                 rewrite -close_list_std_sta_same;[|revert Hce;clear;set_solver].
                 apply std_sta_update_multiple_lookup_in_i. rewrite Heq3'. apply elem_of_app. by right. }
               (* we know that it stayed Static since y3 is not Temporary *)
               apply std_rel_pub_rtc_Static with (g:=m1) in Hrelated as [-> | ->];auto;[contradiction|].
               apply Hstd_related2 with k; auto.
               apply close_list_std_sta_revoked; [revert e0;clear;set_solver|].
               rewrite std_sta_update_multiple_lookup_same_i;auto. 
               2: { rewrite Heq4'. revert Hbc' Hl1 Hl2. clear. set_solver. }
               rewrite std_sta_update_multiple_lookup_in_i;auto.
               rewrite Heq3'. revert Hbc;clear;set_solver. 
           ** (* if k is never a revoked element, we can apply its transitions during the two future world relations *)
             assert (k ∈ dom (gset Addr) Wstd_sta3) as Hin3.
             { apply elem_of_subseteq in Hstd_sta_dom1. apply Hstd_sta_dom1. apply elem_of_gmap_dom.
               apply close_list_std_sta_is_Some.
               apply std_sta_update_multiple_is_Some. 
               rewrite -revoke_std_sta_lookup_Some. eauto. }
             apply elem_of_gmap_dom in Hin3 as [y3 Hy3].
             assert (k ∉ region_addrs b e) as Hbe.
             { rewrite (region_addrs_split _ c'). revert Hbc' n. clear. set_solver.
               revert Hbounds2. clear. solve_addr. }
             assert (k ∉ region_addrs b c) as Hbc.
             { rewrite (region_addrs_split _ c) in Hbe. revert Hbe. clear. set_solver. revert Hbounds1;clear;solve_addr. }
             assert (k ∉ region_addrs c e) as Hce.
             { rewrite (region_addrs_split _ c) in Hbe. revert Hbe. clear. set_solver. revert Hbounds1;clear;solve_addr. }
             rewrite std_sta_update_multiple_lookup_same_i in Hy.
             2: { rewrite Heq4'. revert Hl1 Hl2 Hbc'. clear. set_solver. }
             trans y3. 
             *** apply Hstd_related1 with k; auto.
                 rewrite -close_list_std_sta_same; [|revert Hce;clear;set_solver].
                 rewrite std_sta_update_multiple_lookup_same_i;[|rewrite Heq3';revert Hl1 Hbc;clear;set_solver].
                 rewrite revoke_monotone_lookup_same;auto.
                 intros Hcontr. subst. apply Hiff1 in Hcontr. revert Hcontr. rewrite Heq1' =>Hcontr.
                 revert Hcontr Hl1 Hbe;clear;set_solver.
             *** apply Hstd_related2 with k;auto. 
                 rewrite -close_list_std_sta_same; [|revert n;clear;set_solver]. 
                 rewrite std_sta_update_multiple_lookup_same_i;[|rewrite Heq4';revert Hl1 Hl2 Hbc';clear;set_solver].
                 rewrite std_sta_update_multiple_lookup_same_i;[|rewrite Heq3';revert Hl1 Hbc;clear;set_solver].
                 rewrite revoke_monotone_lookup_same;auto.
                 intros Hcontr. apply Hiff2 in Hcontr. revert Hcontr. rewrite Heq2' =>Hcontr.
                 revert Hcontr Hl1 Hl2 Hce;clear;set_solver.
     - (* owned resources *)
       destruct Hrelated1 as [_ Hloc_related1]. 
       destruct Hrelated2 as [_ Hloc_related2]. simpl in *. 
       destruct Hloc_related2 as [Hloc_sta_dom2 [Hloc_rel_dom2 Hloc_related2] ].
       destruct Hloc_related1 as [Hloc_sta_dom1 [Hloc_rel_dom1 Hloc_related1] ].
       split;[|split].
       + rewrite std_update_multiple_loc_sta /=.
         etrans;[|apply Hloc_sta_dom2]. repeat rewrite std_update_multiple_loc_sta /=.
         trans (dom (gset positive) W3.2.1);[|rewrite dom_insert_L;clear;set_solver].
         etrans;[|apply Hloc_sta_dom1]. rewrite std_update_multiple_loc_sta /=.
         rewrite dom_insert_L;clear;set_solver. 
       + rewrite std_update_multiple_loc_rel /=. etrans;[|apply Hloc_rel_dom2]. 
         repeat rewrite std_update_multiple_loc_rel /=. etrans;[|apply Hloc_rel_dom1].
         by rewrite std_update_multiple_loc_rel /=.
       + rewrite std_update_multiple_loc_sta std_update_multiple_loc_rel /=.
         repeat rewrite std_update_multiple_loc_sta std_update_multiple_loc_rel /= in Hloc_related2.
         repeat rewrite std_update_multiple_loc_sta std_update_multiple_loc_rel /= in Hloc_related1.
         destruct W as [ [Wstd_sta Wstd_rel] [Wloc_sta Wloc_rel] ].
         destruct W3 as [ [Wstd_sta3 Wstd_rel3] [Wloc_sta3 Wloc_rel3] ].
         destruct W6 as [ [Wstd_sta6 Wstd_rel6] [Wloc_sta6 Wloc_rel6] ].
         simpl in *. 
         intros k r1 r2 r1' r2' Hr Hr'.
         assert (is_Some (Wloc_rel3 !! k)) as [ [s1 s2] Hs].
         { apply elem_of_gmap_dom. apply elem_of_subseteq in Hloc_rel_dom1; apply Hloc_rel_dom1.
           assert (k ∈ dom (gset positive) Wloc_rel) as Hin;[apply elem_of_gmap_dom;eauto|].
           rewrite std_update_multiple_loc_rel. auto. }
         edestruct Hloc_related1 with (i0:=k) as [Heq1 [Heq2 Hrelated] ];[eauto|eauto|subst]. 
         edestruct Hloc_related2 with (i0:=k) as [Heq1 [Heq2 Hrelated'] ];[eauto|eauto|subst]. 
         repeat split;auto. intros x0 y Hx0 Hy. 
         assert (is_Some (Wloc_sta3 !! k)) as [y3 Hy3].
         { apply elem_of_gmap_dom. apply elem_of_subseteq in Hloc_sta_dom1; apply Hloc_sta_dom1.
           assert (k ∈ dom (gset positive) Wloc_sta) as Hin;[apply elem_of_gmap_dom;eauto|].
           rewrite std_update_multiple_loc_sta. 
           repeat rewrite dom_insert_L. revert Hin. clear. set_solver. }
         destruct (decide (i = k));[subst|].
         * rewrite Hawk in Hr. inversion Hr; subst.           
           rewrite lookup_insert in Hrelated. rewrite lookup_insert in Hrelated'.
           rewrite Hawki in Hx0. inversion Hx0;subst.
           destruct x;[apply Hrelated'; auto|].
           etrans;[|apply Hrelated']; auto. right with (encode true);[|left].
           exists false,true. repeat split;auto. by constructor. 
         * rewrite lookup_insert_ne in Hrelated;auto. rewrite lookup_insert_ne in Hrelated';auto.
           etrans;[apply Hrelated|apply Hrelated']; eauto.
   Qed.

   Lemma related_pub_local_4 W W' W3 W6 b e l l' l1 l2 m1 m2 i c c' :
     W' = ((revoke_std_sta W.1),(<[i:=encode false]> W.2.1,W.2.2))
     -> (b <= c < e)%a ∧ (b <= c' < e)%a
     (* l is the list of all revoked resources in W *)
     -> (forall a : Addr, W.1 !! a = Some Temporary <-> a ∈ l)
     (* l' is the list of all addition revoked resources in W3 (other than [c,e)) *)
     -> (forall a : Addr, W3.1 !! a = Some Temporary <-> a ∈ l')
     (* m1 and m2 are the maps containing the local frame and the rest of the temporary resources *)
     -> (l ≡ₚl1 ++ (region_addrs b e) ∧ l' ≡ₚl2 ++ (region_addrs c e) ∧
        elements (dom (gset Addr) m1) ≡ₚl1 ++ (region_addrs b c)
        ∧ elements (dom (gset Addr) m2) ≡ₚl1 ++ l2 ++ (region_addrs b c'))
     (* i is the awkward invariant *)
     → W.2.2 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv)
     -> (∃ (b : bool), W.2.1 !! i = Some (encode b))
     (* relation between intermediary worlds *)
     → related_sts_pub_world
         (close_list (region_addrs c e)
                     (std_update_multiple
                        (revoke (W.1,((<[i:=encode false]> W.2.1), W.2.2)))
                     (elements (dom (gset Addr) m1))
                     (Static m1))) W3
     → related_sts_pub_world
         (close_list (region_addrs c' e)
                     (std_update_multiple
                        (std_update_multiple
                           (revoke (W3.1, ((<[i:=encode true]> W3.2.1), W3.2.2)))
                           (elements (dom (gset Addr) m1))
                           Revoked)
                     (elements (dom (gset Addr) m2))
                     (Static m2))) W6
     → related_sts_pub_world W3 (std_update_temp_multiple W6 (elements (dom (gset Addr) m2))).
   Proof.
     intros Heq [Hbounds1 Hbounds2] Hiff1 Hiff2 Happ Hawk [x Hawki] Hrelated1 Hrelated2. 
     subst W'.
     simpl in *.
     split; simpl. 
     - (* standard resources *)
       destruct Hrelated1 as [Hstd_related1 _]. 
       destruct Hrelated2 as [Hstd_related2 _]. simpl in *. 
       destruct Hstd_related2 as [Hstd_sta_dom2 Hstd_related2].
       destruct Hstd_related1 as [Hstd_sta_dom1 Hstd_related1].
       assert (dom (gset Addr) (std W3) ⊆ dom (gset Addr) (std W6)) as Hsub.
       { etrans;[|apply Hstd_sta_dom2].
         rewrite -close_list_dom_eq. 
         repeat (etrans;[|apply std_update_multiple_sta_dom_subseteq]).
         rewrite -revoke_dom_eq. done. 
       }
       split.
       + etrans;[|apply std_update_multiple_sta_dom_subseteq]. auto. 
       + intros a x0 y Hx0 Hy.
         destruct W as [ Wstd_sta [Wloc_sta Wloc_rel] ].
         destruct W3 as [ Wstd_sta3 [Wloc_sta3 Wloc_rel3] ].
         destruct W6 as [ Wstd_sta6 [Wloc_sta6 Wloc_rel6] ].
         simpl in *.
         destruct (decide (a ∈ l1 ++ l2 ++ (region_addrs b c'))).
         * (* k is a revoked element, which is updated to static at the end *)
           destruct Happ as (Heq1' & Heq2' & Heq3' & Heq4'). 
           rewrite std_sta_update_multiple_lookup_in_i in Hy;auto.
           2: { rewrite Heq4'. auto. }
           inversion Hy; subst.
           (* apply elem_of_list_fmap in e0 as [a [Heqa e0] ]. subst. *)
           apply elem_of_app in e0 as [Hl1 | Hl']. 
           ** (* k is a revoked element in l1 *)
             assert (Wstd_sta !! a = Some Temporary) as Htemp.
             { apply Hiff1. rewrite Heq1'. apply elem_of_app. by left. }
             (* in this case x0 is either Temporary or Static *)
             assert (rtc std_rel_pub (Static m1) x0) as Hrtc.
             { apply Hstd_related1 with a;auto.
               rewrite -close_list_std_sta_same_alt.
               - apply std_sta_update_multiple_lookup_in_i. rewrite Heq3'. revert Hl1;clear;set_solver.
               - rewrite std_sta_update_multiple_lookup_in_i;[|rewrite Heq3';revert Hl1;clear;set_solver].
                 intros Hcontr. inversion Hcontr as [Heq]. 
             }
             apply std_rel_pub_rtc_Static with (g:=m1) in Hrtc as [-> | ->]. 
             left. right with Temporary;[|left]. constructor. auto. 
           ** (* k is a either revoked element in l2 or [b,c'] *)
             apply elem_of_app in Hl' as [Hl2 | Hbc']. 
             *** (* k is a revoked element in l2 *)
               assert (Wstd_sta3 !! a = Some Temporary) as Htemp.
               { apply Hiff2. rewrite Heq2'. apply elem_of_app. by left. }
               (* if x0 is temp we are done *)
               rewrite Htemp in Hx0. inversion Hx0. left. 
             *** (* k is a revoked element in [b,c'] *)
               assert (a ∈ region_addrs b e) as Hbe.
               { rewrite (region_addrs_split _ c');[|revert Hbounds2;clear;solve_addr].
                 apply elem_of_app. by left. }
               assert (Wstd_sta !! a = Some Temporary) as Htemp.
               { apply Hiff1. rewrite Heq1'. apply elem_of_app. by right. }
               destruct (decide (a ∈ l1 ++ region_addrs b c)). 
               **** (* a was static during the first call *)
                 assert (rtc std_rel_pub (Static m1) x0) as Hrtc.
                 { apply Hstd_related1 with a;auto.
                   rewrite -close_list_std_sta_same_alt.
                   - apply std_sta_update_multiple_lookup_in_i. rewrite Heq3'. revert e0;clear;set_solver.
                   - rewrite std_sta_update_multiple_lookup_in_i;[|rewrite Heq3';revert e0;clear;set_solver].
                     intros Hcontr. inversion Hcontr as [Heq]. 
                 }
                 subst. 
                 apply std_rel_pub_rtc_Static with (g:=m1) in Hrtc as [-> | ->]. 
                 left. right with Temporary;[|left]. constructor. auto. 
               **** (* a was temporary during the first call *)
                 assert (a ∈ region_addrs c e) as Hce.
                 { rewrite (region_addrs_split _ c) in Hbe;[|revert Hbounds1;clear;solve_addr].
                   revert n Hbe;clear;set_solver. }
                 assert (rtc std_rel_pub Temporary x0) as Hrtc.
                 { apply Hstd_related1 with a;auto.
                   apply close_list_std_sta_revoked;[revert Hce;clear;set_solver|].
                   rewrite std_sta_update_multiple_lookup_same_i;[|rewrite Heq3';auto].
                   apply revoke_lookup_Temp. auto. 
                 } 
                 apply std_rel_pub_rtc_Temporary in Hrtc as ->;auto. left. 
         * destruct Happ as [Heq1' [Heq2' [Heq3' Heq4'] ] ]. 
           apply not_elem_of_app in n as [Hl1 Hn1].
           apply not_elem_of_app in Hn1 as [Hl2 Hbc'].
           (* we have two more cases, either k is an element of the stack passed on to adv call 2, 
              or k was never a revoked element *)
           destruct (decide (a ∈ region_addrs c' e)). 
           ** (* k is an element of the stack and was revoked in W *)
             assert (Wstd_sta !! a = Some Temporary) as Htemp.
             { apply Hiff1. rewrite Heq1'. apply elem_of_app. right.
               rewrite (region_addrs_split _ c');[|revert Hbounds2;clear;solve_addr]. 
               apply elem_of_app. right. revert e0. clear. set_solver. 
             }
             rewrite std_sta_update_multiple_lookup_same_i in Hy.
             2: { rewrite Heq4'. repeat rewrite fmap_app. repeat (apply not_elem_of_app;split;auto). }
             destruct (decide (a ∈ region_addrs c e)) as [Hce | Hce]. 
             *** (* if k is in [c,e], we know its temporary by Hiff2 *)
               assert (Wstd_sta3 !! a = Some Temporary) as Htemp3.
               { apply Hiff2. rewrite Heq2'. apply elem_of_app. right. revert Hce;clear;set_solver. }
               rewrite Htemp3 in Hx0. inversion Hx0; subst. apply Hstd_related2 with a; auto.
               apply close_list_std_sta_revoked;[revert e0;clear;set_solver|]. 
               rewrite std_sta_update_multiple_lookup_same_i;auto. 
               2: { rewrite Heq4'. revert Hl1 Hl2 Hbc'. clear. set_solver. }
               (* if a is in [c,e] and [c',e],it cannot also be in [b,c] *)
               assert (a ∉ region_addrs b c) as Hbc.
               { destruct (decide (c < c')%a). 
                 - rewrite (region_addrs_split _ c) in Hbc';[|revert Hbounds1 l0;clear;solve_addr].
                   revert Hbc'; clear; set_solver.
                 - assert (c' ≤ c)%Z as Hle;[revert n;clear;solve_addr|].
                   destruct (decide (c = c'));[subst;revert Hbc';clear;set_solver|].
                   apply region_addrs_xor_elem_of with (c:=c) in e0;[|revert Hbounds1 Hle;clear;solve_addr]. 
                   rewrite (region_addrs_split _ c');[|revert Hbounds2 Hle;clear;solve_addr].
                   apply not_elem_of_app;split;[revert Hbc';clear;set_solver|].
                   revert Hce e0;clear. set_solver. 
               } 
               rewrite std_sta_update_multiple_lookup_same_i;auto.
               2: { rewrite Heq3'. revert Hl1 Hbc. clear. set_solver. }
               apply revoke_lookup_Temp; auto.
             *** (* otherwise we must assert that it could have been revoked, then closed before the second call *)
               (* apply Hrelated2; auto. *)
               assert (Wstd_sta3 !! a ≠ Some Temporary) as Htemp3.
               { intros Hcontr. apply Hiff2 in Hcontr. subst. 
                 revert Hcontr. rewrite Heq2'. revert Hce Hl2. clear; intros. set_solver. }
               (* if a is not in [c,e],it must also be in [b,c] *)
               assert (a ∈ region_addrs b c) as Hbc.
               { destruct (decide (c < c')%a). 
                 - rewrite (region_addrs_split _ c') in Hce;[|revert Hbounds2 l0;clear;solve_addr].
                   revert Hce e0; clear; set_solver.
                 - assert (c' ≤ c)%Z as Hle;[revert n;clear;solve_addr|].
                   rewrite (region_addrs_split _ c) in e0;[|revert Hbounds1 Hle;clear;solve_addr].
                   apply elem_of_app in e0 as [Hc'c | Hcontr];[|contradiction].
                   rewrite (region_addrs_split _ c');[|revert Hbounds2 Hle;clear;solve_addr].
                   apply elem_of_app. by right. 
               }
               (* before the first call, the resource is set of Static *)
               assert (rtc std_rel_pub (Static m1) x0) as Hrelated.
               { apply Hstd_related1 with a;auto. 
                 rewrite -close_list_std_sta_same;[|revert Hce;clear;set_solver].
                 apply std_sta_update_multiple_lookup_in_i. rewrite Heq3'. apply elem_of_app. by right. }
               assert (rtc std_rel_pub Temporary y) as Hrelated'.
               { apply Hstd_related2 with a;auto. 
                 apply close_list_std_sta_revoked;[revert e0;clear;set_solver|]. 
                 rewrite std_sta_update_multiple_lookup_same_i;[|rewrite Heq4';revert Hl1 Hl2 Hbc';clear;set_solver].
                 apply std_sta_update_multiple_lookup_in_i. rewrite Heq3'. revert Hbc;clear;set_solver. }
               apply std_rel_pub_rtc_Temporary in Hrelated' as ->;auto.
               apply std_rel_pub_rtc_Static with (g:=m1) in Hrelated as [-> | ->];auto;[left|].
               right with Temporary;[|left]. constructor. 
           ** (* if k is never a revoked element, we can apply its transitions during the second future world relations *)
             assert (a ∉ region_addrs b e) as Hbe.
             { rewrite (region_addrs_split _ c'). revert Hbc' n. clear. set_solver.
               revert Hbounds2. clear. solve_addr. }
             assert (a ∉ region_addrs b c) as Hbc.
             { rewrite (region_addrs_split _ c) in Hbe. revert Hbe. clear. set_solver. revert Hbounds1;clear;solve_addr. }
             assert (a ∉ region_addrs c e) as Hce.
             { rewrite (region_addrs_split _ c) in Hbe. revert Hbe. clear. set_solver. revert Hbounds1;clear;solve_addr. }
             rewrite std_sta_update_multiple_lookup_same_i in Hy.
             2: { rewrite Heq4'. revert Hl1 Hl2 Hbc'. clear. set_solver. }
             apply Hstd_related2 with a;auto. 
             rewrite -close_list_std_sta_same; [|revert n;clear;set_solver]. 
             rewrite std_sta_update_multiple_lookup_same_i;[|rewrite Heq4';revert Hl1 Hl2 Hbc';clear;set_solver].
             rewrite std_sta_update_multiple_lookup_same_i;[|rewrite Heq3';revert Hl1 Hbc;clear;set_solver].
             rewrite revoke_monotone_lookup_same;auto.
             intros Hcontr. apply Hiff2 in Hcontr. revert Hcontr. rewrite Heq2' =>Hcontr.
             revert Hcontr Hl1 Hl2 Hce;clear;set_solver.
     - (* owned resources *)
       destruct Hrelated1 as [_ Hloc_related1]. 
       destruct Hrelated2 as [_ Hloc_related2]. simpl in *. 
       destruct Hloc_related2 as [Hloc_sta_dom2 [Hloc_rel_dom2 Hloc_related2] ].
       destruct Hloc_related1 as [Hloc_sta_dom1 [Hloc_rel_dom1 Hloc_related1] ].
       split;[|split].
       + repeat rewrite std_update_multiple_loc_sta /=.
         etrans;[|apply Hloc_sta_dom2]. repeat rewrite std_update_multiple_loc_sta /=.
         rewrite dom_insert_L;clear;set_solver. 
       + rewrite std_update_multiple_loc_rel /=. etrans;[|apply Hloc_rel_dom2]. 
         repeat rewrite std_update_multiple_loc_rel /=. auto. 
       + rewrite std_update_multiple_loc_sta std_update_multiple_loc_rel /=.
         repeat rewrite std_update_multiple_loc_sta std_update_multiple_loc_rel /= in Hloc_related2.
         repeat rewrite std_update_multiple_loc_sta std_update_multiple_loc_rel /= in Hloc_related1.
         destruct W as [ [Wstd_sta Wstd_rel] [Wloc_sta Wloc_rel] ].
         destruct W3 as [ [Wstd_sta3 Wstd_rel3] [Wloc_sta3 Wloc_rel3] ].
         destruct W6 as [ [Wstd_sta6 Wstd_rel6] [Wloc_sta6 Wloc_rel6] ].
         simpl in *. 
         intros k r1 r2 r1' r2' Hr Hr'.
         edestruct Hloc_related2 with (i0:=k) as [Heq1 [Heq2 Hrelated'] ];[eauto|eauto|subst]. 
         repeat split;auto. intros x0 y Hx0 Hy. 
         destruct (decide (i = k));[subst|].
         * edestruct Hloc_related1 with (i:=k) as [Heq1 [Heq2 Hrelated] ];[eauto|eauto|subst].
           apply Hrelated with (x:=encode false) in Hx0;[|apply lookup_insert].
           apply Hrelated' with (x:=encode true) in Hy;[|apply lookup_insert].
           apply rtc_rel_pub_false in Hx0 as [-> | ->];auto.
           apply rtc_rel_pub in Hy as ->;auto.
           right with (encode true);[|left].
           repeat eexists. constructor. auto.  
         * (* we distinguish between the case where k exists i W, or allocated in W3 *)
           rewrite lookup_insert_ne in Hrelated';auto.           
   Qed.

  
  (* Shorthand definition for an adress being currently temporary/revoked *)
  Definition region_type_revoked W (a : Addr) :=
    (std W) !! a = Some Revoked.
  Definition region_type_temporary W (a : Addr) :=
    (std W) !! a = Some Temporary.

   (* the following spec is for the f4 subroutine of the awkward example, jumped to after activating the closure *)
  Lemma f4_spec W pc_p pc_p' pc_g pc_b pc_e (* PC *)
        wadv (* adv *)
        wret (* return cap *)
        f4_addrs (* program addresses *)
        d d' i (* dynamically allocated memory given by preamble, connected to invariant i *)
        a_first a_last (* special adresses *)
        f_a b_link e_link a_link a_entry fail_cap (* linking table variables *)
        wstk (* stack *)
        rmap (* registers *)
        ι1 ι2 (* invariant names *) :

    (* PC assumptions *)
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last ->
    PermFlows pc_p pc_p' -> 

    (* Program adresses assumptions *)
    contiguous_between f4_addrs a_first a_last ->
    
    (* Linking table assumptions *)
    withinBounds (RW, Global, b_link, e_link, a_entry) = true →
    (a_link + f_a)%a = Some a_entry ->

    (* malloc'ed memory assumption *)
    (d + 1)%a = Some d' ->

    (* footprint of the register map *)
    dom (gset RegName) rmap = all_registers_s ∖ {[PC;r_stk;r_adv;r_t0;r_env]} →

    (* The two invariants have different names *)
    (up_close (B:=coPset) ι2 ## ↑ι1) ->
    
    {{{ r_stk ↦ᵣ wstk
      ∗ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,a_first)
      ∗ r_t0 ↦ᵣ wret
      ∗ r_adv ↦ᵣ wadv
      ∗ r_env ↦ᵣ inr (RWX,Global,d,d',d)
      ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
      (* invariant for d *)
      ∗ (∃ ι, inv ι (awk_inv i d))
      ∗ sts_rel_loc (A:=Addr) i awk_rel_pub awk_rel_priv
      (* stack *)
      ∗ interp W wstk
      (* token which states all non atomic invariants are closed *)
      ∗ na_own logrel_nais ⊤
      (* adv code *)
      ∗ interp W wadv
      (* callback validity *)
      ∗ interp W wret
      (* trusted code *)
      ∗ na_inv logrel_nais ι1 (awkward_example f4_addrs pc_p' f_a r_adv)
      (* linking table *)
      ∗ na_inv logrel_nais ι2 (pc_b ↦ₐ[pc_p'] inr (RO,Global,b_link,e_link,a_link) ∗ a_entry ↦ₐ[RO] fail_cap)
      (* we start out with arbitrary sts *)
      ∗ sts_full_world W
      ∗ region W
    }}}
      Seq (Instr Executable)
      {{{ v, RET v; ⌜v = HaltedV⌝ →
                    ∃ r W', full_map r ∧ registers_mapsto r
                         ∗ ⌜related_sts_priv_world W W'⌝
                         ∗ na_own logrel_nais ⊤                           
                         ∗ sts_full_world W'
                         ∗ region W' }}}.
  Proof.
    iIntros (Hvpc Hfl Hcont Hwb_table Hlink_table Hd Hrmap_dom Hιne φ)
            "(Hr_stk & HPC & Hr_t0 & Hr_adv & Hr_env & Hgen_reg & #Hι & #Hrel & #Hstack_val & Hna & #Hadv_val & #Hcallback & #Hf4 & #Htable & Hsts & Hr) Hφ".
    (* Now we step through the program *)
    iMod (na_inv_acc with "Hf4 Hna") as "(>Hprog & Hna & Hcls)";[auto..|]. 
    iDestruct (big_sepL2_length with "Hprog") as %Hprog_length.
    destruct (f4_addrs);[inversion Hprog_length|].
    iDestruct "Hι" as (ι) "Hinv".
    (* We get some general purpose registers *)
    iAssert ((∃ w1, r_t1 ↦ᵣ w1) ∗ (∃ w2, r_t2 ↦ᵣ w2) ∗ [∗ map] r_i↦w_i ∈ delete r_t2 (delete r_t1 rmap), r_i ↦ᵣ w_i)%I
      with "[Hgen_reg]" as "(Hr_t1 & Hr_t2 & Hgen_reg)".
    { assert (is_Some (rmap !! r_t1)) as [w1 Hrt1].
      { apply elem_of_gmap_dom. rewrite Hrmap_dom. apply elem_of_difference.
        split;[apply all_registers_s_correct|clear;set_solver]. }
      assert (is_Some (delete r_t1 rmap !! r_t2)) as [w2 Hrt2].
      { apply elem_of_gmap_dom. rewrite dom_delete_L Hrmap_dom. apply elem_of_difference.
        split;[|clear;set_solver]. apply elem_of_difference.
        split;[apply all_registers_s_correct|clear;set_solver]. }
      iDestruct (big_sepM_delete _ _ r_t1 with "Hgen_reg") as "[Hr_t1 Hgen_reg]";[eauto|].
      iDestruct (big_sepM_delete _ _ r_t2 with "Hgen_reg") as "[Hr_t2 Hgen_reg]";[eauto|].
      iSplitL "Hr_t1";[eauto|]. iSplitL "Hr_t2";[eauto|]. iFrame. 
    }
    (* First we require wadv to be global *)
    iDestruct (contiguous_between_program_split with "Hprog") as (reqperm_prog rest link)
                                                                   "(Hreqglob & Hprog & #Hcont)";[apply Hcont|].
    iDestruct "Hcont" as %(Hcont_reqglob & Hcont_rest & Heqapp & Hlink).
    iDestruct (big_sepL2_length with "Hreqglob") as %Hreqglob_length. simpl in Hreqglob_length. 
    iApply (reqglob_spec with "[-]");
      [|apply Hfl|apply Hcont_reqglob|iFrame "HPC Hreqglob Hr_adv Hr_t1 Hr_t2"]. 
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto.
      apply contiguous_between_bounds in Hcont_rest. revert Hmid Hcont_rest;clear;solve_addr. }
    iNext. destruct (isGlobalWord wadv) eqn:Hglob;[|(* Failure *) iApply "Hφ";iIntros (Hcontr);inversion Hcontr].
    (* If the macro is successful, we can infer that it is a Global capability *)
    destruct wadv as [z | [ [ [ [p g] b] e] a'] ];[inversion Hglob|].
    destruct g;[|inversion Hglob]. iExists _,_,_,_. iSplit;[eauto|]. iIntros "(HPC & Hreqglob & Hr_adv & Hr_t1 & Hr_t2)".
    (* Next we prepare the stack *)
    iDestruct (contiguous_between_program_split with "Hprog") as (preptack_prog rest0 link0)
                                                                   "(Hprepstack & Hprog & #Hcont)";[apply Hcont_rest|].
    iDestruct "Hcont" as %(Hcont_prepstack & Hcont_rest0 & Heqapp0 & Hlink0).
    iDestruct (big_sepL2_length with "Hprepstack") as %Hprepstack_length. simpl in Hprepstack_length. 
    iApply (prepstack_spec with "[-]");
      [|apply Hfl|apply Hcont_prepstack|iFrame "HPC Hprepstack Hr_stk"].
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto.
      apply contiguous_between_bounds in Hcont_rest0. revert Hmid Hcont_rest0 Hlink;clear. solve_addr. }
    iSplitL "Hr_t1";[iNext;eauto|]. iSplitL "Hr_t2";[iNext;eauto|].
    iNext. destruct (isPermWord wstk RWLX) eqn:Hperm;[|(* Failure *) iApply "Hφ";iIntros (Hcontr);inversion Hcontr].
    destruct (11 <? cap_size wstk)%Z eqn:Hsize';[|(* Failure *) iApply "Hφ";iIntros (Hcontr);inversion Hcontr].
    destruct (decide (is_Some (bound_check wstk)))%Z;[|(* Failure *) iApply "Hφ";iIntros (Hcontr);inversion Hcontr].
    iIntros "Hcont".
    iDestruct "Hcont" as (l0 b_r e_r a_r' b_r' Heq Hb_r') "(HPC & Hprestack & Hr_stk & Hr_t1 & Hr_t2)".
    (* We cleanup our definitions *)
    simplify_eq.
    assert (region_size b_r e_r > 11) as Hsize;[|clear Hperm i0 Hsize'].
    { apply Zlt_is_lt_bool in Hsize'. revert Hsize'. clear. rewrite /region_size /=. lia. }
    (* If the stack is Global, validity is false *)
    destruct l0;[by rewrite fixpoint_interp1_eq;iSimpl in "Hstack_val"|].
    rewrite fixpoint_interp1_eq;iSimpl in "Hstack_val".
    iAssert ([∗ list] a0 ∈ region_addrs b_r e_r, read_write_cond a0 RWLX (fixpoint interp1)
                                                 ∧ ⌜region_state_pwl W a0⌝)%I as "#Hstack_region".
    { iApply (big_sepL_mono with "Hstack_val").
      iIntros (k y Hk) "H". iDestruct "H" as (p0 Hperm) "Hw". destruct p0;inversion Hperm.
      iFrame. 
    }
    iAssert (⌜Forall (λ a, region_type_temporary W a) (region_addrs b_r e_r)⌝)%I as %Htemp.
    { iDestruct (big_sepL_and with "Hstack_region") as "[Hstack_rel Hstack_pwl]".
      iDestruct (big_sepL_forall with "Hstack_pwl") as %Hforall.
      iPureIntro. rewrite Forall_forall. intros x Hin. apply elem_of_list_lookup_1 in Hin as [k Hin].
      apply Hforall in Hin. auto. }
    (* We will now need to open the invariant for d. 
       We do not know which state d is in, and may need to 
       do a private transition from 1 to 0! For that reason 
       we will first revoke region, so that we can do private 
       updates to it. We do not care about the stack resources, 
       as it currently in the revoked state. 
     *)
    pose proof (extract_temps_split W (region_addrs b_r e_r)) as [l' [Hdup Hiff] ];
      [apply region_addrs_NoDup|apply Htemp|].
    iMod (monotone_revoke_keep_some W _ (region_addrs b_r e_r) with "[$Hsts $Hr]") as "[Hsts [Hr [Hrest Hstack] ] ]";[apply Hdup|..].
    { iSplit.
      - iApply big_sepL_forall. iPureIntro. intros n. simpl. intros x Hsome. apply Hiff. apply elem_of_app; left.
        apply elem_of_list_lookup. eauto. 
      - iApply (big_sepL_mono with "Hstack_region"). iIntros (k y Hk) "[Hrel _]". rewrite /read_write_cond.
        iFrame. iPureIntro.
        revert Htemp; rewrite Forall_forall =>Htemp. apply Htemp. apply elem_of_list_lookup. eauto. }
    iAssert ((▷ ∃ ws, [[b_r, e_r]]↦ₐ[RWLX][[ws]])
               ∗ ⌜Forall (λ a : Addr, region_type_revoked (revoke W) a) (region_addrs b_r e_r)⌝)%I
      with "[Hstack]" as "[>Hstack #Hrevoked]".
    { iDestruct (big_sepL_sep with "Hstack") as "[Hstack #Hrevoked]".
      iDestruct (big_sepL_forall with "Hrevoked") as %Hrevoked. iSplit;[|iPureIntro].
      - iDestruct (big_sepL_sep with "Hstack") as "[Hstack _]". iNext. 
        iDestruct (region_addrs_exists with "Hstack") as (ws) "Hstack".
        iDestruct (big_sepL2_sep with "Hstack") as "[_ Hstack]".
        iDestruct (big_sepL2_sep with "Hstack") as "[Hstack _]". iExists ws. iFrame.
      - revert Htemp; repeat (rewrite Forall_forall). 
        intros Htemp x Hx. apply revoke_lookup_Temp. by apply Htemp. 
    }
    iDestruct "Hrevoked" as %Hrevoked.
    (* For later use it will be useful to know that W contains i *)
    (* Now we may do any private transitions to our local invariants.
       since we don't know which case we are in, we can generalize and 
       say that there exists some private future world such that   
       the store succeeded, after which the state at i is false
     *)
    iDestruct (big_sepL2_length with "Hprog") as %Hrest0_length.
    destruct rest0;[inversion Hrest0_length|]. 
    iPrologue rest0 Hrest0_length "Hprog".
    apply contiguous_between_cons_inv_first in Hcont_rest0 as Heq. subst a0.
    assert (isCorrectPC_range pc_p pc_g pc_b pc_e link0 a_last) as Hvpc'.
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto.
      revert Hlink Hlink0 Hmid. clear. solve_addr. }
    assert (withinBounds (RWX, Global, d, d', d) = true) as Hwb.
    { isWithinBounds;[lia|]. revert Hd; clear. solve_addr. }
    iAssert (▷ (PC ↦ᵣ inr (pc_p, pc_g, pc_b, pc_e, a1)
              ∗ r_env ↦ᵣ inr (RWX, Global, d, d', d)
              ∗ link0 ↦ₐ[pc_p'] store_z r_env 0
              ∗ (∃ W',⌜(∃ b : bool, W.2.1 !! i = Some (encode b))
                        ∧ W.2.2 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv)⌝ ∧ 
                    ⌜W' = ((revoke_std_sta W.1),(<[i:=encode false]> W.2.1,W.2.2))⌝ ∧
                    ⌜related_sts_priv_world (revoke W) W'⌝ ∧
                    ⌜W'.2.1 !! i = Some (encode false)⌝ ∧
                    region W' ∗ sts_full_world W' ∗
                    ⌜Forall (λ a : Addr, region_type_revoked W' a) (region_addrs b_r e_r)⌝)
              -∗ WP Seq (Instr Executable) {{ v, φ v }})
        -∗ WP Instr Executable {{ v, WP fill [SeqCtx] (of_val v) {{ v, φ v }} }})%I
      with "[HPC Hinstr Hr_env Hr Hsts]" as "Hstore_step".
    { iIntros "Hcont". 
      (* store r_env 0 *)
      iInv ι as (x) "[>Hstate Hb]" "Hcls".
      destruct x; iDestruct "Hb" as ">Hb".
      - iApply (wp_store_success_z with "[$HPC $Hinstr $Hr_env $Hb]");
          [apply decode_encode_instrW_inv|apply Hfl|apply PermFlows_refl|iCorrectPC link0 a_last|iContiguous_next Hcont_rest0 0|auto|auto|..].
        iNext. iIntros "(HPC & Hinstr & Hr_env & Hd)".
        (* we assert that updating the local state d to 0 is a private transition *)
        iDestruct (sts_full_state_loc with "Hsts Hstate") as %Hlookup.
        iDestruct (sts_full_rel_loc with "Hsts Hrel") as %Hrel.        
        assert (related_sts_priv_world W (W.1, (<[i:=encode false]> W.2.1, W.2.2)))
          as Hrelated;[apply related_priv_local_1; auto|].
        (* first we can update region privately since it is revoked *)
        iAssert (sts_full_world (revoke W)
               ∗ region ((revoke W).1, (<[i:=encode false]> (revoke W).2.1, (revoke W).2.2)))%I with "[Hsts Hr]" as "[Hsts Hr]".
        { rewrite region_eq /region_def.
          iDestruct "Hr" as (M Mρ) "(HM & % & % & Hr)".
          iDestruct (monotone_revoke_list_region_def_mono_same $! Hrelated with "Hsts Hr") as "[Hsts Hr]".
          iFrame. iExists M, Mρ. iFrame. iPureIntro. auto.
        }
        (* we must update the local state of d to false *)
        iMod (sts_update_loc _ _ _ false with "Hsts Hstate") as "[Hsts Hstate]". 
        iMod ("Hcls" with "[Hstate Hd]") as "_". 
        { iNext. iExists false. iFrame. }
        iModIntro. iApply wp_pure_step_later;auto;iNext.
        iApply "Hcont". iFrame "HPC Hr_env Hinstr".
        iExists _.
        iFrame "Hsts Hr". iSimpl.
        iPureIntro.
        split;[eauto|].
        split; [auto|]. split;[apply revoke_monotone in Hrelated; auto|split;[apply lookup_insert|] ].
        eapply Forall_impl;[apply Hrevoked|].
        intros a2 Ha0_rev; auto.
      - iApply (wp_store_success_z with "[$HPC $Hinstr $Hr_env $Hb]");
          [apply decode_encode_instrW_inv|apply Hfl|apply PermFlows_refl|iCorrectPC link0 a_last|iContiguous_next Hcont_rest0 0|auto|auto|..].
        iNext. iIntros "(HPC & Hinstr & Hr_env & Hd)".
        (* use sts_state to assert that the current state of i is false *)
        iDestruct (sts_full_state_loc with "Hsts Hstate") as %Hlookup.
        iDestruct (sts_full_rel_loc with "Hsts Hrel") as %Hrel.   
        (* No need to update the world, since we did not change state *)
        iMod ("Hcls" with "[Hstate Hd]") as "_". 
        { iNext. iExists false. iFrame. }
        iModIntro. iApply wp_pure_step_later;auto;iNext.
        iApply "Hcont". iFrame "HPC Hr_env Hinstr".
        iExists _. iFrame. iPureIntro. rewrite /revoke /loc /= in Hlookup.
        apply insert_id in Hlookup as Heq. rewrite Heq. split;[eauto|]. split. 
        { destruct W as [ Wstd_sta [Wloc_sta Wloc_rel] ]. done. }
        split;[apply related_sts_priv_refl_world|split;auto].
    }
    iApply "Hstore_step". 
    iNext. iIntros "(HPC & Hr_env & Hprog_done & HW')".
    iDestruct "HW'" as (W' [Hawki Hawk] HeqW' Hrelated Hfalse) "(Hr & Hsts & #Hforall)".
    clear Hrevoked. iDestruct "Hforall" as %Hrevoked. 
    (* we prepare the stack for storing local state *)
    (* Splitting the stack into own and adv parts *)
    assert (contiguous (region_addrs b_r e_r)) as Hcont_stack;[apply region_addrs_contiguous|].
    assert (contiguous_between (region_addrs b_r e_r) b_r e_r) as Hcontiguous.
    { apply contiguous_between_of_region_addrs; auto. revert Hsize. rewrite /region_size. clear. solve_addr. }
    iDestruct "Hstack" as (ws) "Hstack". 
    iDestruct (big_sepL2_length with "Hstack") as %Hlength.
    assert (∃ ws_own ws_adv, ws = ws_own ++ ws_adv ∧ length ws_own = 11)
      as [ws_own [ws_adv [Happ Hlength'] ] ].
    { rewrite region_addrs_length in Hlength; auto. rewrite Hlength in Hsize. 
      do 11 (destruct ws as [|? ws]; [simpl in Hsize; lia|]).
           by exists [w;w0;w1;w2;w3;w4;w5;w6;w7;w8;w9],ws. }
    rewrite Happ.
    iDestruct (contiguous_between_program_split with "Hstack") as (stack_own stack_adv stack_own_last) "(Hstack_own & Hstack_adv & #Hcont)"; [eauto|].
    iDestruct "Hcont" as %(Hcont1 & Hcont2 & Hstack_eq1 & Hlink1).
    iDestruct (big_sepL2_length with "Hstack_own") as %Hlength_own. rewrite Hlength' in Hlength_own.
    rewrite Hstack_eq1 in Hcontiguous.
    (* The following length assumptions will let us destruct the stack/program *)
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_f2.
    iDestruct (big_sepL2_length with "Hstack_adv") as %Hlength_adv.
    (* Getting the three top adress on the stack *)
    do 3 (destruct stack_own; [inversion Hlength_own|]; destruct ws_own;[inversion Hlength'|]).
    assert ((region_addrs b_r e_r) !! 0 = Some b_r) as Hfirst_stack.
    { apply region_addrs_first. revert Hsize; clear. rewrite /region_size. solve_addr. }
    rewrite Hstack_eq1 /= in Hfirst_stack. inversion Hfirst_stack as [Heq]. subst b_r.
    (* assert that the stack bounds are within bounds *)
    assert (withinBounds (RWLX,Local,a0,e_r,a0) = true ∧ withinBounds (RWLX,Local,a0,e_r,stack_own_last) = true) as [Hwb1 Hwb2].
    { split; isWithinBounds; first lia.
      - revert Hlength. rewrite Happ app_length Hlength' region_addrs_length /region_size. clear. solve_addr.
      - by eapply contiguous_between_bounds.
      - apply contiguous_between_bounds in Hcont2. simplify_eq.
        revert Hlength' Hlength Hlink1 Hsize Hlength_adv Hlength_own Hcont2. rewrite -region_addrs_length app_length. clear.
        rewrite region_addrs_length /region_size. solve_addr.
    }   
    (* push r_stk r_env *)
    iDestruct "Hstack_own" as "[Ha Hstack_own]".
    do 2 (destruct rest0;[inversion Hrest0_length|]).
    iDestruct (big_sepL2_app_inv _ [a1;a4] (a5::rest0) with "Hprog") as "[Hpush Hprog]";[simpl;auto|].
    iApply (push_r_spec);[..|iFrame "HPC Hr_stk Hpush Hr_env Ha"];
      [|apply Hfl|auto|iContiguous_next Hcont_rest0 1|iContiguous_next Hcont_rest0 2|auto|..].
    { split;iCorrectPC link0 a_last. }
    iNext. iIntros "(HPC & Hpush & Hr_stk & Hr_env & Hb_r)". iCombine "Hpush" "Hprog_done" as "Hprog_done".
    (* push r_stk r_self *)
    do 2 (destruct rest0;[inversion Hrest0_length|]).
    iDestruct (big_sepL2_app_inv _ [a5;a6] (a7::rest0) with "Hprog") as "[Hpush Hprog]";[simpl;auto|]. 
    iDestruct "Hstack_own" as "[Ha2 Hstack_own]".
    iApply (push_r_spec);[..|iFrame "HPC Hr_stk Hpush Hr_t0 Ha2"];
      [|apply Hfl| |iContiguous_next Hcont_rest0 3|
       iContiguous_next Hcont_rest0 4|iContiguous_next Hcont1 0|..].
    { split;iCorrectPC link0 a_last. }
    { iContiguous_bounds_withinBounds a0 stack_own_last. }
    iNext. iIntros "(HPC & Hpush & Hr_stk & Hr_self & Ha2)". iCombine "Hpush" "Hprog_done" as "Hprog_done".
    (* push r_stk r_adv *)
    do 2 (destruct rest0;[inversion Hrest0_length|]).
    iDestruct (big_sepL2_app_inv _ [a7;a8] (a9::rest0) with "Hprog") as "[Hpush Hprog]";[simpl;auto|].
    iDestruct "Hstack_own" as "[Ha3 Hstack_own]".
    iApply (push_r_spec);[..|iFrame "HPC Hr_stk Hpush Hr_adv Ha3"];
      [|apply Hfl|iContiguous_bounds_withinBounds a0 stack_own_last|iContiguous_next Hcont_rest0 5|
       iContiguous_next Hcont_rest0 6|iContiguous_next Hcont1 1|..].
    { split;iCorrectPC link0 a_last. }
    iNext. iIntros "(HPC & Hpush & Hr_stk & Hr_adv & Ha3)". iCombine "Hpush" "Hprog_done" as "Hprog_done".
    (* prepare for scall *)
    (* Prepare the scall prologue macro *)
    destruct stack_own as [|stack_own_b stack_own];[inversion Hlength_own|].
    assert ((stack_own_b :: stack_own) = region_addrs stack_own_b stack_own_last) as ->.
    { apply region_addrs_of_contiguous_between; auto.
      repeat (inversion Hcont1 as [|????? Hcont1']; subst; auto; clear Hcont1; rename Hcont1' into Hcont1). }      
    assert (stack_adv = region_addrs stack_own_last e_r) as ->.
    { apply region_addrs_of_contiguous_between; auto. }
    assert (contiguous_between (a9 :: rest0) a9 a_last) as Hcont_weak.
    { repeat (inversion Hcont_rest0 as [|????? Hcont_rest0']; subst; auto; clear Hcont_rest0; rename Hcont_rest0' into Hcont_rest0). }
    iDestruct (contiguous_between_program_split with "Hprog") as (scall_prologue rest1 s_last)
                                                                   "(Hscall & Hf2 & #Hcont)"; [eauto|..].
    clear Hfirst_stack Hcont_weak.
    iDestruct "Hcont" as %(Hcont_scall & Hcont_rest1 & Hrest_app & Hlink').
    iDestruct (big_sepL2_length with "Hscall") as %Hscall_length. simpl in Hscall_length, Hlength_f2.
    assert ((stack_own_b + 8)%a = Some stack_own_last) as Hstack_own_bound.
    { rewrite -(addr_add_assoc a0 _ 3). assert ((3 + 8) = 11)%Z as ->;[done|].
      rewrite Hlength_own in Hlink1. revert Hlink1; clear; solve_addr.
      apply contiguous_between_incr_addr with (i:=3) (ai:=stack_own_b) in Hcont1; auto. }
    assert (∃ a, (stack_own_b + 7)%a = Some a) as [stack_own_end Hstack_own_bound'].
    { revert Hstack_own_bound. clear. intros H. destruct (stack_own_b + 7)%a eqn:Hnone; eauto. solve_addr. }
    assert (a9 < s_last)%a as Hcontlt.
    { revert Hscall_length Hlink'. clear. solve_addr. }
    assert (link0 <= a9)%a as Hcontge.
    { apply region_addrs_of_contiguous_between in Hcont_scall. simplify_eq. revert Hscall_length Hcont_rest0 Hcontlt. clear =>Hscall_length Hf2 Hcontlt.
      apply contiguous_between_middle_bounds with (i := 7) (ai := a9) in Hf2;[solve_addr|auto]. 
    }
    (* scall *)
    iDestruct (big_sepM_insert _ _ r_t1 with "[$Hgen_reg $Hr_t1]") as "Hgen_reg".
    { rewrite lookup_delete_ne;auto. apply lookup_delete. }
    iDestruct (big_sepM_insert _ _ r_t2 with "[$Hgen_reg $Hr_t2]") as "Hgen_reg".
    { rewrite lookup_insert_ne;auto. apply lookup_delete. }
    iDestruct (big_sepM_insert _ _ r_env with "[$Hgen_reg $Hr_env]") as "Hgen_reg".
    { repeat (try rewrite lookup_insert_ne;auto; try rewrite lookup_delete_ne;auto). 
      enough (r_env ∉ dom (gset RegName) rmap) as HH by rewrite not_elem_of_dom // in HH.
      rewrite Hrmap_dom. rewrite not_elem_of_difference; right. set_solver. }
    iDestruct (big_sepM_insert _ _ r_t0 with "[$Hgen_reg $Hr_self]") as "Hgen_reg".
    { repeat (try rewrite lookup_insert_ne;auto; try rewrite lookup_delete_ne;auto). 
      enough (r_t0 ∉ dom (gset RegName) rmap) as HH by rewrite not_elem_of_dom // in HH.
      rewrite Hrmap_dom. rewrite not_elem_of_difference; right. set_solver. }
    iApply (scall_prologue_spec with "[- $HPC $Hr_stk $Hscall $Hstack_own $Hstack_adv $Hgen_reg]");
      [ | | apply Hwb2|apply Hcont_scall|apply Hfl|iNotElemOfList| |
        iContiguous_next Hcont1 2|apply Hstack_own_bound'|apply Hstack_own_bound| |done|..].
    { assert (s_last <= a_last)%a as Hle;[by apply contiguous_between_bounds in Hcont_rest1|].
      intros mid Hmid. apply isCorrectPC_inrange with link0 a_last; auto.
      revert Hle Hcontlt Hcontge Hmid. clear. intros. split; solve_addr. }
    { simplify_eq. iContiguous_bounds_withinBounds a0 stack_own_last. }
    { rewrite !dom_insert_L !dom_delete_L !Hrmap_dom !singleton_union_difference_L
              !difference_diag_L !all_registers_union_l !difference_difference_L.
      f_equal. clear. set_solver. }
    { assert (12 + awkward_epilogue_off = 77)%Z as ->;[done|]. rewrite Hscall_length in Hlink'. done. }
    iNext. iIntros "(HPC & Hr_stk & Hr_t0 & Hr_gen & Hstack_own & Hstack_adv & Hscall)".
    iDestruct (big_sepL2_length with "Hf2") as %Hf2_length. simpl in Hf2_length.
    assert (isCorrectPC_range pc_p pc_g pc_b pc_e s_last a_last) as Hvpc1.
    { intros mid Hmid. assert (link0 <= s_last)%a as Hle;[apply contiguous_between_bounds in Hcont_scall; revert Hcont_scall Hcontge;clear; solve_addr|].
      apply isCorrectPC_inrange with link0 a_last; auto.
      revert Hmid Hle. clear. solve_addr. }
    
    (* We now want to reason about unknown code. For this we invoke validity of wadv *)
    (* Before we can show the validity of the continuation, we need to set up the invariants 
       for local state, as well as the invariant for the stack *)

    (* We set the local stack frame and all the leftover Temporary resources to static *)

    (* first, put together again the resources for the frame *)
    iDestruct (region_mapsto_cons with "[Ha3 Hstack_own]") as "Hstack_own";[iContiguous_next Hcont1 2| |iFrame|].
    { apply contiguous_between_middle_bounds with (i:=3) (ai:=stack_own_b) in Hcont1;auto.
      revert Hcont1;clear. solve_addr. }
    iDestruct (region_mapsto_cons with "[Ha2 Hstack_own]") as "Hstack_own";[iContiguous_next Hcont1 1| |iFrame|].
    { apply contiguous_between_middle_bounds with (i:=2) (ai:=a3) in Hcont1;auto.
      revert Hcont1;clear. solve_addr. }
    iDestruct (region_mapsto_cons with "[Hb_r Hstack_own]") as "Hstack_own";[iContiguous_next Hcont1 0| |iFrame|].
    { apply contiguous_between_middle_bounds with (i:=1) (ai:=a2) in Hcont1;auto.
      revert Hcont1;clear. solve_addr. }
    
    (* Next we want to define the map which will keep track of each word and permission *)
    iDestruct (temp_resources_split with "Hrest") as (pws) "[#Hrest_valid [#Hrev Hrest]]".
    iDestruct "Hrev" as %Hrev.
    match goal with |- context [ [[a0,stack_own_last]]↦ₐ[RWLX][[ ?instrs ]]%I ] =>
                    set l_frame := instrs
    end.
    set m_static1 := lists_to_static_region (region_addrs a0 stack_own_last ++ l')
                                                  (l_frame ++ pws).

    (* we'll need that later to reason on the fact that the [zip] in the definition of
       l_frame indeed fully uses both lists *)
    iDestruct (big_sepL2_length with "Hstack_own") as %Hlength_stack_own1.

    (* Allocate the static region containing the local stack frame and leftovers *)
    assert (NoDup (region_addrs a0 stack_own_last ++ l')) as Hdup1.
    { rewrite Permutation_app_comm.
      rewrite Hstack_eq1 in Hdup. apply region_addrs_of_contiguous_between in Hcont1.
      rewrite Hcont1 app_assoc in Hdup. by apply NoDup_app in Hdup as [Hdup _]. }
    iDestruct (region_revoked_to_static (W.1, (<[i:=encode false]> W.2.1, W.2.2)) m_static1
                 with "[Hsts Hr Hstack_own Hrest]") as ">[Hsts Hr]".
    { rewrite HeqW' /revoke. iFrame. rewrite /region_mapsto. 
      iApply (big_sepL2_to_static_region _ _ (λ a w, ∃ p φ, a ↦ₐ[p] w ∗ rel a p φ)%I with "[] [Hstack_own Hrest]").
      - auto. 
      - iModIntro.
        iIntros (k y wy Hin1 Hin2) "Hy /=".
        iDestruct "Hy" as (p' φ') "[Hy #Hrely]". 
        destruct (decide (k < length (l_frame))). 
        + rewrite lookup_app_l in Hin1;[|rewrite Hlength_stack_own1;auto].
          rewrite lookup_app_l in Hin2;[|auto].
          iExists RWLX,(λ Wv, interp Wv.1 Wv.2). iFrame. 
          iSplit;[iPureIntro;apply _|]. iSplit;auto. 
          rewrite Hstack_eq1. 
          iDestruct (big_sepL_app with "Hstack_region") as "[Hframe _]".
          apply region_addrs_of_contiguous_between in Hcont1. rewrite Hcont1.
          iDestruct (big_sepL_and with "Hframe") as "[Htest _]". rewrite /read_write_cond. 
          iDestruct (big_sepL_lookup with "Htest") as "Htest'";[apply Hin1|auto].
          iDestruct (rel_agree y p' RWLX with "[$Hrely $Htest']") as "[% _]". subst p'.
          iFrame "Hy Htest'". 
        + assert (length l_frame <= k);[revert n;clear;lia|]. 
          rewrite lookup_app_r in Hin1;[|rewrite Hlength_stack_own1;auto].
          rewrite lookup_app_r in Hin2;[|auto].
          rewrite Hlength_stack_own1 in Hin1. simpl in Hin1,Hin2.
          iDestruct (big_sepL2_lookup with "Hrest_valid") as "Hyv";[apply Hin1|apply Hin2|].
          iDestruct "Hyv" as (p0 φ0) "(Hpers & Hne & Hφ & Hrely' & Hmono)".
          iDestruct (rel_agree y p' p0 with "[$Hrely $Hrely']") as "[% Heq]". subst p0.
          iExists _,_. iFrame "Hrely' Hy". auto. 
      - iFrame. rewrite Hstack_eq1. iDestruct (big_sepL_app with "Hstack_region") as "[Hframe _]".
        apply region_addrs_of_contiguous_between in Hcont1. rewrite Hcont1.
        iDestruct (big_sepL2_sep with "[Hframe $Hstack_own]") as "Hstack_own".
        { iApply big_sepL2_to_big_sepL_l;auto. }
        iApply (big_sepL2_mono with "Hstack_own").
        iIntros (k y1 w2 Hin1 Hin2) "[Hy [Hrel _] ]".
        iExists RWLX,(λ Wv, interp Wv.1 Wv.2). iFrame. 
    }
        
    (* Next we close the adversary stack region so that it is Temporary *)
    iDestruct (big_sepL2_length with "Hrest_valid") as %Hlength_rest. 
    iMod (monotone_close _ (region_addrs stack_own_last e_r) RWLX (λ Wv, interp Wv.1 Wv.2)
            with "[$Hsts $Hr Hstack_adv]") as "[Hsts Hr]".
    { rewrite Hstack_eq1. iDestruct (big_sepL_app with "Hstack_region") as "[_ Hstack_val']".
      iApply big_sepL_sep. iSplitL.
      - iDestruct (region_addrs_zeroes_trans with "Hstack_adv") as "Hstack_adv".
        iApply (big_sepL_mono with "Hstack_adv"). iIntros (k y Hsome) "Hy".
        iExists (inl 0%Z). iSplitR;auto. iFrame. simpl. iSplit.
        + iModIntro. iIntros (W1 W2 Hrelated12) "HW1 /=". by repeat (rewrite fixpoint_interp1_eq /=).
        + by repeat (rewrite fixpoint_interp1_eq /=).
      - iDestruct (big_sepL_and with "Hstack_region") as "[Hstack_rel Hstack_pwl]".
        rewrite /read_write_cond.
         iDestruct (big_sepL_app with "Hstack_rel") as "[_ Hstack_rel']".
         iApply big_sepL_sep; iFrame "#". iApply big_sepL_forall. iPureIntro.
        rewrite Hstack_eq1 in Hrevoked. apply Forall_app in Hrevoked as [_ Hrevoked]. 
        intros k x Hsome.
        assert (x ∉ (region_addrs a0 stack_own_last) ++ l') as Hnin.
        { apply elem_of_list_lookup_2 in Hsome.
          apply region_addrs_of_contiguous_between in Hcont1. 
          rewrite Hstack_eq1 Hcont1 app_assoc in Hdup.
          revert Hdup. rewrite Permutation_app_comm =>Hdup. apply NoDup_app in Hdup as [_ [Hnin _] ].
          apply Hnin in Hsome. rewrite Permutation_app_comm. auto. 
        }
        rewrite std_sta_update_multiple_lookup_same_i /std /=.
        apply Forall_lookup_1 with (i0:=k) (x0:=x) in Hrevoked as Hrevoked;auto.
        rewrite HeqW' in Hrevoked. auto.
        rewrite lists_to_static_region_dom.
        rewrite stdpp_extra.elements_list_to_set;auto. repeat rewrite app_length. auto. 
    }
    
    (* Resulting world *)
    evar (W'' : prod (STS_std_states Addr region_type) (prod STS_states STS_rels)).
    instantiate (W'' :=
       (close_list (region_addrs stack_own_last e_r)
               (std_update_multiple (revoke (W.1, (<[i:=encode false]> W.2.1, W.2.2)))
                  (elements (dom (gset Addr) m_static1)) (Static m_static1)))). 
    assert (related_sts_priv_world W' W'') as HW'W''.
    { rewrite HeqW'. eapply related_sts_priv_pub_trans_world;[|apply close_list_related_sts_pub;auto].
      apply related_sts_priv_world_static; auto. 
      apply Forall_forall.
      rewrite /m_static1 lists_to_static_region_dom; [|repeat rewrite app_length;rewrite Hlength_rest;auto].
      intros x Hin. revert Hin. rewrite stdpp_extra.elements_list_to_set; auto. intros Hin.
      apply elem_of_app in Hin as [Hin | Hin].
      - revert Hrevoked. rewrite HeqW' Forall_forall =>Hrevoked. apply Hrevoked.
        apply region_addrs_of_contiguous_between in Hcont1. rewrite Hstack_eq1 Hcont1. apply elem_of_app; by left.
      - revert Hrev. rewrite Forall_forall =>Hrev. apply Hrev. auto.       
    }
    assert (related_sts_priv_world W W'') as HWW''.
    { eapply related_sts_priv_trans_world;[apply revoke_related_sts_priv;auto|].
      eapply related_sts_priv_trans_world;[apply Hrelated|].
      auto. 
    }

    (* We choose the r *)
    set r : gmap RegName Word :=
      <[PC     := inl 0%Z]>
      (<[r_stk := inr (RWLX, Local, stack_own_last, e_r, stack_own_end)]>
      (<[r_t0  := inr (E, Local, a0, e_r, stack_own_b)]>
      (<[r_adv := inr (p, Global, b, e, a')]>
       (create_gmap_default (list_difference all_registers [PC;r_stk;r_t0;r_adv]) (inl 0%Z))))).

    (* Now that the world has been set up, we want to apply the jmp or fail patter of wadv *)
    iDestruct (jmp_or_fail_spec _ _ φ with "Hadv_val") as "Hadv_cont". 
    
    (* jmp r_adv *)
    iDestruct (big_sepL2_length with "Hf2") as %Hrest_length; simpl in Hrest_length. 
    destruct rest0;[inversion Hrest0_length|]. 
    iPrologue rest1 Hrest_length "Hf2".
    apply contiguous_between_cons_inv_first in Hcont_rest1 as Heq. subst a11. 
    iApply (wp_jmp_success with "[$Hinstr $Hr_adv $HPC]");
      [apply decode_encode_instrW_inv|apply Hfl|iCorrectPC s_last a_last|..].
    (* before applying the eplogue, we want to distinguish between a correct or incorrect resulting PC *)
    destruct (decide (isCorrectPC (updatePcPerm (inr (p, Global, b, e, a')))));
      [rewrite decide_True;auto|rewrite decide_False;auto]. 
    2: { iEpilogue "(HPC & _ & _)". iApply ("Hadv_cont" with "[Hφ $HPC]").
         iApply "Hφ". iIntros (Hcontr). done. }
    iDestruct "Hadv_cont" as (p0 g b0 e0 a11 Heq) "Hadv_cont". symmetry in Heq. simplify_eq.
    iDestruct ("Hadv_cont" $! r _ HWW'') as "Hadv_contW''". 
    iEpilogue "(HPC & Hinstr & Hr_adv)". iSimpl in "HPC".
    
    (* We close the invariant for the program *)
    iMod ("Hcls" with "[Hprog_done Hinstr Hprog $Hna Hscall Hreqglob Hprestack]") as "Hna". 
    { iNext. iDestruct "Hprog_done" as "(Hpush3 & Hpush2 & Hpush1 & Ha_first)".
      rewrite Heqapp. 
      iApply (big_sepL2_app with "Hreqglob [-]").
      iApply (big_sepL2_app with "Hprestack [-]").
      iFrame "Ha_first". rewrite Hrest_app. 
      iApply (big_sepL2_app with "Hpush1 [-]"). 
      iApply (big_sepL2_app with "Hpush2 [-]").
      iApply (big_sepL2_app with "Hpush3 [-]").
      iApply (big_sepL2_app with "Hscall [-]").
      iFrame.
    }
    
    (* We have all the resources of r *)
    iAssert (registers_mapsto (<[PC:= (match p with
                | E => inr (RX, Global, b, e, a')
                | _ => inr (p, Global, b, e, a')
                end)]> r))
      with "[Hr_gen Hr_stk Hr_t0 Hr_adv HPC]" as "Hmaps".
    { iApply (registers_mapsto_resources with "Hr_gen Hr_stk Hr_t0 Hr_adv HPC"). 
      rewrite !dom_delete_L !dom_insert_L !dom_delete_L Hrmap_dom.
      rewrite !singleton_union_difference_L !all_registers_union_l !difference_difference_L.
      f_equal. clear. set_solver. }
    (* r contrains all registers *)
    iAssert (full_map r) as "#full";[iApply r_full|].
    iSimpl in "Hadv_val".
    (* We are now ready to show that all registers point to a valid word *)
    iAssert (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → (fixpoint interp1) W'' (r !r! r1))%I
      with "[-Hsts Hr Hmaps Hna Hφ]" as "Hreg".
    { iIntros (r1).
      assert (r1 = PC ∨ r1 = r_stk ∨ r1 = r_t0 ∨ r1 = r_adv ∨ (r1 ≠ PC ∧ r1 ≠ r_stk ∧ r1 ≠ r_t0 ∧ r1 ≠ r_adv)) as
          [-> | [-> | [-> | [Hr_t30 | [Hnpc [Hnr_stk [Hnr_t0 Hnr_t30] ] ] ] ] ] ].
      { destruct (decide (r1 = PC)); [by left|right].
        destruct (decide (r1 = r_stk)); [by left|right].
        destruct (decide (r1 = r_t0)); [by left|right].
        destruct (decide (r1 = r_adv)); [by left|right;auto].  
      }
      - iIntros "%". contradiction.
      - assert (r !! r_stk = Some (inr (RWLX, Local, stack_own_last, e_r, stack_own_end))) as Hr_stk; auto. 
        rewrite /RegLocate Hr_stk !fixpoint_interp1_eq. 
        iIntros (_). 
        iAssert ([∗ list] a ∈ region_addrs stack_own_last e_r, ∃ p0 : Perm,
                                                    ⌜PermFlows RWLX p0⌝
                                                    ∗ read_write_cond a p0 (fixpoint interp1)
                             ∧ ⌜region_state_pwl W'' a⌝)%I as "#Hstack_adv_val". 
        { rewrite Hstack_eq1. 
          iDestruct (big_sepL_app with "Hstack_region") as "[_ Hstack_val']".
          iApply (big_sepL_mono with "Hstack_val'").
          iIntros (k y Hsome) "[Hy _]".
          rewrite Hstack_eq1 in Hrevoked.
          apply Forall_app in Hrevoked as [_ Hrevoked].
          iExists RWLX. iFrame. iSplit;[auto|]. iPureIntro. 
          apply close_list_std_sta_revoked.
          +  apply elem_of_list_lookup; eauto.
          + revert Hrevoked. rewrite Forall_forall =>Hrevoked.
            assert (y ∉ (region_addrs a0 stack_own_last) ++ l') as Hnin.
            { apply elem_of_list_lookup_2 in Hsome.
              apply region_addrs_of_contiguous_between in Hcont1. 
              rewrite Hstack_eq1 Hcont1 app_assoc in Hdup.
                revert Hdup. rewrite Permutation_app_comm =>Hdup. apply NoDup_app in Hdup as [_ [Hnin _] ].
                apply Hnin in Hsome. rewrite Permutation_app_comm. auto. 
            }
            rewrite std_sta_update_multiple_lookup_same_i /std /=. 
            apply Hrevoked. apply elem_of_list_lookup. eauto.
            rewrite lists_to_static_region_dom.
            rewrite stdpp_extra.elements_list_to_set;auto. repeat rewrite app_length. auto. 
        }
        iFrame "Hstack_adv_val".
      - (* continuation *)
        iIntros (_).
        assert (r !! r_t0 = Some (inr (E, Local, a0, e_r, stack_own_b))) as Hr_t0; auto. 
        rewrite /RegLocate Hr_t0 !fixpoint_interp1_eq. iSimpl. 
        (* prove continuation *)
        iModIntro.
        iIntros (r' W3 Hrelated3).
        iNext.

        (* We start by asserting that the adversary stack is still temporary *)
        iAssert ([∗ list] a ∈ (region_addrs stack_own_last e_r),
                 ⌜W3.1 !! a = Some Temporary⌝
                    ∗ rel a RWLX (λ Wv : WORLD * Word, ((fixpoint interp1) Wv.1) Wv.2)
                )%I as "#Hstack_adv_tmp".
        { rewrite Hstack_eq1.
          iDestruct (big_sepL_app with "Hstack_region") as "[_ Hstack_adv]".
          iApply (big_sepL_mono with "Hstack_adv"). iIntros (k y Hsome) "[Hr _]".
          rewrite /read_write_cond. iFrame. iPureIntro.
          assert (region_state_pwl W3 y) as Hlookup;[|auto].
          revert Hrevoked; rewrite Forall_forall =>Hrevoked.
          apply region_state_pwl_monotone with W''; eauto.
          rewrite /W'' /region_state_pwl /std /=.
          apply close_list_std_sta_revoked; [apply elem_of_list_lookup; eauto|].
          assert (y ∉ (region_addrs a0 stack_own_last) ++ l') as Hnin.
          { apply elem_of_list_lookup_2 in Hsome.
            apply region_addrs_of_contiguous_between in Hcont1. 
            rewrite Hstack_eq1 Hcont1 app_assoc in Hdup.
            revert Hdup. rewrite Permutation_app_comm =>Hdup. apply NoDup_app in Hdup as [_ [Hnin _] ].
            apply Hnin in Hsome. rewrite Permutation_app_comm. auto. 
          }
          rewrite std_sta_update_multiple_lookup_same_i /std /=. 
          apply Hrevoked. rewrite Hstack_eq1. apply elem_of_app; right. apply elem_of_list_lookup. eauto.
          rewrite lists_to_static_region_dom.
          rewrite stdpp_extra.elements_list_to_set;auto. repeat rewrite app_length. auto. 
        }
        iDestruct (big_sepL_sep with "Hstack_adv_tmp") as "[Htemp _]". 
        iDestruct (big_sepL_forall with "Htemp") as %HtempW3. iClear "Htemp". 
        
        (* we want to distinguish between the case where the local stack frame is Static (step through 
           continuation) and where the local stack frame is temporary (apply FTLR) *)
        assert (forall a, a ∈ region_addrs a0 stack_own_last ++ l' ->
                  (std W3) !! a = Some Temporary ∨
                  (std W3) !! a = Some (Static m_static1))
          as Hcases.
        { intros a'' Hin. apply or_comm,related_sts_pub_world_static with W'';auto.
          assert (std (std_update_multiple (revoke (W.1, (<[i:=encode false]> W.2.1, W.2.2)))
                                           (elements (dom (gset Addr) m_static1)) (Static m_static1)) !! a'' =
                  Some (Static m_static1)) as Hlookup.
          { apply std_sta_update_multiple_lookup_in_i.
            rewrite lists_to_static_region_dom;[|repeat rewrite app_length;rewrite Hlength_rest;auto].
            rewrite stdpp_extra.elements_list_to_set;auto. }
          rewrite -close_list_std_sta_same_alt;auto. rewrite Hlookup. intros Hcontr;inversion Hcontr as [heq].
        }
        assert (a0 ∈ region_addrs a0 stack_own_last ++ l') as Ha2in.
        { apply elem_of_app. left. apply elem_of_list_lookup. exists 0.
          apply region_addrs_of_contiguous_between in Hcont1 as <-. auto. }
        apply Hcases in Ha2in as [Hm_temp | Hm_static].
        { iSimpl. 
          iIntros "(#[Hfull3 Hreg3] & Hmreg' & Hr & Hsts & Hna)". 
          iSplit; [auto|rewrite /interp_conf].
          (* first we want to assert that if a2 is Temporary, the remaining addresses are also temporary *)
          iAssert (⌜∀ a : Addr, a ∈ dom (gset Addr) m_static1 → temporary W3 a⌝)%I as %Hm_frame_temp_all.
          { (* use fact that if the address is in a public future state, it is either Static or Temp. 
               If it is temp we are done. If it is static then we can use the full_sts_static_all lemma 
               to assert that a2 is also in state Static, which leads to a contradiction, as we are in the 
               case where it should be Temporary *)
            iIntros (a''). rewrite /m_static1. 
            rewrite lists_to_static_region_dom;[|repeat rewrite app_length;rewrite Hlength_rest;auto].
            iIntros (Hin). apply elem_of_list_to_set in Hin. 
            pose proof (Hcases a'' Hin) as [Htemp' | Hstatic].
            - rewrite /temporary. rewrite Htemp'. auto.
            - iDestruct (full_sts_static_all with "Hsts Hr") as %Hforall;[eauto|]. exfalso.
              assert (a0 ∈ dom (gset Addr) m_static1) as Hin'.
              { rewrite lists_to_static_region_dom;[|repeat rewrite app_length;rewrite Hlength_rest;auto].
                apply elem_of_list_to_set. apply elem_of_app. left. apply elem_of_list_lookup. exists 0.
                apply region_addrs_of_contiguous_between in Hcont1 as <-. auto. }
              apply Hforall in Hin'. rewrite /static Hm_temp in Hin'. done. 
          }
          iDestruct (fundamental W3 r' RX Local a0 e_r stack_own_b with "[] [] [-]") as "[_ Hcont]";[by iLeft| |iFrame "∗ #"|..].
          { iSimpl.
            iApply (big_sepL_mono with "Hstack_region").
            iIntros (k y Hk) "[Hrel _]". iExists RWLX. iSplit;[auto|]. iFrame. iPureIntro.            
            left.
            (* we assert that the region is all in state temporary *)
            rewrite (region_addrs_split _ stack_own_last) in Hk. 
            assert (y ∈ region_addrs a0 stack_own_last ++ region_addrs stack_own_last e_r) as Hk'.
            { apply elem_of_list_lookup. eauto. }
            apply elem_of_app in Hk' as [Hframe | Hadv].
            + assert (y ∈ dom (gset Addr) m_static1) as Hk'.
              { rewrite lists_to_static_region_dom;[|repeat rewrite app_length;rewrite Hlength_rest;auto].
                apply elem_of_list_to_set. apply elem_of_app. by left. }
              apply Hm_frame_temp_all in Hk'. rewrite /temporary in Hk'.
              destruct (W3.1 !! y) eqn:Hsome;[subst;auto|inversion Hk'].
            + apply elem_of_list_lookup in Hadv as [j Hj]. by apply HtempW3 with j. 
            + split. 
              * rewrite /le_addr. trans stack_own_b;[|revert Hstack_own_bound;clear;solve_addr].
                apply contiguous_between_middle_bounds with (i:=3) (ai:=stack_own_b) in Hcont1 as [Hle _];auto.
              * apply contiguous_between_bounds in Hcont2. auto. 
          }
          iFrame. 
        }
        
        (* Now we are in the case where m_static1 is still static. We will have to open the region and step through
           the continuation as usual. *)
        iSimpl. 
        iIntros "(#[Hfull' Hreg'] & Hmreg' & Hr & Hsts & Hna)". 
        iSplit; [auto|rewrite /interp_conf].
        (* since a2 is static, all of dom(m_static1) is static *)
        iDestruct (full_sts_static_all with "Hsts Hr") as %Hall_static;eauto. 
        (* get the PC, currently pointing to the activation record *)
        iDestruct (big_sepM_delete _ _ PC with "Hmreg'") as "[HPC Hmreg']";[rewrite lookup_insert; eauto|].
        (* get some registers *)
        iGet_genpur_reg_map r' r_t1 "Hmreg'" "Hfull'" "[Hr_t1 Hmreg']".
        iGet_genpur_reg_map r' r_stk "Hmreg'" "Hfull'" "[Hr_stk Hmreg']".
        iGet_genpur_reg_map r' r_adv "Hmreg'" "Hfull'" "[Hr_adv Hmreg']".
        iGet_genpur_reg_map r' r_t0 "Hmreg'" "Hfull'" "[Hr_t0 Hmreg']".
        iGet_genpur_reg_map r' r_env "Hmreg'" "Hfull'" "[Hr_env Hmreg']".

        (* We will need to step through the activation record. We will therefore have to revoke m_static1. 
           Since this is a private transition, we must first revoke W3. *)

        iDestruct (region_has_static_addr_Forall with "[$Hr $Hsts]") as %HForall_static1; eauto.
        iAssert (⌜Forall (λ a, W3.1 !! a = Some Temporary)
                  (region_addrs stack_own_last e_r)⌝)%I as %Hstack_adv_tmp.
        { iApply region_state_pwl_forall_temp. iApply (big_sepL_mono with "Hstack_adv_tmp").
          iIntros (k y Hk) "[Htemp Hrel]". iFrame. iExact "Hrel". } 
        pose proof (extract_temps_split W3 (region_addrs stack_own_last e_r)) as [l'' [Hdup' Hiff'] ].
        { apply region_addrs_NoDup. }
        { apply Hstack_adv_tmp. }
        
        (* we revoke W3, and keep a list of leftovers l'' *)
        iMod (monotone_revoke_keep_some _ l'' (region_addrs stack_own_last e_r)
                with "[Hstack_adv_tmp $Hr $Hsts]") as "(Hsts & Hr & Hrest' & Hstack_adv)".
        assumption. iSplit.
        { iApply big_sepL_forall. iPureIntro. intros n. simpl. intros x Hsome. apply Hiff'. apply elem_of_app; left.
          apply elem_of_list_lookup. eauto. }
          by iApply "Hstack_adv_tmp".

        iDestruct (region_static_to_revoked with "[$Hr $Hsts]") as ">(Hsts & Hr & Hm_static1_resources & _)". eauto.

        (* finally we split up the static resources into the local stack frame and l' *)
        iAssert ([[a0,stack_own_last]] ↦ₐ[RWLX] [[l_frame]]
                ∗ [∗ list] a;w ∈ l';pws, ∃ p φ, rel a p φ ∗ a ↦ₐ[p] w)%I with "[Hm_static1_resources]" as "[Hframe Hl']".
        { rewrite /m_static1 /region_mapsto /static_resources.
          iAssert (([∗ list] y1;y2 ∈ region_addrs a0 stack_own_last;l_frame, y1 ↦ₐ[RWLX] y2)
                     ∗ ([∗ list] a11;w ∈ l';pws, ∃ p φ, rel a11 p φ ∗ a11 ↦ₐ[p] w))%I with "[-]" as "[H $]".
          { iDestruct (static_region_to_big_sepL2 _ _ (λ a w, ∃ p φ, rel a p φ ∗ a ↦ₐ[p] w)
                         with "[] Hm_static1_resources")%I as "Hm_static1_resources";
              [auto|repeat rewrite app_length;auto|auto|].
            iDestruct (big_sepL2_app' with "Hm_static1_resources") as "[Hframe $]";auto. 
            rewrite Hstack_eq1. apply region_addrs_of_contiguous_between in Hcont1. rewrite Hcont1.
            iDestruct (big_sepL_app with "Hstack_region") as "[Hframe' _]".
            iDestruct (big_sepL2_to_big_sepL_l with "Hframe'") as "Hframe+";eauto.
            iDestruct (big_sepL2_sep with "[$Hframe $Hframe+]") as "Hframe".
            iApply (big_sepL2_mono with "Hframe").
            iIntros (? ? ? ? ?) "HH". iDestruct "HH" as "[H1 [H2 _] ]". iDestruct "H1" as (? ?) "[Hrel Hy]".
            iDestruct (rel_agree with "[$Hrel $H2]") as "[% _]". subst H1. iFrame. 
          }
          iFrame. 
        }

        (* we isolate the activation record from the frame *)
        iDestruct (region_mapsto_cons with "Hframe") as "[Ha2 Hframe]"; [iContiguous_next Hcont1 0|..].
        { apply contiguous_between_middle_bounds with (i:=1) (ai:=a2) in Hcont1;auto. revert Hcont1;clear;solve_addr. }
        iDestruct (region_mapsto_cons with "Hframe") as "[Ha3 Hframe]"; [iContiguous_next Hcont1 1|..].
        { apply contiguous_between_middle_bounds with (i:=2) (ai:=a3) in Hcont1;auto. revert Hcont1;clear;solve_addr. }
        iDestruct (region_mapsto_cons with "Hframe") as "[Ha4 Hframe]"; [iContiguous_next Hcont1 2|..].
        { apply contiguous_between_middle_bounds with (i:=3) (ai:=stack_own_b) in Hcont1;auto.
          revert Hcont1;clear;solve_addr. }

        (* prepare the new stack value *)
        assert (exists stack_new, (stack_new + 1)%a = Some stack_own_end) as [stack_new Hstack_new].
        { revert Hstack_own_bound'. clear. intros H. destruct (stack_own_b + 6)%a eqn:Hsome;[|solve_addr].
          exists a. solve_addr. }

        (* step through instructions in activation record *)
        destruct rest1;[by inversion Hrest_length|].
        iApply (scall_epilogue_spec with "[-]"); last iFrame "Hframe HPC";
          [|done|iContiguous_next Hcont_rest1 0|apply Hstack_new|revert Hstack_own_bound Hstack_own_bound'; clear; solve_addr|..].
        { intros mid Hmid. split;[|auto]. apply withinBounds_le_addr in Hwb2.
          apply (contiguous_between_middle_bounds _ 3 stack_own_b) in Hcont1;[|auto]. revert Hwb2 Hcont1 Hmid. clear. solve_addr.
        }
        iSplitL "Hr_t1";[iNext;eauto|]. iSplitL "Hr_stk";[iNext;eauto|]. 
        iNext. iIntros "(HPC & Hr_stk & Hr_t1 & Hframe)".
        iDestruct "Hr_t1" as (wrt1) "Hr_t1".
        
        (* we can now step through the rest of the program *)
        (* to do that wee need to open the non atomic invariant of the program *)
        iMod (na_inv_acc with "Hf4 Hna") as "(>Hprog & Hna & Hcls')";[solve_ndisj..|]. 
        rewrite Heqapp Hrest_app. repeat rewrite app_assoc. repeat rewrite app_comm_cons. rewrite app_assoc.

        iDestruct (mapsto_decomposition _ _ _ (take 122 (awkward_instrs f_a r_adv)) with "Hprog")
          as "[Hprog_done [Ha Hprog] ]". 
        { simpl. repeat rewrite app_length /=.
          rewrite Hscall_length Hprepstack_length Hreqglob_length. auto. }
        iCombine "Ha" "Hprog_done" as "Hprog_done".
        (* sub r_t1 0 7 *)
        iPrologue rest1 Hrest_length "Hprog".
        iApply (wp_add_sub_lt_success_z_z with "[$HPC $Hr_t1 $Hinstr]");
          [apply decode_encode_instrW_inv|right;left;eauto|iContiguous_next Hcont_rest1 1|apply Hfl|iCorrectPC s_last a_last|..].
        iEpilogue "(HPC & Hinstr & Hr_t1)".
        iCombine "Hinstr" "Hprog_done" as "Hprog_done".
        (* lea r_stk r_t1 *)
        iPrologue rest1 Hrest_length "Hprog". 
        assert ((stack_new + (0 - 7))%a = Some a3) as Hpop.
        { assert ((a3 + 1)%a = Some stack_own_b) as Ha0;[iContiguous_next Hcont1 2|].
          revert Ha0 Hstack_own_bound' Hstack_new. clear. solve_addr. }
        iApply (wp_lea_success_reg with "[$HPC $Hr_t1 $Hr_stk $Hinstr]");
          [apply decode_encode_instrW_inv|apply Hfl|iCorrectPC s_last a_last|iContiguous_next Hcont_rest1 2|apply Hpop|auto..].
        { simpl; auto. }
        iEpilogue "(HPC & Hinstr & Hr_t1 & Hr_stk)". iCombine "Hinstr" "Hprog_done" as "Hprog_done". 
        (* pop r_stk r_adv *)
        do 3 (destruct rest1; [inversion Hrest_length|]).
        iDestruct (big_sepL2_app_inv _ [a13;a14;a15] (a16::rest1) with "Hprog") as "[Hpop Hprog]";[simpl;auto|].
        clear Hpop. assert ((a3 + (0 - 1))%a = Some a2) as Hpop.
        { rewrite -(addr_add_assoc a2 _ 1);[apply addr_add_0|iContiguous_next Hcont1 1]. }
        iApply (pop_spec); [..|iFrame "HPC Hr_stk Hr_t1 Hpop Hr_adv Ha4"];
          [split;[|split];iCorrectPC s_last a_last| apply Hfl|iContiguous_bounds_withinBounds a0 stack_own_last|auto|
           iContiguous_next Hcont_rest1 3|iContiguous_next Hcont_rest1 4|iContiguous_next Hcont_rest1 5|apply Hpop|].
        iNext. iIntros "(HPC & Hpop & Hr_adv & Ha4 & Hr_stk & Hr_t1)". iCombine "Hpop" "Hprog_done" as "Hprog_done".
        (* pop r_stk r_self *)
        do 3 (destruct rest1; [inversion Hrest_length|]).
        iDestruct (big_sepL2_app_inv _ [a16;a17;a18] (a19::rest1) with "Hprog") as "[Hpop Hprog]";[simpl;auto|].
        clear Hpop. assert ((a2 + (0 - 1))%a = Some a0) as Hpop.
        { rewrite -(addr_add_assoc a0 _ 1);[apply addr_add_0|iContiguous_next Hcont1 0]. }
        iApply (pop_spec); [..|iFrame "HPC Hr_stk Hr_t1 Hpop Hr_t0 Ha3"];
          [split;[|split];iCorrectPC s_last a_last| apply Hfl|iContiguous_bounds_withinBounds a0 stack_own_last|auto|
           iContiguous_next Hcont_rest1 6|iContiguous_next Hcont_rest1 7|iContiguous_next Hcont_rest1 8|apply Hpop|].
        iNext. iIntros "(HPC & Hpop & Hr_t0 & Ha3 & Hr_stk & Hr_t1)". iCombine "Hpop" "Hprog_done" as "Hprog_done".
        (* pop r_stk r_env *)
        do 3 (destruct rest1; [inversion Hrest_length|]).
        iDestruct (big_sepL2_app_inv _ [a19;a20;a21] (a22::rest1) with "Hprog") as "[Hpop Hprog]";[simpl;auto|].
        clear Hpop. assert ((a0 + (0 - 1))%a = Some b_r') as Hpop.
        { rewrite -(addr_add_assoc b_r' _ 1);[apply addr_add_0|auto]. }
        iApply (pop_spec); [..|iFrame "HPC Hr_stk Hr_t1 Hpop Hr_env Ha2"];
          [split;[|split];iCorrectPC s_last a_last| apply Hfl|iContiguous_bounds_withinBounds a0 stack_own_last|auto|
           iContiguous_next Hcont_rest1 9|iContiguous_next Hcont_rest1 10|iContiguous_next Hcont_rest1 11|apply Hpop|].
        iNext. iIntros "(HPC & Hpop & Hr_env & Hb_r & Hr_stk & Hr_t1)". iCombine "Hpop" "Hprog_done" as "Hprog_done".
        (* store r_env 1 *)
        iPrologue rest1 Hrest_length "Hprog".
        (* Storing 1 will always constitute a public future world of 
           std_update_multiple (revoke W3) dom(m_static1) Revoked *)
        iAssert (∀ φ, ▷ (PC ↦ᵣ inr (pc_p, pc_g, pc_b, pc_e, a23)
                       ∗ r_env ↦ᵣ inr (RWX, Global, d, d', d)
                       ∗ a22 ↦ₐ[pc_p'] store_z r_env 1
                       ∗ region (std_update_multiple (revoke (W3.1,(<[i:=encode true]> W3.2.1,W3.2.2)))
                                                     (elements (dom (gset Addr) m_static1)) Revoked)
                       ∗ sts_full_world (std_update_multiple (revoke (W3.1,(<[i:=encode true]> W3.2.1,W3.2.2)))
                                                     (elements (dom (gset Addr) m_static1)) Revoked)
                       ∗ ⌜(∃ y : bool, W3.2.1 !! i = Some (encode y)) ∧ W3.2.2 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv)⌝
                       -∗ WP Seq (Instr Executable) {{ v, φ v }})
                   -∗ WP Instr Executable {{ v, WP fill [SeqCtx] (of_val v) {{ v, φ v }} }})%I
          with "[HPC Hinstr Hr_env Hr Hsts]" as "Hstore_step".
        { iIntros (φ') "Hφ".
          iInv ι as (y) "[>Hstate Hb]" "Hcls".
          iDestruct (sts_full_state_loc with "Hsts Hstate") as %Hlookup.
          iDestruct (sts_full_rel_loc with "Hsts Hrel") as %Hrellookup.
          rewrite std_update_multiple_loc_sta in Hlookup.
          rewrite std_update_multiple_loc_rel in Hrellookup. 
          destruct y; iDestruct "Hb" as ">Hb".
          - iApply (wp_store_success_z with "[$HPC $Hinstr $Hr_env $Hb]");
              [apply decode_encode_instrW_inv|apply Hfl|apply PermFlows_refl|iCorrectPC s_last a_last|
               iContiguous_next Hcont_rest1 12|auto|].
            iNext. iIntros "(HPC & Hinstr & Hr_env & Hd)".
            iMod ("Hcls" with "[Hstate Hd]") as "_".
            { iNext. iExists true. iFrame. }
            iModIntro. iApply wp_pure_step_later;auto;iNext. iApply "Hφ". iFrame.            
            rewrite (insert_id _ i);[|auto].
            destruct W3 as [W3_std [W3_loc_pub W3_lo_priv] ]. iFrame.
            eauto. 
          - iApply (wp_store_success_z with "[$HPC $Hinstr $Hr_env $Hb]");
              [apply decode_encode_instrW_inv|apply Hfl|apply PermFlows_refl|iCorrectPC s_last a_last|
               iContiguous_next Hcont_rest1 12|auto|].
            iNext. iIntros "(HPC & Hinstr & Hr_env & Hd)".
            iMod (sts_update_loc _ _ _ true with "Hsts Hstate") as "[Hsts Hstate]".
            iMod ("Hcls" with "[Hstate Hd]") as "_".
            { iNext. iExists true. iFrame. }
            iModIntro. iApply wp_pure_step_later;auto;iNext. iApply "Hφ".
            rewrite std_update_multiple_loc_sta std_update_multiple_loc_rel std_update_multiple_proj_eq.
            iFrame. 
            iSplitL;[|eauto]. iApply (region_monotone with "[] [] Hr").
            + iPureIntro. rewrite /revoke /std /loc /=. erewrite std_update_multiple_std_sta_eq. eauto. 
            + iPureIntro. apply std_update_mutiple_related_monotone.
              split;[apply related_sts_std_pub_refl|].
              rewrite /= /loc. apply related_pub_local_1 with false; auto.
        }
        iApply "Hstore_step". iNext. iIntros "(HPC & Hr_env & Hinstr & Hr & Hsts & #HW3lookup)".
        iDestruct "HW3lookup" as %[HW3lookup Hw3rel]. 
        iCombine "Hinstr" "Hprog_done" as "Hprog_done".
        (* push r_stk r_env *)
        do 2 (destruct rest1;[inversion Hrest_length|]).
        iDestruct (big_sepL2_app_inv _ [a23;a24] (a25::rest1) with "Hprog") as "[Hpush Hprog]";[simpl;auto|]. 
        iApply (push_r_spec);[..|iFrame "HPC Hr_stk Hpush Hr_env Hb_r"];
          [split;iCorrectPC s_last a_last|apply Hfl|auto|iContiguous_next Hcont_rest1 13|iContiguous_next Hcont_rest1 14|auto|..].
        iNext. iIntros "(HPC & Hpush & Hr_stk & Hr_env & Hb_r)". iCombine "Hpush" "Hprog_done" as "Hprog_done".
        (* push r_stk r_self *)
        do 2 (destruct rest1;[inversion Hrest_length|]).
        iDestruct (big_sepL2_app_inv _ [a25;a26] (a27::rest1) with "Hprog") as "[Hpush Hprog]";[simpl;auto|]. 
        iApply (push_r_spec);[..|iFrame "HPC Hr_stk Hpush Hr_t0 Ha3"];
          [split;iCorrectPC s_last a_last|apply Hfl|iContiguous_bounds_withinBounds a0 stack_own_last|iContiguous_next Hcont_rest1 15|
           iContiguous_next Hcont_rest1 16|iContiguous_next Hcont1 0|..].
        iNext. iIntros "(HPC & Hpush & Hr_stk & Hr_self & Ha3)". iCombine "Hpush" "Hprog_done" as "Hprog_done". 
        (* SECOND SCALL *)

        (* we now want to extract the final element of the local stack, which will now be handed off to the adversary *)
        do 2 (iDestruct (big_sepL_sep with "Hstack_adv") as "[Hstack_adv _]").
        (* we will need to split off the last element to adv *)
        assert (forall stack_own_b : Addr, (stack_own_b <= stack_own_end)%Z -> region_addrs stack_own_b stack_own_last = region_addrs stack_own_b stack_own_end ++ [stack_own_end]) as Hstack_localeq'.
        { intros stack_own_b' Hle. rewrite (region_addrs_decomposition _ stack_own_end).
          - repeat f_equiv. assert( (stack_own_end + 1)%a = Some stack_own_last) as ->;[|by rewrite /region_addrs /region_size Z.sub_diag /=].
            revert Hstack_own_bound Hstack_own_bound' Hstack_new; clear. solve_addr. 
          - revert Hle Hstack_own_bound Hstack_own_bound' Hstack_new; clear. solve_addr. 
        }
        
        rewrite /region_mapsto (Hstack_localeq' stack_own_b);[|revert Hstack_own_bound';clear;solve_addr]. 
        iDestruct (mapsto_decomposition _ _ _ [inl w_1; inl w_2; inl w_3; inl w_4a; inl w_4b; inl w_4c;
                                               inr (pc_p, pc_g, pc_b, pc_e, s_last)] with "Hframe") as "[Hframe Hlast']".
        { rewrite region_addrs_length /=. rewrite /region_size. revert Hstack_own_bound'; clear. solve_addr. }
        assert ([stack_own_end] ++ region_addrs stack_own_last e_r = region_addrs stack_own_end e_r) as Hstack_localeq.
        { rewrite /region_addrs. apply withinBounds_le_addr in Hwb2 as [_ Hwb2].
          assert ((stack_own_end + 1)%a = Some stack_own_last) as Hincr;[revert Hstack_own_bound Hstack_own_bound';clear;solve_addr|].
          assert (region_size stack_own_end e_r = S (region_size stack_own_last e_r)) as ->.
          { revert Hstack_own_bound Hstack_own_bound' Hwb2; clear. rewrite /region_size. solve_addr. }
          simpl. f_equiv. rewrite Hincr /=. done.
        }  
        iAssert (∃ ws_adv : list Word, [[stack_own_end,e_r]]↦ₐ[RWLX][[ws_adv]])%I with "[Hstack_adv Hlast']" as (ws_adv'') "Hstack_adv".
        { iDestruct (region_addrs_exists with "Hstack_adv") as (ws_adv') "Hstack_adv".
          iDestruct (big_sepL2_sep with "Hstack_adv") as "[_ Hstack_adv]". iDestruct (big_sepL2_sep with "Hstack_adv") as "[Hstack_adv _]".
          iDestruct (mapsto_decomposition _ _ _ [inr (RWLX, Local, a0, e_r, stack_own_end)] with "[$Hstack_adv $Hlast']") as "Hstack_adv";[auto|..].
          rewrite Hstack_localeq. 
          iExists (_ :: ws_adv'). iFrame. 
        }
        iAssert (∃ ws_own : list Word, [[a3,stack_own_end]]↦ₐ[RWLX][[ws_own]])%I with "[Hframe Ha4]" as (ws_own'') "Hstack_own".
        { iExists ((inr (p, Global, b, e, a')) :: _). rewrite /region_mapsto.
          assert ([a3] ++ region_addrs stack_own_b stack_own_end = region_addrs a3 stack_own_end) as <-.
          { rewrite /region_addrs.
            assert ((a3 + 1)%a = Some stack_own_b) as Hincr;[iContiguous_next Hcont1 2|].
            assert (region_size a3 stack_own_end = S (region_size stack_own_b stack_own_end)) as ->.
            { revert Hstack_own_bound' Hincr; clear. rewrite /region_size. solve_addr. }
            simpl. f_equiv. rewrite Hincr /=. done. 
          }
          iApply (mapsto_decomposition [a3] _ _ [inr (p, Global, b, e, a')]); [auto|]. iFrame. done.
        }
        (* prepare for scall *)
        (* split the program into the scall_prologue and the rest *)
        assert (contiguous_between (a27 :: rest1) a27 a_last) as Hcont_weak.
        { repeat (inversion Hcont_rest1 as [|????? Hcont_rest1']; subst; auto; clear Hcont_rest1; rename Hcont_rest1' into Hcont_rest1). }
        iDestruct (contiguous_between_program_split with "Hprog") as (scall_prologue1 rest2 s_last1)
                                                                       "(Hscall & Hprog & #Hcont)"; [eauto|..].
        clear Hcont_weak.
        iDestruct "Hcont" as %(Hcont_scall1 & Hcont_rest2 & Hrest_app1 & Hlink2). subst.
        iDestruct (big_sepL2_length with "Hscall") as %Hscall_length1. simpl in Hscall_length1.
        destruct scall_prologue1 as [|scall_prologue_first1 scall_prologue1];[inversion Hscall_length1|].
        assert (scall_prologue_first1 = a27) as <-;[inversion Hrest_app1;auto|].
        (* some important element of the stack *)
        assert ((a3 + 8)%a = Some stack_own_end) as Hstack_own_bound1.
        { assert ((a3 + 1)%a = Some stack_own_b) as Ha4;[iContiguous_next Hcont1 2|].
          revert Hstack_own_bound Hstack_own_bound' Ha4. clear. solve_addr. }
        assert ((a3 + 7)%a = Some stack_new) as Hstack_own_bound1'.
        { revert Hstack_own_bound1 Hstack_new. clear. solve_addr. }
        assert (scall_prologue_first1 < s_last1)%a as Hcontlt1.
        { revert Hscall_length1 Hlink2. clear. solve_addr. }
        assert (s_last <= scall_prologue_first1)%a as Hcontge1.
        { apply region_addrs_of_contiguous_between in Hcont_scall. subst. revert Hscall_length1 Hcont_rest1 Hcontlt1.  clear =>Hscall_length Hf2 Hcontlt.
          apply contiguous_between_middle_bounds with (i := 17) (ai := scall_prologue_first1) in Hf2;[solve_addr|auto]. 
        }
        assert (withinBounds (RWLX, Local, a0, e_r, stack_own_end) = true) as Hwb3.
        { isWithinBounds. 
          - assert ((a0 + 3)%a = Some stack_own_b) as Hincr;[apply contiguous_between_incr_addr with (i := 3) (ai := stack_own_b) in Hcont1; auto|].
            revert Hstack_own_bound' Hincr. clear. solve_addr. 
          - apply withinBounds_le_addr in Hwb2 as [_ Hwb2]. revert Hstack_own_bound Hstack_own_bound' Hwb2. clear. solve_addr. 
        }
        (* we can now invoke the stack call prologue *)
        iDestruct (big_sepM_insert _ _ r_t1 with "[$Hmreg' $Hr_t1]") as "Hmreg'".
          repeat (rewrite lookup_delete_ne;[|done]). by rewrite lookup_delete.
          repeat (rewrite -(delete_insert_ne _ _ r_t1);[|done]).
          rewrite insert_delete.
        iDestruct (big_sepM_insert _ _ r_t0 with "[$Hmreg' $Hr_self]") as "Hmreg'".
          rewrite lookup_delete_ne; [|done]. by rewrite lookup_delete.
          rewrite -delete_insert_ne;[|done]. rewrite insert_delete.
        iDestruct (big_sepM_insert _ _ r_env with "[$Hmreg' $Hr_env]") as "Hmreg'".
          by rewrite lookup_delete. rewrite insert_delete.
        iAssert (⌜dom (gset RegName) r' = all_registers_s⌝)%I as %Hdom_r'.
        { iDestruct "Hfull'" as %Hfull'. iPureIntro.
          apply (anti_symm _); [apply all_registers_subseteq|]. rewrite elem_of_subseteq.
          intros x _. rewrite -elem_of_gmap_dom. apply Hfull'. }
        iApply (scall_prologue_spec with "[- $HPC $Hr_stk $Hmreg' $Hscall $Hstack_own $Hstack_adv]");
          [| |apply Hwb3|apply Hcont_scall1|apply Hfl|
           iNotElemOfList| |iContiguous_next Hcont1 1|apply Hstack_own_bound1'|apply Hstack_own_bound1|
           | done |..].
        { assert (s_last1 <= a_last)%a as Hle;[by apply contiguous_between_bounds in Hcont_rest2|].
          intros mid Hmid. apply isCorrectPC_inrange with link0 a_last; auto.
          revert Hle Hcontlt1 Hcontge1 Hcontlt Hcontge Hmid. clear; intros. split; solve_addr. }
        { iContiguous_bounds_withinBounds a0 stack_own_last. }
        { repeat rewrite ?dom_insert_L ?dom_delete_L. rewrite Hdom_r'.
          rewrite !singleton_union_difference_L !all_registers_union_l !difference_difference_L.
          f_equal. clear. set_solver. }
        { assert (12 + awkward_epilogue_off = 77)%Z as ->;[done|]. rewrite Hscall_length1 in Hlink2. done. }
        iNext. iIntros "(HPC & Hr_stk & Hr_t0 & Hr_gen & Hstack_own & Hstack_adv & Hscall)".
        iDestruct (big_sepL2_length with "Hprog") as %Hrest_length1. simpl in Hrest_length1.
        assert (isCorrectPC_range pc_p pc_g pc_b pc_e s_last1 a_last) as Hvpc2.
        { intros mid Hmid. assert (link0 <= s_last1)%a as Hle.
          { apply contiguous_between_bounds in Hcont_scall1.
            apply contiguous_between_bounds in Hcont_scall.
            revert Hcont_scall Hcont_scall1 Hcontge1 Hcontge;clear. solve_addr.
          } 
          apply isCorrectPC_inrange with link0 a_last; auto.
          revert Hmid Hle. clear. solve_addr. }
        (* jmp r_adv *)
        destruct rest2;[inversion Hrest_length1|]. 
        iPrologue rest2 Hrest_length1 "Hprog". apply contiguous_between_cons_inv_first in Hcont_rest2 as Heq. subst s_last1. 
        (* we separate the points to chunk from the persistent parts of the leftovers l'' *)
        iDestruct (temp_resources_split with "Hrest'") as (pws') "[#Hrest_valid' [#Hrev Hrest']]".
        iDestruct "Hrev" as %Hrev'.
        
        (* Allocate a static region to hold our frame *)

        (* first, put together again the resources for the frame *)

        iDestruct (region_mapsto_cons with "[$Ha3 $Hstack_own]") as "Hstack_own";
          [iContiguous_next Hcont1 1|..].
        { revert Hstack_own_bound1. clear; solve_addr. }
        iDestruct (region_mapsto_cons with "[$Hb_r $Hstack_own]") as "Hstack_own";
          [iContiguous_next Hcont1 0|..].
        { have: (a2 + 1 = Some a3)%a. by iContiguous_next Hcont1 1. revert Hstack_own_bound1.
          clear; solve_addr. }

        (* we'll need that later to reason on the fact that the [zip] in the definition of
           m_frame indeed fully uses both lists *)
        iDestruct (big_sepL2_length with "Hstack_own") as %Hlength_stack_own2.
        iDestruct (big_sepL2_length with "Hrest'") as %Hlength_rest''.

        match goal with |- context [ [[a0,stack_own_end]]↦ₐ[RWLX][[ ?instrs ]]%I ] =>
          set l_frame2 := instrs
        end.
        set static2_addrs := region_addrs a0 stack_own_end ++ l' ++ l''.
        set static2_instrs := l_frame2 ++ pws ++ pws'.
        set m_static2 := lists_to_static_region static2_addrs static2_instrs.

        rewrite std_update_multiple_revoke_commute;auto.

        (* fact: l', l'', [a2,stack_own_end] and [stack_own_end, e_r] are all
           disjoint. We will need these facts for later. We can derive them now
           from separation logic and the fact that pointsto (with non-O perm)
           are exclusive... *)

        set static_res := (λ a w, ∃ p φ, a ↦ₐ<p> w ∗ ⌜∀Wv, Persistent (φ Wv)⌝ ∗ rel a p φ)%I.

        (* static_res includes a non-O pointsto, therefore it is exclusive *)
        iAssert (⌜∀ a w1 w2, static_res a w1 -∗ static_res a w2 -∗ False⌝)%I as %Hstatic_res_excl.
        { iIntros (? ? ?) "". iPureIntro. iIntros "H1 H2". iDestruct "H1" as (? ?) "[[? %] _]".
          iDestruct "H2" as (? ?) "[[? %] _]". iApply (cap_duplicate_false with "[$]"). split; assumption. }
        
        iAssert ([∗ list] a;w ∈ l';pws, static_res a w)%I with "[Hl']" as "Hl'".
        { iDestruct (big_sepL2_sep with "[Hrest_valid $Hl']") as "Hl'". by iApply "Hrest_valid".
          iApply (big_sepL2_mono with "Hl'"). cbn. iIntros (k a'' pw ? ?) "[H1 H2]".
          iDestruct "H2" as (? ? ?) "(? & ? & #Hrel' & ?)".
          iDestruct "H1" as (? ?) "[#Hrel ?]".
          iDestruct (rel_agree _ H1 H4 with "[$Hrel $Hrel']") as "[% _]";subst H1. 
          iExists _,_. iFrame. eauto. }
        
        iAssert ([∗ list] a;w ∈ l'';pws', static_res a w)%I with "[Hrest']" as "Hrest'".
        { iDestruct (big_sepL2_sep with "[Hrest_valid' $Hrest']") as "Hrest'". by iApply "Hrest_valid'".
          iApply (big_sepL2_mono with "Hrest'"). cbn. iIntros (k a'' pw ? ?) "[H1 H2]".
          iDestruct "H2" as (? ? ?) "(? & ? & #Hrel' & ?)".
          iDestruct "H1" as (? ?) "[? #Hrel]".
          iDestruct (rel_agree _ H1 H4 with "[$Hrel $Hrel']") as "[% _]";subst H1.
          iExists _. iFrame. eauto. }
        
        assert (a0 <= stack_own_end ∧ stack_own_end <= e_r)%a.
        { move: (withinBounds_le_addr _ _ _ _ _ Hwb3). clear; solve_addr. }

        iAssert ([∗ list] a;w ∈ (region_addrs a0 stack_own_end);l_frame2, static_res a w)%I
          with "[Hstack_own]" as "Hstack_own".
        { rewrite (region_addrs_split a0 stack_own_end e_r) //.
          iDestruct (big_sepL_app with "Hstack_region") as "[Hstack_val' _]".
          iDestruct (big_sepL2_sep with "[Hstack_val' $Hstack_own]") as "Hstack_own".
          { iApply big_sepL2_to_big_sepL_l. auto. iApply "Hstack_val'". }
          iApply (big_sepL2_mono with "Hstack_own"). iIntros (? ? ? ? ?) "(? & ? & ?)". unfold static_res.
          iExists _,_. rewrite /read_write_cond. iFrame. iSplitR; [iPureIntro; congruence|]. iPureIntro.
          intro; apply interp_persistent. }

        iDestruct (big_sepL2_app with "Hl' Hrest'") as "Hl'_rest'".

        (* we will need that later *)
        iAssert (⌜NoDup (region_addrs a0 e_r ++ l' ++ l'')⌝)%I as %Hstack_l'_l''_NoDup.
        { iAssert ([∗ list] a;w ∈ (region_addrs stack_own_end e_r);region_addrs_zeroes stack_own_end e_r, static_res a w)%I
            with "[Hstack_adv]" as "Hstack_adv".
          { rewrite (region_addrs_split a0 stack_own_end e_r) //.
            iDestruct (big_sepL_app with "Hstack_region") as "[_ Hstack_val']".
            iDestruct (big_sepL2_sep with "[Hstack_val' $Hstack_adv]") as "Hstack_adv".
            { iApply big_sepL2_to_big_sepL_l.
              by rewrite /region_addrs !region_addrs_aux_length /region_addrs_zeroes replicate_length //.
              iApply "Hstack_val'". }
            iApply (big_sepL2_mono with "Hstack_adv"). iIntros (? ? ? ? ?) "(? & ? & ?)". unfold static_res.
            unfold read_write_cond. iExists _,_. iFrame. iSplitR; [iPureIntro; congruence|].
            iPureIntro. intro; apply interp_persistent. }
          
          iApply (NoDup_of_sepL2_exclusive with "[] [Hstack_own Hstack_adv Hl'_rest']").
          2: { rewrite (region_addrs_split a0 stack_own_end e_r) //.
               iDestruct (big_sepL2_app with "Hstack_own Hstack_adv") as "Hstack".
               iDestruct (big_sepL2_app with "Hstack Hl'_rest'") as "HH". iApply "HH". }
          iIntros (? ? ?). iApply Hstatic_res_excl. }
        
        (* Allocate the static region; for that we only need the part of Hstack we own *)
        iAssert ([∗ list] a;w ∈ static2_addrs;static2_instrs, static_res a w)%I
          with "[Hstack_own Hl'_rest']" as "Hstatic".
        { iApply (big_sepL2_app with "Hstack_own Hl'_rest'"). }

        iAssert (⌜NoDup static2_addrs⌝)%I as %Hstatic2_addrs_NoDup.
        { iApply (NoDup_of_sepL2_exclusive with "[] Hstatic").
          iIntros (? ? ?) "". iApply Hstatic_res_excl. }
        
        iDestruct (region_revoked_to_static _ m_static2 with "[$Hsts $Hr Hstatic]") as ">[Hsts Hr]".
        { iApply (big_sepL2_to_static_region with "[] Hstatic"). assumption.
          iModIntro. iIntros (? ? pw ? ?) "H". iDestruct "H" as (? ?) "([? ?] & ? & ?)".
          iExists _,_. iFrame. }

        rewrite -std_update_multiple_revoke_commute;auto.

        (* now that we have privately updated our resources, we can close the region invariant for the adv stack *)
        assert (list.last (a0 :: a2 :: a3 :: stack_own_b :: stack_own) = Some stack_own_end) as Hlast.
        { apply contiguous_between_link_last with a0 stack_own_last; [auto|apply gt_Sn_O|].
          revert Hstack_own_bound Hstack_own_bound'; clear. solve_addr. }

        (* To make some of the future proofs easier, let's make certain assertions about addresses in adv frame *)
        assert (∀ a, a ∈ region_addrs stack_own_end e_r -> a ∉ elements (dom (gset Addr) m_static2)) as Hnin2.
        { rewrite lists_to_static_region_dom.
          2: { repeat rewrite app_length. rewrite Hlength_rest Hlength_rest''. auto. }
          intros a'' Ha'. 
          rewrite elements_list_to_set;auto.
          assert (a'' ∈ region_addrs a0 e_r) as Hin'.
          { rewrite -Hstack_localeq in Ha'. rewrite Hstack_eq1.
            apply elem_of_app in Ha' as [Hl | Hr].
            - apply elem_of_list_singleton in Hl. subst.
              apply elem_of_app; left. apply elem_of_list_lookup. exists (11 - 1).
              rewrite -Hlength_own -last_lookup; auto.
            - by apply elem_of_app; right. 
          } 
          apply not_elem_of_app. split.
          - apply region_addrs_xor_elem_of with (c:=stack_own_end) in Hin' as [ [Hin' Hnin] | [Hin' Hnin] ];auto.
            eapply withinBounds_le_addr. apply Hwb3. 
          - rewrite NoDup_app in Hstack_l'_l''_NoDup |- *. intros (_ & HH & _). by apply HH.
        }
        assert (∀ a, a ∈ region_addrs stack_own_last e_r -> a ∉ elements (dom (gset Addr) m_static1)) as Hnin1.
        { rewrite lists_to_static_region_dom.
          2: { repeat rewrite app_length. rewrite Hlength_rest . auto. }
          intros a'' Ha'. 
          rewrite elements_list_to_set;auto.
          assert (a'' ∈ region_addrs a0 e_r) as Hin'.
          { rewrite Hstack_eq1. apply elem_of_app;right. auto. } 
          apply not_elem_of_app. split.
          - apply region_addrs_xor_elem_of with (c:=stack_own_last) in Hin' as [ [Hin' Hnin] | [Hin' Hnin] ];auto.
            eapply withinBounds_le_addr. apply Hwb2.
          - rewrite NoDup_app in Hstack_l'_l''_NoDup |- *. intros (_ & HH & _).
            by eapply (not_elem_of_app l' l''), HH.
        }

        match goal with |- context [ region ?W ] => set W4 := W end.
        
        (* finally we can now close the region: a_last' will be in state revoked in revoke(W3) *)
        assert (∀ x, x ∈ ([stack_own_end] ++ region_addrs stack_own_last e_r) ->
                       W4.1 !! x = Some Revoked) as Hlookup_revoked.
        { intros x Hsome.
          rewrite std_sta_update_multiple_lookup_same_i;auto.
          2: { apply Hnin2. rewrite Hstack_localeq in Hsome. auto. } 
          apply elem_of_app in Hsome as [Hl | Hr]. 
          + apply elem_of_list_singleton in Hl;subst.
            apply std_sta_update_multiple_lookup_in_i.
            rewrite lists_to_static_region_dom;[|repeat rewrite app_length;auto].
            rewrite elements_list_to_set;auto.
            apply elem_of_app;left. apply region_addrs_of_contiguous_between in Hcont1 as <-.
            apply elem_of_list_lookup. exists (11 - 1). rewrite -Hlength_own -last_lookup; auto.
          + rewrite std_sta_update_multiple_lookup_same_i;auto.
            apply elem_of_list_lookup in Hr as [k Hk]. 
            apply revoke_lookup_Temp. 
            eapply HtempW3; eauto. 
        }
        
        iMod (monotone_close _ (region_addrs stack_own_end e_r) RWLX (λ Wv, interp Wv.1 Wv.2)
                with "[$Hsts $Hr Hstack_adv ]") as "[Hsts Hr]".
        { iClear "Hreg' Hfull' full Hf4 Hrel Hinv Hadv_val".
          rewrite Hstack_eq1. 
          iDestruct (region_addrs_zeroes_trans with "Hstack_adv") as "Hstack_adv".
          rewrite /region_mapsto -Hstack_localeq.
          iDestruct (big_sepL_app with "Hstack_adv") as "[ [Hs_last' _] Hstack_adv]". 
          iDestruct (big_sepL_app with "Hstack_region") as "[Hstack_last Hstack_val']".
          iDestruct (big_sepL_lookup _ _ (length (a0 :: a2 :: a3 :: stack_own_b :: stack_own) - 1) stack_own_end with "Hstack_last") as "[Hs_last_val _]";[by rewrite -last_lookup|].
          iApply big_sepL_sep. iSplitL.
          - iApply big_sepL_app. iSplitL "Hs_last'". 
            + iSimpl. iSplit;[|auto]. iExists (inl 0%Z). iSplitR;auto. iFrame. iSplit.
              * iModIntro. iIntros (W1 W2 Hrelated12) "HW1". by repeat (rewrite fixpoint_interp1_eq).
              * by repeat (rewrite fixpoint_interp1_eq).
            + iApply (big_sepL_mono with "Hstack_adv"). iIntros (k y Hsome) "Hy".
              iExists (inl 0%Z). iSplitR;auto. iFrame. iSplit.
              * iModIntro. iIntros (W1 W2 Hrelated12) "HW1". by repeat (rewrite fixpoint_interp1_eq).
              * by repeat (rewrite fixpoint_interp1_eq).
          - iDestruct (big_sepL_and with "Hstack_val'") as "[Hstack_rel _]". 
            iApply big_sepL_sep; iFrame "#". iSplit;[auto|]. iApply big_sepL_forall. iPureIntro.
            hnf. intros x a'' Hin.
            apply Hlookup_revoked. apply elem_of_list_lookup. eauto. 
        }

        (* The resulting world is a private future world of W3 *)
        iSimpl in "Hsts".
        match goal with |- context [ region ?W ] => set W5 := W end.
        
        assert (related_sts_priv_world W3 W5) as Hrelated5.
        { eapply related_sts_priv_pub_trans_world;[|apply close_list_related_sts_pub;auto].
          eapply related_sts_priv_trans_world;[|apply related_sts_priv_world_static];auto.
          eapply related_sts_priv_trans_world;[|apply related_sts_priv_world_revoked with (m:=m_static1)];auto.
          eapply related_sts_priv_trans_world;[|apply revoke_related_sts_priv];auto.
          apply related_sts_pub_priv_world. destruct HW3lookup as [y Hy].
          split;[apply related_sts_std_pub_refl|simpl;eapply related_pub_local_1; eauto].
          - apply Forall_forall. intros a'' Hin.
            apply revoke_lookup_Static. apply elem_of_elements in Hin. 
            apply Hall_static in Hin. rewrite /static in Hin.
            destruct (W3.1 !! a'') eqn:Hsome;[subst|done]; auto.
          - apply Forall_forall. intros a'' Hin.
            destruct (decide (a'' ∈ (elements (dom (gset Addr) m_static1)))). 
            apply std_sta_update_multiple_lookup_in_i;auto.
            rewrite std_sta_update_multiple_lookup_same_i;auto.
            apply revoke_lookup_Temp. apply Hiff'. revert Hin n.
            rewrite lists_to_static_region_dom;[|repeat rewrite app_length;rewrite Hlength_rest Hlength_rest'';auto]. 
            rewrite lists_to_static_region_dom;[|repeat rewrite app_length;rewrite Hlength_rest;auto].
            repeat rewrite elements_list_to_set;auto. rewrite Hstack_localeq'. clear; set_solver.
            apply withinBounds_le_addr in Hwb3 as [? _]. auto. 
        }

        (* we can now finally monotonically update the region to match the new sts collection *)
        iDestruct (sts_full_rel_loc with "Hsts Hrel") as %Hreli.
        (* We choose the r *)
        set r2 : gmap RegName Word :=
          <[PC    := inl 0%Z]>
          (<[r_stk := inr (RWLX, Local, stack_own_end, e_r, stack_new)]>
          (<[r_t0  := inr (E, Local, a0, e_r, a3)]>
          (<[r_adv := inr (p, Global, b, e, a')]>
          (create_gmap_default
             (list_difference all_registers [PC; r_stk; r_t0; r_adv]) (inl 0%Z))))).

        (* we set up the expression relation of the jump *)
        assert (related_sts_priv_world W W5) as Hrelated5'.
        { eapply related_sts_priv_trans_world;[|apply Hrelated5]. 
            by eapply related_sts_priv_pub_trans_world;[|apply Hrelated3]. }
        iDestruct ("Hadv_cont" $! r2 W5 Hrelated5') as "Hadv_contW5".     
        (* we do the actual jump *)
        iApply (wp_jmp_success with "[$Hinstr $Hr_adv $HPC]");
          [apply decode_encode_instrW_inv|apply Hfl|iCorrectPC a27 a_last|..].
        iEpilogue "(HPC & Hinstr & Hr_adv)". iSimpl in "HPC".

        (* We have all the resources of r *)
        iAssert (registers_mapsto (<[PC:=match p with
                | E => inr (RX, Global, b, e, a')
                | _ => inr (p, Global, b, e, a')
                end]> r2))
          with "[Hr_gen Hr_stk Hr_t0 Hr_adv HPC]" as "Hmaps".
        { iApply (registers_mapsto_resources with "Hr_gen Hr_stk Hr_t0 Hr_adv HPC").
          repeat rewrite ?dom_delete_L ?dom_insert_L. rewrite Hdom_r'.
          rewrite !singleton_union_difference_L !all_registers_union_l !difference_difference_L.
          f_equal. clear. set_solver. }
        (* r contrains all registers *)
        iAssert (full_map r2) as "#Hfull2";[iApply r_full|].
        iSimpl in "Hadv_val".
        (* again we are jumping to unknown code. We will now need to close all our invariants so we can 
           reestablish the FTLR on the new state *)
        (* we close the invariant for our program *)
        iMod ("Hcls'" with "[Hprog_done Hprog Hinstr Hscall $Hna]") as "Hna".
        { iNext. iDestruct "Hprog_done" as "(Hpush2 & push1 & Ha19 & Hpop1 & Hpop2 & Hpop3 &
                                             Ha8 & Ha9 & Hrest0_first & Hprog_done)".
          iApply (big_sepL2_app with "Hprog_done [-]"). 
          iFrame "Hrest0_first Ha9 Ha8". 
          iApply (big_sepL2_app with "Hpop3 [-]").
          iApply (big_sepL2_app with "Hpop2 [-]").
          iApply (big_sepL2_app with "Hpop1 [-]").
          iFrame "Ha19".
          iApply (big_sepL2_app with "push1 [-]").
          iApply (big_sepL2_app with "Hpush2 [-]").
          rewrite Hrest_app1. 
          iApply (big_sepL2_app with "Hscall [-]"). iFrame.
        }

        (* the adversary stack is valid in the W5 *)
        iAssert ([∗ list] a ∈ region_addrs stack_own_end e_r,
                 read_write_cond a RWLX (fixpoint interp1)
                 ∗ ⌜region_state_pwl W5 a⌝)%I as "#Hstack_adv_val".
        { rewrite Hstack_eq1.
          iDestruct (big_sepL_app with "Hstack_region") as "[Hstack_last Hstack_val']".
          iDestruct (big_sepL_lookup _ _ (length (a0 :: a2 :: a3 :: stack_own_b :: stack_own) - 1) stack_own_end with "Hstack_last")
            as "[Hs_last_val _]";[by rewrite -last_lookup|].
          iApply big_sepL_sep. iSplit.
          - rewrite /region_mapsto -Hstack_localeq. 
            iApply big_sepL_app. iFrame "Hs_last_val".
            iSplit;[auto|]. 
            iApply (big_sepL_mono with "Hstack_val'").
            iIntros (g y Hsome) "[Hy _]". rewrite /read_write_cond. iFrame.
          - iApply big_sepL_forall. iPureIntro.
            intros g y Hsome.
            apply close_list_std_sta_revoked; auto.
            { apply elem_of_list_lookup_2 with g. auto. }
            apply Hlookup_revoked. rewrite Hstack_localeq.
            apply elem_of_list_lookup_2 with g. auto.
        }
        (* We are now ready to show that all registers point to a valid word *)
        iAssert (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → (fixpoint interp1) W5 (r2 !r! r1))%I
          with "[-Hsts Hr Hmaps Hna]" as "Hreg".
        { iIntros (r1).
          assert (r1 = PC ∨ r1 = r_stk ∨ r1 = r_t0 ∨ r1 = r_adv ∨ (r1 ≠ PC ∧ r1 ≠ r_stk ∧ r1 ≠ r_t0 ∧ r1 ≠ r_adv)) as
              [-> | [-> | [-> | [Hr_t30 | [Hnpc [Hnr_stk [Hnr_t0 Hnr_t30] ] ] ] ] ] ].
          { destruct (decide (r1 = PC)); [by left|right].
            destruct (decide (r1 = r_stk)); [by left|right].
            destruct (decide (r1 = r_t0)); [by left|right].
            destruct (decide (r1 = r_adv)); [by left|right;auto].  
          }
          - iIntros "%". contradiction.
          - assert (r2 !! r_stk = Some (inr (RWLX, Local, stack_own_end, e_r, stack_new))) as Hr_stk; auto. 
            rewrite /RegLocate Hr_stk. repeat rewrite fixpoint_interp1_eq. 
            iIntros (_).
            iAssert ([∗ list] a ∈ region_addrs stack_own_end e_r, ∃ p0 : Perm,
                                                   ⌜PermFlows RWLX p0⌝
                                                   ∗ read_write_cond a p0 (fixpoint interp1)
                                                   ∧ ⌜region_state_pwl W5 a⌝)%I as "#Hstack_adv_val'". 
            { iApply (big_sepL_mono with "Hstack_adv_val"). iIntros (g y Hsome) "(Hr & Hrev)".
              iExists RWLX. iFrame. auto. }
            iFrame "Hstack_adv_val'". 
          - (* continuation *)
            iIntros (_). clear Hr_t0. 
            assert (r2 !! r_t0 = Some (inr (E, Local, a0, e_r, a3))) as Hr_t0; auto. 
            rewrite /RegLocate Hr_t0. repeat rewrite fixpoint_interp1_eq. iSimpl. 
            (* prove continuation *)
            iModIntro.
            iIntros (r3 W6 Hrelated6).
            iNext.

            (* We start by asserting that the adversary stack is still temporary *)
            iAssert ([∗ list] a ∈ (region_addrs stack_own_end e_r),
                     ⌜W6.1 !! a = Some Temporary⌝
                    ∗ rel a RWLX (λ Wv : WORLD * Word, ((fixpoint interp1) Wv.1) Wv.2)
                )%I as "#Hstack_adv_tmp'".
            { iApply (big_sepL_mono with "Hstack_adv_val"). iIntros (k y Hsome) "(Hrel & Htemp)".
              iFrame. iDestruct "Htemp" as %Htemp6. 
              iPureIntro.
              apply region_state_pwl_monotone with W5; eauto. }
            iDestruct (big_sepL_sep with "Hstack_adv_tmp'") as "[Htemp _]". 
            iDestruct (big_sepL_forall with "Htemp") as %HtempW6. iClear "Htemp". 
            
            (* we want to distinguish between the case where the local stack frame is Static (step through 
               continuation) and where the local stack frame is temporary (apply FTLR) *)
            assert (forall a, a ∈ region_addrs a0 stack_own_end ++ l' ++ l'' ->
                         (std W6) !! a = Some Temporary ∨
                         (std W6) !! a = Some (Static m_static2))
              as Hcases'.
            { intros a'' Hin. apply or_comm,related_sts_pub_world_static with W5;auto.
              assert (std W4 !! a'' = Some (Static m_static2)) as Hlookup.
                { apply std_sta_update_multiple_lookup_in_i.
                  rewrite lists_to_static_region_dom;[|repeat rewrite app_length;rewrite Hlength_rest;auto].
                  rewrite elements_list_to_set;auto. }
                rewrite -close_list_std_sta_same_alt;auto. rewrite Hlookup. intros Hcontr;inversion Hcontr as [heq].
            }
            assert (a0 ∈ region_addrs a0 stack_own_end ++ l' ++ l'') as Ha2in.
            { apply elem_of_app. left. apply elem_of_list_lookup. exists 0.
              apply region_addrs_first. assert ((a0 + 2)%a = Some a3) as Hincr.
              eapply (contiguous_between_incr_addr _ 2 a0 a3);[apply Hcont1|auto].
              revert Hstack_own_bound1 Hincr. clear. solve_addr. }
            pose proof (Hcases' _ Ha2in) as [Hm_temp' | Hm_static'].
            { iSimpl. 
              iIntros "(#[Hfull3 Hreg3] & Hmreg' & Hr & Hsts & Hna)". 
              iSplit; [auto|rewrite /interp_conf].
              (* first we want to assert that if a2 is Temporary, the remaining addresses are also temporary *)
              iAssert (⌜∀ a : Addr, a ∈ dom (gset Addr) m_static2 → temporary W6 a⌝)%I as %Hm_frame_temp_all.
              { iIntros (a''). rewrite /m_static2. 
                rewrite lists_to_static_region_dom;[|repeat rewrite app_length;rewrite Hlength_rest;auto].
                iIntros (Hin). apply elem_of_list_to_set in Hin. 
                pose proof (Hcases' a'' Hin) as [Htemp' | Hstatic].
                - rewrite /temporary. rewrite Htemp'. auto.
                - iDestruct (full_sts_static_all with "Hsts Hr") as %Hforall;[eauto|]. exfalso.
                  assert (a0 ∈ dom (gset Addr) m_static2) as Hin'.
                  { rewrite lists_to_static_region_dom;[|repeat rewrite app_length;rewrite Hlength_rest;auto].
                    apply elem_of_list_to_set. auto. }
                  apply Hforall in Hin'. rewrite /static Hm_temp' in Hin'. done. 
              }
              iDestruct (fundamental W6 r3 RX Local a0 e_r a3 with "[] [] [-]") as "[_ Hcont]";[by iLeft| |iFrame "∗ #"|..].
              { iSimpl. 
                iApply (big_sepL_mono with "Hstack_region").
                iIntros (k y Hk) "[Hrel _]". iExists RWLX. iFrame. iSplit;auto. iPureIntro.            
                left. 
                (* we assert that the region is all in state temporary *)
                rewrite (region_addrs_split _ stack_own_end) in Hk. 
                assert (y ∈ region_addrs a0 stack_own_end ++ region_addrs stack_own_end e_r) as Hk'.
                { apply elem_of_list_lookup. eauto. }
                apply elem_of_app in Hk' as [Hframe | Hadv].
                + assert (y ∈ dom (gset Addr) m_static2) as Hk'.
                  { rewrite lists_to_static_region_dom;[|repeat rewrite app_length;rewrite Hlength_rest;auto].
                    apply elem_of_list_to_set. apply elem_of_app. by left. }
                  apply Hm_frame_temp_all in Hk'. rewrite /temporary in Hk'.
                  destruct (W6.1 !! y) eqn:Hsome;[subst;auto|done].
                + apply elem_of_list_lookup in Hadv as [j Hj]. by apply HtempW6 with j. 
                + apply withinBounds_le_addr in Hwb3 as [Hle1 Hle2]. revert Hle1 Hle2.
                  clear. solve_addr. 
              }
              iFrame. 
            }
            
            (* Now we are in the case where m_static2 is still static. We will have to open the region and step through
               the continuation as usual. *)
            iSimpl. 
            iIntros "(#[Hfull3 Hreg3] & Hmreg' & Hr & Hsts & Hna)".
            (* since a2 is static, all of dom(m_static1) is static *)
            iDestruct (full_sts_static_all with "Hsts Hr") as %Hall_static';eauto.
            iSplit; [auto|rewrite /interp_conf].
            (* get the PC, currently pointing to the activation record *)
            iDestruct (big_sepM_delete _ _ PC with "Hmreg'") as "[HPC Hmreg']";[rewrite lookup_insert; eauto|].
            (* get some registers *)
            iGet_genpur_reg_map r3 r_t1 "Hmreg'" "Hfull3" "[Hr_t1 Hmreg']".
            iGet_genpur_reg_map r3 r_stk "Hmreg'" "Hfull3" "[Hr_stk Hmreg']".
            iGet_genpur_reg_map r3 r_adv "Hmreg'" "Hfull3" "[Hr_adv Hmreg']".
            iGet_genpur_reg_map r3 r_env "Hmreg'" "Hfull3" "[Hr_env Hmreg']".
            iGet_genpur_reg_map r3 r_t0 "Hmreg'" "Hfull3" "[Hr_t0 Hmreg']".
            iGet_genpur_reg_map r3 r_t2 "Hmreg'" "Hfull3" "[Hr_t2 Hmreg']".
            
            (* Open the static region for the local stack frame *)
            iMod (region_open_static with "[$Hr $Hsts]") as "(Hr & Hsts & Hstates & Hframe & %)";
              [apply Hm_static'|].
            iAssert ( a0 ↦ₐ[RWLX] inr (RWX, Global, d, d', d)
                    ∗ a2 ↦ₐ[RWLX] wret
                    ∗ [[a3,stack_own_end]] ↦ₐ[RWLX] 
                           [[ [inl w_1; inl w_2; inl w_3; inl w_4a; inl w_4b; inl w_4c;
                               inr (pc_p, pc_g, pc_b, pc_e, a27); inr (RWLX, Local, a0, e_r, stack_new)] ]]
                    ∗ [∗ list] a;w ∈ l'++l''; pws++pws', ∃ p φ, rel a p φ ∗ a ↦ₐ[p] w)%I
              with "[Hframe]" as "(Ha2 & Ha3 & Hframe & Hrest)".
            { iDestruct (static_region_to_big_sepL2 _ _ (λ a v, ∃ p φ, rel a p φ ∗ a ↦ₐ[p] v)%I with "[] Hframe")
                as "Hframe";[auto|..]. 
              { repeat rewrite app_length. rewrite Hlength_rest Hlength_rest'';auto. }
              { iModIntro. auto. }
              iDestruct (big_sepL2_app' with "Hframe") as "[Hframe $]";[auto|].
              iAssert ([∗ list] y1;y2 ∈ region_addrs a0 stack_own_end;l_frame2, y1 ↦ₐ[RWLX] y2)%I
                with "[Hframe]" as "Hframe".
              { rewrite (region_addrs_split _ stack_own_end).
                iDestruct (big_sepL_app with "Hstack_region") as "[Hframe' _]".
                iDestruct (big_sepL2_to_big_sepL_l _ _ l_frame2 with "Hframe'") as "Hframe+";eauto.
                iDestruct (big_sepL2_sep with "[Hframe+ Hframe]") as "Hframe";
                  [iSplitL "Hframe";[iFrame "Hframe"|iFrame "Hframe+"]|].
                iApply (big_sepL2_mono with "Hframe").
                iIntros (k y1 y2 Hin1 Hin2) "[H1 [Hrel2 _] ]".
                iDestruct "H1" as (? ?) "[Hrel1 ?]".
                iDestruct (rel_agree with "[$Hrel1 $Hrel2]") as "[% _]". subst H1. iFrame.
                auto. }                
              iDestruct (region_mapsto_cons with "Hframe") as "[Ha2 Hframe]"; [iContiguous_next Hcont1 0|..].
              { apply contiguous_between_middle_bounds with (i:=1) (ai:=a2) in Hcont1;auto.
                revert Hstack_own_bound Hstack_own_bound' Hcont1;clear. solve_addr. }
              iDestruct (region_mapsto_cons with "Hframe") as "[Ha3 Hframe]"; [iContiguous_next Hcont1 1|..].
              { apply contiguous_between_middle_bounds with (i:=2) (ai:=a3) in Hcont1;auto.
                revert Hstack_own_bound Hstack_own_bound' Hcont1;clear. solve_addr. }
              iFrame. 
            }
            (* prepare the new stack value *)
            assert (∃ stack_new_1, (stack_new_1 + 1)%a = Some stack_new) as [stack_new_1 Hstack_new_1].
            { revert Hstack_own_bound' Hstack_new. clear. intros H. destruct (stack_own_b + 5)%a eqn:Hsome;[|solve_addr].
              exists a. solve_addr. }
            (* step through instructions in activation record *)
            iApply (scall_epilogue_spec with "[-]"); last iFrame "Hframe HPC";
              [|done|iContiguous_next Hcont_rest2 0|apply Hstack_new_1|revert Hstack_own_bound1 Hstack_own_bound1'; clear; solve_addr|..].
            { intros mid Hmid. split;[|auto]. apply withinBounds_le_addr in Hwb3.
              apply (contiguous_between_middle_bounds _ 2 a3) in Hcont1;[|auto].
              revert Hwb3 Hcont1 Hmid. clear. solve_addr. 
            }
            iSplitL "Hr_t1";[iNext;eauto|]. iSplitL "Hr_stk";[iNext;eauto|]. 
            iNext. iIntros "(HPC & Hr_stk & Hr_t1 & Hframe)".
            iDestruct "Hr_t1" as (wrt1') "Hr_t1".
            (* we don't want to close the stack invariant yet, as we will now need to pop it *)
            (* go through rest of the program. We will now need to open the invariant and destruct it into its done and prog part *)
            (* sub r_t1 0 7 *)
            iMod (na_inv_acc with "Hf4 Hna") as "(>Hprog & Hna & Hcls')";[solve_ndisj..|].
            iClear "Hadv_val". 
            rewrite Hrest_app1. repeat rewrite app_comm_cons. rewrite app_assoc.
            rewrite /awkward_example /awkward_instrs.
            iDestruct (mapsto_decomposition _ _ _ (reqglob_instrs r_adv ++
                                                   prepstack_instrs r_stk 11 ++ 
                                                   [store_z r_env 0] ++
                                                   push_r_instrs r_stk r_env ++
                                                   push_r_instrs r_stk r_t0 ++
                                                   push_r_instrs r_stk r_adv ++
                                                   scall_prologue_instrs awkward_epilogue_off r_adv ++
                                                   [jmp r_adv;
                                                    sub_z_z r_t1 0 7;
                                                    lea_r r_stk r_t1] ++
                                                   pop_instrs r_stk r_adv ++
                                                   pop_instrs r_stk r_t0 ++
                                                   pop_instrs r_stk r_env ++
                                                   [store_z r_env 1] ++
                                                   push_r_instrs r_stk r_env ++
                                                   push_r_instrs r_stk r_t0 ++
                                                   scall_prologue_instrs awkward_epilogue_off r_adv) with "Hprog")
              as "[Hprog_done [Ha Hprog] ]". 
            { simpl. inversion Hscall_length as [Heq]. inversion Hscall_length1 as [Heq']. rewrite app_length Heq /=. rewrite Heq'. repeat rewrite app_length. rewrite Hreqglob_length Hprepstack_length. simpl. repeat f_equiv. rewrite Heq. done. }
            iCombine "Ha" "Hprog_done" as "Hprog_done".
            (* sub r_t1 0 7 *)
            iPrologue rest2 Hrest_length1 "Hprog".
            iApply (wp_add_sub_lt_success_z_z with "[$HPC Hr_t1 $Hinstr]");
              [apply decode_encode_instrW_inv|right;left;eauto|iContiguous_next Hcont_rest2 1|apply Hfl|iCorrectPC a27 a_last|
               iSimpl;iFrame;eauto|].
            iEpilogue "(HPC & Hinstr & Hr_t1)".
            iCombine "Hinstr" "Hprog_done" as "Hprog_done".
            (* lea r_stk r_t1 *)
            iPrologue rest2 Hrest_length1 "Hprog". 
            assert ((stack_new_1 + (0 - 7))%a = Some a2) as Hpop1.
            { assert ((a3 + 1)%a = Some stack_own_b) as Hincr;[iContiguous_next Hcont1 2|].
              assert ((a2 + 1)%a = Some a3) as Hincr';[iContiguous_next Hcont1 1|].
              revert Hstack_own_bound1' Hincr Hincr' Hstack_new_1. clear. solve_addr. }
            iApply (wp_lea_success_reg with "[$HPC $Hr_t1 $Hr_stk $Hinstr]");
              [apply decode_encode_instrW_inv|apply Hfl|iCorrectPC a27 a_last|
               iContiguous_next Hcont_rest2 2|apply Hpop1|auto..].
            { simpl; auto. }
            iEpilogue "(HPC & Hinstr & Hr_t1 & Hr_stk)". iCombine "Hinstr" "Hprog_done" as "Hprog_done". 
            (* pop r_stk r_t0 *)
            do 3 (destruct rest2; [inversion Hrest_length1|]).
            iDestruct (big_sepL2_app_inv _ [a30;a31;a32] (a33::rest2) with "Hprog") as "[Hpop Hprog]";[simpl;auto|].
            clear Hpop1. assert ((a2 + (0 - 1))%a = Some a0) as Hpop1.
            { rewrite -(addr_add_assoc a0 _ 1);[apply addr_add_0|iContiguous_next Hcont1 0]. }
            iApply (pop_spec); [..|iFrame "HPC Hr_stk Hr_t1 Hpop Hr_t0 Ha3"];
              [split;[|split];iCorrectPC a27 a_last|apply Hfl|iContiguous_bounds_withinBounds a0 stack_own_last|auto|iContiguous_next Hcont_rest2 3|iContiguous_next Hcont_rest2 4|iContiguous_next Hcont_rest2 5|apply Hpop1|].
            iNext. iIntros "(HPC & Hpop & Hr_t0 & Ha3 & Hr_stk & Hr_t1)". iCombine "Hpop" "Hprog_done" as "Hprog_done".
            (* pop r_stk r_env *)
            do 3 (destruct rest2; [inversion Hrest_length1|]).
            iDestruct (big_sepL2_app_inv _ [a33;a34;a35] (a36::rest2) with "Hprog") as "[Hpop Hprog]";[simpl;auto|].
            clear Hpop1. assert ((a0 + (0 - 1))%a = Some b_r') as Hpop1.
            { revert Hb_r'. clear. solve_addr. }
            iApply (pop_spec); [..|iFrame "HPC Hr_stk Hr_t1 Hpop Hr_env Ha2"];
              [split;[|split];iCorrectPC a27 a_last|apply Hfl|iContiguous_bounds_withinBounds a0 stack_own_last|auto|iContiguous_next Hcont_rest2 6|iContiguous_next Hcont_rest2 7|iContiguous_next Hcont_rest2 8|apply Hpop1|].
            iNext. iIntros "(HPC & Hpop & Hr_env & Ha2 & Hr_stk & Hr_t1)". iCombine "Hpop" "Hprog_done" as "Hprog_done".
            (* we have now arrived at the final load of the environment. we must here assert that the loaded
               value is indeed 1. We are able to show this since W6 is a public future world of W5, in which 
               invariant i is in state true *)
            (* load r_adv r_env *)
            iPrologue rest2 Hrest_length1 "Hprog".
            iAssert (∀ φ, ▷ (PC ↦ᵣ inr (pc_p, pc_g, pc_b, pc_e, a37)
                                ∗ r_env ↦ᵣ inr (RWX, Global, d, d', d)
                                ∗ a36 ↦ₐ[pc_p'] load_r r_adv r_env
                                ∗ sts_full_world W6
                                ∗ r_adv ↦ᵣ inl 1%Z
                                -∗ WP Seq (Instr Executable) {{ v, φ v }})
                            -∗ WP Instr Executable {{ v, WP fill [SeqCtx] (of_val v) {{ v, φ v }} }})%I
              with "[HPC Hinstr Hr_env Hr_adv Hsts]" as "Hload_step".
            { iIntros (φ') "Hφ'".
              iInv ι as (x) "[>Hstate Hb]" "Hcls".
              iDestruct (sts_full_state_loc with "Hsts Hstate") as %Hi.
              assert (x = true) as ->.
              { apply related_pub_lookup_local with W5 W6 i;auto. repeat rewrite std_update_multiple_loc_sta.
                apply lookup_insert. }
              iDestruct "Hb" as ">Hb".
              iAssert (⌜(d =? a36)%a = false⌝)%I as %Hne.
              { destruct (d =? a36)%a eqn:Heq;auto. apply Z.eqb_eq,z_of_eq in Heq. rewrite Heq.
                iDestruct (cap_duplicate_false with "[$Hinstr $Hb]") as "Hfalse";[|done].
                eapply isCorrectPC_contiguous_range with (a := a) in Hvpc;[|eauto|];last (by apply elem_of_cons;left). 
                destruct pc_p,pc_p';inversion Hfl;auto.
                inversion Hvpc as [?????? [Hcontr | [Hcontr | Hcontr] ] ];inversion Hfl;inversion Hcontr. }
              iApply (wp_load_success with "[$HPC $Hinstr $Hr_adv $Hr_env Hb]");
                [apply decode_encode_instrW_inv|apply Hfl|iCorrectPC a27 a_last
                 |auto|iContiguous_next Hcont_rest2 9|rewrite Hne;iFrame;iPureIntro;apply PermFlows_refl|rewrite Hne].
              iNext. iIntros "(HPC & Hr_adv & Ha36 & Hr_env & Hd)".
              iMod ("Hcls" with "[Hstate Hd]") as "_".
              { iNext. iExists true. iFrame. }
              iModIntro. iApply wp_pure_step_later;auto;iNext.
              iApply "Hφ'". iFrame. 
            }
            iApply "Hload_step".
            iNext. iIntros "(HPC & Hr_env & Ha36 & Hsts & Hr_adv)".
            (* We can now assert that r_adv indeed points to 1 *)
            assert (contiguous_between (a37 :: rest2) a37 a_last) as Hcont_rest2_weak.
            { apply contiguous_between_incr_addr with (i:=10) (ai:=a37) in Hcont_rest2 as Hincr;auto. 
              eapply (contiguous_between_app _ [a27;a28;a29;a30;a31;a32;a33;a34;a35;a36] (a37 :: rest2) _ _ a37)
                in Hcont_rest2 as [_ Hcont_rest2];eauto. }
            iDestruct (contiguous_between_program_split with "Hprog") as (assert_prog rest3 link3)
                                                                   "(Hfetch & Hprog & #Hcont)";[apply Hcont_rest2_weak|].
            iDestruct "Hcont" as %(Hcont_assert & Hcont_rest3 & Heqapp3 & Hlink3).
            iGet_genpur_reg_map r3 r_t3 "Hmreg'" "Hfull3" "[Hr_t3 Hmreg']".
            iMod (na_inv_acc with "Htable Hna") as "[ [>Hpc_b >Ha_entry] [Hna Hcls] ]";[revert Hιne;clear;solve_ndisj..|].
            iApply (assert_r_z_success with "[-]");[..|iFrame "HPC Hpc_b Ha_entry Hfetch Hr_adv"];
              [|apply Hfl|apply Hcont_assert|auto|auto|auto|..].
            { intros mid Hmid. apply isCorrectPC_inrange with a27 a_last; auto.
              apply contiguous_between_bounds in Hcont_rest2_weak.
              apply contiguous_between_incr_addr with (i:=10) (ai:=a37) in Hcont_rest2 as Hincr;auto. 
              apply contiguous_between_bounds in Hcont_rest3.              
              revert Hincr Hcont_rest3 Hcont_rest2_weak Hmid; clear. intros. solve_addr. }
            iSplitL "Hr_t1";[iExists _;iFrame|].
            iSplitL "Hr_t2";[iExists _;iFrame|].
            iSplitL "Hr_t3";[iExists _;iFrame|].
            iNext. iIntros "(Hr_t1 & Hr_t2 & Hr_t3 & Hr_adv & HPC & Hassert & Hpc_b & Ha_entry)".
            iMod ("Hcls" with "[$Hna $Hpc_b $Ha_entry]") as "Hna". 
            iDestruct (big_sepL2_length with "Hprog") as %Hrest_length2.
            iDestruct (big_sepL2_length with "Hassert") as %Hassert_length.
            assert (isCorrectPC_range pc_p pc_g pc_b pc_e link3 a_last) as Hvpc3.
            { intros mid Hmid. apply isCorrectPC_inrange with a27 a_last; auto.
              apply contiguous_between_incr_addr with (i:=10) (ai:=a37) in Hcont_rest2 as Hincr;auto.
              revert Hincr Hassert_length Hlink3 Hmid; clear. intros. solve_addr. }
            (* Since the assertion succeeded, we are now ready to jump back to the adv who called us *)
            (* Before we can return to the adversary, we must clear the local stack frame and registers. This will 
               allow us to release the local frame, and show we are in a public future world by reinstating 
               the full stack invariant *)
            (* we must prepare the stack capability so that we only clear the local stack frame *)
            (* getb r_t1 r_stk *)
            destruct rest3;[inversion Hrest_length2|].
            apply contiguous_between_cons_inv_first in Hcont_rest3 as Heq. subst link3. 
            iPrologue rest3 Hrest_length2 "Hprog".            
            iApply (wp_Get_success with "[$HPC $Hinstr $Hr_stk $Hr_t1]");
              [apply decode_encode_instrW_inv|auto|apply Hfl|iCorrectPC a38 a_last|iContiguous_next Hcont_rest3 0|auto..].
            iEpilogue "(HPC & Hinstr & Hr_stk & Hr_t1)"; iSimpl in "Hr_t1"; iCombine "Hinstr" "Hprog_done" as "Hprog_done".
            (* add_r_z r_t2 r_t1 8 *)
            iPrologue rest3 Hrest_length2 "Hprog".
            iApply (wp_add_sub_lt_success_r_z with "[$HPC $Hinstr $Hr_t1 $Hr_t2]");
              [apply decode_encode_instrW_inv|by left|iContiguous_next Hcont_rest3 1|apply Hfl|iCorrectPC a38 a_last|..].
            iEpilogue "(HPC & Hinstr & Hr_t1 & Hr_t2)"; iSimpl in "Hr_t2"; iCombine "Hinstr" "Hprog_done" as "Hprog_done". 
            (* subseg r_stk r_t1 r_t2 *)
            assert (z_to_addr a0 = Some a0) as Ha2.
            { rewrite /z_to_addr /=. clear. 
              destruct (Z_le_dec a0 MemNum),(Z_le_dec 0 a0);destruct a0;
                [f_equiv;by apply z_of_eq|zify_addr;apply Zle_bool_imp_le in pos..]. 
              lia. apply Zle_bool_imp_le in fin. lia. lia.               
            }
            assert ((a0 + 10)%a = Some stack_own_end) as Ha2_stack_own_end.
            { assert ((a0 + 3)%a = Some stack_own_b) as Ha2_stack_own_b.
              { apply (contiguous_between_incr_addr _ 3 _ stack_own_b) in Hcont1; auto. }
              revert Ha2_stack_own_b Hstack_own_bound'. 
              clear; intros. solve_addr. }
            assert (z_to_addr (a0 + 10)%Z = Some stack_own_end) as Ha2_stack_own_end'.
            { (* fixme: very tedious *)
              revert Ha2_stack_own_end;clear. intros.
              destruct stack_own_end;simpl.
              rewrite /z_to_addr.
              zify_addr; subst;
              try solve_addr_close_proof. 
              destruct (Z_le_dec (z1 + 10)%Z MemNum);try lia. 
              destruct (Z_le_dec 0 (z1 + 10)%Z); try lia.
              destruct (Z.leb_le (z1 + 10) MemNum); try lia. 
              destruct (Z.leb_le 0 (z1 + 10)); try lia.
              repeat f_equal; apply eq_proofs_unicity; decide equality.
            }
            iPrologue rest3 Hrest_length2 "Hprog".
            iApply (wp_subseg_success with "[$HPC $Hinstr $Hr_stk $Hr_t1 $Hr_t2]");
              [apply decode_encode_instrW_inv|apply Hfl|iCorrectPC a38 a_last|
               split;[apply Ha2|apply Ha2_stack_own_end']|
               auto|auto| |iContiguous_next Hcont_rest3 2|..].
            { rewrite !andb_true_iff !Z.leb_le. apply withinBounds_le_addr in Hwb2.
              assert ((a0 + 3)%a = Some stack_own_b) as Ha2_stack_own_b.
              { apply (contiguous_between_incr_addr _ 3 _ stack_own_b) in Hcont1; auto. }
              revert Hstack_own_bound Hwb2 Ha2_stack_own_end Ha2_stack_own_b.
              clear. repeat split; try lia; try solve_addr. }
            iEpilogue "(HPC & Hinstr & Hr_t1 & Hr_t2 & Hr_stk)". iCombine "Hinstr" "Hprog_done" as "Hprog_done".
            iAssert ([[a0,stack_own_end]]↦ₐ[RWLX][[l_frame2]])%I with "[Hframe Ha2 Ha3]" as "Hstack".
            { iApply region_mapsto_cons;[iContiguous_next Hcont1 0|..].
              { apply contiguous_between_middle_bounds with (i:=1) (ai:=a2) in Hcont1;auto.
                revert Hstack_own_bound Hstack_own_bound' Hcont1;clear. solve_addr. }
              iFrame.
              iApply region_mapsto_cons;[iContiguous_next Hcont1 1|..].
              { apply contiguous_between_middle_bounds with (i:=2) (ai:=a3) in Hcont1;auto.
                revert Hstack_own_bound Hstack_own_bound' Hcont1;clear. solve_addr. }
              iFrame. 
            }
            (* We are now ready to clear the stack *)
            assert (contiguous_between (a41 :: rest3) a41 a_last) as Hcont_weak.
            { repeat (inversion Hcont_rest3 as [|????? Hcont_rest2']; subst; auto; clear Hcont_rest3; rename Hcont_rest2' into Hcont_rest3). }
            iDestruct (contiguous_between_program_split with "Hprog") as (mclear_addrs rclear_addrs rclear_first)
                                                                           "(Hmclear & Hrclear & #Hcont)"; [eauto|].
            iDestruct "Hcont" as %(Hcont_mclear & Hcont_rest4 & Hstack_eq2 & Hlink4).
            iDestruct (big_sepL2_length with "Hmclear") as %Hmclear_length.
            assert (7 < (length mclear_addrs)) as Hlt7;[rewrite Hmclear_length /=;clear;lia|].
            assert (17 < (length mclear_addrs)) as Hlt17;[rewrite Hmclear_length /=;clear;lia|].
            apply lookup_lt_is_Some_2 in Hlt7 as [ai Hai].
            apply lookup_lt_is_Some_2 in Hlt17 as [aj Haj].
            assert (ai + 10 = Some aj)%a.
            { rewrite (_: 10%Z = Z.of_nat (10 : nat)).
              eapply contiguous_between_incr_addr_middle; [eapply Hcont_mclear|..]. all: eauto. }
            assert (a41 < rclear_first)%a as Hcontlt2.
            { revert Hmclear_length Hlink4. clear. solve_addr. }
            assert (a27 <= a41)%a as Hcontge2.
            { apply region_addrs_of_contiguous_between in Hcont_scall1. subst. 
              revert Hscall_length1 Hcont_rest2 Hcontlt1 Hcontlt2 Hassert_length. rewrite Heqapp3.
              clear =>Hscall_length Hf2 Hcontlt Hcontlt2 Hassert_length.
              apply contiguous_between_middle_bounds with (i := 26) (ai := a41) in Hf2;[solve_addr|auto].
              simpl in *. assert (16 = 13 + 3) as ->;[lia|]. rewrite lookup_app_r;[|lia].
              by rewrite Hassert_length /=.
            }
            iGet_genpur_reg_map r3 r_t4 "Hmreg'" "Hfull3" "[Hr_t4 Hmreg']".
            iGet_genpur_reg_map r3 r_t5 "Hmreg'" "Hfull3" "[Hr_t5 Hmreg']".
            iGet_genpur_reg_map r3 r_t6 "Hmreg'" "Hfull3" "[Hr_t6 Hmreg']".
            iApply (mclear_spec with "[- $HPC $Hr_stk $Hstack $Hr_t1 $Hr_t2 $Hr_t3 $Hr_t4 $Hr_t5 $Hr_t6]");
              [apply Hcont_mclear|..]; eauto.
            { assert (rclear_first <= a_last)%a as Hle;[by apply contiguous_between_bounds in Hcont_rest4|].
              intros mid Hmid. apply isCorrectPC_inrange with link0 a_last; auto.
              revert Hle Hcontlt1 Hcontge1 Hcontlt Hcontge Hmid Hcontlt2 Hcontge2. clear; intros. split; try solve_addr.
            }
            { apply withinBounds_le_addr in Hwb3 as [? _]. auto. }
            rewrite /mclear.
            destruct (strings.length mclear_addrs =? strings.length (mclear_instrs r_stk))%nat eqn:Hcontr;
              [|rewrite Hmclear_length in Hcontr;inversion Hcontr].
            iFrame "Hmclear".
            iNext. iIntros "(HPC & Hr_t1 & Hr_t2' & Hr_t3 & Hr_t4 & Hr_t5 & Hr_t6 & Hr_stk & Hstack & Hmclear)".
            (* insert general purpose registers back into map *)
            repeat (rewrite -(delete_commute _ r_t2)).
            iClose_genpur_reg_map r_t2 "[Hr_t2' $Hmreg']" "Hmreg'".
            rewrite delete_insert_delete.
            repeat (rewrite -(delete_insert_ne _ _ r_t2); [|auto]).
            iClose_genpur_reg_map r_t6 "[Hr_t6 $Hmreg']" "Hmreg'".
            repeat (rewrite -(delete_insert_ne _ _ r_t6); [|auto]).
            iClose_genpur_reg_map r_t5 "[Hr_t5 $Hmreg']" "Hmreg'".
            repeat (rewrite -(delete_insert_ne _ _ r_t5); [|auto]).
            iClose_genpur_reg_map r_t4 "[Hr_t4 $Hmreg']" "Hmreg'".
            repeat (rewrite -(delete_insert_ne _ _ r_t4); [|auto]).
            iClose_genpur_reg_map r_t3 "[Hr_t3 $Hmreg']" "Hmreg'".
            repeat (rewrite -(delete_insert_ne _ _ r_t3); [|auto]).
            repeat (rewrite -(delete_commute _ r_t1)). 
            iClose_genpur_reg_map r_t1 "[Hr_t1 $Hmreg']" "Hmreg'".
            repeat (rewrite -(delete_insert_ne _ _ r_t1); [|auto]).
            repeat (rewrite -(delete_commute _ r_env)). 
            iClose_genpur_reg_map r_env "[Hr_env $Hmreg']" "Hmreg'".
            repeat (rewrite -(delete_insert_ne _ _ r_env); [|auto]).
            repeat (rewrite -(delete_commute _ r_adv)). 
            iClose_genpur_reg_map r_adv "[Hr_adv $Hmreg']" "Hmreg'".
            repeat (rewrite -(delete_insert_ne _ _ r_adv); [|auto]).
            repeat (rewrite -(delete_commute _ r_stk)). 
            iClose_genpur_reg_map r_stk "[Hr_stk $Hmreg']" "Hmreg'".
            repeat (rewrite -(delete_insert_ne _ _ r_stk); [|auto]).

            (* We are now ready to clear the registers *)
            iDestruct (big_sepL2_length with "Hrclear") as %Hrclear_length. 
            destruct rclear_addrs;[inversion Hrclear_length|].
            apply contiguous_between_cons_inv_first in Hcont_rest4 as Heq. subst rclear_first.
            iDestruct (contiguous_between_program_split with "Hrclear") as (rclear jmp_addrs jmp_addr)
                                                                           "(Hrclear & Hjmp & #Hcont)"; [eauto|].
            iDestruct "Hcont" as %(Hcont_rclear & Hcont_rest5 & Hstack_eq3 & Hlink5).
            clear Hrclear_length. iDestruct (big_sepL2_length with "Hrclear") as %Hrclear_length.
            assert (a42 < jmp_addr)%a as Hcontlt3.
            { revert Hrclear_length Hlink5. clear. rewrite /all_registers /=. solve_addr. }
            iAssert (⌜dom (gset RegName) r3 = all_registers_s⌝)%I as %Hdom_r3.
            { iDestruct "Hfull3" as %Hfull3. iPureIntro. apply (anti_symm _); [apply all_registers_subseteq|].
              rewrite elem_of_subseteq. intros ? _. rewrite -elem_of_gmap_dom. apply Hfull3. }
            iApply (rclear_spec with "[- $HPC $Hrclear $Hmreg']").
            { eauto. }
            { apply not_elem_of_list; apply elem_of_cons; by left. }
            { destruct rclear; inversion Hcont_rclear; eauto. inversion Hrclear_length. }
            { assert (jmp_addr <= a_last)%a as Hle;[by apply contiguous_between_bounds in Hcont_rest5|].
              intros mid Hmid. apply isCorrectPC_inrange with link0 a_last; auto.
              revert Hle Hcontlt1 Hcontge1 Hcontlt Hcontge Hmid Hcontlt2 Hcontge2 Hcontlt3. clear; intros. split; solve_addr.
            }
            { apply Hfl. }
            { rewrite list_to_set_difference -/all_registers_s.
              repeat rewrite ?dom_delete_L ?dom_insert_L. rewrite Hdom_r3.
              rewrite !all_registers_union_l !difference_difference_L. f_equal. clear. set_solver. }
            iNext. iIntros "(HPC & Hmreg' & Hrclear)".

            (* we must now invoke the callback validity of the adversary. This means we must show we 
               are currently in a public future world of W *)
            assert (related_sts_pub_world W (std_update_multiple W6 (elements (dom (gset Addr) m_static2)) Temporary))
              as Hrelated7.
            { eapply related_pub_local_3 with (b:=a0) (l1:=l') (l2:=l'');
                [..|apply Hrelated3|apply Hrelated6]; eauto; simpl; auto.
              - revert Hwb2 Hwb3. clear. intros Hwb2 Hwb3.
                apply withinBounds_le_addr in Hwb2.
                apply withinBounds_le_addr in Hwb3. solve_addr.
              - repeat split;auto.
                rewrite lists_to_static_region_dom. rewrite elements_list_to_set;auto. apply Permutation_app_comm. 
                repeat rewrite app_length. rewrite Hlength_rest;auto.
                rewrite lists_to_static_region_dom. rewrite elements_list_to_set;auto.
                rewrite /static2_addrs Permutation_app_comm app_assoc. auto.
                repeat rewrite app_length. rewrite Hlength_rest Hlength_rest'';auto.
            }
            (* in order to handle the leftovers from the revocation of W3, we must also show that the final world 
               is a public future world of W3 *)
            assert (related_sts_pub_world W3 (std_update_multiple W6 (elements (dom (gset Addr) m_static2)) Temporary))
              as Hrelated8.
            { eapply related_pub_local_4 with (b:=a0) (l1:=l') (l2:=l'');
                [..|apply Hrelated3|apply Hrelated6]; eauto; simpl; auto.
              - revert Hwb2 Hwb3. clear. intros Hwb2 Hwb3.
                apply withinBounds_le_addr in Hwb2.
                apply withinBounds_le_addr in Hwb3. solve_addr.
              - repeat split;auto.
                rewrite lists_to_static_region_dom. rewrite elements_list_to_set;auto. apply Permutation_app_comm. 
                repeat rewrite app_length. rewrite Hlength_rest;auto.
                rewrite lists_to_static_region_dom. rewrite elements_list_to_set;auto.
                rewrite /static2_addrs Permutation_app_comm app_assoc. auto.
                repeat rewrite app_length. rewrite Hlength_rest Hlength_rest'';auto.
            } 

            (* We use the fact that the final world is public to W and W3 to close the full static frame *)
            iMod (region_close_static_to_temporary_alt m_static2 with "[$Hr $Hsts Hstack Hrest $Hstates]") as "[Hsts Hr]". 
            { set ψ := ((λ a v, ∃ (p' : Perm) (φ0 : WORLD * Word → iPropI Σ),
                                ⌜∀ Wv : WORLD * Word, Persistent (φ0 Wv)⌝
                                  ∗ temp_resources
                                      (std_update_multiple W6 (elements (dom (gset Addr) m_static2)) Temporary) φ0 a p'
                                      ∗ rel a p' φ0))%I.
              iApply (big_sepL2_to_static_region _ _ ψ)%I;[auto|..]. 
              { iModIntro. iIntros (k a'' pw Hpw1 Hpw2) "Hr". iFrame "Hr". }
              iApply (big_sepL2_app with "[Hstack]").
              - iDestruct (region_addrs_zeroes_trans with "Hstack") as "Hstack".
                rewrite (region_addrs_split _ stack_own_end).
                iDestruct (big_sepL_app with "Hstack_region") as "[Hstack_val_frame _]".
                iDestruct (big_sepL_sep with "[Hstack_val_frame Hstack]") as "Hstack".
                iSplitL;[iFrame "Hstack"|iFrame "Hstack_val_frame"]. 
                iDestruct (big_sepL2_to_big_sepL_l _ _ l_frame2 with "Hstack") as "Hstack";[auto|].
                iApply (big_sepL2_mono with "Hstack"). 
                iIntros (k a'' _v Hy1 Yy2) "[Ha' [Hrel _] ]".
                iExists RWLX,(λ Wv : WORLD * Word, ((fixpoint interp1) Wv.1) Wv.2).
                iSplit;[iPureIntro;apply _|]. iSplit;[auto|]. iFrame. iExists (inl 0%Z). iSimpl.
                iSplit;[auto|]. iFrame. iSplit.
                { iModIntro. iIntros (W0 W'). iApply interp_monotone. }
                rewrite fixpoint_interp1_eq /=. auto. iFrame. 
                apply withinBounds_le_addr in Hwb3 as [Hb1 Hb2].
                revert Hb1 Hb2;clear. solve_addr.
              - iDestruct (big_sepL2_app' with "Hrest") as "[Hrest Hrest']";[auto|].
                iDestruct (big_sepL2_sep with "[Hrest]") as "Hrest".
                { iSplitL;[iFrame "Hrest"|iFrame "Hrest_valid"]. }
                iDestruct (big_sepL2_sep with "[Hrest']") as "Hrest'".
                { iSplitL;[iFrame "Hrest'"|iFrame "Hrest_valid'"]. }
                iApply (big_sepL2_app with "[Hrest]").
                + iApply (big_sepL2_mono with "Hrest").
                  iIntros (k a'' pw Ha' Hpw) "[Ha' Hr]".
                  iDestruct "Hr" as (p0 φ0 Hpers Hne) "(Hφ & #Hrel & mono)".
                  iDestruct "Ha'" as (p1 φ1) "[#Hrel' Ha'']". 
                  rewrite /ψ. simpl.
                  iDestruct (rel_agree _ p0 p1 with "[$Hrel $Hrel']") as "[% _]". subst p0. 
                  iExists p1,φ0.
                  repeat iSplit;auto. iExists pw. destruct (pwl p1).
                  { iDestruct "mono" as "#mono".
                    iAssert (φ0 (std_update_multiple W6 (elements (dom (gset Addr) m_static2)) Temporary, pw))
                      with "[Hφ]" as "Hφ".
                    { iApply ("mono" with "[] Hφ"). auto. }
                    iFrame "∗ #". auto. }
                  { iDestruct "mono" as "#mono".
                    iAssert (φ0 (std_update_multiple W6 (elements (dom (gset Addr) m_static2)) Temporary, pw))
                      with "[Hφ]" as "Hφ".
                    { iApply ("mono" with "[] Hφ"). iPureIntro. apply related_sts_pub_priv_world. auto. }
                    iFrame "∗ #". auto. }
                + iApply (big_sepL2_mono with "Hrest'").
                  iIntros (k a'' pw Ha' Hpw) "[Ha' Hr]".
                  iDestruct "Hr" as (p0 φ0 Hpers Hne) "(Hφ & #Hrel & mono)".
                  iDestruct "Ha'" as (p1 φ1) "[#Hrel' Ha'']".
                  iDestruct (rel_agree _ p0 p1 with "[$Hrel $Hrel']") as "[% _]". subst p1. 
                  rewrite /ψ. simpl. iExists p0,φ0.
                  repeat iSplit;auto. iExists pw. destruct (pwl p0).
                  { iDestruct "mono" as "#mono".
                    iAssert (φ0 (std_update_multiple W6 (elements (dom (gset Addr) m_static2)) Temporary, pw))
                      with "[Hφ]" as "Hφ".
                    { iApply ("mono" with "[] Hφ"). auto. }
                    iFrame "∗ #". auto. }
                  { iDestruct "mono" as "#mono".
                    iAssert (φ0 (std_update_multiple W6 (elements (dom (gset Addr) m_static2)) Temporary, pw))
                      with "[Hφ]" as "Hφ".
                    { iApply ("mono" with "[] Hφ"). iPureIntro. apply related_sts_pub_priv_world. auto. }
                    iFrame "∗ #". auto. }
            }

            (* we can finish reasoning about the program *)
            rewrite /enter_cond /interp_expr /interp_conf. iSimpl in "Hcallback".
            (* again we want to use the jump of fail pattern when jumping to unknown capabilities *)
            iAssert (interp W wret) as "#Hcallback'";[|iClear "Hcallback"].
            { rewrite fixpoint_interp1_eq. iFrame "Hcallback". }
            iDestruct (jmp_or_fail_spec with "Hcallback'") as "Hcallback_now".

            (* We can now finally jump to the return capability *)
            (* jmp r_t0 *)
            iDestruct (big_sepL2_length with "Hjmp") as %Hjmp_length.
            destruct jmp_addrs; [inversion Hjmp_length|].
            destruct jmp_addrs; [|inversion Hjmp_length].
            apply contiguous_between_cons_inv_first in Hcont_rest5 as Heq; subst jmp_addr.
            iDestruct "Hjmp" as "[Hinstr _]". iApply (wp_bind (fill [SeqCtx])).
            iApply (wp_jmp_success with "[$HPC $Hinstr $Hr_t0]");
              [apply decode_encode_instrW_inv|apply Hfl|..].
            { (* apply contiguous_between_bounds in Hcont_rest3 as Hle. *)
              inversion Hcont_rest5 as [| a'' b' c' l3 Hnext Hcont_rest6 Heq Hnil Heq'].
              inversion Hcont_rest6; subst. 
              apply Hvpc2. revert Hcontge2 Hcontlt2 Hcontlt3 Hnext. clear. solve_addr. }

            destruct (decide (isCorrectPC (updatePcPerm wret))).
            2: { iEpilogue "(HPC & Hinstr & Hrt0)". iApply "Hcallback_now". iFrame. iIntros (Hcontr'). done. }
            
            iDestruct "Hcallback_now" as (p_ret g_ret b_ret e_ret a_ret Heqret) "Hcallback_now". simplify_eq. 
            iAssert (future_world g_ret W (std_update_multiple W6 (elements (dom (gset Addr) m_static2)) Temporary))%I
              as "#Hfuture". 
            { destruct g_ret; iSimpl.
              - iPureIntro. apply related_sts_pub_priv_world. apply Hrelated7.
              - iPureIntro. apply Hrelated7.
            }
            set r4 : gmap RegName Word :=
              <[PC := inl 0%Z]>
              (<[r_t0 := inr (p_ret, g_ret, b_ret, e_ret, a_ret)]>
              (create_gmap_default
                 (list_difference all_registers [PC; r_t0]) (inl 0%Z))).
            iDestruct ("Hcallback_now" $! r4 with "Hfuture") as "Hcallback_now'".
            
            iEpilogue "(HPC & Hinstr & Hrt0)". iCombine "Hinstr" "Hprog_done" as "Hprog_done". 

            
            (* We close the program Iris invariant *)
            iMod ("Hcls'" with "[$Hna Hprog_done Hassert Hmclear Hrclear Ha36]") as "Hna". 
            { iNext. iDestruct "Hprog_done" as "(Ha43 & Ha40 & Ha39 & Ha38 & 
                                                 Hpop2 & Hpop1 & Ha29 & Ha28 & Ha27 & Hprog_done)".
              iApply (big_sepL2_app with "Hprog_done [-]").
              iFrame "Ha27 Ha28 Ha29". 
              iApply (big_sepL2_app with "Hpop1 [-]").
              iApply (big_sepL2_app with "Hpop2 [-]").
              iFrame "Ha36". rewrite Heqapp3 Hstack_eq2 Hstack_eq3.
              iApply (big_sepL2_app with "Hassert [-]").
              iFrame "Ha38 Ha39 Ha40". 
              iApply (big_sepL2_app with "Hmclear [-]").
              iApply (big_sepL2_app with "Hrclear [-]").
              iFrame. done.
            } 
            iClear "Hf4 full Hfull' Hfull2 Hreg'".
            iSimpl in "HPC".
            
            (* we apply the callback to the current configuration *)
            iSpecialize ("Hcallback_now'" with "[Hsts Hr Hmreg' HPC Hrt0 Hna]"). 
            { iFrame "Hna Hr Hsts". iSplitR;[iSplit|].
              - iPureIntro. clear. 
                intros x. rewrite /= /r4.
                destruct (decide (PC = x));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
                destruct (decide (r_t0 = x));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
                exists (inl 0%Z). apply create_gmap_default_lookup.
                apply elem_of_list_difference. split;[apply all_registers_correct|].
                repeat (apply not_elem_of_cons; split;[auto|try apply not_elem_of_nil]).
              - iIntros (r0 Hne). rewrite /RegLocate.
                rewrite /r4 lookup_insert_ne;auto.
                destruct (decide (r_t0 = r0));[subst;rewrite lookup_insert|].
                + iApply (interp_monotone $! Hrelated7).
                  rewrite /interp fixpoint_interp1_eq. iFrame "Hcallback'". 
                + rewrite lookup_insert_ne;[|auto]. 
                  assert (r0 ∈ (list_difference all_registers [PC; r_t0])) as Hin.
                  { apply elem_of_list_difference. split;[apply all_registers_correct|].
                    repeat (apply not_elem_of_cons; split;[auto|try apply not_elem_of_nil]). }
                  rewrite !fixpoint_interp1_eq. iRevert (Hin).
                  rewrite (create_gmap_default_lookup _ (inl 0%Z : Word) r0).
                  iIntros (Hin). rewrite Hin. iSimpl. done. 
              - rewrite /registers_mapsto /r4 insert_insert.
                do 2 (rewrite big_sepM_insert; [|done]). iFrame.
                iApply (big_sepM_mono (λ k _, k ↦ᵣ inl 0%Z))%I.
                { intros ? ? [? ->]%create_gmap_default_lookup_is_Some. auto. }
                iDestruct (big_sepM_dom with "Hmreg'") as "Hmreg'". iApply big_sepM_dom.
                rewrite big_opS_proper'. iApply "Hmreg'". done.
                rewrite create_gmap_default_dom list_to_set_difference -/all_registers_s.
                repeat rewrite ?dom_delete_L ?dom_insert_L. rewrite Hdom_r3.
                rewrite !all_registers_union_l !difference_difference_L. f_equal. clear. set_solver.
            }
            iDestruct "Hcallback_now'" as "[_ Hcallback_now']".
            iApply wp_wand_l. iFrame "Hcallback_now'". 
            iIntros (v) "Hv". 
            iIntros (halted). 
            iDestruct ("Hv" $! halted) as (r0 W0) "(#Hfull & Hmreg' & #Hrelated & Hna & Hsts & Hr)". 
            iDestruct ("Hrelated") as %Hrelated10.
            iExists r0,W0. iFrame "Hfull Hmreg' Hsts Hr Hna".
            iPureIntro. 
            eapply related_sts_priv_trans_world;[|apply Hrelated10].
            apply related_sts_pub_priv_world. 
            apply related_sts_pub_world_static_to_temporary with (m:=m_static2);auto.
            apply Forall_forall. intros a'' Hin. apply elem_of_elements in Hin. apply Hall_static' in Hin.
            rewrite /static in Hin. destruct (W6.1 !! a'') eqn:Hsome;[|done].
            subst. auto. 
          - iAssert (interp W (inr (p, Global, b, e, a'))) as "#Hadv_val'";[|iClear "Hadv_val"].
            { rewrite fixpoint_interp1_eq. iFrame "Hadv_val". }
            rewrite Hr_t30. 
            assert (r2 !! r_adv = Some (inr (p, Global, b, e, a'))) as Hr_t30_some; auto. 
            rewrite /RegLocate Hr_t30_some. 
            iIntros (_).
            iApply (interp_monotone_nl with "[] [] Hadv_val'");[iPureIntro|auto].
            apply related_sts_priv_trans_world with W''; auto.
            eapply related_sts_priv_trans_world;[apply related_sts_pub_priv_world;apply Hrelated3|].
            apply related_sts_priv_trans_world with W5; auto.
            apply related_sts_priv_refl_world. 
          - rewrite r_zero; auto.
            repeat rewrite fixpoint_interp1_eq. iPureIntro. auto.
        }
        iDestruct ("Hadv_contW5" with "[$Hsts $Hr $Hna $Hfull2 $Hmaps $Hreg]")
          as "[_ Ho]".
        iApply wp_wand_r. iFrame.
        iIntros (v) "Hhalted".
        iIntros (->).
        iSpecialize ("Hhalted" with "[]");[auto|].
        iDestruct "Hhalted" as (r0 W6) "(Hr0 & Hregr0 & % & Hna & Hsts)".
        iExists _,_. iFrame.
        iPureIntro. eapply related_sts_priv_trans_world;[apply Hrelated5|auto].
      - rewrite Hr_t30. 
        assert (r !! r_adv = Some (inr (p, Global, b, e, a'))) as Hr_t30_some; auto. 
        rewrite /RegLocate Hr_t30_some. iSimpl. 
        iIntros (_). 
        iApply (interp_monotone_nl with "[] [] Hadv_val");[iPureIntro|auto].
        eapply related_sts_priv_trans_world;[apply HWW''|auto].
        apply related_sts_priv_refl_world. 
      - (* in this case we can infer that r1 points to 0, since it is in the list diff *)
        iIntros (Hne). 
        assert (r !r! r1 = inl 0%Z) as Hr1.
        { rewrite /RegLocate.
          destruct (r !! r1) eqn:Hsome; rewrite Hsome; last done. rewrite /r in Hsome. 
          do 4 (rewrite lookup_insert_ne in Hsome;auto). 
          assert (Some w2 = Some (inl 0%Z)) as Heq.
          { rewrite -Hsome. apply create_gmap_default_lookup.
            apply elem_of_list_difference. split; first apply all_registers_correct.
            repeat (apply not_elem_of_cons;split;auto).
            apply not_elem_of_nil. 
          }
            by inversion Heq. 
        }
        rewrite Hr1 !fixpoint_interp1_eq. auto. 
    }
    iAssert (((interp_reg interp) W'' r))%I as "#HvalR";[iSimpl;auto|]. 
    iSpecialize ("Hadv_contW''" with "[$HvalR $Hmaps Hsts $Hna $Hr]"); iFrame. 
    iDestruct "Hadv_contW''" as "[_ Ho]". 
    rewrite /interp_conf.
    iApply wp_wand_r. iFrame.
    iIntros (v) "Htest".
    iApply "Hφ". 
    iIntros (->). 
    iSpecialize ("Htest" with "[]");[auto|]. 
    iDestruct "Htest" as (r0 W6) "(Hr0 & Hregr0 & % & Hna & Hsts)". 
    iExists _,_. iFrame.
    iPureIntro. eapply related_sts_priv_trans_world;[apply HWW''|auto].
  Qed.

End awkward_example.
