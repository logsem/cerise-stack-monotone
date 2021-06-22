From iris.program_logic Require Import language.
From cap_machine Require Import simulation linking.
From cap_machine Require Import addr_reg.

Section Full_Abstraction.

  Variables S T: language.
  Variable b_stk e_stk: Addr.
  Variable Symbols: Type.
  Variable Symbols_eq_dec: EqDecision Symbols.
  Variable Symbols_countable: countable.Countable Symbols.
  Variable WordS WordT: Type.
  Variable can_address_onlyS: WordS -> gmap.gset Addr -> Prop.
  Variable pwlS is_globalS: WordS -> bool.
  Variable can_address_onlyT: WordT -> gmap.gset Addr -> Prop.
  Variable pwlT is_globalT: WordT -> bool.

  Definition componentS := component Symbols Symbols_eq_dec Symbols_countable WordS.
  Definition componentT := component Symbols Symbols_eq_dec Symbols_countable WordT.

  Variable initial_stateS: componentS -> cfg S.
  Variable initial_stateT: componentT -> cfg T.

  Definition Terminates `{L: language} (initial_state: cfg L) (v: language.val L) :=
    exists s, rtc erased_step initial_state s /\ final_state s v.

  Definition contextually_equivalentS (comp1 comp2: componentS) :=
    forall c p1 p2,
      is_context e_stk _ _ _ _ can_address_onlyS pwlS is_globalS c comp1 p1 ->
      is_context e_stk _ _ _ _ can_address_onlyS pwlS is_globalS c comp2 p2 ->
      (forall v, Terminates (initial_stateS p1) v <-> Terminates (initial_stateS p2) v).

  Definition contextually_equivalentT (comp1 comp2: componentT) :=
    forall c p1 p2,
      is_context e_stk _ _ _ _ can_address_onlyT pwlT is_globalT c comp1 p1 ->
      is_context e_stk _ _ _ _ can_address_onlyT pwlT is_globalT c comp2 p2 ->
      (forall v, Terminates (initial_stateT p1) v <-> Terminates (initial_stateT p2) v).

  Definition is_fully_abstract (compile: componentS -> componentT): Prop :=
    forall compS1 compS2,
      contextually_equivalentS compS1 compS2 <-> contextually_equivalentT (compile compS1) (compile compS2).

End Full_Abstraction.

From stdpp Require Import base gmap fin_maps list.
From cap_machine Require Import overlay_cap_lang_sim machine_parameters.
Ltac inv H := inversion H; clear H; subst.

Section Compile_fully_abstract.

  Variables b_stk e_stk: Addr.
  Variable stk_pos: (b_stk < e_stk)%a.
  Context `{MachineParameters}.

  (* Back translating base machine words to overlay words *)
  Definition backtranslate_word (w: machine_base.Word): base.Word :=
    match w with
    | inl n => inl n
    | inr c => inr (base.Regular c)
    end.

  (* Trivial back translation from base machine component to overlay component *)
  Definition decompile (c: cap_lang.machine_component): lang.overlay_component :=
    match c with
    | Lib _ _ _ _ (ms, imp, exp) => Lib _ _ _ _ (@fmap (gmap Addr) _ machine_base.Word base.Word backtranslate_word ms, imp, fmap backtranslate_word exp)
    | Main _ _ _ _ (ms, imp, exp) c_main => Main _ _ _ _ (@fmap (gmap Addr) _ machine_base.Word base.Word backtranslate_word ms, imp, fmap backtranslate_word exp) (backtranslate_word c_main)
    end.

  Lemma translate_backtranslate_word:
    forall w,
      translate_word (backtranslate_word w) = w.
  Proof. destruct w; reflexivity. Qed.

  Lemma backtranslate_translate_word:
    forall w,
      lang.is_global w = true ->
      backtranslate_word (translate_word w) = w.
  Proof. intros; destruct w; inv H0; simpl; [|destruct c; try discriminate]; auto. Qed.

  Lemma translate_backtranslate_map K `(EqDecision K) `(Countable K):
    forall (m: gmap K machine_base.Word),
      translate_word ∘ backtranslate_word <$> m = m.
  Proof.
    intros; eapply map_eq; intros.
    rewrite lookup_fmap. destruct (m !! i) as [w|] eqn:Hw; simpl; auto.
    rewrite translate_backtranslate_word; auto.
  Qed.

  Lemma backtranslate_translate_map K `(EqDecision K) `(Countable K):
    forall (m: gmap K base.Word),
    (forall a w, m !! a = Some w -> lang.is_global w = true) ->
    backtranslate_word ∘ translate_word <$> m = m.
  Proof.
    intros; eapply map_eq; intros.
    rewrite lookup_fmap. destruct (m !! i) as [w|] eqn:Hw; simpl; auto.
    eapply H1 in Hw. erewrite backtranslate_translate_word; eauto.
  Qed.

  Lemma compile_decompile:
    forall comp,
      compile (decompile comp) = comp.
  Proof.
    intros. destruct comp; simpl.
    - destruct p as [ [ms imp] exp].
      simpl. rewrite -!map_fmap_compose.
      rewrite !translate_backtranslate_map //.
    - destruct p as [ [ms imp] exp].
      simpl. rewrite -!map_fmap_compose.
      rewrite !translate_backtranslate_map translate_backtranslate_word //.
  Qed.

  Lemma decompile_compile:
    forall comp,
    well_formed_comp b_stk nat nat_eq_dec nat_countable Word cap_lang.can_address_only cap_lang.pwlW cap_lang.is_global (compile comp) ->
    decompile (compile comp) = comp.
  Proof.
    intros. destruct comp; simpl.
    - destruct p as [ [ms imp] exp].
      simpl. inv H0. inv Hwf_pre.
      rewrite -!map_fmap_compose.
      rewrite !backtranslate_translate_map; auto.
      + intros. generalize (Hexp a _ ltac:(rewrite lookup_fmap H0; auto)).
        intros [A [B C] ]. destruct w; auto.
        destruct c; simpl in C; try congruence; auto.
      + intros. generalize (Hnpwl a _ ltac:(rewrite (@lookup_fmap Addr (gmap Addr)) H0 //)).
        intros [A [B C] ]. destruct w; auto.
        destruct c; simpl in C; try congruence; auto.
    - destruct p as [ [ms imp] exp].
      simpl. inv H0. inv Hwf_pre.
      rewrite -!map_fmap_compose.
      rewrite !backtranslate_translate_map; auto.
      + rewrite backtranslate_translate_word; auto. 
        destruct Hw_main as [A [B C] ]. destruct w; auto.
        destruct c; simpl in C; try congruence; auto.
      + intros. generalize (Hexp a _ ltac:(rewrite lookup_fmap H0; auto)).
        intros [A [B C] ]. destruct w0; auto.
        destruct c; simpl in C; try congruence; auto.
      + intros. generalize (Hnpwl a _ ltac:(rewrite (@lookup_fmap Addr (gmap Addr)) H0 //)).
        intros [A [B C] ]. destruct w0; auto.
        destruct c; simpl in C; try congruence; auto.
  Qed.

  Lemma decompile_preserves_well_formed_comp:
    forall comp,
      well_formed_comp b_stk nat nat_eq_dec nat_countable Word cap_lang.can_address_only cap_lang.pwlW cap_lang.is_global comp ->
      well_formed_comp b_stk nat nat_eq_dec nat_countable base.Word lang.can_address_only lang.pwlW lang.is_global (decompile comp).
  Proof.
    destruct comp; intros.
    - inv H0. inv Hwf_pre.
      econstructor. econstructor; auto.
      + intros. rewrite lookup_fmap in H0.
        erewrite fmap_is_Some in H0.
        apply Hdisj; auto.
      + intros. rewrite lookup_fmap in H0.
        destruct (exp !! s) as [wexp|] eqn:Hwexp; inv H0.
        eapply Hexp in Hwexp. destruct Hwexp as [A1 [A2 A3] ].
        destruct wexp; simpl; auto.
        simpl in A1, A2, A3. destruct c as [ [ [ [p g] b] e] a].
        rewrite (@dom_fmap_L Addr (gmap Addr) (gset Addr)). auto.
      + intros. rewrite (@lookup_fmap Addr (gmap Addr)).
        rewrite fmap_is_Some. eapply Himp; eauto.
      + intros. rewrite (@lookup_fmap Addr (gmap Addr)) in H0.
        destruct (ms !! a) as [wexp|] eqn:Hwexp; rewrite Hwexp in H0; inv H0.
        rewrite (@dom_fmap_L Addr (gmap Addr) (gset Addr)).
        eapply Hnpwl in Hwexp.
        destruct wexp; auto.
      + intros. rewrite (@dom_fmap_L Addr (gmap Addr) (gset Addr)) in H0. auto.
    - inv H0. inv Hwf_pre.
      econstructor; simpl.
      + econstructor; eauto.
        * intros. rewrite lookup_fmap in H0.
          erewrite fmap_is_Some in H0.
          apply Hdisj; auto.
        * intros. rewrite lookup_fmap in H0.
          destruct (exp !! s) as [wexp|] eqn:Hwexp; inv H0.
          eapply Hexp in Hwexp. destruct Hwexp as [A1 [A2 A3] ].
          destruct wexp; simpl; auto.
          simpl in A1, A2, A3. destruct c as [ [ [ [p g] b] e] a].
          rewrite (@dom_fmap_L Addr (gmap Addr) (gset Addr)). auto.
        * intros. rewrite (@lookup_fmap Addr (gmap Addr)).
          rewrite fmap_is_Some. eapply Himp; eauto.
        * intros. rewrite (@lookup_fmap Addr (gmap Addr)) in H0.
          destruct (ms !! a) as [wexp|] eqn:Hwexp; rewrite Hwexp in H0; inv H0.
          rewrite (@dom_fmap_L Addr (gmap Addr) (gset Addr)).
          eapply Hnpwl in Hwexp.
          destruct wexp; auto.
        * intros. rewrite (@dom_fmap_L Addr (gmap Addr) (gset Addr)) in H0. auto.
      + rewrite (@dom_fmap_L Addr (gmap Addr) (gset Addr)). destruct w; auto.
  Qed.

  Lemma compile_preserves_well_formed_comp:
    forall comp,
      well_formed_comp b_stk nat nat_eq_dec nat_countable base.Word lang.can_address_only lang.pwlW lang.is_global comp ->
      well_formed_comp b_stk nat nat_eq_dec nat_countable Word cap_lang.can_address_only cap_lang.pwlW cap_lang.is_global (compile comp).
  Proof.
    destruct comp; intros.
    - inv H0. inv Hwf_pre.
      econstructor. econstructor; auto.
      + intros. rewrite lookup_fmap in H0.
        erewrite fmap_is_Some in H0.
        apply Hdisj; auto.
      + intros. rewrite lookup_fmap in H0.
        destruct (exp !! s) as [wexp|] eqn:Hwexp; inv H0.
        eapply Hexp in Hwexp. destruct Hwexp as [A1 [A2 A3] ].
        destruct wexp; simpl; auto.
        simpl in A1, A2, A3. destruct c; try congruence.
        destruct c as [ [ [ [p g] b] e] a].
        rewrite (@dom_fmap_L Addr (gmap Addr) (gset Addr)). auto.
      + intros. rewrite (@lookup_fmap Addr (gmap Addr)).
        rewrite fmap_is_Some. eapply Himp; eauto.
      + intros. rewrite (@lookup_fmap Addr (gmap Addr)) in H0.
        destruct (ms !! a) as [wexp|] eqn:Hwexp; rewrite Hwexp in H0; inv H0.
        rewrite (@dom_fmap_L Addr (gmap Addr) (gset Addr)).
        eapply Hnpwl in Hwexp. destruct Hwexp as [A [B C] ].
        destruct wexp; auto.
        destruct c; simpl in C; try congruence; auto.
      + intros. rewrite (@dom_fmap_L Addr (gmap Addr) (gset Addr)) in H0. auto.
    - inv H0. inv Hwf_pre.
      econstructor; simpl.
      + econstructor; eauto.
        * intros. rewrite lookup_fmap in H0.
          erewrite fmap_is_Some in H0.
          apply Hdisj; auto.
        * intros. rewrite lookup_fmap in H0.
          destruct (exp !! s) as [wexp|] eqn:Hwexp; inv H0.
          eapply Hexp in Hwexp. destruct Hwexp as [A1 [A2 A3] ].
          destruct wexp; simpl; auto.
          simpl in A1, A2, A3. destruct c; try congruence.
          destruct c as [ [ [ [p g] b] e] a].
          rewrite (@dom_fmap_L Addr (gmap Addr) (gset Addr)). auto.
        * intros. rewrite (@lookup_fmap Addr (gmap Addr)).
          rewrite fmap_is_Some. eapply Himp; eauto.
        * intros. rewrite (@lookup_fmap Addr (gmap Addr)) in H0.
          destruct (ms !! a) as [wexp|] eqn:Hwexp; rewrite Hwexp in H0; inv H0.
          rewrite (@dom_fmap_L Addr (gmap Addr) (gset Addr)).
          eapply Hnpwl in Hwexp. destruct Hwexp as [A [B C] ].
          destruct wexp; auto.
          destruct c; simpl in C; try congruence; auto.
        * intros. rewrite (@dom_fmap_L Addr (gmap Addr) (gset Addr)) in H0. auto.
      + rewrite (@dom_fmap_L Addr (gmap Addr) (gset Addr)). destruct w; auto.
        destruct Hw_main as [A [B C] ].
        destruct c; simpl in C; try congruence; auto.
  Qed.

  Lemma map_fmap_union {K A B} `{EqDecision K} `{Countable K} (f : A → B) (m1 m2 : gmap K A) :
    f <$> (map_union m1 m2) = map_union (f <$> m1) (f <$> m2).
  Proof.
    apply map_eq; intros i. apply option_eq; intros x.
    rewrite lookup_fmap !lookup_union !lookup_fmap.
    destruct (m1 !! i), (m2 !! i); auto.
  Qed.

  (* I hate Coq *)
  Lemma backtranslate_resolve_imports:
    forall imp exp ms
      (Himpdisj: forall s1 s2 a, (s1, a) ∈ imp -> (s2, a) ∈ imp -> s1 = s2),
      @gmap_fmap Addr _ _ Word base.Word backtranslate_word (resolve_imports nat nat_eq_dec nat_countable Word imp exp ms) =
      resolve_imports nat nat_eq_dec nat_countable base.Word imp (backtranslate_word <$> exp) (@gmap_fmap Addr _ _ Word base.Word backtranslate_word ms).
  Proof.
  intros. apply map_eq.
  intros a.
  assert (Hx: forall x, (exists s, (s, x) ∈ imp) \/ ~ (exists s, (s, x) ∈ imp)).
  { intros.
    generalize (@set_Exists_dec (nat * Addr) (imports nat nat_eq_dec nat_countable) ltac:(apply _) ltac:(apply _) ltac:(apply _) ltac:(apply _) ltac:(apply _) ltac:(apply _) ltac:(apply _) ltac:(apply _) ltac:(apply _) (fun s => s.2 = x) ltac:(intros s; destruct (addr_eq_dec s.2 x); [left; auto|right; auto]) imp).
    destruct 1.
    - destruct s. destruct x0. destruct H0. simpl in H1. inv H1.
      left; exists n; auto.
    - right. red; intros. destruct H0.
      eapply n. exists (x0, x). split; auto. }
  destruct (Hx a).
  - destruct H0 as [s Hin].
    destruct (resolve_imports_spec_in nat nat_eq_dec nat_countable Word imp exp ms a s Himpdisj Hin) as [ [A1 A2] | [wexp [A1 A2] ] ].
    + destruct (resolve_imports_spec_in nat nat_eq_dec nat_countable base.Word imp (backtranslate_word <$> exp) (@gmap_fmap Addr _ _ Word base.Word backtranslate_word ms) a s Himpdisj Hin) as [ [B1 B2] | [wexp [B1 B2] ] ].
      * rewrite B2. rewrite lookup_fmap A2. rewrite (@lookup_fmap Addr (gmap Addr) _ _ _ _ _ _ _ _ _ _ _ backtranslate_word ms a). reflexivity.
      * rewrite lookup_fmap in B1. rewrite A1 in B1; inv B1.
    + destruct (resolve_imports_spec_in nat nat_eq_dec nat_countable base.Word imp (backtranslate_word <$> exp) (@gmap_fmap Addr _ _ Word base.Word backtranslate_word ms) a s Himpdisj Hin) as [ [B1 B2] | [wexp' [B1 B2] ] ].
      * rewrite lookup_fmap A1 in B1; inv B1.
      * rewrite lookup_fmap A1 in B1; inv B1.
        rewrite B2. rewrite lookup_fmap A2. reflexivity.
  - erewrite resolve_imports_spec_not_in; eauto.
    rewrite lookup_fmap. erewrite resolve_imports_spec_not_in; eauto.
    rewrite (@lookup_fmap Addr (gmap Addr) _ _ _ _ _ _ _ _ _ _ _ backtranslate_word ms a). reflexivity.
  Qed.

  Lemma translate_resolve_imports:
    forall imp exp ms
      (Himpdisj: forall s1 s2 a, (s1, a) ∈ imp -> (s2, a) ∈ imp -> s1 = s2),
      @gmap_fmap Addr _ _ base.Word Word translate_word (resolve_imports nat nat_eq_dec nat_countable base.Word imp exp ms) =
      resolve_imports nat nat_eq_dec nat_countable Word imp (translate_word <$> exp) (@gmap_fmap Addr _ _ base.Word Word translate_word ms).
  Proof.
  intros. apply map_eq.
  intros a.
  assert (Hx: forall x, (exists s, (s, x) ∈ imp) \/ ~ (exists s, (s, x) ∈ imp)).
  { intros.
    generalize (@set_Exists_dec (nat * Addr) (imports nat nat_eq_dec nat_countable) ltac:(apply _) ltac:(apply _) ltac:(apply _) ltac:(apply _) ltac:(apply _) ltac:(apply _) ltac:(apply _) ltac:(apply _) ltac:(apply _) (fun s => s.2 = x) ltac:(intros s; destruct (addr_eq_dec s.2 x); [left; auto|right; auto]) imp).
    destruct 1.
    - destruct s. destruct x0. destruct H0. simpl in H1. inv H1.
      left; exists n; auto.
    - right. red; intros. destruct H0.
      eapply n. exists (x0, x). split; auto. }
  destruct (Hx a).
  - destruct H0 as [s Hin].
    destruct (resolve_imports_spec_in nat nat_eq_dec nat_countable base.Word imp exp ms a s Himpdisj Hin) as [ [A1 A2] | [wexp [A1 A2] ] ].
    + destruct (resolve_imports_spec_in nat nat_eq_dec nat_countable Word imp (translate_word <$> exp) (@gmap_fmap Addr _ _ base.Word Word translate_word ms) a s Himpdisj Hin) as [ [B1 B2] | [wexp [B1 B2] ] ].
      * rewrite B2. rewrite lookup_fmap A2. rewrite (@lookup_fmap Addr (gmap Addr) _ _ _ _ _ _ _ _ _ _ _ translate_word ms a). reflexivity.
      * rewrite lookup_fmap in B1. rewrite A1 in B1; inv B1.
    + destruct (resolve_imports_spec_in nat nat_eq_dec nat_countable Word imp (translate_word <$> exp) (@gmap_fmap Addr _ _ base.Word Word translate_word ms) a s Himpdisj Hin) as [ [B1 B2] | [wexp' [B1 B2] ] ].
      * rewrite lookup_fmap A1 in B1; inv B1.
      * rewrite lookup_fmap A1 in B1; inv B1.
        rewrite B2. rewrite lookup_fmap A2. reflexivity.
  - erewrite resolve_imports_spec_not_in; eauto.
    rewrite lookup_fmap. erewrite resolve_imports_spec_not_in; eauto.
    rewrite (@lookup_fmap Addr (gmap Addr) _ _ _ _ _ _ _ _ _ _ _ translate_word ms a). reflexivity.
  Qed.

  Lemma decompile_preserves_link:
    forall context comp prog,
      link b_stk nat nat_eq_dec nat_countable Word cap_lang.can_address_only cap_lang.pwlW cap_lang.is_global context comp prog ->
      link b_stk nat nat_eq_dec nat_countable base.Word lang.can_address_only lang.pwlW lang.is_global (decompile context) (decompile comp) (decompile prog).
  Proof.
    intros. inv H0; simpl decompile.
    - destruct comp1 as [ [ms1 imp1] exp1].
      destruct comp2 as [ [ms2 imp2] exp2].
      destruct comp0 as [ [m2 imp] exp].
      econstructor; [|eapply decompile_preserves_well_formed_comp in Hwf_l; simpl; eapply Hwf_l|eapply decompile_preserves_well_formed_comp in Hwf_r; simpl; eapply Hwf_r].
      inv Hlink. econstructor.
      + intros. rewrite lookup_fmap in H0.
        erewrite fmap_is_Some in H0.
        rewrite lookup_fmap in H1.
        erewrite fmap_is_Some in H1.
        eapply Hms_disj; eauto.
      + apply map_eq. intros.
        erewrite lookup_merge; [|reflexivity].
        rewrite !lookup_fmap.
        erewrite lookup_merge; [|reflexivity].
        destruct (exp1 !! i) as [w1|] eqn:Hw1; rewrite Hw1 /= //.
      + intros. split; intros.
        * eapply Himp in H0. destruct H0. split; auto.
          rewrite lookup_fmap. rewrite H1. auto.
        * destruct H0. rewrite lookup_fmap in H1.
          eapply Himp. split; auto.
          match goal with |- ?X = None => destruct X; simpl in H1; auto; inv H1 end.
      + match goal with |- backtranslate_word <$> resolve_imports nat nat_eq_dec nat_countable Word imp2 ?exp ?ms = _ => generalize (backtranslate_resolve_imports imp2 exp ms ltac:(inv Hwf_r; inv Hwf_pre; auto)) end.
        intro X. etransitivity; [apply X|].
        f_equal. rewrite -map_fmap_union.
        apply backtranslate_resolve_imports. inv Hwf_l. inv Hwf_pre; auto.
    - destruct comp1 as [ [ms1 imp1] exp1].
      destruct comp2 as [ [ms2 imp2] exp2].
      destruct comp0 as [ [m2 imp] exp].
      econstructor; [|eapply decompile_preserves_well_formed_comp in Hwf_l; simpl; eapply Hwf_l|eapply decompile_preserves_well_formed_comp in Hwf_r; simpl; eapply Hwf_r].
      inv Hlink. econstructor.
      + intros. rewrite lookup_fmap in H0.
        erewrite fmap_is_Some in H0.
        rewrite lookup_fmap in H1.
        erewrite fmap_is_Some in H1.
        eapply Hms_disj; eauto.
      + apply map_eq. intros.
        erewrite lookup_merge; [|reflexivity].
        rewrite !lookup_fmap.
        erewrite lookup_merge; [|reflexivity].
        destruct (exp1 !! i) as [w1|] eqn:Hw1; rewrite Hw1 /= //.
      + intros. split; intros.
        * eapply Himp in H0. destruct H0. split; auto.
          rewrite lookup_fmap. rewrite H1. auto.
        * destruct H0. rewrite lookup_fmap in H1.
          eapply Himp. split; auto.
          match goal with |- ?X = None => destruct X; simpl in H1; auto; inv H1 end.
      + match goal with |- backtranslate_word <$> resolve_imports nat nat_eq_dec nat_countable Word imp2 ?exp ?ms = _ => generalize (backtranslate_resolve_imports imp2 exp ms ltac:(inv Hwf_r; inv Hwf_pre; auto)) end.
        intro X. etransitivity; [apply X|].
        f_equal. rewrite -map_fmap_union.
        apply backtranslate_resolve_imports. inv Hwf_l. inv Hwf_pre; auto.
    - destruct comp1 as [ [ms1 imp1] exp1].
      destruct comp2 as [ [ms2 imp2] exp2].
      destruct comp0 as [ [m2 imp] exp].
      econstructor; [|eapply decompile_preserves_well_formed_comp in Hwf_l; simpl; eapply Hwf_l|eapply decompile_preserves_well_formed_comp in Hwf_r; simpl; eapply Hwf_r].
      inv Hlink. econstructor.
      + intros. rewrite lookup_fmap in H0.
        erewrite fmap_is_Some in H0.
        rewrite lookup_fmap in H1.
        erewrite fmap_is_Some in H1.
        eapply Hms_disj; eauto.
      + apply map_eq. intros.
        erewrite lookup_merge; [|reflexivity].
        rewrite !lookup_fmap.
        erewrite lookup_merge; [|reflexivity].
        destruct (exp1 !! i) as [w1|] eqn:Hw1; rewrite Hw1 /= //.
      + intros. split; intros.
        * eapply Himp in H0. destruct H0. split; auto.
          rewrite lookup_fmap. rewrite H1. auto.
        * destruct H0. rewrite lookup_fmap in H1.
          eapply Himp. split; auto.
          match goal with |- ?X = None => destruct X; simpl in H1; auto; inv H1 end.
      + match goal with |- backtranslate_word <$> resolve_imports nat nat_eq_dec nat_countable Word imp2 ?exp ?ms = _ => generalize (backtranslate_resolve_imports imp2 exp ms ltac:(inv Hwf_r; inv Hwf_pre; auto)) end.
        intro X. etransitivity; [apply X|].
        f_equal. rewrite -map_fmap_union.
        apply backtranslate_resolve_imports. inv Hwf_l. inv Hwf_pre; auto.
  Qed.

  Lemma compile_preserves_link:
    forall context comp prog,
      link b_stk nat nat_eq_dec nat_countable base.Word lang.can_address_only lang.pwlW lang.is_global context comp prog ->
      link b_stk nat nat_eq_dec nat_countable Word cap_lang.can_address_only cap_lang.pwlW cap_lang.is_global (compile context) (compile comp) (compile prog).
  Proof.
    intros. inv H0; simpl compile.
    - destruct comp1 as [ [ms1 imp1] exp1].
      destruct comp2 as [ [ms2 imp2] exp2].
      destruct comp0 as [ [m2 imp] exp].
      econstructor; [|eapply compile_preserves_well_formed_comp in Hwf_l; simpl; eapply Hwf_l|eapply compile_preserves_well_formed_comp in Hwf_r; simpl; eapply Hwf_r].
      inv Hlink. econstructor.
      + intros. rewrite lookup_fmap in H0.
        erewrite fmap_is_Some in H0.
        rewrite lookup_fmap in H1.
        erewrite fmap_is_Some in H1.
        eapply Hms_disj; eauto.
      + apply map_eq. intros.
        erewrite lookup_merge; [|reflexivity].
        rewrite !lookup_fmap.
        erewrite lookup_merge; [|reflexivity].
        destruct (exp1 !! i) as [w1|] eqn:Hw1; rewrite Hw1 /= //.
      + intros. split; intros.
        * eapply Himp in H0. destruct H0. split; auto.
          rewrite lookup_fmap. rewrite H1. auto.
        * destruct H0. rewrite lookup_fmap in H1.
          eapply Himp. split; auto.
          match goal with |- ?X = None => destruct X; simpl in H1; auto; inv H1 end.
      + match goal with |- translate_word <$> resolve_imports nat nat_eq_dec nat_countable base.Word imp2 ?exp ?ms = _ => generalize (translate_resolve_imports imp2 exp ms ltac:(inv Hwf_r; inv Hwf_pre; auto)) end.
        intro X. etransitivity; [apply X|].
        f_equal. rewrite -map_fmap_union.
        apply translate_resolve_imports. inv Hwf_l. inv Hwf_pre; auto.
    - destruct comp1 as [ [ms1 imp1] exp1].
      destruct comp2 as [ [ms2 imp2] exp2].
      destruct comp0 as [ [m2 imp] exp].
      econstructor; [|eapply compile_preserves_well_formed_comp in Hwf_l; simpl; eapply Hwf_l|eapply compile_preserves_well_formed_comp in Hwf_r; simpl; eapply Hwf_r].
      inv Hlink. econstructor.
      + intros. rewrite lookup_fmap in H0.
        erewrite fmap_is_Some in H0.
        rewrite lookup_fmap in H1.
        erewrite fmap_is_Some in H1.
        eapply Hms_disj; eauto.
      + apply map_eq. intros.
        erewrite lookup_merge; [|reflexivity].
        rewrite !lookup_fmap.
        erewrite lookup_merge; [|reflexivity].
        destruct (exp1 !! i) as [w1|] eqn:Hw1; rewrite Hw1 /= //.
      + intros. split; intros.
        * eapply Himp in H0. destruct H0. split; auto.
          rewrite lookup_fmap. rewrite H1. auto.
        * destruct H0. rewrite lookup_fmap in H1.
          eapply Himp. split; auto.
          match goal with |- ?X = None => destruct X; simpl in H1; auto; inv H1 end.
      + match goal with |- translate_word <$> resolve_imports nat nat_eq_dec nat_countable base.Word imp2 ?exp ?ms = _ => generalize (translate_resolve_imports imp2 exp ms ltac:(inv Hwf_r; inv Hwf_pre; auto)) end.
        intro X. etransitivity; [apply X|].
        f_equal. rewrite -map_fmap_union.
        apply translate_resolve_imports. inv Hwf_l. inv Hwf_pre; auto.
    - destruct comp1 as [ [ms1 imp1] exp1].
      destruct comp2 as [ [ms2 imp2] exp2].
      destruct comp0 as [ [m2 imp] exp].
      econstructor; [|eapply compile_preserves_well_formed_comp in Hwf_l; simpl; eapply Hwf_l|eapply compile_preserves_well_formed_comp in Hwf_r; simpl; eapply Hwf_r].
      inv Hlink. econstructor.
      + intros. rewrite lookup_fmap in H0.
        erewrite fmap_is_Some in H0.
        rewrite lookup_fmap in H1.
        erewrite fmap_is_Some in H1.
        eapply Hms_disj; eauto.
      + apply map_eq. intros.
        erewrite lookup_merge; [|reflexivity].
        rewrite !lookup_fmap.
        erewrite lookup_merge; [|reflexivity].
        destruct (exp1 !! i) as [w1|] eqn:Hw1; rewrite Hw1 /= //.
      + intros. split; intros.
        * eapply Himp in H0. destruct H0. split; auto.
          rewrite lookup_fmap. rewrite H1. auto.
        * destruct H0. rewrite lookup_fmap in H1.
          eapply Himp. split; auto.
          match goal with |- ?X = None => destruct X; simpl in H1; auto; inv H1 end.
      + match goal with |- translate_word <$> resolve_imports nat nat_eq_dec nat_countable base.Word imp2 ?exp ?ms = _ => generalize (translate_resolve_imports imp2 exp ms ltac:(inv Hwf_r; inv Hwf_pre; auto)) end.
        intro X. etransitivity; [apply X|].
        f_equal. rewrite -map_fmap_union.
        apply translate_resolve_imports. inv Hwf_l. inv Hwf_pre; auto.
  Qed.

  Lemma decompile_preserves_is_context:
    forall context comp prog,
      is_context b_stk nat nat_eq_dec nat_countable Word cap_lang.can_address_only cap_lang.pwlW cap_lang.is_global context comp prog ->
      is_context b_stk nat nat_eq_dec nat_countable base.Word lang.can_address_only lang.pwlW lang.is_global (decompile context) (decompile comp) (decompile prog).
  Proof.
    intros. inv H0. econstructor.
    destruct His_program as [Hlink His_program].
    split; [eapply decompile_preserves_link; eauto|].
    inv His_program. simpl. econstructor; auto.
    eapply decompile_preserves_well_formed_comp in Hwfcomp.
    apply Hwfcomp.
  Qed.

  Lemma compile_preserves_is_context:
    forall context comp prog,
      is_context b_stk nat nat_eq_dec nat_countable base.Word lang.can_address_only lang.pwlW lang.is_global context comp prog ->
      is_context b_stk nat nat_eq_dec nat_countable Word cap_lang.can_address_only cap_lang.pwlW cap_lang.is_global (compile context) (compile comp) (compile prog).
  Proof.
    intros. inv H0. econstructor.
    destruct His_program as [Hlink His_program].
    split; [eapply compile_preserves_link; eauto|].
    inv His_program. simpl. econstructor; auto.
    eapply compile_preserves_well_formed_comp in Hwfcomp.
    apply Hwfcomp.
  Qed.

  Lemma cap_lang_cons_is_app:
    forall K (a: cap_lang.ectx_item), a :: K = K ++ [a].
  Proof.
    induction K.
    - reflexivity.
    - simpl. intros; destruct a, a0.
      rewrite IHK. reflexivity.
  Qed.

  Lemma cap_lang_fill_inv_instr:
    forall (K: list (ectxi_language.ectx_item cap_lang.cap_ectxi_lang)) cf e1,
      ectxi_language.fill K e1 = cap_lang.Instr cf ->
      K = [] /\ e1 = cap_lang.Instr cf.
  Proof.
    destruct K; [simpl; auto|].
    rewrite (cap_lang_cons_is_app K e) /=.
    intros. rewrite ectxi_language.fill_app in H0.
    destruct e; simpl in H0; inv H0.
  Qed.

  Lemma cap_lang_fill_inv_instr':
    forall (K: list (ectxi_language.ectx_item cap_lang.cap_ectxi_lang)) cf e1,
      ectxi_language.fill K e1 = cap_lang.Seq (cap_lang.Instr cf) ->
      (K = [] /\ e1 = cap_lang.Seq (cap_lang.Instr cf)) \/ (K = [cap_lang.SeqCtx] /\ e1 = cap_lang.Instr cf).
  Proof.
    destruct K; [simpl; auto|].
    rewrite (cap_lang_cons_is_app K e) /=.
    intros. rewrite ectxi_language.fill_app in H0.
    destruct e; simpl in H0; inv H0. right.
    destruct K; [simpl; auto|].
    rewrite (cap_lang_cons_is_app K e) /= in H2.
    rewrite ectxi_language.fill_app in H2.
    destruct e; simpl in H2; inv H2.
  Qed.

  Lemma cap_lang_determ:
    forall s1 s2 s2' s2'',
    sim e_stk s1 s2 ->
    erased_step s2 s2' ->
    erased_step s2 s2'' ->
    s2' = s2''.
  Proof.
    intros. inv H0. inv H1; inv H2.
    inv H0; inv H1. inv H4; inv H5. simpl in *.
    inv H2; inv H0. destruct t1; simpl in H3; [|destruct t1; simpl in H3; inv H3].
    destruct t0; simpl in H2; [|destruct t0; simpl in H2; inv H2].
    inv H3. inv H2. simpl. inv Hsexpr.
    - symmetry in H3. eapply cap_lang_fill_inv_instr in H3.
      destruct H3 as [-> ->]. simpl in H1.
      symmetry in H1. eapply cap_lang_fill_inv_instr in H1.
      destruct H1 as [-> ->]. simpl.
      generalize (cap_lang.cap_lang_determ _ _ _ _ _ _ _ _ _ _ H4 H6).
      destruct 1 as [-> [-> [-> ->] ] ]. reflexivity.
    - symmetry in H3. eapply cap_lang_fill_inv_instr in H3.
      destruct H3 as [-> ->]. simpl in H1.
      symmetry in H1. eapply cap_lang_fill_inv_instr in H1.
      destruct H1 as [-> ->]. simpl.
      generalize (cap_lang.cap_lang_determ _ _ _ _ _ _ _ _ _ _ H4 H6).
      destruct 1 as [-> [-> [-> ->] ] ]. reflexivity.
    - symmetry in H0. eapply cap_lang_fill_inv_instr' in H0.
      destruct H0 as [ [-> ->]|[-> ->] ].
      + simpl in H1. symmetry in H1. eapply cap_lang_fill_inv_instr' in H1.
        destruct H1 as [ [-> ->]|[-> ->] ].
        * generalize (cap_lang.cap_lang_determ _ _ _ _ _ _ _ _ _ _ H4 H6).
          destruct 1 as [-> [-> [-> ->] ] ]. reflexivity.
        * inv H4. inv H6.
      + simpl in H1. symmetry in H1. eapply cap_lang_fill_inv_instr' in H1.
        destruct H1 as [ [-> ->]|[-> ->] ].
        * inv H4; inv H6.
        * generalize (cap_lang.cap_lang_determ _ _ _ _ _ _ _ _ _ _ H4 H6).
          destruct 1 as [-> [-> [-> ->] ] ]. reflexivity.
  Qed.      

  (* Definition of fully abstract specialized for the overlay and base capability machine semantics *)
  Definition fully_abstract := is_fully_abstract lang.overlay_lang cap_lang.cap_lang b_stk nat _ _ base.Word machine_base.Word lang.can_address_only lang.pwlW lang.is_global cap_lang.can_address_only cap_lang.pwlW cap_lang.is_global (lang.initial_state b_stk e_stk) (cap_lang.initial_state call.r_stk b_stk e_stk).

  Theorem compile_fully_abstract:
    fully_abstract compile.
  Proof.
    intros compS1 compS2; split; intros.
    - red; intros. generalize (decompile_preserves_is_context _ _ _ H1).
      rewrite decompile_compile; [|inv H1; destruct His_program as [A B]; inv A; auto].
      intro Hcontext1.
      generalize (decompile_preserves_is_context _ _ _ H2).
      rewrite decompile_compile; [|inv H2; destruct His_program as [A B]; inv A; auto].
      intro Hcontext2.
      generalize (H0 _ _ _ Hcontext1 Hcontext2). intros X.
      split; intros.
      + destruct H3 as [s1 [step1 Hfinal1] ].
        deterministic
        generalize (fsim_backwards lang.overlay_lang cap_lang.cap_lang cap_lang.cap_lang_determ).
      generalize fsim_terminates.
      generalize (@overlay_to_cap_lang_fsim b_stk e_stk stk_pos H).






End Compile_fully_abstract.