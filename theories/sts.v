From iris.algebra Require Import auth agree gmap excl.
From iris.base_logic Require Export invariants.
From iris.proofmode Require Import tactics.
From cap_machine Require Import stdpp_extra.
Import uPred.

(** The CMRA for the heap of STS.
    We distinguish between the standard and owned sts. *)

(** For shared resources, we register the state. *)

Definition sts_std_stateUR (A B : Type) {eqD: EqDecision A} {count: Countable A} := authUR (gmapUR A (exclR (leibnizO B))).
Definition STS_std_states (A B : Type) {eqD: EqDecision A} {count: Countable A} : Type := gmap A B.


(** For owned resources, we register the state and the transition relation. *)

Definition sts_stateUR := authUR (gmapUR positive (exclR (leibnizO positive))).
Definition sts_relUR :=
  authUR (gmapUR positive (agreeR (leibnizO ((positive → positive → Prop) * (positive → positive → Prop) * (positive → positive → Prop))))).

Notation STS_states := (gmap positive positive).
Notation STS_rels := (gmap positive ((positive → positive → Prop) * (positive → positive → Prop) * (positive → positive → Prop ))).

(** A typeclass for comparable *)
Class Ord A `{EqDecision A} : Type :=
  { le_a : relation A;
    le_a_decision : ∀ a1 a2, Decision (le_a a1 a2);
    le_a_preorder : PreOrder le_a }.

(** Standard STS. *)
(** The Standard STS is made up of three relations *)
Class STS_STD (B : Type) :=
  { Rpub : relation B;
    Rpriv : relation B;
    Rpubp : relation B; }.

(** The CMRA for the sts collection. *)
Class STS_preG A B Σ `{EqDecision A, Countable A} :=
  { sts_pre_state_inG :> inG Σ sts_stateUR;
    sts_pre_std_state_inG :> inG Σ (sts_std_stateUR A B);
    sts_pre_rel_inG :> inG Σ sts_relUR; }.

Class STSG A B Σ `{EqDecision A, Countable A} :=
  { sts_state_inG :> inG Σ sts_stateUR;
    sts_std_state_inG :> inG Σ (sts_std_stateUR A B);
    sts_rel_inG :> inG Σ sts_relUR;
    γs_std : gname;
    γs_loc : gname;
    γr_loc : gname;}.

Definition STS_preΣ A B `{EqDecision A, Countable A} :=
  #[ GFunctor sts_stateUR;
     GFunctor (sts_std_stateUR A B);
     GFunctor sts_relUR ].

Instance subG_STS_preΣ A B `{EqDecision A, Countable A} {Σ} :
  subG (STS_preΣ A B) Σ → STS_preG A B Σ.
Proof.
  (* hack: solve_inG does not currently unfold [subG X _] where X has more than
     4 parameters. We have 5. *)
  set f := STS_preΣ A B. unfold STS_preΣ in f.
  solve_inG.
Qed.

Section definitionsS.

  (* A now needs to be comparable, so we can distinquish between higher and lower a's *)
  Context {A B C D: Type} {Σ : gFunctors} {eqa: EqDecision A} {a_compare : Ord A}
          {count: Countable A}
          {sts_std: STS_STD B} {eqc : EqDecision C} {countC: Countable C}
          {eqd : EqDecision D} {countD: Countable D} {stsg : STSG A B Σ}.
  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states A B)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  Program Definition sts_state_std (i : A) (x : B) : iProp Σ
    := own (γs_std (A:=A)) (◯ {[ i := Excl x ]}).

  Definition sts_state_loc (i : positive) (y : D) : iProp Σ
    := own (γs_loc (A:=A)) (◯ {[ i := Excl (encode y) ]}).

  Definition convert_rel {D : Type} `{Countable D} (R : D → D → Prop) : positive → positive → Prop :=
    λ x y, ∃ a b, x = encode a ∧ y = encode b ∧ R a b.

  Definition sts_rel_loc (i : positive) (R : D → D → Prop) (P : D → D → Prop) (Q : D → D → Prop) : iProp Σ :=
    own (γr_loc (A:=A)) (◯ {[ i := to_agree ((convert_rel R,convert_rel P,convert_rel Q)) ]}).

  Program Definition sts_full γs γr (fs : STS_states) (fr : STS_rels) : iProp Σ
    := (own (A := sts_stateUR) γs (● (Excl <$> fs))
            ∗ own (A := sts_relUR) γr (● (to_agree <$> fr)))%I.
  Program Definition sts_full_std γs (fs : STS_std_states A B) : iProp Σ
    := own (A := sts_std_stateUR A B) γs (● (Excl <$> fs))%I.
  Program Definition sts_full_world W : iProp Σ :=
    ((sts_full_std (γs_std (A:=A)) W.1) ∗ (sts_full (γs_loc (A:=A)) (γr_loc (A:=A)) W.2.1 W.2.2))%I.

  (* We will have three kinds of future world relation (here in subset order) :
     - public
     - public +
     - private

     Additionally, we define a special public future world relation that allows
     public + transitions above an address a, but only public transitions below
     a
   *)

  Definition related_sts_std_pub (fs gs : STS_std_states A B) : Prop :=
    dom (gset A) fs ⊆ dom (gset A) gs ∧
    ∀ i x y, fs !! i = Some x → gs !! i = Some y → rtc (Rpub) x y.

  Definition related_sts_std_pub_plus (fs gs : STS_std_states A B) : Prop :=
    dom (gset A) fs ⊆ dom (gset A) gs ∧
    ∀ i x y, fs !! i = Some x → gs !! i = Some y → rtc (λ x y, (Rpub x y ∨ Rpubp x y)) x y.

  Definition related_sts_std_priv (fs gs : STS_std_states A B) : Prop :=
    dom (gset A) fs ⊆ dom (gset A) gs ∧
    ∀ i x y, fs !! i = Some x → gs !! i = Some y → rtc (λ x y, (Rpub x y ∨ Rpubp x y ∨ Rpriv x y)) x y.

  Program Definition related_sts_a (fs gs : STS_std_states A B) (a : A) : Prop :=
    dom (gset A) fs ⊆ dom (gset A) gs ∧
    ∀ (i : A) (x y : B), fs !! i = Some x → gs !! i = Some y →
                         rtc (λ x y, if (decide(Decision:=le_a_decision i a) (le_a i a))
                                     then (Rpub x y)
                                     else (Rpub x y ∨ Rpubp x y)) x y.

  Definition related_sts_pub (fs gs : STS_states) (fr gr : STS_rels) : Prop :=
    dom (gset positive) fs ⊆ dom (gset positive) gs ∧
    dom (gset positive) fr ⊆ dom (gset positive) gr ∧
    ∀ i (r1 r2 r1' r2' r3 r3' : positive → positive → Prop), fr !! i = Some (r1,r2,r3) → gr !! i = Some (r1',r2',r3') →
                       r1 = r1' ∧ r2 = r2' ∧ r3 = r3' ∧
                       (∀ x y, fs !! i = Some x → gs !! i = Some y → (rtc r1 x y)).


  Definition related_sts_pub_plus (fs gs : STS_states) (fr gr : STS_rels) : Prop :=
    dom (gset positive) fs ⊆ dom (gset positive) gs ∧
    dom (gset positive) fr ⊆ dom (gset positive) gr ∧
    ∀ i (r1 r2 r1' r2' r3 r3' : positive → positive → Prop), fr !! i = Some (r1,r2,r3) → gr !! i = Some (r1',r2',r3') →
                       r1 = r1' ∧ r2 = r2' ∧ r3 = r3' ∧
                       (∀ x y, fs !! i = Some x → gs !! i = Some y → (rtc (λ x y, r1 x y ∨ r2 x y) x y)).

  Definition related_sts_priv (fs gs : STS_states) (fr gr : STS_rels) : Prop :=
    dom (gset positive) fs ⊆ dom (gset positive) gs ∧
    dom (gset positive) fr ⊆ dom (gset positive) gr ∧
    ∀ i (r1 r2 r1' r2' r3 r3' : positive → positive → Prop), fr !! i = Some (r1,r2,r3) → gr !! i = Some (r1',r2',r3') →
                       r1 = r1' ∧ r2 = r2' ∧ r3 = r3' ∧
                       (∀ x y, fs !! i = Some x → gs !! i = Some y → (rtc (λ x y, (r1 x y ∨ r2 x y ∨ r3 x y)) x y)).

  Definition related_sts_pub_world W W' :=
    related_sts_std_pub W.1 W'.1 ∧
    related_sts_pub W.2.1 W'.2.1 W.2.2 W'.2.2.

  Definition related_sts_pub_plus_world W W' :=
    related_sts_std_pub_plus W.1 W'.1 ∧
    related_sts_pub_plus W.2.1 W'.2.1 W.2.2 W'.2.2.

  Definition related_sts_priv_world W W' :=
    related_sts_std_priv W.1 W'.1 ∧
    related_sts_priv W.2.1 W'.2.1 W.2.2 W'.2.2.

  Definition related_sts_a_world W W' a :=
    related_sts_a W.1 W'.1 a ∧
    related_sts_pub_plus W.2.1 W'.2.1 W.2.2 W'.2.2. 

  Global Instance sts_rel_loc_Persistent i R P Q : Persistent (sts_rel_loc i R P Q).
  Proof. apply _. Qed.

  Global Instance sts_rel_loc_Timeless i R P Q : Timeless (sts_rel_loc i R P Q).
  Proof. apply _. Qed.

  Global Instance sts_state_std_Timeless i x : Timeless (sts_state_std i x).
  Proof. apply _. Qed.
  Global Instance sts_state_loc_Timeless i x : Timeless (sts_state_loc i x).
  Proof. apply _. Qed.

  Global Instance sts_full_Timeless γs γr fs fr : Timeless (sts_full γs γr fs fr).
  Proof. apply _. Qed.
  Global Instance sts_full_world_Timeless W : Timeless (sts_full_world W).
  Proof. apply _. Qed.

End definitionsS.

Typeclasses Opaque sts_state_std sts_state_loc sts_rel_loc sts_full
            related_sts_pub related_sts_priv.

Lemma convert_rel_of_rel {A} `{EqDecision A, Countable A} (R: A -> A -> Prop) x y:
  R x y → convert_rel R (encode x) (encode y).
Proof. rewrite /convert_rel. eauto. Qed.

Lemma rel_of_convert_rel {A} `{EqDecision A, Countable A} (R: A -> A -> Prop) x y:
  convert_rel R (encode x) (encode y) → R x y.
Proof.
  rewrite /convert_rel. intros (?&?&HH1&HH2&?).
  apply encode_inj in HH1.
  apply encode_inj in HH2. subst; eauto.
Qed.

Section pre_STS.
  Context {A B C D: Type} {Σ : gFunctors} {eqa: EqDecision A} {compare_a: Ord A}
          {count: Countable A}
          {sts_std: STS_STD B} {eqc : EqDecision C} {countC: Countable C}
          {eqd : EqDecision D} {countD: Countable D} {sts_preg: STS_preG A B Σ}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states A B)).
  Notation WORLD := (prodO STS_STD STS).

  Lemma gen_sts_init :
    ⊢ |==> ∃ (stsg : STSG A B Σ), sts_full_world ((∅, (∅, ∅)) : WORLD).
  Proof.
    iMod (own_alloc (A:=sts_std_stateUR A B) (● ∅)) as (γsstd) "Hstd". by apply auth_auth_valid.
    iMod (own_alloc (A:=sts_stateUR) (● ∅)) as (γs) "Hs". by apply auth_auth_valid.
    iMod (own_alloc (A:=sts_relUR) (● ∅)) as (γr) "Hr". by apply auth_auth_valid.
    iModIntro. iExists (Build_STSG _ _ _ _ _ _ _ _ _ γsstd γs γr).
    rewrite /sts_full_world /sts_full_std /sts_full /=.
    rewrite !map_fmap_empty. iFrame.
  Qed.

End pre_STS.

Section STS.
  Context {A B C D: Type} {Σ : gFunctors} {eqa: EqDecision A} {compare_a: Ord A}
          {count: Countable A}
          {sts_std: STS_STD B} {eqc : EqDecision C} {countC: Countable C}
          {eqd : EqDecision D} {countD: Countable D} {stsg : STSG A B Σ}.
  Implicit Types x y : positive.
  Implicit Types a : A.
  Implicit Types b : B.
  Implicit Types c : C.
  Implicit Types d : D.
  Implicit Types fs gs : STS_states.
  Implicit Types fsd gsd : STS_std_states A B.
  Implicit Types fr_pub fr_priv gr_pub gr_priv : STS_rels.
  Implicit Types R : C → C → Prop.
  Implicit Types Q : D → D → Prop.
  Implicit Types Rp : positive → positive → Prop.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states A B)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  (* --------------------- REFLEXIVITY --------------------- *)

  Lemma related_sts_pub_refl fs fr : related_sts_pub fs fs fr fr.
  Proof.
    split; [|split]; trivial.
    intros; simplify_eq.
    split; [|split]; [..|split]; trivial.
    intros; simplify_eq; eauto using rtc_refl.
  Qed.

  Lemma related_sts_pub_plus_refl fs fr : related_sts_pub_plus fs fs fr fr.
  Proof.
    split; [|split]; trivial.
    intros; simplify_eq.
    split; [|split]; [..|split]; trivial.
    intros; simplify_eq; eauto using rtc_refl.
  Qed.

  Lemma related_sts_priv_refl fs fr : related_sts_priv fs fs fr fr.
  Proof.
    split; [|split]; trivial.
    intros; simplify_eq.
    split; [|split]; [..|split]; trivial.
    intros; simplify_eq;
    eauto using rtc_refl.
  Qed.

  Lemma related_sts_std_pub_refl fsd : related_sts_std_pub fsd fsd.
  Proof.
    split; trivial.
    intros; simplify_eq.
    eauto using rtc_refl.
  Qed.

  Lemma related_sts_std_pub_plus_refl fsd : related_sts_std_pub_plus fsd fsd.
  Proof.
    split; trivial.
    intros; simplify_eq.
    eauto using rtc_refl.
  Qed.

  Lemma related_sts_std_priv_refl fsd : related_sts_std_priv fsd fsd.
  Proof.
    split; trivial.
    intros; simplify_eq.
    eauto using rtc_refl.
  Qed.

  Lemma related_sts_pub_refl_world W : related_sts_pub_world W W.
  Proof. split;[apply related_sts_std_pub_refl|apply related_sts_pub_refl]. Qed.
  Lemma related_sts_pub_plus_refl_world W : related_sts_pub_plus_world W W.
  Proof. split;[apply related_sts_std_pub_plus_refl|apply related_sts_pub_plus_refl]. Qed.
  Lemma related_sts_priv_refl_world W : related_sts_priv_world W W.
  Proof. split;[apply related_sts_std_priv_refl|apply related_sts_priv_refl]. Qed.


  (* --------------------- pub ⊆ pub+ ⊆ priv  --------------------- *)

  Lemma related_sts_pub_pub_plus fs fr gs gr :
    related_sts_pub fs gs fr gr → related_sts_pub_plus fs gs fr gr.
  Proof.
    rewrite /related_sts_pub /related_sts_priv.
    intros [Hf1 [Hf2 Hf3]].
    do 2 (split; auto). intros.
    specialize (Hf3 i r1 r2 r1' r2' r3 r3' H H0) as (Hr1 & Hr2 & Hr3 & Hrtc); auto.
    subst. repeat (split;auto). intros.
    specialize (Hrtc x y H1 H2).
    inversion Hrtc.
    - left.
    - right with y0; auto.
      apply rtc_or_intro. apply H4.
  Qed.

  Lemma related_sts_pub_plus_priv fs fr gs gr :
    related_sts_pub_plus fs gs fr gr → related_sts_priv fs gs fr gr.
  Proof.
    intros [Hf1 [Hf2 Hf3]].
    do 2 (split; auto). intros.
    specialize (Hf3 i r1 r2 r1' r2' r3 r3' H H0) as (Hr1 & Hr2 & Hr3 & Hrtc); auto.
    subst. repeat (split;auto). intros.
    specialize (Hrtc x y H1 H2).
    inversion Hrtc.
    - left.
    - inversion H3.
      + right with y0; auto.
        apply rtc_implies with (R:=(λ x1 y1, (r1' x1 y1 ∨ r2' x1 y1) ∨ r3' x1 y1));
          [intros ? ? [[?|?]|?];auto|].
        apply rtc_or_intro;auto.
      + right with y0; auto.
        apply rtc_implies with (R:=(λ x1 y1, (r1' x1 y1 ∨ r2' x1 y1) ∨ r3' x1 y1));
          [intros ? ? [[?|?]|?];auto|].
        apply rtc_or_intro;auto.
  Qed.

  Lemma related_sts_pub_priv fs fr gs gr :
    related_sts_pub fs gs fr gr → related_sts_priv fs gs fr gr.
  Proof.
    intros Hpub.
    by apply related_sts_pub_plus_priv, related_sts_pub_pub_plus.
  Qed.

  Lemma related_sts_std_pub_pub_plus fsd gsd :
    related_sts_std_pub fsd gsd → related_sts_std_pub_plus fsd gsd.
  Proof.
    intros [Hf1 Hf2].
    split;auto. intros i x y Hx Hy.
    specialize (Hf2 i x y Hx Hy).
    apply rtc_or_intro. auto.
  Qed.

  Lemma related_sts_std_pub_plus_priv fsd gsd :
    related_sts_std_pub_plus fsd gsd → related_sts_std_priv fsd gsd.
  Proof.
    intros [Hf1 Hf2].
    split;auto. intros i x y Hx Hy.
    specialize (Hf2 i x y Hx Hy).
    eapply rtc_implies;[|eauto].
    intros r q [Hr | Hq];auto.
  Qed.

  Lemma related_sts_std_pub_priv fsd gsd :
    related_sts_std_pub fsd gsd → related_sts_std_priv fsd gsd.
  Proof.
    intros Hpub. by apply related_sts_std_pub_plus_priv, related_sts_std_pub_pub_plus.
  Qed.

  Lemma related_sts_pub_pub_plus_world W W' :
    related_sts_pub_world W W' → related_sts_pub_plus_world W W'.
  Proof.
    intros [Hrel Hrel'].
    split;[apply related_sts_std_pub_pub_plus|apply related_sts_pub_pub_plus];auto.
  Qed.
  Lemma related_sts_pub_plus_priv_world W W' :
    related_sts_pub_plus_world W W' → related_sts_priv_world W W'.
  Proof.
    intros [Hrel Hrel'].
    split;[apply related_sts_std_pub_plus_priv|apply related_sts_pub_plus_priv];auto.
  Qed.
  Lemma related_sts_pub_priv_world W W' :
    related_sts_pub_world W W' → related_sts_priv_world W W'.
  Proof.
    intros [Hrel Hrel'].
    split;[apply related_sts_std_pub_priv|apply related_sts_pub_priv];auto.
  Qed. 

  (* --------------------- pub a lemmas --------------------- *)

  Lemma related_sts_a_weak fsd gsd a a' :
    le_a a' a →
    related_sts_a fsd gsd a → related_sts_a fsd gsd a'.
  Proof.
    intros Hleb [Hdom Ha].
    split;auto. intros i x y Hx Hy.
    specialize (Ha i x y Hx Hy).
    eapply rtc_implies;[|eauto].
    intros r q Hr.
    destruct (decide (le_a i a')).
    - assert (le_a i a) as Hle.
      { assert (Transitive le_a) as Htrans;[eapply PreOrder_Transitive|trans a';auto]. }
      rewrite decide_True in Hr;auto.
    - destruct (decide (le_a i a));auto.
      Unshelve. apply le_a_preorder.
  Qed.

  Lemma related_sts_a_weak_world W W' a a' :
    le_a a' a →
    related_sts_a_world W W' a → related_sts_a_world W W' a'.
  Proof.
    destruct W,W'.
    intros Hle [Hrel Hrel']. split; simpl in *.
    - by pose proof (related_sts_a_weak _ _ _ _ Hle Hrel).
    - auto.
  Qed.

  Lemma related_sts_a_pub_plus fsd gsd a :
    related_sts_a fsd gsd a → related_sts_std_pub_plus fsd gsd.
  Proof.
    intros [Hdom Hrel]. split;auto.
    intros i x y Hx Hy.
    specialize (Hrel i x y Hx Hy).
    destruct (decide (le_a i a)).
    - apply rtc_or_intro. auto.
    - auto.
  Qed.

  Lemma related_sts_pub_a fsd gsd a :
    related_sts_std_pub fsd gsd → related_sts_a fsd gsd a.
  Proof.
    intros [Hdom Hrel].
    split;auto. intros i x y Hx Hy.
    specialize (Hrel i x y Hx Hy).
    destruct (decide (le_a i a)).
    - auto.
    - apply rtc_or_intro. auto.
  Qed. 

  Lemma related_sts_a_pub_plus_world W W' a :
    related_sts_a_world W W' a → related_sts_pub_plus_world W W'.
  Proof.
    intros [Hrel Hrel'].
    apply related_sts_a_pub_plus in Hrel.
    split;auto.
  Qed.

  Lemma related_sts_pub_a_world W W' a :
    related_sts_pub_world W W' → related_sts_a_world W W' a.
  Proof.
    intros [Hrel Hrel']. split.
    - apply related_sts_pub_a. auto.
    - apply related_sts_pub_pub_plus. auto.
  Qed.

  (* --------------------- TRANSITIVITY --------------------- *)

  Lemma related_sts_pub_trans fs fr gs gr hs hr :
    related_sts_pub fs gs fr gr → related_sts_pub gs hs gr hr →
    related_sts_pub fs hs fr hr.
  Proof.
    intros [Hf1 [Hf2 Hf3]] [Hg1 [Hg2 Hg3]]; split; [|split]; try by etrans.
    intros i r1 r2 r1' r2' r3 r3' Hfr Hhr.
    specialize (Hf1 i); specialize (Hf2 i);
      revert Hf1 Hf2; rewrite !elem_of_dom; intros Hf1 Hf2.
    destruct Hf2; eauto. destruct x as [[x1 x2] x3].
    edestruct Hf3 as [Heq1 [Heq2 [Heq3 Hrtc]] ] ; eauto; simplify_eq.
    edestruct Hg3 as [Heq1 [Heq2 [Heq3 Hrtc']] ] ; eauto; simplify_eq.
    repeat (split;auto).
    intros x y Hx Hy.
    destruct Hf1;eauto.
    etrans;eauto.
  Qed.

  Lemma related_sts_std_pub_trans fsd gsd hsd :
    related_sts_std_pub fsd gsd → related_sts_std_pub gsd hsd →
    related_sts_std_pub fsd hsd.
  Proof.
    intros [Hf1 Hf2] [Hg1 Hg2]; split; try by etrans.
    intros i x y Hx Hy.
    specialize (Hf1 i);
      revert Hf1; rewrite !elem_of_dom; intros Hf1.
    destruct Hf1 as [x0 Hx0]; eauto.
    specialize (Hf2 i x x0 Hx Hx0); simplify_eq.
    specialize (Hg2 i x0 y Hx0 Hy); simplify_eq.
    etrans;eauto.
  Qed.

  Lemma related_sts_priv_pub_trans fs fr gs gr hs hr :
    related_sts_priv fs gs fr gr → related_sts_pub gs hs gr hr →
    related_sts_priv fs hs fr hr.
  Proof.
    intros [Hf1 [Hf2 Hf3]] [Hg1 [Hg2 Hg3]]; split; [|split]; try by etrans.
    intros i r1 r2 r1' r2' r3 r3' Hfr Hhr.
    specialize (Hf1 i); specialize (Hf2 i);
      revert Hf1 Hf2; rewrite !elem_of_dom; intros Hf1 Hf2.
    destruct Hf2; eauto. destruct x as [[x1 x2] x3].
    edestruct Hf3 as [Heq1 [Heq2 [Heq3 Hrtc]] ] ; eauto; simplify_eq.
    edestruct Hg3 as [Heq1 [Heq2 [Heq3 Hrtc']] ] ; eauto; simplify_eq.
    repeat (split;auto).
    intros x y Hx Hy.
    destruct Hf1;eauto.
    etrans;eauto.
    apply rtc_or_intro; auto.
  Qed.

  Lemma related_sts_std_priv_pub_trans fsd gsd hsd :
    related_sts_std_priv fsd gsd → related_sts_std_pub gsd hsd →
    related_sts_std_priv fsd hsd.
  Proof.
    intros [Hf1 Hf2] [Hg1 Hg2]; split; try by etrans.
    intros i x y Hx Hy.
    specialize (Hf1 i);
      revert Hf1; rewrite !elem_of_dom; intros Hf1.
    destruct Hf1 as [x0 Hx0]; eauto.
    specialize (Hf2 i x x0 Hx Hx0); simplify_eq.
    specialize (Hg2 i x0 y Hx0 Hy); simplify_eq.
    etrans;eauto.
    apply rtc_or_intro; auto.
  Qed.

  Lemma related_sts_pub_priv_trans fs fr gs gr hs hr :
    related_sts_pub fs gs fr gr → related_sts_priv gs hs gr hr →
    related_sts_priv fs hs fr hr.
  Proof.
    intros [Hf1 [Hf2 Hf3]] [Hg1 [Hg2 Hg3]]; split; [|split]; try by etrans.
    intros i r1 r2 r1' r2' r3 r3' Hfr Hhr.
    specialize (Hf1 i); specialize (Hf2 i);
      revert Hf1 Hf2; rewrite !elem_of_dom; intros Hf1 Hf2.
    destruct Hf2; eauto. destruct x as [[x1 x2] x3].
    edestruct Hf3 as [Heq1 [Heq2 [Heq3 Hrtc]] ] ; eauto; simplify_eq.
    edestruct Hg3 as [Heq1 [Heq2 [Heq3 Hrtc']] ] ; eauto; simplify_eq.
    repeat (split;auto).
    intros x y Hx Hy.
    destruct Hf1;eauto.
    etrans;eauto.
    apply rtc_or_intro; auto.
  Qed.

  Lemma related_sts_std_pub_priv_trans fsd gsd hsd :
    related_sts_std_pub fsd gsd → related_sts_std_priv gsd hsd →
    related_sts_std_priv fsd hsd.
  Proof.
    intros [Hf1 Hf2] [Hg1 Hg2]; split; try by etrans.
    intros i x y Hx Hy.
    specialize (Hf1 i);
      revert Hf1; rewrite !elem_of_dom; intros Hf1.
    destruct Hf1 as [x0 Hx0]; eauto.
    specialize (Hf2 i x x0 Hx Hx0); simplify_eq.
    specialize (Hg2 i x0 y Hx0 Hy); simplify_eq.
    etrans;eauto.
    apply rtc_or_intro; auto.
  Qed.

  Lemma related_sts_priv_trans fs fr gs gr hs hr :
    related_sts_priv fs gs fr gr → related_sts_priv gs hs gr hr →
    related_sts_priv fs hs fr hr.
  Proof.
    intros [Hf1 [Hf2 Hf3]] [Hg1 [Hg2 Hg3]]; split; [|split]; try by etrans.
    intros i r1 r2 r1' r2' r3 r3' Hfr Hhr.
    specialize (Hf1 i); specialize (Hf2 i);
      revert Hf1 Hf2; rewrite !elem_of_dom; intros Hf1 Hf2.
    destruct Hf2; eauto. destruct x as [[x1 x2] x3].
    edestruct Hf3 as [Heq1 [Heq2 [Heq3 Hrtc]] ] ; eauto; simplify_eq.
    edestruct Hg3 as [Heq1 [Heq2 [Heq3 Hrtc']] ] ; eauto; simplify_eq.
    repeat (split;auto).
    intros x y Hx Hy.
    destruct Hf1;eauto.
    etrans;eauto.
  Qed.

  Lemma related_sts_std_priv_trans fsd gsd hsd :
    related_sts_std_priv fsd gsd → related_sts_std_priv gsd hsd →
    related_sts_std_priv fsd hsd.
  Proof.
    intros [Hf1 Hf2] [Hg1 Hg2]; split; try by etrans.
    intros i x y Hx Hy.
    specialize (Hf1 i);
      revert Hf1; rewrite !elem_of_dom; intros Hf1.
    destruct Hf1 as [x0 Hx0]; eauto.
    specialize (Hf2 i x x0 Hx Hx0); simplify_eq.
    specialize (Hg2 i x0 y Hx0 Hy); simplify_eq.
    etrans;eauto.
  Qed.

  Lemma related_sts_a_trans_left fsd gsd hsd a a' :
    le_a a a' →
    related_sts_a fsd gsd a → related_sts_a gsd hsd a' →
    related_sts_a fsd hsd a.
  Proof.
    intros Hle Hrel1 Hrel2.
    apply related_sts_a_weak with (a':=a) in Hrel2;[|auto].
    destruct Hrel1 as [Hf1 Hf2]; destruct Hrel2 as [Hg1 Hg2].
    split; try by etrans.
    intros i x y Hx Hy.
    specialize (Hf1 i);
      revert Hf1; rewrite !elem_of_dom; intros Hf1.
    destruct Hf1 as [x0 Hx0]; eauto.
    specialize (Hf2 i x x0 Hx Hx0); simplify_eq.
    specialize (Hg2 i x0 y Hx0 Hy); simplify_eq.
    etrans;eauto.
  Qed.

  Lemma related_sts_a_trans_right fsd gsd hsd a a' :
    le_a a a' →
    related_sts_a fsd gsd a' → related_sts_a gsd hsd a →
    related_sts_a fsd hsd a.
  Proof.
    intros Hle Hrel1 Hrel2.
    apply related_sts_a_weak with (a':=a) in Hrel1;[|auto].
    destruct Hrel1 as [Hf1 Hf2]; destruct Hrel2 as [Hg1 Hg2].
    split; try by etrans.
    intros i x y Hx Hy.
    specialize (Hf1 i);
      revert Hf1; rewrite !elem_of_dom; intros Hf1.
    destruct Hf1 as [x0 Hx0]; eauto.
    specialize (Hf2 i x x0 Hx Hx0); simplify_eq.
    specialize (Hg2 i x0 y Hx0 Hy); simplify_eq.
    etrans;eauto.
  Qed.

  (* Helper functions for transitivity of sts pairs *)
  Lemma related_sts_pub_priv_trans_world W W' W'' :
    related_sts_pub_world W W' -> related_sts_priv_world W' W'' ->
    related_sts_priv_world W W''.
  Proof.
    intros [Hpub_std Hpub_loc] [Hpriv_std Hpriv_loc].
    split.
    - apply related_sts_std_pub_priv_trans with W'.1; auto.
    - apply related_sts_pub_priv_trans with W'.2.1 W'.2.2; auto.
  Qed.

  Lemma related_sts_priv_pub_trans_world W W' W'' :
    related_sts_priv_world W W' -> related_sts_pub_world W' W'' ->
    related_sts_priv_world W W''.
  Proof.
    intros [Hpub_std Hpub_loc] [Hpriv_std Hpriv_loc].
    split.
    - apply related_sts_std_priv_pub_trans with W'.1; auto.
    - apply related_sts_priv_pub_trans with W'.2.1 W'.2.2; auto.
  Qed.

  Lemma related_sts_priv_trans_world W W' W'' :
    related_sts_priv_world W W' -> related_sts_priv_world W' W'' ->
    related_sts_priv_world W W''.
  Proof.
    intros [Hpub_std Hpub_loc] [Hpriv_std Hpriv_loc].
    split.
    - apply related_sts_std_priv_trans with W'.1; auto.
    - apply related_sts_priv_trans with W'.2.1 W'.2.2; auto.
  Qed.

  Lemma related_sts_pub_trans_world W W' W'' :
    related_sts_pub_world W W' -> related_sts_pub_world W' W'' ->
    related_sts_pub_world W W''.
  Proof.
    intros [Hpub_std Hpub_loc] [Hpriv_std Hpriv_loc].
    split.
    - apply related_sts_std_pub_trans with W'.1; auto.
    - apply related_sts_pub_trans with W'.2.1 W'.2.2; auto.
  Qed.


  Lemma related_sts_priv_world_std_sta_is_Some W W' i :
    related_sts_priv_world W W' -> is_Some ((W.1) !! i) -> is_Some ((W'.1) !! i).
  Proof.
    intros [ [Hdom1 _ ] _] Hsome.
    apply elem_of_gmap_dom in Hsome.
    apply elem_of_gmap_dom.
    apply elem_of_subseteq in Hdom1. auto.
  Qed.

  Lemma related_sts_priv_world_std_sta_region_type W W' i ρ :
    related_sts_priv_world W W' ->
    (W.1) !! i = Some ρ ->
    ∃ ρ', (W'.1) !! i = Some ρ'.
  Proof.
    intros Hrelated Hρ.
    assert (is_Some ((W'.1) !! i)) as [x Hx].
    { apply related_sts_priv_world_std_sta_is_Some with W; eauto. }
    destruct Hrelated as [ [Hdom1 Hrevoked ] _].
    specialize (Hrevoked _ _ _ Hρ Hx). simplify_eq.
    eauto.
  Qed.

  Lemma sts_full_rel_loc W i Q Q' P :
    sts_full_world W -∗ sts_rel_loc (A:=A) i Q Q' P  -∗
                   ⌜W.2.2 !! i = Some (convert_rel Q,convert_rel Q',convert_rel P)⌝.
  Proof.
    rewrite /sts_rel_loc /sts_full_world /sts_full.
    destruct W as [Wstd [fs fr]].
    iIntros "[_ [_ H1]] H2 /=".
    iDestruct (own_valid_2 with "H1 H2") as %[HR Hv]%auth_both_valid;
      iPureIntro.
    specialize (Hv i).
    revert HR. rewrite /= singleton_included_l;
      intros [z [Hz HR]]; revert HR; rewrite Some_included_total; intros HR.
    rewrite lookup_fmap in Hz, Hv.
    destruct (fr !! i) eqn:Heq; last by inversion Hz.
    revert Hv; rewrite Hz; intros [u Hu]%to_agree_uninj.
    revert HR; rewrite -Hu; intros HR%to_agree_included%leibniz_equiv;
      simplify_eq.
    inversion Hz as [? ? Hz'|]; simplify_eq.
    revert Hz'; rewrite -Hu. intros Hz'%(to_agree_inj (A:=leibnizO _) p _)%leibniz_equiv.
    by rewrite Hz'.
  Qed.

  Lemma sts_full_state_std W a b :
    sts_full_world W -∗ sts_state_std a b -∗ ⌜W.1 !! a = Some b⌝.
  Proof.
    rewrite /sts_full_world /sts_full /sts_state_std.
    destruct W as [Wsta Wloc].
    iIntros "[H1 _] H2".
    iDestruct (own_valid_2 with "H1 H2") as %[HR Hv]%auth_both_valid;
      iPureIntro.
    specialize (Hv a).
    revert HR; rewrite /= singleton_included_l;
      intros [z [Hz HR]].
    rewrite lookup_fmap in Hz Hv.
    destruct (Wsta !! a) eqn:Heq; rewrite Heq /= in Hz Hv; last by inversion Hz.
    apply leibniz_equiv in Hz; simplify_eq.
    apply Some_included_exclusive in HR; auto; last by typeclasses eauto.
    apply leibniz_equiv in HR; simplify_eq; eauto.
  Qed.

  Lemma sts_full_state_loc W i d :
    sts_full_world W -∗ sts_state_loc (A:=A) i d -∗ ⌜W.2.1 !! i = Some (encode d)⌝.
  Proof.
    rewrite /sts_full_world /sts_full /sts_state_loc.
    destruct W as [Wstd [fs fr] ].
    iIntros "[_ [H1 _]] H2".
    iDestruct (own_valid_2 with "H1 H2") as %[HR Hv]%auth_both_valid;
      iPureIntro.
    specialize (Hv i).
    revert HR; rewrite /= singleton_included_l;
      intros [z [Hz HR]].
    rewrite lookup_fmap in Hz Hv.
    destruct (fs !! i) eqn:Heq; last by inversion Hz.
    apply leibniz_equiv in Hz; simplify_eq. rewrite -Hz in HR.
    apply Some_included_exclusive in HR; auto; last by typeclasses eauto.
    apply leibniz_equiv in HR; simplify_eq; eauto.
  Qed.
 
  Lemma sts_dealloc_std W a b :
    sts_full_world W ∗ sts_state_std a b ==∗ sts_full_world (delete a W.1,W.2).
  Proof.
    rewrite /sts_full_world /sts_full /sts_state_std.
    destruct W as [fs Wloc].
    iIntros "[ [Hsta Hloc] Hstate] /=".
    iCombine "Hsta" "Hstate" as "H1".
    iMod (own_update
            (A := sts_std_stateUR A B)
            _ _
            (● (Excl <$> (delete a fs)))
            with "H1") as "H1".
    { apply auth_update_dealloc.
      rewrite fmap_delete /=.
      apply: delete_singleton_local_update. }
    iFrame. iModIntro. done.
  Qed.

  Lemma sts_alloc_std_i W a b :
    ⌜a ∉ dom (gset A) W.1⌝ -∗
    sts_full_world W ==∗
    sts_full_world (<[a := b]>W.1,W.2) ∗ sts_state_std a b.
  Proof.
    rewrite /sts_full_world /sts_full /sts_state_std /=.
    destruct W as [fsd Wloc]. rewrite /sts_full_std.
    iIntros (Hfresh1) "[H1 Hloc] /=".
    iMod (own_update
            (A := sts_std_stateUR A B)
            _ _
            (● (Excl <$> <[a :=b]> fsd)
            ⋅ ◯ {[a := Excl b]})
            with "H1") as "[H1 Hs]".
    { apply auth_update_alloc.
      rewrite fmap_insert /=.
      apply: alloc_singleton_local_update; last done.
      apply (not_elem_of_dom (D := gset A)).
      rewrite dom_fmap. auto. }
    iFrame. done.
  Qed.

  Lemma sts_alloc_loc W d Q Q' P:
    sts_full_world W ==∗
             ∃ i, sts_full_world (W.1,((<[i := encode d ]>W.2.1),(<[i := (convert_rel Q,convert_rel Q',convert_rel P) ]>W.2.2)))
                  ∗ ⌜i ∉ dom (gset positive) W.2.1⌝ ∗ ⌜i ∉ dom (gset positive) W.2.2⌝
                  ∗ sts_state_loc (A:=A) i d ∗ sts_rel_loc (A:=A) i Q Q' P.
  Proof.
    rewrite /sts_full_world /sts_full /sts_rel_loc /sts_state_loc.
    (* iIntros "[Hd [H1 H2]]". *)
    (* iDestruct "Hd" as %Hd. *)
    destruct W as [Wstd [fs fr]].
    iIntros "[Hstd [H1 H2]] /=".
    assert (fresh (dom (gset positive) fs ∪ dom (gset positive) fr) ∉
                    (dom (gset positive) fs ∪ dom (gset positive) fr)) as Hfresh.
    { apply is_fresh. }
    apply not_elem_of_union in Hfresh as [Hfs Hfr].
    iMod (own_update
            (A := sts_stateUR)
            _ _
            (● (Excl <$>
                <[fresh (dom (gset positive) fs ∪ dom (gset positive) fr) := encode d]> fs)
            ⋅ ◯ {[fresh (dom (gset positive) fs ∪ dom (gset positive) fr) := Excl (encode d)]})
            with "H1") as "[H1 Hs]".
    { apply auth_update_alloc.
      rewrite fmap_insert /=.
      apply: alloc_singleton_local_update; last done.
      apply (not_elem_of_dom (D := gset positive)).
      rewrite dom_fmap.
      auto. }
    iMod (own_update
            (A := sts_relUR)
            _ _
            (● (to_agree <$>
                <[fresh (dom (gset positive) fs ∪ dom (gset positive) fr) := (convert_rel Q,convert_rel Q',convert_rel P)]> fr)
            ⋅ ◯ {[fresh (dom (gset positive) fs ∪ dom (gset positive) fr) := to_agree (convert_rel Q,convert_rel Q',convert_rel P)]})
            with "H2") as "[H2 Hr]".
    { apply auth_update_alloc.
      rewrite fmap_insert /=.
      apply: alloc_singleton_local_update; last done.
      apply (not_elem_of_dom (D := gset positive)).
      rewrite dom_fmap.
      auto. }
    iModIntro.
    iExists _; iFrame.
    repeat iSplit; auto.
  Qed.

  Lemma sts_update_std W a b b' :
    sts_full_world W -∗ sts_state_std a b ==∗
    sts_full_world (<[a := b' ]>W.1,W.2) ∗ sts_state_std a b'.
  Proof.
    iIntros "Hsf Hi".
    iDestruct (sts_full_state_std with "Hsf Hi") as %Hfs.
    rewrite /sts_full_world /sts_full /sts_state_std.
    destruct W as [fsd Wloc].
    iDestruct "Hsf" as "[H1 Hloc] /=".
    iCombine "H1" "Hi" as "H1".
    iMod (own_update (A := sts_std_stateUR A B)
            _ _
            (● (<[a := Excl b']> (Excl <$> fsd))
               ⋅ ◯ {[a := Excl b']})
            with "H1") as "[H1 Hs]".
    { apply auth_update.
      apply: singleton_local_update; eauto.
      rewrite lookup_fmap Hfs //=.
      by apply exclusive_local_update. }
    iFrame. rewrite -fmap_insert;
              first iModIntro; iFrame.
  Qed.

  Lemma sts_update_loc W i d d' :
    sts_full_world W -∗ sts_state_loc (A:=A) i d ==∗
    sts_full_world (W.1,((<[i := encode d' ]>W.2.1),W.2.2)) ∗ sts_state_loc (A:=A) i d'.
  Proof.
    iIntros "Hsf Hi".
    iDestruct (sts_full_state_loc with "Hsf Hi") as %Hfs.
    rewrite /sts_full_world /sts_full /sts_rel_loc /sts_state_loc.
    destruct W as [Wstd [fs fr]].
    iDestruct "Hsf" as "[Hdst [H1 H2]] /=".
    iCombine "H1" "Hi" as "H1".
    iMod (own_update (A := sts_stateUR)
            _ _
            (● (<[i := Excl (encode d')]> (Excl <$> fs))
               ⋅ ◯ {[i := Excl (encode d')]})
            with "H1") as "[H1 Hs]".
    { apply auth_update.
      apply: singleton_local_update; eauto.
      rewrite lookup_fmap Hfs //=.
      by apply exclusive_local_update. }
    rewrite fmap_insert (* dom_insert_L *) (* subseteq_union_1_L *);
      first iModIntro; iFrame.
  Qed.

End STS.
