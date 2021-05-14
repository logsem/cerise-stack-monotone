From iris.program_logic Require Import language.
From stdpp Require Import list.

Section simulation.

  Definition final_state `{L: language} (s: cfg L) (v: val L): Prop :=
    exists e, fst s = [e] /\ to_val e = Some v.

  Record forward_simulation `{L1: language} `{L2: language}
         (initial_state1: cfg L1)
         (initial_state2: cfg L2)
         (fsim: cfg L1 -> cfg L2 -> Prop)
         (fsim_val: val L1 -> val L2 -> Prop): Prop :=
    mk_fsim {
        fsim_init_states: fsim initial_state1 initial_state2;
        fsim_step: forall s1 s2 s1', fsim s1 s1' -> erased_step s1 s2 ->
                                exists s2', rtc erased_step s1' s2' /\ fsim s2 s2';
        fsim_final_states: forall s s' v, final_state s v -> fsim s s' -> exists v', final_state s' v' /\ fsim_val v v'
    }.

  Lemma fsim_terminates:
    forall L1 L2 (initial_state1: cfg L1) (initial_state2: cfg L2) fsim fsim_val (Hsim: forward_simulation initial_state1 initial_state2 fsim fsim_val) s v,
      rtc erased_step initial_state1 s ->
      final_state s v ->
      exists s' v', rtc erased_step initial_state2 s' /\ final_state s' v' /\ fsim_val v v'.
  Proof.
    intros L1 L2 init_state1 init_state2 fsim fsim_val Hsim s v Hsteps Hfinal.
    revert Hsim. revert init_state2. induction Hsteps; intros init_state2 Hsim.
    - eapply (fsim_final_states _ _ _ _ Hsim) in Hfinal; eauto.
      destruct Hfinal as [v' [A B]].
      exists init_state2, v'. split; [left|split; eauto].
      eapply fsim_init_states; eauto.
    - eapply (fsim_step _ _ _ _ Hsim) in H; [|eapply fsim_init_states; eauto].
      destruct H as [y' [HA HB]].
      assert (Hsim': forward_simulation y y' fsim fsim_val).
      { econstructor.
        - eapply HB.
        - intros. eapply fsim_step; eauto.
        - intros. eapply fsim_final_states; eauto. }
      generalize (IHHsteps Hfinal y' Hsim'). intros [s' [v' [HC [HD HE]]]].
      exists s', v'; split; auto.
      eapply rtc_transitive; eauto.
  Qed.

End simulation.
