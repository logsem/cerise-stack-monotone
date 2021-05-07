From iris.program_logic Require Import language.
From stdpp Require Import list.

Section simulation.

  Definition final_state `{L: language} (s: cfg L): Prop :=
    Forall (λ e, is_Some (to_val e)) (fst s).

  Record forward_simulation `{L1: language} `{L2: language} (initial_state1: cfg L1) (initial_state2: cfg L2) :=
    mk_fsim {
        fsim: cfg L1 -> cfg L2 -> Prop;
        fsim_init_states: fsim initial_state1 initial_state2;
        fsim_step: forall s1 s2 s1', fsim s1 s1' -> erased_step s1 s2 ->
                                exists s2', rtc erased_step s1' s2' /\ fsim s2 s2';
        fsim_final_state: forall s s', final_state s -> fsim s s' -> final_state s'
    }.

  Lemma fsim_terminates:
    forall L1 L2 (initial_state1: cfg L1) (initial_state2: cfg L2) s,
      forward_simulation initial_state1 initial_state2 ->
      rtc erased_step initial_state1 s ->
      final_state s ->
      exists s', rtc erased_step initial_state2 s' /\ final_state s'.
  Proof.
    intros L1 L2 init_state1 init_state2 s Hsim Hsteps Hfinal.
    revert Hsim. revert init_state2. induction Hsteps; intros init_state2 Hsim.
    - exists init_state2. split. left. eapply fsim_final_state; eauto.
      eapply fsim_init_states; eauto.
    - eapply fsim_step in H; [|eapply fsim_init_states; eauto].
      destruct H as [y' [HA HB]].
      assert (Hsim': forward_simulation y (y': cfg L2)).
      { econstructor.
        - eapply HB.
        - intros. eapply fsim_step; eauto.
        - eapply fsim_final_state; eauto. }
      generalize (IHHsteps Hfinal y' Hsim'). intros [s' [HC HD]].
      exists s'; split; auto.
      eapply rtc_transitive; eauto.
      Unshelve. all: assumption.
  Qed.

End simulation.
