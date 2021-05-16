From iris.program_logic Require Import language.
From cap_machine Require Import simulation linking.

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

