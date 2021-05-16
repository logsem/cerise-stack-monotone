From iris.algebra Require Import base.
From iris.program_logic Require Import language ectx_language ectxi_language.
From stdpp Require Import gmap fin_maps fin_sets.
From cap_machine Require Import addr_reg.

Section Linking.

  Variable b_stk: Addr.
  Variable e_stk: Addr.
  Variable stk_pos: (b_stk < e_stk)%a.

  Variable Symbols: Type.
  Variable Symbols_eq_dec: EqDecision Symbols.
  Variable Symbols_countable: Countable Symbols.

  Variable Word: Type.
  Variable can_address_only: Word -> gset Addr -> Prop.
  Variable pwl: Word -> bool.
  Variable is_global: Word -> bool.

  Definition imports: Type := gset (Symbols * Addr).
  Definition exports: Type := gmap Symbols Word.
  Definition segment: Type := gmap Addr Word.

  Definition pre_component: Type := (segment * imports * exports).
  Inductive component: Type :=
  | Lib: pre_component -> component
  | Main: pre_component -> Word -> component.

  Inductive well_formed_pre_comp: pre_component -> Prop :=
  | wf_pre_intro:
      forall ms imp exp
        (Hdisj: forall s, is_Some (exp !! s) -> ~ exists a, (s, a) ∈ imp)
        (Hexp: forall s w, exp !! s = Some w -> can_address_only w (dom _ ms))
        (Himp: forall s a, (s, a) ∈ imp -> is_Some (ms !! a))
        (Hnpwl: forall a w, ms !! a = Some w -> can_address_only w (dom _ ms) /\ pwl w = false /\ is_global w = true)
        (Hdisjstk: forall a, a ∈ dom (gset _) ms -> (e_stk <= a)%a), (* \/ (a < b_stk)%a *)
        well_formed_pre_comp (ms, imp, exp).

  Inductive well_formed_comp: component -> Prop :=
  | wf_lib:
      forall comp
        (Hwf_pre: well_formed_pre_comp comp),
        well_formed_comp (Lib comp)
  | wf_main:
      forall comp w_main
        (Hwf_pre: well_formed_pre_comp comp)
        (Hw_main: can_address_only w_main (dom _ (comp.1.1))),
        well_formed_comp (Main comp w_main).

  Inductive is_program: component -> Prop :=
  | is_program_intro:
      forall ms imp exp w_main
        (Hnoimports: imp = ∅)
        (Hwfcomp: well_formed_comp (Main (ms, imp, exp) w_main)),
        is_program (Main (ms,imp, exp) w_main).

  Definition resolve_imports (imp: imports) (exp: exports) (ms: segment) :=
    set_fold (fun '(s, a) m => match exp !! s with Some w => <[a:=w]> m | None => m end) ms imp.

  Inductive link_pre_comp: pre_component -> pre_component -> pre_component -> Prop :=
  | link_pre_comp_intro:
      forall ms1 ms2 ms imp1 imp2 imp exp1 exp2 exp
        (Hms_disj: forall a, is_Some (ms1 !! a) -> is_Some (ms2 !! a) -> False)
        (Hexp: exp = merge (fun o1 o2 => match o1 with | Some _ => o1 | None => o2 end) exp1 exp2)
        (Himp: forall s a, (s, a) ∈ imp <-> (((s, a) ∈ imp1 \/ (s, a) ∈ imp2) /\ exp !! s = None))
        (Hms: ms = resolve_imports imp2 exp (resolve_imports imp1 exp (merge (fun o1 o2 => match o1 with | Some _ => o1 | None => o2 end) ms1 ms2))),
        link_pre_comp (ms1, imp1, exp1) (ms2, imp2, exp2) (ms, imp, exp).

  Inductive link: component -> component -> component -> Prop :=
  | link_lib_lib:
      forall comp1 comp2 comp
        (Hlink: link_pre_comp comp1 comp2 comp),
        link (Lib comp1) (Lib comp2) (Lib comp)
  | link_lib_main:
      forall comp1 comp2 comp w_main
        (Hlink: link_pre_comp comp1 comp2 comp),
        link (Lib comp1) (Main comp2 w_main) (Main comp w_main)
  | link_main_lib:
      forall comp1 comp2 comp w_main
        (Hlink: link_pre_comp comp1 comp2 comp),
        link (Main comp1 w_main) (Lib comp2) (Main comp w_main).

  Inductive is_context (c comp p: component): Prop :=
  | is_context_intro:
      forall (His_program: link c comp p /\ is_program p),
      is_context c comp p.

End Linking.
