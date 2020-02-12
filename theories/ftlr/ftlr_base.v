From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.

Section fundamental.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            Heap: heapG Σ}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation WORLD := (leibnizO (STS * STS)). 
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (leibnizO Word) -n> iProp Σ).
  Notation R := (WORLD -n> (leibnizO Reg) -n> iProp Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).


  Definition ftlr_instr (W : WORLD) (r : leibnizO Reg) (p p' : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (i: instr) (ρ : region_type) := 
      p = RX ∨ p = RWX ∨ (p = RWLX /\ g = Local)
    → (∀ x : RegName, is_Some (r !! x))
    → isCorrectPC (inr (p, g, b, e, a))
    → (b <= a)%a ∧ (a < e)%a
    → PermFlows p p'
    → (if pwl p then region_state_pwl W a else region_state_nwl W a g)
    → region_std W a
    → std_sta W !! countable.encode a = Some (countable.encode ρ)
    → ρ ≠ Revoked 
    → p' ≠ O
    → cap_lang.decode w = i
    -> □ ▷ (∀ a0 a1 a2 a3 a4 a5 a6,
             full_map a1
          -∗ (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → ((fixpoint interp1) a0) (a1 !r! r1))
          -∗ registers_mapsto (<[PC:=inr (a2, a3, a4, a5, a6)]> a1)
          -∗ region a0
          -∗ sts_full_world sts_std a0
          -∗ na_own logrel_nais ⊤
          -∗ ⌜a2 = RX ∨ a2 = RWX ∨ (a2 = RWLX /\ a3 = Local)⌝
             → □ (∃ p'0 : Perm, ⌜PermFlows a2 p'0⌝
                                ∧ ([∗ list] a7 ∈ region_addrs a4 a5, read_write_cond a7 p'0 interp                                                                     
                                                                     ∧ ⌜if pwl a2
                                                                        then region_state_pwl a0 a7
                                                                        else region_state_nwl a0 a7 a3⌝
                                                                     ∧ ⌜region_std a0 a7⌝))
                 -∗ interp_conf a0)
    -∗ ([∗ list] a0 ∈ region_addrs b e, read_write_cond a0 p' interp
                                        ∧ ⌜if pwl p
                                           then region_state_pwl W a0
                                           else region_state_nwl W a0 g⌝
                                        ∧ ⌜region_std W a0⌝)
    -∗ (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → ((fixpoint interp1) W) (r !r! r1))
    -∗ read_write_cond a p' interp
    -∗ (▷ if decide (ρ = Temporary ∧ pwl p' = true)
        then future_pub_mono (λ Wv : prodO (leibnizO (STS * STS)) (leibnizO Word), ((fixpoint interp1) Wv.1) Wv.2) w
        else future_priv_mono (λ Wv : prodO (leibnizO (STS * STS)) (leibnizO Word), ((fixpoint interp1) Wv.1) Wv.2) w)
    -∗ ▷ ((fixpoint interp1) W) w
    -∗ sts_full_world sts_std W
    -∗ na_own logrel_nais ⊤
    -∗ open_region a W
    -∗ sts_state_std (countable.encode a) ρ
    -∗ a ↦ₐ[p'] w
    -∗ PC ↦ᵣ inr (p, g, b, e, a)
    -∗ ([∗ map] k↦y ∈ delete PC (<[PC:=inr (p, g, b, e, a)]> r), k ↦ᵣ y)
    -∗
        WP Instr Executable
        {{ v, WP Seq (cap_lang.of_val v)
                 {{ v0, ⌜v0 = HaltedV⌝
                        → ∃ (r1 : Reg) (W' : WORLD),
                        full_map r1
                        ∧ registers_mapsto r1
                                           ∗ ⌜related_sts_priv_world W W'⌝
                                           ∗ na_own logrel_nais ⊤
                                           ∗ sts_full_world sts_std W' ∗ region W' }} }}.

End fundamental.