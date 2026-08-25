/-
  R47 R6 -- linking the balancing machinery's `ArmBalanced` to the capstone's `Balanced`.

  The single-hub balancing work (R47R6TransferArb / …Progress / …HnormSingleHub) uses
  `ArmBalanced arms := ∀ x y ∈ arms, x ≤ y + 1` (balanced to within one).  The `Hnorm`
  layer of `conjecture1_of_layers` instead requires the STRICTER `Balanced`, whose arm part
  is `BalancedArms arms := ∀ j ∈ arms, j = 4 ∨ j = 5` (arms pinned to {4,5}).

  This file records the honest relationship between the two:

    * `BalancedArms.armBalanced` -- `{4,5}`-arms ARE balanced-to-within-one (the extremal
      family sits inside the balancing machinery's fixed points).
    * `BalancedArms.floor`       -- `{4,5}`-arms satisfy the cherry floor `3 <= j`.
    * `transferStep_not_armBalanced` / `balancedArms_terminal` -- a capstone-`BalancedArms`
      single hub is TRANSFER-TERMINAL: no `TransferStep` fires on it.

  HONEST SCOPE.  This is CONNECTIVE, not reductive.  It shows the balancing process is
  consistent with (and terminates at states compatible with) the capstone's `Balanced`
  family -- but it does NOT produce `BalancedArms` from an arbitrary configuration.  The
  converse direction (`ArmBalanced` -> `BalancedArms`, i.e. pinning arms to exactly {4,5})
  is FALSE without a rate-optimality argument (within-one at value 10 is `ArmBalanced` but
  not `BalancedArms`), and is part of the genuinely open `Hnorm` core (arm-rate pinning,
  the arbitrary-tree -> hub reduction, `Capped`, and multi-hub extremality), none of which
  is discharged here.

  Self-contained; genuine proof (no `sorry`, no `axiom`).  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47Step
import R3Cert.R47R6TransferProgress

namespace R3Cert
namespace Step3

open RTree

/-- Capstone `BalancedArms` (arms ∈ {4,5}) implies `ArmBalanced` (within one). -/
theorem BalancedArms.armBalanced {arms : List ℕ} (h : BalancedArms arms) :
    ArmBalanced arms := by
  intro x hx y hy
  rcases h x hx with rfl | rfl <;> rcases h y hy with rfl | rfl <;> omega

/-- `{4,5}`-arms satisfy the cherry floor `3 ≤ j`. -/
theorem BalancedArms.floor {arms : List ℕ} (h : BalancedArms arms) :
    ∀ j ∈ arms, 3 ≤ j := by
  intro j hj; rcases h j hj with rfl | rfl <;> omega

/-- A `TransferStep` out of a single hub forces two arms differing by `≥ 2`, so those arms
    are NOT balanced-to-within-one. -/
theorem transferStep_not_armBalanced {arms : List ℕ} {c : ℕ} {s' : List Hub}
    (h : TransferStep [(arms, c)] s') : ¬ ArmBalanced arms := by
  obtain ⟨a, b, rest, A, A', C, ha, hb, _hd, hp, _hp', hs, _hs'⟩ := h
  simp only [List.cons.injEq, Prod.mk.injEq, and_true] at hs
  obtain ⟨rfl, rfl⟩ := hs
  intro hbal
  have hamem : a ∈ arms := (hp.mem_iff).mpr (by simp)
  have hbmem : b ∈ arms := (hp.mem_iff).mpr (by simp)
  have hle : b ≤ a + 1 := hbal b hbmem a hamem
  omega

/-- `ArmBalanced` single hubs are transfer-terminal: no `TransferStep` applies. -/
theorem armBalanced_no_transferStep {arms : List ℕ} {c : ℕ} (h : ArmBalanced arms) :
    ¬ ∃ s', TransferStep [(arms, c)] s' := by
  rintro ⟨s', hstep⟩
  exact transferStep_not_armBalanced hstep h

/-- **Capstone-`BalancedArms` single hubs are transfer-terminal.**  The extremal `{4,5}`-arm
    family lies among the balancing process's fixed points: no `TransferStep` fires. -/
theorem balancedArms_terminal {arms : List ℕ} {c : ℕ} (h : BalancedArms arms) :
    ¬ ∃ s', TransferStep [(arms, c)] s' :=
  armBalanced_no_transferStep h.armBalanced

end Step3
end R3Cert
