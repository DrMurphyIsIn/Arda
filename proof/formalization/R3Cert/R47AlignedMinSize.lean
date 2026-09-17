/-
  Aligned-n scoping, formalized: a Balanced+Capped hub-state has size >= 46, so the capstone's `Hnorm`
  (`∃ Balanced+Capped s, stateSize s = usize t`) is UNSATISFIABLE for `0 < n < 46`.  This captures, in the
  kernel, the aligned-n limitation established numerically in `proof/verification/COVER_RELATION_STATUS.md`
  (Correction 2): the `conjecture1_of_layers_fixedN` reduction is inherently aligned-n scoped; small (and
  off-lattice) `n` are a separate residual.

  Min size 46 = a hub with exactly 5 load-4 arms and no cherry: `stateSize = 1 + 9·5 = 46`.

  Kernel-checked, no `sorry`, axiom-clean.  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47SharpRate
import R3Cert.R47Step
import R3Cert.R47Capped
import R3Cert.R47StepSize

namespace R3Cert
namespace Step3

open RTree

/-- A Balanced+Capped single hub has `stateSize ≥ 46` (min: 5 load-4 arms, no cherry). -/
theorem capped_singleHub_size_ge_46 (arms : List ℕ) (c : ℕ)
    (hbal : BalancedArms arms) (hcap : 5 ≤ arms.length) :
    46 ≤ stateSize [(arms, c)] := by
  rw [stateSize_singleHub arms c hbal]
  have hlen : arms.length = arms.count 5 + arms.count 4 := balancedArms_length arms hbal
  omega

/-- A NONEMPTY Balanced+Capped hub-state has `stateSize ≥ 46` (the first hub alone is ≥ 46). -/
theorem capped_state_size_ge_46 (s : List Hub)
    (hbal : Balanced s) (hcap : Capped s) (hne : s ≠ []) :
    46 ≤ stateSize s := by
  obtain ⟨h, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨arms, c⟩ := h
  have hb : BalancedArms arms := (hbal (arms, c) (by simp)).1
  have hc : 5 ≤ arms.length := hcap (arms, c) (by simp)
  have h1 : 46 ≤ stateSize [(arms, c)] := capped_singleHub_size_ge_46 arms c hb hc
  have hsplit : stateSize ((arms, c) :: t) = stateSize [(arms, c)] + stateSize t := by
    simp only [stateSize, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, add_zero]
  rw [hsplit]; omega

/-- **Aligned-n scoping.**  No Balanced+Capped hub-state has size `n` for `0 < n < 46`.  Hence the capstone
    `Hnorm` witness cannot exist for trees of such size — `conjecture1_of_layers_fixedN` is inherently
    aligned-n scoped, and small `n` are a separate residual. -/
theorem no_capped_state_of_size_lt_46 (s : List Hub) (n : ℕ)
    (h0 : 0 < n) (h46 : n < 46) (hbal : Balanced s) (hcap : Capped s) :
    stateSize s ≠ n := by
  intro hn
  rcases eq_or_ne s [] with rfl | hne
  · simp only [stateSize, List.map_nil, List.sum_nil] at hn; omega
  · have := capped_state_size_ge_46 s hbal hcap hne; omega

end Step3
end R3Cert
