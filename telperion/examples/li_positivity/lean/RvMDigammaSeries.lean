/-
RvMDigammaSeries — building the polygamma-at-1/2 theory from the ground up.

This is the foundation for surmounting the Li archimedean main-term barrier by the ORTHOGONAL
Taylor/Möbius route (see RvMLiOrthogonal): the archimedean part of the Li coefficients is governed by
`ψ`-derivatives at `1/2` (exact polygamma values), NOT by any large-argument asymptotic.  Mathlib
has no polygamma/trigamma theory, so we build it.

PHASE 1 (this file, first): the specific ζ-value sum `∑_{k} 1/(k+1/2)² = π²/2` — the value of the
trigamma `ψ'(1/2)`.  Pure Basel + even/odd split, self-contained.

conjecture1_proved = False.  Classical special-function analysis; does not prove or approach RH.
-/
import Mathlib

open Real

namespace RvMDigammaSeries

/-- The Basel term `1/n²`, as a NAMED function so the even/odd split unifies first-order. -/
noncomputable def bTerm (n : ℕ) : ℝ := 1 / (n : ℝ) ^ 2

theorem hasSum_bTerm : HasSum bTerm (π ^ 2 / 6) := hasSum_zeta_two

/-- Even part of Basel: `∑_k bTerm(2k) = ∑_k 1/(2k)² = π²/24`. -/
theorem hasSum_bTerm_even : HasSum (fun k : ℕ => bTerm (2 * k)) (π ^ 2 / 24) := by
  have h := hasSum_zeta_two.mul_left (1 / 4 : ℝ)
  have e1 : (fun n : ℕ => (1 / 4 : ℝ) * (1 / (n : ℝ) ^ 2))
      = (fun k : ℕ => bTerm (2 * k)) := by
    funext n; simp only [bTerm]; push_cast; ring
  have e2 : (1 / 4 : ℝ) * (π ^ 2 / 6) = π ^ 2 / 24 := by ring
  rw [e1, e2] at h; exact h

theorem summable_bTerm_odd : Summable (fun k : ℕ => bTerm (2 * k + 1)) := by
  have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro a b h; simp only at h; omega
  have hc := hasSum_bTerm.summable.comp_injective hinj
  simpa [Function.comp_def] using hc

/-- Odd part of Basel: `∑_k bTerm(2k+1) = ∑_k 1/(2k+1)² = π²/8`. -/
theorem hasSum_bTerm_odd : HasSum (fun k : ℕ => bTerm (2 * k + 1)) (π ^ 2 / 8) := by
  have hcombine := HasSum.even_add_odd hasSum_bTerm_even summable_bTerm_odd.hasSum
  have huniq := hcombine.unique hasSum_bTerm
  have hval : (∑' k : ℕ, bTerm (2 * k + 1)) = π ^ 2 / 8 := by
    have h6 : π ^ 2 / 24 + (∑' k : ℕ, bTerm (2 * k + 1)) = π ^ 2 / 6 := huniq
    linarith
  rw [← hval]; exact summable_bTerm_odd.hasSum

/-- **PHASE 1 — the trigamma value at 1/2 (ζ-value form).**
    `∑_k 1/(k+1/2)² = π²/2` — this is `ψ'(1/2)`.  From Basel via the even/odd split. -/
theorem hasSum_one_div_add_half_sq :
    HasSum (fun k : ℕ => 1 / ((k : ℝ) + 1 / 2) ^ 2) (π ^ 2 / 2) := by
  -- 1/(k+1/2)² = 4·bTerm(2k+1)  (denominators never zero)
  have e1 : (fun k : ℕ => 1 / ((k : ℝ) + 1 / 2) ^ 2)
      = (fun k : ℕ => 4 * bTerm (2 * k + 1)) := by
    funext k
    simp only [bTerm]
    have hne2 : ((k : ℝ) + 1 / 2) ≠ 0 := by positivity
    have hne : ((2 * k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    field_simp
    ring
  have e2 : (4 : ℝ) * (π ^ 2 / 8) = π ^ 2 / 2 := by ring
  rw [e1, ← e2]
  exact hasSum_bTerm_odd.mul_left 4

end RvMDigammaSeries
