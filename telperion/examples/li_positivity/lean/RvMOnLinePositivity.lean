/-
RvMOnLinePositivity — Route P (creative): manifest positivity of on-line zero contributions.

The genus-1 paired-sum formula writes the Li coefficient as a sum over nontrivial zeros of
`liPairedSummand n ρ = liSummand n ρ + liSummand n (pairedZero ρ)` with
`liSummand n ρ = 1 - (1 - 1/ρ)^(-(n+1))` and `pairedZero ρ = 1 - ρ`.  Since the map `ρ ↦ 1 - ρ`
sends `w := 1 - 1/ρ` to `w⁻¹`, the paired summand is `2 - w^(n+1) - w^(-(n+1))`.

For a zero ON the critical line (`ρ.re = 1/2`) one has `|w| = 1`, hence `w^(-(n+1)) = conj(w^(n+1))`
and the paired summand collapses to a PERFECT SQUARE:

  * `onLine_liPairedSummand_eq_normSq` — `liPairedSummand n ρ = ‖1 - (1 - 1/ρ)^(n+1)‖²` (`ρ.re = 1/2`).
  * `onLine_liPairedSummand_nonneg` / `_im` — hence nonnegative and real.

This is unconditional and it is the honest engine of the Li criterion's easy direction: on-line zeros
contribute a manifest sum of squares.  It does NOT prove RH — off-line zeros lack `|w| = 1` and break
the square (the Li-level shadow of the (1,1) Hermitian signature).  conjecture1_proved = False.
-/
import Mathlib
import Lc.LiCriterion.Basic

open Complex

namespace RvMWeierstrass

/-- **On-line paired Li summand is a perfect square.**  For a nontrivial zero `ρ` with `ρ.re = 1/2`,
    `liPairedSummand n ρ = ‖1 - (1 - 1/ρ)^(n+1)‖²` — a manifest, unconditional SOS certificate. -/
theorem onLine_liPairedSummand_eq_normSq (n : ℕ) (ρ : LiCriterion.NontrivialZero)
    (hρ : ρ.val.re = 1 / 2) :
    LiCriterion.liPairedSummand n ρ
      = ((Complex.normSq (1 - (1 - 1 / ρ.val) ^ (n + 1)) : ℝ) : ℂ) := by
  have hρ0 : ρ.val ≠ 0 := LiCriterion.NontrivialZero.ne_zero ρ
  have hρ1 : ρ.val ≠ 1 := LiCriterion.NontrivialZero.ne_one ρ
  have hρ1' : ρ.val - 1 ≠ 0 := sub_ne_zero.mpr hρ1
  have h1ρ : (1 : ℂ) - ρ.val ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  set w : ℂ := 1 - 1 / ρ.val with hw
  -- |w| = 1, from re ρ = 1/2
  have hnρ0 : Complex.normSq ρ.val ≠ 0 := by rw [ne_eq, Complex.normSq_eq_zero]; exact hρ0
  have hwe : w = (ρ.val - 1) / ρ.val := by rw [hw, sub_div, div_self hρ0]
  have hnum : Complex.normSq (ρ.val - 1) = Complex.normSq ρ.val := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    rw [hρ]; ring
  have hnorm : Complex.normSq w = 1 := by
    rw [hwe, Complex.normSq_div, hnum, div_self hnρ0]
  -- the paired base is the inverse of w
  have hpair : (1 : ℂ) - 1 / (1 - ρ.val) = w⁻¹ := by
    rw [hwe, inv_div]; field_simp; ring
  -- negative zpow to nat pow
  have hzp : ∀ x : ℂ, x ^ (-(n + 1 : ℤ)) = (x ^ (n + 1))⁻¹ := by
    intro x; rw [zpow_neg]; congr 1
  have hpair_pow : (w⁻¹) ^ (-(n + 1 : ℤ)) = w ^ (n + 1) := by
    rw [hzp w⁻¹, inv_pow, inv_inv]
  -- unfold the paired summand and rewrite both bases
  simp only [LiCriterion.liPairedSummand, LiCriterion.liSummand, LiCriterion.pairedZero_val]
  rw [← hw, hpair, hzp w, hpair_pow]
  -- now: (1 - (w^(n+1))⁻¹) + (1 - w^(n+1)) = ↑‖1 - w^(n+1)‖²
  set u : ℂ := w ^ (n + 1) with hu
  have hu1 : Complex.normSq u = 1 := by rw [hu, map_pow, hnorm, one_pow]
  have huc : u * (starRingEnd ℂ) u = 1 := by rw [Complex.mul_conj, hu1, Complex.ofReal_one]
  have hinv : u⁻¹ = (starRingEnd ℂ) u := inv_eq_of_mul_eq_one_right huc
  rw [hinv, ← Complex.mul_conj (1 - u), map_sub, map_one]
  linear_combination -huc

/-- On-line zeros contribute nonnegatively to the Li coefficient. -/
theorem onLine_liPairedSummand_nonneg (n : ℕ) (ρ : LiCriterion.NontrivialZero)
    (hρ : ρ.val.re = 1 / 2) : 0 ≤ (LiCriterion.liPairedSummand n ρ).re := by
  rw [onLine_liPairedSummand_eq_normSq n ρ hρ, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

/-- The on-line paired summand is real. -/
theorem onLine_liPairedSummand_im (n : ℕ) (ρ : LiCriterion.NontrivialZero)
    (hρ : ρ.val.re = 1 / 2) : (LiCriterion.liPairedSummand n ρ).im = 0 := by
  rw [onLine_liPairedSummand_eq_normSq n ρ hρ, Complex.ofReal_im]

end RvMWeierstrass
