/- telperion 0.1.6 | family SlitLoopWindingZero | input-hash 610ef7c2793e577d
   2 theorems, 2 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace SlitLoopWindingZero

open Complex intervalIntegral

/-- Winding-zero (Rouché heart) with leash radius `1`: a closed loop `w` pinned
    inside `‖w-1‖ < 1 ≤ 1` (hence in the slit plane) has `∮ w'/w = 0` —
    winding number 0 about the origin.  The argument-principle-free engine of Rouché. -/
theorem slit_loop_winding_zero_one {a b : ℝ} (w w' : ℝ → ℂ)
    (hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt w (w' t) t)
    (hleash : ∀ t ∈ Set.uIcc a b, ‖w t - 1‖ < (1 : ℝ))
    (hint : IntervalIntegrable (fun t => w' t / w t) MeasureTheory.volume a b)
    (hclosed : w a = w b) :
    (∫ t in a..b, w' t / w t) = 0 := by
  have hslit : ∀ t ∈ Set.uIcc a b, w t ∈ Complex.slitPlane := by
    intro t ht
    have h1 : ‖w t - 1‖ < 1 := lt_of_lt_of_le (hleash t ht) (by norm_num : (1 : ℝ) ≤ 1)
    rw [Complex.mem_slitPlane_iff]; left
    have h2 : |(w t - 1).re| ≤ ‖w t - 1‖ := Complex.abs_re_le_norm _
    have h3 : |(w t).re - 1| < 1 := by
      have he : (w t - 1).re = (w t).re - 1 := by simp
      rw [he] at h2; linarith
    have := (abs_lt.mp h3).1; linarith
  have hd : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun t => Complex.log (w t)) (w' t / w t) t :=
    fun t ht => (hderiv t ht).clog_real (hslit t ht)
  rw [integral_eq_sub_of_hasDerivAt hd hint, hclosed, sub_self]
/-- Winding-zero (Rouché heart) with leash radius `(1 / 2)`: a closed loop `w` pinned
    inside `‖w-1‖ < (1 / 2) ≤ 1` (hence in the slit plane) has `∮ w'/w = 0` —
    winding number 0 about the origin.  The argument-principle-free engine of Rouché. -/
theorem slit_loop_winding_zero_half {a b : ℝ} (w w' : ℝ → ℂ)
    (hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt w (w' t) t)
    (hleash : ∀ t ∈ Set.uIcc a b, ‖w t - 1‖ < ((1 / 2) : ℝ))
    (hint : IntervalIntegrable (fun t => w' t / w t) MeasureTheory.volume a b)
    (hclosed : w a = w b) :
    (∫ t in a..b, w' t / w t) = 0 := by
  have hslit : ∀ t ∈ Set.uIcc a b, w t ∈ Complex.slitPlane := by
    intro t ht
    have h1 : ‖w t - 1‖ < 1 := lt_of_lt_of_le (hleash t ht) (by norm_num : ((1 / 2) : ℝ) ≤ 1)
    rw [Complex.mem_slitPlane_iff]; left
    have h2 : |(w t - 1).re| ≤ ‖w t - 1‖ := Complex.abs_re_le_norm _
    have h3 : |(w t).re - 1| < 1 := by
      have he : (w t - 1).re = (w t).re - 1 := by simp
      rw [he] at h2; linarith
    have := (abs_lt.mp h3).1; linarith
  have hd : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun t => Complex.log (w t)) (w' t / w t) t :=
    fun t ht => (hderiv t ht).clog_real (hslit t ht)
  rw [integral_eq_sub_of_hasDerivAt hd hint, hclosed, sub_self]

end SlitLoopWindingZero
