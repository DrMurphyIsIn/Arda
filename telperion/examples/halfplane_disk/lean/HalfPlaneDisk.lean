/- telperion 0.1.6 | family HalfPlaneDisk | input-hash cacc492b1eb7dc3e
   5 theorems, 3 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace HalfPlaneDisk

/-- Moebius half-plane -> disk: `Re w ≤ 1` (with `1 > 0`) implies
    `‖w / (2*1 - w)‖ ≤ 1`.  Core: `4*1*(1 - Re w) ≥ 0`. -/
theorem halfplane_disk_one_core (w : ℂ) (hw : w.re ≤ 1) :
    ‖w / (2 * ((1 : ℝ) : ℂ) - w)‖ ≤ 1 := by
  have hB : (0:ℝ) < 1 := by norm_num
  have hden : (2 * ((1 : ℝ) : ℂ) - w) ≠ 0 := by
    intro hzero
    have hre : (2 * ((1 : ℝ) : ℂ) - w).re = 0 := by rw [hzero]; simp
    simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat,
      Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im, Complex.ofReal_one] at hre
    nlinarith [hw, hB, hre]
  have hpos : 0 < ‖2 * ((1 : ℝ) : ℂ) - w‖ := norm_pos_iff.mpr hden
  rw [norm_div, div_le_one hpos]
  have hsq : ‖w‖ ^ 2 ≤ ‖2 * ((1 : ℝ) : ℂ) - w‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat,
      Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im, Complex.ofReal_one]
    nlinarith [hw, hB, sq_nonneg w.im, sq_nonneg w.re,
      mul_nonneg hB.le (sub_nonneg.mpr hw)]
  have hnn : (0 : ℝ) ≤ ‖w‖ := norm_nonneg _
  nlinarith [hsq, hnn, hpos.le]
/-- Moebius half-plane -> disk: `Re w ≤ 2` (with `2 > 0`) implies
    `‖w / (2*2 - w)‖ ≤ 1`.  Core: `4*2*(2 - Re w) ≥ 0`. -/
theorem halfplane_disk_two_core (w : ℂ) (hw : w.re ≤ 2) :
    ‖w / (2 * ((2 : ℝ) : ℂ) - w)‖ ≤ 1 := by
  have hB : (0:ℝ) < 2 := by norm_num
  have hden : (2 * ((2 : ℝ) : ℂ) - w) ≠ 0 := by
    intro hzero
    have hre : (2 * ((2 : ℝ) : ℂ) - w).re = 0 := by rw [hzero]; simp
    simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat,
      Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im, Complex.ofReal_one] at hre
    nlinarith [hw, hB, hre]
  have hpos : 0 < ‖2 * ((2 : ℝ) : ℂ) - w‖ := norm_pos_iff.mpr hden
  rw [norm_div, div_le_one hpos]
  have hsq : ‖w‖ ^ 2 ≤ ‖2 * ((2 : ℝ) : ℂ) - w‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat,
      Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im, Complex.ofReal_one]
    nlinarith [hw, hB, sq_nonneg w.im, sq_nonneg w.re,
      mul_nonneg hB.le (sub_nonneg.mpr hw)]
  have hnn : (0 : ℝ) ≤ ‖w‖ := norm_nonneg _
  nlinarith [hsq, hnn, hpos.le]
/-- Moebius half-plane -> disk: `Re w ≤ (1 / 2)` (with `(1 / 2) > 0`) implies
    `‖w / (2*(1 / 2) - w)‖ ≤ 1`.  Core: `4*(1 / 2)*((1 / 2) - Re w) ≥ 0`. -/
theorem halfplane_disk_half_core (w : ℂ) (hw : w.re ≤ (1 / 2)) :
    ‖w / (2 * (((1 / 2) : ℝ) : ℂ) - w)‖ ≤ 1 := by
  have hB : (0:ℝ) < (1 / 2) := by norm_num
  have hden : (2 * (((1 / 2) : ℝ) : ℂ) - w) ≠ 0 := by
    intro hzero
    have hre : (2 * (((1 / 2) : ℝ) : ℂ) - w).re = 0 := by rw [hzero]; simp
    simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat,
      Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im, Complex.ofReal_one] at hre
    nlinarith [hw, hB, hre]
  have hpos : 0 < ‖2 * (((1 / 2) : ℝ) : ℂ) - w‖ := norm_pos_iff.mpr hden
  rw [norm_div, div_le_one hpos]
  have hsq : ‖w‖ ^ 2 ≤ ‖2 * (((1 / 2) : ℝ) : ℂ) - w‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat,
      Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im, Complex.ofReal_one]
    nlinarith [hw, hB, sq_nonneg w.im, sq_nonneg w.re,
      mul_nonneg hB.le (sub_nonneg.mpr hw)]
  have hnn : (0 : ℝ) ≤ ‖w‖ := norm_nonneg _
  nlinarith [hsq, hnn, hpos.le]
/-- Algebraic inversion: `w = g/(2*(1 / 2)−g)` with `2*(1 / 2)−g ≠ 0` implies
    `1 + w ≠ 0` and `g = 2*(1 / 2)*w/(1+w)`. -/
theorem halfplane_disk_half_inv {g w : ℂ}
    (hden : (2 * (((1 / 2) : ℝ) : ℂ) - g) ≠ 0)
    (hw : w = g / (2 * (((1 / 2) : ℝ) : ℂ) - g)) :
    (1 + w) ≠ 0 ∧ g = 2 * (((1 / 2) : ℝ) : ℂ) * w / (1 + w) := by
  have hBne : (2 * (((1 / 2) : ℝ) : ℂ)) ≠ 0 := by
    have hBc : (((1 / 2) : ℝ) : ℂ) ≠ 0 := by norm_num
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
    exact hBc
  subst hw
  have h1w : (1 : ℂ) + g / (2 * (((1 / 2) : ℝ) : ℂ) - g)
      = 2 * (((1 / 2) : ℝ) : ℂ) / (2 * (((1 / 2) : ℝ) : ℂ) - g) := by
    field_simp
    ring
  have h1wne : (1 + g / (2 * (((1 / 2) : ℝ) : ℂ) - g)) ≠ 0 := by
    rw [h1w]; exact div_ne_zero hBne hden
  refine ⟨h1wne, ?_⟩
  rw [eq_div_iff h1wne]
  field_simp
  ring
/-- Reverse-triangle bound: `‖w‖ ≤ t < 1` and `g = 2*(1 / 2)*w/(1+w)` implies
    `‖g‖ ≤ 2*(1 / 2)*t/(1−t)`. -/
theorem halfplane_disk_half_reverse {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {g w : ℂ} (hwt : ‖w‖ ≤ t) (h1w : (1 + w) ≠ 0)
    (hg : g = 2 * (((1 / 2) : ℝ) : ℂ) * w / (1 + w)) :
    ‖g‖ ≤ 2 * (1 / 2) * t / (1 - t) := by
  have hB : (0:ℝ) < (1 / 2) := by norm_num
  have hden_pos : 0 < ‖1 + w‖ := norm_pos_iff.mpr h1w
  have hrev : (1 : ℝ) - ‖w‖ ≤ ‖1 + w‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-w)
    simp only [norm_one, norm_neg, sub_neg_eq_add] at this
    simpa [sub_neg_eq_add] using this
  have h1mt_pos : 0 < 1 - t := by linarith
  have hlb : (1 : ℝ) - t ≤ ‖1 + w‖ := by linarith [hrev, hwt]
  have hnum : ‖2 * (((1 / 2) : ℝ) : ℂ) * w‖ = 2 * (1 / 2) * ‖w‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hB, Complex.norm_ofNat]
  rw [hg, norm_div, hnum]
  rw [div_le_div_iff₀ hden_pos h1mt_pos]
  have hlhs : 2 * (1 / 2) * ‖w‖ * (1 - t) ≤ 2 * (1 / 2) * t * ‖1 + w‖ := by
    have hBt : (0 : ℝ) ≤ 2 * (1 / 2) := by positivity
    nlinarith [hwt, hlb, ht0, hden_pos.le, mul_nonneg hBt ht0, hB.le]
  linarith [hlhs]

end HalfPlaneDisk
