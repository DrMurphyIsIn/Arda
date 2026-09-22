/- LOW-HEIGHT ZERO BOX (li_positivity island, brief LI_FACE_BRIEF_2026-09-21 section 4).

   Two hypothesis-free localisation facts for the nontrivial zeros of `riemannZeta`, in Mathlib
   vocabulary only:

     Box 1  `zeta_zero_im_ge`      : a zero `s` with `0 < Re s < 1` has  `sqrt 3 / 2 ≤ |Im s|`;
     Box 2  `zeta_zero_confined`   : such a zero satisfies  `(Re s - 1/2)^2 ≤ (Im s)^2 / 3 - 1/4`.

   ROUTE (a) of the brief: the island already carries the UNCONDITIONAL fractional-part
   representation (StripReprAssembled, `ZeroFreeBridge.zeta_fract_repr`)

       zeta(s) = s/(s-1) - s * J(s),   J(s) = ∫_{x>1} {x} x^{-(s+1)} dx     (Re s > 0, s ≠ 1),

   but only the crude bound |J(s)| ≤ 1/Re s (`zeta_repr_integral_bound`), which localises nothing
   (it gives |Im s|^2 ≥ |2 Re s - 1|, empty at Re s = 1/2).  The new input is the SHARP bound

       |J(s)| ≤ ∫_{x>1} {x} x^{-(σ+1)} dx ≤ 1/(2σ)          (σ = Re s > 0),

   whose real-exponent half `LiFacePrelude.fract_integral_le_half_inv` lives in the shared pack
   `LiFacePrelude` (shapes audit P3, 2026-09-22; the rvm island's integration-by-parts proof of the
   same fact is retired against it).  It is proved by cutting [1, ∞) into the unit cells
   [n+1, n+2) and, on each cell with midpoint c = n + 3/2, using the pointwise sign inequality
   (x - c)(x^{-σ-1} - c^{-σ-1}) ≤ 0 (the kernel is decreasing) together with ∫_cell (x - c) dx = 0.
   No integration by parts and no continuity of {x} is needed.  Here the bound is transported to
   the complex integral (`norm_fractIntegral_le_half`); a zero then forces 2σ ≤ |s - 1|; the
   functional equation (Λ(1-s) = Λ(s), with Gammaℝ s ≠ 0 for Re s > 0) makes 1 - s a zero too,
   forcing 2(1-σ) ≤ |s|; adding the squares gives Box 2, and Box 2 gives Box 1.

   Nothing here proves, or bears on, whether RH holds: the box is an unconditional finite
   localisation (no zeros below height sqrt 3 / 2 ~ 0.866; the first zero is at ~ 14.13).
   conjecture1_proved = False.
-/
import Mathlib
import StripReprAssembled
import LiFacePrelude

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace LowHeightBox

/-! ## The complex tail integral. -/

/-- The sharp bound on the complex fractional-part integral: `‖J(s)‖ ≤ 1/(2 Re s)`. -/
theorem norm_fractIntegral_le_half {s : ℂ} (hs : 0 < s.re) :
    ‖ZeroFreeBridge.fractIntegral s‖ ≤ 1 / (2 * s.re) := by
  have hnorm : ∀ x ∈ Ioi (1 : ℝ),
      ‖ZeroFreeBridge.fractIntegrand s x‖ = Int.fract x * x ^ (-(s.re + 1)) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
    simp only [ZeroFreeBridge.fractIntegrand]
    rw [norm_div, Complex.norm_real, Complex.norm_cpow_eq_rpow_re_of_pos hx0,
      Complex.add_re, Complex.one_re, Real.norm_of_nonneg (Int.fract_nonneg x),
      Real.rpow_neg hx0.le, div_eq_mul_inv]
  calc ‖ZeroFreeBridge.fractIntegral s‖
      ≤ ∫ x in Ioi (1 : ℝ), ‖ZeroFreeBridge.fractIntegrand s x‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ x in Ioi (1 : ℝ), Int.fract x * x ^ (-(s.re + 1)) :=
        setIntegral_congr_fun measurableSet_Ioi hnorm
    _ ≤ 1 / (2 * s.re) := LiFacePrelude.fract_integral_le_half_inv hs

/-! ## Zeros in the strip. -/

/-- A zero of zeta in the open strip is at distance at least `2 Re s` from the pole. -/
theorem two_re_le_norm_sub_one {s : ℂ} (h0 : riemannZeta s = 0) (hre0 : 0 < s.re)
    (hre1 : s.re < 1) : 2 * s.re ≤ ‖s - 1‖ := by
  have hs1 : s ≠ 1 := by
    intro h; rw [h] at hre1; simp at hre1
  have hsD : s ∈ ZeroFreeBridge.stripDomain := ⟨hre0, by simpa using hs1⟩
  have hrepr := ZeroFreeBridge.zeta_fract_repr hsD
  rw [h0] at hrepr
  simp only [ZeroFreeBridge.stripRHS] at hrepr
  have heq : s / (s - 1) = s * ZeroFreeBridge.fractIntegral s := by
    have := hrepr.symm; rwa [sub_eq_zero] at this
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hre0; simp at hre0
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hs1n : 0 < ‖s - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hs1)
  have hJ := norm_fractIntegral_le_half hre0
  have hnormeq : ‖s‖ / ‖s - 1‖ = ‖s‖ * ‖ZeroFreeBridge.fractIntegral s‖ := by
    rw [← norm_div, ← norm_mul, heq]
  have hle : 1 / ‖s - 1‖ ≤ 1 / (2 * s.re) := by
    have h1 : ‖s‖ * (1 / ‖s - 1‖) ≤ ‖s‖ * (1 / (2 * s.re)) := by
      rw [mul_one_div, hnormeq]
      exact mul_le_mul_of_nonneg_left hJ hsn.le
    exact le_of_mul_le_mul_left h1 hsn
  exact (one_div_le_one_div hs1n (by linarith)).mp hle

/-- The functional-equation reflection: a zero `s` in the open strip gives a zero `1 - s`. -/
theorem zeta_one_sub_zero {s : ℂ} (h0 : riemannZeta s = 0) (hre0 : 0 < s.re)
    (hre1 : s.re < 1) : riemannZeta (1 - s) = 0 := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hre0; simp at hre0
  have hG : Gammaℝ s ≠ 0 := by
    rw [Ne, Gammaℝ_eq_zero_iff]
    rintro ⟨n, hn⟩
    have : s.re = -(2 * n) := by rw [hn]; simp
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hΛ : completedRiemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero hs0, div_eq_zero_iff] at h0
    exact h0.resolve_right hG
  have h1s : (1 : ℂ) - s ≠ 0 := by
    intro h
    have : (1 - s).re = 0 := by rw [h]; simp
    simp at this
    linarith
  rw [riemannZeta_def_of_ne_zero h1s, completedRiemannZeta_one_sub, hΛ, zero_div]

/-- **Box 2** (hypothesis-free): every zero of `riemannZeta` in the open strip satisfies
    `(Re s - 1/2)^2 ≤ (Im s)^2 / 3 - 1/4`. -/
theorem zeta_zero_confined (s : ℂ) (h0 : riemannZeta s = 0) (hre : 0 < s.re ∧ s.re < 1) :
    (s.re - 1 / 2) ^ 2 ≤ s.im ^ 2 / 3 - 1 / 4 := by
  obtain ⟨hre0, hre1⟩ := hre
  -- the zero itself: 2σ ≤ ‖s - 1‖
  have hA := two_re_le_norm_sub_one h0 hre0 hre1
  -- its reflection 1 - s: 2(1-σ) ≤ ‖(1 - s) - 1‖ = ‖s‖
  have h0' := zeta_one_sub_zero h0 hre0 hre1
  have hB := two_re_le_norm_sub_one h0' (by simp; linarith) (by simp; linarith)
  rw [show (1 : ℂ) - s - 1 = -s by ring, norm_neg] at hB
  simp only [Complex.sub_re, Complex.one_re] at hB
  -- square both, expand the norms
  have hA2 : (2 * s.re) ^ 2 ≤ ‖s - 1‖ ^ 2 := by
    have : 0 ≤ 2 * s.re := by linarith
    nlinarith
  have hB2 : (2 * (1 - s.re)) ^ 2 ≤ ‖s‖ ^ 2 := by
    have : 0 ≤ 2 * (1 - s.re) := by linarith
    nlinarith
  rw [Complex.sq_norm, Complex.normSq_apply] at hA2 hB2
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero] at hA2
  nlinarith

/-- **Box 1** (hypothesis-free): no zero of `riemannZeta` in the open strip has
    `|Im s| < sqrt 3 / 2`. -/
theorem zeta_zero_im_ge (s : ℂ) (h0 : riemannZeta s = 0) (hre : 0 < s.re ∧ s.re < 1) :
    Real.sqrt 3 / 2 ≤ |s.im| := by
  have hbox := zeta_zero_confined s h0 hre
  have hsq : (3 : ℝ) / 4 ≤ s.im ^ 2 := by nlinarith [sq_nonneg (s.re - 1 / 2)]
  have h1 : Real.sqrt (3 / 4) ≤ Real.sqrt (s.im ^ 2) := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq_eq_abs] at h1
  have h2 : Real.sqrt (3 / 4) = Real.sqrt 3 / 2 := by
    rw [show (3 / 4 : ℝ) = 3 / 2 ^ 2 by norm_num, Real.sqrt_div' _ (by norm_num),
      Real.sqrt_sq (by norm_num)]
  rw [h2] at h1
  exact h1

/-- **Real-axis corollary**: `riemannZeta x ≠ 0` for real `0 < x < 1` (a real zero would have
    `Im = 0 < sqrt 3 / 2`, contradicting Box 1). -/
theorem riemannZeta_ne_zero_of_unit_interval (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    riemannZeta (x : ℂ) ≠ 0 := by
  intro h0
  have h := zeta_zero_im_ge (x : ℂ) h0 (by simpa using ⟨hx0, hx1⟩)
  simp only [Complex.ofReal_im, abs_zero] at h
  have : (0 : ℝ) < Real.sqrt 3 / 2 := by positivity
  linarith

end LowHeightBox
