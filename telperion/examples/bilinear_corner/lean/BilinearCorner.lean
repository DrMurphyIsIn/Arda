/- telperion 0.1.6 | family BilinearCorner | input-hash 0f10dc614f33bf00
   4 theorems, 3 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace BilinearCorner

/-- A bilinear form nonnegative at the four corners of a box is nonnegative on it. -/
theorem bilinear_corner_nonneg {A B C E s t s0 s1 t0 t1 : ℝ}
    (hs0 : s0 ≤ s) (hs1 : s ≤ s1) (ht0 : t0 ≤ t) (ht1 : t ≤ t1)
    (h00 : 0 ≤ A + B * s0 + C * t0 + E * (s0 * t0))
    (h01 : 0 ≤ A + B * s0 + C * t1 + E * (s0 * t1))
    (h10 : 0 ≤ A + B * s1 + C * t0 + E * (s1 * t0))
    (h11 : 0 ≤ A + B * s1 + C * t1 + E * (s1 * t1)) :
    0 ≤ A + B * s + C * t + E * (s * t) := by
  have hfix : ∀ sv : ℝ, 0 ≤ A + B * sv + C * t0 + E * (sv * t0) →
      0 ≤ A + B * sv + C * t1 + E * (sv * t1) →
      0 ≤ A + B * sv + C * t + E * (sv * t) := by
    intro sv e0 e1
    rcases le_total 0 (C + E * sv) with hb | hb
    · nlinarith [mul_nonneg hb (sub_nonneg.mpr ht0)]
    · nlinarith [mul_nonneg (neg_nonneg.mpr hb) (sub_nonneg.mpr ht1)]
  have H0 := hfix s0 h00 h01
  have H1 := hfix s1 h10 h11
  rcases le_total 0 (B + E * t) with hb | hb
  · nlinarith [mul_nonneg hb (sub_nonneg.mpr hs0)]
  · nlinarith [mul_nonneg (neg_nonneg.mpr hb) (sub_nonneg.mpr hs1)]

theorem bc_product_unit (s t : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ 1 + 1 * s + 1 * t + 1 * (s * t) := by
  have hc00 : (0:ℝ) ≤ 1 := by norm_num
  have hc01 : (0:ℝ) ≤ 2 := by norm_num
  have hc10 : (0:ℝ) ≤ 2 := by norm_num
  have hc11 : (0:ℝ) ≤ 4 := by norm_num
  have h00 : 0 ≤ 1 + 1 * 0 + 1 * 0 + 1 * (0 * 0) := by
    have : 1 + 1 * 0 + 1 * 0 + 1 * (0 * 0) = 1 := by norm_num
    rw [this]; exact hc00
  have h01 : 0 ≤ 1 + 1 * 0 + 1 * 1 + 1 * (0 * 1) := by
    have : 1 + 1 * 0 + 1 * 1 + 1 * (0 * 1) = 2 := by norm_num
    rw [this]; exact hc01
  have h10 : 0 ≤ 1 + 1 * 1 + 1 * 0 + 1 * (1 * 0) := by
    have : 1 + 1 * 1 + 1 * 0 + 1 * (1 * 0) = 2 := by norm_num
    rw [this]; exact hc10
  have h11 : 0 ≤ 1 + 1 * 1 + 1 * 1 + 1 * (1 * 1) := by
    have : 1 + 1 * 1 + 1 * 1 + 1 * (1 * 1) = 4 := by norm_num
    rw [this]; exact hc11
  exact bilinear_corner_nonneg hs0 hs1 ht0 ht1 h00 h01 h10 h11

theorem bc_mixed_slopes (s t : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ 3 + (-1) * s + (-2) * t + 1 * (s * t) := by
  have hc00 : (0:ℝ) ≤ 3 := by norm_num
  have hc01 : (0:ℝ) ≤ 1 := by norm_num
  have hc10 : (0:ℝ) ≤ 2 := by norm_num
  have hc11 : (0:ℝ) ≤ 1 := by norm_num
  have h00 : 0 ≤ 3 + (-1) * 0 + (-2) * 0 + 1 * (0 * 0) := by
    have : 3 + (-1) * 0 + (-2) * 0 + 1 * (0 * 0) = 3 := by norm_num
    rw [this]; exact hc00
  have h01 : 0 ≤ 3 + (-1) * 0 + (-2) * 1 + 1 * (0 * 1) := by
    have : 3 + (-1) * 0 + (-2) * 1 + 1 * (0 * 1) = 1 := by norm_num
    rw [this]; exact hc01
  have h10 : 0 ≤ 3 + (-1) * 1 + (-2) * 0 + 1 * (1 * 0) := by
    have : 3 + (-1) * 1 + (-2) * 0 + 1 * (1 * 0) = 2 := by norm_num
    rw [this]; exact hc10
  have h11 : 0 ≤ 3 + (-1) * 1 + (-2) * 1 + 1 * (1 * 1) := by
    have : 3 + (-1) * 1 + (-2) * 1 + 1 * (1 * 1) = 1 := by norm_num
    rw [this]; exact hc11
  exact bilinear_corner_nonneg hs0 hs1 ht0 ht1 h00 h01 h10 h11

theorem bc_shifted_box (s t : ℝ)
    (hs0 : (1 / 2) ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ (1 / 2) + 1 * s + (-1) * t + 2 * (s * t) := by
  have hc00 : (0:ℝ) ≤ 1 := by norm_num
  have hc01 : (0:ℝ) ≤ 1 := by norm_num
  have hc10 : (0:ℝ) ≤ (3 / 2) := by norm_num
  have hc11 : (0:ℝ) ≤ (5 / 2) := by norm_num
  have h00 : 0 ≤ (1 / 2) + 1 * (1 / 2) + (-1) * 0 + 2 * ((1 / 2) * 0) := by
    have : (1 / 2) + 1 * (1 / 2) + (-1) * 0 + 2 * ((1 / 2) * 0) = 1 := by norm_num
    rw [this]; exact hc00
  have h01 : 0 ≤ (1 / 2) + 1 * (1 / 2) + (-1) * 1 + 2 * ((1 / 2) * 1) := by
    have : (1 / 2) + 1 * (1 / 2) + (-1) * 1 + 2 * ((1 / 2) * 1) = 1 := by norm_num
    rw [this]; exact hc01
  have h10 : 0 ≤ (1 / 2) + 1 * 1 + (-1) * 0 + 2 * (1 * 0) := by
    have : (1 / 2) + 1 * 1 + (-1) * 0 + 2 * (1 * 0) = (3 / 2) := by norm_num
    rw [this]; exact hc10
  have h11 : 0 ≤ (1 / 2) + 1 * 1 + (-1) * 1 + 2 * (1 * 1) := by
    have : (1 / 2) + 1 * 1 + (-1) * 1 + 2 * (1 * 1) = (5 / 2) := by norm_num
    rw [this]; exact hc11
  exact bilinear_corner_nonneg hs0 hs1 ht0 ht1 h00 h01 h10 h11

end BilinearCorner
