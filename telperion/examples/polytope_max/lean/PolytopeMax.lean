/- telperion 0.1.6 | family PolytopeMax | input-hash 60f35f6a44cae35f
   5 theorems, 3 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

set_option maxHeartbeats 1000000

namespace PolytopeMax

/-- A multi-affine (degree ≤ 1 per variable) form in 2 variable(s), nonnegative at all 4 corners of a box, is nonnegative on it. -/
theorem multiaffine_corner_nonneg_2
    {c c0 c1 c01 x0 x1 l0 l1 u0 u1 : ℝ}
    (hl0 : l0 ≤ x0) (hu0 : x0 ≤ u0) (hl1 : l1 ≤ x1) (hu1 : x1 ≤ u1)
    (h00 : 0 ≤ c + c0 * l0 + c1 * l1 + c01 * (l0 * l1))
    (h01 : 0 ≤ c + c0 * l0 + c1 * u1 + c01 * (l0 * u1))
    (h10 : 0 ≤ c + c0 * u0 + c1 * l1 + c01 * (u0 * l1))
    (h11 : 0 ≤ c + c0 * u0 + c1 * u1 + c01 * (u0 * u1)) :
    0 ≤ c + c0 * x0 + c1 * x1 + c01 * (x0 * x1) := by
  have hs1 : ∀ va0 : ℝ,
      0 ≤ c + c0 * va0 + c1 * l1 + c01 * (va0 * l1) →
      0 ≤ c + c0 * va0 + c1 * u1 + c01 * (va0 * u1) →
      0 ≤ c + c0 * va0 + c1 * x1 + c01 * (va0 * x1) := by
    intro va0 e_lo e_hi
    rcases le_total 0 (c1 + c01 * ((va0))) with hb | hb
    · nlinarith [mul_nonneg hb (sub_nonneg.mpr hl1)]
    · nlinarith [mul_nonneg (neg_nonneg.mpr hb) (sub_nonneg.mpr hu1)]
  have S1_0 := hs1 l0 h00 h01
  have S1_1 := hs1 u0 h10 h11
  rcases le_total 0 (c0 + c01 * ((x1))) with hb | hb
  · nlinarith [mul_nonneg hb (sub_nonneg.mpr hl0), S1_0, S1_1]
  · nlinarith [mul_nonneg (neg_nonneg.mpr hb) (sub_nonneg.mpr hu0), S1_0, S1_1]

/-- A multi-affine (degree ≤ 1 per variable) form in 3 variable(s), nonnegative at all 8 corners of a box, is nonnegative on it. -/
theorem multiaffine_corner_nonneg_3
    {c c0 c1 c2 c01 c02 c12 c012 x0 x1 x2 l0 l1 l2 u0 u1 u2 : ℝ}
    (hl0 : l0 ≤ x0) (hu0 : x0 ≤ u0) (hl1 : l1 ≤ x1) (hu1 : x1 ≤ u1) (hl2 : l2 ≤ x2) (hu2 : x2 ≤ u2)
    (h000 : 0 ≤ c + c0 * l0 + c1 * l1 + c2 * l2 + c01 * (l0 * l1) + c02 * (l0 * l2) + c12 * (l1 * l2) + c012 * (l0 * l1 * l2))
    (h001 : 0 ≤ c + c0 * l0 + c1 * l1 + c2 * u2 + c01 * (l0 * l1) + c02 * (l0 * u2) + c12 * (l1 * u2) + c012 * (l0 * l1 * u2))
    (h010 : 0 ≤ c + c0 * l0 + c1 * u1 + c2 * l2 + c01 * (l0 * u1) + c02 * (l0 * l2) + c12 * (u1 * l2) + c012 * (l0 * u1 * l2))
    (h011 : 0 ≤ c + c0 * l0 + c1 * u1 + c2 * u2 + c01 * (l0 * u1) + c02 * (l0 * u2) + c12 * (u1 * u2) + c012 * (l0 * u1 * u2))
    (h100 : 0 ≤ c + c0 * u0 + c1 * l1 + c2 * l2 + c01 * (u0 * l1) + c02 * (u0 * l2) + c12 * (l1 * l2) + c012 * (u0 * l1 * l2))
    (h101 : 0 ≤ c + c0 * u0 + c1 * l1 + c2 * u2 + c01 * (u0 * l1) + c02 * (u0 * u2) + c12 * (l1 * u2) + c012 * (u0 * l1 * u2))
    (h110 : 0 ≤ c + c0 * u0 + c1 * u1 + c2 * l2 + c01 * (u0 * u1) + c02 * (u0 * l2) + c12 * (u1 * l2) + c012 * (u0 * u1 * l2))
    (h111 : 0 ≤ c + c0 * u0 + c1 * u1 + c2 * u2 + c01 * (u0 * u1) + c02 * (u0 * u2) + c12 * (u1 * u2) + c012 * (u0 * u1 * u2)) :
    0 ≤ c + c0 * x0 + c1 * x1 + c2 * x2 + c01 * (x0 * x1) + c02 * (x0 * x2) + c12 * (x1 * x2) + c012 * (x0 * x1 * x2) := by
  have hs2 : ∀ va0 va1 : ℝ,
      0 ≤ c + c0 * va0 + c1 * va1 + c2 * l2 + c01 * (va0 * va1) + c02 * (va0 * l2) + c12 * (va1 * l2) + c012 * (va0 * va1 * l2) →
      0 ≤ c + c0 * va0 + c1 * va1 + c2 * u2 + c01 * (va0 * va1) + c02 * (va0 * u2) + c12 * (va1 * u2) + c012 * (va0 * va1 * u2) →
      0 ≤ c + c0 * va0 + c1 * va1 + c2 * x2 + c01 * (va0 * va1) + c02 * (va0 * x2) + c12 * (va1 * x2) + c012 * (va0 * va1 * x2) := by
    intro va0 va1 e_lo e_hi
    rcases le_total 0 (c2 + c02 * ((va0)) + c12 * ((va1)) + c012 * ((va0) * (va1))) with hb | hb
    · nlinarith [mul_nonneg hb (sub_nonneg.mpr hl2)]
    · nlinarith [mul_nonneg (neg_nonneg.mpr hb) (sub_nonneg.mpr hu2)]
  have hs1 : ∀ va0 : ℝ,
      0 ≤ c + c0 * va0 + c1 * l1 + c2 * x2 + c01 * (va0 * l1) + c02 * (va0 * x2) + c12 * (l1 * x2) + c012 * (va0 * l1 * x2) →
      0 ≤ c + c0 * va0 + c1 * u1 + c2 * x2 + c01 * (va0 * u1) + c02 * (va0 * x2) + c12 * (u1 * x2) + c012 * (va0 * u1 * x2) →
      0 ≤ c + c0 * va0 + c1 * x1 + c2 * x2 + c01 * (va0 * x1) + c02 * (va0 * x2) + c12 * (x1 * x2) + c012 * (va0 * x1 * x2) := by
    intro va0 e_lo e_hi
    rcases le_total 0 (c1 + c01 * ((va0)) + c12 * ((x2)) + c012 * ((va0) * (x2))) with hb | hb
    · nlinarith [mul_nonneg hb (sub_nonneg.mpr hl1)]
    · nlinarith [mul_nonneg (neg_nonneg.mpr hb) (sub_nonneg.mpr hu1)]
  have S2_00 := hs2 l0 l1 h000 h001
  have S2_01 := hs2 l0 u1 h010 h011
  have S2_10 := hs2 u0 l1 h100 h101
  have S2_11 := hs2 u0 u1 h110 h111
  have S1_0 := hs1 l0 S2_00 S2_01
  have S1_1 := hs1 u0 S2_10 S2_11
  rcases le_total 0 (c0 + c01 * ((x1)) + c02 * ((x2)) + c012 * ((x1) * (x2))) with hb | hb
  · nlinarith [mul_nonneg hb (sub_nonneg.mpr hl0), S1_0, S1_1]
  · nlinarith [mul_nonneg (neg_nonneg.mpr hb) (sub_nonneg.mpr hu0), S1_0, S1_1]

theorem pm_product_unit_3 (x0 x1 x2 : ℝ)
    (hl0 : 0 ≤ x0) (hu0 : x0 ≤ 1)
    (hl1 : 0 ≤ x1) (hu1 : x1 ≤ 1)
    (hl2 : 0 ≤ x2) (hu2 : x2 ≤ 1) :
    0 ≤ 1 + 1 * x0 + 1 * x1 + 1 * x2 + 1 * (x0 * x1) + 1 * (x0 * x2) + 1 * (x1 * x2) + 1 * (x0 * x1 * x2) := by
  have h000 : (0:ℝ) ≤ 1 + 1 * 0 + 1 * 0 + 1 * 0 + 1 * (0 * 0) + 1 * (0 * 0) + 1 * (0 * 0) + 1 * (0 * 0 * 0) := by
    have : 1 + 1 * 0 + 1 * 0 + 1 * 0 + 1 * (0 * 0) + 1 * (0 * 0) + 1 * (0 * 0) + 1 * (0 * 0 * 0) = (1 : ℝ) := by norm_num
    rw [this]; norm_num
  have h001 : (0:ℝ) ≤ 1 + 1 * 0 + 1 * 0 + 1 * 1 + 1 * (0 * 0) + 1 * (0 * 1) + 1 * (0 * 1) + 1 * (0 * 0 * 1) := by
    have : 1 + 1 * 0 + 1 * 0 + 1 * 1 + 1 * (0 * 0) + 1 * (0 * 1) + 1 * (0 * 1) + 1 * (0 * 0 * 1) = (2 : ℝ) := by norm_num
    rw [this]; norm_num
  have h010 : (0:ℝ) ≤ 1 + 1 * 0 + 1 * 1 + 1 * 0 + 1 * (0 * 1) + 1 * (0 * 0) + 1 * (1 * 0) + 1 * (0 * 1 * 0) := by
    have : 1 + 1 * 0 + 1 * 1 + 1 * 0 + 1 * (0 * 1) + 1 * (0 * 0) + 1 * (1 * 0) + 1 * (0 * 1 * 0) = (2 : ℝ) := by norm_num
    rw [this]; norm_num
  have h011 : (0:ℝ) ≤ 1 + 1 * 0 + 1 * 1 + 1 * 1 + 1 * (0 * 1) + 1 * (0 * 1) + 1 * (1 * 1) + 1 * (0 * 1 * 1) := by
    have : 1 + 1 * 0 + 1 * 1 + 1 * 1 + 1 * (0 * 1) + 1 * (0 * 1) + 1 * (1 * 1) + 1 * (0 * 1 * 1) = (4 : ℝ) := by norm_num
    rw [this]; norm_num
  have h100 : (0:ℝ) ≤ 1 + 1 * 1 + 1 * 0 + 1 * 0 + 1 * (1 * 0) + 1 * (1 * 0) + 1 * (0 * 0) + 1 * (1 * 0 * 0) := by
    have : 1 + 1 * 1 + 1 * 0 + 1 * 0 + 1 * (1 * 0) + 1 * (1 * 0) + 1 * (0 * 0) + 1 * (1 * 0 * 0) = (2 : ℝ) := by norm_num
    rw [this]; norm_num
  have h101 : (0:ℝ) ≤ 1 + 1 * 1 + 1 * 0 + 1 * 1 + 1 * (1 * 0) + 1 * (1 * 1) + 1 * (0 * 1) + 1 * (1 * 0 * 1) := by
    have : 1 + 1 * 1 + 1 * 0 + 1 * 1 + 1 * (1 * 0) + 1 * (1 * 1) + 1 * (0 * 1) + 1 * (1 * 0 * 1) = (4 : ℝ) := by norm_num
    rw [this]; norm_num
  have h110 : (0:ℝ) ≤ 1 + 1 * 1 + 1 * 1 + 1 * 0 + 1 * (1 * 1) + 1 * (1 * 0) + 1 * (1 * 0) + 1 * (1 * 1 * 0) := by
    have : 1 + 1 * 1 + 1 * 1 + 1 * 0 + 1 * (1 * 1) + 1 * (1 * 0) + 1 * (1 * 0) + 1 * (1 * 1 * 0) = (4 : ℝ) := by norm_num
    rw [this]; norm_num
  have h111 : (0:ℝ) ≤ 1 + 1 * 1 + 1 * 1 + 1 * 1 + 1 * (1 * 1) + 1 * (1 * 1) + 1 * (1 * 1) + 1 * (1 * 1 * 1) := by
    have : 1 + 1 * 1 + 1 * 1 + 1 * 1 + 1 * (1 * 1) + 1 * (1 * 1) + 1 * (1 * 1) + 1 * (1 * 1 * 1) = (8 : ℝ) := by norm_num
    rw [this]; norm_num
  exact multiaffine_corner_nonneg_3 hl0 hu0 hl1 hu1 hl2 hu2 h000 h001 h010 h011 h100 h101 h110 h111

theorem pm_mixed_slopes_3 (x0 x1 x2 : ℝ)
    (hl0 : 0 ≤ x0) (hu0 : x0 ≤ 1)
    (hl1 : 0 ≤ x1) (hu1 : x1 ≤ 1)
    (hl2 : 0 ≤ x2) (hu2 : x2 ≤ 1) :
    0 ≤ 4 + (-1) * x0 + (-1) * x1 + (-1) * x2 + 0 * (x0 * x1) + 0 * (x0 * x2) + 0 * (x1 * x2) + 1 * (x0 * x1 * x2) := by
  have h000 : (0:ℝ) ≤ 4 + (-1) * 0 + (-1) * 0 + (-1) * 0 + 0 * (0 * 0) + 0 * (0 * 0) + 0 * (0 * 0) + 1 * (0 * 0 * 0) := by
    have : 4 + (-1) * 0 + (-1) * 0 + (-1) * 0 + 0 * (0 * 0) + 0 * (0 * 0) + 0 * (0 * 0) + 1 * (0 * 0 * 0) = (4 : ℝ) := by norm_num
    rw [this]; norm_num
  have h001 : (0:ℝ) ≤ 4 + (-1) * 0 + (-1) * 0 + (-1) * 1 + 0 * (0 * 0) + 0 * (0 * 1) + 0 * (0 * 1) + 1 * (0 * 0 * 1) := by
    have : 4 + (-1) * 0 + (-1) * 0 + (-1) * 1 + 0 * (0 * 0) + 0 * (0 * 1) + 0 * (0 * 1) + 1 * (0 * 0 * 1) = (3 : ℝ) := by norm_num
    rw [this]; norm_num
  have h010 : (0:ℝ) ≤ 4 + (-1) * 0 + (-1) * 1 + (-1) * 0 + 0 * (0 * 1) + 0 * (0 * 0) + 0 * (1 * 0) + 1 * (0 * 1 * 0) := by
    have : 4 + (-1) * 0 + (-1) * 1 + (-1) * 0 + 0 * (0 * 1) + 0 * (0 * 0) + 0 * (1 * 0) + 1 * (0 * 1 * 0) = (3 : ℝ) := by norm_num
    rw [this]; norm_num
  have h011 : (0:ℝ) ≤ 4 + (-1) * 0 + (-1) * 1 + (-1) * 1 + 0 * (0 * 1) + 0 * (0 * 1) + 0 * (1 * 1) + 1 * (0 * 1 * 1) := by
    have : 4 + (-1) * 0 + (-1) * 1 + (-1) * 1 + 0 * (0 * 1) + 0 * (0 * 1) + 0 * (1 * 1) + 1 * (0 * 1 * 1) = (2 : ℝ) := by norm_num
    rw [this]; norm_num
  have h100 : (0:ℝ) ≤ 4 + (-1) * 1 + (-1) * 0 + (-1) * 0 + 0 * (1 * 0) + 0 * (1 * 0) + 0 * (0 * 0) + 1 * (1 * 0 * 0) := by
    have : 4 + (-1) * 1 + (-1) * 0 + (-1) * 0 + 0 * (1 * 0) + 0 * (1 * 0) + 0 * (0 * 0) + 1 * (1 * 0 * 0) = (3 : ℝ) := by norm_num
    rw [this]; norm_num
  have h101 : (0:ℝ) ≤ 4 + (-1) * 1 + (-1) * 0 + (-1) * 1 + 0 * (1 * 0) + 0 * (1 * 1) + 0 * (0 * 1) + 1 * (1 * 0 * 1) := by
    have : 4 + (-1) * 1 + (-1) * 0 + (-1) * 1 + 0 * (1 * 0) + 0 * (1 * 1) + 0 * (0 * 1) + 1 * (1 * 0 * 1) = (2 : ℝ) := by norm_num
    rw [this]; norm_num
  have h110 : (0:ℝ) ≤ 4 + (-1) * 1 + (-1) * 1 + (-1) * 0 + 0 * (1 * 1) + 0 * (1 * 0) + 0 * (1 * 0) + 1 * (1 * 1 * 0) := by
    have : 4 + (-1) * 1 + (-1) * 1 + (-1) * 0 + 0 * (1 * 1) + 0 * (1 * 0) + 0 * (1 * 0) + 1 * (1 * 1 * 0) = (2 : ℝ) := by norm_num
    rw [this]; norm_num
  have h111 : (0:ℝ) ≤ 4 + (-1) * 1 + (-1) * 1 + (-1) * 1 + 0 * (1 * 1) + 0 * (1 * 1) + 0 * (1 * 1) + 1 * (1 * 1 * 1) := by
    have : 4 + (-1) * 1 + (-1) * 1 + (-1) * 1 + 0 * (1 * 1) + 0 * (1 * 1) + 0 * (1 * 1) + 1 * (1 * 1 * 1) = (2 : ℝ) := by norm_num
    rw [this]; norm_num
  exact multiaffine_corner_nonneg_3 hl0 hu0 hl1 hu1 hl2 hu2 h000 h001 h010 h011 h100 h101 h110 h111

theorem pm_bilinear_d2 (x0 x1 : ℝ)
    (hl0 : 0 ≤ x0) (hu0 : x0 ≤ 1)
    (hl1 : 0 ≤ x1) (hu1 : x1 ≤ 1) :
    0 ≤ 3 + (-1) * x0 + (-2) * x1 + 1 * (x0 * x1) := by
  have h00 : (0:ℝ) ≤ 3 + (-1) * 0 + (-2) * 0 + 1 * (0 * 0) := by
    have : 3 + (-1) * 0 + (-2) * 0 + 1 * (0 * 0) = (3 : ℝ) := by norm_num
    rw [this]; norm_num
  have h01 : (0:ℝ) ≤ 3 + (-1) * 0 + (-2) * 1 + 1 * (0 * 1) := by
    have : 3 + (-1) * 0 + (-2) * 1 + 1 * (0 * 1) = (1 : ℝ) := by norm_num
    rw [this]; norm_num
  have h10 : (0:ℝ) ≤ 3 + (-1) * 1 + (-2) * 0 + 1 * (1 * 0) := by
    have : 3 + (-1) * 1 + (-2) * 0 + 1 * (1 * 0) = (2 : ℝ) := by norm_num
    rw [this]; norm_num
  have h11 : (0:ℝ) ≤ 3 + (-1) * 1 + (-2) * 1 + 1 * (1 * 1) := by
    have : 3 + (-1) * 1 + (-2) * 1 + 1 * (1 * 1) = (1 : ℝ) := by norm_num
    rw [this]; norm_num
  exact multiaffine_corner_nonneg_2 hl0 hu0 hl1 hu1 h00 h01 h10 h11

end PolytopeMax
