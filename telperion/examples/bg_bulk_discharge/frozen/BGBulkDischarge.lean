/- telperion 0.1.6 | family BGBulkDischarge | input-hash f26bf66ab910fd8d
   2 theorems, 34 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace BG
namespace BulkDischarge

-- bg_bulk_fulledge_c4: Handelman certificate  p = Σ c_α ∏ ℓ_i^α (nonneg combination of constraint products) on the polytope.
theorem bg_bulk_fulledge_c4 : ∀ h1 h2 : ℝ, (0:ℝ) ≤ h1 → (0:ℝ) ≤ 1 - h1 → (0:ℝ) ≤ h2 → (0:ℝ) ≤ 1 - h2 → (0:ℝ) ≤ 12100 + 3300 * h1 + 3300 * h2 + 225 * h1 ^ 2 + 54 * h1 * h2 + 225 * h2 ^ 2 - 54 * h1 ^ 2 * h2 - 54 * h1 * h2 ^ 2 := by
  intro h1 h2 hx0 hx1 hy0 hy1
  have t1 : (0:ℝ) ≤ 12100 * (1 - h1)^3 * (1 - h2)^3 := mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ 12100)) (pow_nonneg hx1 3)) (pow_nonneg hy1 3)
  have t2 : (0:ℝ) ≤ 39600 * (1 - h1)^3 * (h2)^1 * (1 - h2)^2 := mul_nonneg (mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ 39600)) (pow_nonneg hx1 3)) (pow_nonneg hy0 1)) (pow_nonneg hy1 2)
  have t3 : (0:ℝ) ≤ 43125 * (1 - h1)^3 * (h2)^2 * (1 - h2)^1 := mul_nonneg (mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ 43125)) (pow_nonneg hx1 3)) (pow_nonneg hy0 2)) (pow_nonneg hy1 1)
  have t4 : (0:ℝ) ≤ 15625 * (1 - h1)^3 * (h2)^3 := mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ 15625)) (pow_nonneg hx1 3)) (pow_nonneg hy0 3)
  have t5 : (0:ℝ) ≤ 39600 * (h1)^1 * (1 - h1)^2 * (1 - h2)^3 := mul_nonneg (mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ 39600)) (pow_nonneg hx0 1)) (pow_nonneg hx1 2)) (pow_nonneg hy1 3)
  have t6 : (0:ℝ) ≤ 128754 * (h1)^1 * (1 - h1)^2 * (h2)^1 * (1 - h2)^2 := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ 128754)) (pow_nonneg hx0 1)) (pow_nonneg hx1 2)) (pow_nonneg hy0 1)) (pow_nonneg hy1 2)
  have t7 : (0:ℝ) ≤ 139329 * (h1)^1 * (1 - h1)^2 * (h2)^2 * (1 - h2)^1 := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ 139329)) (pow_nonneg hx0 1)) (pow_nonneg hx1 2)) (pow_nonneg hy0 2)) (pow_nonneg hy1 1)
  have t8 : (0:ℝ) ≤ 50175 * (h1)^1 * (1 - h1)^2 * (h2)^3 := mul_nonneg (mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ 50175)) (pow_nonneg hx0 1)) (pow_nonneg hx1 2)) (pow_nonneg hy0 3)
  have t9 : (0:ℝ) ≤ 43125 * (h1)^2 * (1 - h1)^1 * (1 - h2)^3 := mul_nonneg (mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ 43125)) (pow_nonneg hx0 2)) (pow_nonneg hx1 1)) (pow_nonneg hy1 3)
  have t10 : (0:ℝ) ≤ 139329 * (h1)^2 * (1 - h1)^1 * (h2)^1 * (1 - h2)^2 := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ 139329)) (pow_nonneg hx0 2)) (pow_nonneg hx1 1)) (pow_nonneg hy0 1)) (pow_nonneg hy1 2)
  have t11 : (0:ℝ) ≤ 149850 * (h1)^2 * (1 - h1)^1 * (h2)^2 * (1 - h2)^1 := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ 149850)) (pow_nonneg hx0 2)) (pow_nonneg hx1 1)) (pow_nonneg hy0 2)) (pow_nonneg hy1 1)
  have t12 : (0:ℝ) ≤ 53646 * (h1)^2 * (1 - h1)^1 * (h2)^3 := mul_nonneg (mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ 53646)) (pow_nonneg hx0 2)) (pow_nonneg hx1 1)) (pow_nonneg hy0 3)
  have t13 : (0:ℝ) ≤ 15625 * (h1)^3 * (1 - h2)^3 := mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ 15625)) (pow_nonneg hx0 3)) (pow_nonneg hy1 3)
  have t14 : (0:ℝ) ≤ 50175 * (h1)^3 * (h2)^1 * (1 - h2)^2 := mul_nonneg (mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ 50175)) (pow_nonneg hx0 3)) (pow_nonneg hy0 1)) (pow_nonneg hy1 2)
  have t15 : (0:ℝ) ≤ 53646 * (h1)^3 * (h2)^2 * (1 - h2)^1 := mul_nonneg (mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ 53646)) (pow_nonneg hx0 3)) (pow_nonneg hy0 2)) (pow_nonneg hy1 1)
  have t16 : (0:ℝ) ≤ 19096 * (h1)^3 * (h2)^3 := mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ 19096)) (pow_nonneg hx0 3)) (pow_nonneg hy0 3)
  have hid : (12100 + 3300 * h1 + 3300 * h2 + 225 * h1 ^ 2 + 54 * h1 * h2 + 225 * h2 ^ 2 - 54 * h1 ^ 2 * h2 - 54 * h1 * h2 ^ 2 : ℝ) = 12100 * (1 - h1)^3 * (1 - h2)^3 + 39600 * (1 - h1)^3 * (h2)^1 * (1 - h2)^2 + 43125 * (1 - h1)^3 * (h2)^2 * (1 - h2)^1 + 15625 * (1 - h1)^3 * (h2)^3 + 39600 * (h1)^1 * (1 - h1)^2 * (1 - h2)^3 + 128754 * (h1)^1 * (1 - h1)^2 * (h2)^1 * (1 - h2)^2 + 139329 * (h1)^1 * (1 - h1)^2 * (h2)^2 * (1 - h2)^1 + 50175 * (h1)^1 * (1 - h1)^2 * (h2)^3 + 43125 * (h1)^2 * (1 - h1)^1 * (1 - h2)^3 + 139329 * (h1)^2 * (1 - h1)^1 * (h2)^1 * (1 - h2)^2 + 149850 * (h1)^2 * (1 - h1)^1 * (h2)^2 * (1 - h2)^1 + 53646 * (h1)^2 * (1 - h1)^1 * (h2)^3 + 15625 * (h1)^3 * (1 - h2)^3 + 50175 * (h1)^3 * (h2)^1 * (1 - h2)^2 + 53646 * (h1)^3 * (h2)^2 * (1 - h2)^1 + 19096 * (h1)^3 * (h2)^3 := by ring
  rw [hid]; linarith

-- bg_bulk_fulledge_c5: Handelman certificate  p = Σ c_α ∏ ℓ_i^α (nonneg combination of constraint products) on the polytope.
theorem bg_bulk_fulledge_c5 : ∀ h1 h2 : ℝ, (0:ℝ) ≤ h1 → (0:ℝ) ≤ 1 - h1 → (0:ℝ) ≤ h2 → (0:ℝ) ≤ 1 - h2 → (0:ℝ) ≤ 3380 + 780 * h1 + 780 * h2 + 45 * h1 ^ 2 + 45 * h2 ^ 2 - 1314 * h1 * h2 - 162 * h1 ^ 2 * h2 - 162 * h1 * h2 ^ 2 := by
  intro h1 h2 hx0 hx1 hy0 hy1
  have t1 : (0:ℝ) ≤ 3380 * (1 - h1)^3 * (1 - h2)^3 := mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ 3380)) (pow_nonneg hx1 3)) (pow_nonneg hy1 3)
  have t2 : (0:ℝ) ≤ 10920 * (1 - h1)^3 * (h2)^1 * (1 - h2)^2 := mul_nonneg (mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ 10920)) (pow_nonneg hx1 3)) (pow_nonneg hy0 1)) (pow_nonneg hy1 2)
  have t3 : (0:ℝ) ≤ 11745 * (1 - h1)^3 * (h2)^2 * (1 - h2)^1 := mul_nonneg (mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ 11745)) (pow_nonneg hx1 3)) (pow_nonneg hy0 2)) (pow_nonneg hy1 1)
  have t4 : (0:ℝ) ≤ 4205 * (1 - h1)^3 * (h2)^3 := mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ 4205)) (pow_nonneg hx1 3)) (pow_nonneg hy0 3)
  have t5 : (0:ℝ) ≤ 10920 * (h1)^1 * (1 - h1)^2 * (1 - h2)^3 := mul_nonneg (mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ 10920)) (pow_nonneg hx0 1)) (pow_nonneg hx1 2)) (pow_nonneg hy1 3)
  have t6 : (0:ℝ) ≤ 33786 * (h1)^1 * (1 - h1)^2 * (h2)^1 * (1 - h2)^2 := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ 33786)) (pow_nonneg hx0 1)) (pow_nonneg hx1 2)) (pow_nonneg hy0 1)) (pow_nonneg hy1 2)
  have t7 : (0:ℝ) ≤ 34785 * (h1)^1 * (1 - h1)^2 * (h2)^2 * (1 - h2)^1 := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ 34785)) (pow_nonneg hx0 1)) (pow_nonneg hx1 2)) (pow_nonneg hy0 2)) (pow_nonneg hy1 1)
  have t8 : (0:ℝ) ≤ 11919 * (h1)^1 * (1 - h1)^2 * (h2)^3 := mul_nonneg (mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ 11919)) (pow_nonneg hx0 1)) (pow_nonneg hx1 2)) (pow_nonneg hy0 3)
  have t9 : (0:ℝ) ≤ 11745 * (h1)^2 * (1 - h1)^1 * (1 - h2)^3 := mul_nonneg (mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ 11745)) (pow_nonneg hx0 2)) (pow_nonneg hx1 1)) (pow_nonneg hy1 3)
  have t10 : (0:ℝ) ≤ 34785 * (h1)^2 * (1 - h1)^1 * (h2)^1 * (1 - h2)^2 := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ 34785)) (pow_nonneg hx0 2)) (pow_nonneg hx1 1)) (pow_nonneg hy0 1)) (pow_nonneg hy1 2)
  have t11 : (0:ℝ) ≤ 34146 * (h1)^2 * (1 - h1)^1 * (h2)^2 * (1 - h2)^1 := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ 34146)) (pow_nonneg hx0 2)) (pow_nonneg hx1 1)) (pow_nonneg hy0 2)) (pow_nonneg hy1 1)
  have t12 : (0:ℝ) ≤ 11106 * (h1)^2 * (1 - h1)^1 * (h2)^3 := mul_nonneg (mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ 11106)) (pow_nonneg hx0 2)) (pow_nonneg hx1 1)) (pow_nonneg hy0 3)
  have t13 : (0:ℝ) ≤ 4205 * (h1)^3 * (1 - h2)^3 := mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ 4205)) (pow_nonneg hx0 3)) (pow_nonneg hy1 3)
  have t14 : (0:ℝ) ≤ 11919 * (h1)^3 * (h2)^1 * (1 - h2)^2 := mul_nonneg (mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ 11919)) (pow_nonneg hx0 3)) (pow_nonneg hy0 1)) (pow_nonneg hy1 2)
  have t15 : (0:ℝ) ≤ 11106 * (h1)^3 * (h2)^2 * (1 - h2)^1 := mul_nonneg (mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ 11106)) (pow_nonneg hx0 3)) (pow_nonneg hy0 2)) (pow_nonneg hy1 1)
  have t16 : (0:ℝ) ≤ 3392 * (h1)^3 * (h2)^3 := mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ 3392)) (pow_nonneg hx0 3)) (pow_nonneg hy0 3)
  have hid : (3380 + 780 * h1 + 780 * h2 + 45 * h1 ^ 2 + 45 * h2 ^ 2 - 1314 * h1 * h2 - 162 * h1 ^ 2 * h2 - 162 * h1 * h2 ^ 2 : ℝ) = 3380 * (1 - h1)^3 * (1 - h2)^3 + 10920 * (1 - h1)^3 * (h2)^1 * (1 - h2)^2 + 11745 * (1 - h1)^3 * (h2)^2 * (1 - h2)^1 + 4205 * (1 - h1)^3 * (h2)^3 + 10920 * (h1)^1 * (1 - h1)^2 * (1 - h2)^3 + 33786 * (h1)^1 * (1 - h1)^2 * (h2)^1 * (1 - h2)^2 + 34785 * (h1)^1 * (1 - h1)^2 * (h2)^2 * (1 - h2)^1 + 11919 * (h1)^1 * (1 - h1)^2 * (h2)^3 + 11745 * (h1)^2 * (1 - h1)^1 * (1 - h2)^3 + 34785 * (h1)^2 * (1 - h1)^1 * (h2)^1 * (1 - h2)^2 + 34146 * (h1)^2 * (1 - h1)^1 * (h2)^2 * (1 - h2)^1 + 11106 * (h1)^2 * (1 - h1)^1 * (h2)^3 + 4205 * (h1)^3 * (1 - h2)^3 + 11919 * (h1)^3 * (h2)^1 * (1 - h2)^2 + 11106 * (h1)^3 * (h2)^2 * (1 - h2)^1 + 3392 * (h1)^3 * (h2)^3 := by ring
  rw [hid]; linarith

end BulkDischarge
end BG
