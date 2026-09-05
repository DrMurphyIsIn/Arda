/- telperion 0.1.6 | family SphereBound | input-hash 2261efff18abe2d9
   2 theorems, 2 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace SphereBound

-- strip→sphere bound (R = 1/2): a strip-type growth bound on f becomes a
-- UNIFORM bound on the sphere about c (c.re > R+1), via disk geometry.
theorem sphere_bound_half {f : ℂ → ℂ} {c : ℂ} (hcR : (1 / 2 : ℝ) + 1 < c.re)
    (hstrip : ∀ z ∈ Metric.sphere c (1 / 2 : ℝ), ‖f z‖ ≤ ‖z‖ / ‖z - 1‖ + ‖z‖ / z.re)
    {z : ℂ} (hz : z ∈ Metric.sphere c (1 / 2 : ℝ)) :
    ‖f z‖ ≤ (‖c‖ + (1 / 2 : ℝ)) / (c.re - (1 / 2 : ℝ) - 1) + (‖c‖ + (1 / 2 : ℝ)) / (c.re - (1 / 2 : ℝ)) := by
  have hzc : ‖z - c‖ = (1 / 2 : ℝ) := by
    rw [Metric.mem_sphere, Complex.dist_eq] at hz; exact hz
  have hre_dist : |z.re - c.re| ≤ (1 / 2 : ℝ) := by
    calc |z.re - c.re| = |(z - c).re| := by rw [Complex.sub_re]
      _ ≤ ‖z - c‖ := Complex.abs_re_le_norm _
      _ = (1 / 2 : ℝ) := hzc
  have hzre : c.re - (1 / 2 : ℝ) ≤ z.re := by have := (abs_le.mp hre_dist).1; linarith
  have hd1 : 0 < c.re - (1 / 2 : ℝ) - 1 := by linarith
  have hd2 : 0 < c.re - (1 / 2 : ℝ) := by linarith
  have hsb := hstrip z hz
  have hznorm : ‖z‖ ≤ ‖c‖ + (1 / 2 : ℝ) := by
    calc ‖z‖ = ‖(z - c) + c‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
      _ = ‖c‖ + (1 / 2 : ℝ) := by rw [hzc]; ring
  have hz1 : c.re - (1 / 2 : ℝ) - 1 ≤ ‖z - 1‖ := by
    calc c.re - (1 / 2 : ℝ) - 1 ≤ z.re - 1 := by linarith
      _ = (z - 1).re := by rw [Complex.sub_re, Complex.one_re]
      _ ≤ |(z - 1).re| := le_abs_self _
      _ ≤ ‖z - 1‖ := Complex.abs_re_le_norm _
  have hb1 : ‖z‖ / ‖z - 1‖ ≤ (‖c‖ + (1 / 2 : ℝ)) / (c.re - (1 / 2 : ℝ) - 1) := by gcongr
  have hb2 : ‖z‖ / z.re ≤ (‖c‖ + (1 / 2 : ℝ)) / (c.re - (1 / 2 : ℝ)) := by gcongr
  linarith [hsb, hb1, hb2]

-- strip→sphere bound (R = 1/4): a strip-type growth bound on f becomes a
-- UNIFORM bound on the sphere about c (c.re > R+1), via disk geometry.
theorem sphere_bound_qtr {f : ℂ → ℂ} {c : ℂ} (hcR : (1 / 4 : ℝ) + 1 < c.re)
    (hstrip : ∀ z ∈ Metric.sphere c (1 / 4 : ℝ), ‖f z‖ ≤ ‖z‖ / ‖z - 1‖ + ‖z‖ / z.re)
    {z : ℂ} (hz : z ∈ Metric.sphere c (1 / 4 : ℝ)) :
    ‖f z‖ ≤ (‖c‖ + (1 / 4 : ℝ)) / (c.re - (1 / 4 : ℝ) - 1) + (‖c‖ + (1 / 4 : ℝ)) / (c.re - (1 / 4 : ℝ)) := by
  have hzc : ‖z - c‖ = (1 / 4 : ℝ) := by
    rw [Metric.mem_sphere, Complex.dist_eq] at hz; exact hz
  have hre_dist : |z.re - c.re| ≤ (1 / 4 : ℝ) := by
    calc |z.re - c.re| = |(z - c).re| := by rw [Complex.sub_re]
      _ ≤ ‖z - c‖ := Complex.abs_re_le_norm _
      _ = (1 / 4 : ℝ) := hzc
  have hzre : c.re - (1 / 4 : ℝ) ≤ z.re := by have := (abs_le.mp hre_dist).1; linarith
  have hd1 : 0 < c.re - (1 / 4 : ℝ) - 1 := by linarith
  have hd2 : 0 < c.re - (1 / 4 : ℝ) := by linarith
  have hsb := hstrip z hz
  have hznorm : ‖z‖ ≤ ‖c‖ + (1 / 4 : ℝ) := by
    calc ‖z‖ = ‖(z - c) + c‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
      _ = ‖c‖ + (1 / 4 : ℝ) := by rw [hzc]; ring
  have hz1 : c.re - (1 / 4 : ℝ) - 1 ≤ ‖z - 1‖ := by
    calc c.re - (1 / 4 : ℝ) - 1 ≤ z.re - 1 := by linarith
      _ = (z - 1).re := by rw [Complex.sub_re, Complex.one_re]
      _ ≤ |(z - 1).re| := le_abs_self _
      _ ≤ ‖z - 1‖ := Complex.abs_re_le_norm _
  have hb1 : ‖z‖ / ‖z - 1‖ ≤ (‖c‖ + (1 / 4 : ℝ)) / (c.re - (1 / 4 : ℝ) - 1) := by gcongr
  have hb2 : ‖z‖ / z.re ≤ (‖c‖ + (1 / 4 : ℝ)) / (c.re - (1 / 4 : ℝ)) := by gcongr
  linarith [hsb, hb1, hb2]

end SphereBound
