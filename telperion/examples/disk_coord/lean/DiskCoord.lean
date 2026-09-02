/- telperion 0.1.6 | family DiskCoord | input-hash b77d10c57a57619c
   3 theorems, 3 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace DiskCoord

/-- Disk -> coordinate bounds: `z ∈ closedBall (2 + 3·I) (1 / 2)`
    implies `2 - (1 / 2) ≤ z.re ≤ 2 + (1 / 2)` and
    `3 - (1 / 2) ≤ z.im ≤ 3 + (1 / 2)`.  Farkas-style linear
    certificate (radius (1 / 2) > 0). -/
theorem disk_coord_2_3i (z : ℂ)
    (hz : z ∈ Metric.closedBall (((2 : ℝ) : ℂ) + ((3 : ℝ) : ℂ) * Complex.I) ((1 / 2) : ℝ)) :
    (2 - (1 / 2) : ℝ) ≤ z.re ∧ z.re ≤ (2 : ℝ) + ((1 / 2) : ℝ) ∧
    (3 - (1 / 2) : ℝ) ≤ z.im ∧ z.im ≤ (3 : ℝ) + ((1 / 2) : ℝ) := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  set w : ℂ := ((2 : ℝ) : ℂ) + ((3 : ℝ) : ℂ) * Complex.I with hw
  have hwre : w.re = (2 : ℝ) := by simp [hw]
  have hwim : w.im = (3 : ℝ) := by simp [hw]
  have hre1 : |(z - w).re| ≤ ‖z - w‖ := Complex.abs_re_le_norm _
  have hre2 : (z - w).re = z.re - (2 : ℝ) := by rw [Complex.sub_re, hwre]
  rw [hre2] at hre1
  have hreb := abs_le.mp (le_trans hre1 hz)
  have him1 : |(z - w).im| ≤ ‖z - w‖ := Complex.abs_im_le_norm _
  have him2 : (z - w).im = z.im - (3 : ℝ) := by rw [Complex.sub_im, hwim]
  rw [him2] at him1
  have himb := abs_le.mp (le_trans him1 hz)
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith [hreb.1]
  · linarith [hreb.2]
  · linarith [himb.1]
  · linarith [himb.2]
/-- Disk -> coordinate bounds: `z ∈ closedBall ((-(1 / 2)) + 1·I) 1`
    implies `(-(1 / 2)) - 1 ≤ z.re ≤ (-(1 / 2)) + 1` and
    `1 - 1 ≤ z.im ≤ 1 + 1`.  Farkas-style linear
    certificate (radius 1 > 0). -/
theorem disk_coord_neg_half (z : ℂ)
    (hz : z ∈ Metric.closedBall ((((-(1 / 2)) : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I) (1 : ℝ)) :
    ((-(1 / 2)) - 1 : ℝ) ≤ z.re ∧ z.re ≤ ((-(1 / 2)) : ℝ) + (1 : ℝ) ∧
    (1 - 1 : ℝ) ≤ z.im ∧ z.im ≤ (1 : ℝ) + (1 : ℝ) := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  set w : ℂ := (((-(1 / 2)) : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I with hw
  have hwre : w.re = ((-(1 / 2)) : ℝ) := by simp [hw]
  have hwim : w.im = (1 : ℝ) := by simp [hw]
  have hre1 : |(z - w).re| ≤ ‖z - w‖ := Complex.abs_re_le_norm _
  have hre2 : (z - w).re = z.re - ((-(1 / 2)) : ℝ) := by rw [Complex.sub_re, hwre]
  rw [hre2] at hre1
  have hreb := abs_le.mp (le_trans hre1 hz)
  have him1 : |(z - w).im| ≤ ‖z - w‖ := Complex.abs_im_le_norm _
  have him2 : (z - w).im = z.im - (1 : ℝ) := by rw [Complex.sub_im, hwim]
  rw [him2] at him1
  have himb := abs_le.mp (le_trans him1 hz)
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith [hreb.1]
  · linarith [hreb.2]
  · linarith [himb.1]
  · linarith [himb.2]
/-- Disk -> coordinate bounds: `z ∈ closedBall (0 + (5 / 4)·I) (3 / 2)`
    implies `0 - (3 / 2) ≤ z.re ≤ 0 + (3 / 2)` and
    `(5 / 4) - (3 / 2) ≤ z.im ≤ (5 / 4) + (3 / 2)`.  Farkas-style linear
    certificate (radius (3 / 2) > 0). -/
theorem disk_coord_origin (z : ℂ)
    (hz : z ∈ Metric.closedBall (((0 : ℝ) : ℂ) + (((5 / 4) : ℝ) : ℂ) * Complex.I) ((3 / 2) : ℝ)) :
    (0 - (3 / 2) : ℝ) ≤ z.re ∧ z.re ≤ (0 : ℝ) + ((3 / 2) : ℝ) ∧
    ((5 / 4) - (3 / 2) : ℝ) ≤ z.im ∧ z.im ≤ ((5 / 4) : ℝ) + ((3 / 2) : ℝ) := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  set w : ℂ := ((0 : ℝ) : ℂ) + (((5 / 4) : ℝ) : ℂ) * Complex.I with hw
  have hwre : w.re = (0 : ℝ) := by simp [hw]
  have hwim : w.im = ((5 / 4) : ℝ) := by simp [hw]
  have hre1 : |(z - w).re| ≤ ‖z - w‖ := Complex.abs_re_le_norm _
  have hre2 : (z - w).re = z.re - (0 : ℝ) := by rw [Complex.sub_re, hwre]
  rw [hre2] at hre1
  have hreb := abs_le.mp (le_trans hre1 hz)
  have him1 : |(z - w).im| ≤ ‖z - w‖ := Complex.abs_im_le_norm _
  have him2 : (z - w).im = z.im - ((5 / 4) : ℝ) := by rw [Complex.sub_im, hwim]
  rw [him2] at him1
  have himb := abs_le.mp (le_trans him1 hz)
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith [hreb.1]
  · linarith [hreb.2]
  · linarith [himb.1]
  · linarith [himb.2]

end DiskCoord
