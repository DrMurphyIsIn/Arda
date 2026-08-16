/- telperion 0.1.1 | family ToySplit | input-hash 27bea50800930a58
   13 theorems, 15 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib
import Toy.Box

namespace Toy

/-! ### Instance (a = 1) -/

noncomputable def toy_split_a1_qLc1 (u v : ℝ) : ℝ :=
  (1) / ((2 + u) * (2 + v))

noncomputable def toy_split_a1_qLc2 (u v : ℝ) : ℝ :=
  (0 - 1) / (2 * (2 + u))

noncomputable def toy_split_a1_qLc3 (u v : ℝ) : ℝ :=
  (0 - 1) / (2 * (2 + v))

noncomputable def toy_split_a1_qLc4 (u v : ℝ) : ℝ :=
  (1) / ((2 + u) * (2 + v))

theorem toy_split_a1_qL_bilinear (u v q r : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (40 + 36 * u + 36 * v + 8 * q + 8 * r + 8 * u ^ 2 + 34 * u * v + 4 * u * q + 8 * u * r + 8 * v ^ 2 + 8 * v * q + 4 * v * r + 16 * q * r + 8 * u ^ 2 * v + 2 * u ^ 2 * r + 8 * u * v ^ 2 + 4 * u * v * q + 4 * u * v * r + 8 * u * q * r + 2 * v ^ 2 * q + 8 * v * q * r + 2 * u ^ 2 * v ^ 2 + u ^ 2 * v * r + u * v ^ 2 * q + 4 * u * v * q * r) / (2 * (2 + u) * (2 + u) * (2 + v) * (2 + v)) - (16 + 16 * u + 16 * v + 8 * q + 8 * r + 4 * u ^ 2 + 16 * u * v + 4 * u * q + 8 * u * r + 4 * v ^ 2 + 8 * v * q + 4 * v * r + 4 * q * r + 4 * u ^ 2 * v + 2 * u ^ 2 * r + 4 * u * v ^ 2 + 4 * u * v * q + 4 * u * v * r + 2 * u * q * r + 2 * v ^ 2 * q + 2 * v * q * r + u ^ 2 * v ^ 2 + u ^ 2 * v * r + u * v ^ 2 * q + u * v * q * r) / ((2 + u) * (2 + u) * (2 + v) * (2 + v))
      = toy_split_a1_qLc1 u v + toy_split_a1_qLc2 u v * q + toy_split_a1_qLc3 u v * r
        + toy_split_a1_qLc4 u v * (q * r) := by
  have hd1 : (2 + u : ℝ) ≠ 0 := by positivity
  have hd2 : (2 + v : ℝ) ≠ 0 := by positivity
  simp only [toy_split_a1_qLc1, toy_split_a1_qLc2, toy_split_a1_qLc3, toy_split_a1_qLc4]
  push_cast
  field_simp
  try ring

theorem toy_split_a1_qL_corner00 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ toy_split_a1_qLc1 u v + toy_split_a1_qLc2 u v * (0) + toy_split_a1_qLc3 u v * (0)
        + toy_split_a1_qLc4 u v * ((0) * (0)) := by
  have hd1 : (2 + u : ℝ) ≠ 0 := by positivity
  have hd2 : (2 + v : ℝ) ≠ 0 := by positivity
  have hkey : toy_split_a1_qLc1 u v + toy_split_a1_qLc2 u v * (0) + toy_split_a1_qLc3 u v * (0)
        + toy_split_a1_qLc4 u v * ((0) * (0))
      = (1)
        / ((2 + u) * (2 + v)) := by
    simp only [toy_split_a1_qLc1, toy_split_a1_qLc2, toy_split_a1_qLc3, toy_split_a1_qLc4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem toy_split_a1_qL_corner01 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ toy_split_a1_qLc1 u v + toy_split_a1_qLc2 u v * (0) + toy_split_a1_qLc3 u v * ((1) / ((2 + u)))
        + toy_split_a1_qLc4 u v * ((0) * ((1) / ((2 + u)))) := by
  have hd1 : (2 + u : ℝ) ≠ 0 := by positivity
  have hd2 : (2 + v : ℝ) ≠ 0 := by positivity
  have hkey : toy_split_a1_qLc1 u v + toy_split_a1_qLc2 u v * (0) + toy_split_a1_qLc3 u v * ((1) / ((2 + u)))
        + toy_split_a1_qLc4 u v * ((0) * ((1) / ((2 + u))))
      = (4 + 2 * u + 2 * v + u * v)
        / (2 * (2 + u) * (2 + u) * (2 + v) * (2 + v)) := by
    simp only [toy_split_a1_qLc1, toy_split_a1_qLc2, toy_split_a1_qLc3, toy_split_a1_qLc4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem toy_split_a1_qL_corner10 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ toy_split_a1_qLc1 u v + toy_split_a1_qLc2 u v * ((1) / (2 * (2 + v))) + toy_split_a1_qLc3 u v * (0)
        + toy_split_a1_qLc4 u v * (((1) / (2 * (2 + v))) * (0)) := by
  have hd1 : (2 + u : ℝ) ≠ 0 := by positivity
  have hd2 : (2 + v : ℝ) ≠ 0 := by positivity
  have hkey : toy_split_a1_qLc1 u v + toy_split_a1_qLc2 u v * ((1) / (2 * (2 + v))) + toy_split_a1_qLc3 u v * (0)
        + toy_split_a1_qLc4 u v * (((1) / (2 * (2 + v))) * (0))
      = (12 + 6 * u + 6 * v + 3 * u * v)
        / (4 * (2 + u) * (2 + u) * (2 + v) * (2 + v)) := by
    simp only [toy_split_a1_qLc1, toy_split_a1_qLc2, toy_split_a1_qLc3, toy_split_a1_qLc4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem toy_split_a1_qL_corner11 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ toy_split_a1_qLc1 u v + toy_split_a1_qLc2 u v * ((1) / (2 * (2 + v))) + toy_split_a1_qLc3 u v * ((1) / ((2 + u)))
        + toy_split_a1_qLc4 u v * (((1) / (2 * (2 + v))) * ((1) / ((2 + u)))) := by
  have hd1 : (2 + u : ℝ) ≠ 0 := by positivity
  have hd2 : (2 + v : ℝ) ≠ 0 := by positivity
  have hkey : toy_split_a1_qLc1 u v + toy_split_a1_qLc2 u v * ((1) / (2 * (2 + v))) + toy_split_a1_qLc3 u v * ((1) / ((2 + u)))
        + toy_split_a1_qLc4 u v * (((1) / (2 * (2 + v))) * ((1) / ((2 + u))))
      = (6 + 2 * u + 2 * v + u * v)
        / (4 * (2 + u) * (2 + u) * (2 + v) * (2 + v)) := by
    simp only [toy_split_a1_qLc1, toy_split_a1_qLc2, toy_split_a1_qLc3, toy_split_a1_qLc4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem toy_split_a1_qL_cell (u v q r : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hQ0 : 0 ≤ q) (hQ1 : q ≤ ((1) / (2 * (2 + v))))
    (hS0 : 0 ≤ r) (hS1 : r ≤ ((1) / ((2 + u)))) :
    (16 + 16 * u + 16 * v + 8 * q + 8 * r + 4 * u ^ 2 + 16 * u * v + 4 * u * q + 8 * u * r + 4 * v ^ 2 + 8 * v * q + 4 * v * r + 4 * q * r + 4 * u ^ 2 * v + 2 * u ^ 2 * r + 4 * u * v ^ 2 + 4 * u * v * q + 4 * u * v * r + 2 * u * q * r + 2 * v ^ 2 * q + 2 * v * q * r + u ^ 2 * v ^ 2 + u ^ 2 * v * r + u * v ^ 2 * q + u * v * q * r) / ((2 + u) * (2 + u) * (2 + v) * (2 + v)) ≤ (40 + 36 * u + 36 * v + 8 * q + 8 * r + 8 * u ^ 2 + 34 * u * v + 4 * u * q + 8 * u * r + 8 * v ^ 2 + 8 * v * q + 4 * v * r + 16 * q * r + 8 * u ^ 2 * v + 2 * u ^ 2 * r + 8 * u * v ^ 2 + 4 * u * v * q + 4 * u * v * r + 8 * u * q * r + 2 * v ^ 2 * q + 8 * v * q * r + 2 * u ^ 2 * v ^ 2 + u ^ 2 * v * r + u * v ^ 2 * q + 4 * u * v * q * r) / (2 * (2 + u) * (2 + u) * (2 + v) * (2 + v)) := by
  rw [← sub_nonneg, toy_split_a1_qL_bilinear u v q r hu hv]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((toy_split_a1_qL_corner00 u v hu hv)) ((toy_split_a1_qL_corner01 u v hu hv)) ((toy_split_a1_qL_corner10 u v hu hv)) ((toy_split_a1_qL_corner11 u v hu hv))

/-! ### Instance (a = 1) -/

noncomputable def toy_split_a1_qRc1 (u v : ℝ) : ℝ :=
  (1) / ((2 + u) * (2 + v))

noncomputable def toy_split_a1_qRc2 (u v : ℝ) : ℝ :=
  (0 - 1) / (2 * (2 + u))

noncomputable def toy_split_a1_qRc3 (u v : ℝ) : ℝ :=
  (0 - 1) / (2 * (2 + v))

noncomputable def toy_split_a1_qRc4 (u v : ℝ) : ℝ :=
  (1) / ((2 + u) * (2 + v))

theorem toy_split_a1_qR_bilinear (u v q r : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (40 + 36 * u + 36 * v + 8 * q + 8 * r + 8 * u ^ 2 + 34 * u * v + 4 * u * q + 8 * u * r + 8 * v ^ 2 + 8 * v * q + 4 * v * r + 16 * q * r + 8 * u ^ 2 * v + 2 * u ^ 2 * r + 8 * u * v ^ 2 + 4 * u * v * q + 4 * u * v * r + 8 * u * q * r + 2 * v ^ 2 * q + 8 * v * q * r + 2 * u ^ 2 * v ^ 2 + u ^ 2 * v * r + u * v ^ 2 * q + 4 * u * v * q * r) / (2 * (2 + u) * (2 + u) * (2 + v) * (2 + v)) - (16 + 16 * u + 16 * v + 8 * q + 8 * r + 4 * u ^ 2 + 16 * u * v + 4 * u * q + 8 * u * r + 4 * v ^ 2 + 8 * v * q + 4 * v * r + 4 * q * r + 4 * u ^ 2 * v + 2 * u ^ 2 * r + 4 * u * v ^ 2 + 4 * u * v * q + 4 * u * v * r + 2 * u * q * r + 2 * v ^ 2 * q + 2 * v * q * r + u ^ 2 * v ^ 2 + u ^ 2 * v * r + u * v ^ 2 * q + u * v * q * r) / ((2 + u) * (2 + u) * (2 + v) * (2 + v))
      = toy_split_a1_qRc1 u v + toy_split_a1_qRc2 u v * q + toy_split_a1_qRc3 u v * r
        + toy_split_a1_qRc4 u v * (q * r) := by
  have hd1 : (2 + u : ℝ) ≠ 0 := by positivity
  have hd2 : (2 + v : ℝ) ≠ 0 := by positivity
  simp only [toy_split_a1_qRc1, toy_split_a1_qRc2, toy_split_a1_qRc3, toy_split_a1_qRc4]
  push_cast
  field_simp
  try ring

theorem toy_split_a1_qR_corner00 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ toy_split_a1_qRc1 u v + toy_split_a1_qRc2 u v * ((1) / (2 * (2 + v))) + toy_split_a1_qRc3 u v * (0)
        + toy_split_a1_qRc4 u v * (((1) / (2 * (2 + v))) * (0)) := by
  have hd1 : (2 + u : ℝ) ≠ 0 := by positivity
  have hd2 : (2 + v : ℝ) ≠ 0 := by positivity
  have hkey : toy_split_a1_qRc1 u v + toy_split_a1_qRc2 u v * ((1) / (2 * (2 + v))) + toy_split_a1_qRc3 u v * (0)
        + toy_split_a1_qRc4 u v * (((1) / (2 * (2 + v))) * (0))
      = (12 + 6 * u + 6 * v + 3 * u * v)
        / (4 * (2 + u) * (2 + u) * (2 + v) * (2 + v)) := by
    simp only [toy_split_a1_qRc1, toy_split_a1_qRc2, toy_split_a1_qRc3, toy_split_a1_qRc4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem toy_split_a1_qR_corner01 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ toy_split_a1_qRc1 u v + toy_split_a1_qRc2 u v * ((1) / (2 * (2 + v))) + toy_split_a1_qRc3 u v * ((1) / ((2 + u)))
        + toy_split_a1_qRc4 u v * (((1) / (2 * (2 + v))) * ((1) / ((2 + u)))) := by
  have hd1 : (2 + u : ℝ) ≠ 0 := by positivity
  have hd2 : (2 + v : ℝ) ≠ 0 := by positivity
  have hkey : toy_split_a1_qRc1 u v + toy_split_a1_qRc2 u v * ((1) / (2 * (2 + v))) + toy_split_a1_qRc3 u v * ((1) / ((2 + u)))
        + toy_split_a1_qRc4 u v * (((1) / (2 * (2 + v))) * ((1) / ((2 + u))))
      = (6 + 2 * u + 2 * v + u * v)
        / (4 * (2 + u) * (2 + u) * (2 + v) * (2 + v)) := by
    simp only [toy_split_a1_qRc1, toy_split_a1_qRc2, toy_split_a1_qRc3, toy_split_a1_qRc4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem toy_split_a1_qR_corner10 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ toy_split_a1_qRc1 u v + toy_split_a1_qRc2 u v * ((1) / ((2 + v))) + toy_split_a1_qRc3 u v * (0)
        + toy_split_a1_qRc4 u v * (((1) / ((2 + v))) * (0)) := by
  have hd1 : (2 + u : ℝ) ≠ 0 := by positivity
  have hd2 : (2 + v : ℝ) ≠ 0 := by positivity
  have hkey : toy_split_a1_qRc1 u v + toy_split_a1_qRc2 u v * ((1) / ((2 + v))) + toy_split_a1_qRc3 u v * (0)
        + toy_split_a1_qRc4 u v * (((1) / ((2 + v))) * (0))
      = (4 + 2 * u + 2 * v + u * v)
        / (2 * (2 + u) * (2 + u) * (2 + v) * (2 + v)) := by
    simp only [toy_split_a1_qRc1, toy_split_a1_qRc2, toy_split_a1_qRc3, toy_split_a1_qRc4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem toy_split_a1_qR_corner11 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ toy_split_a1_qRc1 u v + toy_split_a1_qRc2 u v * ((1) / ((2 + v))) + toy_split_a1_qRc3 u v * ((1) / ((2 + u)))
        + toy_split_a1_qRc4 u v * (((1) / ((2 + v))) * ((1) / ((2 + u)))) := by
  have hd1 : (2 + u : ℝ) ≠ 0 := by positivity
  have hd2 : (2 + v : ℝ) ≠ 0 := by positivity
  have hkey : toy_split_a1_qRc1 u v + toy_split_a1_qRc2 u v * ((1) / ((2 + v))) + toy_split_a1_qRc3 u v * ((1) / ((2 + u)))
        + toy_split_a1_qRc4 u v * (((1) / ((2 + v))) * ((1) / ((2 + u))))
      = (1)
        / ((2 + u) * (2 + u) * (2 + v) * (2 + v)) := by
    simp only [toy_split_a1_qRc1, toy_split_a1_qRc2, toy_split_a1_qRc3, toy_split_a1_qRc4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem toy_split_a1_qR_cell (u v q r : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hQ0 : ((1) / (2 * (2 + v))) ≤ q) (hQ1 : q ≤ ((1) / ((2 + v))))
    (hS0 : 0 ≤ r) (hS1 : r ≤ ((1) / ((2 + u)))) :
    (16 + 16 * u + 16 * v + 8 * q + 8 * r + 4 * u ^ 2 + 16 * u * v + 4 * u * q + 8 * u * r + 4 * v ^ 2 + 8 * v * q + 4 * v * r + 4 * q * r + 4 * u ^ 2 * v + 2 * u ^ 2 * r + 4 * u * v ^ 2 + 4 * u * v * q + 4 * u * v * r + 2 * u * q * r + 2 * v ^ 2 * q + 2 * v * q * r + u ^ 2 * v ^ 2 + u ^ 2 * v * r + u * v ^ 2 * q + u * v * q * r) / ((2 + u) * (2 + u) * (2 + v) * (2 + v)) ≤ (40 + 36 * u + 36 * v + 8 * q + 8 * r + 8 * u ^ 2 + 34 * u * v + 4 * u * q + 8 * u * r + 8 * v ^ 2 + 8 * v * q + 4 * v * r + 16 * q * r + 8 * u ^ 2 * v + 2 * u ^ 2 * r + 8 * u * v ^ 2 + 4 * u * v * q + 4 * u * v * r + 8 * u * q * r + 2 * v ^ 2 * q + 8 * v * q * r + 2 * u ^ 2 * v ^ 2 + u ^ 2 * v * r + u * v ^ 2 * q + 4 * u * v * q * r) / (2 * (2 + u) * (2 + u) * (2 + v) * (2 + v)) := by
  rw [← sub_nonneg, toy_split_a1_qR_bilinear u v q r hu hv]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((toy_split_a1_qR_corner00 u v hu hv)) ((toy_split_a1_qR_corner01 u v hu hv)) ((toy_split_a1_qR_corner10 u v hu hv)) ((toy_split_a1_qR_corner11 u v hu hv))

theorem toy_split_a1_cell (u v q r : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hQ0 : 0 ≤ q) (hQ1 : q ≤ ((1) / ((2 + v))))
    (hS0 : 0 ≤ r) (hS1 : r ≤ ((1) / ((2 + u)))) :
    (16 + 16 * u + 16 * v + 8 * q + 8 * r + 4 * u ^ 2 + 16 * u * v + 4 * u * q + 8 * u * r + 4 * v ^ 2 + 8 * v * q + 4 * v * r + 4 * q * r + 4 * u ^ 2 * v + 2 * u ^ 2 * r + 4 * u * v ^ 2 + 4 * u * v * q + 4 * u * v * r + 2 * u * q * r + 2 * v ^ 2 * q + 2 * v * q * r + u ^ 2 * v ^ 2 + u ^ 2 * v * r + u * v ^ 2 * q + u * v * q * r) / ((2 + u) * (2 + u) * (2 + v) * (2 + v)) ≤ (40 + 36 * u + 36 * v + 8 * q + 8 * r + 8 * u ^ 2 + 34 * u * v + 4 * u * q + 8 * u * r + 8 * v ^ 2 + 8 * v * q + 4 * v * r + 16 * q * r + 8 * u ^ 2 * v + 2 * u ^ 2 * r + 8 * u * v ^ 2 + 4 * u * v * q + 4 * u * v * r + 8 * u * q * r + 2 * v ^ 2 * q + 8 * v * q * r + 2 * u ^ 2 * v ^ 2 + u ^ 2 * v * r + u * v ^ 2 * q + 4 * u * v * q * r) / (2 * (2 + u) * (2 + u) * (2 + v) * (2 + v)) := by
  rcases le_total q ((1) / (2 * (2 + v))) with h | h
  · exact toy_split_a1_qL_cell u v q r hu hv hQ0 h hS0 hS1
  · exact toy_split_a1_qR_cell u v q r hu hv h hQ1 hS0 hS1

end Toy
