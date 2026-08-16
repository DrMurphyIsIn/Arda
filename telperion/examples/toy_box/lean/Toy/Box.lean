/- telperion 0.1.1 | family ToyBox | input-hash 5489bd58750e7215
   24 theorems, 20 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

set_option maxHeartbeats 1600000

namespace Toy

/-- A bilinear form nonnegative at the four corners of a box is nonnegative on it.
    (Verbatim from the R47 campaign's CI-green `R47Cert.lean`.) -/
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

/-! ### Instance (a = 1, b = 1) -/

noncomputable def toy_a1b1c1 (u v : ℝ) : ℝ :=
  (1) / ((2 + u) * (2 + v))

noncomputable def toy_a1b1c2 (u v : ℝ) : ℝ :=
  (0 - 1) / (2 * (2 + u))

noncomputable def toy_a1b1c3 (u v : ℝ) : ℝ :=
  (0 - 1) / (2 * (2 + v))

noncomputable def toy_a1b1c4 (u v : ℝ) : ℝ :=
  (1) / ((2 + u) * (2 + v))

theorem toy_a1b1_bilinear (u v q r : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (40 + 36 * u + 36 * v + 8 * q + 8 * r + 8 * u ^ 2 + 34 * u * v + 4 * u * q + 8 * u * r + 8 * v ^ 2 + 8 * v * q + 4 * v * r + 16 * q * r + 8 * u ^ 2 * v + 2 * u ^ 2 * r + 8 * u * v ^ 2 + 4 * u * v * q + 4 * u * v * r + 8 * u * q * r + 2 * v ^ 2 * q + 8 * v * q * r + 2 * u ^ 2 * v ^ 2 + u ^ 2 * v * r + u * v ^ 2 * q + 4 * u * v * q * r) / (2 * (2 + u) * (2 + u) * (2 + v) * (2 + v)) - (16 + 16 * u + 16 * v + 8 * q + 8 * r + 4 * u ^ 2 + 16 * u * v + 4 * u * q + 8 * u * r + 4 * v ^ 2 + 8 * v * q + 4 * v * r + 4 * q * r + 4 * u ^ 2 * v + 2 * u ^ 2 * r + 4 * u * v ^ 2 + 4 * u * v * q + 4 * u * v * r + 2 * u * q * r + 2 * v ^ 2 * q + 2 * v * q * r + u ^ 2 * v ^ 2 + u ^ 2 * v * r + u * v ^ 2 * q + u * v * q * r) / ((2 + u) * (2 + u) * (2 + v) * (2 + v))
      = toy_a1b1c1 u v + toy_a1b1c2 u v * q + toy_a1b1c3 u v * r
        + toy_a1b1c4 u v * (q * r) := by
  have hd1 : (2 + u : ℝ) ≠ 0 := by positivity
  have hd2 : (2 + v : ℝ) ≠ 0 := by positivity
  simp only [toy_a1b1c1, toy_a1b1c2, toy_a1b1c3, toy_a1b1c4]
  push_cast
  field_simp
  try ring

theorem toy_a1b1_corner00 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ toy_a1b1c1 u v + toy_a1b1c2 u v * (0) + toy_a1b1c3 u v * (0)
        + toy_a1b1c4 u v * ((0) * (0)) := by
  have hd1 : (2 + u : ℝ) ≠ 0 := by positivity
  have hd2 : (2 + v : ℝ) ≠ 0 := by positivity
  have hkey : toy_a1b1c1 u v + toy_a1b1c2 u v * (0) + toy_a1b1c3 u v * (0)
        + toy_a1b1c4 u v * ((0) * (0))
      = (1)
        / ((2 + u) * (2 + v)) := by
    simp only [toy_a1b1c1, toy_a1b1c2, toy_a1b1c3, toy_a1b1c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem toy_a1b1_corner01 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ toy_a1b1c1 u v + toy_a1b1c2 u v * (0) + toy_a1b1c3 u v * ((1) / ((2 + u)))
        + toy_a1b1c4 u v * ((0) * ((1) / ((2 + u)))) := by
  have hd1 : (2 + u : ℝ) ≠ 0 := by positivity
  have hd2 : (2 + v : ℝ) ≠ 0 := by positivity
  have hkey : toy_a1b1c1 u v + toy_a1b1c2 u v * (0) + toy_a1b1c3 u v * ((1) / ((2 + u)))
        + toy_a1b1c4 u v * ((0) * ((1) / ((2 + u))))
      = (4 + 2 * u + 2 * v + u * v)
        / (2 * (2 + u) * (2 + u) * (2 + v) * (2 + v)) := by
    simp only [toy_a1b1c1, toy_a1b1c2, toy_a1b1c3, toy_a1b1c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem toy_a1b1_corner10 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ toy_a1b1c1 u v + toy_a1b1c2 u v * ((1) / ((2 + v))) + toy_a1b1c3 u v * (0)
        + toy_a1b1c4 u v * (((1) / ((2 + v))) * (0)) := by
  have hd1 : (2 + u : ℝ) ≠ 0 := by positivity
  have hd2 : (2 + v : ℝ) ≠ 0 := by positivity
  have hkey : toy_a1b1c1 u v + toy_a1b1c2 u v * ((1) / ((2 + v))) + toy_a1b1c3 u v * (0)
        + toy_a1b1c4 u v * (((1) / ((2 + v))) * (0))
      = (4 + 2 * u + 2 * v + u * v)
        / (2 * (2 + u) * (2 + u) * (2 + v) * (2 + v)) := by
    simp only [toy_a1b1c1, toy_a1b1c2, toy_a1b1c3, toy_a1b1c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem toy_a1b1_corner11 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ toy_a1b1c1 u v + toy_a1b1c2 u v * ((1) / ((2 + v))) + toy_a1b1c3 u v * ((1) / ((2 + u)))
        + toy_a1b1c4 u v * (((1) / ((2 + v))) * ((1) / ((2 + u)))) := by
  have hd1 : (2 + u : ℝ) ≠ 0 := by positivity
  have hd2 : (2 + v : ℝ) ≠ 0 := by positivity
  have hkey : toy_a1b1c1 u v + toy_a1b1c2 u v * ((1) / ((2 + v))) + toy_a1b1c3 u v * ((1) / ((2 + u)))
        + toy_a1b1c4 u v * (((1) / ((2 + v))) * ((1) / ((2 + u))))
      = (1)
        / ((2 + u) * (2 + u) * (2 + v) * (2 + v)) := by
    simp only [toy_a1b1c1, toy_a1b1c2, toy_a1b1c3, toy_a1b1c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem toy_a1b1_cell (u v q r : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hQ0 : 0 ≤ q) (hQ1 : q ≤ ((1) / ((2 + v))))
    (hS0 : 0 ≤ r) (hS1 : r ≤ ((1) / ((2 + u)))) :
    (16 + 16 * u + 16 * v + 8 * q + 8 * r + 4 * u ^ 2 + 16 * u * v + 4 * u * q + 8 * u * r + 4 * v ^ 2 + 8 * v * q + 4 * v * r + 4 * q * r + 4 * u ^ 2 * v + 2 * u ^ 2 * r + 4 * u * v ^ 2 + 4 * u * v * q + 4 * u * v * r + 2 * u * q * r + 2 * v ^ 2 * q + 2 * v * q * r + u ^ 2 * v ^ 2 + u ^ 2 * v * r + u * v ^ 2 * q + u * v * q * r) / ((2 + u) * (2 + u) * (2 + v) * (2 + v)) ≤ (40 + 36 * u + 36 * v + 8 * q + 8 * r + 8 * u ^ 2 + 34 * u * v + 4 * u * q + 8 * u * r + 8 * v ^ 2 + 8 * v * q + 4 * v * r + 16 * q * r + 8 * u ^ 2 * v + 2 * u ^ 2 * r + 8 * u * v ^ 2 + 4 * u * v * q + 4 * u * v * r + 8 * u * q * r + 2 * v ^ 2 * q + 8 * v * q * r + 2 * u ^ 2 * v ^ 2 + u ^ 2 * v * r + u * v ^ 2 * q + 4 * u * v * q * r) / (2 * (2 + u) * (2 + u) * (2 + v) * (2 + v)) := by
  rw [← sub_nonneg, toy_a1b1_bilinear u v q r hu hv]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((toy_a1b1_corner00 u v hu hv)) ((toy_a1b1_corner01 u v hu hv)) ((toy_a1b1_corner10 u v hu hv)) ((toy_a1b1_corner11 u v hu hv))

/-! ### Instance (a = 1, b = 2) -/

noncomputable def toy_a1b2c1 (u v : ℝ) : ℝ :=
  (1) / ((2 + u) * (3 + v))

noncomputable def toy_a1b2c2 (u v : ℝ) : ℝ :=
  (0 - 1) / (2 * (2 + u))

noncomputable def toy_a1b2c3 (u v : ℝ) : ℝ :=
  (0 - 1) / ((3 + v))

noncomputable def toy_a1b2c4 (u v : ℝ) : ℝ :=
  (2) / ((2 + u) * (3 + v))

theorem toy_a1b2_bilinear (u v q r : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (84 + 78 * u + 52 * v + 18 * q + 24 * r + 18 * u ^ 2 + 50 * u * v + 9 * u * q + 24 * u * r + 8 * v ^ 2 + 12 * v * q + 8 * v * r + 48 * q * r + 12 * u ^ 2 * v + 6 * u ^ 2 * r + 8 * u * v ^ 2 + 6 * u * v * q + 8 * u * v * r + 24 * u * q * r + 2 * v ^ 2 * q + 16 * v * q * r + 2 * u ^ 2 * v ^ 2 + 2 * u ^ 2 * v * r + u * v ^ 2 * q + 8 * u * v * q * r) / (2 * (2 + u) * (2 + u) * (3 + v) * (3 + v)) - (36 + 36 * u + 24 * v + 18 * q + 24 * r + 9 * u ^ 2 + 24 * u * v + 9 * u * q + 24 * u * r + 4 * v ^ 2 + 12 * v * q + 8 * v * r + 12 * q * r + 6 * u ^ 2 * v + 6 * u ^ 2 * r + 4 * u * v ^ 2 + 6 * u * v * q + 8 * u * v * r + 6 * u * q * r + 2 * v ^ 2 * q + 4 * v * q * r + u ^ 2 * v ^ 2 + 2 * u ^ 2 * v * r + u * v ^ 2 * q + 2 * u * v * q * r) / ((2 + u) * (2 + u) * (3 + v) * (3 + v))
      = toy_a1b2c1 u v + toy_a1b2c2 u v * q + toy_a1b2c3 u v * r
        + toy_a1b2c4 u v * (q * r) := by
  have hd1 : (2 + u : ℝ) ≠ 0 := by positivity
  have hd2 : (3 + v : ℝ) ≠ 0 := by positivity
  simp only [toy_a1b2c1, toy_a1b2c2, toy_a1b2c3, toy_a1b2c4]
  push_cast
  field_simp
  try ring

theorem toy_a1b2_corner00 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ toy_a1b2c1 u v + toy_a1b2c2 u v * (0) + toy_a1b2c3 u v * (0)
        + toy_a1b2c4 u v * ((0) * (0)) := by
  have hd1 : (2 + u : ℝ) ≠ 0 := by positivity
  have hd2 : (3 + v : ℝ) ≠ 0 := by positivity
  have hkey : toy_a1b2c1 u v + toy_a1b2c2 u v * (0) + toy_a1b2c3 u v * (0)
        + toy_a1b2c4 u v * ((0) * (0))
      = (1)
        / ((2 + u) * (3 + v)) := by
    simp only [toy_a1b2c1, toy_a1b2c2, toy_a1b2c3, toy_a1b2c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem toy_a1b2_corner01 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ toy_a1b2c1 u v + toy_a1b2c2 u v * (0) + toy_a1b2c3 u v * ((1) / (2 * (2 + u)))
        + toy_a1b2c4 u v * ((0) * ((1) / (2 * (2 + u)))) := by
  have hd1 : (2 + u : ℝ) ≠ 0 := by positivity
  have hd2 : (3 + v : ℝ) ≠ 0 := by positivity
  have hkey : toy_a1b2c1 u v + toy_a1b2c2 u v * (0) + toy_a1b2c3 u v * ((1) / (2 * (2 + u)))
        + toy_a1b2c4 u v * ((0) * ((1) / (2 * (2 + u))))
      = (6 + 3 * u + 2 * v + u * v)
        / (2 * (2 + u) * (2 + u) * (3 + v) * (3 + v)) := by
    simp only [toy_a1b2c1, toy_a1b2c2, toy_a1b2c3, toy_a1b2c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem toy_a1b2_corner10 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ toy_a1b2c1 u v + toy_a1b2c2 u v * ((1) / ((3 + v))) + toy_a1b2c3 u v * (0)
        + toy_a1b2c4 u v * (((1) / ((3 + v))) * (0)) := by
  have hd1 : (2 + u : ℝ) ≠ 0 := by positivity
  have hd2 : (3 + v : ℝ) ≠ 0 := by positivity
  have hkey : toy_a1b2c1 u v + toy_a1b2c2 u v * ((1) / ((3 + v))) + toy_a1b2c3 u v * (0)
        + toy_a1b2c4 u v * (((1) / ((3 + v))) * (0))
      = (6 + 3 * u + 2 * v + u * v)
        / (2 * (2 + u) * (2 + u) * (3 + v) * (3 + v)) := by
    simp only [toy_a1b2c1, toy_a1b2c2, toy_a1b2c3, toy_a1b2c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem toy_a1b2_corner11 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ toy_a1b2c1 u v + toy_a1b2c2 u v * ((1) / ((3 + v))) + toy_a1b2c3 u v * ((1) / (2 * (2 + u)))
        + toy_a1b2c4 u v * (((1) / ((3 + v))) * ((1) / (2 * (2 + u)))) := by
  have hd1 : (2 + u : ℝ) ≠ 0 := by positivity
  have hd2 : (3 + v : ℝ) ≠ 0 := by positivity
  have hkey : toy_a1b2c1 u v + toy_a1b2c2 u v * ((1) / ((3 + v))) + toy_a1b2c3 u v * ((1) / (2 * (2 + u)))
        + toy_a1b2c4 u v * (((1) / ((3 + v))) * ((1) / (2 * (2 + u))))
      = (1)
        / ((2 + u) * (2 + u) * (3 + v) * (3 + v)) := by
    simp only [toy_a1b2c1, toy_a1b2c2, toy_a1b2c3, toy_a1b2c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem toy_a1b2_cell (u v q r : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hQ0 : 0 ≤ q) (hQ1 : q ≤ ((1) / ((3 + v))))
    (hS0 : 0 ≤ r) (hS1 : r ≤ ((1) / (2 * (2 + u)))) :
    (36 + 36 * u + 24 * v + 18 * q + 24 * r + 9 * u ^ 2 + 24 * u * v + 9 * u * q + 24 * u * r + 4 * v ^ 2 + 12 * v * q + 8 * v * r + 12 * q * r + 6 * u ^ 2 * v + 6 * u ^ 2 * r + 4 * u * v ^ 2 + 6 * u * v * q + 8 * u * v * r + 6 * u * q * r + 2 * v ^ 2 * q + 4 * v * q * r + u ^ 2 * v ^ 2 + 2 * u ^ 2 * v * r + u * v ^ 2 * q + 2 * u * v * q * r) / ((2 + u) * (2 + u) * (3 + v) * (3 + v)) ≤ (84 + 78 * u + 52 * v + 18 * q + 24 * r + 18 * u ^ 2 + 50 * u * v + 9 * u * q + 24 * u * r + 8 * v ^ 2 + 12 * v * q + 8 * v * r + 48 * q * r + 12 * u ^ 2 * v + 6 * u ^ 2 * r + 8 * u * v ^ 2 + 6 * u * v * q + 8 * u * v * r + 24 * u * q * r + 2 * v ^ 2 * q + 16 * v * q * r + 2 * u ^ 2 * v ^ 2 + 2 * u ^ 2 * v * r + u * v ^ 2 * q + 8 * u * v * q * r) / (2 * (2 + u) * (2 + u) * (3 + v) * (3 + v)) := by
  rw [← sub_nonneg, toy_a1b2_bilinear u v q r hu hv]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((toy_a1b2_corner00 u v hu hv)) ((toy_a1b2_corner01 u v hu hv)) ((toy_a1b2_corner10 u v hu hv)) ((toy_a1b2_corner11 u v hu hv))

/-! ### Instance (a = 2, b = 1) -/

noncomputable def toy_a2b1c1 (u v : ℝ) : ℝ :=
  (1) / ((3 + u) * (2 + v))

noncomputable def toy_a2b1c2 (u v : ℝ) : ℝ :=
  (0 - 1) / ((3 + u))

noncomputable def toy_a2b1c3 (u v : ℝ) : ℝ :=
  (0 - 1) / (2 * (2 + v))

noncomputable def toy_a2b1c4 (u v : ℝ) : ℝ :=
  (2) / ((3 + u) * (2 + v))

theorem toy_a2b1_bilinear (u v q r : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (84 + 52 * u + 78 * v + 24 * q + 18 * r + 8 * u ^ 2 + 50 * u * v + 8 * u * q + 12 * u * r + 18 * v ^ 2 + 24 * v * q + 9 * v * r + 48 * q * r + 8 * u ^ 2 * v + 2 * u ^ 2 * r + 12 * u * v ^ 2 + 8 * u * v * q + 6 * u * v * r + 16 * u * q * r + 6 * v ^ 2 * q + 24 * v * q * r + 2 * u ^ 2 * v ^ 2 + u ^ 2 * v * r + 2 * u * v ^ 2 * q + 8 * u * v * q * r) / (2 * (3 + u) * (3 + u) * (2 + v) * (2 + v)) - (36 + 24 * u + 36 * v + 24 * q + 18 * r + 4 * u ^ 2 + 24 * u * v + 8 * u * q + 12 * u * r + 9 * v ^ 2 + 24 * v * q + 9 * v * r + 12 * q * r + 4 * u ^ 2 * v + 2 * u ^ 2 * r + 6 * u * v ^ 2 + 8 * u * v * q + 6 * u * v * r + 4 * u * q * r + 6 * v ^ 2 * q + 6 * v * q * r + u ^ 2 * v ^ 2 + u ^ 2 * v * r + 2 * u * v ^ 2 * q + 2 * u * v * q * r) / ((3 + u) * (3 + u) * (2 + v) * (2 + v))
      = toy_a2b1c1 u v + toy_a2b1c2 u v * q + toy_a2b1c3 u v * r
        + toy_a2b1c4 u v * (q * r) := by
  have hd1 : (3 + u : ℝ) ≠ 0 := by positivity
  have hd2 : (2 + v : ℝ) ≠ 0 := by positivity
  simp only [toy_a2b1c1, toy_a2b1c2, toy_a2b1c3, toy_a2b1c4]
  push_cast
  field_simp
  try ring

theorem toy_a2b1_corner00 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ toy_a2b1c1 u v + toy_a2b1c2 u v * (0) + toy_a2b1c3 u v * (0)
        + toy_a2b1c4 u v * ((0) * (0)) := by
  have hd1 : (3 + u : ℝ) ≠ 0 := by positivity
  have hd2 : (2 + v : ℝ) ≠ 0 := by positivity
  have hkey : toy_a2b1c1 u v + toy_a2b1c2 u v * (0) + toy_a2b1c3 u v * (0)
        + toy_a2b1c4 u v * ((0) * (0))
      = (1)
        / ((3 + u) * (2 + v)) := by
    simp only [toy_a2b1c1, toy_a2b1c2, toy_a2b1c3, toy_a2b1c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem toy_a2b1_corner01 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ toy_a2b1c1 u v + toy_a2b1c2 u v * (0) + toy_a2b1c3 u v * ((1) / ((3 + u)))
        + toy_a2b1c4 u v * ((0) * ((1) / ((3 + u)))) := by
  have hd1 : (3 + u : ℝ) ≠ 0 := by positivity
  have hd2 : (2 + v : ℝ) ≠ 0 := by positivity
  have hkey : toy_a2b1c1 u v + toy_a2b1c2 u v * (0) + toy_a2b1c3 u v * ((1) / ((3 + u)))
        + toy_a2b1c4 u v * ((0) * ((1) / ((3 + u))))
      = (6 + 2 * u + 3 * v + u * v)
        / (2 * (3 + u) * (3 + u) * (2 + v) * (2 + v)) := by
    simp only [toy_a2b1c1, toy_a2b1c2, toy_a2b1c3, toy_a2b1c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem toy_a2b1_corner10 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ toy_a2b1c1 u v + toy_a2b1c2 u v * ((1) / (2 * (2 + v))) + toy_a2b1c3 u v * (0)
        + toy_a2b1c4 u v * (((1) / (2 * (2 + v))) * (0)) := by
  have hd1 : (3 + u : ℝ) ≠ 0 := by positivity
  have hd2 : (2 + v : ℝ) ≠ 0 := by positivity
  have hkey : toy_a2b1c1 u v + toy_a2b1c2 u v * ((1) / (2 * (2 + v))) + toy_a2b1c3 u v * (0)
        + toy_a2b1c4 u v * (((1) / (2 * (2 + v))) * (0))
      = (6 + 2 * u + 3 * v + u * v)
        / (2 * (3 + u) * (3 + u) * (2 + v) * (2 + v)) := by
    simp only [toy_a2b1c1, toy_a2b1c2, toy_a2b1c3, toy_a2b1c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem toy_a2b1_corner11 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ toy_a2b1c1 u v + toy_a2b1c2 u v * ((1) / (2 * (2 + v))) + toy_a2b1c3 u v * ((1) / ((3 + u)))
        + toy_a2b1c4 u v * (((1) / (2 * (2 + v))) * ((1) / ((3 + u)))) := by
  have hd1 : (3 + u : ℝ) ≠ 0 := by positivity
  have hd2 : (2 + v : ℝ) ≠ 0 := by positivity
  have hkey : toy_a2b1c1 u v + toy_a2b1c2 u v * ((1) / (2 * (2 + v))) + toy_a2b1c3 u v * ((1) / ((3 + u)))
        + toy_a2b1c4 u v * (((1) / (2 * (2 + v))) * ((1) / ((3 + u))))
      = (1)
        / ((3 + u) * (3 + u) * (2 + v) * (2 + v)) := by
    simp only [toy_a2b1c1, toy_a2b1c2, toy_a2b1c3, toy_a2b1c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem toy_a2b1_cell (u v q r : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hQ0 : 0 ≤ q) (hQ1 : q ≤ ((1) / (2 * (2 + v))))
    (hS0 : 0 ≤ r) (hS1 : r ≤ ((1) / ((3 + u)))) :
    (36 + 24 * u + 36 * v + 24 * q + 18 * r + 4 * u ^ 2 + 24 * u * v + 8 * u * q + 12 * u * r + 9 * v ^ 2 + 24 * v * q + 9 * v * r + 12 * q * r + 4 * u ^ 2 * v + 2 * u ^ 2 * r + 6 * u * v ^ 2 + 8 * u * v * q + 6 * u * v * r + 4 * u * q * r + 6 * v ^ 2 * q + 6 * v * q * r + u ^ 2 * v ^ 2 + u ^ 2 * v * r + 2 * u * v ^ 2 * q + 2 * u * v * q * r) / ((3 + u) * (3 + u) * (2 + v) * (2 + v)) ≤ (84 + 52 * u + 78 * v + 24 * q + 18 * r + 8 * u ^ 2 + 50 * u * v + 8 * u * q + 12 * u * r + 18 * v ^ 2 + 24 * v * q + 9 * v * r + 48 * q * r + 8 * u ^ 2 * v + 2 * u ^ 2 * r + 12 * u * v ^ 2 + 8 * u * v * q + 6 * u * v * r + 16 * u * q * r + 6 * v ^ 2 * q + 24 * v * q * r + 2 * u ^ 2 * v ^ 2 + u ^ 2 * v * r + 2 * u * v ^ 2 * q + 8 * u * v * q * r) / (2 * (3 + u) * (3 + u) * (2 + v) * (2 + v)) := by
  rw [← sub_nonneg, toy_a2b1_bilinear u v q r hu hv]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((toy_a2b1_corner00 u v hu hv)) ((toy_a2b1_corner01 u v hu hv)) ((toy_a2b1_corner10 u v hu hv)) ((toy_a2b1_corner11 u v hu hv))

/-! ### Instance (a = 2, b = 2) -/

noncomputable def toy_a2b2c1 (u v : ℝ) : ℝ :=
  (1) / ((3 + u) * (3 + v))

noncomputable def toy_a2b2c2 (u v : ℝ) : ℝ :=
  (0 - 1) / ((3 + u))

noncomputable def toy_a2b2c3 (u v : ℝ) : ℝ :=
  (0 - 1) / ((3 + v))

noncomputable def toy_a2b2c4 (u v : ℝ) : ℝ :=
  (4) / ((3 + u) * (3 + v))

theorem toy_a2b2_bilinear (u v q r : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (90 + 57 * u + 57 * v + 27 * q + 27 * r + 9 * u ^ 2 + 37 * u * v + 9 * u * q + 18 * u * r + 9 * v ^ 2 + 18 * v * q + 9 * v * r + 72 * q * r + 6 * u ^ 2 * v + 3 * u ^ 2 * r + 6 * u * v ^ 2 + 6 * u * v * q + 6 * u * v * r + 24 * u * q * r + 3 * v ^ 2 * q + 24 * v * q * r + u ^ 2 * v ^ 2 + u ^ 2 * v * r + u * v ^ 2 * q + 8 * u * v * q * r) / ((3 + u) * (3 + u) * (3 + v) * (3 + v)) - (81 + 54 * u + 54 * v + 54 * q + 54 * r + 9 * u ^ 2 + 36 * u * v + 18 * u * q + 36 * u * r + 9 * v ^ 2 + 36 * v * q + 18 * v * r + 36 * q * r + 6 * u ^ 2 * v + 6 * u ^ 2 * r + 6 * u * v ^ 2 + 12 * u * v * q + 12 * u * v * r + 12 * u * q * r + 6 * v ^ 2 * q + 12 * v * q * r + u ^ 2 * v ^ 2 + 2 * u ^ 2 * v * r + 2 * u * v ^ 2 * q + 4 * u * v * q * r) / ((3 + u) * (3 + u) * (3 + v) * (3 + v))
      = toy_a2b2c1 u v + toy_a2b2c2 u v * q + toy_a2b2c3 u v * r
        + toy_a2b2c4 u v * (q * r) := by
  have hd1 : (3 + u : ℝ) ≠ 0 := by positivity
  have hd2 : (3 + v : ℝ) ≠ 0 := by positivity
  simp only [toy_a2b2c1, toy_a2b2c2, toy_a2b2c3, toy_a2b2c4]
  push_cast
  field_simp
  try ring

theorem toy_a2b2_corner00 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ toy_a2b2c1 u v + toy_a2b2c2 u v * (0) + toy_a2b2c3 u v * (0)
        + toy_a2b2c4 u v * ((0) * (0)) := by
  have hd1 : (3 + u : ℝ) ≠ 0 := by positivity
  have hd2 : (3 + v : ℝ) ≠ 0 := by positivity
  have hkey : toy_a2b2c1 u v + toy_a2b2c2 u v * (0) + toy_a2b2c3 u v * (0)
        + toy_a2b2c4 u v * ((0) * (0))
      = (1)
        / ((3 + u) * (3 + v)) := by
    simp only [toy_a2b2c1, toy_a2b2c2, toy_a2b2c3, toy_a2b2c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem toy_a2b2_corner01 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ toy_a2b2c1 u v + toy_a2b2c2 u v * (0) + toy_a2b2c3 u v * ((1) / (2 * (3 + u)))
        + toy_a2b2c4 u v * ((0) * ((1) / (2 * (3 + u)))) := by
  have hd1 : (3 + u : ℝ) ≠ 0 := by positivity
  have hd2 : (3 + v : ℝ) ≠ 0 := by positivity
  have hkey : toy_a2b2c1 u v + toy_a2b2c2 u v * (0) + toy_a2b2c3 u v * ((1) / (2 * (3 + u)))
        + toy_a2b2c4 u v * ((0) * ((1) / (2 * (3 + u))))
      = (9 + 3 * u + 3 * v + u * v)
        / (2 * (3 + u) * (3 + u) * (3 + v) * (3 + v)) := by
    simp only [toy_a2b2c1, toy_a2b2c2, toy_a2b2c3, toy_a2b2c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem toy_a2b2_corner10 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ toy_a2b2c1 u v + toy_a2b2c2 u v * ((1) / (2 * (3 + v))) + toy_a2b2c3 u v * (0)
        + toy_a2b2c4 u v * (((1) / (2 * (3 + v))) * (0)) := by
  have hd1 : (3 + u : ℝ) ≠ 0 := by positivity
  have hd2 : (3 + v : ℝ) ≠ 0 := by positivity
  have hkey : toy_a2b2c1 u v + toy_a2b2c2 u v * ((1) / (2 * (3 + v))) + toy_a2b2c3 u v * (0)
        + toy_a2b2c4 u v * (((1) / (2 * (3 + v))) * (0))
      = (9 + 3 * u + 3 * v + u * v)
        / (2 * (3 + u) * (3 + u) * (3 + v) * (3 + v)) := by
    simp only [toy_a2b2c1, toy_a2b2c2, toy_a2b2c3, toy_a2b2c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem toy_a2b2_corner11 (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ toy_a2b2c1 u v + toy_a2b2c2 u v * ((1) / (2 * (3 + v))) + toy_a2b2c3 u v * ((1) / (2 * (3 + u)))
        + toy_a2b2c4 u v * (((1) / (2 * (3 + v))) * ((1) / (2 * (3 + u)))) := by
  have hd1 : (3 + u : ℝ) ≠ 0 := by positivity
  have hd2 : (3 + v : ℝ) ≠ 0 := by positivity
  have hkey : toy_a2b2c1 u v + toy_a2b2c2 u v * ((1) / (2 * (3 + v))) + toy_a2b2c3 u v * ((1) / (2 * (3 + u)))
        + toy_a2b2c4 u v * (((1) / (2 * (3 + v))) * ((1) / (2 * (3 + u))))
      = (1)
        / ((3 + u) * (3 + u) * (3 + v) * (3 + v)) := by
    simp only [toy_a2b2c1, toy_a2b2c2, toy_a2b2c3, toy_a2b2c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem toy_a2b2_cell (u v q r : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hQ0 : 0 ≤ q) (hQ1 : q ≤ ((1) / (2 * (3 + v))))
    (hS0 : 0 ≤ r) (hS1 : r ≤ ((1) / (2 * (3 + u)))) :
    (81 + 54 * u + 54 * v + 54 * q + 54 * r + 9 * u ^ 2 + 36 * u * v + 18 * u * q + 36 * u * r + 9 * v ^ 2 + 36 * v * q + 18 * v * r + 36 * q * r + 6 * u ^ 2 * v + 6 * u ^ 2 * r + 6 * u * v ^ 2 + 12 * u * v * q + 12 * u * v * r + 12 * u * q * r + 6 * v ^ 2 * q + 12 * v * q * r + u ^ 2 * v ^ 2 + 2 * u ^ 2 * v * r + 2 * u * v ^ 2 * q + 4 * u * v * q * r) / ((3 + u) * (3 + u) * (3 + v) * (3 + v)) ≤ (90 + 57 * u + 57 * v + 27 * q + 27 * r + 9 * u ^ 2 + 37 * u * v + 9 * u * q + 18 * u * r + 9 * v ^ 2 + 18 * v * q + 9 * v * r + 72 * q * r + 6 * u ^ 2 * v + 3 * u ^ 2 * r + 6 * u * v ^ 2 + 6 * u * v * q + 6 * u * v * r + 24 * u * q * r + 3 * v ^ 2 * q + 24 * v * q * r + u ^ 2 * v ^ 2 + u ^ 2 * v * r + u * v ^ 2 * q + 8 * u * v * q * r) / ((3 + u) * (3 + u) * (3 + v) * (3 + v)) := by
  rw [← sub_nonneg, toy_a2b2_bilinear u v q r hu hv]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((toy_a2b2_corner00 u v hu hv)) ((toy_a2b2_corner01 u v hu hv)) ((toy_a2b2_corner10 u v hu hv)) ((toy_a2b2_corner11 u v hu hv))

end Toy
