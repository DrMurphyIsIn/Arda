/- telperion 0.1.3 | family HFloors | input-hash e7ac8d500ae3cdc9
   336 theorems, 280 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace G1
namespace HFloor

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

/-! ### Instance (piece = 0) -/

noncomputable def hfloor_m2_S0_1_1_2c1 : ℝ :=
  ((-179547730859)) / (895500000000)

noncomputable def hfloor_m2_S0_1_1_2c2 : ℝ :=
  1

noncomputable def hfloor_m2_S0_1_1_2c3 : ℝ :=
  0

noncomputable def hfloor_m2_S0_1_1_2c4 : ℝ :=
  0

theorem hfloor_m2_S0_1_1_2_bilinear (L _iv_dummy_HFloors : ℝ) :
    (895500000000 * L - 179547730859) / (895500000000) - 0
      = hfloor_m2_S0_1_1_2c1  + hfloor_m2_S0_1_1_2c2  * L + hfloor_m2_S0_1_1_2c3  * _iv_dummy_HFloors
        + hfloor_m2_S0_1_1_2c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m2_S0_1_1_2c1, hfloor_m2_S0_1_1_2c2, hfloor_m2_S0_1_1_2c3, hfloor_m2_S0_1_1_2c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m2_S0_1_1_2_corner00  :
    0 ≤ hfloor_m2_S0_1_1_2c1 + hfloor_m2_S0_1_1_2c2 * ((103293) / (500000)) + hfloor_m2_S0_1_1_2c3 * (0)
        + hfloor_m2_S0_1_1_2c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m2_S0_1_1_2c1 + hfloor_m2_S0_1_1_2c2 * ((103293) / (500000)) + hfloor_m2_S0_1_1_2c3 * (0)
        + hfloor_m2_S0_1_1_2c4 * (((103293) / (500000)) * (0))
      = (5450032141)
        / (895500000000) := by
    simp only [hfloor_m2_S0_1_1_2c1, hfloor_m2_S0_1_1_2c2, hfloor_m2_S0_1_1_2c3, hfloor_m2_S0_1_1_2c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S0_1_1_2_corner01  :
    0 ≤ hfloor_m2_S0_1_1_2c1 + hfloor_m2_S0_1_1_2c2 * ((103293) / (500000)) + hfloor_m2_S0_1_1_2c3 * (1)
        + hfloor_m2_S0_1_1_2c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m2_S0_1_1_2c1 + hfloor_m2_S0_1_1_2c2 * ((103293) / (500000)) + hfloor_m2_S0_1_1_2c3 * (1)
        + hfloor_m2_S0_1_1_2c4 * (((103293) / (500000)) * (1))
      = (5450032141)
        / (895500000000) := by
    simp only [hfloor_m2_S0_1_1_2c1, hfloor_m2_S0_1_1_2c2, hfloor_m2_S0_1_1_2c3, hfloor_m2_S0_1_1_2c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S0_1_1_2_corner10  :
    0 ≤ hfloor_m2_S0_1_1_2c1 + hfloor_m2_S0_1_1_2c2 * ((206587) / (1000000)) + hfloor_m2_S0_1_1_2c3 * (0)
        + hfloor_m2_S0_1_1_2c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m2_S0_1_1_2c1 + hfloor_m2_S0_1_1_2c2 * ((206587) / (1000000)) + hfloor_m2_S0_1_1_2c3 * (0)
        + hfloor_m2_S0_1_1_2c4 * (((206587) / (1000000)) * (0))
      = (5450927641)
        / (895500000000) := by
    simp only [hfloor_m2_S0_1_1_2c1, hfloor_m2_S0_1_1_2c2, hfloor_m2_S0_1_1_2c3, hfloor_m2_S0_1_1_2c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S0_1_1_2_corner11  :
    0 ≤ hfloor_m2_S0_1_1_2c1 + hfloor_m2_S0_1_1_2c2 * ((206587) / (1000000)) + hfloor_m2_S0_1_1_2c3 * (1)
        + hfloor_m2_S0_1_1_2c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m2_S0_1_1_2c1 + hfloor_m2_S0_1_1_2c2 * ((206587) / (1000000)) + hfloor_m2_S0_1_1_2c3 * (1)
        + hfloor_m2_S0_1_1_2c4 * (((206587) / (1000000)) * (1))
      = (5450927641)
        / (895500000000) := by
    simp only [hfloor_m2_S0_1_1_2c1, hfloor_m2_S0_1_1_2c2, hfloor_m2_S0_1_1_2c3, hfloor_m2_S0_1_1_2c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S0_1_1_2_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (895500000000 * L - 179547730859) / (895500000000) := by
  rw [← sub_nonneg, hfloor_m2_S0_1_1_2_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m2_S0_1_1_2_corner00)) ((hfloor_m2_S0_1_1_2_corner01)) ((hfloor_m2_S0_1_1_2_corner10)) ((hfloor_m2_S0_1_1_2_corner11))

/-! ### Instance (piece = 1) -/

noncomputable def hfloor_m2_S1_2_9_16c1 : ℝ :=
  ((-34444799)) / (175000000)

noncomputable def hfloor_m2_S1_2_9_16c2 : ℝ :=
  1

noncomputable def hfloor_m2_S1_2_9_16c3 : ℝ :=
  0

noncomputable def hfloor_m2_S1_2_9_16c4 : ℝ :=
  0

theorem hfloor_m2_S1_2_9_16_bilinear (L _iv_dummy_HFloors : ℝ) :
    (175000000 * L - 34444799) / (175000000) - 0
      = hfloor_m2_S1_2_9_16c1  + hfloor_m2_S1_2_9_16c2  * L + hfloor_m2_S1_2_9_16c3  * _iv_dummy_HFloors
        + hfloor_m2_S1_2_9_16c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m2_S1_2_9_16c1, hfloor_m2_S1_2_9_16c2, hfloor_m2_S1_2_9_16c3, hfloor_m2_S1_2_9_16c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m2_S1_2_9_16_corner00  :
    0 ≤ hfloor_m2_S1_2_9_16c1 + hfloor_m2_S1_2_9_16c2 * ((103293) / (500000)) + hfloor_m2_S1_2_9_16c3 * (0)
        + hfloor_m2_S1_2_9_16c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m2_S1_2_9_16c1 + hfloor_m2_S1_2_9_16c2 * ((103293) / (500000)) + hfloor_m2_S1_2_9_16c3 * (0)
        + hfloor_m2_S1_2_9_16c4 * (((103293) / (500000)) * (0))
      = (1707751)
        / (175000000) := by
    simp only [hfloor_m2_S1_2_9_16c1, hfloor_m2_S1_2_9_16c2, hfloor_m2_S1_2_9_16c3, hfloor_m2_S1_2_9_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S1_2_9_16_corner01  :
    0 ≤ hfloor_m2_S1_2_9_16c1 + hfloor_m2_S1_2_9_16c2 * ((103293) / (500000)) + hfloor_m2_S1_2_9_16c3 * (1)
        + hfloor_m2_S1_2_9_16c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m2_S1_2_9_16c1 + hfloor_m2_S1_2_9_16c2 * ((103293) / (500000)) + hfloor_m2_S1_2_9_16c3 * (1)
        + hfloor_m2_S1_2_9_16c4 * (((103293) / (500000)) * (1))
      = (1707751)
        / (175000000) := by
    simp only [hfloor_m2_S1_2_9_16c1, hfloor_m2_S1_2_9_16c2, hfloor_m2_S1_2_9_16c3, hfloor_m2_S1_2_9_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S1_2_9_16_corner10  :
    0 ≤ hfloor_m2_S1_2_9_16c1 + hfloor_m2_S1_2_9_16c2 * ((206587) / (1000000)) + hfloor_m2_S1_2_9_16c3 * (0)
        + hfloor_m2_S1_2_9_16c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m2_S1_2_9_16c1 + hfloor_m2_S1_2_9_16c2 * ((206587) / (1000000)) + hfloor_m2_S1_2_9_16c3 * (0)
        + hfloor_m2_S1_2_9_16c4 * (((206587) / (1000000)) * (0))
      = (853963)
        / (87500000) := by
    simp only [hfloor_m2_S1_2_9_16c1, hfloor_m2_S1_2_9_16c2, hfloor_m2_S1_2_9_16c3, hfloor_m2_S1_2_9_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S1_2_9_16_corner11  :
    0 ≤ hfloor_m2_S1_2_9_16c1 + hfloor_m2_S1_2_9_16c2 * ((206587) / (1000000)) + hfloor_m2_S1_2_9_16c3 * (1)
        + hfloor_m2_S1_2_9_16c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m2_S1_2_9_16c1 + hfloor_m2_S1_2_9_16c2 * ((206587) / (1000000)) + hfloor_m2_S1_2_9_16c3 * (1)
        + hfloor_m2_S1_2_9_16c4 * (((206587) / (1000000)) * (1))
      = (853963)
        / (87500000) := by
    simp only [hfloor_m2_S1_2_9_16c1, hfloor_m2_S1_2_9_16c2, hfloor_m2_S1_2_9_16c3, hfloor_m2_S1_2_9_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S1_2_9_16_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (175000000 * L - 34444799) / (175000000) := by
  rw [← sub_nonneg, hfloor_m2_S1_2_9_16_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m2_S1_2_9_16_corner00)) ((hfloor_m2_S1_2_9_16_corner01)) ((hfloor_m2_S1_2_9_16_corner10)) ((hfloor_m2_S1_2_9_16_corner11))

/-! ### Instance (piece = 2) -/

noncomputable def hfloor_m2_S9_16_5_8c1 : ℝ :=
  ((-354428520691)) / (1761300000000)

noncomputable def hfloor_m2_S9_16_5_8c2 : ℝ :=
  1

noncomputable def hfloor_m2_S9_16_5_8c3 : ℝ :=
  0

noncomputable def hfloor_m2_S9_16_5_8c4 : ℝ :=
  0

theorem hfloor_m2_S9_16_5_8_bilinear (L _iv_dummy_HFloors : ℝ) :
    (1761300000000 * L - 354428520691) / (1761300000000) - 0
      = hfloor_m2_S9_16_5_8c1  + hfloor_m2_S9_16_5_8c2  * L + hfloor_m2_S9_16_5_8c3  * _iv_dummy_HFloors
        + hfloor_m2_S9_16_5_8c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m2_S9_16_5_8c1, hfloor_m2_S9_16_5_8c2, hfloor_m2_S9_16_5_8c3, hfloor_m2_S9_16_5_8c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m2_S9_16_5_8_corner00  :
    0 ≤ hfloor_m2_S9_16_5_8c1 + hfloor_m2_S9_16_5_8c2 * ((103293) / (500000)) + hfloor_m2_S9_16_5_8c3 * (0)
        + hfloor_m2_S9_16_5_8c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m2_S9_16_5_8c1 + hfloor_m2_S9_16_5_8c2 * ((103293) / (500000)) + hfloor_m2_S9_16_5_8c3 * (0)
        + hfloor_m2_S9_16_5_8c4 * (((103293) / (500000)) * (0))
      = (9431401109)
        / (1761300000000) := by
    simp only [hfloor_m2_S9_16_5_8c1, hfloor_m2_S9_16_5_8c2, hfloor_m2_S9_16_5_8c3, hfloor_m2_S9_16_5_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S9_16_5_8_corner01  :
    0 ≤ hfloor_m2_S9_16_5_8c1 + hfloor_m2_S9_16_5_8c2 * ((103293) / (500000)) + hfloor_m2_S9_16_5_8c3 * (1)
        + hfloor_m2_S9_16_5_8c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m2_S9_16_5_8c1 + hfloor_m2_S9_16_5_8c2 * ((103293) / (500000)) + hfloor_m2_S9_16_5_8c3 * (1)
        + hfloor_m2_S9_16_5_8c4 * (((103293) / (500000)) * (1))
      = (9431401109)
        / (1761300000000) := by
    simp only [hfloor_m2_S9_16_5_8c1, hfloor_m2_S9_16_5_8c2, hfloor_m2_S9_16_5_8c3, hfloor_m2_S9_16_5_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S9_16_5_8_corner10  :
    0 ≤ hfloor_m2_S9_16_5_8c1 + hfloor_m2_S9_16_5_8c2 * ((206587) / (1000000)) + hfloor_m2_S9_16_5_8c3 * (0)
        + hfloor_m2_S9_16_5_8c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m2_S9_16_5_8c1 + hfloor_m2_S9_16_5_8c2 * ((206587) / (1000000)) + hfloor_m2_S9_16_5_8c3 * (0)
        + hfloor_m2_S9_16_5_8c4 * (((206587) / (1000000)) * (0))
      = (9433162409)
        / (1761300000000) := by
    simp only [hfloor_m2_S9_16_5_8c1, hfloor_m2_S9_16_5_8c2, hfloor_m2_S9_16_5_8c3, hfloor_m2_S9_16_5_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S9_16_5_8_corner11  :
    0 ≤ hfloor_m2_S9_16_5_8c1 + hfloor_m2_S9_16_5_8c2 * ((206587) / (1000000)) + hfloor_m2_S9_16_5_8c3 * (1)
        + hfloor_m2_S9_16_5_8c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m2_S9_16_5_8c1 + hfloor_m2_S9_16_5_8c2 * ((206587) / (1000000)) + hfloor_m2_S9_16_5_8c3 * (1)
        + hfloor_m2_S9_16_5_8c4 * (((206587) / (1000000)) * (1))
      = (9433162409)
        / (1761300000000) := by
    simp only [hfloor_m2_S9_16_5_8c1, hfloor_m2_S9_16_5_8c2, hfloor_m2_S9_16_5_8c3, hfloor_m2_S9_16_5_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S9_16_5_8_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (1761300000000 * L - 354428520691) / (1761300000000) := by
  rw [← sub_nonneg, hfloor_m2_S9_16_5_8_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m2_S9_16_5_8_corner00)) ((hfloor_m2_S9_16_5_8_corner01)) ((hfloor_m2_S9_16_5_8_corner10)) ((hfloor_m2_S9_16_5_8_corner11))

/-! ### Instance (piece = 3) -/

noncomputable def hfloor_m2_S5_8_11_16c1 : ℝ :=
  ((-11136703224287)) / (54723000000000)

noncomputable def hfloor_m2_S5_8_11_16c2 : ℝ :=
  1

noncomputable def hfloor_m2_S5_8_11_16c3 : ℝ :=
  0

noncomputable def hfloor_m2_S5_8_11_16c4 : ℝ :=
  0

theorem hfloor_m2_S5_8_11_16_bilinear (L _iv_dummy_HFloors : ℝ) :
    (54723000000000 * L - 11136703224287) / (54723000000000) - 0
      = hfloor_m2_S5_8_11_16c1  + hfloor_m2_S5_8_11_16c2  * L + hfloor_m2_S5_8_11_16c3  * _iv_dummy_HFloors
        + hfloor_m2_S5_8_11_16c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m2_S5_8_11_16c1, hfloor_m2_S5_8_11_16c2, hfloor_m2_S5_8_11_16c3, hfloor_m2_S5_8_11_16c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m2_S5_8_11_16_corner00  :
    0 ≤ hfloor_m2_S5_8_11_16c1 + hfloor_m2_S5_8_11_16c2 * ((103293) / (500000)) + hfloor_m2_S5_8_11_16c3 * (0)
        + hfloor_m2_S5_8_11_16c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m2_S5_8_11_16c1 + hfloor_m2_S5_8_11_16c2 * ((103293) / (500000)) + hfloor_m2_S5_8_11_16c3 * (0)
        + hfloor_m2_S5_8_11_16c4 * (((103293) / (500000)) * (0))
      = (168302453713)
        / (54723000000000) := by
    simp only [hfloor_m2_S5_8_11_16c1, hfloor_m2_S5_8_11_16c2, hfloor_m2_S5_8_11_16c3, hfloor_m2_S5_8_11_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S5_8_11_16_corner01  :
    0 ≤ hfloor_m2_S5_8_11_16c1 + hfloor_m2_S5_8_11_16c2 * ((103293) / (500000)) + hfloor_m2_S5_8_11_16c3 * (1)
        + hfloor_m2_S5_8_11_16c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m2_S5_8_11_16c1 + hfloor_m2_S5_8_11_16c2 * ((103293) / (500000)) + hfloor_m2_S5_8_11_16c3 * (1)
        + hfloor_m2_S5_8_11_16c4 * (((103293) / (500000)) * (1))
      = (168302453713)
        / (54723000000000) := by
    simp only [hfloor_m2_S5_8_11_16c1, hfloor_m2_S5_8_11_16c2, hfloor_m2_S5_8_11_16c3, hfloor_m2_S5_8_11_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S5_8_11_16_corner10  :
    0 ≤ hfloor_m2_S5_8_11_16c1 + hfloor_m2_S5_8_11_16c2 * ((206587) / (1000000)) + hfloor_m2_S5_8_11_16c3 * (0)
        + hfloor_m2_S5_8_11_16c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m2_S5_8_11_16c1 + hfloor_m2_S5_8_11_16c2 * ((206587) / (1000000)) + hfloor_m2_S5_8_11_16c3 * (0)
        + hfloor_m2_S5_8_11_16c4 * (((206587) / (1000000)) * (0))
      = (168357176713)
        / (54723000000000) := by
    simp only [hfloor_m2_S5_8_11_16c1, hfloor_m2_S5_8_11_16c2, hfloor_m2_S5_8_11_16c3, hfloor_m2_S5_8_11_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S5_8_11_16_corner11  :
    0 ≤ hfloor_m2_S5_8_11_16c1 + hfloor_m2_S5_8_11_16c2 * ((206587) / (1000000)) + hfloor_m2_S5_8_11_16c3 * (1)
        + hfloor_m2_S5_8_11_16c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m2_S5_8_11_16c1 + hfloor_m2_S5_8_11_16c2 * ((206587) / (1000000)) + hfloor_m2_S5_8_11_16c3 * (1)
        + hfloor_m2_S5_8_11_16c4 * (((206587) / (1000000)) * (1))
      = (168357176713)
        / (54723000000000) := by
    simp only [hfloor_m2_S5_8_11_16c1, hfloor_m2_S5_8_11_16c2, hfloor_m2_S5_8_11_16c3, hfloor_m2_S5_8_11_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S5_8_11_16_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (54723000000000 * L - 11136703224287) / (54723000000000) := by
  rw [← sub_nonneg, hfloor_m2_S5_8_11_16_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m2_S5_8_11_16_corner00)) ((hfloor_m2_S5_8_11_16_corner01)) ((hfloor_m2_S5_8_11_16_corner10)) ((hfloor_m2_S5_8_11_16_corner11))

/-! ### Instance (piece = 4) -/

noncomputable def hfloor_m2_S11_16_3_4c1 : ℝ :=
  ((-12126789551)) / (59000000000)

noncomputable def hfloor_m2_S11_16_3_4c2 : ℝ :=
  1

noncomputable def hfloor_m2_S11_16_3_4c3 : ℝ :=
  0

noncomputable def hfloor_m2_S11_16_3_4c4 : ℝ :=
  0

theorem hfloor_m2_S11_16_3_4_bilinear (L _iv_dummy_HFloors : ℝ) :
    (59000000000 * L - 12126789551) / (59000000000) - 0
      = hfloor_m2_S11_16_3_4c1  + hfloor_m2_S11_16_3_4c2  * L + hfloor_m2_S11_16_3_4c3  * _iv_dummy_HFloors
        + hfloor_m2_S11_16_3_4c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m2_S11_16_3_4c1, hfloor_m2_S11_16_3_4c2, hfloor_m2_S11_16_3_4c3, hfloor_m2_S11_16_3_4c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m2_S11_16_3_4_corner00  :
    0 ≤ hfloor_m2_S11_16_3_4c1 + hfloor_m2_S11_16_3_4c2 * ((103293) / (500000)) + hfloor_m2_S11_16_3_4c3 * (0)
        + hfloor_m2_S11_16_3_4c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m2_S11_16_3_4c1 + hfloor_m2_S11_16_3_4c2 * ((103293) / (500000)) + hfloor_m2_S11_16_3_4c3 * (0)
        + hfloor_m2_S11_16_3_4c4 * (((103293) / (500000)) * (0))
      = (61784449)
        / (59000000000) := by
    simp only [hfloor_m2_S11_16_3_4c1, hfloor_m2_S11_16_3_4c2, hfloor_m2_S11_16_3_4c3, hfloor_m2_S11_16_3_4c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S11_16_3_4_corner01  :
    0 ≤ hfloor_m2_S11_16_3_4c1 + hfloor_m2_S11_16_3_4c2 * ((103293) / (500000)) + hfloor_m2_S11_16_3_4c3 * (1)
        + hfloor_m2_S11_16_3_4c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m2_S11_16_3_4c1 + hfloor_m2_S11_16_3_4c2 * ((103293) / (500000)) + hfloor_m2_S11_16_3_4c3 * (1)
        + hfloor_m2_S11_16_3_4c4 * (((103293) / (500000)) * (1))
      = (61784449)
        / (59000000000) := by
    simp only [hfloor_m2_S11_16_3_4c1, hfloor_m2_S11_16_3_4c2, hfloor_m2_S11_16_3_4c3, hfloor_m2_S11_16_3_4c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S11_16_3_4_corner10  :
    0 ≤ hfloor_m2_S11_16_3_4c1 + hfloor_m2_S11_16_3_4c2 * ((206587) / (1000000)) + hfloor_m2_S11_16_3_4c3 * (0)
        + hfloor_m2_S11_16_3_4c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m2_S11_16_3_4c1 + hfloor_m2_S11_16_3_4c2 * ((206587) / (1000000)) + hfloor_m2_S11_16_3_4c3 * (0)
        + hfloor_m2_S11_16_3_4c4 * (((206587) / (1000000)) * (0))
      = (61843449)
        / (59000000000) := by
    simp only [hfloor_m2_S11_16_3_4c1, hfloor_m2_S11_16_3_4c2, hfloor_m2_S11_16_3_4c3, hfloor_m2_S11_16_3_4c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S11_16_3_4_corner11  :
    0 ≤ hfloor_m2_S11_16_3_4c1 + hfloor_m2_S11_16_3_4c2 * ((206587) / (1000000)) + hfloor_m2_S11_16_3_4c3 * (1)
        + hfloor_m2_S11_16_3_4c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m2_S11_16_3_4c1 + hfloor_m2_S11_16_3_4c2 * ((206587) / (1000000)) + hfloor_m2_S11_16_3_4c3 * (1)
        + hfloor_m2_S11_16_3_4c4 * (((206587) / (1000000)) * (1))
      = (61843449)
        / (59000000000) := by
    simp only [hfloor_m2_S11_16_3_4c1, hfloor_m2_S11_16_3_4c2, hfloor_m2_S11_16_3_4c3, hfloor_m2_S11_16_3_4c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S11_16_3_4_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (59000000000 * L - 12126789551) / (59000000000) := by
  rw [← sub_nonneg, hfloor_m2_S11_16_3_4_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m2_S11_16_3_4_corner00)) ((hfloor_m2_S11_16_3_4_corner01)) ((hfloor_m2_S11_16_3_4_corner10)) ((hfloor_m2_S11_16_3_4_corner11))

/-! ### Instance (piece = 5) -/

noncomputable def hfloor_m2_S3_4_25_32c1 : ℝ :=
  ((-77049142523)) / (387000000000)

noncomputable def hfloor_m2_S3_4_25_32c2 : ℝ :=
  1

noncomputable def hfloor_m2_S3_4_25_32c3 : ℝ :=
  0

noncomputable def hfloor_m2_S3_4_25_32c4 : ℝ :=
  0

theorem hfloor_m2_S3_4_25_32_bilinear (L _iv_dummy_HFloors : ℝ) :
    (387000000000 * L - 77049142523) / (387000000000) - 0
      = hfloor_m2_S3_4_25_32c1  + hfloor_m2_S3_4_25_32c2  * L + hfloor_m2_S3_4_25_32c3  * _iv_dummy_HFloors
        + hfloor_m2_S3_4_25_32c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m2_S3_4_25_32c1, hfloor_m2_S3_4_25_32c2, hfloor_m2_S3_4_25_32c3, hfloor_m2_S3_4_25_32c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m2_S3_4_25_32_corner00  :
    0 ≤ hfloor_m2_S3_4_25_32c1 + hfloor_m2_S3_4_25_32c2 * ((103293) / (500000)) + hfloor_m2_S3_4_25_32c3 * (0)
        + hfloor_m2_S3_4_25_32c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m2_S3_4_25_32c1 + hfloor_m2_S3_4_25_32c2 * ((103293) / (500000)) + hfloor_m2_S3_4_25_32c3 * (0)
        + hfloor_m2_S3_4_25_32c4 * (((103293) / (500000)) * (0))
      = (2899639477)
        / (387000000000) := by
    simp only [hfloor_m2_S3_4_25_32c1, hfloor_m2_S3_4_25_32c2, hfloor_m2_S3_4_25_32c3, hfloor_m2_S3_4_25_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S3_4_25_32_corner01  :
    0 ≤ hfloor_m2_S3_4_25_32c1 + hfloor_m2_S3_4_25_32c2 * ((103293) / (500000)) + hfloor_m2_S3_4_25_32c3 * (1)
        + hfloor_m2_S3_4_25_32c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m2_S3_4_25_32c1 + hfloor_m2_S3_4_25_32c2 * ((103293) / (500000)) + hfloor_m2_S3_4_25_32c3 * (1)
        + hfloor_m2_S3_4_25_32c4 * (((103293) / (500000)) * (1))
      = (2899639477)
        / (387000000000) := by
    simp only [hfloor_m2_S3_4_25_32c1, hfloor_m2_S3_4_25_32c2, hfloor_m2_S3_4_25_32c3, hfloor_m2_S3_4_25_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S3_4_25_32_corner10  :
    0 ≤ hfloor_m2_S3_4_25_32c1 + hfloor_m2_S3_4_25_32c2 * ((206587) / (1000000)) + hfloor_m2_S3_4_25_32c3 * (0)
        + hfloor_m2_S3_4_25_32c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m2_S3_4_25_32c1 + hfloor_m2_S3_4_25_32c2 * ((206587) / (1000000)) + hfloor_m2_S3_4_25_32c3 * (0)
        + hfloor_m2_S3_4_25_32c4 * (((206587) / (1000000)) * (0))
      = (2900026477)
        / (387000000000) := by
    simp only [hfloor_m2_S3_4_25_32c1, hfloor_m2_S3_4_25_32c2, hfloor_m2_S3_4_25_32c3, hfloor_m2_S3_4_25_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S3_4_25_32_corner11  :
    0 ≤ hfloor_m2_S3_4_25_32c1 + hfloor_m2_S3_4_25_32c2 * ((206587) / (1000000)) + hfloor_m2_S3_4_25_32c3 * (1)
        + hfloor_m2_S3_4_25_32c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m2_S3_4_25_32c1 + hfloor_m2_S3_4_25_32c2 * ((206587) / (1000000)) + hfloor_m2_S3_4_25_32c3 * (1)
        + hfloor_m2_S3_4_25_32c4 * (((206587) / (1000000)) * (1))
      = (2900026477)
        / (387000000000) := by
    simp only [hfloor_m2_S3_4_25_32c1, hfloor_m2_S3_4_25_32c2, hfloor_m2_S3_4_25_32c3, hfloor_m2_S3_4_25_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S3_4_25_32_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (387000000000 * L - 77049142523) / (387000000000) := by
  rw [← sub_nonneg, hfloor_m2_S3_4_25_32_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m2_S3_4_25_32_corner00)) ((hfloor_m2_S3_4_25_32_corner01)) ((hfloor_m2_S3_4_25_32_corner10)) ((hfloor_m2_S3_4_25_32_corner11))

/-! ### Instance (piece = 6) -/

noncomputable def hfloor_m2_S25_32_13_16c1 : ℝ :=
  ((-3431389691)) / (17160000000)

noncomputable def hfloor_m2_S25_32_13_16c2 : ℝ :=
  1

noncomputable def hfloor_m2_S25_32_13_16c3 : ℝ :=
  0

noncomputable def hfloor_m2_S25_32_13_16c4 : ℝ :=
  0

theorem hfloor_m2_S25_32_13_16_bilinear (L _iv_dummy_HFloors : ℝ) :
    (17160000000 * L - 3431389691) / (17160000000) - 0
      = hfloor_m2_S25_32_13_16c1  + hfloor_m2_S25_32_13_16c2  * L + hfloor_m2_S25_32_13_16c3  * _iv_dummy_HFloors
        + hfloor_m2_S25_32_13_16c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m2_S25_32_13_16c1, hfloor_m2_S25_32_13_16c2, hfloor_m2_S25_32_13_16c3, hfloor_m2_S25_32_13_16c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m2_S25_32_13_16_corner00  :
    0 ≤ hfloor_m2_S25_32_13_16c1 + hfloor_m2_S25_32_13_16c2 * ((103293) / (500000)) + hfloor_m2_S25_32_13_16c3 * (0)
        + hfloor_m2_S25_32_13_16c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m2_S25_32_13_16c1 + hfloor_m2_S25_32_13_16c2 * ((103293) / (500000)) + hfloor_m2_S25_32_13_16c3 * (0)
        + hfloor_m2_S25_32_13_16c4 * (((103293) / (500000)) * (0))
      = (113626069)
        / (17160000000) := by
    simp only [hfloor_m2_S25_32_13_16c1, hfloor_m2_S25_32_13_16c2, hfloor_m2_S25_32_13_16c3, hfloor_m2_S25_32_13_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S25_32_13_16_corner01  :
    0 ≤ hfloor_m2_S25_32_13_16c1 + hfloor_m2_S25_32_13_16c2 * ((103293) / (500000)) + hfloor_m2_S25_32_13_16c3 * (1)
        + hfloor_m2_S25_32_13_16c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m2_S25_32_13_16c1 + hfloor_m2_S25_32_13_16c2 * ((103293) / (500000)) + hfloor_m2_S25_32_13_16c3 * (1)
        + hfloor_m2_S25_32_13_16c4 * (((103293) / (500000)) * (1))
      = (113626069)
        / (17160000000) := by
    simp only [hfloor_m2_S25_32_13_16c1, hfloor_m2_S25_32_13_16c2, hfloor_m2_S25_32_13_16c3, hfloor_m2_S25_32_13_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S25_32_13_16_corner10  :
    0 ≤ hfloor_m2_S25_32_13_16c1 + hfloor_m2_S25_32_13_16c2 * ((206587) / (1000000)) + hfloor_m2_S25_32_13_16c3 * (0)
        + hfloor_m2_S25_32_13_16c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m2_S25_32_13_16c1 + hfloor_m2_S25_32_13_16c2 * ((206587) / (1000000)) + hfloor_m2_S25_32_13_16c3 * (0)
        + hfloor_m2_S25_32_13_16c4 * (((206587) / (1000000)) * (0))
      = (113643229)
        / (17160000000) := by
    simp only [hfloor_m2_S25_32_13_16c1, hfloor_m2_S25_32_13_16c2, hfloor_m2_S25_32_13_16c3, hfloor_m2_S25_32_13_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S25_32_13_16_corner11  :
    0 ≤ hfloor_m2_S25_32_13_16c1 + hfloor_m2_S25_32_13_16c2 * ((206587) / (1000000)) + hfloor_m2_S25_32_13_16c3 * (1)
        + hfloor_m2_S25_32_13_16c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m2_S25_32_13_16c1 + hfloor_m2_S25_32_13_16c2 * ((206587) / (1000000)) + hfloor_m2_S25_32_13_16c3 * (1)
        + hfloor_m2_S25_32_13_16c4 * (((206587) / (1000000)) * (1))
      = (113643229)
        / (17160000000) := by
    simp only [hfloor_m2_S25_32_13_16c1, hfloor_m2_S25_32_13_16c2, hfloor_m2_S25_32_13_16c3, hfloor_m2_S25_32_13_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S25_32_13_16_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (17160000000 * L - 3431389691) / (17160000000) := by
  rw [← sub_nonneg, hfloor_m2_S25_32_13_16_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m2_S25_32_13_16_corner00)) ((hfloor_m2_S25_32_13_16_corner01)) ((hfloor_m2_S25_32_13_16_corner10)) ((hfloor_m2_S25_32_13_16_corner11))

/-! ### Instance (piece = 7) -/

noncomputable def hfloor_m2_S13_16_27_32c1 : ℝ :=
  ((-12247294461)) / (61000000000)

noncomputable def hfloor_m2_S13_16_27_32c2 : ℝ :=
  1

noncomputable def hfloor_m2_S13_16_27_32c3 : ℝ :=
  0

noncomputable def hfloor_m2_S13_16_27_32c4 : ℝ :=
  0

theorem hfloor_m2_S13_16_27_32_bilinear (L _iv_dummy_HFloors : ℝ) :
    (61000000000 * L - 12247294461) / (61000000000) - 0
      = hfloor_m2_S13_16_27_32c1  + hfloor_m2_S13_16_27_32c2  * L + hfloor_m2_S13_16_27_32c3  * _iv_dummy_HFloors
        + hfloor_m2_S13_16_27_32c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m2_S13_16_27_32c1, hfloor_m2_S13_16_27_32c2, hfloor_m2_S13_16_27_32c3, hfloor_m2_S13_16_27_32c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m2_S13_16_27_32_corner00  :
    0 ≤ hfloor_m2_S13_16_27_32c1 + hfloor_m2_S13_16_27_32c2 * ((103293) / (500000)) + hfloor_m2_S13_16_27_32c3 * (0)
        + hfloor_m2_S13_16_27_32c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m2_S13_16_27_32c1 + hfloor_m2_S13_16_27_32c2 * ((103293) / (500000)) + hfloor_m2_S13_16_27_32c3 * (0)
        + hfloor_m2_S13_16_27_32c4 * (((103293) / (500000)) * (0))
      = (354451539)
        / (61000000000) := by
    simp only [hfloor_m2_S13_16_27_32c1, hfloor_m2_S13_16_27_32c2, hfloor_m2_S13_16_27_32c3, hfloor_m2_S13_16_27_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S13_16_27_32_corner01  :
    0 ≤ hfloor_m2_S13_16_27_32c1 + hfloor_m2_S13_16_27_32c2 * ((103293) / (500000)) + hfloor_m2_S13_16_27_32c3 * (1)
        + hfloor_m2_S13_16_27_32c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m2_S13_16_27_32c1 + hfloor_m2_S13_16_27_32c2 * ((103293) / (500000)) + hfloor_m2_S13_16_27_32c3 * (1)
        + hfloor_m2_S13_16_27_32c4 * (((103293) / (500000)) * (1))
      = (354451539)
        / (61000000000) := by
    simp only [hfloor_m2_S13_16_27_32c1, hfloor_m2_S13_16_27_32c2, hfloor_m2_S13_16_27_32c3, hfloor_m2_S13_16_27_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S13_16_27_32_corner10  :
    0 ≤ hfloor_m2_S13_16_27_32c1 + hfloor_m2_S13_16_27_32c2 * ((206587) / (1000000)) + hfloor_m2_S13_16_27_32c3 * (0)
        + hfloor_m2_S13_16_27_32c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m2_S13_16_27_32c1 + hfloor_m2_S13_16_27_32c2 * ((206587) / (1000000)) + hfloor_m2_S13_16_27_32c3 * (0)
        + hfloor_m2_S13_16_27_32c4 * (((206587) / (1000000)) * (0))
      = (354512539)
        / (61000000000) := by
    simp only [hfloor_m2_S13_16_27_32c1, hfloor_m2_S13_16_27_32c2, hfloor_m2_S13_16_27_32c3, hfloor_m2_S13_16_27_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S13_16_27_32_corner11  :
    0 ≤ hfloor_m2_S13_16_27_32c1 + hfloor_m2_S13_16_27_32c2 * ((206587) / (1000000)) + hfloor_m2_S13_16_27_32c3 * (1)
        + hfloor_m2_S13_16_27_32c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m2_S13_16_27_32c1 + hfloor_m2_S13_16_27_32c2 * ((206587) / (1000000)) + hfloor_m2_S13_16_27_32c3 * (1)
        + hfloor_m2_S13_16_27_32c4 * (((206587) / (1000000)) * (1))
      = (354512539)
        / (61000000000) := by
    simp only [hfloor_m2_S13_16_27_32c1, hfloor_m2_S13_16_27_32c2, hfloor_m2_S13_16_27_32c3, hfloor_m2_S13_16_27_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S13_16_27_32_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (61000000000 * L - 12247294461) / (61000000000) := by
  rw [← sub_nonneg, hfloor_m2_S13_16_27_32_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m2_S13_16_27_32_corner00)) ((hfloor_m2_S13_16_27_32_corner01)) ((hfloor_m2_S13_16_27_32_corner10)) ((hfloor_m2_S13_16_27_32_corner11))

/-! ### Instance (piece = 8) -/

noncomputable def hfloor_m2_S27_32_7_8c1 : ℝ :=
  ((-4096218128239)) / (20325750000000)

noncomputable def hfloor_m2_S27_32_7_8c2 : ℝ :=
  1

noncomputable def hfloor_m2_S27_32_7_8c3 : ℝ :=
  0

noncomputable def hfloor_m2_S27_32_7_8c4 : ℝ :=
  0

theorem hfloor_m2_S27_32_7_8_bilinear (L _iv_dummy_HFloors : ℝ) :
    (20325750000000 * L - 4096218128239) / (20325750000000) - 0
      = hfloor_m2_S27_32_7_8c1  + hfloor_m2_S27_32_7_8c2  * L + hfloor_m2_S27_32_7_8c3  * _iv_dummy_HFloors
        + hfloor_m2_S27_32_7_8c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m2_S27_32_7_8c1, hfloor_m2_S27_32_7_8c2, hfloor_m2_S27_32_7_8c3, hfloor_m2_S27_32_7_8c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m2_S27_32_7_8_corner00  :
    0 ≤ hfloor_m2_S27_32_7_8c1 + hfloor_m2_S27_32_7_8c2 * ((103293) / (500000)) + hfloor_m2_S27_32_7_8c3 * (0)
        + hfloor_m2_S27_32_7_8c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m2_S27_32_7_8c1 + hfloor_m2_S27_32_7_8c2 * ((103293) / (500000)) + hfloor_m2_S27_32_7_8c3 * (0)
        + hfloor_m2_S27_32_7_8c4 * (((103293) / (500000)) * (0))
      = (102797261261)
        / (20325750000000) := by
    simp only [hfloor_m2_S27_32_7_8c1, hfloor_m2_S27_32_7_8c2, hfloor_m2_S27_32_7_8c3, hfloor_m2_S27_32_7_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S27_32_7_8_corner01  :
    0 ≤ hfloor_m2_S27_32_7_8c1 + hfloor_m2_S27_32_7_8c2 * ((103293) / (500000)) + hfloor_m2_S27_32_7_8c3 * (1)
        + hfloor_m2_S27_32_7_8c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m2_S27_32_7_8c1 + hfloor_m2_S27_32_7_8c2 * ((103293) / (500000)) + hfloor_m2_S27_32_7_8c3 * (1)
        + hfloor_m2_S27_32_7_8c4 * (((103293) / (500000)) * (1))
      = (102797261261)
        / (20325750000000) := by
    simp only [hfloor_m2_S27_32_7_8c1, hfloor_m2_S27_32_7_8c2, hfloor_m2_S27_32_7_8c3, hfloor_m2_S27_32_7_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S27_32_7_8_corner10  :
    0 ≤ hfloor_m2_S27_32_7_8c1 + hfloor_m2_S27_32_7_8c2 * ((206587) / (1000000)) + hfloor_m2_S27_32_7_8c3 * (0)
        + hfloor_m2_S27_32_7_8c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m2_S27_32_7_8c1 + hfloor_m2_S27_32_7_8c2 * ((206587) / (1000000)) + hfloor_m2_S27_32_7_8c3 * (0)
        + hfloor_m2_S27_32_7_8c4 * (((206587) / (1000000)) * (0))
      = (102817587011)
        / (20325750000000) := by
    simp only [hfloor_m2_S27_32_7_8c1, hfloor_m2_S27_32_7_8c2, hfloor_m2_S27_32_7_8c3, hfloor_m2_S27_32_7_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S27_32_7_8_corner11  :
    0 ≤ hfloor_m2_S27_32_7_8c1 + hfloor_m2_S27_32_7_8c2 * ((206587) / (1000000)) + hfloor_m2_S27_32_7_8c3 * (1)
        + hfloor_m2_S27_32_7_8c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m2_S27_32_7_8c1 + hfloor_m2_S27_32_7_8c2 * ((206587) / (1000000)) + hfloor_m2_S27_32_7_8c3 * (1)
        + hfloor_m2_S27_32_7_8c4 * (((206587) / (1000000)) * (1))
      = (102817587011)
        / (20325750000000) := by
    simp only [hfloor_m2_S27_32_7_8c1, hfloor_m2_S27_32_7_8c2, hfloor_m2_S27_32_7_8c3, hfloor_m2_S27_32_7_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S27_32_7_8_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (20325750000000 * L - 4096218128239) / (20325750000000) := by
  rw [← sub_nonneg, hfloor_m2_S27_32_7_8_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m2_S27_32_7_8_corner00)) ((hfloor_m2_S27_32_7_8_corner01)) ((hfloor_m2_S27_32_7_8_corner10)) ((hfloor_m2_S27_32_7_8_corner11))

/-! ### Instance (piece = 9) -/

noncomputable def hfloor_m2_S7_8_29_32c1 : ℝ :=
  ((-6262689845227)) / (30969000000000)

noncomputable def hfloor_m2_S7_8_29_32c2 : ℝ :=
  1

noncomputable def hfloor_m2_S7_8_29_32c3 : ℝ :=
  0

noncomputable def hfloor_m2_S7_8_29_32c4 : ℝ :=
  0

theorem hfloor_m2_S7_8_29_32_bilinear (L _iv_dummy_HFloors : ℝ) :
    (30969000000000 * L - 6262689845227) / (30969000000000) - 0
      = hfloor_m2_S7_8_29_32c1  + hfloor_m2_S7_8_29_32c2  * L + hfloor_m2_S7_8_29_32c3  * _iv_dummy_HFloors
        + hfloor_m2_S7_8_29_32c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m2_S7_8_29_32c1, hfloor_m2_S7_8_29_32c2, hfloor_m2_S7_8_29_32c3, hfloor_m2_S7_8_29_32c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m2_S7_8_29_32_corner00  :
    0 ≤ hfloor_m2_S7_8_29_32c1 + hfloor_m2_S7_8_29_32c2 * ((103293) / (500000)) + hfloor_m2_S7_8_29_32c3 * (0)
        + hfloor_m2_S7_8_29_32c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m2_S7_8_29_32c1 + hfloor_m2_S7_8_29_32c2 * ((103293) / (500000)) + hfloor_m2_S7_8_29_32c3 * (0)
        + hfloor_m2_S7_8_29_32c4 * (((103293) / (500000)) * (0))
      = (135071988773)
        / (30969000000000) := by
    simp only [hfloor_m2_S7_8_29_32c1, hfloor_m2_S7_8_29_32c2, hfloor_m2_S7_8_29_32c3, hfloor_m2_S7_8_29_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S7_8_29_32_corner01  :
    0 ≤ hfloor_m2_S7_8_29_32c1 + hfloor_m2_S7_8_29_32c2 * ((103293) / (500000)) + hfloor_m2_S7_8_29_32c3 * (1)
        + hfloor_m2_S7_8_29_32c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m2_S7_8_29_32c1 + hfloor_m2_S7_8_29_32c2 * ((103293) / (500000)) + hfloor_m2_S7_8_29_32c3 * (1)
        + hfloor_m2_S7_8_29_32c4 * (((103293) / (500000)) * (1))
      = (135071988773)
        / (30969000000000) := by
    simp only [hfloor_m2_S7_8_29_32c1, hfloor_m2_S7_8_29_32c2, hfloor_m2_S7_8_29_32c3, hfloor_m2_S7_8_29_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S7_8_29_32_corner10  :
    0 ≤ hfloor_m2_S7_8_29_32c1 + hfloor_m2_S7_8_29_32c2 * ((206587) / (1000000)) + hfloor_m2_S7_8_29_32c3 * (0)
        + hfloor_m2_S7_8_29_32c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m2_S7_8_29_32c1 + hfloor_m2_S7_8_29_32c2 * ((206587) / (1000000)) + hfloor_m2_S7_8_29_32c3 * (0)
        + hfloor_m2_S7_8_29_32c4 * (((206587) / (1000000)) * (0))
      = (135102957773)
        / (30969000000000) := by
    simp only [hfloor_m2_S7_8_29_32c1, hfloor_m2_S7_8_29_32c2, hfloor_m2_S7_8_29_32c3, hfloor_m2_S7_8_29_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S7_8_29_32_corner11  :
    0 ≤ hfloor_m2_S7_8_29_32c1 + hfloor_m2_S7_8_29_32c2 * ((206587) / (1000000)) + hfloor_m2_S7_8_29_32c3 * (1)
        + hfloor_m2_S7_8_29_32c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m2_S7_8_29_32c1 + hfloor_m2_S7_8_29_32c2 * ((206587) / (1000000)) + hfloor_m2_S7_8_29_32c3 * (1)
        + hfloor_m2_S7_8_29_32c4 * (((206587) / (1000000)) * (1))
      = (135102957773)
        / (30969000000000) := by
    simp only [hfloor_m2_S7_8_29_32c1, hfloor_m2_S7_8_29_32c2, hfloor_m2_S7_8_29_32c3, hfloor_m2_S7_8_29_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S7_8_29_32_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (30969000000000 * L - 6262689845227) / (30969000000000) := by
  rw [← sub_nonneg, hfloor_m2_S7_8_29_32_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m2_S7_8_29_32_corner00)) ((hfloor_m2_S7_8_29_32_corner01)) ((hfloor_m2_S7_8_29_32_corner10)) ((hfloor_m2_S7_8_29_32_corner11))

/-! ### Instance (piece = 10) -/

noncomputable def hfloor_m2_S29_32_15_16c1 : ℝ :=
  ((-202862953)) / (1000000000)

noncomputable def hfloor_m2_S29_32_15_16c2 : ℝ :=
  1

noncomputable def hfloor_m2_S29_32_15_16c3 : ℝ :=
  0

noncomputable def hfloor_m2_S29_32_15_16c4 : ℝ :=
  0

theorem hfloor_m2_S29_32_15_16_bilinear (L _iv_dummy_HFloors : ℝ) :
    (1000000000 * L - 202862953) / (1000000000) - 0
      = hfloor_m2_S29_32_15_16c1  + hfloor_m2_S29_32_15_16c2  * L + hfloor_m2_S29_32_15_16c3  * _iv_dummy_HFloors
        + hfloor_m2_S29_32_15_16c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m2_S29_32_15_16c1, hfloor_m2_S29_32_15_16c2, hfloor_m2_S29_32_15_16c3, hfloor_m2_S29_32_15_16c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m2_S29_32_15_16_corner00  :
    0 ≤ hfloor_m2_S29_32_15_16c1 + hfloor_m2_S29_32_15_16c2 * ((103293) / (500000)) + hfloor_m2_S29_32_15_16c3 * (0)
        + hfloor_m2_S29_32_15_16c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m2_S29_32_15_16c1 + hfloor_m2_S29_32_15_16c2 * ((103293) / (500000)) + hfloor_m2_S29_32_15_16c3 * (0)
        + hfloor_m2_S29_32_15_16c4 * (((103293) / (500000)) * (0))
      = (3723047)
        / (1000000000) := by
    simp only [hfloor_m2_S29_32_15_16c1, hfloor_m2_S29_32_15_16c2, hfloor_m2_S29_32_15_16c3, hfloor_m2_S29_32_15_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S29_32_15_16_corner01  :
    0 ≤ hfloor_m2_S29_32_15_16c1 + hfloor_m2_S29_32_15_16c2 * ((103293) / (500000)) + hfloor_m2_S29_32_15_16c3 * (1)
        + hfloor_m2_S29_32_15_16c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m2_S29_32_15_16c1 + hfloor_m2_S29_32_15_16c2 * ((103293) / (500000)) + hfloor_m2_S29_32_15_16c3 * (1)
        + hfloor_m2_S29_32_15_16c4 * (((103293) / (500000)) * (1))
      = (3723047)
        / (1000000000) := by
    simp only [hfloor_m2_S29_32_15_16c1, hfloor_m2_S29_32_15_16c2, hfloor_m2_S29_32_15_16c3, hfloor_m2_S29_32_15_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S29_32_15_16_corner10  :
    0 ≤ hfloor_m2_S29_32_15_16c1 + hfloor_m2_S29_32_15_16c2 * ((206587) / (1000000)) + hfloor_m2_S29_32_15_16c3 * (0)
        + hfloor_m2_S29_32_15_16c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m2_S29_32_15_16c1 + hfloor_m2_S29_32_15_16c2 * ((206587) / (1000000)) + hfloor_m2_S29_32_15_16c3 * (0)
        + hfloor_m2_S29_32_15_16c4 * (((206587) / (1000000)) * (0))
      = (3724047)
        / (1000000000) := by
    simp only [hfloor_m2_S29_32_15_16c1, hfloor_m2_S29_32_15_16c2, hfloor_m2_S29_32_15_16c3, hfloor_m2_S29_32_15_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S29_32_15_16_corner11  :
    0 ≤ hfloor_m2_S29_32_15_16c1 + hfloor_m2_S29_32_15_16c2 * ((206587) / (1000000)) + hfloor_m2_S29_32_15_16c3 * (1)
        + hfloor_m2_S29_32_15_16c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m2_S29_32_15_16c1 + hfloor_m2_S29_32_15_16c2 * ((206587) / (1000000)) + hfloor_m2_S29_32_15_16c3 * (1)
        + hfloor_m2_S29_32_15_16c4 * (((206587) / (1000000)) * (1))
      = (3724047)
        / (1000000000) := by
    simp only [hfloor_m2_S29_32_15_16c1, hfloor_m2_S29_32_15_16c2, hfloor_m2_S29_32_15_16c3, hfloor_m2_S29_32_15_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S29_32_15_16_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (1000000000 * L - 202862953) / (1000000000) := by
  rw [← sub_nonneg, hfloor_m2_S29_32_15_16_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m2_S29_32_15_16_corner00)) ((hfloor_m2_S29_32_15_16_corner01)) ((hfloor_m2_S29_32_15_16_corner10)) ((hfloor_m2_S29_32_15_16_corner11))

/-! ### Instance (piece = 11) -/

noncomputable def hfloor_m2_S15_16_31_32c1 : ℝ :=
  ((-1735437365227)) / (8530200000000)

noncomputable def hfloor_m2_S15_16_31_32c2 : ℝ :=
  1

noncomputable def hfloor_m2_S15_16_31_32c3 : ℝ :=
  0

noncomputable def hfloor_m2_S15_16_31_32c4 : ℝ :=
  0

theorem hfloor_m2_S15_16_31_32_bilinear (L _iv_dummy_HFloors : ℝ) :
    (8530200000000 * L - 1735437365227) / (8530200000000) - 0
      = hfloor_m2_S15_16_31_32c1  + hfloor_m2_S15_16_31_32c2  * L + hfloor_m2_S15_16_31_32c3  * _iv_dummy_HFloors
        + hfloor_m2_S15_16_31_32c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m2_S15_16_31_32c1, hfloor_m2_S15_16_31_32c2, hfloor_m2_S15_16_31_32c3, hfloor_m2_S15_16_31_32c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m2_S15_16_31_32_corner00  :
    0 ≤ hfloor_m2_S15_16_31_32c1 + hfloor_m2_S15_16_31_32c2 * ((103293) / (500000)) + hfloor_m2_S15_16_31_32c3 * (0)
        + hfloor_m2_S15_16_31_32c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m2_S15_16_31_32c1 + hfloor_m2_S15_16_31_32c2 * ((103293) / (500000)) + hfloor_m2_S15_16_31_32c3 * (0)
        + hfloor_m2_S15_16_31_32c4 * (((103293) / (500000)) * (0))
      = (26782531973)
        / (8530200000000) := by
    simp only [hfloor_m2_S15_16_31_32c1, hfloor_m2_S15_16_31_32c2, hfloor_m2_S15_16_31_32c3, hfloor_m2_S15_16_31_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S15_16_31_32_corner01  :
    0 ≤ hfloor_m2_S15_16_31_32c1 + hfloor_m2_S15_16_31_32c2 * ((103293) / (500000)) + hfloor_m2_S15_16_31_32c3 * (1)
        + hfloor_m2_S15_16_31_32c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m2_S15_16_31_32c1 + hfloor_m2_S15_16_31_32c2 * ((103293) / (500000)) + hfloor_m2_S15_16_31_32c3 * (1)
        + hfloor_m2_S15_16_31_32c4 * (((103293) / (500000)) * (1))
      = (26782531973)
        / (8530200000000) := by
    simp only [hfloor_m2_S15_16_31_32c1, hfloor_m2_S15_16_31_32c2, hfloor_m2_S15_16_31_32c3, hfloor_m2_S15_16_31_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S15_16_31_32_corner10  :
    0 ≤ hfloor_m2_S15_16_31_32c1 + hfloor_m2_S15_16_31_32c2 * ((206587) / (1000000)) + hfloor_m2_S15_16_31_32c3 * (0)
        + hfloor_m2_S15_16_31_32c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m2_S15_16_31_32c1 + hfloor_m2_S15_16_31_32c2 * ((206587) / (1000000)) + hfloor_m2_S15_16_31_32c3 * (0)
        + hfloor_m2_S15_16_31_32c4 * (((206587) / (1000000)) * (0))
      = (26791062173)
        / (8530200000000) := by
    simp only [hfloor_m2_S15_16_31_32c1, hfloor_m2_S15_16_31_32c2, hfloor_m2_S15_16_31_32c3, hfloor_m2_S15_16_31_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S15_16_31_32_corner11  :
    0 ≤ hfloor_m2_S15_16_31_32c1 + hfloor_m2_S15_16_31_32c2 * ((206587) / (1000000)) + hfloor_m2_S15_16_31_32c3 * (1)
        + hfloor_m2_S15_16_31_32c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m2_S15_16_31_32c1 + hfloor_m2_S15_16_31_32c2 * ((206587) / (1000000)) + hfloor_m2_S15_16_31_32c3 * (1)
        + hfloor_m2_S15_16_31_32c4 * (((206587) / (1000000)) * (1))
      = (26791062173)
        / (8530200000000) := by
    simp only [hfloor_m2_S15_16_31_32c1, hfloor_m2_S15_16_31_32c2, hfloor_m2_S15_16_31_32c3, hfloor_m2_S15_16_31_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S15_16_31_32_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (8530200000000 * L - 1735437365227) / (8530200000000) := by
  rw [← sub_nonneg, hfloor_m2_S15_16_31_32_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m2_S15_16_31_32_corner00)) ((hfloor_m2_S15_16_31_32_corner01)) ((hfloor_m2_S15_16_31_32_corner10)) ((hfloor_m2_S15_16_31_32_corner11))

/-! ### Instance (piece = 12) -/

noncomputable def hfloor_m2_S31_32_1_1c1 : ℝ :=
  ((-2650061752267)) / (12992100000000)

noncomputable def hfloor_m2_S31_32_1_1c2 : ℝ :=
  1

noncomputable def hfloor_m2_S31_32_1_1c3 : ℝ :=
  0

noncomputable def hfloor_m2_S31_32_1_1c4 : ℝ :=
  0

theorem hfloor_m2_S31_32_1_1_bilinear (L _iv_dummy_HFloors : ℝ) :
    (12992100000000 * L - 2650061752267) / (12992100000000) - 0
      = hfloor_m2_S31_32_1_1c1  + hfloor_m2_S31_32_1_1c2  * L + hfloor_m2_S31_32_1_1c3  * _iv_dummy_HFloors
        + hfloor_m2_S31_32_1_1c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m2_S31_32_1_1c1, hfloor_m2_S31_32_1_1c2, hfloor_m2_S31_32_1_1c3, hfloor_m2_S31_32_1_1c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m2_S31_32_1_1_corner00  :
    0 ≤ hfloor_m2_S31_32_1_1c1 + hfloor_m2_S31_32_1_1c2 * ((103293) / (500000)) + hfloor_m2_S31_32_1_1c3 * (0)
        + hfloor_m2_S31_32_1_1c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m2_S31_32_1_1c1 + hfloor_m2_S31_32_1_1c2 * ((103293) / (500000)) + hfloor_m2_S31_32_1_1c3 * (0)
        + hfloor_m2_S31_32_1_1c4 * (((103293) / (500000)) * (0))
      = (33924218333)
        / (12992100000000) := by
    simp only [hfloor_m2_S31_32_1_1c1, hfloor_m2_S31_32_1_1c2, hfloor_m2_S31_32_1_1c3, hfloor_m2_S31_32_1_1c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S31_32_1_1_corner01  :
    0 ≤ hfloor_m2_S31_32_1_1c1 + hfloor_m2_S31_32_1_1c2 * ((103293) / (500000)) + hfloor_m2_S31_32_1_1c3 * (1)
        + hfloor_m2_S31_32_1_1c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m2_S31_32_1_1c1 + hfloor_m2_S31_32_1_1c2 * ((103293) / (500000)) + hfloor_m2_S31_32_1_1c3 * (1)
        + hfloor_m2_S31_32_1_1c4 * (((103293) / (500000)) * (1))
      = (33924218333)
        / (12992100000000) := by
    simp only [hfloor_m2_S31_32_1_1c1, hfloor_m2_S31_32_1_1c2, hfloor_m2_S31_32_1_1c3, hfloor_m2_S31_32_1_1c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S31_32_1_1_corner10  :
    0 ≤ hfloor_m2_S31_32_1_1c1 + hfloor_m2_S31_32_1_1c2 * ((206587) / (1000000)) + hfloor_m2_S31_32_1_1c3 * (0)
        + hfloor_m2_S31_32_1_1c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m2_S31_32_1_1c1 + hfloor_m2_S31_32_1_1c2 * ((206587) / (1000000)) + hfloor_m2_S31_32_1_1c3 * (0)
        + hfloor_m2_S31_32_1_1c4 * (((206587) / (1000000)) * (0))
      = (33937210433)
        / (12992100000000) := by
    simp only [hfloor_m2_S31_32_1_1c1, hfloor_m2_S31_32_1_1c2, hfloor_m2_S31_32_1_1c3, hfloor_m2_S31_32_1_1c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S31_32_1_1_corner11  :
    0 ≤ hfloor_m2_S31_32_1_1c1 + hfloor_m2_S31_32_1_1c2 * ((206587) / (1000000)) + hfloor_m2_S31_32_1_1c3 * (1)
        + hfloor_m2_S31_32_1_1c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m2_S31_32_1_1c1 + hfloor_m2_S31_32_1_1c2 * ((206587) / (1000000)) + hfloor_m2_S31_32_1_1c3 * (1)
        + hfloor_m2_S31_32_1_1c4 * (((206587) / (1000000)) * (1))
      = (33937210433)
        / (12992100000000) := by
    simp only [hfloor_m2_S31_32_1_1c1, hfloor_m2_S31_32_1_1c2, hfloor_m2_S31_32_1_1c3, hfloor_m2_S31_32_1_1c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m2_S31_32_1_1_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (12992100000000 * L - 2650061752267) / (12992100000000) := by
  rw [← sub_nonneg, hfloor_m2_S31_32_1_1_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m2_S31_32_1_1_corner00)) ((hfloor_m2_S31_32_1_1_corner01)) ((hfloor_m2_S31_32_1_1_corner10)) ((hfloor_m2_S31_32_1_1_corner11))

/-! ### Instance (piece = 13) -/

noncomputable def hfloor_m3_S0_1_3_4c1 : ℝ :=
  ((-99933033)) / (500000000)

noncomputable def hfloor_m3_S0_1_3_4c2 : ℝ :=
  1

noncomputable def hfloor_m3_S0_1_3_4c3 : ℝ :=
  0

noncomputable def hfloor_m3_S0_1_3_4c4 : ℝ :=
  0

theorem hfloor_m3_S0_1_3_4_bilinear (L _iv_dummy_HFloors : ℝ) :
    (500000000 * L - 99933033) / (500000000) - 0
      = hfloor_m3_S0_1_3_4c1  + hfloor_m3_S0_1_3_4c2  * L + hfloor_m3_S0_1_3_4c3  * _iv_dummy_HFloors
        + hfloor_m3_S0_1_3_4c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m3_S0_1_3_4c1, hfloor_m3_S0_1_3_4c2, hfloor_m3_S0_1_3_4c3, hfloor_m3_S0_1_3_4c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m3_S0_1_3_4_corner00  :
    0 ≤ hfloor_m3_S0_1_3_4c1 + hfloor_m3_S0_1_3_4c2 * ((103293) / (500000)) + hfloor_m3_S0_1_3_4c3 * (0)
        + hfloor_m3_S0_1_3_4c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m3_S0_1_3_4c1 + hfloor_m3_S0_1_3_4c2 * ((103293) / (500000)) + hfloor_m3_S0_1_3_4c3 * (0)
        + hfloor_m3_S0_1_3_4c4 * (((103293) / (500000)) * (0))
      = (3359967)
        / (500000000) := by
    simp only [hfloor_m3_S0_1_3_4c1, hfloor_m3_S0_1_3_4c2, hfloor_m3_S0_1_3_4c3, hfloor_m3_S0_1_3_4c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m3_S0_1_3_4_corner01  :
    0 ≤ hfloor_m3_S0_1_3_4c1 + hfloor_m3_S0_1_3_4c2 * ((103293) / (500000)) + hfloor_m3_S0_1_3_4c3 * (1)
        + hfloor_m3_S0_1_3_4c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m3_S0_1_3_4c1 + hfloor_m3_S0_1_3_4c2 * ((103293) / (500000)) + hfloor_m3_S0_1_3_4c3 * (1)
        + hfloor_m3_S0_1_3_4c4 * (((103293) / (500000)) * (1))
      = (3359967)
        / (500000000) := by
    simp only [hfloor_m3_S0_1_3_4c1, hfloor_m3_S0_1_3_4c2, hfloor_m3_S0_1_3_4c3, hfloor_m3_S0_1_3_4c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m3_S0_1_3_4_corner10  :
    0 ≤ hfloor_m3_S0_1_3_4c1 + hfloor_m3_S0_1_3_4c2 * ((206587) / (1000000)) + hfloor_m3_S0_1_3_4c3 * (0)
        + hfloor_m3_S0_1_3_4c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m3_S0_1_3_4c1 + hfloor_m3_S0_1_3_4c2 * ((206587) / (1000000)) + hfloor_m3_S0_1_3_4c3 * (0)
        + hfloor_m3_S0_1_3_4c4 * (((206587) / (1000000)) * (0))
      = (3360467)
        / (500000000) := by
    simp only [hfloor_m3_S0_1_3_4c1, hfloor_m3_S0_1_3_4c2, hfloor_m3_S0_1_3_4c3, hfloor_m3_S0_1_3_4c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m3_S0_1_3_4_corner11  :
    0 ≤ hfloor_m3_S0_1_3_4c1 + hfloor_m3_S0_1_3_4c2 * ((206587) / (1000000)) + hfloor_m3_S0_1_3_4c3 * (1)
        + hfloor_m3_S0_1_3_4c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m3_S0_1_3_4c1 + hfloor_m3_S0_1_3_4c2 * ((206587) / (1000000)) + hfloor_m3_S0_1_3_4c3 * (1)
        + hfloor_m3_S0_1_3_4c4 * (((206587) / (1000000)) * (1))
      = (3360467)
        / (500000000) := by
    simp only [hfloor_m3_S0_1_3_4c1, hfloor_m3_S0_1_3_4c2, hfloor_m3_S0_1_3_4c3, hfloor_m3_S0_1_3_4c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m3_S0_1_3_4_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (500000000 * L - 99933033) / (500000000) := by
  rw [← sub_nonneg, hfloor_m3_S0_1_3_4_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m3_S0_1_3_4_corner00)) ((hfloor_m3_S0_1_3_4_corner01)) ((hfloor_m3_S0_1_3_4_corner10)) ((hfloor_m3_S0_1_3_4_corner11))

/-! ### Instance (piece = 14) -/

noncomputable def hfloor_m3_S3_4_27_32c1 : ℝ :=
  ((-7942047)) / (40000000)

noncomputable def hfloor_m3_S3_4_27_32c2 : ℝ :=
  1

noncomputable def hfloor_m3_S3_4_27_32c3 : ℝ :=
  0

noncomputable def hfloor_m3_S3_4_27_32c4 : ℝ :=
  0

theorem hfloor_m3_S3_4_27_32_bilinear (L _iv_dummy_HFloors : ℝ) :
    (40000000 * L - 7942047) / (40000000) - 0
      = hfloor_m3_S3_4_27_32c1  + hfloor_m3_S3_4_27_32c2  * L + hfloor_m3_S3_4_27_32c3  * _iv_dummy_HFloors
        + hfloor_m3_S3_4_27_32c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m3_S3_4_27_32c1, hfloor_m3_S3_4_27_32c2, hfloor_m3_S3_4_27_32c3, hfloor_m3_S3_4_27_32c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m3_S3_4_27_32_corner00  :
    0 ≤ hfloor_m3_S3_4_27_32c1 + hfloor_m3_S3_4_27_32c2 * ((103293) / (500000)) + hfloor_m3_S3_4_27_32c3 * (0)
        + hfloor_m3_S3_4_27_32c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m3_S3_4_27_32c1 + hfloor_m3_S3_4_27_32c2 * ((103293) / (500000)) + hfloor_m3_S3_4_27_32c3 * (0)
        + hfloor_m3_S3_4_27_32c4 * (((103293) / (500000)) * (0))
      = (321393)
        / (40000000) := by
    simp only [hfloor_m3_S3_4_27_32c1, hfloor_m3_S3_4_27_32c2, hfloor_m3_S3_4_27_32c3, hfloor_m3_S3_4_27_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m3_S3_4_27_32_corner01  :
    0 ≤ hfloor_m3_S3_4_27_32c1 + hfloor_m3_S3_4_27_32c2 * ((103293) / (500000)) + hfloor_m3_S3_4_27_32c3 * (1)
        + hfloor_m3_S3_4_27_32c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m3_S3_4_27_32c1 + hfloor_m3_S3_4_27_32c2 * ((103293) / (500000)) + hfloor_m3_S3_4_27_32c3 * (1)
        + hfloor_m3_S3_4_27_32c4 * (((103293) / (500000)) * (1))
      = (321393)
        / (40000000) := by
    simp only [hfloor_m3_S3_4_27_32c1, hfloor_m3_S3_4_27_32c2, hfloor_m3_S3_4_27_32c3, hfloor_m3_S3_4_27_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m3_S3_4_27_32_corner10  :
    0 ≤ hfloor_m3_S3_4_27_32c1 + hfloor_m3_S3_4_27_32c2 * ((206587) / (1000000)) + hfloor_m3_S3_4_27_32c3 * (0)
        + hfloor_m3_S3_4_27_32c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m3_S3_4_27_32c1 + hfloor_m3_S3_4_27_32c2 * ((206587) / (1000000)) + hfloor_m3_S3_4_27_32c3 * (0)
        + hfloor_m3_S3_4_27_32c4 * (((206587) / (1000000)) * (0))
      = (321433)
        / (40000000) := by
    simp only [hfloor_m3_S3_4_27_32c1, hfloor_m3_S3_4_27_32c2, hfloor_m3_S3_4_27_32c3, hfloor_m3_S3_4_27_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m3_S3_4_27_32_corner11  :
    0 ≤ hfloor_m3_S3_4_27_32c1 + hfloor_m3_S3_4_27_32c2 * ((206587) / (1000000)) + hfloor_m3_S3_4_27_32c3 * (1)
        + hfloor_m3_S3_4_27_32c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m3_S3_4_27_32c1 + hfloor_m3_S3_4_27_32c2 * ((206587) / (1000000)) + hfloor_m3_S3_4_27_32c3 * (1)
        + hfloor_m3_S3_4_27_32c4 * (((206587) / (1000000)) * (1))
      = (321433)
        / (40000000) := by
    simp only [hfloor_m3_S3_4_27_32c1, hfloor_m3_S3_4_27_32c2, hfloor_m3_S3_4_27_32c3, hfloor_m3_S3_4_27_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m3_S3_4_27_32_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (40000000 * L - 7942047) / (40000000) := by
  rw [← sub_nonneg, hfloor_m3_S3_4_27_32_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m3_S3_4_27_32_corner00)) ((hfloor_m3_S3_4_27_32_corner01)) ((hfloor_m3_S3_4_27_32_corner10)) ((hfloor_m3_S3_4_27_32_corner11))

/-! ### Instance (piece = 15) -/

noncomputable def hfloor_m3_S27_32_15_16c1 : ℝ :=
  ((-199892413)) / (1000000000)

noncomputable def hfloor_m3_S27_32_15_16c2 : ℝ :=
  1

noncomputable def hfloor_m3_S27_32_15_16c3 : ℝ :=
  0

noncomputable def hfloor_m3_S27_32_15_16c4 : ℝ :=
  0

theorem hfloor_m3_S27_32_15_16_bilinear (L _iv_dummy_HFloors : ℝ) :
    (1000000000 * L - 199892413) / (1000000000) - 0
      = hfloor_m3_S27_32_15_16c1  + hfloor_m3_S27_32_15_16c2  * L + hfloor_m3_S27_32_15_16c3  * _iv_dummy_HFloors
        + hfloor_m3_S27_32_15_16c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m3_S27_32_15_16c1, hfloor_m3_S27_32_15_16c2, hfloor_m3_S27_32_15_16c3, hfloor_m3_S27_32_15_16c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m3_S27_32_15_16_corner00  :
    0 ≤ hfloor_m3_S27_32_15_16c1 + hfloor_m3_S27_32_15_16c2 * ((103293) / (500000)) + hfloor_m3_S27_32_15_16c3 * (0)
        + hfloor_m3_S27_32_15_16c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m3_S27_32_15_16c1 + hfloor_m3_S27_32_15_16c2 * ((103293) / (500000)) + hfloor_m3_S27_32_15_16c3 * (0)
        + hfloor_m3_S27_32_15_16c4 * (((103293) / (500000)) * (0))
      = (6693587)
        / (1000000000) := by
    simp only [hfloor_m3_S27_32_15_16c1, hfloor_m3_S27_32_15_16c2, hfloor_m3_S27_32_15_16c3, hfloor_m3_S27_32_15_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m3_S27_32_15_16_corner01  :
    0 ≤ hfloor_m3_S27_32_15_16c1 + hfloor_m3_S27_32_15_16c2 * ((103293) / (500000)) + hfloor_m3_S27_32_15_16c3 * (1)
        + hfloor_m3_S27_32_15_16c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m3_S27_32_15_16c1 + hfloor_m3_S27_32_15_16c2 * ((103293) / (500000)) + hfloor_m3_S27_32_15_16c3 * (1)
        + hfloor_m3_S27_32_15_16c4 * (((103293) / (500000)) * (1))
      = (6693587)
        / (1000000000) := by
    simp only [hfloor_m3_S27_32_15_16c1, hfloor_m3_S27_32_15_16c2, hfloor_m3_S27_32_15_16c3, hfloor_m3_S27_32_15_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m3_S27_32_15_16_corner10  :
    0 ≤ hfloor_m3_S27_32_15_16c1 + hfloor_m3_S27_32_15_16c2 * ((206587) / (1000000)) + hfloor_m3_S27_32_15_16c3 * (0)
        + hfloor_m3_S27_32_15_16c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m3_S27_32_15_16c1 + hfloor_m3_S27_32_15_16c2 * ((206587) / (1000000)) + hfloor_m3_S27_32_15_16c3 * (0)
        + hfloor_m3_S27_32_15_16c4 * (((206587) / (1000000)) * (0))
      = (6694587)
        / (1000000000) := by
    simp only [hfloor_m3_S27_32_15_16c1, hfloor_m3_S27_32_15_16c2, hfloor_m3_S27_32_15_16c3, hfloor_m3_S27_32_15_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m3_S27_32_15_16_corner11  :
    0 ≤ hfloor_m3_S27_32_15_16c1 + hfloor_m3_S27_32_15_16c2 * ((206587) / (1000000)) + hfloor_m3_S27_32_15_16c3 * (1)
        + hfloor_m3_S27_32_15_16c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m3_S27_32_15_16c1 + hfloor_m3_S27_32_15_16c2 * ((206587) / (1000000)) + hfloor_m3_S27_32_15_16c3 * (1)
        + hfloor_m3_S27_32_15_16c4 * (((206587) / (1000000)) * (1))
      = (6694587)
        / (1000000000) := by
    simp only [hfloor_m3_S27_32_15_16c1, hfloor_m3_S27_32_15_16c2, hfloor_m3_S27_32_15_16c3, hfloor_m3_S27_32_15_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m3_S27_32_15_16_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (1000000000 * L - 199892413) / (1000000000) := by
  rw [← sub_nonneg, hfloor_m3_S27_32_15_16_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m3_S27_32_15_16_corner00)) ((hfloor_m3_S27_32_15_16_corner01)) ((hfloor_m3_S27_32_15_16_corner10)) ((hfloor_m3_S27_32_15_16_corner11))

/-! ### Instance (piece = 16) -/

noncomputable def hfloor_m3_S15_16_33_32c1 : ℝ :=
  ((-39615349)) / (200000000)

noncomputable def hfloor_m3_S15_16_33_32c2 : ℝ :=
  1

noncomputable def hfloor_m3_S15_16_33_32c3 : ℝ :=
  0

noncomputable def hfloor_m3_S15_16_33_32c4 : ℝ :=
  0

theorem hfloor_m3_S15_16_33_32_bilinear (L _iv_dummy_HFloors : ℝ) :
    (200000000 * L - 39615349) / (200000000) - 0
      = hfloor_m3_S15_16_33_32c1  + hfloor_m3_S15_16_33_32c2  * L + hfloor_m3_S15_16_33_32c3  * _iv_dummy_HFloors
        + hfloor_m3_S15_16_33_32c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m3_S15_16_33_32c1, hfloor_m3_S15_16_33_32c2, hfloor_m3_S15_16_33_32c3, hfloor_m3_S15_16_33_32c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m3_S15_16_33_32_corner00  :
    0 ≤ hfloor_m3_S15_16_33_32c1 + hfloor_m3_S15_16_33_32c2 * ((103293) / (500000)) + hfloor_m3_S15_16_33_32c3 * (0)
        + hfloor_m3_S15_16_33_32c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m3_S15_16_33_32c1 + hfloor_m3_S15_16_33_32c2 * ((103293) / (500000)) + hfloor_m3_S15_16_33_32c3 * (0)
        + hfloor_m3_S15_16_33_32c4 * (((103293) / (500000)) * (0))
      = (1701851)
        / (200000000) := by
    simp only [hfloor_m3_S15_16_33_32c1, hfloor_m3_S15_16_33_32c2, hfloor_m3_S15_16_33_32c3, hfloor_m3_S15_16_33_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m3_S15_16_33_32_corner01  :
    0 ≤ hfloor_m3_S15_16_33_32c1 + hfloor_m3_S15_16_33_32c2 * ((103293) / (500000)) + hfloor_m3_S15_16_33_32c3 * (1)
        + hfloor_m3_S15_16_33_32c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m3_S15_16_33_32c1 + hfloor_m3_S15_16_33_32c2 * ((103293) / (500000)) + hfloor_m3_S15_16_33_32c3 * (1)
        + hfloor_m3_S15_16_33_32c4 * (((103293) / (500000)) * (1))
      = (1701851)
        / (200000000) := by
    simp only [hfloor_m3_S15_16_33_32c1, hfloor_m3_S15_16_33_32c2, hfloor_m3_S15_16_33_32c3, hfloor_m3_S15_16_33_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m3_S15_16_33_32_corner10  :
    0 ≤ hfloor_m3_S15_16_33_32c1 + hfloor_m3_S15_16_33_32c2 * ((206587) / (1000000)) + hfloor_m3_S15_16_33_32c3 * (0)
        + hfloor_m3_S15_16_33_32c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m3_S15_16_33_32c1 + hfloor_m3_S15_16_33_32c2 * ((206587) / (1000000)) + hfloor_m3_S15_16_33_32c3 * (0)
        + hfloor_m3_S15_16_33_32c4 * (((206587) / (1000000)) * (0))
      = (1702051)
        / (200000000) := by
    simp only [hfloor_m3_S15_16_33_32c1, hfloor_m3_S15_16_33_32c2, hfloor_m3_S15_16_33_32c3, hfloor_m3_S15_16_33_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m3_S15_16_33_32_corner11  :
    0 ≤ hfloor_m3_S15_16_33_32c1 + hfloor_m3_S15_16_33_32c2 * ((206587) / (1000000)) + hfloor_m3_S15_16_33_32c3 * (1)
        + hfloor_m3_S15_16_33_32c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m3_S15_16_33_32c1 + hfloor_m3_S15_16_33_32c2 * ((206587) / (1000000)) + hfloor_m3_S15_16_33_32c3 * (1)
        + hfloor_m3_S15_16_33_32c4 * (((206587) / (1000000)) * (1))
      = (1702051)
        / (200000000) := by
    simp only [hfloor_m3_S15_16_33_32c1, hfloor_m3_S15_16_33_32c2, hfloor_m3_S15_16_33_32c3, hfloor_m3_S15_16_33_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m3_S15_16_33_32_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (200000000 * L - 39615349) / (200000000) := by
  rw [← sub_nonneg, hfloor_m3_S15_16_33_32_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m3_S15_16_33_32_corner00)) ((hfloor_m3_S15_16_33_32_corner01)) ((hfloor_m3_S15_16_33_32_corner10)) ((hfloor_m3_S15_16_33_32_corner11))

/-! ### Instance (piece = 17) -/

noncomputable def hfloor_m3_S33_32_9_8c1 : ℝ :=
  ((-195913807)) / (1000000000)

noncomputable def hfloor_m3_S33_32_9_8c2 : ℝ :=
  1

noncomputable def hfloor_m3_S33_32_9_8c3 : ℝ :=
  0

noncomputable def hfloor_m3_S33_32_9_8c4 : ℝ :=
  0

theorem hfloor_m3_S33_32_9_8_bilinear (L _iv_dummy_HFloors : ℝ) :
    (1000000000 * L - 195913807) / (1000000000) - 0
      = hfloor_m3_S33_32_9_8c1  + hfloor_m3_S33_32_9_8c2  * L + hfloor_m3_S33_32_9_8c3  * _iv_dummy_HFloors
        + hfloor_m3_S33_32_9_8c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m3_S33_32_9_8c1, hfloor_m3_S33_32_9_8c2, hfloor_m3_S33_32_9_8c3, hfloor_m3_S33_32_9_8c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m3_S33_32_9_8_corner00  :
    0 ≤ hfloor_m3_S33_32_9_8c1 + hfloor_m3_S33_32_9_8c2 * ((103293) / (500000)) + hfloor_m3_S33_32_9_8c3 * (0)
        + hfloor_m3_S33_32_9_8c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m3_S33_32_9_8c1 + hfloor_m3_S33_32_9_8c2 * ((103293) / (500000)) + hfloor_m3_S33_32_9_8c3 * (0)
        + hfloor_m3_S33_32_9_8c4 * (((103293) / (500000)) * (0))
      = (10672193)
        / (1000000000) := by
    simp only [hfloor_m3_S33_32_9_8c1, hfloor_m3_S33_32_9_8c2, hfloor_m3_S33_32_9_8c3, hfloor_m3_S33_32_9_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m3_S33_32_9_8_corner01  :
    0 ≤ hfloor_m3_S33_32_9_8c1 + hfloor_m3_S33_32_9_8c2 * ((103293) / (500000)) + hfloor_m3_S33_32_9_8c3 * (1)
        + hfloor_m3_S33_32_9_8c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m3_S33_32_9_8c1 + hfloor_m3_S33_32_9_8c2 * ((103293) / (500000)) + hfloor_m3_S33_32_9_8c3 * (1)
        + hfloor_m3_S33_32_9_8c4 * (((103293) / (500000)) * (1))
      = (10672193)
        / (1000000000) := by
    simp only [hfloor_m3_S33_32_9_8c1, hfloor_m3_S33_32_9_8c2, hfloor_m3_S33_32_9_8c3, hfloor_m3_S33_32_9_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m3_S33_32_9_8_corner10  :
    0 ≤ hfloor_m3_S33_32_9_8c1 + hfloor_m3_S33_32_9_8c2 * ((206587) / (1000000)) + hfloor_m3_S33_32_9_8c3 * (0)
        + hfloor_m3_S33_32_9_8c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m3_S33_32_9_8c1 + hfloor_m3_S33_32_9_8c2 * ((206587) / (1000000)) + hfloor_m3_S33_32_9_8c3 * (0)
        + hfloor_m3_S33_32_9_8c4 * (((206587) / (1000000)) * (0))
      = (10673193)
        / (1000000000) := by
    simp only [hfloor_m3_S33_32_9_8c1, hfloor_m3_S33_32_9_8c2, hfloor_m3_S33_32_9_8c3, hfloor_m3_S33_32_9_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m3_S33_32_9_8_corner11  :
    0 ≤ hfloor_m3_S33_32_9_8c1 + hfloor_m3_S33_32_9_8c2 * ((206587) / (1000000)) + hfloor_m3_S33_32_9_8c3 * (1)
        + hfloor_m3_S33_32_9_8c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m3_S33_32_9_8c1 + hfloor_m3_S33_32_9_8c2 * ((206587) / (1000000)) + hfloor_m3_S33_32_9_8c3 * (1)
        + hfloor_m3_S33_32_9_8c4 * (((206587) / (1000000)) * (1))
      = (10673193)
        / (1000000000) := by
    simp only [hfloor_m3_S33_32_9_8c1, hfloor_m3_S33_32_9_8c2, hfloor_m3_S33_32_9_8c3, hfloor_m3_S33_32_9_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m3_S33_32_9_8_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (1000000000 * L - 195913807) / (1000000000) := by
  rw [← sub_nonneg, hfloor_m3_S33_32_9_8_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m3_S33_32_9_8_corner00)) ((hfloor_m3_S33_32_9_8_corner01)) ((hfloor_m3_S33_32_9_8_corner10)) ((hfloor_m3_S33_32_9_8_corner11))

/-! ### Instance (piece = 18) -/

noncomputable def hfloor_m3_S9_8_39_32c1 : ℝ :=
  ((-377766)) / (1953125)

noncomputable def hfloor_m3_S9_8_39_32c2 : ℝ :=
  1

noncomputable def hfloor_m3_S9_8_39_32c3 : ℝ :=
  0

noncomputable def hfloor_m3_S9_8_39_32c4 : ℝ :=
  0

theorem hfloor_m3_S9_8_39_32_bilinear (L _iv_dummy_HFloors : ℝ) :
    (1953125 * L - 377766) / (1953125) - 0
      = hfloor_m3_S9_8_39_32c1  + hfloor_m3_S9_8_39_32c2  * L + hfloor_m3_S9_8_39_32c3  * _iv_dummy_HFloors
        + hfloor_m3_S9_8_39_32c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m3_S9_8_39_32c1, hfloor_m3_S9_8_39_32c2, hfloor_m3_S9_8_39_32c3, hfloor_m3_S9_8_39_32c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m3_S9_8_39_32_corner00  :
    0 ≤ hfloor_m3_S9_8_39_32c1 + hfloor_m3_S9_8_39_32c2 * ((103293) / (500000)) + hfloor_m3_S9_8_39_32c3 * (0)
        + hfloor_m3_S9_8_39_32c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m3_S9_8_39_32c1 + hfloor_m3_S9_8_39_32c2 * ((103293) / (500000)) + hfloor_m3_S9_8_39_32c3 * (0)
        + hfloor_m3_S9_8_39_32c4 * (((103293) / (500000)) * (0))
      = (823113)
        / (62500000) := by
    simp only [hfloor_m3_S9_8_39_32c1, hfloor_m3_S9_8_39_32c2, hfloor_m3_S9_8_39_32c3, hfloor_m3_S9_8_39_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m3_S9_8_39_32_corner01  :
    0 ≤ hfloor_m3_S9_8_39_32c1 + hfloor_m3_S9_8_39_32c2 * ((103293) / (500000)) + hfloor_m3_S9_8_39_32c3 * (1)
        + hfloor_m3_S9_8_39_32c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m3_S9_8_39_32c1 + hfloor_m3_S9_8_39_32c2 * ((103293) / (500000)) + hfloor_m3_S9_8_39_32c3 * (1)
        + hfloor_m3_S9_8_39_32c4 * (((103293) / (500000)) * (1))
      = (823113)
        / (62500000) := by
    simp only [hfloor_m3_S9_8_39_32c1, hfloor_m3_S9_8_39_32c2, hfloor_m3_S9_8_39_32c3, hfloor_m3_S9_8_39_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m3_S9_8_39_32_corner10  :
    0 ≤ hfloor_m3_S9_8_39_32c1 + hfloor_m3_S9_8_39_32c2 * ((206587) / (1000000)) + hfloor_m3_S9_8_39_32c3 * (0)
        + hfloor_m3_S9_8_39_32c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m3_S9_8_39_32c1 + hfloor_m3_S9_8_39_32c2 * ((206587) / (1000000)) + hfloor_m3_S9_8_39_32c3 * (0)
        + hfloor_m3_S9_8_39_32c4 * (((206587) / (1000000)) * (0))
      = (1646351)
        / (125000000) := by
    simp only [hfloor_m3_S9_8_39_32c1, hfloor_m3_S9_8_39_32c2, hfloor_m3_S9_8_39_32c3, hfloor_m3_S9_8_39_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m3_S9_8_39_32_corner11  :
    0 ≤ hfloor_m3_S9_8_39_32c1 + hfloor_m3_S9_8_39_32c2 * ((206587) / (1000000)) + hfloor_m3_S9_8_39_32c3 * (1)
        + hfloor_m3_S9_8_39_32c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m3_S9_8_39_32c1 + hfloor_m3_S9_8_39_32c2 * ((206587) / (1000000)) + hfloor_m3_S9_8_39_32c3 * (1)
        + hfloor_m3_S9_8_39_32c4 * (((206587) / (1000000)) * (1))
      = (1646351)
        / (125000000) := by
    simp only [hfloor_m3_S9_8_39_32c1, hfloor_m3_S9_8_39_32c2, hfloor_m3_S9_8_39_32c3, hfloor_m3_S9_8_39_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m3_S9_8_39_32_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (1953125 * L - 377766) / (1953125) := by
  rw [← sub_nonneg, hfloor_m3_S9_8_39_32_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m3_S9_8_39_32_corner00)) ((hfloor_m3_S9_8_39_32_corner01)) ((hfloor_m3_S9_8_39_32_corner10)) ((hfloor_m3_S9_8_39_32_corner11))

/-! ### Instance (piece = 19) -/

noncomputable def hfloor_m3_S39_32_21_16c1 : ℝ :=
  ((-190595817)) / (1000000000)

noncomputable def hfloor_m3_S39_32_21_16c2 : ℝ :=
  1

noncomputable def hfloor_m3_S39_32_21_16c3 : ℝ :=
  0

noncomputable def hfloor_m3_S39_32_21_16c4 : ℝ :=
  0

theorem hfloor_m3_S39_32_21_16_bilinear (L _iv_dummy_HFloors : ℝ) :
    (1000000000 * L - 190595817) / (1000000000) - 0
      = hfloor_m3_S39_32_21_16c1  + hfloor_m3_S39_32_21_16c2  * L + hfloor_m3_S39_32_21_16c3  * _iv_dummy_HFloors
        + hfloor_m3_S39_32_21_16c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m3_S39_32_21_16c1, hfloor_m3_S39_32_21_16c2, hfloor_m3_S39_32_21_16c3, hfloor_m3_S39_32_21_16c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m3_S39_32_21_16_corner00  :
    0 ≤ hfloor_m3_S39_32_21_16c1 + hfloor_m3_S39_32_21_16c2 * ((103293) / (500000)) + hfloor_m3_S39_32_21_16c3 * (0)
        + hfloor_m3_S39_32_21_16c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m3_S39_32_21_16c1 + hfloor_m3_S39_32_21_16c2 * ((103293) / (500000)) + hfloor_m3_S39_32_21_16c3 * (0)
        + hfloor_m3_S39_32_21_16c4 * (((103293) / (500000)) * (0))
      = (15990183)
        / (1000000000) := by
    simp only [hfloor_m3_S39_32_21_16c1, hfloor_m3_S39_32_21_16c2, hfloor_m3_S39_32_21_16c3, hfloor_m3_S39_32_21_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m3_S39_32_21_16_corner01  :
    0 ≤ hfloor_m3_S39_32_21_16c1 + hfloor_m3_S39_32_21_16c2 * ((103293) / (500000)) + hfloor_m3_S39_32_21_16c3 * (1)
        + hfloor_m3_S39_32_21_16c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m3_S39_32_21_16c1 + hfloor_m3_S39_32_21_16c2 * ((103293) / (500000)) + hfloor_m3_S39_32_21_16c3 * (1)
        + hfloor_m3_S39_32_21_16c4 * (((103293) / (500000)) * (1))
      = (15990183)
        / (1000000000) := by
    simp only [hfloor_m3_S39_32_21_16c1, hfloor_m3_S39_32_21_16c2, hfloor_m3_S39_32_21_16c3, hfloor_m3_S39_32_21_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m3_S39_32_21_16_corner10  :
    0 ≤ hfloor_m3_S39_32_21_16c1 + hfloor_m3_S39_32_21_16c2 * ((206587) / (1000000)) + hfloor_m3_S39_32_21_16c3 * (0)
        + hfloor_m3_S39_32_21_16c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m3_S39_32_21_16c1 + hfloor_m3_S39_32_21_16c2 * ((206587) / (1000000)) + hfloor_m3_S39_32_21_16c3 * (0)
        + hfloor_m3_S39_32_21_16c4 * (((206587) / (1000000)) * (0))
      = (15991183)
        / (1000000000) := by
    simp only [hfloor_m3_S39_32_21_16c1, hfloor_m3_S39_32_21_16c2, hfloor_m3_S39_32_21_16c3, hfloor_m3_S39_32_21_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m3_S39_32_21_16_corner11  :
    0 ≤ hfloor_m3_S39_32_21_16c1 + hfloor_m3_S39_32_21_16c2 * ((206587) / (1000000)) + hfloor_m3_S39_32_21_16c3 * (1)
        + hfloor_m3_S39_32_21_16c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m3_S39_32_21_16c1 + hfloor_m3_S39_32_21_16c2 * ((206587) / (1000000)) + hfloor_m3_S39_32_21_16c3 * (1)
        + hfloor_m3_S39_32_21_16c4 * (((206587) / (1000000)) * (1))
      = (15991183)
        / (1000000000) := by
    simp only [hfloor_m3_S39_32_21_16c1, hfloor_m3_S39_32_21_16c2, hfloor_m3_S39_32_21_16c3, hfloor_m3_S39_32_21_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m3_S39_32_21_16_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (1000000000 * L - 190595817) / (1000000000) := by
  rw [← sub_nonneg, hfloor_m3_S39_32_21_16_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m3_S39_32_21_16_corner00)) ((hfloor_m3_S39_32_21_16_corner01)) ((hfloor_m3_S39_32_21_16_corner10)) ((hfloor_m3_S39_32_21_16_corner11))

/-! ### Instance (piece = 20) -/

noncomputable def hfloor_m3_S21_16_3_2c1 : ℝ :=
  ((-1637251)) / (8000000)

noncomputable def hfloor_m3_S21_16_3_2c2 : ℝ :=
  1

noncomputable def hfloor_m3_S21_16_3_2c3 : ℝ :=
  0

noncomputable def hfloor_m3_S21_16_3_2c4 : ℝ :=
  0

theorem hfloor_m3_S21_16_3_2_bilinear (L _iv_dummy_HFloors : ℝ) :
    (8000000 * L - 1637251) / (8000000) - 0
      = hfloor_m3_S21_16_3_2c1  + hfloor_m3_S21_16_3_2c2  * L + hfloor_m3_S21_16_3_2c3  * _iv_dummy_HFloors
        + hfloor_m3_S21_16_3_2c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m3_S21_16_3_2c1, hfloor_m3_S21_16_3_2c2, hfloor_m3_S21_16_3_2c3, hfloor_m3_S21_16_3_2c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m3_S21_16_3_2_corner00  :
    0 ≤ hfloor_m3_S21_16_3_2c1 + hfloor_m3_S21_16_3_2c2 * ((103293) / (500000)) + hfloor_m3_S21_16_3_2c3 * (0)
        + hfloor_m3_S21_16_3_2c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m3_S21_16_3_2c1 + hfloor_m3_S21_16_3_2c2 * ((103293) / (500000)) + hfloor_m3_S21_16_3_2c3 * (0)
        + hfloor_m3_S21_16_3_2c4 * (((103293) / (500000)) * (0))
      = (15437)
        / (8000000) := by
    simp only [hfloor_m3_S21_16_3_2c1, hfloor_m3_S21_16_3_2c2, hfloor_m3_S21_16_3_2c3, hfloor_m3_S21_16_3_2c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m3_S21_16_3_2_corner01  :
    0 ≤ hfloor_m3_S21_16_3_2c1 + hfloor_m3_S21_16_3_2c2 * ((103293) / (500000)) + hfloor_m3_S21_16_3_2c3 * (1)
        + hfloor_m3_S21_16_3_2c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m3_S21_16_3_2c1 + hfloor_m3_S21_16_3_2c2 * ((103293) / (500000)) + hfloor_m3_S21_16_3_2c3 * (1)
        + hfloor_m3_S21_16_3_2c4 * (((103293) / (500000)) * (1))
      = (15437)
        / (8000000) := by
    simp only [hfloor_m3_S21_16_3_2c1, hfloor_m3_S21_16_3_2c2, hfloor_m3_S21_16_3_2c3, hfloor_m3_S21_16_3_2c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m3_S21_16_3_2_corner10  :
    0 ≤ hfloor_m3_S21_16_3_2c1 + hfloor_m3_S21_16_3_2c2 * ((206587) / (1000000)) + hfloor_m3_S21_16_3_2c3 * (0)
        + hfloor_m3_S21_16_3_2c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m3_S21_16_3_2c1 + hfloor_m3_S21_16_3_2c2 * ((206587) / (1000000)) + hfloor_m3_S21_16_3_2c3 * (0)
        + hfloor_m3_S21_16_3_2c4 * (((206587) / (1000000)) * (0))
      = (3089)
        / (1600000) := by
    simp only [hfloor_m3_S21_16_3_2c1, hfloor_m3_S21_16_3_2c2, hfloor_m3_S21_16_3_2c3, hfloor_m3_S21_16_3_2c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m3_S21_16_3_2_corner11  :
    0 ≤ hfloor_m3_S21_16_3_2c1 + hfloor_m3_S21_16_3_2c2 * ((206587) / (1000000)) + hfloor_m3_S21_16_3_2c3 * (1)
        + hfloor_m3_S21_16_3_2c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m3_S21_16_3_2c1 + hfloor_m3_S21_16_3_2c2 * ((206587) / (1000000)) + hfloor_m3_S21_16_3_2c3 * (1)
        + hfloor_m3_S21_16_3_2c4 * (((206587) / (1000000)) * (1))
      = (3089)
        / (1600000) := by
    simp only [hfloor_m3_S21_16_3_2c1, hfloor_m3_S21_16_3_2c2, hfloor_m3_S21_16_3_2c3, hfloor_m3_S21_16_3_2c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m3_S21_16_3_2_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (8000000 * L - 1637251) / (8000000) := by
  rw [← sub_nonneg, hfloor_m3_S21_16_3_2_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m3_S21_16_3_2_corner00)) ((hfloor_m3_S21_16_3_2_corner01)) ((hfloor_m3_S21_16_3_2_corner10)) ((hfloor_m3_S21_16_3_2_corner11))

/-! ### Instance (piece = 21) -/

noncomputable def hfloor_m4_S0_1_1_1c1 : ℝ :=
  ((-12637456727)) / (61400000000)

noncomputable def hfloor_m4_S0_1_1_1c2 : ℝ :=
  1

noncomputable def hfloor_m4_S0_1_1_1c3 : ℝ :=
  0

noncomputable def hfloor_m4_S0_1_1_1c4 : ℝ :=
  0

theorem hfloor_m4_S0_1_1_1_bilinear (L _iv_dummy_HFloors : ℝ) :
    (61400000000 * L - 12637456727) / (61400000000) - 0
      = hfloor_m4_S0_1_1_1c1  + hfloor_m4_S0_1_1_1c2  * L + hfloor_m4_S0_1_1_1c3  * _iv_dummy_HFloors
        + hfloor_m4_S0_1_1_1c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m4_S0_1_1_1c1, hfloor_m4_S0_1_1_1c2, hfloor_m4_S0_1_1_1c3, hfloor_m4_S0_1_1_1c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m4_S0_1_1_1_corner00  :
    0 ≤ hfloor_m4_S0_1_1_1c1 + hfloor_m4_S0_1_1_1c2 * ((103293) / (500000)) + hfloor_m4_S0_1_1_1c3 * (0)
        + hfloor_m4_S0_1_1_1c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m4_S0_1_1_1c1 + hfloor_m4_S0_1_1_1c2 * ((103293) / (500000)) + hfloor_m4_S0_1_1_1c3 * (0)
        + hfloor_m4_S0_1_1_1c4 * (((103293) / (500000)) * (0))
      = (46923673)
        / (61400000000) := by
    simp only [hfloor_m4_S0_1_1_1c1, hfloor_m4_S0_1_1_1c2, hfloor_m4_S0_1_1_1c3, hfloor_m4_S0_1_1_1c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m4_S0_1_1_1_corner01  :
    0 ≤ hfloor_m4_S0_1_1_1c1 + hfloor_m4_S0_1_1_1c2 * ((103293) / (500000)) + hfloor_m4_S0_1_1_1c3 * (1)
        + hfloor_m4_S0_1_1_1c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m4_S0_1_1_1c1 + hfloor_m4_S0_1_1_1c2 * ((103293) / (500000)) + hfloor_m4_S0_1_1_1c3 * (1)
        + hfloor_m4_S0_1_1_1c4 * (((103293) / (500000)) * (1))
      = (46923673)
        / (61400000000) := by
    simp only [hfloor_m4_S0_1_1_1c1, hfloor_m4_S0_1_1_1c2, hfloor_m4_S0_1_1_1c3, hfloor_m4_S0_1_1_1c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m4_S0_1_1_1_corner10  :
    0 ≤ hfloor_m4_S0_1_1_1c1 + hfloor_m4_S0_1_1_1c2 * ((206587) / (1000000)) + hfloor_m4_S0_1_1_1c3 * (0)
        + hfloor_m4_S0_1_1_1c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m4_S0_1_1_1c1 + hfloor_m4_S0_1_1_1c2 * ((206587) / (1000000)) + hfloor_m4_S0_1_1_1c3 * (0)
        + hfloor_m4_S0_1_1_1c4 * (((206587) / (1000000)) * (0))
      = (46985073)
        / (61400000000) := by
    simp only [hfloor_m4_S0_1_1_1c1, hfloor_m4_S0_1_1_1c2, hfloor_m4_S0_1_1_1c3, hfloor_m4_S0_1_1_1c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m4_S0_1_1_1_corner11  :
    0 ≤ hfloor_m4_S0_1_1_1c1 + hfloor_m4_S0_1_1_1c2 * ((206587) / (1000000)) + hfloor_m4_S0_1_1_1c3 * (1)
        + hfloor_m4_S0_1_1_1c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m4_S0_1_1_1c1 + hfloor_m4_S0_1_1_1c2 * ((206587) / (1000000)) + hfloor_m4_S0_1_1_1c3 * (1)
        + hfloor_m4_S0_1_1_1c4 * (((206587) / (1000000)) * (1))
      = (46985073)
        / (61400000000) := by
    simp only [hfloor_m4_S0_1_1_1c1, hfloor_m4_S0_1_1_1c2, hfloor_m4_S0_1_1_1c3, hfloor_m4_S0_1_1_1c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m4_S0_1_1_1_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (61400000000 * L - 12637456727) / (61400000000) := by
  rw [← sub_nonneg, hfloor_m4_S0_1_1_1_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m4_S0_1_1_1_corner00)) ((hfloor_m4_S0_1_1_1_corner01)) ((hfloor_m4_S0_1_1_1_corner10)) ((hfloor_m4_S0_1_1_1_corner11))

/-! ### Instance (piece = 22) -/

noncomputable def hfloor_m4_S1_1_9_8c1 : ℝ :=
  ((-25663025263)) / (125400000000)

noncomputable def hfloor_m4_S1_1_9_8c2 : ℝ :=
  1

noncomputable def hfloor_m4_S1_1_9_8c3 : ℝ :=
  0

noncomputable def hfloor_m4_S1_1_9_8c4 : ℝ :=
  0

theorem hfloor_m4_S1_1_9_8_bilinear (L _iv_dummy_HFloors : ℝ) :
    (125400000000 * L - 25663025263) / (125400000000) - 0
      = hfloor_m4_S1_1_9_8c1  + hfloor_m4_S1_1_9_8c2  * L + hfloor_m4_S1_1_9_8c3  * _iv_dummy_HFloors
        + hfloor_m4_S1_1_9_8c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m4_S1_1_9_8c1, hfloor_m4_S1_1_9_8c2, hfloor_m4_S1_1_9_8c3, hfloor_m4_S1_1_9_8c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m4_S1_1_9_8_corner00  :
    0 ≤ hfloor_m4_S1_1_9_8c1 + hfloor_m4_S1_1_9_8c2 * ((103293) / (500000)) + hfloor_m4_S1_1_9_8c3 * (0)
        + hfloor_m4_S1_1_9_8c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m4_S1_1_9_8c1 + hfloor_m4_S1_1_9_8c2 * ((103293) / (500000)) + hfloor_m4_S1_1_9_8c3 * (0)
        + hfloor_m4_S1_1_9_8c4 * (((103293) / (500000)) * (0))
      = (242859137)
        / (125400000000) := by
    simp only [hfloor_m4_S1_1_9_8c1, hfloor_m4_S1_1_9_8c2, hfloor_m4_S1_1_9_8c3, hfloor_m4_S1_1_9_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m4_S1_1_9_8_corner01  :
    0 ≤ hfloor_m4_S1_1_9_8c1 + hfloor_m4_S1_1_9_8c2 * ((103293) / (500000)) + hfloor_m4_S1_1_9_8c3 * (1)
        + hfloor_m4_S1_1_9_8c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m4_S1_1_9_8c1 + hfloor_m4_S1_1_9_8c2 * ((103293) / (500000)) + hfloor_m4_S1_1_9_8c3 * (1)
        + hfloor_m4_S1_1_9_8c4 * (((103293) / (500000)) * (1))
      = (242859137)
        / (125400000000) := by
    simp only [hfloor_m4_S1_1_9_8c1, hfloor_m4_S1_1_9_8c2, hfloor_m4_S1_1_9_8c3, hfloor_m4_S1_1_9_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m4_S1_1_9_8_corner10  :
    0 ≤ hfloor_m4_S1_1_9_8c1 + hfloor_m4_S1_1_9_8c2 * ((206587) / (1000000)) + hfloor_m4_S1_1_9_8c3 * (0)
        + hfloor_m4_S1_1_9_8c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m4_S1_1_9_8c1 + hfloor_m4_S1_1_9_8c2 * ((206587) / (1000000)) + hfloor_m4_S1_1_9_8c3 * (0)
        + hfloor_m4_S1_1_9_8c4 * (((206587) / (1000000)) * (0))
      = (242984537)
        / (125400000000) := by
    simp only [hfloor_m4_S1_1_9_8c1, hfloor_m4_S1_1_9_8c2, hfloor_m4_S1_1_9_8c3, hfloor_m4_S1_1_9_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m4_S1_1_9_8_corner11  :
    0 ≤ hfloor_m4_S1_1_9_8c1 + hfloor_m4_S1_1_9_8c2 * ((206587) / (1000000)) + hfloor_m4_S1_1_9_8c3 * (1)
        + hfloor_m4_S1_1_9_8c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m4_S1_1_9_8c1 + hfloor_m4_S1_1_9_8c2 * ((206587) / (1000000)) + hfloor_m4_S1_1_9_8c3 * (1)
        + hfloor_m4_S1_1_9_8c4 * (((206587) / (1000000)) * (1))
      = (242984537)
        / (125400000000) := by
    simp only [hfloor_m4_S1_1_9_8c1, hfloor_m4_S1_1_9_8c2, hfloor_m4_S1_1_9_8c3, hfloor_m4_S1_1_9_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m4_S1_1_9_8_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (125400000000 * L - 25663025263) / (125400000000) := by
  rw [← sub_nonneg, hfloor_m4_S1_1_9_8_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m4_S1_1_9_8_corner00)) ((hfloor_m4_S1_1_9_8_corner01)) ((hfloor_m4_S1_1_9_8_corner10)) ((hfloor_m4_S1_1_9_8_corner11))

/-! ### Instance (piece = 23) -/

noncomputable def hfloor_m4_S9_8_5_4c1 : ℝ :=
  ((-201080409)) / (1000000000)

noncomputable def hfloor_m4_S9_8_5_4c2 : ℝ :=
  1

noncomputable def hfloor_m4_S9_8_5_4c3 : ℝ :=
  0

noncomputable def hfloor_m4_S9_8_5_4c4 : ℝ :=
  0

theorem hfloor_m4_S9_8_5_4_bilinear (L _iv_dummy_HFloors : ℝ) :
    (1000000000 * L - 201080409) / (1000000000) - 0
      = hfloor_m4_S9_8_5_4c1  + hfloor_m4_S9_8_5_4c2  * L + hfloor_m4_S9_8_5_4c3  * _iv_dummy_HFloors
        + hfloor_m4_S9_8_5_4c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m4_S9_8_5_4c1, hfloor_m4_S9_8_5_4c2, hfloor_m4_S9_8_5_4c3, hfloor_m4_S9_8_5_4c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m4_S9_8_5_4_corner00  :
    0 ≤ hfloor_m4_S9_8_5_4c1 + hfloor_m4_S9_8_5_4c2 * ((103293) / (500000)) + hfloor_m4_S9_8_5_4c3 * (0)
        + hfloor_m4_S9_8_5_4c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m4_S9_8_5_4c1 + hfloor_m4_S9_8_5_4c2 * ((103293) / (500000)) + hfloor_m4_S9_8_5_4c3 * (0)
        + hfloor_m4_S9_8_5_4c4 * (((103293) / (500000)) * (0))
      = (5505591)
        / (1000000000) := by
    simp only [hfloor_m4_S9_8_5_4c1, hfloor_m4_S9_8_5_4c2, hfloor_m4_S9_8_5_4c3, hfloor_m4_S9_8_5_4c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m4_S9_8_5_4_corner01  :
    0 ≤ hfloor_m4_S9_8_5_4c1 + hfloor_m4_S9_8_5_4c2 * ((103293) / (500000)) + hfloor_m4_S9_8_5_4c3 * (1)
        + hfloor_m4_S9_8_5_4c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m4_S9_8_5_4c1 + hfloor_m4_S9_8_5_4c2 * ((103293) / (500000)) + hfloor_m4_S9_8_5_4c3 * (1)
        + hfloor_m4_S9_8_5_4c4 * (((103293) / (500000)) * (1))
      = (5505591)
        / (1000000000) := by
    simp only [hfloor_m4_S9_8_5_4c1, hfloor_m4_S9_8_5_4c2, hfloor_m4_S9_8_5_4c3, hfloor_m4_S9_8_5_4c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m4_S9_8_5_4_corner10  :
    0 ≤ hfloor_m4_S9_8_5_4c1 + hfloor_m4_S9_8_5_4c2 * ((206587) / (1000000)) + hfloor_m4_S9_8_5_4c3 * (0)
        + hfloor_m4_S9_8_5_4c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m4_S9_8_5_4c1 + hfloor_m4_S9_8_5_4c2 * ((206587) / (1000000)) + hfloor_m4_S9_8_5_4c3 * (0)
        + hfloor_m4_S9_8_5_4c4 * (((206587) / (1000000)) * (0))
      = (5506591)
        / (1000000000) := by
    simp only [hfloor_m4_S9_8_5_4c1, hfloor_m4_S9_8_5_4c2, hfloor_m4_S9_8_5_4c3, hfloor_m4_S9_8_5_4c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m4_S9_8_5_4_corner11  :
    0 ≤ hfloor_m4_S9_8_5_4c1 + hfloor_m4_S9_8_5_4c2 * ((206587) / (1000000)) + hfloor_m4_S9_8_5_4c3 * (1)
        + hfloor_m4_S9_8_5_4c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m4_S9_8_5_4c1 + hfloor_m4_S9_8_5_4c2 * ((206587) / (1000000)) + hfloor_m4_S9_8_5_4c3 * (1)
        + hfloor_m4_S9_8_5_4c4 * (((206587) / (1000000)) * (1))
      = (5506591)
        / (1000000000) := by
    simp only [hfloor_m4_S9_8_5_4c1, hfloor_m4_S9_8_5_4c2, hfloor_m4_S9_8_5_4c3, hfloor_m4_S9_8_5_4c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m4_S9_8_5_4_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (1000000000 * L - 201080409) / (1000000000) := by
  rw [← sub_nonneg, hfloor_m4_S9_8_5_4_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m4_S9_8_5_4_corner00)) ((hfloor_m4_S9_8_5_4_corner01)) ((hfloor_m4_S9_8_5_4_corner10)) ((hfloor_m4_S9_8_5_4_corner11))

/-! ### Instance (piece = 24) -/

noncomputable def hfloor_m4_S5_4_11_8c1 : ℝ :=
  ((-15760778711)) / (81500000000)

noncomputable def hfloor_m4_S5_4_11_8c2 : ℝ :=
  1

noncomputable def hfloor_m4_S5_4_11_8c3 : ℝ :=
  0

noncomputable def hfloor_m4_S5_4_11_8c4 : ℝ :=
  0

theorem hfloor_m4_S5_4_11_8_bilinear (L _iv_dummy_HFloors : ℝ) :
    (81500000000 * L - 15760778711) / (81500000000) - 0
      = hfloor_m4_S5_4_11_8c1  + hfloor_m4_S5_4_11_8c2  * L + hfloor_m4_S5_4_11_8c3  * _iv_dummy_HFloors
        + hfloor_m4_S5_4_11_8c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m4_S5_4_11_8c1, hfloor_m4_S5_4_11_8c2, hfloor_m4_S5_4_11_8c3, hfloor_m4_S5_4_11_8c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m4_S5_4_11_8_corner00  :
    0 ≤ hfloor_m4_S5_4_11_8c1 + hfloor_m4_S5_4_11_8c2 * ((103293) / (500000)) + hfloor_m4_S5_4_11_8c3 * (0)
        + hfloor_m4_S5_4_11_8c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m4_S5_4_11_8c1 + hfloor_m4_S5_4_11_8c2 * ((103293) / (500000)) + hfloor_m4_S5_4_11_8c3 * (0)
        + hfloor_m4_S5_4_11_8c4 * (((103293) / (500000)) * (0))
      = (1075980289)
        / (81500000000) := by
    simp only [hfloor_m4_S5_4_11_8c1, hfloor_m4_S5_4_11_8c2, hfloor_m4_S5_4_11_8c3, hfloor_m4_S5_4_11_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m4_S5_4_11_8_corner01  :
    0 ≤ hfloor_m4_S5_4_11_8c1 + hfloor_m4_S5_4_11_8c2 * ((103293) / (500000)) + hfloor_m4_S5_4_11_8c3 * (1)
        + hfloor_m4_S5_4_11_8c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m4_S5_4_11_8c1 + hfloor_m4_S5_4_11_8c2 * ((103293) / (500000)) + hfloor_m4_S5_4_11_8c3 * (1)
        + hfloor_m4_S5_4_11_8c4 * (((103293) / (500000)) * (1))
      = (1075980289)
        / (81500000000) := by
    simp only [hfloor_m4_S5_4_11_8c1, hfloor_m4_S5_4_11_8c2, hfloor_m4_S5_4_11_8c3, hfloor_m4_S5_4_11_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m4_S5_4_11_8_corner10  :
    0 ≤ hfloor_m4_S5_4_11_8c1 + hfloor_m4_S5_4_11_8c2 * ((206587) / (1000000)) + hfloor_m4_S5_4_11_8c3 * (0)
        + hfloor_m4_S5_4_11_8c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m4_S5_4_11_8c1 + hfloor_m4_S5_4_11_8c2 * ((206587) / (1000000)) + hfloor_m4_S5_4_11_8c3 * (0)
        + hfloor_m4_S5_4_11_8c4 * (((206587) / (1000000)) * (0))
      = (1076061789)
        / (81500000000) := by
    simp only [hfloor_m4_S5_4_11_8c1, hfloor_m4_S5_4_11_8c2, hfloor_m4_S5_4_11_8c3, hfloor_m4_S5_4_11_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m4_S5_4_11_8_corner11  :
    0 ≤ hfloor_m4_S5_4_11_8c1 + hfloor_m4_S5_4_11_8c2 * ((206587) / (1000000)) + hfloor_m4_S5_4_11_8c3 * (1)
        + hfloor_m4_S5_4_11_8c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m4_S5_4_11_8c1 + hfloor_m4_S5_4_11_8c2 * ((206587) / (1000000)) + hfloor_m4_S5_4_11_8c3 * (1)
        + hfloor_m4_S5_4_11_8c4 * (((206587) / (1000000)) * (1))
      = (1076061789)
        / (81500000000) := by
    simp only [hfloor_m4_S5_4_11_8c1, hfloor_m4_S5_4_11_8c2, hfloor_m4_S5_4_11_8c3, hfloor_m4_S5_4_11_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m4_S5_4_11_8_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (81500000000 * L - 15760778711) / (81500000000) := by
  rw [← sub_nonneg, hfloor_m4_S5_4_11_8_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m4_S5_4_11_8_corner00)) ((hfloor_m4_S5_4_11_8_corner01)) ((hfloor_m4_S5_4_11_8_corner10)) ((hfloor_m4_S5_4_11_8_corner11))

/-! ### Instance (piece = 25) -/

noncomputable def hfloor_m4_S11_8_3_2c1 : ℝ :=
  ((-24645103309)) / (133000000000)

noncomputable def hfloor_m4_S11_8_3_2c2 : ℝ :=
  1

noncomputable def hfloor_m4_S11_8_3_2c3 : ℝ :=
  0

noncomputable def hfloor_m4_S11_8_3_2c4 : ℝ :=
  0

theorem hfloor_m4_S11_8_3_2_bilinear (L _iv_dummy_HFloors : ℝ) :
    (133000000000 * L - 24645103309) / (133000000000) - 0
      = hfloor_m4_S11_8_3_2c1  + hfloor_m4_S11_8_3_2c2  * L + hfloor_m4_S11_8_3_2c3  * _iv_dummy_HFloors
        + hfloor_m4_S11_8_3_2c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m4_S11_8_3_2c1, hfloor_m4_S11_8_3_2c2, hfloor_m4_S11_8_3_2c3, hfloor_m4_S11_8_3_2c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m4_S11_8_3_2_corner00  :
    0 ≤ hfloor_m4_S11_8_3_2c1 + hfloor_m4_S11_8_3_2c2 * ((103293) / (500000)) + hfloor_m4_S11_8_3_2c3 * (0)
        + hfloor_m4_S11_8_3_2c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m4_S11_8_3_2c1 + hfloor_m4_S11_8_3_2c2 * ((103293) / (500000)) + hfloor_m4_S11_8_3_2c3 * (0)
        + hfloor_m4_S11_8_3_2c4 * (((103293) / (500000)) * (0))
      = (2830834691)
        / (133000000000) := by
    simp only [hfloor_m4_S11_8_3_2c1, hfloor_m4_S11_8_3_2c2, hfloor_m4_S11_8_3_2c3, hfloor_m4_S11_8_3_2c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m4_S11_8_3_2_corner01  :
    0 ≤ hfloor_m4_S11_8_3_2c1 + hfloor_m4_S11_8_3_2c2 * ((103293) / (500000)) + hfloor_m4_S11_8_3_2c3 * (1)
        + hfloor_m4_S11_8_3_2c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m4_S11_8_3_2c1 + hfloor_m4_S11_8_3_2c2 * ((103293) / (500000)) + hfloor_m4_S11_8_3_2c3 * (1)
        + hfloor_m4_S11_8_3_2c4 * (((103293) / (500000)) * (1))
      = (2830834691)
        / (133000000000) := by
    simp only [hfloor_m4_S11_8_3_2c1, hfloor_m4_S11_8_3_2c2, hfloor_m4_S11_8_3_2c3, hfloor_m4_S11_8_3_2c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m4_S11_8_3_2_corner10  :
    0 ≤ hfloor_m4_S11_8_3_2c1 + hfloor_m4_S11_8_3_2c2 * ((206587) / (1000000)) + hfloor_m4_S11_8_3_2c3 * (0)
        + hfloor_m4_S11_8_3_2c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m4_S11_8_3_2c1 + hfloor_m4_S11_8_3_2c2 * ((206587) / (1000000)) + hfloor_m4_S11_8_3_2c3 * (0)
        + hfloor_m4_S11_8_3_2c4 * (((206587) / (1000000)) * (0))
      = (2830967691)
        / (133000000000) := by
    simp only [hfloor_m4_S11_8_3_2c1, hfloor_m4_S11_8_3_2c2, hfloor_m4_S11_8_3_2c3, hfloor_m4_S11_8_3_2c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m4_S11_8_3_2_corner11  :
    0 ≤ hfloor_m4_S11_8_3_2c1 + hfloor_m4_S11_8_3_2c2 * ((206587) / (1000000)) + hfloor_m4_S11_8_3_2c3 * (1)
        + hfloor_m4_S11_8_3_2c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m4_S11_8_3_2c1 + hfloor_m4_S11_8_3_2c2 * ((206587) / (1000000)) + hfloor_m4_S11_8_3_2c3 * (1)
        + hfloor_m4_S11_8_3_2c4 * (((206587) / (1000000)) * (1))
      = (2830967691)
        / (133000000000) := by
    simp only [hfloor_m4_S11_8_3_2c1, hfloor_m4_S11_8_3_2c2, hfloor_m4_S11_8_3_2c3, hfloor_m4_S11_8_3_2c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m4_S11_8_3_2_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (133000000000 * L - 24645103309) / (133000000000) := by
  rw [← sub_nonneg, hfloor_m4_S11_8_3_2_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m4_S11_8_3_2_corner00)) ((hfloor_m4_S11_8_3_2_corner01)) ((hfloor_m4_S11_8_3_2_corner10)) ((hfloor_m4_S11_8_3_2_corner11))

/-! ### Instance (piece = 26) -/

noncomputable def hfloor_m4_S3_2_7_4c1 : ℝ :=
  ((-16889896337)) / (86375000000)

noncomputable def hfloor_m4_S3_2_7_4c2 : ℝ :=
  1

noncomputable def hfloor_m4_S3_2_7_4c3 : ℝ :=
  0

noncomputable def hfloor_m4_S3_2_7_4c4 : ℝ :=
  0

theorem hfloor_m4_S3_2_7_4_bilinear (L _iv_dummy_HFloors : ℝ) :
    (86375000000 * L - 16889896337) / (86375000000) - 0
      = hfloor_m4_S3_2_7_4c1  + hfloor_m4_S3_2_7_4c2  * L + hfloor_m4_S3_2_7_4c3  * _iv_dummy_HFloors
        + hfloor_m4_S3_2_7_4c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m4_S3_2_7_4c1, hfloor_m4_S3_2_7_4c2, hfloor_m4_S3_2_7_4c3, hfloor_m4_S3_2_7_4c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m4_S3_2_7_4_corner00  :
    0 ≤ hfloor_m4_S3_2_7_4c1 + hfloor_m4_S3_2_7_4c2 * ((103293) / (500000)) + hfloor_m4_S3_2_7_4c3 * (0)
        + hfloor_m4_S3_2_7_4c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m4_S3_2_7_4c1 + hfloor_m4_S3_2_7_4c2 * ((103293) / (500000)) + hfloor_m4_S3_2_7_4c3 * (0)
        + hfloor_m4_S3_2_7_4c4 * (((103293) / (500000)) * (0))
      = (953969413)
        / (86375000000) := by
    simp only [hfloor_m4_S3_2_7_4c1, hfloor_m4_S3_2_7_4c2, hfloor_m4_S3_2_7_4c3, hfloor_m4_S3_2_7_4c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m4_S3_2_7_4_corner01  :
    0 ≤ hfloor_m4_S3_2_7_4c1 + hfloor_m4_S3_2_7_4c2 * ((103293) / (500000)) + hfloor_m4_S3_2_7_4c3 * (1)
        + hfloor_m4_S3_2_7_4c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m4_S3_2_7_4c1 + hfloor_m4_S3_2_7_4c2 * ((103293) / (500000)) + hfloor_m4_S3_2_7_4c3 * (1)
        + hfloor_m4_S3_2_7_4c4 * (((103293) / (500000)) * (1))
      = (953969413)
        / (86375000000) := by
    simp only [hfloor_m4_S3_2_7_4c1, hfloor_m4_S3_2_7_4c2, hfloor_m4_S3_2_7_4c3, hfloor_m4_S3_2_7_4c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m4_S3_2_7_4_corner10  :
    0 ≤ hfloor_m4_S3_2_7_4c1 + hfloor_m4_S3_2_7_4c2 * ((206587) / (1000000)) + hfloor_m4_S3_2_7_4c3 * (0)
        + hfloor_m4_S3_2_7_4c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m4_S3_2_7_4c1 + hfloor_m4_S3_2_7_4c2 * ((206587) / (1000000)) + hfloor_m4_S3_2_7_4c3 * (0)
        + hfloor_m4_S3_2_7_4c4 * (((206587) / (1000000)) * (0))
      = (238513947)
        / (21593750000) := by
    simp only [hfloor_m4_S3_2_7_4c1, hfloor_m4_S3_2_7_4c2, hfloor_m4_S3_2_7_4c3, hfloor_m4_S3_2_7_4c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m4_S3_2_7_4_corner11  :
    0 ≤ hfloor_m4_S3_2_7_4c1 + hfloor_m4_S3_2_7_4c2 * ((206587) / (1000000)) + hfloor_m4_S3_2_7_4c3 * (1)
        + hfloor_m4_S3_2_7_4c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m4_S3_2_7_4c1 + hfloor_m4_S3_2_7_4c2 * ((206587) / (1000000)) + hfloor_m4_S3_2_7_4c3 * (1)
        + hfloor_m4_S3_2_7_4c4 * (((206587) / (1000000)) * (1))
      = (238513947)
        / (21593750000) := by
    simp only [hfloor_m4_S3_2_7_4c1, hfloor_m4_S3_2_7_4c2, hfloor_m4_S3_2_7_4c3, hfloor_m4_S3_2_7_4c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m4_S3_2_7_4_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (86375000000 * L - 16889896337) / (86375000000) := by
  rw [← sub_nonneg, hfloor_m4_S3_2_7_4_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m4_S3_2_7_4_corner00)) ((hfloor_m4_S3_2_7_4_corner01)) ((hfloor_m4_S3_2_7_4_corner10)) ((hfloor_m4_S3_2_7_4_corner11))

/-! ### Instance (piece = 27) -/

noncomputable def hfloor_m4_S7_4_2_1c1 : ℝ :=
  ((-31666839421)) / (179000000000)

noncomputable def hfloor_m4_S7_4_2_1c2 : ℝ :=
  1

noncomputable def hfloor_m4_S7_4_2_1c3 : ℝ :=
  0

noncomputable def hfloor_m4_S7_4_2_1c4 : ℝ :=
  0

theorem hfloor_m4_S7_4_2_1_bilinear (L _iv_dummy_HFloors : ℝ) :
    (179000000000 * L - 31666839421) / (179000000000) - 0
      = hfloor_m4_S7_4_2_1c1  + hfloor_m4_S7_4_2_1c2  * L + hfloor_m4_S7_4_2_1c3  * _iv_dummy_HFloors
        + hfloor_m4_S7_4_2_1c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m4_S7_4_2_1c1, hfloor_m4_S7_4_2_1c2, hfloor_m4_S7_4_2_1c3, hfloor_m4_S7_4_2_1c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m4_S7_4_2_1_corner00  :
    0 ≤ hfloor_m4_S7_4_2_1c1 + hfloor_m4_S7_4_2_1c2 * ((103293) / (500000)) + hfloor_m4_S7_4_2_1c3 * (0)
        + hfloor_m4_S7_4_2_1c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m4_S7_4_2_1c1 + hfloor_m4_S7_4_2_1c2 * ((103293) / (500000)) + hfloor_m4_S7_4_2_1c3 * (0)
        + hfloor_m4_S7_4_2_1c4 * (((103293) / (500000)) * (0))
      = (5312054579)
        / (179000000000) := by
    simp only [hfloor_m4_S7_4_2_1c1, hfloor_m4_S7_4_2_1c2, hfloor_m4_S7_4_2_1c3, hfloor_m4_S7_4_2_1c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m4_S7_4_2_1_corner01  :
    0 ≤ hfloor_m4_S7_4_2_1c1 + hfloor_m4_S7_4_2_1c2 * ((103293) / (500000)) + hfloor_m4_S7_4_2_1c3 * (1)
        + hfloor_m4_S7_4_2_1c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m4_S7_4_2_1c1 + hfloor_m4_S7_4_2_1c2 * ((103293) / (500000)) + hfloor_m4_S7_4_2_1c3 * (1)
        + hfloor_m4_S7_4_2_1c4 * (((103293) / (500000)) * (1))
      = (5312054579)
        / (179000000000) := by
    simp only [hfloor_m4_S7_4_2_1c1, hfloor_m4_S7_4_2_1c2, hfloor_m4_S7_4_2_1c3, hfloor_m4_S7_4_2_1c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m4_S7_4_2_1_corner10  :
    0 ≤ hfloor_m4_S7_4_2_1c1 + hfloor_m4_S7_4_2_1c2 * ((206587) / (1000000)) + hfloor_m4_S7_4_2_1c3 * (0)
        + hfloor_m4_S7_4_2_1c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m4_S7_4_2_1c1 + hfloor_m4_S7_4_2_1c2 * ((206587) / (1000000)) + hfloor_m4_S7_4_2_1c3 * (0)
        + hfloor_m4_S7_4_2_1c4 * (((206587) / (1000000)) * (0))
      = (5312233579)
        / (179000000000) := by
    simp only [hfloor_m4_S7_4_2_1c1, hfloor_m4_S7_4_2_1c2, hfloor_m4_S7_4_2_1c3, hfloor_m4_S7_4_2_1c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m4_S7_4_2_1_corner11  :
    0 ≤ hfloor_m4_S7_4_2_1c1 + hfloor_m4_S7_4_2_1c2 * ((206587) / (1000000)) + hfloor_m4_S7_4_2_1c3 * (1)
        + hfloor_m4_S7_4_2_1c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m4_S7_4_2_1c1 + hfloor_m4_S7_4_2_1c2 * ((206587) / (1000000)) + hfloor_m4_S7_4_2_1c3 * (1)
        + hfloor_m4_S7_4_2_1c4 * (((206587) / (1000000)) * (1))
      = (5312233579)
        / (179000000000) := by
    simp only [hfloor_m4_S7_4_2_1c1, hfloor_m4_S7_4_2_1c2, hfloor_m4_S7_4_2_1c3, hfloor_m4_S7_4_2_1c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m4_S7_4_2_1_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (179000000000 * L - 31666839421) / (179000000000) := by
  rw [← sub_nonneg, hfloor_m4_S7_4_2_1_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m4_S7_4_2_1_corner00)) ((hfloor_m4_S7_4_2_1_corner01)) ((hfloor_m4_S7_4_2_1_corner10)) ((hfloor_m4_S7_4_2_1_corner11))

/-! ### Instance (piece = 28) -/

noncomputable def hfloor_m5_S0_1_5_8c1 : ℝ :=
  ((-10389593903)) / (84750000000)

noncomputable def hfloor_m5_S0_1_5_8c2 : ℝ :=
  1

noncomputable def hfloor_m5_S0_1_5_8c3 : ℝ :=
  0

noncomputable def hfloor_m5_S0_1_5_8c4 : ℝ :=
  0

theorem hfloor_m5_S0_1_5_8_bilinear (L _iv_dummy_HFloors : ℝ) :
    (84750000000 * L - 10389593903) / (84750000000) - 0
      = hfloor_m5_S0_1_5_8c1  + hfloor_m5_S0_1_5_8c2  * L + hfloor_m5_S0_1_5_8c3  * _iv_dummy_HFloors
        + hfloor_m5_S0_1_5_8c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m5_S0_1_5_8c1, hfloor_m5_S0_1_5_8c2, hfloor_m5_S0_1_5_8c3, hfloor_m5_S0_1_5_8c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m5_S0_1_5_8_corner00  :
    0 ≤ hfloor_m5_S0_1_5_8c1 + hfloor_m5_S0_1_5_8c2 * ((103293) / (500000)) + hfloor_m5_S0_1_5_8c3 * (0)
        + hfloor_m5_S0_1_5_8c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m5_S0_1_5_8c1 + hfloor_m5_S0_1_5_8c2 * ((103293) / (500000)) + hfloor_m5_S0_1_5_8c3 * (0)
        + hfloor_m5_S0_1_5_8c4 * (((103293) / (500000)) * (0))
      = (7118569597)
        / (84750000000) := by
    simp only [hfloor_m5_S0_1_5_8c1, hfloor_m5_S0_1_5_8c2, hfloor_m5_S0_1_5_8c3, hfloor_m5_S0_1_5_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S0_1_5_8_corner01  :
    0 ≤ hfloor_m5_S0_1_5_8c1 + hfloor_m5_S0_1_5_8c2 * ((103293) / (500000)) + hfloor_m5_S0_1_5_8c3 * (1)
        + hfloor_m5_S0_1_5_8c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m5_S0_1_5_8c1 + hfloor_m5_S0_1_5_8c2 * ((103293) / (500000)) + hfloor_m5_S0_1_5_8c3 * (1)
        + hfloor_m5_S0_1_5_8c4 * (((103293) / (500000)) * (1))
      = (7118569597)
        / (84750000000) := by
    simp only [hfloor_m5_S0_1_5_8c1, hfloor_m5_S0_1_5_8c2, hfloor_m5_S0_1_5_8c3, hfloor_m5_S0_1_5_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S0_1_5_8_corner10  :
    0 ≤ hfloor_m5_S0_1_5_8c1 + hfloor_m5_S0_1_5_8c2 * ((206587) / (1000000)) + hfloor_m5_S0_1_5_8c3 * (0)
        + hfloor_m5_S0_1_5_8c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m5_S0_1_5_8c1 + hfloor_m5_S0_1_5_8c2 * ((206587) / (1000000)) + hfloor_m5_S0_1_5_8c3 * (0)
        + hfloor_m5_S0_1_5_8c4 * (((206587) / (1000000)) * (0))
      = (7118654347)
        / (84750000000) := by
    simp only [hfloor_m5_S0_1_5_8c1, hfloor_m5_S0_1_5_8c2, hfloor_m5_S0_1_5_8c3, hfloor_m5_S0_1_5_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S0_1_5_8_corner11  :
    0 ≤ hfloor_m5_S0_1_5_8c1 + hfloor_m5_S0_1_5_8c2 * ((206587) / (1000000)) + hfloor_m5_S0_1_5_8c3 * (1)
        + hfloor_m5_S0_1_5_8c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m5_S0_1_5_8c1 + hfloor_m5_S0_1_5_8c2 * ((206587) / (1000000)) + hfloor_m5_S0_1_5_8c3 * (1)
        + hfloor_m5_S0_1_5_8c4 * (((206587) / (1000000)) * (1))
      = (7118654347)
        / (84750000000) := by
    simp only [hfloor_m5_S0_1_5_8c1, hfloor_m5_S0_1_5_8c2, hfloor_m5_S0_1_5_8c3, hfloor_m5_S0_1_5_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S0_1_5_8_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (84750000000 * L - 10389593903) / (84750000000) := by
  rw [← sub_nonneg, hfloor_m5_S0_1_5_8_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m5_S0_1_5_8_corner00)) ((hfloor_m5_S0_1_5_8_corner01)) ((hfloor_m5_S0_1_5_8_corner10)) ((hfloor_m5_S0_1_5_8_corner11))

/-! ### Instance (piece = 29) -/

noncomputable def hfloor_m5_S5_8_15_16c1 : ℝ :=
  ((-168682011)) / (1000000000)

noncomputable def hfloor_m5_S5_8_15_16c2 : ℝ :=
  1

noncomputable def hfloor_m5_S5_8_15_16c3 : ℝ :=
  0

noncomputable def hfloor_m5_S5_8_15_16c4 : ℝ :=
  0

theorem hfloor_m5_S5_8_15_16_bilinear (L _iv_dummy_HFloors : ℝ) :
    (1000000000 * L - 168682011) / (1000000000) - 0
      = hfloor_m5_S5_8_15_16c1  + hfloor_m5_S5_8_15_16c2  * L + hfloor_m5_S5_8_15_16c3  * _iv_dummy_HFloors
        + hfloor_m5_S5_8_15_16c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m5_S5_8_15_16c1, hfloor_m5_S5_8_15_16c2, hfloor_m5_S5_8_15_16c3, hfloor_m5_S5_8_15_16c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m5_S5_8_15_16_corner00  :
    0 ≤ hfloor_m5_S5_8_15_16c1 + hfloor_m5_S5_8_15_16c2 * ((103293) / (500000)) + hfloor_m5_S5_8_15_16c3 * (0)
        + hfloor_m5_S5_8_15_16c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m5_S5_8_15_16c1 + hfloor_m5_S5_8_15_16c2 * ((103293) / (500000)) + hfloor_m5_S5_8_15_16c3 * (0)
        + hfloor_m5_S5_8_15_16c4 * (((103293) / (500000)) * (0))
      = (37903989)
        / (1000000000) := by
    simp only [hfloor_m5_S5_8_15_16c1, hfloor_m5_S5_8_15_16c2, hfloor_m5_S5_8_15_16c3, hfloor_m5_S5_8_15_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S5_8_15_16_corner01  :
    0 ≤ hfloor_m5_S5_8_15_16c1 + hfloor_m5_S5_8_15_16c2 * ((103293) / (500000)) + hfloor_m5_S5_8_15_16c3 * (1)
        + hfloor_m5_S5_8_15_16c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m5_S5_8_15_16c1 + hfloor_m5_S5_8_15_16c2 * ((103293) / (500000)) + hfloor_m5_S5_8_15_16c3 * (1)
        + hfloor_m5_S5_8_15_16c4 * (((103293) / (500000)) * (1))
      = (37903989)
        / (1000000000) := by
    simp only [hfloor_m5_S5_8_15_16c1, hfloor_m5_S5_8_15_16c2, hfloor_m5_S5_8_15_16c3, hfloor_m5_S5_8_15_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S5_8_15_16_corner10  :
    0 ≤ hfloor_m5_S5_8_15_16c1 + hfloor_m5_S5_8_15_16c2 * ((206587) / (1000000)) + hfloor_m5_S5_8_15_16c3 * (0)
        + hfloor_m5_S5_8_15_16c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m5_S5_8_15_16c1 + hfloor_m5_S5_8_15_16c2 * ((206587) / (1000000)) + hfloor_m5_S5_8_15_16c3 * (0)
        + hfloor_m5_S5_8_15_16c4 * (((206587) / (1000000)) * (0))
      = (37904989)
        / (1000000000) := by
    simp only [hfloor_m5_S5_8_15_16c1, hfloor_m5_S5_8_15_16c2, hfloor_m5_S5_8_15_16c3, hfloor_m5_S5_8_15_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S5_8_15_16_corner11  :
    0 ≤ hfloor_m5_S5_8_15_16c1 + hfloor_m5_S5_8_15_16c2 * ((206587) / (1000000)) + hfloor_m5_S5_8_15_16c3 * (1)
        + hfloor_m5_S5_8_15_16c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m5_S5_8_15_16c1 + hfloor_m5_S5_8_15_16c2 * ((206587) / (1000000)) + hfloor_m5_S5_8_15_16c3 * (1)
        + hfloor_m5_S5_8_15_16c4 * (((206587) / (1000000)) * (1))
      = (37904989)
        / (1000000000) := by
    simp only [hfloor_m5_S5_8_15_16c1, hfloor_m5_S5_8_15_16c2, hfloor_m5_S5_8_15_16c3, hfloor_m5_S5_8_15_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S5_8_15_16_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (1000000000 * L - 168682011) / (1000000000) := by
  rw [← sub_nonneg, hfloor_m5_S5_8_15_16_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m5_S5_8_15_16_corner00)) ((hfloor_m5_S5_8_15_16_corner01)) ((hfloor_m5_S5_8_15_16_corner10)) ((hfloor_m5_S5_8_15_16_corner11))

/-! ### Instance (piece = 30) -/

noncomputable def hfloor_m5_S15_16_35_32c1 : ℝ :=
  ((-34658295871)) / (181500000000)

noncomputable def hfloor_m5_S15_16_35_32c2 : ℝ :=
  1

noncomputable def hfloor_m5_S15_16_35_32c3 : ℝ :=
  0

noncomputable def hfloor_m5_S15_16_35_32c4 : ℝ :=
  0

theorem hfloor_m5_S15_16_35_32_bilinear (L _iv_dummy_HFloors : ℝ) :
    (181500000000 * L - 34658295871) / (181500000000) - 0
      = hfloor_m5_S15_16_35_32c1  + hfloor_m5_S15_16_35_32c2  * L + hfloor_m5_S15_16_35_32c3  * _iv_dummy_HFloors
        + hfloor_m5_S15_16_35_32c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m5_S15_16_35_32c1, hfloor_m5_S15_16_35_32c2, hfloor_m5_S15_16_35_32c3, hfloor_m5_S15_16_35_32c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m5_S15_16_35_32_corner00  :
    0 ≤ hfloor_m5_S15_16_35_32c1 + hfloor_m5_S15_16_35_32c2 * ((103293) / (500000)) + hfloor_m5_S15_16_35_32c3 * (0)
        + hfloor_m5_S15_16_35_32c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m5_S15_16_35_32c1 + hfloor_m5_S15_16_35_32c2 * ((103293) / (500000)) + hfloor_m5_S15_16_35_32c3 * (0)
        + hfloor_m5_S15_16_35_32c4 * (((103293) / (500000)) * (0))
      = (2837063129)
        / (181500000000) := by
    simp only [hfloor_m5_S15_16_35_32c1, hfloor_m5_S15_16_35_32c2, hfloor_m5_S15_16_35_32c3, hfloor_m5_S15_16_35_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S15_16_35_32_corner01  :
    0 ≤ hfloor_m5_S15_16_35_32c1 + hfloor_m5_S15_16_35_32c2 * ((103293) / (500000)) + hfloor_m5_S15_16_35_32c3 * (1)
        + hfloor_m5_S15_16_35_32c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m5_S15_16_35_32c1 + hfloor_m5_S15_16_35_32c2 * ((103293) / (500000)) + hfloor_m5_S15_16_35_32c3 * (1)
        + hfloor_m5_S15_16_35_32c4 * (((103293) / (500000)) * (1))
      = (2837063129)
        / (181500000000) := by
    simp only [hfloor_m5_S15_16_35_32c1, hfloor_m5_S15_16_35_32c2, hfloor_m5_S15_16_35_32c3, hfloor_m5_S15_16_35_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S15_16_35_32_corner10  :
    0 ≤ hfloor_m5_S15_16_35_32c1 + hfloor_m5_S15_16_35_32c2 * ((206587) / (1000000)) + hfloor_m5_S15_16_35_32c3 * (0)
        + hfloor_m5_S15_16_35_32c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m5_S15_16_35_32c1 + hfloor_m5_S15_16_35_32c2 * ((206587) / (1000000)) + hfloor_m5_S15_16_35_32c3 * (0)
        + hfloor_m5_S15_16_35_32c4 * (((206587) / (1000000)) * (0))
      = (2837244629)
        / (181500000000) := by
    simp only [hfloor_m5_S15_16_35_32c1, hfloor_m5_S15_16_35_32c2, hfloor_m5_S15_16_35_32c3, hfloor_m5_S15_16_35_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S15_16_35_32_corner11  :
    0 ≤ hfloor_m5_S15_16_35_32c1 + hfloor_m5_S15_16_35_32c2 * ((206587) / (1000000)) + hfloor_m5_S15_16_35_32c3 * (1)
        + hfloor_m5_S15_16_35_32c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m5_S15_16_35_32c1 + hfloor_m5_S15_16_35_32c2 * ((206587) / (1000000)) + hfloor_m5_S15_16_35_32c3 * (1)
        + hfloor_m5_S15_16_35_32c4 * (((206587) / (1000000)) * (1))
      = (2837244629)
        / (181500000000) := by
    simp only [hfloor_m5_S15_16_35_32c1, hfloor_m5_S15_16_35_32c2, hfloor_m5_S15_16_35_32c3, hfloor_m5_S15_16_35_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S15_16_35_32_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (181500000000 * L - 34658295871) / (181500000000) := by
  rw [← sub_nonneg, hfloor_m5_S15_16_35_32_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m5_S15_16_35_32_corner00)) ((hfloor_m5_S15_16_35_32_corner01)) ((hfloor_m5_S15_16_35_32_corner10)) ((hfloor_m5_S15_16_35_32_corner11))

/-! ### Instance (piece = 31) -/

noncomputable def hfloor_m5_S35_32_5_4c1 : ℝ :=
  ((-187894202563)) / (927000000000)

noncomputable def hfloor_m5_S35_32_5_4c2 : ℝ :=
  1

noncomputable def hfloor_m5_S35_32_5_4c3 : ℝ :=
  0

noncomputable def hfloor_m5_S35_32_5_4c4 : ℝ :=
  0

theorem hfloor_m5_S35_32_5_4_bilinear (L _iv_dummy_HFloors : ℝ) :
    (927000000000 * L - 187894202563) / (927000000000) - 0
      = hfloor_m5_S35_32_5_4c1  + hfloor_m5_S35_32_5_4c2  * L + hfloor_m5_S35_32_5_4c3  * _iv_dummy_HFloors
        + hfloor_m5_S35_32_5_4c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m5_S35_32_5_4c1, hfloor_m5_S35_32_5_4c2, hfloor_m5_S35_32_5_4c3, hfloor_m5_S35_32_5_4c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m5_S35_32_5_4_corner00  :
    0 ≤ hfloor_m5_S35_32_5_4c1 + hfloor_m5_S35_32_5_4c2 * ((103293) / (500000)) + hfloor_m5_S35_32_5_4c3 * (0)
        + hfloor_m5_S35_32_5_4c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m5_S35_32_5_4c1 + hfloor_m5_S35_32_5_4c2 * ((103293) / (500000)) + hfloor_m5_S35_32_5_4c3 * (0)
        + hfloor_m5_S35_32_5_4c4 * (((103293) / (500000)) * (0))
      = (3611019437)
        / (927000000000) := by
    simp only [hfloor_m5_S35_32_5_4c1, hfloor_m5_S35_32_5_4c2, hfloor_m5_S35_32_5_4c3, hfloor_m5_S35_32_5_4c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S35_32_5_4_corner01  :
    0 ≤ hfloor_m5_S35_32_5_4c1 + hfloor_m5_S35_32_5_4c2 * ((103293) / (500000)) + hfloor_m5_S35_32_5_4c3 * (1)
        + hfloor_m5_S35_32_5_4c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m5_S35_32_5_4c1 + hfloor_m5_S35_32_5_4c2 * ((103293) / (500000)) + hfloor_m5_S35_32_5_4c3 * (1)
        + hfloor_m5_S35_32_5_4c4 * (((103293) / (500000)) * (1))
      = (3611019437)
        / (927000000000) := by
    simp only [hfloor_m5_S35_32_5_4c1, hfloor_m5_S35_32_5_4c2, hfloor_m5_S35_32_5_4c3, hfloor_m5_S35_32_5_4c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S35_32_5_4_corner10  :
    0 ≤ hfloor_m5_S35_32_5_4c1 + hfloor_m5_S35_32_5_4c2 * ((206587) / (1000000)) + hfloor_m5_S35_32_5_4c3 * (0)
        + hfloor_m5_S35_32_5_4c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m5_S35_32_5_4c1 + hfloor_m5_S35_32_5_4c2 * ((206587) / (1000000)) + hfloor_m5_S35_32_5_4c3 * (0)
        + hfloor_m5_S35_32_5_4c4 * (((206587) / (1000000)) * (0))
      = (3611946437)
        / (927000000000) := by
    simp only [hfloor_m5_S35_32_5_4c1, hfloor_m5_S35_32_5_4c2, hfloor_m5_S35_32_5_4c3, hfloor_m5_S35_32_5_4c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S35_32_5_4_corner11  :
    0 ≤ hfloor_m5_S35_32_5_4c1 + hfloor_m5_S35_32_5_4c2 * ((206587) / (1000000)) + hfloor_m5_S35_32_5_4c3 * (1)
        + hfloor_m5_S35_32_5_4c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m5_S35_32_5_4c1 + hfloor_m5_S35_32_5_4c2 * ((206587) / (1000000)) + hfloor_m5_S35_32_5_4c3 * (1)
        + hfloor_m5_S35_32_5_4c4 * (((206587) / (1000000)) * (1))
      = (3611946437)
        / (927000000000) := by
    simp only [hfloor_m5_S35_32_5_4c1, hfloor_m5_S35_32_5_4c2, hfloor_m5_S35_32_5_4c3, hfloor_m5_S35_32_5_4c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S35_32_5_4_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (927000000000 * L - 187894202563) / (927000000000) := by
  rw [← sub_nonneg, hfloor_m5_S35_32_5_4_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m5_S35_32_5_4_corner00)) ((hfloor_m5_S35_32_5_4_corner01)) ((hfloor_m5_S35_32_5_4_corner10)) ((hfloor_m5_S35_32_5_4_corner11))

/-! ### Instance (piece = 32) -/

noncomputable def hfloor_m5_S5_4_85_64c1 : ℝ :=
  ((-588662683)) / (3000000000)

noncomputable def hfloor_m5_S5_4_85_64c2 : ℝ :=
  1

noncomputable def hfloor_m5_S5_4_85_64c3 : ℝ :=
  0

noncomputable def hfloor_m5_S5_4_85_64c4 : ℝ :=
  0

theorem hfloor_m5_S5_4_85_64_bilinear (L _iv_dummy_HFloors : ℝ) :
    (3000000000 * L - 588662683) / (3000000000) - 0
      = hfloor_m5_S5_4_85_64c1  + hfloor_m5_S5_4_85_64c2  * L + hfloor_m5_S5_4_85_64c3  * _iv_dummy_HFloors
        + hfloor_m5_S5_4_85_64c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m5_S5_4_85_64c1, hfloor_m5_S5_4_85_64c2, hfloor_m5_S5_4_85_64c3, hfloor_m5_S5_4_85_64c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m5_S5_4_85_64_corner00  :
    0 ≤ hfloor_m5_S5_4_85_64c1 + hfloor_m5_S5_4_85_64c2 * ((103293) / (500000)) + hfloor_m5_S5_4_85_64c3 * (0)
        + hfloor_m5_S5_4_85_64c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m5_S5_4_85_64c1 + hfloor_m5_S5_4_85_64c2 * ((103293) / (500000)) + hfloor_m5_S5_4_85_64c3 * (0)
        + hfloor_m5_S5_4_85_64c4 * (((103293) / (500000)) * (0))
      = (31095317)
        / (3000000000) := by
    simp only [hfloor_m5_S5_4_85_64c1, hfloor_m5_S5_4_85_64c2, hfloor_m5_S5_4_85_64c3, hfloor_m5_S5_4_85_64c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S5_4_85_64_corner01  :
    0 ≤ hfloor_m5_S5_4_85_64c1 + hfloor_m5_S5_4_85_64c2 * ((103293) / (500000)) + hfloor_m5_S5_4_85_64c3 * (1)
        + hfloor_m5_S5_4_85_64c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m5_S5_4_85_64c1 + hfloor_m5_S5_4_85_64c2 * ((103293) / (500000)) + hfloor_m5_S5_4_85_64c3 * (1)
        + hfloor_m5_S5_4_85_64c4 * (((103293) / (500000)) * (1))
      = (31095317)
        / (3000000000) := by
    simp only [hfloor_m5_S5_4_85_64c1, hfloor_m5_S5_4_85_64c2, hfloor_m5_S5_4_85_64c3, hfloor_m5_S5_4_85_64c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S5_4_85_64_corner10  :
    0 ≤ hfloor_m5_S5_4_85_64c1 + hfloor_m5_S5_4_85_64c2 * ((206587) / (1000000)) + hfloor_m5_S5_4_85_64c3 * (0)
        + hfloor_m5_S5_4_85_64c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m5_S5_4_85_64c1 + hfloor_m5_S5_4_85_64c2 * ((206587) / (1000000)) + hfloor_m5_S5_4_85_64c3 * (0)
        + hfloor_m5_S5_4_85_64c4 * (((206587) / (1000000)) * (0))
      = (31098317)
        / (3000000000) := by
    simp only [hfloor_m5_S5_4_85_64c1, hfloor_m5_S5_4_85_64c2, hfloor_m5_S5_4_85_64c3, hfloor_m5_S5_4_85_64c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S5_4_85_64_corner11  :
    0 ≤ hfloor_m5_S5_4_85_64c1 + hfloor_m5_S5_4_85_64c2 * ((206587) / (1000000)) + hfloor_m5_S5_4_85_64c3 * (1)
        + hfloor_m5_S5_4_85_64c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m5_S5_4_85_64c1 + hfloor_m5_S5_4_85_64c2 * ((206587) / (1000000)) + hfloor_m5_S5_4_85_64c3 * (1)
        + hfloor_m5_S5_4_85_64c4 * (((206587) / (1000000)) * (1))
      = (31098317)
        / (3000000000) := by
    simp only [hfloor_m5_S5_4_85_64c1, hfloor_m5_S5_4_85_64c2, hfloor_m5_S5_4_85_64c3, hfloor_m5_S5_4_85_64c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S5_4_85_64_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (3000000000 * L - 588662683) / (3000000000) := by
  rw [← sub_nonneg, hfloor_m5_S5_4_85_64_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m5_S5_4_85_64_corner00)) ((hfloor_m5_S5_4_85_64_corner01)) ((hfloor_m5_S5_4_85_64_corner10)) ((hfloor_m5_S5_4_85_64_corner11))

/-! ### Instance (piece = 33) -/

noncomputable def hfloor_m5_S85_64_45_32c1 : ℝ :=
  ((-194298341)) / (1000000000)

noncomputable def hfloor_m5_S85_64_45_32c2 : ℝ :=
  1

noncomputable def hfloor_m5_S85_64_45_32c3 : ℝ :=
  0

noncomputable def hfloor_m5_S85_64_45_32c4 : ℝ :=
  0

theorem hfloor_m5_S85_64_45_32_bilinear (L _iv_dummy_HFloors : ℝ) :
    (1000000000 * L - 194298341) / (1000000000) - 0
      = hfloor_m5_S85_64_45_32c1  + hfloor_m5_S85_64_45_32c2  * L + hfloor_m5_S85_64_45_32c3  * _iv_dummy_HFloors
        + hfloor_m5_S85_64_45_32c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m5_S85_64_45_32c1, hfloor_m5_S85_64_45_32c2, hfloor_m5_S85_64_45_32c3, hfloor_m5_S85_64_45_32c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m5_S85_64_45_32_corner00  :
    0 ≤ hfloor_m5_S85_64_45_32c1 + hfloor_m5_S85_64_45_32c2 * ((103293) / (500000)) + hfloor_m5_S85_64_45_32c3 * (0)
        + hfloor_m5_S85_64_45_32c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m5_S85_64_45_32c1 + hfloor_m5_S85_64_45_32c2 * ((103293) / (500000)) + hfloor_m5_S85_64_45_32c3 * (0)
        + hfloor_m5_S85_64_45_32c4 * (((103293) / (500000)) * (0))
      = (12287659)
        / (1000000000) := by
    simp only [hfloor_m5_S85_64_45_32c1, hfloor_m5_S85_64_45_32c2, hfloor_m5_S85_64_45_32c3, hfloor_m5_S85_64_45_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S85_64_45_32_corner01  :
    0 ≤ hfloor_m5_S85_64_45_32c1 + hfloor_m5_S85_64_45_32c2 * ((103293) / (500000)) + hfloor_m5_S85_64_45_32c3 * (1)
        + hfloor_m5_S85_64_45_32c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m5_S85_64_45_32c1 + hfloor_m5_S85_64_45_32c2 * ((103293) / (500000)) + hfloor_m5_S85_64_45_32c3 * (1)
        + hfloor_m5_S85_64_45_32c4 * (((103293) / (500000)) * (1))
      = (12287659)
        / (1000000000) := by
    simp only [hfloor_m5_S85_64_45_32c1, hfloor_m5_S85_64_45_32c2, hfloor_m5_S85_64_45_32c3, hfloor_m5_S85_64_45_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S85_64_45_32_corner10  :
    0 ≤ hfloor_m5_S85_64_45_32c1 + hfloor_m5_S85_64_45_32c2 * ((206587) / (1000000)) + hfloor_m5_S85_64_45_32c3 * (0)
        + hfloor_m5_S85_64_45_32c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m5_S85_64_45_32c1 + hfloor_m5_S85_64_45_32c2 * ((206587) / (1000000)) + hfloor_m5_S85_64_45_32c3 * (0)
        + hfloor_m5_S85_64_45_32c4 * (((206587) / (1000000)) * (0))
      = (12288659)
        / (1000000000) := by
    simp only [hfloor_m5_S85_64_45_32c1, hfloor_m5_S85_64_45_32c2, hfloor_m5_S85_64_45_32c3, hfloor_m5_S85_64_45_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S85_64_45_32_corner11  :
    0 ≤ hfloor_m5_S85_64_45_32c1 + hfloor_m5_S85_64_45_32c2 * ((206587) / (1000000)) + hfloor_m5_S85_64_45_32c3 * (1)
        + hfloor_m5_S85_64_45_32c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m5_S85_64_45_32c1 + hfloor_m5_S85_64_45_32c2 * ((206587) / (1000000)) + hfloor_m5_S85_64_45_32c3 * (1)
        + hfloor_m5_S85_64_45_32c4 * (((206587) / (1000000)) * (1))
      = (12288659)
        / (1000000000) := by
    simp only [hfloor_m5_S85_64_45_32c1, hfloor_m5_S85_64_45_32c2, hfloor_m5_S85_64_45_32c3, hfloor_m5_S85_64_45_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S85_64_45_32_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (1000000000 * L - 194298341) / (1000000000) := by
  rw [← sub_nonneg, hfloor_m5_S85_64_45_32_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m5_S85_64_45_32_corner00)) ((hfloor_m5_S85_64_45_32_corner01)) ((hfloor_m5_S85_64_45_32_corner10)) ((hfloor_m5_S85_64_45_32_corner11))

/-! ### Instance (piece = 34) -/

noncomputable def hfloor_m5_S45_32_25_16c1 : ℝ :=
  ((-76621572281)) / (387000000000)

noncomputable def hfloor_m5_S45_32_25_16c2 : ℝ :=
  1

noncomputable def hfloor_m5_S45_32_25_16c3 : ℝ :=
  0

noncomputable def hfloor_m5_S45_32_25_16c4 : ℝ :=
  0

theorem hfloor_m5_S45_32_25_16_bilinear (L _iv_dummy_HFloors : ℝ) :
    (387000000000 * L - 76621572281) / (387000000000) - 0
      = hfloor_m5_S45_32_25_16c1  + hfloor_m5_S45_32_25_16c2  * L + hfloor_m5_S45_32_25_16c3  * _iv_dummy_HFloors
        + hfloor_m5_S45_32_25_16c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m5_S45_32_25_16c1, hfloor_m5_S45_32_25_16c2, hfloor_m5_S45_32_25_16c3, hfloor_m5_S45_32_25_16c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m5_S45_32_25_16_corner00  :
    0 ≤ hfloor_m5_S45_32_25_16c1 + hfloor_m5_S45_32_25_16c2 * ((103293) / (500000)) + hfloor_m5_S45_32_25_16c3 * (0)
        + hfloor_m5_S45_32_25_16c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m5_S45_32_25_16c1 + hfloor_m5_S45_32_25_16c2 * ((103293) / (500000)) + hfloor_m5_S45_32_25_16c3 * (0)
        + hfloor_m5_S45_32_25_16c4 * (((103293) / (500000)) * (0))
      = (3327209719)
        / (387000000000) := by
    simp only [hfloor_m5_S45_32_25_16c1, hfloor_m5_S45_32_25_16c2, hfloor_m5_S45_32_25_16c3, hfloor_m5_S45_32_25_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S45_32_25_16_corner01  :
    0 ≤ hfloor_m5_S45_32_25_16c1 + hfloor_m5_S45_32_25_16c2 * ((103293) / (500000)) + hfloor_m5_S45_32_25_16c3 * (1)
        + hfloor_m5_S45_32_25_16c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m5_S45_32_25_16c1 + hfloor_m5_S45_32_25_16c2 * ((103293) / (500000)) + hfloor_m5_S45_32_25_16c3 * (1)
        + hfloor_m5_S45_32_25_16c4 * (((103293) / (500000)) * (1))
      = (3327209719)
        / (387000000000) := by
    simp only [hfloor_m5_S45_32_25_16c1, hfloor_m5_S45_32_25_16c2, hfloor_m5_S45_32_25_16c3, hfloor_m5_S45_32_25_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S45_32_25_16_corner10  :
    0 ≤ hfloor_m5_S45_32_25_16c1 + hfloor_m5_S45_32_25_16c2 * ((206587) / (1000000)) + hfloor_m5_S45_32_25_16c3 * (0)
        + hfloor_m5_S45_32_25_16c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m5_S45_32_25_16c1 + hfloor_m5_S45_32_25_16c2 * ((206587) / (1000000)) + hfloor_m5_S45_32_25_16c3 * (0)
        + hfloor_m5_S45_32_25_16c4 * (((206587) / (1000000)) * (0))
      = (3327596719)
        / (387000000000) := by
    simp only [hfloor_m5_S45_32_25_16c1, hfloor_m5_S45_32_25_16c2, hfloor_m5_S45_32_25_16c3, hfloor_m5_S45_32_25_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S45_32_25_16_corner11  :
    0 ≤ hfloor_m5_S45_32_25_16c1 + hfloor_m5_S45_32_25_16c2 * ((206587) / (1000000)) + hfloor_m5_S45_32_25_16c3 * (1)
        + hfloor_m5_S45_32_25_16c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m5_S45_32_25_16c1 + hfloor_m5_S45_32_25_16c2 * ((206587) / (1000000)) + hfloor_m5_S45_32_25_16c3 * (1)
        + hfloor_m5_S45_32_25_16c4 * (((206587) / (1000000)) * (1))
      = (3327596719)
        / (387000000000) := by
    simp only [hfloor_m5_S45_32_25_16c1, hfloor_m5_S45_32_25_16c2, hfloor_m5_S45_32_25_16c3, hfloor_m5_S45_32_25_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S45_32_25_16_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (387000000000 * L - 76621572281) / (387000000000) := by
  rw [← sub_nonneg, hfloor_m5_S45_32_25_16_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m5_S45_32_25_16_corner00)) ((hfloor_m5_S45_32_25_16_corner01)) ((hfloor_m5_S45_32_25_16_corner10)) ((hfloor_m5_S45_32_25_16_corner11))

/-! ### Instance (piece = 35) -/

noncomputable def hfloor_m5_S25_16_15_8c1 : ℝ :=
  ((-204104787)) / (1000000000)

noncomputable def hfloor_m5_S25_16_15_8c2 : ℝ :=
  1

noncomputable def hfloor_m5_S25_16_15_8c3 : ℝ :=
  0

noncomputable def hfloor_m5_S25_16_15_8c4 : ℝ :=
  0

theorem hfloor_m5_S25_16_15_8_bilinear (L _iv_dummy_HFloors : ℝ) :
    (1000000000 * L - 204104787) / (1000000000) - 0
      = hfloor_m5_S25_16_15_8c1  + hfloor_m5_S25_16_15_8c2  * L + hfloor_m5_S25_16_15_8c3  * _iv_dummy_HFloors
        + hfloor_m5_S25_16_15_8c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m5_S25_16_15_8c1, hfloor_m5_S25_16_15_8c2, hfloor_m5_S25_16_15_8c3, hfloor_m5_S25_16_15_8c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m5_S25_16_15_8_corner00  :
    0 ≤ hfloor_m5_S25_16_15_8c1 + hfloor_m5_S25_16_15_8c2 * ((103293) / (500000)) + hfloor_m5_S25_16_15_8c3 * (0)
        + hfloor_m5_S25_16_15_8c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m5_S25_16_15_8c1 + hfloor_m5_S25_16_15_8c2 * ((103293) / (500000)) + hfloor_m5_S25_16_15_8c3 * (0)
        + hfloor_m5_S25_16_15_8c4 * (((103293) / (500000)) * (0))
      = (2481213)
        / (1000000000) := by
    simp only [hfloor_m5_S25_16_15_8c1, hfloor_m5_S25_16_15_8c2, hfloor_m5_S25_16_15_8c3, hfloor_m5_S25_16_15_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S25_16_15_8_corner01  :
    0 ≤ hfloor_m5_S25_16_15_8c1 + hfloor_m5_S25_16_15_8c2 * ((103293) / (500000)) + hfloor_m5_S25_16_15_8c3 * (1)
        + hfloor_m5_S25_16_15_8c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m5_S25_16_15_8c1 + hfloor_m5_S25_16_15_8c2 * ((103293) / (500000)) + hfloor_m5_S25_16_15_8c3 * (1)
        + hfloor_m5_S25_16_15_8c4 * (((103293) / (500000)) * (1))
      = (2481213)
        / (1000000000) := by
    simp only [hfloor_m5_S25_16_15_8c1, hfloor_m5_S25_16_15_8c2, hfloor_m5_S25_16_15_8c3, hfloor_m5_S25_16_15_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S25_16_15_8_corner10  :
    0 ≤ hfloor_m5_S25_16_15_8c1 + hfloor_m5_S25_16_15_8c2 * ((206587) / (1000000)) + hfloor_m5_S25_16_15_8c3 * (0)
        + hfloor_m5_S25_16_15_8c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m5_S25_16_15_8c1 + hfloor_m5_S25_16_15_8c2 * ((206587) / (1000000)) + hfloor_m5_S25_16_15_8c3 * (0)
        + hfloor_m5_S25_16_15_8c4 * (((206587) / (1000000)) * (0))
      = (2482213)
        / (1000000000) := by
    simp only [hfloor_m5_S25_16_15_8c1, hfloor_m5_S25_16_15_8c2, hfloor_m5_S25_16_15_8c3, hfloor_m5_S25_16_15_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S25_16_15_8_corner11  :
    0 ≤ hfloor_m5_S25_16_15_8c1 + hfloor_m5_S25_16_15_8c2 * ((206587) / (1000000)) + hfloor_m5_S25_16_15_8c3 * (1)
        + hfloor_m5_S25_16_15_8c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m5_S25_16_15_8c1 + hfloor_m5_S25_16_15_8c2 * ((206587) / (1000000)) + hfloor_m5_S25_16_15_8c3 * (1)
        + hfloor_m5_S25_16_15_8c4 * (((206587) / (1000000)) * (1))
      = (2482213)
        / (1000000000) := by
    simp only [hfloor_m5_S25_16_15_8c1, hfloor_m5_S25_16_15_8c2, hfloor_m5_S25_16_15_8c3, hfloor_m5_S25_16_15_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S25_16_15_8_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (1000000000 * L - 204104787) / (1000000000) := by
  rw [← sub_nonneg, hfloor_m5_S25_16_15_8_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m5_S25_16_15_8_corner00)) ((hfloor_m5_S25_16_15_8_corner01)) ((hfloor_m5_S25_16_15_8_corner10)) ((hfloor_m5_S25_16_15_8_corner11))

/-! ### Instance (piece = 36) -/

noncomputable def hfloor_m5_S15_8_35_16c1 : ℝ :=
  ((-182461379803)) / (1047000000000)

noncomputable def hfloor_m5_S15_8_35_16c2 : ℝ :=
  1

noncomputable def hfloor_m5_S15_8_35_16c3 : ℝ :=
  0

noncomputable def hfloor_m5_S15_8_35_16c4 : ℝ :=
  0

theorem hfloor_m5_S15_8_35_16_bilinear (L _iv_dummy_HFloors : ℝ) :
    (1047000000000 * L - 182461379803) / (1047000000000) - 0
      = hfloor_m5_S15_8_35_16c1  + hfloor_m5_S15_8_35_16c2  * L + hfloor_m5_S15_8_35_16c3  * _iv_dummy_HFloors
        + hfloor_m5_S15_8_35_16c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m5_S15_8_35_16c1, hfloor_m5_S15_8_35_16c2, hfloor_m5_S15_8_35_16c3, hfloor_m5_S15_8_35_16c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m5_S15_8_35_16_corner00  :
    0 ≤ hfloor_m5_S15_8_35_16c1 + hfloor_m5_S15_8_35_16c2 * ((103293) / (500000)) + hfloor_m5_S15_8_35_16c3 * (0)
        + hfloor_m5_S15_8_35_16c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m5_S15_8_35_16c1 + hfloor_m5_S15_8_35_16c2 * ((103293) / (500000)) + hfloor_m5_S15_8_35_16c3 * (0)
        + hfloor_m5_S15_8_35_16c4 * (((103293) / (500000)) * (0))
      = (33834162197)
        / (1047000000000) := by
    simp only [hfloor_m5_S15_8_35_16c1, hfloor_m5_S15_8_35_16c2, hfloor_m5_S15_8_35_16c3, hfloor_m5_S15_8_35_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S15_8_35_16_corner01  :
    0 ≤ hfloor_m5_S15_8_35_16c1 + hfloor_m5_S15_8_35_16c2 * ((103293) / (500000)) + hfloor_m5_S15_8_35_16c3 * (1)
        + hfloor_m5_S15_8_35_16c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m5_S15_8_35_16c1 + hfloor_m5_S15_8_35_16c2 * ((103293) / (500000)) + hfloor_m5_S15_8_35_16c3 * (1)
        + hfloor_m5_S15_8_35_16c4 * (((103293) / (500000)) * (1))
      = (33834162197)
        / (1047000000000) := by
    simp only [hfloor_m5_S15_8_35_16c1, hfloor_m5_S15_8_35_16c2, hfloor_m5_S15_8_35_16c3, hfloor_m5_S15_8_35_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S15_8_35_16_corner10  :
    0 ≤ hfloor_m5_S15_8_35_16c1 + hfloor_m5_S15_8_35_16c2 * ((206587) / (1000000)) + hfloor_m5_S15_8_35_16c3 * (0)
        + hfloor_m5_S15_8_35_16c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m5_S15_8_35_16c1 + hfloor_m5_S15_8_35_16c2 * ((206587) / (1000000)) + hfloor_m5_S15_8_35_16c3 * (0)
        + hfloor_m5_S15_8_35_16c4 * (((206587) / (1000000)) * (0))
      = (33835209197)
        / (1047000000000) := by
    simp only [hfloor_m5_S15_8_35_16c1, hfloor_m5_S15_8_35_16c2, hfloor_m5_S15_8_35_16c3, hfloor_m5_S15_8_35_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S15_8_35_16_corner11  :
    0 ≤ hfloor_m5_S15_8_35_16c1 + hfloor_m5_S15_8_35_16c2 * ((206587) / (1000000)) + hfloor_m5_S15_8_35_16c3 * (1)
        + hfloor_m5_S15_8_35_16c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m5_S15_8_35_16c1 + hfloor_m5_S15_8_35_16c2 * ((206587) / (1000000)) + hfloor_m5_S15_8_35_16c3 * (1)
        + hfloor_m5_S15_8_35_16c4 * (((206587) / (1000000)) * (1))
      = (33835209197)
        / (1047000000000) := by
    simp only [hfloor_m5_S15_8_35_16c1, hfloor_m5_S15_8_35_16c2, hfloor_m5_S15_8_35_16c3, hfloor_m5_S15_8_35_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S15_8_35_16_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (1047000000000 * L - 182461379803) / (1047000000000) := by
  rw [← sub_nonneg, hfloor_m5_S15_8_35_16_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m5_S15_8_35_16_corner00)) ((hfloor_m5_S15_8_35_16_corner01)) ((hfloor_m5_S15_8_35_16_corner10)) ((hfloor_m5_S15_8_35_16_corner11))

/-! ### Instance (piece = 37) -/

noncomputable def hfloor_m5_S35_16_5_2c1 : ℝ :=
  ((-12439074787)) / (87000000000)

noncomputable def hfloor_m5_S35_16_5_2c2 : ℝ :=
  1

noncomputable def hfloor_m5_S35_16_5_2c3 : ℝ :=
  0

noncomputable def hfloor_m5_S35_16_5_2c4 : ℝ :=
  0

theorem hfloor_m5_S35_16_5_2_bilinear (L _iv_dummy_HFloors : ℝ) :
    (87000000000 * L - 12439074787) / (87000000000) - 0
      = hfloor_m5_S35_16_5_2c1  + hfloor_m5_S35_16_5_2c2  * L + hfloor_m5_S35_16_5_2c3  * _iv_dummy_HFloors
        + hfloor_m5_S35_16_5_2c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m5_S35_16_5_2c1, hfloor_m5_S35_16_5_2c2, hfloor_m5_S35_16_5_2c3, hfloor_m5_S35_16_5_2c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m5_S35_16_5_2_corner00  :
    0 ≤ hfloor_m5_S35_16_5_2c1 + hfloor_m5_S35_16_5_2c2 * ((103293) / (500000)) + hfloor_m5_S35_16_5_2c3 * (0)
        + hfloor_m5_S35_16_5_2c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m5_S35_16_5_2c1 + hfloor_m5_S35_16_5_2c2 * ((103293) / (500000)) + hfloor_m5_S35_16_5_2c3 * (0)
        + hfloor_m5_S35_16_5_2c4 * (((103293) / (500000)) * (0))
      = (5533907213)
        / (87000000000) := by
    simp only [hfloor_m5_S35_16_5_2c1, hfloor_m5_S35_16_5_2c2, hfloor_m5_S35_16_5_2c3, hfloor_m5_S35_16_5_2c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S35_16_5_2_corner01  :
    0 ≤ hfloor_m5_S35_16_5_2c1 + hfloor_m5_S35_16_5_2c2 * ((103293) / (500000)) + hfloor_m5_S35_16_5_2c3 * (1)
        + hfloor_m5_S35_16_5_2c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m5_S35_16_5_2c1 + hfloor_m5_S35_16_5_2c2 * ((103293) / (500000)) + hfloor_m5_S35_16_5_2c3 * (1)
        + hfloor_m5_S35_16_5_2c4 * (((103293) / (500000)) * (1))
      = (5533907213)
        / (87000000000) := by
    simp only [hfloor_m5_S35_16_5_2c1, hfloor_m5_S35_16_5_2c2, hfloor_m5_S35_16_5_2c3, hfloor_m5_S35_16_5_2c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S35_16_5_2_corner10  :
    0 ≤ hfloor_m5_S35_16_5_2c1 + hfloor_m5_S35_16_5_2c2 * ((206587) / (1000000)) + hfloor_m5_S35_16_5_2c3 * (0)
        + hfloor_m5_S35_16_5_2c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m5_S35_16_5_2c1 + hfloor_m5_S35_16_5_2c2 * ((206587) / (1000000)) + hfloor_m5_S35_16_5_2c3 * (0)
        + hfloor_m5_S35_16_5_2c4 * (((206587) / (1000000)) * (0))
      = (5533994213)
        / (87000000000) := by
    simp only [hfloor_m5_S35_16_5_2c1, hfloor_m5_S35_16_5_2c2, hfloor_m5_S35_16_5_2c3, hfloor_m5_S35_16_5_2c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S35_16_5_2_corner11  :
    0 ≤ hfloor_m5_S35_16_5_2c1 + hfloor_m5_S35_16_5_2c2 * ((206587) / (1000000)) + hfloor_m5_S35_16_5_2c3 * (1)
        + hfloor_m5_S35_16_5_2c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m5_S35_16_5_2c1 + hfloor_m5_S35_16_5_2c2 * ((206587) / (1000000)) + hfloor_m5_S35_16_5_2c3 * (1)
        + hfloor_m5_S35_16_5_2c4 * (((206587) / (1000000)) * (1))
      = (5533994213)
        / (87000000000) := by
    simp only [hfloor_m5_S35_16_5_2c1, hfloor_m5_S35_16_5_2c2, hfloor_m5_S35_16_5_2c3, hfloor_m5_S35_16_5_2c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m5_S35_16_5_2_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (87000000000 * L - 12439074787) / (87000000000) := by
  rw [← sub_nonneg, hfloor_m5_S35_16_5_2_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m5_S35_16_5_2_corner00)) ((hfloor_m5_S35_16_5_2_corner01)) ((hfloor_m5_S35_16_5_2_corner10)) ((hfloor_m5_S35_16_5_2_corner11))

/-! ### Instance (piece = 38) -/

noncomputable def hfloor_m6_S0_1_3_4c1 : ℝ :=
  ((-49637458071)) / (396200000000)

noncomputable def hfloor_m6_S0_1_3_4c2 : ℝ :=
  1

noncomputable def hfloor_m6_S0_1_3_4c3 : ℝ :=
  0

noncomputable def hfloor_m6_S0_1_3_4c4 : ℝ :=
  0

theorem hfloor_m6_S0_1_3_4_bilinear (L _iv_dummy_HFloors : ℝ) :
    (396200000000 * L - 49637458071) / (396200000000) - 0
      = hfloor_m6_S0_1_3_4c1  + hfloor_m6_S0_1_3_4c2  * L + hfloor_m6_S0_1_3_4c3  * _iv_dummy_HFloors
        + hfloor_m6_S0_1_3_4c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m6_S0_1_3_4c1, hfloor_m6_S0_1_3_4c2, hfloor_m6_S0_1_3_4c3, hfloor_m6_S0_1_3_4c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m6_S0_1_3_4_corner00  :
    0 ≤ hfloor_m6_S0_1_3_4c1 + hfloor_m6_S0_1_3_4c2 * ((103293) / (500000)) + hfloor_m6_S0_1_3_4c3 * (0)
        + hfloor_m6_S0_1_3_4c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m6_S0_1_3_4c1 + hfloor_m6_S0_1_3_4c2 * ((103293) / (500000)) + hfloor_m6_S0_1_3_4c3 * (0)
        + hfloor_m6_S0_1_3_4c4 * (((103293) / (500000)) * (0))
      = (32211915129)
        / (396200000000) := by
    simp only [hfloor_m6_S0_1_3_4c1, hfloor_m6_S0_1_3_4c2, hfloor_m6_S0_1_3_4c3, hfloor_m6_S0_1_3_4c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m6_S0_1_3_4_corner01  :
    0 ≤ hfloor_m6_S0_1_3_4c1 + hfloor_m6_S0_1_3_4c2 * ((103293) / (500000)) + hfloor_m6_S0_1_3_4c3 * (1)
        + hfloor_m6_S0_1_3_4c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m6_S0_1_3_4c1 + hfloor_m6_S0_1_3_4c2 * ((103293) / (500000)) + hfloor_m6_S0_1_3_4c3 * (1)
        + hfloor_m6_S0_1_3_4c4 * (((103293) / (500000)) * (1))
      = (32211915129)
        / (396200000000) := by
    simp only [hfloor_m6_S0_1_3_4c1, hfloor_m6_S0_1_3_4c2, hfloor_m6_S0_1_3_4c3, hfloor_m6_S0_1_3_4c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m6_S0_1_3_4_corner10  :
    0 ≤ hfloor_m6_S0_1_3_4c1 + hfloor_m6_S0_1_3_4c2 * ((206587) / (1000000)) + hfloor_m6_S0_1_3_4c3 * (0)
        + hfloor_m6_S0_1_3_4c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m6_S0_1_3_4c1 + hfloor_m6_S0_1_3_4c2 * ((206587) / (1000000)) + hfloor_m6_S0_1_3_4c3 * (0)
        + hfloor_m6_S0_1_3_4c4 * (((206587) / (1000000)) * (0))
      = (32212311329)
        / (396200000000) := by
    simp only [hfloor_m6_S0_1_3_4c1, hfloor_m6_S0_1_3_4c2, hfloor_m6_S0_1_3_4c3, hfloor_m6_S0_1_3_4c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m6_S0_1_3_4_corner11  :
    0 ≤ hfloor_m6_S0_1_3_4c1 + hfloor_m6_S0_1_3_4c2 * ((206587) / (1000000)) + hfloor_m6_S0_1_3_4c3 * (1)
        + hfloor_m6_S0_1_3_4c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m6_S0_1_3_4c1 + hfloor_m6_S0_1_3_4c2 * ((206587) / (1000000)) + hfloor_m6_S0_1_3_4c3 * (1)
        + hfloor_m6_S0_1_3_4c4 * (((206587) / (1000000)) * (1))
      = (32212311329)
        / (396200000000) := by
    simp only [hfloor_m6_S0_1_3_4c1, hfloor_m6_S0_1_3_4c2, hfloor_m6_S0_1_3_4c3, hfloor_m6_S0_1_3_4c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m6_S0_1_3_4_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (396200000000 * L - 49637458071) / (396200000000) := by
  rw [← sub_nonneg, hfloor_m6_S0_1_3_4_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m6_S0_1_3_4_corner00)) ((hfloor_m6_S0_1_3_4_corner01)) ((hfloor_m6_S0_1_3_4_corner10)) ((hfloor_m6_S0_1_3_4_corner11))

/-! ### Instance (piece = 39) -/

noncomputable def hfloor_m6_S3_4_9_8c1 : ℝ :=
  ((-44837714123)) / (259875000000)

noncomputable def hfloor_m6_S3_4_9_8c2 : ℝ :=
  1

noncomputable def hfloor_m6_S3_4_9_8c3 : ℝ :=
  0

noncomputable def hfloor_m6_S3_4_9_8c4 : ℝ :=
  0

theorem hfloor_m6_S3_4_9_8_bilinear (L _iv_dummy_HFloors : ℝ) :
    (259875000000 * L - 44837714123) / (259875000000) - 0
      = hfloor_m6_S3_4_9_8c1  + hfloor_m6_S3_4_9_8c2  * L + hfloor_m6_S3_4_9_8c3  * _iv_dummy_HFloors
        + hfloor_m6_S3_4_9_8c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m6_S3_4_9_8c1, hfloor_m6_S3_4_9_8c2, hfloor_m6_S3_4_9_8c3, hfloor_m6_S3_4_9_8c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m6_S3_4_9_8_corner00  :
    0 ≤ hfloor_m6_S3_4_9_8c1 + hfloor_m6_S3_4_9_8c2 * ((103293) / (500000)) + hfloor_m6_S3_4_9_8c3 * (0)
        + hfloor_m6_S3_4_9_8c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m6_S3_4_9_8c1 + hfloor_m6_S3_4_9_8c2 * ((103293) / (500000)) + hfloor_m6_S3_4_9_8c3 * (0)
        + hfloor_m6_S3_4_9_8c4 * (((103293) / (500000)) * (0))
      = (8848822627)
        / (259875000000) := by
    simp only [hfloor_m6_S3_4_9_8c1, hfloor_m6_S3_4_9_8c2, hfloor_m6_S3_4_9_8c3, hfloor_m6_S3_4_9_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m6_S3_4_9_8_corner01  :
    0 ≤ hfloor_m6_S3_4_9_8c1 + hfloor_m6_S3_4_9_8c2 * ((103293) / (500000)) + hfloor_m6_S3_4_9_8c3 * (1)
        + hfloor_m6_S3_4_9_8c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m6_S3_4_9_8c1 + hfloor_m6_S3_4_9_8c2 * ((103293) / (500000)) + hfloor_m6_S3_4_9_8c3 * (1)
        + hfloor_m6_S3_4_9_8c4 * (((103293) / (500000)) * (1))
      = (8848822627)
        / (259875000000) := by
    simp only [hfloor_m6_S3_4_9_8c1, hfloor_m6_S3_4_9_8c2, hfloor_m6_S3_4_9_8c3, hfloor_m6_S3_4_9_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m6_S3_4_9_8_corner10  :
    0 ≤ hfloor_m6_S3_4_9_8c1 + hfloor_m6_S3_4_9_8c2 * ((206587) / (1000000)) + hfloor_m6_S3_4_9_8c3 * (0)
        + hfloor_m6_S3_4_9_8c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m6_S3_4_9_8c1 + hfloor_m6_S3_4_9_8c2 * ((206587) / (1000000)) + hfloor_m6_S3_4_9_8c3 * (0)
        + hfloor_m6_S3_4_9_8c4 * (((206587) / (1000000)) * (0))
      = (4424541251)
        / (129937500000) := by
    simp only [hfloor_m6_S3_4_9_8c1, hfloor_m6_S3_4_9_8c2, hfloor_m6_S3_4_9_8c3, hfloor_m6_S3_4_9_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m6_S3_4_9_8_corner11  :
    0 ≤ hfloor_m6_S3_4_9_8c1 + hfloor_m6_S3_4_9_8c2 * ((206587) / (1000000)) + hfloor_m6_S3_4_9_8c3 * (1)
        + hfloor_m6_S3_4_9_8c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m6_S3_4_9_8c1 + hfloor_m6_S3_4_9_8c2 * ((206587) / (1000000)) + hfloor_m6_S3_4_9_8c3 * (1)
        + hfloor_m6_S3_4_9_8c4 * (((206587) / (1000000)) * (1))
      = (4424541251)
        / (129937500000) := by
    simp only [hfloor_m6_S3_4_9_8c1, hfloor_m6_S3_4_9_8c2, hfloor_m6_S3_4_9_8c3, hfloor_m6_S3_4_9_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m6_S3_4_9_8_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (259875000000 * L - 44837714123) / (259875000000) := by
  rw [← sub_nonneg, hfloor_m6_S3_4_9_8_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m6_S3_4_9_8_corner00)) ((hfloor_m6_S3_4_9_8_corner01)) ((hfloor_m6_S3_4_9_8_corner10)) ((hfloor_m6_S3_4_9_8_corner11))

/-! ### Instance (piece = 40) -/

noncomputable def hfloor_m6_S9_8_21_16c1 : ℝ :=
  ((-97675129)) / (500000000)

noncomputable def hfloor_m6_S9_8_21_16c2 : ℝ :=
  1

noncomputable def hfloor_m6_S9_8_21_16c3 : ℝ :=
  0

noncomputable def hfloor_m6_S9_8_21_16c4 : ℝ :=
  0

theorem hfloor_m6_S9_8_21_16_bilinear (L _iv_dummy_HFloors : ℝ) :
    (500000000 * L - 97675129) / (500000000) - 0
      = hfloor_m6_S9_8_21_16c1  + hfloor_m6_S9_8_21_16c2  * L + hfloor_m6_S9_8_21_16c3  * _iv_dummy_HFloors
        + hfloor_m6_S9_8_21_16c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m6_S9_8_21_16c1, hfloor_m6_S9_8_21_16c2, hfloor_m6_S9_8_21_16c3, hfloor_m6_S9_8_21_16c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m6_S9_8_21_16_corner00  :
    0 ≤ hfloor_m6_S9_8_21_16c1 + hfloor_m6_S9_8_21_16c2 * ((103293) / (500000)) + hfloor_m6_S9_8_21_16c3 * (0)
        + hfloor_m6_S9_8_21_16c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m6_S9_8_21_16c1 + hfloor_m6_S9_8_21_16c2 * ((103293) / (500000)) + hfloor_m6_S9_8_21_16c3 * (0)
        + hfloor_m6_S9_8_21_16c4 * (((103293) / (500000)) * (0))
      = (5617871)
        / (500000000) := by
    simp only [hfloor_m6_S9_8_21_16c1, hfloor_m6_S9_8_21_16c2, hfloor_m6_S9_8_21_16c3, hfloor_m6_S9_8_21_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m6_S9_8_21_16_corner01  :
    0 ≤ hfloor_m6_S9_8_21_16c1 + hfloor_m6_S9_8_21_16c2 * ((103293) / (500000)) + hfloor_m6_S9_8_21_16c3 * (1)
        + hfloor_m6_S9_8_21_16c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m6_S9_8_21_16c1 + hfloor_m6_S9_8_21_16c2 * ((103293) / (500000)) + hfloor_m6_S9_8_21_16c3 * (1)
        + hfloor_m6_S9_8_21_16c4 * (((103293) / (500000)) * (1))
      = (5617871)
        / (500000000) := by
    simp only [hfloor_m6_S9_8_21_16c1, hfloor_m6_S9_8_21_16c2, hfloor_m6_S9_8_21_16c3, hfloor_m6_S9_8_21_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m6_S9_8_21_16_corner10  :
    0 ≤ hfloor_m6_S9_8_21_16c1 + hfloor_m6_S9_8_21_16c2 * ((206587) / (1000000)) + hfloor_m6_S9_8_21_16c3 * (0)
        + hfloor_m6_S9_8_21_16c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m6_S9_8_21_16c1 + hfloor_m6_S9_8_21_16c2 * ((206587) / (1000000)) + hfloor_m6_S9_8_21_16c3 * (0)
        + hfloor_m6_S9_8_21_16c4 * (((206587) / (1000000)) * (0))
      = (5618371)
        / (500000000) := by
    simp only [hfloor_m6_S9_8_21_16c1, hfloor_m6_S9_8_21_16c2, hfloor_m6_S9_8_21_16c3, hfloor_m6_S9_8_21_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m6_S9_8_21_16_corner11  :
    0 ≤ hfloor_m6_S9_8_21_16c1 + hfloor_m6_S9_8_21_16c2 * ((206587) / (1000000)) + hfloor_m6_S9_8_21_16c3 * (1)
        + hfloor_m6_S9_8_21_16c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m6_S9_8_21_16c1 + hfloor_m6_S9_8_21_16c2 * ((206587) / (1000000)) + hfloor_m6_S9_8_21_16c3 * (1)
        + hfloor_m6_S9_8_21_16c4 * (((206587) / (1000000)) * (1))
      = (5618371)
        / (500000000) := by
    simp only [hfloor_m6_S9_8_21_16c1, hfloor_m6_S9_8_21_16c2, hfloor_m6_S9_8_21_16c3, hfloor_m6_S9_8_21_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m6_S9_8_21_16_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (500000000 * L - 97675129) / (500000000) := by
  rw [← sub_nonneg, hfloor_m6_S9_8_21_16_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m6_S9_8_21_16_corner00)) ((hfloor_m6_S9_8_21_16_corner01)) ((hfloor_m6_S9_8_21_16_corner10)) ((hfloor_m6_S9_8_21_16_corner11))

/-! ### Instance (piece = 41) -/

noncomputable def hfloor_m6_S21_16_3_2c1 : ℝ :=
  ((-8937185027)) / (43470000000)

noncomputable def hfloor_m6_S21_16_3_2c2 : ℝ :=
  1

noncomputable def hfloor_m6_S21_16_3_2c3 : ℝ :=
  0

noncomputable def hfloor_m6_S21_16_3_2c4 : ℝ :=
  0

theorem hfloor_m6_S21_16_3_2_bilinear (L _iv_dummy_HFloors : ℝ) :
    (43470000000 * L - 8937185027) / (43470000000) - 0
      = hfloor_m6_S21_16_3_2c1  + hfloor_m6_S21_16_3_2c2  * L + hfloor_m6_S21_16_3_2c3  * _iv_dummy_HFloors
        + hfloor_m6_S21_16_3_2c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m6_S21_16_3_2c1, hfloor_m6_S21_16_3_2c2, hfloor_m6_S21_16_3_2c3, hfloor_m6_S21_16_3_2c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m6_S21_16_3_2_corner00  :
    0 ≤ hfloor_m6_S21_16_3_2c1 + hfloor_m6_S21_16_3_2c2 * ((103293) / (500000)) + hfloor_m6_S21_16_3_2c3 * (0)
        + hfloor_m6_S21_16_3_2c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m6_S21_16_3_2c1 + hfloor_m6_S21_16_3_2c2 * ((103293) / (500000)) + hfloor_m6_S21_16_3_2c3 * (0)
        + hfloor_m6_S21_16_3_2c4 * (((103293) / (500000)) * (0))
      = (43108393)
        / (43470000000) := by
    simp only [hfloor_m6_S21_16_3_2c1, hfloor_m6_S21_16_3_2c2, hfloor_m6_S21_16_3_2c3, hfloor_m6_S21_16_3_2c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m6_S21_16_3_2_corner01  :
    0 ≤ hfloor_m6_S21_16_3_2c1 + hfloor_m6_S21_16_3_2c2 * ((103293) / (500000)) + hfloor_m6_S21_16_3_2c3 * (1)
        + hfloor_m6_S21_16_3_2c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m6_S21_16_3_2c1 + hfloor_m6_S21_16_3_2c2 * ((103293) / (500000)) + hfloor_m6_S21_16_3_2c3 * (1)
        + hfloor_m6_S21_16_3_2c4 * (((103293) / (500000)) * (1))
      = (43108393)
        / (43470000000) := by
    simp only [hfloor_m6_S21_16_3_2c1, hfloor_m6_S21_16_3_2c2, hfloor_m6_S21_16_3_2c3, hfloor_m6_S21_16_3_2c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m6_S21_16_3_2_corner10  :
    0 ≤ hfloor_m6_S21_16_3_2c1 + hfloor_m6_S21_16_3_2c2 * ((206587) / (1000000)) + hfloor_m6_S21_16_3_2c3 * (0)
        + hfloor_m6_S21_16_3_2c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m6_S21_16_3_2c1 + hfloor_m6_S21_16_3_2c2 * ((206587) / (1000000)) + hfloor_m6_S21_16_3_2c3 * (0)
        + hfloor_m6_S21_16_3_2c4 * (((206587) / (1000000)) * (0))
      = (43151863)
        / (43470000000) := by
    simp only [hfloor_m6_S21_16_3_2c1, hfloor_m6_S21_16_3_2c2, hfloor_m6_S21_16_3_2c3, hfloor_m6_S21_16_3_2c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m6_S21_16_3_2_corner11  :
    0 ≤ hfloor_m6_S21_16_3_2c1 + hfloor_m6_S21_16_3_2c2 * ((206587) / (1000000)) + hfloor_m6_S21_16_3_2c3 * (1)
        + hfloor_m6_S21_16_3_2c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m6_S21_16_3_2c1 + hfloor_m6_S21_16_3_2c2 * ((206587) / (1000000)) + hfloor_m6_S21_16_3_2c3 * (1)
        + hfloor_m6_S21_16_3_2c4 * (((206587) / (1000000)) * (1))
      = (43151863)
        / (43470000000) := by
    simp only [hfloor_m6_S21_16_3_2c1, hfloor_m6_S21_16_3_2c2, hfloor_m6_S21_16_3_2c3, hfloor_m6_S21_16_3_2c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m6_S21_16_3_2_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (43470000000 * L - 8937185027) / (43470000000) := by
  rw [← sub_nonneg, hfloor_m6_S21_16_3_2_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m6_S21_16_3_2_corner00)) ((hfloor_m6_S21_16_3_2_corner01)) ((hfloor_m6_S21_16_3_2_corner10)) ((hfloor_m6_S21_16_3_2_corner11))

/-! ### Instance (piece = 42) -/

noncomputable def hfloor_m6_S3_2_51_32c1 : ℝ :=
  ((-43067195063)) / (219800000000)

noncomputable def hfloor_m6_S3_2_51_32c2 : ℝ :=
  1

noncomputable def hfloor_m6_S3_2_51_32c3 : ℝ :=
  0

noncomputable def hfloor_m6_S3_2_51_32c4 : ℝ :=
  0

theorem hfloor_m6_S3_2_51_32_bilinear (L _iv_dummy_HFloors : ℝ) :
    (219800000000 * L - 43067195063) / (219800000000) - 0
      = hfloor_m6_S3_2_51_32c1  + hfloor_m6_S3_2_51_32c2  * L + hfloor_m6_S3_2_51_32c3  * _iv_dummy_HFloors
        + hfloor_m6_S3_2_51_32c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m6_S3_2_51_32c1, hfloor_m6_S3_2_51_32c2, hfloor_m6_S3_2_51_32c3, hfloor_m6_S3_2_51_32c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m6_S3_2_51_32_corner00  :
    0 ≤ hfloor_m6_S3_2_51_32c1 + hfloor_m6_S3_2_51_32c2 * ((103293) / (500000)) + hfloor_m6_S3_2_51_32c3 * (0)
        + hfloor_m6_S3_2_51_32c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m6_S3_2_51_32c1 + hfloor_m6_S3_2_51_32c2 * ((103293) / (500000)) + hfloor_m6_S3_2_51_32c3 * (0)
        + hfloor_m6_S3_2_51_32c4 * (((103293) / (500000)) * (0))
      = (2340407737)
        / (219800000000) := by
    simp only [hfloor_m6_S3_2_51_32c1, hfloor_m6_S3_2_51_32c2, hfloor_m6_S3_2_51_32c3, hfloor_m6_S3_2_51_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m6_S3_2_51_32_corner01  :
    0 ≤ hfloor_m6_S3_2_51_32c1 + hfloor_m6_S3_2_51_32c2 * ((103293) / (500000)) + hfloor_m6_S3_2_51_32c3 * (1)
        + hfloor_m6_S3_2_51_32c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m6_S3_2_51_32c1 + hfloor_m6_S3_2_51_32c2 * ((103293) / (500000)) + hfloor_m6_S3_2_51_32c3 * (1)
        + hfloor_m6_S3_2_51_32c4 * (((103293) / (500000)) * (1))
      = (2340407737)
        / (219800000000) := by
    simp only [hfloor_m6_S3_2_51_32c1, hfloor_m6_S3_2_51_32c2, hfloor_m6_S3_2_51_32c3, hfloor_m6_S3_2_51_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m6_S3_2_51_32_corner10  :
    0 ≤ hfloor_m6_S3_2_51_32c1 + hfloor_m6_S3_2_51_32c2 * ((206587) / (1000000)) + hfloor_m6_S3_2_51_32c3 * (0)
        + hfloor_m6_S3_2_51_32c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m6_S3_2_51_32c1 + hfloor_m6_S3_2_51_32c2 * ((206587) / (1000000)) + hfloor_m6_S3_2_51_32c3 * (0)
        + hfloor_m6_S3_2_51_32c4 * (((206587) / (1000000)) * (0))
      = (2340627537)
        / (219800000000) := by
    simp only [hfloor_m6_S3_2_51_32c1, hfloor_m6_S3_2_51_32c2, hfloor_m6_S3_2_51_32c3, hfloor_m6_S3_2_51_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m6_S3_2_51_32_corner11  :
    0 ≤ hfloor_m6_S3_2_51_32c1 + hfloor_m6_S3_2_51_32c2 * ((206587) / (1000000)) + hfloor_m6_S3_2_51_32c3 * (1)
        + hfloor_m6_S3_2_51_32c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m6_S3_2_51_32c1 + hfloor_m6_S3_2_51_32c2 * ((206587) / (1000000)) + hfloor_m6_S3_2_51_32c3 * (1)
        + hfloor_m6_S3_2_51_32c4 * (((206587) / (1000000)) * (1))
      = (2340627537)
        / (219800000000) := by
    simp only [hfloor_m6_S3_2_51_32c1, hfloor_m6_S3_2_51_32c2, hfloor_m6_S3_2_51_32c3, hfloor_m6_S3_2_51_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m6_S3_2_51_32_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (219800000000 * L - 43067195063) / (219800000000) := by
  rw [← sub_nonneg, hfloor_m6_S3_2_51_32_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m6_S3_2_51_32_corner00)) ((hfloor_m6_S3_2_51_32_corner01)) ((hfloor_m6_S3_2_51_32_corner10)) ((hfloor_m6_S3_2_51_32_corner11))

/-! ### Instance (piece = 43) -/

noncomputable def hfloor_m6_S51_32_27_16c1 : ℝ :=
  ((-170470705851)) / (889000000000)

noncomputable def hfloor_m6_S51_32_27_16c2 : ℝ :=
  1

noncomputable def hfloor_m6_S51_32_27_16c3 : ℝ :=
  0

noncomputable def hfloor_m6_S51_32_27_16c4 : ℝ :=
  0

theorem hfloor_m6_S51_32_27_16_bilinear (L _iv_dummy_HFloors : ℝ) :
    (889000000000 * L - 170470705851) / (889000000000) - 0
      = hfloor_m6_S51_32_27_16c1  + hfloor_m6_S51_32_27_16c2  * L + hfloor_m6_S51_32_27_16c3  * _iv_dummy_HFloors
        + hfloor_m6_S51_32_27_16c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m6_S51_32_27_16c1, hfloor_m6_S51_32_27_16c2, hfloor_m6_S51_32_27_16c3, hfloor_m6_S51_32_27_16c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m6_S51_32_27_16_corner00  :
    0 ≤ hfloor_m6_S51_32_27_16c1 + hfloor_m6_S51_32_27_16c2 * ((103293) / (500000)) + hfloor_m6_S51_32_27_16c3 * (0)
        + hfloor_m6_S51_32_27_16c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m6_S51_32_27_16c1 + hfloor_m6_S51_32_27_16c2 * ((103293) / (500000)) + hfloor_m6_S51_32_27_16c3 * (0)
        + hfloor_m6_S51_32_27_16c4 * (((103293) / (500000)) * (0))
      = (13184248149)
        / (889000000000) := by
    simp only [hfloor_m6_S51_32_27_16c1, hfloor_m6_S51_32_27_16c2, hfloor_m6_S51_32_27_16c3, hfloor_m6_S51_32_27_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m6_S51_32_27_16_corner01  :
    0 ≤ hfloor_m6_S51_32_27_16c1 + hfloor_m6_S51_32_27_16c2 * ((103293) / (500000)) + hfloor_m6_S51_32_27_16c3 * (1)
        + hfloor_m6_S51_32_27_16c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m6_S51_32_27_16c1 + hfloor_m6_S51_32_27_16c2 * ((103293) / (500000)) + hfloor_m6_S51_32_27_16c3 * (1)
        + hfloor_m6_S51_32_27_16c4 * (((103293) / (500000)) * (1))
      = (13184248149)
        / (889000000000) := by
    simp only [hfloor_m6_S51_32_27_16c1, hfloor_m6_S51_32_27_16c2, hfloor_m6_S51_32_27_16c3, hfloor_m6_S51_32_27_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m6_S51_32_27_16_corner10  :
    0 ≤ hfloor_m6_S51_32_27_16c1 + hfloor_m6_S51_32_27_16c2 * ((206587) / (1000000)) + hfloor_m6_S51_32_27_16c3 * (0)
        + hfloor_m6_S51_32_27_16c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m6_S51_32_27_16c1 + hfloor_m6_S51_32_27_16c2 * ((206587) / (1000000)) + hfloor_m6_S51_32_27_16c3 * (0)
        + hfloor_m6_S51_32_27_16c4 * (((206587) / (1000000)) * (0))
      = (13185137149)
        / (889000000000) := by
    simp only [hfloor_m6_S51_32_27_16c1, hfloor_m6_S51_32_27_16c2, hfloor_m6_S51_32_27_16c3, hfloor_m6_S51_32_27_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m6_S51_32_27_16_corner11  :
    0 ≤ hfloor_m6_S51_32_27_16c1 + hfloor_m6_S51_32_27_16c2 * ((206587) / (1000000)) + hfloor_m6_S51_32_27_16c3 * (1)
        + hfloor_m6_S51_32_27_16c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m6_S51_32_27_16c1 + hfloor_m6_S51_32_27_16c2 * ((206587) / (1000000)) + hfloor_m6_S51_32_27_16c3 * (1)
        + hfloor_m6_S51_32_27_16c4 * (((206587) / (1000000)) * (1))
      = (13185137149)
        / (889000000000) := by
    simp only [hfloor_m6_S51_32_27_16c1, hfloor_m6_S51_32_27_16c2, hfloor_m6_S51_32_27_16c3, hfloor_m6_S51_32_27_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m6_S51_32_27_16_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (889000000000 * L - 170470705851) / (889000000000) := by
  rw [← sub_nonneg, hfloor_m6_S51_32_27_16_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m6_S51_32_27_16_corner00)) ((hfloor_m6_S51_32_27_16_corner01)) ((hfloor_m6_S51_32_27_16_corner10)) ((hfloor_m6_S51_32_27_16_corner11))

/-! ### Instance (piece = 44) -/

noncomputable def hfloor_m6_S27_16_15_8c1 : ℝ :=
  ((-874452521711)) / (4543000000000)

noncomputable def hfloor_m6_S27_16_15_8c2 : ℝ :=
  1

noncomputable def hfloor_m6_S27_16_15_8c3 : ℝ :=
  0

noncomputable def hfloor_m6_S27_16_15_8c4 : ℝ :=
  0

theorem hfloor_m6_S27_16_15_8_bilinear (L _iv_dummy_HFloors : ℝ) :
    (4543000000000 * L - 874452521711) / (4543000000000) - 0
      = hfloor_m6_S27_16_15_8c1  + hfloor_m6_S27_16_15_8c2  * L + hfloor_m6_S27_16_15_8c3  * _iv_dummy_HFloors
        + hfloor_m6_S27_16_15_8c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m6_S27_16_15_8c1, hfloor_m6_S27_16_15_8c2, hfloor_m6_S27_16_15_8c3, hfloor_m6_S27_16_15_8c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m6_S27_16_15_8_corner00  :
    0 ≤ hfloor_m6_S27_16_15_8c1 + hfloor_m6_S27_16_15_8c2 * ((103293) / (500000)) + hfloor_m6_S27_16_15_8c3 * (0)
        + hfloor_m6_S27_16_15_8c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m6_S27_16_15_8c1 + hfloor_m6_S27_16_15_8c2 * ((103293) / (500000)) + hfloor_m6_S27_16_15_8c3 * (0)
        + hfloor_m6_S27_16_15_8c4 * (((103293) / (500000)) * (0))
      = (64067676289)
        / (4543000000000) := by
    simp only [hfloor_m6_S27_16_15_8c1, hfloor_m6_S27_16_15_8c2, hfloor_m6_S27_16_15_8c3, hfloor_m6_S27_16_15_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m6_S27_16_15_8_corner01  :
    0 ≤ hfloor_m6_S27_16_15_8c1 + hfloor_m6_S27_16_15_8c2 * ((103293) / (500000)) + hfloor_m6_S27_16_15_8c3 * (1)
        + hfloor_m6_S27_16_15_8c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m6_S27_16_15_8c1 + hfloor_m6_S27_16_15_8c2 * ((103293) / (500000)) + hfloor_m6_S27_16_15_8c3 * (1)
        + hfloor_m6_S27_16_15_8c4 * (((103293) / (500000)) * (1))
      = (64067676289)
        / (4543000000000) := by
    simp only [hfloor_m6_S27_16_15_8c1, hfloor_m6_S27_16_15_8c2, hfloor_m6_S27_16_15_8c3, hfloor_m6_S27_16_15_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m6_S27_16_15_8_corner10  :
    0 ≤ hfloor_m6_S27_16_15_8c1 + hfloor_m6_S27_16_15_8c2 * ((206587) / (1000000)) + hfloor_m6_S27_16_15_8c3 * (0)
        + hfloor_m6_S27_16_15_8c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m6_S27_16_15_8c1 + hfloor_m6_S27_16_15_8c2 * ((206587) / (1000000)) + hfloor_m6_S27_16_15_8c3 * (0)
        + hfloor_m6_S27_16_15_8c4 * (((206587) / (1000000)) * (0))
      = (64072219289)
        / (4543000000000) := by
    simp only [hfloor_m6_S27_16_15_8c1, hfloor_m6_S27_16_15_8c2, hfloor_m6_S27_16_15_8c3, hfloor_m6_S27_16_15_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m6_S27_16_15_8_corner11  :
    0 ≤ hfloor_m6_S27_16_15_8c1 + hfloor_m6_S27_16_15_8c2 * ((206587) / (1000000)) + hfloor_m6_S27_16_15_8c3 * (1)
        + hfloor_m6_S27_16_15_8c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m6_S27_16_15_8c1 + hfloor_m6_S27_16_15_8c2 * ((206587) / (1000000)) + hfloor_m6_S27_16_15_8c3 * (1)
        + hfloor_m6_S27_16_15_8c4 * (((206587) / (1000000)) * (1))
      = (64072219289)
        / (4543000000000) := by
    simp only [hfloor_m6_S27_16_15_8c1, hfloor_m6_S27_16_15_8c2, hfloor_m6_S27_16_15_8c3, hfloor_m6_S27_16_15_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m6_S27_16_15_8_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (4543000000000 * L - 874452521711) / (4543000000000) := by
  rw [← sub_nonneg, hfloor_m6_S27_16_15_8_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m6_S27_16_15_8_corner00)) ((hfloor_m6_S27_16_15_8_corner01)) ((hfloor_m6_S27_16_15_8_corner10)) ((hfloor_m6_S27_16_15_8_corner11))

/-! ### Instance (piece = 45) -/

noncomputable def hfloor_m6_S15_8_9_4c1 : ℝ :=
  ((-227868330871)) / (1183000000000)

noncomputable def hfloor_m6_S15_8_9_4c2 : ℝ :=
  1

noncomputable def hfloor_m6_S15_8_9_4c3 : ℝ :=
  0

noncomputable def hfloor_m6_S15_8_9_4c4 : ℝ :=
  0

theorem hfloor_m6_S15_8_9_4_bilinear (L _iv_dummy_HFloors : ℝ) :
    (1183000000000 * L - 227868330871) / (1183000000000) - 0
      = hfloor_m6_S15_8_9_4c1  + hfloor_m6_S15_8_9_4c2  * L + hfloor_m6_S15_8_9_4c3  * _iv_dummy_HFloors
        + hfloor_m6_S15_8_9_4c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m6_S15_8_9_4c1, hfloor_m6_S15_8_9_4c2, hfloor_m6_S15_8_9_4c3, hfloor_m6_S15_8_9_4c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m6_S15_8_9_4_corner00  :
    0 ≤ hfloor_m6_S15_8_9_4c1 + hfloor_m6_S15_8_9_4c2 * ((103293) / (500000)) + hfloor_m6_S15_8_9_4c3 * (0)
        + hfloor_m6_S15_8_9_4c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m6_S15_8_9_4c1 + hfloor_m6_S15_8_9_4c2 * ((103293) / (500000)) + hfloor_m6_S15_8_9_4c3 * (0)
        + hfloor_m6_S15_8_9_4c4 * (((103293) / (500000)) * (0))
      = (16522907129)
        / (1183000000000) := by
    simp only [hfloor_m6_S15_8_9_4c1, hfloor_m6_S15_8_9_4c2, hfloor_m6_S15_8_9_4c3, hfloor_m6_S15_8_9_4c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m6_S15_8_9_4_corner01  :
    0 ≤ hfloor_m6_S15_8_9_4c1 + hfloor_m6_S15_8_9_4c2 * ((103293) / (500000)) + hfloor_m6_S15_8_9_4c3 * (1)
        + hfloor_m6_S15_8_9_4c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m6_S15_8_9_4c1 + hfloor_m6_S15_8_9_4c2 * ((103293) / (500000)) + hfloor_m6_S15_8_9_4c3 * (1)
        + hfloor_m6_S15_8_9_4c4 * (((103293) / (500000)) * (1))
      = (16522907129)
        / (1183000000000) := by
    simp only [hfloor_m6_S15_8_9_4c1, hfloor_m6_S15_8_9_4c2, hfloor_m6_S15_8_9_4c3, hfloor_m6_S15_8_9_4c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m6_S15_8_9_4_corner10  :
    0 ≤ hfloor_m6_S15_8_9_4c1 + hfloor_m6_S15_8_9_4c2 * ((206587) / (1000000)) + hfloor_m6_S15_8_9_4c3 * (0)
        + hfloor_m6_S15_8_9_4c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m6_S15_8_9_4c1 + hfloor_m6_S15_8_9_4c2 * ((206587) / (1000000)) + hfloor_m6_S15_8_9_4c3 * (0)
        + hfloor_m6_S15_8_9_4c4 * (((206587) / (1000000)) * (0))
      = (16524090129)
        / (1183000000000) := by
    simp only [hfloor_m6_S15_8_9_4c1, hfloor_m6_S15_8_9_4c2, hfloor_m6_S15_8_9_4c3, hfloor_m6_S15_8_9_4c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m6_S15_8_9_4_corner11  :
    0 ≤ hfloor_m6_S15_8_9_4c1 + hfloor_m6_S15_8_9_4c2 * ((206587) / (1000000)) + hfloor_m6_S15_8_9_4c3 * (1)
        + hfloor_m6_S15_8_9_4c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m6_S15_8_9_4c1 + hfloor_m6_S15_8_9_4c2 * ((206587) / (1000000)) + hfloor_m6_S15_8_9_4c3 * (1)
        + hfloor_m6_S15_8_9_4c4 * (((206587) / (1000000)) * (1))
      = (16524090129)
        / (1183000000000) := by
    simp only [hfloor_m6_S15_8_9_4c1, hfloor_m6_S15_8_9_4c2, hfloor_m6_S15_8_9_4c3, hfloor_m6_S15_8_9_4c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m6_S15_8_9_4_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (1183000000000 * L - 227868330871) / (1183000000000) := by
  rw [← sub_nonneg, hfloor_m6_S15_8_9_4_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m6_S15_8_9_4_corner00)) ((hfloor_m6_S15_8_9_4_corner01)) ((hfloor_m6_S15_8_9_4_corner10)) ((hfloor_m6_S15_8_9_4_corner11))

/-! ### Instance (piece = 46) -/

noncomputable def hfloor_m6_S9_4_3_1c1 : ℝ :=
  ((-24060185301)) / (127925000000)

noncomputable def hfloor_m6_S9_4_3_1c2 : ℝ :=
  1

noncomputable def hfloor_m6_S9_4_3_1c3 : ℝ :=
  0

noncomputable def hfloor_m6_S9_4_3_1c4 : ℝ :=
  0

theorem hfloor_m6_S9_4_3_1_bilinear (L _iv_dummy_HFloors : ℝ) :
    (127925000000 * L - 24060185301) / (127925000000) - 0
      = hfloor_m6_S9_4_3_1c1  + hfloor_m6_S9_4_3_1c2  * L + hfloor_m6_S9_4_3_1c3  * _iv_dummy_HFloors
        + hfloor_m6_S9_4_3_1c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m6_S9_4_3_1c1, hfloor_m6_S9_4_3_1c2, hfloor_m6_S9_4_3_1c3, hfloor_m6_S9_4_3_1c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m6_S9_4_3_1_corner00  :
    0 ≤ hfloor_m6_S9_4_3_1c1 + hfloor_m6_S9_4_3_1c2 * ((103293) / (500000)) + hfloor_m6_S9_4_3_1c3 * (0)
        + hfloor_m6_S9_4_3_1c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m6_S9_4_3_1c1 + hfloor_m6_S9_4_3_1c2 * ((103293) / (500000)) + hfloor_m6_S9_4_3_1c3 * (0)
        + hfloor_m6_S9_4_3_1c4 * (((103293) / (500000)) * (0))
      = (2367328749)
        / (127925000000) := by
    simp only [hfloor_m6_S9_4_3_1c1, hfloor_m6_S9_4_3_1c2, hfloor_m6_S9_4_3_1c3, hfloor_m6_S9_4_3_1c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m6_S9_4_3_1_corner01  :
    0 ≤ hfloor_m6_S9_4_3_1c1 + hfloor_m6_S9_4_3_1c2 * ((103293) / (500000)) + hfloor_m6_S9_4_3_1c3 * (1)
        + hfloor_m6_S9_4_3_1c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m6_S9_4_3_1c1 + hfloor_m6_S9_4_3_1c2 * ((103293) / (500000)) + hfloor_m6_S9_4_3_1c3 * (1)
        + hfloor_m6_S9_4_3_1c4 * (((103293) / (500000)) * (1))
      = (2367328749)
        / (127925000000) := by
    simp only [hfloor_m6_S9_4_3_1c1, hfloor_m6_S9_4_3_1c2, hfloor_m6_S9_4_3_1c3, hfloor_m6_S9_4_3_1c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m6_S9_4_3_1_corner10  :
    0 ≤ hfloor_m6_S9_4_3_1c1 + hfloor_m6_S9_4_3_1c2 * ((206587) / (1000000)) + hfloor_m6_S9_4_3_1c3 * (0)
        + hfloor_m6_S9_4_3_1c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m6_S9_4_3_1c1 + hfloor_m6_S9_4_3_1c2 * ((206587) / (1000000)) + hfloor_m6_S9_4_3_1c3 * (0)
        + hfloor_m6_S9_4_3_1c4 * (((206587) / (1000000)) * (0))
      = (1183728337)
        / (63962500000) := by
    simp only [hfloor_m6_S9_4_3_1c1, hfloor_m6_S9_4_3_1c2, hfloor_m6_S9_4_3_1c3, hfloor_m6_S9_4_3_1c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m6_S9_4_3_1_corner11  :
    0 ≤ hfloor_m6_S9_4_3_1c1 + hfloor_m6_S9_4_3_1c2 * ((206587) / (1000000)) + hfloor_m6_S9_4_3_1c3 * (1)
        + hfloor_m6_S9_4_3_1c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m6_S9_4_3_1c1 + hfloor_m6_S9_4_3_1c2 * ((206587) / (1000000)) + hfloor_m6_S9_4_3_1c3 * (1)
        + hfloor_m6_S9_4_3_1c4 * (((206587) / (1000000)) * (1))
      = (1183728337)
        / (63962500000) := by
    simp only [hfloor_m6_S9_4_3_1c1, hfloor_m6_S9_4_3_1c2, hfloor_m6_S9_4_3_1c3, hfloor_m6_S9_4_3_1c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m6_S9_4_3_1_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (127925000000 * L - 24060185301) / (127925000000) := by
  rw [← sub_nonneg, hfloor_m6_S9_4_3_1_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m6_S9_4_3_1_corner00)) ((hfloor_m6_S9_4_3_1_corner01)) ((hfloor_m6_S9_4_3_1_corner10)) ((hfloor_m6_S9_4_3_1_corner11))

/-! ### Instance (piece = 47) -/

noncomputable def hfloor_m7_S0_1_7_8c1 : ℝ :=
  ((-25459359)) / (200000000)

noncomputable def hfloor_m7_S0_1_7_8c2 : ℝ :=
  1

noncomputable def hfloor_m7_S0_1_7_8c3 : ℝ :=
  0

noncomputable def hfloor_m7_S0_1_7_8c4 : ℝ :=
  0

theorem hfloor_m7_S0_1_7_8_bilinear (L _iv_dummy_HFloors : ℝ) :
    (200000000 * L - 25459359) / (200000000) - 0
      = hfloor_m7_S0_1_7_8c1  + hfloor_m7_S0_1_7_8c2  * L + hfloor_m7_S0_1_7_8c3  * _iv_dummy_HFloors
        + hfloor_m7_S0_1_7_8c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m7_S0_1_7_8c1, hfloor_m7_S0_1_7_8c2, hfloor_m7_S0_1_7_8c3, hfloor_m7_S0_1_7_8c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m7_S0_1_7_8_corner00  :
    0 ≤ hfloor_m7_S0_1_7_8c1 + hfloor_m7_S0_1_7_8c2 * ((103293) / (500000)) + hfloor_m7_S0_1_7_8c3 * (0)
        + hfloor_m7_S0_1_7_8c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m7_S0_1_7_8c1 + hfloor_m7_S0_1_7_8c2 * ((103293) / (500000)) + hfloor_m7_S0_1_7_8c3 * (0)
        + hfloor_m7_S0_1_7_8c4 * (((103293) / (500000)) * (0))
      = (15857841)
        / (200000000) := by
    simp only [hfloor_m7_S0_1_7_8c1, hfloor_m7_S0_1_7_8c2, hfloor_m7_S0_1_7_8c3, hfloor_m7_S0_1_7_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m7_S0_1_7_8_corner01  :
    0 ≤ hfloor_m7_S0_1_7_8c1 + hfloor_m7_S0_1_7_8c2 * ((103293) / (500000)) + hfloor_m7_S0_1_7_8c3 * (1)
        + hfloor_m7_S0_1_7_8c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m7_S0_1_7_8c1 + hfloor_m7_S0_1_7_8c2 * ((103293) / (500000)) + hfloor_m7_S0_1_7_8c3 * (1)
        + hfloor_m7_S0_1_7_8c4 * (((103293) / (500000)) * (1))
      = (15857841)
        / (200000000) := by
    simp only [hfloor_m7_S0_1_7_8c1, hfloor_m7_S0_1_7_8c2, hfloor_m7_S0_1_7_8c3, hfloor_m7_S0_1_7_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m7_S0_1_7_8_corner10  :
    0 ≤ hfloor_m7_S0_1_7_8c1 + hfloor_m7_S0_1_7_8c2 * ((206587) / (1000000)) + hfloor_m7_S0_1_7_8c3 * (0)
        + hfloor_m7_S0_1_7_8c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m7_S0_1_7_8c1 + hfloor_m7_S0_1_7_8c2 * ((206587) / (1000000)) + hfloor_m7_S0_1_7_8c3 * (0)
        + hfloor_m7_S0_1_7_8c4 * (((206587) / (1000000)) * (0))
      = (15858041)
        / (200000000) := by
    simp only [hfloor_m7_S0_1_7_8c1, hfloor_m7_S0_1_7_8c2, hfloor_m7_S0_1_7_8c3, hfloor_m7_S0_1_7_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m7_S0_1_7_8_corner11  :
    0 ≤ hfloor_m7_S0_1_7_8c1 + hfloor_m7_S0_1_7_8c2 * ((206587) / (1000000)) + hfloor_m7_S0_1_7_8c3 * (1)
        + hfloor_m7_S0_1_7_8c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m7_S0_1_7_8c1 + hfloor_m7_S0_1_7_8c2 * ((206587) / (1000000)) + hfloor_m7_S0_1_7_8c3 * (1)
        + hfloor_m7_S0_1_7_8c4 * (((206587) / (1000000)) * (1))
      = (15858041)
        / (200000000) := by
    simp only [hfloor_m7_S0_1_7_8c1, hfloor_m7_S0_1_7_8c2, hfloor_m7_S0_1_7_8c3, hfloor_m7_S0_1_7_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m7_S0_1_7_8_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (200000000 * L - 25459359) / (200000000) := by
  rw [← sub_nonneg, hfloor_m7_S0_1_7_8_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m7_S0_1_7_8_corner00)) ((hfloor_m7_S0_1_7_8_corner01)) ((hfloor_m7_S0_1_7_8_corner10)) ((hfloor_m7_S0_1_7_8_corner11))

/-! ### Instance (piece = 48) -/

noncomputable def hfloor_m7_S7_8_21_16c1 : ℝ :=
  ((-43854011)) / (250000000)

noncomputable def hfloor_m7_S7_8_21_16c2 : ℝ :=
  1

noncomputable def hfloor_m7_S7_8_21_16c3 : ℝ :=
  0

noncomputable def hfloor_m7_S7_8_21_16c4 : ℝ :=
  0

theorem hfloor_m7_S7_8_21_16_bilinear (L _iv_dummy_HFloors : ℝ) :
    (250000000 * L - 43854011) / (250000000) - 0
      = hfloor_m7_S7_8_21_16c1  + hfloor_m7_S7_8_21_16c2  * L + hfloor_m7_S7_8_21_16c3  * _iv_dummy_HFloors
        + hfloor_m7_S7_8_21_16c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m7_S7_8_21_16c1, hfloor_m7_S7_8_21_16c2, hfloor_m7_S7_8_21_16c3, hfloor_m7_S7_8_21_16c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m7_S7_8_21_16_corner00  :
    0 ≤ hfloor_m7_S7_8_21_16c1 + hfloor_m7_S7_8_21_16c2 * ((103293) / (500000)) + hfloor_m7_S7_8_21_16c3 * (0)
        + hfloor_m7_S7_8_21_16c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m7_S7_8_21_16c1 + hfloor_m7_S7_8_21_16c2 * ((103293) / (500000)) + hfloor_m7_S7_8_21_16c3 * (0)
        + hfloor_m7_S7_8_21_16c4 * (((103293) / (500000)) * (0))
      = (7792489)
        / (250000000) := by
    simp only [hfloor_m7_S7_8_21_16c1, hfloor_m7_S7_8_21_16c2, hfloor_m7_S7_8_21_16c3, hfloor_m7_S7_8_21_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m7_S7_8_21_16_corner01  :
    0 ≤ hfloor_m7_S7_8_21_16c1 + hfloor_m7_S7_8_21_16c2 * ((103293) / (500000)) + hfloor_m7_S7_8_21_16c3 * (1)
        + hfloor_m7_S7_8_21_16c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m7_S7_8_21_16c1 + hfloor_m7_S7_8_21_16c2 * ((103293) / (500000)) + hfloor_m7_S7_8_21_16c3 * (1)
        + hfloor_m7_S7_8_21_16c4 * (((103293) / (500000)) * (1))
      = (7792489)
        / (250000000) := by
    simp only [hfloor_m7_S7_8_21_16c1, hfloor_m7_S7_8_21_16c2, hfloor_m7_S7_8_21_16c3, hfloor_m7_S7_8_21_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m7_S7_8_21_16_corner10  :
    0 ≤ hfloor_m7_S7_8_21_16c1 + hfloor_m7_S7_8_21_16c2 * ((206587) / (1000000)) + hfloor_m7_S7_8_21_16c3 * (0)
        + hfloor_m7_S7_8_21_16c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m7_S7_8_21_16c1 + hfloor_m7_S7_8_21_16c2 * ((206587) / (1000000)) + hfloor_m7_S7_8_21_16c3 * (0)
        + hfloor_m7_S7_8_21_16c4 * (((206587) / (1000000)) * (0))
      = (7792739)
        / (250000000) := by
    simp only [hfloor_m7_S7_8_21_16c1, hfloor_m7_S7_8_21_16c2, hfloor_m7_S7_8_21_16c3, hfloor_m7_S7_8_21_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m7_S7_8_21_16_corner11  :
    0 ≤ hfloor_m7_S7_8_21_16c1 + hfloor_m7_S7_8_21_16c2 * ((206587) / (1000000)) + hfloor_m7_S7_8_21_16c3 * (1)
        + hfloor_m7_S7_8_21_16c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m7_S7_8_21_16c1 + hfloor_m7_S7_8_21_16c2 * ((206587) / (1000000)) + hfloor_m7_S7_8_21_16c3 * (1)
        + hfloor_m7_S7_8_21_16c4 * (((206587) / (1000000)) * (1))
      = (7792739)
        / (250000000) := by
    simp only [hfloor_m7_S7_8_21_16c1, hfloor_m7_S7_8_21_16c2, hfloor_m7_S7_8_21_16c3, hfloor_m7_S7_8_21_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m7_S7_8_21_16_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (250000000 * L - 43854011) / (250000000) := by
  rw [← sub_nonneg, hfloor_m7_S7_8_21_16_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m7_S7_8_21_16_corner00)) ((hfloor_m7_S7_8_21_16_corner01)) ((hfloor_m7_S7_8_21_16_corner10)) ((hfloor_m7_S7_8_21_16_corner11))

/-! ### Instance (piece = 49) -/

noncomputable def hfloor_m7_S21_16_49_32c1 : ℝ :=
  ((-99317167)) / (500000000)

noncomputable def hfloor_m7_S21_16_49_32c2 : ℝ :=
  1

noncomputable def hfloor_m7_S21_16_49_32c3 : ℝ :=
  0

noncomputable def hfloor_m7_S21_16_49_32c4 : ℝ :=
  0

theorem hfloor_m7_S21_16_49_32_bilinear (L _iv_dummy_HFloors : ℝ) :
    (500000000 * L - 99317167) / (500000000) - 0
      = hfloor_m7_S21_16_49_32c1  + hfloor_m7_S21_16_49_32c2  * L + hfloor_m7_S21_16_49_32c3  * _iv_dummy_HFloors
        + hfloor_m7_S21_16_49_32c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m7_S21_16_49_32c1, hfloor_m7_S21_16_49_32c2, hfloor_m7_S21_16_49_32c3, hfloor_m7_S21_16_49_32c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m7_S21_16_49_32_corner00  :
    0 ≤ hfloor_m7_S21_16_49_32c1 + hfloor_m7_S21_16_49_32c2 * ((103293) / (500000)) + hfloor_m7_S21_16_49_32c3 * (0)
        + hfloor_m7_S21_16_49_32c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m7_S21_16_49_32c1 + hfloor_m7_S21_16_49_32c2 * ((103293) / (500000)) + hfloor_m7_S21_16_49_32c3 * (0)
        + hfloor_m7_S21_16_49_32c4 * (((103293) / (500000)) * (0))
      = (3975833)
        / (500000000) := by
    simp only [hfloor_m7_S21_16_49_32c1, hfloor_m7_S21_16_49_32c2, hfloor_m7_S21_16_49_32c3, hfloor_m7_S21_16_49_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m7_S21_16_49_32_corner01  :
    0 ≤ hfloor_m7_S21_16_49_32c1 + hfloor_m7_S21_16_49_32c2 * ((103293) / (500000)) + hfloor_m7_S21_16_49_32c3 * (1)
        + hfloor_m7_S21_16_49_32c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m7_S21_16_49_32c1 + hfloor_m7_S21_16_49_32c2 * ((103293) / (500000)) + hfloor_m7_S21_16_49_32c3 * (1)
        + hfloor_m7_S21_16_49_32c4 * (((103293) / (500000)) * (1))
      = (3975833)
        / (500000000) := by
    simp only [hfloor_m7_S21_16_49_32c1, hfloor_m7_S21_16_49_32c2, hfloor_m7_S21_16_49_32c3, hfloor_m7_S21_16_49_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m7_S21_16_49_32_corner10  :
    0 ≤ hfloor_m7_S21_16_49_32c1 + hfloor_m7_S21_16_49_32c2 * ((206587) / (1000000)) + hfloor_m7_S21_16_49_32c3 * (0)
        + hfloor_m7_S21_16_49_32c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m7_S21_16_49_32c1 + hfloor_m7_S21_16_49_32c2 * ((206587) / (1000000)) + hfloor_m7_S21_16_49_32c3 * (0)
        + hfloor_m7_S21_16_49_32c4 * (((206587) / (1000000)) * (0))
      = (3976333)
        / (500000000) := by
    simp only [hfloor_m7_S21_16_49_32c1, hfloor_m7_S21_16_49_32c2, hfloor_m7_S21_16_49_32c3, hfloor_m7_S21_16_49_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m7_S21_16_49_32_corner11  :
    0 ≤ hfloor_m7_S21_16_49_32c1 + hfloor_m7_S21_16_49_32c2 * ((206587) / (1000000)) + hfloor_m7_S21_16_49_32c3 * (1)
        + hfloor_m7_S21_16_49_32c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m7_S21_16_49_32c1 + hfloor_m7_S21_16_49_32c2 * ((206587) / (1000000)) + hfloor_m7_S21_16_49_32c3 * (1)
        + hfloor_m7_S21_16_49_32c4 * (((206587) / (1000000)) * (1))
      = (3976333)
        / (500000000) := by
    simp only [hfloor_m7_S21_16_49_32c1, hfloor_m7_S21_16_49_32c2, hfloor_m7_S21_16_49_32c3, hfloor_m7_S21_16_49_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m7_S21_16_49_32_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (500000000 * L - 99317167) / (500000000) := by
  rw [← sub_nonneg, hfloor_m7_S21_16_49_32_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m7_S21_16_49_32_corner00)) ((hfloor_m7_S21_16_49_32_corner01)) ((hfloor_m7_S21_16_49_32_corner10)) ((hfloor_m7_S21_16_49_32_corner11))

/-! ### Instance (piece = 50) -/

noncomputable def hfloor_m7_S49_32_105_64c1 : ℝ :=
  ((-195971649)) / (1000000000)

noncomputable def hfloor_m7_S49_32_105_64c2 : ℝ :=
  1

noncomputable def hfloor_m7_S49_32_105_64c3 : ℝ :=
  0

noncomputable def hfloor_m7_S49_32_105_64c4 : ℝ :=
  0

theorem hfloor_m7_S49_32_105_64_bilinear (L _iv_dummy_HFloors : ℝ) :
    (1000000000 * L - 195971649) / (1000000000) - 0
      = hfloor_m7_S49_32_105_64c1  + hfloor_m7_S49_32_105_64c2  * L + hfloor_m7_S49_32_105_64c3  * _iv_dummy_HFloors
        + hfloor_m7_S49_32_105_64c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m7_S49_32_105_64c1, hfloor_m7_S49_32_105_64c2, hfloor_m7_S49_32_105_64c3, hfloor_m7_S49_32_105_64c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m7_S49_32_105_64_corner00  :
    0 ≤ hfloor_m7_S49_32_105_64c1 + hfloor_m7_S49_32_105_64c2 * ((103293) / (500000)) + hfloor_m7_S49_32_105_64c3 * (0)
        + hfloor_m7_S49_32_105_64c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m7_S49_32_105_64c1 + hfloor_m7_S49_32_105_64c2 * ((103293) / (500000)) + hfloor_m7_S49_32_105_64c3 * (0)
        + hfloor_m7_S49_32_105_64c4 * (((103293) / (500000)) * (0))
      = (10614351)
        / (1000000000) := by
    simp only [hfloor_m7_S49_32_105_64c1, hfloor_m7_S49_32_105_64c2, hfloor_m7_S49_32_105_64c3, hfloor_m7_S49_32_105_64c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m7_S49_32_105_64_corner01  :
    0 ≤ hfloor_m7_S49_32_105_64c1 + hfloor_m7_S49_32_105_64c2 * ((103293) / (500000)) + hfloor_m7_S49_32_105_64c3 * (1)
        + hfloor_m7_S49_32_105_64c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m7_S49_32_105_64c1 + hfloor_m7_S49_32_105_64c2 * ((103293) / (500000)) + hfloor_m7_S49_32_105_64c3 * (1)
        + hfloor_m7_S49_32_105_64c4 * (((103293) / (500000)) * (1))
      = (10614351)
        / (1000000000) := by
    simp only [hfloor_m7_S49_32_105_64c1, hfloor_m7_S49_32_105_64c2, hfloor_m7_S49_32_105_64c3, hfloor_m7_S49_32_105_64c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m7_S49_32_105_64_corner10  :
    0 ≤ hfloor_m7_S49_32_105_64c1 + hfloor_m7_S49_32_105_64c2 * ((206587) / (1000000)) + hfloor_m7_S49_32_105_64c3 * (0)
        + hfloor_m7_S49_32_105_64c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m7_S49_32_105_64c1 + hfloor_m7_S49_32_105_64c2 * ((206587) / (1000000)) + hfloor_m7_S49_32_105_64c3 * (0)
        + hfloor_m7_S49_32_105_64c4 * (((206587) / (1000000)) * (0))
      = (10615351)
        / (1000000000) := by
    simp only [hfloor_m7_S49_32_105_64c1, hfloor_m7_S49_32_105_64c2, hfloor_m7_S49_32_105_64c3, hfloor_m7_S49_32_105_64c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m7_S49_32_105_64_corner11  :
    0 ≤ hfloor_m7_S49_32_105_64c1 + hfloor_m7_S49_32_105_64c2 * ((206587) / (1000000)) + hfloor_m7_S49_32_105_64c3 * (1)
        + hfloor_m7_S49_32_105_64c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m7_S49_32_105_64c1 + hfloor_m7_S49_32_105_64c2 * ((206587) / (1000000)) + hfloor_m7_S49_32_105_64c3 * (1)
        + hfloor_m7_S49_32_105_64c4 * (((206587) / (1000000)) * (1))
      = (10615351)
        / (1000000000) := by
    simp only [hfloor_m7_S49_32_105_64c1, hfloor_m7_S49_32_105_64c2, hfloor_m7_S49_32_105_64c3, hfloor_m7_S49_32_105_64c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m7_S49_32_105_64_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (1000000000 * L - 195971649) / (1000000000) := by
  rw [← sub_nonneg, hfloor_m7_S49_32_105_64_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m7_S49_32_105_64_corner00)) ((hfloor_m7_S49_32_105_64_corner01)) ((hfloor_m7_S49_32_105_64_corner10)) ((hfloor_m7_S49_32_105_64_corner11))

/-! ### Instance (piece = 51) -/

noncomputable def hfloor_m7_S105_64_7_4c1 : ℝ :=
  ((-12201359)) / (62500000)

noncomputable def hfloor_m7_S105_64_7_4c2 : ℝ :=
  1

noncomputable def hfloor_m7_S105_64_7_4c3 : ℝ :=
  0

noncomputable def hfloor_m7_S105_64_7_4c4 : ℝ :=
  0

theorem hfloor_m7_S105_64_7_4_bilinear (L _iv_dummy_HFloors : ℝ) :
    (62500000 * L - 12201359) / (62500000) - 0
      = hfloor_m7_S105_64_7_4c1  + hfloor_m7_S105_64_7_4c2  * L + hfloor_m7_S105_64_7_4c3  * _iv_dummy_HFloors
        + hfloor_m7_S105_64_7_4c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m7_S105_64_7_4c1, hfloor_m7_S105_64_7_4c2, hfloor_m7_S105_64_7_4c3, hfloor_m7_S105_64_7_4c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m7_S105_64_7_4_corner00  :
    0 ≤ hfloor_m7_S105_64_7_4c1 + hfloor_m7_S105_64_7_4c2 * ((103293) / (500000)) + hfloor_m7_S105_64_7_4c3 * (0)
        + hfloor_m7_S105_64_7_4c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m7_S105_64_7_4c1 + hfloor_m7_S105_64_7_4c2 * ((103293) / (500000)) + hfloor_m7_S105_64_7_4c3 * (0)
        + hfloor_m7_S105_64_7_4c4 * (((103293) / (500000)) * (0))
      = (355133)
        / (31250000) := by
    simp only [hfloor_m7_S105_64_7_4c1, hfloor_m7_S105_64_7_4c2, hfloor_m7_S105_64_7_4c3, hfloor_m7_S105_64_7_4c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m7_S105_64_7_4_corner01  :
    0 ≤ hfloor_m7_S105_64_7_4c1 + hfloor_m7_S105_64_7_4c2 * ((103293) / (500000)) + hfloor_m7_S105_64_7_4c3 * (1)
        + hfloor_m7_S105_64_7_4c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m7_S105_64_7_4c1 + hfloor_m7_S105_64_7_4c2 * ((103293) / (500000)) + hfloor_m7_S105_64_7_4c3 * (1)
        + hfloor_m7_S105_64_7_4c4 * (((103293) / (500000)) * (1))
      = (355133)
        / (31250000) := by
    simp only [hfloor_m7_S105_64_7_4c1, hfloor_m7_S105_64_7_4c2, hfloor_m7_S105_64_7_4c3, hfloor_m7_S105_64_7_4c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m7_S105_64_7_4_corner10  :
    0 ≤ hfloor_m7_S105_64_7_4c1 + hfloor_m7_S105_64_7_4c2 * ((206587) / (1000000)) + hfloor_m7_S105_64_7_4c3 * (0)
        + hfloor_m7_S105_64_7_4c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m7_S105_64_7_4c1 + hfloor_m7_S105_64_7_4c2 * ((206587) / (1000000)) + hfloor_m7_S105_64_7_4c3 * (0)
        + hfloor_m7_S105_64_7_4c4 * (((206587) / (1000000)) * (0))
      = (1420657)
        / (125000000) := by
    simp only [hfloor_m7_S105_64_7_4c1, hfloor_m7_S105_64_7_4c2, hfloor_m7_S105_64_7_4c3, hfloor_m7_S105_64_7_4c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m7_S105_64_7_4_corner11  :
    0 ≤ hfloor_m7_S105_64_7_4c1 + hfloor_m7_S105_64_7_4c2 * ((206587) / (1000000)) + hfloor_m7_S105_64_7_4c3 * (1)
        + hfloor_m7_S105_64_7_4c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m7_S105_64_7_4c1 + hfloor_m7_S105_64_7_4c2 * ((206587) / (1000000)) + hfloor_m7_S105_64_7_4c3 * (1)
        + hfloor_m7_S105_64_7_4c4 * (((206587) / (1000000)) * (1))
      = (1420657)
        / (125000000) := by
    simp only [hfloor_m7_S105_64_7_4c1, hfloor_m7_S105_64_7_4c2, hfloor_m7_S105_64_7_4c3, hfloor_m7_S105_64_7_4c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m7_S105_64_7_4_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (62500000 * L - 12201359) / (62500000) := by
  rw [← sub_nonneg, hfloor_m7_S105_64_7_4_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m7_S105_64_7_4_corner00)) ((hfloor_m7_S105_64_7_4_corner01)) ((hfloor_m7_S105_64_7_4_corner10)) ((hfloor_m7_S105_64_7_4_corner11))

/-! ### Instance (piece = 52) -/

noncomputable def hfloor_m7_S7_4_63_32c1 : ℝ :=
  ((-205378409)) / (1000000000)

noncomputable def hfloor_m7_S7_4_63_32c2 : ℝ :=
  1

noncomputable def hfloor_m7_S7_4_63_32c3 : ℝ :=
  0

noncomputable def hfloor_m7_S7_4_63_32c4 : ℝ :=
  0

theorem hfloor_m7_S7_4_63_32_bilinear (L _iv_dummy_HFloors : ℝ) :
    (1000000000 * L - 205378409) / (1000000000) - 0
      = hfloor_m7_S7_4_63_32c1  + hfloor_m7_S7_4_63_32c2  * L + hfloor_m7_S7_4_63_32c3  * _iv_dummy_HFloors
        + hfloor_m7_S7_4_63_32c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m7_S7_4_63_32c1, hfloor_m7_S7_4_63_32c2, hfloor_m7_S7_4_63_32c3, hfloor_m7_S7_4_63_32c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m7_S7_4_63_32_corner00  :
    0 ≤ hfloor_m7_S7_4_63_32c1 + hfloor_m7_S7_4_63_32c2 * ((103293) / (500000)) + hfloor_m7_S7_4_63_32c3 * (0)
        + hfloor_m7_S7_4_63_32c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m7_S7_4_63_32c1 + hfloor_m7_S7_4_63_32c2 * ((103293) / (500000)) + hfloor_m7_S7_4_63_32c3 * (0)
        + hfloor_m7_S7_4_63_32c4 * (((103293) / (500000)) * (0))
      = (1207591)
        / (1000000000) := by
    simp only [hfloor_m7_S7_4_63_32c1, hfloor_m7_S7_4_63_32c2, hfloor_m7_S7_4_63_32c3, hfloor_m7_S7_4_63_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m7_S7_4_63_32_corner01  :
    0 ≤ hfloor_m7_S7_4_63_32c1 + hfloor_m7_S7_4_63_32c2 * ((103293) / (500000)) + hfloor_m7_S7_4_63_32c3 * (1)
        + hfloor_m7_S7_4_63_32c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m7_S7_4_63_32c1 + hfloor_m7_S7_4_63_32c2 * ((103293) / (500000)) + hfloor_m7_S7_4_63_32c3 * (1)
        + hfloor_m7_S7_4_63_32c4 * (((103293) / (500000)) * (1))
      = (1207591)
        / (1000000000) := by
    simp only [hfloor_m7_S7_4_63_32c1, hfloor_m7_S7_4_63_32c2, hfloor_m7_S7_4_63_32c3, hfloor_m7_S7_4_63_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m7_S7_4_63_32_corner10  :
    0 ≤ hfloor_m7_S7_4_63_32c1 + hfloor_m7_S7_4_63_32c2 * ((206587) / (1000000)) + hfloor_m7_S7_4_63_32c3 * (0)
        + hfloor_m7_S7_4_63_32c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m7_S7_4_63_32c1 + hfloor_m7_S7_4_63_32c2 * ((206587) / (1000000)) + hfloor_m7_S7_4_63_32c3 * (0)
        + hfloor_m7_S7_4_63_32c4 * (((206587) / (1000000)) * (0))
      = (1208591)
        / (1000000000) := by
    simp only [hfloor_m7_S7_4_63_32c1, hfloor_m7_S7_4_63_32c2, hfloor_m7_S7_4_63_32c3, hfloor_m7_S7_4_63_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m7_S7_4_63_32_corner11  :
    0 ≤ hfloor_m7_S7_4_63_32c1 + hfloor_m7_S7_4_63_32c2 * ((206587) / (1000000)) + hfloor_m7_S7_4_63_32c3 * (1)
        + hfloor_m7_S7_4_63_32c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m7_S7_4_63_32c1 + hfloor_m7_S7_4_63_32c2 * ((206587) / (1000000)) + hfloor_m7_S7_4_63_32c3 * (1)
        + hfloor_m7_S7_4_63_32c4 * (((206587) / (1000000)) * (1))
      = (1208591)
        / (1000000000) := by
    simp only [hfloor_m7_S7_4_63_32c1, hfloor_m7_S7_4_63_32c2, hfloor_m7_S7_4_63_32c3, hfloor_m7_S7_4_63_32c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m7_S7_4_63_32_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (1000000000 * L - 205378409) / (1000000000) := by
  rw [← sub_nonneg, hfloor_m7_S7_4_63_32_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m7_S7_4_63_32_corner00)) ((hfloor_m7_S7_4_63_32_corner01)) ((hfloor_m7_S7_4_63_32_corner10)) ((hfloor_m7_S7_4_63_32_corner11))

/-! ### Instance (piece = 53) -/

noncomputable def hfloor_m7_S63_32_35_16c1 : ℝ :=
  ((-46371109)) / (250000000)

noncomputable def hfloor_m7_S63_32_35_16c2 : ℝ :=
  1

noncomputable def hfloor_m7_S63_32_35_16c3 : ℝ :=
  0

noncomputable def hfloor_m7_S63_32_35_16c4 : ℝ :=
  0

theorem hfloor_m7_S63_32_35_16_bilinear (L _iv_dummy_HFloors : ℝ) :
    (250000000 * L - 46371109) / (250000000) - 0
      = hfloor_m7_S63_32_35_16c1  + hfloor_m7_S63_32_35_16c2  * L + hfloor_m7_S63_32_35_16c3  * _iv_dummy_HFloors
        + hfloor_m7_S63_32_35_16c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m7_S63_32_35_16c1, hfloor_m7_S63_32_35_16c2, hfloor_m7_S63_32_35_16c3, hfloor_m7_S63_32_35_16c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m7_S63_32_35_16_corner00  :
    0 ≤ hfloor_m7_S63_32_35_16c1 + hfloor_m7_S63_32_35_16c2 * ((103293) / (500000)) + hfloor_m7_S63_32_35_16c3 * (0)
        + hfloor_m7_S63_32_35_16c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m7_S63_32_35_16c1 + hfloor_m7_S63_32_35_16c2 * ((103293) / (500000)) + hfloor_m7_S63_32_35_16c3 * (0)
        + hfloor_m7_S63_32_35_16c4 * (((103293) / (500000)) * (0))
      = (5275391)
        / (250000000) := by
    simp only [hfloor_m7_S63_32_35_16c1, hfloor_m7_S63_32_35_16c2, hfloor_m7_S63_32_35_16c3, hfloor_m7_S63_32_35_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m7_S63_32_35_16_corner01  :
    0 ≤ hfloor_m7_S63_32_35_16c1 + hfloor_m7_S63_32_35_16c2 * ((103293) / (500000)) + hfloor_m7_S63_32_35_16c3 * (1)
        + hfloor_m7_S63_32_35_16c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m7_S63_32_35_16c1 + hfloor_m7_S63_32_35_16c2 * ((103293) / (500000)) + hfloor_m7_S63_32_35_16c3 * (1)
        + hfloor_m7_S63_32_35_16c4 * (((103293) / (500000)) * (1))
      = (5275391)
        / (250000000) := by
    simp only [hfloor_m7_S63_32_35_16c1, hfloor_m7_S63_32_35_16c2, hfloor_m7_S63_32_35_16c3, hfloor_m7_S63_32_35_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m7_S63_32_35_16_corner10  :
    0 ≤ hfloor_m7_S63_32_35_16c1 + hfloor_m7_S63_32_35_16c2 * ((206587) / (1000000)) + hfloor_m7_S63_32_35_16c3 * (0)
        + hfloor_m7_S63_32_35_16c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m7_S63_32_35_16c1 + hfloor_m7_S63_32_35_16c2 * ((206587) / (1000000)) + hfloor_m7_S63_32_35_16c3 * (0)
        + hfloor_m7_S63_32_35_16c4 * (((206587) / (1000000)) * (0))
      = (5275641)
        / (250000000) := by
    simp only [hfloor_m7_S63_32_35_16c1, hfloor_m7_S63_32_35_16c2, hfloor_m7_S63_32_35_16c3, hfloor_m7_S63_32_35_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m7_S63_32_35_16_corner11  :
    0 ≤ hfloor_m7_S63_32_35_16c1 + hfloor_m7_S63_32_35_16c2 * ((206587) / (1000000)) + hfloor_m7_S63_32_35_16c3 * (1)
        + hfloor_m7_S63_32_35_16c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m7_S63_32_35_16c1 + hfloor_m7_S63_32_35_16c2 * ((206587) / (1000000)) + hfloor_m7_S63_32_35_16c3 * (1)
        + hfloor_m7_S63_32_35_16c4 * (((206587) / (1000000)) * (1))
      = (5275641)
        / (250000000) := by
    simp only [hfloor_m7_S63_32_35_16c1, hfloor_m7_S63_32_35_16c2, hfloor_m7_S63_32_35_16c3, hfloor_m7_S63_32_35_16c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m7_S63_32_35_16_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (250000000 * L - 46371109) / (250000000) := by
  rw [← sub_nonneg, hfloor_m7_S63_32_35_16_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m7_S63_32_35_16_corner00)) ((hfloor_m7_S63_32_35_16_corner01)) ((hfloor_m7_S63_32_35_16_corner10)) ((hfloor_m7_S63_32_35_16_corner11))

/-! ### Instance (piece = 54) -/

noncomputable def hfloor_m7_S35_16_21_8c1 : ℝ :=
  ((-179407673)) / (1000000000)

noncomputable def hfloor_m7_S35_16_21_8c2 : ℝ :=
  1

noncomputable def hfloor_m7_S35_16_21_8c3 : ℝ :=
  0

noncomputable def hfloor_m7_S35_16_21_8c4 : ℝ :=
  0

theorem hfloor_m7_S35_16_21_8_bilinear (L _iv_dummy_HFloors : ℝ) :
    (1000000000 * L - 179407673) / (1000000000) - 0
      = hfloor_m7_S35_16_21_8c1  + hfloor_m7_S35_16_21_8c2  * L + hfloor_m7_S35_16_21_8c3  * _iv_dummy_HFloors
        + hfloor_m7_S35_16_21_8c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m7_S35_16_21_8c1, hfloor_m7_S35_16_21_8c2, hfloor_m7_S35_16_21_8c3, hfloor_m7_S35_16_21_8c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m7_S35_16_21_8_corner00  :
    0 ≤ hfloor_m7_S35_16_21_8c1 + hfloor_m7_S35_16_21_8c2 * ((103293) / (500000)) + hfloor_m7_S35_16_21_8c3 * (0)
        + hfloor_m7_S35_16_21_8c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m7_S35_16_21_8c1 + hfloor_m7_S35_16_21_8c2 * ((103293) / (500000)) + hfloor_m7_S35_16_21_8c3 * (0)
        + hfloor_m7_S35_16_21_8c4 * (((103293) / (500000)) * (0))
      = (27178327)
        / (1000000000) := by
    simp only [hfloor_m7_S35_16_21_8c1, hfloor_m7_S35_16_21_8c2, hfloor_m7_S35_16_21_8c3, hfloor_m7_S35_16_21_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m7_S35_16_21_8_corner01  :
    0 ≤ hfloor_m7_S35_16_21_8c1 + hfloor_m7_S35_16_21_8c2 * ((103293) / (500000)) + hfloor_m7_S35_16_21_8c3 * (1)
        + hfloor_m7_S35_16_21_8c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m7_S35_16_21_8c1 + hfloor_m7_S35_16_21_8c2 * ((103293) / (500000)) + hfloor_m7_S35_16_21_8c3 * (1)
        + hfloor_m7_S35_16_21_8c4 * (((103293) / (500000)) * (1))
      = (27178327)
        / (1000000000) := by
    simp only [hfloor_m7_S35_16_21_8c1, hfloor_m7_S35_16_21_8c2, hfloor_m7_S35_16_21_8c3, hfloor_m7_S35_16_21_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m7_S35_16_21_8_corner10  :
    0 ≤ hfloor_m7_S35_16_21_8c1 + hfloor_m7_S35_16_21_8c2 * ((206587) / (1000000)) + hfloor_m7_S35_16_21_8c3 * (0)
        + hfloor_m7_S35_16_21_8c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m7_S35_16_21_8c1 + hfloor_m7_S35_16_21_8c2 * ((206587) / (1000000)) + hfloor_m7_S35_16_21_8c3 * (0)
        + hfloor_m7_S35_16_21_8c4 * (((206587) / (1000000)) * (0))
      = (27179327)
        / (1000000000) := by
    simp only [hfloor_m7_S35_16_21_8c1, hfloor_m7_S35_16_21_8c2, hfloor_m7_S35_16_21_8c3, hfloor_m7_S35_16_21_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m7_S35_16_21_8_corner11  :
    0 ≤ hfloor_m7_S35_16_21_8c1 + hfloor_m7_S35_16_21_8c2 * ((206587) / (1000000)) + hfloor_m7_S35_16_21_8c3 * (1)
        + hfloor_m7_S35_16_21_8c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m7_S35_16_21_8c1 + hfloor_m7_S35_16_21_8c2 * ((206587) / (1000000)) + hfloor_m7_S35_16_21_8c3 * (1)
        + hfloor_m7_S35_16_21_8c4 * (((206587) / (1000000)) * (1))
      = (27179327)
        / (1000000000) := by
    simp only [hfloor_m7_S35_16_21_8c1, hfloor_m7_S35_16_21_8c2, hfloor_m7_S35_16_21_8c3, hfloor_m7_S35_16_21_8c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m7_S35_16_21_8_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (1000000000 * L - 179407673) / (1000000000) := by
  rw [← sub_nonneg, hfloor_m7_S35_16_21_8_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m7_S35_16_21_8_corner00)) ((hfloor_m7_S35_16_21_8_corner01)) ((hfloor_m7_S35_16_21_8_corner10)) ((hfloor_m7_S35_16_21_8_corner11))

/-! ### Instance (piece = 55) -/

noncomputable def hfloor_m7_S21_8_7_2c1 : ℝ :=
  ((-162294993)) / (1000000000)

noncomputable def hfloor_m7_S21_8_7_2c2 : ℝ :=
  1

noncomputable def hfloor_m7_S21_8_7_2c3 : ℝ :=
  0

noncomputable def hfloor_m7_S21_8_7_2c4 : ℝ :=
  0

theorem hfloor_m7_S21_8_7_2_bilinear (L _iv_dummy_HFloors : ℝ) :
    (1000000000 * L - 162294993) / (1000000000) - 0
      = hfloor_m7_S21_8_7_2c1  + hfloor_m7_S21_8_7_2c2  * L + hfloor_m7_S21_8_7_2c3  * _iv_dummy_HFloors
        + hfloor_m7_S21_8_7_2c4  * (L * _iv_dummy_HFloors) := by
  simp only [hfloor_m7_S21_8_7_2c1, hfloor_m7_S21_8_7_2c2, hfloor_m7_S21_8_7_2c3, hfloor_m7_S21_8_7_2c4]
  push_cast
  field_simp
  try ring

theorem hfloor_m7_S21_8_7_2_corner00  :
    0 ≤ hfloor_m7_S21_8_7_2c1 + hfloor_m7_S21_8_7_2c2 * ((103293) / (500000)) + hfloor_m7_S21_8_7_2c3 * (0)
        + hfloor_m7_S21_8_7_2c4 * (((103293) / (500000)) * (0)) := by
  have hkey : hfloor_m7_S21_8_7_2c1 + hfloor_m7_S21_8_7_2c2 * ((103293) / (500000)) + hfloor_m7_S21_8_7_2c3 * (0)
        + hfloor_m7_S21_8_7_2c4 * (((103293) / (500000)) * (0))
      = (44291007)
        / (1000000000) := by
    simp only [hfloor_m7_S21_8_7_2c1, hfloor_m7_S21_8_7_2c2, hfloor_m7_S21_8_7_2c3, hfloor_m7_S21_8_7_2c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m7_S21_8_7_2_corner01  :
    0 ≤ hfloor_m7_S21_8_7_2c1 + hfloor_m7_S21_8_7_2c2 * ((103293) / (500000)) + hfloor_m7_S21_8_7_2c3 * (1)
        + hfloor_m7_S21_8_7_2c4 * (((103293) / (500000)) * (1)) := by
  have hkey : hfloor_m7_S21_8_7_2c1 + hfloor_m7_S21_8_7_2c2 * ((103293) / (500000)) + hfloor_m7_S21_8_7_2c3 * (1)
        + hfloor_m7_S21_8_7_2c4 * (((103293) / (500000)) * (1))
      = (44291007)
        / (1000000000) := by
    simp only [hfloor_m7_S21_8_7_2c1, hfloor_m7_S21_8_7_2c2, hfloor_m7_S21_8_7_2c3, hfloor_m7_S21_8_7_2c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m7_S21_8_7_2_corner10  :
    0 ≤ hfloor_m7_S21_8_7_2c1 + hfloor_m7_S21_8_7_2c2 * ((206587) / (1000000)) + hfloor_m7_S21_8_7_2c3 * (0)
        + hfloor_m7_S21_8_7_2c4 * (((206587) / (1000000)) * (0)) := by
  have hkey : hfloor_m7_S21_8_7_2c1 + hfloor_m7_S21_8_7_2c2 * ((206587) / (1000000)) + hfloor_m7_S21_8_7_2c3 * (0)
        + hfloor_m7_S21_8_7_2c4 * (((206587) / (1000000)) * (0))
      = (44292007)
        / (1000000000) := by
    simp only [hfloor_m7_S21_8_7_2c1, hfloor_m7_S21_8_7_2c2, hfloor_m7_S21_8_7_2c3, hfloor_m7_S21_8_7_2c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m7_S21_8_7_2_corner11  :
    0 ≤ hfloor_m7_S21_8_7_2c1 + hfloor_m7_S21_8_7_2c2 * ((206587) / (1000000)) + hfloor_m7_S21_8_7_2c3 * (1)
        + hfloor_m7_S21_8_7_2c4 * (((206587) / (1000000)) * (1)) := by
  have hkey : hfloor_m7_S21_8_7_2c1 + hfloor_m7_S21_8_7_2c2 * ((206587) / (1000000)) + hfloor_m7_S21_8_7_2c3 * (1)
        + hfloor_m7_S21_8_7_2c4 * (((206587) / (1000000)) * (1))
      = (44292007)
        / (1000000000) := by
    simp only [hfloor_m7_S21_8_7_2c1, hfloor_m7_S21_8_7_2c2, hfloor_m7_S21_8_7_2c3, hfloor_m7_S21_8_7_2c4]
    field_simp
    try ring
  rw [hkey]
  positivity

theorem hfloor_m7_S21_8_7_2_cell (L _iv_dummy_HFloors : ℝ)
    (hQ0 : ((103293) / (500000)) ≤ L) (hQ1 : L ≤ ((206587) / (1000000)))
    (hS0 : 0 ≤ _iv_dummy_HFloors) (hS1 : _iv_dummy_HFloors ≤ (1)) :
    0 ≤ (1000000000 * L - 162294993) / (1000000000) := by
  rw [← sub_nonneg, hfloor_m7_S21_8_7_2_bilinear L _iv_dummy_HFloors]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ((hfloor_m7_S21_8_7_2_corner00)) ((hfloor_m7_S21_8_7_2_corner01)) ((hfloor_m7_S21_8_7_2_corner10)) ((hfloor_m7_S21_8_7_2_corner11))

end HFloor
end G1
