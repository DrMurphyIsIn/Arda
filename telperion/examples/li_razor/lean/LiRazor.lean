/-
LiRazor — the geometric heart of the Li-positivity crux, in the kernel.

RH is equivalent (li_criterion_rh_iff) to `∀ n, 0 ≤ Re (taylorCoeff riemannXi n)`, where the
Li coefficient is a sum over zeros of the summand `1 − (1 − 1/ρ)^n`.  This file isolates WHY
that criterion is a RAZOR — true iff RH, with no "almost" — rather than an approximable bound:

    a zero ρ lies on the critical line  ⇔  its base (1 − 1/ρ) lies exactly on the UNIT CIRCLE.

Off the line the base is off the circle, and the summand's size is exactly rⁿ with r ≠ 1
(li_summand_normSq_pow) — a single off-line zero on the LEFT (Re < 1/2) gives r > 1, i.e.
geometric BLOW-UP that no finite prefix of rungs can see but the `∀ n` does.  This is the exact
mechanism by which the finite faces (li_rung_0..19, each an Arb enclosure) are provable while the
uniform crux is RH itself.

conjecture1_proved = False.  These are unconditional facts about the geometry of the criterion;
they explain the wall, they do not breach it.  The missing bound is "every base is on the circle"
— which is RH.
-/
import Mathlib

open Complex

namespace LiRazor

/-- **Reality ⇔ unit circle.**  For a nonzero `ρ`, the Li-summand base `1 − 1/ρ` has
`normSq = 1` (lies on the unit circle) exactly when `Re ρ = 1/2`. -/
theorem critical_line_iff_unit_normSq (ρ : ℂ) (hρ : ρ ≠ 0) :
    Complex.normSq (1 - 1 / ρ) = 1 ↔ ρ.re = 1 / 2 := by
  have hρ2 : Complex.normSq ρ ≠ 0 := by simpa [Complex.normSq_eq_zero] using hρ
  have h1 : (1 : ℂ) - 1 / ρ = (ρ - 1) / ρ := by field_simp
  rw [h1, Complex.normSq_div, div_eq_one_iff_eq hρ2]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  constructor
  · intro h; nlinarith [h]
  · intro h; nlinarith [h]

/-- **Off-line LEFT ⇔ outside the circle.**  `Re ρ < 1/2` iff the base is OUTSIDE the unit
circle (`normSq > 1`) — the geometric-blow-up side. -/
theorem left_of_line_iff_outside (ρ : ℂ) (hρ : ρ ≠ 0) :
    1 < Complex.normSq (1 - 1 / ρ) ↔ ρ.re < 1 / 2 := by
  have hρ2 : (0 : ℝ) < Complex.normSq ρ := Complex.normSq_pos.mpr hρ
  have h1 : (1 : ℂ) - 1 / ρ = (ρ - 1) / ρ := by field_simp
  rw [h1, Complex.normSq_div, lt_div_iff₀ hρ2, one_mul]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  constructor
  · intro h; nlinarith [h]
  · intro h; nlinarith [h]

/-- **Off-line RIGHT ⇔ inside the circle.**  `1/2 < Re ρ` iff the base is INSIDE the unit
circle (`normSq < 1`) — the geometric-decay side. -/
theorem right_of_line_iff_inside (ρ : ℂ) (hρ : ρ ≠ 0) :
    Complex.normSq (1 - 1 / ρ) < 1 ↔ 1 / 2 < ρ.re := by
  have hρ2 : (0 : ℝ) < Complex.normSq ρ := Complex.normSq_pos.mpr hρ
  have h1 : (1 : ℂ) - 1 / ρ = (ρ - 1) / ρ := by field_simp
  rw [h1, Complex.normSq_div, div_lt_one hρ2]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  constructor
  · intro h; nlinarith [h]
  · intro h; nlinarith [h]

/-- **The summand's size is exactly rⁿ.**  The `n`-th Li summand base to the `n` has
`normSq = (normSq base)ⁿ` — so its magnitude is governed purely by whether the base is on,
inside, or outside the unit circle. -/
theorem li_summand_normSq_pow (ρ : ℂ) (n : ℕ) :
    Complex.normSq ((1 - 1 / ρ) ^ n) = (Complex.normSq (1 - 1 / ρ)) ^ n :=
  map_pow Complex.normSq _ n

/-- **THE RAZOR.**  A single off-line-LEFT zero (`Re ρ < 1/2`) makes the Li-summand base sit
OUTSIDE the unit circle, so the summand magnitude `normSq((1−1/ρ)ⁿ) = rⁿ` with `r > 1` grows
geometrically in `n`.  No finite prefix of Li rungs detects it; the `∀ n` criterion does.  This
is why Li positivity is equivalent to RH and not approximable — reality is `r = 1` exactly. -/
theorem offline_left_geometric_blowup (ρ : ℂ) (hρ : ρ ≠ 0) (hoff : ρ.re < 1 / 2) :
    1 < Complex.normSq (1 - 1 / ρ)
      ∧ ∀ n : ℕ, Complex.normSq ((1 - 1 / ρ) ^ n) = (Complex.normSq (1 - 1 / ρ)) ^ n := by
  refine ⟨(left_of_line_iff_outside ρ hρ).mpr hoff, fun n => li_summand_normSq_pow ρ n⟩

end LiRazor

#print axioms LiRazor.critical_line_iff_unit_normSq
#print axioms LiRazor.left_of_line_iff_outside
#print axioms LiRazor.right_of_line_iff_inside
#print axioms LiRazor.li_summand_normSq_pow
#print axioms LiRazor.offline_left_geometric_blowup
