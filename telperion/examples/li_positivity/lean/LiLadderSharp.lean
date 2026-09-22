/-
LiLadderSharp -- the SHARPENED exchange rate of the Li ladder.

Campaign brief: telperion/docs/LI_FACE_BRIEF_2026-09-21.md (workstream li-rung0, follow-up).
Builds on `LiLadderHeight` (Lemmas A, A', B; Theorems C, D there).  Hand-written, not emitted.

Numerics put the true termwise threshold at |Im rho| = N/(2 pi) + 1/2 + o(1) (attained as
beta -> 0).  This module proves the matching kernel statement: a zero at height
|Im rho| >= 1 contributes a nonnegative term to rung n = N - 1 as soon as
N <= 2 pi (|Im rho| - 1/2), so height T buys every rung with n + 1 <= 2 pi (T - 1/2)
(against 3 pi T / 2 in `LiLadderHeight`; at T = 4000: rungs 0..25128 instead of 0..18848).

  1. Lemma A'' `cosh_mul_cos_le_one_window`: if 3 pi/2 < |b| <= 2 pi and |a| <= 2 pi - |b| then
     cosh a * cos b <= 1.  With d = 2 pi - |b| in [0, pi/2), cos b = cos d and Lemma A applies
     to (a, d).
  2. Lemma B'' `abs_arg_add_abs_log_le`: for 0 < Re z < 1 and |Im z| >= 1,
        |arg u| + |log|u|| <= 1/|Im z| + 1/(2 (Im z)^2) <= 1/(|Im z| - 1/2),   u = 1 - 1/z,
     from the two halves of Lemma B and the algebraic fact (2g+1)(2g-1) <= 4 g^2.
  3. Theorem C'' `re_liPairedSummand_nonneg_of_height_sharp`: |Im rho| >= 1 and
     N <= 2 pi (|Im rho| - 1/2) give 0 <= Re (liPairedSummand n rho).  With b = N |arg u| and
     a = N log|u|: b <= 3 pi/2 is Lemma A' (|a| <= b by Lemma B); b > 3 pi/2 has
     |a| + b <= N (|log|u|| + |arg u|) <= N/(|Im rho| - 1/2) <= 2 pi, so Lemma A'' applies.
  4. Theorem D'' `li_rung_of_zeros_on_line_below_sharp`: zeros on the line up to height T >= 1
     buy every rung with n + 1 <= 2 pi (T - 1/2).  Conditional on the line hypothesis.
  5. The height-4000 composition, sharp: `li_rungs_of_bands_4000_sharp` and
     `li_rungs_of_bands_4000_upto_sharp` (rungs 0..25128; 7999 pi > 25129 needs `pi_gt_d6`),
     under the capstone's conclusion shape only (real-zero residual discharged in
     `LiLadderHeight` from the li-box module).

conjecture1_proved = False.  Nothing here proves, or approaches, the Riemann Hypothesis: every
theorem is a finite real inequality or an implication from a named zero-localisation hypothesis;
the uniform `forall n` IS RH (upstream `li_criterion_rh_iff`) and is not touched.
-/
import Mathlib
import LiLadderHeight

open scoped Real

namespace LiLadderHeight

open LiCriterion

/-! ### 1. Lemma A'': the window `3 pi/2 < |b| <= 2 pi` -/

/-- **Lemma A''.**  If `3 pi/2 < |b| <= 2 pi` and `|a| <= 2 pi - |b|` then `cosh a * cos b <= 1`. -/
theorem cosh_mul_cos_le_one_window {a b : ℝ} (hb1 : 3 * π / 2 < |b|) (hb2 : |b| ≤ 2 * π)
    (ha : |a| ≤ 2 * π - |b|) : Real.cosh a * Real.cos b ≤ 1 := by
  have hd0 : 0 ≤ 2 * π - |b| := by linarith
  have hd : abs (2 * π - |b|) ≤ π / 2 := by
    rw [abs_of_nonneg hd0]; linarith
  have hcos : Real.cos b = Real.cos (2 * π - |b|) := by
    rw [Real.cos_two_pi_sub, Real.cos_abs]
  rw [hcos]
  exact cosh_mul_cos_le_one (ha.trans (le_abs_self _)) hd

/-! ### 2. Lemma B'': the combined angle-plus-log bound -/

/-- `1/g + 1/(2 g^2) <= 1/(g - 1/2)` for `g > 1/2` (i.e. `(2g+1)(2g-1) <= 4g^2`). -/
lemma one_div_add_one_div_two_sq_le {g : ℝ} (hg : 1 / 2 < g) :
    1 / g + 1 / (2 * g ^ 2) ≤ 1 / (g - 1 / 2) := by
  have hg0 : 0 < g := by linarith
  have h1 : 1 / g + 1 / (2 * g ^ 2) = (2 * g + 1) / (2 * g ^ 2) := by
    field_simp
  rw [h1, div_le_div_iff₀ (by positivity) (by linarith)]
  nlinarith

/-- **Lemma B''.**  For `0 < Re z < 1` and `|Im z| >= 1`, with `u = 1 - 1/z`,
`|arg u| + |log|u|| <= 1/(|Im z| - 1/2)`. -/
theorem abs_arg_add_abs_log_le (z : ℂ) (h0 : 0 < z.re) (h1 : z.re < 1) (hγ : 1 ≤ |z.im|) :
    |Complex.arg ((1 : ℂ) - 1 / z)| + |Real.log ‖(1 : ℂ) - 1 / z‖| ≤ 1 / (|z.im| - 1 / 2) := by
  have hγ0 : z.im ≠ 0 := by
    intro h; rw [h] at hγ; norm_num at hγ
  have harg := abs_arg_base_le z h0 h1 hγ
  have hlog := abs_log_norm_one_sub_inv_le z h0 h1 hγ0
  have hsq : z.im ^ 2 = |z.im| ^ 2 := (sq_abs z.im).symm
  rw [hsq] at hlog
  have halg := one_div_add_one_div_two_sq_le (g := |z.im|) (by linarith)
  linarith

/-! ### 3. Theorem C'': the sharp termwise threshold -/

/-- **Theorem C''.**  A nontrivial zero with `|Im rho| >= 1` and
`n + 1 <= 2 pi (|Im rho| - 1/2)` contributes a nonnegative term to rung `n`, on or off the
line. -/
theorem re_liPairedSummand_nonneg_of_height_sharp (n : ℕ) (ρ : NontrivialZero)
    (h1 : 1 ≤ |ρ.val.im|) (hN : ((n : ℝ) + 1) ≤ 2 * π * (|ρ.val.im| - 1 / 2)) :
    0 ≤ (liPairedSummand n ρ).re := by
  rw [re_liPairedSummand_eq]
  have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hNn : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have hg : 0 < |ρ.val.im| - 1 / 2 := by linarith
  -- |a| <= |b|
  have hab0 := abs_log_norm_le_abs_arg ρ.val ρ.property.2.1 ρ.property.2.2 h1
  have hab : |((n + 1 : ℕ) : ℝ) * Real.log ‖(1 : ℂ) - 1 / ρ.val‖|
      ≤ |((n + 1 : ℕ) : ℝ) * Complex.arg ((1 : ℂ) - 1 / ρ.val)| := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left hab0 (abs_nonneg _)
  -- |a| + |b| <= N / (|Im| - 1/2) <= 2 pi
  have hsum0 := abs_arg_add_abs_log_le ρ.val ρ.property.2.1 ρ.property.2.2 h1
  have hsum : |((n + 1 : ℕ) : ℝ) * Real.log ‖(1 : ℂ) - 1 / ρ.val‖|
      + |((n + 1 : ℕ) : ℝ) * Complex.arg ((1 : ℂ) - 1 / ρ.val)| ≤ 2 * π := by
    rw [abs_mul, abs_mul, abs_of_pos hNpos]
    calc ((n + 1 : ℕ) : ℝ) * |Real.log ‖(1 : ℂ) - 1 / ρ.val‖|
          + ((n + 1 : ℕ) : ℝ) * |Complex.arg ((1 : ℂ) - 1 / ρ.val)|
        = ((n + 1 : ℕ) : ℝ) * (|Complex.arg ((1 : ℂ) - 1 / ρ.val)|
            + |Real.log ‖(1 : ℂ) - 1 / ρ.val‖|) := by ring
      _ ≤ ((n + 1 : ℕ) : ℝ) * (1 / (|ρ.val.im| - 1 / 2)) :=
          mul_le_mul_of_nonneg_left hsum0 hNpos.le
      _ ≤ 2 * π := by
          rw [mul_one_div, div_le_iff₀ hg, hNn]
          linarith
  rcases le_or_gt |((n + 1 : ℕ) : ℝ) * Complex.arg ((1 : ℂ) - 1 / ρ.val)| (3 * π / 2)
    with hsmall | hbig
  · have := cosh_mul_cos_le_one_of_le_three_pi_div_two hab hsmall
    linarith
  · have hb2 : |((n + 1 : ℕ) : ℝ) * Complex.arg ((1 : ℂ) - 1 / ρ.val)| ≤ 2 * π := by
      linarith [abs_nonneg (((n + 1 : ℕ) : ℝ) * Real.log ‖(1 : ℂ) - 1 / ρ.val‖)]
    have ha : |((n + 1 : ℕ) : ℝ) * Real.log ‖(1 : ℂ) - 1 / ρ.val‖|
        ≤ 2 * π - |((n + 1 : ℕ) : ℝ) * Complex.arg ((1 : ℂ) - 1 / ρ.val)| := by linarith
    have := cosh_mul_cos_le_one_window hbig hb2 ha
    linarith

/-! ### 4. Theorem D'': the sharp ladder -/

/-- **Theorem D''.**  Let `T >= 1`.  If every nontrivial zero with `|Im rho| <= T` has real part
`1/2`, then `0 <= Re (taylorCoeff riemannXi n)` for every rung `n` with
`n + 1 <= 2 pi (T - 1/2)`.  Conditional; proves nothing about RH. -/
theorem li_rung_of_zeros_on_line_below_sharp (T : ℝ) (hT : 1 ≤ T)
    (hline : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ T → ρ.re = 1 / 2)
    (n : ℕ) (hn : (n + 1 : ℝ) ≤ 2 * π * (T - 1 / 2)) :
    0 ≤ (taylorCoeff riemannXi n).re := by
  apply re_taylorCoeff_nonneg_of_termwise
  intro ρ
  rcases le_or_gt |ρ.val.im| T with hle | hlt
  · exact re_liPairedSummand_nonneg_of_onLine n ρ
      (hline ρ.val ρ.property.1 ρ.property.2.1 ρ.property.2.2 hle)
  · apply re_liPairedSummand_nonneg_of_height_sharp n ρ (by linarith)
    have hmono : 2 * π * (T - 1 / 2) ≤ 2 * π * (|ρ.val.im| - 1 / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith

/-! ### 5. The height-4000 composition, sharp -/

/-- **The height-4000 Li ladder, sharp.**  Under the capstone's conclusion shape alone (the
real-zero residual discharged in `LiLadderHeight`), every rung `n + 1 <= 2 pi (4000 - 1/2)` is
nonnegative.  Conditional on `hall`; proves nothing about RH. -/
theorem li_rungs_of_bands_4000_sharp
    (hall : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 4000 → ρ.re = 1 / 2) :
    ∀ n : ℕ, (n + 1 : ℝ) ≤ 2 * π * (4000 - 1 / 2) → 0 ≤ (taylorCoeff riemannXi n).re :=
  fun n hn => li_rung_of_zeros_on_line_below_sharp 4000 (by norm_num)
    (line_hyp_of_upper_half 4000 hall noRealZeroInStrip) n hn

/-- Concretely: rungs `0 .. 25128` (`7999 pi > 25129`, via `Real.pi_gt_d6`). -/
theorem li_rungs_of_bands_4000_upto_sharp
    (hall : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 4000 → ρ.re = 1 / 2) :
    ∀ n : ℕ, n ≤ 25128 → 0 ≤ (taylorCoeff riemannXi n).re := by
  intro n hn
  apply li_rungs_of_bands_4000_sharp hall n
  have hπ := Real.pi_gt_d6
  have hn' : (n : ℝ) ≤ 25128 := by exact_mod_cast hn
  nlinarith

end LiLadderHeight
