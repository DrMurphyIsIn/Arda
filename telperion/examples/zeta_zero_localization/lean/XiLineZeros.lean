/- telperion 0.1.6 | family XiLineZeros | input-hash 64f8103b24f3ebab
   1 theorems, 2 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib
import LambdaLineReal

open Complex
set_option linter.unusedVariables false

namespace XiLineZeros

/-!
# On-line zero localization of the completed Riemann zeta function (Stage 1 core)

Each theorem below states: given certified real enclosures of `Lambda(1/2 + i*t)`
(the documented Arb-certified NON-KERNEL input, as hypotheses) with alternating
signs, there exist strictly increasing reals in `[a, b]` at which
`completedRiemannZeta (1/2 + t*I) = 0`, i.e. `>= N` zeros of `Lambda` on the
critical line.  The proof lifts to the real part `gLine` (real on the line by the
Task-2 prelude `ZetaZeroLocalization.completedZeta_im_eq_zero`), uses its
continuity, and applies the intermediate value theorem on each sign-change
subinterval.

Note: `conjecture1_proved = False`.  This localizes individual nontrivial zeros ON
the critical line from certified enclosures; it does NOT prove RH.
-/

-- Real part of Lambda on the critical line.
noncomputable def gLine (t : ℝ) : ℝ := (completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I)).re

-- The lifting point `1/2 + t*I` is never 0 nor 1 (its real part is 1/2).
theorem line_ne_zero (t : ℝ) : (1 / 2 + (t : ℂ) * Complex.I) ≠ 0 := by
  intro h
  have hre : ((1 / 2 + (t : ℂ) * Complex.I)).re = (0 : ℂ).re := by rw [h]
  simp at hre

theorem line_ne_one (t : ℝ) : (1 / 2 + (t : ℂ) * Complex.I) ≠ 1 := by
  intro h
  have hre : ((1 / 2 + (t : ℂ) * Complex.I)).re = (1 : ℂ).re := by rw [h]
  simp at hre

-- `gLine` is continuous on all of ℝ.  `completedRiemannZeta` is differentiable
-- (hence continuous) at each line point `1/2 + t*I`, which is never 0 nor 1.
theorem gLine_continuous : Continuous gLine := by
  have hline : Continuous (fun t : ℝ => (1 / 2 + (t : ℂ) * Complex.I)) := by
    fun_prop
  have hZeta : Continuous (fun t : ℝ => completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hd : DifferentiableAt ℂ completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) :=
      differentiableAt_completedZeta (line_ne_zero t) (line_ne_one t)
    exact ContinuousAt.comp (g := completedRiemannZeta)
      (f := fun t : ℝ => (1 / 2 + (t : ℂ) * Complex.I)) hd.continuousAt
      (hline.continuousAt (x := t))
  exact Complex.continuous_re.comp hZeta

-- On the line, Lambda equals its real part promoted to ℂ.
theorem lambda_eq_gLine (t : ℝ) :
    completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = (gLine t : ℂ) := by
  have him : (completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I)).im = 0 :=
    ZetaZeroLocalization.completedZeta_im_eq_zero t
  apply Complex.ext
  · rfl
  · rw [him]; simp [gLine]

theorem lambda_zero_first_14_15 : ∀ (henc_lo0 : (-(7249049639811687071616942716790511139780407740184070913554353348319 / 3533694129556768659166595001485837031654967793751237916243212402585239552)) ≤ gLine 14) (henc_hi0 : gLine 14 ≤ (-(7249049639811687071616942716790511139780407740184070913553518960929 / 3533694129556768659166595001485837031654967793751237916243212402585239552))) (henc_lo1 : (2767725565291782891550731528526599663612525895384952805911803741157 / 441711766194596082395824375185729628956870974218904739530401550323154944) ≤ gLine 15) (henc_hi1 : gLine 15 ≤ (2767725565291782891550731528526599663612525895384952805912392481819 / 441711766194596082395824375185729628956870974218904739530401550323154944)) , ∃ x1 : ℝ, (14 ≤ x1 ∧ x1 ≤ 15) ∧ (completedRiemannZeta (1 / 2 + (x1 : ℂ) * Complex.I) = 0) := by
  intro henc_lo0 henc_hi0 henc_lo1 henc_hi1
  -- sign-change subinterval [14, 15]: root r1
  have hle0 : (14 : ℝ) ≤ 15 := by norm_num
  have hcont0 : ContinuousOn gLine (Set.Icc (14 : ℝ) 15) :=
    gLine_continuous.continuousOn
  have hneg0 : gLine 14 < 0 := by linarith [henc_lo0, henc_hi0, henc_lo1, henc_hi1]
  have hpos0 : (0 : ℝ) < gLine 15 := by linarith [henc_lo0, henc_hi0, henc_lo1, henc_hi1]
  have hmem0 : (0 : ℝ) ∈ gLine '' Set.Icc (14 : ℝ) 15 :=
    intermediate_value_Icc hle0 hcont0 ⟨le_of_lt hneg0, le_of_lt hpos0⟩
  obtain ⟨r1, hIcc0, hz0⟩ := hmem0
  have hri_lo0 : (14 : ℝ) < r1 := by
    rcases lt_or_eq_of_le hIcc0.1 with h | h
    · exact h
    · exfalso
      rw [← h] at hz0; rw [hz0] at hneg0; exact lt_irrefl 0 hneg0
  have hri_hi0 : r1 < (15 : ℝ) := by
    rcases lt_or_eq_of_le hIcc0.2 with h | h
    · exact h
    · exfalso
      rw [h] at hz0; rw [hz0] at hpos0; exact lt_irrefl 0 hpos0
  have hLam0 : completedRiemannZeta (1 / 2 + (r1 : ℂ) * Complex.I) = 0 := by
    rw [lambda_eq_gLine, hz0]; simp
  have ha_le : (14 : ℝ) ≤ 14 := by norm_num
  have hb_ge : (15 : ℝ) ≤ 15 := by norm_num
  exact ⟨r1, ⟨by linarith [hri_lo0], by linarith [hri_hi0]⟩, hLam0⟩
example : ∀ (henc_lo0 : (-(7249049639811687071616942716790511139780407740184070913554353348319 / 3533694129556768659166595001485837031654967793751237916243212402585239552)) ≤ gLine 14) (henc_hi0 : gLine 14 ≤ (-(7249049639811687071616942716790511139780407740184070913553518960929 / 3533694129556768659166595001485837031654967793751237916243212402585239552))) (henc_lo1 : (2767725565291782891550731528526599663612525895384952805911803741157 / 441711766194596082395824375185729628956870974218904739530401550323154944) ≤ gLine 15) (henc_hi1 : gLine 15 ≤ (2767725565291782891550731528526599663612525895384952805912392481819 / 441711766194596082395824375185729628956870974218904739530401550323154944)) , ∃ x1 : ℝ, (14 ≤ x1 ∧ x1 ≤ 15) ∧ (completedRiemannZeta (1 / 2 + (x1 : ℂ) * Complex.I) = 0) := lambda_zero_first_14_15

end XiLineZeros
