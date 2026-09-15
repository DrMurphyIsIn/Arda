/-
RvMBacklundExplicit — Arc A (effective RvM), PR A1: the pure-in-T Backlund bound.

The slimmed Backlund headline (`riemannS_abs_le_log_of_ne_zero`, PR 6) bounds `|S(T)|` by
`log((4T+19)/‖F_T(2)‖)/log(7/6) + 2`, whose denominator still carries the auxiliary function
`F_T(2)`.  The Jensen-centre floor `2 − π²/6 ≤ ‖F_T(2)‖` (PR 3a, `backlundAux_two_norm_ge`)
lets the norm be majorized away: the bound becomes a closed-form function of `T` alone,

  `|S(T)| ≤ log((4T+19)/(2 − π²/6)) / log(7/6) + 2`,

an explicit `O(log T)` with every constant concrete.  No new hypotheses: `4 ≤ T` and the genuine
`T`-not-a-zero-ordinate caveat `hζne`, exactly as in PR 6.

Honesty: this is a rigorous classical growth bound (Backlund 1918 proved sharper constants —
`0.137·log T + 0.445·log log T + 4.35`; Trudgian 2014 sharper still).  The contribution is the
kernel derivation, stated at exactly its strength.  conjecture1_proved = False.
-/
import Mathlib
import RvMBacklundLogCont

open Complex MeasureTheory

namespace Backlund

/-- The Jensen-centre floor is positive: `0 < 2 − π²/6` (since `π < 3.15` gives `π² < 12`). -/
theorem two_sub_pi_sq_div_six_pos : (0 : ℝ) < 2 - Real.pi ^ 2 / 6 := by
  nlinarith [Real.pi_lt_d2, Real.pi_pos]

/-- **The pure-in-`T` Backlund bound**: for `T ≥ 4` with `ζ ≠ 0` on `[1/2,2] + iT`,

  `|S(T)| ≤ log((4T+19)/(2 − π²/6)) / log(7/6) + 2`.

The `‖F_T(2)‖` denominator of the PR-6 headline is replaced by its Jensen-centre floor
`2 − π²/6` (`backlundAux_two_norm_ge`), so the right-hand side is a closed-form function of `T` —
an explicit `O(log T)` with concrete constants.  Sole carried hypothesis: `hζne` (the genuine
`S(T)`-jump caveat).  conjecture1_proved = False. -/
theorem riemannS_abs_le_log_explicit {T : ℝ} (hT : 4 ≤ T)
    (hζne : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2, riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0) :
    |DiffractionCore.riemannS T|
      ≤ Real.log ((4 * T + 19) / (2 - Real.pi ^ 2 / 6)) / Real.log (7 / 6) + 2 := by
  have hbase := riemannS_abs_le_log_of_ne_zero hT hζne
  have hb : (7 : ℝ) / 4 / (3 / 2) = 7 / 6 := by norm_num
  rw [hb] at hbase
  have hc : (0 : ℝ) < 2 - Real.pi ^ 2 / 6 := two_sub_pi_sq_div_six_pos
  have hFge : 2 - Real.pi ^ 2 / 6 ≤ ‖backlundAux T ((2 : ℝ) : ℂ)‖ := backlundAux_two_norm_ge T
  have hF : (0 : ℝ) < ‖backlundAux T ((2 : ℝ) : ℂ)‖ := lt_of_lt_of_le hc hFge
  have hnum : (0 : ℝ) < 4 * T + 19 := by linarith
  have hlogbase : (0 : ℝ) < Real.log (7 / 6) := Real.log_pos (by norm_num)
  refine hbase.trans ?_
  gcongr

end Backlund
