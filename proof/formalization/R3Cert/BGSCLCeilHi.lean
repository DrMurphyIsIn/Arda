/-
  Per-child-degree BUDGET lemmas toward the d≥7 hub-ceiling residual `CeilStepHi` (BGSCLCeil).

  The natural attack on `CeilStepHi` (`bell(node cs) ≤ 0` for a hub of degree `d ≥ 7`) is the all-cherry
  concave-log tangent at slope `μ* = 3/(4d-1)`, using the SHARP per-degree ceiling `bell(c) ≤ cbound(deg c)`
  (`= A_k` for `3 ≤ k ≤ 6`, `= log(3/2) − 2F*` for `k = 2` [the cherry, NOT `A_2`], `= −F*` for a leaf, `= 0`
  for `k ≥ 7`) with `deg-2` children handled by SCL extend-below-`I` (their `y ≥ 1/3`).  This closes EXACTLY for
  `7 ≤ d ≤ 15`; for `d ≥ 16` the price `μ*` drops below the crossover and the incompatible (bell-max, y-max) of
  low-degree children breaks the per-child inequality — the genuine `TieSlack` regime (matching the BG ledger's
  step 2a, `k ≥ 16`), which needs a separate slack argument.  So these lemmas are NECESSARY infrastructure but
  do NOT on their own discharge `CeilStepHi`; the `d ≥ 16` tail remains open.

  The `key_dk` lemmas (`7·A_k + 1/k ≤ F*`, the `d = 7` per-child budget; `d ≥ 7` follows by `A_k ≤ 0`
  monotonicity) reduce (11×-clear) to `log(W_k) ≤ −11/k`, discharged by bounding `exp(11/k) ≤ r_k` (small
  integer, via `(exp(11/k))^k = (exp 1)^11 < 2.7182818286^11 ≤ r_k^k`) then `W_k · r_k ≤ 1` (`norm_num`, no
  large powers).  `k = 5, 6` instead use `A_k ≤ 0` + `1/k ≤ F*` (avoids the huge `norm_num`).
  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.BGSCLInduction
import R3Cert.BGSCLStep
import R3Cert.BGSCLHub
import R3Cert.BGSCLCeil

namespace R3Cert
namespace BGSCL

/-- Per-child budget, k=2: `7·A_2 + 1/2 ≤ F*`, `A_2 = log(3/2) + log(7/6) − 3F*`. -/
theorem key_d2 : 7*(Real.log (3/2) + Real.log (7/6) - 3*FSTAR) + 1/2 ≤ FSTAR := by
  have e1 : (Real.exp (11/2))^2 = Real.exp 11 := by rw [← Real.exp_nat_mul]; congr 1; norm_num
  have e2 : (Real.exp 1)^11 = Real.exp 11 := by rw [← Real.exp_nat_mul]; congr 1; norm_num
  have hb : (Real.exp 1)^11 ≤ (2.7182818286:ℝ)^11 :=
    pow_le_pow_left₀ (Real.exp_nonneg 1) (le_of_lt Real.exp_one_lt_d9) 11
  have hexp : Real.exp (11/2) ≤ (300:ℝ) := by
    have hpk : (Real.exp (11/2))^2 ≤ (300:ℝ)^2 := by
      rw [e1, ← e2]; have : (2.7182818286:ℝ)^11 ≤ (300:ℝ)^2 := by norm_num
      linarith
    exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hpk
  have hWK : (0:ℝ) < (3/2:ℝ)^77*(7/6)^77*(64/621)^22 := by positivity
  have h1 : ((3/2:ℝ)^77*(7/6)^77*(64/621)^22) * Real.exp (11/2) ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left hexp (le_of_lt hWK)
    have hWr : ((3/2:ℝ)^77*(7/6)^77*(64/621)^22) * (300:ℝ) ≤ 1 := by norm_num
    linarith
  have hlogW : Real.log ((3/2:ℝ)^77*(7/6)^77*(64/621)^22) ≤ -(11/2) := by
    have h3 : Real.log (((3/2:ℝ)^77*(7/6)^77*(64/621)^22) * Real.exp (11/2)) ≤ 0 := by
      rw [Real.log_le_iff_le_exp (by positivity), Real.exp_zero]; exact h1
    rw [Real.log_mul (ne_of_gt hWK) (ne_of_gt (Real.exp_pos _)), Real.log_exp] at h3; linarith
  have hF : FSTAR = Real.log (621/64)/11 := rfl
  have hcomb : (11:ℝ)*(7*(Real.log (3/2) + Real.log (7/6) - 3*FSTAR) + 1/2 - FSTAR)
      = Real.log ((3/2:ℝ)^77*(7/6)^77*(64/621)^22) + 11/2 := by
    rw [hF, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_pow, show (64:ℝ)/621=(621/64)⁻¹ by norm_num, Real.log_inv]
    ring
  linarith [hcomb, hlogW]

/-- Per-child budget, k=3: `7·A_3 + 1/3 ≤ F*`, `A_3 = 2 log(3/2) + log(11/9) − 5F*`. -/
theorem key_d3 : 7*(2*Real.log (3/2) + Real.log (11/9) - 5*FSTAR) + 1/3 ≤ FSTAR := by
  have e1 : (Real.exp (11/3))^3 = Real.exp 11 := by rw [← Real.exp_nat_mul]; congr 1; norm_num
  have e2 : (Real.exp 1)^11 = Real.exp 11 := by rw [← Real.exp_nat_mul]; congr 1; norm_num
  have hb : (Real.exp 1)^11 ≤ (2.7182818286:ℝ)^11 :=
    pow_le_pow_left₀ (Real.exp_nonneg 1) (le_of_lt Real.exp_one_lt_d9) 11
  have hexp : Real.exp (11/3) ≤ (45:ℝ) := by
    have hpk : (Real.exp (11/3))^3 ≤ (45:ℝ)^3 := by
      rw [e1, ← e2]; have : (2.7182818286:ℝ)^11 ≤ (45:ℝ)^3 := by norm_num
      linarith
    exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hpk
  have hWK : (0:ℝ) < (3/2:ℝ)^154*(11/9)^77*(64/621)^36 := by positivity
  have h1 : ((3/2:ℝ)^154*(11/9)^77*(64/621)^36) * Real.exp (11/3) ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left hexp (le_of_lt hWK)
    have hWr : ((3/2:ℝ)^154*(11/9)^77*(64/621)^36) * (45:ℝ) ≤ 1 := by norm_num
    linarith
  have hlogW : Real.log ((3/2:ℝ)^154*(11/9)^77*(64/621)^36) ≤ -(11/3) := by
    have h3 : Real.log (((3/2:ℝ)^154*(11/9)^77*(64/621)^36) * Real.exp (11/3)) ≤ 0 := by
      rw [Real.log_le_iff_le_exp (by positivity), Real.exp_zero]; exact h1
    rw [Real.log_mul (ne_of_gt hWK) (ne_of_gt (Real.exp_pos _)), Real.log_exp] at h3; linarith
  have hF : FSTAR = Real.log (621/64)/11 := rfl
  have hcomb : (11:ℝ)*(7*(2*Real.log (3/2) + Real.log (11/9) - 5*FSTAR) + 1/3 - FSTAR)
      = Real.log ((3/2:ℝ)^154*(11/9)^77*(64/621)^36) + 11/3 := by
    rw [hF, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_pow, show (64:ℝ)/621=(621/64)⁻¹ by norm_num, Real.log_inv]
    ring
  linarith [hcomb, hlogW]

/-- Per-child budget, k=4 (binding): `7·A_4 + 1/4 ≤ F*`, `A_4 = 3 log(3/2) + log(5/4) − 7F*`. -/
theorem key_d4 : 7*(3*Real.log (3/2) + Real.log (5/4) - 7*FSTAR) + 1/4 ≤ FSTAR := by
  have e1 : (Real.exp (11/4))^4 = Real.exp 11 := by rw [← Real.exp_nat_mul]; congr 1; norm_num
  have e2 : (Real.exp 1)^11 = Real.exp 11 := by rw [← Real.exp_nat_mul]; congr 1; norm_num
  have hb : (Real.exp 1)^11 ≤ (2.7182818286:ℝ)^11 :=
    pow_le_pow_left₀ (Real.exp_nonneg 1) (le_of_lt Real.exp_one_lt_d9) 11
  have hexp : Real.exp (11/4) ≤ (16:ℝ) := by
    have hpk : (Real.exp (11/4))^4 ≤ (16:ℝ)^4 := by
      rw [e1, ← e2]; have : (2.7182818286:ℝ)^11 ≤ (16:ℝ)^4 := by norm_num
      linarith
    exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hpk
  have hWK : (0:ℝ) < (3/2:ℝ)^231*(5/4)^77*(64/621)^50 := by positivity
  have h1 : ((3/2:ℝ)^231*(5/4)^77*(64/621)^50) * Real.exp (11/4) ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left hexp (le_of_lt hWK)
    have hWr : ((3/2:ℝ)^231*(5/4)^77*(64/621)^50) * (16:ℝ) ≤ 1 := by norm_num
    linarith
  have hlogW : Real.log ((3/2:ℝ)^231*(5/4)^77*(64/621)^50) ≤ -(11/4) := by
    have h3 : Real.log (((3/2:ℝ)^231*(5/4)^77*(64/621)^50) * Real.exp (11/4)) ≤ 0 := by
      rw [Real.log_le_iff_le_exp (by positivity), Real.exp_zero]; exact h1
    rw [Real.log_mul (ne_of_gt hWK) (ne_of_gt (Real.exp_pos _)), Real.log_exp] at h3; linarith
  have hF : FSTAR = Real.log (621/64)/11 := rfl
  have hcomb : (11:ℝ)*(7*(3*Real.log (3/2) + Real.log (5/4) - 7*FSTAR) + 1/4 - FSTAR)
      = Real.log ((3/2:ℝ)^231*(5/4)^77*(64/621)^50) + 11/4 := by
    rw [hF, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_pow, show (64:ℝ)/621=(621/64)⁻¹ by norm_num, Real.log_inv]
    ring
  linarith [hcomb, hlogW]

/-- `1/5 ≤ F*` (`11/5 ≤ log(621/64)`, via `exp(11/5) ≤ 9.5 ≤ 621/64`). -/
theorem recip5_le_fstar : (1:ℝ)/5 ≤ FSTAR := by
  have e1 : (Real.exp (11/5))^5 = Real.exp 11 := by rw [← Real.exp_nat_mul]; congr 1; norm_num
  have e2 : (Real.exp 1)^11 = Real.exp 11 := by rw [← Real.exp_nat_mul]; congr 1; norm_num
  have hb : (Real.exp 1)^11 ≤ (2.7182818286:ℝ)^11 :=
    pow_le_pow_left₀ (Real.exp_nonneg 1) (le_of_lt Real.exp_one_lt_d9) 11
  have hexp : Real.exp (11/5) ≤ (9.5:ℝ) := by
    have hpk : (Real.exp (11/5))^5 ≤ (9.5:ℝ)^5 := by
      rw [e1, ← e2]; have : (2.7182818286:ℝ)^11 ≤ (9.5:ℝ)^5 := by norm_num
      linarith
    exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hpk
  have hlog : (11:ℝ)/5 ≤ Real.log (621/64) := by
    rw [Real.le_log_iff_exp_le (by norm_num)]; exact le_trans hexp (by norm_num)
  rw [FSTAR]; linarith

/-- Per-child budget, k=5: `7·A_5 + 1/5 ≤ F*` — since `A_5 ≤ 0` (`acl_d5`) and `1/5 ≤ F*`. -/
theorem key_d5 : 7*(4*Real.log (3/2) + Real.log (19/15) - 9*FSTAR) + 1/5 ≤ FSTAR := by
  have hA5 : 4*Real.log (3/2) + Real.log (19/15) - 9*FSTAR ≤ 0 := acl_d5
  linarith [hA5, recip5_le_fstar]

/-- Per-child budget, k=6: `7·A_6 + 1/6 ≤ F*` — since `A_6 ≤ 0` (`acl_d6`) and `1/6 ≤ 1/5 ≤ F*`. -/
theorem key_d6 : 7*(5*Real.log (3/2) + Real.log (23/18) - 11*FSTAR) + 1/6 ≤ FSTAR := by
  have hA6 : 5*Real.log (3/2) + Real.log (23/18) - 11*FSTAR ≤ 0 := acl_d6
  linarith [hA6, recip5_le_fstar]

end BGSCL
end R3Cert
