/-
RvMDigammaLogDeriv — Phase 2 brick 4 (part 1): the log-derivative of the Weierstrass factor.

With the product = 1/Γ established (b3, `weierstrass_prod_eq_inv_Gamma`), b4 log-differentiates it
into the digamma series.  This file lands the per-factor log-derivative that the assembly needs:

  * `logDeriv_wFactor` — the log-derivative of a single factor is the exact rational term
      `logDeriv (wFactor n) s = 1/(s+(n+1)) − 1/(n+1)` — the classical digamma summand.

conjecture1_proved = False.
-/
import Mathlib
import RvMWeierstrass

open Complex

namespace RvMWeierstrass

set_option maxHeartbeats 1000000 in
/-- **Log-derivative of a Weierstrass factor.**  For `s` off the pole `−(n+1)`,
    `logDeriv (wFactor n) s = 1/(s+(n+1)) − 1/(n+1)` — the classical digamma summand.
    Product rule: `logDeriv[(1+s/(n+1))·e^{−s/(n+1)}] = 1/(s+(n+1)) + (−1/(n+1))`. -/
theorem logDeriv_wFactor {n : ℕ} {s : ℂ} (h : s + ((n : ℂ) + 1) ≠ 0) :
    logDeriv (wFactor n) s = 1 / (s + ((n : ℂ) + 1)) - 1 / ((n : ℂ) + 1) := by
  have hden : ((n : ℂ) + 1) ≠ 0 := natCast_add_one_ne_zero n
  have hexp : Complex.exp (-(s / ((n : ℂ) + 1))) ≠ 0 := Complex.exp_ne_zero _
  have hf0 : (1 + s / ((n : ℂ) + 1)) ≠ 0 := by
    intro hc; apply h; field_simp at hc; linear_combination hc
  have hderf : HasDerivAt (fun z : ℂ => 1 + z / ((n : ℂ) + 1)) (1 / ((n : ℂ) + 1)) s := by
    simpa using ((hasDerivAt_id s).div_const ((n : ℂ) + 1)).const_add (1 : ℂ)
  have hderg : HasDerivAt (fun z : ℂ => Complex.exp (-(z / ((n : ℂ) + 1))))
      (Complex.exp (-(s / ((n : ℂ) + 1))) * (-(1 / ((n : ℂ) + 1)))) s := by
    have h0 : HasDerivAt (fun z : ℂ => z / ((n : ℂ) + 1)) (1 / ((n : ℂ) + 1)) s := by
      simpa using (hasDerivAt_id s).div_const ((n : ℂ) + 1)
    exact h0.neg.cexp
  have hwf : wFactor n = fun z : ℂ => (1 + z / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1))) :=
    rfl
  rw [hwf, logDeriv_mul s hf0 hexp hderf.differentiableAt hderg.differentiableAt,
    logDeriv_apply, logDeriv_apply, hderf.deriv, hderg.deriv]
  -- second summand: (e^{-w}·(-1/(n+1))) / e^{-w} = -(1/(n+1))
  have e2 : (Complex.exp (-(s / ((n : ℂ) + 1))) * -(1 / ((n : ℂ) + 1)))
      / Complex.exp (-(s / ((n : ℂ) + 1))) = -(1 / ((n : ℂ) + 1)) := by
    rw [mul_comm]; exact mul_div_cancel_right₀ _ hexp
  -- first summand: (1/(n+1)) / (1+s/(n+1)) = 1/(s+(n+1))
  have e1 : (1 / ((n : ℂ) + 1)) / (1 + s / ((n : ℂ) + 1)) = 1 / (s + ((n : ℂ) + 1)) := by
    rw [div_eq_div_iff hf0 h]; field_simp; ring
  rw [e2, e1]; ring

end RvMWeierstrass
