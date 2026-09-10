/-
RvMGammaR — Phase 4b: the archimedean log-derivative identity.

`Complex.Gammaℝ s = π^{-s/2}·Γ(s/2)` (Deligne's real archimedean factor).  Its logarithmic derivative
splits into a constant and a half-argument digamma:

  * `logDeriv_Gammaℝ_eq` — `logDeriv Γℝ s = −log π/2 + ½·ψ(s/2)`  (for `s` off the even poles).

This is the algebraic core of Phase 4b: it reduces the archimedean factor's log-derivative (and, on
iterating, its higher derivatives) to the polygamma values at `1/2` established in Phase 4a.  The
`m = 0` specialisation recovers the merged `logDeriv_gammaR_one`.  conjecture1_proved = False.
-/
import Mathlib
import RvMPolygammaHigher

open Complex

namespace RvMWeierstrass

/-- **The archimedean log-derivative identity.**  For `s` with `s/2` off the non-positive integers,
    `logDeriv Complex.Gammaℝ s = −log π/2 + ½·digamma (s/2)`. -/
theorem logDeriv_Gammaℝ_eq {s : ℂ} (hs : ∀ m : ℕ, s / 2 ≠ -(m : ℂ)) :
    logDeriv Complex.Gammaℝ s
      = -Complex.log (Real.pi : ℂ) / 2 + (1 / 2) * Complex.digamma (s / 2) := by
  have hπ : ((Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  -- derivative of the two factors
  have hlin1 : HasDerivAt (fun z : ℂ => -z / 2) (-1 / 2) s := by
    simpa using ((hasDerivAt_id s).neg).div_const 2
  have hd1 : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2))
      ((Real.pi : ℂ) ^ (-s / 2) * Complex.log (Real.pi : ℂ) * (-1 / 2)) s :=
    hlin1.const_cpow (Or.inl hπ)
  have hlin2 : HasDerivAt (fun z : ℂ => z / 2) (1 / 2) s := by
    simpa using (hasDerivAt_id s).div_const 2
  have hG : HasDerivAt Complex.Gamma (deriv Complex.Gamma (s / 2)) (s / 2) :=
    (Complex.differentiableAt_Gamma (s / 2) hs).hasDerivAt
  have hd2 : HasDerivAt (fun z : ℂ => Complex.Gamma (z / 2))
      (deriv Complex.Gamma (s / 2) * (1 / 2)) s := hG.comp s hlin2
  -- nonvanishing of the factors
  have hv1 : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := fun hc => hπ ((Complex.cpow_eq_zero_iff _ _).mp hc).1
  have hv2 : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero hs
  -- split the log-derivative of the product
  have hGR : Complex.Gammaℝ = fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2) := by
    funext z; rw [Complex.Gammaℝ_def]
  rw [hGR, logDeriv_mul (f := fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2))
      (g := fun z : ℂ => Complex.Gamma (z / 2)) s hv1 hv2 hd1.differentiableAt hd2.differentiableAt,
    logDeriv_apply, logDeriv_apply, hd1.deriv, hd2.deriv, Complex.digamma_def, logDeriv_apply]
  field_simp

end RvMWeierstrass
