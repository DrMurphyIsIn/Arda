/-
RvMGammaRCapstone — the archimedean Li coefficient as one explicit polygamma-at-½ combination.

Single headline statement gluing the whole Phase-4 arc:
  #458 `taylorCoeff_Gammaℝ_leibniz`  (Leibniz over the Möbius pullback)
  #456 `iteratedDeriv_logDerivGammaℝ_comp_mobius`  (Faà di Bruno on `(logDeriv Γℝ)∘M`)
  #453 `iteratedDeriv_logDeriv_Gammaℝ_one`  +  #452 `logDeriv_Gammaℝ_eq`  (reduction to ψ at ½).

The archimedean log-derivative data at `1` is packaged as the explicit polygamma-at-½ primitive
`archGamma m`:  `archGamma 0 = −log π/2 + ½·ψ(½)` (the surviving constant), and for `m ≥ 1`
`archGamma m = (½)^(m+1)·ψ^{(m)}(½)` where `ψ^{(m)}(½) = iteratedDeriv m digamma (1/2)`.

  * `iteratedDeriv_logDeriv_Gammaℝ_one_eq_archGamma` — `iteratedDeriv m (logDeriv Γℝ) 1 = archGamma m`.
  * `taylorCoeff_Gammaℝ_polygamma` — the capstone:
      `taylorCoeff Γℝ n = (∑_{k≤n} C(n,k)·(∑_{c:OFP k} (∏_j (partSize c j)!)·archGamma c.length)·(n−k+1)!) / n!`.

Every archimedean derivative in the n-th Li coefficient now reads as a finite combination of
polygamma-at-½ values.  conjecture1_proved = False.
-/
import Mathlib
import RvMArchimedeanCoeff
import RvMFaaDiBruno
import RvMGammaRIterate
import RvMGammaR

open Complex

namespace RvMWeierstrass

/-- The archimedean log-derivative data at `1`, as an explicit polygamma-at-½ value.
    `archGamma 0 = −log π/2 + ½·ψ(½)`;  `archGamma m = (½)^(m+1)·ψ^{(m)}(½)` for `m ≥ 1`. -/
noncomputable def archGamma (m : ℕ) : ℂ :=
  if m = 0 then -Complex.log (Real.pi : ℂ) / 2 + (1 / 2) * Complex.digamma (1 / 2)
  else (1 / 2) ^ (m + 1) * iteratedDeriv m Complex.digamma (1 / 2)

/-- `½` avoids every pole of `ψ` (its real part is positive), so `logDeriv_Gammaℝ_eq` applies at 1. -/
private theorem half_ne_neg_nat : ∀ m : ℕ, (1 : ℂ) / 2 ≠ -(m : ℂ) := by
  intro m h
  have hre : (1 : ℝ) / 2 = -(m : ℝ) := by
    have := congrArg Complex.re h; simpa using this
  have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

/-- **The archimedean derivative-at-1 IS the polygamma-at-½ primitive**, for every order `m`
    (bridging the `m = 0` constant term of #452 with the `m ≥ 1` reduction of #453). -/
theorem iteratedDeriv_logDeriv_Gammaℝ_one_eq_archGamma (m : ℕ) :
    iteratedDeriv m (logDeriv Complex.Gammaℝ) 1 = archGamma m := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    rw [iteratedDeriv_zero, archGamma, if_pos rfl, logDeriv_Gammaℝ_eq half_ne_neg_nat]
  · rw [archGamma, if_neg h.ne', iteratedDeriv_logDeriv_Gammaℝ_one m h]

/-- **Capstone: the archimedean Li coefficient as one explicit polygamma-at-½ combination.**
    Glues #458 (Leibniz) → #456 (Faà di Bruno) → #453/#452 (reduction to ψ at ½). -/
theorem taylorCoeff_Gammaℝ_polygamma (n : ℕ) :
    LiCriterion.taylorCoeff Complex.Gammaℝ n
      = (∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) *
          ((∑ c : OrderedFinpartition k,
              (∏ j, ((c.partSize j).factorial : ℂ)) • archGamma c.length)
            * (((n - k + 1).factorial : ℕ) : ℂ))) / ((n.factorial : ℕ) : ℂ) := by
  rw [taylorCoeff_Gammaℝ_leibniz]
  simp only [iteratedDeriv_logDerivGammaℝ_comp_mobius,
    iteratedDeriv_logDeriv_Gammaℝ_one_eq_archGamma]

end RvMWeierstrass
