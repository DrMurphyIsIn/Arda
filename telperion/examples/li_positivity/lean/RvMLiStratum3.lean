/-
RvMLiStratum3 — the finite explicit formula for the Li weight: the ARITHMETIC
(prime) side of the finite Li partial sum.

STRATUM 3 of the N(T) ↔ λ_n bridge — the deep, arithmetic content.  The Weil
explicit formula reads a weighted zero-sum as an archimedean transform MINUS a
prime-power sum.  Our `rect_explicit_formula` already carries this for `ζ` and a
holomorphic weight `g`, over a rectangle whose right edge sits in `Re > 1` (where
`ζ'/ζ = −∑ Λ(n)/nˢ` — the von Mangoldt / "Bragg peak" prime series).

This file specialises it to the Li weight `g = liWeight n`, so the conclusion is
the finite Li explicit formula:

  `2πi · ∑_{ρ∈box} mult(ρ)·(1−(1−1/ρ)ⁿ)
     = [horizontal + left-vertical edge integrals of liWeight·(ζ'/ζ)]  −  i·∑_m [von Mangoldt prime terms]`.

The left side is the finite Li partial sum (Stratum 1's weighted winding); the
right side is the archimedean/boundary part MINUS the prime sum.  This is the
finite, kernel-verified skeleton of the Bombieri–Lagarias formula.

HONEST FRONTIER (what this does NOT do — the genuine research program):
  (i)  This is the `ζ` weighted count.  The `ξ` version adds `Γℝ'/Γℝ` (the
       archimedean piece); on a strip box it corrects the boundary edges, and its
       `T→∞` boundary contribution is the archimedean MAIN TERM (`~ (n/2)log n`).
  (ii) `λ_n` is the `T→∞` limit of this finite formula (Stratum 2's exhaustion).
       Extracting the archimedean main term from the boundary integrals in that
       limit — the point where the zero density `dN(T) ~ (1/2π)log(T/2π)` becomes
       load-bearing — is the asymptotic analysis that neither this development nor
       the upstream contains.  That limit + extraction is the research core.

So: the finite explicit formula (prime side) is FORMALIZED here; the infinite
limit and archimedean main-term asymptotics are the named, unbuilt frontier.
conjecture1_proved = False.
-/
import RvMLiCountBridge

namespace DiffractionCore

open Complex MeasureTheory Real

/-- **The finite Li explicit formula (Stratum 3, prime side).**  Specialising
    `rect_explicit_formula` to the Li weight `liWeight n` over a rectangle in the
    right half-plane (`0 < σ₀`, so the weight is holomorphic; `1 < σ₁`, so the right
    edge exposes the von Mangoldt prime series): the finite Li-weighted zero-sum of
    `ζ` equals the horizontal + left-edge integrals minus the prime-power sum.

    The `hnz*` edge hypotheses are the classical zero-avoidance of the contour (Arb
    enclosures); the box/ball geometry is as in `rect_explicit_formula`.  The left
    side is the finite Li partial sum; the right side is boundary − primes. -/
theorem li_finite_explicit_formula (n : ℕ)
    (sigma0 sigma1 T0 T1 : ℝ) (hsig : sigma0 ≤ sigma1) (hT : T0 ≤ T1)
    (hσ0 : 0 < sigma0) (hσ1 : 1 < sigma1)
    (c : ℂ) (R : ℝ)
    (hbox_ball : ∀ ρ : ℂ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      ρ ∈ Metric.ball c R)
    (hs1 : (1 : ℂ) ∉ Metric.ball c R)
    (hnzb : ∀ x ∈ Set.uIcc sigma0 sigma1, riemannZeta (↑x + (T0 : ℂ) * I) ≠ 0)
    (hnzt : ∀ x ∈ Set.uIcc sigma0 sigma1, riemannZeta (↑x + (T1 : ℂ) * I) ≠ 0)
    (hnzl : ∀ y ∈ Set.uIcc T0 T1, riemannZeta ((sigma0 : ℂ) + ↑y * I) ≠ 0)
    (hins : ∀ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
      sigma0 < ρ.re ∧ ρ.re < sigma1 ∧ T0 < ρ.im ∧ ρ.im < T1) :
    2 * ↑π * I * ∑ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
        (((MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ) ρ : ℂ) * liWeight n ρ)
      = (∫ x in sigma0..sigma1, liWeight n (↑x + (T0 : ℂ) * I) * logDeriv riemannZeta (↑x + (T0 : ℂ) * I))
        - (∫ x in sigma0..sigma1, liWeight n (↑x + (T1 : ℂ) * I) * logDeriv riemannZeta (↑x + (T1 : ℂ) * I))
        - I • (∑' m : ℕ, (∫ y in T0..T1, liWeight n ((sigma1 : ℂ) + ↑y * I)
            * LSeries.term (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
                ((sigma1 : ℂ) + ↑y * I) m))
        - I • (∫ y in T0..T1, liWeight n ((sigma0 : ℂ) + ↑y * I)
            * logDeriv riemannZeta ((sigma0 : ℂ) + ↑y * I)) := by
  -- the Li weight is holomorphic on the open right half-plane, which contains the box
  set W : Set ℂ := {z : ℂ | 0 < z.re} with hWdef
  have hWopen : IsOpen W := isOpen_lt continuous_const Complex.continuous_re
  have h0W : (0 : ℂ) ∉ W := by simp [hWdef]
  have hgW : DifferentiableOn ℂ (liWeight n) W := liWeight_differentiableOn h0W
  have hsubW : (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) ⊆ W := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    simp only [hWdef, Set.mem_setOf_eq]
    exact lt_of_lt_of_le hσ0 hz.1.1
  exact rect_explicit_formula sigma0 sigma1 T0 T1 hsig hT hσ1 c R hbox_ball hs1
    (liWeight n) hWopen hgW hsubW hnzb hnzt hnzl hins

end DiffractionCore
