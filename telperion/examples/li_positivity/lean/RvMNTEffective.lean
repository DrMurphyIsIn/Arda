/-
RvMNTEffective — Arc A (effective RvM), PR A2: the effective Riemann–von Mangoldt bound.

The exact counting formula `(N:ℝ) = 1 + θ(T)/π + S(T)` (`xiTele_winding_eq_RvM`) places the box
winding integer `N` against the smooth main term `1 + θ(T)/π` with the *error* being exactly
`S(T) = riemannS T`.  Composing the pure-in-`T` Backlund bound (PR A1) gives the effective form:

  `|N − 1 − θ(T)/π| ≤ log((4T+19)/(2 − π²/6)) / log(7/6) + 2`,

i.e. the winding count is pinned to the main term within an explicit `O(log T)`.

The hypotheses are exactly those of `xiTele_winding_eq_RvM` (the four ξ edge-nonvanishings, the
height-`T` ζ-segment nonvanishing, and the boundary winding `= 2πiN`), together with `4 ≤ T` for
the Backlund bound.  The ζ-segment hypothesis is stated once, in the `Set.Icc (1/2) 2` orientation
that both consumers want; it is converted to the `uIcc` orientation `xiTele_winding_eq_RvM`
expects internally.

Honesty: the winding integer `N` enters as the boundary-contour value `hwind`, never as an
assumed zero count; `S(T)` is the genuine error term, here bounded, not eliminated.  This is the
classical effective RvM, formalized — not a statement about where the zeros lie.
conjecture1_proved = False.
-/
import Mathlib
import RvMBacklundExplicit
import RvMDiffractionCore

open Complex Real MeasureTheory DiffractionCore

namespace Backlund

/-- **The effective Riemann–von Mangoldt bound.**  Under the box-boundary nonvanishing and winding
hypotheses of `xiTele_winding_eq_RvM`, and `4 ≤ T`, the winding integer `N` of the symmetric box
`[−1,2]×[0,T]` is pinned to the main term `1 + θ(T)/π` within an explicit `O(log T)`:

  `|N − 1 − θ(T)/π| ≤ log((4T+19)/(2 − π²/6)) / log(7/6) + 2`.

Combined with `xiTele_count_eq_winding`, `N` is the box ξ-zero count (= number of nontrivial
ζ-zeros to height `T`), so this is the effective count formula.  The error is `riemannS T`
(`S(T)`), bounded by the pure-in-`T` Backlund estimate (PR A1).  conjecture1_proved = False. -/
theorem nt_effective_bound (T : ℝ) (hT : 4 ≤ T) (N : ℤ)
    (hnzBot : ∀ x ∈ Set.Icc (-1:ℝ) 2, xiTele ((x : ℂ)) ≠ 0)
    (hnzTop : ∀ x ∈ Set.Icc (-1:ℝ) 2, xiTele ((x : ℂ) + (T : ℂ) * I) ≠ 0)
    (hnzL : ∀ y ∈ Set.Icc (0:ℝ) T, xiTele (((-1:ℝ) : ℂ) + (y : ℂ) * I) ≠ 0)
    (hnzR : ∀ y ∈ Set.Icc (0:ℝ) T, xiTele (((2:ℝ) : ℂ) + (y : ℂ) * I) ≠ 0)
    (hζne : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2, riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0)
    (hwind : (∫ x in (-1:ℝ)..2, logDeriv xiTele (↑x + ((0:ℝ) : ℂ) * I))
        - (∫ x in (-1:ℝ)..2, logDeriv xiTele (↑x + ((T:ℝ) : ℂ) * I))
        + I • (∫ y in (0:ℝ)..T, logDeriv xiTele (((2:ℝ) : ℂ) + ↑y * I))
        - I • (∫ y in (0:ℝ)..T, logDeriv xiTele (((-1:ℝ) : ℂ) + ↑y * I))
      = 2 * ↑π * I * (N : ℂ)) :
    |(N : ℝ) - 1 - ZeroFreeBridge.riemannSiegelTheta T / π|
      ≤ Real.log ((4 * T + 19) / (2 - Real.pi ^ 2 / 6)) / Real.log (7 / 6) + 2 := by
  -- orientation bridge: `uIcc 2 (1/2) = Icc (1/2) 2`, so `hζne` supplies the `hζT` the RvM wants
  have hζT : ∀ x ∈ Set.uIcc (2:ℝ) (1/2), riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_ge (by norm_num : (1/2:ℝ) ≤ 2)] at hx
    exact hζne x hx
  -- the exact counting formula
  have hRvM := xiTele_winding_eq_RvM T (by linarith) N hnzBot hnzTop hnzL hnzR hζT hwind
  -- the error is exactly S(T)
  have herr : (N : ℝ) - 1 - ZeroFreeBridge.riemannSiegelTheta T / π = riemannS T := by
    rw [hRvM]; ring
  rw [herr]
  exact riemannS_abs_le_log_explicit hT hζne

end Backlund
