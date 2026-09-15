/-
RvMNTCount — Arc A (effective RvM), PR A3: the effective bound on the box ξ-zero count.

`nt_effective_bound` (PR A2) pins the boundary winding integer `N` to `1 + θ(T)/π` within an
explicit `O(log T)`.  The box argument principle `xiTele_count_eq_winding` identifies that same `N`
as the *zero count* of ξ in the box `[−1,2]×[0,T]` (the multiplicity sum `∑_{ρ} d(ρ)` over the
ξ-zeros there, which — by the guarded ξ↔ζ correspondence elsewhere on the island — are exactly the
nontrivial ζ-zeros to height `T`).  Composing the two, the zero count itself obeys the effective
Riemann–von Mangoldt estimate:

  `|(zero count) − 1 − θ(T)/π| ≤ log((4T+19)/(2 − π²/6)) / log(7/6) + 2`.

Honesty: the winding integer enters only as the boundary-contour value `hwind`; the zero count is
the *derived* quantity, never assumed.  `S(T)` is the genuine error, bounded not eliminated.
conjecture1_proved = False.
-/
import Mathlib
import RvMNTEffective
import RvMDiffractionCore

open Complex Real MeasureTheory DiffractionCore

namespace Backlund

/-- **The effective RvM bound, phrased on the box ξ-zero count.**  Under the box-boundary
nonvanishing (`Icc` orientation), the strict-interior hypothesis `hin`, the enclosing-ball
hypothesis `hbox_ball`, the boundary winding `= 2πiN`, `4 ≤ T`, and the height-`T` ζ-segment
nonvanishing `hζne`, there is a finite multiset of ξ-zeros (with positive multiplicities `d`)
containing every ξ-zero of the box, whose multiplicity sum obeys

  `|(∑ ρ, d ρ : ℝ) − 1 − θ(T)/π| ≤ log((4T+19)/(2 − π²/6)) / log(7/6) + 2`.

The multiplicity sum is the box zero count `N`; this is the effective count formula.
conjecture1_proved = False. -/
theorem nt_count_effective_bound (T : ℝ) (hT : 4 ≤ T) (c : ℂ) (R : ℝ) (N : ℤ)
    (hbox_ball : ∀ ρ : ℂ, ((-1:ℝ) ≤ ρ.re ∧ ρ.re ≤ 2) → ((0:ℝ) ≤ ρ.im ∧ ρ.im ≤ T) →
      ρ ∈ Metric.ball c R)
    (hnzBot : ∀ x ∈ Set.Icc (-1:ℝ) 2, xiTele ((x : ℂ)) ≠ 0)
    (hnzTop : ∀ x ∈ Set.Icc (-1:ℝ) 2, xiTele ((x : ℂ) + (T : ℂ) * I) ≠ 0)
    (hnzL : ∀ y ∈ Set.Icc (0:ℝ) T, xiTele (((-1:ℝ) : ℂ) + (y : ℂ) * I) ≠ 0)
    (hnzR : ∀ y ∈ Set.Icc (0:ℝ) T, xiTele (((2:ℝ) : ℂ) + (y : ℂ) * I) ≠ 0)
    (hin : ∀ ρ ∈ (divisor_xiTele_ball_support_finite c R).toFinset,
      (-1:ℝ) < ρ.re ∧ ρ.re < 2 ∧ (0:ℝ) < ρ.im ∧ ρ.im < T)
    (hζne : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2, riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0)
    (hwind : (∫ x in (-1:ℝ)..2, logDeriv xiTele (↑x + ((0:ℝ) : ℂ) * I))
        - (∫ x in (-1:ℝ)..2, logDeriv xiTele (↑x + ((T:ℝ) : ℂ) * I))
        + I • (∫ y in (0:ℝ)..T, logDeriv xiTele (((2:ℝ) : ℂ) + ↑y * I))
        - I • (∫ y in (0:ℝ)..T, logDeriv xiTele (((-1:ℝ) : ℂ) + ↑y * I))
      = 2 * ↑π * I * (N : ℂ)) :
    ∃ (s : Finset ℂ) (d : ℂ → ℤ),
      (∀ ρ ∈ s, (1 : ℤ) ≤ d ρ) ∧
      (∀ ρ : ℂ, ((-1:ℝ) ≤ ρ.re ∧ ρ.re ≤ 2) → ((0:ℝ) ≤ ρ.im ∧ ρ.im ≤ T) →
        xiTele ρ = 0 → ρ ∈ s) ∧
      (∑ ρ ∈ s, d ρ) = N ∧
      |((∑ ρ ∈ s, d ρ : ℤ) : ℝ) - 1 - ZeroFreeBridge.riemannSiegelTheta T / π|
        ≤ Real.log ((4 * T + 19) / (2 - Real.pi ^ 2 / 6)) / Real.log (7 / 6) + 2 := by
  have hT0 : (0 : ℝ) ≤ T := by linarith
  -- edge hypotheses in the `uIcc` orientation the count theorem wants
  have huBot : ∀ x ∈ Set.uIcc (-1:ℝ) 2, xiTele (↑x + ((0:ℝ) : ℂ) * I) ≠ 0 := by
    intro x hx; rw [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 2)] at hx
    simpa using hnzBot x hx
  have huTop : ∀ x ∈ Set.uIcc (-1:ℝ) 2, xiTele (↑x + ((T:ℝ) : ℂ) * I) ≠ 0 := by
    intro x hx; rw [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 2)] at hx
    exact hnzTop x hx
  have huR : ∀ y ∈ Set.uIcc (0:ℝ) T, xiTele ((2 : ℂ) + ↑y * I) ≠ 0 := by
    intro y hy; rw [Set.uIcc_of_le hT0] at hy
    simpa using hnzR y hy
  have huL : ∀ y ∈ Set.uIcc (0:ℝ) T, xiTele (((-1:ℝ) : ℂ) + ↑y * I) ≠ 0 := by
    intro y hy; rw [Set.uIcc_of_le hT0] at hy
    exact hnzL y hy
  obtain ⟨s, d, hpos, hsub, hsum⟩ :=
    xiTele_count_eq_winding (-1) 2 0 T c R N (by norm_num) hT0 hbox_ball
      huBot huTop huR huL hin hwind
  refine ⟨s, d, hpos, hsub, hsum, ?_⟩
  rw [hsum]
  exact nt_effective_bound T hT N hnzBot hnzTop hnzL hnzR hζne hwind

end Backlund
