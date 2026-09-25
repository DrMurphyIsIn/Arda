/-  RS5_Band_Joint.lean -- lane B5: the two band certificates glued: [1000, 10000] (RS5_Band_T1000, 32
    chunks) and [10000, 11000] (RS5_Band_T10000, 4 chunks) share the sample t = 10000.

    Result: 9493 + 1182 = 10675 DISTINCT zeros of Mathlib's `riemannZeta` on the critical line with
    ordinates in (1000, 11000).  Untrusted cross-check: mpmath N(11000) - N(1000) = 11324 - 649 = 10675,
    so the lower count is SHARP numerically.  The matching UPPER count (no further zeros in the band,
    on or off the line) is NOT proved on this branch; see the docstring of `RS5_Band`.

    Seam note: the Riemann-Siegel range starts at 1000 here only by choice of band; the bound used,
    `RSSeam.rs_Z_C0_seam`, holds from t >= 509 (see `RS5_Band_T510`), and the island's Euler-Maclaurin
    kernel ladder covers heights up to 1000 on this branch.

    conjecture1_proved = False.  Finitely many certified zeros; nothing about RH.
-/
import RS5_Band_T1000
import RS5_Band_T10000

open Complex

namespace RS5.BandJoint

open RS5

/-- **10675 distinct on-line zeros in (1000, 11000).** -/
theorem zeros : BandZeros 1000 11000 10675 :=
  BandZeros.glue (by norm_num) (by norm_num) RS5.BandT1000.zeros RS5.BandT10000.zeros

/-- **10675 distinct zeros of `riemannZeta` on the critical line with ordinates in (1000, 11000).** -/
theorem zeta_zeros : ∃ xs : List ℝ, xs.length = 10675 ∧ xs.IsChain (· < ·) ∧
    (∀ x ∈ xs, (1000 : ℝ) < x ∧ x < 11000) ∧
    (∀ x ∈ xs, riemannZeta (1 / 2 + (x : ℂ) * I) = 0) := zeros.zeta

/-- The same as a `Finset` of card 10675. -/
theorem zeta_zeros_finset : ∃ S : Finset ℝ, S.card = 10675 ∧
    ∀ x ∈ S, (1000 : ℝ) < x ∧ x < 11000 ∧ riemannZeta (1 / 2 + (x : ℂ) * I) = 0 := zeros.finset

/-- The `hLine` antecedent of `TuringBand.BandStatement _ _ 1000 11000 10675 ...`, verbatim shape. -/
theorem hLine : ∃ xs : List ℝ, xs.length = 10675 ∧ xs.IsChain (· < ·) ∧
    (∀ t ∈ xs, (1000 : ℝ) ≤ t ∧ t ≤ 11000) ∧
    (∀ t ∈ xs, completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0) := zeros.hLine

end RS5.BandJoint
