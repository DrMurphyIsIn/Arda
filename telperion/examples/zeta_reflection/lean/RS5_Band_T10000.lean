/-  RS5_Band_T10000.lean -- lane B5: the band certificate on [10000, 11000] (headline; glues 4 kernel-checked chunks).

    1183 dyadic sample heights t_i = tn_i / 2^6, t_0 = 10000, t_k = 11000, emitted by the UNTRUSTED pipeline
    scratchpad/b5/emit5.py and re-checked chunk by chunk by `decide +kernel` (`RS5.bandOK`), chunks
    RS5_Band_T10000_C0, RS5_Band_T10000_C1, RS5_Band_T10000_C2, RS5_Band_T10000_C3.  Per-chunk sign-change counts 296 + 295 + 295 + 296 = 1182.

    Result: 1182 DISTINCT zeros of Mathlib's `riemannZeta` on the critical line with ordinates in (10000, 11000).
    Untrusted cross-check: mpmath N(11000) - N(10000) = 1182, so this lower count is
    SHARP (equals N(T1) - N(T0)) numerically.  The matching UPPER count (that there
    are no other zeros, on or off the line, in the band) is NOT proved on this branch: see `RS5_Band`
    (argument principle / Turing count, branches cl/arb3-h1000 #613 and cl/arb4 #620).

    conjecture1_proved = False.  Finitely many certified zeros; nothing about RH.
-/
import RS5_Band_T10000_C0
import RS5_Band_T10000_C1
import RS5_Band_T10000_C2
import RS5_Band_T10000_C3

open Complex

namespace RS5.BandT10000

open RS5

/-- **1182 distinct on-line zeros in (10000, 11000)** (`BandZeros`: strictly increasing list, Lambda = 0 and
    riemannZeta = 0 at 1/2 + i x). -/
theorem zeros : BandZeros 10000 11000 1182 :=
  ((((BandT10000.C0.zeros).glue (by norm_num) (by norm_num) BandT10000.C1.zeros).glue (by norm_num) (by norm_num) BandT10000.C2.zeros).glue (by norm_num) (by norm_num) BandT10000.C3.zeros).mono (by norm_num) (by norm_num)

/-- **1182 distinct zeros of `riemannZeta` on the critical line with ordinates in (10000, 11000).** -/
theorem zeta_zeros : ∃ xs : List ℝ, xs.length = 1182 ∧ xs.IsChain (· < ·) ∧
    (∀ x ∈ xs, (10000 : ℝ) < x ∧ x < 11000) ∧
    (∀ x ∈ xs, riemannZeta (1 / 2 + (x : ℂ) * I) = 0) := zeros.zeta

/-- The same as a `Finset` of card 1182. -/
theorem zeta_zeros_finset : ∃ S : Finset ℝ, S.card = 1182 ∧
    ∀ x ∈ S, (10000 : ℝ) < x ∧ x < 11000 ∧ riemannZeta (1 / 2 + (x : ℂ) * I) = 0 := zeros.finset

/-- The `hLine` antecedent of `TuringBand.BandStatement _ _ 10000 11000 1182 ...`, verbatim shape. -/
theorem hLine : ∃ xs : List ℝ, xs.length = 1182 ∧ xs.IsChain (· < ·) ∧
    (∀ t ∈ xs, (10000 : ℝ) ≤ t ∧ t ≤ 11000) ∧
    (∀ t ∈ xs, completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0) := zeros.hLine

end RS5.BandT10000
