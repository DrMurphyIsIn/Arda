/-  RS5_Band_T510.lean -- lane B5: the band certificate on [510, 520] (headline; glues 1 kernel-checked chunks).

    8 dyadic sample heights t_i = tn_i / 2^6, t_0 = 510, t_k = 520, emitted by the UNTRUSTED pipeline
    scratchpad/b5/emit5.py and re-checked chunk by chunk by `decide +kernel` (`RS5.bandOK`), chunks
    RS5_Band_T510_C0.  Per-chunk sign-change counts 7 = 7.

    Result: 7 DISTINCT zeros of Mathlib's `riemannZeta` on the critical line with ordinates in (510, 520).
    Untrusted cross-check: mpmath N(520) - N(510) = 7, so this lower count is
    SHARP (equals N(T1) - N(T0)) numerically.  The matching UPPER count (that there
    are no other zeros, on or off the line, in the band) is NOT proved on this branch: see `RS5_Band`
    (argument principle / Turing count, branches cl/arb3-h1000 #613 and cl/arb4 #620).

    conjecture1_proved = False.  Finitely many certified zeros; nothing about RH.
-/
import RS5_Band_T510_C0

open Complex

namespace RS5.BandT510

open RS5

/-- **7 distinct on-line zeros in (510, 520)** (`BandZeros`: strictly increasing list, Lambda = 0 and
    riemannZeta = 0 at 1/2 + i x). -/
theorem zeros : BandZeros 510 520 7 :=
  (BandT510.C0.zeros).mono (by norm_num) (by norm_num)

/-- **7 distinct zeros of `riemannZeta` on the critical line with ordinates in (510, 520).** -/
theorem zeta_zeros : ∃ xs : List ℝ, xs.length = 7 ∧ xs.IsChain (· < ·) ∧
    (∀ x ∈ xs, (510 : ℝ) < x ∧ x < 520) ∧
    (∀ x ∈ xs, riemannZeta (1 / 2 + (x : ℂ) * I) = 0) := zeros.zeta

/-- The same as a `Finset` of card 7. -/
theorem zeta_zeros_finset : ∃ S : Finset ℝ, S.card = 7 ∧
    ∀ x ∈ S, (510 : ℝ) < x ∧ x < 520 ∧ riemannZeta (1 / 2 + (x : ℂ) * I) = 0 := zeros.finset

/-- The `hLine` antecedent of `TuringBand.BandStatement _ _ 510 520 7 ...`, verbatim shape. -/
theorem hLine : ∃ xs : List ℝ, xs.length = 7 ∧ xs.IsChain (· < ·) ∧
    (∀ t ∈ xs, (510 : ℝ) ≤ t ∧ t ≤ 520) ∧
    (∀ t ∈ xs, completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0) := zeros.hLine

end RS5.BandT510
