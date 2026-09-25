/-  RS5_Band_T1000.lean -- lane B5: the band certificate on [1000, 10000] (headline; glues 32 kernel-checked chunks).

    9494 dyadic sample heights t_i = tn_i / 2^6, t_0 = 1000, t_k = 10000, emitted by the UNTRUSTED pipeline
    scratchpad/b5/emit5.py and re-checked chunk by chunk by `decide +kernel` (`RS5.bandOK`), chunks
    RS5_Band_T1000_C0, RS5_Band_T1000_C1, RS5_Band_T1000_C2, RS5_Band_T1000_C3, RS5_Band_T1000_C4, RS5_Band_T1000_C5, RS5_Band_T1000_C6, RS5_Band_T1000_C7, RS5_Band_T1000_C8, RS5_Band_T1000_C9, RS5_Band_T1000_C10, RS5_Band_T1000_C11, RS5_Band_T1000_C12, RS5_Band_T1000_C13, RS5_Band_T1000_C14, RS5_Band_T1000_C15, RS5_Band_T1000_C16, RS5_Band_T1000_C17, RS5_Band_T1000_C18, RS5_Band_T1000_C19, RS5_Band_T1000_C20, RS5_Band_T1000_C21, RS5_Band_T1000_C22, RS5_Band_T1000_C23, RS5_Band_T1000_C24, RS5_Band_T1000_C25, RS5_Band_T1000_C26, RS5_Band_T1000_C27, RS5_Band_T1000_C28, RS5_Band_T1000_C29, RS5_Band_T1000_C30, RS5_Band_T1000_C31.  Per-chunk sign-change counts 297 + 296 + 297 + 297 + 296 + 297 + 297 + 296 + 297 + 297 + 296 + 297 + 297 + 296 + 297 + 296 + 297 + 297 + 296 + 297 + 297 + 296 + 297 + 297 + 296 + 297 + 297 + 296 + 297 + 297 + 296 + 297 = 9493.

    Result: 9493 DISTINCT zeros of Mathlib's `riemannZeta` on the critical line with ordinates in (1000, 10000).
    Untrusted cross-check: mpmath N(10000) - N(1000) = 9493, so this lower count is
    SHARP (equals N(T1) - N(T0)) numerically.  The matching UPPER count (that there
    are no other zeros, on or off the line, in the band) is NOT proved on this branch: see `RS5_Band`
    (argument principle / Turing count, branches cl/arb3-h1000 #613 and cl/arb4 #620).

    conjecture1_proved = False.  Finitely many certified zeros; nothing about RH.
-/
import RS5_Band_T1000_C0
import RS5_Band_T1000_C1
import RS5_Band_T1000_C2
import RS5_Band_T1000_C3
import RS5_Band_T1000_C4
import RS5_Band_T1000_C5
import RS5_Band_T1000_C6
import RS5_Band_T1000_C7
import RS5_Band_T1000_C8
import RS5_Band_T1000_C9
import RS5_Band_T1000_C10
import RS5_Band_T1000_C11
import RS5_Band_T1000_C12
import RS5_Band_T1000_C13
import RS5_Band_T1000_C14
import RS5_Band_T1000_C15
import RS5_Band_T1000_C16
import RS5_Band_T1000_C17
import RS5_Band_T1000_C18
import RS5_Band_T1000_C19
import RS5_Band_T1000_C20
import RS5_Band_T1000_C21
import RS5_Band_T1000_C22
import RS5_Band_T1000_C23
import RS5_Band_T1000_C24
import RS5_Band_T1000_C25
import RS5_Band_T1000_C26
import RS5_Band_T1000_C27
import RS5_Band_T1000_C28
import RS5_Band_T1000_C29
import RS5_Band_T1000_C30
import RS5_Band_T1000_C31

open Complex

namespace RS5.BandT1000

open RS5

/-- **9493 distinct on-line zeros in (1000, 10000)** (`BandZeros`: strictly increasing list, Lambda = 0 and
    riemannZeta = 0 at 1/2 + i x). -/
theorem zeros : BandZeros 1000 10000 9493 :=
  ((((((((((((((((((((((((((((((((BandT1000.C0.zeros).glue (by norm_num) (by norm_num) BandT1000.C1.zeros).glue (by norm_num) (by norm_num) BandT1000.C2.zeros).glue (by norm_num) (by norm_num) BandT1000.C3.zeros).glue (by norm_num) (by norm_num) BandT1000.C4.zeros).glue (by norm_num) (by norm_num) BandT1000.C5.zeros).glue (by norm_num) (by norm_num) BandT1000.C6.zeros).glue (by norm_num) (by norm_num) BandT1000.C7.zeros).glue (by norm_num) (by norm_num) BandT1000.C8.zeros).glue (by norm_num) (by norm_num) BandT1000.C9.zeros).glue (by norm_num) (by norm_num) BandT1000.C10.zeros).glue (by norm_num) (by norm_num) BandT1000.C11.zeros).glue (by norm_num) (by norm_num) BandT1000.C12.zeros).glue (by norm_num) (by norm_num) BandT1000.C13.zeros).glue (by norm_num) (by norm_num) BandT1000.C14.zeros).glue (by norm_num) (by norm_num) BandT1000.C15.zeros).glue (by norm_num) (by norm_num) BandT1000.C16.zeros).glue (by norm_num) (by norm_num) BandT1000.C17.zeros).glue (by norm_num) (by norm_num) BandT1000.C18.zeros).glue (by norm_num) (by norm_num) BandT1000.C19.zeros).glue (by norm_num) (by norm_num) BandT1000.C20.zeros).glue (by norm_num) (by norm_num) BandT1000.C21.zeros).glue (by norm_num) (by norm_num) BandT1000.C22.zeros).glue (by norm_num) (by norm_num) BandT1000.C23.zeros).glue (by norm_num) (by norm_num) BandT1000.C24.zeros).glue (by norm_num) (by norm_num) BandT1000.C25.zeros).glue (by norm_num) (by norm_num) BandT1000.C26.zeros).glue (by norm_num) (by norm_num) BandT1000.C27.zeros).glue (by norm_num) (by norm_num) BandT1000.C28.zeros).glue (by norm_num) (by norm_num) BandT1000.C29.zeros).glue (by norm_num) (by norm_num) BandT1000.C30.zeros).glue (by norm_num) (by norm_num) BandT1000.C31.zeros).mono (by norm_num) (by norm_num)

/-- **9493 distinct zeros of `riemannZeta` on the critical line with ordinates in (1000, 10000).** -/
theorem zeta_zeros : ∃ xs : List ℝ, xs.length = 9493 ∧ xs.IsChain (· < ·) ∧
    (∀ x ∈ xs, (1000 : ℝ) < x ∧ x < 10000) ∧
    (∀ x ∈ xs, riemannZeta (1 / 2 + (x : ℂ) * I) = 0) := zeros.zeta

/-- The same as a `Finset` of card 9493. -/
theorem zeta_zeros_finset : ∃ S : Finset ℝ, S.card = 9493 ∧
    ∀ x ∈ S, (1000 : ℝ) < x ∧ x < 10000 ∧ riemannZeta (1 / 2 + (x : ℂ) * I) = 0 := zeros.finset

/-- The `hLine` antecedent of `TuringBand.BandStatement _ _ 1000 10000 9493 ...`, verbatim shape. -/
theorem hLine : ∃ xs : List ℝ, xs.length = 9493 ∧ xs.IsChain (· < ·) ∧
    (∀ t ∈ xs, (1000 : ℝ) ≤ t ∧ t ≤ 10000) ∧
    (∀ t ∈ xs, completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0) := zeros.hLine

end RS5.BandT1000
