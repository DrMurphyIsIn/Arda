/-  H11K_Line.lean -- lane H11K: the on-line zeros of the wide band [31851/4, 11004].

    3541 distinct zeros of `completedRiemannZeta` (and of `riemannZeta`) on the critical line with
    ordinates in (31851/4, 11004), glued from kernel-checked Riemann-Siegel sign-change chunks
    (`RS5.bandOK`, lane B5 format):

      * RS5_Band_T8000Lo_C0   [509616/64, 525170/64]   277  (new, lane H11K)
      * RS5_Band_T1000_C25 .. C31  [525170/64, 640000/64]  2077  (lane B5)
      * RS5_Band_T10000       [10000, 11000]          1182  (lane B5)
      * RS5_Band_T8000Hi_C0   [704000/64, 704256/64]     5  (new, lane H11K)

    `hLine` is VERBATIM the on-line antecedent (`BandGlue.BandData.LineHyp`) of the band.
    Untrusted cross-check: mpmath N(11004) - N(7962.75) = 11329 - 7788 = 3541 (the count is sharp).
    Axioms within [propext, Classical.choice, Quot.sound] (H11K_AxiomGuard).  No `sorry`.
    conjecture1_proved = False.  Finitely many certified zeros; nothing about RH.
-/
import RS5_Band_T8000Lo_C0
import RS5_Band_T1000_C25
import RS5_Band_T1000_C26
import RS5_Band_T1000_C27
import RS5_Band_T1000_C28
import RS5_Band_T1000_C29
import RS5_Band_T1000_C30
import RS5_Band_T1000_C31
import RS5_Band_T10000
import RS5_Band_T8000Hi_C0

open Complex

namespace H11K.Line

open RS5

/-- The chunks `[509616/64, 640000/64]` (lower new chunk + lane B5 chunks C25 .. C31). -/
theorem zeros_lo : BandZeros (509616 / 64 : ℝ) (640000 / 64 : ℝ) (277 + 297 + 297 + 296 + 297 + 297 + 296 + 297) :=
  (((((((BandT8000Lo.C0.zeros.glue (by norm_num) (by norm_num) BandT1000.C25.zeros).glue
    (by norm_num) (by norm_num) BandT1000.C26.zeros).glue (by norm_num) (by norm_num)
    BandT1000.C27.zeros).glue (by norm_num) (by norm_num) BandT1000.C28.zeros).glue
    (by norm_num) (by norm_num) BandT1000.C29.zeros).glue (by norm_num) (by norm_num)
    BandT1000.C30.zeros).glue (by norm_num) (by norm_num) BandT1000.C31.zeros)

/-- The upper part `[10000, 704256/64]` (lane B5 band T10000 + the upper new chunk). -/
theorem zeros_hi : BandZeros (10000 : ℝ) (704256 / 64 : ℝ) (1182 + 5) :=
  (BandT10000.zeros.mono (le_refl _) (by norm_num : (11000 : ℝ) ≤ 704000 / 64)).glue
    (by norm_num) (by norm_num) BandT8000Hi.C0.zeros

/-- **3541 distinct on-line zeros in `(31851/4, 11004)`.** -/
theorem zeros : BandZeros (31851 / 4 : ℝ) (11004 : ℝ) 3541 := by
  have h := (zeros_lo.mono (le_refl _) (by norm_num : (640000 / 64 : ℝ) ≤ 10000)).glue
    (by norm_num) (by norm_num) zeros_hi
  exact h.mono (by norm_num) (by norm_num)

/-- The `hLine` antecedent of the band `[31851/4, 11004]` with `n = 3541`, verbatim shape. -/
theorem hLine : ∃ xs : List ℝ, xs.length = 3541 ∧ xs.IsChain (· < ·) ∧
    (∀ t ∈ xs, (31851 / 4 : ℝ) ≤ t ∧ t ≤ (11004 : ℝ)) ∧
    (∀ t ∈ xs, completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0) := zeros.hLine

end H11K.Line
