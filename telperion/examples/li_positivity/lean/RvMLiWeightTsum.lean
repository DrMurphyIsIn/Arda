/-
RvMLiWeightTsum — Route P Brick D2b-2: the paired coefficient sum as a liWeight sum.

Folds the genus-1 paired-sum formula (Stratum 2) through the D2b-1 hinge
(`liPairedSummand_eq_liWeight_paired`, #476) to express `taylorCoeff riemannXi n` as a `liWeight (n+1)`
paired tsum, carrying the analytic hypotheses `hgenus`/`hhad` UNDISCHARGED (they are RH-adjacent).

  * `taylorCoeff_riemannXi_eq_liWeight_paired_tsum` (hgenus)(hhad)(n):
      `taylorCoeff riemannXi n = 2⁻¹ · ∑'_ρ (liWeight (n+1) ρ + liWeight (n+1) (pairedZero ρ))`.

CONVERGENCE DISCIPLINE (load-bearing — do NOT collapse to an unpaired sum).  The raw Li summand
behaves like `(n+1)/ρ`, so the UNPAIRED series `∑'_ρ liWeight (n+1) ρ` does NOT converge (only the
PAIRED summand is summable, `summable_Li_paired_summand_of_genus_one`).  Hence one may NOT pull the
`2⁻¹` inside and split via `tsum_add` — that needs each unpaired series summable, which fails, and the
collapsed `tsum` would be `0` (the non-summable convention) while the true value is nonzero.  D2b-2
therefore stays PAIRED.  The bridge to `li_finite_explicit_formula`'s left side — a FINITE `Finset.sum`
(`taylorCoeff_finite_Li`), not a `tsum` — is D2b-3's job, done at the finite / exhaustion level.

The companion `tsum_liWeight_pairedZero_eq` records the functional-equation symmetry `ρ ↔ 1−ρ` at the
reindex level (unconditional, `Equiv.tsum_eq`); its docstring flags that it does NOT license the split.

Category (b): a finite-checkable structural identity, consistent with RH, proving nothing.
conjecture1_proved = False.
-/
import Mathlib
import RvMLiWeightReconcile
import Lc.LiCriterion.GenusOnePairedSumFormula

open Complex

namespace RvMWeierstrass

/-- **D2b-2.**  `taylorCoeff riemannXi n = 2⁻¹ · ∑'_ρ (liWeight (n+1) ρ + liWeight (n+1) (pairedZero ρ))`.
    The paired-sum formula (Stratum 2, conditional on `hgenus`/`hhad`) rewritten termwise through the
    D2b-1 hinge.  Stays PAIRED (the unpaired `liWeight` tsum diverges); `hgenus`/`hhad` undischarged. -/
theorem taylorCoeff_riemannXi_eq_liWeight_paired_tsum
    (hgenus : Summable (fun ρ : LiCriterion.NontrivialZero => (1 : ℝ) / ‖ρ.val‖ ^ 2))
    (hhad : ∃ a : ℂ, ∀ s : ℂ,
        LiCriterion.riemannXi s = Complex.exp a * LiCriterion.xiE1ShiftedProd s)
    (n : ℕ) :
    LiCriterion.taylorCoeff LiCriterion.riemannXi n
      = 2⁻¹ * ∑' ρ : LiCriterion.NontrivialZero,
          (DiffractionCore.liWeight (n + 1) ρ.val
            + DiffractionCore.liWeight (n + 1) (LiCriterion.pairedZero ρ).val) := by
  rw [LiCriterion.paired_sum_formula_of_standard_hypotheses hgenus hhad n,
    tsum_congr fun ρ => liPairedSummand_eq_liWeight_paired n ρ]

/-- The functional-equation symmetry `ρ ↔ 1−ρ` at the reindex level:
    `∑'_ρ liWeight (n+1) (pairedZero ρ) = ∑'_ρ liWeight (n+1) ρ` (unconditional, `Equiv.tsum_eq`).

    WARNING: this reindex holds even when BOTH sides are non-summable (both are then `0` by the `tsum`
    convention), so it does NOT license splitting the paired sum in
    `taylorCoeff_riemannXi_eq_liWeight_paired_tsum` via `tsum_add` — that split is FALSE here (the
    unpaired `liWeight` series diverges).  It records the FE symmetry only. -/
theorem tsum_liWeight_pairedZero_eq (n : ℕ) :
    ∑' ρ : LiCriterion.NontrivialZero,
        DiffractionCore.liWeight (n + 1) (LiCriterion.pairedZero ρ).val
      = ∑' ρ : LiCriterion.NontrivialZero, DiffractionCore.liWeight (n + 1) ρ.val := by
  have h := LiCriterion.pairedZeroEquiv.tsum_eq
    (fun ρ : LiCriterion.NontrivialZero => DiffractionCore.liWeight (n + 1) ρ.val)
  simpa [LiCriterion.coe_pairedZeroEquiv] using h

end RvMWeierstrass
