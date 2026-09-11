/-
RvMLiWeightReconcile — Route P, Brick D2b-1: the weight-reconciliation hinge.

The finite Bragg identity for the companion coefficient (D2b) must bridge #430's two halves, which use
DIFFERENT weights: Stratum 2 writes `taylorCoeff riemannXi n = ½ Σ'_ρ liPairedSummand n ρ` (the paired
summand, negative power `w^{−(n+1)}`), while `li_finite_explicit_formula` weights ζ's divisor by
`liWeight n ρ = 1 − wⁿ` (positive power).  This brick is the elementary, unconditional hinge that
reconciles them:

  * `liPairedSummand_eq_liWeight_paired` —
      `liPairedSummand n ρ = liWeight (n+1) ρ + liWeight (n+1) (pairedZero ρ)`.

Both sides equal `2 − w^{n+1} − w^{−(n+1)}` (`w := 1 − 1/ρ`): `liWeight (n+1) ρ = 1 − w^{n+1}` and, via
`1 − 1/(1−ρ) = w⁻¹`, `liWeight (n+1) (pairedZero ρ) = 1 − (w⁻¹)^{n+1} = 1 − w^{−(n+1)}`.  It lets the
finite explicit formula (in `liWeight`) speak the coefficient's language (in `liPairedSummand`).
Unconditional and kernel-clean; a structural bridge, NOT progress toward RH.  conjecture1_proved = False.
See ROUTEP_D2B_WEIGHT_RECONCILIATION_SPEC_2026-09-11.md.
-/
import Mathlib
import RvMPairedSummandAnatomy
import RvMLiCountBridge

open Complex

namespace RvMWeierstrass

/-- **Route P, Brick D2b-1 — the weight-reconciliation hinge.**  The paired Li coefficient summand
    equals the sum of the finite-explicit-formula weight `liWeight (n+1)` at `ρ` and at its
    functional-equation partner `pairedZero ρ = 1 − ρ`:
    `liPairedSummand n ρ = liWeight (n+1) ρ + liWeight (n+1) (pairedZero ρ)`.
    Elementary and unconditional (both sides are `2 − w^{n+1} − w^{−(n+1)}`, `w = 1 − 1/ρ`).  The hinge
    that lets `li_finite_explicit_formula` (weighted by `liWeight`) meet Stratum 2's coefficient
    zero-sum (weighted by `liPairedSummand`).  conjecture1_proved = False. -/
theorem liPairedSummand_eq_liWeight_paired (n : ℕ) (ρ : LiCriterion.NontrivialZero) :
    LiCriterion.liPairedSummand n ρ
      = DiffractionCore.liWeight (n + 1) ρ.val
        + DiffractionCore.liWeight (n + 1) (LiCriterion.pairedZero ρ).val := by
  have hρ0 : ρ.val ≠ 0 := LiCriterion.NontrivialZero.ne_zero ρ
  have hρ1 : ρ.val ≠ 1 := LiCriterion.NontrivialZero.ne_one ρ
  have h1ρ : (1 : ℂ) - ρ.val ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  rw [liPairedSummand_eq_two_sub_v_sub_inv,
      DiffractionCore.liWeight_at_zero, DiffractionCore.liWeight_at_zero,
      LiCriterion.pairedZero_val]
  set w : ℂ := 1 - 1 / ρ.val with hw
  have hwe : w = (ρ.val - 1) / ρ.val := by rw [hw, sub_div, div_self hρ0]
  have hpair : (1 : ℂ) - 1 / (1 - ρ.val) = w⁻¹ := by rw [hwe, inv_div]; field_simp; ring
  rw [hpair, inv_pow]
  ring

end RvMWeierstrass
