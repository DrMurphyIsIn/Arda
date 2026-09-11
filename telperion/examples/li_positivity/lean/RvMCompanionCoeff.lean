/-
RvMCompanionCoeff — Route P Brick D2b-3: isolation of the companion Taylor coefficient.

Isolates `taylorCoeff zetaPoleCompanion n` (the sole arithmetic-carrying term of the Li coefficient)
as an explicit expression, by combining the D2b-2 paired zero-sum (#478) with the explicit split (#463):

  * `taylorCoeff_companion_eq_liWeight_paired_tsum` (hgenus)(hhad)(n):
      `taylorCoeff zetaPoleCompanion n
         = 2⁻¹ · ∑'_ρ (liWeight (n+1) ρ + liWeight (n+1) (pairedZero ρ)) − 1 − taylorCoeff Γℝ n`.

This is the **zero-sum-side** isolation: the companion coefficient equals the paired zero-sum (its
Bombieri–Lagarias / geometric content, D2b-2) minus the two fully-explicit non-companion parts — the
elementary `1` (the `1/s` pole) and the archimedean polygamma datum `taylorCoeff Γℝ n` (the #464
capstone).  It stays on the valid PAIRED zero-sum side; `hgenus`/`hhad` are carried undischarged.

HONEST SCOPE — the PRIME/Bragg-side dual is NOT here.  Expressing this same companion coefficient
through the finite explicit formula's von-Mangoldt (Bragg) side (`li_finite_explicit_formula` +
D1/D2a) requires the `T→∞` exhaustion limit AND the archimedean main-term extraction from the boundary
integrals — which `RvMLiStratum3`'s own header names as "the named, unbuilt frontier ... the research
core that neither this development nor the upstream contains."  That prime-side isolation stays
category-(c) and is deliberately not attempted.

Category (b): a finite-checkable structural identity, consistent with RH, proving nothing.
conjecture1_proved = False.
-/
import Mathlib
import RvMLiWeightTsum
import RvMLiCoeffId

open Complex

namespace RvMWeierstrass

/-- **D2b-3 (zero-sum side).**  The companion Taylor coefficient isolated as the D2b-2 paired zero-sum
    minus the explicit non-companion parts (`1` + archimedean `taylorCoeff Γℝ n`).  Conditional on
    `hgenus`/`hhad` (carried undischarged); stays on the valid paired zero-sum side. -/
theorem taylorCoeff_companion_eq_liWeight_paired_tsum
    (hgenus : Summable (fun ρ : LiCriterion.NontrivialZero => (1 : ℝ) / ‖ρ.val‖ ^ 2))
    (hhad : ∃ a : ℂ, ∀ s : ℂ,
        LiCriterion.riemannXi s = Complex.exp a * LiCriterion.xiE1ShiftedProd s)
    (n : ℕ) :
    LiCriterion.taylorCoeff DiffractionCore.zetaPoleCompanion n
      = 2⁻¹ * ∑' ρ : LiCriterion.NontrivialZero,
          (DiffractionCore.liWeight (n + 1) ρ.val
            + DiffractionCore.liWeight (n + 1) (LiCriterion.pairedZero ρ).val)
        - 1 - LiCriterion.taylorCoeff Complex.Gammaℝ n := by
  have hsplit := taylorCoeff_riemannXi_split_explicit n
  rw [taylorCoeff_riemannXi_eq_liWeight_paired_tsum hgenus hhad n] at hsplit
  linear_combination -hsplit

end RvMWeierstrass
