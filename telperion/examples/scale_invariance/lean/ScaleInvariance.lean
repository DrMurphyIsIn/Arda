/- telperion 0.1.6 | family ScaleInvariance | input-hash fe092633f4da7c2d
   2 theorems, 9 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace ScaleInvariance

-- si_return_indep_position_size: parameter cancellation — the objective does not depend on s (∂f/∂s ≡ 0), so any two values agree (field_simp; ring).
theorem si_return_indep_position_size (L : ℝ) (capital : ℝ) (direction : ℝ) (dprice : ℝ) (fee : ℝ) (price : ℝ) (s : ℝ) (s2 : ℝ) (hd0 : (L : ℝ) ≠ 0) (hd1 : (capital : ℝ) ≠ 0) (hd2 : (s : ℝ) ≠ 0) (hd3 : (price : ℝ) ≠ 0) (hd4 : (s2 : ℝ) ≠ 0) :
    (((((-1) * L * capital * fee * s) + ((L * capital * direction * dprice * s) / (price)))) / (L * capital * s)) = (((((-1) * L * capital * fee * s2) + ((L * capital * direction * dprice * s2) / (price)))) / (L * capital * s2)) := by
  field_simp
  all_goals ring

-- si_sharpe_sq_leverage_invariant: degree-0 homogeneity — scaling the arguments by lam > 0 leaves the objective invariant (field_simp; ring).
theorem si_sharpe_sq_leverage_invariant (r1 : ℝ) (r2 : ℝ) (r3 : ℝ) (lam : ℝ) (hpos : (0 : ℝ) < lam) (hd0 : ((((1 * ((((-1) * lam * r1) / (3)) + (((-1) * lam * r2) / (3)) + ((2 * lam * r3) / (3))) ^ 2) / (3)) + ((1 * ((((-1) * lam * r1) / (3)) + (((-1) * lam * r3) / (3)) + ((2 * lam * r2) / (3))) ^ 2) / (3)) + ((1 * ((((-1) * lam * r2) / (3)) + (((-1) * lam * r3) / (3)) + ((2 * lam * r1) / (3))) ^ 2) / (3))) : ℝ) ≠ 0) (hd1 : ((((1 * ((((-1) * r1) / (3)) + (((-1) * r2) / (3)) + ((2 * r3) / (3))) ^ 2) / (3)) + ((1 * ((((-1) * r1) / (3)) + (((-1) * r3) / (3)) + ((2 * r2) / (3))) ^ 2) / (3)) + ((1 * ((((-1) * r2) / (3)) + (((-1) * r3) / (3)) + ((2 * r1) / (3))) ^ 2) / (3))) : ℝ) ≠ 0) :
    ((3 * (((1 * lam * r1) / (3)) + ((1 * lam * r2) / (3)) + ((1 * lam * r3) / (3))) ^ 2) / ((((1 * ((((-1) * lam * r1) / (3)) + (((-1) * lam * r2) / (3)) + ((2 * lam * r3) / (3))) ^ 2) / (3)) + ((1 * ((((-1) * lam * r1) / (3)) + (((-1) * lam * r3) / (3)) + ((2 * lam * r2) / (3))) ^ 2) / (3)) + ((1 * ((((-1) * lam * r2) / (3)) + (((-1) * lam * r3) / (3)) + ((2 * lam * r1) / (3))) ^ 2) / (3))))) = ((3 * (((1 * r1) / (3)) + ((1 * r2) / (3)) + ((1 * r3) / (3))) ^ 2) / ((((1 * ((((-1) * r1) / (3)) + (((-1) * r2) / (3)) + ((2 * r3) / (3))) ^ 2) / (3)) + ((1 * ((((-1) * r1) / (3)) + (((-1) * r3) / (3)) + ((2 * r2) / (3))) ^ 2) / (3)) + ((1 * ((((-1) * r2) / (3)) + (((-1) * r3) / (3)) + ((2 * r1) / (3))) ^ 2) / (3))))) := by
  field_simp
  all_goals ring

end ScaleInvariance
