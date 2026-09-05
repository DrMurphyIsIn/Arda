/- telperion 0.1.6 | family BCSplit | input-hash a7436ac492accd7e
   2 theorems, 2 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace BCSplit

-- BC-split combine (tight combine): from w = Z + E with ‖E‖ ≤ B,
-- the entire part costs at most ‖E‖, so -Re(w) ≤ B - Re(Z).
theorem bc_split_tight (w Z E : ℂ) (B : ℝ) (hw : w = Z + E) (hE : ‖E‖ ≤ B) :
    (-w).re ≤ B - Z.re := by
  have h1 : (-w).re = -Z.re - E.re := by rw [hw]; simp; ring
  have h2 : -E.re ≤ ‖E‖ :=
    le_trans (neg_le_abs E.re) (Complex.abs_re_le_norm E)
  rw [h1]; linarith [h2, hE]

-- BC-split combine (combine with a 1/10 slack margin): from w = Z + E with ‖E‖ ≤ B,
-- the entire part costs at most ‖E‖, so -Re(w) ≤ B - Re(Z) + (1 / 10 : ℝ).
theorem bc_split_slack (w Z E : ℂ) (B : ℝ) (hw : w = Z + E) (hE : ‖E‖ ≤ B) :
    (-w).re ≤ B - Z.re + (1 / 10 : ℝ) := by
  have h1 : (-w).re = -Z.re - E.re := by rw [hw]; simp; ring
  have h2 : -E.re ≤ ‖E‖ :=
    le_trans (neg_le_abs E.re) (Complex.abs_re_le_norm E)
  rw [h1]; linarith [h2, hE]

end BCSplit
