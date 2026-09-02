/- telperion 0.1.6 | family MagnitudeSplit | input-hash 9a90665ecdfada92
   3 theorems, 3 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace MagnitudeSplit

/-- Triangle-inequality magnitude split: `‖A‖ ≤ α`, `‖B‖ ≤ β`, `‖C‖ ≤ γ`
    imply `‖A + B − C‖ ≤ α + β + γ`.  Assembly of `norm_sub_le` +
    `norm_add_le` (as in `zeta_log_bound`). -/
theorem magsplit_abc_universal (A B C : ℂ) (α β γ : ℝ)
    (hA : ‖A‖ ≤ α) (hB : ‖B‖ ≤ β) (hC : ‖C‖ ≤ γ) :
    ‖A + B - C‖ ≤ α + β + γ := by
  have h1 := norm_sub_le (A + B) C
  have h2 := norm_add_le A B
  linarith [h1, h2, hA, hB, hC]

/-- Concrete-bounds magnitude split (`α = 1`, `β = 1`, `γ = 4`):
    `‖A‖ ≤ 1`, `‖B‖ ≤ 1`, `‖C‖ ≤ 4` imply
    `‖A + B − C‖ ≤ 1 + 1 + 4`. -/
theorem magsplit_abc_concrete (A B C : ℂ)
    (hA : ‖A‖ ≤ (1 : ℝ)) (hB : ‖B‖ ≤ (1 : ℝ)) (hC : ‖C‖ ≤ (4 : ℝ)) :
    ‖A + B - C‖ ≤ (1 : ℝ) + 1 + 4 := by
  have h1 := norm_sub_le (A + B) C
  have h2 := norm_add_le A B
  linarith [h1, h2, hA, hB, hC]

/-- General signed-sum magnitude split: `‖Σ sᵢ·tᵢ‖ ≤ Σ bᵢ`
    (folded `norm_add_le` / `norm_sub_le`). -/
theorem magsplit_nterm_alt (t1 t2 t3 t4 : ℂ) (b1 b2 b3 b4 : ℝ)
    (hb1 : ‖t1‖ ≤ b1) (hb2 : ‖t2‖ ≤ b2) (hb3 : ‖t3‖ ≤ b3) (hb4 : ‖t4‖ ≤ b4) :
    ‖(((t1) - t2) + t3) - t4‖ ≤ b1 + b2 + b3 + b4 := by
  have hs2 := norm_sub_le (t1) t2
  have hs3 := norm_add_le ((t1) - t2) t3
  have hs4 := norm_sub_le (((t1) - t2) + t3) t4
  linarith [hb1, hs2, hb2, hs3, hb3, hs4, hb4]

end MagnitudeSplit
