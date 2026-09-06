/- telperion 0.1.6 | family MaxModulus | input-hash bd8b6bed8e3cd9f1
   2 theorems, 2 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace MaxModulus

open Complex Metric

/-- Maximum-modulus propagation on the disk of radius `(1 / 2)` about `c`:
    `f` holomorphic on `ball c (1 / 2)` (continuous up to the boundary) with
    `‖f z‖ ≤ 12` on `sphere c (1 / 2)` implies `‖f z‖ ≤ 12` throughout `ball c (1 / 2)`.
    A concrete-radius wrapper of `Complex.norm_le_of_forall_mem_frontier_norm_le`. -/
theorem max_modulus_half (f : ℂ → ℂ) (c : ℂ)
    (hd : DiffContOnCl ℂ f (ball c ((1 / 2) : ℝ)))
    (hB : ∀ z ∈ sphere c ((1 / 2) : ℝ), ‖f z‖ ≤ (12 : ℝ)) :
    ∀ z ∈ ball c ((1 / 2) : ℝ), ‖f z‖ ≤ (12 : ℝ) := by
  intro z hz
  refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd ?_
    (subset_closure hz)
  rw [frontier_ball c (by norm_num : ((1 / 2) : ℝ) ≠ 0)]
  exact hB
/-- Maximum-modulus propagation on the disk of radius `(1 / 4)` about `c`:
    `f` holomorphic on `ball c (1 / 4)` (continuous up to the boundary) with
    `‖f z‖ ≤ 3` on `sphere c (1 / 4)` implies `‖f z‖ ≤ 3` throughout `ball c (1 / 4)`.
    A concrete-radius wrapper of `Complex.norm_le_of_forall_mem_frontier_norm_le`. -/
theorem max_modulus_qtr (f : ℂ → ℂ) (c : ℂ)
    (hd : DiffContOnCl ℂ f (ball c ((1 / 4) : ℝ)))
    (hB : ∀ z ∈ sphere c ((1 / 4) : ℝ), ‖f z‖ ≤ (3 : ℝ)) :
    ∀ z ∈ ball c ((1 / 4) : ℝ), ‖f z‖ ≤ (3 : ℝ) := by
  intro z hz
  refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd ?_
    (subset_closure hz)
  rw [frontier_ball c (by norm_num : ((1 / 4) : ℝ) ≠ 0)]
  exact hB

end MaxModulus
