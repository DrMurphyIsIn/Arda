/- telperion 0.1.6 | family EndpointGeomCap | input-hash ab0b231fcddb045a
   2 theorems, 2 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace EndpointGeomCap

/-- Endpoint geometric-factor cap (R = (3 / 2) > 1): for `z ≤ 1` (here `z = ‖·‖ ∈ [0,1]`)
    the entire-part factor `(R + z)/(R - z)²` is maximised at the endpoint `z = 1`,
    `((3 / 2) + z) / ((3 / 2) - z)^2 ≤ ((3 / 2) + 1) / ((3 / 2) - 1)^2`.  The σ-independent cap that
    breaks the σ↔L fixpoint in the dVP numeric coupling. -/
theorem endpoint_geom_cap_3half (z : ℝ) (hz : z ≤ 1) :
    ((3 / 2) + z) / ((3 / 2) - z) ^ 2 ≤ ((3 / 2) + 1) / ((3 / 2) - 1) ^ 2 := by
  have hd1 : (0 : ℝ) < (3 / 2) - 1 := by norm_num
  have hnz : (0 : ℝ) < (3 / 2) - z := by linarith
  gcongr
/-- Endpoint geometric-factor cap (R = 2 > 1): for `z ≤ 1` (here `z = ‖·‖ ∈ [0,1]`)
    the entire-part factor `(R + z)/(R - z)²` is maximised at the endpoint `z = 1`,
    `(2 + z) / (2 - z)^2 ≤ (2 + 1) / (2 - 1)^2`.  The σ-independent cap that
    breaks the σ↔L fixpoint in the dVP numeric coupling. -/
theorem endpoint_geom_cap_two (z : ℝ) (hz : z ≤ 1) :
    (2 + z) / (2 - z) ^ 2 ≤ (2 + 1) / (2 - 1) ^ 2 := by
  have hd1 : (0 : ℝ) < 2 - 1 := by norm_num
  have hnz : (0 : ℝ) < 2 - z := by linarith
  gcongr

end EndpointGeomCap
