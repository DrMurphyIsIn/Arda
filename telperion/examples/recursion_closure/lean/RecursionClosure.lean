/- telperion 0.1.6 | family RecursionClosure | input-hash 7bb6c17706251181
   2 theorems, 2 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace RecursionClosure

/-- **The BG per-hub SCL node-decouple assembly** (reusable, abstract reals).

    At a fixed price `muStar`, with `bV μ b = bell b + μ·bY b`, this packages
    the proven tangent-majorant (`bell_node_tangent`) + a per-hub ceiling into
    the node ceiling:

      * `htan`  : nodeVal ≤ childBellSum + tangentBracket + muStar·nodeY
                  (the proven `bell_node_tangent` at reference `s0`, plus the
                   price term `muStar·nodeY` added to both sides — here
                   `nodeVal = bell (node cs)`, `nodeY = bY (node cs)`);
      * `hceil` : childBellSum + tangentBracket + muStar·nodeY ≤ cherryVal
                  (the per-hub ceiling, `cherryVal = bV muStar cherry`);
      * ⟹ nodeVal ≤ cherryVal.

    HONEST SCOPE: packages the tangent+ceiling → node-ceiling ASSEMBLY at a
    fixed price.  Does NOT re-derive the log-tangent (that is `bell_node_tangent`)
    nor prove the all-cherry exchange (structural).  conjecture1_proved=False. -/
theorem recursion_closure_assembly
    (nodeVal childBellSum tangentBracket muStar nodeY cherryVal : ℝ)
    (htan : nodeVal ≤ childBellSum + tangentBracket + muStar * nodeY)
    (hceil : childBellSum + tangentBracket + muStar * nodeY ≤ cherryVal) :
    nodeVal ≤ cherryVal := by
  linarith

-- CONCRETE per-hub SCL node-decouple at fixed price μ* = 1/4 ∈ I = [456/3703, 3/7].
-- Grounds `recursion_closure_assembly` with concrete rational childBellSum/tangentBracket/nodeY/cherryVal;
-- htan (the proven `bell_node_tangent` + price) and hceil (the per-hub ceiling) are the ABSTRACT hypotheses.
-- Middle quantity childBellSum+tangentBracket+μ*·nodeY = 29/160 ≤ cherryVal = 1/5 (the certified ceiling).
theorem scl_node_decouple (nodeVal : ℝ)
    (htan : nodeVal
      ≤ (1/5 : ℝ) + (-1/20) + (1/4) * (1/8))
    (hceil : (1/5 : ℝ) + (-1/20) + (1/4) * (1/8) ≤ (1/5)) :
    nodeVal ≤ (1/5 : ℝ) := by
  exact recursion_closure_assembly nodeVal (1/5) (-1/20) (1/4) (1/8) (1/5) htan hceil

-- CONCRETE per-hub SCL node-decouple at fixed price μ* = 1/4 ∈ I = [456/3703, 3/7].
-- Grounds `recursion_closure_assembly` with concrete rational childBellSum/tangentBracket/nodeY/cherryVal;
-- htan (the proven `bell_node_tangent` + price) and hceil (the per-hub ceiling) are the ABSTRACT hypotheses.
-- Middle quantity childBellSum+tangentBracket+μ*·nodeY = 29/160 ≤ cherryVal = 29/160 (the certified ceiling).
theorem scl_node_decouple_tie (nodeVal : ℝ)
    (htan : nodeVal
      ≤ (1/5 : ℝ) + (-1/20) + (1/4) * (1/8))
    (hceil : (1/5 : ℝ) + (-1/20) + (1/4) * (1/8) ≤ (29/160)) :
    nodeVal ≤ (29/160 : ℝ) := by
  exact recursion_closure_assembly nodeVal (1/5) (-1/20) (1/4) (1/8) (29/160) htan hceil

-- TIE: the all-cherry config gives EQUALITY of the middle quantity with the
-- cherry ceiling (29/160 = 29/160), composing with the tie of `tight_cap_enclosure`.
example : ((1/5 : ℝ) + (-1/20) + (1/4) * (1/8)) = (29/160) := by norm_num

end RecursionClosure
