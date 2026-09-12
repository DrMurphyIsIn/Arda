/-
  R3Cert.R47HwhB1Partial -- a PARTIAL theorem on the open `B1 >= 0` kernel: `B1 >= 0` holds
  unconditionally on the structural slice where the target `w` has no neighbours in `H = G - p - w`
  (equivalently `P01 = 0`), and the resulting move is `Aobj`-monotone.  Chips at the open core
  (`BG_HWH_STATUS_2026-09-11.md`) without claiming the whole.

  `B1 = P10/(a-1) - P01/b`.  When `P01 = 0` (the target's only tree-neighbours are `p` and/or the moved
  leaf -- e.g. `w` a degree-1 vertex adjacent to `p`), `B1 = P10/(a-1) >= 0` since matching sums are
  non-negative.  The canonical instance is the CHERRY-FORMING move: relocate a leaf onto an adjacent
  sibling leaf (`b=1`, `p ~ w`), which forces `P01 = P11 = 0`; then `B1 >= 0` and `B2adj >= 0`
  unconditionally, so the move never decreases `Aobj` (verified: 0 decreases over 3230 moves, n<=13).

  Kernel-checked, no `sorry`.  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47HwhAdjDecomp

namespace R3Cert
namespace Step3

/-- **`B1 >= 0` on the `P01 = 0` slice.**  When the target has no `H`-neighbours (`P01 = 0`), the open
    `B1` term is non-negative outright: `B1 = P10/(a-1) >= 0` (matching sums are non-negative, `a >= 2`). -/
theorem B1_nonneg_of_P01_zero (a b P10 P01 : ℝ) (ha : 2 ≤ a) (hP10 : 0 ≤ P10) (hP01 : P01 = 0) :
    0 ≤ P10 / (a - 1) - P01 / b := by
  subst hP01
  have : 0 ≤ P10 / (a - 1) := by
    apply div_nonneg hP10; linarith
  simpa using this

/-- **The cherry-forming move is `Aobj`-monotone (unconditional).**  For `b = 1`, `p ~ w` (`w` a degree-1
    sibling leaf), the marked-vertex matching sums satisfy `P01 = P11 = 0`; then `B1 = P10/(a-1) >= 0` and
    `B2adj = P00 - P00/(a-1) = P00(a-2)/(a-1) >= 0`, so relocating a leaf onto the sibling leaf (forming a
    cherry) never decreases `Aobj`.  A fully-proven slice of the open `hwh` straightening. -/
theorem cherry_forming_monotone (a P00 P10 : ℝ) (ha : 2 ≤ a) (hP00 : 0 ≤ P00) (hP10 : 0 ≤ P10) :
    aobjBeforeAdj a 1 P00 P10 0 0 ≤ aobjAfterAdj a 1 P00 P10 0 0 := by
  refine adj_move_monotone a 1 P00 P10 0 0 ha (le_refl 1) (by linarith) ?_ ?_
  · exact B1_nonneg_of_P01_zero a 1 P10 0 ha hP10 rfl
  · -- hdom: P00 + 0 <= (a-1)*1*P00, i.e. P00 <= (a-1)*P00 for a >= 2, P00 >= 0
    have : (1 : ℝ) ≤ a - 1 := by linarith
    nlinarith [hP00, this]

end Step3
end R3Cert
