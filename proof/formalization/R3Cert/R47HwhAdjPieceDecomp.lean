/-
  R3Cert.R47HwhAdjPieceDecomp -- the ADJACENT-`p,w` GENERAL-piece relocation decomposition, completing the
  mechanical grid (leaf/piece x non-adjacent/adjacent). Scaffolding toward `hwh`
  (see `proof/docs/BG_HWH_STATUS_2026-09-11.md`).

  Combines the general piece (`Z = Ztot(dtSub K)`, `rho = phi/dc`; `R47HwhPieceDecomp`) with the adjacent
  `p-w`-edge correction (`R47HwhAdjDecomp`): when `p ~ w`, a matching using the `p-w` edge contributes
  `Z * Z(H) = Z * P00` (before `Z*P00/(a*b)`, after `Z*P00/((a-1)*(b+1))`).  This folds `P00` and `P11`
  together in the `(a-b-1)` coefficient:

    (AobjAfter - AobjBefore) * (a*(b+1))
      = (a-b-1)*(rho*P00 - Z*(P00+P11)/(b*(a-1)))
        + (Z*(b+1)+rho*a)/(a-1)*P10 - (Z*a+rho*(b+1))/b*P01.

  Verified exact (0 mismatches) for adjacent cherry/arm moves.  Specializations: leaf `Z=rho=1` gives the
  adjacent leaf form (`R47HwhAdjDecomp`); `Z*P00/... -> 0` (non-adjacent) gives `R47HwhPieceDecomp`.  The
  open input is again `B1 >= 0`.

  Kernel-checked, no `sorry`.  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47HwhPieceDecomp

namespace R3Cert
namespace Step3

/-- Objective before an adjacent general-piece move (general piece + `p-w`-edge correction `Z*P00/(a*b)`). -/
noncomputable def aobjBeforePAdj (Z rho a b P00 P10 P01 P11 : ℝ) : ℝ :=
  aobjBeforeP Z rho a b P00 P10 P01 P11 + Z * P00 / (a * b)

/-- Objective after an adjacent general-piece move. -/
noncomputable def aobjAfterPAdj (Z rho a b P00 P10 P01 P11 : ℝ) : ℝ :=
  aobjAfterP Z rho a b P00 P10 P01 P11 + Z * P00 / ((a - 1) * (b + 1))

/-- **The adjacent general-piece decomposition identity.** -/
theorem hwh_adj_piece_decomp (Z rho a b P00 P10 P01 P11 : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) :
    (aobjAfterPAdj Z rho a b P00 P10 P01 P11 - aobjBeforePAdj Z rho a b P00 P10 P01 P11) * (a * (b + 1))
      = (a - b - 1) * (rho * P00 - Z * (P00 + P11) / (b * (a - 1)))
        + (Z * (b + 1) + rho * a) / (a - 1) * P10 - (Z * a + rho * (b + 1)) / b * P01 := by
  have ha0 : a ≠ 0 := by linarith
  have ha1 : a - 1 ≠ 0 := by linarith
  have hb0 : b ≠ 0 := by linarith
  have hb1 : b + 1 ≠ 0 := by linarith
  unfold aobjAfterPAdj aobjBeforePAdj aobjAfterP aobjBeforeP
  field_simp
  ring

/-- **Monotonicity of an adjacent general-piece move** from non-negativity of the decomposition RHS. -/
theorem adj_piece_move_monotone (Z rho a b P00 P10 P01 P11 : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b)
    (hrhs : 0 ≤ (a - b - 1) * (rho * P00 - Z * (P00 + P11) / (b * (a - 1)))
        + (Z * (b + 1) + rho * a) / (a - 1) * P10 - (Z * a + rho * (b + 1)) / b * P01) :
    aobjBeforePAdj Z rho a b P00 P10 P01 P11 ≤ aobjAfterPAdj Z rho a b P00 P10 P01 P11 := by
  have hpos : 0 < a * (b + 1) := mul_pos (by linarith) (by linarith)
  rw [← sub_nonneg]
  by_contra hcon
  push_neg at hcon
  nlinarith [hwh_adj_piece_decomp Z rho a b P00 P10 P01 P11 ha hb,
    mul_neg_of_neg_of_pos hcon hpos, hrhs]

end Step3
end R3Cert
