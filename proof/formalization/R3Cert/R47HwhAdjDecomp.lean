/-
  R3Cert.R47HwhAdjDecomp -- the ADJACENT-`p,w` leaf-relocation decomposition (the `p ~ w` case of
  `R47HwhLeafDecomp`, which assumed `p,w` non-adjacent).  Scaffolding toward `hwh`
  (see `proof/docs/BG_HWH_STATUS_2026-09-11.md`).

  When `p` and `w` are adjacent, `G = T - leaf` contains the edge `p-w`.  A matching may use it (both `p,w`
  matched to EACH OTHER); in reduced weights that term equals `Z(H) = P00` (`H = G - p - w`), contributing
  `P00/(a*b)` before and `P00/((a-1)*(b+1))` after.  Hence, over the SAME matching sums `P00,P10,P01,P11` of
  `G` restricted to matchings NOT using the `p-w` edge (`P11` = `p,w` matched to distinct non-partners):

      (AobjAfter - AobjBefore) * (a*(b+1)) = (a+b+1)*B1 + (a-b-1)*B2adj,
        B1    = P10/(a-1) - P01/b        (unchanged from the leaf case),
        B2adj = P00 - (P00+P11)/(b*(a-1)).

  Verified exact (0 mismatches, 5940 adjacent leaf-moves).  `B2adj >= 0` is provable (adjacent counting:
  `q != w`, `r != p` give `P11 <= (a-2)(b-1) P00`, so `P00+P11 <= (a-1)b P00`); taken here as the hypothesis
  `hdom : P00 + P11 <= (a-1)*b*P00`.  The open core is again `B1 >= 0`.

  Kernel-checked, no `sorry`.  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47HwhLeafDecomp

namespace R3Cert
namespace Step3

/-- Objective before an adjacent (`p ~ w`) leaf move: the non-adjacent form plus the `p-w`-edge term. -/
noncomputable def aobjBeforeAdj (a b P00 P10 P01 P11 : ℝ) : ℝ :=
  P00 * (a + 1) / a + P10 / a + P01 * (a + 1) / (a * b) + P11 / (a * b) + P00 / (a * b)

/-- Objective after an adjacent leaf move. -/
noncomputable def aobjAfterAdj (a b P00 P10 P01 P11 : ℝ) : ℝ :=
  P00 * (b + 2) / (b + 1) + P10 * (b + 2) / ((a - 1) * (b + 1))
    + P01 / (b + 1) + P11 / ((a - 1) * (b + 1)) + P00 / ((a - 1) * (b + 1))

/-- **The adjacent-`p,w` leaf decomposition identity.** -/
theorem hwh_adj_decomp (a b P00 P10 P01 P11 : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) :
    (aobjAfterAdj a b P00 P10 P01 P11 - aobjBeforeAdj a b P00 P10 P01 P11) * (a * (b + 1))
      = (a + b + 1) * (P10 / (a - 1) - P01 / b)
        + (a - b - 1) * (P00 - (P00 + P11) / (b * (a - 1))) := by
  have ha0 : a ≠ 0 := by linarith
  have ha1 : a - 1 ≠ 0 := by linarith
  have hb0 : b ≠ 0 := by linarith
  have hb1 : b + 1 ≠ 0 := by linarith
  unfold aobjAfterAdj aobjBeforeAdj
  field_simp
  ring

/-- **`B2adj >= 0`** from the adjacent combinatorial bound `P00 + P11 <= (a-1)*b*P00`. -/
theorem B2adj_nonneg (a b P00 P11 : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b)
    (hdom : P00 + P11 ≤ (a - 1) * b * P00) : 0 ≤ P00 - (P00 + P11) / (b * (a - 1)) := by
  have hb0 : 0 < b := by linarith
  have ha1 : 0 < a - 1 := by linarith
  rw [sub_nonneg, div_le_iff₀ (by positivity)]
  nlinarith [hdom]

/-- **The adjacent leaf move is `Aobj`-monotone** when `B1 >= 0`, the adjacent bound holds, and the move
    goes to strictly-lower degree (`b+1 <= a`).  The open input is again `0 <= B1`. -/
theorem adj_move_monotone (a b P00 P10 P01 P11 : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) (hab : b + 1 ≤ a)
    (hB1 : 0 ≤ P10 / (a - 1) - P01 / b) (hdom : P00 + P11 ≤ (a - 1) * b * P00) :
    aobjBeforeAdj a b P00 P10 P01 P11 ≤ aobjAfterAdj a b P00 P10 P01 P11 :=
  monotone_of_decomp _ _ _ _ a b (hwh_adj_decomp a b P00 P10 P01 P11 ha hb) ha hb hab hB1
    (B2adj_nonneg a b P00 P11 ha hb hdom)

end Step3
end R3Cert
