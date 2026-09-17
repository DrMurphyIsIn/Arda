/-
  R3Cert.R47HwhLeafDecomp -- the exact analytic decomposition of the `Aobj` change under a LEAF
  RELOCATION, and the monotonicity criterion it yields.  Scaffolding toward `hwh` (the tree->cherry-
  backbone straightening; see `proof/docs/BG_HWH_STATUS_2026-09-11.md`).

  Setup (proved on paper / exhaustively de-risked in `proof/verification/hwh_leaf_decomposition.py`):
  relocating a leaf from a degree-`a` vertex `p` to a non-adjacent degree-`b` vertex `w` changes `Aobj`
  by an amount that, in terms of the four matching sums `P00,P10,P01,P11` of `G = T - leaf`
  (classified by whether `p`/`w` are matched, their degree factors removed), satisfies the EXACT identity

      (AobjAfter - AobjBefore) * (a*(b+1)) = (a+b+1)*B1 + (a-b-1)*B2,
        B1 = P10/(a-1) - P01/b,   B2 = P00 - P11/(b*(a-1)).

  This file formalizes, over abstract nonnegative reals, (i) the identity, (ii) that the proven
  combinatorial bound `P11 <= (a-1)*b*P00` gives `B2 >= 0`, and (iii) the monotonicity implication:
  `B1 >= 0`, that bound, and `b+1 <= a` force `AobjBefore <= AobjAfter`.

  The matching-sum inputs (that `AobjBefore/After` equal the P-expressions, and `P11 <= (a-1)*b*P00`)
  are the hypotheses -- both established on paper (the latter by subset-domination + counting); a full
  Lean discharge needs a weighted-matching theory bridged to the cavity `Aobj`, which is future work.
  `B1 >= 0` under the min-degree defect-reducing selection remains the open core.

  Kernel-checked, no `sorry`.  conjecture1_proved = False.
-/
import Mathlib

namespace R3Cert
namespace Step3

/-- `AobjBefore`: the objective of the original tree, in the four-matching-sum coordinates. -/
noncomputable def aobjBefore (a b P00 P10 P01 P11 : ℝ) : ℝ :=
  P00 * (a + 1) / a + P10 / a + P01 * (a + 1) / (a * b) + P11 / (a * b)

/-- `AobjAfter`: the objective after relocating the leaf to `w`. -/
noncomputable def aobjAfter (a b P00 P10 P01 P11 : ℝ) : ℝ :=
  P00 * (b + 2) / (b + 1) + P10 * (b + 2) / ((a - 1) * (b + 1))
    + P01 / (b + 1) + P11 / ((a - 1) * (b + 1))

/-- `B1 = P10/(a-1) - P01/b`. -/
noncomputable def leafB1 (a b P10 P01 : ℝ) : ℝ := P10 / (a - 1) - P01 / b

/-- `B2 = P00 - P11/(b(a-1))`. -/
noncomputable def leafB2 (a b P00 P11 : ℝ) : ℝ := P00 - P11 / (b * (a - 1))

/-- **The exact leaf-move decomposition identity.** -/
theorem hwh_leaf_decomp (a b P00 P10 P01 P11 : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) :
    (aobjAfter a b P00 P10 P01 P11 - aobjBefore a b P00 P10 P01 P11) * (a * (b + 1))
      = (a + b + 1) * leafB1 a b P10 P01 + (a - b - 1) * leafB2 a b P00 P11 := by
  have ha0 : a ≠ 0 := by linarith
  have ha1 : a - 1 ≠ 0 := by linarith
  have hb0 : b ≠ 0 := by linarith
  have hb1 : b + 1 ≠ 0 := by linarith
  unfold aobjAfter aobjBefore leafB1 leafB2
  field_simp
  ring

/-- **`B2 >= 0` from the proven combinatorial bound** `P11 <= (a-1)*b*P00`. -/
theorem leafB2_nonneg (a b P00 P11 : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b)
    (hdom : P11 ≤ (a - 1) * b * P00) : 0 ≤ leafB2 a b P00 P11 := by
  have hb0 : 0 < b := by linarith
  have ha1 : 0 < a - 1 := by linarith
  unfold leafB2
  rw [sub_nonneg, div_le_iff₀ (by positivity)]
  nlinarith [hdom]

/-- **The abstract monotonicity criterion**: given the decomposition, `B1 >= 0`, `B2 >= 0`, and the
    strictly-lower-degree condition `b+1 <= a`, the move does not decrease the objective. -/
theorem monotone_of_decomp (before after b1 b2 a b : ℝ)
    (hdec : (after - before) * (a * (b + 1)) = (a + b + 1) * b1 + (a - b - 1) * b2)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hab : b + 1 ≤ a) (hB1 : 0 ≤ b1) (hB2 : 0 ≤ b2) :
    before ≤ after := by
  have hpos : 0 < a * (b + 1) := mul_pos (by linarith) (by linarith)
  have hrhs : 0 ≤ (a + b + 1) * b1 + (a - b - 1) * b2 :=
    add_nonneg (mul_nonneg (by linarith) hB1) (mul_nonneg (by linarith) hB2)
  rw [← sub_nonneg]
  by_contra hcon
  push_neg at hcon
  nlinarith [hdec, mul_neg_of_neg_of_pos hcon hpos, hrhs]

/-- **The leaf move is `Aobj`-monotone** whenever `B1 >= 0`, the combinatorial bound holds, and the move
    goes to strictly-lower degree (`b+1 <= a`).  Combines the exact decomposition, `leafB2_nonneg`, and
    the abstract criterion.  The remaining OPEN input is `0 <= B1` under the min-degree defect-reducing
    selection (the sharp residual of the leaf case). -/
theorem leaf_move_monotone (a b P00 P10 P01 P11 : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) (hab : b + 1 ≤ a)
    (hB1 : 0 ≤ leafB1 a b P10 P01) (hdom : P11 ≤ (a - 1) * b * P00) :
    aobjBefore a b P00 P10 P01 P11 ≤ aobjAfter a b P00 P10 P01 P11 :=
  monotone_of_decomp _ _ _ _ a b (hwh_leaf_decomp a b P00 P10 P01 P11 ha hb) ha hb hab hB1
    (leafB2_nonneg a b P00 P11 ha hb hdom)

end Step3
end R3Cert
