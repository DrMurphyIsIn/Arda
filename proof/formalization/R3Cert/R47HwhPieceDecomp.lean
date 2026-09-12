/-
  R3Cert.R47HwhPieceDecomp -- the GENERAL piece-relocation `Aobj` decomposition, extending
  `R47HwhLeafDecomp` from a single leaf to an arbitrary rigid piece (leaf / cherry / arm-of-cherries /
  sub-star).  Scaffolding toward `hwh` (see `proof/docs/BG_HWH_STATUS_2026-09-11.md`).

  Relocate a rigid piece `K` (anchor `c`, tree-degree `dc`) from a degree-`a` vertex `p` to a
  non-adjacent degree-`b` vertex `w`.  Let `G = T - K` and `P00,P10,P01,P11` its matching sums
  classified by whether `p`/`w` are matched (their degree factors removed).  The piece enters through two
  cavity scalars:
      Z   = Ztot(dtSub K)          (the piece's total matching value),
      rho = phi / dc               (phi = matchings of K with the anchor `c` unmatched, over `dc`).
  Special cases: leaf `Z=1, rho=1`; cherry `Z=3/2, rho=1/2`; arm-`j` `Z=(3/2)^j(1+j/(3(j+1))),
  rho=(3/2)^j/(j+1)`.  Verified exact (0 mismatches) in `proof/verification` for leaf/cherry/arm.

  Then the EXACT identity (proved below by `field_simp; ring`):

    (AobjAfter - AobjBefore) * (a*(b+1))
      = rho*(a-b-1)*P00 + (Z*(b+1)+rho*a)/(a-1)*P10 - (Z*a+rho*(b+1))/b*P01 - Z*(a-b-1)/(b*(a-1))*P11.

  NOTE: the clean `B2 >= 0` split of the LEAF case (`R47HwhLeafDecomp`) is special to `Z=rho=1`; for a
  general piece the `P00,P11` coefficient is `rho*(a-b-1)` and `-Z*(a-b-1)/(b(a-1))`, whose non-negativity
  needs `rho*(a-1)*b*P00 >= Z*P11` -- a piece-dependent bound (e.g. for the cherry this is 3x stronger than
  the universal leaf bound and does NOT hold unconditionally).  So monotonicity for general pieces uses the
  full right-hand side, provided here as an abstract hypothesis.

  Kernel-checked, no `sorry`.  conjecture1_proved = False.
-/
import Mathlib

namespace R3Cert
namespace Step3

/-- Objective before the piece move, in cavity+matching-sum coordinates (`Z`, `rho`, degrees `a,b`). -/
noncomputable def aobjBeforeP (Z rho a b P00 P10 P01 P11 : ℝ) : ℝ :=
  Z * (P00 + P10 / a + P01 / b + P11 / (a * b)) + rho / a * (P00 + P01 / b)

/-- Objective after relocating the piece to `w`. -/
noncomputable def aobjAfterP (Z rho a b P00 P10 P01 P11 : ℝ) : ℝ :=
  Z * (P00 + P10 / (a - 1) + P01 / (b + 1) + P11 / ((a - 1) * (b + 1)))
    + rho / (b + 1) * (P00 + P10 / (a - 1))

/-- **The general piece-relocation decomposition identity.** -/
theorem hwh_piece_decomp (Z rho a b P00 P10 P01 P11 : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) :
    (aobjAfterP Z rho a b P00 P10 P01 P11 - aobjBeforeP Z rho a b P00 P10 P01 P11) * (a * (b + 1))
      = rho * (a - b - 1) * P00 + (Z * (b + 1) + rho * a) / (a - 1) * P10
        - (Z * a + rho * (b + 1)) / b * P01 - Z * (a - b - 1) / (b * (a - 1)) * P11 := by
  have ha0 : a ≠ 0 := by linarith
  have ha1 : a - 1 ≠ 0 := by linarith
  have hb0 : b ≠ 0 := by linarith
  have hb1 : b + 1 ≠ 0 := by linarith
  unfold aobjAfterP aobjBeforeP
  field_simp
  ring

/-- **Monotonicity of a general piece move** from non-negativity of the decomposition's right-hand side. -/
theorem piece_move_monotone (Z rho a b P00 P10 P01 P11 : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b)
    (hrhs : 0 ≤ rho * (a - b - 1) * P00 + (Z * (b + 1) + rho * a) / (a - 1) * P10
        - (Z * a + rho * (b + 1)) / b * P01 - Z * (a - b - 1) / (b * (a - 1)) * P11) :
    aobjBeforeP Z rho a b P00 P10 P01 P11 ≤ aobjAfterP Z rho a b P00 P10 P01 P11 := by
  have hpos : 0 < a * (b + 1) := mul_pos (by linarith) (by linarith)
  rw [← sub_nonneg]
  by_contra hcon
  push_neg at hcon
  nlinarith [hwh_piece_decomp Z rho a b P00 P10 P01 P11 ha hb, mul_neg_of_neg_of_pos hcon hpos, hrhs]

/-- The leaf case is the specialization `Z = rho = 1`: the general RHS collapses to
    `(a+b+1)*(P10/(a-1) - P01/b) + (a-b-1)*(P00 - P11/(b*(a-1)))`, matching `R47HwhLeafDecomp`. -/
theorem hwh_piece_decomp_leaf (a b P00 P10 P01 P11 : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) :
    (aobjAfterP 1 1 a b P00 P10 P01 P11 - aobjBeforeP 1 1 a b P00 P10 P01 P11) * (a * (b + 1))
      = (a + b + 1) * (P10 / (a - 1) - P01 / b) + (a - b - 1) * (P00 - P11 / (b * (a - 1))) := by
  have ha1 : a - 1 ≠ 0 := by linarith
  have hb0 : b ≠ 0 := by linarith
  rw [hwh_piece_decomp 1 1 a b P00 P10 P01 P11 ha hb]
  field_simp
  ring

end Step3
end R3Cert
