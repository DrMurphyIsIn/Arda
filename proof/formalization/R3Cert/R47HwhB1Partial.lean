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

/-- **`B1 >= 0` under g-DOMINANCE** (the next step on the open kernel).  Recall
    `B1 = avg_{q~p} g(q) - avg_{r~w} g(r)` with `g(v) = Z(H-v)/deg_v` (so `P10 = sum_q g(q)`,
    `P01 = sum_r g(r)`).  If there is a threshold `M` with every `p`-neighbour's `g`-value `>= M` and every
    `w`-neighbour's `g`-value `<= M`, then `avg_{q~p} g >= M >= avg_{r~w} g`, hence `B1 >= 0`.

    This is a genuine sufficient condition for the open `B1` kernel, strictly broader than the `P01 = 0`
    slice: verified sound (g-dominance => B1 >= 0, 106/106) and non-vacuous (covers ~69% of defect-reducing
    lower-degree leaf moves; every defective tree tested has >= 1 g-dominant straightening move).  The open
    kernel is now: does every non-backbone tree admit a g-DOMINANT defect-reducing move? -/
theorem B1_nonneg_of_gdominance {ιq ιr : Type*} (Qs : Finset ιq) (Rs : Finset ιr)
    (gq : ιq → ℝ) (gr : ιr → ℝ) (M : ℝ) (hQne : Qs.Nonempty) (hRne : Rs.Nonempty)
    (hQ : ∀ q ∈ Qs, M ≤ gq q) (hR : ∀ r ∈ Rs, gr r ≤ M) :
    (∑ r ∈ Rs, gr r) / (Rs.card : ℝ) ≤ (∑ q ∈ Qs, gq q) / (Qs.card : ℝ) := by
  have hqc : (0:ℝ) < (Qs.card : ℝ) := by exact_mod_cast hQne.card_pos
  have hrc : (0:ℝ) < (Rs.card : ℝ) := by exact_mod_cast hRne.card_pos
  have h1 : M ≤ (∑ q ∈ Qs, gq q) / (Qs.card : ℝ) := by
    rw [le_div_iff₀ hqc, mul_comm]
    calc (Qs.card : ℝ) * M = ∑ _q ∈ Qs, M := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ q ∈ Qs, gq q := Finset.sum_le_sum hQ
  have h2 : (∑ r ∈ Rs, gr r) / (Rs.card : ℝ) ≤ M := by
    rw [div_le_iff₀ hrc, mul_comm]
    calc ∑ r ∈ Rs, gr r ≤ ∑ _r ∈ Rs, M := Finset.sum_le_sum hR
      _ = (Rs.card : ℝ) * M := by rw [Finset.sum_const, nsmul_eq_mul]
  linarith

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
