/-
  The small-`s+j` exact-Rval node one-liners -- GENERATED (do not edit by hand).

  Companion to `Sweep.grid_nodes` (the certificate's 16-node binding box `s in [2,7], j in [2,4], sp in
  {3,4}`).  `grid_nodes` covers the BINDING near-star-child nodes; this file covers the rest of the small box
  `s in [0,9], j in [2,4], sp in {2,3,4,5}` (the near-tie hull vertices) -- 104 nodes -- where the
  linear `g`-bound (`gVal_le_lin_tight`) is too loose but the EXACT `Rval` bound is `norm_num`-evaluable
  (`s+j <= 22`, `sp*j <= 20`, so all exponents `< 256`).  Each is the exact-arithmetic one-liner
  `node_ns_le s j sp (by unfold Rval Romval cpl; norm_num)`, reducing the node bound `Q <= omega` to the exact
  rational `Rval(s+j) * Rval(sp)^j * cpl^11 <= Romval^(j+1)`.  Together with `grid_nodes` (binding box), the
  chain/shoulder direct bounds (E2/E3), the linear grid (large `s+j`, `Grid.lean`), and the tails, this
  discharges the near-star-child part of the finite sweep on concrete data.
-/
import R3Cert.Sweep

namespace R3Cert

open Real

/-- The small-`s+j` near-star-child nodes (outside `grid_nodes`' binding box), each `Q <= omega` by the exact
    rational reduction `node_ns_le`. -/
theorem grid_nodes_small (s j sp : ℕ)
    (h : (s, j, sp) ∈ [
      (0, 2, 2), (0, 2, 3), (0, 2, 4), (0, 2, 5), (0, 3, 2), (0, 3, 3), (0, 3, 4), (0, 3, 5),
      (0, 4, 2), (0, 4, 3), (0, 4, 4), (0, 4, 5), (1, 2, 2), (1, 2, 3), (1, 2, 4), (1, 2, 5),
      (1, 3, 2), (1, 3, 3), (1, 3, 4), (1, 3, 5), (1, 4, 2), (1, 4, 3), (1, 4, 4), (1, 4, 5),
      (2, 2, 2), (2, 2, 4), (2, 2, 5), (2, 3, 2), (2, 3, 3), (2, 3, 4), (2, 3, 5), (2, 4, 2),
      (2, 4, 3), (2, 4, 4), (2, 4, 5), (3, 2, 2), (3, 2, 4), (3, 2, 5), (3, 3, 2), (3, 3, 3),
      (3, 3, 5), (3, 4, 2), (3, 4, 3), (3, 4, 5), (4, 2, 2), (4, 2, 3), (4, 2, 5), (4, 3, 2),
      (4, 3, 3), (4, 3, 5), (4, 4, 2), (4, 4, 3), (4, 4, 5), (5, 2, 2), (5, 2, 3), (5, 2, 5),
      (5, 3, 2), (5, 3, 3), (5, 3, 5), (5, 4, 2), (5, 4, 3), (5, 4, 5), (6, 2, 2), (6, 2, 3),
      (6, 2, 5), (6, 3, 2), (6, 3, 3), (6, 3, 5), (6, 4, 2), (6, 4, 3), (6, 4, 5), (7, 2, 2),
      (7, 2, 3), (7, 2, 5), (7, 3, 2), (7, 3, 3), (7, 3, 5), (7, 4, 2), (7, 4, 3), (7, 4, 5),
      (8, 2, 2), (8, 2, 3), (8, 2, 4), (8, 2, 5), (8, 3, 2), (8, 3, 3), (8, 3, 4), (8, 3, 5),
      (8, 4, 2), (8, 4, 3), (8, 4, 4), (8, 4, 5), (9, 2, 2), (9, 2, 3), (9, 2, 4), (9, 2, 5),
      (9, 3, 2), (9, 3, 3), (9, 3, 4), (9, 3, 5), (9, 4, 2), (9, 4, 3), (9, 4, 4), (9, 4, 5)]) :
    gVal (s + j) - (j : ℝ) * omegaVal + (j : ℝ) * gVal sp + Real.log (cpl s j sp) ≤ omegaVal := by
  fin_cases h <;> exact node_ns_le _ _ _ (by unfold Rval Romval cpl; norm_num)

end R3Cert
