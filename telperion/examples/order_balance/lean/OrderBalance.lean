/- telperion order-balance example | family OrderBalance
   2 theorems, 2 generation-time self-checks passed.
   The integer zero/pole-order hinge at the 1-line (`ζ(1+it) ≠ 0`),
   generalizing `zeta_boundary_contradiction` (examples/zero_free_bridge).
   Residue limits are abstract-real hypotheses; only the finite linear
   order-balance hinge is certified.  conjecture1_proved = False. -/

import Mathlib

namespace OrderBalance

/-- ORDER-BALANCE BOUNDARY CONTRADICTION (weights a = (3, 4, 1); orders k = (1, 1)),
    the finite integer/linear hinge of the classical dVP boundary `ζ(1+it) ≠ 0`, generalized
    from `zeta_boundary_contradiction` (examples/zero_free_bridge).  The residue LIMITS `P_j`
    are abstract reals (real-line `residue_logDeriv`: `(z-z₀)·logDeriv ζ → order`, supplied
    elsewhere); from the cosine positivity `0 ≤ Σ a_j·P_j`, the pole `P₀ = 1`, and the
    order-`k_j` polar bounds `P_j ≤ -k_j` (j ≥ 1), the order balance `a₀ ≥ Σ a1·k1, a2·k2` is
    forced — but the certificate has `a₀ < Σ a_j·k_j` (deficit 2 > 0), so `False`.
    Boundary (c=0) hinge only; FEEDS the classical region, NOT a proof of RH. -/
theorem ob_dvp_341 (P0 P1 P2 : ℝ) (k1 k2 : ℤ)
    (hk1 : 1 ≤ k1) (hk2 : 1 ≤ k2)
    (hpos : (0 : ℝ) ≤ 3 * P0 + 4 * P1 + 1 * P2)
    (hpole : P0 = 1)
    (hb1 : P1 ≤ -(k1 : ℝ)) (hb2 : P2 ≤ -(k2 : ℝ)) :
    False := by
  have hk1r : (1 : ℝ) ≤ (k1 : ℝ) := by exact_mod_cast hk1
  have hk2r : (1 : ℝ) ≤ (k2 : ℝ) := by exact_mod_cast hk2
  linarith [hpos, hpole, hb1, hb2, hk1r, hk2r]
/-- ORDER-BALANCE BOUNDARY CONTRADICTION (weights a = (20, 30, 12, 2); orders k = (1, 1, 1)),
    the finite integer/linear hinge of the classical dVP boundary `ζ(1+it) ≠ 0`, generalized
    from `zeta_boundary_contradiction` (examples/zero_free_bridge).  The residue LIMITS `P_j`
    are abstract reals (real-line `residue_logDeriv`: `(z-z₀)·logDeriv ζ → order`, supplied
    elsewhere); from the cosine positivity `0 ≤ Σ a_j·P_j`, the pole `P₀ = 1`, and the
    order-`k_j` polar bounds `P_j ≤ -k_j` (j ≥ 1), the order balance `a₀ ≥ Σ a1·k1, a2·k2, a3·k3` is
    forced — but the certificate has `a₀ < Σ a_j·k_j` (deficit 24 > 0), so `False`.
    Boundary (c=0) hinge only; FEEDS the classical region, NOT a proof of RH. -/
theorem ob_fejer_deg3 (P0 P1 P2 P3 : ℝ) (k1 k2 k3 : ℤ)
    (hk1 : 1 ≤ k1) (hk2 : 1 ≤ k2) (hk3 : 1 ≤ k3)
    (hpos : (0 : ℝ) ≤ 20 * P0 + 30 * P1 + 12 * P2 + 2 * P3)
    (hpole : P0 = 1)
    (hb1 : P1 ≤ -(k1 : ℝ)) (hb2 : P2 ≤ -(k2 : ℝ)) (hb3 : P3 ≤ -(k3 : ℝ)) :
    False := by
  have hk1r : (1 : ℝ) ≤ (k1 : ℝ) := by exact_mod_cast hk1
  have hk2r : (1 : ℝ) ≤ (k2 : ℝ) := by exact_mod_cast hk2
  have hk3r : (1 : ℝ) ≤ (k3 : ℝ) := by exact_mod_cast hk3
  linarith [hpos, hpole, hb1, hb2, hb3, hk1r, hk2r, hk3r]

end OrderBalance
