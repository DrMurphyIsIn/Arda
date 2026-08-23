/-
  Bridge STEP 4k: the amplitude payoff -- the limiting hub amplitude does not exceed its tie value.

  The bridge capstones (`amplitude_bridge_logPhi` / `amplitude_bridge_real'`) show the hub amplitude
  ratio converges to `exp (logPhi b) * rhoB ^ (Vb b)`.  Composed with the capstone
  `phi_le_one : logPhi b <= 0`, that limit value is `<= rhoB ^ (Vb b)` -- i.e. grafting a branch `b`
  onto a saturated hub cannot increase the limiting amplitude beyond the pure-arm (tie) value.

  This is the one-line `le_of_tendsto`-style corollary flagged in BRIDGE_AUDIT_20260822.md: it makes
  the bridge's payoff explicit and CI-checked.  It is NOT new mathematics -- `exp` monotonicity plus
  `phi_le_one` -- and it does NOT close Conjecture 1: the R7/G7 assembly (composing this per-branch
  bound over an arbitrary tree, plus root-invariance) and Gap 1 (the R3 master inequality that
  `phi_le_one` rests on) remain.  Downstream, `amplitude_limit_le_tie` feeds `ge_of_tendsto` /
  `le_of_tendsto` against `amplitude_bridge_real'` to bound the real permanent-ratio limit.

  Genuine proofs (no `sorry`).  conjecture1_proved=False.
-/
import Mathlib
import R3Cert.BridgeStep4j
import R3Cert.PotentialFinal
import R3Cert.ExactCruxes

namespace R3Cert

/-- `exp (logPhi b) <= 1`, from the capstone `phi_le_one`. -/
theorem exp_logPhi_le_one (b : Branch) : Real.exp (logPhi b) ≤ 1 :=
  Real.exp_le_one_iff.mpr (phi_le_one b)

/-- **The limiting hub amplitude does not exceed its tie value.**
    `exp (logPhi b) * rhoB ^ (Vb b) <= rhoB ^ (Vb b)` -- the bridge limit value bounded by
    `phi_le_one`.  This is the target `exp (logPhi b) * rhoB ^ (Vb b)` of the unconditional Tendsto
    capstones `amplitude_bridge_logPhi` (Ztot level) and `amplitude_bridge_real'` (real Laplacian). -/
theorem amplitude_limit_le_tie (b : Branch) :
    Real.exp (logPhi b) * rhoB ^ (Vb b) ≤ rhoB ^ (Vb b) :=
  mul_le_of_le_one_left (pow_nonneg rhoB_pos.le _) (exp_logPhi_le_one b)

end R3Cert
