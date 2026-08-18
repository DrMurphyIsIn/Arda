import R3Cert.R47Parse
import R3Cert.BridgeStep4c
import R3Cert.PotentialFinal
import R3Cert.R47StepSize
import R3Cert.ExactCruxes

/-!
  # Rate port, step 4: `Z ≤ rhoB^n`

  The stratum-(i) rate bound `pi(T) ≤ (4/3) rhoB^n` (`P5_SEAM_DESIGN.md`,
  `rate_bound_fixed_n.py`) is a four-step argument:
  (1) the phantom-root split `pi = A0 + A1/d`, `Z = A0 + A1/(d+1)`;
  (2) `S ≤ 1` at a leaf root; (3) `R = (1+S/d)/(1+S/(d+1)) ≤ 4/3` (leaf root);
  (4) `Z ≤ rhoB^n`.

  This file lands step (4) as a genuine assembly of already-green lemmas — no new
  mathematics — closing the Z-bound corner of `HypRatePort`:

    `Ztot (dtSub t) = Ztot (litRealize (parseB t))`   (`Ztot_dtSub_eq_lit`, green)
      `= exp (logPhi (parseB t)) · rhoB ^ (Vb (parseB t))`  (`exp_logPhi_mul_rhoB_pow`, green)
      `= exp (logPhi (parseB t)) · rhoB ^ (usize t)`   (`Vb_parseB`, green)
      `≤ 1 · rhoB ^ (usize t)`                          (`phi_le_one`: exp(logPhi) ≤ 1)

  Steps (1)-(3) — the phantom-root reparametrization giving `R ≤ 4/3` (the leaf
  rooting, `A0/A1` split, `S ≤ 1` injection) — remain for the full `pi_le_rate`;
  the ground truth is `rate_bound_fixed_n.py` (exact on every tree ≤ 9).
  conjecture1_proved = False.
-/

namespace R3Cert
namespace Step3

open RTree

/-- **Step 4 of the rate port**: `Ztot (dtSub t) ≤ rhoB ^ (usize t)` — the
    phantom-root partition function of any tree is bounded by `rhoB^n`, assembled
    from the parse identity, the local amplitude bridge, and `phi_le_one`. -/
theorem Ztot_dtSub_le_rhoB_pow (t : UTree) : Ztot (dtSub t) ≤ rhoB ^ usize t := by
  have hb : Real.exp (logPhi (parseB t)) * rhoB ^ (usize t)
      = Ztot (litRealize (parseB t)) := by
    have h := exp_logPhi_mul_rhoB_pow (parseB t)
    rwa [Vb_parseB] at h
  rw [Ztot_dtSub_eq_lit t, ← hb]
  have hexp : Real.exp (logPhi (parseB t)) ≤ 1 := by
    calc Real.exp (logPhi (parseB t))
        ≤ Real.exp 0 := Real.exp_le_exp.mpr (phi_le_one (parseB t))
      _ = 1 := Real.exp_zero
  have hpow : (0 : ℝ) ≤ rhoB ^ usize t := le_of_lt (pow_pos rhoB_pos _)
  calc Real.exp (logPhi (parseB t)) * rhoB ^ usize t
      ≤ 1 * rhoB ^ usize t := mul_le_mul_of_nonneg_right hexp hpow
    _ = rhoB ^ usize t := one_mul _

end Step3
end R3Cert
