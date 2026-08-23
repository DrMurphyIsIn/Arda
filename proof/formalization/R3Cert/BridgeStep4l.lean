/-
  Bridge STEP 4l: THE AMPLITUDE-LIMIT COMPOSITION -- per-branch bound feeding the objective.

  This file wires the two CI-green capstones into a single per-branch amplitude bound:

    * `phi_le_one`               (PotentialFinal): `logPhi b ≤ 0`  -- the WEAK Phi ≤ 1 bound;
    * `exp_logPhi_mul_rhoB_pow`  (BridgeStep4c) : `exp(logPhi b) * rhoB^(Vb b) = Ztot (litRealize b)`.

  The composition:

    * `amplitude_limit_le_tie`   : `exp(logPhi b) * rhoB^(Vb b) ≤ rhoB^(Vb b)`.
        The amplitude limit of any gadget branch is at most the TIE value `rhoB^(Vb b)`
        (attained exactly when `logPhi b = 0`, i.e. at the exact tie).  Proof: `exp(logPhi b) ≤ 1`
        from `phi_le_one` via `Real.exp_le_one_iff`, then `mul_le_of_le_one_left` against the
        nonnegative tie factor.
    * `Ztot_litRealize_le_tie`   : `Ztot (litRealize b) ≤ rhoB^(Vb b)`.
        The SAME bound transported through `exp_logPhi_mul_rhoB_pow` onto the raw matching
        partition function of the literal realization -- the `Ztot`-of-a-realization object that
        the R4-R7 objective `Aobj t = Ztot (dtRealize t)` (R47Tree) is built from.  This is the
        per-branch amplitude input the objective layer consumes.

  SCOPE / HONESTY NOTE.  This is the composition of the WEAK master bound (`Phi ≤ 1`), NOT the
  TIGHT master inequality `F(C) ≤ env★(μ_C)` with quantified slack away from the tie, which
  remains OPEN (MASTER_INEQUALITY.md; conjecture1_proved=False).  The bound proved here is exactly
  `≤ rhoB^(Vb b)` with equality possible at the tie -- it does not by itself certify strict slack
  off the tie.  It supplies the per-branch amplitude ceiling that the objective assembly needs;
  the strict-off-tie residual is the open GAP-1 obligation, not discharged here.

  WIRING NOTE (CI-pending).  This module is NOT yet imported by the aggregator `R3Cert.lean`
  (which the authoring rule forbids editing here); its transitive dependencies
  (`BridgeStep4c`, `PotentialFinal`) ARE already in the build graph.  To place it under CI, the
  owning session adds `import R3Cert.BridgeStep4l` to `R3Cert.lean`.  Name-checked against the
  vendored Mathlib (`.lake/packages/mathlib`, v4.32.0); NOT locally lake-built.

  Genuine proofs (no `sorry`).  conjecture1_proved=False.
-/
import Mathlib
import R3Cert.BridgeStep4c
import R3Cert.PotentialFinal

namespace R3Cert

open RTree

/-- **The amplitude limit is at most the tie value.**  For every gadget branch `b`, the DEC
    amplitude limit `exp(logPhi b) * rhoB^(Vb b)` is bounded by the tie factor `rhoB^(Vb b)`,
    with equality exactly when `logPhi b = 0` (the exact tie).  Immediate from `phi_le_one`. -/
theorem amplitude_limit_le_tie (b : Branch) :
    Real.exp (logPhi b) * rhoB ^ (Vb b) ≤ rhoB ^ (Vb b) := by
  have hexp : Real.exp (logPhi b) ≤ 1 := Real.exp_le_one_iff.mpr (phi_le_one b)
  have hpow : (0 : ℝ) ≤ rhoB ^ (Vb b) := (pow_pos rhoB_pos (Vb b)).le
  exact mul_le_of_le_one_left hpow hexp

/-- **The per-branch amplitude bound feeding the objective.**  The raw matching partition
    function of the literal realization of any branch `b` is at most the tie value
    `rhoB^(Vb b)`.  This is `amplitude_limit_le_tie` transported through the amplitude identity
    `exp_logPhi_mul_rhoB_pow`; `Ztot (litRealize b)` is the `Ztot`-of-a-realization object shared
    with the R4-R7 objective `Aobj t = Ztot (dtRealize t)` (R47Tree). -/
theorem Ztot_litRealize_le_tie (b : Branch) :
    Ztot (litRealize b) ≤ rhoB ^ (Vb b) := by
  rw [← exp_logPhi_mul_rhoB_pow b]
  exact amplitude_limit_le_tie b

end R3Cert
