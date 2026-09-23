/-  AxiomGuardRSTheta.lean -- kernel-axiom guard of the Riemann-Siegel theta brick (B0), `RSTheta`.

    A `lean_lib` (not a default target). Run as

        lake build AxiomGuardRSTheta && lake env lean AxiomGuardRSTheta.lean

    Expected on EVERY line: a subset of {propext, Classical.choice, Quot.sound}. There is no
    `sorryAx` (nothing is assumed), no `Lean.ofReduceBool` (nothing is compiled), and no new axiom.

    Every theorem of `RSTheta` is printed below, 24 in all. The registry anchor of the proposed
    node `AND_theta_branch` is `RSDesignTheta.gaussBranch_theta_sub_thetaMain_le`: for every t > 0,
    the branch limit Lam of `ThetaGap.imLnVal (1/4) (t/2)` exists and satisfies
    |Lam - (t/2) log pi - ZeroFreeBridge.thetaMain t| <= 1/t.

    conjecture1_proved = False. This is a height-uniform bound on one special-function phase, not a
    proof of RH.
-/
import RSTheta

/-! ### The registry anchor (`AND_theta_branch`) and the brackets it rests on -/
#print axioms RSDesignTheta.gaussBranch_theta_sub_thetaMain_le
#print axioms RSDesignTheta.theta_sub_thetaMain
#print axioms RSDesignTheta.theta_bracket
#print axioms RSDesignTheta.lam_bracket

/-! ### The registry statement spells names in full; the probe used `open`s. Same proposition.

    The anchor's statement writes `Filter.Tendsto (ThetaGap.imLnVal ...) Filter.atTop (nhds Λ)`, so
    that its text is the registry statement verbatim. The probe it was promoted from wrote the
    same statement under `open Filter Topology ThetaGap`. The anchor proves that spelling too. -/
open Filter Topology ThetaGap in
example {t : ℝ} (ht : 0 < t) :
    ∃ Λ : ℝ, Tendsto (imLnVal (1/4) (t/2)) atTop (𝓝 Λ) ∧
      |Λ - t / 2 * Real.log Real.pi - ZeroFreeBridge.thetaMain t| ≤ 1 / t :=
  RSDesignTheta.gaussBranch_theta_sub_thetaMain_le ht

/-! ### The convex-trapezoid engine -/
#print axioms RSDesignTheta.secant_bounds
#print axioms RSDesignTheta.trapezoid_convex
#print axioms RSDesignTheta.hasDerivAt_fA
#print axioms RSDesignTheta.hasDerivAt_FA
#print axioms RSDesignTheta.gA_monotoneOn
#print axioms RSDesignTheta.gA_nonpos
#print axioms RSDesignTheta.eA_bounds
#print axioms RSDesignTheta.sum_split
#print axioms RSDesignTheta.sumE_bounds
#print axioms RSDesignTheta.imLnVal_sandwich
#print axioms RSDesignTheta.tendsto_H

/-! ### The numeric instance at t = 280000 and its elementary boxes -/
#print axioms RSDesignTheta.log2_box
#print axioms RSDesignTheta.log1mxv_box
#print axioms RSDesignTheta.logv_box
#print axioms RSDesignTheta.log1mxL_lo
#print axioms RSDesignTheta.log1mxH_hi
#print axioms RSDesignTheta.logpi_box
#print axioms RSDesignTheta.arctan560000_box
#print axioms RSDesignTheta.theta_280000_box
#print axioms RSDesignTheta.theta_280000_exists
