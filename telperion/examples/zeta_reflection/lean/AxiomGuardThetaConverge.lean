/-  AxiomGuardThetaConverge.lean -- ANDÚRIL θ-bridge kernel-axiom guard.

    NOT a `lean_lib`; run via the toolchain lean with a hand-built LEAN_PATH (lake env is
    E2BIG-dead in this island).  Expected on ALL: {propext, Classical.choice, Quot.sound} --
    no sorryAx, no ofReduceBool.

    The two DISCHARGED obligations (the entire remaining distance to the φ(14) value box):
      * convergence_obligation : ThetaGap.ConvergenceObligation  -- branch bridge
      * rate_obligation        : ThetaGap.RateObligation         -- explicit C/n

    Supporting proved terms:
      * imLnVal_succ_sub / incr_bound / imLnVal_cauchy  -- the analytic core
      * Lc_im / Lc_exp                                   -- the complex L_n bridges
      * finite_tail / sum_Ico_inv_sq_bound              -- the rate machinery

    The payoff (hypothesis-free, argument-free):
      * theta_14_box  -- the kernel φ(14) box (Γ(1/4+7i)=‖·‖exp(IΛ) ∧ −7 log π + Λ ∈ [lo,hi])

    conjecture1_proved = False.
-/
import ThetaConverge

#print axioms ThetaConverge.imLnVal_succ_sub
#print axioms ThetaConverge.incr_bound
#print axioms ThetaConverge.imLnVal_cauchy
#print axioms ThetaConverge.Lc_im
#print axioms ThetaConverge.Lc_exp
#print axioms ThetaConverge.convergence_obligation
#print axioms ThetaConverge.sum_Ico_inv_sq_bound
#print axioms ThetaConverge.finite_tail
#print axioms ThetaConverge.rate_obligation
#print axioms ThetaConverge.imLnVal_14_partial_box
#print axioms ThetaConverge.logpi_box
#print axioms ThetaConverge.gamma_14_ne_zero
#print axioms ThetaConverge.theta_14_box
