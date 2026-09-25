/-  RS_AxiomGuardB3.lean -- kernel-axiom guard of lane RS, brick B3 parts 2-4
    (RS_B3: exact saddle-point reduction; RS_B3Bound: analytic estimates + the explicit C0 remainder
    bound; RS_Bridge: the Riemann-Siegel formula for Hardy's Z with explicit remainder).

    A `lean_lib` (not a default target).  Run as

        lake build RS_AxiomGuardB3 && lake env lean RS_AxiomGuardB3.lean

    Expected on EVERY line: a subset of {propext, Classical.choice, Quot.sound}.  No `sorryAx`
    (nothing is assumed), no `Lean.ofReduceBool` (nothing is compiled), no new axiom.

    Registry anchors (proposed):
      * AND_rs_remainder_c0 (B3): `RSInt.rs_remainder_C0` -- for t >= 10000, 0 < p, cos(2 pi p) ≠ 0,
        |phi - thetaMain t| <= 1/t:
        |2 Re(e^{i phi} rsRem t) - (-1)^(N+1) (t/2pi)^(-1/4) Psi(p)| <= 2 t^(-3/4).
      * AND_rs_Z_c0 (B3, phase discharged): `RSInt.rs_Z_C0` -- the same for Re Lambda(1/2+it)/M with
        the island's branch-correct theta.

    conjecture1_proved = False.  An explicit finite-height remainder inequality; nothing here bears
    on the Riemann Hypothesis.
-/
import RS_Bridge


/-! ### RS_B3 (15 theorems) -/
#print axioms RSInt.rsAlpha_pos
#print axioms RSInt.rsAlpha_sq
#print axioms RSInt.t_eq_rsAlpha
#print axioms RSInt.rsNn_le
#print axioms RSInt.rsAlpha_lt
#print axioms RSInt.rsFrac_lt_one
#print axioms RSInt.rsAlpha_eq
#print axioms RSInt.rsD_add_nat
#print axioms RSInt.upLine_ne_zero
#print axioms RSInt.rsG_cpow_factor
#print axioms RSInt.integrable_upLine_cpow
#print axioms RSInt.integrable_J2_integrand
#print axioms RSInt.rsRem_factor
#print axioms RSInt.rs_phase
#print axioms RSInt.rs_remainder_exact

/-! ### RS_B3Bound (30 theorems) -/
#print axioms RSInt.integral_Ioi_sq_mul_exp_neg_mul_sq
#print axioms RSInt.integral_sq_mul_exp_neg_mul_sq
#print axioms RSInt.norm_rsD_ge_two_pi_im
#print axioms RSInt.logTaylor_three
#print axioms RSInt.rsPhi_eq_exp
#print axioms RSInt.norm_rsPhi_sub_one_le
#print axioms RSInt.saddle_X_mem
#print axioms RSInt.saddle_hasDerivAt
#print axioms RSInt.saddle_arg_le
#print axioms RSInt.norm_gauss_rsPhi_le
#print axioms RSInt.integrable_sq_mul_exp_neg_mul_sq
#print axioms RSInt.rsD_midline_re_im
#print axioms RSInt.two_le_norm_rsD_midline
#print axioms RSInt.rsJ_line_eq
#print axioms RSInt.rsJ_eq_mid
#print axioms RSInt.norm_rsJ_le
#print axioms RSInt.norm_w_eq
#print axioms RSInt.sqrt_two_le_three_halves
#print axioms RSInt.rsPhi_zero
#print axioms RSInt.norm_exp_gauss_diag
#print axioms RSInt.norm_E1_integrand_near
#print axioms RSInt.norm_E1_integrand_far
#print axioms RSInt.norm_rsE1_le
#print axioms RSInt.E1_const_le
#print axioms RSInt.rsAlpha_ge_39
#print axioms RSInt.rs_remainder_C0_alpha
#print axioms RSInt.rsAlpha_rpow_neg_half
#print axioms RSInt.rsAlpha_rpow_neg_three_halves
#print axioms RSInt.two_pi_rpow_three_quarters_le
#print axioms RSInt.rs_remainder_C0

/-! ### RS_Bridge (2 theorems) -/
#print axioms RSInt.rsThetaMain_eq_thetaMain
#print axioms RSInt.rs_Z_C0
