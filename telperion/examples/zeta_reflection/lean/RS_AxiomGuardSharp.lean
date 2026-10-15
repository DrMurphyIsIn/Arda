/-  RS_AxiomGuardSharp.lean -- kernel-axiom guard of the RSC0 Phase 2 modules (RS_B3Sharp: the
    sharpened C0-corrected Riemann-Siegel remainder; RS_BridgeSharp: the Z formula with it).

    Not yet a `lean_lib` (lakefile.toml untouched in Phase 2).  Run, after writing the two oleans to
    `.lake/rsc0_side` with `lake env lean -o`, as

        LEAN_PATH=$PWD/.lake/rsc0_side lake env lean RS_AxiomGuardSharp.lean

    Expected on EVERY line: a subset of {propext, Classical.choice, Quot.sound}.  No `sorryAx`
    (nothing is assumed), no `Lean.ofReduceBool` (nothing is compiled), no new axiom.

    conjecture1_proved = False.  An explicit finite-height remainder inequality; nothing here bears
    on the Riemann Hypothesis.
-/
import RS_BridgeSharp

/-! ### RS_B3Sharp (66 theorems; definitions: gaussMom, rsEone, cMain, cEtwo, cS) -/
#print axioms RSInt.integrable_abs_pow_mul_exp
#print axioms RSInt.gaussMom_eq
#print axioms RSInt.gaussMom_odd
#print axioms RSInt.gaussMom_even
#print axioms RSInt.Gamma_three_halves'
#print axioms RSInt.Gamma_five_halves'
#print axioms RSInt.Gamma_seven_halves'
#print axioms RSInt.gaussMom_0
#print axioms RSInt.gaussMom_1
#print axioms RSInt.gaussMom_2
#print axioms RSInt.gaussMom_3
#print axioms RSInt.gaussMom_4
#print axioms RSInt.gaussMom_5
#print axioms RSInt.gaussMom_6
#print axioms RSInt.gaussMom_7
#print axioms RSInt.integrable_poly_gauss
#print axioms RSInt.integral_poly_gauss
#print axioms RSInt.logTaylor_two
#print axioms RSInt.logTaylor_four
#print axioms RSInt.norm_rsPhi_sub_one_le'
#print axioms RSInt.rsEone_line
#print axioms RSInt.sqrt_two_le_1415
#print axioms RSInt.sqrt_two_le_141422
#print axioms RSInt.sum_cMain
#print axioms RSInt.sum_cEtwo
#print axioms RSInt.sum_cS
#print axioms RSInt.qMain_nonneg
#print axioms RSInt.abs_one_sub_le_quad
#print axioms RSInt.amgm_sqrt_two
#print axioms RSInt.coef_le_37_10
#print axioms RSInt.near_eta_le_lin
#print axioms RSInt.near_eta_le_sq
#print axioms RSInt.near_T1
#print axioms RSInt.near_T2
#print axioms RSInt.near_T3
#print axioms RSInt.norm_E1_integrand_near'
#print axioms RSInt.sqrt_pi_div_four_pi
#print axioms RSInt.sum_cMain_gauss
#print axioms RSInt.sum_cEtwo_gauss
#print axioms RSInt.sum_cS_gauss
#print axioms RSInt.norm_rsE1_le'
#print axioms RSInt.IS_mono
#print axioms RSInt.IS_reshape
#print axioms RSInt.sum_cS_gauss_le
#print axioms RSInt.IS_9_le
#print axioms RSInt.IS_26_le
#print axioms RSInt.far_seam_le
#print axioms RSInt.far_main_le
#print axioms RSInt.main_term_le
#print axioms RSInt.etwo_term_le
#print axioms RSInt.second_term_le
#print axioms RSInt.E1_sharp_const_seam
#print axioms RSInt.E1_sharp_const_main
#print axioms RSInt.norm_rsE1_le_main
#print axioms RSInt.norm_rsE1_le_seam'
#print axioms RSInt.exp_pi_div_four_le
#print axioms RSInt.norm_rsJ_le'
#print axioms RSInt.rsAlpha_ge_26
#print axioms RSInt.rs_remainder_C0_alpha'
#print axioms RSInt.rs_remainder_C0'
#print axioms RSInt.rs_remainder_C0_alpha_of_sharp
#print axioms RSInt.rs_remainder_C0_of_sharp
#print axioms RSSeam.rs_remainder_C0_alpha_seam'
#print axioms RSSeam.rs_remainder_C0_seam'
#print axioms RSSeam.rs_remainder_C0_alpha_seam_of_sharp
#print axioms RSSeam.rs_remainder_C0_seam_of_sharp

/-! ### RS_BridgeSharp (5 theorems; definitions: none) -/
#print axioms RSInt.rs_Z_of_remainder
#print axioms RSInt.rs_Z_C0'
#print axioms RSInt.rs_Z_C0_of_sharp
#print axioms RSSeam.rs_Z_C0_seam'
#print axioms RSSeam.rs_Z_C0_seam_of_sharp
