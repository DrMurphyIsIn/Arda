/-  RS4_AxiomGuard.lean -- kernel-axiom guard of lane B4 (the Riemann-Siegel main-term evaluator).

    A `lean_lib` (not a default target).  Run as

        lake build RS4_AxiomGuard && lake env lean RS4_AxiomGuard.lean

    Expected on EVERY line: a subset of {propext, Classical.choice, Quot.sound}.  No `sorryAx`
    (nothing is assumed), no `Lean.ofReduceBool` (the certificates are checked by `decide +kernel`,
    i.e. by kernel reduction, nothing is compiled), no new axiom.

    Headlines:
      * `RS4.check_sound`      -- an accepted certificate encloses the Riemann-Siegel main term of
                                  `RSInt.rs_Z_C0` for EVERY phase with |phi - thetaMain t| <= 1/t, and
                                  discharges t >= 10000, 0 < p, cos(2 pi p) ≠ 0;
      * `RS4.rs4_Z_enclosure`  -- glued to `rs_Z_C0`: Re Lambda(1/2+it)/|Gammaℝ| within the box +- 2/1000;
      * `RS4.Demo.sign_A`      -- Re completedRiemannZeta(1/2 + 10000.5 i) > 0 (kernel-checked);
      * `RS4.Demo.sign_B`      -- Re completedRiemannZeta(1/2 + 10000 i) < 0 (kernel-checked);
      * `RS4.Demo.bad_*`       -- three tampered certificates the kernel rejects.

    conjecture1_proved = False.
-/
import RS4_Demo

#print axioms RS4.checks_of
#print axioms RS4.log_one_add_near
#print axioms RS4.lp_real
#print axioms RS4.sgnI_cast
#print axioms RS4.two_zpow_negP
#print axioms RS4.ballD_mem
#print axioms RS4.brD_mem
#print axioms RS4.negIf_mem
#print axioms RS4.oneR
#print axioms RS4.pi_lo
#print axioms RS4.pi_hi
#print axioms RS4.t_ge
#print axioms RS4.t_pos
#print axioms RS4.alpha_sq
#print axioms RS4.alpha_nonneg
#print axioms RS4.alpha_key
#print axioms RS4.A0_le
#print axioms RS4.A1_ge
#print axioms RS4.N_lt_alpha
#print axioms RS4.alpha_lt_N1
#print axioms RS4.N_eq
#print axioms RS4.frac_eq
#print axioms RS4.frac_pos
#print axioms RS4.NO_le_A0
#print axioms RS4.NO_le_A1
#print axioms RS4.p_lo
#print axioms RS4.p_hi
#print axioms RS4.N_pos
#print axioms RS4.y_lo
#print axioms RS4.y_hi
#print axioms RS4.y_nonneg
#print axioms RS4.y_le_half
#print axioms RS4.log_alpha
#print axioms RS4.lg_lo
#print axioms RS4.lg_hi
#print axioms RS4.dstate_inv
#print axioms RS4.loga_lo
#print axioms RS4.loga_hi
#print axioms RS4.thetaMain_eq
#print axioms RS4.phase_scaled
#print axioms RS4.tn_pos
#print axioms RS4.phase_lo
#print axioms RS4.phase_hi
#print axioms RS4.alpha_pos
#print axioms RS4.w_sq_alpha
#print axioms RS4.w_lo
#print axioms RS4.w_hi
#print axioms RS4.U_lo
#print axioms RS4.U_hi
#print axioms RS4.G_bounds
#print axioms RS4.V_lo
#print axioms RS4.V_hi
#print axioms RS4.psi_num_eq
#print axioms RS4.lin_le_max
#print axioms RS4.lin_ge_min
#print axioms RS4.quot_sound
#print axioms RS4.main_sum_eq
#print axioms RS4.mainBox_mem
#print axioms RS4.neg_one_pow_eq
#print axioms RS4.c0Box_mem
#print axioms RS4.zBox_e
#print axioms RS4.check_sound
#print axioms RS4.tpow_le
#print axioms RS4.rs4_Z_enclosure
#print axioms RS4.rs4_sign_pos
#print axioms RS4.rs4_sign_neg
#print axioms RS4.Demo.validA
#print axioms RS4.Demo.okA
#print axioms RS4.Demo.zA_lo
#print axioms RS4.Demo.sign_A
#print axioms RS4.Demo.hardyZ_A
#print axioms RS4.Demo.validB
#print axioms RS4.Demo.okB
#print axioms RS4.Demo.zB_hi
#print axioms RS4.Demo.sign_B
#print axioms RS4.Demo.bad_flip
#print axioms RS4.Demo.bad_narrow
#print axioms RS4.Demo.bad_psi
