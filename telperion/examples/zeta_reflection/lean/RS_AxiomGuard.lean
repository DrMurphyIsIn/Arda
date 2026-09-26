/-  RS_AxiomGuard.lean -- kernel-axiom guard of lane RS (ANDURIL Riemann-Siegel bricks B2 and B3).

    A `lean_lib` (not a default target).  Run as

        lake build RS_AxiomGuard && lake env lean RS_AxiomGuard.lean

    Expected on EVERY line: a subset of {propext, Classical.choice, Quot.sound}.  No `sorryAx`
    (nothing is assumed), no `Lean.ofReduceBool` (nothing is compiled), no new axiom.

    Registry anchors (proposed):
      * AND_rs_representation (B2): `RSInt.riemann_siegel_integral` -- Riemann's integral
        representation of zeta(s) for every complex s outside {1,3,5,...}, with the residue
        bookkeeping  sum_{n<=N} n^-s + chi(s) sum_{m<=M} m^(s-1) + two remainder line integrals;
        and its critical-line forms `RSInt.completedRiemannZeta_eq_rs`, `RSInt.completed_re_eq_rs_cos`.
      * B3 part 1 (C0): `RSInt.rsJ_C0` -- 2 Re(e^{-i pi/8} rsJ p) = cos(2 pi (p^2-p-1/16))/cos(2 pi p).

    conjecture1_proved = False.  Exact integral identities for zeta and a special-function value;
    nothing here bears on the Riemann Hypothesis.
-/
import RS_C0


/-! ### RS_Strip (15 theorems) -/
#print axioms RSInt.exp_quad_le
#print axioms RSInt.integrable_exp_quad
#print axioms RSInt.integrable_of_continuous_of_tail
#print axioms RSInt.strip_integral_eq
#print axioms RSInt.lineUp_point
#print axioms RSInt.lineDn_point
#print axioms RSInt.lineUp_eq_rot
#print axioms RSInt.lineDn_eq_rot
#print axioms RSInt.re_sub_im_rotUp
#print axioms RSInt.re_add_im_rotDn
#print axioms RSInt.norm_rot_ge
#print axioms RSInt.norm_one_add_I
#print axioms RSInt.norm_one_sub_I
#print axioms RSInt.lineUp_eq_of_strip
#print axioms RSInt.lineDn_eq_of_strip

/-! ### RS_Kernel (68 theorems) -/
#print axioms RSInt.pi_ne_zero'
#print axioms RSInt.rsD_eq_zero_iff
#print axioms RSInt.rsD_int
#print axioms RSInt.differentiable_rsD
#print axioms RSInt.hasDerivAt_rsD
#print axioms RSInt.deriv_rsD_int_ne_zero
#print axioms RSInt.exp_neg_piI
#print axioms RSInt.rsD_add_one
#print axioms RSInt.rsG_add_one
#print axioms RSInt.rsH_add_one
#print axioms RSInt.norm_exp_piI_sq
#print axioms RSInt.norm_exp_neg_piI_sq
#print axioms RSInt.norm_exp_piI
#print axioms RSInt.norm_exp_neg_piI
#print axioms RSInt.norm_rsD_ge
#print axioms RSInt.one_le_norm_rsD
#print axioms RSInt.norm_rsG_le_of_im
#print axioms RSInt.norm_rsH_le_of_im
#print axioms RSInt.norm_le_of_upStrip
#print axioms RSInt.norm_le_of_dnStrip
#print axioms RSInt.norm_rsG_le
#print axioms RSInt.norm_rsH_le
#print axioms RSInt.one_add_I_sq
#print axioms RSInt.half_cpow_half_mul
#print axioms RSInt.lineUp_fresnel
#print axioms RSInt.lineUp_gauss
#print axioms RSInt.lineUp_gauss_zero
#print axioms RSInt.gauss_tail_small
#print axioms RSInt.lineUp_pt_mem
#print axioms RSInt.lineUp_pt_im
#print axioms RSInt.lineDn_pt_mem
#print axioms RSInt.lineDn_pt_im
#print axioms RSInt.integrable_lineUp
#print axioms RSInt.integrable_lineDn
#print axioms RSInt.lineUp_eq_of_strip'
#print axioms RSInt.lineDn_eq_of_strip'
#print axioms RSInt.norm_rsG_mul_le
#print axioms RSInt.norm_rsH_mul_le
#print axioms RSInt.lineUp_congr
#print axioms RSInt.lineDn_congr
#print axioms RSInt.lineUp_const_mul
#print axioms RSInt.lineUp_add
#print axioms RSInt.lineUp_sub_mul
#print axioms RSInt.lineUp_add_one
#print axioms RSInt.rsD_ne_zero_of_ne
#print axioms RSInt.differentiableAt_rsG
#print axioms RSInt.differentiableAt_rsH
#print axioms RSInt.lineUp_pt_ne_int
#print axioms RSInt.lineDn_pt_ne_int
#print axioms RSInt.notInt_of_Ioo
#print axioms RSInt.fresnel_pt
#print axioms RSInt.integrable_fresnel
#print axioms RSInt.gauss_pt
#print axioms RSInt.integrable_lineUp_gauss
#print axioms RSInt.lineUp_same_gap
#print axioms RSInt.integrable_lineUp_rsG_mul
#print axioms RSInt.integrable_lineUp_rsG
#print axioms RSInt.lineUp_rsG_jump
#print axioms RSInt.lineUp_cross
#print axioms RSInt.conj_lineUp_pt
#print axioms RSInt.lineDn_eq_conj
#print axioms RSInt.conj_rsD_conj
#print axioms RSInt.conj_rsH_conj
#print axioms RSInt.lineDn_rsH_eq
#print axioms RSInt.conj_mem_dnStrip
#print axioms RSInt.lineDn_cross
#print axioms RSInt.lineDn_same_gap
#print axioms RSInt.lineUp_mordell

/-! ### RS_Mellin (28 theorems) -/
#print axioms RSInt.integrableOn_rpow_exp
#print axioms RSInt.norm_ofReal_cpow
#print axioms RSInt.one_add_I_ne_zero
#print axioms RSInt.one_sub_I_ne_zero
#print axioms RSInt.arg_ne_pi_of_re_pos
#print axioms RSInt.one_div_cpow_eq
#print axioms RSInt.one_div_mul_cpow
#print axioms RSInt.integral_cpow_mul_exp_neg_mul_Ioi_complex
#print axioms RSInt.re_lineUp_mul
#print axioms RSInt.cpow_mul_cpow_neg_one_add_I
#print axioms RSInt.gamma_cpow_line
#print axioms RSInt.continuous_rsG_line
#print axioms RSInt.mellin_step
#print axioms RSInt.norm_exp_one_add_I_mul
#print axioms RSInt.exp_one_add_I_ne_one
#print axioms RSInt.rsK_split
#print axioms RSInt.cpow_nat_succ_mul
#print axioms RSInt.integral_bose
#print axioms RSInt.rsH_ray
#print axioms RSInt.ofReal_mul_cpow
#print axioms RSInt.cpow_mul_cpow_neg
#print axioms RSInt.integral_Epart
#print axioms RSInt.le_exp_sub_exp
#print axioms RSInt.norm_exp_half_sub_ge
#print axioms RSInt.norm_exp_sub_one_ge
#print axioms RSInt.integrableOn_bose
#print axioms RSInt.integrableOn_Epart
#print axioms RSInt.mellin_identity

/-! ### RS_Fold (12 theorems) -/
#print axioms RSInt.norm_cpow_le_exp
#print axioms RSInt.rsH_neg
#print axioms RSInt.continuousAt_rsH_cpow_zero
#print axioms RSInt.log_neg_one_sub_I
#print axioms RSInt.cpow_neg_line
#print axioms RSInt.rsFdn_neg
#print axioms RSInt.continuous_rsFdn
#print axioms RSInt.growth_cpow_sub_one
#print axioms RSInt.integrable_rsFdn
#print axioms RSInt.lineDn_zero_fold
#print axioms RSInt.lineDn_zero_eq
#print axioms RSInt.lineDn_eq_fold

/-! ### RS_Entire (18 theorems) -/
#print axioms RSInt.abs_log_le_of_ge
#print axioms RSInt.norm_log_le
#print axioms RSInt.differentiable_integral_cpow
#print axioms RSInt.norm_ge_half_of_upLine
#print axioms RSInt.norm_ge_half_of_dnLine
#print axioms RSInt.norm_le_of_upLine
#print axioms RSInt.norm_le_of_dnLine
#print axioms RSInt.upLine_mem_slitPlane
#print axioms RSInt.dnLine_mem_slitPlane
#print axioms RSInt.continuous_rsH_line
#print axioms RSInt.differentiable_rsA
#print axioms RSInt.differentiable_rsB
#print axioms RSInt.differentiableAt_rsChi
#print axioms RSInt.rsChi_mul_Gamma_cos
#print axioms RSInt.one_add_I_cpow_mul
#print axioms RSInt.one_add_exp_eq
#print axioms RSInt.cos_ne_zero_of_one_add_exp
#print axioms RSInt.rsChi_eq

/-! ### RS_B2 (23 theorems) -/
#print axioms RSInt.one_add_exp_ne_zero
#print axioms RSInt.rs_identity_re_gt_two
#print axioms RSInt.mem_oddSet_compl
#print axioms RSInt.isClosed_oddSet
#print axioms RSInt.isPreconnected_oddSet_compl
#print axioms RSInt.rs_identity
#print axioms RSInt.norm_cpow_le_of_ge
#print axioms RSInt.slit_of_upStrip
#print axioms RSInt.slit_of_dnStrip
#print axioms RSInt.norm_ge_of_upStrip
#print axioms RSInt.norm_ge_of_dnStrip
#print axioms RSInt.lineUp_cpow_same_gap
#print axioms RSInt.lineDn_cpow_same_gap
#print axioms RSInt.lineUp_book
#print axioms RSInt.lineDn_book
#print axioms RSInt.riemann_siegel_integral
#print axioms RSInt.conj_ofReal_cpow
#print axioms RSInt.lineDn_eq_conj_neg_lineUp
#print axioms RSInt.conj_natCast_cpow_crit
#print axioms RSInt.Gammaℝ_mul_rsChi
#print axioms RSInt.Gammaℝ_conj
#print axioms RSInt.completedRiemannZeta_eq_rs
#print axioms RSInt.completed_re_eq_rs_cos

/-! ### RS_C0 (22 theorems) -/
#print axioms RSInt.lineDn_const_mul
#print axioms RSInt.lineDn_sub
#print axioms RSInt.lineUp_shift
#print axioms RSInt.lineDn_shift
#print axioms RSInt.half_cpow_half_mul_sub
#print axioms RSInt.gauss_fourier_dn
#print axioms RSInt.rsD_one_sub
#print axioms RSInt.rsJ_symm
#print axioms RSInt.pt_ne_int
#print axioms RSInt.continuous_J_integrand
#print axioms RSInt.norm_J_integrand_le
#print axioms RSInt.integrable_J_integrand
#print axioms RSInt.rsJ_fubini
#print axioms RSInt.inner_mordell
#print axioms RSInt.dnLine_neg_p_ne_int
#print axioms RSInt.integrable_T1
#print axioms RSInt.integrable_T2
#print axioms RSInt.rsJ_outer
#print axioms RSInt.T2_eq
#print axioms RSInt.norm_exp_lin_le
#print axioms RSInt.T1_eq
#print axioms RSInt.rsJ_C0
