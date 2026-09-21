/-  AxiomGuardRvMBridge -- CI kernel-axiom guard for the E6 RvM bridge island.

    Declared as a `lean_lib` in defaultTargets, so `lake build` compiles this file and thus
    transitively every module it imports. CI then runs

        lake env lean AxiomGuardRvMBridge.lean

    AFTER `lake build`, and FAILS if any `#print axioms` output mentions `sorryAx`.

    Guarded anchors:
      * RvMBridge.rvm_unbounded_mean_density -- the MIRRORMERE node statement, verbatim.
      * RvMBridge.eventually_Ncount_ge       -- the T log T lower bound from the RvM main clause.
      * RvMBridge2.rvm_unconditional         -- the RH node RH_rvm_unconditional, verbatim
        (cumulative RvM, O(log T)); plus its seam (zetaZeroCount_eq_Ncount), the integrated
        Stirling window lemma (int_mu_cumulative) and the two assembly stages.
      * Zeta23.RvM.{N_eq_halfContour_completedZeta, halfContour_completedZeta_split, gamma_side,
        backlund_horizontal, vertical_two} / Zeta23.StirlingVert.mu_stirling -- the upstream
        general-window internals the second bridge consumes as black boxes.
      * RvMBridge3.corridor_bound            -- the RH node RH_corridor_bound, verbatim (the
        good-ordinate lemma: zero-free segment -1 <= sigma <= 2 at a height in [T, T+1] with
        |zeta'/zeta| <= C log^2 T); plus its stages good_height_real (real-height good ordinate),
        corridor_large (T >= 7, both halves), corridor_small (2 <= T <= 7, compactness), the
        functional-equation identity logDeriv_zeta_reflect and the Gamma_R bounds.
      * Zeta23.WeilEF.{zeta_logDeriv_partial_fraction, exists_far_point, logDeriv_completedZeta,
        logDeriv_completedZeta_one_sub} / Zeta23.StirlingVert.digamma_stirling -- the upstream
        inputs the third bridge consumes as black boxes.
      * RvMBridge4.limit_explicit_formula    -- the RH node RH_limit_explicit_formula, verbatim
        (the Weil/Guinand explicit formula: Integrable archimedean integrand + HasSum of the
        divisor-weighted zero side over all rho : C to archSide - primeSide, for every smooth
        compactly supported g); plus its stages integrable_archIntegrand, archSide_eq,
        archSide_sub_primeSide, inversion_zero (Fourier inversion at 0), weilKernel_eq_Hfn
        (transform seam) and zeroMult_eq_of_strip / zeroMult_eq_zero_of_not_nontrivial
        (divisor vs analyticOrderAt seam).
      * Zeta23.WeilEF.EF_lit_zetaZeroConfig / Zeta23.EF.paper_inversion /
        Zeta23.WeilEF.gammaR_bracket / Zeta23.WeilEF.integrable_mul_logDeriv_Gammaℝ_of_decay --
        the upstream inputs the fourth bridge consumes as black boxes (the literature-form
        explicit formula itself, Fourier inversion, the Gamma_R bracket, the majorant lemma).
      * RvMBridge5.rh_implies_weil_positivity -- the MIRRORMERE dictionary node
        MM_rh_implies_weil_positivity, verbatim (Weil's criterion, forward half: Mathlib's
        RiemannHypothesis implies 0 <= Re weilForm (autocorr g) for every IsWeilTest g); plus its
        stages autocorr_eq_weilTest (autocorr = Zeta23's weilTest g g), isWeilTest_autocorr,
        eq_half_add_im_of_rh, weilKernel_autocorr_line (the |h(r)|^2 factorisation on the line)
        and term_re_nonneg.  Proves nothing about RH; discharges the hpos hypothesis of
        weil_negative_refutes_rh.  conjecture1_proved = False.
      * RvMBridge6.weil_positivity_implies_rh_of / weil_positivity_implies_rh_of' /
        rh_iff_weil_positivity_of -- the Weil converse ATTACK (2026-09-20): Weil positivity implies
        Mathlib's RiemannHypothesis MODULO the named obligations GaussianTransfer (or the zero-free
        GaussianApprox) and GaussianDominance, carried as explicit hypotheses; plus every
        unconditional stage (explicit formula with the zero side isolated, zeroSide real,
        reflection symmetry gammaOf_reflect / zeroMult_reflect, strip_of_zero, pair split,
        Gaussian summability, gaussianTransfer_of_approx).  Proves nothing about RH.
      * RvMBridge7.gaussian_dominance -- the MIRRORMERE node MM_gaussian_dominance, verbatim
        (O2 DISCHARGED, 2026-09-21: every off-line nontrivial zero admits a centre c and width
        lam > 0 with Re zeroSide (gaussTest c lam) < 0); plus its stages (window finiteness,
        generic centre, maximiser with gap, phase choice exists_lam_re_gaussTest, tail_bound,
        re_zeroSide_le) and weil_positivity_implies_rh_of_approx (the converse modulo the single
        remaining Fourier obligation GaussianApprox).  Proves nothing about RH.
      * RvMBridge8.gaussian_approx -- the MIRRORMERE node MM_gaussian_approx, verbatim (O1'
        DISCHARGED, 2026-09-21: truncated Gaussian-derivative Weil tests approximate gaussTest on
        the strip with an n-uniform C/(1+|z|^2) bound); plus its stages (Gaussian Fourier integral
        integral_mul_cexp_gaussian_fourier, paperFT_gaussPhi, the generic integration by parts
        I_mul_paperFT_eq, the DCT limit and the uniform bound).
      * RvMBridge9.gaussian_transfer / weil_positivity_implies_rh / zeta_comb_membership_iff_rh
        -- the MIRRORMERE nodes MM_gaussian_transfer, MM_weil_positivity_implies_rh and
        MM_zeta_comb_membership_iff_rh, verbatim: the Weil converse unconditional on this island
        and the dictionary theorem (goal statement <-> Mathlib RiemannHypothesis).  NOT a proof
        of RH.  conjecture1_proved = False.
      * RvMBridge.zeta_ordinates_not_uniformly_discrete -- the MIRRORMERE milestone
        MM_zeta_ordinates_not_uniformly_discrete, verbatim (W2c, unconditional form: the zeta
        ordinates are not uniformly discrete); plus the verbatim re-proof of the v4.32
        quasicrystal pigeonhole brick it composes with rvm_unbounded_mean_density
        (zeta_ordinates_not_uniformlyDiscrete_of_unbounded_density and its stages
        exists_close_of_card_gt, not_uniformlyDiscrete_of_gaps_to_zero,
        windowedDensity_of_unboundedMeanDensity, not_uniformlyDiscrete_of_windowedDensity).
      * Zeta23.thmA₀ / Zeta23.two_thirds_on_critical_line -- Theorem A (Alpoege--Furman), the
        UPSTREAM input (anthropics/formal-math zeta23/, pinned in lakefile.toml); guarding it here
        re-verifies the dependency's axiom hygiene at our pin.
      * Zeta23.riemannVonMangoldt_zeta / Zeta23.RvM.zeta_local_zero_count -- the upstream
        unconditional Riemann--von Mangoldt package (dyadic main clause + local count).
      * Zeta23.zetaSeam -- the seam facts (finite windows, reflection symmetry) the bridge uses.

    Expected: every line reads `[propext, Classical.choice, Quot.sound]`.
    conjecture1_proved = False. -/
import E6Bridge
import E6Bridge2
import E6Bridge3
import E6Bridge4
import E6Bridge5
import E6Bridge6
import E6Bridge7
import E6Bridge8
import E6Bridge9
import W2cAssembly

#print axioms RvMBridge.rvm_unbounded_mean_density
#print axioms RvMBridge.eventually_Ncount_ge
#print axioms RvMBridge.zeta_ordinates_not_uniformly_discrete
#print axioms RvMBridge.zeta_ordinates_not_uniformlyDiscrete_of_unbounded_density
#print axioms RvMBridge.exists_close_of_card_gt
#print axioms RvMBridge.not_uniformlyDiscrete_of_gaps_to_zero
#print axioms RvMBridge.windowedDensity_of_unboundedMeanDensity
#print axioms RvMBridge.not_uniformlyDiscrete_of_windowedDensity
#print axioms RvMBridge2.rvm_unconditional
#print axioms RvMBridge2.rvm_cumulative
#print axioms RvMBridge2.rvm_cumulative_eventually
#print axioms RvMBridge2.int_mu_cumulative
#print axioms RvMBridge2.zetaZeroCount_eq_Ncount
#print axioms RvMBridge3.corridor_bound
#print axioms RvMBridge3.corridor_large
#print axioms RvMBridge3.corridor_small
#print axioms RvMBridge3.good_height_real
#print axioms RvMBridge3.logDeriv_zeta_reflect
#print axioms RvMBridge3.zeta_ne_zero_of_reflect
#print axioms RvMBridge3.logDeriv_Gammaℝ_shift
#print axioms RvMBridge3.norm_logDeriv_Gammaℝ_le_log_strip
#print axioms RvMBridge4.limit_explicit_formula
#print axioms RvMBridge4.integrable_archIntegrand
#print axioms RvMBridge4.archSide_eq
#print axioms RvMBridge4.archSide_sub_primeSide
#print axioms RvMBridge4.inversion_zero
#print axioms RvMBridge4.weilKernel_eq_Hfn
#print axioms RvMBridge4.zeroMult_eq_of_strip
#print axioms RvMBridge4.zeroMult_eq_zero_of_not_nontrivial
#print axioms RvMBridge5.rh_implies_weil_positivity
#print axioms RvMBridge5.autocorr_eq_weilTest
#print axioms RvMBridge5.isWeilTest_autocorr
#print axioms RvMBridge5.eq_half_add_im_of_rh
#print axioms RvMBridge5.weilKernel_autocorr_line
#print axioms RvMBridge5.term_re_nonneg
#print axioms RvMBridge6.weilKernel_autocorr
#print axioms RvMBridge6.hasSum_weilForm_autocorr
#print axioms RvMBridge6.weilForm_autocorr_eq_zeroSide
#print axioms RvMBridge6.summable_hermitian_zeroSide
#print axioms RvMBridge6.reflect_reflect
#print axioms RvMBridge6.gammaOf_reflect
#print axioms RvMBridge6.zeroMult_reflect
#print axioms RvMBridge6.zeroSide_conj
#print axioms RvMBridge6.hermitianTransform_conj
#print axioms RvMBridge6.gaussTest_conj
#print axioms RvMBridge6.weilForm_autocorr_real
#print axioms RvMBridge6.strip_of_zero
#print axioms RvMBridge6.rh_of_all_on_line
#print axioms RvMBridge6.weil_positivity_implies_rh_of
#print axioms RvMBridge6.rh_iff_weil_positivity_of
#print axioms RvMBridge6.reflect_ne_self
#print axioms RvMBridge6.zeroSide_pair_split
#print axioms RvMBridge6.gaussTest_axis
#print axioms RvMBridge6.gaussTest_axis_re_neg
#print axioms RvMBridge6.norm_gaussTest_mul_le
#print axioms RvMBridge6.summable_mult_div_one_add_normSq
#print axioms RvMBridge6.summable_gauss_zeroSide
#print axioms RvMBridge6.gauss_zeroSide_real
#print axioms RvMBridge6.gauss_zeroSide_pair_split
#print axioms RvMBridge6.gaussianTransfer_of_approx
#print axioms RvMBridge6.weil_positivity_implies_rh_of'
#print axioms RvMBridge7.zeroSide_gauss_eq
#print axioms RvMBridge7.norm_gaussTest
#print axioms RvMBridge7.norm_term
#print axioms RvMBridge7.re_gaussTest
#print axioms RvMBridge7.exists_lam_trig
#print axioms RvMBridge7.exists_lam_re_gaussTest
#print axioms RvMBridge7.windowSet_finite
#print axioms RvMBridge7.mem_window
#print axioms RvMBridge7.self_mem_window
#print axioms RvMBridge7.eq_badOf_of_phi_eq
#print axioms RvMBridge7.badOf_mem_badSet
#print axioms RvMBridge7.exists_generic_centre
#print axioms RvMBridge7.eq_or_eq_reflect_of_phi_eq
#print axioms RvMBridge7.exists_maximiser_gap
#print axioms RvMBridge7.phi_neg_of_not_mem_window
#print axioms RvMBridge7.majorant_nonneg
#print axioms RvMBridge7.summable_majorant
#print axioms RvMBridge7.norm_term_le_majorant
#print axioms RvMBridge7.constA_nonneg
#print axioms RvMBridge7.constB_nonneg
#print axioms RvMBridge7.tsum_majorant
#print axioms RvMBridge7.tail_bound
#print axioms RvMBridge7.re_zeroSide_le
#print axioms RvMBridge7.gaussian_dominance
#print axioms RvMBridge7.weil_positivity_implies_rh_of_approx
#print axioms RvMBridge8.integrable_exp_quadratic
#print axioms RvMBridge8.integrable_exp_quadratic_abs
#print axioms RvMBridge8.abs_pow_le_exp
#print axioms RvMBridge8.integrable_abs_pow_mul_exp_quadratic_abs
#print axioms RvMBridge8.integrable_mul_cexp_quadratic
#print axioms RvMBridge8.integral_mul_cexp_gaussian_fourier
#print axioms RvMBridge8.gaussB_pos
#print axioms RvMBridge8.gaussTest_eq_half_mul_conj
#print axioms RvMBridge8.gaussK_ne_zero
#print axioms RvMBridge8.paperFT_gaussPhi
#print axioms RvMBridge8.cutoff_nonneg
#print axioms RvMBridge8.cutoff_le_one
#print axioms RvMBridge8.abs_cutoff_le_one
#print axioms RvMBridge8.cutoff_eq_one
#print axioms RvMBridge8.cutoff_eq_zero
#print axioms RvMBridge8.contDiff_cutoff
#print axioms RvMBridge8.hasCompactSupport_cutoff
#print axioms RvMBridge8.contDiff_gaussPhi
#print axioms RvMBridge8.isWeilTest_gaussTests
#print axioms RvMBridge8.norm_gaussPhi
#print axioms RvMBridge8.norm_cexp_I_mul_le
#print axioms RvMBridge8.norm_gaussTests_mul_le
#print axioms RvMBridge8.norm_gaussPhi_mul_le
#print axioms RvMBridge8.integrable_majorant
#print axioms RvMBridge8.paperFT_gaussTests_tendsto
#print axioms RvMBridge8.hasDerivAt_gaussPhi
#print axioms RvMBridge8.norm_gaussPhi'_le
#print axioms RvMBridge8.exists_deriv_bump_bound
#print axioms RvMBridge8.hasDerivAt_cutoff
#print axioms RvMBridge8.hasDerivAt_gaussTests
#print axioms RvMBridge8.integrable_derivMajorant
#print axioms RvMBridge8.norm_deriv_gaussTests_mul_le
#print axioms RvMBridge8.I_mul_paperFT_eq
#print axioms RvMBridge8.norm_mul_paperFT_gaussTests_le
#print axioms RvMBridge8.norm_paperFT_gaussTests_le
#print axioms RvMBridge8.exists_paperFT_gaussTests_bound
#print axioms RvMBridge8.norm_hermitianTransform_eq
#print axioms RvMBridge8.gaussian_approx
#print axioms RvMBridge9.gaussian_transfer
#print axioms RvMBridge9.weil_positivity_implies_rh
#print axioms RvMBridge9.zeta_comb_membership_iff_rh
#print axioms RvMBridge9.weil_negative_refutes_rh
#print axioms Zeta23.RvM.N_eq_halfContour_completedZeta
#print axioms Zeta23.RvM.halfContour_completedZeta_split
#print axioms Zeta23.RvM.gamma_side
#print axioms Zeta23.RvM.backlund_horizontal
#print axioms Zeta23.RvM.vertical_two
#print axioms Zeta23.StirlingVert.mu_stirling
#print axioms Zeta23.thmA₀
#print axioms Zeta23.two_thirds_on_critical_line
#print axioms Zeta23.riemannVonMangoldt_zeta
#print axioms Zeta23.RvM.zeta_local_zero_count
#print axioms Zeta23.zetaSeam
#print axioms Zeta23.WeilEF.zeta_logDeriv_partial_fraction
#print axioms Zeta23.WeilEF.exists_far_point
#print axioms Zeta23.WeilEF.logDeriv_completedZeta
#print axioms Zeta23.WeilEF.logDeriv_completedZeta_one_sub
#print axioms Zeta23.StirlingVert.digamma_stirling
#print axioms Zeta23.RvM.riemannZeta_zeros_finite_of_isCompact
#print axioms Zeta23.WeilEF.EF_lit_zetaZeroConfig
#print axioms Zeta23.EF.paper_inversion
#print axioms Zeta23.WeilEF.gammaR_bracket
#print axioms Zeta23.WeilEF.integrable_mul_logDeriv_Gammaℝ_of_decay
#print axioms Zeta23.EF.integrable_fourier_of_contDiff_two
