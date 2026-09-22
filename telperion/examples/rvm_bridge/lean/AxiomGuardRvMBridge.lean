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
      * RvMBridge10.{rh_iff_gaussian_positivity, zeroSide_gaussTest_eq, rh_iff_gaussian_prime_le_arch}
        -- WALL ASSAULT seam A (2026-09-21): the Wall in two real parameters (RH <-> Gaussian
        positivity <-> prime side <= archimedean side for every centre and width), plus the
        limit stages of the Gaussian explicit formula.  Equivalences only; NOT a proof of RH.
      * RvMBridge12.{gaussian_positivity_of_window, gaussian_positivity_of_window_two,
        gaussian_positivity_of_all_on_line} -- WALL ASSAULT seam C (2026-09-21): the
        ladder-certified region instrument (WindowOnLine hypothesis + one certified near zero +
        lam above an explicit threshold => Gaussian positivity at that centre); plus stages
        (zeroSide_split, tail_bound_window, near_term_ge, tail_le_near_of_threshold).
        NOT a proof of RH; the on-line hypothesis is load-bearing.
      * RvMBridge11.re_weilForm_gauss_nonneg -- WALL ASSAULT seam B (2026-09-21): the small-width
        region lam <= lam0 = 1e-7 is UNCONDITIONAL (archimedean dominance), plus its stages.
      * RvMBridge13.{gaussianExplicitFormula, gaussian_positivity_small_lam,
        rh_iff_gaussian_positivity_above_lam0} -- THE WALL MAP: RH <-> Gaussian positivity on
        widths above lam0 only.  Equivalence; NOT a proof of RH.  conjecture1_proved = False.
      * RvMBridge14.{effective_gaussian_dominance, offline_zeros_small_or_margin,
        effectiveThreshold_unbounded_of_small_spacing} -- open lemma 1 (2026-09-21): effective
        Gaussian dominance with the explicit threshold and the localisation instrument; the
        spacing floor is load-bearing.  NOT a proof of RH.  conjecture1_proved = False.
      * RvMBridge15.{liZeroSum_tendsto, bl_explicit_formula_of, rh_implies_liLimit_re_nonneg}
        -- open lemma 2 (2026-09-21): the Weil-to-Li dictionary; B7 convergence half proved, the
        node modulo the named LiValue obligation; Li's criterion forward half.  NOT a proof of RH.
      * RvMBridge16.{gaussian_positivity_envelope_sharp, band_upper_edge} -- seam B sharpened
        (2026-09-21): the sharp c-uniform envelope with the exact prime-side constant primeAbs;
        plus stages (fourier_autocorrGauss, norm_primeSide_le_primeAbs, primeAbs_le_crude).
        NOT a proof of RH.  conjecture1_proved = False.
      * RvMBridge17.{rh_iff_theta_positivity, theta_heat, theta_pos_mono, rh_iff_thetaWidths_eq,
        not_thetaFree_of_offline, rh_or_thetaWidths_bddAbove} -- the THETA FACE (2026-09-21): the
        plain Gaussian face is heat-monotone in width; RH <-> every width free.  NOT a proof of RH.
      * RvMBridge18.{xi_logDeriv_deriv_eq_of, eq_const_of_log_growth, summable_inv_sub_sq,
        tsum_inv_sub_sq_tendsto, logDeriv_xi_eq} -- the xi derivative partial fraction skeleton
        (2026-09-21), modulo the named obligations XiDiffRegular / XiLogDerivDerivDecay.
      * RvMBridge20.{xiDiffExt_differentiable, xiDiffExt_eq, xiDiffExt_one_sub, exists_local_form,
        analyticOrderAt_xi_eq, xiDiffRegular_of} -- obligation 1 part A (2026-09-21): the entire
        extension across the zeros; growth remains the named obligation XiDiffExtGrowthRight.
      * RvMBridge21.{xi_logDeriv_deriv_decay, xi_logDeriv_deriv_eq_of_regular,
        digamma_deriv_tendsto_zero, zeta_logDeriv_deriv_tendsto_zero, hasSum_trigamma_of_re_pos}
        -- obligation 2 DISCHARGED (2026-09-21): real-axis decay of (log xi)''.
      * RvMBridge22.{xiLogDerivDerivEq_of_two, xiDiffExtGrowthRight_of_two, rightDerivBound,
        growth_compact, growth_right, growth_strip, norm_tsum_far_le} -- obligation 1 reduced to
        LocalCountSum + StripDerivBound (2026-09-21).
      * RvMBridge19.{liValue_of, bl_explicit_formula_of_partialFraction, powerSum_eq_taylor,
        pairedPowerSum_one_eq, iteratedDeriv_psiHalf, taylorOne_eq, liLimit_eq_taylorOne,
        xiDerivPartialFraction_iff} -- the LiValue Taylor bookkeeping (2026-09-21), modulo
        XiDerivPartialFraction + NoRealZeroInUnitInterval.
      * RvMBridge23.{local_count_sum, xiLogDerivDerivEq_of_strip} -- LocalCountSum DISCHARGED
        (2026-09-21).  RvMBridge25.{noRealZeroInUnitInterval, liValue_of_two,
        bl_explicit_formula_of_two} -- no real zero in (0,1) DISCHARGED; B7 modulo StripDerivBound.
      * RvMBridge24.{stripDerivBound, xiLogDerivDerivEq_of_localCount, Fwin_bound_core,
        FwinExt_differentiableOn, exists_window_bound} -- StripDerivBound DISCHARGED (2026-09-21).
      * RvMBridge27.{xi_logDeriv_deriv_eq, liValue, bl_explicit_formula} -- THE UNCONDITIONAL
        ASSEMBLY: the derivative partial fraction of xi'/xi (no Hadamard), the Bombieri-Lagarias
        value identity, and the rh node RH_bl_explicit_formula verbatim.  NOT about RH.
      * RvMBridge28.{liLimit_re_nonneg_of_line_below, archSide_add_finiteSide_re_nonneg_of_line_below,
        liLimit_one_re_nonneg, ..., liLimit_five_re_nonneg, box_one, box_two,
        norm_integral_fract_cpow_le} -- THE LI LADDER (2026-09-21): zeros on the line up to
        height T >= 1 give 0 <= Re (liLimit N) for N <= 3 pi T / 2 (pair identity, Lemmas A/B,
        Theorems C/D); the low-height box |Im rho| >= sqrt 3 / 2 and (Re rho - 1/2)^2 <=
        Im^2/3 - 1/4 from the sharp sawtooth bound; rungs N = 1..5 hypothesis-free.  Consumes
        zero localisation, proves nothing about RH.
      * RvMBridge29.{pair_re_nonneg_of_far_sharp, liLimit_re_nonneg_of_line_below_sharp,
        archSide_add_finiteSide_re_nonneg_of_line_below_sharp} -- the SHARPENED exchange rate
        (2026-09-21): N <= 2 pi (T - 1/2) (Lemma A'' window, Lemma B'' combined bound).
        Consumes zero localisation, proves nothing about RH.
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
import E6Bridge10
import E6Bridge11
import E6Bridge12
import E6Bridge13
import E6Bridge14
import E6Bridge15
import E6Bridge16
import E6Bridge17
import E6Bridge18
import E6Bridge20
import E6Bridge21
import E6Bridge22
import E6Bridge19
import E6Bridge23
import E6Bridge25
import E6Bridge26
import E6Bridge24
import E6Bridge27
import E6Bridge28
import E6Bridge29
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
#print axioms RvMBridge10.gaussTest_ofReal
#print axioms RvMBridge10.gaussTest_ofReal_re_nonneg
#print axioms RvMBridge10.gammaOf_eq_im_of_rh
#print axioms RvMBridge10.gauss_term_re_nonneg
#print axioms RvMBridge10.rh_implies_gaussian_positivity
#print axioms RvMBridge10.gaussian_positivity_implies_rh
#print axioms RvMBridge10.rh_iff_gaussian_positivity
#print axioms RvMBridge10.gaussian_positivity_iff_weil_positivity
#print axioms RvMBridge10.exists_hermitian_gaussTests_bound
#print axioms RvMBridge10.hermitianTransform_gaussTests_tendsto
#print axioms RvMBridge10.zeroSide_gaussTests_tendsto
#print axioms RvMBridge10.continuous_gaussPhi
#print axioms RvMBridge10.norm_gaussTests_le
#print axioms RvMBridge10.norm_phi_mul_phi_le
#print axioms RvMBridge10.integrable_sq_add_mul_gauss
#print axioms RvMBridge10.integrable_vMaj
#print axioms RvMBridge10.gaussI0_nonneg
#print axioms RvMBridge10.gaussI2_nonneg
#print axioms RvMBridge10.autocorrMaj_nonneg
#print axioms RvMBridge10.autocorrMaj_neg
#print axioms RvMBridge10.integral_vMaj
#print axioms RvMBridge10.norm_gaussTests_mul_conj_le
#print axioms RvMBridge10.norm_autocorr_gaussTests_le
#print axioms RvMBridge10.autocorr_gaussTests_tendsto
#print axioms RvMBridge10.primeBound_nonneg
#print axioms RvMBridge10.norm_primeTerm_le
#print axioms RvMBridge10.summable_primeBound
#print axioms RvMBridge10.primeSide_gaussTests_tendsto
#print axioms RvMBridge10.continuous_autocorr_gaussTests
#print axioms RvMBridge10.integrable_kernelMaj
#print axioms RvMBridge10.norm_kernel_term_le
#print axioms RvMBridge10.weilKernel_gaussTests_tendsto
#print axioms RvMBridge10.gammaOf_half_add
#print axioms RvMBridge10.exists_paperFT_autocorr_gaussTests_bound
#print axioms RvMBridge10.integrable_archBound
#print axioms RvMBridge10.norm_archIntegrand_le
#print axioms RvMBridge10.archIntegral_gaussTests_tendsto
#print axioms RvMBridge10.archSide_gaussTests_tendsto
#print axioms RvMBridge10.zeroSide_gaussTest_eq
#print axioms RvMBridge10.gaussian_positivity_iff_prime_le_arch
#print axioms RvMBridge10.rh_iff_gaussian_prime_le_arch
#print axioms RvMBridge12.windowOnLine_of_all_on_line
#print axioms RvMBridge12.tailWeight_nonneg
#print axioms RvMBridge12.summable_tailWeight
#print axioms RvMBridge12.tsum_tailWeight
#print axioms RvMBridge12.one_le_lamThreshold
#print axioms RvMBridge12.re_term_of_on_line
#print axioms RvMBridge12.re_term_nonneg_of_on_line
#print axioms RvMBridge12.term_eq_zero_of_not_nontrivial
#print axioms RvMBridge12.re_term_nonneg
#print axioms RvMBridge12.near_term_ge
#print axioms RvMBridge12.gaussian_positivity_of_all_on_line
#print axioms RvMBridge12.summable_term_subtype
#print axioms RvMBridge12.zeroSide_split
#print axioms RvMBridge12.re_window_ge_term
#print axioms RvMBridge12.phi_le_of_far
#print axioms RvMBridge12.norm_term_le_tail
#print axioms RvMBridge12.tail_bound_window
#print axioms RvMBridge12.tail_le_near_of_threshold
#print axioms RvMBridge12.gaussian_positivity_of_window
#print axioms RvMBridge12.gaussian_positivity_of_window_two
#print axioms RvMBridge12.zeroWindowSet_finite
#print axioms RvMBridge12.mem_zeroWindow
#print axioms RvMBridge12.windowSum_nonneg
#print axioms RvMBridge12.tailEnvelope_nonneg
#print axioms RvMBridge12.re_window_eq_windowSum
#print axioms RvMBridge12.gaussian_positivity_of_window_dominance
#print axioms RvMBridge12.re_zeroSide_ge_windowSum_sub
#print axioms RvMBridge12.near_term_le_windowSum
#print axioms RvMBridge11.gaussA_pos
#print axioms RvMBridge11.integral_sq_mul_exp_neg_mul_sq
#print axioms RvMBridge11.integral_sq_mul_cexp_neg_mul_sq
#print axioms RvMBridge11.re_digamma_quarter_ge
#print axioms RvMBridge11.re_digamma_quarter_ge_two
#print axioms RvMBridge11.gaussPhi_mul_conj
#print axioms RvMBridge11.autocorr_gaussPhi_eq_integral
#print axioms RvMBridge11.integral_sq_sub_mul_cexp
#print axioms RvMBridge11.gaussK_mul_conj
#print axioms RvMBridge11.autocorr_gaussPhi
#print axioms RvMBridge11.autocorrGauss_zero
#print axioms RvMBridge11.abs_one_sub_two_mul_exp_le
#print axioms RvMBridge11.norm_autocorrGauss_le
#print axioms RvMBridge11.autocorr_gaussPhi_funext
#print axioms RvMBridge11.prime_term_bound
#print axioms RvMBridge11.norm_primeSide_le
#print axioms RvMBridge11.norm_integral_autocorrGauss_mul_exp_le
#print axioms RvMBridge11.weilKernel_zero_eq
#print axioms RvMBridge11.weilKernel_one_eq
#print axioms RvMBridge11.norm_weilKernel_zero_le
#print axioms RvMBridge11.norm_weilKernel_one_le
#print axioms RvMBridge11.integral_sq_mul_cexp_gaussian_fourier
#print axioms RvMBridge11.weilKernel_line_eq
#print axioms RvMBridge11.cpow_pi_div_a
#print axioms RvMBridge11.weilKernel_autocorrGauss_line
#print axioms RvMBridge11.psiR_eq
#print axioms RvMBridge11.psiR_ge
#print axioms RvMBridge11.psiR_ge_two
#print axioms RvMBridge11.continuous_psiR
#print axioms RvMBridge11.bumpR_nonneg
#print axioms RvMBridge11.continuous_bumpR
#print axioms RvMBridge11.integrable_bumpR
#print axioms RvMBridge11.integrable_bumpR_mul_psiR
#print axioms RvMBridge11.bumpR_le
#print axioms RvMBridge11.integral_bumpR
#print axioms RvMBridge11.R₀_pos
#print axioms RvMBridge11.setIntegral_bumpR_le
#print axioms RvMBridge11.integral_bumpR_mul_psiR_ge
#print axioms RvMBridge11.integral_archIntegrand_eq
#print axioms RvMBridge11.re_archSide_ge
#print axioms RvMBridge11.re_weilForm_gauss_nonneg
#print axioms RvMBridge11.gaussian_positivity_small_lam_of
#print axioms RvMBridge11.gaussian_positivity_small_lam_explicit_of
#print axioms RvMBridge11.gaussianExplicitFormula
#print axioms RvMBridge11.gaussian_positivity_small_lam
#print axioms RvMBridge11.gaussian_positivity_small_lam_explicit
#print axioms RvMBridge11.prime_term_bound_uniform
#print axioms RvMBridge11.norm_primeSide_le_uniform
#print axioms RvMBridge11.re_digamma_quarter_ge_log
#print axioms RvMBridge11.psiR_ge_log
#print axioms RvMBridge11.gaussA_half
#print axioms RvMBridge11.bumpR_half
#print axioms RvMBridge11.integral_indicator_bumpR_tail_le
#print axioms RvMBridge11.integral_bumpR_mul_psiR_ge_envelope
#print axioms RvMBridge11.envelopeX_nonneg
#print axioms RvMBridge11.re_weilForm_gauss_nonneg_of_large_c
#print axioms RvMBridge11.gaussian_positivity_envelope
#print axioms RvMBridge11.gaussian_positivity_envelope'
#print axioms RvMBridge13.gaussianExplicitFormula
#print axioms RvMBridge13.gaussian_positivity_small_lam
#print axioms RvMBridge13.rh_iff_gaussian_positivity_above_lam₀
#print axioms RvMBridge14.one_le_effectiveThreshold
#print axioms RvMBridge14.effectiveThreshold_pos
#print axioms RvMBridge14.le_exp_of_log_le
#print axioms RvMBridge14.effectiveThreshold_mono_B
#print axioms RvMBridge14.effectiveThreshold_unbounded_of_small_spacing
#print axioms RvMBridge14.tsum_winSet_eq_sum
#print axioms RvMBridge14.re_term_centre
#print axioms RvMBridge14.re_term_centre_nonpos
#print axioms RvMBridge14.norm_term_le_competitor
#print axioms RvMBridge14.re_window_sum_le
#print axioms RvMBridge14.effective_gaussian_dominance
#print axioms RvMBridge14.band_finite
#print axioms RvMBridge14.offline_zeros_small_or_margin
#print axioms RvMBridge14.windowCount_le_Ncount
#print axioms RvMBridge15.isNontrivialZero_conj
#print axioms RvMBridge15.isNontrivialZero_conj_iff
#print axioms RvMBridge15.zeroMult_conj
#print axioms RvMBridge15.mem_windowSet
#print axioms RvMBridge15.conj_mem_windowSet
#print axioms RvMBridge15.finite_zeros_window
#print axioms RvMBridge15.liKernel_conj
#print axioms RvMBridge15.liTerm_eq_zero_of_not_nontrivial
#print axioms RvMBridge15.liPaired_eq_zero_of_not_nontrivial
#print axioms RvMBridge15.liTerm_conj
#print axioms RvMBridge15.windowSupport_finite
#print axioms RvMBridge15.liZeroSum_eq_tsum_indicator
#print axioms RvMBridge15.indicator_liTerm_conj
#print axioms RvMBridge15.summable_indicator_liTerm
#print axioms RvMBridge15.liZeroSum_eq_tsum_paired
#print axioms RvMBridge15.liZeroSum_im
#print axioms RvMBridge15.liKernel_eq_sum
#print axioms RvMBridge15.sum_choose_succ_le
#print axioms RvMBridge15.abs_re_liKernel_le
#print axioms RvMBridge15.liPaired_re
#print axioms RvMBridge15.liPaired_im
#print axioms RvMBridge15.norm_liPaired
#print axioms RvMBridge15.norm_liPaired_le_majorant
#print axioms RvMBridge15.finite_zeros_small
#print axioms RvMBridge15.summable_liBound
#print axioms RvMBridge15.norm_liPaired_le
#print axioms RvMBridge15.summable_liPaired
#print axioms RvMBridge15.liZeroSum_tendsto
#print axioms RvMBridge15.bl_explicit_formula_of
#print axioms RvMBridge15.norm_one_sub_inv_of_on_line
#print axioms RvMBridge15.liPaired_re_nonneg_of_rh
#print axioms RvMBridge15.rh_implies_liZeroSum_re_nonneg
#print axioms RvMBridge15.rh_implies_liLimit_re_nonneg
#print axioms RvMBridge16.integral_sq_mul_cexp_gaussian_fourier'
#print axioms RvMBridge16.gaussA_mul_sqrt
#print axioms RvMBridge16.fourier_autocorrGauss
#print axioms RvMBridge16.weilKernel_zero_eq_gaussTest
#print axioms RvMBridge16.weilKernel_one_eq_gaussTest
#print axioms RvMBridge16.norm_gaussTest_half
#print axioms RvMBridge16.norm_poles_le
#print axioms RvMBridge16.primeAbsTerm_nonneg
#print axioms RvMBridge16.primeAbsTerm_le
#print axioms RvMBridge16.summable_primeAbsTerm
#print axioms RvMBridge16.primeAbs_nonneg
#print axioms RvMBridge16.primeAbs_le_crude
#print axioms RvMBridge16.norm_autocorrGauss_add_neg_le
#print axioms RvMBridge16.norm_primeSide_le_primeAbs
#print axioms RvMBridge16.re_digamma_quarter_ge_log'
#print axioms RvMBridge16.psiR_ge_log'
#print axioms RvMBridge16.integral_indicator_bumpR_tail_le'
#print axioms RvMBridge16.integral_bumpR_mul_psiR_ge_capped
#print axioms RvMBridge16.tailRadius_sq
#print axioms RvMBridge16.tailRadius_nonneg
#print axioms RvMBridge16.re_weilForm_gauss_nonneg_sharp
#print axioms RvMBridge16.gaussian_positivity_envelope_sharp
#print axioms RvMBridge16.band_upper_edge
#print axioms RvMBridge16.envelopeCsharp_le_crude
#print axioms RvMBridge16.gaussian_positivity_above_height
#print axioms RvMBridge16.gaussian_positivity_above_height_log
#print axioms RvMBridge17.zeroSide_plain_eq
#print axioms RvMBridge17.theta_eq
#print axioms RvMBridge17.plainGauss_re_exponent
#print axioms RvMBridge17.plainGauss_im_exponent
#print axioms RvMBridge17.norm_plainGauss
#print axioms RvMBridge17.norm_pterm
#print axioms RvMBridge17.re_plainGauss
#print axioms RvMBridge17.plainGauss_conj
#print axioms RvMBridge17.plainGauss_ofReal
#print axioms RvMBridge17.pterm_eq_zero_of_not_nontrivial
#print axioms RvMBridge17.norm_plainGauss_mul_le
#print axioms RvMBridge17.plainC_nonneg
#print axioms RvMBridge17.norm_pterm_le
#print axioms RvMBridge17.summable_plain_zeroSide
#print axioms RvMBridge17.zeroSide_plain_im
#print axioms RvMBridge17.pterm_re_nonneg_of_rh
#print axioms RvMBridge17.theta_nonneg_of_rh
#print axioms RvMBridge17.exists_lam_cos_neg_one
#print axioms RvMBridge17.exists_generic_centre'
#print axioms RvMBridge17.pmajorant_nonneg
#print axioms RvMBridge17.summable_pmajorant
#print axioms RvMBridge17.norm_pterm_le_pmajorant
#print axioms RvMBridge17.pconstA_nonneg
#print axioms RvMBridge17.pconstB_nonneg
#print axioms RvMBridge17.tsum_pmajorant
#print axioms RvMBridge17.ptail_bound
#print axioms RvMBridge17.theta_le_pair_add_tail
#print axioms RvMBridge17.exists_theta_neg_of_offline
#print axioms RvMBridge17.rh_iff_theta_positivity
#print axioms RvMBridge17.heatVar_pos
#print axioms RvMBridge17.heatKernel_nonneg
#print axioms RvMBridge17.continuous_heatKernel
#print axioms RvMBridge17.heat_A_eq
#print axioms RvMBridge17.heat_integrand_eq
#print axioms RvMBridge17.plainGauss_heat
#print axioms RvMBridge17.real_gauss_heat
#print axioms RvMBridge17.integrable_heatF
#print axioms RvMBridge17.integral_norm_heatF_le
#print axioms RvMBridge17.summable_integral_norm_heatF
#print axioms RvMBridge17.nontrivialZeros_countable
#print axioms RvMBridge17.tsum_pterm_NZ
#print axioms RvMBridge17.tsum_pterm_re_NZ
#print axioms RvMBridge17.theta_heat
#print axioms RvMBridge17.theta_pos_mono
#print axioms RvMBridge17.thetaFree_mono
#print axioms RvMBridge17.thetaWidths_Ioc_subset
#print axioms RvMBridge17.rh_iff_thetaFree_all
#print axioms RvMBridge17.rh_iff_thetaWidths_eq
#print axioms RvMBridge17.not_thetaFree_of_offline
#print axioms RvMBridge17.thetaWidths_bddAbove_of_offline
#print axioms RvMBridge17.rh_or_thetaWidths_bddAbove
#print axioms RvMBridge18.xi_differentiable
#print axioms RvMBridge18.xi_eq
#print axioms RvMBridge18.xi_eventuallyEq
#print axioms RvMBridge18.logDeriv_xi_eq
#print axioms RvMBridge18.normSq_gammaOf_le
#print axioms RvMBridge18.polTerm_eq_zero_of_not_nontrivial
#print axioms RvMBridge18.norm_polTerm
#print axioms RvMBridge18.norm_polTerm_le_majorant
#print axioms RvMBridge18.finite_zeros_near
#print axioms RvMBridge18.summable_polBound
#print axioms RvMBridge18.norm_polTerm_le
#print axioms RvMBridge18.summable_inv_sub_sq
#print axioms RvMBridge18.summable_polTerm
#print axioms RvMBridge18.norm_polTerm_le_real
#print axioms RvMBridge18.polTerm_tendsto_zero
#print axioms RvMBridge18.tsum_inv_sub_sq_tendsto
#print axioms RvMBridge18.eq_const_of_log_growth
#print axioms RvMBridge18.not_nontrivialZero_of_one_le_re
#print axioms RvMBridge18.xi_logDeriv_deriv_eq_of
#print axioms RvMBridge20.xi_one_sub
#print axioms RvMBridge20.xi_one
#print axioms RvMBridge20.xi_ne_zero_of_one_le_re
#print axioms RvMBridge20.xi_eq_zero_iff
#print axioms RvMBridge20.xi_ne_zero_of_not_nontrivial
#print axioms RvMBridge20.analyticOrderAt_xi_ne_top
#print axioms RvMBridge20.analyticAt_completedZeta
#print axioms RvMBridge20.analyticOrderAt_xi_eq_of_zero
#print axioms RvMBridge20.analyticOrderAt_xi_eq
#print axioms RvMBridge20.tsum_polTerm_eq
#print axioms RvMBridge20.nearZeros_finite
#print axioms RvMBridge20.exists_ball_avoid
#print axioms RvMBridge20.polTerm_differentiableAt
#print axioms RvMBridge20.exists_ball_rest
#print axioms RvMBridge20.exists_unit_factor
#print axioms RvMBridge20.analyticAt_logDeriv
#print axioms RvMBridge20.deriv_logDeriv_xi_local
#print axioms RvMBridge20.exists_local_form
#print axioms RvMBridge20.xiDiffExt_eq
#print axioms RvMBridge20.xiDiffExt_eventuallyEq
#print axioms RvMBridge20.xiDiffExt_differentiable
#print axioms RvMBridge20.isNontrivialZero_one_sub_iff
#print axioms RvMBridge20.logDeriv_xi_one_sub
#print axioms RvMBridge20.deriv_logDeriv_xi_one_sub
#print axioms RvMBridge20.zeroMult_one_sub
#print axioms RvMBridge20.tsum_polTerm_one_sub
#print axioms RvMBridge20.xiDiffReg_one_sub
#print axioms RvMBridge20.xiDiffExt_one_sub
#print axioms RvMBridge20.xiDiffExtGrowth_of_right
#print axioms RvMBridge20.xiDiffRegular_of
#print axioms RvMBridge20.xiDiffRegular_of_right
#print axioms RvMBridge21.ne_neg_nat_of_re_pos
#print axioms RvMBridge21.isOpen_re_pos
#print axioms RvMBridge21.analyticAt_Gamma_of_re_pos
#print axioms RvMBridge21.analyticAt_digamma_of_re_pos
#print axioms RvMBridge21.continuousAt_deriv_digamma
#print axioms RvMBridge21.norm_trigTerm_le
#print axioms RvMBridge21.summable_trigBound
#print axioms RvMBridge21.continuousOn_trigSum
#print axioms RvMBridge21.summable_trigTerm
#print axioms RvMBridge21.eq_of_intCast_near
#print axioms RvMBridge21.hasSum_trigamma_of_re_pos
#print axioms RvMBridge21.sum_range_inv_sq_le
#print axioms RvMBridge21.summable_inv_sq_real
#print axioms RvMBridge21.tsum_inv_sq_real_le
#print axioms RvMBridge21.norm_trigTerm_real
#print axioms RvMBridge21.norm_deriv_digamma_real_le
#print axioms RvMBridge21.digamma_deriv_tendsto_zero
#print axioms RvMBridge21.abscissa_vonMangoldt_le_one
#print axioms RvMBridge21.abscissa_vonMangoldt_lt
#print axioms RvMBridge21.isOpen_one_lt_re
#print axioms RvMBridge21.logDeriv_zeta_eq
#print axioms RvMBridge21.deriv_logDeriv_zeta_eq
#print axioms RvMBridge21.term_logMul_one
#print axioms RvMBridge21.term_tendsto_zero
#print axioms RvMBridge21.norm_term_le_of_two_le
#print axioms RvMBridge21.zeta_logDeriv_deriv_tendsto_zero
#print axioms RvMBridge21.logDeriv_xi_eq_of_one_lt_re
#print axioms RvMBridge21.deriv_logDeriv_xi_real
#print axioms RvMBridge21.tendsto_neg_inv_sq
#print axioms RvMBridge21.tendsto_inv_sub_one_sq
#print axioms RvMBridge21.xi_logDeriv_deriv_decay
#print axioms RvMBridge21.xi_logDeriv_deriv_eq_of_regular
#print axioms RvMBridge22.lcTerm_nonneg
#print axioms RvMBridge22.lcTerm_le_majorant
#print axioms RvMBridge22.summable_lcTerm
#print axioms RvMBridge22.windowSet_finite
#print axioms RvMBridge22.mem_window
#print axioms RvMBridge22.norm_polTerm_le_lcTerm_right
#print axioms RvMBridge22.norm_polTerm_le_lcTerm_far
#print axioms RvMBridge22.norm_tsum_polTerm_le_right
#print axioms RvMBridge22.norm_tsum_far_le
#print axioms RvMBridge22.bound_of_bound_off_zeros
#print axioms RvMBridge22.growth_compact
#print axioms RvMBridge22.growth_right
#print axioms RvMBridge22.isOpen_stripOpen
#print axioms RvMBridge22.growth_strip_off_zeros
#print axioms RvMBridge22.growth_strip
#print axioms RvMBridge22.abs_im_le_norm'
#print axioms RvMBridge22.xiDiffExtGrowthRight_of
#print axioms RvMBridge22.xiDiffRegular_of_three
#print axioms RvMBridge22.xiLogDerivDerivEq_of_three
#print axioms RvMBridge22.deriv_logDeriv_xi_of_one_lt_re
#print axioms RvMBridge22.norm_deriv_digamma_le
#print axioms RvMBridge22.norm_term_le_of_two_le_re
#print axioms RvMBridge22.summable_dirTerms
#print axioms RvMBridge22.norm_deriv_logDeriv_zeta_le
#print axioms RvMBridge22.rightDerivBound
#print axioms RvMBridge22.xiDiffExtGrowthRight_of_two
#print axioms RvMBridge22.xiLogDerivDerivEq_of_two
#print axioms RvMBridge19.xi_one_sub
#print axioms RvMBridge19.xi_zero
#print axioms RvMBridge19.xi_one
#print axioms RvMBridge19.xi_analyticAt
#print axioms RvMBridge19.xi_eq_zero_iff
#print axioms RvMBridge19.xiLogDerivDerivEq_def
#print axioms RvMBridge19.smallZeros_finite
#print axioms RvMBridge19.summable_zeroBound
#print axioms RvMBridge19.inv_normSq_le_majorant
#print axioms RvMBridge19.one_le_norm_of_nontrivial
#print axioms RvMBridge19.norm_pos_of_nontrivial
#print axioms RvMBridge19.norm_le_zeroBound
#print axioms RvMBridge19.summable_of_zeroBound
#print axioms RvMBridge19.iteratedDeriv_tsum_ball
#print axioms RvMBridge19.analyticAt_tsum_ball
#print axioms RvMBridge19.exists_zero_radius
#print axioms RvMBridge19.zeroRadius_pos
#print axioms RvMBridge19.zeroRadius_le_one
#print axioms RvMBridge19.zeroRadius_le
#print axioms RvMBridge19.not_nontrivialZero_of_mem_ball
#print axioms RvMBridge19.norm_sub_ge_half
#print axioms RvMBridge19.coef_succ
#print axioms RvMBridge19.coef_zero
#print axioms RvMBridge19.norm_coef
#print axioms RvMBridge19.zterm_zero_eq
#print axioms RvMBridge19.zterm_eq_zero_of_not_nontrivial
#print axioms RvMBridge19.hasDerivAt_zterm
#print axioms RvMBridge19.norm_zterm_le
#print axioms RvMBridge19.summable_zbound
#print axioms RvMBridge19.norm_zterm_le_zbound
#print axioms RvMBridge19.powerSum_term_eq_zero_of_not_nontrivial
#print axioms RvMBridge19.summable_powerSum
#print axioms RvMBridge19.powerSum_conj
#print axioms RvMBridge19.powerSum_re
#print axioms RvMBridge19.zterm_at_zero
#print axioms RvMBridge19.tsum_zterm_zero
#print axioms RvMBridge19.deriv_logDeriv_xi_eventuallyEq
#print axioms RvMBridge19.iteratedDeriv_tsum_zterm
#print axioms RvMBridge19.powerSum_eq_taylor
#print axioms RvMBridge19.powerSum_eq_neg_taylor
#print axioms RvMBridge19.pairedPowerSum_term_eq_zero_of_not_nontrivial
#print axioms RvMBridge19.abs_re_inv_pow_le
#print axioms RvMBridge19.summable_pairedPowerSum
#print axioms RvMBridge19.pairedPowerSum_eq_powerSum
#print axioms RvMBridge19.logDeriv_xi_one_sub
#print axioms RvMBridge19.logDeriv_xi_eq
#print axioms RvMBridge19.logDeriv_xi_analyticAt
#print axioms RvMBridge19.hasDerivAt_logDeriv_xi
#print axioms RvMBridge19.xi_ne_zero_on_segment
#print axioms RvMBridge19.im_ne_zero_of_nontrivial
#print axioms RvMBridge19.ofReal_ne_of_im_ne_zero
#print axioms RvMBridge19.abs_im_le_norm_ofReal_sub
#print axioms RvMBridge19.norm_zterm_zero_ofReal_le
#print axioms RvMBridge19.inv_im_sq_le_majorant
#print axioms RvMBridge19.norm_zterm_zero_ofReal_le_segBound
#print axioms RvMBridge19.continuous_zterm_zero_ofReal
#print axioms RvMBridge19.integral_zterm_zero
#print axioms RvMBridge19.zeros_countable
#print axioms RvMBridge19.support_zterm_subset
#print axioms RvMBridge19.hasSum_integral_zterm
#print axioms RvMBridge19.tsum_inv_add_inv_one_sub
#print axioms RvMBridge19.refTerm_reflect
#print axioms RvMBridge19.refTerm_eq_zero_of_not_nontrivial
#print axioms RvMBridge19.summable_refTerm
#print axioms RvMBridge19.tsum_refTerm
#print axioms RvMBridge19.pairedPowerSum_one_eq
#print axioms RvMBridge19.logDeriv_zeta_eq_near_one
#print axioms RvMBridge19.zetaLogDerivReg_eventuallyEq
#print axioms RvMBridge19.logDeriv_zeta₁_analyticAt
#print axioms RvMBridge19.eta_eq
#print axioms RvMBridge19.dcoef_succ
#print axioms RvMBridge19.norm_dcoef
#print axioms RvMBridge19.re_pos_of_mem_ball
#print axioms RvMBridge19.norm_le_of_mem_ball
#print axioms RvMBridge19.norm_shift_ge
#print axioms RvMBridge19.shift_ne_zero
#print axioms RvMBridge19.hasDerivAt_dterm
#print axioms RvMBridge19.summable_dbound
#print axioms RvMBridge19.norm_dterm_le
#print axioms RvMBridge19.iteratedDeriv_dtail
#print axioms RvMBridge19.dtail_analyticAt
#print axioms RvMBridge19.half_mem_integerComplement
#print axioms RvMBridge19.psiHalf_eq
#print axioms RvMBridge19.psiHalf_eventuallyEq
#print axioms RvMBridge19.psiHalf_analyticAt
#print axioms RvMBridge19.summable_inv_nat_pow
#print axioms RvMBridge19.summable_even_inv_pow
#print axioms RvMBridge19.summable_odd_inv_pow'
#print axioms RvMBridge19.summable_odd_inv_pow
#print axioms RvMBridge19.tsum_odd_inv_pow
#print axioms RvMBridge19.iteratedDeriv_psiHalf
#print axioms RvMBridge19.archFn_analyticAt
#print axioms RvMBridge19.archCoeff_zero
#print axioms RvMBridge19.archCoeff_succ
#print axioms RvMBridge19.logDeriv_xi_eq_closed
#print axioms RvMBridge19.closedFn_analyticAt
#print axioms RvMBridge19.logDeriv_xi_eventuallyEq_one
#print axioms RvMBridge19.iteratedDeriv_one_div
#print axioms RvMBridge19.taylorOne_eq
#print axioms RvMBridge19.iter_deriv_comp_add_const
#print axioms RvMBridge19.taylorZero_eq
#print axioms RvMBridge19.pairedPowerSum_succ_eq
#print axioms RvMBridge19.liKernel_re
#print axioms RvMBridge19.liPaired_eq_sum
#print axioms RvMBridge19.liLimit_eq_sum
#print axioms RvMBridge19.liLimit_eq_taylorOne
#print axioms RvMBridge19.sum_choose_alt
#print axioms RvMBridge19.sum_choose_eta
#print axioms RvMBridge19.sum_choose_archCoeff
#print axioms RvMBridge19.liValue_of
#print axioms RvMBridge19.bl_explicit_formula_of_partialFraction
#print axioms RvMBridge19.zeroSet_closed
#print axioms RvMBridge19.logDeriv_xi_eq_lambda
#print axioms RvMBridge19.logDeriv_xi_eventuallyEq_lambda
#print axioms RvMBridge19.logDeriv_lambda_analyticAt
#print axioms RvMBridge19.deriv_logDeriv_lambda_eq
#print axioms RvMBridge19.lambdaDerivPartialFraction_of_xi
#print axioms RvMBridge19.eq_of_continuousAt_of_eventually_ne
#print axioms RvMBridge19.zeroMult_one_sub
#print axioms RvMBridge19.tsum_zero_series_one_sub
#print axioms RvMBridge19.deriv_logDeriv_xi_one_sub
#print axioms RvMBridge19.xiDerivPartialFraction_of_lambda
#print axioms RvMBridge19.xiDerivPartialFraction_iff
#print axioms RvMBridge19.liValue_of_lambda
#print axioms RvMBridge19.liValue_of_growth
#print axioms RvMBridge19.bl_explicit_formula_of_growth
#print axioms RvMBridge23.one_add_sq_le_of_ceil
#print axioms RvMBridge23.lcTerm_le_fiber_weight
#print axioms RvMBridge23.lcTerm_eq_zero_of_not_nontrivial
#print axioms RvMBridge23.zeroMult_cast_eq
#print axioms RvMBridge23.sum_zeroMult_fiber_le
#print axioms RvMBridge23.wt_nonneg
#print axioms RvMBridge23.wlog_nonneg
#print axioms RvMBridge23.summable_wt
#print axioms RvMBridge23.log_add_four_le
#print axioms RvMBridge23.log_div_le_rpow
#print axioms RvMBridge23.summable_wlog
#print axioms RvMBridge23.wcount_le
#print axioms RvMBridge23.wcount_nonneg
#print axioms RvMBridge23.summable_wbound
#print axioms RvMBridge23.summable_wcount
#print axioms RvMBridge23.sum_lcTerm_le
#print axioms RvMBridge23.S1_nonneg
#print axioms RvMBridge23.S2_nonneg
#print axioms RvMBridge23.tsum_wcount_le
#print axioms RvMBridge23.local_count_sum
#print axioms RvMBridge23.xiDiffExtGrowthRight_of_strip
#print axioms RvMBridge23.xiLogDerivDerivEq_of_strip
#print axioms RvMBridge25.norm_tail_integral_le
#print axioms RvMBridge25.re_riemannZeta_neg_of_unit_interval
#print axioms RvMBridge25.riemannZeta_ne_zero_of_unit_interval
#print axioms RvMBridge25.noRealZeroInUnitInterval
#print axioms RvMBridge25.liValue_of_partialFraction
#print axioms RvMBridge25.liValue_of_growth
#print axioms RvMBridge25.liValue_of_two
#print axioms RvMBridge25.bl_explicit_formula_of_two
#print axioms RvMBridge26.liValue_of_strip
#print axioms RvMBridge26.bl_explicit_formula_of_strip
#print axioms RvMBridge24.zeroMult_eq_zeta23
#print axioms RvMBridge24.zerosIn_finite
#print axioms RvMBridge24.sum_le_Ncount
#print axioms RvMBridge24.window_sum_le_five
#print axioms RvMBridge24.exists_window_bound
#print axioms RvMBridge24.norm_log_le
#print axioms RvMBridge24.norm_digamma_le_log
#print axioms RvMBridge24.landau_window
#print axioms RvMBridge24.FwinExt_eq
#print axioms RvMBridge24.isClosed_zeros
#print axioms RvMBridge24.eventually_not_zero
#print axioms RvMBridge24.logDeriv_xi_local
#print axioms RvMBridge24.Fwin_differentiableAt
#print axioms RvMBridge24.FwinExt_eventuallyEq_at_zero
#print axioms RvMBridge24.FwinExt_differentiableOn
#print axioms RvMBridge24.deriv_FwinExt
#print axioms RvMBridge24.exists_radius
#print axioms RvMBridge24.norm_deriv_FwinExt_le
#print axioms RvMBridge24.window_one_sub
#print axioms RvMBridge24.Fwin_one_sub
#print axioms RvMBridge24.le_mul_one_add
#print axioms RvMBridge24.Fwin_bound_core
#print axioms RvMBridge24.sphere_bound
#print axioms RvMBridge24.target_bound_high
#print axioms RvMBridge24.tsum_lcTerm_le
#print axioms RvMBridge24.target_bound_low
#print axioms RvMBridge24.stripDerivBound
#print axioms RvMBridge24.xiDiffExtGrowthRight_of_localCount
#print axioms RvMBridge24.xiLogDerivDerivEq_of_localCount
#print axioms RvMBridge27.xi_logDeriv_deriv_eq
#print axioms RvMBridge27.liValue
#print axioms RvMBridge27.bl_explicit_formula
#print axioms RvMBridge28.zeroMult_one_sub_conj
#print axioms RvMBridge28.isNontrivialZero_one_sub_conj
#print axioms RvMBridge28.wOf
#print axioms RvMBridge28.wOf_ne_zero
#print axioms RvMBridge28.one_sub_inv_eq_inv_wOf
#print axioms RvMBridge28.one_sub_inv_one_sub_conj
#print axioms RvMBridge28.liKernel_eq_inv_wOf
#print axioms RvMBridge28.liKernel_one_sub_conj
#print axioms RvMBridge28.re_pow_eq
#print axioms RvMBridge28.re_inv_pow_eq
#print axioms RvMBridge28.pair_re_eq
#print axioms RvMBridge28.pow_add_inv_pow_eq_cosh
#print axioms RvMBridge28.sinh_mul_cos_sub_cosh_mul_sin_nonpos
#print axioms RvMBridge28.cosh_mul_cos_le_one
#print axioms RvMBridge28.cosh_mul_cos_le_one_of_abs_le
#print axioms RvMBridge28.arctan_le_self
#print axioms RvMBridge28.half_le_arctan
#print axioms RvMBridge28.abs_arctan
#print axioms RvMBridge28.wOf_re
#print axioms RvMBridge28.wOf_im
#print axioms RvMBridge28.normSq_sub_one
#print axioms RvMBridge28.normSq_eq_sq_add_sq
#print axioms RvMBridge28.wOf_re_pos
#print axioms RvMBridge28.abs_arg_wOf_eq
#print axioms RvMBridge28.abs_arg_wOf_le
#print axioms RvMBridge28.le_abs_arg_wOf
#print axioms RvMBridge28.abs_log_norm_wOf_le
#print axioms RvMBridge28.pair_re_nonneg_of_far
#print axioms RvMBridge28.pair_re_nonneg_of_on_line
#print axioms RvMBridge28.pair_re_nonneg_of_line_below
#print axioms RvMBridge28.liRe
#print axioms RvMBridge28.liRe_eq
#print axioms RvMBridge28.liRe_add_one_sub_conj
#print axioms RvMBridge28.hasSum_liRe
#print axioms RvMBridge28.liLimit_re_nonneg_of_pairs
#print axioms RvMBridge28.liLimit_re_nonneg_of_line_below
#print axioms RvMBridge28.archSide_add_finiteSide_re_nonneg_of_line_below
#print axioms RvMBridge28.liKernel_one
#print axioms RvMBridge28.liRe_one_nonneg
#print axioms RvMBridge28.liLimit_one_re_nonneg
#print axioms RvMBridge28.archSide_add_finiteSide_one_re_nonneg
#print axioms RvMBridge28.integral_shifted_mul_rpow_nonpos
#print axioms RvMBridge28.integral_fract_eq_shifted
#print axioms RvMBridge28.integrableOn_sawtooth
#print axioms RvMBridge28.integral_sawtooth_nonpos
#print axioms RvMBridge28.integral_fract_mul_rpow_le
#print axioms RvMBridge28.norm_integral_fract_cpow_le
#print axioms RvMBridge28.integral_fract_cpow_eq_of_zero
#print axioms RvMBridge28.zero_constraint
#print axioms RvMBridge28.zero_constraint_reflect
#print axioms RvMBridge28.box_one_sq
#print axioms RvMBridge28.box_one
#print axioms RvMBridge28.box_two
#print axioms RvMBridge28.one_sub_inv_eq_div_normSq
#print axioms RvMBridge28.liKernel_re_eq
#print axioms RvMBridge28.liLimit_re_nonneg_of_termwise
#print axioms RvMBridge28.re_pow_two
#print axioms RvMBridge28.re_pow_three
#print axioms RvMBridge28.re_pow_four
#print axioms RvMBridge28.re_pow_five
#print axioms RvMBridge28.ne_zero_of_nontrivial
#print axioms RvMBridge28.liKernel_two_re_nonneg
#print axioms RvMBridge28.liKernel_three_re_nonneg
#print axioms RvMBridge28.liKernel_four_re_nonneg
#print axioms RvMBridge28.liLimit_two_re_nonneg
#print axioms RvMBridge28.liLimit_three_re_nonneg
#print axioms RvMBridge28.liLimit_four_re_nonneg
#print axioms RvMBridge28.archSide_add_finiteSide_two_re_nonneg
#print axioms RvMBridge28.archSide_add_finiteSide_three_re_nonneg
#print axioms RvMBridge28.archSide_add_finiteSide_four_re_nonneg
#print axioms RvMBridge28.li5c0
#print axioms RvMBridge28.li5c1
#print axioms RvMBridge28.li5c2
#print axioms RvMBridge28.li5c3
#print axioms RvMBridge28.li5c4
#print axioms RvMBridge28.li5c4_nonneg
#print axioms RvMBridge28.li5c3_nonneg
#print axioms RvMBridge28.li5c2_nonneg
#print axioms RvMBridge28.li5c1_nonneg
#print axioms RvMBridge28.li5c0_nonneg
#print axioms RvMBridge28.rung5_identity
#print axioms RvMBridge28.liKernel_five_re_nonneg
#print axioms RvMBridge28.liLimit_five_re_nonneg
#print axioms RvMBridge28.archSide_add_finiteSide_five_re_nonneg
#print axioms RvMBridge29.cosh_mul_cos_le_one_window
#print axioms RvMBridge29.inv_add_inv_two_sq_le
#print axioms RvMBridge29.abs_arg_add_abs_log_le
#print axioms RvMBridge29.abs_arg_add_abs_log_le_sharp
#print axioms RvMBridge29.pair_re_nonneg_of_far_sharp
#print axioms RvMBridge29.pair_re_nonneg_of_line_below_sharp
#print axioms RvMBridge29.liLimit_re_nonneg_of_line_below_sharp
#print axioms RvMBridge29.archSide_add_finiteSide_re_nonneg_of_line_below_sharp
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
