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

#print axioms RvMBridge.rvm_unbounded_mean_density
#print axioms RvMBridge.eventually_Ncount_ge
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
