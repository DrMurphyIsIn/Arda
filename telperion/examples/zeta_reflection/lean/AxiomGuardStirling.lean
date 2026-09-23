/-  AxiomGuardStirling.lean -- A2 Theorem 2 (Stirling/Binet Γℝ enclosure) kernel-axiom guard.

    A `lean_lib`; CI (telperion-zeta-reflection.yml) builds it, then runs

        lake env lean AxiomGuardStirling.lean

    Prints the axiom sets of the completed A2 Theorem 2 anchors.  Expected on all:
    {propext, Classical.choice, Quot.sound} -- no sorryAx, no ofReduceBool.

      §1  Binet remainder + its K=1 enclosures:
        * binetRem                      (def -- printed for completeness)
        * norm_binetRem_le_ofReal       (unconditional, real argument)
        * norm_binetRem_le_of_anchor    (complex argument, anchor-parametrised)
      §2  Shift trick:
        * digamma_eq_shift_sub
        * binetRem_shift
      §3  Stirling decomposition of logDeriv Γℝ:
        * logDeriv_gammaR_stirling
        * logDeriv_gammaR_stirling_shift
      §4  Remainder envelope for Re z ≥ 1/4:
        * re_shift_ge
        * binet_remainder_envelope
      §5  Packaged enclosure (the interval-evaluator artifact):
        * logDeriv_gammaR_enclosure
      §6  Re/Im part enclosures (argChangeVert / θ integrands):
        * re_logDeriv_gammaR_enclosure
        * im_logDeriv_gammaR_enclosure
        * theta_integrand_enclosure

    conjecture1_proved = False (a finite computable enclosure, NOT a proof of RH).
-/
import StirlingBinet

#print axioms ZetaReflection.norm_binetRem_le_ofReal
#print axioms ZetaReflection.norm_binetRem_le_of_anchor
#print axioms ZetaReflection.digamma_eq_shift_sub
#print axioms ZetaReflection.binetRem_shift
#print axioms ZetaReflection.logDeriv_gammaR_stirling
#print axioms ZetaReflection.logDeriv_gammaR_stirling_shift
#print axioms ZetaReflection.re_shift_ge
#print axioms ZetaReflection.binet_remainder_envelope
#print axioms ZetaReflection.logDeriv_gammaR_enclosure
#print axioms ZetaReflection.re_logDeriv_gammaR_enclosure
#print axioms ZetaReflection.im_logDeriv_gammaR_enclosure
#print axioms ZetaReflection.theta_integrand_enclosure
