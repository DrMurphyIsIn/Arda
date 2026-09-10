/-  AxiomGuardLiPositivity -- CI kernel-axiom guard for the Li positivity ladder.

    Mirrors AxiomGuardRHInBox.lean: NOT a `lean_lib`; CI runs it explicitly with

        lake env lean AxiomGuardLiPositivity.lean

    AFTER `lake build`, and FAILS if any `#print axioms` output mentions `sorryAx`.

    Guarded anchors:
      * LiPositivity.li_rung_0 / li_rung_19 -- the first and last emitted rungs
        (0 ≤ (taylorCoeff riemannXi n).re from the certified rational lower
        bound hypothesis; the Arb enclosure is the documented trust seam).
      * LiPositivity.li_neg_refutes_rh -- the falsifiability face: a certified
        negative upper bound on any rung refutes RH through the upstream
        equivalence.  Never expected to fire.
      * LiCriterion.li_criterion_rh_iff -- the UPSTREAM reduction itself
        (nicholasbulka/li-criterion-rh-equivalence-lean, pinned in
        lakefile.toml): RiemannHypothesis ↔ ∀ n, 0 ≤ (taylorCoeff riemannXi n).re.
        Guarding it here re-verifies the dependency's axiom hygiene at our pin.

    conjecture1_proved = False: rungs are finite necessary-condition checks;
    the uniform ∀ n IS RH and nothing here approaches it.
-/
import LiPositivity
import LiLadder
import RvMXiBridge
import RvMDigammaProd
import RvMDigammaLogDeriv
import RvMDigammaSummable
import RvMDigammaTprod
import RvMDigammaComplete
import RvMTrigamma

#print axioms LiPositivity.li_rung_0
#print axioms LiPositivity.li_rung_19
#print axioms LiPositivity.li_neg_refutes_rh
#print axioms LiCriterion.li_criterion_rh_iff

-- LiLadder (hand-written reduction layer): the ladder as a reduction of RH to
-- its tail. Restates li_criterion_rh_iff relative to a certified prefix; proves
-- neither side of RH. conjecture1_proved = False.
#print axioms LiPositivity.li_rh_iff_tail
#print axioms LiPositivity.li_tail_peel
#print axioms LiPositivity.li_rh_iff_tail_zero

-- RvMXiBridge (shared-object anchor): the RvM reflection foundation ported to
-- the UPSTREAM riemannXi -- the SAME function whose Taylor coefficients Li's
-- criterion uses. Demonstrates the RvM apparatus attaches to the Li object on
-- the unified v4.34 island. Does NOT link count N(T) to coefficients lambda_n
-- (that needs the explicit formula). conjecture1_proved = False.
#print axioms LiPositivity.logDeriv_riemannXi_reflect
#print axioms LiPositivity.logDeriv_riemannXi_conj
#print axioms LiPositivity.fold_pointwise_riemannXi

-- Phase 2 brick 3 (the crux): the Weierstrass product equals 1/Gamma.
-- core_prod_identity: s*prod(1+s/(n+1)) = prod(s+j)/N!; partial_wFactor_prod: closed-form
-- partial product; weierstrass_prod_eq_inv_Gamma: s*e^{gamma s}*prod' wFactor = 1/Gamma,
-- gamma pinned via GammaSeq_tendsto_Gamma + tendsto_harmonic_sub_log. conjecture1_proved = False.
#print axioms RvMWeierstrass.core_prod_identity
#print axioms RvMWeierstrass.partial_wFactor_prod
#print axioms RvMWeierstrass.weierstrass_prod_eq_inv_Gamma

-- Phase 2 brick 4 (part 1): log-derivative of a Weierstrass factor.
-- logDeriv (wFactor n) s = 1/(s+(n+1)) - 1/(n+1) -- the classical digamma summand; the per-factor
-- input to logDeriv_tprod_eq_tsum in the b4 assembly. conjecture1_proved = False.
#print axioms RvMWeierstrass.logDeriv_wFactor

-- Phase 2 brick 4 (part 2): summability of the digamma summands (O(1/n^2)) -- the Summable
-- hypothesis feeding logDeriv_tprod_eq_tsum in the b4 assembly. conjecture1_proved = False.
#print axioms RvMWeierstrass.summable_logDeriv_wFactor

-- Phase 2 brick 4 (part 3): log-derivative of the Weierstrass product = the digamma series.
-- logDeriv (prod'_n wFactor n) s = sum'_n (1/(s+n+1) - 1/(n+1)), via logDeriv_tprod_eq_tsum
-- (factors entire+nonzero, summands summable [part 2], product loc-unif convergent [b2] and
-- nonzero [b3]). conjecture1_proved = False.
#print axioms RvMWeierstrass.logDeriv_tprod_wFactor

-- Phase 2 brick 4 (part 4, FINAL, b4 COMPLETE): the digamma series for Complex.digamma.
-- digamma s = -1/s - gamma - sum'_n (1/(s+n+1) - 1/(n+1)) (poles excluded). Bridge: G z =
-- z e^{gamma z} prod' wFactor = (Gamma z)^{-1} EVERYWHERE (Continuous.ext_on, dense pole complement),
-- so logDeriv G s = -digamma s; product rule = 1/s + gamma + series. conjecture1_proved = False.
#print axioms RvMWeierstrass.digamma_series

-- Phase 3: the trigamma value psi'(1/2) = pi^2/2 + the pole-complement-neighbourhood foundation.
-- deriv Complex.digamma (1/2) = pi^2/2: differentiate digamma_series (b4) term-by-term on B(1/2,1/4)
-- (hasSum_deriv_of_summable_norm) and sum via Phase 1. poleCompl_mem_nhds: the pole complement is a
-- neighbourhood (reusable). conjecture1_proved = False.
#print axioms RvMWeierstrass.poleCompl_mem_nhds
#print axioms RvMWeierstrass.deriv_digamma_one_half
