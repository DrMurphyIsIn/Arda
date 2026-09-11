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
import RvMLiUnified
import RvMLiCountBridge
import RvMLiStratum2
import RvMLiStratum3
import RvMLiFrontierA
import RvMLiFrontierD
import RvMLiOrthogonal
import RvMDigammaLogDeriv
import RvMDigammaSummable
import RvMDigammaTprod
import RvMDigammaComplete
import RvMTrigamma
import RvMPolygamma
import RvMPolygammaHigher
import RvMGammaR
import RvMGammaRIterate
import RvMMobius
import RvMPhiChain
import RvMFaaDiBruno
import RvMLeibniz
import RvMArchimedeanCoeff
import RvMLiConnection

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

-- ============================================================================
-- The N(T) <-> lambda_n bridge arc (S1-S3 + frontier a + d + orthogonal reroute).
-- These headline theorems were merged in #427/#429/#430/#431/#434/#436 but were
-- not wired into this guard; below closes that gap so CI enforces their
-- sorryAx-freedom too. conjecture1_proved = False throughout.
-- ============================================================================

-- RvMLiUnified (#427): the two developments are about ONE function. xiTele_eq_riemannXi
-- is a `ring` identity; riemannXi_winding_eq_RvM restates the RvM count for the upstream
-- riemannXi; rvm_and_li_share_riemannXi is the CONJUNCTION of the two facts -- it asserts
-- NO implication linking the count N(T) to the coefficients lambda_n. conjecture1_proved = False.
#print axioms RvMLiUnified.xiTele_eq_riemannXi
#print axioms RvMLiUnified.riemannXi_winding_eq_RvM
#print axioms RvMLiUnified.rvm_and_li_share_riemannXi

-- RvMLiCountBridge (#429, Stratum 1): the shared weighted argument-principle engine.
-- analytic_weighted_count_eq_winding computes 2*pi*i*sum mult*g(rho) for arbitrary
-- analytic f and holomorphic weight g -- weight 1 gives N(T), weight liWeight n gives
-- the finite Li partial sum. One engine, two weights. conjecture1_proved = False.
#print axioms DiffractionCore.analytic_weighted_count_eq_winding
#print axioms DiffractionCore.liWeight_analyticAt
#print axioms DiffractionCore.liWeight_at_zero

-- RvMLiStratum2 (#430): lambda_n is the limit of finite partial sums over zero-subsets,
-- conditional on genus-1 summability (hgenus) and the Hadamard product (hhad) -- the two
-- named analytic hypotheses, left undischarged. conjecture1_proved = False.
#print axioms RvMLiStratum2.liCoeff_isLimit_partialSums

-- RvMLiStratum3 (#430): the finite Li explicit formula, DERIVED from rect_explicit_formula.
-- Prime (Bragg) side on the right edge as a term-level von Mangoldt sum; the left/horizontal
-- edges remain raw integrals of liWeight*zeta'/zeta -- the archimedean residual is NOT closed
-- here. This is the finite skeleton of Bombieri-Lagarias, NOT the lambda_n asymptotic (which
-- needs the archimedean main-term extraction). conjecture1_proved = False.
#print axioms DiffractionCore.li_finite_explicit_formula

-- RvMLiFrontierA (#431): the xi four-way split (log xi)' = 1/s + 1/(s-1) + (log zeta)' +
-- (log Gamma_R)' -- isolates the archimedean factor as 1/2 psi(s/2). conjecture1_proved = False.
#print axioms DiffractionCore.logDeriv_xiTele_four_split

-- RvMLiFrontierD (#434): the divisor <-> NontrivialZero index-match (value-preserving reindex).
-- conjecture1_proved = False.
#print axioms RvMLiFrontierD.zeroFinset_sum_via_nontrivial

-- RvMLiOrthogonal (#436): the reroute base stone. logDeriv_gammaR_one = -(gamma + log 4pi)/2,
-- the exact k=0 archimedean datum at s=1 -- the digamma asymptotic barrier is route-specific,
-- and this Taylor/Mobius route samples at the fixed point s=1. conjecture1_proved = False.
#print axioms RvMLiOrthogonal.logDeriv_gammaR_one
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

-- Phase 4a foundation: the general trigamma series (any s off the poles).
-- deriv Complex.digamma s = sum'_k 1/(s+k)^2. Differentiate digamma_series term-by-term on the ball
-- B(s, eps/2) with a case-split O(1/n^2) bound; reindex/summability from the differentiation HasSum.
-- Base case for the polygamma induction. conjecture1_proved = False.
#print axioms RvMWeierstrass.deriv_digamma_eq_tsum

-- Phase 4a proper: higher polygamma values. hasDerivAt_P: d/ds sum' 1/(s+k)^p = -p sum'
-- 1/(s+k)^(p+1) (p>=2, case-split O(1/n^p) bound). iteratedDeriv_digamma: iteratedDeriv m digamma s
-- = (-1)^(m+1) m! sum' 1/(s+k)^(m+1) (m>=1), by induction. conjecture1_proved = False.
#print axioms RvMWeierstrass.hasDerivAt_P
#print axioms RvMWeierstrass.iteratedDeriv_digamma

-- Phase 4b: the archimedean log-derivative identity. logDeriv Gammaℝ s = -log pi/2 + (1/2) psi(s/2)
-- (s/2 off the non-positive integers), from Gammaℝ = pi^(-s/2)*Gamma(s/2) via logDeriv_mul +
-- HasDerivAt.const_cpow + Gamma chain rule. Reduces the archimedean factor to the Phase-4a polygamma
-- values at 1/2; m=0 recovers logDeriv_gammaR_one. conjecture1_proved = False.
#print axioms RvMWeierstrass.logDeriv_Gammaℝ_eq

-- Phase 4b iterate (COMPLETE): local iterated chain rule for the half-argument digamma.
-- digamma_contDiffOn_re_pos (analytic on {Re>0}), iteratedDeriv_digamma_half (iteratedDeriv m
-- (psi(s/2)) x = (1/2)^m psi^(m)(x/2) via iteratedDerivWithin_comp_const_smul + open-set conversion),
-- iteratedDeriv_logDeriv_GammaR_one: iteratedDeriv m (logDeriv GammaR) 1 = (1/2)^(m+1) iteratedDeriv m
-- digamma (1/2) (m>=1). conjecture1_proved = False.
#print axioms RvMWeierstrass.digamma_contDiffOn_re_pos
#print axioms RvMWeierstrass.iteratedDeriv_digamma_half
#print axioms RvMWeierstrass.iteratedDeriv_logDeriv_Gammaℝ_one

-- Phase 4c foundation: Mobius iterated derivatives. iteratedDeriv n (1-w)^{-1} z = n!/(1-z)^(n+1)
-- (induction, eventual-eq on {w!=1}, HasDerivAt.pow.inv.const_mul); at 0 gives n!. Feeds Faa di Bruno
-- on the (logDeriv GammaR) o (1/(1-z)) composition. conjecture1_proved = False.
#print axioms RvMWeierstrass.iteratedDeriv_mobius
#print axioms RvMWeierstrass.iteratedDeriv_mobius_zero

-- Phase 4c foundation: log-derivative of the Mobius pullback phi f = f o M, M(z)=(1-z)^{-1}.
-- logDeriv (fun w => f((1-w)^{-1})) z = logDeriv f ((1-z)^{-1}) * M'(z) (logDeriv_comp). Separates the
-- outer logDeriv f (frontier-a split) from the inner Mobius derivative. conjecture1_proved = False.
#print axioms RvMWeierstrass.logDeriv_phi

-- Phase 4c core: Faa di Bruno on the archimedean composition (logDeriv GammaR) o M, M=(1-z)^{-1}.
-- iteratedDeriv_logDerivGammaR_comp_mobius (i): iteratedDeriv i (fun z => logDeriv GammaR ((1-z)^{-1}))
-- 0 = sum_{c:OrderedFinpartition i} (prod_j (c.partSize j)!) . iteratedDeriv c.length (logDeriv GammaR) 1.
-- Via iteratedDeriv_scomp_eq_sum_orderedFinpartition (logDeriv GammaR analytic at 1, M smooth at 0) +
-- iteratedDeriv_mobius_zero. conjecture1_proved = False.
#print axioms RvMWeierstrass.iteratedDeriv_logDerivGammaℝ_comp_mobius

-- Phase 4c: the Leibniz product rule for iterated derivatives (Mathlib GAP -- only had the norm
-- bound). leibniz_sum_step (Pascal reindex), iteratedDerivWithin_mul (open set, ContDiffOn top),
-- iteratedDeriv_mul_of_isOpen. iteratedDeriv n (f*g) x = sum_k C(n,k) iteratedDeriv k f x . iteratedDeriv
-- (n-k) g x. conjecture1_proved = False.
#print axioms RvMWeierstrass.leibniz_sum_step
#print axioms RvMWeierstrass.iteratedDerivWithin_mul
#print axioms RvMWeierstrass.iteratedDeriv_mul_of_isOpen

-- Phase 4c CAPSTONE: the archimedean Li coefficient as a Leibniz sum.
-- taylorCoeff_GammaR_leibniz (n): LiCriterion.taylorCoeff Complex.GammaR n = (sum_{k<=n} C(n,k) *
-- iteratedDeriv k (logDeriv GammaR o M) 0 * (n-k+1)!) / n!. Assembles logDeriv_phi + Leibniz (iterated
-- Deriv_mul_of_isOpen) + Mobius derivs, wired to the upstream taylorCoeff. Composition-derivs are the
-- Phase-4c Faa di Bruno sums of Phase-4b polygamma values. conjecture1_proved = False.
#print axioms RvMWeierstrass.taylorCoeff_Gammaℝ_leibniz

-- The FULL connection to the upstream Li machinery.
-- logDeriv_phi_riemannXi_split: logDeriv (phi riemannXi) z = (1/s)M' + (1/(s-1))M' + logDeriv zeta(s)M'
-- + logDeriv (phi GammaR) z, s=(1-z)^{-1}. Exhibits the archimedean generating function logDeriv(phi
-- GammaR) (whose Taylor coeffs = Phase-4 polygamma data, taylorCoeff_GammaR_leibniz) as an explicit
-- summand of the Li coefficient generating function, via logDeriv_phi + xiTele_eq_riemannXi + the
-- frontier-a four-split. conjecture1_proved = False.
#print axioms RvMWeierstrass.logDeriv_phi_riemannXi_split
