/-  AxiomGuardLiPositivity -- CI kernel-axiom guard for the Li positivity ladder.

    Declared as a `lean_lib` in defaultTargets, so `lake build` compiles this file and thus
    transitively every module it imports -- the guard's import closure is always built before the
    check, with no defaultTargets list to maintain (cf. #448/#451). CI then still runs it explicitly
    with

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
import RvMLiCoeffSplit
import RvMZetaPoleReg
import RvMLiCoeffId
import RvMGammaRCapstone
import RvMRouteP
import RvMOnLinePositivity
import RvMPairedSummandAnatomy
import RvMCompanionPrime
import RvMCompanionBragg
import RvMLiWeightReconcile
import RvMLiWeightTsum
import RvMCompanionCoeff
import RvMCompanionBraggLimit
import ZetaLogBound
import DlvpZetaRateEffective
import RvMBacklundAux
import RvMBacklundIVT
import RvMBacklundCenter
import RvMBacklundJensen
import RvMBacklundConfine
import RvMBacklundPartition
import RvMBacklundSignConst
import RvMBacklundFinite
import RvMBacklundOrder
import RvMBacklundConfineNonstrict
import RvMBacklundSignClosed
import RvMBacklundCount
import RvMBacklundZeta
import RvMBacklundCountJensen
import RvMBacklundS
import RvMBacklundLogCont
import RvMBacklundExplicit
import RvMNTEffective
import RvMNTCount
import RvMRoutePFalsify
import BraggFloor
import RvMNTLadder
import AllZeros_h4000
import StripClear

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

-- The coefficient-level connection to the upstream Li machinery.
-- taylorCoeff_riemannXi_split (n): LiCriterion.taylorCoeff riemannXi n = taylorCoeff (fun s=>s) n +
-- taylorCoeff zetaPoleCompanion n + taylorCoeff GammaR n. The actual Li coefficient (whose positivity
-- li_criterion_rh_iff equates to RH) decomposed additively, the archimedean summand taylorCoeff GammaR
-- n being the exact polygamma data (taylorCoeff_GammaR_leibniz). Via companion regularisation of the
-- zeta pole + full-nbhd split (continuity upgrade) + iteratedDeriv_add. conjecture1_proved = False.
#print axioms RvMWeierstrass.taylorCoeff_riemannXi_split

-- The ζ-pole regularization of the coefficient split, made explicit.
-- logDeriv_phi_zetaPoleCompanion_regularizes: on 𝓝[≠]0 the companion pullback = pole pullback
-- logDeriv(phi (·-1)) + ζ pullback logDeriv(phi ζ) (both singular at 0);
-- analyticAt_logDeriv_phi_zetaPoleCompanion: yet the companion pullback is analytic at 0, so
-- taylorCoeff zetaPoleCompanion n is a FINITE datum with the s=1 pole cancelled. conjecture1_proved=False.
#print axioms RvMWeierstrass.logDeriv_phi_zetaPoleCompanion_regularizes
#print axioms RvMWeierstrass.analyticAt_logDeriv_phi_zetaPoleCompanion

-- The elementary summand resolved + the explicit split.
-- taylorCoeff_id_eq_one: taylorCoeff (fun s=>s) n = 1 (the 1/s pole pulls back to M, deriv^[n] M 0 = n!).
-- taylorCoeff_riemannXi_split_explicit: taylorCoeff riemannXi n = 1 + taylorCoeff zetaPoleCompanion n
-- + taylorCoeff GammaR n -- every non-arithmetic term explicit. conjecture1_proved=False.
#print axioms RvMWeierstrass.taylorCoeff_id_eq_one
#print axioms RvMWeierstrass.taylorCoeff_riemannXi_split_explicit

-- The archimedean Li coefficient as one explicit polygamma-at-1/2 combination.
-- iteratedDeriv_logDeriv_GammaR_one_eq_archGamma: iteratedDeriv m (logDeriv GammaR) 1 = archGamma m
-- (archGamma 0 = -log pi/2 + (1/2)psi(1/2); archGamma m = (1/2)^(m+1) psi^(m)(1/2) for m>=1).
-- taylorCoeff_GammaR_polygamma: taylorCoeff GammaR n = Leibniz/FaaDiBruno finite combination of
-- archGamma (glues #458->#456->#453/#452). conjecture1_proved=False.
#print axioms RvMWeierstrass.iteratedDeriv_logDeriv_Gammaℝ_one_eq_archGamma
#print axioms RvMWeierstrass.taylorCoeff_Gammaℝ_polygamma

-- Route P: RH localized onto the companion coefficient (kernel reduction, NOT a proof).
-- rh_iff_companion_ge: RiemannHypothesis <-> forall n, -(1+(taylorCoeff GammaR n).re) <=
-- (taylorCoeff zetaPoleCompanion n).re. An IFF -- relocates RH onto one explicit inequality per n;
-- proves nothing about RH. conjecture1_proved=False.
#print axioms RvMWeierstrass.rh_iff_companion_ge

-- Route P (Brick D3 part 1): the falsifiability atom.
-- companion_below_floor_refutes_rh (n)(h: (taylorCoeff zetaPoleCompanion n).re <
--   -(1+(taylorCoeff GammaR n).re)): ¬RiemannHypothesis. Contrapositive of rh_iff_companion_ge --
--   one sub-floor companion value refutes RH. The negative face the bragg_floor emitter targets;
--   never expected to fire. Proves nothing about RH. conjecture1_proved=False.
#print axioms RvMWeierstrass.companion_below_floor_refutes_rh

-- Route P (creative): manifest positivity of on-line zero contributions.
-- onLine_liPairedSummand_eq_normSq: for a nontrivial zero with re=1/2, liPairedSummand n rho =
-- normSq(1 - (1-1/rho)^(n+1)) -- a perfect square (|w|=1 => w^-(n+1)=conj w^(n+1)); nonneg + real.
-- Unconditional; the on-line side of the signature dichotomy. Does NOT prove RH. conjecture1_proved=False.
#print axioms RvMWeierstrass.onLine_liPairedSummand_eq_normSq
#print axioms RvMWeierstrass.onLine_liPairedSummand_nonneg
#print axioms RvMWeierstrass.onLine_liPairedSummand_im

-- Route P extended: unconditional anatomy of the paired Li summand.
-- liPairedSummand_eq_two_sub_v_sub_inv: liPairedSummand n ρ = 2 - v - v⁻¹ (v=(1-1/ρ)^(n+1)), ANY zero.
-- liPairedSummand_re_nonneg_iff: 0 ≤ (·).re ↔ (v+v⁻¹).re ≤ 2 (the exact per-zero positivity condition).
-- onLine_re_v_add_inv_le_two: on-line (|v|=1) ⟹ condition holds automatically. conjecture1_proved=False.
#print axioms RvMWeierstrass.liPairedSummand_eq_two_sub_v_sub_inv
#print axioms RvMWeierstrass.liPairedSummand_re_nonneg_iff
#print axioms RvMWeierstrass.onLine_re_v_add_inv_le_two

-- Route P, Brick D1 (diffraction reading): the companion IS the log-prime spectrum plus the pole.
-- logDeriv_zetaPoleCompanion_eq_vonMangoldt: for Re s>1, logDeriv zetaPoleCompanion s = -L(Λ) s + (s-1)⁻¹
-- (von Mangoldt Bragg peaks at k·log p, + explicit pole). Compose of logDeriv_zeta_eq_companion_sub_pole
-- (#461) + logDeriv_zeta_eq_neg_LSeries_vonMangoldt. Re-coordinatization onto the prime side, NOT a step
-- toward RH (the series converges only Re s>1). See ROUTEP_DIFFRACTION_SCOPE. conjecture1_proved=False.
#print axioms RvMWeierstrass.logDeriv_zetaPoleCompanion_eq_vonMangoldt

-- Route P, Brick D2a: the companion right-edge Bragg integrand.
-- companion_right_edge_prime_integrand: for 1<σ₁, g·logDeriv zetaPoleCompanion = g·(-L(Λ)+(·-1)⁻¹).
#print axioms RvMWeierstrass.companion_right_edge_prime_integrand

-- Route P, Brick D3 part 2: the bragg_floor diffraction ladder (emitted, DO NOT EDIT BY HAND).
-- bragg_rung_0 / bragg_rung_19: the first and last emitted Bragg rungs -- the truncated log-prime
-- (von Mangoldt / Bragg) amplitude at base point s0>1, net of a certified tail, clears the explicit
-- archimedean floor -(1+Re taylorCoeff GammaR n). A FINITE rational inequality (norm_num); the three
-- literals are Arb (python-flint) enclosures (the documented trust seam). Mid-range orders n=1..5 are
-- honestly REFUSED (the fixed-s0 order-0 amplitude does not dominate their floors), so the emitted
-- orders are n=0 and n=6..19. conjecture1_proved=False.
#print axioms BraggFloor.bragg_rung_0
#print axioms BraggFloor.bragg_rung_19
-- bragg_below_floor_refutes_rh (n)(braggVal)(hcomp: (taylorCoeff zetaPoleCompanion n).re = braggVal)
--   (hbelow: braggVal < -(1+(taylorCoeff GammaR n).re)): ¬RiemannHypothesis. The falsifiability face:
--   a certified sub-floor Bragg datum refutes RH via companion_below_floor_refutes_rh, but ONLY through
--   hcomp -- the CONDITIONAL, RH-hard taylorCoeff_companion_bragg_of_exhaustion_limits seam, carried as
--   an UNDISCHARGED hypothesis (never crossed). Never expected to fire. conjecture1_proved=False.
#print axioms BraggFloor.bragg_below_floor_refutes_rh

-- Route P, Brick D2b-1: the liWeight <-> liPairedSummand reconciliation.
-- liPairedSummand_eq_liWeight_paired: liPairedSummand n ρ = liWeight (n+1) ρ + liWeight (n+1) (pairedZero ρ).
#print axioms RvMWeierstrass.liPairedSummand_eq_liWeight_paired

-- Route P Brick D2b-2: the paired coefficient sum as a liWeight sum.
-- taylorCoeff_riemannXi_eq_liWeight_paired_tsum: taylorCoeff riemannXi n = 2⁻¹·∑'_ρ (liWeight (n+1) ρ
-- + liWeight (n+1) (pairedZero ρ)), conditional on hgenus/hhad (undischarged). Stays PAIRED -- the
-- unpaired liWeight tsum diverges, so no tsum_add split. tsum_liWeight_pairedZero_eq: FE symmetry at
-- reindex level (does NOT license the split). conjecture1_proved=False.
#print axioms RvMWeierstrass.taylorCoeff_riemannXi_eq_liWeight_paired_tsum
#print axioms RvMWeierstrass.tsum_liWeight_pairedZero_eq

-- Route P Brick D2b-3: isolation of the companion Taylor coefficient (zero-sum side).
-- taylorCoeff_companion_eq_liWeight_paired_tsum: taylorCoeff zetaPoleCompanion n = 2⁻¹·∑'_ρ (liWeight
-- (n+1) ρ + liWeight (n+1) (pairedZero ρ)) - 1 - taylorCoeff GammaR n. Combines D2b-2 (#478) + split
-- (#463); conditional hgenus/hhad (undischarged). Prime/Bragg-side dual stays category-(c) frontier.
#print axioms RvMWeierstrass.taylorCoeff_companion_eq_liWeight_paired_tsum

-- Route P D2b-3 (prime/Bragg side): CONDITIONAL reduction (frontier quarantined).
-- taylorCoeff_companion_bragg_of_exhaustion_limits: GIVEN the finite explicit formula along a box
-- exhaustion + the exhaustion/boundary/Bragg LIMITS (the unbuilt T→∞ + archimedean-extraction frontier,
-- carried as explicit hypotheses -- NONE established here), THEN companion coeff = (boundaryLim-braggLim)
-- /(2πi) - 1 - GammaR. Real limit-passage (tendsto_nhds_unique) + split (#463). Proves nothing about RH;
-- pins the frontier as three named limits. conjecture1_proved=False.
#print axioms RvMWeierstrass.taylorCoeff_companion_bragg_of_exhaustion_limits

-- Toolchain unification (2026-09-11): the v4.32 de la Vallee Poussin zero-free region +
-- zeta log-bound cascade (66 files, ~6255 lines) ported to the v4.34 li_positivity island -- 0 drift.
-- These supply the analytic-control inputs (zeta magnitude bound + dVP region) the RvM box->half-line
-- limit / li-weighted archimedean boundary extraction needs. conjecture1_proved=False.
#print axioms ZeroFreeBridge.zeta_log_bound
#print axioms ZeroFreeBridge.dlvp_zeta_region_rate_effective

-- Backlund S(T)=O(log T), PR 1: the auxiliary function F_T(z)=½(ζ(z+iT)+ζ(z-iT)).
-- backlundAux_ofReal: F_T(σ)=Re ζ(σ+iT) on the real axis (via riemannZeta_conj); backlundAux_analyticAt:
-- analytic off the poles z=1∓iT. Foundation for the sign-change/Jensen zero-count bound. conjecture1_proved=False.
#print axioms Backlund.backlundAux_ofReal
#print axioms Backlund.backlundAux_analyticAt

-- Backlund S(T)=O(log T), PR 2: sign changes of Re ζ yield real zeros of F_T (IVT).
-- backlundAux_im (real on axis); continuous_backlundAux_line (T≠0, poles 1∓iT off the axis);
-- backlundAux_root_of_sign_change (opposite signs ⟹ real zero of F_T). conjecture1_proved=False.
#print axioms Backlund.backlundAux_root_of_sign_change
#print axioms Backlund.continuous_backlundAux_line

-- Backlund S(T)=O(log T), PR 3a: the Jensen centre lower bound.
-- re_zeta_two_ge: 2-π²/6 ≤ Re ζ(2+iT) (Re-analogue of zeta_norm_ge_two_sub, via Dirichlet series +
-- basel_tail); backlundAux_two_norm_ge: 2-π²/6 ≤ ‖F_T(2)‖ (the Jensen denominator). conjecture1_proved=False.
#print axioms Backlund.re_zeta_two_ge
#print axioms Backlund.backlundAux_two_norm_ge

-- Backlund S(T)=O(log T), PR 3b: the Jensen zero-count of F_T is O(log T).
-- backlundAux_zero_count_le (T≥4): ∑ᶠ divisor F_T (closedBall 2 (3/2)) ≤ log((4T+19)/‖F_T(2)‖)/log(7/6),
-- via zeta_strip_bound (Re>0 sphere bound, survives below 1/2) + PR 3a centre bound + AnalyticOnNhd.
-- sum_divisor_le. Explicit O(log T). conjecture1_proved=False.
#print axioms Backlund.backlundAux_zero_count_le
#print axioms Backlund.backlundAux_analyticOnNhd_ball

-- Backlund S(T)=O(log T), PR 4a: half-plane argument-confinement (the hardest piece).
-- argChangeHoriz_abs_lt_pi_of_rePos: if Re f > 0 on the segment [x0,x1]+iT (and f differentiable,
-- logDeriv f continuous there), then |argChangeHoriz f T x0 x1| < π -- FTC (clog_real) turns Im ∫ f'/f
-- into arg f(x1+iT) - arg f(x0+iT), both in (-π/2,π/2). conjecture1_proved=False.
#print axioms Backlund.argChangeHoriz_abs_lt_pi_of_rePos

-- Backlund S(T)=O(log T), PR 4b: partition + sum.
-- argChangeHoriz_abs_lt_pi_of_re_sign: |argChangeHoriz f| < π when Re f is one sign (pos OR neg) on the
--   segment -- the Re<0 case reduces to PR 4a via f↦-f (logDeriv invariant, logDeriv_const_mul a=-1).
-- argChangeHoriz_abs_le_partition: over a partition σ0<...<σn with per-piece |argChangeHoriz|≤π, the
--   total ≤ n·π (sum_integral_adjacent_intervals + Finset.abs_sum_le_sum_abs). conjecture1_proved=False.
#print axioms Backlund.argChangeHoriz_abs_lt_pi_of_re_sign
#print axioms Backlund.argChangeHoriz_abs_le_partition

-- Backlund S(T)=O(log T), PR 4c (first piece): sign-constancy => confinement.
-- argChangeHoriz_abs_lt_pi_of_re_ne_zero: if Re f is continuous and NONVANISHING on the segment, then
--   |argChangeHoriz f| < π. A continuous nowhere-zero real fn on connected [[x0,x1]] can't change sign
--   (IVT intermediate_value_uIcc), so Re f one sign => PR 4b either-sign confinement. Reduces the
--   per-piece hyp to the natural output of partitioning at Re ζ's zeros. conjecture1_proved=False.
#print axioms Backlund.argChangeHoriz_abs_lt_pi_of_re_ne_zero

-- Backlund S(T)=O(log T), PR 4c (finiteness): F_T's real zeros are finite.
-- backlundAux_real_zeros_finite: {σ ∈ [1/2,2] | F_T σ = 0} is finite -- it injects (Complex.ofReal)
--   into the finite support of F_T's divisor on closedBall 2 (3/2) (PR 3b machinery). A real zero σ
--   gives ↑σ with F_T ↑σ=0: analyticOrderAt ≠0 (analyticOrderAt_ne_zero) and ≠⊤ (identity theorem, else
--   F_T≡0 contra F_T(2)≠0), so ↑σ ∈ divisor support. conjecture1_proved=False.
#print axioms Backlund.backlundAux_real_zeros_finite

-- Backlund S(T)=O(log T), PR 4c (ordering): finite forbidden set => monotone partition.
-- exists_monotone_partition_of_finite (Z:Finset ℝ)(a b)(hab)(hZ: Z ⊆ [a,b]): ∃ N σ, Monotone σ ∧ σ0=a
--   ∧ σN=b ∧ N≤Z.card+1 ∧ (∀k, σk∈[a,b]) ∧ (∀k<N, ∀z∈Z, z≤σk ∨ σ(k+1)≤z). Pure order theory:
--   sort {a,b}∪Z via Finset.orderEmbOfFin (strict-mono enum, _zero=min, _last=max, order-reflecting =>
--   nothing strictly between consecutive). Feeds PR 4b partition sum. conjecture1_proved=False.
#print axioms Backlund.exists_monotone_partition_of_finite

-- Backlund S(T)=O(log T), PR 4c (nonstrict): confinement allowing zeros at endpoints.
-- argChangeHoriz_abs_le_pi_of_re_nonneg: Re f ≥ 0 ∧ f ≠ 0 on segment ⟹ |argChangeHoriz| ≤ π (arg ∈
--   [-π/2,π/2] via Complex.abs_arg_le_pi_div_two_iff; FTC via f∈slitPlane from Re≥0∧f≠0).
-- argChangeHoriz_abs_le_pi_of_re_sign': either sign (Re f ≥0 OR ≤0) ∧ f≠0 ⟹ ≤π (Re≤0 case via -f).
-- Needed because partition endpoints ARE zeros (Re=0). conjecture1_proved=False.
#print axioms Backlund.argChangeHoriz_abs_le_pi_of_re_nonneg
#print axioms Backlund.argChangeHoriz_abs_le_pi_of_re_sign'

-- Backlund S(T)=O(log T), PR 4c (sign-on-closed): bridge 4c-order -> 4c-nonstrict.
-- re_one_sign_of_ne_zero_Ioo (g)(x0 x1)(hlt:x0<x1)(hcont: g cont on Icc)(hopen: g≠0 on Ioo): 0≤g on Icc
--   OR g≤0 on Icc. A continuous fn nonzero on the OPEN interval is one sign on the CLOSED (endpoints are
--   sign-compatible limits) -- else IVT (intermediate_value_uIcc between midpoint & opposite-sign point)
--   forces a zero strictly inside. Feeds 4c-nonstrict (endpoints = zeros ok). conjecture1_proved=False.
#print axioms Backlund.re_one_sign_of_ne_zero_Ioo

-- Backlund S(T)=O(log T), PR 4c (count): the capstone assembly.
-- argChangeHoriz_abs_le_card_zeros (f)(T a b)(hab)(Z)(hdiff)(hcont)(hne: f≠0 on segment)(hZsub: Z⊆[a,b])
--   (hZzero: Re f=0 => in Z): |argChangeHoriz f T a b| ≤ (Z.card+1)·π. Combines 4c-order (partition) +
--   4c-sign-on-closed (Re f one sign per closed piece) + 4c-nonstrict (piece ≤π, endpoints=zeros ok) +
--   4b (sum) + degenerate pieces=0 (integral_same). Horizontal half of Backlund S(T). conjecture1_proved=False.
#print axioms Backlund.argChangeHoriz_abs_le_card_zeros

-- Backlund S(T)=O(log T), PR 5: the ζ instantiation of the horizontal bound.
-- zeta_argChangeHoriz_abs_le (hT:4≤T)(hζne: ζ≠0 on [1/2,2]+iT CARRIED = S(T)-jump)(hlogcont: logDeriv ζ
--   cont CARRIED): |argChangeHoriz ζ T (1/2) 2| ≤ ((F_T real zeros).toFinset.card + 1)·π. Instantiates
--   the capstone argChangeHoriz_abs_le_card_zeros at f=riemannZeta; hdiff via differentiableAt_riemannZeta
--   (segment avoids pole s=1 since im=T≠0), hZsub/hZzero via backlundAux_ofReal (F_T ↑x=↑(Re ζ)).
--   conjecture1_proved=False.
#print axioms Backlund.zeta_argChangeHoriz_abs_le

-- Backlund S(T)=O(log T), PR 5 step 3: the EXPLICIT O(log T) horizontal bound.
-- zeta_argChangeHoriz_abs_le_log (hT:4≤T)(hζne)(hlogcont): |argChangeHoriz ζ T (1/2) 2| ≤
--   (log((4T+19)/‖F_T 2‖)/log(7/6) + 1)·π. Real zeros of F_T inject (ofReal) into divisor support (each
--   positive analytic order), so count ≤ card(support) ≤ Σᶠ divisor (≥1 on support) ≤ Jensen (PR 3b).
--   conjecture1_proved=False.
#print axioms Backlund.zeta_argChangeHoriz_abs_le_log

-- Backlund S(T)=O(log T), PR 6: discharging hlogcont.
-- continuousOn_logDeriv_zeta_segment (hT:4≤T)(hζne): logDeriv ζ continuous on [1/2,2]+iT -- derived from
--   ζ-analyticity (AnalyticOnNhd on {≠1}, .deriv, .continuousOn, comp path) + ζ≠0 (ContinuousOn.div).
-- riemannS_abs_le_log_of_ne_zero (hT:4≤T)(hζne): |riemannS T| ≤ log((4T+19)/‖F_T 2‖)/log(7/6)+2 --
--   the SLIMMED S(T)=O(log T), carrying ONLY hζne. conjecture1_proved=False.
#print axioms Backlund.continuousOn_logDeriv_zeta_segment
#print axioms Backlund.riemannS_abs_le_log_of_ne_zero

-- Arc A (effective RvM), PR A1: the pure-in-T Backlund bound.
-- riemannS_abs_le_log_explicit (hT:4≤T)(hζne): |riemannS T| ≤ log((4T+19)/(2−π²/6))/log(7/6)+2 --
--   the PR-6 headline with ‖F_T 2‖ majorized away by its Jensen-centre floor 2−π²/6
--   (backlundAux_two_norm_ge), giving a closed-form O(log T) in T alone. conjecture1_proved=False.
#print axioms Backlund.riemannS_abs_le_log_explicit

-- Arc A (effective RvM), PR A2: the effective Riemann-von Mangoldt bound.
-- nt_effective_bound (T)(hT:4≤T)(N)(4 xi-edge nonvanishings)(hζne)(hwind=2πiN):
--   |(N:ℝ) − 1 − θ(T)/π| ≤ log((4T+19)/(2−π²/6))/log(7/6)+2 -- the winding integer pinned to the
--   smooth main term 1+θ/π within explicit O(log T); error = riemannS T bounded by PR A1. Composes
--   xiTele_winding_eq_RvM (N=1+θ/π+S) with riemannS_abs_le_log_explicit. conjecture1_proved=False.
#print axioms Backlund.nt_effective_bound

-- Arc A (effective RvM), PR A3: the effective bound on the box xi-zero count.
-- nt_count_effective_bound (T)(hT:4≤T)(c R N)(hbox_ball)(4 Icc edge nonvanishings)(hin strict
--   interior)(hζne)(hwind=2πiN): ∃ s d, zeros⊆s ∧ Σd=N ∧ |(Σd:ℝ) − 1 − θ/π| ≤ bound. Composes
--   xiTele_count_eq_winding (box zero count = N) with nt_effective_bound. The zero count is derived
--   from the boundary winding, never assumed. conjecture1_proved=False.
#print axioms Backlund.nt_count_effective_bound

-- Arc A (effective RvM), PR A5: the LADDER PORT + interlock. The complete tiled Turing ladder
-- (AllZeros_h100..h4000 + StripClear + its RHInBox/confinement chain, 110 files) is PORTED from the
-- v4.32 zeta_zero_localization/zero_free_bridge islands onto this island (method of #424/#427/#483:
-- source copy, single import redirect RHInBoxAnalytic->RvMRHInBox; ZERO content drift). The two RH
-- tracks now interlock in ONE kernel statement:
-- zeta_segment_ne_zero_of_ladder: ladder conclusion + single-point ζ(1/2+iT)≠0 ⟹ the segment hζne --
--   the "T not a zero-ordinate" caveat COLLAPSES TO ONE POINT for T ≤ 4000.
-- nt_effective_bound_of_ladder: the effective RvM bound with the trust-shrunk hypothesis set.
-- all_nontrivial_zeros_up_to_height_4000_of_bands: the ported ladder capstone (3,474 zeros), its
--   per-band Arb bundles the documented trust seam, now importable beside the Li/RvM corpus.
-- conjecture1_proved=False throughout: finite verification + classical count; nothing approaches RH.
#print axioms Backlund.zeta_segment_ne_zero_of_ladder
#print axioms Backlund.nt_effective_bound_of_ladder
#print axioms AllZeros_h4000.all_nontrivial_zeros_up_to_height_4000_of_bands
#print axioms StripClear.height_floor_of_box_certs
