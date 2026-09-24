/-
  AxiomGuardDBN -- CI axiom guard for the Route C (de Bruijn-Newman) foundations island.

  Run as `lake env lean AxiomGuardDBN.lean | tee axioms.out; ! grep -q sorryAx axioms.out`.
  Every theorem/lemma of every island module gets a `#print axioms` line; the expected closure
  is `[propext, Classical.choice, Quot.sound]` (definitions like `thetaMoment`/`Φ`/`H`/`g`/`psi`
  are noncomputable and are covered through the theorems that mention them).

  Scope reminder.  The C2 representation theorem H_0 = ξ/8 (registry node RH.dbn_H0_eq_xi) IS an
  island theorem: `dbn_H0_eq_xi` in DBNXi (module E), assembled from DBNXiRiemann (module A:
  Riemann's symmetric integral for Mathlib's entire completedRiemannZeta₀), DBNXiCos (module B:
  the substitution x = e^{4u}), DBNGKernel (module C: the kernel g(u) = e^u psi(e^{4u}),
  g'' - g = 8 Phi, g'(0) = -1/2, decay and integration-by-parts side conditions) and DBNXiIBP
  (module D: two integrations by parts).  It is an identity between two entire functions, NOT
  RH-equivalent, and says nothing about where any zero lies.  DBNRealZerosIff proves the C4
  bridge RH <-> (all zeros of H_0 real) conditionally on C2 (explicit hypothesis / the named Prop
  obligation DBN.H0EqXi); DBNRealZerosIffFinal specialises it at `dbn_H0_eq_xi`, which gives the
  registry statement of RH.dbn_rh_iff_H0_real_zeros unconditionally.  That is an equivalence
  between two restatements of the same OPEN conjecture: it proves neither side.  NOTHING here is
  de Bruijn's t ≥ 1/2 theorem (registry node RH.dbn_debruijn_real_zeros, a registry STATEMENT,
  not an island theorem) or RH.  conjecture1_proved = False.
-/
import DBNDefs
import DBNRealZerosIff
import DBNXiRiemann
import DBNGKernel
import DBNXiCos
import DBNXiIBP
import DBNXi
import DBNRealZerosIffFinal
import DBNStrip
import DBNStep
import DBNStepControls
import DBNHurwitz
import DBNHeatApprox
import DBNDeBruijnReduction
import DBNHadamardCount
import DBNHadamardProduct
import DBNHadamardMean
import DBNHadamardLinear
import DBNHadamard
import DBNHadamardApprox
import DBNM1Approx
import DBNM1Parametric
import DBNM1RHIff
import DBNM1Controls
import DBNM4P15Defs
import DBNM4LocalStep
import DBNM4HeatUniform
import DBNM4P15Criterion

-- theta moments
#print axioms DBN.summable_thetaTerm
#print axioms DBN.summable_thetaMoment
#print axioms DBN.hasDerivAt_thetaMoment
#print axioms DBN.continuous_thetaMoment
#print axioms DBN.ofReal_thetaMoment_zero
#print axioms DBN.thetaMoment_zero_fe
#print axioms DBN.thetaMoment_fe_deriv1
#print axioms DBN.thetaMoment_fe_deriv2

-- Φ
#print axioms DBN.summable_thetaTerm_pnat
#print axioms DBN.summable_Φ_term
#print axioms DBN.thetaMoment_eq_two_mul_pnat
#print axioms DBN.Φ_eq
#print axioms DBN.Φ_neg
#print axioms DBN.Φ_even
#print axioms DBN.continuous_Φ

-- decay
#print axioms DBN.ΦBoundConst_nonneg
#print axioms DBN.summable_ΦBoundConst_term
#print axioms DBN.abs_Φ_le

-- integrability of the heat-flow integrand
#print axioms DBN.integrableOn_exp_quad_mul_exp_neg_exp
#print axioms DBN.norm_cos_le_exp_norm
#print axioms DBN.continuous_HIntegrand
#print axioms DBN.integrableOn_HIntegrand

-- H_t
#print axioms DBN.H_neg
#print axioms DBN.H_ofReal
#print axioms DBN.H_ofReal_im

-- ξ vocabulary bridge
#print axioms DBN.riemannXi_eq_completedRiemannZeta

-- H_t is entire
#print axioms DBN.norm_sin_le_exp_norm
#print axioms DBN.hasDerivAt_HIntegrand
#print axioms DBN.continuous_HIntegrand'
#print axioms DBN.hasDerivAt_H
#print axioms DBN.differentiable_H

-- Route C / C4 bridge (DBNRealZerosIff): change of variables + upstream unpacking (unconditional)
#print axioms DBN.xiArg_re
#print axioms DBN.xiArg_re_eq_half_iff
#print axioms DBN.xiArg_surj
#print axioms DBN.xiArgInv_im
#print axioms DBN.riemannXi_eq_zero_iff_strip_zero

-- Route C / C4 bridge, CONDITIONAL on C2 (hypothesis hC2 / obligation DBN.H0EqXi); the
-- expected closure is still [propext, Classical.choice, Quot.sound] because C2 is a hypothesis,
-- not an axiom.  These are NOT the registry theorem dbn_rh_iff_H0_real_zeros.
#print axioms DBN.H_zero_eq_zero_iff_of_H0_eq_xi
#print axioms dbn_rh_iff_H0_real_zeros_of_H0_eq_xi
#print axioms dbn_rh_iff_H0_real_zeros_of_obligation

-- Route C / C2 module A (DBNXiRiemann): ψ, the theta-kernel vocabulary bridges (N5), the
-- two-`Ioi 1`-integral formula for an arbitrary weak FE-pair (N1, N2), and Riemann's symmetric
-- integral for completedRiemannZeta₀ at every s (unconditional; NOT C2, NOT RH)
#print axioms DBN.summable_psi_term
#print axioms DBN.tsum_int_exp_eq_one_add_two_mul_psi
#print axioms DBN.thetaMoment_zero_eq_one_add_two_mul_psi
#print axioms DBN.thetaMoment_zero_eq_one_add_two_mul_pnat
#print axioms DBN.psi_exp_eq_thetaMoment
#print axioms DBN.psi_nonneg
#print axioms DBN.evenKernel_zero_eq_tsum
#print axioms DBN.evenKernel_zero_eq_one_add_two_mul_psi
#print axioms DBN.evenKernel_zero_eq_thetaMoment
#print axioms DBN.psi_eq_evenKernel
#print axioms DBN.continuousOn_psi
#print axioms DBN.weakFEPair_mellinConvergent_f_modif
#print axioms DBN.weakFEPair_f_modif_of_one_lt
#print axioms DBN.weakFEPair_integrableOn_Ioi_one
#print axioms DBN.mellin_indicator_Ioi_one
#print axioms DBN.weakFEPair_Λ₀_eq
#print axioms DBN.hurwitzEvenFEPair_zero_integrand
#print axioms DBN.integrableOn_psi_mul_cpow
#print axioms DBN.integral_hurwitzEvenFEPair_zero
#print axioms DBN.completedRiemannZeta₀_eq_integral_psi

-- C2 module C (DBNGKernel): the kernel g(u) = e^u psi(e^{4u}) of Riemann's symmetric
-- integral.  Ingredients of the representation theorem H_0 = xi/8, NOT the theorem itself.

-- DBNGKernel: N5 and the shared theta-moment decay helper
#print axioms DBN.thetaMoment_zero_sub_one_eq_two_mul_pnat
#print axioms DBN.thetaMoment_nonneg
#print axioms DBN.one_le_thetaMoment_zero
#print axioms DBN.thetaPnatConst_nonneg
#print axioms DBN.abs_thetaMoment_pnat_le
#print axioms DBN.thetaMoment_le_decay
#print axioms DBN.thetaMoment_zero_sub_one_le_decay

-- DBNGKernel: the kernel g and its closed-form derivatives
#print axioms DBN.g_eq_exp_mul_tsum_pnat
#print axioms DBN.g_nonneg
#print axioms DBN.hasDerivAt_g
#print axioms DBN.hasDerivAt_g'
#print axioms DBN.deriv_g
#print axioms DBN.deriv_g'
#print axioms DBN.continuous_g
#print axioms DBN.continuous_g'
#print axioms DBN.continuous_g''

-- DBNGKernel: kernel identity g'' - g = 8 Phi and g'(0) = -1/2
#print axioms DBN.g''_sub_g_eq
#print axioms DBN.g'_zero

-- DBNGKernel: decay bounds on u >= 0
#print axioms DBN.gKernelConst_nonneg
#print axioms DBN.abs_g_le
#print axioms DBN.abs_g'_le
#print axioms DBN.abs_g''_le

-- DBNGKernel: the atTop limit behind the island majorant
#print axioms DBN.tendsto_exp_quad_mul_exp_neg_exp
#print axioms DBN.tendsto_exp_lin_mul_exp_neg_exp

-- DBNGKernel: generic integrability / vanishing against exponential weights
#print axioms DBN.integrableOn_superExp_mul
#print axioms DBN.tendsto_superExp_mul_atTop
#print axioms DBN.norm_cos_mul_ofReal_le
#print axioms DBN.norm_sin_mul_ofReal_le

-- DBNGKernel: complexified kernels
#print axioms DBN.hasDerivAt_ofReal_g
#print axioms DBN.hasDerivAt_ofReal_g'
#print axioms DBN.continuous_ofReal_g
#print axioms DBN.continuous_ofReal_g'
#print axioms DBN.continuous_ofReal_g''
#print axioms DBN.norm_ofReal_g_le
#print axioms DBN.norm_ofReal_g'_le
#print axioms DBN.norm_ofReal_g''_le

-- DBNGKernel: integrability (pointwise and Pi.mul shapes; cos / sin instances)
#print axioms DBN.integrableOn_g_mul
#print axioms DBN.integrableOn_g'_mul
#print axioms DBN.integrableOn_g''_mul
#print axioms DBN.integrableOn_ofReal_g_mul_pi
#print axioms DBN.integrableOn_ofReal_g'_mul_pi
#print axioms DBN.integrableOn_ofReal_g''_mul_pi
#print axioms DBN.integrableOn_g_mul_cos
#print axioms DBN.integrableOn_g_mul_sin
#print axioms DBN.integrableOn_g'_mul_cos
#print axioms DBN.integrableOn_g'_mul_sin
#print axioms DBN.integrableOn_g''_mul_cos

-- DBNGKernel: boundary limits at +infinity and 0+
#print axioms DBN.tendsto_ofReal_g_mul_atTop
#print axioms DBN.tendsto_ofReal_g'_mul_atTop
#print axioms DBN.tendsto_ofReal_g''_mul_atTop
#print axioms DBN.tendsto_ofReal_g_mul_nhdsGT
#print axioms DBN.tendsto_ofReal_g'_mul_nhdsGT

-- DBNGKernel: the side conditions of the two integrations by parts (module D consumes these)
#print axioms DBN.hasDerivAt_cos_mul_ofReal
#print axioms DBN.hasDerivAt_neg_sin_mul_ofReal_mul
#print axioms DBN.norm_neg_sin_mul_ofReal_mul_le
#print axioms DBN.norm_neg_cos_mul_ofReal_mul_mul_le
#print axioms DBN.integrableOn_ofReal_g_mul_cos_deriv2
#print axioms DBN.integrableOn_ofReal_g'_mul_cos_deriv
#print axioms DBN.integrableOn_ofReal_g''_mul_cos_pi
#print axioms DBN.tendsto_ofReal_g_mul_cos_deriv_nhdsGT
#print axioms DBN.tendsto_ofReal_g_mul_cos_deriv_atTop
#print axioms DBN.tendsto_ofReal_g'_mul_cos_nhdsGT
#print axioms DBN.tendsto_ofReal_g'_mul_cos_atTop

-- DBNGKernel: the bridge to H_0
#print axioms DBN.integral_g''_sub_g_mul_cos

-- DBNGKernel: registry-shaped summary (proposed lemma node RH_dbn_g_kernel_identities)
#print axioms dbn_g_kernel_identities

-- Route C / C2 module B (DBNXiCos): the substitution x = e^{4u} in Riemann's symmetric integral,
-- completedRiemannZeta₀ (1/2 + iz/2) = 8 ∫_0^∞ g(u) cos(zu) du (unconditional; NOT RH)
#print axioms DBN.g_eq_thetaMoment
#print axioms DBN.g_eq_exp_mul_psi
#print axioms DBN.image_exp_four_mul_Ioi
#print axioms DBN.hasDerivAt_exp_four_mul
#print axioms DBN.integral_Ioi_one_eq_integral_exp_four_mul
#print axioms DBN.ofReal_exp_cpow
#print axioms DBN.xiCos_integrand
#print axioms DBN.completedRiemannZeta₀_half_add_eq

-- Route C / C2 module D (DBNXiIBP): the two integrations by parts (unconditional; NOT RH)
#print axioms DBN.integral_g_cos_ibp
#print axioms DBN.integral_g_cos_eq

-- Route C / C2 module E (DBNXi): the representation theorem H_0 = ξ/8 (registry node
-- RH.dbn_H0_eq_xi, statement verbatim) and H_0(i) = 1/16.  An identity between two entire
-- functions, NOT RH-equivalent.
#print axioms dbn_H0_eq_xi
#print axioms DBN.H_zero_I

-- Route C / C4, unconditional (DBNRealZerosIffFinal): the named obligation DBN.H0EqXi
-- discharged, and the registry statement of RH.dbn_rh_iff_H0_real_zeros verbatim.  An
-- equivalence between two restatements of the same OPEN conjecture; it proves neither side.
#print axioms DBN.H0EqXi_holds
#print axioms dbn_rh_iff_H0_real_zeros

-- Route C / C3 input (DBNStrip): the zero strip of H_0, C2-free.  L1b Gamma integral on the line
#print axioms DBN.integral_exp_smul_comp_exp
#print axioms DBN.ofReal_exp_cpow_comm
#print axioms DBN.integral_cexp_mul_exp_neg_exp
#print axioms DBN.integral_exp_mul_exp_neg_exp
#print axioms DBN.integrable_cexp_mul_exp_neg_exp
#print axioms DBN.integrable_exp_mul_exp_neg_exp

-- DBNStrip L1a: two-sided fold and Schwarz reflection
#print axioms DBN.continuous_expIntegrand
#print axioms DBN.norm_cexp_mul_I_le
#print axioms DBN.expIntegrand_neg
#print axioms DBN.integrableOn_expIntegrand_Ioi
#print axioms DBN.integrableOn_expIntegrand_Iic
#print axioms DBN.integrable_expIntegrand
#print axioms DBN.H_zero_eq_half_integral
#print axioms DBN.H_conj

-- DBNStrip L1b termwise + L1c Tonelli/Fubini and the half-plane identity (Im z < -1 only)
#print axioms DBN.Φ_eq_tsum_ΦTerm
#print axioms DBN.expTerm_eq
#print axioms DBN.stripArg_re
#print axioms DBN.one_div_pi_mul_sq_cpow
#print axioms DBN.integral_expTerm
#print axioms DBN.integrable_expTerm
#print axioms DBN.norm_expTerm_le
#print axioms DBN.pnat_pow_mul_one_div_rpow
#print axioms DBN.summable_integral_norm_expTerm
#print axioms DBN.hasSum_integral_expTerm
#print axioms DBN.integral_expIntegrand_eq
#print axioms DBN.H_zero_eq_of_im_lt

-- DBNStrip L1d: nonvanishing off the strip, the zero strip, and the registry statement verbatim
#print axioms DBN.H_zero_ne_zero_of_im_lt
#print axioms DBN.H_zero_ne_zero_of_one_lt_im
#print axioms DBN.H0_zero_strip
#print axioms DBN.H0_ne_zero
#print axioms dbn_H0_zero_strip

-- Route C / C3 groundwork, L4 (DBNStep): the vertical-shift average and the discrete de Bruijn
-- step against abstract even Hadamard data (pure Mathlib)
#print axioms DBN.differentiable_shiftAvg
#print axioms DBN.shiftAvg_neg
#print axioms DBN.shiftAvg_conj
#print axioms DBN.eq_zero_of_tendsto_prod_of_eq_zero
#print axioms DBN.prod_ne_zero_of_tendsto
#print axioms DBN.EvenHadamardData.even
#print axioms DBN.EvenHadamardData.eq_zero_of_factor
#print axioms DBN.EvenHadamardData.apply_inv_eq_zero
#print axioms DBN.EvenHadamardData.eq_const
#print axioms DBN.EvenHadamardData.tendsto_prod_conj
#print axioms DBN.EvenHadamardData.eq_zero_of_conj_factor
#print axioms DBN.EvenHadamardData.ofHasProd
#print axioms DBN.EvenHadamardData.ofMultipliable
#print axioms DBN.hadQ_nonneg
#print axioms DBN.hadQ_zero
#print axioms DBN.EvenHadamardData.tendsto_sq_norm
#print axioms DBN.sq_norm_sub_mul_norm_sub_conj
#print axioms DBN.pair_lt
#print axioms DBN.hadQ_eq
#print axioms DBN.hadQ_lt
#print axioms DBN.norm_sub_lt_norm_add
#print axioms DBN.max_sub_max_zero
#print axioms DBN.EvenHadamardData.norm_lt_norm
#print axioms DBN.EvenHadamardData.shiftAvg_zero_im_sq_le
#print axioms DBN.EvenHadamardData.shiftAvg_real_zeros
#print axioms DBN.zero_im_sq_le_of_shiftAvg_iterate

-- DBNStepControls: positive control (1 + z^2; hypotheses met, bound attained) and negative
-- control (z^2 - 2i; not real, conclusion of the step lemma fails)
#print axioms DBN.evenHadamardData_one_add_sq
#print axioms DBN.one_add_sq_conj
#print axioms DBN.one_add_sq_zero_im_sq_le
#print axioms DBN.shiftAvg_one_add_sq
#print axioms DBN.step_one_add_sq
#print axioms DBN.step_bound_attained
#print axioms DBN.evenHadamardData_sq_sub_two_I
#print axioms DBN.sq_sub_two_I_zero_im_sq_le
#print axioms DBN.shiftAvg_sq_sub_two_I
#print axioms DBN.step_needs_reality

-- Route C / C3 groundwork, L2e (DBNHurwitz): Hurwitz, maximum-modulus form (pure Mathlib)
#print axioms DBN.hurwitz_ne_zero
#print axioms DBN.hurwitz_ne_zero_of_entire

-- Route C / C3 groundwork, L2a-d (DBNHeatApprox): the de Bruijn approximants
#print axioms DBN.norm_cos_le_exp_abs_im
#print axioms DBN.norm_cos_mul_le
#print axioms DBN.one_add_sq_div_two_le_cosh
#print axioms DBN.cosh_pow_le_exp
#print axioms DBN.integrableOn_exp_mul_abs_Φ
#print axioms DBN.continuous_GδIntegrand
#print axioms DBN.norm_GδIntegrand_le
#print axioms DBN.integrableOn_GδIntegrand
#print axioms DBN.GδIntegrand_succ
#print axioms DBN.Gδ_succ
#print axioms DBN.Gδ_zero
#print axioms DBN.Gδ_eq_iterate
#print axioms DBN.differentiable_Gδ
#print axioms DBN.Gδ_neg
#print axioms DBN.Gδ_conj
#print axioms DBN.Gδ_ofReal_im
#print axioms DBN.norm_Gδ_le
#print axioms DBN.cosh_le_exp_abs
#print axioms DBN.mul_le_rpow_add_cube
#print axioms DBN.cube_add_le_exp
#print axioms DBN.norm_GδIntegrand_le_rpow
#print axioms DBN.norm_Gδ_le_exp_rpow
#print axioms DBN.norm_Gδ_le_exp_rpow_norm
#print axioms DBN.cosh_sqrt_pow_le
#print axioms DBN.one_add_div_pow_le_cosh_sqrt_pow
#print axioms DBN.tendsto_cosh_sqrt_pow
#print axioms DBN.continuous_approxErrIntegrand
#print axioms DBN.approxErrIntegrand_nonneg
#print axioms DBN.approxErrIntegrand_le
#print axioms DBN.integrableOn_approxErrIntegrand
#print axioms DBN.tendsto_approxErr
#print axioms DBN.norm_H_sub_G_le
#print axioms DBN.tendstoUniformlyOn_G
#print axioms DBN.tendstoLocallyUniformly_G
#print axioms DBN.norm_G_le
#print axioms DBN.Φ_term_pos
#print axioms DBN.Φ_pos
#print axioms DBN.setIntegral_weight_mul_Φ_pos
#print axioms DBN.H_zero_re_pos
#print axioms DBN.H_zero_ne_zero
#print axioms DBN.Gδ_zero_re_pos
#print axioms DBN.H_ne_zero_of_approx_on
#print axioms DBN.H_ne_zero_of_approx

-- Route C / C3 REDUCED (DBNDeBruijnReduction), CONDITIONAL on the named obligations
-- H0ZeroFreeOffStrip (L1) and ApproxHadamard (L3); they enter as hypotheses, so the expected
-- closure is still [propext, Classical.choice, Quot.sound].  NOT the registry node.
#print axioms DBN.Gδ_zero_delta
#print axioms DBN.G_zero_im_sq_le_of_obligations
#print axioms DBN.H_zero_im_sq_le_of_obligations
#print axioms DBN.H_ne_zero_of_obligations

-- Route C / C3 obligation L3, the Hadamard factorisation (telperion/docs/HADAMARD_PLAN_2026-09-23.md):
-- Mathlib-only pieces (Count/Product/Mean/Linear), the even factorisation theorem (DBNHadamard),
-- and its instantiation on the approximants plus de Bruijn's theorem (DBNHadamardApprox).
-- Everything unconditional; expected closure [propext, Classical.choice, Quot.sound].
-- Classical, NOT RH: nothing about zeros of H_0 inside the strip.  conjecture1_proved = False.
-- DBNHadamardCount
#print axioms DBN.analyticOrderAt_ne_top_of_entire
#print axioms DBN.divisor_eq_analyticOrderNatAt
#print axioms DBN.one_le_analyticOrderNatAt
#print axioms DBN.sum_ord_le_zeroCount
#print axioms DBN.zeroCount_le
#print axioms DBN.two_pow_dyadicIdx_le
#print axioms DBN.lt_two_pow_dyadicIdx_succ
#print axioms DBN.two_pow_rpow_neg_mul
#print axioms DBN.two_pow_rpow_neg
#print axioms DBN.dyadic_group_sum_le
#print axioms DBN.summable_zero_multiplicity_rpow
-- DBNHadamardProduct
#print axioms DBN.factor_eq_one_add
#print axioms DBN.factor_fun_eq
#print axioms DBN.norm_neg_factor
#print axioms DBN.summable_norm_neg_factor
#print axioms DBN.multipliable_factor
#print axioms DBN.differentiable_finset_prod_factor
#print axioms DBN.differentiable_tprod_factor
#print axioms DBN.tprod_factor_ne_zero
#print axioms DBN.hasProd_evenProduct
#print axioms DBN.differentiable_evenProduct
#print axioms DBN.evenProduct_zero
#print axioms DBN.evenProduct_neg
#print axioms DBN.log_one_add_le_rpow
#print axioms DBN.mul_sq_rpow_half
#print axioms DBN.norm_factor_le_exp
#print axioms DBN.norm_evenProduct_le
#print axioms DBN.eq_zero_of_hasProd_of_eq_zero
#print axioms DBN.evenProduct_eq_zero_iff
#print axioms DBN.evenProduct_ne_zero
#print axioms DBN.finite_setOf_factor_eq_zero
#print axioms DBN.analyticOrderAt_factor
#print axioms DBN.analyticOrderAt_finset_prod_factor
#print axioms DBN.evenProduct_eq_finset_prod_mul
#print axioms DBN.analyticOrderNatAt_evenProduct
-- DBNHadamardMean
#print axioms DBN.exists_exp_eq_of_ne_zero
#print axioms DBN.abs_eq_two_mul_max_sub
#print axioms DBN.posLog_exp_of_nonneg
#print axioms DBN.circleAverage_re_eq
#print axioms DBN.circleAverage_log_norm_nonneg
#print axioms DBN.circleAverage_posLog_norm_le
#print axioms DBN.circleAverage_abs_re_le
-- DBNHadamardLinear
#print axioms DBN.poissonKernel_zero_le
#print axioms DBN.poissonKernel_zero_nonneg
#print axioms DBN.poissonKernel_zero_le_three
#print axioms DBN.continuousOn_poissonKernel_zero
#print axioms DBN.abs_re_le_three_mul_circleAverage
#print axioms DBN.norm_le_of_re_le
#print axioms DBN.norm_deriv_le_of_forall_sphere
#print axioms DBN.norm_deriv_deriv_le
#print axioms DBN.eq_linear_of_circleAverage_abs_re_le
-- DBNHadamard
#print axioms DBN.analyticOrderAt_neg_of_even
#print axioms DBN.analyticOrderNatAt_neg_of_even
#print axioms DBN.even_analyticOrderNatAt_zero
#print axioms DBN.isRep_or_isRep_neg
#print axioms DBN.not_isRep_neg_of_isRep
#print axioms DBN.summable_zeroIdx_rpow
#print axioms DBN.countable_zeroIdx_of_summable
#print axioms DBN.repSeq_apply
#print axioms DBN.repSeq_of_notMem_range
#print axioms DBN.summable_repSeq_rpow
#print axioms DBN.ncard_factor_eq_analyticOrderNatAt
#print axioms DBN.exists_quotient
#print axioms DBN.evenHadamardData_of_order_lt_two
-- DBNHadamardApprox
#print axioms DBN.norm_Gδ_le_growth
#print axioms DBN.Gδ_exists_ne_zero
#print axioms DBN.approxHadamard
#print axioms DBN.H0ZeroFreeOffStrip_holds
#print axioms DBN.H_zero_im_sq_le
#print axioms DBN.H_ne_zero_of_half_le
#print axioms dbn_debruijn_real_zeros
-- lane m1: DBNM1Approx
#print axioms DBN.m1_continuous_WIntegrand
#print axioms DBN.m1_norm_HIntegrand_le
#print axioms DBN.m1_norm_WIntegrand
#print axioms DBN.m1_integrableOn_WIntegrand
#print axioms DBN.m1_WIntegrand_succ
#print axioms DBN.m1W_succ
#print axioms DBN.m1W_zero
#print axioms DBN.m1W_zero_base
#print axioms DBN.m1W_eq_iterate
#print axioms DBN.m1_differentiable_W
#print axioms DBN.m1W_neg
#print axioms DBN.m1W_conj
#print axioms DBN.m1_W_zero_re_pos
#print axioms DBN.m1_W_zero_ne_zero
#print axioms DBN.m1_mul_sq_le_exp
#print axioms DBN.m1_cube_add_le_exp
#print axioms DBN.m1_norm_WIntegrand_le_rpow
#print axioms DBN.m1_norm_W_le_exp_rpow
#print axioms DBN.m1_norm_W_le_exp_rpow_norm
#print axioms DBN.m1_norm_W_le_growth
#print axioms DBN.m1_evenHadamardData_W
#print axioms DBN.m1_continuous_ErrIntegrand
#print axioms DBN.m1_ErrIntegrand_nonneg
#print axioms DBN.m1_ErrIntegrand_le
#print axioms DBN.m1_integrableOn_ErrIntegrand
#print axioms DBN.m1_tendsto_Err
#print axioms DBN.m1_HIntegrand_sub_WIntegrand
#print axioms DBN.m1_norm_H_sub_G_le
#print axioms DBN.m1_tendstoUniformlyOn_G
#print axioms DBN.m1_tendstoLocallyUniformly_G
-- lane m1: DBNM1Parametric
#print axioms DBN.m1_G_zero_im_sq_le
#print axioms DBN.m1_H_zero_im_sq_le
#print axioms DBN.m1_H_zero_im_sq_le_of_le
#print axioms DBN.m1_H_real_zeros_of_le
#print axioms DBN.m1_H_real_zeros_of_im_sq_le
#print axioms DBN.m1_im_sq_le_of_upper_zero_free
#print axioms DBN.m1_real_zeros_of_upper_zero_free
#print axioms dbn_debruijn_parametric
#print axioms dbn_real_zeros_upset
-- lane m1: DBNM1RHIff
#print axioms dbn_rh_iff_real_zeros_nonneg_t
-- lane m1: DBNM1Controls
#print axioms m1_control_contraction_via_parametric
#print axioms m1_control_debruijn_via_parametric

-- lane m4 (Route C M4): DBNM4LocalStep
#print axioms DBN.m4_pair_lt_local
#print axioms DBN.m4_hadQ_lt_local
#print axioms DBN.EvenHadamardData.m4_norm_lt_norm_local
#print axioms DBN.EvenHadamardData.m4_shiftAvg_ne_zero_local
#print axioms DBN.m4_zero_abs_of_zero
#print axioms DBN.m4_barrier_induction
#print axioms DBN.m4_compact_margin
-- lane m4: DBNM4HeatUniform
#print axioms DBN.m4_continuous_H_uncurry
#print axioms DBN.m4_exp_sub_cosh_pow_le
#print axioms DBN.m4_integrableOn_approxIntegrand
#print axioms DBN.m4ApproxConst_nonneg
#print axioms DBN.m4_norm_H_sub_Gδ_le
-- lane m4: DBNM4P15Criterion (Polymath15 Prop 3.3; Thm 1.2 conclusion conditional on M1aStep)
#print axioms DBN.m4_H_real
#print axioms DBN.m4_im_le_sqrt_of_H_eq_zero
#print axioms DBN.m4_re_add_im_mul_I
#print axioms DBN.m4_im_add_im_mul_I
#print axioms DBN.m4_barrier_margin
#print axioms DBN.m4_rect_margin
#print axioms DBN.m4_lowered_curve
#print axioms DBN.m4_path_zero_free
#print axioms DBN.m4_inner_zero_free
#print axioms DBN.m4_p15_prop33
#print axioms DBN.m4_p15_prop33_abs_im_lt
#print axioms DBN.m4_p15_prop33_upper
#print axioms DBN.m4_p15_criterion_of_M1aStep
#print axioms DBN.m4_P15Barrier_of_box
#print axioms DBN.m4_p15_hyps_satisfiable
#print axioms DBN.m4_p15_control_instance
#print axioms m4_dbn_p15_prop33
#print axioms m4_dbn_p15_criterion_of_parametric
