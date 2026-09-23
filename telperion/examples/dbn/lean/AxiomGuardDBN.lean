/-
  AxiomGuardDBN -- CI axiom guard for the Route C (de Bruijn-Newman) foundations island.

  Run as `lake env lean AxiomGuardDBN.lean | tee axioms.out; ! grep -q sorryAx axioms.out`.
  Every theorem/lemma of DBNDefs gets a `#print axioms` line; the expected closure is
  `[propext, Classical.choice, Quot.sound]` (definitions like `thetaMoment`/`Φ`/`H` are
  noncomputable and are covered through the theorems that mention them).

  Scope reminder: NOTHING here is the representation theorem H_0 = ξ/8, de Bruijn's t ≥ 1/2
  theorem, or RH.  Those are registry STATEMENTS (RH.dbn_H0_eq_xi, RH.dbn_debruijn_real_zeros,
  RH.dbn_rh_iff_H0_real_zeros), not island theorems.  DBNRealZerosIff proves the C4 bridge
  RH <-> (all zeros of H_0 real) ONLY conditionally on C2 (explicit hypothesis / the named
  Prop obligation DBN.H0EqXi); the unconditional registry theorem dbn_rh_iff_H0_real_zeros is
  NOT stated anywhere on this island.  conjecture1_proved = False.

  Route C / C3 groundwork (the Hadamard-independent part of de Bruijn's t >= 1/2 theorem):
  DBNStep (L4, the discrete step against ABSTRACT even Hadamard data), DBNStepControls
  (kernel-checked positive/negative controls for the step lemma), DBNHurwitz (L2e),
  DBNHeatApprox (L2a-d: approximants, shift identity, locally uniform convergence, H t 0 > 0,
  Hurwitz transfer) and DBNDeBruijnReduction (C3 CONDITIONAL on the two named obligations
  H0ZeroFreeOffStrip (L1) and ApproxHadamard (L3), which are hypotheses, not axioms).  The
  registry node RH.dbn_debruijn_real_zeros is NOT stated anywhere on this island.
-/
import DBNDefs
import DBNRealZerosIff
import DBNStep
import DBNStepControls
import DBNHurwitz
import DBNHeatApprox
import DBNDeBruijnReduction

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
