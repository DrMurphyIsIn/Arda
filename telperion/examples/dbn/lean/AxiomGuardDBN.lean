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
  NOT stated anywhere on this island.  DBNStrip proves the registry node RH.dbn_H0_zero_strip
  (every zero of H_0 lies in the closed strip |Im z| <= 1) C2-FREE, from the absolutely
  convergent half-plane Re s > 1 only; it says nothing about zeros inside the strip and is not
  RH.  conjecture1_proved = False.
-/
import DBNDefs
import DBNRealZerosIff
import DBNStrip

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

-- Route C / C3 input (DBNStrip): the zero strip of H_0, C2-free.  L1b Gamma integral on the line
#print axioms DBN.integral_exp_smul_comp_exp
#print axioms DBN.ofReal_exp_cpow
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
