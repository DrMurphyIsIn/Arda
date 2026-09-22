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
-/
import DBNDefs
import DBNRealZerosIff

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
