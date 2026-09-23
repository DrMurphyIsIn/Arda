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
