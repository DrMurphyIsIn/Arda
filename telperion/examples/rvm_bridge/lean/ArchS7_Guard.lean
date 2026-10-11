import ArchS7_Term
import ArchS7_HS
import ArchS7_Abstract
import ArchS7_Concrete
import ArchS7_Dilation

/-! Axiom guard for stage S7 (CC Thm 4.7).  Every line must print
`[propext, Classical.choice, Quot.sound]`.  conjecture1_proved = False. -/

#print axioms ArchS7.integrand_eq
#print axioms ArchS7.integral_coeff
#print axioms ArchS7.cc84_coeff
#print axioms ArchS7.eps_eq_tsum
#print axioms ArchS7.eps_abs_eq_tsum
#print axioms ArchS7.hasSum_norm_inner_sq
#print axioms ArchS7.tsum_ofReal_norm_inner_sq
#print axioms ArchS7.tsum_norm_sq_swap
#print axioms ArchS7.hsSq_indep
#print axioms ArchS7.hsSq_adjoint
#print axioms ArchS7.ProlateBasis.hasSum_norm_hatP_P
#print axioms ArchS7.ProlateBasis.ofReal_norm_hatP_P
#print axioms ArchS7.ProlateBasis.tsum_PhatPP
#print axioms ArchS7.Scaling.inner_F_θ_F
#print axioms ArchS7.Scaling.norm_inner_le
#print axioms ArchS7.ProlateBasis.inner_ζ_θ_ξ
#print axioms ArchS7.ProlateBasis.τ_eq
#print axioms ArchS7.ProlateBasis.delta_term
#print axioms ArchS7.ProlateBasis.inner_ψ_θ_ψ
#print axioms ArchS7.ProlateBasis.inner_ξ_θ_η
#print axioms ArchS7.ProlateBasis.inner_η_θ_ξ
#print axioms ArchS7.ProlateBasis.cζ_neg
#print axioms ArchS7.ProlateBasis.abs_lam_le_abs_τ
#print axioms ArchS7.ProlateBasis.lam_sq_le_abs_τ
#print axioms ArchS7.ProlateBasis.norm_ξ_ζ_coeff
#print axioms ArchS7.ProlateBasis.norm_cζ_le
#print axioms ArchS7.ProlateBasis.summable_lam_sq
#print axioms ArchS7.ProlateBasis.summable_ε_terms
#print axioms ArchS7.ProlateBasis.summable_cζ_terms
#print axioms ArchS7.ProlateBasis.δS_eq
#print axioms ArchS7.ProlateBasis.δS_abs_eq
#print axioms ArchS7.ProlateBasis.continuous_εS
#print axioms ArchS7.ProlateBasis.norm_εS_le
#print axioms ArchS7.ProlateBasis.integrable_mul_εS
#print axioms ArchS7.ProlateBasis.integrable_mul_cζ
#print axioms ArchS7.ProlateBasis.integral_δS
#print axioms ArchS7.hasSum_of_tsum_ofReal
#print axioms ArchS7.ProlateBasis.thm47
#print axioms ArchS7.ProlateBasis.thm47_nonneg
#print axioms ArchS7.ae_ne_real
#print axioms ArchS7.ae_comp_mul
#print axioms ArchS7.cosTransR_neg
#print axioms ArchS7.phiR_neg
#print axioms ArchS7.phiR_abs
#print axioms ArchS7.c2_eq
#print axioms ArchS7.xi_ae
#print axioms ArchS7.zeta_ae
#print axioms ArchS7.inner_evenL2
#print axioms ArchS7.inner_dil
#print axioms ArchS7.εS_term
#print axioms ArchS7.εS_eq_eps
#print axioms ArchS7.integral_εS_eq_Eplus
#print axioms ArchS7.xiRep_conj
#print axioms ArchS7.hreal_of_pointwise
#print axioms ArchS7.thm47_concrete
#print axioms ArchS7.thm47_concrete_nonneg
#print axioms ArchS7.thF_congr
#print axioms ArchS7.memLp_comp_mul
#print axioms ArchS7.memLp_thF
#print axioms ArchS7.exp_half_sq
#print axioms ArchS7.integral_thF
#print axioms ArchS7.coeFn_thRaw
#print axioms ArchS7.inner_thRaw
#print axioms ArchS7.thL_apply
#print axioms ArchS7.coeFn_thL
#print axioms ArchS7.thL_add
#print axioms ArchS7.thL_zero
#print axioms ArchS7.thL_neg_thL
#print axioms ArchS7.inner_thL_left
#print axioms ArchS7.reflect_thL
#print axioms ArchS7.thL_mem_evenL2
#print axioms ArchS7.P1_thL_neg
#print axioms ArchS7.fourier_congr_ae
#print axioms ArchS7.fourier_thF
#print axioms ArchS7.integrable_thF
#print axioms ArchS7.fourier_thL
#print axioms ArchS7.fourier_thL_fourier
#print axioms ArchS7.norm_sq_eq_integral
#print axioms ArchS7.continuous_thF_apply
#print axioms ArchS7.continuous_thL_of_compact
#print axioms ArchS7.continuous_thL
#print axioms ArchS7.coe_thE
#print axioms ArchS7.scalingEven_θ
#print axioms ArchS7.isPointwise_scalingEven
#print axioms ArchS7.thm47_even
