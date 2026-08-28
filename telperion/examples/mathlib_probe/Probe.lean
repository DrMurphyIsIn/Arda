/- Mathlib v4.32.0 zeta/gamma-numerics API probe.
   `#check @foo` prints foo's type if it exists, else errors "unknown identifier".
   The CI log therefore maps exactly what is available for the deep-transcendental
   (zeta(1/2), derivative) formalization.  This file is EXPECTED to error on the
   names Mathlib lacks -- read the log, do not treat red as a regression. -/
import Mathlib
open scoped Real

-- zeta core
#check @riemannZeta
#check @completedRiemannZeta
#check @completedRiemannZeta₀
#check @riemannZeta_two
#check @riemannZeta_one_sub

-- possible COMPUTABLE handles for zeta at 1/2
#check @LSeries
#check @LSeries_riemannZeta
#check @riemannZeta_eq_tsum_one_div_nat_add_one_cpow
#check @hurwitzZeta
#check @hurwitzZetaEven
#check @riemannZeta_eq_hurwitzZeta

-- theta / integral representation (for a convergent rep at 1/2)
#check @jacobiTheta
#check @completedRiemannZeta_eq
#check @completedRiemannZeta₀_one_sub

-- gamma and DERIVATIVES
#check @Real.Gamma
#check @Real.Gamma_one_half_eq
#check @Real.deriv_Gamma
#check @Real.digamma
#check @digamma
#check @Real.hasDerivAt_Gamma

-- constants with numeric bounds (needed to bracket derivative values)
#check @Real.eulerMascheroniConstant
#check @Real.eulerMascheroniConstant_lt
#check @Real.log_two_lt_d9
#check @Real.log_two_gt_d9

-- pi bounds actually present in v4.32.0
#check @Real.pi_gt_314
#check @Real.pi_lt_315
#check @Real.pi_gt_3141592
#check @Real.pi_gt_three
