/- Mathlib v4.32.0 API probe #2, focused on the zeta/Gamma-derivative-numerics
   contribution.  `#check @foo` types what exists, errors on what does not. -/
import Mathlib
open scoped Real

-- pi bounds: find the tight ones v4.32.0 actually has (only pi_gt_three confirmed so far)
#check @Real.pi_gt_three
#check @Real.pi_lt_four
#check @Real.pi_le_four
#check @Real.pi_gt_3141592
#check @Real.pi_lt_3141593

-- Euler-Mascheroni: constant exists; what bound/characterization API is there?
#check @Real.eulerMascheroniConstant
#check @Real.eulerMascheroniConstant_lt_two_thirds
#check @Real.eulerMascheroniConstant_gt_half
#check @Real.tendsto_harmonic_sub_log_atTop
#check @Real.harmonic

-- Gamma differentiability (digamma/deriv_Gamma are absent; what exists to build on?)
#check @Real.hasDerivAt_Gamma
#check @Real.differentiableAt_Gamma
#check @Complex.differentiableAt_Gamma
#check @Complex.hasDerivAt_Gamma
#check @Real.GammaSeq
#check @Real.Gamma_seq
#check @Real.tendsto_logGammaSeq
#check @Real.deriv_logGamma

-- log two bounds (confirm; needed for psi(1/2) = -gamma - 2 log 2)
#check @Real.log_two_lt_d9
#check @Real.log_two_gt_d9

-- completed zeta representation + theta (the convergent handle for zeta(1/2))
#check @completedRiemannZeta_eq
#check @completedRiemannZeta₀
#check @riemannZeta_def
#check @jacobiTheta
#check @completedRiemannZeta_one_sub
