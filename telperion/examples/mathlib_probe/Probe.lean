/- Emitter-design probe: multiple-angle machinery + nlinarith SOS reach for nonneg cosine
   polynomials (the zero-free-region certificate family). -/
import Mathlib
open scoped Real

#check @Real.cos_two_mul
#check @Real.cos_three_mul
#check @Polynomial.Chebyshev.T_real_cos

-- degree-3 nonneg cosine poly  |1 + e^{iθ}|^2 * (1+cosθ) style: test explicit-SOS nlinarith.
-- P = (1+cosθ)(2+2cosθ)... use a real one: 2(1+cosθ)^2*(...). Try |1+e^{iθ}+e^{2iθ}|^2-derived.
-- Fejer kernel deg2: (1 + 2/3 cosθ...)... just test the tactic reach on a known SOS:
example (θ : ℝ) : 0 ≤ 6 + 8*Real.cos θ + 4*Real.cos (2*θ) + 2*Real.cos (3*θ) := by
  have h2 := Real.cos_two_mul θ
  have h3 := Real.cos_three_mul θ
  nlinarith [h2, h3, sq_nonneg (Real.cos θ + 1), sq_nonneg (2*(Real.cos θ)^2 + Real.cos θ - 1),
    Real.neg_one_le_cos θ, Real.cos_le_one θ, sq_nonneg (Real.cos θ - 1),
    mul_nonneg (sub_nonneg.mpr (Real.cos_le_one θ)) (sub_nonneg.mpr (Real.neg_one_le_cos θ))]
