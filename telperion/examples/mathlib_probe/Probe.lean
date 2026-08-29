/- Scoping probe: what analytic-zeta machinery exists in Mathlib v4.32.0?
   (info: <type> = present; error: unknown = missing). -/
import Mathlib
open scoped Real

-- Core zeta + completed zeta + functional equation
#check @riemannZeta
#check @completedRiemannZeta
#check @completedRiemannZeta₀
#check @completedRiemannZeta_one_sub          -- functional equation
#check @riemannZeta_one_sub
#check @differentiableAt_riemannZeta
-- Zeros
#check @riemannZeta_ne_zero_of_one_le_re      -- no zeros Re >= 1 (PNT input)
#check @riemannZeta_neg_two_mul_nat_add_one   -- trivial zeros
-- Special functions underlying zeta
#check @jacobiTheta
#check @hurwitzZeta
#check @hurwitzZetaEven
-- Prime-side machinery / PNT
#check @ArithmeticFunction.vonMangoldt
#check @Nat.primeCounting
#check @Chebyshevθ
#check @ChebyshevPsi
-- Laurent / residue at s=1, Stieltjes
#check @riemannZeta_residue_one
