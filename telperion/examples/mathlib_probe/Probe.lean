/- Weil-positivity feasibility: does Mathlib have the archimedean (digamma / Gamma'/Gamma)
   + prime-sum machinery whose bracketable values are the entries of the finite Weil form? -/
import Mathlib
open scoped Real

#check @Complex.Gamma          -- archimedean factor
#check @Real.Gamma
#check @Complex.deriv_Gamma     -- Gamma' (digamma numerator)  [guess]
#check @Real.digamma            -- Gamma'/Gamma  [guess]
#check @Complex.digamma
#check @ArithmeticFunction.vonMangoldt   -- prime side
#check @completedRiemannZeta_one_sub     -- functional equation (Weil symmetry)
#check @riemannZeta_residue_one
