/- PROBE 4: how does Mathlib v4.32.0 encode riemannZeta's pole at s=1?
   Need MeromorphicAt riemannZeta 1  (equiv: AnalyticAt (fun s => (s-1)*zeta s) 1). -/
import Mathlib
open Filter Topology Complex

-- completed zeta structure (entire zeta0, simple poles at 0,1):
#check @completedRiemannZeta₀
#check @completedRiemannZeta
#check @differentiable_completedZeta₀
#check @differentiable_completedRiemannZeta₀
#check @completedRiemannZeta_eq
#check @riemannZeta_def
#check @riemannZeta_one_ne_zero
#check @riemannZeta_residue_one

-- the simple-zero residue lemma A4 found (order-1 logDeriv residue):
#check @AnalyticAt.tendsto_mul_logDeriv_simple_zero

-- order-of-deriv lemmas A4 found:
#check @meromorphicOrderAt_deriv_eq_sub_one

-- Can we get zeta meromorphic at 1?  (definition: exists n, AnalyticAt (z-1)^n * zeta)
example : MeromorphicAt riemannZeta 1 := by
  apply?

-- reciprocal analytic at the pole (the 1/zeta simple-zero handle for the pole term)?
example : AnalyticAt ℂ (fun s => (riemannZeta s)⁻¹) 1 := by
  apply?
