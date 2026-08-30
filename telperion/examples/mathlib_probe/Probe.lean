/- PROBE 3: exact sigs (logDeriv_zpow/comp, deriv_zpow, AnalyticAt.meromorphicOrderAt_eq)
   + how Mathlib expresses riemannZeta meromorphy / the pole at s=1. -/
import Mathlib
open Filter Topology

set_option pp.fieldNotation false in
section sigs
#check @logDeriv_zpow
#check @logDeriv_comp
#check @deriv_zpow
#check @AnalyticAt.meromorphicOrderAt_eq
#check @EventuallyEq.deriv_eq
end sigs

-- How is zeta meromorphic at 1?  Try candidate names / provability.
#check @meromorphicOn_riemannZeta
#check @riemannZeta_meromorphicOn
#check @MeromorphicOn.riemannZeta

-- Can we get MeromorphicAt riemannZeta 1 at all?
example : MeromorphicAt riemannZeta 1 := by
  exact?

-- Is (s-1)*zeta analytic at 1 (removable) -- the residue as an analytic handle?
example : AnalyticAt ℂ (fun s => (s - 1) * riemannZeta s) 1 := by
  exact?
