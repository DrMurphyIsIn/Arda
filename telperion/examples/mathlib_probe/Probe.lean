/- PROBE 2: signatures needed to build  residue_logDeriv  (order = residue of logDeriv),
   and to pin the three orders for riemannZeta at 1, 1+it, 1+2it. -/
import Mathlib
open Filter Topology

-- is zeta globally meromorphic? and its order at the pole s=1?
#check @meromorphic_riemannZeta
#check @riemannZeta_residue_one
#check @MeromorphicOn
#check @MeromorphicAt

-- meromorphic <-> analytic order bridging (for the zero points where zeta is analytic):
#check @AnalyticAt.meromorphicAt
#check @analyticOrderAt_eq_zero_iff
#check @meromorphicOrderAt_eq_zero_iff
#check @AnalyticAt.meromorphicOrderAt_eq
#check @analyticOrderAt_pos_iff

-- order from a nonzero limit of (z-z0)^k f  (to get order(zeta,1) = -1 from residue):
#check @meromorphicOrderAt_eq_neg_one_iff
#check @meromorphicOrderAt_eq_int_iff
#check @MeromorphicAt.meromorphicOrderAt_eq

-- deriv/logDeriv of the shifted zpow  (z-z0)^n  and helpers:
#check @deriv_zpow
#check @logDeriv_zpow
#check @deriv_sub_const
#check @logDeriv_mul
#check @logDeriv_id'
#check @logDeriv_comp

-- more packaged-residue guesses:
#check @MeromorphicAt.tendsto_logDeriv
#check @meromorphicOrderAt_eq_of_tendsto
#check @logDeriv_sub

-- transfer deriv/logDeriv through eventual equality:
#check @Filter.EventuallyEq.logDeriv_eq
#check @Filter.EventuallyEq.deriv_eq
