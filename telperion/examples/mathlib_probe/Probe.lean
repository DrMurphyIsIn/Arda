/- PROBE: discover the Mathlib v4.32.0 API for "residue of logDeriv = order".
   Needed for the boundary reproof zeta(1+it)!=0 via the Mertens bridge.
   Each #check is independent; unknown names log an error but do not abort the file. -/
import Mathlib
open Filter Topology

-- Order API (meromorphic + analytic):
#check @meromorphicOrderAt
#check @analyticOrderAt
#check @logDeriv

-- Candidate: analytic local factorization  f =ᶠ (·-z0)^n • g,  g z0 != 0.
#check @AnalyticAt.order_eq_nat_iff
#check @analyticOrderAt_eq_natCast
#check @AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff
#check @AnalyticAt.order

-- Candidate: meromorphic order / normal form / divisor.
#check @MeromorphicAt.order
#check @meromorphicOrderAt_eq_int_iff
#check @MeromorphicNFAt

-- Candidate: logDeriv algebra we will need regardless.
#check @logDeriv_mul
#check @logDeriv_pow
#check @logDeriv_fun_mul
#check @logDeriv_prod

-- Candidate: any direct logDeriv-order / residue lemma (guesses).
#check @meromorphicOrderAt_logDeriv
#check @MeromorphicAt.logDeriv
#check @logDeriv_tendsto

-- zeta pole handle we already know:
#check @riemannZeta_residue_one
#check @analyticOnNhd_riemannZeta
#check @analyticOn_riemannZeta
