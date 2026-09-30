# EFW experiment + Davenport-Heilbronn horizon (2026-09-25)

conjecture1_proved = False.

## Lane efw

**Status.** DONE. conjecture1_proved = False. Two results.

(1) The exact form of (ii) behaves as conjectured, but only numerically, with no certificate. Here the exact form means: FE-consistency with some Ramanujan-bounded Euler completion, taken in the X -> infinity limit of the finite relaxation below, with a genuine pole. In that form, the feasible data for n < x (x <= 25) is pinned to zeta_K. So mu(x) = lambda_zeta_K(x) > 0 on [5, 25], and within that range there is no horizon.

(2) Every finite relaxation has adversaries, and the horizon depends on two knobs: X (how far the Euler completion is kept) and R0 (the floor on the pole residue). The negative witnesses are genuine, because Galerkin (Ritz) values are upper bounds. The positive values and the infeasibility claims are float evidence from a local optimizer. The linear FE constraints and the dps-60 control checks are high-precision. Nothing is interval-certified.

**Findings.**

A. What (ii) should mean, made precise and computable
- **As literally stated, (ii) is vacuous.** For tests supported in the window with the prime side truncated at x, the explicit formula only *defines* the zero-side distribution on band-limited tests, so any c(n) satisfies it. Moving the tests outside the window does not help: they still bring in the unknown zeros.
- **The zero-free global content is the functional equation on the Dirichlet coefficients a(n).** With Lambda(s) = 20^{s/2} Gamma_C(s) L(s) and Lambda(s) = Lambda(1-s), the FE (with polar part R/(s-1) - R/s) is equivalent to g(1/y) = y g(y), where g(y) = R + 2 sum a(n) e^{-2 pi n y/sqrt 20}. This is the Hecke/Fricke modular relation.
- **The finite relaxation P_x^{(X)}:**
  - Satake data at all p <= X is Euler-shaped and free (only the p < x part enters Q_x). Beyond X, only |a(n)| <= d(n) is assumed.
  - The requirement is |r_X(y_j)| <= T_X(y_j) at 60 nodes y_j in (0.12, 1), where T_X is a rigorous Ramanujan tail bound.
  - Every genuine completion lies in P_x^{(X)}, and the sets decrease monotonically in X. So mu_X(x) <= mu_true(x), and the X -> infinity limit is exactly "c restricted to n < x extends to an L-function in the class".
  - What the relaxation loses: the per-row constraint is relaxed to a 2-norm ball; float weights are capped at 1e12; the tail beyond X carries no Euler structure.
- **Justification.** The rigorous tail makes every relaxation *necessary*, never sufficient. Controls:
  - zeta_K (R=2), L_G = L(chi_-4)L(chi_5) (R=0) and E (R=1, and E = (zeta_K + L_G)/2 exactly) all satisfy the FE, with max_j |r|/T = 0.20 / 0.077 / 0.083 at dps 60 (X=30).
  - Random Euler data violates it by a factor of 1e20.

B. Choices forced by the local data (and a flaw in (i) as written)
- Condition (i) as literally written ("degree 2 with |alpha|=1 at every p") makes zeta_K infeasible, because at the ramified primes 2 and 5 it has alpha = (1, 0).
- I used the GL2 conductor bookkeeping instead, which gives discrete sets at the ramified primes:
  - at 2 (conductor exponent 2): alpha in {0, +-1};
  - at 5 (exponent 1): alpha in {+-1, +-5^{-1/2}}.
- At unramified primes, self-dual data is either t = cos(theta) in [-1, 1] with omega = +1, or the inert point {1, -1}.
- A continuous box at 2 and 5 was also tested. Any deviation from alpha = 1 is infeasible at X=30 (0.999 already gives min ||wz||^2 = 2.8e14).

C. Main numerical result: FE plus Euler is very rigid
- **Informative constraints.** The weighted FE constraint has about 0.27X informative singular values: 5 / 8 / 13 above sqrt(J) at X = 20 / 30 / 50.
- **Search.** At each (x, X): all single and double flips of the discrete data from zeta_K, 60 random discrete configurations, and least-squares feasibility followed by SLSQP.
- **Only two feasible branches exist at X >= 25:**
  - the zeta_K branch;
  - the L_G branch, which forces R ~ 0. Its largest admissible residue is R_max(X) ~ 0.3, 0.1, 1e-2, 1e-3, 3e-5, 1e-6, 1e-8, 1e-11 at X = 8, 10, 12, 15, 20, 25, 30, 50.
- **Pinning radius at zeta_K** (linearized half-width in t = cos theta_p, other parameters free):
  - X=30: p=3: 1.8e-5; p=7: 1.8e-4; p=11: 3.6e-3; p=13: 2.0e-2.
  - X=50: p=3 to 23 all pinned to <= 2.5e-4.
- **Nonlinear pinning is tighter still (X=30):** with p=23 forced to t=0.5, or p=17 or p=19 forced away from inert, the rest is infeasible (min ||wz||^2 = 12 to 5e6).
- **The LEB witness is killed.** The witness (alpha2=-1, alpha3=beta3=-1, alpha5=-1) has no FE-consistent completion: min ||wz||^2 = 8.4e20 at X=30, the same over 300 outer configurations.

D. Controls
- zeta_K is feasible and positive in every run.
- E is infeasible by (i) but feasible by (ii):
  - c_E(4) = 2 log 2 while c_E(2) = 0. This violates degree <= 1 at 2. (A degree-2 box at 2 would allow it, via {1, -1}.)
  - c_E(6) = 3.58 != 0, and c_E(9) = 6 log 3 > 2 log 3.
  - So E is excluded by (i) at n = 4 and 6, as expected, and not by (ii).
- The no-FE (LEB) baseline reproduces the barrier: mu = +0.209 (x=4.5), +0.020 (x=5), -0.167 (5.5), -0.356 (6), -1.22 (8), -5.14 (20).

E. New structural fact: the LEB worst case near x ~ 5 is a genuine L-function
- For x <= 5, the unconstrained LEB minimizer is exactly L_G data (alpha2=-1, theta3=pi, alpha5=+1) combined with zeta_K's pole kernel. The values agree to all digits (0.020409 at x=5).
- The pole kernel is indefinite, so a pole-free L-function's own Weil form is positive while "L_G + pole" goes negative:
  - L_G without the pole term: 4.1e-3 at x=5, 1.7e-7 at x=20, all positive;
  - L_G + pole crosses zero at x = 5.07476 (exact closed-form Galerkin, N=32).
- Because L_G really satisfies the FE, (ii) cannot remove it. Only a quantified pole can (see F).

F. Horizons x_EFW(X, R0), where R0 is the floor on the residue of Lambda at s=1 (N=16 Ritz; bisection width 0.016)
- X <= 20, R0 = 1e-6: about 5.07. The adversary is the L_G branch with residue at the floor (R = 1e-6 at X = 15, 20; about 1e-4 to 2e-6 at X <= 12), the same horizon as LEB. With R0 this small, (ii) changes nothing.
- X = 12, R0 = 0.01: x_EFW in [5.1875, 5.2031]. The worst datum is L_G deformed: t3 = -0.976, R = 0.01.
- X = 15 or 20, R0 = 0.01: a spurious branch B appears, with alpha2 = -1, alpha5 = +5^{-1/2} (Steinberg-type), t3 = -0.762, t7 = -0.042, R = 0.092.
  - X=20: x_EFW in [7.734, 7.750].
  - Exact Galerkin at x=8: -8.22e-3 / -8.56e-3 / -8.63e-3 at N = 16 / 32 / 48, so the negative value is a genuine witness.
  - Branch B dies at X = 25 (min ||wz||^2 = 1.01, marginal) and at X = 30 (2.3e4).
- R0 = 1, X >= 8: no horizon for x <= X. The weakest case is X=20, x=20: mu = 2.38e-3 against lambda_zeta_K = 5.01e-3, with an adversary that flips p = 17 and 19 to t ~ +1 and still stays positive.
- X >= 25, any R0 >= 1e-6: no horizon on [5, 25].
  - X=50: mu_50(x) = lambda_zeta_K(x) to a relative 1e-11, with the worst data within 1e-11 of zeta_K.
  - X=30: relative gap at most 5e-2 (x = 24, 25; the p=23 angle is loosely pinned).
- No feasible data with R < 0 exists at X = 30 or 50.

G. Suzuki arXiv:2606.09096 ("Weil's quadratic form via the screw function")
- Only the abstract was verified, via WebFetch. The full text was not read.
- His framework is linear in c: the screw function is the Weil distribution. It gives an operator realization of Q_x on [-a, a] with a -> infinity. The abstract mentions no Euler-product or FE-on-coefficients structure.
- Recommendation: phrase the objective of EFW in his operators, i.e. mu(x) = inf over admissible screw functions g_c. The constraint set P_x (Euler shape plus the Fricke modular relation on a(n)) is nonlinear in c and lies outside his framework, and his framework gives no handle on it.

**Numbers.**

lambda_zeta_K (N=16 Neumann, Ritz upper bound):
| x | lambda_zeta_K |
|---|---|
| 5 | 1.0816 |
| 6 | 0.9091 |
| 8 | 0.6627 |
| 10 | 0.3790 |
| 12 | 0.1676 |
| 14 | 7.549e-2 |
| 16 | 3.496e-2 |
| 18 | 1.385e-2 |
| 20 | 5.010e-3 |
| 22 | 1.875e-3 |
| 24 | 7.380e-4 |
| 25 | 4.606e-4 |

Checks on these values:
- Quadrature and closed-form Galerkin agree to about 1e-9.
- At x=20: N=32 gives 4.645e-3 and N=48 gives 4.587e-3 (lane B's converged value is 4.53e-3).
- 7.38017e-4 at x=24 matches the value lane B reproduced from the geometry angle.

mu_X(x), pole residue >= 1e-6:
- **X=50:** equal to lambda_zeta_K for all x in {5, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 25}, relative gap <= 3.5e-11.
- **X=30:** equal to lambda_zeta_K up to x=20 (relative gap <= 6e-5). At x=22 it is 1.847e-3; at 24, 7.00e-4; at 25, 4.37e-4 (relative gap <= 5.2e-2).
- **X=25:** at x=20 it is 4.975e-3; at 22, 1.762e-3; at 24, 7.17e-4; at 25, 4.35e-4.
- **X <= 20:** equal to the L_G + pole values (N=16): +0.0204 (x=5), -0.135 (6), -0.224 (8), -0.372 (10), -0.503 (12), -0.641 (14), -0.775 (16), -0.939 (18), -1.06 (20).

Pole residue floor R0 = 1:
- X=20: 5..10 same as lambda_zeta_K; 12: 0.1672; 14: 7.53e-2; 16: 3.46e-2; 18: 1.12e-2; 20: 2.38e-3.
- X=15: x=12 gives 0.1665; x=14 gives 7.14e-2.
- X=12: x=12 gives 0.1487.

Pole residue floor R0 = 0.01:
- X=20: 0.281 (x=5), 0.108 (6), 0.031 (7), -8.3e-3 (8), -5.4e-2 (10), -0.171 (20).
- X=15: -3.3e-2 at x=8.

No-FE (LEB) baseline: +0.209 (x=4.5), +0.020 (5), -0.167 (5.5), -0.356 (6), -0.737 (7), -1.22 (8), -1.88 (10), -3.05 (14), -5.14 (20).

Horizons:
- LEB (no (ii)): x_P in (5.0, 5.5).
- L_G + pole: 5.07476.
- X=12, R0=0.01: [5.1875, 5.2031].
- X=20, R0=0.01: [7.734, 7.750].
- X >= 25: none in [5, 25].

Worst datum at the X=20, R0=0.01 horizon, compared with zeta_K:
| p | worst datum | zeta_K |
|---|---|---|
| 2 | a(2) = -1 | a(2) = +1 |
| 3 | theta3 = 139.6 deg (a(3) = -1.52) | theta3 = 0 (a(3) = 2) |
| 5 | alpha5 = 0.447 | alpha5 = 1 |
| 7 | theta7 = 92.4 deg (a(7) = -0.085) | a(7) = 2 |
The worst datum has pole residue R = 0.092 (zeta_K: 2). Sup-distance in c(n), n < 8: 4.06.

Other quantities:
- FE informative singular values (> sqrt(J)): 4 at X=15, 5 at X=20, 6 at X=25, 8 at X=30, 11 at X=40, 13 at X=50.
- The LEB witness at x=6 has lambda = -0.338. Its FE-completion residual is 8.4e20, where feasibility requires <= 1.

**Precision.** **Float64 evidence:**
- all optimization (SLSQP, least_squares);
- lambda_min on 16-mode Neumann spans, both parity sectors, via the pur.py quadrature;
- the infeasibility claims. These are local-optimizer minima of ||wz||^2 over many starts, not a global certificate.

**Rayleigh-Ritz caveat.** Every lambda is an upper bound on the true lambda_min. So:
- the negative values are genuine witnesses at float level (L_G + pole, branch B at x = 8 and 10, the LEB baseline);
- the positive values, and hence "no horizon", are not certified. zeta_K drops about 10% from N=16 to N=48 at x=20.

**Exact Galerkin checks** (bcore closed-form Crux3 FWindow with custom c(n)):
- They agree with quadrature to 1e-9 for zeta_K and L_G at x = 5, 6, 12, 20, 24.
- N-convergence was checked at 16 / 32 / 48 for the key candidates.

**High precision (mpmath):**
- the FE constraint matrices and their SVD (dps 60 to 85);
- tail bounds;
- the zeta_K / L_G / E FE residuals (dps 50 to 60, per-row, genuinely feasible).

**Interval certification:** none.

**Known relaxations and gaps:**
- The 2-norm ball stands in for the per-row constraint.
- Weights are capped at 1e12, so the true pinning is tighter than computed.
- Components with weight >= 1e4 are treated as equalities in SLSQP, a restriction of order 1e-4 in constraint slack.
- Self-dual data only. Non-self-dual Satake data is NOT explored and is the main open loophole.
- The discrete search covers all single and double flips from zeta_K plus 60 random configurations per (x, X), not exhaustive enumeration.
- The ramified sets rely on GL2 local conductor theory. The continuous box was spot-checked only.
- Suzuki: abstract only.

**Interpretation.** Is (ii) strong enough to pin the data to zeta_K up to x, i.e. class P at finite scale? Numerically yes, provided (ii) is read as a genuine global FE on the Dirichlet coefficients with a Ramanujan-bounded Euler completion kept out to X ~ 2x, and the pole is quantified. At conductor 20 the FE, the Euler shape and a d(n) growth bound are extremely rigid. The Fricke relation g(1/y) = y g(y) gives about 0.27X usable constraints. Euler data up to X has only pi(X) + 1 unknowns. The two combine so that, at X = 50, every Satake angle at p <= 23 is locked to within 1e-4 of zeta_K's. Class P at finite scale looks true here.

But this makes EFW true for the wrong reason as a positivity mechanism:
- mu(x) = lambda_zeta_K(x) because the feasible set collapses to zeta_K. Positivity is inherited from zeta_K's own Weil positivity, which is GRH input for zeta_K, checked numerically.
- EFW at scale x reduces to "finite-scale uniqueness (a converse theorem) plus lambda_zeta_K(x) > 0". The claim that X(q) -> infinity is then equivalent to GRH for zeta_K on growing windows, so it is circular with respect to RH.
- The "near-null saturation slack" that the synthesis feared never shows up. The data simply cannot move.

Adversaries do survive when either knob is loosened:
1. **R0 too small** (a pole of arbitrarily small residue is indistinguishable from none). The pole-free automorphic L_G = L(chi_-4)L(chi_5), which has the same Gamma factor and conductor, survives. Paired with the indefinite pole kernel it is Weil-negative from x = 5.075.
   - This is essentially the whole LEB barrier near x ~ 5: the LEB minimizer at x <= 5 IS L_G + pole.
   - So with an unquantified pole, adding (ii) does NOT move the horizon: it stays at about 5.07 against LEB's 5.0 to 5.5.
   - (iii) must be stated with a residue floor. The admissible residue on the L_G branch decays like 10^{-0.35X}, so any fixed floor kills L_G once X is past about 10 to 25.
2. **X too small** (X <= 20 with R0 = 0.01). A spurious branch B (Steinberg-type at 5, R = 0.09) goes negative from x = 7.74. It is not a real L-function, and it dies by X = 25 to 30.

With R0 = 1 (zeta_K has 2), no adversary was found for x <= X for any X >= 8. The horizon therefore moves from about 5 (LEB) to beyond 25 (X >= 25), and beyond X itself for R0 = 1.

**Verdict.** EFW as a precise finite statement is supported numerically at conductor 20 for x <= 25, but only as a consequence of finite-scale uniqueness. It isolates no new positivity mechanism. The Hodge-index gap therefore moves entirely to "why is the unique survivor positive", which is RH for zeta_K itself.

**The honest open loophole** is non-self-dual Satake data, together with a certified (interval or exhaustive) version of the uniqueness claim. That is the obvious next step: rigidity at X=50 is a finite polynomial system in about 15 angles.

## Skeptic (efw): refuted=False

I rebuilt everything independently in /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/efw/efw_skeptic/ (sk.py plus t1..t15.py). The only thing shared with the lane is the Neumann-basis convention. My code covers:
- my own Kronecker symbol;
- zeta_K and E coefficients counted directly on the lattices x^2+5y^2 and 2x^2+2xy+3y^2;
- my own Euler-product recursion;
- my own theta residual and tail bound;
- a time-domain Weil form (arch kernel 1/sinh(t/2), constant log20 - 2logpi + psi(1/4) + psi(3/4), pole 2[(int f cosh)^2 - (int f sinh)^2]).

The core numbers and the verdict (rigidity leads to finite-scale uniqueness, which leads to inherited zeta_K positivity, so EFW gives no new positivity mechanism) survive. conjecture1_proved = False.

Two points are overstated and need fixing. Neither overturns the conclusions.

(1) One reported horizon only holds under the 2-norm ball relaxation. The report gives x_EFW(12, 0.01) in [5.1875, 5.2031] for P_x^{(X)}, which the report defines per-row. Its worst datum is 2:-1, 3:t=-0.9764, 5:+1, R=0.01. At X=12 the FE residual is affine in (s7, s11, R), so an LP over those is a global test. Scanning t3 over [-1, -0.9] (step 1e-4 near the optimum), the best achievable max_j |r|/T is 1.053 at t3 = -0.9764. That is > 1, so the datum is infeasible for the per-row constraint as defined. It is admitted only by the disclosed relaxation ||r/T||_2^2 <= J (radius sqrt(60), about 7.7 per row). The number describes the ball relaxation, not P_x^{(12)}.

(2) "The X -> infinity limit is exactly 'c extends to an L-function in the class'" is false as stated. The constraint is imposed at J = 60 fixed nodes y in (0.12, 1). As X -> infinity it becomes r(y_j) = 0 at 60 isolated points. r is analytic, and vanishing at finitely many points does not imply the full FE. It is exact only if J -> infinity as well. In practice this is probably harmless, since there are about 16 unknowns against 60 nodes at X = 50.

Other limits of my check:
- The report's float labelling (SLSQP multistart, Ritz upper bounds, nothing interval-certified) is accurate.
- The X >= 25 "no horizon" and the X = 50 pinning to 1e-11 are local-optimizer statements. I did not re-run global searches.
- The EQW = 1e4 equality treatment is a restriction, not a relaxation, so it could in principle hide adversaries on the positive side. This is disclosed.

Reproduced: All float64 unless stated. My code is independent of the lane's.

**FE soundness**
- Lambda(s) = 20^{s/2} Gamma_C(s) L(s) is equivalent to g(1/y) = y g(y), with g = R + 2 sum a(n) e^{-2 pi n y/sqrt20} and polar part R/(s-1) - R/s. I re-derived this.
- At dps 50, X = 60, y in [0.12, 1], max|r| is 8.5e-5 (ZK, R=2), 1.2e-5 (L_G, R=0) and 3.6e-5 (E, R=1). This is pure truncation. ZK with R=1.9 gives 0.088.
- Lattice counts equal the Euler products. E = (ZK + L_G)/2 exactly.
- The tail bound |a(n)| <= d(n) and the monotonicity in X are sound.
- The ramified sets {0, +-1} at 2 and {+-1, +-5^{-1/2}} at 5, and the self-dual unramified sets, agree with GL2 local theory. The per-prime central character is a superset, which is fine.
- True L_G and ZK truncated at X = 20/25/30 are per-row feasible: max|r|/T = 0.70/0.25/0.077 and 0.76/0.36/0.20.

**lambda_min (N=16 Neumann, both sectors)**

| x | ZK | L_G + pole | L_G, no pole |
|---|---|---|---|
| 5 | 1.081635 | 0.020409 | 4.1009e-3 |
| 8 | 0.662724 | -0.22356 | 4.53e-4 |
| 10 | 0.37900 | | |
| 14 | 7.5485e-2 | | |
| 20 | 5.00967e-3 | -1.0559 | 1.686e-7 |
| 22 | 1.8750e-3 | | |
| 24 | 7.3802e-4 | | |
| 25 | 4.6064e-4 | | |

- Every value matches the report.
- x=24, odd sector: 0.1865386, matching lane B's interval certificate.

**L_G + pole zero crossing**
- 5.082058 at N=16, and 5.074758 at N=32. The latter matches the report's 5.07476 (N=32).

**LEB box minimum**
- x=5: 0.020409, at exactly L_G data (a2 = -1, s3 = -2). This confirms finding E, though the minimizer is simply the extreme corner of the box.
- x=6: -0.355608, matching -0.356.

**Branch B (X=20, R0=0.01): confirmed genuinely per-row feasible**
- Datum: 2:-1, t3 = -0.7622, 5:+5^{-1/2}, t7 = -0.0423, R = 0.0919.
- A global LP over the free a(11), a(13), a(17), a(19) gives max_j |r|/T = 0.663 at the lane's nodes and 0.666 on a dense y grid, both <= 1.
- lambda at x=8: -8.216e-3 (N=16) and -8.560e-3 (N=32). At x=7.75: -3.76e-4 (N=16). Matches -8.22e-3 / -8.56e-3.

**L_G branch residue: nonlinear SLP in mp dps 80, uncapped per-row**
- X=15: R = 1e-4 feasible, 1e-3 not.
- X=20: 1e-6 feasible (0.13), 1e-5 feasible (0.43), 1e-4 not (8.8). This agrees with R_max(20) of about 3e-5, so the X=20, R0=1e-6 horizon of about 5.07 stands.
- X=25: R = 1e-6 infeasible (2.8).

**LEB witness at X=30**
- Per-row min max is 3.8e14 to 1.7e16 for R in {0, 1e-6, 0.01, 1, 2}. It is confirmed dead.

**X=12, R0=0.01 worst datum: NOT per-row feasible**
- The lambda values themselves reproduce: 3.13e-3 at x=5.1875 and -9.1e-5 at x=5.2031 (t3 = -0.976).
- But the best per-row value is 1.053 > 1, and ||r/T||^2 = 7333 at the rounded t3 = -0.976. It only enters under the ball relaxation.

**E coefficient claims**
- c_E(4) = 2 log 2, c_E(6) = 2 log 6 = 3.58, c_E(9) = 6 log 3. Checked by hand from the lattice counts.

Fixes: ["Relabel x_EFW(X=12, R0=0.01) in [5.1875, 5.2031] as a horizon of the 2-norm-ball relaxation (||r/T||^2 <= J), not of the per-row P_x^{(X)}. Its worst datum (t3=-0.9764, R=0.01) has a global per-row minimum max|r|/T of 1.053 > 1 (LP over s7, s11, R with 2, 3, 5 fixed; t3 scanned). The per-row horizon at X=12, R0=0.01 is somewhere above 5.19 and is not determined. Recompute every horizon and R_max with the per-row constraint (for example an LP/SLP in SVD coordinates at mp precision) and report both numbers.", "Change 'the X -> infinity limit is exactly \"c restricted to n<x extends to an L-function in the class\"' to: the X -> infinity limit enforces the FE only at J=60 fixed nodes in (0.12, 1). It is exact only if J -> infinity too, or if the full-FE equivalence is argued separately (r is analytic, so vanishing on a set with an accumulation point would suffice).", "State explicitly that the EQW=1e4 equality treatment is a restriction, not a relaxation, so the positive-side claims (no horizon at X>=25, mu_50 = lambda_zeta_K to 1e-11) could in principle be flattered by it. Re-run a few X=25/30 cases with the inequality constraint only.", "Say whether the reported L_G-branch R_max(X) values are ball or per-row. My per-row SLP gives feasible/infeasible pairs 1e-4/1e-3 at X=15, 1e-5/1e-4 at X=20, and R=1e-6 infeasible at X=25 (2.8). So R_max(25) of about 1e-6 is ball-relaxation only.", "Soften finding E slightly. At x<=5 the LEB minimizer is the extreme corner c(2)=-log2, c(3)=-2log3, c(4)=log2 of the box, and L_G happens to realize it. The observation is true (reproduced to 0.020409), but it is an extreme-point coincidence, not a structural discovery."]
## Lane dh

**Status.** RESOLVED. D's full-window horizon is x_D = 30.571 (±0.002; high-precision evidence, converged). Interval-certified upper bound: x_D <= 30.60. The binding sector is even; the odd sector crosses at about 31.24. The project's claim "D is Weil-positive to 31-35" is FALSE beyond 30.57 (at x=35, lambda_min = -4.9e-11). conjecture1_proved = False.

**Findings.**

1. Why wave-1 failed. lambda_min(Q_D, x) is a positive near-null floor that decays about like e^{-x}: 3.8e-13 at x=15, 3.5e-18 at 20, 1.2e-23 at 25, 5.1e-27 at 28, 1.1e-30 at 30.55. From x~20 on that is far below float64 resolution, so every float code saw noise. The horizon itself sits at the 1e-30 scale.

2. Horizon. The even sector crosses first, at x_D = 30.5714 (bracket [30.571, 30.572] with head N=120 and tail M=4000, i.e. 4120 Neumann modes, k <= 7567). The odd sector crosses at about 31.242 (+4.3e-27 at 31.20, -7.7e-28 at 31.25).

3. The Galerkin trap (new finding). The Neumann Ritz crossing does NOT converge at moderate basis sizes:

| N | even-sector crossing |
|---|---|
| 80 | 30.7444 |
| 120 | 30.6537 |
| 160 | 30.6363 |
| 200 | 30.6289 |
| 280 | 30.6125 |
| 360 | 30.5987 |

- The shift per 80 modes stays at about 0.014, and dps 80/90 reruns reproduce it exactly, so it is not a precision artifact.
- Cause: the minimizer's Neumann coefficients fall super-exponentially to about 3e-10 at m=20, then sit on a non-decaying plateau near 1e-16 out to m >= 350. At the 1e-30 energy scale that plateau is load-bearing.
- D's comb mass is A_L^D(30.6) = sum 2|c_D(n)|/sqrt n = 17.23. The naive symbol cutoff 2 pi e^{A_L}/5 is about 4e7, so high frequencies are not negligible a priori.
- Fix: a full Schur complement onto a high-precision head. S = Lambda - R^T T^{-1} R, where R = K V; the near-null columns are exact in mpmath and the tail T is in float64. By Haynsworth, when T > 0 the inertia equals inertia(T) + inertia(S).
- This reproduces direct Galerkin to 8 digits: 1.4906454e-30 (N+M=200) and -6.2169187e-32 (N+M=360) at x=30.6.
- With tail size it converges like M^-2: at x=30.6 the values are -9.59e-31 (M=600), -1.202e-30 (1200), -1.257e-30 (2000), -1.275e-30 (3000), extrapolating to about -1.29e-30.
- The tail block stays solidly positive definite: lambda_min(T) = 1.48 to 1.88, stable in M.

4. Witnesses, interval-certified with mpmath.iv (Lane B icore rigorous complex digamma/trigamma, enclosed beta-family tails, and c_D(n) by an interval recursion with kappa enclosed):

| x | modes (even, Neumann cos) | Q(v)/norm(v)^2 | width |
|---|---|---|---|
| 31 | 80 | -5.94132114396e-30 | 9e-58 |
| 30.63 | 200 | -5.21299311559e-32 | 9e-58 |
| 30.6 | 360 | -6.21691871795e-32 | 1.4e-47 |

- The witness is concentrated in the LOW modes (m=1: 63%, m=0: 31%, m=2: 6%), not near frequency 86.
- Rational coefficient vectors are saved as JSON (see report).

5. Zero-side cross-check (explicit formula; 204 on-line zeros below 299 plus the 4 off-line quadruples from Crux3 dh_zeros.json, with a density tail).
- Smooth 3-mode tests (f(+-A)=0) agree with the arithmetic side to 1e-12 at x = 20, 35 and 40.
- The x=31 witness: on-line +1.0152e-28, off-line -1.0833e-28 (the 0.8085+85.699i quadruple alone gives -1.0782e-28; 114.16 gives -5.3e-31), tail ~7e-31. The zero-side total is -6.08e-30 against the certified arithmetic value of -5.94e-30.
- So the sign is driven by the 85.7 quadruple, as expected.

6. Other consistency checks.
- Entries agree with Crux3 weilfreq.FWindow to 4e-40.
- kappa-certify D floors: we get 8.77e-5 at x=6.996 (certified lower bound 7.25e-5, Legendre 8.68e-5) and 7.97e-9 at x=11.006 (7.2e-9, 7.73e-9).
- Crux3 band test v=(-3,2): Rayleigh quotient -0.654576. Their -0.65462 is the band lambda_min, which is consistent.
- At x=40, N=120: even -0.0246, which matches kappa-certify Legendre -2.44e-2.

**Numbers.**

Setup:
- Completed function: Lambda_D = (5/pi)^{s/2} Gamma((s+1)/2) D(s). chi mod 5 is odd with chi(2)=i; root number 1; no pole.
- Arch side: log(5/pi) g(0) + (1/2pi) int |F|^2 Re psi(3/4 + ir/2).
- kappa = (sqrt(10-2sqrt5)-2)/(sqrt5-1) = 0.28407.
- c_D(n) from a(n) log n = sum_{d|n} c(d) a(n/d). c_D(4) = -1.442, c_D(6) = 1.936, and so on; nonzero off prime powers.
- Normalization: Q(f)/int|f|^2 on [-A, A], x = e^{2A}.

lambda_min table. Values are upper bounds (Ritz), dps 50-60. Galerkin N=120 values are listed for the whole range; Schur values (80+3000 modes) where computed.

| x | even, N=120 | even, Schur | odd, N=120 | odd, Schur |
|---|---|---|---|---|
| 15 | 3.95e-13 | 3.76e-13 | 1.08e-9 | 1.04e-9 |
| 18 | 4.35e-16 | | 1.11e-12 | |
| 20 | 3.92e-18 | 3.47e-18 | 1.33e-14 | 1.23e-14 |
| 22 | 2.80e-20 | | 1.32e-16 | |
| 25 | 1.42e-23 | 1.19e-23 | 1.12e-19 | 8.99e-20 |
| 28 | 6.51e-27 | 5.11e-27 | 7.85e-23 | 6.37e-23 |
| 30 | 9.64e-29 | | 6.46e-25 | |
| 30.3 | | 2.33e-29 | | |
| 30.4 | | 1.22e-29 | | |
| 30.45 | | 7.77e-30 | | |
| 30.5 | 9.85e-30 | 4.08e-30 | 2.81e-25 | |
| 30.55 | | 1.09e-30 | | |
| 30.571 | | +1.92e-32 (120+4000) | | |
| 30.572 | | -2.89e-32 (120+4000) | | |
| 30.6 | | -1.275e-30 | | |
| 31 | -7.35e-30 | | 5.51e-26 | |
| 31.2 | | | | +4.28e-27 |
| 31.25 | | | | -7.66e-28 |
| 31.3 | | | | -4.89e-27 |
| 32 | -3.93e-28 | | -1.77e-26 | |
| 33 | -1.95e-23 | | -6.42e-21 | |
| 35 | -3.13e-11 | -4.93e-11 | -8.07e-16 | |
| 37.5 | -4.71e-7 | | -7.30e-6 | |
| 40 | -2.46e-2 | | -6.06e-3 | |

Horizon brackets:
- Galerkin-only, even: 30.7444 (N=80), 30.6537 (120), 30.6363 (160), 30.6289 (200), 30.6125 (280), 30.5987 (360).
- Galerkin-only, odd: 31.4500 (N=80), 31.3306 (120), 31.3119 (160), 31.3034 (200).
- Schur-converged: even 30.5714, odd about 31.242.
- Exactly one negative eigenvalue per sector just above the horizon (kappa_D = 1 per sector).
- Slope dlambda/dx is about -4.7e-29 per unit x at the crossing.
- Remaining tail extrapolation (M^-2) moves x_D by about 3e-4.

**Precision.** - Interval-certified (mpmath.iv): the three negative Rayleigh quotients at x = 31, 30.63 and 30.60. Hence x_D <= 30.60 rigorously, modulo the same paper-level conditions as Lane B: the explicit formula for Lipschitz g = f*f~ (Neumann f jumps at +-A), and the identity of the closed forms with the Weil functional. The closed forms were independently checked here by the zero side to 1e-12.
- High precision (mpmath dps 50-90, not interval): every lambda_min and bisection. dps 60 vs 80 at N=120 give the same crossing to 1e-6, and dps 60 vs 90 at N=360 agree. Schur values at dps 50 and 70 agree to about 1e-33 absolute.
- The Schur tail block and the solve are float64. The error analysis puts the resulting error below 1e-40 on lambda, because only tiny y = T^{-1}R enters and the near-null columns of R are computed in mpmath.
- NOT certified: the positive side, i.e. that lambda_min > 0 below 30.571. All positive values are Ritz upper bounds. The lower end of the bracket is a convergence statement: M^-2 in the tail, stable across head N=80/120 and M=3000/4000.
- A Lane-B-style full-class lower bound is not feasible here. lambda is about 1e-30, and with A_L^D = 17.2 the pointwise symbol argument needs a cutoff near k ~ 4e7. The zero-side ledger is not rigorous either: it depends on D's zeros, D has infinitely many off-line zeros, and the tail is too coarse for 1e-30.
- Float64 is useless for D beyond x ~ 20. That confirms the wave-1 diagnosis.

**Interpretation.** - Numbers to quote:
  - "D is Weil-positive on the full window up to x_D = 30.57 (even sector; odd sector 31.24). Negativity is interval-certified at x = 30.60 (-6.2e-32 norm(v)^2), and more robustly at x=31 (-5.9e-30) and x = 35 (-4.9e-11, high precision)."
  - Drop "31-35". Anything above 30.6 is certifiably wrong.
- The old "~31" was never a computation. It was kappa-certify's heuristic sentence ("first detectable off-line pair needs x ~ 31") and happens to be close.
- Crux3's 42.1 answers a different question: the band-local horizon for height-local bands of at most 6 modes near 86. Full-window detection comes much earlier (30.57) because the minimizer is a delocalized low-frequency vector whose transform nearly vanishes at the on-line zeros but not at 85.699 ± 0.3085i.
- Comparison with E: x_E is about 19.82 (Lane B). E's lambda there is about 1e-4, while D's is about 1e-30 at its horizon. D is the "deep near-null" counterfeit.
- Consequence for Lane 1 of the synthesis: "resolve D at x in {28, 31, 35}" is done. D is positive (Ritz) at 28 and certified negative at 31; at 35 it is negative (-4.9e-11, high precision; not interval-checked).
- Methodological warning for the program: at 1e-30 scales, finite Neumann Galerkin (even N=360) overestimates the horizon by about 0.03, because a 1e-16 coefficient plateau in the minimizer carries 1e-30 energy. Any horizon claim below about 1e-20 needs a tail-converged (Schur) check.
- Nothing here bears on RH. D is a negative control.

## Skeptic (dh): refuted=False

The report's main claims survive an independent re-implementation. I rebuilt D from first principles and wrote a new Weil-form evaluator that works in u-space through Gauss's integral for digamma: g = f*f~ in closed form, then Gauss-Legendre quadrature. None of the lane's closed forms are used. This evaluator reproduces all three certified witnesses to 15 significant digits.

I also wrote a separate Galerkin and Schur code of my own. Its matrix entries are built from two closed-form functionals, S(k) = L[sin ku] and P(k) = L[(L-u)cos ku]. It reproduces the lane's Galerkin table, the Schur values, and the horizon bracket. Pushed further, it puts the crossing at about 30.571.

Nothing false or overstated affects the conclusions. There are two small inaccuracies:
1. "lambda_min decays about like e^{-x}" is wrong. Their own table gives about e^{-2.3x} to e^{-2.5x} (3.8e-13 at x=15, 3.5e-18 at 20, 1.2e-23 at 25).
2. The Schur tail does not converge like M^-2. Increments out to M=8000 fit about M^-1.6. The extrapolated limit is essentially unchanged (-1.294e-30 against their -1.29e-30), and the shift in x_D is still about 3e-4.

The positive side below 30.571 is still not certified, as the lane itself states. My agreement with their certified values is high precision (dps 50-70, quadrature converged), not interval arithmetic. conjecture1_proved = False.

Reproduced: Code is in /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/efw/dh_skeptic/: fe.py, qeval.py, dsk.py, and logs s1.log, s2.log, b1-b4.log.

(1) Functional equation, checked from first principles with mpmath.dirichlet:
- Lambda_D(s) = (5/pi)^{s/2} Gamma((s+1)/2) D(s) with kappa = 0.284079043840412 satisfies Lambda(s) = Lambda(1-s) to 15 digits at s = 0.3+2i, -0.7+11.5i and 0.1+40i.
- With Gamma(s/2) it fails, confirming that D is odd-type.
- Off-line zero: 0.808517182456637 + 85.699348485377592i (|D| = 8e-36). There is also a zero at 0.65083 + 114.16334i.
- c_D(4) = -1.44223 and c_D(6) = 1.93636, matching the report.

(2) Arithmetic side, derived independently:
- Q = (log(5/pi) - gamma) g(0) + 2 int_0^inf [e^{-2u} g(0) - e^{-3u/2} g(u)]/(1 - e^{-2u}) du - sum_{n<x} 2 c(n)/sqrt(n) g(log n).
- This comes from psi(z) = -gamma + int (e^{-t} - e^{-zt})/(1 - e^{-t}).
- Their arch term, log(5/pi) g(0) + (1/2pi) int |F|^2 Re psi(3/4 + ir/2), is correct.

(3) Witness Rayleigh quotients, my quadrature code (dps 50-70, GL degree 4 vs 5 agree):

| witness | my value | reported |
|---|---|---|
| x=31, N=80 | -5.94132114396268e-30 | -5.94132114396268e-30 |
| x=30.63, N=200 | -5.21299311559071e-32 | -5.21299311559071e-32 |
| x=30.6, N=360 | -6.21691871794898e-32 | -6.21691871794898e-32 |

So Q(v) < 0 at x=30.6, and x_D <= 30.60 holds. Independently this is high precision, not interval.

(4) My own Galerkin (N=80 or 120, as listed) matches their table:

| x | modes | my lambda_min |
|---|---|---|
| 15 | N=120 | 3.94526e-13 |
| 28 | N=80 | 7.70055e-27 |
| 30.5 | N=120 | 9.84539e-30 |
| 31 | N=80 | -5.94132e-30 |
| 40 | N=120 | -0.0246200 |

(5) My own Schur, head in mpmath and tail in float64:

| x | head + tail | Schur lambda_min |
|---|---|---|
| 28 | 80+3000 | 5.106e-27 |
| 30.55 | 80+3000, dps 60 | 1.0931e-30 |
| 35 | 80+3000 | -4.9295e-11 |
| 30.571 | 120+4000 | +1.920e-32 (matches theirs) |
| 30.571 | 120+8000 | +1.054e-32 (still positive) |
| 30.572 | 120+4000 | -2.887e-32 |
| 30.565 | 160+8000 | +3.04e-31 (consistent with the slope 4.7e-29 per unit x, so head size is stable) |

(6) Tail convergence at x=30.6 with an 80-mode head:

| M | lambda_min |
|---|---|
| 600 | -9.594e-31 |
| 1200 | -1.2022e-30 |
| 2000 | -1.2572e-30 |
| 3000 | -1.2751e-30 |
| 4000 | -1.2820e-30 |
| 6000 | -1.2875e-30 |
| 8000 | -1.2897e-30 |

The increments fit about M^-1.6, not M^-2. The limit is about -1.294e-30, so x_D is about 30.5711, inside the claimed ±0.002.

Not independently reproduced: the odd-sector crossing near 31.24, and the zero-side ledger.

Fixes: ["Replace 'lambda_min decays about like e^{-x}' with the measured rate: about e^{-2.3x} to e^{-2.5x} over x = 15..28 (3.8e-13 at 15, 3.5e-18 at 20, 1.2e-23 at 25).", "Replace 'converges like M^-2' with 'about M^-1.6 (fit on M = 3000..8000 at x=30.6: -1.2751, -1.2820, -1.2875, -1.2897 e-30)'. The limit is about -1.294e-30. At x=30.571, M=8000 still gives +1.05e-32, so the best estimate is x_D \u2248 30.5711.", "State explicitly that the 30.571 bracket is a Ritz/Schur statement. Negativity at 30.572 with 4120 modes is an upper-bound-type (non-interval) result. Positivity at 30.571 is extrapolation, not a bound.", "The x=35 value -4.93e-11 and the odd-sector 31.24 crossing are high precision only. Label them that way wherever the 30.60 interval certificate is quoted."]
## Independent peer-session confirmation (peterwmurphy-95, 2026-09-25; different session, same git identity -> "unverified" under #607)

DH horizon CONFIRMED, independently. Own code, arb balls at 256 bits, nothing imported from efw/.
- Setup: D = (1-i kappa)/2 L(chi) + (1+i kappa)/2 L(chi-bar), with Conrey character (5,2).
- Functional equation of Lambda_D: residual 6e-41 to 6e-38 at 5 points. Control: kappa -> -kappa fails at 1.12.
- Off-line zeros: 0.808517182456637 + 85.699348485377592i and 0.650830080609737 + 114.163342730757i.
- Explicit formula cross-checked against 61 zeros (argument principle gives 61.000000) to 5.6e-37 on Gaussian tests. Controls: dropping the quadruple gives 2.54; the wrong gamma factor gives 0.61.

Horizon, both sectors:
| sector / point | peer | ours |
|---|---|---|
| even, Galerkin crossing N = 512 | 30.585 | |
| even, Schur M = 2048 -> 4096 | 30.5725 -> 30.5719 | 30.571 +- 0.002 (stands) |
| odd | 31.243 | 31.242 |

RIGOROUS value at x = 30.60, even sector: an arb ball -6.906e-31 +- 1e-74. This is a stronger certificate than our -6.2e-32 vector.
Other values: x = 31 gives -8.02e-30; x = 35 gives -4.80e-11. Decay below the horizon is e^{-2.40x}.

EFW:
- The circularity argument is logically correct. But the pinning to zeta_K is float SLSQP evidence over self-dual data, with no certificate.
- The "surviving adversary" L(chi_-4)L(chi_5) + zeta_K's pole kernel is NOT the explicit formula of any L-function, because the pole kernel is indefinite. So its negativity only shows that a residue floor belongs in the constraint set.
- Its crossing is at 5.0726, with the odd sector binding (ours: 5.07476). L_G's own pole-free form stays positive (1.32e-7 at x = 20).

Caveats:
- Positive values are Ritz upper bounds only; there is no full-class certificate for "D positive below 30.571".
- Schur tail solves are float64.
- The explicit formula for Lipschitz tests is assumed (the same paper-level point as lane B).
