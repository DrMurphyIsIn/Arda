# Phase-0 numeric de-risk of the E6Bridge6 Gaussian obligations (2026-09-21)

Script: `telperion/examples/rvm_bridge/phase0_gaussian_obligations.py` (`--quick` runs in 6 s, full in 23 s;
`--mode add|replace`, `--skip-b`).  Measures, never claims.  No Lean.  conjecture1_proved = False.

Vocabulary confirmed against Zeta23.Defs: `paperFT g z = int g(u) e^{i z u} du`, `gammaOf rho = (rho - 1/2)/i`,
so rho = beta + i t gives gamma = t + i(1/2 - beta) =: x + i y.  The quadruple rho, 1 - conj rho, conj rho, 1 - rho
maps to gamma, conj gamma, -conj gamma, -gamma (E6Bridge6 proves the first; the others follow the same way).
`gaussTest c lam z = (z-c)^2 exp(-2 lam (z-c)^2)`.  Pair {gamma, conj gamma} at w = x + i y contributes
`2 |w|^2 e^{2 lam (y^2 - x^2)} cos(2 arg w - 4 lam x y)`, i.e. `-2 y^2 e^{2 lam y^2}` at x = 0.  Even in y.

Data: first 2000 zeros (t <= 2515.29) plus 1200 zeros around height 10000 (t in [9485.8, 10507.9]) from
`flint.acb.zeta_zeros`, cross-checked against `mpmath.zetazero` at n = 1, 100, 2000, 10142 (max diff 1.8e-12).
All are on the line (|Re rho - 1/2| = 0 to working precision), so the unperturbed zero side is a sum of
nonnegative terms.  Off-line zeros are INJECTED: quadruple at (beta, t0), beta in {0.6, 0.55, 0.51, 0.501},
t0 in {50, 1000, 10000}.  Two modes: `replace` (drop the on-line zero nearest t0, insert the quadruple at t0;
default) and `add` (keep every on-line zero).  Multiplicity 1 throughout.

## A. O2 GaussianDominance

**Control (no injection).**  min over c in [t0-3, t0+3] step 0.01 and lam in {1..200} of Re zeroSide:
0 (t0=50), 5.0e-106 (t0=1000), 1.4e-102 (t0=10000).  Nonnegative as it must be.

**A.i / A.iii, c = t0 exactly.**  lam* = continuous crossover (first lam with S < 0, bisected); B(1) = on-line
background at lam = 1; x1 = distance from t0 to the nearest surviving on-line zero.  Models:
lam_paper = (1/(2y^2)) log(B(1)/(2y^2)) (lam-uniform background, the memo's prediction);
lam_nn1 = log(x1^2/(2y^2)) / (2 (x1^2 + y^2)) (pair term vs the single nearest on-line image).

| mode | t0 | x1 | B(1) | y=0.1: lam* / lam_paper / lam_nn1 | y=0.05 | y=0.01 | y=0.001 |
|---|---|---|---|---|---|---|---|
| replace | 50 | 1.995 | 1.4e-3 | 0.664 / n/a / 0.663 | 0.839 / n/a / 0.839 | 1.244 / 9698 / 1.244 | 1.822 / 3.3e6 / 1.822 |
| replace | 1000 | 1.172 | 0.136 | 1.625 / 95.7 / 1.528 | 2.106 / 660 / 2.039 | 3.239 / 3.3e4 / 3.213 | 4.895 / 5.6e6 / 4.889 |
| replace | 10000 | 0.652 | 0.435 | 3.624 / 154 / 3.514 | 5.226 / 893 / 5.197 | 9.014 / 3.8e4 / 9.013 | 14.43 / 6.1e6 / 14.43 |
| add | 50 | 0.226 | 0.048 | 7.68 / 43.3 / 7.68 | 21.67 / 451 / 21.67 | 54.09 / 2.7e4 / 54.09 | 99.21 / 5.0e6 / 99.21 |
| add | 1000 | 0.208 | 0.176 | 7.26 / 109 / 7.26 | 23.53 / 712 / 23.53 | 61.79 / 3.4e4 / 61.79 | 114.9 / 5.7e6 / 114.9 |
| add | 10000 | 0.065 | 0.439 | 3.85 / 154 / (pair wins all lam) | 6.96 / 895 / (same) | 350.2 / 3.8e4 / 350.2 | 897.5 / 6.1e6 / 897.5 |

(n/a: B(1) < 2y^2, S < 0 already at lam = 1.)  In every case S stays negative for all lam >= lam* on a
600-point log grid up to 1e6.  Smallest LISTED lam with S < 0 in replace mode: 1,1,2,2 (t0=50); 2,5,5,5
(1000); 5,10,10,20 (10000).  In add mode at t0 = 10000, y <= 0.01 needs lam beyond the list (350, 897).

Reading.  The crossover is NOT governed by the e^{2 lam y^2} growth of the pair term against a lam-uniform
background: at c = t0 the on-line background decays like sum_j x_j^2 e^{-2 lam x_j^2}, so the race is decided
by the nearest on-line gap x1 and lam* = lam_nn1 to 3-4 digits whenever y < x1 (the other zeros shift it by
< 3 %, always upward).  lam* grows like log(1/y^2)/(2 x1^2), logarithmic in 1/y, not 1/(2 y^2); the paper's
rule overestimates by 2 to 6 orders of magnitude.  When x1 < |y| the pair beats the nearest on-line image at
every lam >= 0 and lam* is set by the second neighbour.  Mechanism at beta = 0.51, t0 = 1000: lam=1 S = +1.36e-1
(bg 1.36e-1, pair -2.0e-4); lam=10 S = -2.0e-4 (bg 1.6e-12); lam=50 bg 2.7e-60.

**A.ii, c = t0 + delta, |delta| <= 3, step 0.01.**  Band := |delta| < |y| (pair exponent y^2 - delta^2 > 0).
- Sign changes along c grow linearly with lam (y = 0.1, t0 = 50: 2, 2, 6, 6, 8, 18, 36, 63 for lam = 1..200;
  y = 0.05: up to 33; y = 0.01: up to 9): the phase 4 lam x y, period pi/(2 lam |y|) in delta.
- The negative set is NOT confined to the band once lam >= 5: in replace mode at y = 0.1, lam = 10, 23 % of the
  6-unit window has S < 0 (band is 0.2 wide) because the hole left by the removed zero makes the background tiny
  and the pair term with its phase decides the sign out to the half-way points to the neighbours.  Inside the band
  the fraction with S < 0 falls from 0.90 (lam = 1) to 0.40-0.55 (lam >= 50) as the phase oscillates.
- For y = 0.001 the band is a single grid point; S < 0 only at c = t0 (fraction 0.002, 2 sign changes) for every
  lam >= 2 (t0=50), >= 5 (1000), >= 20 (10000).
- Genericity (A.ii-b, beta = 0.55).  Exponent race: the pair dominates at large lam iff y^2 - delta^2 > -x1(c)^2,
  x1(c) = nearest on-line gap to c.  Measured at lam = 200 and 500: 0 grid points violate the race in replace mode
  (1 point in add mode at t0 = 50 where the exponent gap is 6.3e-4, i.e. 2 lam gap < 1, not yet asymptotic).
  Inside the pair-dominated region S < 0 at lam = 200 or 500 for 65-76 % of c; the rest have cos > 0 there and
  flip at other lam.  Min exponent gap on the 0.01 grid: 7.8e-3 / 6.4e-3 (replace), 6.3e-4 / 8.8e-5 (add): the
  bad c (ties) form a finite set that the grid never hits.  This is the memo's "generic c" made visible.

**A.iv, truncation.**  Omitted on-line mass when keeping only |t - t0| <= X versus all cached zeros, against the
bound 2 (log(T/2pi)/(2pi) + 1) int_X^inf x^2 e^{-2 lam x^2} dx:

| t0, lam | X=1 omitted / bound | X=2 | X=3 |
|---|---|---|---|
| 1000, 1 | 1.4e-1 / 1.5e-1 | 8.1e-5 / 6.4e-4 | 5.7e-9 / 4.2e-8 |
| 10000, 1 | 9.7e-2 / 1.8e-1 | 1.6e-4 / 7.7e-4 | 6.0e-10 / 5.1e-8 |
| 10000, 5 | 2.4e-6 / 1.0e-5 | 0 / 1.9e-18 | 0 / 5.4e-40 |
| any, 20 | 0 / 2.3e-19 | 0 / 3.6e-71 | 0 / 7e-158 |

All 45 (t0, lam, X) cases: omitted <= bound.  N = 1000 vs N = 2000 zeros: bit-identical at t0 = 50 and 1000;
window +-100 vs +-600 zeros at t0 = 10000: identical.  X = 3 suffices to 1e-8 at lam = 1, X = 2 at lam >= 5.

**Recommended parameter rule for O2.**  c = t0 = Im rho_0 exactly (always inside the band, no genericity
needed there: the only tie would be an on-line zero at ordinate t0 with x1 = 0, where the on-line image is
0 and the pair still wins).  Then S(t0, lam) < 0 as soon as
    2 y^2 e^{2 lam y^2} > sum_{on-line j} x_j^2 e^{-2 lam x_j^2} + (images at -t: negligible, Gaussian in 2 t0),
which the numerics put at lam* = lam_nn1(y, x1) (1 + <0.03).  A safe explicit choice in all 24 cases:
lam >= 2 lam_nn1 and lam >= 1.  The prover should NOT aim for the memo's lam ~ (1/(2y^2)) log(...).

## B. O1' GaussianApprox constants

**K.**  phi(u) = K u e^{-u^2/(4 lam)} e^{-i c u} with K = -i / (4 sqrt(pi) lam^{3/2}) gives
paperFT phi = (z - c) e^{-lam (z-c)^2} (differentiate int e^{-u^2/(4 lam)} e^{i w u} du = sqrt(4 pi lam) e^{-lam w^2}
in w).  mpmath (30 digits) at 5 strip points, lam in {1,10}, c in {0,50}: max error 6e-29 (lam=1), 2.3e-12 (lam=10).

**Truncation.**  g_n = phi chi(u/n), chi the exp(-1/s) cutoff (1 on |u| <= n, 0 on |u| >= 2n).  h_n by the
trapezoid rule on [-2n, 2n], du = 0.004 (self-check at du/2: 2e-17).  Strip grid Re z in [-200, 200] step 0.5,
Im z in {-1/2, 0, 1/2}.  T_k := int |g_n^{(k)}| e^{|u|/2} du (k integrations by parts give |z|^k |h_n(z)| <= T_k
on the strip).  H_n = h_n(z) conj(h_n(conj z)).

| lam, c | n | sup(1+|z|)|h_n| | sup(1+|z|^2)|H_n| | sup(1+|z|^2)^2|H_n| | max|H_n - G| | T0 / T1 / T2 |
|---|---|---|---|---|---|---|
| 1, 0 | 1 / 4 / 8 / 64 | 0.60 / 1.21 / 1.21 / 1.21 | 0.20 / 0.75 / 0.75 / 0.75 | 1.33 / 1.42 / 1.41 / 1.41 | 4.8e-1 / 3.0e-3 / 5.8e-10 / 1e-12 | 1.54 / 1.40 / 1.59 |
| 1, 50 | 1 / 4 / 8 / 64 | 12.2 / 36.4 / 36.4 / 36.4 | 144 / 1276 / 1276 / 1276 | 3.8e5 / 3.3e6 / 3.3e6 / 3.3e6 | same as c=0 | 1.54 / 76.5 / 3800 |
| 10, 0 | 8 / 16 / 32 / 64 | 4.66 / 9.07 / 9.14 / 9.14 | 12.1 / 45.7 / 46.4 / 46.4 | 15.1 / 57.2 / 58.0 / 58.0 | 27 / 0.52 / 5.4e-9 / 9e-11 | 12.2 / 6.23 / 3.26 |
| 10, 50 | 8 / 16 / 32 / 64 | 158 / 309 / 311 / 311 | 2.4e4 / 9.2e4 / 9.3e4 / 9.3e4 | 6.0e7 / 2.3e8 / 2.3e8 / 2.3e8 | same as c=0 | 12.2 / 606 / 3.0e4 |

(The limit G itself has sup(1+|z|^2)|G| = 0.75, 1276, 46.4, 9.28e4 on the grid: the approximants never exceed it.)

Findings.
- C is uniform in n: every sup increases monotonically with n to the limit's own value and stays there.  On the
  grid sup(1+|z|^2)|H_n| <= 2 (T0^2 + T1^2) with 8-10x slack (9.3e4 vs 7.3e5; 1276 vs 1.2e4), and T_k(n) is
  bounded by its n = infinity value (int |phi'| e^{|u|/2} + sup|chi'| int |phi| e^{|u|/2}), which is finite.
- ONE integration by parts suffices for O1' as stated.  |z| |h_n(z)| <= T1 and |h_n| <= T0 give
  |H_n(z)| <= min(T0, T1/|z|)^2 <= 2 (T0^2 + T1^2) / (1 + |z|^2).  Two integrations by parts are needed only for
  the stronger C/(1+|z|^2)^2 in the O1 docstring, which O1' does not require.  Both constants are finite because
  g_n is Schwartz-times-cutoff; the e^{|u|/2} weight from |Im z| <= 1/2 is what makes T_k lam-dependent.
- Scaling.  For lam >= 2 the strip sup of the limit is exactly (1 + c^2 + 1/4) (1/4) e^{lam/2} (attained at
  z = c + i/2): (1 + c^2) from the weight, e^{lam/2} from |e^{-2 lam w^2}| at Im w = 1/2.  T1 scales the same way
  (76.5 -> 606 for lam 1 -> 10 at c = 50; 1.40 -> 6.23 at c = 0; the c-dependence of T1 is the factor c from
  differentiating e^{-icu}).  c does not affect the convergence rate at all (identical error columns).
- Convergence rate in n is NOT uniform in lam: the strip-edge error |H_n - G| is set by int_{|u|>n} |phi| e^{|u|/2} du
  ~ e^{-(n^2/(4 lam) - n/2)}, which only starts decaying once n > 2 lam.  lam = 1: 3e-3 at n = 4, 6e-10 at n = 8.
  lam = 10: error stuck at 37 (= |G| at the strip edge) through n = 8, 0.52 at n = 16, 5e-9 at n = 32.  The
  provers need n -> infinity only (Tannery), so this is harmless, but any "n = lam-independent constant" shortcut
  fails.

## What the numerics can NOT establish
- Anything about the true zero set: the off-line zeros are synthetic; the real ones (if any) are at unknown
  heights with unknown neighbours, so x1 is not a known constant and the rule is an existence statement
  (pair exponent y^2 > 0 >= -x_j^2 for every on-line j) whose numerical margin is what is measured here.
- The all-zeros quantifier and the infinite tail: only windows of the zero set enter; the tail bound in A.iv is
  checked against cached zeros, not proved against the Riemann-von Mangoldt count (the +1 in the density is a
  fudge, and the rigorous majorant is Zeta23.WeilEF.zero_sum_inv_sq, a different shape).
- Multiplicities: m = 1 assumed for injected and real zeros.
- Sup over the strip: the grid stops at |Re z| = 200 and Im z in {-1/2, 0, 1/2}; interior Im values and the
  far field are covered only by the T_k integration-by-parts bound, not measured.
- The finite-set claim for bad c (ties) is a statement about exponents of a finite window; the memo's "only zeros
  within ordinate distance 1 of gamma_0 can tie" is not tested beyond the +-3 window.
- Trapezoid quadrature and float64: verified by du-halving (2e-17) and by the K check, not by interval arithmetic.
