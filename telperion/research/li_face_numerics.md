# Li face numerics (2026-09-21)

conjecture1_proved = False. Nothing in this document proves, or is meant to prove, anything about
the Riemann Hypothesis. Every number below is a float or a ball-arithmetic midpoint produced by
`telperion/research/li_face_numerics.py` (JSON of every number: scratchpad `li_face/li_face.json`;
runtime 4 to 11 minutes on 32 cores depending on load, no ranges were cut). The document checks the claims of
`docs/LI_FACE_BRIEF_2026-09-21.md` sections 2 to 4 and the Gaussian-face resonance claim.

Conventions. N = n + 1 with n the li-island rung index, so `taylorCoeff riemannXi n` is Li's
lambda_N. For a zero rho = beta + i gamma, w = rho/(rho - 1) = r e^{i theta} and the paired term is
Re P_N = 2 - (r^N + r^-N) cos(N theta) = 2 - 2 cosh(N log r) cos(N theta). The pair is symmetric
under beta -> 1 - beta and gamma -> -gamma, so beta in (0, 1/2], gamma > 0 is scanned.

## Summary

* lambda_N for N = 1..2000 from two independent routes agree to 11.8 digits at worst (N = 2000)
  and 13 digits for N <= 20; all 20 certified Lean lower bounds sit 1e-14 to 1e-11 below the
  computed values. lambda_N > 0 for every N computed.
* Theorem C (Re P_N >= 0 when gamma >= max(1, 2N/pi)) holds on every grid point tested, N up to
  2000. The true threshold is four times smaller: gamma_min(N) = N/(2 pi) + 1/2 + o(1), so
  gamma_min(N)/N -> 1/(2 pi) = 0.15915. The exchange rate could be n + 1 <= 2 pi (T - 1/2) instead of
  n + 1 <= pi T/2 if the lemma were sharpened to the window N theta in (3 pi/2, 2 pi).
* Box region: Re P_N >= 0 on the box for N = 1..5 (N = 5 attains exactly 1 at the corner
  (1/2, sqrt(3)/2)); N = 6 is negative, minimum -0.718 at (beta, gamma) = (0.300, 0.932) on the
  confinement boundary (equivalently (0.700, 0.932)). The brief's "(0.64, 0.9)" is the right
  neighbourhood but not the minimiser. N = 7, 8 are also negative.
* Lemma B holds on beta in (0,1), gamma >= 1 with slack, and |log r| <= |theta| holds for all
  gamma >= gamma* = 0.2855 (exact edge: arctan(1/g) = (1/2) log(1 + 1/g^2), reached as beta -> 0).
  The brief's "gamma >= 2/pi suffices" is true with room; on the box the minimum slack is 0.178.
* Gaussian face: at lam = 0.7 and 1.0 the largest prime-side value found on c in [0, 1e6] is 0.69
  of the l1 bound, and that is the coherent peak at c ~ 0.6-0.8. Away from it (c >= 100) the sup
  is 0.53 (lam = 0.7) and 0.36 (lam = 1.0) of the l1 bound, growing about 0.5-1 per decade of c.
  Reaching the l1 envelope needs 46 (lam = 0.7) or 126 (lam = 1.0) independent prime phases aligned,
  i.e. c of order 10^46 or 10^126 by Kronecker box counting.

## 1. Li coefficients lambda_N three ways

Route (b), the primary one: the Taylor series of log xi(1/(1 - z)) at z = 0 in ball arithmetic
(python-flint `acb_series`, 3400 bits, order 2000, 4 s). xi(s) = (1/2) s (s - 1) pi^{-s/2}
Gamma(s/2) zeta(s) is built with the deflated zeta series so s = 1 is regular. About 1.2 bits are
lost per order; at 3400 bits every radius is below the float64 range, and the imaginary parts are
exactly zero. mpmath `mp.taylor` (numerical differentiation, 60 dps) reproduces N <= 24 to all
float64 digits but costs 150 s at order 24 and is unusable at order 2000.

Route (a): the paired zero sum 2 sum_j (1 - cos(N theta_j)), theta_j = 2 arctan(1/(2 gamma_j)),
over the first M = 100000 zeros (flint `acb.zeta_zeros` at 64 bits, parallel chunks, 31 s; all
have real part exactly 1/2 in the ball; the first 1000 agree with mpmath `zetazero` to float64), plus
a smooth tail: the integral of the same weight against the density (1/2 pi) log(t/2 pi) dt from T*
where the smooth count N_smooth(T*) = M (T* = 74921.23). The scipy and mpmath quadratures of the
tail agree to 1e-16.

| N | lambda_N (series) | zero sum, M zeros | smooth tail | (a) total | rel diff | digits |
|---|---|---|---|---|---|---|
| 1 | 0.023095708966 | 0.02307365 | 0.000022 | 0.02309571 | 9.8e-14 | 13.0 |
| 2 | 0.092345735228 | 0.09225748 | 0.000088 | 0.09234574 | 9.8e-14 | 13.0 |
| 5 | 0.575542714461 | 0.57499112 | 0.000552 | 0.57554271 | 9.8e-14 | 13.0 |
| 10 | 2.279339363193 | 2.27713300 | 0.002206 | 2.27933936 | 9.9e-14 | 13.0 |
| 20 | 8.769276872093 | 8.76045142 | 0.008825 | 8.76927687 | 1.0e-13 | 13.0 |
| 50 | 43.531096488374 | 43.47593744 | 0.055159 | 43.53109649 | 1.3e-13 | 12.9 |
| 100 | 118.603775376791 | 118.38313919 | 0.220636 | 118.60377538 | 1.9e-13 | 12.7 |
| 200 | 306.655764851345 | 305.77322022 | 0.882545 | 306.65576485 | 3.0e-13 | 12.5 |
| 500 | 991.900092992245 | 986.38419441 | 5.515899 | 991.90009299 | 5.7e-13 | 12.2 |
| 1000 | 2326.053161686466 | 2303.98964400 | 22.063518 | 2326.05316169 | 9.7e-13 | 12.0 |
| 1500 | 3791.705972635218 | 3742.06334521 | 49.642627 | 3791.70597264 | 1.3e-12 | 11.9 |
| 2000 | 5351.759538381503 | 5263.50669374 | 88.252845 | 5351.75953839 | 1.7e-12 | 11.8 |

Agreement (a) vs (b): minimum 11.8 digits (N = 2000), median 12.0 over N = 1..2000. The tail is
1.65 percent of lambda_2000 and the smooth-density tail is accurate to about 1e-12 relative, which
means the fluctuation of the zero count above height 75000 contributes nothing visible at this
scale (the weight 4 sin^2(N theta/2) varies on the scale of t, not of the zero spacing).

Route (c), the certified lower bounds in `examples/li_positivity/lean/LiPositivity.lean` (hlo,
index n = N - 1): all 20 satisfy hlo <= lambda_N, with lambda_N - hlo between 2.1e-14 (n = 0) and
8.8e-12 (n = 15). The hlo values are the Arb enclosure lower ends truncated at 11 to 12 decimals;
the series values extend them to 300 digits if a tighter rung certificate is ever wanted.

| n | N | hlo | lambda_N (series) | lambda_N - hlo |
|---|---|---|---|---|
| 0 | 1 | 0.023095708966 | 0.02309570896612 | 2.1e-14 |
| 1 | 2 | 0.092345735228 | 0.09234573522805 | 4.7e-14 |
| 2 | 3 | 0.207638920554 | 0.20763892055432 | 3.3e-13 |
| 5 | 6 | 0.827566012282 | 0.82756601228238 | 3.8e-13 |
| 9 | 10 | 2.279339363190 | 2.27933936319316 | 3.2e-12 |
| 15 | 16 | 5.717108248860 | 5.71710824886879 | 8.8e-12 |
| 19 | 20 | 8.769276872090 | 8.76927687209322 | 3.2e-12 |

## 2. The termwise lemma and the sharp exchange rate

Theorem C region check. For every N = 1..2000, on gamma in [max(1, 2N/pi), max(1, 2N/pi) + 60]
(and up to 200 when that is larger) and 203 values of beta in (0, 1/2] including 1e-6, no grid
point has Re P_N < 0. The smallest value seen is 2.5e-5 (N = 1, beta = 1e-6, gamma = 200, where
Re P_1 ~ 1/gamma^2). Theorem C is consistent with everything computed.

Sharpness. gamma_min(N) := sup{gamma : some beta in (0,1) has Re P_N(beta, gamma) < 0}, found by a
0.01 scan downward from 2N/(3 pi) + 2 and bisection of the top edge on 2007 betas. Above N/(2 pi),
N theta < 2 pi for every beta, so a failure needs cos(N theta) > 0 with N theta in (3 pi/2, 2 pi)
and cosh(N log r) > 1/cos(N theta). That window is where all the failures live; between 2N/(3 pi)
and 2N/pi nothing fails (cos <= 0), and above 2N/pi Lemma A applies.

| N | gamma_min | gamma_min/N | 2N/pi | gamma_min / (2N/pi) | beta at the edge | gamma_min - N/(2 pi) |
|---|---|---|---|---|---|---|
| 1, 2, 3 | none for gamma >= 0.5 | | | | | |
| 4 | 0.607084 | 0.151771 | 2.546 | 0.2384 | 0.28 | -0.0295 |
| 5 | 0.809583 | 0.161917 | 3.183 | 0.2543 | 0.25 | 0.0138 |
| 6 | 1.004261 | 0.167377 | 3.820 | 0.2629 | 0.21 | 0.0493 |
| 10 | 1.752512 | 0.175251 | 6.366 | 0.2753 | 0.046 | 0.1610 |
| 12 | 2.117996 | 0.176500 | 7.639 | 0.2772 | -> 0 | 0.2081 |
| 20 | 3.498653 | 0.174933 | 12.732 | 0.2748 | -> 0 | 0.3156 |
| 50 | 8.382140 | 0.167643 | 31.831 | 0.2633 | -> 0 | 0.4244 |
| 100 | 16.377964 | 0.163780 | 63.662 | 0.2573 | -> 0 | 0.4625 |
| 200 | 32.312397 | 0.161562 | 127.324 | 0.2538 | -> 0 | 0.4814 |
| 500 | 80.070094 | 0.160140 | 318.310 | 0.2515 | -> 0 | 0.4926 |
| 1000 | 159.651266 | 0.159651 | 636.620 | 0.2508 | -> 0 | 0.4963 |
| 1500 | 239.229966 | 0.159487 | 954.930 | 0.2505 | -> 0 | 0.4976 |
| 2000 | 318.808050 | 0.159404 | 1273.240 | 0.2504 | -> 0 | 0.4982 |

The constant: gamma_min(N)/N decreases monotonically to 1/(2 pi) = 0.159155, and
gamma_min(N) - N/(2 pi) -> 1/2. Derivation of the limit from the beta -> 0 edge: there
|log r| = (1/2) log(1 + 1/gamma^2) and theta = arctan(1/gamma); near N theta = 2 pi the failure
condition cosh(a) cos(b) > 1 is |b - 2 pi| < |a| to leading order, i.e. N (theta + |log r|) > 2 pi,
i.e. N (1/gamma + 1/(2 gamma^2)) > 2 pi, whose top root is gamma = N/(2 pi) + 1/2 + O(1/N). The
ratio gamma_min/(2N/pi) is 0.2504 at N = 2000: Theorem C's exchange rate pi T/2 is exactly four
times conservative in the limit. For N <= 11 the edge is at an interior beta (0.2 to 0.3) because
the O(N |log r|) width of the window is not yet small; for N <= 3 there is no failure at any
gamma >= 0.5 (N = 1 never fails, matching the hypothesis-free rung 0; N = 2 cannot reach
N theta = 2 pi; N = 3 needs gamma < 0.29).

What a sharpened Lemma A would buy. If the termwise lemma were proved on the whole range
N theta < 2 pi - N |log r| rather than |b| <= pi/2, Theorem D would read n + 1 <= 2 pi (T - 1/2)
instead of n + 1 <= pi T/2: with T = 4000 that is rungs up to 25128 instead of 6282. The numerics
say the gap between the two is genuinely empty of counterexamples for every N tested.

First failing rung N*(beta, gamma), the smallest N <= 2000 with Re P_N < 0 (dash = none):

| beta / gamma | 0.9 | 1 | 1.5 | 2 | 3 | 5 | 10 | 14.13 | 20 | 50 | 100 | 200 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 0.5 | - | - | - | - | - | - | - | - | - | - | - | - |
| 0.49 | 25 | 27 | 39 | 64 | 19 | 63 | 377 | 444 | 377 | 1571 | 1885 | - |
| 0.45 | 6 | 7 | 10 | 13 | 19 | 63 | 63 | 89 | 126 | 314 | 1257 | - |
| 0.4 | 6 | 7 | 10 | 13 | 19 | 31 | 63 | 89 | 126 | 314 | 628 | 1257 |
| 0.3 | 6 | 7 | 9 | 12 | 18 | 31 | 62 | 88 | 125 | 313 | 628 | 1256 |
| 0.1 | 6 | 7 | 9 | 12 | 18 | 30 | 61 | 87 | 124 | 312 | 626 | 1255 |
| 0.001 | 6 | 7 | 9 | 12 | 18 | 30 | 61 | 86 | 123 | 312 | 626 | 1254 |

For beta away from 1/2 the first failing rung is N* ~ 2 pi gamma - O(1) (the first time N theta
reaches the window below 2 pi); for beta near 1/2 the window is so narrow that the first hit can be
at a higher multiple of 2 pi (hence the non-monotone row at beta = 0.49). This is the "no clean
N*(beta, gamma)" of brief section 6 made concrete: N* is determined by which multiple of 2 pi the
angle first lands near, not by a smooth function of (beta, gamma).

## 3. The low-height box

Region: gamma >= sqrt(3)/2 and (beta - 1/2)^2 <= gamma^2/3 - 1/4. Grid 4001 x 12001 in
(beta, gamma) on gamma up to max(1, 2N/pi) + 1 (Theorem C covers beyond), then Nelder-Mead
refinement with the constraint.

| N | min Re P_N | beta* | gamma* | where |
|---|---|---|---|---|
| 1 | > 0 | | | no interior min; Re P_1 = 1/|rho(1-rho)|^2 * (beta(1-beta) + gamma^2) > 0, inf 0 as gamma -> inf |
| 2 | > 0 | | | same, decreasing in gamma like N^2/gamma^2 |
| 3 | > 0 | | | same |
| 4 | > 0 | | | same; max of cosh(a) cos(b) on the box is 0.286 |
| 5 | 1.000000 | 0.5 | 0.866025 | corner of the box (a = 0, b = 5 pi/3, cos b = 1/2 exactly) |
| 6 | -0.718318 | 0.300419 | 0.932469 | confinement boundary; mirror image (0.699581, 0.932469) |
| 7 | -2.914196 | 0.186914 | 1.021797 | confinement boundary |
| 8 | -5.421343 | 0.095533 | 1.113904 | confinement boundary |

Verdict on brief section 4: N = 1..5 nonnegative on the box, N = 6 negative, confirmed. Two
corrections of detail. (i) The N = 6 minimiser is (0.30, 0.93) or its mirror (0.70, 0.93), not
(0.64, 0.9); the brief's point is inside the negative set but not its bottom. (ii) The brief's
"cosh(a) cos(b) <= 0.5 there" for N <= 5 is exactly attained: for N = 5 the maximum over the box is
0.4984 on the grid and 1/2 at the corner (beta, gamma) = (1/2, sqrt(3)/2) where a = 0 and
b = 5 pi/3, so the honest statement is "<= 1/2 with equality at the corner", giving
Re P_5 >= 1 on the box. For N = 4 the maximum is 0.286.

## 4. Lemma B

On the grid beta in (0,1) (4011 points down to 1e-9 from each end), gamma in [1, 1e6] (14001
points): min(|theta| - |log r|) = 1.0e-6 (at beta -> 1, gamma = 1e6, where both are ~ 1/gamma and
1/(2 gamma^2)), min(1/gamma - |theta|) = 8e-20 (at gamma = 1e6, arctan x <= x). The brief's
intermediate bound |log r| <= (1/2)|2 beta - 1|/(min(beta, 1-beta)^2 + gamma^2) holds (min slack
-1.6e-16, rounding), and |theta| >= pi/(4 gamma) for gamma >= 1 holds (min slack 5e-10 at gamma = 1,
beta -> 0).

Smallest gamma where |log r| <= |theta| can fail. Both |log r| (maximal) and |theta| (minimal) are
worst as beta -> 0, so the edge is the beta -> 0 equation arctan(1/g) = (1/2) log(1 + 1/g^2):
gamma* = 0.285498997. A 2D scan confirms: gamma = 0.2798 fails (min over beta = -0.013, at
beta -> 0), gamma = 0.2912 holds (+0.013). So |log r| <= |theta| holds for every zero with
|gamma| >= 0.2855, comfortably below 2/pi = 0.6366 (the brief's stated sufficient value),
sqrt(3)/2 = 0.8660 (Box 1) and 1 (Theorem C's hypothesis). On the box itself the minimum of
|theta| - |log r| is 0.178, and the brief's (1 - beta)/gamma <= 0.91 for gamma < 1 on the box is
loose: the actual maximum is 0.789.

## 5. Sanity

lambda_N >= 0 for all N = 1..2000 (minimum lambda_1 = 0.0231). The ratio
lambda_N / (N log N / 2) has minimum 0.126 at N = 3 and rises to 0.704 at N = 2000; it tends to
1 from below because the Bombieri-Lagarias asymptotic is lambda_N ~ (N/2)(log N - log(2 pi)
+ gamma_E - 1) + o(N): at N = 2000 that main term is 5340.2 vs lambda_2000 = 5351.8.

## 6. Gaussian face resonance at fixed width

prime(c, lam)/A = 2 sum_n Lambda(n) n^{-1/2} cos(c log n) f0(log n)/A as in
`examples/rvm_bridge/fixed_width_band.py` (its `Sweeper` reused; prime powers to 2e7; terms cut
where the tail bound is 1e-3). Sweep c in [0, 1e6] at step 0.1, the top candidates refined at step
0.00025. The l1 bound S_l1 = 2 sum Lambda n^{-1/2} |f0(log n)|/A over all prime powers (tail
bound included) is the envelope Kronecker's theorem makes attainable in the limit.

| lam | S_l1 | P(0) (signed coherent sum) | sup on [0, 1e6] (at c) | sup / S_l1 | sup on [100, 1e6] (at c) | ratio |
|---|---|---|---|---|---|---|
| 0.7 | 13.7785 | -10.680 | 9.4621 (c = 0.756) | 0.687 | 7.336 (c = 605023.94) | 0.532 |
| 1.0 | 23.7185 | -19.172 | 16.3436 (c = 0.614) | 0.689 | 8.499 (c = 605023.93) | 0.358 |

Per-decade sup of prime/A (lam = 0.7; lam = 1.0): [10,100): 2.73; 2.74. [100,1e3): 4.35; 4.85.
[1e3,1e4): 5.74; 6.28. [1e4,1e5): 6.17; 7.75. [1e5,1e6): 7.28; 8.45. The running sup grows by
roughly 0.5 to 1.5 per decade of c, as expected of the maximum of a quasi-periodic sum with many
incommensurable frequencies (the largest value found in [100, 1e6] sits at the same c ~ 605024 for
both widths, a resonance of the low primes). Ninety percent of the l1 mass sits on 57 (lam = 0.7)
or 142 (lam = 1.0) prime powers, of which 46 or 126 are primes with Q-linearly independent
frequencies log p. Aligning k independent phases to within a tenth of a turn needs c of order 10^k,
so the envelope S_l1 is approached only at c ~ 10^46 (lam = 0.7) or 10^126 (lam = 1.0). The
claim that the envelope is essentially attainable only at astronomically large c is supported;
within any computable range the prime side stays at 35 to 55 percent of its l1 bound away from the
coherent peak near c = 0, and at 69 percent including it. These values agree with the earlier
`fixed_width_band.py` sweep (sup 9.462 and 16.344 at the same c).

## Method notes and caveats

* Nothing here is interval-certified except the flint ball values for lambda_N, which are
  reported as midpoints; the zero sum, tail, grids and optimisers are float64.
* Grids can miss a failure between grid points; the gamma_min(N) top edges are bisected to 1e-12
  in gamma but only on 2007 beta values, and beta -> 0 is represented by 1e-9. The asymptotic
  formula gamma_min = N/(2 pi) + 1/2 + o(1) is derived, not proved.
* The box-region minima for N = 6..8 are on the confinement boundary, so they are sensitive to the
  exact constant in Box 2; a tighter box would move them.
* The M = 100000 zeros are cached in the scratchpad (`li_face/zeros_100000.json`, 31 s to regenerate
  on 24 processes).
