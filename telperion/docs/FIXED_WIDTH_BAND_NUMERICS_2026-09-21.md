# Fixed-width band closure from the prime side: feasibility numerics (2026-09-21)

Script: `telperion/examples/rvm_bridge/fixed_width_band.py` (`--quick` 19 s, full 105 s; json in the wall scratch dir).
Float numerics, no intervals, no Lean.  Real zeros from flint where used.  conjecture1_proved = False.

## Object

At fixed lam, F(c, lam) = arch(c, lam) - prime(c, lam), everything divided by A = f(0) = 1/(8 sqrt(2pi) lam^{3/2}):
prime/A = 2 sum_n Lambda(n) n^{-1/2} cos(c log n) (1 - log^2 n/4lam) e^{-log^2 n/8lam}, a trigonometric polynomial in c;
arch/A = 2 Re G(i/2)/A + (1/2pi A) int G Re digamma(1/4 + ir/2) dr - log pi = log(c/2pi) + o(1) (verified in
WALL_LANDSCAPE: the two sides agree to 1e-15).  Ladder: T = 640000, D = 2; the band is [T - D, c_triv(lam)] where
c_triv is the height at which the archimedean floor exceeds the trivial sup bound of the prime side.

## 1. N_eff, trivial bound, floor, c_triv

| lam | log N(1e-6) | N_eff (prime powers) | S_triv = sum 2 Lambda n^{-1/2} |f0|/A | L (Lipschitz of prime/A) | c_triv |
|---|---|---|---|---|---|
| 0.3 | 7.29 | 260 | 4.603 | 10.3 | 627 |
| 0.5 | 9.68 | 1920 | 8.737 | 25.4 | 3.92e4 |
| 0.7 | 11.72 | 11669 | 13.779 | 48.8 | 6.05e6 |
| 1 | 14.09 | 101695 | 23.718 | 104.8 | 1.26e11 |
| 1.5 | 17.88 | > 1.27e6 (nmax 2e7) | 48.925 | 282 | 1.11e22 |
| 2 | 21.39 | > 1.27e6 (nmax 2e7) | 89.632 | 630 | 5.31e39 |

Archimedean floor arch/A (identical to 4 digits for every lam in the list: digamma is flat across the window):
c = 1e3: 5.070, 1e4: 7.372, 1e5: 9.675, 6.4e5: 11.531, 1e6: 11.978, 1e7: 14.280, 1e8: 16.583, 1e9: 18.885, 1e12: 25.793.
So c_triv(lam) = 2pi e^{S_triv(lam)} to leading order, and S_triv grows like e^{lam/2} sqrt(lam): the envelope is
doubly exponential in lam, as the wall map says.  The two widths lam = 0.3, 0.5 have c_triv BELOW T: at those widths
the trivial bound alone closes everything above the ladder and the residual band is EMPTY.  (Caveat: the ladder itself
needs lam >= lamThreshold ~ 0.27 at D = 2 per WALL_LANDSCAPE, so lam = 0.3 sits at its edge.)

## 2. Actual sup of prime/A and min of F/A (dense sweep, h = 0.02 or 0.1, N truncated at relative tail 1e-3, refined)

Global sup over [0, min(c_triv, 1e7)] is always attained at c ~ 0.6-1.2 where all cosines align: 3.18 (lam 0.3),
5.97 (0.5), 9.46 (0.7), 16.34 (1.0), i.e. 0.68-0.69 of S_triv in every case; it is never exceeded later (running sup
flat from X = 1e3 to 1e7).  That region is ladder territory.  What matters is the band:

| lam | band | points | sup prime/A on band (at c) | min F/A on band (at c) | margin after tail |
|---|---|---|---|---|---|
| 0.3 | empty (c_triv 627 < T) | - | - | - | - |
| 0.5 | empty (c_triv 3.9e4 < T) | - | - | - | - |
| 0.7 | [6.4e5, 6.05e6] = ALL of it | 5.4e7 | 7.20 (6.043e6) | 5.043 (656811.62) | 5.042 |
| 1.0 | [6.4e5, 1e7] of [6.4e5, 1.26e11] | 9.4e7 | 9.59 (7.198e6) | 3.494 (935450.83) | 3.493 |

Band sup grows slowly with range at lam = 1: 8.35 over [T-D, 1e6], 9.59 over [T-D, 1e7]; floor 11.5 -> 14.3 over the
same range, so the margin (floor - sup) actually widens with c.  Extrapolating +1.2 per decade the sup would reach ~14.5
at 1e11 against a floor 23.7: positivity almost certainly holds on the whole lam = 1 band, but that is not a certificate.
Below the band (ladder territory) the fixed-width margin is NOT uniform: min F/A on [200, T-D] is 1.20 (lam 0.3), 0.51
(0.5), 0.19 (0.7), 0.038 (1.0), all at c ~ 250-330, and on [14, 200] it is 0 to float precision at the isolated low
zeros (c = t_j, F ~ 0).  A pure prime-side "all c" certificate at fixed lam is impossible below c ~ 1e3; the ladder
must cover that part, which it does.

Zero-side check (task 3): F from flint zeros (window +-25) vs arch - prime at c = 639998, 640000.5, 640250.25, 640999,
1e6, 1e6 + 0.5, 1e6 + 123.4 and lam in {0.3, 0.5, 1}: F/A = 11.4-15.5, relative agreement 1e-8 to 3e-6 (limited by the
sweep's 1e-3 truncation of the prime sum, not by the zeros).  The prime-side values in the band are real.

Rigorous certificate cost (Lipschitz grid h = margin/L over the band, every evaluation an N_eff-term interval sum):

| lam | range | h_cert | evaluations | interval terms | arb (~3e6 terms/s) | float + a-priori error bound (~1e9/s) |
|---|---|---|---|---|---|---|
| 0.7 | [T-D, 6.05e6] (whole band) | 0.103 | 5.2e7 | 6.1e11 | 57 h | 0.17 h |
| 1.0 | [T-D, 1e7] | 0.033 | 2.8e8 | 2.9e13 | 2640 h | 8 h |
| 1.0 | [T-D, 1.26e11] (whole band) | 0.033 | 3.8e12 | 3.8e17 | 3.6e7 h | 1.1e5 h (12 years) |

The float+error-bound route (one block-Vandermonde matmul per 1024 centres with a rigorous rounding-error majorant
M N 2^{-52} sum|a_n| plus the prime tail bound) is what the sweep already does; wrapping it rigorously is engineering.
A NUFFT (not installed here) or Chebyshev-interpolated blocks would cut the lam = 1 to-1e7 cost by ~10-100x but cannot
touch the 1.26e11 band: the band length, not the per-point cost, is the wall.

## 3. What closing a fixed width would say about zeros

Detection floor y0(lam, t): a zero at |beta - 1/2| < y0 leaves F(c, lam) >= 0 for EVERY c at this lam.  Model
(nearest-neighbour lam* = log(x1^2/2y^2)/(2(x1^2+y^2)), x1 = 2pi/log(t/2pi)) and the REAL-neighbour measurement
(flint zeros, replace-mode quadruple at t0, c scanned t0 +- 1 step 0.005, fixed lam; 'none' = F >= 0 for every c even
at y = 0.5, the strip edge):

| lam | model t=1e3 | 1e5 | 1e6 | 1e8 | 1e12 | real t0=640000.9 (x1 .60) | 640500.1 (.38) | 999999.8 (.42) | 1000499.7 (.56) |
|---|---|---|---|---|---|---|---|---|---|
| 0.3 | 0.511 | 0.387 | 0.331 | 0.252 | 0.168 | none | none | none | none |
| 0.5 | 0.379 | 0.350 | 0.308 | 0.242 | 0.165 | none | none | none | none |
| 0.7 | 0.283 | 0.318 | 0.289 | 0.233 | 0.162 | none | none | none | none |
| 1.0 | 0.183 | 0.279 | 0.263 | 0.221 | 0.158 | 0.435 | 0.423 | 0.449 | 0.388 |
| 1.5 | 0.087 | 0.226 | 0.227 | 0.203 | 0.152 | 0.315 | 0.334 | 0.319 | 0.270 |
| 2.0 | 0.041 | 0.185 | 0.198 | 0.187 | 0.147 | 0.244 | 0.282 | 0.248 | 0.211 |

The model is wrong at height (WALL_LANDSCAPE already showed this at 1e4): with mean gap 0.53-0.6 and Gaussian width
1/sqrt(2 lam) = 0.85-1.3 at lam <= 0.7, several on-line neighbours sit inside the window and their positive mass beats
2 y^2 e^{2 lam y^2} even at y = 1/2.  So at lam <= 0.7, F(c, lam) >= 0 for all c is consistent with a zero ANYWHERE in
the strip at heights >= 6.4e5 (four sample ordinates, all 'none').  At lam = 1 the floor is 0.39-0.45: only zeros within
0.05-0.11 of the strip edge would be excluded, a sliver the classical zero-free region (y < 0.487 at t = 1e6) already
mostly covers.  New localisation content starts at lam ~ 1.5-2 (floor 0.21-0.33), exactly the widths whose bands
(1e22, 5e39) are astronomically beyond any prime-side sweep.

## Verdict

- lam = 0.3, 0.5: the fixed-width residual above the ladder is EMPTY (c_triv = 627, 3.9e4 < T); closable today at zero
  cost given the ladder; closing it certifies NOTHING about zeros beyond the ladder (y0 = none at every sampled height).
- lam = 0.7: the band [6.4e5, 6.05e6] IS closable from the prime side today: min F/A = 5.04, Lipschitz grid 5.2e7
  evaluations x 1.2e4 terms = 6e11 interval terms, ~57 h in arb or well under an hour with float plus a rigorous
  rounding/tail majorant (the float sweep itself took 17 s).  Closing it certifies NOTHING about zeros beyond the
  ladder: at lam = 0.7 an off-line zero anywhere in the strip above 6.4e5 leaves F >= 0 at every c.
- lam = 1: NOT closable today: the band runs to 1.26e11; positivity holds numerically with margin >= 3.5 on the first
  1e7 and the margin widens with c, but a certificate needs 3.8e12 evaluations (3.8e17 terms, 12 years float, 4e7 h arb).
  Even closed, it would exclude only zeros within ~0.05-0.1 of the strip edge above T.
- lam >= 1.5: bands to 1e22 and 5e39; out of reach by 10-30 orders of magnitude, and those are the first widths whose
  positivity would say anything (floor 0.2-0.3) about zeros.
Fixed-width closure and zero content are anti-correlated across lam: the widths that are closable are exactly the widths
that see nothing.  This is the wall map's diagonal in numbers.

## What the numerics cannot establish

- Nothing rigorous: float sweeps with a 1e-3-relative prime truncation, arch/A linearly interpolated (error ~1e-5 for
  c < 50, negligible on the band), Lipschitz grid not actually run as intervals.
- The lam = 1 band beyond 1e7 (extrapolated sup only); lam >= 1.5 sups not swept at all.
- y0 'none' rests on four sampled ordinates near 6.4e5 and 1e6, not on all heights; the model column is a lower bound
  on the true floor at height, not an estimate.
