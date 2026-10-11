# Weil positivity on the one-prime window log(2)/2 < a < log(3)/2 (2026-10-11)

**Status: a bounded numerical SEARCH, not a proof. Nothing here is progress on the Riemann
Hypothesis. `conjecture1_proved = False`.** Every finite Gram matrix below is positive, as it must be
given the numerically verified low zeros of zeta; that is a consistency check, not evidence.

Code: `one_prime.py` (imports, does not edit, `../weil_form.py` and `../gram_experiments.py`).
Tables: `results/` (`tables.md`, `extrapolation.md`, `rates.md`, `cc_hyperplane.md`,
`lag_tolerance_n120.md`, `lag_tolerance_n240_float64.md`, per-case JSON in `results/records/`).
Python `~/hodge-engine/venv/bin/python`, `OMP_NUM_THREADS=1`, `OPENBLAS_NUM_THREADS=1`.
Basis: the validated cubic B-spline basis of E1 (`WEIL_POSITIVITY_SEARCH_2026-10-11.md`), n splines on
[-a, a], 60-digit arithmetic, every matrix split into its even and odd sectors (all matrices are
centrosymmetric). Grid: a in {0.30, 0.3466, 0.36, 0.38, 0.40, 0.42, 0.45, 0.48, 0.50, 0.52, 0.54,
0.549}, n in {30, 60, 90, 120, 180, 240}: 72 cases.

---

## Verdict first

1. **G = A - w2 Q is positive definite on every case** (a up to 0.549, n up to 240). Its minimum
   eigenvalue falls from 2.1e-4 (a = 0.40) to 7.4e-8 (a = 0.549) at n = 240. It decays like
   exp(-55 a) on the window. The even sector always carries the minimum.
2. **Correction to the task's premise: Q_2 is not rank <= 2.** Q(f) = (f*f~)(log 2) + (f*f~)(-log 2)
   = 2 int f(y) f(y - log 2) dy is the lag-log-2 correlation form. On L^2[-a, a] it vanishes on
   functions supported in |x| <= log 2 - a. It pairs the two end strips [-a, a - log 2] and
   [log 2 - a, a], each of length 2a - log 2. On L^2(strips) it is unitarily [[0, 1], [1, 0]], with
   spectrum {-1, +1} of infinite multiplicity. Its numerical rank in the basis grows linearly in n,
   from 12+12 at n = 30 to 87+87 at n = 240 for a = 0.549. The set of admissible weights is still an
   interval, and the Schur-complement derivation still works, but on an r x r block with r ~ n.
3. **Admissible interval.** {c : A - cQ >= 0} = [c_lo(a), c_hi(a)] always contains
   w2 = log 2/sqrt 2 = 0.4901290717 strictly.
   * c_lo is set by the odd sector and c_hi by the even sector.
   * Both margins **converge in n**, roughly like n^-1.2, to positive limits. The interval does not
     collapse onto w2 as n grows.
   * Both margins **shrink exponentially in a**. At a = 0.549 the extrapolated limits are
     w2 - c_lo = 4.0e-5 and c_hi - w2 = 1.6e-6. So the "knife edge" of E1 is a large-a effect,
     already severe inside the window, and not an n-effect.
   * c_lo never reaches w2.
   * No credible closed form exists for c_lo or c_hi.
4. **Mechanism.** The exact reduction is not a 2 x 2 matrix inequality. It is **one scalar inequality
   per parity sector, through the rank-one pole term**. Write K = ARCH - CONST (archimedean place
   without poles). Then:

       even f:  W(f*f~) = K(f) - w2 Q(f) + 2 C(f)^2,   C(f) = int f(x) cosh(x/2) dx
       odd  f:  W(f*f~) = K(f) - w2 Q(f) - 2 S(f)^2,   S(f) = int f(x) sinh(x/2) dx

   Weil positivity on the window is equivalent to the following.
   * **(H) Hyperplane part.** K - w2 Q >= 0 on {C = 0} (even) and on {S = 0} (odd). This is the
     Connes-Consani object (pole functionals killed) plus one prime. It holds with a comfortable
     margin: 1.1e-3 even and 0.044 odd at a = 0.549. The archimedean part alone, K, is already
     positive there, at 0.09 and 0.39, so on the hyperplane **the prime is not needed and only
     costs margin**.
   * **(S) Scalar part.** rho_even := 2 <cosh(x/2), (K - w2 Q)^{-1} cosh(x/2)> <= -1 and
     rho_odd := 2 <sinh(x/2), (K - w2 Q)^{-1} sinh(x/2)> <= 1. Equivalently, the minimum of
     W(f*f~) over even f with 2C(f)^2 = 1 is 1 + 1/rho_even >= 0.
     - At a = 0.549, n = 240: -1 - rho_even = 5.7e-8 and 1 - rho_odd = 9.0e-4.
     - The even scalar is the knife edge. It tracks lambda_min(G) within 25 %.
     - Without the prime, K has a negative direction in the odd sector for a >= 0.40. K is positive
       on the hyperplane {S = 0}, so that direction must overlap the sinh(x/2) pole direction. The
       prime removes it: K - w2 Q > 0 on odd functions.
   * **Range of Q.** The negative eigenvector of A lies increasingly inside range(Q) as a grows, but
     never asymptotically in n:
     - mass in the end strips is 0.28, 0.61, 0.83 and 0.94 at a = 0.40, 0.45, 0.50 and 0.549;
     - its Q-Rayleigh quotient is -0.94 at a = 0.549, against an extreme of -1;
     - the even analogue reaches only 0.30.
5. **Is (S) provable by prolate/Sonin methods? Not as they stand.**
   * (H) is the kind of statement CC1 proves, but CC1 proves it only for 2a <= log 2 = 0.693. Its
     Prop 5.5 uses that support bound structurally. Here (H) is needed up to 2a = log 3.
   * (S) has a margin of 5.7e-8 that decays like exp(-55 a). CC1's analytic error budget is about
     1e-3 (epsilon_1 = 0.00122), and it is not certified. Under RH, (S) reads
     min sum_gamma |f^(gamma)|^2 / (2 f^(i/2)^2) >= 0, the zero sum against the value at the pole.
     So its margin is set by the zeros, not by any visible archimedean quantity.
   * A certified computation at fixed a might settle (S), but only if the n-truncation, which
     converges like n^-1.2, can be bounded rigorously. That would be a finite verification with no
     bearing on RH.
6. **The prime's location is special, and the knife edge needs the pole.**
   * Moving the lag to log q with the natural weight log q/sqrt q keeps positivity only for q in
     [2 - 6.5e-7, 2 + 2.9e-5] at a = 0.549, n = 240. This is consistent with CC2 sec 2.3's "within
     1e-3 of 2".
   * For q = 1.8, 2.2 and 2.5, at most a values in the window no weight c at all makes A - cQ_q
     positive. The interval is empty.
   * Davenport-Heilbronn on the same window has no pole. Its archimedean part is positive on its
     own, and its weight kappa log 2/sqrt 2 = 0.139 sits deep inside a wide interval, about
     [-1.3, 0.48]. There is no knife edge.

---

## 1. Setup

E1's validated convention: W(g) = POLE - PRIME - CONST + ARCH and B(f, f) = W(f * f~). For supp f in
[-a, a], g = f * f~ lives in [-2a, 2a]. For log 2 < 2a < log 3 the only prime power with
log n < 2a is n = 2. So PRIME = w2 [g(log 2) + g(-log 2)] with w2 = Lambda(2)/sqrt 2 = log 2/sqrt 2.
That gives G = A - w2 Q with A = POLE - CONST + ARCH. In the spline basis Q is Toeplitz, with entries
h M8((log 2 - m h)/h) + h M8((-log 2 - m h)/h). Its column builder (`q_col`) reproduces E1's prime
matrix exactly, and G agrees with `weil_form.spline_gram` to 3e-52 (a = 0.5, n = 30).

**Admissible interval, derivation.** S(c) = A - cQ is affine in c and the PSD cone is convex, so
I = {c : S(c) >= 0} is an interval. Q is indefinite (spectrum +-1 on the strips), so I is bounded.

* **Pencil form (used).** If G = S(w2) > 0, then S(c) = G - (c - w2) Q >= 0 iff (c - w2) mu <= 1 for
  every eigenvalue mu of the pencil Q v = mu G v. That gives c_lo = w2 + 1/mu_min and
  c_hi = w2 + 1/mu_max.
* **Schur form (the "restrict to range(Q)" version).** Let N span ker Q and W a complement. If
  A_NN > 0, then I = {c : S0 - c Q_WW >= 0}, an r x r problem with r = rank Q. Here
  S0 = A_WW - A_WN A_NN^{-1} A_NW is the Schur complement of A onto range(Q). A_NN is A on
  functions that do not reach the strips; its minimum is 0.085 at a = 0.45, n = 30.

Both forms were computed on the full matrix (`schur_check`, a = 0.45, n = 30) and agree to 1e-60.
The production runs use the pencil form per parity sector, and the overall interval is the
intersection of the two sector intervals.

## 2. Task 1: lambda_min(G) and where A alone fails

n = 240, 60 digits. Generalized eigenvalues of (X, M) are Rayleigh quotients X(f)/||f||^2. Full
table in `results/tables.md`, T1.

| a | lambda_min G (even) | lambda_min G (odd) | lambda_min A even | lambda_min A odd | lambda_min K odd |
|---|---|---|---|---|---|
| 0.30 | 8.27e-3 | 0.231 | 8.27e-3 | 0.231 | 0.239 |
| 0.3466 | 1.43e-3 | 0.0816 | 1.43e-3 | 0.0816 | 0.0931 |
| 0.36 | 9.41e-4 | 0.0530 | 1.11e-3 | 0.0419 | 0.0549 |
| 0.38 | 4.58e-4 | 0.0297 | 1.06e-3 | **-0.0149** | 3.3e-4 |
| 0.40 | 2.08e-4 | 0.0163 | 7.6e-4 | -0.0693 | **-0.0515** |
| 0.42 | 8.69e-5 | 8.5e-3 | **-6.1e-4** | -0.122 | -0.101 |
| 0.45 | 1.97e-5 | 2.8e-3 | -6.3e-3 | -0.196 | -0.171 |
| 0.48 | 3.60e-6 | 7.2e-4 | -0.0181 | -0.267 | -0.236 |
| 0.50 | 1.15e-6 | 2.4e-4 | -0.0296 | -0.313 | -0.278 |
| 0.52 | 4.24e-7 | 7.8e-5 | -0.0440 | -0.357 | -0.318 |
| 0.54 | 1.45e-7 | 3.0e-5 | -0.0610 | -0.401 | -0.357 |
| 0.549 | 7.42e-8 | 2.0e-5 | -0.0694 | -0.420 | -0.374 |

**Positivity.** G > 0 in all 72 cases. A rerun of a = 0.549, n = 120 at 80 digits reproduces
lambda_min, c_lo, c_hi and rho_even to all 20 printed digits. Precision is not the limit; truncation
in n is.

**Three thresholds for the prime-free form (n = 240 grid brackets).** All are relative to
log(2)/2 = 0.3466 and log(3)/2 = 0.5493.

* The odd sector of A fails first, in (0.36, 0.38). This is E1's a* ~ 0.3757 at n = 180, about
  0.372 extrapolated.
* The archimedean part K alone, with no pole, fails in the odd sector in (0.38, 0.40).
* A fails in the even sector in (0.40, 0.42).

All three thresholds fall slightly with n, like E1's a*(n). They lie inside the window, well below
log(3)/2.

**Cross-check with CC2.** At a = log(2)/2 the even minimum extrapolates to 1.34e-3 (n -> inf fit;
1.43e-3 at n = 240). CC2 Fig. 5 reports about 0.00133. CC2's "sign change a bit beyond log 2"
corresponds to e^{2 x 0.372} = 2.10, consistent with the A-alone threshold. That match is read off a
plot.

**lambda_min(G) in n.** It decreases in n but fits c_inf + C n^-p with p ~ 1.1-1.2 and a positive
c_inf. Examples: 9.6e-7 at a = 0.50 and about 5.6e-8 at a = 0.549 (`results/extrapolation.md`).
Under RH this is expected: the zero ordinates contain separated subsequences of arbitrarily large
uniform density. So by Beurling's sampling theorem, sum_gamma |f^(gamma)|^2 >= c(a) ||f||^2 with
c(a) > 0 for supp f in [-a, a]. E1 sec. 6 says the infimum over L^2[-a, a] "is 0". That should be
read as a large-a statement, not an n -> inf statement at fixed a. **This is flagged for E1, not
proved here.**

## 3. Task 2: the admissible interval [c_lo, c_hi]

n = 240 (full grid: `results/tables.md` T2/T2b). The numbers mu_max and mu_min are the extreme
eigenvalues of the pencil (Q, G) in the binding sector. "Next" is the second one.

| a | c_lo (odd) | c_hi (even) | w2 - c_lo | c_hi - w2 | rank Q (e+o) | mu_max even (next) | mu_min odd (next) |
|---|---|---|---|---|---|---|---|
| 0.36 | -0.906 | 1.397 | 1.40 | 0.907 | 9+9 | 1.10 (0.28) | -0.72 (-0.22) |
| 0.38 | 0.1325 | 0.6377 | 0.358 | 0.148 | 21+21 | 6.8 (0.41) | -2.8 (-0.29) |
| 0.40 | 0.3645 | 0.5246 | 0.126 | 0.0345 | 31+31 | 29 (0.54) | -8.0 (-0.34) |
| 0.42 | 0.4416 | 0.4992 | 0.0485 | 9.1e-3 | 41+41 | 110 (0.69) | -21 (-0.39) |
| 0.45 | 0.47844 | 0.49140 | 0.0117 | 1.28e-3 | 54+54 | 784 (0.97) | -86 (-0.45) |
| 0.48 | 0.487684 | 0.490299 | 2.4e-3 | 1.70e-4 | 66+66 | 5.9e3 (1.4) | -409 (-0.50) |
| 0.50 | 0.4893715 | 0.4901754 | 7.6e-4 | 4.6e-5 | 73+73 | 2.2e4 (1.8) | -1.3e3 (-0.54) |
| 0.52 | 0.4899039 | 0.4901439 | 2.3e-4 | 1.5e-5 | 79+79 | 6.8e4 (2.3) | -4.4e3 (-0.58) |
| 0.54 | 0.49004810 | 0.49013342 | 8.1e-5 | 4.3e-6 | 85+85 | 2.3e5 (3.0) | -1.2e4 (-0.62) |
| 0.549 | 0.49007584 | 0.49013115 | 5.3e-5 | 2.1e-6 | 87+87 | 4.8e5 (3.5) | -1.9e4 (-0.63) |

For a <= log(2)/2, Q = 0 and every c is admissible. At a = 0.3466 the strips have length 5e-5, so
Q ~ 1e-16 and the interval is about +-1e16.

**(i) Convergence in n, not collapse.** The table below shows n = 30 ... 240, the Aitken limit
from n = 60, 120, 240, and a power fit c_inf + C n^-p through n = 120, 180, 240.

| a | quantity | n=30 | 60 | 120 | 240 | Aitken | power fit (p) | limit margin |
|---|---|---|---|---|---|---|---|---|
| 0.45 | c_lo | 0.456963 | 0.471130 | 0.476275 | 0.478444 | 0.480025 | 0.480192 (1.16) | w2 - c_lo = 9.9e-3 |
| 0.45 | c_hi | 0.495116 | 0.492552 | 0.491729 | 0.491405 | 0.491195 | 0.491165 (1.23) | c_hi - w2 = 1.04e-3 |
| 0.50 | c_lo | 0.4871980 | 0.4886821 | 0.4891759 | 0.4893715 | 0.4895000 | 0.4895165 (1.23) | 6.1e-4 |
| 0.50 | c_hi | 0.4903121 | 0.4902179 | 0.4901873 | 0.4901754 | 0.4901679 | 0.4901668 (1.25) | 3.8e-5 |
| 0.549 | c_lo | 0.48996718 | 0.49003987 | 0.49006424 | 0.49007584 | 0.49008638 | 0.49008860 (0.93) | 4.0e-5 |
| 0.549 | c_hi | 0.49013844 | 0.49013406 | 0.49013197 | 0.49013115 | 0.49013064 | 0.49013067 (1.42) | 1.6e-6 |

w2 is strictly inside, with a margin that converges as n grows. The interval does **not** collapse
onto w2 in n. It does narrow fast in a.

**Empirical rates (n = 240, a in [0.42, 0.549], `results/rates.md`).** Each margin behaves like
C exp(-kappa a):

| margin | kappa | kappa / gamma_1 |
|---|---|---|
| lambda_min G | 54.5 | 3.85 |
| c_hi - w2 | 64.2 | 4.54 |
| w2 - c_lo | 53.9 | 3.81 |
| -1 - rho_even(w2) | 55.1 | 3.90 |
| 1 - rho_odd(w2) | 47.8 | 3.38 |

The ratio (c_hi - w2)/lambda_min G drifts from 105 to 28 across the window. kappa ~ 55 is close to
4 gamma_1 = 56.5, where gamma_1 = 14.1347 is the first zero ordinate. That is a fit over a factor
1.3 in a, so it is a coincidence until shown otherwise. It is at least the right scale for an
extremal function whose transform must be small at gamma_1 over an interval of half-width a.

**(ii) Sanity.** c_lo < w2 < c_hi in all 72 cases. c_lo never crosses w2.

**(iii) Closed forms: nothing credible.** `mp.identify` on the Aitken limits, against
{log 2, pi, euler, sqrt 2} at tolerance 1e-7, returns a rational combination for every value. One
example is c_hi(0.50) ~ -2/5 + (13/5) log 2 - (3/5) gamma - (2/5) sqrt 2. These are artefacts: the
limits are known to about 1e-6 at best (Aitken and power fits differ at the 1e-7 to 1e-5 level), and
four constants with small rational coefficients fit any 7-digit number. They are listed in
`results/extrapolation.md` only to document the attempt. c_lo and c_hi are n -> inf limits of
extremal problems involving the full archimedean operator. They should not be expected to be
elementary.

## 4. Task 3: the mechanism and the reduced inequality

**Is the negative direction of A inside range(Q)?** Partly, and more so as a grows. The table gives
the normalized minimal eigenvector of A per sector (`results/tables.md`, T3):

* "strip mass" is the share of int f^2 on |x| >= log 2 - a;
* "in range(Q)" is the squared M-norm of its projection on range(M^-1 Q);
* "Q(v)" is the Q-Rayleigh quotient, with extremes +-1.

| a | n | odd: strip mass / in range(Q) / Q(v) | even: strip mass / in range(Q) / Q(v) |
|---|---|---|---|
| 0.40 | 30 / 240 | 0.22 / 0.39 / -0.12 ; 0.28 / 0.27 / -0.25 | 0.006 / 0.026 / 6e-4 ; 0.006 / 0.006 / -1e-3 |
| 0.45 | 30 / 240 | 0.56 / 0.71 / -0.42 ; 0.61 / 0.60 / -0.57 | 0.034 / 0.087 / -0.009 ; 0.036 / 0.034 / -0.025 |
| 0.50 | 30 / 240 | 0.81 / 0.87 / -0.70 ; 0.83 / 0.83 / -0.81 | 0.11 / 0.18 / -0.05 ; 0.13 / 0.12 / -0.10 |
| 0.549 | 30 / 240 | 0.93 / 0.97 / -0.87 ; 0.94 / 0.94 / -0.94 | 0.27 / 0.38 / -0.15 ; 0.30 / 0.28 / -0.24 |

* In the odd sector, A's negative direction moves into the strips and towards the Q = -1 eigenspace
  (f_R = -tau f_L) as a -> log(3)/2. That is why the subtracted prime term -w2 Q can cancel it.
* The containment is stable in n but never complete.
* Q's range has dimension about 0.36 n per sector. So there is **no 2 x 2 reduction**.

What is low-dimensional is the pencil (Q, G): one eigenvalue dominates per sector. In the even
sector mu_max = 4.8e5 against 3.5 for the next; in the odd sector mu_min = -1.9e4 against -0.63. So
each endpoint of the interval is a rank-one phenomenon, along G's near-null vector. That rank one is
the pole.

**The exact reduced inequality (rank-one pole Schur complement).** The pole term is +2 C(f)^2 on even
f and -2 S(f)^2 on odd f, rank one per sector. This was checked on every case: one nonzero
eigenvalue, the other 1e-60. Sylvester's law of inertia then gives, exactly on every finite basis
(`results/tables.md` T4):

* **odd:** G >= 0 iff K - w2 Q > 0 on odd functions and
  rho_odd = 2 <sinh(x/2), (K - w2 Q)^{-1} sinh(x/2)> <= 1;
* **even:** G >= 0 iff K - w2 Q has exactly one negative direction on even functions and
  rho_even = 2 <cosh(x/2), (K - w2 Q)^{-1} cosh(x/2)> <= -1.

The equivalent "CC plus one scalar" form is: (H) K - w2 Q >= 0 on the pole-free hyperplane of each
sector, and (S) sigma_even = 1 + 1/rho_even >= 0 and sigma_odd = 1/rho_odd - 1 >= 0. Here sigma_even
is the minimum of W(f*f~) over even f with 2 C(f)^2 = 1, and sigma_odd the same with 2 S(f)^2 = 1.

Values at n = 240. Columns 2-3 count negative directions of K - cQ, written even/odd. Columns 7-8 are
lambda_min of K - cQ on the pole-free hyperplane (`results/cc_hyperplane.md`).

| a | #neg K, c = 0 | #neg K, c = w2 | rho_even(0) | -1 - rho_even(w2) | rho_odd(0) | 1 - rho_odd(w2) | (H) even: K / K - w2 Q | (H) odd: K / K - w2 Q |
|---|---|---|---|---|---|---|---|---|
| 0.30 | 1/0 | 1/0 | -1.0081 | 8.1e-3 | 0.032 | 0.968 | 0.700 / 0.700 | 0.996 / 0.996 |
| 0.3466 | 1/0 | 1/0 | -1.0013 | 1.30e-3 | 0.126 | 0.874 | 0.555 / 0.555 | 0.851 / 0.851 |
| 0.38 | 1/0 | 1/0 | -1.00094 | 3.99e-4 | 46.5 | 0.679 | 0.463 / 0.363 | 0.759 / 0.807 |
| 0.40 | 1/1 | 1/0 | -1.00069 | 1.77e-4 | -0.34 | 0.517 | 0.411 / 0.242 | 0.708 / 0.785 |
| 0.45 | 1/1 | 1/0 | -0.99355 | 1.60e-5 | -0.14 | 0.134 | 0.292 / 0.073 | 0.590 / 0.511 |
| 0.50 | 1/1 | 1/0 | -0.95970 | 9.1e-7 | -0.12 | 0.0118 | 0.186 / 0.014 | 0.484 / 0.208 |
| 0.549 | 1/1 | 1/0 | -0.83952 | **5.7e-8** | -0.11 | **9.0e-4** | 0.091 / 0.0011 | 0.390 / 0.044 |

Reading of the table:

* **Without the prime.** For a >= 0.40, K has a negative direction in the odd sector, so the odd
  criterion fails before the pole is even considered. In the even sector rho_even(0) > -1 from about
  0.42. That is A's two failures.
* **With the prime.** K - w2 Q is positive on odd functions, and the pole stays below the threshold:
  1 - rho_odd = 9e-4 at a = 0.549. In the even sector the scalar lands at -1 - 5.7e-8.
* **On the pole-free hyperplane (H).** The archimedean part alone is positive across the whole window
  (0.09 even, 0.39 odd at a = 0.549). Including the prime *lowers* those numbers. So on the window,
  every bit of necessary help from the prime sits in the scalar coupling to the two pole directions.
* **Beyond the window.** For a > log(3)/2 this is archimedean information only, n = 120. With
  int f = 0 also imposed, the even-sector hyperplane value of K stays positive to about a = 1
  (0.016 at a = 1.0). With only the pole condition it turns negative between a = 0.60 and 0.65.

**Two sides of the knife-edge inequality, a = 0.549, n = 240.**

    2 <cosh(x/2), (K - w2 Q)^{-1} cosh(x/2)> = -1.000000057   versus the threshold -1
    2 <sinh(x/2), (K - w2 Q)^{-1} sinh(x/2)> = 0.99910       versus the threshold 1

The even margin is 5.7e-8, extrapolating to about 4.4e-8 as n -> inf. The odd margin is 9.0e-4,
extrapolating to 6.9e-4.

**What the reduced inequality is, honestly.** It is a scalar, but not one between "explicit
archimedean quantities and w2". Both sides involve the resolvent of the full operator K - w2 Q,
which contains the prime. Under RH, sigma_even = min sum_gamma |f^(gamma)|^2 over even f with
2 f^(i/2)^2 = 1. In words: how small the transform can be at all zeta ordinates once its value at
the pole is pinned. That makes (S) a restatement of the explicit formula with the zeros' margin
built in, not a reduction to something the zeros do not already control.

**Provability by the CC methods (prolate/Sonin).**

* **(H)** is CC1's kind of statement: archimedean place, pole functionals killed. It has an O(0.1)
  margin across the window. But CC1's proof is tied to |supp| <= log 2. Prop 5.5 and the kernel
  K_I need the window, and the extension needed here is to log 3. A prime term must also be carried.
  It is an open question whether the Sonin compression survives that. Nothing here says it does.
* **(S)** has a margin of 5.7e-8 that shrinks like exp(-55 a). CC1's analytic error budget is about
  1e-3 (epsilon_1 = 0.00122), and their numerics are uncertified per the CC reading. Prolate/Sonin
  estimates of that quality cannot see a 1e-7 margin.
* The realistic route to a proof of positivity on this window is a certified computation (interval
  arithmetic plus a rigorous n-truncation bound). The slow n^-1.2 convergence makes that bound the
  hard part. It would be a finite-window verification. The DH control in E1 shows that a single
  off-line zero at height 86 stays invisible until a ~ 2, so such a statement says nothing about RH.

## 5. Task 4: controls

**Fake prime location** (n = 120, `results/tables.md` T5). G_q = A - (log q/sqrt q) Q_{log q}, with
the term present once 2a > log q.

| form | a = 0.3466 | 0.40 | 0.42 | 0.45 | 0.50 | 0.549 |
|---|---|---|---|---|---|---|
| q = 1.8 (w = 0.438) | even fails (-0.015); interval nonempty | even fails (-0.053) | even: no c works | even: no c works | even: no c works | both sectors: no c works |
| q = 2 (zeta, w2) | PSD | PSD | PSD | PSD | PSD | PSD |
| q = 2.2 (w = 0.532) | no term | odd: no c works | odd: no c works | both: no c works | both: no c works | both: no c works |
| q = 2.5 (w = 0.580) | no term | no term | no term | no term | both: no c works | both: no c works |

"No c works" means max over c of lambda_min(A - cQ_q) is negative, for example -0.06 to -0.25 in the
odd sector for q = 2.2 and 2.5. So for most of the window, a correlation term at the wrong lag cannot
repair A at any weight. Only lags very close to log 2 can. With the natural weight:

| a | q-window keeping G_q PSD (n = 120; endpoints confirmed by a sign flip at 60 digits) | width at n = 240 (float64) |
|---|---|---|
| 0.40 | [1.99379, 2.03239] | 3.4e-2 |
| 0.45 | [1.999651, 2.004787] | 4.4e-3 |
| 0.50 | [1.9999845, 2.0004348] | 3.6e-4 |
| 0.52 | [1.9999949, 2.0001390] | - |
| 0.549 | [1.99999911, 2.00003452] | 2.9e-5, i.e. [2 - 6.5e-7, 2 + 2.9e-5] |

This is consistent with CC2 sec. 2.3, where at 2L = log 3 positivity needs p within less than 1e-3 of
2.

**Davenport-Heilbronn on the same window** (n = 120, lag log 2, weight c(2)/sqrt 2 = kappa log 2/sqrt 2
= 0.1392, archimedean part with Gamma((s+1)/2), no pole):

| a | lambda_min A_DH even / odd | lambda_min G_DH even / odd | even interval | odd interval |
|---|---|---|---|---|
| 0.40 | 0.551 / 1.570 | 0.536 / 1.598 | [-3.63, 1.86] | [-2.36, 3.65] |
| 0.45 | 0.457 / 1.453 | 0.419 / 1.520 | [-2.87, 1.09] | [-1.77, 2.93] |
| 0.549 | 0.305 / 1.255 | 0.225 / 1.381 | [-2.11, 0.48] | [-1.30, 2.26] |

DH's archimedean part is positive on its own here. Its prime weight sits deep inside a wide interval
with O(1) margins, and lambda_min(G_DH) ~ 0.2 rather than 1e-7. **The knife edge in zeta is made by
the pole.** The two pole directions are what force A negative and what the prime must cancel almost
exactly. DH has no pole, so it shows neither. (DH fails only at a ~ 2, through an off-line zero; E1.)

## 6. Caveats

* Floating point at 60 digits (80-digit spot check identical). Nothing is certified.
* Every statement is about finite spline subspaces of L^2[-a, a], n <= 240. The n -> inf limits are
  extrapolations from Aitken and power fits. They agree to 1e-7 to 1e-5 and are not bounds.
* Splines are C^2, so g = f * f~ is C^6. That is enough for the explicit formula, but it is not
  Weil's C_c^inf class.
* "c_lo/c_hi binding sector", "rank Q" and the effective rank-one pencil are basis-level
  observations.
* The rank-one Schur equivalences are exact linear algebra on each basis.
* The rate kappa ~ 55 ~ 3.9 gamma_1 is a three-decade fit, not a derivation.
* The Beurling-sampling remark (positive n -> inf limit of lambda_min G at fixed a) is conditional on
  RH and is not checked beyond the n-trend.

## 7. Reproduction

    cd telperion/research/weil_positivity/one_prime; PY=~/hodge-engine/venv/bin/python
    for each (a, n) in the grid:  $PY one_prime.py build A N 60      # caches Toeplitz columns (scratchpad)
    for each (a, n):              $PY one_prime.py analyse A N       # tasks 1-4 per case (controls for n <= 120)
    for each (a, n):              $PY one_prime.py ccplus A N        # pole-free hyperplane (H)
    $PY one_prime.py schur_check 0.45 30                               # Schur vs pencil interval
    $PY one_prime.py tables; $PY one_prime.py extrap; $PY one_prime.py rates; $PY one_prime.py cctable
    $PY one_prime.py lagscan 120; $PY one_prime.py lagscan 240 0.45,0.50,0.549 0

The column caches live in the scratchpad (`.../scratchpad/one_prime/cols`, regenerable in about
15 minutes on 8 cores). Per-case results are copied to `results/records/`.

Nothing here is progress on RH. **conjecture1_proved = False.**

## Addendum (2026-10-11, after review by the Riemann session)

- **The window "knows" the prime 2, one-sidedly.** At a = 0.549 positivity survives only for prime locations
  q ∈ [2 − 6.5e-7, 2 + 2.9e-5] (weight log q/√q): a window about 45 times tighter below 2 than above.
- **One knife edge, seen two ways.** The upper c-margin at a = 0.549 (c_hi − w2 = 1.6e-6, set by the even sector)
  and the even-sector Schur scalar (ρ = −1.000000057, margin 5.7e-8 to −1) measure the distance from the same point
  (w2, even sector) to the same boundary of the even-sector PSD cone, along two different directions: raising the
  prime weight, versus the pole functional at fixed weight. They are the same constraint; their ratio is the slope
  dρ/dc ≈ 0.036 at that point. We agree with the reviewer's reading.
- **Decision recorded by the island owner** (`~/rh-team/gates/kwin2_one_prime_decision.md`): no monolithic kernel
  certificate at 2L ≤ 1.098 (floor 5.6e-8, 6-7x below the 19 GB L = 1/2 certificate; and rungs below L ≈ 1.86 cannot
  separate zeta from DH, so the extra window carries no information about the zeros). Queued instead: a probe that
  re-emits L = 1/2 in the split form (LDL^T of K − w2Q on the pole hyperplane, the tail condition, and one exact
  rational check of the Schur scalar) to compare peak memory; if far below 19 GB, 0.549 becomes cheap.
- **Correction to E1.** E1's note says the infimum of the Weil form over L²[−a, a] "is 0". At fixed a the data here
  show λ_min converging in n to a positive limit (as Beurling's sampling theorem predicts under RH); E1's statement
  should be read as a large-a statement. Fixed in the E1 note.
