# Weil positivity on the open one-prime strip 1/2 < L < log(3)/2 (2026-10-11)

**Status: a bounded numerical SEARCH, not a proof. Nothing here is progress on the Riemann
Hypothesis. `conjecture1_proved = False`.** Finite-window Weil positivity is not RH. Every positive
number below follows from the numerically verified low zeros and is a consistency check.

**Already a kernel theorem (main, rvm_bridge island).** `KWin2_BridgeHeavy.weil_positivity_window_half`
covers every `IsWeilTest` g with supp g in [-L, L] and 2L <= 1. It gives
Re weilForm(autocorr g) >= 0, with the pole terms kept and the n = 2 prime term exact. The certified
floors are:

* 4.5e-6 ||g||^2 at L = 9/20;
* 3.5e-7 ||g||^2 at L = 1/2 (`weil_window_floor_half`).

The prime-free part, 2L <= log 2, is `KWin_Bridge`. So in half-width L (= a below) **only
1/2 < L < log(3)/2 = 0.549306 is open on the one-prime window**. This note concerns that open strip
and the margins there. The rational endpoint a certificate would target is L = 0.549, i.e.
2L = 1.098 < log 3.

Code: `one_prime.py`. It imports, without editing, `../weil_form.py` and `../gram_experiments.py`.
The new polynomial-basis part is the `PolyForm`, `poly_forms`, `poly_case`, `poly_validate` and
`poly_lagscan` functions. Results are in `results/`, with per-case JSON in `results/records/`
(`poly_a*_N*.json`). Python `~/hodge-engine/venv/bin/python`, single-threaded BLAS. The island files
KWin2_* and `~/rh-team/B/scripts/reconcile.py` were read, not modified.

---

## Verdict first

1. **The floor stays positive across the whole open strip.** It falls smoothly, with no sign of
   reaching 0 before log(3)/2. KWin2-style basis (Legendre P_{2k+par}(x/L), the span of the island's
   monomials (x/L)^{2k+par}), 60 digits, 24 functions per sector:

   | L | floor |
   |---|---|
   | 0.50 | 9.365e-7 |
   | 0.52 | 3.491e-7 |
   | 0.54 | 1.069e-7 |
   | **0.549** | **5.654e-8**, converging in basis size to 5.629e-8 at N = 40 per sector (limit about 5.6e-8) |
   | 0.5493 | 5.570e-8 |

2. **Against the owner's prediction.** The owner's numbers are 9.4e-7 at 0.5 (mine: 9.38e-7 at K = 40)
   and 1.6e-9 at 0.6 (mine: 1.62e-9; prime 3 enters there). Log-interpolation gives 4.1e-8 at 0.549.
   The measured floor runs 1.1-1.5x **above** that line across the strip: 5.63e-8 at 0.549. The curve
   steepens past log 3 because the prime 3 enters.
3. **Size relative to the L = 1/2 certificate.** The floor at 0.549 is 6.2x below the certified
   3.5e-7 and 16.7x below the true floor at 1/2 (9.38e-7). The L = 1/2 certificate kept 37 % of its
   true floor. At that rate a 0.549 certificate would land near 2e-8.
   **One concrete obstacle from the island's own parameter file:** KWin2_Par12 reports a Psi_0
   minorant gap of about 1.2e-7 at low frequency (Nser = 1200, and Nser = 1500 gets `decide` stuck).
   That gap is already 2x the whole floor at 0.549. The minorant must get several times tighter before
   anything else matters.
4. **The admissible weight on the cos(t log 2) multiplier.** The interval [c_lo, c_hi] contains
   sqrt2 log 2 = 0.980258 strictly at every L. The odd sector sets c_lo and the even sector sets c_hi.

   | L | c_lo | c_hi | margin below | margin above |
   |---|---|---|---|---|
   | 0.50 | 0.979071 | 0.980331 | 1.2e-3 | 7.3e-5 |
   | 0.549 | 0.9801775 | 0.9802612 | 8.1e-5 | **3.1e-6** (relative 3.2e-6) |

   The upper margin shrinks like exp(-57 L). It converges in basis size (3.08e-6 at N = 40). This is
   a margin on the weight, not on the floor; the certificate pins c to 1e-16, so it costs nothing
   there.
5. **The prime location and the pole matter.**
   * With the natural weight log q/sqrt q, positivity at L = 0.549 survives only for q in
     [2 - 4.9e-7, 2 + 2.2e-5].
   * For q = 1.8, 2.2 and 2.5 no weight at all makes the form positive on most of the strip.
   * Davenport-Heilbronn, which has no pole, is comfortably positive. Its floor is about 0.2 and its
     weight sits in an O(1)-wide interval.
6. **Correction to the original premise, as the lead noted.** Q_2 is the Fourier multiplier
   2 cos(t log 2) on |g^|^2/(2 pi), not a rank-2 form. In the polynomial basis it has full numerical
   rank, 24/24 per sector at relative threshold 1e-30. The "negative directions live in range(Q_2)"
   reduction is dropped. The exact reduction that does exist goes through the rank-one *pole* term;
   it is kept in the appendix.

---

## 1. Setup and validation

Symbol form (lead's convention), half-width L:

    W(g * g~) = (1/2pi) int |g^(t)|^2 [Psi(t) - c cos(t log 2)] dt + pole terms,
    Psi(t) = Re psi(1/4 + it/2) - log pi,   c = 2 Lambda(2)/sqrt 2 = sqrt2 log 2 = 0.98025814.

This is E1's W = POLE - CONST + ARCH - PRIME, with PRIME = (log2/sqrt2) [f(log 2) + f(-log 2)] and
f = g * g~. So the multiplier weight c is twice the weight on the correlation form used in the
spline appendix.

**Polynomial basis.** Sector par in {0, 1}: phi_k(x) = P_{2k+par}(x/L), k < N. This has the same span
as KWin2's monomials (x/L)^{2k+par}. The construction is the u-space identity used by the island's
`gram_uspace`, in 60-digit mpmath:

* correlations F_jk(t) = int phi_j(v) phi_k(v - t) dv, polynomials on [0, 2L], computed by exact
  Gauss rules;
* ARCH = int_0^{2L} [2 e^{-2t} M - e^{-t/2} (F + F^T)] / (1 - e^{-2t}) dt - M log(1 - e^{-4L}), by
  Gauss-Legendre with 2D + 40 nodes (doubling changes entries by 2e-61);
* poles from the e^{+-x/2} moments;
* the prime matrix sum over n < e^{2L} of Lambda(n)/sqrt n (F(log n) + F(log n)^T).

The floor is lambda_min of the pencil (W, Gram), i.e. min W / ||g||_2^2, which is the normalization
of `WindowFloor`.

**Validation.**

* **Against `reconcile.py` (K = 40 Legendre = N = 20 per sector).** Mine: A alone 1.08347e-3 at 0.36
  and -2.35829e-2 at 0.38; full form 9.37661e-7 at 0.50. The script's values are 1.0835e-3,
  -2.3583e-2 and 9.3766e-7.
* **Zero side.** For the even minimiser at L = 0.5, N = 20, sum over the first 20000 zero pairs of
  |g^(gamma)|^2 = 9.3648e-7, against lambda_min = 9.3766e-7. The transform is exact through spherical
  Bessel functions, and the gap matches the slowly decaying tail (2.9e-10 in the last 5000 pairs).
* **The floor converges variationally.** The Legendre spaces are nested, so each finite-N floor is an
  upper bound for the infimum over L^2[-L, L], decreasing in N.

## 2. Task (a): the floor on the open strip

N = 24 per sector (degree <= 47), 60 digits. The even sector is always the binding one. The spline
column is my earlier B-spline basis at n = 240; see the appendix for why it is too high.

| L | 2L | floor (even) | odd sector min | owner log-interpolation 9.4e-7 -> 1.6e-9 | measured / interpolation | spline n = 240 |
|---|---|---|---|---|---|---|
| 0.45 | 0.90 | 1.619e-5 | 2.41e-3 | (certified 4.5e-6) | - | 1.97e-5 |
| 0.50 | 1.00 | 9.365e-7 | 1.94e-4 | 9.4e-7 | 1.00 | 1.15e-6 |
| 0.505 | 1.01 | 7.234e-7 | 1.45e-4 | 6.8e-7 | 1.06 | - |
| 0.51 | 1.02 | 5.644e-7 | 1.09e-4 | 5.0e-7 | 1.14 | - |
| 0.515 | 1.03 | 4.436e-7 | 8.19e-5 | 3.6e-7 | 1.23 | - |
| 0.52 | 1.04 | 3.491e-7 | 6.23e-5 | 2.6e-7 | 1.33 | 4.24e-7 |
| 0.525 | 1.05 | 2.723e-7 | 4.82e-5 | 1.9e-7 | 1.42 | - |
| 0.53 | 1.06 | 2.078e-7 | 3.80e-5 | 1.4e-7 | 1.50 | - |
| 0.535 | 1.07 | 1.527e-7 | 3.05e-5 | 1.0e-7 | 1.50 | - |
| 0.54 | 1.08 | 1.069e-7 | 2.47e-5 | 7.3e-8 | 1.46 | 1.45e-7 |
| 0.545 | 1.09 | 7.302e-8 | 1.96e-5 | 5.3e-8 | 1.37 | - |
| **0.549** | **1.098** | **5.654e-8** | 1.53e-5 | 4.1e-8 | 1.37 | 7.42e-8 |
| 0.5493 | 1.0986 | 5.570e-8 | 1.50e-5 | 4.1e-8 | 1.37 | - |
| 0.60 (n = 2, 3) | 1.20 | 1.621e-9 | 6.0e-7 | 1.6e-9 | 1.00 | - |

* Over [0.50, 0.549] the floor decays like exp(-57.4 L). From 0.549 to 0.60 it decays like
  exp(-69.6 L), because the prime 3 enters at 2L = log 3 with a vanishing overlap strip. So the
  log-linear interpolation through 0.6 undershoots inside the strip.
* There is no singular behaviour at log(3)/2. At 0.5493, 6e-6 below the endpoint, the floor is
  5.57e-8.

**Basis-size convergence at the exact rational endpoint L = 0.549:**

| N per sector (max degree) | 8 (15) | 12 (23) | 16 (31) | 20 (39) | 24 (47) | 28 (55) | 32 (63) | 40 (79) |
|---|---|---|---|---|---|---|---|---|
| floor | 6.662e-8 | 5.758e-8 | 5.720e-8 | 5.665e-8 | 5.654e-8 | 5.643e-8 | 5.634e-8 | **5.629e-8** |
| c_hi - sqrt2 log 2 | 3.54e-6 | 3.16e-6 | 3.14e-6 | 3.11e-6 | 3.10e-6 | 3.09e-6 | 3.09e-6 | 3.09e-6 |

* The floor converges, but the last digits creep: about 1e-10 per four degrees at the end. A
  conservative limit is 5.6e-8 to within 1 %. The finite-N values are upper bounds.
* At L = 0.50 the floor is 9.404e-7, 9.377e-7, 9.365e-7 and 9.357e-7 for N = 16, 20, 24 and 28.
* The island's head at L = 1/2 uses N = 31 even and 29 odd, in the same regime.

**What this says about extending the certificate.** These are observations, not a cost model.

* The target floor is about 5.6e-8. That is 6.2x below the certified 3.5e-7 at L = 1/2 and 16.7x
  below the true L = 1/2 floor. With the same slack (certified / true = 0.37) the certified number at
  0.549 would be about 2e-8.
* Every error term in the certificate (minorant gap, comb Taylor remainder, tail envelope, rounding)
  must fit under that.
* The Par12 comment gives the Psi_0 minorant gap as about 1.2e-7 with Nser = 1200 series terms. That
  is larger than the entire floor at 0.549. The minorant is the first thing that must improve, and
  Par12 notes that Nser = 1500 already makes the kernel's `decide` stall. This is the binding issue as
  far as these numbers can say.
* The extremal function is even-sector and well resolved by degree about 40 to 60 polynomials.
* Nothing indicates that the head dimension must grow much beyond the L = 1/2 values.

## 3. Task (b): the admissible weight interval at the location log 2

{c : A - c * [multiplier cos(t log 2)] >= 0} = [c_lo, c_hi], computed per sector and intersected,
from the pencil (Q_2, G): c = sqrt2 log 2 + 2/mu. N = 24 per sector.

| L | c_lo (odd) | c_hi (even) | sqrt2 log 2 - c_lo | c_hi - sqrt2 log 2 | relative upper margin | even pencil: top mu (next) |
|---|---|---|---|---|---|---|
| 0.40 | 0.76588 | 1.03551 | 0.214 | 0.0553 | 5.6e-2 | 36 (0.56) |
| 0.45 | 0.960722 | 0.982267 | 1.95e-2 | 2.01e-3 | 2.0e-3 | 996 (1.0) |
| 0.50 | 0.9790710 | 0.9803312 | 1.19e-3 | 7.31e-5 | 7.5e-5 | 2.7e4 (1.9) |
| 0.52 | 0.9799020 | 0.9802818 | 3.56e-4 | 2.37e-5 | 2.4e-5 | 8.5e4 (2.4) |
| 0.54 | 0.9801243 | 0.9802644 | 1.34e-4 | 6.21e-6 | 6.3e-6 | 3.2e5 (3.2) |
| 0.549 | 0.98017733 | 0.98026125 | 8.08e-5 | **3.10e-6** | 3.2e-6 | 6.5e5 (3.7) |
| 0.549, N = 40 | 0.98017752 | 0.98026123 | 8.07e-5 | 3.09e-6 | 3.2e-6 | |

* sqrt2 log 2 is strictly inside at every L, closer to the upper end. Raising the prime weight by
  3e-6 relative breaks positivity at 0.549. Lowering it by 8e-5 breaks it in the odd sector.
* The margins converge in N. They do not collapse onto sqrt2 log 2 as the basis grows. They do
  shrink exponentially in L.
* At each L the upper end is a rank-one effect. One pencil eigenvalue dominates (6.5e5 against 3.7
  next), along the near-null vector of G.
* No closed form was found for c_lo or c_hi. Earlier `mp.identify` attempts on spline extrapolations
  produced only overfit artefacts, as recorded in `results/extrapolation.md`.

## 4. Task (c): controls

**Fake location** (lag log q, natural multiplier weight 2 log q/sqrt q). N = 24, polynomial basis.
"Empty" means max over c of lambda_min < 0, so no weight at that lag works.

| L | q = 1.8 even / odd | q = 2.2 even / odd | q = 2.5 even / odd |
|---|---|---|---|
| 0.40 | fails (-0.058); interval [-0.33, 0.059] misses w / ok | ok (5.5e-4) / EMPTY (-0.063) | no term |
| 0.45 | EMPTY (-4.4e-3) / ok | EMPTY / EMPTY | no term |
| 0.50 | EMPTY (-0.011) / ok | EMPTY / EMPTY | EMPTY / EMPTY |
| 0.52 | EMPTY / EMPTY (-7.4e-3) | EMPTY / EMPTY | EMPTY / EMPTY |
| 0.54 | EMPTY / EMPTY | EMPTY / EMPTY | EMPTY / EMPTY |
| 0.549 | EMPTY (-0.019) / EMPTY (-0.127) | EMPTY (-0.070) / EMPTY (-0.113) | EMPTY (-0.048) / EMPTY (-0.249) |

**Lag tolerance** (natural weight, both sectors, N = 24). Endpoints are confirmed at 60 digits by
a sign flip at +-5e-8.

| L | q-window keeping positivity |
|---|---|
| 0.45 | [2 - 2.3e-4, 2 + 3.5e-3] |
| 0.50 | [2 - 1.0e-5, 2 + 2.8e-4] |
| 0.549 | [2 - 4.9e-7, 2 + 2.2e-5] |

This is consistent with CC2 sec. 2.3, "within 1e-3 of 2". The spline basis gives slightly wider
windows, [2 - 6.5e-7, 2 + 2.9e-5] at 0.549, n = 240, as expected from its too-high floor.

**Davenport-Heilbronn** (no pole; Gamma((s+1)/2); prime 2 with multiplier weight
2 kappa log 2/sqrt 2 = 0.2785; N = 24):

| L | min A_DH even / odd | floor even / odd | even c-interval | odd c-interval |
|---|---|---|---|---|
| 0.45 | 0.445 / 1.44 | 0.403 / 1.51 | [-5.61, 2.03] | [-3.44, 5.73] |
| 0.50 | 0.363 / 1.33 | 0.299 / 1.44 | [-4.74, 1.32] | [-2.89, 4.96] |
| 0.549 | 0.293 / 1.24 | 0.209 / 1.37 | [-4.13, 0.90] | [-2.56, 4.44] |

The DH archimedean part is positive by itself here. The weight sits deep inside an O(1) interval,
and the floor is about 0.2. The 1e-7-scale knife edge of zeta is made by the pole terms, which DH
does not have.

## 5. Caveats

* Floating point, 60 digits. Nothing is certified.
* The floors are lambda_min on finite polynomial subspaces. They are upper bounds for the infimum
  and converge to about 1 % by N = 40 at L = 0.549.
* The Weil class here is polynomial on [-L, L], extended by zero. That is the class the island's head
  matrix uses. The infimum over L^2 is what the certificate's floor must bound.
* The interpolation comparison uses the owner's two numbers as given.
* "Feasibility" remarks are read off the island's Par12 comments. No certificate was attempted.
* The DH weight convention: c(2) = kappa log 2 from E1's `dh_control.py`, and only n = 2 enters on
  this strip.

---

## Appendix: the earlier spline-basis study (superseded for floors, kept for structure)

The first pass used E1's cubic B-spline basis (n <= 240, 72 cases, `results/tables.md`,
`extrapolation.md`, `rates.md`, `cc_hyperplane.md`).

**Why its floors are too high.** Those splines vanish to third order at +-L. A Legendre basis times
(1 - u^2)^3 reproduces the effect at L = 0.5: 2.36e-6, 1.28e-6 and 1.09e-6 for N = 8, 16 and 24,
against the unconstrained 9.37e-7. The minimiser does not vanish at the endpoints. So the spline
floors converge like n^-1.2 from above, and E1's remark that the infimum "is 0" mistook that slow
drift for decay. In the polynomial basis the floor at fixed L converges to a positive limit, as
Beurling-type sampling predicts under RH.

**Results that carry over.** They are consistent with the polynomial basis. The spline-extrapolated
interval margins at 0.549, 4.0e-5 below and 1.6e-6 above in correlation-form units, double to the
multiplier-unit 8.1e-5 and 3.1e-6 above.

* Positivity of every case.
* c_lo is set by the odd sector and c_hi by the even sector.
* A alone fails first in the odd sector, near E1's 0.372, and later in the even sector, at 0.40-0.42.
* The fake-lag and DH controls.

**Exact rank-one pole reduction** (linear algebra, valid on any basis). Let K = ARCH - CONST. The pole
term is +2 (int g cosh(x/2))^2 on even g and -2 (int g sinh(x/2))^2 on odd g. Weil positivity on the
window is then equivalent to two conditions:

* **(H)** K - c Q_2 >= 0 on the pole-free hyperplane of each sector. This is the CC-type object plus
  one prime.
* **(S)** rho_even = 2 <cosh, (K - cQ_2)^{-1} cosh> <= -1, with exactly one negative direction of
  K - cQ_2 on even functions, and rho_odd = 2 <sinh, (K - cQ_2)^{-1} sinh> <= 1.

Spline values at n = 240, L = 0.549:

* (H) even 1.1e-3, odd 0.044. K alone is already positive there (0.09 / 0.39), so the prime only
  lowers (H).
* (S) even margin -1 - rho_even = 5.7e-8, which tracks the floor. Odd margin 9.0e-4.

So on this window the prime is needed only in the scalar coupling to the pole direction. Under RH,
(S) reads min sum_gamma |g^(gamma)|^2 / (2 g^(i/2)^2) >= 0, so its margin is set by the zeros.
CC1-type prolate/Sonin estimates, with an error budget of about 1e-3, cannot reach a 5.7e-8 margin.
A certified computation like KWin2 is the realistic route.

**Dropped, per the lead.** The claim that A's negative direction lives in "range(Q_2)". Q_2 has full
numerical rank in the polynomial basis. In the spline basis the overlap was measured with a 1e-40
relative rank threshold, and it grew with L, to 0.94 for the odd negative direction at 0.549. That
measurement is basis-dependent and is not a reduction.

## Reproduction

    cd telperion/research/weil_positivity/one_prime; PY=~/hodge-engine/venv/bin/python
    $PY one_prime.py poly_validate                       # reconcile.py cross-check, nt convergence, zero side
    $PY one_prime.py poly_case L N 1                     # floor, c-interval, controls (records in scratchpad)
    $PY one_prime.py poly_lagscan 24 0.45,0.50,0.549
    # spline appendix: build / analyse / ccplus / tables / extrap / rates / cctable / lagscan (see docstrings)

Nothing here is progress on RH. **conjecture1_proved = False.**

## Addendum (2026-10-11, after review by the Riemann session; restored after the Legendre revision)

- **The window "knows" the prime 2, one-sidedly.** At L = 0.549 positivity survives only for prime locations
  q ∈ [2 − 4.9e-7, 2 + 2.2e-5] in the Legendre basis ([2 − 6.5e-7, 2 + 2.9e-5] in the spline appendix): about 45
  times tighter below 2 than above.
- **One knife edge, seen two ways.** The upper c-margin at L = 0.549 (3.1e-6 in c = √2 log 2 units, i.e. 1.6e-6 in
  w2 = c/2 units; set by the even sector) and the even-sector Schur scalar of the pole reduction (margin 5.7e-8 to −1)
  measure the distance from the same point to the same boundary of the even-sector PSD cone, along two directions
  (raising the prime weight versus the pole functional at fixed weight). They are the same constraint.
- **Decision recorded by the island owner** (`~/rh-team/gates/kwin2_one_prime_decision.md`): no monolithic kernel
  certificate at 2L ≤ 1.098; rungs below L ≈ 1.86 cannot separate zeta from DH, so the extra window carries no
  information about the zeros. Queued: a probe re-emitting L = 1/2 in the split form (hyperplane LDL^T + tail + one
  exact Schur-scalar check) to compare peak memory. This revision adds the binding cost: the Psi_0 minorant gap
  (~1.2e-7, `KWin2_Par12.lean` header) is already twice the whole floor at 0.549, so the minorant must tighten before
  any extension, split or not.
- **E1 correction** stands: the infimum at fixed L is positive (spline floors converge from above like 1/n; the
  Legendre floor at 0.549 is converged to 1%).
