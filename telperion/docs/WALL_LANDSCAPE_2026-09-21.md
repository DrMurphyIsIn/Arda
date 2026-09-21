# Wall landscape: F(c, lam) measured, and the bandwidth barrier (2026-09-21)

> **ERRATUM (2026-09-21, scoped; see WALL_ASSAULT_SEAMS_RECONCILIATION_2026-09-21.md, E2/E3):** the barrier table in section 3 normalises the truncation error against f(0), which at lam = 4 is a relative precision of ~1.6e-6, far stricter than certification (tail <= F itself) needs; the headline Lam_max = 2 is an artefact of that choice. Corrected cost law and table in the reconciliation: honest Lam_max under a 1e12 sieve is ~5 (full c-grid at height 1e4) to ~6 (height 1e12). The qualitative conclusions (y0 rises with height; bandwidth, not precision, is the obstacle) stand.


Script: `telperion/examples/rvm_bridge/wall_landscape.py` (`--quick` 11 s, full 51 s; results json in the wall scratch dir).
Measures only.  No Lean.  Real zeros (flint, on the line to working precision); nothing is claimed about the true zero set
beyond the computed windows.  conjecture1_proved = False.

## Object and formula (verified)

F(c, lam) = Re sum_rho m(rho) G(gammaOf rho), G(z) = (z-c)^2 e^{-2 lam (z-c)^2}, both images +t, -t of every zero.
Explicit formula: F = pole + psi - f(0) log pi - prime with pole = 2 Re G(i/2), psi = (1/2pi) int G(r) Re digamma(1/4 + ir/2) dr,
prime = sum Lambda(n) n^{-1/2} (f(log n) + f(-log n)).  Closed form of f = phi * phi~:

    f(u) = e^{-icu} f0(u),  f0(u) = A (1 - u^2/(4 lam)) e^{-u^2/(8 lam)},  A = f(0) = 1/(8 sqrt(2 pi) lam^{3/2}),

so prime = 2 sum Lambda(n) n^{-1/2} cos(c log n) f0(log n).  Checks: f0 vs direct convolution 3.4e-13; paperFT f vs G at strip
points 9e-27 (mpmath); scipy complex digamma vs mpmath 6e-16; psi quadrature (composite Gauss-Legendre, panels <= 1 wide
because digamma has a pole 0.5 off the real axis) 8e-13 relative.

## 1. Landscape (10 c x 13 lam = 130 cells)

Zero side vs arch - prime agree on all 90 cells where the prime side is directly summable (lam <= 2, n <= 1e8):
median relative difference 2.7e-15; worst 2.9e-14 for lam <= 0.05, 3.6e-13 at 0.2, 2.7e-12 at 0.5, 2.0e-12 at 1 (N = 1e8),
2.5e-4 at lam = 2 (prime tail bound 3.2e-4 f(0): the barrier is already visible at lam = 2).  For lam >= 5 the prime side
is INFERRED as arch - F_zero (no independent check possible: n up to e^{2 lam + ...} would be needed).
Sign: F_zero >= 0 in every cell (as it must be: every image is real).  arch - prime_direct < 0 in 5 cells, all with F_zero
= 0 to double precision and |arch - prime| <= the prime tail bound (c = 0, 5 at lam 0.2/1/2): tail artifacts, not bugs.

Selected rows (F, pole, psi, -f(0) log pi, prime):

| c | lam | F | pole | psi | -f0 log pi | prime |
|---|---|---|---|---|---|---|
| 0 | 0.005 | 67.46 | -0.501 | 229.4 | -161.5 | -0.0193 |
| 0 | 10 | 0 | -74.2 | -0.0053 | -0.0018 | -74.21* (pole e^{lam/2}/2 vs prime sum out to n ~ e^{2 lam}) |
| 14.1347 | 5 | 6.3e-10 | 0 | 8.7e-3 | -5.1e-3 | 3.61e-3* (c on a zero: prime = arch) |
| 100 | 1 | 0.1428 | 0 | 0.1951 | -0.0571 | -0.0048 |
| 100 | 2 | 7.46e-3 | 0 | 0.0690 | -0.0202 | 0.0413 (direct, 2 digits) |
| 1e4 | 1 | 0.4388 | 0 | 0.4247 | -0.0571 | -0.0711 |
| 1e4 | 50 | 2.79e-3 | 0 | 1.20e-3 | -1.6e-4 | -1.75e-3* |

(* inferred; rows c = 500, 5000 and lam 0.05..0.5 omitted, all in the json.)  For c >> 1 the pole term vanishes and
arch = f(0) (log(c/2pi) + o(1)); at c = 0 the pole -(1/2) e^{lam/2} dominates for lam >= 5, arch < 0 for lam >= 0.02.

Small-lam mechanism, |prime|/arch (direct cells; '-' = arch <= 0; c = 5, 500, 5000 in the log: 0.018, >= 2, >= 2):

| c | 0.005 | 0.01 | 0.02 | 0.05 | 0.1 | 0.2 | 0.5 | 1 | 2 | first >1% / >10% / >50% at lam | lam0(c) |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 0 | 2.9e-4 | 0.22 | - | - | - | - | - | - | - | 0.01/0.01/none | 0.011 |
| 14.13 | 1.8e-4 | 0.038 | 0.34 | 0.88 | 1.00 | 1.00 | 1.00 | 1.00 | 1.00 | 0.01/0.02/0.05 | 0.026 |
| 20 | 3.9e-5 | 0.007 | 0.051 | 0.20 | 0.42 | 0.072 | 1.25 | 1.24 | 0.22 | 0.02/0.05/0.5 | 0.274 |
| 50 | 6.7e-5 | 0.013 | 0.12 | 0.18 | 0.032 | 0.032 | 0.58 | 0.54 | 0.14 | 0.01/0.02/0.5 | 0.418 |
| 100 | 4.9e-5 | 0.009 | 0.083 | 0.044 | 0.11 | 0.12 | 0.68 | 0.035 | 0.85 | 0.02/0.1/0.5 | 0.320 |
| 1000 | 1.1e-5 | 0.002 | 0.019 | 0.001 | 0.056 | 0.063 | 4e-4 | 0.31 | 0.52 | 0.02/1/2 | 1.418 |
| 1e4 | 8.1e-6 | 0.002 | 0.013 | 0.025 | 0.12 | 0.11 | 0.081 | 0.19 | 0.096 | 0.02/0.1/none | >= 2 (grid top) |

lam0(c) := sup{lam : arch > 0 and |prime| + tail <= arch/2 for all lam' <= lam} (200-point log grid, 0.001..2).
It is NOT c-uniform in the region c <= 100: 0.01-0.03 for c <= 14 (arch turns negative), 0.27-0.42 for c = 20-100.
For c >= 500 the measured lam0 is >= 1.4-2 (grid-limited) and looks flat, but that rests on cos(c log n) cancellation
in the actual prime sum.  The c-UNIFORM envelope P_abs(lam) = 2 sum Lambda(n) n^{-1/2} |f0(log n)| (what a certificate
valid for every c would use) gives P_abs/f(0) = 1.4e-4, 0.027, 0.25, 0.80, 1.40, 3.04, 8.7, 23.7, 89.6 at lam = 0.005 ...
2, so arch/2 >= P_abs needs log(c/2pi) >= 2 P_abs/f(0): c >= 10 at lam 0.02, 31 at 0.05, 102 at 0.1, 2.7e3 at 0.2,
2.4e8 at 0.5, 2.5e21 at lam = 1.  The uniform small-lam region is lam <~ 0.1 (any c >= 100), lam <~ 0.2 (c >= 3000).

## 2. Near-zero regime (lam >= 1)

Omitted mass F - F_D (near sum over |t - c| <= D) is below the strip tail bound tail_D = e^{lam/2} sum_{|t-c|>D}
((t-c)^2 + 1/4) e^{-2 lam (t-c)^2} in all 192 (c, lam, D) cells.  Typical (c = 1e4): lam = 1: D=1 9.7e-2 / bound 1.9e-1,
D=2 1.6e-4 / 2.8e-4, D=5 0 / 1.9e-23; lam = 2: D=1 6.7e-3 / 2.2e-2, D=2 4.9e-9 / 1.4e-8; lam = 5: D=1 2.4e-6 / 3.5e-5,
D=2 0 / 1.8e-21; lam >= 10: D=1 4e-12 / 8e-10, D >= 2 below 1e-40.  D = 50 is exact at every lam >= 1.
The bound is loose by a factor 2-15 at D = 1 (the e^{lam/2} strip allowance) and tight within 2x at D = 2.

lam1(c, D) = smallest lam beyond which the certified near part beats tail_D for all larger lam (log grid 0.05..200):

| c | D=2: near sum / largest term / smallest term | D=5: sum / largest / smallest | nearest gap |
|---|---|---|---|
| 20 | 0.074 / 0.074 / 0.074 | 0.074 / 0.074 / 0.074 | 1.02 |
| 100 | 0.092 / 0.112 / 0.118 | 0.05 / 0.053 / never | 1.17 |
| 1000 | 0.189 / 0.264 / 0.5 | 0.05 / 0.051 / never | 0.21 |
| 1e4 | 0.140 / 0.243 / never | 0.05 / 0.061 / never | 0.065 |

So with D = 2 the near SUM beats the strip tail for every lam >= 0.27 (all c tested), with D = 5 for every lam >= 0.06;
the "smallest single certified term" reading is hopeless (a zero just inside D loses to one just outside) and should not
be the instrument's criterion.  The ladder region therefore starts at lam1 ~ 0.3 (D = 2) or ~ 0.1 (D = 5).

## 3. The barrier

Exact prime cutoff.  Term envelope Lambda(n) n^{-1/2} |f0(log n)| ~ e^{u/2} (u^2/4 lam) A e^{-u^2/8 lam} =
A e^{lam/2} (u^2/4 lam) e^{-(u - 2 lam)^2/(8 lam)}: the n^{-1/2} against the prime density e^u shifts the Gaussian centre
to u = 2 lam.  So log N(lam, eps) = 2 lam + sqrt(8 lam (log(1/eps) + lam/2 + log terms)), not sqrt(8 lam log(1/eps)).
N solves tail bound (Rosser-Schoenfeld psi(x) <= 1.04 x, Abel summation) = eps f(0):

| lam | eps=1e-3 | eps=1e-10 | eps=1e-30 | naive exp(sqrt(8 lam log 1e10)) |
|---|---|---|---|---|
| 0.1 | 55 | 139 | 2.8e3 | 73 |
| 0.5 | 2.4e3 | 1.2e5 | 7.4e7 | 1.5e4 |
| 1 | 1.3e5 | 2.0e7 | 2.7e11 (heroic) | 7.8e5 |
| 2 | 5.2e7 | 9.4e10 (heroic) | 5.7e16 (impossible) | 2.2e8 |
| 4 | 2.9e12 (impossible) | 7.4e16 | 8.1e24 | 6.2e11 |

Sieve-feasible (n <= 1e9): lam <= 2 at 1e-3, lam <= 1 at 1e-10.  Heroic (1e12): lam = 2 at 1e-10, nothing at lam >= 4.
Lam_max = 2 is the honest bandwidth ceiling; Lam_max = 4 needs 3e12 terms even at three digits.

O2 crossover in these coordinates.  lam*(y, x1) = log(x1^2/(2 y^2)) / (2 (x1^2 + y^2)); y0 solves lam*(y0, x1) = Lam_max
with x1 = 2 pi / log(c/2pi) (model), and against real neighbours (replace-mode quadruple at the ordinate of the zero
nearest c, c scanned over t0 +- 1 step 0.005, lam log grid up to Lam_max; c = 1e6, 1e12 use the 1e4 window rescaled to
the mean gap: PROXY).  'signal' = most negative F at y = 1.5 y0 (absolute accuracy the prime side would need).

| c | x1 | y0 model, Lam = 1 / 2 / 4 / 8 | y0 real, Lam = 1 / 2 / 4 / 8 | signal at 1.5 y0, Lam = 2 |
|---|---|---|---|---|
| 100 | 2.27 | 0.0093 / 1e-4 / 1e-8 / 1e-16 | 0.0036 / <1e-4 / <1e-6 / <1e-6 | -1.4e-10 |
| 1e4 | 0.852 | 0.271 / 0.136 / 0.033 / 0.0018 | 0.392 / 0.228 / 0.101 / 0.026 | -0.24 |
| 1e6 | 0.525 | 0.263 / 0.198 / 0.117 / 0.041 | 0.435 / 0.287 / 0.179 / 0.090 (PROXY) | -0.54 |
| 1e12 | 0.244 | 0.158 / 0.147 / 0.127 / 0.099 | none (>0.5) / 0.348 / 0.222 / 0.145 (PROXY) | -1.2 |

Reading.  The nearest-neighbour model is right at c = 100 (gaps 2.3: a Gaussian of width 0.7 isolates one zero and any
y > 0.01 flips the sign at lam <= 1) but wrong at height: as gaps shrink below the Gaussian width 1/sqrt(2 lam), several
on-line zeros sit inside the window and their positive mass must be beaten by 2 y^2 e^{2 lam y^2}, so y0 RISES with c.
At the feasible ceiling Lam_max = 2: y0 = 0.23 (c = 1e4), 0.29 (1e6), 0.35 (1e12); at Lam_max = 1: 0.39, 0.44, none.
Landau-Widom barrier in Gaussian coordinates: log N >= 2 lam + sqrt(8 lam log(1/eps)) forces lam <= 2, i.e. t-resolution
1/sqrt(2 lam) >= 0.5, and with mean gap 2 pi/log(c/2pi) -> 0 the number of zeros per resolution cell grows like
log c / (4 pi); the detectable off-line distance climbs from 0.23 at height 1e4 to ~0.35 at 1e12 and reaches the strip
edge 0.5 for Lam_max = 1 by height ~1e12.  Prime-side positivity certificates localise zeros only at low height; at the
heights where localisation would matter they do no better than the strip, which is the expected answer.  The precision
needed (signal 0.1-1) is not the obstacle; the bandwidth is.

## 4. The quadrant

    lam
     50 |  R R R R R R R R L L L L L L L L L L L L L L L L L L |  R = RESIDUAL (the Wall)
     10 |  R R R R R R R R L L L L L L L L L L L L L L L L L L |  L = LADDER-CERTIFIED: c <= T - D, lam >= lam1 ~ 0.3
      2 |  R R R R R R R R L L L L L L L L L L L L L L L L L L |      (D = 2; near sum beats strip tail; needs zeros)
      1 |  R R R R R R R R L L L L L L L L L L L L L L L L L L |  - - - prime side directly summable below lam ~ 2
    0.3 |  R R R R R R R R L L L L L L L L L L L L L L L L L L |      (n <= 1e8; independent check of F to 1e-12 at lam 1)
    0.1 |  R R R U U U U U U U U U U U U U U U U U U U U U U U |  U = UNCONDITIONAL: |prime| <= arch/2 with the c-uniform
   0.02 |  R U U U U U U U U U U U U U U U U U U U U U U U U U |      envelope; lam0 ~ 0.02 (c >= 10), 0.1 (c >= 100),
  0.005 |  U U U U U U U U U U U U U U U U U U U U U U U U U U |      0.2 (c >= 3e3); NOT reaching lam1 for any c
        +----------------------------------------------------
          0  5 14 20 50 1e2 1e3 1e4 ... T=3e12 (verified) ->  c     (c > T: only U survives; everything above it is R)

The gap between U (lam <~ 0.1-0.2) and L (lam >~ 0.3) is a factor 2-3 in lam at every c <= T: the two regions do
NOT overlap on the c-uniform reading; they touch only on the measured (non-uniform) lam0 for c >= 500.  Beyond T the
whole band lam > lam0 is the Wall, and the barrier (lam <= 2 for prime numerics) is irrelevant there: no certificate of
any bandwidth reaches c > T without zero data.

## What the numerics cannot establish

- Nothing about zeros beyond the cached windows (t <= 2515, 4880-5120, 9486-10508); c = 1e6, 1e12 rows are a rescaled proxy.
- That lam0(c) >= 1.4 for c >= 500 holds for all c: it is measured on 4 values and rests on cos(c log n) cancellation.
- The prime side for lam >= 5 (inferred, not computed); the lam = 2 column is 4 digits at best.
- Any statement about F for c > 3e12, or any RH claim: F >= 0 is checked, not proved, and only on 130 cells.
