# The Gaussian window: how far an honest hypothesis-free argument can raise lam0 (2026-09-22)

**Status line.** `conjecture1_proved = False`. Nothing in this memo proves RH. It measures the
pieces of an unconditional identity (E6Bridge10/11) and designs a lower bound on one of them. The
script is `telperion/research/gauss_window_numerics.py` (with `gauss_window_extra.py` for the
hybrid and the polynomial LP); its full output is `telperion/research/gauss_window_numerics.log`;
the first 2000 zeros it uses are `telperion/research/zeros2000.json` (mpmath `zetazero`).

**Ten-line summary.**

* The identity `F = P + Arch - Primes` with the brief's normalisation is exact: zero sum against
  prime side agrees to `3e-14` relative at all twelve test points. Nothing to fix.
* The true c-uniform ceiling of ANY argument that bounds the prime side by its l1 size is
  `lam_max(l1) = 0.0115` (argmin at `c = 0`). `P + Arch` itself goes negative at `lam = 0.0127`,
  `Arch` without the pole term at `lam = 0.0058`. Above `0.0127`, `F >= 0` is a cancellation
  between `Arch` and the SIGNED prime side (at `lam = 0.03`, `c = 0`: `Arch/A = -0.42`,
  `Primes/A = -0.48`, `F/A = 2.6e-4`), which no domination argument sees. There is no finite
  `lam_max(sign)`: `min_c F >= 0` at every width tested, as it must be with the zeros on the line.
* Method (a), c-uniform band floors on `Re psi` with sup-of-bump mass caps: `lam0 = 6.3e-5` with
  one band, `3.8e-4` with two (the lead's back-of-envelope), `1.1e-3` with five, `1.6e-3` with ten,
  `2.3e-3` in the many-band limit. The floor quality matters: E6Bridge16's Stirling floor
  `log(r/2) - 20/r^2` caps the method at `8.5e-4`; exact values at the edges are needed for `1e-3`.
* Method (b), c-dependent exact masses per band and a numerical minimum over c: `7.3e-3` (five
  bands), `9.6e-3` (ten), converging to `lam_max(l1)`. Its elementary form (c-cells with
  enlarged-window caps) reaches `8.0e-3` with ten bands and 80 c-cells, `9.7e-3` with twenty bands.
  Its erf-free form loses a further 25 percent.
* Method (c), Binet: the decomposition is exact and the two non-log pieces are harmless
  (`INV <= 1.84 sqrt(lam)`, `|KERNEL| <= 0.0018` at `lam = 1e-3`), but the log piece has no
  closed form against a shifted Gaussian, and the best polynomial-moment lower bound (an LP over
  degree-6 polynomials in `r^2`) loses `0.95` at `lam = 1e-3` where the whole margin is `0.92`. Dead
  as a closed-form route; its by-product, the global floor (B), is worse than Stirling.
* Recommendation: method (a) with eight bands at `lam0 = 1/1000`, margin `0.185` in units of A
  with rigorous-quality floors; section 7 is the inequality chain with all constants. This is a
  factor `10^4` over the current `lam0 = 1e-7`, and a factor 5 to 10 below the honest ceiling
  `0.0115`, which only the hybrid (b') approaches at a formalisation cost an order of magnitude
  larger.

## 1. The identity and its check

With `B(r) = (r - c)^2 e^{-2 lam (r - c)^2}`, `A = 1/(8 sqrt(2 pi) lam^{3/2})`, `M = int B = 2 pi A`,
`psiR(r) = Re psi(1/4 + i r/2)`, `w = 1/sqrt(2 lam)` (the lobe position of the bump):

    F(c, lam) = P + Arch - Primes,
    P        = 2 e^{-2 lam (c^2 - 1/4)} [(c^2 - 1/4) cos(2 lam c) + c sin(2 lam c)]   (= 2 Re gaussTest(i/2), E6Bridge16),
    Arch     = (1/2 pi) int B(r) (psiR(r) - log pi) dr  =  A (<psiR>_B - log pi),
    Primes   = 2 A Sum_{n>=2} Lambda(n) n^{-1/2} (1 - u^2/(4 lam)) e^{-u^2/(8 lam)} cos(c u),  u = log n.

Section 0 of the log: mpmath quadrature (dps 25) for `Arch`, the Lambda sum to `2e5`, the zero sum
over `+-gamma_k`, `k <= 2000`, at `lam in {0.003, 0.01, 0.03}`, `c in {0, 5, 13, 30}`:

```
   lam    c     F zero-sum/A          P/A       Arch/A     Primes/A            RHS/A   rel.diff
 0.003    0     0.7360125433     -0.00165   0.73766246 -7.7399482e-8     0.7360125433   8.21e-17
 0.003   30      1.388159339    0.0265478    1.3616116  2.828182e-8      1.388159339  -8.47e-17
  0.01    0     0.1500394749   -0.0100768   0.13350144 -0.026614806     0.1500394749   3.58e-16
  0.01    5     0.3532524427     0.614256  -0.23579161  0.025211667     0.3532524427   1.68e-16
  0.03    0  0.0002590558961   -0.0528867  -0.42388808   -0.4770338  0.0002590558961  -2.67e-14
  0.03    5    0.05820473663      1.18583  -0.80616734    0.3214562    0.05820473663   1.03e-15
```

Worst relative difference `2.7e-14` (the `lam = 0.03`, `c = 0` row, where `F` is a `1e-3`
cancellation of the two sides). The normalisation in the brief is right as stated; `P` at `c = 0`
is `-e^{lam/2}/2`, negative, which is the only place the pole term ever hurts.

## 2. The true landscape (section 1 of the log)

Minima over `c in [0, 200]` (c step `0.01`, FFT convolution of `psiR` with the bump on an r-grid of
step `0.01`; the zero sum on a c step of `0.1`), all in units of `A`:

```
    lam      w         A  PrimeAbs/A |  min Arch     @c | min P+Arch     @c | min P+Arch-PrimeAbs     @c | min F(zeros)     @c
 0.0001   70.7 4.987e+04   0.000e+00 |    2.0874  65.45 |     2.1602  64.52 |              2.1602  64.52 |   2.1602e+00  64.52
 0.0003   40.8      9597   0.000e+00 |    1.5314  37.83 |     1.6573  36.79 |              1.6573  36.79 |   1.6573e+00  36.79
  0.001   22.4      1577   9.661e-25 |    0.9165  20.76 |     1.1455  19.38 |              1.1455  19.38 |   1.1455e+00  19.38
  0.003   12.9     303.5   7.740e-08 |    0.3466  12.02 |     0.7315   7.32 |              0.7315   7.32 |   7.3153e-01   7.32
   0.01    7.1     49.87   2.661e-02 |   -0.2948   6.62 |     0.1234   0.00 |              0.0968   0.00 |   1.5004e-01   0.00
   0.02    5.0     17.63   2.532e-01 |   -0.6760   4.70 |    -0.2455   0.00 |             -0.4987   0.00 |   7.6679e-03   0.00
   0.03    4.1     9.597   4.770e-01 |   -0.9041   3.85 |    -0.4768   0.00 |             -0.9538   0.00 |   2.5906e-04   0.00
   0.05    3.2      4.46   8.038e-01 |   -1.1974   3.00 |    -0.8038   0.00 |             -1.6076   0.00 |   1.8856e-07   0.00
    0.1    2.2     1.577   1.396e+00 |   -1.6057   2.13 |    -1.3958   0.00 |             -2.7915   0.00 |   1.1226e-15   0.00
```

Thresholds by bisection:

```
lam_max(l1)         = 0.01151   min_c [P + Arch - PrimeAbs] >= 0; argmin c = 0; there min P+Arch = PrimeAbs/A = 0.0502
lam_max(arch)       = 0.01267   min_c [P + Arch] >= 0; argmin c = 0
lam_max(Arch alone) = 0.00578   min_c Arch >= 0 without the pole term; argmin c = 8.68 = 0.93 w
lam_max(sign)       = none      min_c [P + Arch - Primes(c)] = min_c F >= 0 at every lam tested
```

Reading. (i) For `lam <= 3e-3` the worst centre is NOT `c = 0` but `c ~ 0.9 w`: one lobe of the
bump sits on `r = 0` where `psiR(0) = psi(1/4) = -4.227`. The pole term `P/A ~ 2 c^2/A` pulls the
argmin of `P + Arch` inward (`0.87 w` at `1e-4`, `0.57 w` at `3e-3`) and to `c = 0` from `lam = 0.01`
on, where `P(0) = -e^{lam/2}/2` is the only negative pole value. (ii) The l1 prime bound is
invisible below `lam = 5e-3` (`PrimeAbs/A = 1.4e-4` there; `7.7e-8` at `3e-3`), so up to `5e-3`
the whole question is the archimedean average. (iii) The prime side is exactly the n = 2 term to
three digits until `lam = 0.015`. (iv) Beyond `lam_max(arch)` positivity is the `1e-3`-level
cancellation quoted above; it holds because `F` is a sum of nonnegative zero terms, i.e. because
the zeros up to height `c + 7 w ~ 50` are on the line, and for no reason visible on the prime
side. So no hypothesis-free argument of the domination shape reaches `0.013`, let alone the
prime-free window's `0.03` to `0.12`: the Gaussian test's tails carry prime terms whose SIGN
does the work there, and using that sign is using where the zeros are.

## 3. Method (a): c-uniform band bounds (section 2 of the log)

Bands `[r_k, r_{k+1})` in `|r|`, `r_0 = 0`, floors `phi_k = floor(r_k)` with `floor <= psiR`
increasing in `|r|` (`psiR` is increasing in `|r|` termwise from the Zeta23 series, see section 7),
and a c-uniform cap `m(rho) >= sup_c int_{|r| < rho} B(r - c) dr`:

    <psiR>_B >= phi_0 + Sum_{k>=1} (phi_k - phi_{k-1}) (1 - m(r_k)/M),                          (a)

    F/A >= -e^{lam/2}/(2 A) + [right side of (a)] - log pi - PrimeBound(lam).

With the sup cap `m(rho) = min(M, 2 rho sup B)`, `sup B = 1/(2 lam e)`, one has
`m(rho)/M = min(1, kappa sqrt(lam) rho)`, `kappa = 4 sqrt(2/pi)/e = 1.17410`.

**3a. The literal E6Bridge11 and its one-step sharpenings (one band at `R0 = 41`, floors -5 / 2):**

```
E6Bridge11 literal (sup B <= 1/(2 lam), prime bound 64 e^{-(log 2)^2/(16 lam)})   lam0 = 8.7e-07
  + sup B <= 1/(2 lam e)                                                            lam0 = 6.4e-06
  + closed prime bound (n = 2 exact + tail)                                         lam0 = 6.4e-06
  + rearranged window mass                                                          lam0 = 6.5e-06
```

(The Lean file certifies `1e-7` with cruder arithmetic on the same configuration.)

**3b. K optimised bands, sup cap, closed prime bound (certified lam0):**

```
floor                                         K=1          K=2          K=3          K=5         K=10         K=20        K=inf
exact psiR at edges                     6.263e-05    3.818e-04    7.006e-04    1.115e-03    1.585e-03    1.880e-03    2.269e-03
  outer edge / w                         R/w=0.17     R/w=0.44     R/w=0.63     R/w=0.82     R/w=0.99     R/w=1.07     R/w=1.26
E6Bridge11 (-5 / 2 beyond 41)           6.442e-06    (K irrelevant)
Stirling20 + floor -5 (E6Bridge16)      4.318e-05    1.992e-04    3.185e-04    4.604e-04    6.045e-04    6.795e-04    7.899e-04
Stirling20 + psi(1/4) floor             5.435e-05    2.279e-04    3.558e-04    5.055e-04    6.371e-04    7.348e-04    8.475e-04
Binet (B)                               1.164e-05    7.087e-05    1.311e-04    2.140e-04    3.081e-04    3.685e-04    4.442e-04
Stirling (S) 7/24                       3.720e-05    2.820e-04    5.308e-04    8.722e-04    1.269e-03    1.524e-03    1.861e-03
max(B, S)                               6.208e-05    3.575e-04    6.304e-04    9.861e-04    1.388e-03    1.633e-03    1.980e-03
```

Floors: `Stirling20` is E6Bridge16's `psiR(r) >= log(r/2) - 20/r^2` for `r >= 2`; `(B)` and `(S)`
are the survey's Binet floor `(1/2) log(1/16 + r^2/4) - 1/(8|z|^2) - 0.84116` and Stirling-remainder
floor `(1/2) log(1/16 + r^2/4) - (7/24)/|z|^2` (E.3 of LI_FACE_SURVEY); `exact` means the true value
of `psiR` at each edge (obtainable in Lean from the series, section 7).

Reading. The many-band limit with the sup cap is `2.3e-3`, matching the analytic estimate: the
bound is `psiR(R) - log pi - kappa sqrt(lam) int_0^R (psiR(R) - psiR(r)) dr`, and with
`psiR ~ log(r/2)` the integral is `~ R`, so the optimum is `R = 1/(kappa sqrt lam)`, value
`-log(2 kappa sqrt lam) - 1 - log pi >= 0` iff `lam <= 2.5e-3`. The optimal outer edge sits at
`R ~ w`, and the cap there says "up to 83 percent of the mass may lie inside R" while the truth
(next table) is 49 percent; that is the loss of c-uniform caps. Five bands recover half of the
limit, ten bands 70 percent. The Stirling floor with `20/r^2` costs a factor 2.7 at every K: its
error is 40 times the true Stirling remainder, and the inner bands (`r` between 2 and 8) are where
it hurts. `(S)` is nearly as good as exact values; `(B)` alone is poor because its `-0.84` is a
uniform loss.

**3c. Sharper c-uniform caps.** The rearrangement argument (memo section 7, step 4') gives
`sup_c int_{|r|<rho} B(r - c) dr <= 4 int_w^{w + rho/2} x^2 e^{-2 lam x^2} dx` (elementary: the outer
slope of the lobe dominates the inner one, `B(w - d) <= B(w + d)`, plus Jensen for the two half
windows), and an erf-free majorant of that via `e^{-2 lam x^2} <= e^{-1} e^{-4 lam w (x - w)}`:

```
 rho/w  sup(2 rho S)/M   rearr/M  rearr-ef/M  true sup_c/M
  0.30         0.2491    0.2455      0.2462        0.2348
  0.50         0.4151    0.3993      0.4022        0.3543
  0.70         0.5812    0.5399      0.5468        0.4329
  1.00         0.8302    0.7202      0.7358        0.4863
  1.50         1.0000    0.9334      0.9680        0.7877
  2.00         1.0000    1.0000      1.0000        0.9540
```

```
floor (exact psiR)   cap              K=1          K=2          K=3          K=5         K=10         K=20        K=inf
                     rearr      6.321e-05    3.998e-04    7.553e-04    1.243e-03    1.827e-03    2.227e-03    2.732e-03
                     rearr-ef   6.308e-05    3.960e-04    7.440e-04    1.217e-03    1.775e-03    2.155e-03    2.629e-03
                     true sup_c 6.516e-05    6.690e-04    1.324e-03    1.952e-03    2.776e-03    3.340e-03    4.140e-03
```

So the rearranged cap buys 15 to 20 percent in `lam0`, and the ceiling of ANY per-window c-uniform
cap (the true `sup_c` window mass, not elementary) is `4.1e-3`. The gap from `4.1e-3` to
`lam_max(l1) = 11.5e-3` is the loss from bounding each window's mass at its own worst centre
instead of one centre for all windows: that loss is intrinsic to c-uniformity.

## 4. Method (b): c-dependent bands (section 3 of the log)

For each `c`, exact band masses `m_k(c)` (differences of the erf-closed-form cumulative
`G(x) = int_{-inf}^x t^2 e^{-2 lam t^2} dt`), the same floors, the actual pole term `P(c)`, then the
minimum over `c in [0, 200]` (step 0.05):

```
floor                                         K=2          K=3          K=5         K=10         K=20         K=40
exact psiR at edges                     1.343e-03    3.115e-03    7.258e-03    9.569e-03    1.048e-02    1.096e-02
Stirling20 + psi(1/4) floor             5.513e-04    7.790e-04    1.132e-03    1.635e-03    2.098e-03    2.418e-03
Binet (B)                               1.747e-04    3.459e-04    6.546e-04    1.116e-03    1.564e-03    1.862e-03
max(B, S)                               1.165e-03    2.225e-03    4.419e-03    8.845e-03    9.876e-03    1.037e-02
```

At `K = 10` (exact floors) the certified `lam0(b) = 9.57e-3` with edges at
`0.13, 0.28, 0.43, 0.60, 0.77, 0.94, 1.11, 1.29, 1.47, 1.65` times `w` and the minimising centre
`c = 0`; `K -> infinity` recovers `lam_max(l1)`. Method (b) beats (a) by a factor 4 to 6 at equal K
because the window masses are evaluated at the actual centre.

**Erf-free (b).** Replacing each `m_k(c)` by elementary cell bounds (cells split at `x = 0` and
`x = +-w` where `x^2 e^{-2 lam x^2}` is monotone, then `sub` equal parts; on each cell the exact
identity `int x^2 e^{-2 lam x^2} = [-x e^{-2 lam x^2}/(4 lam)] + (1/(4 lam)) int e^{-2 lam x^2}` with
`int_a^b e^{-2 lam x^2}` bracketed by `(b - a) e^{-2 lam b^2}`, `(b - a) - 2 lam (b^3 - a^3)/3` from
below and `(b - a) e^{-2 lam a^2}`, `e^{-2 lam a^2}/(4 lam a)` from above; a lower bound on the
mass is used where the floor is nonnegative, an upper bound where it is negative):

```
  sub  lam0(b, erf-free)  argmin c        (K = 10, same edges as above)
    1          5.915e-03      12.5
    2          6.442e-03      11.0
    4          6.823e-03      10.5
    8          7.057e-03       9.5
   16          7.174e-03       9.0
```

So the erf-free version reproduces (b) to within a factor 1.35 with 16 sub-cells per monotone
piece; it is a rigorous interval quadrature and its cost is proportional to the cell count.

**The hybrid (b'), which is what a Lean proof of (b) would actually be.** The c-dependence has to
be discharged for ALL c, so split `[0, 4 w]` into cells `[c_j, c_{j+1}]` of width `dc` (plus one cell
`[4 w, 200]` and the envelope beyond). On a cell, the bump mass in `|r| < rho` is at most the
centred-bump mass in the enlarged window `[-rho - c_{j+1}, rho - c_j]` (monotone in the window),
and the pole term is at least `2 e^{-2 lam (c_{j+1}^2 - 1/4)} (c_j^2 - 1/4) cos(2 lam c_{j+1})` (its
pieces are monotone on the cell while `2 lam c <= pi/2`). Every quantity is then elementary in the
cell corners, and there is no `min over c` left (section 3c of the log; exact erf caps):

```
floor                              K    dc=0.5w   dc=0.25w    dc=0.1w   dc=0.05w
exact psiR at edges                5  2.947e-04  9.890e-04  2.626e-03  3.918e-03
exact psiR at edges               10  4.880e-04  1.593e-03  4.906e-03  8.020e-03
exact psiR at edges               20  6.367e-04  2.248e-03  7.815e-03  9.660e-03
Stirling (S) 7/24                 10  1.947e-04  7.788e-04  2.335e-03  3.646e-03
Stirling (S) 7/24                 20  2.598e-04  1.100e-03  3.633e-03  5.990e-03
Stirling20 + psi(1/4) floor       20  3.389e-04  7.540e-04  1.342e-03  1.680e-03
```

Cell width matters more than band count: the enlarged window loses `dc sup B` of mass per cap,
which is `dc/w` of `M` times `e^{-1}`, so `dc = 0.05 w` costs about 2 percent per cap. With
`K = 10`, `dc = 0.05 w` (80 cells) the certificate is 80 x 10 caps, each two erf values, or, erf-free,
each a handful of exponentials at rational points; `lam0 = 8.0e-3`. With `K = 20` it is `9.7e-3`, within
16 percent of the ceiling.

## 5. Method (c): Binet (section 4 of the log)

With `phi(t) = 1/(e^t - 1) - 1/t + 1/2` and `f_0(u) = A (1 - u^2/(4 lam)) e^{-u^2/(8 lam)}`,

    <psiR>_B = LOG - INV - KERNEL,
    LOG    = (1/M) int B(r - c) (1/2) log(1/16 + r^2/4) dr,
    INV    = (1/M) int B(r - c) / (8 (1/16 + r^2/4)) dr,
    KERNEL = (2/M) int_0^inf phi(2u) e^{-u/2} [2 pi f_0(u) cos(c u)] du,

(`int B(r - c) cos(r u) dr = 2 pi f_0(u) cos(c u)`, E6Bridge16.fourier_autocorrGauss at real
frequency), checked against the direct average to `3e-10` at 20 points:

```
    lam      c   <psiR>_B      LOG      INV     KERNEL |KERNEL|<=
  0.001    0.0    2.43220   2.4329   0.0019   -0.00123    0.00179
  0.001   22.4    2.06672   2.1244   0.0564    0.00126    0.00179
  0.003   12.9    1.49652   1.5954   0.0953    0.00361    0.00513
   0.01    7.1    0.85474   1.0319   0.1662    0.01100    0.01559
   0.03    4.1    0.24484   0.5413   0.2680    0.02846    0.04018
```

`INV` has the closed c-uniform bound `sup B . int 2/(1 + 4 r^2) dr / M = (2/e) sqrt(2 pi lam) =
1.844 sqrt(lam)` (an arctan integral; `0.058` at `1e-3`). `|KERNEL|` is bounded by the lam-only
column, `0.0018` at `1e-3` (the Faddeeva series of the survey is not needed: `phi(2u) <= u/6`,
`e^{-u/2} <= 1`, and `(1/3) int_0^inf u |1 - u^2/(4 lam)| e^{-u^2/(8 lam)} du = (4 lam/3)(4 e^{-1/2} - 1)`
in closed form, so `|KERNEL| <= 1.90 lam`). Both pieces are harmless.

Everything is in `LOG`. It has no closed form for `c != 0` (and the `c = 0` value is an erfc in the
parameter `1/16`). Lower bounds of the concave `log(1/16 + x/4)`, `x = r^2`, with closed-form
Gaussian moments must be polynomials in `x` (a lower bound of `log` on `[0, inf)` that is a
polynomial has negative leading coefficient, so it is only useful while the bump mass beyond the
fitting range is negligible), and the natural one-chord-plus-constant floor
`min(l(x), log(1/16 + x2/4))` is not closed-form because of the `min`; replacing `(y)_+` by
`y^2/(4 delta) + delta` (the only polynomial way) gives, optimised over the chord and `delta`:

```
    lam  best x2/w^2  delta lam  LOG bound c=0  true LOG c=0
 0.0001        1.276      0.311        -0.3726        3.5837
  0.001        1.283      0.311        -0.6025        2.4329
  0.003        1.289      0.311        -0.7121        1.8845
```

a loss of 3 to 4 units. The best possible polynomial-moment bound (section 4c: a linear programme
over degree-d polynomials `p(x)` with `p <= log(1/16 + x/4)` on `[0, (15 w)^2]`, maximising the
minimum over `c in [0, 3 w]` of `E_c[p(r^2)]`, all moments closed-form in c):

```
    lam  deg  (1/2)min E_c[p]  true min LOG    loss
 0.0003    6           1.5064        2.7080   1.202
  0.001    4           0.9717        2.1186   1.147
  0.001    6           1.1655        2.1186   0.953
  0.003    6           0.8543        1.5892   0.735
```

(degree 8 and above is numerically ill-conditioned in this LP, but the trend is flat). The loss
`0.95` at `lam = 1e-3` equals the entire margin `min_c Arch/A = 0.92` there: a closed-form,
c-uniform Binet argument certifies nothing near `1e-3`, and its c-dependent version still needs the
envelope for large `c` since every polynomial bound tends to `-inf` in `c`. What Binet does give is
the pointwise floor (B), and the table in section 3 shows (B) is beaten by the Stirling remainder
floor (S) and by exact values. Binet's formula for `psi` is not on the island (Zeta23 has the
vertical-line series and a Stirling bound), so (B) would also be the most expensive floor to
formalise. Verdict: method (c) is not a route; keep Binet as a numerical cross-check only.

## 6. Ranking: certified lam0 against formalisation cost

```
method                                        lam0 certified   new Lean (est.)   new lemmas needed
E6Bridge11 as is                                     1e-7            0            -
(a) K=1, sup/e cap, exact pole                     6.3e-5          ~150          pole sign lemma; sup B <= 1/(2 lam e)
(a) K=5, exact floors                              1.1e-3          ~600          + psiR monotone in |r|; 5 edge values from the series; K-band layer cake
(a) K=8, exact floors  [RECOMMENDED]               1.0e-3 (margin 0.185) ~750     same, 8 edge values
(a) K=12, exact floors                             1.5e-3 (margin 0.05)  ~900     same, 12 edge values
(a) K=inf, rearranged cap                          2.7e-3          ~1200         + rearrangement window lemma (elementary); many edges
(a) ceiling with any per-window c-uniform cap      4.1e-3          not elementary (true sup_c mass)
(b') hybrid c-cells, K=10, dc=0.05w, erf-free      ~6e-3           ~2500 or a tactic   + cell caps, cell pole floors, ~800 exp evaluations at rationals
(b') hybrid, K=20, dc=0.05w, exact erf             9.7e-3          erf not available in Mathlib numerics
ceiling of any l1-prime-side argument             11.5e-3          -
ceiling of any argument of this shape             12.7e-3          -               (P + Arch < 0 beyond; sign of primes needed)
(c) Binet closed form                               < 1e-4          ~800 (Binet itself)   not worth it
```

Line-count estimates are relative to E6Bridge11's existing `re_archSide_ge` (about 200 lines for
its one-band version) and its prime bound; they exclude nothing hidden, but they are estimates.

The recommendation is (a) with eight bands at `lam0 = 1/1000`: it is the last step whose
ingredients are all already on the island in some form (series on vertical lines, Stirling,
Gaussian moment, the E6Bridge16 evaluated pole term, the E6Bridge11 prime bound is enough), it has
a margin of `0.185` (so every constant may be rounded to three digits), and the next factor of 2
costs the rearrangement lemma plus twenty edges, while the next factor of 5 costs the hybrid's
computational certificate. `lam0 = 1.2e-3` with the same eight-band shape has margin `0.09`;
`1.5e-3` needs twelve bands (margin `0.05`); `2e-3` is out of reach for (a) with fewer than about
forty bands, and `2.3e-3` is its limit.

## 7. The inequality chain for the recommended method (a spec)

Fixed constants: `lam0 = 1/1000`; edges (absolute, not scaled) `r_1..r_8 = 0.6, 1.4, 2.9, 5.1, 8.0,
11.6, 16.0, 21.1`; `kappa = 4 sqrt(2/pi)/e`. Everything below is for `0 < lam <= lam0` and every
real `c`; every step is monotone in `lam` in the right direction (the caps `kappa sqrt(lam) r_k`,
the pole `-e^{lam/2}/(2A)` and the prime bound all decrease as `lam` decreases), so the numeric
evaluation at `lam = lam0` is the only one needed. Units of `A` throughout, i.e. divide the
`archSide - primeSide` real part by `gaussA lam > 0`.

**Step 1 (pole term, new lemma `pole_floor`).** By E6Bridge16 `weilKernel_zero_eq_gaussTest`,
`weilKernel_one_eq_gaussTest`, the two pole terms sum to
`P = 2 e^{-2 lam (c^2 - 1/4)} [(c^2 - 1/4) cos(2 lam c) + c sin(2 lam c)]`. Claim: `P >= -e^{lam/2}/2`
for all `c` when `lam <= 1/2`. Proof: if `2 lam |c| <= pi/2` then `cos(2 lam c) >= 0`,
`c sin(2 lam c) >= 0`, `(c^2 - 1/4) cos(2 lam c) >= -1/4`, and `e^{-2 lam (c^2 - 1/4)} <= e^{lam/2}`,
so `P >= -e^{lam/2}/2`. If `2 lam |c| > pi/2` then `x := 2 lam c^2 > pi^2/(8 lam) >= pi^2/4` and
`|P| <= 2 e^{lam/2} e^{-x} (c^2 + |c| + 1/4) <= 2 e^{lam/2} e^{-x} . 2 c^2 = 2 e^{lam/2} x e^{-x}/lam`
(using `|c| > pi/(4 lam) >= 1.3`), with `x e^{-x} <= e^{-x/2}` for all `x >= 0`; so
`|P| <= (2/lam) e^{lam/2} e^{-pi^2/(16 lam)} <= e^{lam/2}/2` for every `lam <= 1/5` (at `lam = 1/5`
the middle expression is `0.46`; numerically `min_c P = -e^{lam/2}/2` holds to `lam = 0.3`). At
`lam0` the second case is `e^{-617}`. State the lemma for `lam <= 1/5`. Hence `P/A >= -e^{lam/2}/(2 A) = -4 sqrt(2 pi) lam^{3/2} e^{lam/2} >= -3.2e-4` at `lam0`.
E6Bridge11's own `norm_weilKernel_zero_le` (`2 A e^{2 lam} sqrt(32 pi lam)` each) would cost `1.27`
here and must NOT be used.

**Step 2 (prime side, existing).** E6Bridge11 `norm_primeSide_le`: `|Primes|/A <= 64 e^{-(log 2)^2/(16 lam)}
<= 5.9e-12` at `lam0` (valid since `log 2/(16 lam) >= 2`). Nothing new; the sharper closed form
(n = 2 term plus tail, `prime_abs_closed_form` in the script) is only needed above `lam ~ 3e-3`.

**Step 3 (sup of the bump, three lines).** `bumpR c lam r <= 1/(2 lam e)`: with `y = 2 lam (r - c)^2`,
`y e^{-y} <= e^{-1}` from `y <= e^{y - 1}` (`Real.add_one_le_exp`). E6Bridge11's `bumpR_le` has
`1/(2 lam)`; the factor `e` is a factor 7 in `lam0` for one band.

**Step 4 (window mass, parametrised existing lemma).** For every `rho > 0` and every `c`:
`int_{|r| < rho} bumpR c lam r dr <= 2 rho/(2 lam e)` (E6Bridge11 `setIntegral_bumpR_le` with `R0`
replaced by `rho` and step 3). In units of `M = 2 pi A`: `<= kappa sqrt(lam) rho`,
`kappa sqrt(lam0) = 0.037128`.

*(Step 4', optional, for the rearranged cap: `int_{|r|<rho} bumpR c lam r dr <= 4 int_w^{w + rho/2}
x^2 e^{-2 lam x^2} dx`. Ingredients: `B(w - d) <= B(w + d)` for `0 <= d < w`, i.e.
`log(1 + s) - log(1 - s) >= 2 s` on `[0, 1)`; a window `[a, a + l]` in `[0, inf)` has
`int <= 2 int_w^{w + l/2} B` (split at `w`, reflect the inner part, Jensen for the concave
`p -> int_0^p B(w + .)`); a window of length `2 rho` on the line splits into two such and Jensen
again. Erf-free upper bound of the right side: `[-x e^{-2 lam x^2}/(4 lam)]_w^{w + rho/2} +
(w/(8 lam e)) (1 - e^{-rho/w})`. Not needed for the recommended target.)*

**Step 5 (monotonicity of `psiR` in `|r|`, new lemma `psiR_mono`).** From Zeta23
`re_digamma_vertical` with `a = 1/4`, `t = r/2`: `psiR(r) = -gamma - a/(a^2 + t^2) + Sum_{n>=0} f_n(t)`,
`f_n(t) = 1/(n+1) - (n + 1 + a)/((n + 1 + a)^2 + t^2)`. Each `f_n` and `-a/(a^2 + t^2)` is increasing in
`t^2`, each `f_n >= 0` (E6Bridge11 already proves this for the `-5` bound), so `psiR` is increasing
in `|r|` (`tsum_le_tsum` with the summability already used in `integrable_bumpR_mul_psiR`).

**Step 6 (edge values, new lemma `psiR_series_lower` plus eight instances).** With `N = 40`:
`f_n` is decreasing in `n` for fixed `t` (its derivative is `-1/(x+1)^2 + ((x+b)^2 - t^2)/((x+b)^2 + t^2)^2`
with `b = 5/4 > 1`, negative in both regimes `x + b <= t` and `x + b > t`), hence
`Sum_{n>=N} f_n >= int_N^inf f(x) dx = (1/2) log((N + b)^2 + t^2) - log(N + 1)`, and

    psiR(r) >= -gamma_up - a/(a^2 + t^2) + Sum_{n<N} f_n(t) + (1/2) log(((N + b)^2 + t^2)/(N + 1)^2),

with `gamma_up = 0.58221 >= eulerMascheroniSeq' 100 = H_100 - log 100 > gamma` (Mathlib
`eulerMascheroniConstant_lt_eulerMascheroniSeq'`; the cruder `gamma < 2/3` loses `0.085` on every
floor and the margin drops to `0.10`, still positive) and `log X >= 1 - 1/X` for the last term
(loses `< 0.003`). The partial sum is 40 rationals per edge (`norm_num`). Rigorous-quality values
(the script's `psiR_series_lower`, N = 40, gamma_up = 0.58221, rounded DOWN to 4 decimals) against
the exact ones:

```
    r_k     0      0.6      1.4      2.9      5.1      8.0     11.6     16.0     21.1
 phi_k  -4.2275  -1.8148  -0.4243   0.3611   0.9294   1.3805   1.7522   2.0738   2.3502   (rigorous lower bounds)
 exact  -4.2275  -1.8097  -0.4192   0.3662   0.9345   1.3856   1.7575   2.0793   2.3560
```

`phi_0 = psi(1/4) = -gamma - pi/2 - 3 log 2 = -4.22745` (Gauss's digamma theorem at 1/4; if not
on the island, the `-5` of E6Bridge11 costs `0.77 x 0.0223 = 0.017` of margin, acceptable).
Alternative for the outer edges: E6Bridge16's `psiR_ge_log'` gives `1.0738, 1.6092, 2.0013, 2.3112`
at `8.0, 11.6, 16.0, 21.1`, costing `0.31 x (1 - 0.297) + 0.15 x ... = 0.36` of margin in total:
too much; use the series for all eight.

**Step 7 (layer cake, generalises `integral_bumpR_mul_psiR_ge`).** Define the step function
`L(r) = phi_0 + Sum_{k=1}^{8} (phi_k - phi_{k-1}) 1[|r| >= r_k]`. By steps 5 and 6, `L <= psiR`
pointwise. Integrating against `bumpR >= 0` and using step 4 for each of the eight windows
(`phi_k - phi_{k-1} > 0`):

    int bumpR psiR >= int bumpR L = phi_0 M + Sum_k (phi_k - phi_{k-1}) (M - int_{|r|<r_k} bumpR)
                  >= M [ phi_0 + Sum_k (phi_k - phi_{k-1}) (1 - kappa sqrt(lam) r_k) ].

At `lam0` with the rigorous `phi_k` and `kappa sqrt(lam0) r_k = 0.02228, 0.05198, 0.10767, 0.18935,
0.29703, 0.43069, 0.59405, 0.78341`:

    <psiR>_B >= 1.3303.

**Step 8 (assembly, as `re_archSide_ge` then `re_weilForm_gauss_nonneg`).**

    F/A >= P/A + <psiR>_B - log pi - |Primes|/A
        >= -0.00032 + 1.3303 - 1.14473 - 6e-12 = 0.1852 > 0.

(`log pi <= 1.14473`: `pi < 3.1416` and `log 3.1416 < 1.14473`, or `log pi <= 2 log 2 < 1.3863`
costs `0.24` and kills the margin: use the sharper one.) Every quantity is a rational or a value of
`exp`/`log` at a rational, so the final inequality is `norm_num` after the eight edge lemmas. For
`lam < lam0` the same fixed edges give a larger bound (the script checks `0.48` at `5e-4`, `0.88`
at `1e-4`, `1.20` at `1e-7`), so the theorem is `0 < lam <= 1/1000 -> 0 <= F(c, lam)` for every `c`,
replacing `lam0 = 1e-7`.

**What is new relative to the island:** `pole_floor` (step 1, ~60 lines), `bumpR_le'` (step 3, ~10),
`setIntegral_bumpR_le'` (step 4, parametrised, ~20), `psiR_mono` (step 5, ~50), `psiR_series_lower`
(step 6, generic ~80, plus eight `norm_num` instances ~20 each), the eight-window layer cake (step 7,
~150), assembly (~80). About 600 to 750 lines; no new analysis beyond what E6Bridge11/16 and Zeta23
already contain.

## 8. Ceilings, stated honestly

* No c-uniform-in-the-prime-side argument passes `lam_max(l1) = 0.0115`: at that width, with
  `c = 0`, `P + Arch` equals the l1 prime size exactly and is smaller beyond.
* No argument of the shape `P + Arch - (something about the prime side that does not use the
  zeros)` passes `lam_max(arch) = 0.0127`: beyond it `P + Arch < 0` at `c = 0` and positivity is a
  cancellation with the signed prime side at the `1e-3` level by `lam = 0.03` (`F/A = 2.6e-4`
  against `|Arch/A| = 0.42`). That cancellation is `F = Sum over zeros of nonnegative terms`, i.e. it
  is where the zeros are; the correct hypothesis-free statement there is the ladder's (positivity
  for `|c| <= C` at width `lam` given the zeros up to height `C + 7 w` on the line), not a Gaussian
  window theorem. The prime-free window's `0.03 to 0.12` is not reachable by this family of tests:
  the Gaussian tails carry `e^{-(log 2)^2/(8 lam)}` of prime mass with a c-dependent sign.
* Within the honest region, c-uniform window caps are capped at `4.1e-3` (true `sup_c` masses,
  not elementary) and at `2.3e-3` with the elementary sup cap; c-dependent (hybrid) certificates
  approach `0.0115` at a cost that grows like the number of c-cells times the number of bands.
* The recommended `lam0 = 1e-3` is a factor `10^4` over the current theorem and a factor 11.5 below
  the ceiling; the gap is bought only by the hybrid's computational certificate.

`conjecture1_proved = False`. Nothing here proves RH.
