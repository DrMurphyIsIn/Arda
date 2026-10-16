# Pitch 1: Davenport-Heilbronn against its Euler-product sibling (2026-10-15/16)

**Status: a numerical exploration, not a proof. Nothing here is progress on RH. `conjecture1_proved = False`.**
Finite-window Weil positivity is not RH. One non-Euler example (DH), two windows (a = 2, 3), float64 for
everything except the archimedean columns (30 digits) and the explicit-formula validation (30 digits).

Code: `sparring.py` (build / validate / analyse), `negdirs.py` (where every negative direction sits).
Tables: `results/`. Logs: `logs/`. Imports, without editing, `../../weil_positivity/weil_form.py` and
`dh_control.py`.

## The control that was missing

`weil_positivity/dh_control.py` showed DH's Weil form going negative at its off-line zero
0.8085 + 85.699i, and zeta's not. But zeta and DH differ in everything: gamma factor, conductor, pole, and
coefficients. So that comparison can't say which difference matters.

DH = (1 - i kappa)/2 L(s, chi) + (1 + i kappa)/2 L(s, chibar), with chi mod 5 and chi(2) = i. Restricted to real
test functions f, g = f * f~ is even, and the Weil form of L(s, chi) becomes

    W_sib(g) = ARCH - CONST - sum_n Lambda(n) Re chi(n) n^{-1/2} (g(log n) + g(-log n)).

This has **exactly DH's archimedean part**: Gamma((s+1)/2), conductor 5, no pole. Under GRH for L(s, chi mod 5),
which is numerically known at these heights, it is PSD. So DH and this "sibling" differ **only in the
coefficient sequence** c(n) of -L'/L:

| n | c_DH(n) (DH, by Dirichlet division) | c_sib(n) = Lambda(n) Re chi(n) |
|---|---|---|
| p = 1, 4 mod 5 | ±log p | ±log p (same) |
| p = 2, 3 mod 5 | ±kappa log p, kappa = 0.2840 | 0 |
| p^k, k >= 2 | not the Euler value | log p · Re chi(p^k) |
| n not a prime power | nonzero in general | 0 |

**Validation** (`results/validation_sibling.txt`): 31 zeros of L(s, chi) with |t| < 40 found by sign changes of the
rotated completed function (Riemann-von Mangoldt predicts 31.3). The sibling's explicit formula matches the zero
side to 2e-30 on four shifted Gaussians. The DH minimum at a = 2 is reproduced: -0.6397875 against dh_control's
-0.639788.

Every experiment below uses G(c) = ARCH - CONST - sum_n c(n) P_n, with the same B-spline basis as dh_control
(h ≈ pi/150, so heights up to ~150 are resolved). Only c changes.

## Verdict first

1. **DH's off-line zero lives in the coefficients that an Euler product forces to vanish.**
   - DH has exactly 2 negative directions at a = 2 (both at t = 84.5) and 6 at a = 3; its two largest are at
     t = 86.4. That is the rank-2 signature of one off-line quadruple {rho, 1 - rho-bar}.
   - At a = 3 we put DH's coefficients back into the sibling one group at a time:
     - DH's non-prime-power coefficients only: the t ≈ 86 pair comes back at full strength (-4.07, -3.99, against
       DH's own -3.59, -3.52).
     - DH's prime values only: nothing near t = 86.
     - DH's p^k (k >= 2) values only: nothing near t = 86 (a weaker pair at t = 92.9).
   - Linear attribution at DH's witness vector says the same:
     - a = 3: W_DH(v) - W_sib(v) = -7.57, of which non-prime-powers give -7.99, primes ≡ ±2 mod 5 give +0.42, and
       prime powers give ~0.
     - a = 2 (coarser): non-prime-powers 81 %, prime powers 14 %, primes 5 %.
2. **But at a = 2 no single group carries the pair alone.**
   - The pair needs the composite and p^k coefficients together. Composites alone give only a -0.05 trace at t = 84.6.
   - At a = 2 the window resolves t ≈ 85 only coarsely, so treat the a = 3 split as the cleaner one.
3. **Every hybrid sequence fails somewhere else too.**
   - Any mixture that is neither DH nor the sibling picks up negative directions at low frequency (t ≈ 0.5-16).
   - Neither "Euler product without functional equation" (DH's prime values made multiplicative: 3 negatives at
     a = 2, 11 at a = 3, all at t ≤ 3) nor "functional equation without Euler product" (DH) is positive.
   - The two failures look different. DH fails sparsely, exactly at its off-line zero. The bare Euler product
     fails diffusely, at low frequency, where the archimedean side and the coefficients have to cancel exactly.
4. **No sparse repair.**
   - Replacing c_DH(n) by c_sib(n) on a subset S restores positivity (to 1e-9 relative) only when S is all of the
     differing n: 34 of 34 at a = 2, 189 of 189 at a = 3.
   - Greedy search confirms this, and so does a genetic algorithm over subsets (3 seeds at a = 2, 1 at a = 3).
   - The GA's best partial sets (22-23 of 34; 168 of 189) stay negative. The greedy trajectory is not monotone:
     fixing more coefficients often makes things worse until the last few go in.
5. **Mixing all coefficients is different from fixing some of them.**
   - G(theta) = (1 - theta) G_DH + theta G_sib becomes PSD at theta* = 0.194 (a = 2) and 0.517 (a = 3).
   - A rank-one estimate from DH's witness predicts 0.188 and 0.474.
   - theta* rises with the window. That is expected: the off-line zero's negative weight grows like
     e^{(2 beta - 1) a}-ish with the support, and the sibling's positive mass at that height does not. So
     theta* -> 1, and in the limit positivity is all or nothing.

**What this does and does not say.** It is a concrete, checkable footprint of "the Euler product is
load-bearing". At the window where DH's off-line zero becomes visible, the failure is carried by the
coefficients of -L'/L off the prime powers, the ones the Euler product sets to zero. DH's "wrong" prime values
(±kappa on p ≡ ±2 mod 5) are nearly irrelevant to that failure and slightly help at a = 3.

That is natural in hindsight. DH's off-line zeros come from interference between L(chi) and L(chibar), and in
-f'/f that interference lives on the composite n. The result is about one function at two window sizes, and it
does not touch zeta. The hybrid forms are quadratic forms, not Weil forms of any L-function. Their low-frequency
failures only say the archimedean side and the coefficients must match. The project's earlier finding (positivity
is an exact cancellation between the archimedean side and the primes, tight at the pole) already said that.

## Tables

### Coefficient surgeries (`results/E1_surgeries_a*.csv`, `results/E1_negative_directions_a*.txt`)

| coefficients | a = 2: min eig, #neg | a = 3: min eig, #neg | negative pair near the off-line zero? (a = 3) |
|---|---|---|---|
| DH | -0.640, 2 | -3.585, 6 | yes, -3.59 / -3.52 at t = 86.4 |
| sibling L(chi) | +1.3e-11, 0 | -7.7e-14 (float64 noise), 0 | no |
| DH on prime powers only | -0.770, 6 | -1.539, 20 | no (pair at 92.9) |
| DH off prime powers only | -1.404, 3 | -4.160, 22 | yes, at t = 85.0 |
| Euler product of DH's a(p), no FE | -0.829, 3 | -1.250, 11 | no |
| sibling at primes, DH elsewhere | -0.472, 6 | -4.045, 36 | yes, at t = 86.4 |
| DH at primes, sibling elsewhere | -0.221, 4 | -0.359, 14 | no |
| sibling + DH's p^k (k >= 2) | -0.716, 6 | (21 neg) | no (pair at 92.9) |
| sibling + DH's non-prime-powers | -0.645, 4 (trace -0.05 at 84.6) | (31 neg) | yes, -4.07 / -3.99 at t = 86.4 |
| no primes at all | -0.397, 1 | -0.500, 2 | no |

"#neg" counts eigenvalues below -1e-10 · max|eig|.

### Interpolation (`results/E2_interpolation_a*.csv`)

| a | theta* (PSD onset, lambda_min >= -1e-12 max|eig|) | rank-one witness estimate |
|---|---|---|
| 2 | 0.1937 | 0.1878 |
| 3 | 0.5174 | 0.4736 |

(The `summary_a3.txt` line reporting theta* = 1 was a float64 artifact; the correction is appended there and the
code now uses the tolerance.)

### Witness attribution (`results/E3_witness_terms_a*.csv`)

v is DH's minimal eigenvector (unit norm). The table splits W_DH(v) - W_sib(v) = -sum_n (c_DH - c_sib)(n) v^T P_n v by group.

| group of n | a = 2 | a = 3 |
|---|---|---|
| non prime powers | -2.747 | -7.995 |
| prime powers p^k, k >= 2 | -0.479 | -0.0001 |
| primes = ±2 mod 5 | -0.182 | +0.425 |
| primes = ±1 mod 5, p = 5 | 0 | 0 |
| **total** | **-3.408** | **-7.570** |

The largest single contributions at a = 3 come from n = 39, 26, 21, 84, 34, 126, 94, 91, 14, 42, 51, 141: all
composite, each -0.28 to -0.53. No single n dominates.

### Sparse repair (`results/E5_repair_a*.txt`)

Greedy needs every differing coefficient: 34/34 at a = 2, 189/189 at a = 3. The GA (40 individuals, 60
generations) never finds a feasible proper subset. Its best partial sets are 22/34 (lambda_min = -2e-3) at a = 2
and 168/189 (-7e-4) at a = 3.

A remark on method: a GA over test functions would have been pointless. The Rayleigh quotient is quadratic, and
its global minimiser is an eigenvector. The search problem that is genuinely combinatorial is the one over
coefficient subsets, and that is where the GA went.

## Limits

- One non-Euler function (DH, conductor 5). Other Davenport-Heilbronn-type combinations and Epstein zeta
  functions with off-line zeros were not tried.
- Two windows, a = 2 and 3. At a = 2 the resolution near t = 85 is coarse.
- float64 eigenvalues. The sibling's floor at a = 3 is below float64 resolution, so "PSD" means
  lambda_min >= -1e-12 · max|eig| there.
- The attribution in E3 is linear accounting at one fixed vector, not a causal decomposition. The surgery table
  is the causal check, and the two agree at a = 3.

## Next step, if anyone wants one

Repeat at a = 4-5 and on a second Davenport-Heilbronn-type function whose off-line zero is at a different
height. Either the "non-prime-power coefficients carry the off-line zero" pattern sharpens, or it was an a = 3
coincidence.
