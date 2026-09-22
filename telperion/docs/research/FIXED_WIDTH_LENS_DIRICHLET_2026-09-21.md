# Fixed-width lens: Dirichlet polynomials, almost periodicity, large values (2026-09-21)

conjecture1_proved = False. Nothing here proves RH or any (c, lam) instance of Gaussian positivity beyond
what E6Bridge11/12 already prove. Research only, no Lean. Survivors are instruments or reductions with
their walls named. Sidecar: `FIXED_WIDTH_LENS_DIRICHLET_2026-09-21.json`. Scratch scripts (numbers below):
`fixed_width_numbers.py`, `bisect_lam.py`, `probe_sup.py` in the session scratchpad; float estimates, not enclosures.

## 0. The object at fixed width, and the numbers

With `a_n := 2 Lambda(n) n^{-1/2} f0(log n)`, `f0(u) = A (1 - u^2/(4 lam)) e^{-u^2/(8 lam)}`, the prime side is the
cosine Dirichlet polynomial `prime(c, lam) = Sum_{n >= 2} a_n cos(c log n)` (landscape memo convention, F = arch - prime).
Its coefficients change sign at `log n = 2 sqrt(lam)` and are Gaussian-damped around `log n = 2 lam` with width `sqrt(4 lam)`.
Every quantity below is in units of A (= f(0)). Sieve to 1e7 with the psi(x) ~ x tail integral beyond (tail < 1e-9 for lam <= 1).

| lam | S = Sum abs(a_n)/A | sigma^2 = Sum (a_n/A)^2 / 2 | L1 = Sum abs(a_n) log n / A | N_eff (tail 1e-3) | K_p (primes carrying 90 % of S) | c1_sharp = 2 pi e^S | c1_crude (Lean floor) | grid points M for band certification |
|---|---|---|---|---|---|---|---|---|
| 0.30 | 4.60 | 0.88 | 10.3 | 223 | 9 | 6.3e2 | 1.7e5 | 0 |
| 0.50 | 8.74 | 1.59 | 25.4 | 1.5e3 | 22 | 3.9e4 | 1.4e7 | 0 |
| 0.60 | 11.10 | 1.96 | 35.9 | 3.6e3 | 31 | 4.2e5 | 1.7e8 | 0 |
| 0.70 | 13.78 | 2.34 | 48.8 | 8.1e3 | 44 | 6.1e6 | 2.9e9 | 2.6e8 |
| 0.80 | 16.79 | 2.71 | 64.4 | 1.8e4 | 62 | 1.2e8 | 6.9e10 | 7.9e9 |
| 1.00 | 23.72 | 3.48 | 104.8 | 7.8e4 | 123 | 1.26e11 | 1.06e14 | 1.3e13 |
| 1.50 | 48.9 | 5.40 | 282 | 2.2e6 | 591 | 1.1e22 | 4.1e25 | 3e24 |
| 2.00 | 89.6 | 7.34 | 630 | > 1e7 | 2591 | 5e39 | 2e44 | 3e42 |

Floors at c = T = 640000: true `arch/A -> log(c/(2 pi)) = 11.53`; the in-kernel floor (seam B section 4b,
`theta (1 - 3 e^{-4}) - 15 e^{-4} - log pi`, theta = log((c - 2/sqrt lam)/2) - 5) is 5.83. The 5.7 units of slack are the
Stirling `-5` and the tail split, not the mathematics: `Re psi(1/4 + i r/2) = log(r/2) + O(1/r^2)`.
`c1_crude` is the Lean envelope mechanism with the trivial prime bound S in place of the crude `X(lam)`; the shipped
`envelopeC` (with `16 e^{16 lam}`) is 10^41499 at lam = 0.5 and 10^(1.2e8) at lam = 1, unusable as a band edge.
CORRECTION to the brief: with S(1) = 23.7 the sharp band at lam = 1 is [6.4e5, 1.26e11], not [6.4e5, ~1e8] (that used
`P ~ e^{lam/2} sqrt(8 pi lam)` without the polynomial factor, erratum E5); the reconciliation's `P_abs/f(0) = 27` at lam = 1
is 23.7 by direct sieve (the two differ by the sign-change region of f0; flagged, not load-bearing).
Width thresholds (bisection on S): the trivial bound `prime <= S A` beats the floor at every c >= T for
lam <= 0.618 (sharp floor) / lam <= 0.361 (in-kernel floor); against T = 3e12 (Platt-Trudgian): lam <= 1.078 / 0.909.
Empirical probe (`probe_sup.py`, c in [T, T + 4000], step 0.02): max prime/A = 5.54 (lam 0.6), 6.69 (0.8), 7.35 (1.0),
all at c = 643005.18 (a partial alignment), rms = sigma to three digits, floor 11.53. Heuristic, not a bound.

## 1. Sup over a bounded range: what beats Sum abs(a_n)?

Claim. Nothing rigorous, in this regime. Large-value theory (Halasz-Montgomery, Huxley, Bourgain, Guth-Maynard)
bounds the NUMBER of 1-separated points t in [0, T] with |D(t)| >= V, and it is designed for V comparable to
`sqrt(G N)` (Guth-Maynard: `V ~ N^{3/4}` for `|b_n| <= 1`). Classical form in Guth-Maynard's normalisation:
`|W| <= T^{o(1)} (N^2 V^{-2} + T min(N V^{-2}, N^4 V^{-6}))`; Guth-Maynard: `T^{o(1)} (N^2 V^{-2} + N^{18/5} V^{-4} + T N^{12/5} V^{-4})`.
Mechanism. Our regime is the opposite corner: fixed polynomial (`G = 2 sigma^2 ~ 7` at lam = 1, `N_eff ~ 1e5`),
threshold `V = log(c/2 pi) ~ 12-26`, range `C = c1 ~ 1e11` exponentially longer than the polynomial. There every
large-value bound reduces to the mean-value/Chebyshev bound `|W| <= C G / V^2`: a positive proportion (2.6 % at lam = 1,
c = T), never zero, never a sup. Kronecker-Weyl alignment: the pigeonhole (Dirichlet) upper bound on the first height
where the K_p leading phases align to eps is `eps^{-K_p}`: 10^22 (lam 0.5), 10^62 (0.8), 10^123 (1.0) at eps = 0.1,
astronomically above c1_sharp. No lower bound of that shape exists; effective lower bounds on alignment heights
(Baker-type linear forms in log p) are polynomial in 1/eps, not exponential in K_p (UNRESOLVED: no primary read).
Limitation / wall. THE SUP WALL: for a bounded-range sup of an unstructured trigonometric polynomial there is no
theorem below the l^1 norm; the only rigorous route is pointwise evaluation. But the l^1 bound itself is not empty:
it closes the band above T = 640000 for lam <= 0.618 (sharp floor) and lam <= 0.361 (in-kernel floor).
Verdict. COLLAPSE_TO_FREE for lam <= 0.618 (band empty by the trivial bound + a sharper floor; lam <= 0.361 already
with the shipped floor). TRANSFER for lam in (0.62, ~0.85]: finite pointwise certification (section 3 cost). Wall for lam >~ 0.9.
Probe. Kernel: `S(lam) <= log(T/2pi)` as a `norm_num`/interval fact for one lam in (0.36, 0.62) plus the sharpened floor of
proposal P1 gives `F(c, lam) >= 0` for all |c| >= T at that lam, unconditionally.

## 2. Consistency: can resonance/alignment refute positivity, and is fixed-lam envelope positivity a theorem?

Claim. Fixed-lam positivity outside a bounded band IS a theorem today: `gaussian_positivity_envelope` (E6Bridge11),
unconditional, for |c| >= envelopeC(lam). Its sharp constant is elementary: `c1_sharp(lam) = 2 pi e^{S(lam)}` needs only
(i) `prime <= S A` (triangle inequality, already the mechanism of `norm_primeSide_le_uniform`) and (ii) a floor
`arch/A >= log(c/2pi) - o(1)`; the shipped `16 e^{16 lam}` (AM-GM) and `-5` (Stirling) are what separate 1e11 from 10^(1e8).
Mechanism (why nothing is pinched). Resonance (Soundararajan 2008, Bondarenko-Seip 2017, Aistleitner 2016) makes
`Re Sum_{p <= N} p^{-1/2 - it}` large by a resonator `r(p) = A/sqrt p` on `A^2 <= p <= N^{1/(2A^2)}`, `N = T^{1-eps}`;
the values produced at height T are of size `sqrt(log T / log log T)` for zeta, i.e. `sigma(lam) * sqrt(2 log T)`-scale
for our fixed polynomial: 9.2 (model) vs 7.35 (measured) at lam = 1 over a 4000-wide window, against a floor of 11.53.
Both the model maximum `sigma sqrt(2 log c)` and the resonance guarantee stay below `log(c/2pi)` exactly when
`log c >~ 2 sigma^2(lam)` (~ 7 at lam = 1, ~ 15 at lam = 2), i.e. above c ~ 1e3-1e7, inside the ladder. The residual band
`[T, c1_sharp]` lies entirely where every heuristic says the polynomial is below the floor by a factor 1.6-2.5; the l^1
bound is what is loose, not the polynomial.
Limitation. Fixed-lam positivity is not RH (only the forall-lam quantifier is). Under RH `prime(c, lam) <= arch(c, lam)` for
every c is a consequence; unconditionally nothing forbids an exceedance inside the band, and an exceedance would be an
off-line zero within O(1/sqrt lam) of c (E6Bridge7's `gaussian_dominance` read backwards). Sources: Soundararajan
arXiv:0708.3990 (checked, PDF: Theorem 1 and the resonator choice p. 7-8), Bondarenko-Seip arXiv:1507.05840 (checked, abstract),
Aistleitner arXiv:1409.6035 (checked, abstract), E6Bridge11 (this corpus).
Verdict. COLLAPSE_TO_FREE (already the free region of seam B); the sharp constant is proposal P1.
Probe. Refute-attempt probe: NUFFT scan of `prime(c, 1)` over [T, 1e8] (M ~ 1e10 points at spacing 0.01) and report the
running `max prime/A - log(c/2pi)`; the heuristic predicts it stays below -3. Float only, no rigor, cost ~ hours.

## 3. Mean square, moments, and a certification cost model

Claim A (unconditional lemma, prime side only, NOT in the corpus). Montgomery-Vaughan gives
`int_C^{2C} prime(c, lam)^2 dc = A^2 (C sigma^2 + O(Sum a_n^2 n))` with the error finite and lam-only (Gaussian decay in
log n). With any rigorous floor `arch/A >= phi(C)` on [C, 2C], Chebyshev gives
`|{c in [C, 2C] : F(c, lam) < 0}| <= C sigma^2(lam) / phi(C)^2 + O_lam(1)`: density -> 0 like `1/log^2 C`.
Higher moments (the polynomial's 2k-th moment equals its independent-phase model for `k <= log C / (3 log N)`, the exact
form of Lamzouri-Lester-Radziwill Lemma 3.2, checked) sharpen this to a measure `<= C^{1 - eta}`,
`eta ~ log(log C log N / sigma^2) / log N` (0.4 at lam = 1, C = 1e8). This RESOLVES S10 of the reconciliation as a lemma
("density zero for fixed lam") without any clustering input, and beats it (power saving) --- but it is a measure
statement, not a sup, hence no certificate.
Claim B (cost). "Mean value + derivative" does not give a rigorous sup: Sobolev on [0, C] scales with C. The honest
certificate is a Lipschitz grid: `|d prime/dc| <= L1 A`, spacing `delta = margin / L1`, margin 1 (units A) generic, adaptive
refinement where `floor - prime < 1`. Points `M = (c1_sharp - T) L1`: 2.6e8 (lam 0.7), 7.9e9 (0.8), 2.7e11 (0.9), 1.3e13 (1.0);
each point is an N_eff-term sum (8e3, 1.8e4, 3.8e4, 7.8e4): direct cost 2e12 / 1.4e14 / 1e16 / 1e18 flops. NUFFT type-1
brings evaluation to `O(M log M + N_eff)` (5e14 at lam = 1) but rigor then needs a Taylor-in-c remainder per chunk
(Platt's zeta method), i.e. back to `O(M N_eff / chunk)`. Feasible: lam <= 0.8 (days, interval arithmetic); heroic:
0.9; infeasible: 1.0 (the band edge grows like `exp(e^{lam/2} poly(lam))`, doubly exponential in lam).
Limitation / wall. THE MOMENT WALL: the exceedance level `V = log c` sits at moment order `k ~ log^2 c / sigma^2`, but moments
match the model only for `k <= log c / (3 log N)`; the gap `log c * log N / sigma^2` grows with c, so no moment method
reaches the tail that positivity is about. Sources: Montgomery-Vaughan 1974 (UNRESOLVED primary, JLMS paywalled; weighted
Hilbert inequality restated in arXiv:2203.14950, checked), LLR arXiv:1402.6682 (checked, PDF Lemma 3.2 and Theorem 1.1).
Verdict. FOOTHOLD as a lemma (Claim A, worth a two-page paper proof; Lean wall: no Montgomery-Vaughan in Mathlib);
COLLAPSE_TO_FREE as RH progress (family average, capstone clause 2); TRANSFER for Claim B (finite certification, lam <= 0.8).

## 4. Selberg CLT, log zeta, and the smoothed -zeta'/zeta

Claim. Since `F0(w) = int f0(u) e^{wu} du` is entire (Gaussian), Perron/Mellin gives
`Sum Lambda(n) n^{-1/2 - ic} f0(log n) = (1/2 pi i) int_{Re w = a} (-zeta'/zeta)(1/2 + ic + w) F0(w) dw`, a > 1/2,
so `prime(c, lam) = 2 Re` of a Gaussian-smoothed `-zeta'/zeta` at `1/2 + ic`, evaluated on a contour to the right; shifting
to Re w = 0 picks up the zeros and IS the explicit formula `zeroSide_gaussTest_eq`. Fixed-lam positivity is therefore
"the Gaussian-smoothed `-zeta'/zeta` on the half-line, read from the right, never exceeds the Gamma-factor floor".
Relation to S8 (Hinkkanen-Lagarias face): the lam-Laplace transform replaces the Gaussian `F0` by a rational kernel and the
prime sum by `xi'/xi` at one point; same content, third coordinate system (reconciliation E3).
Selberg's CLT (Radziwill-Soundararajan arXiv:1509.06827, checked, abstract: `log|zeta(1/2 + it)|` is Gaussian with variance
`(1/2) log log t`) is the `N -> infinity with c` regime: the truncation `p <= X = c^{o(1)}` grows with height. At fixed lam
the polynomial has FIXED variance `sigma^2(lam)` (3.5 at lam = 1) and a Bohr-Jessen limit law (LLR Theorem 1.1 gives
discrepancy `(log T)^{-sigma}` for `sigma > 1/2`; on the line itself only the CLT scaling is known). The fixed-lam Wall is
the `c -> infinity` tail of a fixed-variance law at level `log c`, which no limit law controls (section 3 wall).
Verdict. TRANSFER (coordinates), no foothold. Probe: none beyond section 3.

## 5. Almost periodicity, Besicovitch norms, Turan, GUE

Almost periodicity (Bohr). `Sum abs(a_n) < infinity`, so `prime(., lam)` is a uniformly almost periodic function; its
sup over ALL c equals `S*(lam) := Sum_p max_theta Sum_k a_{p^k} cos(k theta) <= S(lam)` (Kronecker on the Q-independent
`log p`), attained in the limit on a relatively dense set. Consequence: the sharp envelope `2 pi e^{S*}` is SHARP for the
l^1 mechanism (the polynomial really does approach S* A at unboundedly many heights); the band cannot be shrunk by any
bound on the polynomial alone; only the height at which the approaches occur (unknown, section 1) or pointwise data can.
`F(c, lam)` itself is not a.p. (arch grows like log c): the Wall at fixed width is "an a.p. function below a log floor".
Besicovitch/B^2 norm = `sigma sqrt 2`, section 3. Sources: Bohr 1925, Kronecker (UNRESOLVED, no primary read).
Turan power sums. Second main theorem: over an interval of exponents of length n, `max |Sum b_j z_j^nu| >= 2 (n/(8e(m+n)))^n min_j |b_1 + ... + b_j|`
(Wikipedia restatement, UNRESOLVED primary). With `n = K_p ~ 100` the factor is `< 10^{-150}`: useless for locating large
values in the band, and large values are the threat, not the help. Verdict COLLAPSE_TO_FREE.
GUE. Enters only through the zero side: `int F^2 dc` cross terms are the pair-correlation/Frobenius quantity (S9); the prime
polynomial's own distribution at fixed lam is the Bohr-Jessen (independent phases) law, not GUE. No new foothold.

## 6. Proposals for closure or reduction of the fixed-width residual (ranked)

P1. SHARPEN THE ARCHIMEDEAN FLOOR (Lean, small). Replace `Re psi(1/4 + i r/2) >= log(|r|/2) - 5` by a Stirling remainder
`>= log(|r|/2) - 1/|r|` for |r| >= 1e3, and integrate the log against the full bump instead of splitting at L = 2/sqrt lam.
Then `arch/A >= log(c/2pi) - 1e-3` for c >= 1e5, and the trivial prime bound `S(lam)` (one `norm_num`/interval fact per lam,
or the sieve-free integral bound `2 A e^{lam/2} int |1 - u^2/4lam| e^{-(u - 2 lam)^2/8 lam} du` + Rosser-Schoenfeld) gives
`F(c, lam) >= 0` for all |c| >= T at every lam <= 0.618, and with seam C for |c| <= T - D at lam >= lamThreshold:
whole horizontal lines of the wall map at lam in [thr, 0.618]. Cost: one Mathlib-level Stirling lemma + rewiring, days.
Establishes: fixed-lam positivity on full lines. Does NOT establish: anything about the forall-lam quantifier (RH).
P2. LIPSCHITZ-GRID BAND CERTIFICATE (numerics + registry hypothesis). Certify `prime(c, lam) <= floor(c)` on
[T, c1_sharp(lam)] by interval evaluation at spacing `1/L1`, adaptive near small margins. Cost 2e12 flops (lam 0.7),
1.4e14 (0.8), 1e16 (0.9). Extends P1's full lines to lam <= 0.8-0.9. Wall: doubly exponential in lam past 0.9; enters the
registry as computed data, like the ladder.
P3. ADOPT THE PLATT-TRUDGIAN HEIGHT (registry-level, external). `WindowOnLine c D` for |c| <= 3e12 - D as a hypothesis
from arXiv:2004.09765 (checked, abstract: all zeros with 0 < gamma <= 3e12 have beta = 1/2, interval arithmetic). With P1,
band empty for lam <= 1.078 (0.909 with the shipped floor). Establishes lines up to lam ~ 1.08. Wall: external
certificate trust; lamThreshold at height 3e12 must be re-derived (seam C constants).
P4. NEGATIVE-SET DENSITY LEMMA (paper). Prove section 3 Claim A: for fixed lam, `|{c in [C, 2C] : F(c, lam) < 0}| <= C^{1 - eta}`,
prime side only, via Montgomery-Vaughan + LLR-type moments. Resolves S10 (reconciliation) as an unconditional lemma.
Cost: 2-3 pages; Lean: blocked on a mean-value theorem for Dirichlet polynomials. Establishes: a density statement.
Does NOT establish: any sup, any (c, lam) instance, anything about zeros.
P5. HEURISTIC MARGIN SCAN (float probe, hours). NUFFT scan of `max prime/A - log(c/2pi)` over [T, 1e8] at lam in {0.7, 0.8, 1};
the model predicts margin <= -3 throughout. Purpose: decide whether P2's adaptive refinement will be cheap (large margins)
before committing interval-arithmetic budget. Establishes nothing; informs P2.

## 7. Sources

Checked (primary read): Guth-Maynard arXiv:2405.20552 (HTML, Theorem 1.1 and the classical comparison bound);
Soundararajan arXiv:0708.3990 (PDF, Theorem 1, resonator (2), r(p) choice); Bondarenko-Seip arXiv:1507.05840 (abstract);
Aistleitner arXiv:1409.6035 (abstract, Theorem with c_alpha); Radziwill-Soundararajan arXiv:1509.06827 (abstract);
Lamzouri-Lester-Radziwill arXiv:1402.6682 (PDF, Theorem 1.1, Lemma 3.2; no Baker's theorem used); Platt-Trudgian
arXiv:2004.09765 (abstract); Montgomery-Vaughan weighted Hilbert inequality as restated in arXiv:2203.14950 (HTML);
corpus memos WALL_MAP / SEAM_A / SEAM_B 4b / LANDSCAPE / RECONCILIATION (read on disk).
UNRESOLVED (secondary only or inaccessible): Montgomery-Vaughan 1974 JLMS "Hilbert's inequality" (paywalled); Huxley 1973
Acta Arith 24 large values (EUDML landing page only, PDF 403); Halasz-Montgomery / Montgomery LNM 227; Turan's second main
theorem (Wikipedia restatement); Bohr 1925 and Kronecker's theorem (textbook knowledge, no primary fetched); Baker-type
effective Kronecker lower bounds (no primary); Selberg 1946; Bohr-Jessen 1930/32.

## 8. Honesty footer

RH not proved; no (c, lam) instance newly proved. The numbers are double-precision sieve sums, not enclosures; S(1) = 23.7
disagrees with the reconciliation's 27 (E5) and should be re-derived by the numerics thread before P1 constants are fixed.
The probe maxima are over a 4000-wide window only. Section 3 Claim A is a paper-level sketch (Montgomery-Vaughan error
term and the moment range need to be written out), not a theorem in the corpus.
