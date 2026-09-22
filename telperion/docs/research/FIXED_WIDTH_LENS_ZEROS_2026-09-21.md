# Fixed-width lens: zeros, zero-density, spectral and geometric analogues (2026-09-21)

Finder thread of the fixed-width survey. Research only; no Lean; no git state touched. Sidecar:
`FIXED_WIDTH_LENS_ZEROS_2026-09-21.json` (`checked: true` only where an arXiv abstract/HTML was read this pass).
**conjecture1_proved = False.** Nothing here proves RH or is progress toward a proof; survivors are instrument
or reduction proposals with their walls named.

## 0. The shape in this lens (from WALL_MAP / LANDSCAPE / SEAMS / RECONCILIATION / PHASE0 / E6Bridge7)

F(c, lam) = Re sum_rho m(rho) (gamma_rho - c)^2 e^{-2 lam (gamma_rho - c)^2}; on-line zero at distance x
gives x^2 e^{-2 lam x^2} >= 0; off-line pair at (x, y) gives 2|w|^2 e^{2 lam (y^2 - x^2)} cos(2 arg w - 4 lam x y),
i.e. -2 y^2 e^{2 lam y^2} at c = t. Two facts that organise every answer below:

- **Detection threshold.** With neighbours on the line at mean gap 2 pi/log(t/2 pi) << 1/sqrt(lam), the
  background at c is B(t, lam) ~ (log(t/2 pi)/2 pi) sqrt(pi)/(4 sqrt 2 lam^{3/2}) and the zero is invisible at
  width lam unless 2 y^2 e^{2 lam y^2} > B, i.e. y > y0(lam, t) (computed, heuristic background):

  | lam | t=1e4 | 6.4e5 | 1e8 | 1e12 | 1e20 | log(t*/2pi) with y0 = 1/2 |
  |---|---|---|---|---|---|---|
  | 1 | 0.373 | 0.441 | >1/2 | >1/2 | >1/2 | 33 |
  | 2 | 0.229 | 0.274 | 0.314 | 0.365 | 0.431 | 154 |
  | 4 | 0.140 | 0.169 | 0.195 | 0.230 | 0.275 | 1.19e3 |
  | 10 | 0.072 | 0.088 | 0.103 | 0.123 | 0.149 | 9.4e4 |

  The last column is 8 sqrt(2 pi) lam^{3/2} e^{lam/2} = 2 P_abs/f(0): the zero-side "nothing detectable" height
  coincides to leading order with the archimedean envelope c1(lam) of the wall map (the strip-edge term
  e^{lam/2}/2 of one off-line zero equals the absolute prime envelope). So the band T - D < c < c1(lam) is
  exactly the set of heights where a zero with y0(lam, t) < |beta - 1/2| <= 1/2 would be visible at width lam.
- **Circularity.** The background B uses neighbours ON the line. Unconditionally the neighbours are unknown, so
  the zero-side estimate of the residual is self-referential: fixed-width positivity on the band is a zero-free
  region "no zero with |beta - 1/2| > y0(lam, t)" whose own hypothesis (neighbours near the line) is the same
  statement one gap over. This is why every certificate below factors through certified zeros or the prime side.

## 1. Zero-density estimates

Claim. N(sigma, T) <= T^{A(sigma)(1-sigma)+o(1)} could control the band by counting the detectable zeros.
Mechanism, worked at sigma = 1/2 + y (Ingham 3(1-s)/(2-s); Guth-Maynard 30/13, checked: abstract + HTML intro,
Theorem 1.2, N(sigma,T) <= T^{30(1-sigma)/13 + o(1)}, improving Huxley 12/5 and coinciding with Ingham at
sigma = 7/10; near-line: Selberg 1946 1 - y/4 with log T, Jutila 1983 1 - (1-eps) y, Conrey 1989 1 - (8/7) y,
via the Kadiri-Lumley-Ng-type explicit memo arXiv 1910.08274 abstract (checked) and its intro (secondary)):

| y | 0.05 | 0.10 | 0.15 | 0.20 | 0.25 | 0.30 | 0.35 |
|---|---|---|---|---|---|---|---|
| Ingham | 0.931 | 0.857 | 0.778 | 0.692 | 0.600 | 0.500 | 0.391 |
| Guth-Maynard | 1.038 | 0.923 | 0.808 | 0.692 | 0.577 | 0.462 | 0.346 |
| Conrey (8/7) | 0.943 | 0.886 | 0.829 | 0.771 | 0.714 | 0.657 | 0.600 |

Guth-Maynard beats Ingham only for y > 0.2 (sigma > 7/10) and is trivial (exponent > 1) for y < 1/12. At the
operative y0 = 0.1-0.35 the count of detectable zeros up to height X is X^{0.35-0.93} >> 1, so POINTWISE
positivity on the band never follows. Averaged form: each bad zero makes F < 0 only within O(y + 1/sqrt lam)
of its ordinate, so meas{c in [T, X] : F < 0} <= N(1/2 + y0, X) * O(1) = o(X). But the step "F(c) < 0 => a zero
with y >= y0 within O(1/sqrt lam) of c" is the effective-O2 clustering lemma (S3, S10): O(log t) sub-threshold
zeros can sum to a negative F. UNRESOLVED via zeros; a zero-blind averaged statement exists (section 6, D).
Limitation: counted density = the capstone's excluded class; pointwise = RH-strength. Sources: GM 2405.20552
(checked), 1910.08274 (checked). **Verdict: COLLAPSE_TO_FREE** (pointwise: no; averaged: yes but zero-blind).
Wall: pointwise positivity needs N(1/2 + y0, X) = 0 on the band, which is the zero-free region of section 2.

## 2. Zero-free regions near the line

Claim probed: any "no zeros with beta > 1/2 + y0(t)" with y0 < 1/2 uniformly in t. Confirmed: none. Known
regions all hug Re s = 1: de la Vallee Poussin 1 - 1/(R log t) (Bellotti: R = 4.896 for t >= 3, secondary);
Vinogradov-Korobov 1 - 1/(55.241 (log t)^{2/3} (log log t)^{1/3}) (Mossinghoff-Trudgian-Yang 2024, secondary
via arXiv 2301.03165/2603.21490 hits); Littlewood 1922 1 - c log log t/log t. Width of every known region -> 0
as t -> infinity, i.e. y0_known(t) = 1/2 - o(1) -> 1/2. Below height 3e12 every zero is on the line
(Platt-Trudgian 2004.09765, abstract checked: interval arithmetic). Exact gap: fixed-width positivity on the
band at width lam needs y0(lam, t) ~ 0.1-0.35 UNIFORMLY on T < t < c1(lam); the known y0 is 1 - o(1) away
from that for every t above the ladder, and even the quasi-RH "beta <= 1 - delta for one fixed delta > 0" is
open (it would already give Lindelof-type consequences). Proportions on the line (Conrey 2/5, Pratt-Robles-
Zaharescu-Zeindler 5/12) are counted statements, not regions. **Verdict: COLLAPSE_TO_RH.** Wall: the
fixed-width statement IS a near-line zero-free region on a bounded band; no instrument in the literature
produces one; the only known route to any such region is the ladder (finite height) or RH.

## 3. Pair correlation / GUE and the on-line background

Montgomery's theorem (form factor F(alpha) for |alpha| < 1) assumes RH; an unconditional form exists
(Baluyot-Goldston-Suriajaya-Turnage-Butterbaugh arXiv 2306.04799, abstract checked: unconditional Montgomery
theorem, applied under a thin-box density hypothesis to 61.7 percent simple zeros). What it says about the
background: the c-average of B is fixed by N(T) (S7a); its fluctuation is a linear statistic of the zeros with
kernel x^2 e^{-2 lam x^2}, whose variance is the pair-correlation integral, O(1) per window. So y0(lam, t) is
deterministic to O(1) relative accuracy once >= 1 zero sits inside the Gaussian width, i.e. t > 2 pi
exp(2 pi sqrt(2 lam)) (4.5e4 at lam = 1, 3.3e8 at lam = 4, 1e13 at lam = 10); below that the Phase-0
nearest-neighbour law lam* = log(x1^2/2y^2)/(2(x1^2 + y^2)) rules and gap statistics move y0 by O(1) factors.
Pair correlation does not change the shape of y0; it does not lower it.
Unconditional lower bound on the background = "no large gaps" plus "neighbours on the line". Gaps: Littlewood
1924 (Proc. Cambridge Phil. Soc. 22, 234-242; primary NOT accessed, cited through the arXiv 1001.0494 search
hit) gives unconditionally gamma_{n+1} - gamma_n <= 32/log log log gamma_n, Hall-Hayman pi/2 + o(1); on RH,
C/log log t (Littlewood; Carneiro-Chandee-Milinovich constants). Arithmetic: to put a zero inside the Gaussian
sweet spot 1/(2 sqrt lam) the unconditional gap needs log log log t >= 2 C sqrt(lam), i.e. log log t >= e^{3.1}
= 23 already at lam = 1 with C = pi/2, versus the envelope log log c1(lam) = 3.5 at lam = 1, 7.1 at lam = 4,
11.5 at lam = 10: the unconditional gap bound bites only ABOVE the archimedean envelope, where positivity is
already free. The RH-conditional 1/log log t bound would bite inside the band, but is circular. Sources: 2306.04799
(checked); Littlewood 1924 (unchecked); 1001.0494 (abstract checked, Littlewood sentence not in abstract).
**Verdict: COLLAPSE_TO_FREE** (fluctuation) and **COLLAPSE_TO_RH** (lower bound). Wall: the background is
made of the very zeros the statement is about; the one unconditional gap bound lives above the envelope.

## 4. Spectral: Hilbert-Polya, de Branges, Connes-Consani, coherent states

Coordinates. In the u-variable the family is phi(u) = K u e^{-u^2/(4 lam)} e^{-icu}: modulation by c, dilation
by sqrt(lam), mother function u e^{-u^2/4}. On the zero side F(c, lam) = (mu_zero * K_lam)(c) with the positive
kernel K_lam(x) = x^2 e^{-2 lam x^2}, analytically continued: a Gabor/Berezin transform of the zero measure.
Identity: G = -(1/2) d/dlam e^{-2 lam (z-c)^2}, so F = -(1/2) d/dlam H(c, lam), H := Re sum m e^{-2 lam (gamma - c)^2}
(the pure-Gaussian Weil test; converges). Hence RH <=> H(c, .) is non-increasing in lam for every c: the
Gauss-smoothed zero density seen from c shrinks as the window narrows. Transfer of coordinates only (the pure
Gaussian cannot detect an off-line zero by sign, +e^{2 lam y^2}; the derivative can).
Hilbert-Polya: a self-adjoint realisation gives F = Tr((H-c)^2 e^{-2 lam (H-c)^2}) >= 0 trivially; the converse
is O2. De Branges/Lagarias spaces and the Hinkkanen-Lagarias face are the S8 rational coordinates. Connes-Consani archimedean positivity (2006.13771, Theorem 1 verified by the skeptic pass: support in
[2^{-1/2}, 2^{1/2}], hat g(i/2) = hat g(0) = 0, W_infinity(g*g^*) >= Tr(theta(g) S theta(g)^*), Sonin space;
"rational primes not involved"), and the prolate line (Connes-Moscovici 2112.05500 abstract; Connes-Consani-
Moscovici 2310.18423 abstract checked: semilocal prolate operator, UV negative spectrum ~ squares of zeros,
eigenfunctions in Sonin space, "fits with" the archimedean positivity proof). Fixed-width extraction: NO, and
essentially so. A compact-support test has hat h of exponential type (Paley-Wiener); the Gaussian test at any
fixed lam has mass e^{-(log p)^2/(8 lam)} at EVERY prime, O(1) for p <= e^{2 lam}; the archimedean theorem is
a statement with the prime side identically zero, the Gaussian small-lam region is the same theorem with the
prime side small (seam B), and at fixed lam > lam0 the prime side is neither. The prolate papers are spectral-
realisation statements, not positivity extensions. **Verdict: COLLAPSE_TO_FREE** (same foothold as seam B).
Wall: prime-side mass at fixed width; compact support and Gaussian width are incompatible by Paley-Wiener.

## 5. Function-field analogue

Over F_q(C), genus g: Z(C, u) has 2g inverse roots alpha_j = q^{1/2} e^{i theta_j} (Weil), so in s the zeros are
1/2 + i (theta_j + 2 pi k)/log q: a PERIODIC comb with period 2 pi/log q and 2g zeros per period. Fixed-width
Gaussian family: F_C(c, lam) = sum_{j, k} x_{jk}^2 e^{-2 lam x_{jk}^2}, x_{jk} = (theta_j + 2 pi k)/log q - c, a
theta-function-like finite object; an "off-line" zero would be |alpha_j| != q^{1/2}, y = log(|alpha_j| q^{-1/2})/log q.
Weil positivity holds for every test (Hodge index / Castelnuovo-Severi on C x C: D^2 <= 0 for divisors
orthogonal to the ample class, applied to Frobenius correspondences; Milne 1509.00797 abstract checked, proof
mechanism from standard texts, not re-read). Two structural readings:
(i) The band is EMPTY. Periodicity makes "height" bounded by one period; the ladder (2g zeros, one finite
computation) certifies every c. The number-field band exists because the comb is aperiodic and unbounded.
(ii) The mechanism is a CONE certificate of unbounded bandwidth: intersection positivity holds for all
correspondences at once, so all tests, all lam. It is not a fixed-width mechanism and gives no hint of one.
What the number-field band would need: a "surface" whose Hodge-index inequality is Weil positivity on Gaussian
tests of width lam: Deninger's foliated-space Kahler positivity (math/0505354, math/0204110; program, no space
constructed) or Connes' adele class space, where RH is the validity of the trace formula (math/9811068 abstract
checked); the 2020-2024 Connes-Consani line builds the geometry, not the index inequality. **Verdict: TRANSFER of shape, COLLAPSE_TO_FREE of content** (every function-
field certification factors through finiteness = ladder). Wall: no Hodge-index inequality on any number-field
"surface"; the analogue of the band is void where the theorem is known.

## 6. Creative items from this lens

A. **Turing's method as a fixed-width object.** The ladder counts zeros by the argument principle: sign changes
of Z(t) (Riemann-Siegel, ~sqrt(t/2 pi) terms) plus Turing's bound on int S(t) dt (Trudgian 0903.1885, abstract
checked; constants not re-read). Its underlying test is a box (infinite bandwidth) evaluated on the zeta side.
A Gaussian certificate is one real inequality per (c, lam) from the prime side and can never produce an
integer. Quantified: the Gauss-smoothed count H(c, lam) errs by log(t/2 pi)/(2 pi sqrt(2 lam)) zeros, >= 1 for t > 4.5e4
(lam = 1), 3.3e8 (lam = 4), 1e13 (lam = 10); pinning N(t) needs lam >= lam_res(t) = (log(t/2 pi))^2/(4 pi^2):
3.4 at 6.4e5 (primes to 1e7, but the ladder is already there), 18.3 at 3e12 (primes to 1e37), 49.5 at 1e20
(1e101) against Riemann-Siegel 6.9e5 and 4e9 terms. Even resolved, on-line and y < y0(lam) are indistinguishable,
so WindowOnLine is never reproduced. Extending the certified region upward by prime-side data alone: NO; best
conceivable yield is "no zero with y > y0(lam, t) in [T, T + h]", resting on effective O2. **COLLAPSE_TO_FREE.**
B. **Lehmer pairs.** Correction to the expected "they help": a close pair at +-d/2 contributes 2 (d/2)^2
e^{-lam d^2/2} at its midpoint, tiny for d << 1/sqrt(lam), and its off-line twin at +-i d/2 contributes
-2 (d/2)^2 e^{+lam d^2/2}; the two differ by ~2 lam d^4 and both sit far below the neighbour background
(d = 0.005, height 7005: on 1.25e-5, off 1.25e-5, B = 4.4e-2 at lam = 4; separating them needs lam ~ 6.5e5).
Zeros at the sweet-spot distance 1/(2 sqrt lam) maximise the background and help; Lehmer near-collisions are
the fixed-width family's blind spot, the same configurations that bound the de Bruijn-Newman constant from
below (Csordas-Smith-Varga 1994, secondary). Consequence: fixed-width positivity at lam is blind to any
near-collision with d < d0(lam) ~ sqrt(log(B/d^2)/lam), i.e. to the near-violations of RH that exist.
C. **Reflection symmetry.** The pair term is even in y (Phase 0, E6Bridge7): F is a function of (rho - 1/2)^2.
Consequences: (1) the family certifies |beta - 1/2| <= y0, never a one-sided region (no loss: the functional
equation symmetrises anyway); (2) the c-average is y-blind (S7a), the second moment sees e^{4 lam y^2} (S9);
(3) evenness keeps the prime side a Hermitian square, inside the Weil class (S7b stands).
D. **Unconditional negative-set bound with no zero input (upgrade of S10).** prime(c) = 2 sum Lambda(n) n^{-1/2}
f0(log n) cos(c log n) is a Dirichlet polynomial of effective length e^{4.7 lam}. Its mean square over
[T, 2T] is 2 sum Lambda(n)^2 n^{-1} f0(log n)^2 + off-diagonal, and with sum_{n<=x} Lambda(n)^2 ~ x log x the
diagonal is 4 lam f(0)^2 (exact integral 2 lam, checked numerically); the off-diagonal is <= P_abs^2 X ~
e^{5.7 lam}, negligible for T >> e^{6 lam}. Arch = f(0) log(c/2 pi) + o(1). Chebyshev:
    meas{c in [T, 2T] : F(c, lam) < 0} <= T (4 lam + o(1)) / (log(T/2 pi))^2      (T >= C e^{6 lam}).
Numbers: lam = 4 gives 12 percent at T = 6.4e5, 2.2 percent at 3e12, 0.8 percent at 1e20; lam = 1: 3, 0.6,
0.2 percent. Higher moments (2k-th, k <= log T/(4.7 lam)) push this to T^{1 - (log log T)/(5 lam) + o(1)}.
Elementary (no Montgomery-Vaughan needed at k = 1; Zeta23 Chebyshev bounds suffice), zero-blind, and NOT
saturable to zero (Kronecker alignment, S12, happens at triply exponential heights). As a foothold
**COLLAPSE_TO_FREE** (family average, capstone clause 2); as a lemma it is provable, unlike S10's zero route.
E. **de Bruijn-Newman coordinates.** H_t(x) = int e^{tu^2} Phi(u) cos(xu) du; RH <=> Lambda <= 0; Rodgers-Tao
1801.05914 (abstract checked) Lambda >= 0; Polymath 15 1904.12438 (HTML checked) Lambda <= 0.22 unconditionally
via exactly the wall map's three-region structure: ladder (RH verified to ~3e10 at t = 0), asymptotic zone
(no zeros of H_t with x >= X + ...), and a BARRIER (no zeros in a rectangle for all 0 < t <= 0.2, by a
continuity argument on the zero dynamics). The wall in these coordinates is the interval (0, 0.22] of one real
parameter, and the barrier is the piece the Gaussian family lacks: zeros do not move with lam, so nothing
connects the ladder region to the envelope region across the band. **TRANSFER** (a compact one-parameter
residual; cost unbounded since the asymptotic-zone height -> infinity as t -> 0). Not the same object as ours
(zeros of the flowed function, not smoothed zeros of xi).

## 7. Ranked proposals for closure or reduction of the fixed-width residual

1. **Effective dominance with certified background (instrument, cheap, ladder-bound).** State and prove:
   WindowOnLine c D, plus explicit gap data from the certificate, plus "every zero in [c-R, c+R] has y < y1(lam)"
   => F(c, lam) >= 0, with y1 explicit (cos-phase control 4 lam R y1 < pi/2 and count <= C log c in the window).
   Establishes: the residual is EQUIVALENT (up to explicit constants) to the near-line zero-free region of
   section 2 on the band. Cost: paper proof ~ 5 pages; Lean ~ 400 lines on E6Bridge7 vocabulary. Wall: never
   applies above T because y < y1 is unknown there; it sharpens the wall's statement, not its location.
2. **Zero-blind measure lemma (item D), kernel-grade.** meas{c in [T,2T]: F < 0} <= T (4 lam + o(1))/log^2(T/2 pi).
   Establishes: the first unconditional statement about F on the band that is not archimedean dominance and
   needs no zeros; a numerically checkable instrument and a negative control (a certified F < 0 on a set of
   larger measure would refute the prime-side model). Cost: paper ~ 3 pages; Lean ~ 300 lines (Chebyshev
   partial summation, Zeta23 vonMangoldt bounds). Wall: averaged; pointwise is RH.
3. **de Bruijn-Newman barrier transplant (research).** Ask whether a lam-parametrised deformation of the zero
   set exists for which F is monotone and zeros move continuously (a Rodgers-Tao-type flow on the Weil form).
   Establishes, if yes: a barrier argument connecting ladder and envelope regions, the only mechanism in the
   literature that crosses a bounded band unconditionally (Polymath 15). Cost: unknown; likely the flow
   lives on xi (Newman's), not on tests, and the transplant collapses to "RH <=> Lambda = 0". Wall: no
   dynamics in (c, lam).
4. **Density-averaged band statement with the clustering lemma (research).** Prove effective O2 by averaging
   over lam in [Lambda/2, Lambda] (S3 attack) with the unconditional unit-window count as the only input;
   then Ingham/Guth-Maynard gives meas{F < 0 on the band} <= c1^{0.35-0.93}. Establishes: a zero-side
   companion to proposal 2, stronger at large height. Cost: open lemma (S3/S10); Wall: clustering at scale
   1/(Lambda y0), no unconditional handle.
5. **Function-field dry run (instrument, cheap).** F_C(c, lam) for a few curves plus a synthetic off-line root:
   a negative control for TRANSFER claims (periodicity makes the ladder total). Cost 1 day. Wall: no content.

## 8. Honesty footer

conjecture1_proved = False. Primary sources read this pass (abstract or HTML on arXiv): Guth-Maynard 2405.20552;
Polymath 15 1904.12438; Rodgers-Tao 1801.05914; Kadiri-Lumley-Ng-type explicit Selberg density 1910.08274;
Baluyot et al. 2306.04799; Connes-Consani-Moscovici 2310.18423; Platt-Trudgian 2004.09765; Milne 1509.00797;
Connes math/9811068; Trudgian 0903.1885; 1001.0494 (abstract only). Connes-Consani 2006.13771 verified by the
skeptic pass, not re-read. NOT accessed (secondary only): Littlewood 1924 gap bound and Hall-Hayman constant;
Selberg 1946 / Jutila 1983 / Conrey 1989 exponents (via 1910.08274's intro as reported by search); Mossinghoff-
Trudgian-Yang 2024 and Bellotti constants; Csordas-Smith-Varga 1994; Deninger's foliated program papers;
Weil/Castelnuovo-Severi mechanism (standard texts); Trudgian's constants. Tables are float computations of the
heuristic on-line-background model (neighbours on the line, m = 1): estimates, not enclosures, circular above
the ladder by construction (section 0). Single finder pass; no replication.
