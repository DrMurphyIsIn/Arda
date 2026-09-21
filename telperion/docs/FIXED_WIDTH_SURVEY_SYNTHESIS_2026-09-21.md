# Fixed-width survey: synthesis and refutation of the three lenses (2026-09-21)

Synthesis under the wall-sweep taxonomy of three independent finder threads on the fixed-width residual
(`research/FIXED_WIDTH_LENS_{DIRICHLET,ZEROS,HEAT}_2026-09-21.md`), the band numerics
(`FIXED_WIDTH_BAND_NUMERICS_2026-09-21.md`), the wall map section 7 addendum, the seam reconciliation and the
effective-O2 memo (E6Bridge14). Research only; no Lean; no git state touched. Sidecar:
`research/FIXED_WIDTH_SURVEY_SYNTHESIS_2026-09-21.json`. Scratch: `scratchpad/skeptic/fixed_width_S.py`
(sieve to 1e7, float, not enclosures). **conjecture1_proved = False.** Nothing here proves RH or any new (c, lam)
instance; every survivor is an instrument or a reduction with its wall named.

Notation: F(c, lam) = arch - prime in units of A = f(0); floor(c) = log(c/2pi) + o(1); S(lam) = sum_n |a_n|/A the
trivial (l1) prime bound; band edge c1(lam) = 2pi e^{S(lam)}; ladder T = 640000 (kernel), 3e12 (Platt-Trudgian).

## 1. Convergence table (three independent lenses + numerics)

| fact | Dirichlet | zeros | heat | numerics | status |
|---|---|---|---|---|---|
| band edge at fixed width is 2pi e^{S(lam)}, doubly exponential in lam | c1_sharp, table | "detection height = envelope" (leading order) | envelopeC^{-1}(T), crude F constant | c_triv, table | CONVERGE (four routes) |
| S(1) | 23.72 | 33 (last column; spurious factor 2, see E1) | not computed | 23.718 | SETTLED: 23.72 sieve; 26.8 = RS majorant (reconciliation E5, valid upper bound, 13 percent loose); 16.5 = large-lam asymptotic 4 sqrt(2pi) lam^{3/2} e^{lam/2} (30 percent low at lam = 1) |
| detection at width lam needs y > y0(lam, t); y0 -> 1/2 at height t* with log(t*/2pi) = S_asym(lam) | - | organising fact | GUE: fragility decreases with height | y0 "none" for lam <= 0.7 at 6.4e5, 1e6 | CONVERGE: the asymptotic S(lam) = 4 sqrt(2pi) lam^{3/2} e^{lam/2} is EXACTLY the strip-edge detection height (both carry the e^{lam/2} of the strip half-width 1/2); the zeros lens wrote 8 sqrt(2pi), a factor 2 slip |
| closable widths are the blind widths | lam <= 0.618 free by l1 | same shape | same (Theta worse detector) | anti-correlation measured | CONVERGE |
| l1 bound is sharp for the a.p. polynomial (Bohr-Kronecker), but only as c -> infinity | S* <= S attained in the limit | Kronecker heights triply exponential (S12) | - | sup on [T, 1e7] = 9.6 vs S = 23.7 at lam = 1 | CONVERGE: no c-uniform bound beats l1; on the band the true sup is ~2.5x lower and no theorem gives it (the SUP WALL) |
| measure lemma (S10) provable, zero-blind | Claim A: MV mean square + Chebyshev; moments -> C^{1-eta} | item D: elementary diagonal 4 lam, crude off-diagonal, T^{1-...} | Widder/backward heat reading | - | CONVERGE on provability; constants reconciled below |
| rigorous grid certification cost, lam = 0.7 | 2.6e8 points x 8e3 terms = 2e12 flops | - | - | 5.2e7 x 1.2e4 = 6e11 terms, 0.17 h float / 57 h arb | CONSISTENT: Dirichlet uses generic margin 1, numerics the measured margin 5.04 (spacing 0.02 vs 0.10); both "hours" |
| in-kernel floor vs sharp floor | 5.83 vs 11.53 | - | - | 11.531 | VERIFIED: theta(1 - 3e^{-4}) - 15e^{-4} - log pi = 5.835 at T; log(T/2pi) = 11.531 |

Measure-lemma constants reconciled. Mean square of prime/A over c is sigma^2(lam) = 2 sum Lambda(n)^2 n^{-1} (f0/A)^2:
sieve 0.88, 1.59, 2.34, 3.48, 5.40, 7.34 at lam = 0.3, 0.5, 0.7, 1, 1.5, 2; the zeros lens's 4 lam is the asymptotic
(sum_{n <= x} Lambda(n)^2 ~ x log x gives the integral 2 lam int (1-v)^2 e^{-v} dv = 2 lam per unit, times 2) and is 15
percent high at lam = 1. Both give meas{c in [T, 2T] : F < 0} <= T sigma^2(lam)/floor(T)^2 + off-diagonal; Dirichlet
takes the off-diagonal from Montgomery-Vaughan (primary UNRESOLVED), zeros bounds it crudely by S^2 A^2 e^{...}/T,
valid for T >> e^{6 lam}, which holds on the band for lam <= 2. For a rigorous lemma use an explicit Chebyshev-type
bound sum_{n <= x} Lambda(n)^2 <= C x log x with the diagonal 4 lam C. Moment upgrade: the exponent eta must use the
polynomial's actual length; the zeros lens's k <= log T/(4.7 lam) takes log N_eff = 4.7 lam, the large-lam cutoff,
whereas at lam = 1 log N_eff = 11-14; LLR Lemma 3.2's range k <= log C/(3 log N) gives eta = 0.36-0.40 at lam = 1,
C = 1e8 (Dirichlet), not 0.58 (zeros). Adopt the Dirichlet constants.

## 2. Refutations (three lenses: G = collapse_to_goal, A = single_axis, L = literature)

(a) Heat lens: the plain Gaussian face Theta and the width semigroup. Derivation checked. Variances add under
convolution: e^{-2 lam u^2} has variance 1/(4 lam), the heat kernel of time s has 2s, so P_s e^{-2 lam (.)^2} =
sqrt(lam'/lam) e^{-2 lam' (.)^2} with 1/(4 lam') = 1/(4 lam) + 2s, i.e. lam' = lam/(1 + 8 lam s) < lam (mass
sqrt(pi/2lam) preserved). For a complex centre both sides are entire in the centre and agree on R, so (M) holds
per zero. Fubini over zeros: |e^{-2 lam (x + t + iy)^2}| <= e^{lam/2} e^{-2 lam (x+t)^2} (|y| <= 1/2), whose heat
average is sqrt(lam'/lam) e^{lam/2} e^{-2 lam' x^2}, summable against the zero count; so (M) holds for the actual
zero set, off-line zeros included, and positivity is preserved because P_s is a positive operator with infinite
support (the certificate must cover the WHOLE line at lam). (D) re-derived from (M) and the seed identity
Theta_cc = 16 lam^2 F - 4 lam Theta: F(lam') = (lam/lam')^{5/2} P_s F(lam) - 2s (lam/lam') Theta(lam'), exactly as
fitted; the source term is negative wherever Theta > 0, so F has no monotonicity. Both identities are algebraic;
E6Bridge17 on disk carries `plainGauss_heat`, `rh_iff_theta_positivity`, `exists_theta_neg_of_offline` (statements
seen; build and axiom audit NOT performed here). Grading of RH <-> Theta >= 0: forward trivial; converse an
E6Bridge7 clone whose pair term 2 e^{2 lam (y^2 - x^2)} cos(4 lam x y) is POSITIVE at the ordinate (x = 0) and dips
only at 4 lam x y ~ pi, so the generic-centre-plus-phase choice is load-bearing and E6Bridge14's centre-at-the-
ordinate trick does NOT transfer to Theta (an effective Theta dominance would need a phase-controlled centre).
Until the E6Bridge17 audit lands: argued-not-proved for doctrine. Lambda_Theta >= lam_cert: a real reduction for
the THETA face (one whole-line certificate at lam_cert closes every smaller width, killing the sub-threshold band
there); not for F. Honest reachable number: the Theta prime side has no polynomial factor, S_Theta(lam) = 3.25,
5.62, 8.19, 12.57, 21.8, 34.2 at lam = 0.3, 0.5, 0.7, 1, 1.5, 2, so the Theta band edge is 2pi e^{S_Theta}: 2.3e4
(0.7), 1.8e6 (1), 1.8e10 (1.5), 4.3e15 (2); the trivial bound closes the Theta band above T for lam <= 0.933
(T = 6.4e5) and lam <= 1.725 (T = 3e12). So Lambda_Theta >= 0.93 (kernel ladder) or >= 1.72 (Platt-Trudgian) is
reachable with the l1 bound alone, better than the brief's 0.6 and the heat lens's crude 0.4/0.9, PROVIDED the
Theta-face ladder threshold at T - D is at or below those widths (not computed; expected <= F's 0.27 because the
on-line terms e^{-2 lam x^2} are bounded below by e^{-2 lam gap^2} rather than x^2 e^{-2 lam x^2}). What it asserts
about zeros above the ladder: nothing detectable. A strip-edge zero (y = 1/2) makes Theta dip by at most
2 e^{2 lam y^2 - pi^2/(8 lam y^2)}: 7e-4 (lam 0.6), 0.024 (1), 0.46 (2), 3.1 (3.6) against an on-line background
(log(T/2pi)/2pi) sqrt(pi/2lam) = 3.0, 2.3, 1.6, 1.2 at T = 6.4e5: invisible below lam ~ 3.6 (and at 3e12 the
background is larger). Theta is a WORSE detector than F (F sees y = 1/2 at lam ~ 1). Hence "Lambda_Theta >= 0.93"
is a clean restatement of ladder + envelope + (M): true, unconditional, zero-blind. Verdicts: G no (no RH in (M));
A: the certification content is the envelope + ladder of seam B/C, the monotonicity is new structure (Widder's
backward-heat ill-posedness IS the residual); L: Widder 1944 unread (403), Balanzario-Cardenas read. **TRANSFER
(instrument: a one-parameter dBN-type constant Lambda_Theta); COLLAPSE_TO_FREE as zero content.** Wall: Lambda_Theta
= infinity is RH; lam_cert is capped by the Theta envelope, doubly exponential in lam.

(b) Measure lemma. Statement: for fixed lam, meas{c in [T, 2T] : F(c, lam) < 0} <= T sigma^2(lam)/log^2(T/2pi) +
O_lam(1) (k = 1), and <= T^{1 - eta(lam, T)} with LLR-range moments. G: no RH, no zeros; A: it is a family-average
(capstone clause 2) and a Dirichlet-polynomial mean value, the AF/S9 axis; L: Montgomery-Vaughan 1974 UNRESOLVED
(restated in arXiv 2203.14950, checked by the Dirichlet lens), LLR 1402.6682 checked. **FOOTHOLD as a lemma**
(unconditional, elementary at k = 1, resolves S10 without clustering input), **COLLAPSE_TO_FREE as RH progress**
(a measure, never a sup; Kronecker alignment shows it cannot be pushed to zero). Wall: THE MOMENT WALL (moment
order needed ~ log^2 c/sigma^2, available ~ log c/(3 log N)).

(c) Dirichlet P1 (sharpen the in-kernel floor). Arithmetic verified: sharp floor log(640000/2pi) = 11.531; S(lam)
crosses it at lam = 0.6175 (Dirichlet 0.618; numerics' c_triv(0.618) = 6.48e5 ~ T); in-kernel floor 5.835 crossed
at lam = 0.361; at T = 3e12 the sharp floor 26.89 is crossed at lam = 1.078. So P1 closes whole horizontal lines
lam in [thr, 0.618] (0.361 today) with the l1 bound alone. G: no RH; A: it is the envelope mechanism of seam B
with the sharp constant, nothing else; L: Stirling remainder is textbook. **COLLAPSE_TO_FREE** as content (the
region was free by mechanism, P1 fixes constants); worth doing as hygiene. LARGELY LANDED: E6Bridge16
(`WALL_SHARP_ENVELOPE_2026-09-21.md`, on disk, not audited here) proves `envelopeCsharp` with the exact prime
constant and a capped floor: lam_* = 0.597 at T, c1sharp(1) = 2.07e11 vs the exact 1.26e11 (an e^{1/2} loss);
the residual gain of P1 is 0.597 -> 0.618. Wall: every line closed this way is a blind line (y0 = none at lam <= 0.7).

(d) Numerics "lam = 0.7 closable in hours" vs Dirichlet 2e12 flops: consistent (row above). Rigorous closure of
lam = 0.7 requires the measured margin 5.04 to survive interval arithmetic and the Lipschitz constant 48.8; float
plus a rounding majorant is engineering. **TRANSFER** (finite certification), content nil at lam = 0.7.

(e) Remaining claims, briefly. Zeros lens proposal 1 (effective dominance with certified background): now
partly a theorem, E6Bridge14 `effective_gaussian_dominance` / `offline_zeros_small_or_margin`, with the honest
inputs named (window maximality, spacing floor xmin, count N, tail B); its threshold is unbounded as xmin -> 0
(kernel-checked), which is the clustering wall in explicit form; consumer above T needs y < y1 there: never
applies above the ladder. COLLAPSE_TO_FREE as content, instrument available. dBN transplant (zeros 3): no
dynamics in (c, lam); the Theta face supplies monotonicity (heat 1'), not zero motion; UNRESOLVED as research,
likely collapses to RH <-> Lambda = 0. Hankel / Hamburger, Laguerre-Polya, Lee-Yang, Gabor, tropical, function
field: all COLLAPSE_TO_FREE or TRANSFER of shape, no refutation needed beyond the lenses' own. Turing's method
as a fixed-width object (zeros 6A): correct and important: a Gaussian certificate is one real inequality and
never an integer; WindowOnLine is never reproduced from the prime side. COLLAPSE_TO_FREE.

## 3. Ranked proposals (merged; each: establishes / cost / wall / zero content)

1. P1 floor sharpening (Dirichlet P1; E6Bridge16 already at 0.597). Establishes F >= 0 on every full line lam in
   [thr, 0.618] above the kernel ladder (l1 bound + exact floor). Cost: the last e^{1/2}, small. Wall: envelope
   mechanism. Zero content: none (blind lines).
2. P2 Theta face + Lambda_Theta >= lam_cert (heat P1 + P2 with the sharp S_Theta). Establishes a monotone
   reduction: one whole-line certificate at lam_cert = 0.93 (T = 6.4e5) closes all smaller widths for Theta;
   needs the Theta ladder threshold and the Theta envelope constant in Lean (E6Bridge17 in flight). Cost:
   ~200 lines convolution + constant chase. Wall: Lambda_Theta = infinity is RH. Zero content: a clean
   restatement (Theta blind below lam ~ 3.6 at T).
3. P3 Lipschitz-grid band certificate for F to lam ~ 0.8-0.9 (Dirichlet P2, numerics section 2). Establishes
   full F-lines to 0.8 (days) / 0.9 (heroic). Wall: band length doubly exponential; lam = 1 needs 3.8e12 points.
   Zero content: at lam = 1 a sliver y > 0.39-0.45 above T, mostly inside the classical region; below 1 none.
4. P4 Platt-Trudgian height as a registry hypothesis (Dirichlet P3). Establishes lines to lam = 1.078 with P1
   (Theta: 1.72). Cost: registry composition; re-derive lamThreshold at 3e12. Wall: external certificate trust.
   Zero content: none new (the band closed is the blind band at the new height).
5. P5 Measure lemma, paper then Lean (Dirichlet P4, zeros 2). Establishes the first unconditional non-archimedean
   statement about F on the band. Cost: 2-3 pages; Lean ~300 lines at k = 1 (Zeta23 Chebyshev bounds), blocked on
   Montgomery-Vaughan for the sharp off-diagonal. Wall: measure, not sup. Zero content: none.
6. P6 Effective-O2 consumer (E6Bridge14 instrument). Establishes, from certified window data (Ncount, spacing,
   B pinned), "no zero with y >= y0 in [T1, T2] or a maximal zero in the margin". Cost: pin constB numerically;
   consumer plumbing. Wall: only where zeros are certified, i.e. inside the ladder. Zero content: instrument only.
7. P7 (research, unranked) short-interval zero density at O(1) windows (heat P3, zeros 4): the same clustering
   lemma; a literature statement of why none exists is the deliverable.

## 4. Meta-verdict on "orthogonal approaches for the residual at fixed width"

Genuinely orthogonal readings, both instruments: (i) the prime-side polynomial reading (Dirichlet): at fixed
width the Wall is an almost-periodic trigonometric polynomial of bounded l1 norm sitting under a log floor, with
a provable measure lemma and a sup wall; (ii) the Theta heat structure: widths talk to each other on the plain
face (monotone), not on the derivative face (negative source), which is the exact reason the F-Wall is a diagonal
and gives a one-parameter constant Lambda_Theta. Everything else collapses: zero-density and zero-free regions
(COLLAPSE_TO_RH pointwise, FREE averaged), pair correlation, spectral and function-field readings, Jensen /
Laguerre (S8 face), dBN (structure only), Turing (integer vs inequality). The one-sentence truth: the residual
closes at exactly the widths that see no zeros (lam <= 0.62 free, <= 0.9 by hours to days of numerics, all with
y0 = none above the ladder); the widths that see zeros (lam >= 1.5, y0 ~ 0.2-0.3) have bands to 1e22 and beyond;
the diagonal that joins them is RH. No proposal above moves the diagonal; the two orthogonal readings sharpen
its statement and its cost, and Lambda_Theta gives it a single number to push. conjecture1_proved = False.

## 5. Errata to the lens memos (scoped)

- E1 (zeros lens, section 0 table, last column): log(t*/2pi) at y0 = 1/2 is 4 sqrt(2pi) lam^{3/2} e^{lam/2} (16.5,
  77, 593 at lam = 1, 2, 4), not 8 sqrt(2pi)... (33, 154, 1190); the table's own y0 convention 2 y^2 e^{2 lam y^2} =
  B gives the former. The "detection height = envelope" identity is exact at leading order with the corrected factor.
- E2 (zeros lens, item D): moment range uses log N = 4.7 lam, valid only for large lam; at lam = 1 use log N_eff ~
  11-14, giving eta ~ 0.36-0.40 (Dirichlet), not 0.58. The k = 1 Chebyshev statement is unaffected.
- E3 (Dirichlet lens, section 0): the 23.7 vs 27 discrepancy is NOT the sign-change region of f0; 26.8 is the
  Rosser-Schoenfeld Abel majorant (factor 1.04 plus the boundary term plus integral-vs-sum), a valid upper bound
  on the sieve value 23.72. Reconciliation E5 stands as an upper bound and should quote 23.7 as the value.
- E4 (heat lens, section 1'): lam_cert ~ 0.4 / 0.9 used the F-face crude constant; with the Theta face's own
  trivial bound S_Theta the reachable widths are 0.93 (T = 6.4e5) and 1.72 (3e12), modulo the Theta ladder
  threshold. Also: the centre-at-the-ordinate effective dominance (E6Bridge14) does not transfer to Theta.
- E5 (wall map addendum): "Lambda_Theta <= C/y^2" is configuration-dependent (E6Bridge7 constants); and the
  addendum should carry the sentence "Lambda_Theta >= lam_cert asserts nothing detectable about zeros above the
  ladder at any reachable lam_cert".

## 6. Honesty footer

conjecture1_proved = False. No new (c, lam) instance is proved here; the sieve numbers are float (n <= 1e7 plus an
integral tail), not enclosures; identities (M), (D) are verified algebraically here and numerically by the heat
lens, not audited in Lean (E6Bridge17 present on disk, unbuilt by this pass). UNRESOLVED primaries, merged from the
three lenses: Montgomery-Vaughan 1974 JLMS; Huxley 1973; Halasz-Montgomery / Montgomery LNM 227; Turan's second
main theorem; Bohr 1925; Kronecker; Bohr-Jessen 1930/32; Selberg 1946; Baker-type effective Kronecker bounds;
Littlewood 1924 gap bound and Hall-Hayman; Jutila 1983 / Conrey 1989 exponents; Mossinghoff-Trudgian-Yang 2024
and Bellotti constants; Csordas-Smith-Varga 1994; Csordas-Norfolk-Varga 1986; Deninger's foliated program; the
Weil / Castelnuovo-Severi mechanism (standard texts); Trudgian's Turing constants; Widder 1944; Platt-Trudgian's
Lambda <= 0.2 companion; Newman 1976; Littlewood / Selberg S(t) results; Montgomery 1973; Connes-Consani 2006.13771
verified by the reconciliation pass only; Hinkkanen 1997 / Lagarias 1999 (S8 face). Single synthesis pass; the
three lenses were independent finders, this document is one refuter's vote per lens.
