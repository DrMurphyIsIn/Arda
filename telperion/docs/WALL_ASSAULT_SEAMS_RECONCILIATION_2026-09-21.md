# Seam sweep, skeptic replication and reconciliation (2026-09-21)

Replicate-then-reconcile pass (wall-sweep house rule) on `WALL_ASSAULT_SEAMS_2026-09-21.md` and its JSON. Research
only; no Lean; no git state touched. Scratch: `scratchpad/skeptic/{cutoff_reconcile,laplace_face}.py`.
**conjecture1_proved = False.** Nothing here proves RH; survivors are instrument claims. Convergences are
evidence, divergences are errata with scope, UNRESOLVED is never a refutation.

Protocol caveat (honest): the brief asked for blind-first verdicts on S1b, S2, S4. I read the sweep in full
before deriving, so those rows are independent re-derivations from the artifacts, not blind replications.

## 1. Per-seam convergence table

Lenses: G = collapse_to_goal, A = single_axis, L = literature (checked = primary source read this pass).
| Seam | Sweep verdict | Skeptic verdict | G / A / L | Status |
|---|---|---|---|---|
| S1a | TRANSFER | TRANSFER (now a theorem: `RvMBridge10.rh_iff_gaussian_positivity`, axioms std) | no RH used in the equivalence / novelty is coordinates only / Bombieri 2000 not re-read | CONVERGE |
| S1b | COLLAPSE_TO_FREE | COLLAPSE_TO_FREE | no / YES: envelope = Yoshida-CC-Zhu archimedean dominance (Zhu abstract checked: "classical for supp f in [-(log 2)/2,(log 2)/2] (Yoshida; Connes-Consani)"); ladder region factors through certified zeros / checked | CONVERGE, with erratum E1 on "certifiable rectangle" scope |
| S2 | TRANSFER (barrier) | TRANSFER, but the cost table and Lam_max are wrong in both memos; corrected in section 2 | no / the barrier is a property of the PRIME-SIDE Gaussian coordinates, not of the Wall (new seam S8) / Zhu abstract checked | DIVERGE on numbers (E2) and on scope (E3) |
| S3 | COLLAPSE_TO_FREE; implication UNRESOLVED | same | partial (clustering input is RH-adjacent) / dominated by ladder / `gaussian_dominance` read: lam0 = max 1 (max (A/(2 eta K)) (B/(2 M K))) with A = constA rho0 c, B = constB c, eta the maximiser gap: configuration-dependent, non-effective, exactly as stated | CONVERGE |
| S4 | TRANSFER | TRANSFER; ceiling claim needs two scope qualifiers (section 3) | no / yes / AF HTML section 7.2(a), 7.2(e), 7.3 checked verbatim; Zeta23 files read | CONVERGE with erratum E4 |
| S5 | FREE via RH; direct UNRESOLVED | same; nothing new to add, BL 1999 still unread | - / - / UNRESOLVED (BL) | CONVERGE |
| S6 | COLLAPSE_TO_FREE | same; CC Theorem 1 and Corollary 2 confirmed verbatim (section 4) | no / yes / checked | CONVERGE |
| S7a | COLLAPSE_TO_FREE | same: contour shift makes the c-average y-blind | - / ordinate sweep / - | CONVERGE |
| S7b | not the asymmetric coupling | agree: even in y, inside the Weil class, yields an equivalence | - / joint axis / - | CONVERGE |
| S7c | diagonal-wall geometry | descriptive only, and coordinate-bound: lam_res and the widening gap vanish on the rational face (S8) | - / - / - | CONVERGE on content, erratum E3 on scope |

## 2. The bandwidth discrepancy, resolved

Both memos use the same tail bound (Rosser-Schoenfeld psi(x) <= 1.04 x, Abel summation against the term
envelope Lambda(n) n^{-1/2} |f0(log n)|); they differ only in what the tail is compared to. Derivation, from
f0(u) = A (1 - u^2/(4 lam)) e^{-u^2/(8 lam)}, A = f(0) = 1/(8 sqrt(2 pi) lam^{3/2}), and prime density ~ e^u du:

    summand in u  ~  A e^{u/2} |1 - u^2/(4 lam)| e^{-u^2/(8 lam)}  =  A e^{lam/2} |1 - u^2/(4 lam)| e^{-(u - 2 lam)^2/(8 lam)},

peak at u = 2 lam, Gaussian width sqrt(4 lam), and the polynomial factor is ~ lam there, so the FULL absolute
prime envelope is P_abs = 2 A lam sqrt(8 pi lam) e^{lam/2} (1 + o(1)) = (1/2) e^{lam/2} (the memo's c = 0,
lam = 10 row, prime = -74.21 = e^5/2, is exactly this). The tail beyond log N = U is P_abs times
exp(-(U - 2 lam)^2/(8 lam)) up to an erfc factor. Requiring tail <= target gives

    U = 2 lam + sqrt(8 lam log(P_abs / target)).

- The numerics memo takes target = eps f(0). Since P_abs / f(0) = 27, 96, 643, 3.1e3, 1.3e4 at lam = 1, 2, 4,
  6, 8 (computed), its "eps = 1e-3" is a RELATIVE precision of 1.6e-6 at lam = 4 and 8e-8 at lam = 8.
- The sweep takes target = the certification margin m = F(c, lam) itself (what a certificate of F >= 0 must
  beat). Its closed form log X = 2 lam (1 + sqrt(1 + 4 x1^2 + 2 log(C/x1^2)/lam)) is the same formula with
  m = 2 x1^2 e^{-2 lam x1^2} (c midway between zeros) and P_abs = e^{lam/2}/2. Correct in form; but the
  sweep's table then uses X = e^{4.2 lam}, whereas its own formula at x1 = 0.43 gives 4.75 lam (lam = 4),
  4.71 lam (lam = 6): X = 1.8e8, 1.9e12, not 2e7, 9e10. The "+O(x1^2)" was dropped in the table.
- The memo's own section 3 says "the precision needed (signal 0.1-1) is not the obstacle": that sentence is
  right and its Lam_max = 2 table contradicts it, because the table demands 1e3-1e5 times more precision than
  the signal. The memo is right that lam = 4 at eps = 1e-3 f(0) needs 2.9e12 terms; that criterion is the
  wrong one for certification.

Corrected N(lam, eps) (same tail bound; scratch script; "heroic" = 1e9 < N <= 1e12):

| lam | (M) tail <= eps f(0), eps = 1e-3 / 1e-10 | (R) tail <= eps P_abs, 1e-3 / 1e-10 | (C) tail <= F: c = 1e4 midway / c = 1e4 on a zero / c = 3e12 window law |
|---|---|---|---|
| 1 | 1.3e5 / 2.0e7 | 2.8e4 / 7.7e6 | 6.7e2 / 4.8e2 / 2 |
| 2 | 5.2e7 / 9.4e10 | 2.4e6 / 1.5e10 | 4.6e4 / 1.3e5 / 9.6e3 |
| 4 | 2.9e12 / 7.4e16 | 7.3e9 / 2.0e15 | 1.4e8 / 6.4e9 / 4.7e7 |
| 6 | 5.6e16 / 9.3e21 | 7.9e12 / 4.0e19 | 1.1e12 / 7.8e14 / 2.9e11 |
| 8 | 6.7e20 / 4.7e26 | 5.1e15 / 3.1e23 | 9.6e15 / 9.8e19 / 1.5e15 |

Margins in (C): midway m = 2 x1^2 e^{-2 lam x1^2}, x1 = 0.43; on a zero m = 2 g^2 e^{-2 lam g^2}, g = 0.85; window law
m = (log(c/2pi)/2pi) sqrt(pi)/(2 (2 lam)^{3/2}).

Honest Lam_max (bisection on lam at N = 1e12 / N = 1e9):

| criterion | 1e12 sieve | 1e9 sieve |
|---|---|---|
| memo, eps = 1e-3 f(0) | 3.8 | 2.5 |
| relative 1e-3 of P_abs | 5.4 | 3.5 |
| certify, c = 1e4, midway c | 6.0 | 4.4 |
| certify, c = 1e4, c on a zero (binding for a full c-grid) | 4.9 | 3.7 |
| certify, c = 3e12, window law | 6.3 | 4.7 |

Verdict. Neither memo's headline is right. Memo Lam_max = 2 is an artefact of normalising eps to f(0) (its
own "signal 0.1-1" remark refutes it). Sweep Lam_max = 6-7 is the best-case c (midway or high height) with
the O(x1^2) term dropped; on a c-grid that must include zero ordinates the margin decays like
e^{-2 lam g(c)^2} and the binding number is Lam_max ~ 5 (1e12) / ~ 3.7 (1e9) at c ~ 1e4, ~ 6 at
c ~ 1e12 where gaps are small and the window law holds. Both memos agree, and the corrected numbers
confirm, that (i) the cost is singly exponential in lam, (ii) precision is not the obstacle, (iii) with
lam <~ 5-6 the instrument resolves individual zeros only below c ~ 1e6-3e7, inside the ladder. The S3 y_0
numbers should be read at Lambda = 4-6 (sweep's 0.10-0.23), not at Lambda = 2 (memo's 0.23-0.35); both are
below 1/2, so the qualitative S3 verdict is unchanged. At LOW height the on-zero margin is tiny
(c = 100, g = 2.27, lam = 4: m ~ 1e-17), so prime-side certification of a whole rectangle is infeasible
exactly where the ladder is cheapest; this is erratum E1.

## 3. S4 check (Zeta23 PairCeiling and RankTrace, read on disk)

- `ceiling_law256` is a STABILITY inequality: for a certificate (c0, r), r in C^1[0,1] with r' differentiable
  off a countable set and integrable r'', that is VALID AGAINST the N = 256 near-CUE law
  (c0 + sum_j massOf S 256 j r(j/256) <= p), the certificate's value c0 + int_0^1 r(x) x dx is
  <= p + 0.82395317 |r(1)| + 2.5431316e-6 (|r'(1)| + int |r''|). It is a ceiling on the CERTIFICATE CLASS (any
  bandwidth-one (c0, r) certificate that is valid against every configuration must be valid against this
  law), not a statement about the true zeros, and it does not need the certificate to be AF's specifically.
  Two qualifiers the sweep omits: (a) the ONE displayed hypothesis `EnclOK LawN256.K S 0 LawN256.encl` (the
  256 integer enclosures of the law's form factor) was obtained OUTSIDE Lean by interval arithmetic
  (README: sha256 cc3de991..., "available from the authors"); only what is downstream is kernel-checked
  (`decide` on the 255 row inequalities and the edge bound). So "kernel-checked ceiling" = kernel-checked
  modulo EnclOK. (b) The bound is p + 0.824 |r(1)| + ...; the headline 0.6818287 assumes r(1) = 0.
  With those two scopes, the sweep's use is correct: any better window is worth at most ~0.009 over 0.6725.
- `RHLinalg.rank_trace_ineq` (RankTrace.lean): for Hermitian P >= 0 with rank P <= r and n_+(Q) <= b,
  ||P+Q||_F^2 >= c tr P - c^2 r/4 + 2c tr Q - c^2 b. Every input (trace, Frobenius norm, rank, positive index)
  is a spectral invariant; AF 7.2(e) confirms the certificate uses "the first two trace moments" only. The
  sweep's "unitarily invariant, so the pair phase 2 arg w - 4 lam x y is invisible by construction" HOLDS: an
  off-line pair block has inertia (1,1) whatever its phase. CONVERGE.

## 4. S6 check (Connes-Consani arXiv 2006.13771, PDF pages 1-3 read)

Theorem 1 verbatim: "Let g in C_c^infinity(R_+^*) have support in the interval [2^{-1/2}, 2^{1/2}] and Fourier
transform vanishing at i/2 and 0. Then one has W_infinity(g * g^*) >= Tr(theta(g) S theta(g)^*)." Page 2:
support of the test function "contained in the interval (1/2, 2) ... so that rational primes are not involved".
Theorem 6.11 / (5): constant c with 13 < c < 17 when only hat g(i/2) = 0 is imposed. Corollary 2 verbatim:
"c |hat g(0)|^2 + sum_{s in S} hat g(s) conj(hat g(s)) >= Tr(theta(g) S theta(g)^*)", followed by "as if one
would multiply zeta(z) by (z - 1/2)^17". Everything the sweep states is confirmed. CONVERGE. The sweep's
erratum note on roadmap B9 (vanishing conditions omitted) stands.

## 5. Seams the sweep missed (each with lenses)

S8 (new, load-bearing for scope). Laplace-transform the Gaussian family in lam:
int_0^inf lam e^{-s lam} F(c, lam) dlam = Re sum_rho m(rho) w^2/(2 w^2 + s)^2, w = gamma_rho - c, and by
partial fractions in z = rho - (1/2 + ic), a = sqrt(s/2):
    = -(1/4) [ (L(p-) - L(p+))/(4a) - (L'(p+) + L'(p-))/4 ],  L = xi'/xi,  p+- = 1/2 + ic +- a.
Checked numerically (scratch `laplace_face.py`, mpmath, 400 zeros): zero sum vs xi-side agree to the
truncation tail (constant offset 6.7e-4 at four (c, s) points, Im part 1e-27), and the Laplace transform of
F reproduces the zero sum. Forward: on the line the summand is w^2/(2w^2+s)^2 >= 0. Converse: at c = x0 an
off-line pair at +-iy contributes -2 y^2/(s - 2 y^2)^2 -> -infinity as s -> 2 y^2 while all other terms stay
bounded. So RH <=> for all c, s > 0: this rational zero sum is >= 0, and each point is EXACTLY evaluable from
xi'/xi at one point 1/2 + a + ic (Riemann-Siegel cost ~ c^{1/2}, certifiable by interval arithmetic), with NO
prime sum, NO bandwidth barrier and NO resolution law. This is the Hinkkanen-Lagarias face (RH <=>
Re xi'/xi(s) > 0 for Re s > 1/2; attribution via arXiv 2201.08599, which cites Hinkkanen 1997; Lagarias 1999
Acta Arith. 89 primary NOT read: UNRESOLVED as attribution). Verdict: TRANSFER; as a foothold
COLLAPSE_TO_FREE (G: no RH in the equivalence; A: a grid of xi'/xi signs is the argument-principle ladder in
disguise and certifies nothing the ladder does not; L: secondary only). Consequence: the S2/S7c "prime count
is the barrier" and "resolution gap widens without bound" are properties of the PRIME-SIDE GAUSSIAN
coordinates, not of the Wall. Erratum E3.

S9. Second moment in c: the cross term of an off-line pair in int F^2 dc is int |G(x + iy)|^2 dx ~ e^{4 lam y^2},
so it IS y-sensitive; for 4 lam <~ log T it is the AF Frobenius / Montgomery-Vaughan quantity, unconditionally
evaluable, and yields sum_{off-line} T^{y^2}-type control: a zero-density estimate, Ingham-strength only at the
strip edge. Verdict COLLAPSE_TO_FREE (ordinate/joint density; a counted density, capstone's excluded class).

S10. Negative-set density: "for fixed lam, {c <= T : F(c, lam) < 0} has density 0" is far weaker than RH. Sketch:
F < 0 forces an off-line zero with y >= y_0(lam, gap) within O(1) of c, then Ingham. The step fails for O(log T)
near-line zeros clustered within y_0 of c (pair terms negative in the band |x| <~ y against a background of only
gap^2 e^{-2 lam gap^2}): the same clustering input as S3's effective O2. Verdict UNRESOLVED as a lemma; as a
foothold COLLAPSE_TO_FREE (family average, fails capstone clause 2).

S11. d/dlam F = -2 Re sum (gamma - c)^4 e^{-2 lam (gamma - c)^2}: a quartic Gaussian test, still a Hermitian
square inside the Weil class. Verdict COLLAPSE_TO_FREE (weight axis).

S12. Sign structure of the prime side: by Kronecker (independence of log p) there are c where the cosines
align and the prime side is ~ P_abs = e^{lam/2}/2; positivity then forces c >= 2 pi exp(2 P(lam)), the envelope
threshold read from the prime side. The Dirichlet bound on the first aligned c is a LARGER double exponential
(exp(pi(e^{2 lam}) log(1/delta))), so nothing is pinched. Verdict COLLAPSE_TO_FREE (S1b's envelope region).

## 6. Errata (scoped)

- E1 (sweep, meta-verdict and S1b): "every bounded rectangle {c <= C, lam <= Lambda} is certifiable at explicit
  cost" is true only as ladder + low-lam prime sum: the prime side alone cannot certify c at a zero ordinate
  for lam >~ 3 at low height (margin e^{-2 lam g^2}, g ~ 2 at c ~ 100). Scope: rectangle certification =
  ladder region (needs zeros) plus prime side for lam <~ 1-2; the prime-side "feasible lam <= 6-7" is a
  point-certificate statement at generic c.
- E2 (sweep S2 cost table; numerics memo section 3 table and quadrant caption): replace by section 2 above.
  Sweep: X = e^{4.7 lam} not e^{4.2 lam}; Lam_max 5-6, not 6-7. Memo: Lam_max = 2 is a normalisation
  artefact; 4-5 at 1e12, 3.5-4.5 at 1e9. Memo "Lam_max = 4 needs 3e12 terms even at three digits" is true
  for eps = 1e-3 f(0) and irrelevant for certification. Memo section 3 y_0 rows at Lam = 2 remain correct
  as computed; the operative Lambda is 4-6.
- E3 (sweep S2, S7c, meta-verdict wording): "the prime COUNT is [the barrier]" and "the gap widens without
  bound" hold for prime-side Gaussian certification. On the lam-Laplace (rational, xi'/xi) face there is no
  prime count and no resolution law; the residual is plain height, as for the ladder. The meta-verdict
  "coordinates, not content" is STRENGTHENED (a third coordinate system, same content), but the barrier
  sentences must be scoped to the coordinates.
- E4 (sweep S4): "the ceiling is in-kernel" -> "in-kernel modulo the displayed hypothesis EnclOK (256
  enclosures computed outside Lean, sha256 recorded), and with r(1) = 0". No change to the verdict.
- E5 (sweep S1b prose): P(lam) ~ e^{lam/2} sqrt(8 pi lam) omits the polynomial factor ~ lam and the A
  normalisation; the absolute envelope is (1/2) e^{lam/2}, the ratio to f(0) is 2 lam sqrt(8 pi lam) e^{lam/2}
  (27, 96, 643 at lam = 1, 2, 4, computed). The dictionary L_eff is unaffected to leading order.

## 7. Meta-verdict

The sweep's conclusion survives and is sharpened: three coordinate systems for the same clause (C_c^infinity cone;
Gaussian (c, lam) with a prime-side barrier; rational (c, s) with exact xi-side evaluation and no barrier), no new
foothold in any, and every candidate seam here (S8-S12) is TRANSFER, COLLAPSE_TO_FREE, or UNRESOLVED on the same
clustering lemma as S3. The barrier statements are the only overreach: coordinate facts, not wall facts. Kernel
probe priority unchanged (P1 is now `RvMBridge10`); one cheap addition: the S8 identity (zero sum = xi'/xi
expression) as a ~100-line Lean consumer of the zero-sum machinery, scope hygiene only, not progress.

## 8. Honesty footer

conjecture1_proved = False. Primary sources read this pass: Connes-Consani 2006.13771 (PDF pp. 1-3);
Alpoge-Furman 2608.13637 (HTML, section 7.2(a), 7.2(e), 7.3); Zhu 2608.24827 (abstract); Zeta23
PairCeiling/{Ceiling,CeilingLaw256,Defs,Stability}.lean, LinAlg/RankTrace.lean, README; E6Bridge6/7 (statements);
wall_landscape.py (tail-bound code reused verbatim). UNRESOLVED (not read): Lagarias 1999 Acta Arith. 89 and
Hinkkanen 1997 (S8 attribution via arXiv 2201.08599 only); Bombieri 2000; Bombieri-Lagarias 1999; Landau-
Widom 1980; Yoshida 1992; Liu (alphaXiv, Sept 2026). Numerical inputs are float/mpmath estimates, not
enclosures; the S8 identity is checked to truncation accuracy on 400 zeros, not proved. The blind-first
protocol was not met (see caveat at top). Single skeptic pass; the "2 of 3 lenses" kill rule was applied by
one agent and should be read as one vote per lens.
