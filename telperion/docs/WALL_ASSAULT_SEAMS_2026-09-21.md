# Wall assault, the seam sweep: what the in-kernel Weil criterion changes about the Wall (2026-09-21)

> **ERRATA (2026-09-21, scoped; see WALL_ASSAULT_SEAMS_RECONCILIATION_2026-09-21.md, E1-E5):** the S2 cost table uses e^{4.2 lam} where the sweep's own formula gives e^{4.75 lam} at x1 = 0.43, so "lam <= 6-7 feasible" is optimistic (honest ~5-6); the S2/S7c barrier and resolution-gap sentences describe the prime-side Gaussian coordinates, not the Wall (the Laplace-in-lam face, new seam S8, evaluates every point exactly with no prime sum); the S4 ceiling 0.6818 is kernel-checked modulo the external EnclOK enclosures and assumes r(1) = 0; P(lam) omits a ~lam polynomial factor; "every rectangle certifiable" needs the stated scope. No verdict changes; the meta-verdict (coordinates, not content) is strengthened by S8.


Adversarial map under the wall-sweep taxonomy (FOOTHOLD / COLLAPSE_TO_RH / COLLAPSE_TO_FREE /
TRANSFER / UNRESOLVED). Research only; no Lean was written. Builds on the five-sweep capstone
(every axis collapses into the temperedness/positivity clause) and does not re-derive it.
Structured findings: `docs/research/WALL_ASSAULT_SEAMS_2026-09-21.json`.
**conjecture1_proved = False.** Nothing here proves RH; nothing here is progress toward a proof.
Survivors are instrument claims.

## 0. What is now a theorem (the input, read on disk)

`RvMBridge9.zeta_comb_membership_iff_rh` (E6Bridge5..9, axioms propext/choice/Quot.sound): Weil
positivity on Hermitian autocorrelations of C_c^infinity tests <=> Mathlib `RiemannHypothesis`.
The converse went through `gaussTest c lam z = (z-c)^2 exp(-2 lam (z-c)^2)`: an off-line zero
forces `Re zeroSide (gaussTest c lam) < 0` for some centre c and some lam > 0
(`RvMBridge7.gaussian_dominance`, O2), and the Gaussian is a strip-limit of Weil tests
(`RvMBridge8.gaussian_approx`, O1'). Write

    F(c, lam) := Re Sum_rho m(rho) (gamma_rho - c)^2 exp(-2 lam (gamma_rho - c)^2),   gamma_rho = (rho - 1/2)/i.

For a zero at rho = beta + i t, with x = t - c and y = 1/2 - beta, the pair {rho, 1 - conj rho}
contributes 2 m (x^2 + y^2) e^{2 lam (y^2 - x^2)} cos(2 arg(x + i y) - 4 lam x y); on the line it
contributes m x^2 e^{-2 lam x^2} >= 0.

## 1. Verdict table

| Seam | Claim probed | Verdict | Binding wall / what transfer buys |
|---|---|---|---|
| S1a | RH <=> forall c, lam > 0: F(c, lam) >= 0 (the family reduction) | **TRANSFER** | Wall moves intact from the C_c^infinity cone to the (c, lam) quarter-plane; buys coordinates: c = height, lam = resolution. Kernel-derivable today (P1). |
| S1b | Region picture: small-lam / large-height region unconditional; ladder region from certified zeros; residual = Wall | **COLLAPSE_TO_FREE** (both regions) | Envelope region = Zhu Lemma 3.1 / Yoshida / Connes-Consani mechanism (prime side negligible, archimedean dominance): zero content about zeros. Ladder region factors through certified on-line zeros (roadmap B4: near-true by construction). Residual = the diagonal strip lam >= lam_res(c), c -> infinity. |
| S2 | Prime-side certification bandwidth; is it Landau-Widom in these coordinates | **TRANSFER** (barrier identified; as a foothold COLLAPSE_TO_FREE) | Per-point cost is SINGLY exponential, primes to X ~ e^{(4+O(x1^2)) lam}; feasible lam <~ 6-7. Zhu's doubly-exponential threshold reappears as the certified-resolution law lam_1(T) ~ 2 log log T with dictionary L_eff = lam/2 + (1/2) log(2 pi lam). |
| S3 | O2 as a prime-side zero-localisation instrument: certified F >= 0 for lam <= Lambda near c => no off-line zero with y >= y_0(Lambda) | **COLLAPSE_TO_FREE**; the implication itself **UNRESOLVED** (open lemma: effective O2) | y_0(4..6) ~ 0.10-0.23, NOT >= 1/2 (the "useless" hypothesis is refuted numerically). But the implication is not a theorem: `gaussian_dominance` gives lam >= max(1, A/(2 eta K), B/(2 M K)) with eta, A, B configuration-dependent; an effective version needs short-range zero-clustering control at scale 1/(Lambda y_0). At every feasible height the Turing ladder certifies strictly more. |
| S4 | Alpoge-Furman transfer: sharper proportion from a better window or from the exact off-line pair phase | **TRANSFER** (no sharpening) | Rank-trace certificates use only tr and the Frobenius norm: unitarily invariant, so the pair phase 2 arg w - 4 lam x y is invisible to them by construction. Bandwidth-one ceiling 0.6818287 (Zeta23 PairCeiling, kernel) caps ANY window at +0.009 over 0.6725. Beyond: Montgomery form factor for |alpha| > 1 / higher moments = prime-pair (Hardy-Littlewood-type) input (AF section 7.2(a), 7.2(e-f), 7.3). |
| S5 | Li face: is `li_criterion_rh_iff` now derivable in-kernel via a direct Weil -> Li dictionary | Via RH: **COLLAPSE_TO_FREE** (vacuous, and not even single-kernel: islands differ). Direct dictionary: **UNRESOLVED** | rvm_bridge is Lean v4.33.0-rc2 / Mathlib 51e6992; li_positivity is v4.34.0-rc1 / Mathlib de5ce8a: the composition is a two-island statement. The direct BL dictionary needs the explicit formula on BL's non-compact g_n (B7 admissibility gap) and whether g_n is an autocorrelation limit; BL primary source paywalled this session. Non-vacuous finite content: localized vs global detector costs (section 5). |
| S6 | Connes-Consani archimedean positivity vs the small-lam region: same foothold | **COLLAPSE_TO_FREE** (same mechanism, different coordinates) | CC Theorem 1 (verified from the PDF): support [2^{-1/2}, 2^{1/2}], hat g(i/2) = hat g(0) = 0, W_infinity(g * g^*) >= Tr(theta(g) S theta(g)^*); rational primes "not involved" at that support. Gaussian small-lam region is the same archimedean-dominance foothold with the prime side small instead of empty. Neither extends past the prime threshold except by certified computation (Zhu L = 0.8). |
| S7a | c -> infinity asymptotics of F with the RvM density | **COLLAPSE_TO_FREE** (the ordinate sweep) | Integral over c of the pair term is independent of y (contour shift): the c-average of F is N(T) sqrt(pi)/(2 (2 lam)^{3/2}) whatever the zeros' real parts. Reflection-blind by construction. |
| S7b | Is the phase term 4 lam x y the "asymmetric coupling" the capstone asked for | **No** | The pair term is even in y and the family lies inside the Weil class: it re-symmetrizes (fails clause 3) and yields an equivalence, not an unconditional statement (fails clause 1). It is a joint (x, y) coupling, which is exactly the capped joint axis. Escape stays unpopulated. |
| S7c | The diagonal-wall geometry (new, descriptive) | TRANSFER-grade observation, no verdict inflation | Resolution needed to see one zero at height c: lam_res(c) = (log(c/2 pi))^2/(4 pi^2). Certified resolution from a ladder of height T: lam_1(T) ~ 2 log log T. The gap widens without bound (section 3). |

Meta-verdict: the in-kernel Weil criterion changes the Wall's COORDINATES, not its content.
The temperedness/positivity clause is now the statement "F(c, lam) >= 0 on the quarter-plane";
every bounded rectangle {c <= C, lam <= Lambda} is certifiable at explicit cost, and the residual
is the infinite-height diagonal. No new foothold. Two open lemmas (effective O2; BL admissibility)
and one transfer (AF bandwidth) are the only places where work that is not RH itself remains.
conjecture1_proved = False.

## 2. S1: the two-parameter Wall

Family reduction (S1a). Forward: under RH every gamma_rho is real, each summand is
x^2 e^{-2 lam x^2} >= 0, and the sum converges (`summable_gauss_zeroSide`). Converse: the
contrapositive of `gaussian_dominance` plus `rh_of_all_on_line`. So
RH <=> forall c, forall lam > 0, 0 <= Re zeroSide (gaussTest c lam)
is a ~60-line theorem on the island today (P1). Literature: Weil's original localisation uses
a concentrating family; Bombieri 2000 (abstract verified) proves the C_c^infinity form and the
finite-truncation index count; a two-parameter Gaussian *equivalence* is not stated in any
source read this session (secondary hits only; UNRESOLVED as a literature attribution).
Note the zero-side form mentions no primes; the prime-side form needs the explicit formula
for the Schwartz test phi * phi~ (P2), a Tannery limit on all three sides.

Region picture (S1b). Write P(lam) := Sum_n Lambda(n) n^{-1/2} e^{-(log n)^2/(8 lam)}, the
Gaussian comb mass; by Chebyshev partial summation P(lam) ~ e^{lam/2} sqrt(8 pi lam) for lam >~ 1
(the integrand e^{u/2 - u^2/(8 lam)} peaks at u = 2 lam), and P(lam) ~ 2^{-1/2} log 2 e^{-(log 2)^2/(8 lam)}
for lam << 0.1. The archimedean side is ~ log(c/2 pi) sqrt(pi)/(4 pi (2 lam)^{3/2}) for c > 2 pi.

- Envelope region {log(c/2 pi) >~ 2 P(lam)}: F(c, lam) >= 0 unconditionally because the
  archimedean integral beats the absolute prime sum. Threshold c_1(lam) ~ 2 pi exp(2 P(lam)):
  doubly exponential in lam. This is Zhu's T_1(L) = 2 pi e^{A_L}, A_L ~ 4 e^L, under the
  dictionary A_L <-> 2 P(lam), i.e. L_eff = lam/2 + (1/2) log(2 pi lam). Small lam at fixed c is
  the same region read the other way (P(lam) -> 0 super-exponentially). Zero content about
  zeros: the bound never looks at the zero side.
- Ladder region {c <= T - D(lam)}: with all zeros of height <= T certified on the line, the
  uncertified tail is bounded by e^{2 lam (1/4 - D^2)} times the summable majorant
  (`summable_mult_div_one_add_normSq`, Zeta23 `zero_sum_inv_sq`), while the nearest certified
  zero contributes x1^2 e^{-2 lam x1^2}; D^2 >= x1^2 + 1/4 + log(C/x1^2)/(2 lam) suffices, so
  D ~ 1-2 for lam >= 1. Cross-island: the ladder lives on li_positivity (v4.34.0-rc1).
- Residual: {T - D < c < c_1(lam)} for lam above lam_1(T), where c_1(lam_1) = T, i.e.
  lam_1(T) ~ 2 log log T (~0.7 at T = 6.4e5, ~1.6 at T = 3e12). Below lam_1 the whole line of
  centres is certified; above it an unbounded height interval is not. As T grows the certified
  resolution grows doubly-logarithmically. This is the Landau-Widom/Zhu barrier in these
  coordinates (S2): verified height buys resolution at rate 2 log log T.

Refutation record (S1b claimed FOOTHOLD initially): collapse_to_goal no (no RH used); single_axis
YES (archimedean dominance = Yoshida / CC Theorem 1 / Zhu Lemma 3.1, all checked) -> demoted to
COLLAPSE_TO_FREE; literature: Zhu abstract and CC PDF read.

## 3. S2 and S3: bandwidth, resolution, and the localisation instrument

Cost of one point. The prompt's formula "primes to exp(sqrt(8 lam log(1/eps)))" is the naive
support criterion e^{-(log n)^2/(8 lam)} <= eps; it omits the n^{-1/2} against the ~n density of
Lambda(n), i.e. the e^{u/2} weight. Adjudicated: the tail beyond log X = U is
~ e^{lam/2} e^{-(U - 2 lam)^2/(8 lam)}, and the margin to certify (F itself under RH, c midway
between zeros with half-gap x1) is ~ x1^2 e^{-2 lam x1^2}. Hence

    log X ~ 2 lam (1 + sqrt(1 + 4 x1^2 + 2 log(C/x1^2)/lam)) ~ (4 + O(x1^2)) lam.

With X = e^{4.2 lam}: lam = 4 -> X ~ 2e7 (cheap); 5 -> 1e9 (cheap); 6 -> 9e10 (sieve-scale);
7 -> 6e12 (edge of feasibility). Precision is not a barrier (cancellation ratio only e^{lam/2 + 2 lam x1^2}); the prime COUNT is.
A c-grid needs spacing ~ margin / (log c) because F is Lipschitz in c, and lam must be gridded
too; both multiply cost polynomially, not exponentially.

Why this is not Landau-Widom in the cost sense. Zhu certifies a CONE (all f with support in
[-L, L]) and pays a doubly-exponential matrix (N ~ L T_1) plus a margin that collapses at the
Landau-Widom rate (-ln lambda*(L) ~ 2 pi^2 N(T*)/ln N(T*), fitted). A Gaussian point certificate
is one scalar: singly exponential cost and margin, NO cone conclusion, infinitely many points
needed, still finite height. Landau-Widom enters the Gaussian family only through resolution: the r-width of
|h|^2 = x^2 e^{-2 lam x^2} is 1/(2 sqrt lam); the mean zero gap at height c is 2 pi/log(c/2 pi);
resolving one zero needs

    lam >= lam_res(c) = (log(c/2 pi))^2 / (4 pi^2)     (1.4 at c = 1e4; 3.4 at 6.4e5; 18.7 at 3e12).

With lam <= 6-7 feasible, the instrument resolves individual zeros only below c ~ 3e7, where the
ladder (6.4e5 in-kernel, 3e12 published) already certifies every zero exactly. Combined cost
per height is X ~ c^{log c/(pi^2)}: super-polynomial in height, versus c^{1+o(1)} for
Odlyzko-Schonhage verification.

S3 numbers. Using the Phase-0 nearest-neighbour law lam* = log(x1^2/(2 y^2))/(2 (x1^2 + y^2))
where it applies (lam >~ lam_res) and the window-sum law 2 y^2 e^{2 lam y^2} > (log(c/2 pi)/2 pi)
sqrt(pi)/(2 (2 lam)^{3/2}) where it does not:

| Lambda | c = 1e4 (x1 ~ 0.43) | c = 3e12 (window law) |
|---|---|---|
| 4 | y_0 ~ 0.14 | y_0 ~ 0.23 |
| 6 | y_0 ~ 0.10 | y_0 ~ 0.18 |

So y_0 is well below 1/2: the bandwidth barrier does NOT make the instrument vacuous. What
does: (i) the implication "F >= 0 on the grid => no zero with y >= y_0" is not a theorem. The
crude absolute bound fails once the window holds >= 2 other zeros (terms with x_j ~ pi/(4 lam y)
have positive phase and full size); `gaussian_dominance` escapes only through a configuration-
dependent lam (gap eta, window sum A, majorant B). An effective O2 needs clustering control at
scale 1/(Lambda y_0), short-range pair-correlation territory where the only unconditional
input is the O(log t) unit-window count. Natural attack: average over lam in
[Lambda/2, Lambda] (the pair term is monotone in lam, the hurting terms oscillate with
frequencies 4 x_j y_j); unproven. (ii) Even granted, at every feasible height the ladder
certifies exactly, not to within y_0. Verdict: COLLAPSE_TO_FREE to the ladder; the
refutation direction (a certified F < 0 refutes RH) is already `weil_negative_refutes_rh`.

## 4. S4: the Alpoge-Furman transfer

AF (arXiv:2608.13637, abstract and section 7 read; Lean in Zeta23 read on disk) compress
Weil's form to a finite Gram matrix over a window of tests of Fourier support in [-1, 1]
(pair-correlation scale), evaluate tr and ||.||_F^2 on the prime side through
Montgomery-Vaughan (diagonal dominance, X <= T), and apply the rank-trace inequality with
Sylvester inertia for off-line pairs. Three facts fix the transfer:

1. Unitary invariance. tr and the Frobenius norm see only the spectrum. The off-line pair
   block has signature (1,1) whatever its phase; the corpus's exact phase 2 arg w - 4 lam x y
   is a basis-dependent datum and cannot enter a rank-trace certificate. So the corpus's
   E6Bridge7 pieces cannot sharpen AF by construction.
2. The ceiling is in-kernel. `Zeta23.PairCeiling.ceiling_law256`: every bandwidth-one
   certificate of AF's type certifies at most 0.6818287 + 2.55e-6 (|r'(1)| + int |r''|)
   simple on-line zeros. The optimal window (Montgomery-Taylor, 0.6725) is within 0.009 of
   the cap. "A better window" is worth at most that.
3. What lies beyond is named by AF themselves: section 7.2(a) "for X >> T the off-diagonal
   prime sum is no longer dominated by the diagonal, and its evaluation would require
   information on prime pairs"; section 7.3: with Montgomery's form factor known on
   (-lambda_0, lambda_0) for all lambda_0 the method would certify 100 percent; section
   7.2(e-f): higher moments are unavailable unconditionally. In Gaussian coordinates,
   bandwidth one is 4 lam <~ log T, i.e. lam <~ log T/4, far below lam_res(T) ~ (log T)^2/(4 pi^2):
   bandwidth-one windows average over ~ log T zeros, which is why they yield proportions and
   never a named zero (the capstone's excluded class).

Verdict TRANSFER. The open lemma, stated concretely: an unconditional evaluation of the prime
side of a compressed Weil form with Fourier support in [-lambda_0, lambda_0] for some
lambda_0 > 1 (equivalently Montgomery's F(alpha, T) for 1 < alpha <= lambda_0), or of a third
moment tr(A^3). Both are prime-pair statements; no unconditional method is known.

## 5. S5 and S6: the Li face and Connes-Consani

Li. `li_criterion_rh_iff` is a proved upstream theorem (LiCriterion pin 35df682f, axiom-guarded
on li_positivity). Composing it with `zeta_comb_membership_iff_rh` gives Li positivity <=> Weil
positivity, but (a) routed through RH it is vacuous (roadmap section 1), and (b) the two
islands have different toolchains, so it is not a single kernel statement. The non-vacuous
direct dictionary (each lambda_n as the Weil form of a BL test, without RH) needs the explicit
formula on BL's non-compact g_n (a Tannery limit of the same shape as O1', majorant
n^2/|rho|^2 summable) and the fact, not verified this session, that the positivity direction
Weil -> Li uses autocorrelation-type tests; BL 1999 was paywalled, so UNRESOLVED.
What IS non-vacuous and finite-grade: the two faces are height-localized versus global
detectors. A zero at (t, y) needs Li index n ~ t^2/y (the (1 - 1/rho)^n blow-up rate 2 y/t^2)
at ~n bits of precision and cubic cost (LI_LADDER_COST_MODEL), versus Gaussian lam ~
log(1/y)/x1^2 at centre c ~ t and primes to e^{4 lam}. At t = 1e12 the Li face needs
n ~ 1e24 rungs; the Gaussian face needs ~1e10 primes. Instrument fact only; both are
finite-height. Non-effective inter-conversion (lambda_n < 0 => some F(c, lam) < 0 and back)
holds through the existence of an off-line zero and carries no effective (n, c, lam) map;
an effective map is blocked by Freitas delocalization on the Li side.

Connes-Consani. Theorem 1 of arXiv:2006.13771 (PDF read): for g in C_c^infinity with support
in [2^{-1/2}, 2^{1/2}] and hat g vanishing at i/2 and 0, W_infinity(g * g^*) >= Tr(theta(g) S theta(g)^*),
S the projection onto Sonin's space; the paper states that at this support "rational primes are
not involved". Corollary 2 shows the Sonin trace equals the zero sum up to c |hat g(0)|^2 with
13 < c < 17, "as if one would multiply zeta by (z - 1/2)^17": an archimedean positivity with an
artificial order-17 zero at 1/2, irrelevant for RH. Half-width (log 2)/2 = Yoshida's range
(Bombieri 2000 abstract: "prove again Yoshida's theorem"; Zhu abstract: same attribution).
The Gaussian small-lam / large-height region is the same foothold in coordinates where the
prime side is small rather than empty and the archimedean side grows like log c. Both stop at
the prime threshold; the only known way past is certified computation (Zhu L = 0.8; the Sept 2026
alphaXiv preprint by V. Liu claiming L = 1 and 17/16 is under review, not reproduced: UNRESOLVED).
The prolate papers (Connes-Moscovici arXiv:2112.05500, abstract read) are a spectral realization
statement, not a positivity extension, and do not move the threshold.

## 6. Kernel probes, in priority order (rvm_bridge island, Lean v4.33.0-rc2)

P1 (cheap, do first). `theorem gaussian_criterion_iff : RiemannHypothesis <-> forall c lam : R,
0 < lam -> 0 <= (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re`. Forward: `Zeta23.RH_implies_on_line`,
gaussTest on a real argument is x^2 e^{-2 lam x^2} >= 0, `summable_gauss_zeroSide`, real part of
a tsum. Converse: contrapositive of `RvMBridge7.gaussian_dominance` and `RvMBridge6.rh_of_all_on_line`
/ `strip_of_zero`. About 60 lines. Value: the Wall in two real parameters, in-kernel. Negative
control: `gaussTest_axis_re_neg` already shows the converse direction is load-bearing.

P2 (the prime-side form). `theorem gauss_explicit_formula (c lam) (h : 0 < lam) :
archSide (autocorr (gaussPhi c lam)) - primeSide (autocorr (gaussPhi c lam)) = zeroSide (gaussTest c lam)`
where archSide/primeSide are read as absolutely convergent for the Schwartz test. Proof: Tannery
along `RvMBridge8.gaussTests` on all three sides; prime majorant Lambda(n) n^{-1/2} sup_n |g_n(log n)|
summable via partial summation against `Zeta23.Chebyshev.sum_vonMangoldt_div_sqrt_le`; arch majorant
from `Zeta23.GammaFacts.re_digamma_vertical`. About 300 lines. Value: turns P1 into the
membership form F(c, lam) = arch - prime >= 0 that any prime-side certificate consumes.

P3 (the envelope region, after P2). `theorem gauss_positivity_of_large_height (lam) (h : 0 < lam) :
exists c1, forall c >= c1, 0 <= F c lam`. Inputs: lower bound on the archimedean integral from
`re_digamma_mono` / `re_digamma_vertical` (Zhu's Lemma 3.1 Binet route is NOT in Mathlib; the
Zeta23 Stirling-type bounds are the available substitute) and the Chebyshev prime bound. About
400 lines. Value: kernel anchor of the unconditional region, zero RH content, states the
c_1(lam) ~ 2 pi e^{2 P(lam)} threshold explicitly.

P4 (ladder region, hypothesis-as-parameter, deferred). `theorem gauss_positivity_below_ladder
(T) (hT : forall rho, IsNontrivialZero rho -> |rho.im| <= T -> rho.re = 1/2) (lam) (h : 1 <= lam)
(c) (hc : c <= T - 2) : 0 <= F c lam`, tail via `summable_mult_div_one_add_normSq`. Cross-island
consumer of the ladder statement; B4-grade significance warning applies.

P5 (research, paper proof first, do not author). Effective O2: `forall y0 > 0, forall t0, exists
Lambda, forall rho off-line with 1/2 - Re rho >= y0 and |Im rho - t0| <= 1/2, exists c in [t0-1, t0+1],
exists lam <= Lambda, F c lam < 0`. The lam-averaging attack of section 3 is the candidate; its input
is a short-range clustering bound that does not exist unconditionally. The only probe here whose
success would be a new instrument.

## 7. Honesty footer

conjecture1_proved = False. Verified this session (read, not cited from memory): Connes-Consani
arXiv:2006.13771 (PDF, Theorem 1, Corollary 2); Alpoge-Furman arXiv:2608.13637 (abstract; HTML
section 7.2/7.3); Zeta23 README and PairCeiling (on disk); Zhu arXiv:2608.24827 (abstract; the
Zhu import memo for the theorems); Bombieri 2000 (EUDML abstract only); Connes-Moscovici
arXiv:2112.05500 (abstract only). UNRESOLVED primary sources (primary-verify before any kernel
probe cites them): Bombieri-Lagarias 1999 JNT 77 (sciencedirect 403; the S5 autocorrelation
question rests on it); Landau-Widom 1980 JMAA 77 (403 twice; cited only through Zhu's abstract);
Yoshida 1992 Adv. Stud. Pure Math. 21 (no primary access; range corroborated by three checked
sources); attribution of the two-parameter Gaussian equivalence to any published source; Liu,
"Certified Weil positivity beyond the unit window" (alphaXiv, Sept 2026, under review). Numerical
inputs (lam*, y_0, cost table) are float-model estimates, not enclosures. Replicate-then-reconcile
has not been run; verdicts are single-run until a second pass agrees.
