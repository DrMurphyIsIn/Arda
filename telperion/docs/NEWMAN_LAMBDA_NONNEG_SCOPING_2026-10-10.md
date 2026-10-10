# Formalizing Lambda >= 0 (Newman's conjecture): scoping, 2026-10-10

Second item of the agreed RH direction (project_rh_next_direction). This is a plan, not a result. Nothing
is formalized here. conjecture1_proved = False.

## 1. Which proof

Two proofs exist.

**Rodgers-Tao 2018** (arXiv:1801.05914, 61 pp.): assume Lambda < 0, so RH holds and the zeros of H_t are real
and simple for Lambda < t <= 0; the zeros obey the ODE d/dt x_k = 2 sum_{j != k} 1/(x_k - x_j); a Hamiltonian/
energy functional is monotone under it; integrated-energy bounds plus a pigeonholing argument show the zeros
of H_0 are locally in equilibrium (gaps near the average); this contradicts the pair-correlation estimate of
Conrey-Ghosh-Goldston-Gonek-Heath-Brown (itself a theorem under RH, proved by the explicit formula and
Montgomery's method). Ingredients: saddle-point asymptotics of H_t for t < 0 (§2), Riemann-von Mangoldt-type
counts for H_t (§3, Theorem 9), zero dynamics (§4, Theorem 11), gap lower bounds (Prop 13), energy bounds
(Prop 15, Thm 17, §7-8), and CGGGH (§9). Every one of these is new formalization work and the last one is a
substantial analytic-number-theory result in its own right.

**Dobner 2020/2026** (arXiv:2005.05142v2, 35 pp., "A proof of Newman's conjecture for the extended Selberg
class"): for every t < 0, xi_t has zeros off the critical line, found directly. No information about the zeros
of zeta is used; no pair correlation; no dynamics. Rodgers-Tao themselves call it "significantly simpler".
This is the one to formalize. For zeta the argument is:

1. **A contour representation** (eq. 9): for t < 0, xi_t(s) = (1/(i sqrt(pi|t|))) int_{Re w = 2} xi(w)
   exp((s - w)^2/|t|) dw, obtained from the Fourier definition by Fubini and a contour shift to the half-plane
   of absolute convergence of the Dirichlet series.
2. **The approximation** (Theorem 4): in the region |x| <= C y^{1/4}, y large, with s = x + iy,
       xi_t(J_t(s)) = gamma_t(s) ( F_t(s) + O(y^{-1/5} exp((10/|t|) min(x,-2)^2)) ),
   where F_t(s) = sum_n exp(-(|t|/4) log^2 n) n^{-s} is an everywhere absolutely convergent Dirichlet series,
   J_t(s) = s + (|t|/4) Log(s/(2 pi)) is a nonlinear shift to the right, and gamma_t is a gamma-type factor.
   Proof: interchange sum and integral on Re w = 2; each term is a Gaussian integral against gamma(w) n^{-w};
   Stirling for Gamma in vertical strips; the saddle of gamma(w) n^{-w} exp((s-w)^2/|t|) sits at J_t(s).
   Lemmas 4-7 (§5) are the error estimates. This is the bulk of the work.
3. **F_t has a zero** (Lemma 3): F_t is entire of order <= 2 and bounded in right half-planes; if zero-free,
   Hadamard gives F_t = exp(P) with deg P <= 2, boundedness forces P(s) = -lambda s + rho, and a Dirichlet
   series with two or more nonzero coefficients cannot equal a single exponential (uniqueness of coefficients).
4. **Infinitely many zeros at height** (Theorem 5 = Bohr almost periodicity): an absolutely convergent
   Dirichlet series is uniformly close to its own vertical shifts G(s + i tau_m) on any strip, for a sequence
   tau_m -> infinity. So F_t has zeros s_0 + i tau_m + o(1) at arbitrarily large height (Rouche on a small
   circle around s_0).
5. **Transfer to xi_t** (§3.1): h(s) = xi_t(J_t(s))/gamma_t(s) satisfies h(s + i tau_m) -> F_t(s) uniformly on
   the circle (by 2 and 4), so h has a zero near s_0 + i tau_m (Rouche again). Its image under J_t has real
   part x_0 + (|t|/4) log(tau_m/(2 pi)) + o(1) -> infinity, hence lies off the critical line for large m.
6. **Conclusion**: for every t < 0 some zero of xi_t is off the line, so no c < 0 has "all zeros real for all
   t >= c"; in the island's sInf-free form, Lambda >= 0. Theorem 1 (existence of Lambda, for the extended
   Selberg class) uses Hurwitz for closedness of the real-zero set and Polya/de Bruijn for monotonicity.

## 2. What exists already

| Need | Where | Status |
|---|---|---|
| H_t, Phi, H_0 = xi/8, evenness | dbn island (DBNDefs, DBNXi) | proved, judge-verified |
| de Bruijn / Polya monotonicity in t | dbn island (`dbn_debruijn_parametric`, `dbn_real_zeros_upset`) | proved |
| Lambda <= 1/2 and the sInf-free convention | dbn island; registry nodes `RH_dbn_*` | proved |
| Hurwitz, zero-free form, for locally uniform limits | dbn island `DBNHurwitz.hurwitz_ne_zero` | proved |
| Hadamard products / order < 2 | dbn island DBNHadamard* | proved |
| zero-free entire of finite order is exp(polynomial) | LiCriterion `Hadamard/Basic.entire_no_zeros_is_exp_polynomial` (pinned dependency of dbn) | available |
| Dirichlet series: convergence, abscissa, injectivity of coefficients | Mathlib `NumberTheory/LSeries/*` (`LSeries_eq_zero_iff`, `tendsto_cpow_mul_atTop`) | available |
| Borel-Caratheodory, Phragmen-Lindelof, Hadamard three lines | Mathlib `Analysis/Complex/*` | available |
| Cauchy integral on rectangles, contour shifts | Mathlib | available |
| Gaussian integrals, Fubini, Fourier/Mellin basics | Mathlib | available |
| Real Stirling (n!) | Mathlib `Stirling.lean` | available |

## 3. The gaps

1. **Complex Stirling in vertical strips.** Bounds of the shape |Gamma(x + iy)| = sqrt(2 pi) |y|^{x - 1/2}
   e^{-pi|y|/2} (1 + O(1/|y|)) uniformly for x in a compact range, plus the matching bound for the phase, with
   explicit error terms (Dobner's Lemma 7 is a crude version: |gamma(z)| <= exp(K (Re z)^{1.1})). Mathlib has
   Bohr-Mollerup and real Stirling only. The rvm_bridge island cites Stirling in several files (KWin*, E6Bridge*,
   ZhuTail); whether a reusable complex-strip Stirling with error lives there has to be checked, and if it
   does it is likely specialized. Estimate: 1.5-3k lines if written from Binet's formula or the Legendre
   duplication route.
2. **Bohr almost periodicity for absolutely convergent Dirichlet series** (Theorem 5). Not in Mathlib. Proof:
   truncate to N terms uniformly on the strip, then simultaneous Diophantine approximation of
   (tau log n / 2 pi)_{n <= N} mod 1 (pigeonhole on the N-torus) gives tau with n^{-i tau} within epsilon of 1
   for all n <= N; infinitely many such tau. Dobner's density conditions on tau_m are not needed for step 5,
   only tau_m -> infinity. Estimate: 1-2k lines.
3. **Rouche's theorem.** Not in Mathlib, not in Arda. It can be avoided twice over: in step 4 and step 5 use the
   contrapositive of `hurwitz_ne_zero` (if the shifted functions were all zero-free on the disc, the locally
   uniform limit F_t would be zero-free there, but it vanishes at s_0 and is not identically zero). The island
   already states Hurwitz in exactly this form. No new theorem needed.
4. **Theorem 4 itself**: the contour representation, the term-by-term Gaussian integrals, the saddle shift, and
   the error accounting of Lemmas 4-7. This is the core. Estimate: 4-8k lines, dominated by the estimates, and
   it should be formalized in a simplified qualitative form, which is all step 5 uses (eq. 14):
       xi_t(J_t(s)) = gamma_t(s) (F_t(s) + o(1))   uniformly for s in a vertical strip, y -> infinity.
   The explicit y^{-1/5} rate is not needed.
5. **The sInf-free statement and the registry node.** `theorem dbn_newman : forall t < 0, exists z, DBN.H t z = 0
   and z.im != 0` on the dbn island (v4.34.0-rc1, de5ce8a9) composes with the existing `RH_dbn_rh_iff_*` nodes.
   With Lambda <= 9/32 proved at OpenAI's pin, the complete kernel-checked picture would be 0 <= Lambda <= 9/32
   (in one environment if also ported, as the 9/32 closure was).

## 4. Effort and plan

Total: roughly 8-15k lines of Lean over the dbn island's existing 8.6k, i.e. comparable to the island itself;
weeks of session time, not days, with the Stirling bounds and Theorem 4's estimates as the long pole. Order:

1. Bohr almost periodicity (self-contained, Mathlib-only; a good first island module: `DBNBohr.lean`).
2. Lemma 3 (F_t has a zero) from LiCriterion's Hadamard lemma + Mathlib LSeries injectivity (`DBNFtZero.lean`).
3. Complex Stirling in strips with explicit error, as a reusable module (check rvm_bridge first).
4. The contour representation (9) and the term-by-term Gaussian evaluation (exact identities, Telperion can
   certify the completing-the-square algebra).
5. Theorem 4 in qualitative form.
6. Steps 5-6 via Hurwitz; the registry node; the judge.
Each step gets its own node in the rh campaign so the judge certifies them one at a time, as the dbn Hadamard
work was done.

## 5. What this does and does not change

Lambda >= 0 is already a theorem (two proofs, refereed). Formalizing it does not move RH, and the paper that
proves it says so in its first paragraph: Newman's "if RH is true it is only barely so". Its value here is
(a) completing the kernel-checked picture of the de Bruijn-Newman constant, 0 <= Lambda <= 9/32; (b) the
reusable analytic infrastructure (complex Stirling, Bohr, the contour-shift representation of H_t for t < 0)
that any future work on H_t will need; (c) exercising the registry and judge on a multi-node analytic proof
whose inputs are all classical. It is the right next project for the dbn island if the project wants one.
conjecture1_proved = False.
