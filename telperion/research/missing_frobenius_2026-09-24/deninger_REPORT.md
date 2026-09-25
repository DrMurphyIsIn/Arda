# Missing Frobenius: angle `deninger` (2026-09-24)

conjecture1_proved = False. This is a research report. It is unreviewed except for the skeptic verdict in SKEPTIC_VERDICTS.md, which supersedes it where they disagree.

## Summary

deninger: Deninger's foliated dynamical systems. The Lefschetz trace formula plays the explicit formula, the leafwise Hodge/Kahler scaling plays RH, and the angle asks why Spec Z has no realization.

## Axioms

This is Deninger's checklist, taken from ICM 1998 (Doc. Math. Extra Vol. I, 23-46), Progr. Math. 171 (2000), Jber. DMV 103 (2001) and arXiv:0709.2801.

D1 (space and flow). A foliated system (X, F, phi^t) of dimension 3, with a codimension-1 foliation whose leaves are "Riemann surfaces". The R-flow maps leaves to leaves and is transverse to them, except at finitely many preserved compact leaves. Those leaves are the fixed points and correspond to the archimedean place.

D2 (orbits = closed points). Closed orbits correspond to primes p, with length l = log p; for a scheme, l = log N(x), and N(x) is always a prime power.

D3 (H^1). H^i is the reduced leafwise cohomology. On H^0 the generator Theta is 0; on H^2 it is 1 (the pole); on the infinite-dimensional H^1 its spectrum is the zeros.

D4 (Lefschetz = explicit formula). The alternating trace sum_i (-1)^i Tr(phi^*f | H^i) equals sum over gamma of l(gamma) sum_k eps_gamma(k) f(k l(gamma)), plus fixed-point terms. The fixed-point terms must equal W_infinity.
- This is now a theorem in the smooth compact category: Alvarez Lopez, Kordyukov and Leichtnam, arXiv:2402.06671 (Feb 2024), which includes preserved compact leaves.
- For 3-dimensional Riemannian systems: Alvarez Lopez, Kim and Morishita, arXiv:2410.20758 (Oct 2024), Thm 2.5(3): 2 - sum_rho e^{rho x} = sum_gamma l(gamma) sum_k eps_gamma(k) delta_{k l(gamma)}.

D5 (duality = FE). The leafwise Hodge star gives H^i dual to H^{2-i}, which is the s -> 1-s symmetry.

D6 (Kahler = RH). The flow is leafwise conformal, with phi^{t*} omega_F = e^{alpha t} omega_F and alpha = 1. Deninger's Jber. DMV 2001 Thm 2.1 (cited in AKM Thm 1.8) then gives Theta = alpha/2 + skew on H^1, so Re rho = 1/2. Through D4, this Hodge inner product on H^1 is exactly the Weil quadratic form, so D6 is equivalent to Weil positivity for all L, which is equivalent to RH. The project's KWin and KWin2 results are D6 checked on the part of H^1 visible below the first orbit (log 2), and through the log 2 orbit only (width 4/5).

D7 (implicit in Deligne, made explicit here) covers holonomy twists, where local factors are det(1 - rho(gamma) e^{-sl})^{-1}. It has two parts:
- (P) Purity: holonomy eigenvalues have absolute value 1 in every complex embedding.
- (G) Galois coherence: if the characteristic polynomials lie over O_E, then every conjugate local system rho^sigma exists on the same system and satisfies D5 with the same archimedean data. (G) is the analogue of Deligne's companion conjecture (Weil II, Conj. 1.2.10), proved by L. Lafforgue (2002) for curves and Drinfeld (2012) for smooth varieties. These references are from memory and not re-verified.

## Best existing realization and its failure point

R1 is the smooth compact 3-dimensional Riemannian foliated dynamical systems: KMNT, arXiv:1906.02424 (Munster J. Math. 14 (2021)); Kim, arXiv:1912.02159; AKM, arXiv:2410.20758. Here D1, D2 (in weakened form), D4 and D5 hold, but D6 holds only with alpha = 0. Theta is skew on H^1, so the spectrum lies on iR, and H^0 and H^2 are both R with Theta = 0 (AKM Thm 1.8 and Thm 2.5(1)). That is "RH" in the wrong normalization, and it is automatic. Two elementary lemmas, proved in this report, pin the exact failure. Both assume the foliation is an R-Lie foliation given by a closed form omega (AKM Rem. 1.2(2)), normalized so that omega(Y) = 1.
1. Period-group lemma: every orbit length l(gamma) is an integral of omega and lies in omega(H_1(M;Z)), a finitely generated subgroup of R of rank at most b_1. The log p are infinitely many and Q-independent, so no compact finite-dimensional manifold realizes Spec Z. For Spec Z the period group would have to be log Q_{>0}^x, the image of the idele norm. That is where the Connes adelic space enters, and Morishita's arXiv:2508.15971 (2025-26) is the bridge.
2. Volume lemma: L_Y omega = 0, so a leafwise volume scaling as e^{alpha t} would scale the total volume of a compact M. A diffeomorphism cannot do that, so alpha = 0. The Kahler scaling alpha = 1 is therefore impossible without preserved leaves (fixed points, i.e. the archimedean place) or non-compactness. The ALKL 2024 trace formula handles preserved leaves, but nobody has a Hodge theory there.

R2 is the laminated and solenoidal models: Leichtnam, arXiv:math/0603576 (p-adic transversals) and arXiv:1307.3851; Kopei, Abh. Math. Sem. Hamburg 81 (2011). They realize D2 and D4, but there is no leafwise Hodge theory, so the spectral side is defined by the explicit formula itself. For RH that is circular.

R3 is Deninger, "Dynamical systems for arithmetic schemes", arXiv:1807.06400 (v4, 7 Feb 2024), which uses rational Witt vectors. It is the most faithful realization of D1 and D2, but it has no cohomology, no trace formula and no positivity.

R4 is Morin's Weil-etale topos, arXiv:1006.0527. Its cohomology is finite-dimensional and gives special values, not an H^1 that carries the zeros.

The exact failure point: no realization has D3 and D6 together. The missing object is a non-compact or solenoidal foliated space with a preserved archimedean leaf and a leafwise Hodge theory in which the flow is leafwise conformal with factor e^t. Its H^1 inner product would be the Weil form, so building it would restate RH, not reduce it.

Why Deligne's tensor-power trick does not transport (an analysis, not a theorem): the trace on H^1 tensor H^1-bar is |sum_rho e^{t rho}|^2. That requires pointwise products of distributions such as delta_{log p}^2, which are undefined; the degenerate periodic sets gamma x gamma on X x X are the geometric sign of this. Smoothing gives Montgomery's pair correlation F(alpha), which is known only for |alpha| < 1. Beyond that it needs Hardy-Littlewood prime-pair input. That diagonal positivity is where the Frobenius is really missing.

## Proposal

GALOIS-COHERENCE EXCLUSION (GCE) lemma. It is small and plausibly kernel-checkable on the rvm_bridge island, using Mathlib's DirichletCharacter.IsPrimitive.completedLFunction_one_sub and rootNumber from Mathlib/NumberTheory/LSeries/DirichletContinuation.lean (present in the island's Mathlib).

Setup. Let chi be the primitive character mod 5 with chi(2) = i. For real y, let D_y = ((1-iy)/2) L(s,chi) + ((1+iy)/2) L(s,chi-bar); its coefficients are 1, y, -y, -1, 0 by residue mod 5. Then D_kappa = D, with kappa = (sqrt(10-2sqrt5)-2)/(sqrt5-1). Let Lambda_y(s) = (5/pi)^{(s+1)/2} Gamma((s+1)/2) D_y(s).

GCE-1 (FE rigidity). If Lambda_y(1-s) = w Lambda_y(s) for all s, with w = +1 or -1, then (1+iy)/(1-iy) = +r or -r, where r is fixed by rootNumber. So y is y0 or -1/y0 for a single y0. D's own FE pins y0 = kappa without evaluating a Gauss sum. The proof uses Mathlib's FE plus LSeries independence of L(chi) and L(chi-bar) at n = 2 (i is not -i). Estimate: 300-600 lines.

GCE-2 (Galois splitting, pure algebra). kappa is a unit with minimal polynomial x^4+2x^3-6x^2-2x+1 = (x^2+(1+sqrt5)x-1)(x^2+(1-sqrt5)x-1). The first factor has roots kappa and -1/kappa. The second has roots lambda = 1.79360449 and -1/lambda = -0.55753652, which are the images of kappa under sqrt5 -> -sqrt5. Estimate: about 100 lines.

Corollary, conditional on axiom (G): D_lambda has no FE. So no Deninger system with algebraically integral, Galois-coherent holonomy satisfying duality D5 realizes D's explicit formula.

Falsifiable points:
- If rootNumber cannot be pinned through D's FE, GCE-1 needs the mod-5 Gauss sum. That is harder but still finite: a sum of 4 terms in Q(zeta_20).
- If (G) fails for Deninger systems, for example because rho^sigma is not unitary and so has no Hodge theory, then GCE excludes nothing. That gap is exactly why purity (P) must come first.

The two lemmas from the failure analysis (period group; volume forces alpha = 0) are secondary proposals. They are elementary, but Mathlib's support for differential forms is weak.

## Davenport-Heilbronn control

The control has four layers. C1-C3 are computed exactly; C4 numerically.

C1 (arithmetic-scheme axiom D2, independent of any twist). Write D = prod_{n>=2} (1 - n^{-s})^{-b(n)}. For n not a perfect power, b(n) equals the sum over orbits of length log n of eps times the holonomy trace. Exact values: b(6) = 1+kappa^2, b(12) = -kappa^3-kappa, b(14) = -1-kappa^2, and so on. The n <= 60 that are not prime powers but have b(n) nonzero are 6, 12, 14, 18, 21, 24, 26, 28, 34, 36, 39, 42, 46, 48, 51, 52, 54, 56. In short, d(6) = 1 but d(2)d(3) = -kappa^2. So any realization needs closed orbits of length log 6, log 14, and so on, which are not closed points of any scheme over Z. This is the precise form of "no Euler product, hence no log p orbits with the right multiplicities". The kernel already encodes c_D(6) = (1+kappa^2)(log 2 + log 3) as dtab 6 in Crux3_BandDHData.lean.

C2 (untwisted, like zeta itself). The orbit count at log 2 would have to be kappa, about 0.284, and at log 6 it would have to be 1+kappa^2; neither is an integer.

C3 (twisted, integral holonomy). kappa is an algebraic integer, in fact a unit, so integrality alone does not kill D. Galois coherence does. Relative FE defects from mpmath at 40 digits:

| y | w = +1 | w = -1 |
|---|---|---|
| kappa | at most 1.3e-31 | 2 |
| -1/kappa | 2 | at most 2.4e-29 (an "anti-DH" function) |
| lambda = 1.7936 | 0.05 to 0.93 | 1.3 to 1.9 |
| -1/lambda | 0.06 to 2.2 | 1.8 to 4.1 |

So the two sqrt5-conjugates have no FE; exactly half of D's Galois orbit has one. As a control, L(chi) maps to L(chi-bar) with a unit root number, 0.85065+0.52573i.

C4 (growth). D has zeros in Re s > 1 (Davenport-Heilbronn 1936; Titchmarsh 10.25), so its Lefschetz mass per unit length is unbounded. The maximum of |a_D(n)|/log n per dyadic block is 1.08 up to n = 64, 3.58 up to n = 2048, 27.2 up to n = 65536, and 51.8 at n = 111384. For zeta it is at most 1. The growth law was not fitted and may mix divisor-type effects.

Honest limits:
- (G) is automatic for rational coefficients.
- The Epstein function for x^2+5y^2 is killed by C1 (its b(6) = 2).
- The surgered Euler products W_{p,c} with integer c pass C1, C2 and G. They are killed only by purity (P): the holonomy eigenvalues at p have modulus sqrt p.
- Zeta, Dirichlet and Artin L-functions satisfy every one of these axioms, so the filters are consistent with RH but do not imply it.

## Numerics (untrusted)

Scripts are in /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/frob/deninger/. Each ran as a single process, and nothing is left running.
- galois_fe.py (output in galois_fe.out): computes the minimal polynomial of kappa (x^4+2x^3-6x^2-2x+1) and its factorization over Q(sqrt5), and the FE defect table for all four conjugates. kappa satisfies the FE with w = +1 (defect at most 1.3e-31); -1/kappa with w = -1 (at most 2.4e-29); lambda = 1.7936 and -0.5575 have no FE (defects 0.05 to 4.1).
- orbits.py (orbits.out): exact formal Euler exponents b(n) in Q[kappa] for n <= 60. The non-Z[kappa] denominators at 4, 8, 9, 16, 27, 32, 36, 49 come from necklace/Dold terms at perfect powers and do not affect C1.
- growth.py (growth.out): computes a_D(n) up to 2e5 by the recursion d(n) log n = sum_{m|n} a(m) d(n/m); the max of |a_D(n)|/log n reaches 51.8 at n = 111384.
- akm.txt: the extracted text of arXiv:2410.20758, used for the quotes of Thm 1.8, Thm 2.5 and Lemma 2.3.

## Honest odds

The chance that this angle reaches RH is well below 1%, on any foreseeable horizon.
- The only setting with a real Hodge theory (compact Riemannian) is structurally barred from Spec Z by the period-group and volume lemmas.
- The spaces that can host Spec Z (solenoids, Deninger's Witt-vector systems) have no Hodge theory.
- D6 on H^1 is, through the trace formula, literally Weil positivity. Building the Kahler structure restates RH; it does not reduce it.
- The 2024 theorems (ALKL trace formula, AKM determinant formula) strengthen the dictionary but put no pressure on positivity.

Realistic deliverables:
1. The GCE lemma in Lean. This would be the program's first structural (not windowed) exclusion of D, using an arithmetic (Galois) input that FE-plus-growth fooling lemmas cannot see.
2. An exact C1 certificate that D needs an orbit at log 6; it is essentially already in the kernel data.
3. An axiom checklist (C1 / G / P / D6) that sorts every project fake by the arithmetic axiom it violates, leaving D6 as the only axiom that carries RH: D fails C1 and G, Epstein fails C1, W_{p,c} fails P, and the pole-shadow fakes fail entireness.
4. Optionally, the period and volume lemmas in Lean (low priority).
5. A precise pointer: the missing Frobenius is missing at the diagonal restriction of the two-parameter trace, which amounts to pair correlation beyond |alpha| = 1.

## Key citations

- Deninger, Dynamical systems for arithmetic schemes, arXiv:1807.06400 (v1 2018-07-17, v4 2024-02-07) [verified abstract page]
- Deninger, Analogies between analysis on foliated spaces and arithmetic geometry, arXiv:0709.2801 (LMS LN 354, 2008); also arXiv:math/0505354 and The Hilbert-Polya strategy and height pairings arXiv:1001.1621 [verified via arXiv API]
- Deninger, ICM 1998 Doc. Math. Extra Vol. I 23-46; Progr. Math. 171 (2000) 29-87; Jber. DMV 103 (2001) 79-100, Thm 2.1 (skew-symmetry of Theta) [as cited in AKM bibliography]
- Alvarez Lopez, Kordyukov, Leichtnam, A trace formula for foliated flows, arXiv:2402.06671 (Feb 2024, post-2024; solves a Deninger conjecture) [verified]
- Alvarez Lopez, Kim, Morishita, Regularized determinant formulas for zeta functions of 3-dim Riemannian foliated dynamical systems, arXiv:2410.20758 (Oct 2024): Thm 1.8, Thm 2.5, Lemma 2.3 [verified, text extracted]
- Kim, Morishita, Noda, Terashima, arXiv:1906.02424, Munster J. Math. 14 (2021) 323-348; Kim arXiv:1912.02159 [verified]
- Morishita, On a relation between Deninger's foliated dynamical systems and Connes-Consani's adelic spaces, arXiv:2508.15971 (v5 Jan 2026, accepted Munster J. Math.) [verified]
- Leichtnam arXiv:math/0603576 and arXiv:1307.3851; Morin arXiv:1006.0527; Filali-Lemma arXiv:1608.08555; Kopei Abh. Math. Sem. Hamburg 81 (2011) 141-189
- Deligne, Weil II, Publ. IHES 52 (1980) Conj. 1.2.10; L. Lafforgue Invent. Math. 147 (2002); Drinfeld, On a conjecture of Deligne, Moscow Math. J. 12 (2012) [from memory, unverified]
- Davenport-Heilbronn, J. London Math. Soc. 11 (1936); Titchmarsh, Theory of the Riemann zeta-function, 10.25
- Montgomery, Pair correlation of zeros of the zeta function, Proc. Symp. Pure Math. 24 (1973); Connes-Consani arXiv:2006.13771 [unverified]
- Mathlib: DirichletCharacter.IsPrimitive.completedLFunction_one_sub, DirichletCharacter.rootNumber (Mathlib/NumberTheory/LSeries/DirichletContinuation.lean)
