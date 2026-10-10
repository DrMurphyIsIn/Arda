# Missing Frobenius: angle `connes` (2026-09-24)

conjecture1_proved = False. This is a research report. It is unreviewed except for the skeptic verdict in SKEPTIC_VERDICTS.md, which supersedes it where they disagree.

## Summary

connes: Connes' adele class space and semilocal trace formula, the Connes-Consani archimedean positivity, prolate operators (Connes-Moscovici, CCM), and zeta-cycles (Connes-Consani 2021; Connes-van Suijlekom Nov 2025; CCM "Zeta spectral triples" Nov 2025; Connes "letter" Feb 2026).

VERDICT:
(1) The Connes-Consani archimedean theorem (arXiv 2006.13771) and our KWin use the same window, x = e^{2A} = 2, i.e. supp g in [2^{-1/2}, 2^{1/2}], or [-log2/2, log2/2] additively. They use different test classes:
- Connes-Consani: the pole-free class (ĝ(±i/2) = 0; Theorem 1 also needs ĝ(0) = 0). Least-eigenvalue margins are 0.547 (even), 1.063 (even with ĝ(0) = 0) and 0.847 (odd).
- KWin: the full class, margin 1.33e-3. The kernel floor is 9e-4.
- This tiny margin is exactly the slack of a window Castelnuovo-Severi inequality: 1 + sigma_+ = -0.0012.
(2) Every S-local window certificate is blind to Davenport-Heilbronn:
- At x = 2, D's form has least eigenvalue 0.656, 490 times zeta's.
- D stays positive for S = {inf,2} and S = {inf,2,3} (x <= 5), and up to x of about 31-35.
- So adding p = 3 is worthless as an RH separator. The project's kappa_zeta(11.006) = 0 certificate already covers that range.
(3) New finding: the Connes-Consani-Moscovici zeta-cycle construction reproduces D's zeros just as spectacularly as zeta's, and it breaks down exactly at D's positivity horizon. The Connes-van Suijlekom real-zero theorem applies to D verbatim.
(4) So the only RH-bearing input in the whole Connes program is still global Weil positivity, and CCM's own Corollary 3.8 states that criterion. The missing piece is a positivity (a Hodge index), not an operator.

## Axioms

DICTIONARY (Weil / Deligne 1974 compared with Connes, Selecta Math 5 (1999) 29-106, arXiv math/9811068; Connes-Consani-Marcolli math/0703392):
- The curve corresponds to the adele class space A_Q/Q^x, the arithmetic site / scaling site (arXiv 1405.4527, 1502.05580), Riemann-Roch for Spec Z-bar (arXiv 2205.01391) and "absolute geometry of Spec Z" (arXiv 2606.06604, June 2026; only the abstract was read).
- H^1 corresponds to the cokernel of the restriction map E (Connes' "absorption spectrum"), equivalently the complement of the Sonin space.
- Frobenius corresponds to the scaling action of C_Q -> R_+^x.
- The Lefschetz formula corresponds to Connes' trace formula. The semilocal version (finite S) is PROVED (Connes 1999). The global version is EQUIVALENT to RH.
- The Hodge index corresponds to Weil positivity, W(f*f^*) >= 0. It is open and equivalent to RH (Weil 1952; Bombieri, Rend. Lincei 11 (2000)).

AXIOMS:
- A1: a unitary R_+^x flow whose spectrum on the H^1 part is the set of zeta ordinates. Realized by Connes, conditionally on the cutoff limit.
- A2: a trace formula equal to the explicit formula, with local terms W_p(h) = log p * sum_k p^{-k/2} (h(p^k) + h(p^{-k})). Semilocal version proved, global equivalent to RH.
- A3 (Euler-product locality): the weights w(n) vanish unless n is a prime power, and w(p^k) = log p times a power sum of unit-modulus local roots. THIS IS WHAT D VIOLATES.
- A4 (Hodge index): Q >= 0 on the complement of the trivial classes, which here are the pole functionals f -> f-hat(±i/2) (the analog of the two fibres). This is all of RH.
- A5 (window form of A4; new, elementary, a relabeling):
  - Parity diagonalizes the pole term: it is +2(∫f cosh(u/2))^2 on even tests and -2(∫f sinh(u/2))^2 on odd tests.
  - Lemma H (Haynsworth / rank-one Schur complement):
    - Q0 - 2vv^T >= 0 iff Q0 > 0 and sigma = 2 v^T Q0^{-1} v <= 1.
    - Q0 + 2vv^T >= 0 iff Q0 >= 0, or ind(Q0) = 1 and sigma <= -1.
  - Hence RH iff, for every window x: ind Q0_even = 1, ind Q0_odd = 0, sigma_+(x) <= -1 and sigma_-(x) <= 1. This is the Castelnuovo-Severi shape, since -D^2 has exactly one negative direction.
  - Computed for zeta:
    - The index is (1, 0) at every x tested.
    - sigma_+ = -1.136 (x = 1.5), -1.001203 (x = 2), -1.000155 (x = e^0.8), -1.00000004 (x = 3).
    - sigma_- = 0.004, 0.134, 0.501, 0.99926 at the same windows.
    - So both inequalities saturate as x grows (the equality case, which is the "near-null" phenomenon).
  - Structural reason the pole-free statement (Connes-Consani) and the full-class statement (KWin) are not equivalent: the fibre directions e^{±u/2} are not window-supported, so they cannot be projected off inside the test class.

## Best existing realization and its failure point

1. Connes 1999 (spectral realization plus semilocal trace formula).
   - Failure: removing the cutoff term 2h(1) log Lambda (the global formula) is equivalent to Weil positivity. The construction supplies no sign.
2. Connes-Consani 2006.13771 (June 2020): archimedean positivity on [2^{-1/2}, 2^{1/2}], explained by Sonin compression, prolate functions and a Toeplitz spectrum.
   - Its class is pole-free: same window as KWin (x = 2), different class, margins 0.547 against 1.33e-3.
   - Failure: it is a single place. The arch pole-free form stays positive only up to x of about 3.27. With poles restored, the full class goes negative at x of about 2.1 (odd sector) and 2.5 (even sector).
   - Beyond x = 2, positivity needs primes, and then it is just window Weil positivity, a relabeling (project round 2).
3. Connes-Moscovici 2112.05500 (PNAS 2022, UV prolate spectrum) and CCM 2310.18423 (v2 May 2024, semilocal prolate / Sonin stability).
   - Failure: the archimedean prolate operator contains no primes, so it cannot distinguish zeta from anything with the same Gamma factor. Only the Weyl law matches.
4. The current program:
   - Connes-Consani 2106.01715 (zeta-cycles).
   - Connes-van Suijlekom 2511.23257 (Nov 2025, CMP 2025): the lowest even eigenvector of any lower-bounded real even-kernel form has only real Fourier zeros (Caratheodory-Fejer plus Hurwitz).
   - CCM 2511.22755 (Nov 2025): rank-one perturbed scaling triples built from the minimal Weil eigenvector with primes <= x. Their Cor. 3.8 says "if lim mu_lambda = 0 then RH"; convergence of the determinants to Xi would give RH.
   - Connes 2602.04022 (Feb 2026): primes < 13 give the first 50 zeros to accuracies of 2.6e-55 to 1e-3, exactly on the line.
   - Exact failure point: realness uses no arithmetic, and convergence is equivalent to mu_lambda >= 0 for all lambda, which is Weil positivity.
   - Neither 2511.22755 nor 2602.04022 contains a Davenport-Heilbronn or other negative control (checked via the arXiv HTML).

## Proposal

DH CONTROL OF THE CCM ZETA-CYCLE STRATEGY (Claim P; falsifiable; computed in float64, certifiable in Arb).

Setup. Take the window form Q_x^F with Crux3 conventions. For D: Omega = Re psi(3/4 + it/2) + log(5/pi), weights c_D(n) from -D'/D, no pole. Let xi_x be the lowest even eigenvector and consider the real zeros of its Fourier transform.

(P1) The CvS real-zero theorem applies to D verbatim. Its hypotheses are a real even kernel, lower-bounded, with a simple isolated lowest eigenvalue and even eigenvector; the gap exceeds 1e-3 for x <= 13. So realness of the approximants involves no Euler product.

(P2) Below its horizon, D's zeta-cycles reproduce D's on-line zeros at least as well as zeta's cycles reproduce zeta's, at matched lambda_0. Error on the first zero:
- zeta at x = 4: lambda_0 = 8.0e-13, error 1.4e-9, 5 leading zeros within 1e-2.
- D at x = 15: lambda_0 = 4.0e-13, error 6.9e-12, 10 zeros matched.
- D at x = 17: lambda_0 = 5.8e-15, error 6.6e-14, 13 zeros matched.
- lambda_0^D(x) behaves roughly like lambda_0^zeta(x/5): conductor 5 rescales the window.
So the "spectacular accuracy" cited as evidence is D-blind.

(P3) At D's horizon (between about 31 per Crux3 and 35, the first negative value visible in float64: lambda_0 = -3.2e-11 at x = 35), approximation of ALL of D's zeros collapses together:
- median error on the first 10 zeros: about 1e-13 at x = 34, then 5e-8 at x = 37, 8.8e-3 at x = 40, 0.12 at x = 57.
- Meanwhile the 2nd eigenvector (lambda of about +1e-15) still reproduces D's zeros to 1e-11 or better.
- The negative index is exactly (1 even, 1 odd), matching D's one off-line quadruple, 0.8085 ± 85.6993i (re-verified).
- The lowest eigenvector produces a FALSE real zero shadowing the off-line pair: 85.729 (x = 40), 85.705 (x = 57), 85.698 (x = 80).

(P4) Arithmetic pinpoint. At x = 40 the negative D eigenvector gives Q_D = -0.0250. The Euler-product L(s, chi mod 5, chi(2) = i) has identical archimedean data but gives +2.154 on the same vector. The leading terms of the prime-side difference sit at COMPOSITE n, where an Euler product forces w(n) = 0: n = 6 (-0.472), 14 (-0.310), 21 (-0.300), 26 (-0.300), 34 (-0.189). Prime powers also contribute: n = 4 (-0.240) and n = 9 (-0.185), where c_D(p^k) differs from the Euler value. The total over n < 40 is -2.179.

Kernel-checkable pieces:
- L1: Lemma H, a small Mathlib linear-algebra lemma using PosSemidef and Schur blocks.
- L2: an odd-sector negative witness for Q_D at x = 57, extending Crux3's even dh_band_negative. Together they give the kernel theorem "ind Q_D,57 >= (1, 1)", the Pontryagin-index form of the off-line quadruple.
- L3: the zeta side at x = 57 (lambda of about 1e-150) is NOT feasible.

Falsifiers:
- Arb recomputation shows D's cycles are materially worse than zeta's at matched lambda_0.
- ind Q_D,57 differs from (1, 1).
- The CvS hypotheses fail for D.

## Davenport-Heilbronn control

P1 and P2 are satisfied by D. They use no arithmetic, so they are worthless as RH evidence, and demonstrating that is the point of the proposal. It shows that the numerical agreement in Connes 2602.04022 and CCM 2511.22755, and the CvS real-zero theorem, cannot separate zeta from a function with zeros off the line.

D fails only at the sign of lambda_0(x), for x of about 31-35 and beyond. The input it lacks is A3, Euler-product locality:
- -D'/D has nonzero weights at composite n (c_D(6) = (1+k^2) log 6 = 1.936, c_D(14) = -2.852, c_D(21) = 3.290, c_D(26) = 3.521, c_D(34) = -3.811).
- At prime powers its weights are not local-root power sums (c_D(4) = -(2+k^2) log 2).
- The Euler-product twin L(chi_5), with the same Gamma factor and conductor, stays positive (+2.154 on D's negative vector; least eigenvalue 1.1e-9 at x = 40).

Any Connes-type positivity proof must therefore use prime-power support of the weights at windows x >~ 31.

Lemma H is undefined for D, which has no pole. The correct negative control for the pole structure is an Epstein zeta function of class number > 1 (e.g. x^2 + 5y^2). It is not computed here and is flagged as next.

The "next S" test (add p = 3, x <= 5) is D-blind. D's margins there are 6e-3 to 0.2, against zeta's 1e-8 to 1e-13, so it is worthless as a separator.

## Numerics (untrusted)

All scripts are in /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/frob/connes/. They are float64 numpy plus mpmath, single-process, and nothing is left running.

Scripts:
- weilwin.py (Galerkin, with u-space arch term):
  - Arch term: g(0) psi(1/4 + a/2) + ∫_0^∞ (g(0) - g(u)) W_a(u) du, with W_0 = e^{u/2}/sinh u and W_1 = e^{-u/2}/sinh u.
  - Closed-form autocorrelations; Gauss-Legendre with 8 panels of 400 nodes.
- validate.py: validation (results below).
- scan.py: least eigenvalues for zeta, D, L(chi_5) and arch-only.
- cc_schur.py: Connes-Consani pole-free margins and the Schur scalars.
- hodge.py: the Lemma H invariants for zeta.
- dh_zeros.py: D's zeros.
- zetacycle2.py, shadow.py, shadow2.py, second.py: the zeta-cycle experiments.
- defect.py: the composite-n decomposition.

Validation:
- The code reproduces Crux3's numbers exactly: zeta 0.6988851 and D -0.6545762050 on the Crux3 band test.
- zeta at x = 2 gives 1.333e-3, against the plan doc's 1.329e-3.
- The archimedean constants equal psi(1/4) and psi(3/4) to 15 digits.
- D has 52 on-line zeros below height 100, plus the off-line zero 0.80851718 + 85.69934849i. Together (52 + 2) they agree with the smooth count of about 53.7.

Key tables (least eigenvalue, even / odd):

| x | zeta | D | L(chi_5) | arch + pole only |
|---|---|---|---|---|
| 2 | 1.33e-3 / 7.7e-2 | 0.656 / 1.70 | 0.656 / 1.70 | 1.33e-3 / 7.7e-2 |
| e^0.8 | 1.8e-4 / 1.5e-2 | 0.520 / 1.59 | — | 6.3e-4 / -7.4e-2 |
| 3 | 5.7e-8 / 1.7e-5 | 0.209 / 1.37 | — | -7.4e-2 / -0.43 |
| 5 | — | 6.0e-3 / 0.44 | — | — |
| 11 | — | 7.8e-9 / 9.0e-6 | — | — |
| 35 | — | -3.5e-11 even | — | — |
| 40 | — | -2.5e-2 / -4.6e-3 | 1.1e-9 / 8.9e-7 | — |
| 57 (D) / 80 (D) | — | lambda_0 = -0.852 / -1.25 | — | — |

At x = 80 D gains a second negative even direction. It was not analyzed; a candidate is D's next off-line pair (not re-verified).

Caveats:
- Any value below ~1e-14 is roundoff. That limits the zeta-cycle experiments to x <= 4.
- Connes' 1e-55 accuracies need 100+ digit arithmetic, which is unavailable here (no flint or gmpy2).
- D's horizon is placed only between ~31 (Crux3, high precision) and 35.

Note: the full report text could not be saved as REPORT.md, because the harness blocked writing report files from this subagent. Its content is in this structured output.

## Honest odds

Chance this angle proves RH: well under 1%.
- Every ingredient Connes has built is D-blind or a relabeling of Weil's criterion; this was shown here or by project round 2. That covers the spectral realization, the semilocal trace formula, the Sonin/prolate machinery, zeta-cycles and CvS realness.
- The one RH-bearing input, global Weil positivity (A4), has no candidate mechanism in the literature through Sept 2026. CCM Nov 2025 states its criterion as Weil's (Cor. 3.8).
- The "curve" (arithmetic/scaling site, Riemann-Roch for Spec Z-bar, the June 2026 absolute geometry) would need an intersection pairing whose positivity sees composite-n vanishing (A3). None is known.

Realistic deliverables:
(1) The first explicit DH control of the CCM zeta-cycle program (P1-P4). Cheap to Arb-certify; calibration of publishable quality.
(2) The window Hodge-index dictionary (Lemma H). It explains KWin's 1.3e-3 margin exactly as Castelnuovo slack. It is a small Mathlib lemma.
(3) The kernel theorem ind Q_D,57 >= (1, 1), the odd-sector companion to Crux3.
(4) A precise statement of where Euler-product arithmetic must enter any Connes-type positivity proof: prime-power support, at windows x >~ 31. There, zeta's lambda_0 is about 1e-150 (round 2's estimate), so certifying zeta at that window is currently infeasible.

## Key citations

- Connes, Trace formula in noncommutative geometry and the zeros of the Riemann zeta function, Selecta Math. 5 (1999) 29-106, arXiv:math/9811068
- Connes-Consani, Weil positivity and trace formula, the archimedean place, arXiv:2006.13771 (June 2020)
- Connes-Consani, Spectral triples and zeta-cycles, arXiv:2106.01715 (2021), Enseign. Math. 69 (2023)
- Connes-Moscovici, Prolate spheroidal operator and zeta, arXiv:2112.05500 (Dec 2021), PNAS 2022
- Connes-Consani-Moscovici, Zeta zeros and prolate wave operators, arXiv:2310.18423 (v2 May 2024)
- Connes-Consani-Moscovici, Zeta spectral triples, arXiv:2511.22755 (Nov 2025); Cor. 3.8: lim mu_lambda = 0 => RH; no DH control
- Connes-van Suijlekom, Quadratic forms, real zeros and echoes of the spectral action, arXiv:2511.23257 (Nov 2025), CMP 2025: real zeros of lowest even eigenvector (applies to D verbatim)
- Connes, The Riemann Hypothesis: past, present and a letter through time, arXiv:2602.04022 (Feb 2026): primes<13 give 50 zeros to 2.6e-55..1e-3; no DH control
- Connes-Consani, On the absolute geometry of Spec Z, arXiv:2606.06604 (June 2026; abstract only)
- Connes-Consani, The arithmetic site arXiv:1405.4527; Geometry of the arithmetic site arXiv:1502.05580; Riemann-Roch for Spec Z-bar arXiv:2205.01391
- Connes-Consani-Marcolli, The Weil proof and the geometry of the adeles class space, arXiv:math/0703392
- Weil 1952, Sur les formules explicites; Bombieri, Remarks on Weil's quadratic functional, Rend. Lincei 11 (2000) 183-233; Yoshida 1992 (Adv. Stud. Pure Math. 21)
- Davenport-Heilbronn, J. London Math. Soc. 11 (1936); off-line zero 0.808517+85.699348i (re-verified here)
- Project: arda-crux3 telperion/docs/Crux3_BAND_CERTIFICATE_2026-09-24.md; arda-crux2 RH_CRUX_ROUND2_2026-09-23.md; PRIME_FREE_WINDOW_PLAN_2026-09-23.md; KWin_Window.lean (kwin_primeFreeWindow, floor 9/10000)
