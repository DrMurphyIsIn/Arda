# Missing Frobenius: angle `geometry` (2026-09-24)

conjecture1_proved = False. This is a research report. It is unreviewed except for the skeptic verdict in SKEPTIC_VERDICTS.md, which supersedes it where they disagree.

## Summary

geometry: curve over F_1 / absolute geometry (Borger lambda-rings, Connes-Consani arithmetic site and Riemann-Roch, Fargues-Fontaine curve, Scholze's analytic stacks, Habiro ring, Arakelov/Faltings-Hriljac)

## Axioms

This compares the Weil/Deninger/Connes dictionary with the six properties of C x C that Weil used over F_q: F1 the classes, F2 composition, F3 Lefschetz, F4 Hodge index, F5 finite genus, F6 Euler product. The missing object "Spec Z-bar x_{F_1} Spec Z-bar" would need:

(A1) An intersection pairing on a class group that contains the diagonal Delta, the graphs Gamma_lambda (lambda in R_+^*) of the scaling Frobenius, and two fibre classes.

(A2) Composition: Gamma_lambda o Gamma_mu = Gamma_{lambda mu} and Gamma_lambda^t = lambda Gamma_{1/lambda}. For smeared classes, f -> Gamma_f is an algebra map. This is what makes the Weil form translation-invariant (Toeplitz). D and E also satisfy it.

(A3) Trace formula = Weil explicit formula. Gamma_f . Delta = fhat(0) + fhat(1) - sum_rho fhat(rho) = sum_v W_v(f). This is a theorem (Weil 1952; Connes, Selecta 1999, with the semilocal trace formula proved).

(A4) Hodge index. D_f^2 <= 0 for primitive smeared classes, i.e. sum_v W_v(g * gbar^#) <= 0. This is exactly RH (Weil's criterion; stated as eq. (2) of Connes-Consani arXiv 2006.13771, checked).

(A5) Infinite genus. dim H^1 = infinity and Delta^2 = 2 - 2g = -infinity. So the pairing can only be a distribution, positivity only makes sense for smeared classes, and there is no finite Castelnuovo-Severi and no tensor-power trick.

(A6) The separating axiom: locality / Euler product. The fixed points of Frob_lambda on Delta are the periodic orbits p^k with weight log p (Lambda supported on prime powers, multiplicatively generated). D fails A6. The new Epstein control E fails ONLY A6.

## Best existing realization and its failure point

(1) Connes-Consani. They have the semilocal trace formula, the arithmetic site whose square carries Frobenius correspondences, and a Riemann-Roch theorem for Spec Z-bar (arXiv 2205.01391, May 2022 / v2 March 2023, checked). Their archimedean Weil positivity (arXiv 2006.13771, June 2020, PDF checked) covers test functions supported in (1/2, 2). They say explicitly that this result was proved by H. Yoshida (1992) through an explicit computation. So the project's KWin (2L <= log 2) is Yoshida's theorem; what is new is the kernel check. Failure point: their Riemann-Roch is on the curve, not the surface, and the square has no intersection theory satisfying A3 and A4 together. Worse, a Riemann-Roch/theta mechanism holds class by class, and the Epstein zeta E of the principal class of Q(sqrt-5) has zeros off the line (section 3).

(2) Borger's lambda-rings (arXiv 0906.3146). Coproduct = tensor product and Z is initial, so Spec Z x_{F_1} Spec Z = Spec(Z tensor Z) = Spec Z. The square is 1-dimensional: there is no surface. The Frobenius lifts psi_p are the identity on Z.

(3) Fargues-Fontaine curve (Astérisque 406) and Fargues-Scholze (arXiv 2102.13459). The curve is complete with Pic = Z, H^0(O) = Q_p and H^1(O) = 0, so it has genus 0. The local Frobenius only gives the H^0 Euler factor (1 - p^{-s})^{-1}; the zeros are a global H^1 that no local object sees (the same is true over F_q). The local square Spd Z_p x_{F_p} Spd Z_p with partial Frobenii (Drinfeld's lemma, Scholze-Weinstein) is taken over F_p, not F_1, and nothing glues the different primes. Scholze's papers from 2025-26 (arXiv 2501.07944, 2510.15196 with Anschütz-Bosco-Le Bras-Rodríguez Camargo, 2605.03655, 2605.11731 with Clausen) are local or foundational. I could not verify any published statement of his hoped-for Spec Z x_{F_1} Spec Z.

(4) Habiro ring, Garoufalidis-Scholze-Wheeler-Zagier (arXiv 2412.04241, 5 Dec 2024, abstract checked). It makes no claim about zeta zeros, RH or F_1. As an F_{1^n} = mu_n tower it is the analogue of constant-field extension, but going from Q to Q(mu_n) adds new H^1 (the L(s, chi) zeros) instead of raising Frobenius eigenvalues to the n-th power. So it provides no amplification.

(5) Faltings-Hriljac arithmetic Hodge index. It is proved, but for a curve over Q fibred over Spec Z, not for Spec Z x Spec Z. Its only RH-sign consequence that I know of is L'(E/K,1) >= 0 via Gross-Zagier. The computable Arakelov numbers (omega^2 of X_0(N), Kühn's zeta'(-1) formula) are Euler-product data that D lacks, but they do not constrain zeros.

(6) Deligne's tensor-power trick has no analogue over Q. The prime-side distribution has atoms on the non-discrete set {log n}, so it has no pointwise powers. Schur products after smoothing give nothing new, because no Euler-product object has sums of zeros rho_1 + ... + rho_k as its zeros (zeta tensor zeta = zeta).

## Proposal

EFFECTIVE ARAKELOV COUNTERFEIT E AND THE CLASS-SUM CRITERION. All numbers below were computed this session.

The counterfeit: E(s) = (1/2) sum'(x^2 + 5y^2)^{-s} = zeta(s) L(s, chi_-20) + L(s, chi_-4) L(s, chi_5), the principal ideal class of Q(sqrt-5). It has:
- coefficients r(n) >= 0;
- a pole at s = 1;
- the same functional equation as zeta_K (Gamma_C, conductor 20, root number +1);
- a theta/Poisson (single-class Arakelov Riemann-Roch) proof of that functional equation;
- log-derivative weights c_E(n) >= 0 for all n < 36 (the first negative is c_E(36) = -7.17).
It has no Euler product (c_E(6) = 3.58).

Results:
- First off-line zero at rho = 0.9329697 + 15.6682495 i. There are 13 off-line pairs below height 100. D's first off-line zero is at height 85.7.
- The full-window Weil form of E becomes indefinite at x ~ 20 (lambda_min(19) = +0.0024, lambda_min(20) = -0.00004). The project's D threshold is ~31. zeta_K stays positive throughout.
- Certificate at x = 28 with 9 Dirichlet-cosine modes: Q_E(v) = -0.165 ||v||^2 and Q_zetaK(v) = +4.96 ||v||^2. The zero side agrees (E: -0.45073 vs arithmetic side -0.45071). The off-line quadruple contributes -1.825.
- Every weight c_E(n), n < 28, is >= 0. So E's "Lefschetz numbers" are effective on the whole window where its form is negative.
- Height-local bands of 2-3 modes fail below x = 36, the same pattern as Crux3 found for D.

P1 (Lean, same shape as Crux3). Three theorems:
- epstein_window_negative: under the hypothesis hw (aE(n) log n = sum_{d|n} w(d) aE(n/d) for n <= 27), (weilFormGammaC 20 w (autocorr f_v)).re <= -(1/10) ||f_v||^2.
- zetaK_window_pos: WeilFormZK(autocorr f_v) >= 4 ||f_v||^2.
- cE_nonneg: c_E(n) >= 0 for n < 36.
This reuses Crux3_BandDH: D's Gamma_R(s+1) arch, with the conductor changed to 20.
Falsifiable predictions: the Arb value of Q_E/||v||^2 lies in [-0.17, -0.16], and no 2-3-mode band works below x = 36.

P2 (structural). Any positivity mechanism whose inputs are only the functional equation, growth, a pole, a_n >= 0, one-class Riemann-Roch/theta, or nonnegative window weights is refuted by E at x ~ 20. A valid Hodge index must be sensitive to the class group / Hecke structure, i.e. it must distinguish zeta_K from E_Q1. This gives a one-minute test for any future F_1 proposal. One more consequence: every current project window theorem (x <= e) also holds for E.

## Davenport-Heilbronn control

The positive half of the proposal (zeta_K >= 0) uses the von Mangoldt weights Lambda(n)(1 + chi_-20(n)). These are supported on prime powers and come from the Euler product (A6).

D fails this (already known from Crux3). D has no Euler product, no pole, signed coefficients a_n, and signed weights (c_D(4) = -1.44 and c_D(6) = 1.94 at a composite).

E is a strictly stronger control than D. It keeps every non-Euler-product feature (effectivity a_n >= 0, the pole, the identical functional equation, Riemann-Roch/theta, c_E(n) >= 0 on the window), and it still fails at x ~ 20. So the proposal isolates A6 (summing over the class group / multiplicativity) as the only separating input among the properties listed.

I say so explicitly: the project's current window results (KWin at x = 2, KWin2 at x = e^0.8, L = 1/2 at x = e) are all satisfied by E as well, since lambda_min(E) > 0 for x <= 19. So they are E-blind as well as D-blind. The same holds for Connes-Consani Riemann-Roch taken alone and for zeta-regularized genus invariants.

## Numerics (untrusted)

Scripts are in /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/frob/geometry/. All runs were single-process mpmath at 20 digits, and all have finished (none left running).

- Zeros (ep_zerolist.py; output zeros_E.txt, zeros_ZK.txt):
  - E has 105 zeros up to T = 100, 26 of them off the line: 0.93297+15.66825i, 0.93767+29.98340i, 0.69693+36.37406i, 0.82319+44.00011i, 0.63491+46.75841i, 0.59744+52.74327i, and more.
  - The off-line count matches the deficit against theta/pi + 1.
  - zeta_K has 103 zeros up to T = 100, none off the line.
- Explicit formula checked against the zero side (ep_validate.py): with a smooth test at x = 11.0 and x = 24.5, the arithmetic side equals the zero side to 10 digits for both functions (for example E: 1.4566380476 on both sides).
- Matrix model (the Crux3 FWindow closed forms, reused unmodified with two Gamma_R families) against quadrature (ep_crosscheck.py): agreement to 12 digits.
- Full-window lambda_min (ep_weil.py, ep_thresh*.py):
  - E: +0.0024 at x = 19, -0.00004 at x = 20, -0.035 at x = 24, -0.20 at x = 28, -0.44 at x = 32. The values are converged in the number of modes.
  - zeta_K: always positive (for example +1e-5 at x = 32).
- Certificate (ep_cert.py, ep_zside.py): x = 28, 9 cosine modes, v = (-0.344, -0.022, -0.386, 0.245, -0.312, 0.128, -0.383, 1, -0.223).
  - E: Q = -0.45071 (arithmetic side) vs -0.45073 (zero side).
  - zeta_K: Q = +13.539 on both sides.
  - Normalized: -0.165 and +4.96.
- Band search (ep_band.py): no band of 2 or 3 modes is negative for E at any x < 36; the best one still gives E >= +0.12.
- Weights: c_E(n) >= 0 for all n < 36. The negative values are at n = 36, 54, 84, 126, ...

## Honest odds

Below 1% that the F_1/absolute-geometry angle reaches RH in any foreseeable horizon.
- No programme constructs a surface (A1) that also has a Hodge index (A4).
- The strongest local tool (the FF curve plus analytic stacks) has genus 0 and works one prime at a time.
- None of the 2024-26 Scholze or GSWZ papers I checked claims anything about RH.
- The positivity Connes-Consani obtain is Yoshida's prime-free window.

What the angle can realistically deliver:
(1) A cheaper and stronger standard counterfeit E: its off-line zero is at height 15.7, and its Weil form fails at x ~ 20. The zeros, weights and a validated model are ready to use.
(2) Kernel certificates P1, feasible with the existing Crux3 infrastructure.
(3) The class-sum criterion P2, which retires "effectivity" and "Riemann-Roch" as candidate sources of positivity.
(4) A correct attribution: KWin is Yoshida's 1992 theorem, now formalized.

## Key citations

- Connes-Consani, Weil positivity and Trace formula, the archimedean place, arXiv:2006.13771 (24 Jun 2020), PDF checked; attributes the positivity for support in (1/2,2) to H. Yoshida, On Hermitian forms attached to zeta functions, Adv. Stud. Pure Math. 21 (1992)
- Connes-Consani, Riemann-Roch for Spec Z-bar, arXiv:2205.01391 (May 2022, v2 Mar 2023), abstract checked
- Garoufalidis-Scholze-Wheeler-Zagier, The Habiro ring of a number field, arXiv:2412.04241 (5 Dec 2024), abstract checked: no RH/zeta/F_1 claim
- Fargues-Scholze, Geometrization of the local Langlands correspondence, arXiv:2102.13459; Scholze arXiv:2501.07944 (2025); Anschutz-Bosco-Le Bras-Rodriguez Camargo-Scholze arXiv:2510.15196 (2025); Scholze arXiv:2605.03655 and Clausen-Scholze arXiv:2605.11731 (2026) (listing checked)
- Scholze, Canonical q-deformations in arithmetic geometry, arXiv:1606.01796
- Borger, Lambda-rings and the field with one element, arXiv:0906.3146 (from memory)
- Fargues-Fontaine, Courbes et fibres vectoriels en theorie de Hodge p-adique, Asterisque 406 (2018) (from memory)
- Connes, Trace formula in noncommutative geometry and the zeros of the Riemann zeta function, Selecta Math. 5 (1999); Connes, An essay on the Riemann Hypothesis, arXiv:1509.05576 (from memory)
- Connes-Consani, The arithmetic site, C.R. 2014; Geometry of the arithmetic site, Adv. Math. 2016 (from memory)
- Faltings, Calculus on arithmetic surfaces, Ann. Math. 119 (1984); Hriljac, Amer. J. Math. 107 (1985); Yuan-Zhang arXiv:1304.3538; Gross-Zagier, Invent. Math. 84 (1986) (from memory)
- Weil 1948 (Courbes algebriques), Weil 1952 (formules explicites), Grothendieck 1958 (Hodge index), Deligne Weil I Publ. IHES 43 (1974), Deninger ICM 1998 (from memory)
- Davenport-Heilbronn 1936 (off-line zeros of Epstein zeta, class number > 1) (from memory)
- Project: arda-crux3/telperion/docs/Crux3_BAND_CERTIFICATE_2026-09-24.md and research/Crux3_band_certificate/ (FWindow model reused unmodified)
