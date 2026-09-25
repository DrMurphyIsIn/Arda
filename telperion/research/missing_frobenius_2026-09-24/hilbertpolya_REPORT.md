# Missing Frobenius: angle `hilbertpolya` (2026-09-24)

conjecture1_proved = False. This is a research report. It is unreviewed except for the skeptic verdict in SKEPTIC_VERDICTS.md, which supersedes it where they disagree.

## Summary

hilbertpolya. Bottom line: a Hilbert-Polya operator is Weil positivity restated, and I found no arithmetic freedom left beyond positivity. I verified that local GUE statistics do not tell D apart from zeta, but the Weyl-anchored count does. conjecture1_proved = False. Nothing here proves, reduces or narrows RH.

## Axioms

Notation: rho = 1/2 + i*gamma runs over the zeros, theta(t) = arg Gamma(1/4+it/2) - (t/2) log pi, and N(T) = theta(T)/pi + 1 + S(T).

HP1 (spectral realization). There is a self-adjoint operator H with discrete spectrum equal to the zero ordinates {gamma}, with multiplicity. Without "self-adjoint" this has no content: Meyer (Duke 2005) and Connes (Selecta 1999) already realize all zeros, off-line ones included, as the spectrum of a non-self-adjoint operator. A diagonal real matrix realizes any real sequence, so the whole content of HP1 is a structural proof of self-adjointness.

HP2 (Weyl law with the 7/8 term). N_H(T) = (T/2pi) log(T/2pi e) + 7/8 + S(T) + O(1/T).
- The 7/8 is 1 - 1/8: the 1 comes from the pole at s = 1 and the -1/8 from the Stirling phase. A Maslov index gives only quarter-integers, so -1/8 is half a Maslov unit, and the +1 has no phase-space origin. Both are known embarrassments for xp semiclassics.
- S(T) = O(log T), with Trudgian's 2014 bound |S| <= 0.112 log T + 0.278 log log T + 2.51.
- The integral of S from 0 to T is O(log T) (Littlewood).
- Selberg: S(T) is Gaussian with variance (1/2pi^2) log log T.
- Consequence: on every window, the eigenvalue count must equal the Weyl increment plus O(log T).

HP3 (trace formula = Weil explicit formula). sum_gamma h(gamma) = h(i/2) + h(-i/2) - g(0) log pi + (1/2pi) ∫ h(r) Re psi(1/4 + ir/2) dr - 2 sum_n Lambda(n) n^{-1/2} g(log n).
- Read as a Gutzwiller/Selberg formula: primitive orbit lengths are log p, and the k-th repetition has amplitude log p * p^{-k/2}. That is a uniformly hyperbolic flow with Lyapunov exponent 1, carrying the opposite sign to Gutzwiller (Connes' "absorption spectrum").
- For self-adjoint H, W(g * g~) = sum |g^(gamma)|^2 >= 0 follows immediately. So HP1 + HP3 is equivalent to RH by Weil's criterion.

HP4 (symmetry class: chiral, not time-reversal). The coefficients are real and xi is real on the line, so there is an antiunitary C with C H C^-1 = -H.
- Montgomery 1973 and Rudnick-Sarnak 1996 give GUE statistics, so H must not have a time-reversal T with T^2 = 1 (that would give GOE).
- Consistency check: time reversal sends xp to -xp, so Berry-Keating's xp is chiral in exactly the right way.
- Honesty flag: this is a random-matrix heuristic, not a theorem.

HP5 (positivity = Hodge index). Over function fields, Weil used Hodge index and Deligne used weights plus the tensor-power trick; unitarity came from a compact monodromy group (Katz-Sarnak). In the Hilbert-Polya setting, positivity is self-adjointness itself, and nothing supplies it.

HP6 (Euler-product encoding: the orbit axioms). The orbit side has lengths {log p^k}, amplitudes 0 <= c(n) <= log n, and the repetition law c(p^k) = log p.

LEMMA O. Assume a(1) = 1 and write -F'/F = sum c(n) n^{-s}. Then c is supported on prime powers if and only if a is multiplicative. Proof: log F = sum (c(n)/log n) n^{-s}.

Combined with the project's classP_eq_zeta, HP3 + HP6 with zeta's archimedean side force F = zeta. So the missing Frobenius is exactly the missing positivity, with no arithmetic freedom left.

## Best existing realization and its failure point

DH-safe realizations (the Euler product is built into the space). All of them stall at positivity.
- Connes 1999 (Selecta Math 5), the adelic cutoff: the zeros appear as an absorption spectrum, and RH is reduced to an unproved positivity of the global trace formula.
- Connes-Consani-Moscovici, "Zeta zeros and prolate wave operators", arXiv:2310.18423 (Oct 2023, revised May 2024; post-2023; verified): a semilocal prolate operator whose positive spectrum tracks the low-lying zeros. It covers finite S only, has no positivity proof, and falls under the project's semilocal barrier W_{p,c} and fooling identity.
- de Branges spaces: RH is equivalent to a Hermite-Biehler condition on E(z) built from xi and xi' (Lagarias 2005-06; from memory). De Branges' extra positivity condition, meant to prove it from the Euler product, is FALSE for zeta: Conrey-Li, arXiv:math/9812166, verified; IMRN 2000.

DH-trapped realizations: all of the following also produce D.
- Berry-Keating xp (SIAM Review 1999): smooth Weyl term only, no S(T), no orbits.
- Sierra 2007 (Nucl. Phys. B 776), Sierra-Townsend 2008 (PRL 101:110201), Sierra 2019 (Symmetry 11:494): the fluctuating part is imported from zeta through boundary data or a potential, and self-adjointness is proved only for the smooth model.
- Bender-Brody-Muller 2017 (PRL 118:130201, arXiv:1608.03679, verified): H = Delta^-1 (xp+px) Delta with Delta = 1 - e^{-ip}, eigenfunctions -zeta(z, x+1), and boundary condition psi(0) = 0. H is not self-adjoint and the PT argument is heuristic. Bellissard's comment (arXiv:1704.02644, verified, Apr 2017) says the approach "does not actually work".
- Franca-LeClair and LeClair-Mussardo (JHEP 2024, from memory): the quantization theta + arg zeta = pi(n - 3/2) sees only on-line zeros, so completeness is equivalent to RH. For D it silently drops each off-line pair, which is exactly the -2 steps measured in the numerics.

PROPOSITION T (the trap). Suppose a self-adjointness proof uses only the coefficients linearly (Hurwitz or Dirichlet-series eigenfunctions), the functional equation with Lambda real on the line, growth, and real coefficients. Then the same proof works for D, whose spectrum contains i(2z0 - 1) with z0 = 0.80851718 + 85.69934849i. That is a contradiction, so every valid proof must use multiplicativity (HP6).

Explicit BBM instance (checked numerically in bbm_trap.py):
- For a periodic mod 5, set A(w) = (sum_j a_j w^j)/(1 - w^5), phi_z(u) = -sum a(m)(u+m)^{-z} = -A(e^{ip}) u^{-z}, and H_a = A (xp+px) A^-1.
- Then H_a phi_z = i(2z-1) phi_z and phi_z(0) = -F_a(z).
- zeta corresponds to a = (1,1,1,1,1), which is BBM itself (residual 3e-26 at the first zero). D corresponds to a = (1, kappa, -kappa, -1, 0).
- At D's off-line zero, phi_z(0) = 5e-26 and E = -171.3987 + 0.6170i, which is not real.
- D has real coefficients, so the PT heuristic transfers to D verbatim.
- Locality does not help either: A^-1 is non-local for both L(s,(./5)) and D. The distinction must be arithmetic.

## Proposal

THE ORBIT-HOLE TEST (OHT). It has two parts.

OHT-1 (kernel-checkable and small).
(a) Prove Lemma O in Mathlib ArithmeticFunction form: if a 1 = 1 and a·log = c * a, then (for all n, c n ≠ 0 → IsPrimePow n) ↔ a.IsMultiplicative. The proof is induction on the recursion a(n) log n = sum_{d|n} c(d) a(n/d) over coprime splits. Estimated 200-500 lines.
(b) Prove the instance c_D(6) = (1 + kappa^2) log 6 ≈ 1.9364. This is nonzero and larger than log 6.
- Derivation: c(6) = a(6) log 6 - c(2) a(3) - c(3) a(2), with a(6) = 1, c(2) = kappa log 2 and c(3) = -kappa log 3.
- It follows in a few lines from the hw identity already in Crux3.dh_band_negative, or from the cD closed form.
(c) Combine with classP_eq_zeta into one kernel statement: the Hilbert-Polya orbit axioms plus zeta's archimedean side single out zeta, and D violates them at n = 6. The residual obligation is then exactly Weil positivity for all L, i.e. the KWin family.

OHT-2 (finite certificate of the first D "hole").
(a) Arb: Z_D(t) ≠ 0 on [83.2, 87.6]. The neighbouring line zeros are at 83.11 and 87.65.
(b) Arb argument-principle count: D has exactly 2 zeros in the box [-1, 2] x [83.2, 87.6].
Consequence: no self-adjoint operator obeying the Weyl identity HP2 realizes D's line spectrum. This is a zero-side certificate of the same off-line quadruple that Crux3 detects prime-side, at the same height 85.7.

Falsifiable predictions beyond T = 1200:
1. Every hole larger than 2.2 unfolded spacings in D's line spectrum contains an off-line pair, and every off-line pair makes a hole of at least 2.
2. The fraction of D's zeros off the line falls slowly, as Bombieri-Hejhal predict.
3. With the holes removed, D's spacing law matches L5's. A significant difference (KS p < 1e-3 on 10^4 spacings) would REFUTE the DH-blindness of local statistics, which would be a positive surprise for the Hilbert-Polya program.

What OHT does NOT do: it does not narrow the positivity gap and does not advance RH.

## Davenport-Heilbronn control

OHT-1: D fails for a genuinely arithmetic reason. Its coefficients mod 5 are (1, kappa, -kappa, -1, 0), with kappa = (sqrt(10 - 2 sqrt 5) - 2)/(sqrt 5 - 1) ≈ 0.28408, and they are not multiplicative: a(2) a(3) = -kappa^2, but a(6) = 1. By Lemma O the orbit side then contains the composite length log 6, with amplitude (1 + kappa^2) log 6 > log 6. That breaks both the prime-power support and the Ramanujan-type bound.
- Measured: max |c_D(n)|/log n over dyadic blocks up to n = 400 grows 1.08 -> 1.34 -> 1.38, while for L5, c vanishes off prime powers to 2e-15.
- Asymptotically |c_D(n)| is at least n^{beta* - 1 - eps} infinitely often, because D has zeros in sigma > 1.
- Saias-Weingartner (Acta Arith 2009, from memory): a periodic Dirichlet series with no zeros in sigma > 1 is L(s, chi) times a Dirichlet polynomial.

OHT-2: D fails because it really has the off-line pair at 85.699; the finite certificate uses no Euler product. The Euler product enters only in the scalable version, via Turing's bound on the integral of S. That bound needs |log zeta(sigma+it)| <= log zeta(sigma) for sigma > 1, i.e. an Euler product with no zeros in sigma > 1. For D, log D is unbounded in sigma > 1. Honestly, this part is classical: Turing 1953 in Hilbert-Polya clothing.

GUE local statistics are DH-BLIND and so worthless as an RH discriminator. D's line spectrum shows the same small-gap repulsion as L5.

## Numerics (untrusted)

Setup.
- Real Z-functions: Z_D(t) = e^{i theta_D} D(1/2+it) with theta_D = arg Gamma(3/4 + it/2) + (t/2) log(5/pi). Z_L5 is the same with Gamma(1/4 + it/2), for L(s,(./5)), which has the same conductor and an Euler product.
- Imaginary parts are at most 3.6e-18, which confirms both functions are real on the line.
- Up to T = 1200 there are 1047 line zeros for D and 1119 for L5.
- Grid step 0.07. Re-counting [300, 400] at step 0.015 gave 83 = 83, and [1100, 1150] at step 0.012 gave 52 = 52, so no close pairs were missed.

(N1) Weyl counting residual (n - 1/2) - theta/pi.
- L5 stays at 0 ± 0.02 throughout.
- D is 0 below 85, then steps by exactly -2 at 85.70, 114.16, 166.48 and 176.70, which are the known off-line zeros (confirmed 0.808517182 + 85.699348485i).
- D reaches -15.7 at 400, -40.8 at 800 and -69.8 at 1190. The slope is about 0.069 per unit height, i.e. roughly 35 off-line pairs, or 6-7% of D's zeros near T = 1000.

(N2) Holes, in unfolded spacing units.
- (83.11, 87.65) = 3.05, (112.38, 116.72) = 3.12, (164.16, 168.32) = 3.24, (174.60, 178.17) = 2.81.
- D has 36 gaps larger than 2.2; L5 has none (its maximum is 2.16).

(N3) Spacing statistics, D / L5 against GUE / GOE (Wigner surmise).
- P(s < 0.25): 0.0076 / 0.0072, against 0.016 / 0.048.
- P(s < 0.5): 0.074 / 0.072, against 0.112 / 0.178.
- P(s > 2): 0.034 / 0.006, against 0.017 / 0.043.
- var(s): 0.191 / 0.129, against 0.178 / 0.273.
- Two-sample KS, D vs L5: 0.086, p = 7e-4.
- With the holes removed: KS 0.068, p = 0.015, and variance 0.105 against 0.129. So D is marginally MORE rigid, and the local GUE-type repulsion is DH-blind.

(N4) Orbit amplitudes of -F'/F up to n = 400.
- L5 is zero off prime powers to 2e-15.
- D at non-prime-powers: c(6) = 1.936, c(14) = -2.852, c(21) = 3.290, c(26) = 3.521, c(34) = -3.811, c(39) = -3.959.
- max |c_D|/log n over dyadic blocks: 1.08 -> 1.34 -> 1.38.

(N5) BBM trap at D's off-line zero: phi_z(0) = 5e-26, and E = i(2z-1) = -171.3987 + 0.6170i. The zeta embedding via a = (1,1,1,1,1) is exact (residual 3e-26).

## Honest odds

Below 1% that the Hilbert-Polya angle reaches RH in any foreseeable horizon.
- Every DH-safe realization (adelic, semilocal prolate, de Branges) stalls exactly at positivity, and de Branges' positivity is false (Conrey-Li).
- Every realization that proves self-adjointness is DH-trapped, so none can be correct as stated.
- In 25 years (Connes 1999 to Connes-Consani-Moscovici 2024), nothing has supplied an intersection-pairing source of unitarity over Q.

What the angle can realistically deliver:
1. A kernel-checked statement (OHT-1) that the Hilbert-Polya axioms amount to zeta plus Weil positivity, with no arithmetic freedom left and D's failure pinpointed at n = 6.
2. Proposition T, which turns any "Hamiltonian for the zeros" claim into a mechanical check: run it with the coefficients of D.
3. A quantified negative control: local GUE statistics are DH-blind, while the Weyl-anchored count is not (-2 steps and roughly 3-spacing holes). This argues for spending no effort on statistical signatures and keeping it on KWin toward all L.
4. A second, zero-side certificate of D's off-line quadruple at height 85.7, alongside Crux3's prime-side one.

## Key citations

- Bender, Brody, Muller, Hamiltonian for the zeros of the Riemann zeta function, PRL 118 (2017) 130201, arXiv:1608.03679 [verified]
- Bellissard, Comment on 'Hamiltonian for the Zeros of the Riemann Zeta Function', arXiv:1704.02644 (Apr 2017) [verified]
- Conrey, Li, A note on some positivity conditions related to zeta- and L-functions (de Branges positivity fails), arXiv:math/9812166; IMRN 2000 [arXiv verified]
- Connes, Consani, Moscovici, Zeta zeros and prolate wave operators, arXiv:2310.18423 (Oct 2023, rev. May 2024) [verified, post-2023]
- Connes, Trace formula in noncommutative geometry and the zeros of the Riemann zeta function, Selecta Math 5 (1999) [memory]
- Berry, Keating, The Riemann zeros and eigenvalue asymptotics, SIAM Review 41 (1999) [memory]
- Sierra, Townsend, Landau levels and Riemann zeros, PRL 101 (2008) 110201; Sierra, Nucl. Phys. B 776 (2007) [memory]
- Lagarias, Hilbert spaces of entire functions and Dirichlet L-functions (2006) / Zero spacing distributions for differenced L-functions, Acta Arith 120 (2005) [memory]
- Montgomery 1973 pair correlation; Rudnick-Sarnak, Duke 81 (1996) [memory]
- Saias, Weingartner, Zeros of Dirichlet series with periodic coefficients, Acta Arith 140 (2009) [memory]
- Davenport, Heilbronn 1936; Bombieri, Hejhal, Duke 80 (1995) on zeros of linear combinations [memory]
- Trudgian, J. Number Theory 2014 (S(T) bounds); Platt, Trudgian, Bull. LMS 2021 (RH verified to 3e12) [memory]
- LeClair, Mussardo, Riemann zeros as quantized energies of scattering with impurities, JHEP 2024 [memory, not verified]
- Project: Crux3_BAND_CERTIFICATE_2026-09-24.md (arda-crux3), RH_CRUX_ROUND2_2026-09-23.md (arda-crux2): classP_eq_zeta, fooling identity, semilocal barrier
