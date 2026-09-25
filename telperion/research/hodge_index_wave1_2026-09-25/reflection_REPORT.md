# Hodge index for Spec Z, wave 1: angle `reflection`

conjecture1_proved = False. Mechanism alive: False. Survived adversarial review: False.

# Physics positivity for the Weil form (reflection angle)

conjecture1_proved = False. Nothing here proves, reduces or narrows RH.

## 0. Summary

I read Osterwalder-Schrader, Bost-Connes/KMS, Lee-Yang and Newman as three precise mechanisms and tested each against the counterfeits E and D.

1. **M1: the Weil form is a ferromagnet.** The windowed Weil form minus its pole terms is exactly a Beurling-Deny (Markov) Dirichlet form plus a constant. This holds whenever c(n) >= 0 on the window, and "c(n) >= 0" is what the Euler product gives. Consequences:
   - Perron-Frobenius: the ground state is a positive function.
   - The even pole term is a positive rank-one term on that "magnetization" mode.
   - Weil positivity becomes: index 1, plus one Schur scalar (the Hodge-index shape, i.e. the project's Lemma H).
   - **The sign-of-coupling input is refuted as the separating mechanism.** E is fully ferromagnetic on every window x < 36 (first negative c_E(n) is at n = 36), yet it goes Weil-negative at x ~ 19.82. D is antiferromagnetic from n = 3, yet it stays positive to about 31.
2. **M2: Lee-Yang in the Bohr fugacities z_p = p^{-s}.** Euler products are "stable" (zero-free on the polydisc). E and D are sums of two stable functions and have zeros up to sigma*_E ~ 1.134 and sigma*_D ~ 1.120. This is classical (Davenport-Heilbronn / Bohr) and only valid for sigma > 1. The product diverges at exactly the Bost-Connes beta = 1 transition.
3. **M3: Bost-Connes / primon gas.** zeta_K is a free boson gas (tensor product over primes, infinitely divisible). E is the same gas projected onto the class-group-neutral sector (a Z/2 gauge projection): E = Tr(P_0 e^{-sH}). D is not a positive system at all. Again, this is sigma > 1 information only.
4. **New empirical discriminator (T3).** For zeta_K, the lowest eigenvector of the full even-sector Weil form is a positive function at every window tested, x = 8 to 45 (and zeta at x = 2 to 4). For E it changes sign at every window, x = 8 to 22, including where E is still positive. E fails off the positive cone: at x = 20.5 and 22 its copositive minimum is still about +0.18 while the full minimum is negative.

## 1. Mechanism M1: the Beurling-Deny decomposition

**Setup.** Take L in the class used by bcore:
- gamma families b in {1/2, 3/2};
- coefficients c(n) of -L'/L;
- f real and supported in I = [-a, a], with x = e^{2a};
- the form Q(f) = W(f * f~) = Pole + Arch - Comb.

**The archimedean term is a Levy exponent.** Write
  Re psi(b/2 + ir/2) = psi(b/2) + integral_0^inf (1 - cos(ru)) nu_b(u) du,  with  nu_b(u) = 2e^{-bu}/(1 - e^{-2u}) >= 0.
So the archimedean spectral multiplier is a constant plus a Levy-Khintchine exponent.

**Identity.** For f supported in I:
  Q(f) = Pole(f) + (1/2) integral integral |f(v) - f(v-u)|^2 nu_inf(u) du dv + sum_{n<x} (c(n)/sqrt n) integral |f(v) - f(v - log n)|^2 dv + K_x ||f||^2,
where K_x = C_arch - 2 sum_{n<x} c(n)/sqrt n is a constant.

**Lemma.** If c(n) >= 0 for all n < x, then Q0 = Q - Pole satisfies Q0(|f|) <= Q0(f). Consequences:
- Q0's ground state psi0 is positive (Perron-Frobenius / Beurling-Deny).
- In the even sector, Pole = 2(integral of f cosh(u/2))^2, a positive rank-one term that is largest exactly on positive f.
- In the odd sector, Pole is a negative rank-one term.

So Q is PSD in the even sector iff
- ind(Q0_even) = 1, and
- 2 w^T Q0^{-1} w <= -1, where w is the cosh(u/2) functional (the Castelnuovo / Lemma H shape).

In the odd sector, Q is PSD iff Q0_odd dominates the negative rank-one pole term.

**Physics reading.** Q is a Gaussian ferromagnet:
- couplings Lambda(n)/sqrt n at lag log n, in a box of length log x;
- the pole acts as a mass term on the magnetization mode only;
- RH says the ferromagnet is stable in every box;
- zeta's near-null saturation (lambda_min ~ 1e-38 at x = 20) means the ferromagnet sits at criticality.

**Euler product.** It enters only through c(n) >= 0, which is nonlinear (a log-derivative). This is the sole place it enters.

**Counterfeit test (T1, coeffs.py).**
- c_E(n) >= 0 for n < 36. The first negatives are c_E(36) = -7.167, c_E(54) = -7.978, c_E(84) = -17.72.
- So on every window x < 36, E satisfies the full hypothesis of the Lemma, yet it is Weil-negative from x ~ 19.82.
- D: c_D(3) = -0.312 and c_D(4) = -1.442 (kappa = 0.28408), yet D is positive to about 31.
- **Verdict: ferromagnetism is neither sufficient nor necessary. M1 is a correct reduction but not a source of positivity.**

**Index test (T2).** Least eigenvalues of Q0:

| Function | x | Sector | Q0 eigenvalues | Full-form result |
|---|---|---|---|---|
| E | 22 | even | (-6.72, +0.517, +0.801) | lambda_min = -5.4e-4 (Schur scalar fails; index still 1) |
| E | 24 | even | (-7.18, -0.059, ...) | index 2 |
| E | 28 | odd | Q0 least = -0.175 | fails |
| zeta_K | 28 | even | (-7.92, +0.700, ...) | positive |
| zeta_K | 45 | even | (-9.70, +0.00195, ...) | positive |
| zeta_K | 45 | odd | least = 0.083 | positive |

So the index condition is also counterfeit-blind at E's horizon. For zeta_K the index slack itself saturates, which is the same near-null problem in different clothes.

## 2. New observation T3: the minimizer's sign pattern

The table gives the sign pattern of the even-sector minimizer of the full form. The column "edge min/max" is min(f)/max(f) of the minimizer on the window, a measure of how close it is to changing sign.

| Function | x | lambda_min | Sign changes | Edge min/max |
|---|---|---|---|---|
| zeta | 2 | 1.33e-3 | 0 | 0.039 |
| zeta | 3 | 5.8e-8 | 0 | 5e-4 |
| zeta | 4 | 9e-13 | 0 | 2.5e-6 |
| zeta_K | 8 | 0.661 | 0 | 0.49 |
| zeta_K | 16 | 0.0339 | 0 | 0.24 |
| zeta_K | 20 | 4.6e-3 | 0 | 0.12 |
| zeta_K | 24 | 6.8e-4 | 0 | 0.055 |
| zeta_K | 28 | 6.4e-5 | 0 | 0.020 |
| zeta_K | 32 | 7.7e-6 | 0 | 0.0076 |
| zeta_K | 36 | 8.8e-7 | 0 | 0.0026 |
| zeta_K | 40 | 1.6e-7 | 0 | 0.0011 |
| zeta_K | 45 | 4.2e-8 | 0 | 0.0004 |
| E | 8 | 0.888 | 2 | - |
| E | 16 | 0.046 | 2 | - |
| E | 19 | 2.3e-3 | 2 | - |
| E | 20.5 | -4.2e-4 | 2 | - |
| E | 22 | -5.4e-4 | 4 | - |
| E | 24 | -0.065 | 12 | - |

Robustness: the pattern is unchanged at N = 24/40/56 for E at 8, 16, 22 and zeta_K at 16, 28, 40.

Copositive minimum (24 symmetrized Gaussian bumps, about 7% projection error):
- E: +0.19 at x = 20.5, +0.18 at x = 22, +0.11 at x = 24, -0.08 at x = 28.
- zeta_K: about equal to the full minimum.

**Reading.**
- For the Euler-product function, the weakest direction is the Perron-Frobenius magnetization mode, held exactly critical by the pole.
- For the gauge-projected counterfeit, the weakest direction is a sign-changing "primitive" mode, and E fails there first.

**Conjecture PF-H.** For an L-function with an Euler product and c >= 0, the even-sector Weil minimizer is a positive function for every x.
- If true, it reduces W(x) to: copositivity plus a single Schur scalar on the PF mode.
- Copositivity is itself counterfeit-blind up to about 25 for E, so the Euler product would still have to enter quantitatively.
- This is an observation with no proof. Its float64 reach for zeta is x <= 4.

## 3. Mechanism M2: Lee-Yang in the Bohr variables (bohr.py)

**Setup for E.** Write E = (zeta_K + L_psi)/2, where psi is the class-group character. Then:
- R = L_psi / zeta_K = product over non-principal p of ((1 - z_p)/(1 + z_p))^{m_p};
- m_2 = 1, and m_p = 2 for p = 3, 7 mod 20;
- for sigma > 1, E = 0 iff R = -1.

**Setup for D.** D = 0 iff the product over p = 2, 3 mod 5 of (1 - i z_p)/(1 + i z_p) equals e^{i(pi - 2 arctan kappa)}.

**Computing sigma\*.** Each factor has maximal argument 2 arctan r at |z| = r, attained with modulus 1. So sigma* solves
  sum_p m_p * 2 arctan(p^{-sigma}) = target angle.

**Results.**
- sigma*_E ~ 1.134 (primes < 1e7 plus a tail; 1.128 without the tail).
- sigma*_D ~ 1.120 (1.112 without the tail).
- zeta_K: the Bohr lift is a product, so it is zero-free on the whole open polydisc.

**Limits.**
- This is the classical Davenport-Heilbronn mechanism.
- It holds only where the product converges (l^1 of fugacities, sigma > 1).
- At sigma <= 1 the product diverges. This is the Bost-Connes beta = 1 phase transition, where KMS uniqueness holds and says nothing about zeros.
- It predicts nothing about x_E or x_D.

## 4. Mechanism M3: Bost-Connes, primon gas, Newman

- zeta_K = Tr over the Fock space of a free boson per prime ideal. The energy law at sigma > 1 is infinitely divisible, with Levy measure c(n) n^{-sigma}/log n >= 0.
- E = Tr(P_0 e^{-sH}) with P_0 = (1 + U_psi)/2 (Gauss-law projection). Its Levy measure is signed (n = 36), so it is not infinitely divisible.
- D has negative weights, so it is not a trace of anything positive.
- **Correction to the brief:** E does have a quantum-statistical system (the class-neutral sector of the Ha-Paugam K-system). What it lacks is the tensor-product-over-primes structure.
- Newman: RH <=> the Polya measure is in the Lee-Yang class. That class is closed under products and ferromagnetic coupling, but the Euler factors are zero-free in t with poles on Im t = -1/2. The known physical representations (theta, Biane-Pitman-Yor) are additive/Poisson, i.e. linear, so they are DH-blind.
- Osterwalder-Schrader reflection positivity (Hankel / complete monotonicity) and Weil's condition (Toeplitz / Bochner on an interval) are different positivities. Rewriting W as reflection positivity is a relabeling that adds no input.

## 5. Literature

Unverified: web-search budget exhausted, fetches failed.
- Lee-Yang 1952; Newman 1974 (CPAM), 1976 (PAMS 61), 1991 (Constr. Approx. 7, GHS and RH); Rodgers-Tao 2020.
- Bost-Connes 1995; Julia 1990; Spector 1990.
- Knauf 1993 and 1998 (CMP 196: number-theoretical spin chain and the Riemann zeros); Contucci-Knauf 1997; Kleban-Ozluk 1999.
- Davenport-Heilbronn 1936.
- Gonek 2012; Gonek-Montgomery 2013.
- Lin-Hu 2001; Nakamura 2015.
- Yoshida 1992; Bombieri 2000; Connes-Consani 2020; Lagarias 2005.

Probably new but unconfirmed: the Beurling-Deny / Markov reading of the full windowed Weil form, the ferromagnetic-E refutation, and the T3 discriminator.

## 6. Odds and deliverables

**RH via this angle:** < 0.3%. **alive: false** for physics positivity as a proof source.

**Deliverables short of RH:**
- (a) A Lean-able Markov/Perron-Frobenius lemma for the windowed Weil form.
- (b) A certified statement: E is ferromagnetic yet Weil-negative on (19.82, 36). This kills every sign-of-coupling / GKS / Lee-Yang-type argument.
- (c) Arb certification and scaling of T3 (zeta_K to x ~ 100, zeta at small x) as a structural fingerprint of Euler products. About 40% that it persists.

**Next step:** certify T3 at x = 22 (E sign-changing vs zeta_K positive) in high precision, and test whether the zeta_K minimizer's edge decay (min/max roughly halving per unit of log x) persists or develops a node.

Scripts are in /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hodge/reflection/ (coeffs.py, win.py, pf2.py, bohr.py; logs win.log, pf2.log). No processes were left running.

## Adversarial verdict

```json
{
 "angle": "reflection (physics positivity: Osterwalder-Schrader, Bost-Connes/KMS, Lee-Yang, Newman), adversarial skeptic review",
 "survives": false,
 "fatal_flaws": [
  "M1 (Beurling-Deny / ferromagnetic decomposition) is a correct identity, but it is elementary: it comes from integral |f(v)-f(v-y)|^2 dv = 2||f||^2 - 2g(y) plus the standard Levy-Khintchine form of Re digamma. As a positivity source it is refuted by E: I independently confirmed c_E(n) >= 0 for all n < 36 (first negative is c_E(36) = -7.167), yet E is Weil-negative from x ~ 19.82. D is the opposite case: it has negative couplings from n = 3 and is still positive to about 31. Ferromagnetism is neither sufficient nor necessary.",
  "The index-1 + Schur reduction is only the project's own Lemma H restated. It is counterfeit-blind: E still has index 1 at x = 22, where it already fails through the Schur scalar alone.",
  "M2 (Lee-Yang in the Bohr fugacities) and M3 (Bost-Connes / primon gas / infinite divisibility) are classical Davenport-Heilbronn / Bohr facts that hold only for sigma > 1. They stop at the beta = 1 transition and say nothing about W(x) or where it fails.",
  "The new conjecture T3 / PF-H is REFUTED by a genuine Euler product. The Dedekind zeta of Q(sqrt -163) has a pole, an Euler product and c(n) >= 0, but its even-sector minimizer has 2 sign changes at x = 8, 16, 22, 45 and 80. This is robust at N = 32/48 and in both Neumann and Dirichlet bases, with lambda_min between 3.7 and 0.61, all positive as GRH predicts. Positivity of the minimizer tracks how strong the small-prime couplings are (split primes / conductor). It is not a fingerprint of the Euler product.",
  "Newman / Osterwalder-Schrader relabelings add no input. The proposer concedes this, and I agree."
 ],
 "linearity_or_classP_violation": "M1 enters nonlinearly only through the sign of c(n) (a log-derivative), but the sign alone does not separate: E passes the sign condition on every window x < 36 and still fails at 19.82, so it goes through verbatim for E. M2 and M3 are nonlinear but live only at sigma > 1. On the critical-strip question they are silent, which in effect makes them fooled. T3 does not break linearity or class P as the proposer hoped. It separates zeta_K(-20) from E, but it also puts zeta_{Q(sqrt -163)} (Euler product) on E's side. So the quantity it measures is coupling strength, which is multiplicativity-blind.",
 "counterfeit_check": "E: reproduced with my own driver (t3ctl.py, which uses bcore read-only). lambda_min = +4.6e-2 at x = 16. It is -4.4e-5 (N = 32) / -1.3e-4 (N = 48) at x = 20 and -5.4e-4 at x = 22. So the failure lies between 16 and 20, consistent with x_E ~ 19.82; I did not re-certify the threshold itself. The minimizer has 2 sign changes at x = 16 and 20 and 4 at x = 22, as claimed. zeta_K(-20): lambda = 3.4e-2 at x = 16 and 1.7e-3 at x = 22, with 0 sign changes (as claimed); my generic Dedekind driver with D = -20 reproduces this exactly (sanity check). D: not checked (the proposer also produced no D window numerics). None of M1, M2 or M3 predicts x_E or x_D.",
 "numerics_reproduced": "Reproduced:\n- T1: E coefficients by brute-force lattice count of x^2 + 5y^2 plus the Dirichlet-log recursion (independent of bcore). First negatives at 36, 54, 84, 126 with values -7.167, -7.978, -17.723, -38.69. This matches the proposer exactly.\n- T3 for E and zeta_K at x = 16, 20, 22: matches.\n\nNew control that refutes PF-H:\n- zeta_{Q(sqrt -163)} (Gamma_R(s)Gamma_R(s+1), conductor 163, weights Lambda(n)(1 + chi_-163(n))) has a sign-changing minimizer with 2 sign changes and min(f)/max(f) between -0.43 and -0.87. This holds at x = 8, 16, 22, 45 and 80, while lambda_min = 3.73, 3.58, 3.49, 3.20 and 0.61 (all positive).\n- zeta_{Q(sqrt -23)} has a positive minimizer at x = 8, 16 and 22.\n- Q(i) and Q(sqrt -3) are at roundoff level (lambda ~ 1e-12 to 1e-15), so they are uninformative for x >= 16 / 30.\n\nScripts: /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hodge/reflection_skeptic/{coef.py,t3ctl.py,t3a.log,t3b.log}. No processes are left running.",
 "novelty": "- The Markov / Beurling-Deny reading of the windowed Weil form is almost certainly folklore-level and follows in two lines. The Levy-Khintchine form of digamma is classical (Malmsten / Binet). I could not verify novelty: the web-search budget is exhausted (200/200) for this session too, so all of the proposer's citations remain UNVERIFIED by me.\n- M2 is Davenport-Heilbronn 1936 / Bohr, which is standard.\n- M3 is Bost-Connes / Julia / Spector, also standard.\n- The one plausibly new item, T3, is refuted as an Euler-product fingerprint by the Q(sqrt -163) control.",
 "what_is_real": "- (a) The exact decomposition Q = Pole + Levy-Dirichlet(arch) + sum_n (c(n)/sqrt n) ||f - f(. - log n)||^2 + K_x ||f||^2. Q0 is Markovian when c >= 0 on the window, so its ground state is positive (Perron-Frobenius). It is modest and could be written in Lean, but it is not a positivity source.\n- (b) A clean certifiable counterfeit statement, worth keeping as a barrier lemma: E has c_E(n) >= 0 for all n < 36 and is still Weil-negative on (19.82, 36). This kills any sign-of-coupling, GKS-type or ferromagnetic argument for W(x).\n- (c) Empirically, E's failure happens in a sign-changing (non-PF) direction, with copositive minimum around +0.18 at x = 22 per the proposer; I did not re-check that. But that direction is also the minimizer for honest Euler products with weak small-prime coupling, e.g. Q(sqrt -163), so the sign pattern is not a separator.",
 "next_step_if_survives": "The proposal does not survive. The most informative salvage is to certify barrier (b) in Arb/Lean: E is ferromagnetic on every window x < 36, yet lambda_min(E, x = 22) < 0. File it next to the linearity barrier as a \"sign barrier\": no argument that uses only c(n) >= 0 plus FE/growth can prove W(x). Drop PF-H. If anyone wants to revive T3, the refined question is whether PF-positivity of the minimizer holds eventually (for x beyond the first several split primes) for every Dedekind zeta. Q(sqrt -163) is still sign-changing at x = 80 with lambda = 0.61, so test it at x = 150 to 300 in high precision."
}
```
