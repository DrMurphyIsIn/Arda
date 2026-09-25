# Hodge index WAVE2: angle `jensen`

conjecture1_proved = False. Mechanism alive: False. Survived adversarial review: False.

# ANGLE jensen: are Jensen polynomials and the Laguerre-Polya class counterfeit-blind?

**Verdict: DEAD as a route to RH. Useful as a calibration theorem.** conjecture1_proved = False.

## 1. Setup (precise)

For a completed function xi_F with xi_F(s) = xi_F(1-s), real on the critical line:

- Xi_F(t) = xi_F(1/2+it) = 2 ∫_0^∞ Phi_F(u) cos(tu) du, with Phi_F(u) = e^{u/2} g_F(e^u).
- g_F is the inverse Mellin transform of xi_F. For a pole case, g = (yD)(yD+1) f, where f(y) = sum a_n k(n y / Q). Kernels:
  - zeta: k = 2e^{-pi y^2}.
  - E and zeta_K: k = e^{-w}, with w = pi n y / sqrt 5.
  - D: f = sum a_n n y e^{-pi n^2 y^2/5}, no pole.
- Taylor data: b_F(m) = ∫_0^∞ u^{2m} Phi_F(u) du and gamma_F(m) = 2 m! b_F(m)/(2m)!, so that Xi_F = sum_m gamma_F(m) z^m/m! with z = -t^2.
- Jensen polynomials: J^{d,n}(X) = sum_j C(d,j) gamma(n+j) X^j. This is the degree-d Jensen polynomial of F^{(n)}(z).
- Polya: Xi_F is in the Laguerre-Polya class (RH for F) iff J^{d,n} is hyperbolic for every d and n.
- GORZ: for each fixed d, J^{d,n} is hyperbolic for n >= N(d), because the normalized J^{d,n} converges to the Hermite polynomial H_d. They also prove d <= 8 for all n.

The four functions:

| Function | Definition | Coefficients | Completion |
|---|---|---|---|
| E | (1/2) sum' (x^2+5y^2)^{-s} | a_n = r_Q(n)/2 | (sqrt5/pi)^s Gamma(s), times s(s-1) |
| zeta_K | zeta · L(chi_{-20}) | a_n = sum_{d\|n} chi_{-20}(d) | same as E |
| D | Davenport-Heilbronn | 1, kappa, -kappa, -1, 0 (mod 5) | (5/pi)^{s/2} Gamma((s+1)/2) |
| zeta | Riemann zeta | a_n = 1 | standard |

Validation:
- Every kernel is even (Phi(0.5) - Phi(-0.5) <= 1e-143).
- Integrating 2∫Phi cos(tu) reproduces xi_F(1/2+it) at t = 0, 3, 10 up to a fixed constant factor.
- Moments were computed to m = 400 at 160 digits (Gauss-Legendre on [0, 14]).

## 2. The mechanism under test, and why it cannot see the Euler product

**Tail-dominance lemma** (proof sketch):

- Assumptions: a_1 = 1, a_n = O(n^A), and a single-Gamma kernel psi(w) = P(w) e^{-c w^kappa}.
- For u >= 0, |Phi_F(u) - Phi_1(u)| <= C exp(-c 2^kappa e^{kappa u}) · poly, where Phi_1 is the n = 1 term.
- For large m, the integrand u^{2m} Phi_1(u) peaks at u_m with c kappa e^{kappa u_m} ~ 2m/u_m. Hence gamma_F(m) = gamma_1(m) (1 + O(exp(-c' m / log m))).
- This error is o(delta(n)^d) for every d. So the hypotheses of GORZ Theorem 3 (the expansion of log(gamma(n+j)/gamma(n)) in j) are the same for F as for the one-term model.
- Consequence: the Hermite limit holds and N_F(d) is finite for EVERY such F, including E, D, and any linear combination with a_1 != 0.

GORZ's proof for zeta runs through exactly this first-term asymptotic of Phi. So their theorem is counterfeit-blind by construction.

- Remaining gap: a routine check of the saddle-point hypotheses for the Gamma_C kernel (w^2 - 2w) e^{-w} and the odd Gamma_R kernel. I did not look this up in the literature.
- Empirical check of the rate: -ln(1 - gamma_E/gamma_zetaK) divided by (m / log m) is 1.9 at m = 100 and 1.86 at m = 400, as predicted.

**Euler-product usage: none.**

- gamma_F(m) is linear in (a_n). Jensen conditions are polynomial in the gamma's, so they are nonlinear in L, but multiplicativity never enters.
- Refined barrier (moment-functional barrier): "positivity of polynomials in the central Taylor moments, for n >= N(d)" is decided by a_1. Being nonlinear in L is necessary but not sufficient; the separator must use multiplicativity itself.

## 3. Numerical tests (all run)

Scripts: `/private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hodge2/jensen/`. Moments come from moments.py (pickled in gam.pkl). Supporting scripts: validate.py, jtest.py, scan1.py, sturm.py, jbox.py, jbis.py, fbox.py, hermite.py.

### 3a. Is the GORZ regime counterfeit-blind? Yes.

- **Turan (d = 2):** gamma(n+1)^2 >= gamma(n) gamma(n+2) for all n <= 397, for all four functions: zeta, zeta_K, E and D.
- **Low degree:** J^{d,n} was tested for d in {3, 4, 5, 6, 8, 10, 12, 16, 20, 24, 30} and n in {0..39} ∪ {40, 60, ..., 340} (polyroots at 160 digits). Result: ZERO failures for zeta, zeta_K, E and D. So "d <= 8 for all n" appears true for E and D as well; numerically this is shown for n <= 340, and it follows from tail dominance beyond.
- **Hermite limit:** the distance from the normalized roots of J^{d,n} to the roots of H_d shrinks at the same rate for all four functions:

| d = 6 | n = 20 | n = 100 | n = 390 |
|---|---|---|---|
| zeta | 1.24 | 0.72 | 0.40 |
| zeta_K | 1.48 | 0.78 | 0.42 |
| E | 1.48 | 0.78 | 0.42 |
| D | 1.62 | 0.82 | 0.44 |

- **The Jensen data of E and zeta_K merge:**

| m | 20 | 50 | 100 | 200 | 400 |
|---|---|---|---|---|---|
| 1 - gamma_E(m)/gamma_zetaK(m) | 3.6e-6 | 2.9e-11 | 1.5e-18 | 2.1e-31 | 2.1e-54 |

**Conclusion.** A theorem of GORZ type cannot tell zeta_K (GRH expected) from E (RH false). **The calibration theorem is worth recording.**

### 3b. Where do the counterfeits fail? Large d, low n: the zero-resolution corner.

Method: the argument principle for P_{d,n}(z) = J^{d,n}(z/d) on boxes around each known off-line zero.

- Truncating at 400 Taylor terms is safe: the tail is below 1e-130 on every box used.
- The global Sturm count is reliable only up to d ~ 250. At d = 300 it shows spurious failures even for zeta (160-digit data), so it was not used for large d.

| Function | Off-line zero (s) | z = -t^2 | First non-hyperbolic d (n = 0) |
|---|---|---|---|
| E | 0.93297 + 15.66825i | -245.3 + 13.57i | **381** (382 with box floor Im z = 0.5) |
| E | 0.93767 + 29.98340i | -898.8 + 26.25i | **1645** (1646) |
| D | 0.80852 + 85.69935i | -7344.3 + 52.88i | **~20,794** (floor Im z = 1; true onset possibly slightly lower) |
| zeta | none | same boxes | none up to d = 10^5 (E box) and 10^6 (D box) |
| zeta_K | none | E box | none up to d = 10^5 |

- Empirical horizon: d0 / (t^2 log t) = 0.565, 0.538, 0.636, so **d0 ~ 0.6 t^2 log t**.
- This is the Jensen-side counterpart of the Weil thresholds x_E ~ 19.82 and x_D ~ 31-35. Both simply encode the height of the first off-line zero. Low-n hyperbolicity up to degree d certifies RH only up to height ~ sqrt(d / log d), which is the Chasse-type zero verification.

**Derivative smoothing.** Counts of non-real zeros of F_E^{(n)} with Re z in [-2600, -100] and 0.3 < Im z < 90:

- n = 0: 5 (matches the E zero list, which validates the method).
- n = 1: 1.
- n = 2: 0.
- zeta_K and D: 0 at n = 0 on this box.

J^{d,1} of E never fails in the first two boxes (d up to 10^5), and neither does J^{d,3} or J^{d,10} in the second box. So E's failure set is concentrated at small n and large d, with n_max growing slowly with height. A heuristic prediction, not tested: off-line pairs survive about y log t / 2pi derivatives.

## 4. Counterfeit control summary

The mechanism (GORZ asymptotic hyperbolicity) **does not fail for E or D**. It is refuted as an RH mechanism. The full Jensen family does separate the functions, but only through zero location. No Euler-product input is identifiable. Nothing fails for E near x ~ 19.8 in any Jensen parameter except d0 = 381, which is a zero-height proxy.

## 5. Side observation

E's Polya kernel is negative at the origin: Phi_E(0) = -0.0750. The kernels of zeta, zeta_K and D are positive there. Positivity of the Polya kernel is a known sufficient input for some Turan-type results, but it is not an RH criterion. This is a cheap probe to log, not a lead.

## 6. Literature

- GORZ, PNAS 116 (2019), arXiv:1902.07321 (verified).
- Farmer, "Jensen polynomials and the Riemann Hypothesis", arXiv:2008.07206 (verified; argues the Hermite phenomenon is universal and not evidence for RH). Journal reference unverified.
- Unverified (search budget exhausted): Polya 1927; Csordas-Norfolk-Varga 1986 (Turan for Xi); Chasse 2013 (large-d J^{d,0} from zero verification); Ki-Kim (J. Anal. Math., ~2003; high derivatives of Xi-type transforms eventually have only real zeros); O'Sullivan; Larson-Wagner.
- I know of no prior E/D Jensen computation.

## 7. Odds and deliverables

- P(Jensen route leads to RH or to Weil at all scales) < 0.1%.
- Deliverables:
  1. Calibration theorem: the GORZ asymptotics hold for all F with a_1 = 1 and a functional equation; candidate Lean target.
  2. Moment-functional barrier, refining the linearity barrier.
  3. Horizon law d0 ~ 0.6 t^2 log t, with first failing d = 381 (E) and ~2.08e4 (D).


## Adversarial verdict

```json
{
 "angle": "jensen (skeptic): Jensen polynomials / Laguerre-Polya, GORZ asymptotic hyperbolicity. Is it counterfeit-blind?",
 "survives": false,
 "fatal_flaws": [
  "As a mechanism for Weil positivity it is dead, and the proposer says so. GORZ-type asymptotic hyperbolicity (fixed d, n >= N(d)), and Turan at d=2, hold for E and zeta_K alike. I confirmed this independently: no Turan failures for n <= 198 for E, zeta_K or zeta. E's moments merge with zeta_K's at a rate of about exp(-1.9 m/log m).",
  "No Euler-product input at any step. gamma_F(m) is linear in (a_n), and the Jensen conditions are polynomials in the gamma's. Multiplicativity never enters.",
  "The only regime that tells the functions apart is low n and large d. There, hyperbolicity of J^{d,0} is equivalent to verifying zeros up to height ~ sqrt(d/log d). That is RH-equivalent bookkeeping (circular as a proof route), not a positivity reason.",
  "Overclaim in the 'moment-functional barrier': 'decided by a_1 alone' is true only of the asymptotic statement (the Hermite limit and the finiteness of N(d)). The actual threshold N_F(d), and all finite-n Jensen data, depend on every a_n. The barrier should be stated asymptotically only.",
  "Novelty is low. The tail-dominance/universality point is essentially Farmer's thesis (arXiv:2008.07206). High-derivative real-rootedness for this kernel class is, from memory and unverified this session, a theorem of Ki-Kim (J. Anal. Math., ~2003). That would already imply hyperbolicity of J^{d,n} for all d once n is large, for E-type kernels too (it needs checking that their hypotheses allow E's sign-indefinite kernel). The E/D computation is new as a calibration, not as a mechanism."
 ],
 "linearity_or_classP_violation": "It violates the spirit of the linearity barrier and is fooled exactly as the fooling lemma predicts. The Jensen conditions are polynomial in linear functionals of (a_n), so they escape the literal linearity barrier. But the whole asymptotic argument (the tail lemma plus GORZ Theorem 3) goes through verbatim for E and D, because it uses only a_1 = 1, the gamma factor and growth. The corner that does separate the functions (n = 0, d ~ 0.6 t^2 log t) separates them only by locating zeros; it contains no Euler-product structure.",
 "counterfeit_check": "E: reproduced with independent code (my own theta/Mellin kernel and Gauss-Legendre moments at 110 digits, M = 200). Newton on the Taylor series recovers E's off-line zero at s = 0.9329697 + 15.6682495i, which independently validates the moment data. The argument-principle count of J^{d,0}(z/d) on the upper half of a box around z0 = -245.31 + 13.57i, with floor Im z = 0.5, gives 0 for d = 200, 370, 380 and 381, and 1 for d = 382 and 395. zeta_K gives 0 in the same box for every d tested. This matches the proposer's 381/382. So the first Jensen failure of E is at d ~ 382, i.e. at zero-height ~15.67, which is the same information the Weil threshold x_E ~ 19.82 carries. It is not a separate mechanism. D (onset d ~ 2.08e4) was NOT reproduced; too costly for this pass. The Hermite/Turan regime does not fail for E: no Turan failures for n <= 198.",
 "numerics_reproduced": "Scripts are in /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hodge2/jensen_skeptic/: sk.py (moments, pickled to g.pkl) and box.py (argument-principle counts).\n\nReproduced:\n- Phi_E(0) = -0.075024152. For comparison, Phi_K(0) = 0.3476 and the classical Phi_zeta(0) = 0.4467.\n- Evenness of Phi_E to 6e-92.\n- 1 - gamma_E/gamma_K = 3.599e-6, 2.929e-11, 1.549e-18, 3.711e-25, 2.088e-31 at m = 20, 50, 100, 150, 200. These agree digit for digit with the proposer's values.\n- Turan holds for n <= 198 for E, zeta_K and zeta.\n- The E off-line zero is recovered from the moments.\n- Jensen onset for E at d = 382 (floor 0.5).\n\nTruncation check: the tail term at j = 200 is below 2e-155 at |z| ~ 1.3|z0|.\n\nNot reproduced: D's onset at ~2.08e4, the second E zero's onset at 1645, the Hermite-distance table, and the large-n (n > 200) claims.",
 "novelty": "Low as mathematics, modest as calibration.\n- The GORZ universality / counterfeit-blindness is Farmer's argument (arXiv:2008.07206, verified by the proposer; I could not re-verify it, as the search budget is exhausted).\n- High-derivative real-rootedness is likely Ki-Kim (unverified this session).\n- New, to our knowledge: the explicit counterfeit calibration (E/zeta_K moment merging, E's first Jensen failure at d = 381/382, D at ~2e4), and the fact that Phi_E(0) < 0.\nNo verification of citations was possible this session (web search budget exhausted). Polya 1927, Csordas-Norfolk-Varga, Chasse, Ki-Kim, O'Sullivan and Larson-Wagner all remain UNVERIFIED.",
 "what_is_real": "1. A sound calibration result: asymptotic Jensen hyperbolicity (GORZ) holds for any F with a_1 = 1, a gamma factor and polynomially bounded coefficients, including E and D. Numerically confirmed by two independent codes; the proof is a routine saddle-point argument. It is a fine Lean/record item. Stated precisely: counterfeit-blindness of the Hermite limit, NOT 'all Jensen data decided by a_1'.\n2. E's first Jensen failure is at (d, n) = (~382, 0), i.e. at zero-height resolution. This matches the Weil-threshold picture that every such criterion just encodes the height of the first off-line zero.\n3. Phi_E(0) < 0 while zeta, zeta_K and D have positive kernel at 0. It is a curiosity, not a criterion: D has a positive kernel at 0 yet off-line zeros, so kernel positivity at 0 already fails as a separator (by the proposer's own D data).\n4. The refined barrier moral: nonlinearity in L is necessary but not sufficient; the separator must use multiplicativity itself. It is correct as a heuristic lesson, not a theorem.",
 "next_step_if_survives": "Does not survive. The single most informative cheap follow-up is to record the calibration theorem precisely: state and prove (or formalize) the tail-dominance lemma, gamma_F(m) = gamma_1(m)(1 + O(exp(-c m/log m))), for Gamma_C and Gamma_R kernels. Before claiming novelty, check Ki-Kim (J. Anal. Math. 2003) and Farmer 2020 for the existing statement. Also check whether the global positivity of Phi (as opposed to its value at 0) fails for D. If D's kernel is everywhere positive, 'kernel positivity' is refuted as a separator outright, closing the side lead."
}
```
