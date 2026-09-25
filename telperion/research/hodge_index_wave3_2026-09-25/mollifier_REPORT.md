# Hodge index WAVE3: angle `mollifier`

conjecture1_proved = False. Mechanism alive: False. Survived adversarial review: False.

# Wave 3, angle "mollifier": Levinson/Conrey mollification as positivity

**Verdict: DEAD as a mechanism for W(x).** Three things are worth keeping:
- a restriction lemma that kills the "mollified Weil form";
- a validated finite-window Jensen/Littlewood certificate that tells zeta_K from E, and L(chi_5) from D, at mollifier length y ~ 11-13;
- a clean decoupling result: mollification carries only the Euler half of class P.

conjecture1_proved = False.

Code and logs are in `/private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hodge3/mollifier/`:
- `wcore.py`: a new hat-spline Weil engine that allows continuous shifts;
- t1-t9 scripts, each with a `.log`.

---

## 1. Mathematics

### 1.1 Set-up
Q_X(h) = Pole + (1/2pi) int |hhat|^2 Omega dt - sum c(n) n^{-1/2} (g(log n) + g(-log n)), where g = h * h~, the support of h lies in [-(1/2)log X, (1/2)log X], and Omega = log q + sum_j [-log pi + Re psi((1/2 + mu_j + it)/2)].

### 1.2 Lemma M1: additivity and restriction (proved, elementary)
(a) Additivity. For any Dirichlet polynomial M, -(LM)'/(LM) = -L'/L - M'/M. So the explicit-formula form of LM is W_L + W_M. "Mollifying the Weil form" adds the zero distribution of M; it does not reshape W_L. When M is the truncated inverse of L, the arithmetic side of LM vanishes for n <= y. By the explicit formula that is a rebookkeeping identity, not a gain.

(b) Restriction. Let mu_M = sum b_n n^{-1/2} delta_{log n}. Then (f * mu_M)^(t) = fhat(t) M(1/2 - it), so

  sum_rho |fhat(gamma)|^2 |M(rho)|^2 = Q_X(f * mu_M), with log X = log(X/y) + log y.

Any mollified zero-sum positivity is therefore W(X) restricted to the subspace V_{X,y}. It is implied by W(X) and can never imply it: lambda_min on V_{X,y} is at least lambda_min of Q_X. Consequence: mollification enters the explicit formula LINEARLY (as test-function shifts), so the linearity barrier applies.

### 1.3 Where the nonlinearity really lives: weighted Littlewood + Jensen
Let F = L M_b with b_1 = 1 (so F -> 1 as sigma -> infinity), Phi >= 0 smooth, and U(sigma) = int Phi log|F(sigma + it)| dt.

From Delta log|F| = 2 pi sum delta_rho, integrating twice in sigma:

  2 pi D_F(s0) = U(s0) + C_F, where D_F = sum_{rho(F), beta > s0} (beta - s0) Phi(gamma) and C_F = int_{s0}^inf (sigma - s0) int Phi''(t) log|F(sigma + it)| dt dsigma.

Since zeros of L are zeros of F, D_L <= D_F. Jensen (concavity of log, the AM-GM step used in Levinson/Conrey) gives

  **D_L <= B(b) := D_F + Gap(F), where Gap(F) = (1/2pi)[(|Phi|/2) log(mean_Phi |F(s0 + it)|^2) - int Phi log|F|] >= 0.**

Mean-value theorems (Montgomery-Vaughan) are what estimate mean_Phi |F|^2 in the asymptotic theory.

### 1.4 What mean value + mollification can prove, and the 100% barrier in finite form
- B -> 0 requires |F| -> constant in L^2(Phi), i.e. M_y -> 1/L at depth s0.
- For class P under GRH, the error decays like y^{1/2 - s0}. Certifying off-line mass < eps at depth 1/2 + delta therefore needs y ~ eps^{-1/delta}.
- W(x) is a depth-0 statement about all zeros (Weil gives up height locality to reach depth 0; Levinson gives up depth 0 to get height locality). So the method never reaches W(x) at any finite x.
- Asymptotically the output is density or proportion information: Selberg/Carlson N(sigma, T) = o(T); Levinson/Conrey kappa > 0.4.
- D satisfies the proportion-type conclusions. Selberg (1989) gives a positive proportion for linear combinations; Bombieri-Hejhal (1995, conditional) give 100%. D still has off-line zeros (Davenport-Heilbronn; >> T of them per Voronin). Both citations are from memory and unverified this run.
- **Proportion barrier:** no statement of mollifier type ("almost all zeros") can reach W(x), because W(x) fails on a single zero.

### 1.5 Euler-product usage and the decoupling
The Euler product enters only through b_L = 1/L. Multiplicativity plus Ramanujan give |b_L(n)| <= d_k(n), so sum |b|^2 n^{-2s} < infinity for s > 1/2, unconditionally. This is where density theorems and self-mollifier convergence come from. It is a local-Euler, right-half-plane property and never sees the FE.

For E, b_E is not multiplicative and 1/E has a pole at 0.933 + 15.668i, so its partial sums diverge at s0 < 0.933. That is the exact failing step. The same step fails for D, at 0.8085.

**Decoupling proposition (numerical, t5 + t9):**
- Random pure Euler data with zeta_K local types have inverse partial sums O(y^{~0.5}), the Wintner-type behaviour.
- Yet their Weil window forms (zeta_K Gamma factor, conductor 20, pole) are negative in 10% of draws at X = 10 and 80% at X = 20.
- zeta_K itself stays positive: 5.1e-3 at X = 20.

So mollifier convergence is generic for Euler products, while Weil positivity is not. In class P the two are tied only by GRH <=> (Littlewood criterion) <=> W(x) for all x. That tie is RH-equivalent, not a positivity. This repeats the wave-1 Local-Euler barrier from the mollifier side.

---

## 2. Tests run

### T1/T2: engine validation (wcore.py; hat splines; arch term by trapezoid in t with aliasing period 40)

| Case | Result | Reference |
|---|---|---|
| zeta, x = 2 | lambda_min 1.358e-3 (N = 200) | certified 1.33e-3 |
| zeta_K, X = 20 / 22 / 25 | +4.9e-3 / +1.7e-3 / +4.0e-4 | positive |
| E threshold, N = 200 | 19.946 | 19.825 |
| E threshold, N = 400 | 19.890 | 19.825 |
| E, X = 22 / 25 | -1.6e-2 / -1.5e-1 | negative |

The engine's noise floor is about 1e-8, so zeta beyond x ~ 5 is out of reach. Zeta was not used past that point.

### T3: mollified window forms, X in {15, 18, 19.5, 20.5, 22, 25}, y in {2.5, 3.5, 5.5}, P(x) = x
- Every mollified lambda_min is positive, of order 0.4-2.7, for zeta_K AND for E, including E at 20.5 / 22 / 25, where the full window is negative (-4.1e-4 / -1.4e-2 / -1.4e-1).
- Prediction "mollified form fails for E near 19.82": **refuted**, exactly as lemma M1 says it must be.

### T4: detection thresholds of E on mollified subspaces (90 hats per unit; plain threshold at this resolution ~ 20.07)

| y | mollifier | E fails at total X | X/y |
|---|---|---|---|
| 2.5 | own (= plain, since b_E(2) = 0) | 50.2 | 20.1 |
| 5.5 | own | 105.6 | 19.2 |
| 5.5 | zeta_K's | 76.6 | 13.9 |
| 5.5 | zeta's | 84.6 | 15.4 |
| 10.5 | own | 170.7 | 16.3 |
| 10.5 | zeta_K's | 125.1 | 11.9 |

- Detection in total window is always far beyond 19.82.
- **The counterfeit's own mollifier is the worst detector.** Self-mollification adapts to whatever L is, Euler product or not.

### T5: Littlewood/Mertens test, S(y) = sum_{n<=y} b_L(n), up to y = 1e6
Values are max |S| / sqrt(y) over [Y/10, Y].

| L | 1e2 | 1e3 | 1e4 | 1e5 | 1e6 | fitted exponent (theory) |
|---|---|---|---|---|---|---|
| zeta_K | 1.31 | 1.85 | 1.80 | 2.27 | 2.20 | 0.57 (log-inflated) |
| zeta | 0.83 | 0.57 | 0.47 | 0.46 | 0.44 | 0.49 |
| E | 2.40 | 3.89 | 7.23 | 21.3 | 52.5 | 0.89 (0.933) |
| D | 0.74 | 0.75 | 0.90 | 1.91 | 3.11 | 0.73 (0.8085) |
| random Euler | ~1 | ~1 | ~1 | ~1 | ~1 | 0.47-0.52 |

Separation scale: y ~ 1e3-1e4 for E and ~1e5 for D. That is much weaker than the Weil windows (19.82 and ~31).

### T6-T8: finite-window Levinson/Jensen certificate
Phi is a Gaussian of width 2 centred at the counterfeit's zero. Mollifiers are natural: b = b_L(n) times the Levinson weight log(y/n)/log y, or the Riesz weight (1 - n/y)^2.

The identity checks out: D_E = 0.1830 exactly (theory 0.933 - 0.75), D_{zeta_K} = -0.001 (quadrature error), and neither moves with y.

Bound B(y), in the form "Levinson / Riesz":

| s0 | L | counterfeit mass | y = 5 | y = 13 | y = 20 | y = 100 | y = 1000 | tail gap G at 5e4 |
|---|---|---|---|---|---|---|---|---|
| 0.75 | zeta_K | (E: 0.183) | .34 / .40 | .157 / .163 | .12 / .10 | .08 / .06 | .04 / .04 | .018 / .008 |
| 0.75 | E | 0.183 | .39 / .40 | .34 / .35 | .32 / .32 | .29 / .41 | .30 / .65 | .23 / .41 (rising) |
| 0.60 | zeta_K | (E: 0.333) | .53 / .58 | .27 / .29 | .23 / .23 | .18 / .19 | .12 / .26 | .062 / .16 |
| 0.60 | E | 0.333 | .61 / .61 | .55 / .56 | .54 / .56 | .59 / .85 | .81 / 1.42 | rising |
| 0.90 | zeta_K | (E: 0.033) | .23 / .29 | .10 / .10 | .075 / .056 | .04 / .018 | .019 / .006 | .008 / .000 |
| 0.90 | E | 0.033 | .24 / .25 | .20 / .20 | .18 / .17 | .13 / .15 | .09 / .17 | .034 / .14 |
| 0.65, t = 85.7 | L(chi_5) | (D: 0.157) | .27 / .41 | .148 / .148 | .125 / .104 | .083 / .063 | .052 / .042 | .023 / .011 |
| 0.65, t = 85.7 | D | 0.157 | .42 / .43 | .36 / .36 | .34 / .35 | .28 / .43 | .27 / .64 | .16 / .35 (rising) |

Findings:
- **Separation:** the genuine L-function's certificate drops below the counterfeit's true off-line mass at y = 11 (Levinson; refined in t7b: B = 0.180 at y = 11) or 12 (Riesz) for zeta_K vs E at s0 = 0.75. The crossing is at y ~ 13 for s0 = 0.60, y ~ 34-300 for s0 = 0.90, and y ~ 13 for L(chi_5) vs D.
- **Counterfeit behaviour:** the counterfeit's own self-mollifier bound bottoms out and then grows. This is the finite shadow of 1/E and 1/D diverging. Riesz self-mollifiers of E and D even create extra off-line zeros of M (D_F climbs from 0.183 to 0.40).
- **Depth barrier, visible directly:** at s0 = 0.60 zeta_K's gap is still 0.06 at y = 5e4. The sharp and Riesz zeta_K mollifiers also create spurious off-line zeros of M: D_F = +0.04 to +0.05 for y >= 300 at 0.60, and up to +0.24 for sharp truncations at 0.75.

### T9: random Euler data vs Weil windows (40 draws, zeta_K local types)
- Fraction Weil-negative: 0.00 at X = 6, 0.10 at X = 10, 0.80 at X = 20.
- Minimum lambda: -0.55 at X = 10, -2.1 at X = 20.
- zeta_K itself: +0.91 (X = 6), +0.39 (X = 10), +5.1e-3 (X = 20).

### Nyman-Beurling side-calculation (the known criterion this angle collapses to)
- Blaschke floor: the distance from 1 to E * (Dirichlet polynomials) in L^2(ds/|s|^2) is at least about (2 beta - 1)/|rho|^2 = 3.5e-3 from E's first zero (9.7e-4 and 3.0e-4 from the next two). For D the floor is 8.4e-5.
- zeta_K's distance: heuristically d_N^2 ~ C_K / log N, with C_K = sum 1/|rho|^2 = 0.0462 (zeta) + 0.6388 (L(chi_-20)) = 0.685. Carrying Burnol's theorem over to zeta_K is an assumption.
- Separation therefore needs log N ~ 195, i.e. **N ~ e^195**, against x_E = 19.82 for Weil. Nyman-Beurling is an exponentially worse detector.

---

## 3. Counterfeit control summary
| Object | zeta_K / L(chi_5) | E | D |
|---|---|---|---|
| Mollified Weil subspaces (M1) | positive | positive to X ~ 50-170 (never near 19.82) | not run |
| 1/L partial sums | ~ y^{1/2} | y^0.89 (0.933) | y^0.73 (0.8085) |
| Jensen certificate B -> 0 | yes; crossing at y ~ 11-13 | no; bottoms at 0.285, then rises | no; bottoms at 0.26, then rises |
| Random Euler (no FE) | 1/L partial sums ~ y^{1/2}, yet Weil-negative (80% at X = 20) | - | - |

Every separation above is ZERO-driven: the counterfeit's 1/L has poles. None of it is a positivity that could prove W(x).

## 4. Literature
**Verified this run:** Bettin-Conrey-Farmer, arXiv:1211.5191, "An optimal choice of Dirichlet polynomials for the Nyman-Beurling criterion": under RH and sum 1/|zeta'(rho)|^2 << T^{3/2-delta}, the Baez-Duarte constant equals Burnol's lower bound.

**From memory, flagged UNVERIFIED** (the web-search budget was exhausted this session):
- Levinson 1974 (Adv. Math. 13); Conrey 1989 (J. reine angew. Math. 399), > 2/5 of zeros on the line.
- Bui-Conrey-Young 2011 (Acta Arith.); Pratt-Robles-Zaharescu-Zeindler 2020, > 5/12.
- Farmer 1993, long mollifiers (theta = infinity implies 100%).
- Selberg, Amalfi 1989: positive proportion for linear combinations.
- Bombieri-Hejhal, Duke Math. J. 80 (1995): 100% for linear combinations, conditional.
- Davenport-Heilbronn 1936; Voronin 1976.
- Littlewood 1912: the M(x) criterion.
- Wintner 1944: random multiplicative functions.
- Burnol 2002 (Adv. Math.); Baez-Duarte 2003 (Rend. Lincei); Lagarias 1999 (Acta Arith.).
- Kaczorowski-Perelli: density theorems in the Selberg class.

No prior "mollified Weil form positivity" proposal was found. M1 shows why it would fail.

## 5. Odds and deliverables
- RH via this angle: < 0.1%.
- Kept for the barrier ledger: M1, the restriction/additivity lemma. With it goes the finite-scale "100% barrier": certifying depth 1/2 + delta needs y ~ exp(c/delta), and the proportion barrier via Selberg/Bombieri-Hejhal for D.
- Lean candidate (~60% within weeks): the weighted Littlewood identity plus Jensen as a zero-exclusion certificate, e.g. certify B_{zeta_K}(0.75, y = 13) < 0.183 in Arb. It tells zeta_K from E at finite scale, but only by zeros.
- Structural takeaway for wave 4: mollification is exactly the Euler (right-half-plane, L^2) half of class P, and it is generic for random Euler products. The FE half is what makes Weil positivity non-generic. A Hodge index for Spec Z must couple b_L = 1/L to the reflection s -> 1-s. Mollifier technology does not attempt that coupling.

## Adversarial verdict

```json
{
 "angle": "mollifier (Levinson/Conrey mollification as a \"mollified Weil form\"): adversarial skeptic review",
 "survives": false,
 "fatal_flaws": [
  "The proposer says the angle is dead, and I agree. Lemma M1 is correct and elementary. Write mu_M = sum b_n n^{-1/2} delta_{log n}. The mollified zero sum sum_rho |fhat(gamma)|^2 |M(rho)|^2 equals Q_X(f*mu_M), because Q depends only on f*f~, which is translation invariant, so the shifted support re-centres to width log X. A mollified Weil form is therefore W(X) restricted to a subspace. Positivity on a subspace is implied by W(X) and can never imply it, so no positivity mechanism can come from it.",
  "Mollification enters the explicit formula linearly: W_{LM} = W_L + W_M, and b_n acts only through test-function shifts. So the linearity barrier applies to the mollified-form version. The one nonlinear step (the Dirichlet inverse b_L = 1/L, then Jensen/log-concavity) only controls zeros at depth s0 > 1/2. Certifying depth 1/2 + delta needs mollifier length y ~ exp(c/delta), so the method never reaches W(x), which is a depth-0 statement.",
  "The asymptotic outputs are proportion statements, which Davenport-Heilbronn also satisfies: Selberg gives a positive proportion of zeros on the line for linear combinations, and Bombieri-Hejhal give 100% conditionally. One off-line zero is enough to break W(x), so no 'almost all zeros' result can reach it.",
  "Every separation of zeta_K from E and of L(chi_5) from D is driven by zeros (1/E and 1/D have poles at the off-line zeros). None of it is a positivity. The counterfeit's own mollifier is the worst detector: E stays Weil-positive on its self-mollified subspace up to X ~ 105-110 at y = 5.5. So the mechanism fails the requirement that its separation come from a positivity."
 ],
 "linearity_or_classP_violation": "The mollified Weil form is linear in the L-function data: additivity W_{LM} = W_L + W_M, plus restriction to f*mu_M. It sits squarely inside the linearity barrier and is only a restriction of W, so it passes for any L on which W holds. The Euler product does enter nonlinearly in one place, the Dirichlet inverse b_L = 1/L, where multiplicativity gives |b| <= d_k. But that is a local-Euler, right-half-plane input and never touches the functional equation, so it hits the wave-1 Local-Euler barrier again. The proposer's own t9 shows this: random pure Euler data have square-root-cancelling inverse partial sums, yet are Weil-negative in 80% of draws at X = 20. Class P is tied to mollifiers only through the known RH-equivalences (Littlewood's M(x) criterion and Nyman-Beurling/Baez-Duarte). Those are circular, not a new positivity. The fooling lemma is respected in the sense that the proposer claims nothing that would also hold for D.",
 "counterfeit_check": "Reproduced independently, with my own frequency-space hat engine in scratchpad/hodge3/mollifier_skeptic/ (a separate Galerkin: closed-form hat Fourier transforms, cubic-B-spline autocorrelations, arbitrary centres).\n\nPlain Weil controls:\n- E is positive at 19.9 (9.7e-5 at M = 160) and negative at 20.0 (-3.9e-5), converging downward toward x_E ~ 19.82. At 22 it is -1.46e-2.\n- zeta_K is positive at 20 / 22 / 25: 4.95e-3 / 1.83e-3 / 4.3e-4.\n- c_E(n) >= 0 for n < 36 is confirmed (first negative at n = 36).\n\nMollified subspaces (Levinson weights, y = 2.5 and 5.5, X = 20.5 / 22 / 25):\n- E's own mollifier, zeta_K's mollifier, and zeta_K with its own mollifier are all positive, with lambda_min between 0.40 and 2.52. So the predicted separation at ~19.82 is refuted, exactly as M1 says it must be.\n\nE detection on the mollified subspace at y = 5.5:\n- Own mollifier: +1.2e-4 at X = 105, -1.7e-3 at X = 110 (proposer: 105.6).\n- zeta_K's mollifier: already negative at X = 90 (proposer: 76.6; not bracketed further).\n\nD control:\n- My engine does NOT resolve D's Weil failure near 31. At X = 28 / 31 / 34 / 38 lambda_min is about 1.5e-6 to 5.4e-6 at M = 160, and it is still falling as M grows, so this is a resolution limit.\n- x_D ~ 31 therefore remains unconfirmed by me. The proposal makes no claim about D's Weil threshold, so this does not affect the verdict.",
 "numerics_reproduced": "Script: scratchpad/hodge3/mollifier_skeptic/{sk.py, t1-t4.py}. Single process, nothing left running.\n\n(1) Engine validation:\n- zeta at x = 2: lambda_min 1.45e-3 (M = 40), 1.395e-3 (M = 80), heading toward the certified 1.33e-3.\n- zeta_K at 20 / 22 / 25: 4.95e-3 / 1.83e-3 / 4.27e-4 (proposer: 4.9e-3 / 1.7e-3 / 4.0e-4).\n- E crosses zero between 19.9 and 20.0 at M = 160; the zero-crossing falls as M grows.\n\n(2) Mollified forms (T3): all positive, 0.40-2.52, including E at 20.5 / 22 / 25. Reproduced.\n\n(3) T4 threshold, E with its own Levinson mollifier at y = 5.5: sign change between X = 105 and 110. Reproduced (proposer: 105.6). With zeta_K's mollifier, E is negative by X = 90, consistent with the proposer's 76.6.\n\n(4) T5 inverse partial sums, max|S|/sqrt(Y) at Y = 1e3 / 1e4 / 1e5 / 1e6, with the exponent fitted over 1e4-1e6:\n\n| L | 1e3 | 1e4 | 1e5 | 1e6 | fitted exponent (theory) |\n|---|---|---|---|---|---|\n| zeta | 0.38 | 0.43 | 0.42 | 0.37 | 0.47 |\n| zeta_K | 1.33 | 1.47 | 1.89 | 2.18 | 0.59 |\n| E | 3.42 | 6.09 | 20.95 | 49.5 | 0.955 (0.933) |\n| D | 0.62 | 0.76 | 1.86 | 2.95 | 0.79 (0.8085) |\n\nReproduced within window-choice noise.\n\nNot reproduced: the T6-T8 Jensen/Littlewood certificate crossings (y ~ 11-13) and the T9 random-Euler fractions. The weighted Littlewood identity itself is standard.",
 "novelty": "Low.\n- The restriction lemma is an elementary observation. I know of no paper stating it, but it is folklore-level.\n- The mollifier <-> Nyman-Beurling link is known: Bettin-Conrey-Farmer, arXiv:1211.5191. The proposer checked the abstract; I could not re-verify it because this session's web-search budget is used up.\n- Littlewood's criterion, Selberg's positive proportion for linear combinations, Bombieri-Hejhal (Duke Math. J. 80, 1995, conditional 100% on the line for linear combinations) and Farmer's long-mollifier heuristic are standard. The citations match my knowledge, but I did not verify them online this run.\n- The finite-scale framing is mildly new: the explicit y ~ exp(c/delta) depth barrier and the measured \"self-mollification hides counterfeits\" thresholds.\n- Nothing in it is a new positivity mechanism.",
 "what_is_real": "Three things are real and worth keeping:\n(a) Lemma M1 (additivity plus restriction): a clean barrier-ledger entry. \"Mollified Weil positivity\" is W restricted to the subspace f*mu_M, so it can only delay detection. I confirmed numerically that it delays E's detection from ~19.9 to ~105-110 at y = 5.5.\n(b) The measured fact that self-mollification is the worst counterfeit detector, while a foreign (genuine) mollifier detects E earlier.\n(c) Growth of the 1/L partial sums as a zero-driven separator: E and D exponents close to their off-line beta, against about 1/2 for zeta and zeta_K. It is real, but it is a weak detector (y ~ 1e3-1e5, versus Weil 19.82) and just Littlewood's criterion restated.\n\nThe Euler/FE decoupling claim (mollifier convergence is generic for random Euler products while Weil positivity is not) is a useful structural restatement of the wave-1 Local-Euler barrier. I did not rerun t9.\n\nThe finite Jensen certificate is a legitimate zero-exclusion tool. It tells zeta_K from E at y ~ 11-13, but only through zeros, never through a positivity.\n\nconjecture1_proved = False.",
 "next_step_if_survives": "It does not survive. The single most useful next step is to add M1 (restriction/additivity) and the finite depth barrier (y ~ exp(c/delta)) to the barrier ledger. Record there that any wave-4 candidate that acts on W only through test-function shifts or convolution by arithmetic measures is automatically a restriction of W, and dead.\n\nIf the project wants a concrete deliverable, the cheapest one is an Arb-certified finite Jensen/Littlewood zero-exclusion: B_{zeta_K}(s0 = 0.75, y = 13) < 0.183. It is formalizable but gives no progress on W(x).\n\nHousekeeping: my engine cannot resolve D's Weil failure near x ~ 31, where lambda_min is about 1e-6 and not converged. The D-threshold control should be re-certified with the project's high-precision code before any wave relies on the \"D fails beyond ~31\" number."
}
```
