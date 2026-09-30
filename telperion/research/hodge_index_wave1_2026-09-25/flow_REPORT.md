# Hodge index for Spec Z, wave 1: angle `flow`

conjecture1_proved = False. Mechanism alive: False. Survived adversarial review: False.

# Flow angle: can positivity be carried across scales? (conjecture1_proved = False)

## 1. What the flow is, stated precisely

Take real test functions f supported in [-A, A], with x = e^{2A}. The Weil form is Toeplitz:

Q_x(f) = ∫∫ f(u) f(v) W(u - v) du dv, where
W(t) = 2 cosh(t/2) + W_∞(t) - Σ_n c(n) n^{-1/2} [δ(t - log n) + δ(t + log n)].

Here W_∞ is the archimedean distribution coming from Re ψ(b/2 + ir/2) + c_0 for each Γ family. The pole term is the kernel 2 cosh(t/2), so the pole term is also Toeplitz.

Consequences of this form:

- **Nesting.** The spaces L²[-A, A] are nested, so λ_min(x) is non-increasing in x. This is trivial and holds for every Dirichlet series.
- **The flow is Krein's.** "Positivity at every scale" says the distribution W is positive definite on every interval (-log x, log x). The flow from window x to window x e^δ is exactly Krein's continuous Schur/Levinson recursion, i.e. the de Branges chain. W(x) holds for all x iff the Krein reflection function stays strictly inside the unit disk. (Discrete analogue: a Toeplitz matrix is positive definite iff every Verblunsky coefficient has |α_k| < 1.)
- **Prime entry is continuous.** The task framed each new prime power as a rank-2 perturbation of Q_x. That framing is wrong. The atom at log n enters with weight (f * f~)(log n), and the overlap vanishes at the edge of the window, so Q_x varies continuously in x. What jumps is the slope: formally, dλ/dx jumps by ≈ -ε_par · c(n) n^{-1/2} |φ(edge)|² · (1/x), where ε_even = +1 and ε_odd = -1. In words, an atom with c > 0 lowers the even-sector slope and raises the odd-sector slope.

**Test of the jump rule** (N = 48, one-sided slopes with h = 0.02). The notation "a/b" below means the jump in the even-sector slope / the jump in the odd-sector slope.

| Function, atom n | Slope jump even / odd |
|---|---|
| zeta_K, 9 | -2.2e-2 / -1.6e-4 |
| E, 9 | -5.4e-2 / +6.8e-2 |
| E, 14 | -7.6e-3 / +7.2e-2 |
| zeta_K, 16 | -2.8e-4 / +1.0e-2 |
| E, 16 | -1.5e-3 / +5.6e-3 |
| E, 21 | -2.7e-5 / +8.3e-2 |
| zeta_K, 23 | -1.3e-4 / +3.3e-2 |
| zeta_K, 25 | -1.2e-5 / +3.9e-3 |
| E, 25 | -3.3e-3 / -8.6e-5 |

- Even sector: all 9 jumps are negative, as predicted.
- Odd sector: 7 of 9 are positive, as predicted. The two exceptions (zeta_K at 9, E at 25) have the wrong sign but are tiny (-1.6e-4 and -8.6e-5).

The rule is linear in c, so it separates nothing.

## 2. Does E fail at a jump? No.

**Weights for n ≤ 36.**

- zeta_K has atoms at 2, 3, 4, 5, 7, 8, 9, 16, 23, 25, 27, 29, 32.
- E has atoms at 4, 5, 6, 9, 14, 16, 21, 25, 29, 36, with values:
  - c_E(6) = 3.58
  - c_E(9) = 6.59
  - c_E(14) = 5.28
  - c_E(21) = 12.18
  - c_E(36) = -7.17
- E has zero weight at 2, 3 and 7.

**Scan over x in [8, 26], step 0.1, N = 48.**

- Both functions are monotone in both parity sectors.
- zeta_K stays positive throughout. Even-sector λ_min runs from 0.66 at x = 8 to 4.6e-3 at x = 20 to 2.1e-4 at x = 26.
- E's even sector changes sign in (19.8, 19.9). This reproduces the certified x_E = 19.82, and **E has no atom anywhere in (16, 21)**.
- E's odd sector changes sign in (21.3, 21.4), just after the atom at 21 enters. That atom raised the odd slope by +0.083, so it pushed the failure later, not earlier.

Both of E's failures happen during smooth flow. No p^k crossing causes either one.

## 3. Which atom is responsible? Counterfactuals (N = 40)

| Weights | Even threshold | Odd threshold |
|---|---|---|
| E as is | 19.91 | 21.43 |
| c_E(6) = 0 | > 40 | 39.2 |
| c_E(14) = 0 | 22.3 | **17.7** (fails earlier: the parity rule) |
| c_E(9) set to zeta_K's value | 25.0 | 32.1 |
| c_E(21) = 0 | 19.91 | 21.17 |
| c_E(6, 14, 21) = 0 | > 40 | 27.7 |

**Decomposition on E's null vector at x = 20.5.**

- Q_E = -4.2e-4, while Q_zetaK = +1.864 on the same vector.
- Contributions to Q_E - Q_zetaK by atom:
  - atoms 2 and 3 (zeta_K has weight there, E does not): -0.89
  - atom 6: -1.27
  - atom 9: -1.01
  - atom 14: -0.19
  - atoms 7 and 8: +1.52
- The negative vector correlates positively with shifts by log 6 and log 9, and negatively with shifts by log 2 and log 3. In other words, it exploits the fact that for E, a(6) is not a(2)a(3).
- E's near-null vector hardly changes between x = 19 and x = 22. The sign change comes from a slow drift of about 3e-2 in the pole + archimedean part.

So E's horizon is controlled by the composite orbit of length log 6, the Lemma O witness c_E(6). But the flow only makes this visible after the fact: nothing in it predicts the failure.

## 4. The decisive barrier: adversaries built from local Euler data

Keep zeta_K's archimedean data, conductor 20 and pole, and choose the arithmetic adversarially. The minimization over the adversary's parameters is iterated or done by grid coordinate search.

- **Purity box** (|c(n)| ≤ 2Λ(n), any signs): stays positive at x = 6 (λ = +0.051) and fails at x = 7 (even -0.24, odd -0.49). Threshold in (6, 7).
- **Euler-shaped adversary** (c(p^k) = 2 log p cos(kθ_p) at the split and inert primes, θ_p free; the ramified prime 2 as in zeta_K): odd sector is +0.19 at x = 7 and -0.095 at x = 8, with θ_3 = θ_7 = π, i.e. local factors (1 + p^{-s})^{-2}. Threshold in (7, 8), and this failure *is* caused by a jump (the prime 7 entering).
- **E**, which has no Euler product at all, survives to x = 19.8.

**Conclusion.** Local Euler structure plus purity (unitary Satake parameters) is strictly weaker, as a source of positivity, than E's global structure. So a reason for positivity cannot come from the flow plus local Euler data. It needs the Euler product coupled to the global functional equation and to the actual Satake data. By class P = {zeta}, in degree 1 that coupled set is a single point, so the flow reduces the problem back to the moments of that one function.

## 5. Heuristic horizon law (bonus prediction; 2 data points, a guess)

x_c ≈ κ · q · (T0 / (2πe))^d, where T0 is the height of the counterfeit's first off-line zero. This is a Nyquist count: a function of exponential type A can vanish at the on-line zeros below height T0 once A exceeds πN(T0)/T0.

| Counterfeit | Predicted q (T0/2πe)^d | Actual horizon | κ |
|---|---|---|---|
| E (q = 20, d = 2, T0 = 15.67) | 16.8 | 19.82 | 1.18 |
| D (q = 5, d = 1, T0 = 85.70) | 25.1 | 31-35 | 1.24-1.39 |

This is a calibration tool for picking counterfeit controls, not a mechanism.

## 6. Literature

Web search was unavailable (budget exhausted), so everything here is cited from memory and unverified:

- Krein's extension theorem and de Branges' canonical systems: standard.
- M. Suzuki, screw functions for zeta (RH iff -g_ζ is a screw function; about 2022-2023).
- Lagarias, de Branges spaces for Dirichlet L-functions (about 2005-2006).
- Burnol, de Branges-Sonine spaces (about 2002-2004).
- de Bruijn-Newman: Rodgers-Tao (Λ ≥ 0), Polymath15 (Λ ≤ 0.22).
- Yoshida 1992 and Bombieri 2000 for small windows.
- Connes-Consani on archimedean Weil positivity.

That the scale flow is Krein's recursion is folklore. The parity rule, the counterfeit and adversary horizons and the log 6 attribution are, as far as I know, new, but that is unverified.

## 7. Verdict

The flow angle is **dead as a mechanism**: every structural property of the flow is linear in c or holds for any moment sequence. Linearity alone does not kill it: the Schur recursion is nonlinear in the moments. What kills it is that the recursion treats every moment sequence the same way, including E's and the Euler-shaped adversary's.

Odds that it leads to RH: about 0.1%.

What it can still deliver:

1. A Lean lemma: λ_min is continuous and non-increasing, and a prime entering changes only the slope.
2. A certified adversarial-horizon barrier: local Euler data plus purity fails at x < 8, while E, with no Euler product, survives to 19.8.
3. Identification of c_E(6) as the atom that controls E's horizon, for the Lemma O lane.
4. The horizon law, for choosing counterfeit controls.

Numerics are float64 Galerkin at N = 40-48, and were not certified in Arb. The E threshold matches the certified value to about 0.1. All sign claims rest on values of magnitude at least 1e-4 (one E odd-sector value, -1.1e-3 at x = 21.4, sits right at the crossing), except the two small odd-sector slope jumps flagged in section 1.

## Adversarial verdict

```json
{
 "angle": "flow (skeptic review): scale flow of the window Weil forms Q_x, read as a Krein/de Branges chain, and what happens as prime powers enter the window",
 "survives": false,
 "fatal_flaws": [
  "By the proposer's own admission, the flow is counterfeit-blind. Nesting (lambda_min non-increasing), continuity at atom entry and the parity slope-jump rule hold for every moment sequence c(n), including E and D. That makes it a restatement of W(x), not a reason for it.",
  "'W(x) for all x iff the Krein reflection function stays in the unit disk' is Bochner/Krein positive-definiteness, and Weil already made that equivalent to RH. It is a reformulation that contains RH, not a route to it. There is no hidden circularity only because nothing is claimed to be proved.",
  "Minor rigor gap: the kernel W is a distribution (log singularity at 0 plus delta atoms), not a continuous accelerant. So Krein's continuous Schur/Levinson theory does not apply verbatim. Suzuki's screw-function framework is the correct rigorous replacement, and it is already published (see novelty).",
  "The slope-jump rule (slope jump proportional to -eps_par * c(n) n^{-1/2} phi(A)^2) is a heuristic for finite-N Galerkin minimizers that are nonzero at the window edge. For the true infimum over C_c^infinity, the edge values of the minimizer are not controlled. The rule is also linear in c, so it separates nothing.",
  "The 'c_E(6) controls E's horizon' attribution is overclaimed. The edited sequences are not L-functions (they break the FE balance), and removing any large positive atom inflates positivity far above that of any genuine L-function. My check: E with c_E(6)=0 has even lambda_min 0.945 at x=22, versus 1.7e-3 for zeta_K. The proposer's own table also moves the threshold to 25 when c_E(9) is edited instead. 'Lemma O witness' is not established by this test.",
  "The adversarial-horizon 'barrier' (purity box fails at x in (6,7), Euler-shaped adversary at (7,8)) is really the known fooling / class-P barrier: data that drops the global FE cannot give positivity. It adds calibration numbers, not a new barrier.",
  "The horizon law x_c ~ kappa q (T0/2 pi e)^d fits 2 points with kappa ranging over 1.18-1.39. It is numerology, not a prediction."
 ],
 "linearity_or_classP_violation": "Yes, and the proposer concedes it. Every structural statement of the flow (monotonicity, continuity, parity jump sign, Krein/Schur recursion applied to arbitrary moments) is either linear in c or holds uniformly over all moment sequences, so it goes through verbatim for E and D. The Euler product enters only as input data. The proposer's own test, which I reproduced, shows that local Euler shape plus purity, without the global FE, gives less positivity (horizon 7-8) than E, which has no Euler product (horizon 19.8). So the only separating set is Euler product coupled with FE, which is class P = {zeta}. The flow contributes nothing nonlinear-arithmetic. It is dead by the linearity barrier and the fooling lemma.",
 "counterfeit_check": "I reproduced this with fully independent code (/private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hodge/flow_skeptic/wf.py). It evaluates the Fourier-side explicit formula directly: arch term = (1/2pi) integral of |Fhat|^2 times sum_fam[c0 + Re psi(b0/2 + ir/2)] dr, computed by quadrature to r=600. The basis is (1-t^2)P_k(t), which vanishes at the edges, so it is a different basis and a different arch evaluation from bcore. Pole and prime terms use Gauss quadrature.\nSanity check: zeta at x=2, even sector, gives 1.364e-3 at N=10, converging down toward the certified KWin margin 1.33e-3. zeta_K at x=10 and x=20 agrees with bcore (0.378 vs 0.374; 4.8e-3 vs 4.6e-3).\nE even-sector root: x = 20.33 / 19.94 / 19.88 / 19.85 at N = 16 / 24 / 32 / 40 (Galerkin upper bounds, converging down), consistent with x_E ~ 19.82 and the proposer's (19.8, 19.9).\nE odd-sector root: 22.15 / 21.50 / 21.38 / 21.31, consistent with the proposer's (21.3, 21.4).\nzeta_K stays positive at 22 and 26 (N=24: even 1.73e-3 and 2.19e-4, odd 0.34 and 0.096).\nE's weights are zero on n = 17-20, so the failure does happen in pure smooth flow (confirmed).\nD: NOT reproduced. At x >= 20, D's degree-1 form is near-null (lambda_min about 1e-13 to 1e-14, the float64 noise floor, the same saturation seen for zeta). I also checked that D is clearly positive at small windows (x = 2: 0.66; x = 5: 6.3e-3), so the code is sound, but the x_D ~ 31 horizon needs high precision (Arb) and was not tested by either party.",
 "numerics_reproduced": "Reproduced independently (N up to 40, float64):\n(1) E even threshold converges to about 19.85, trending toward 19.82; E odd about 21.31. zeta_K positive through 26.\n(2) Purity box with all c = +2 Lambda(n): even +0.056 at x=6, -0.232 at x=7 (proposer: -0.24). A sign brute force over n <= 7 at x=7 reaches -1.77 (odd sector). So the proposer's coordinate search understated the failure, but the conclusion holds.\n(3) Euler-shaped adversary with theta_3 = theta_7 = pi: odd +0.192 at x=7, -0.085 at x=8 (proposer: +0.19 / -0.095).\n(4) Counterfactual c_E(14)=0: odd sector goes negative between x = 17.5 and 18 (proposer: 17.7). Counterfactual c_E(6)=0: even stays positive to x=40 (0.163), odd is -0.040 at x=40 (proposer: 39.2).\n(5) zeta at x=2 matches the certified KWin margin.\nNot reproduced: the D horizon (below float64 resolution) and the slope-jump table (not re-run; the rule is linear in c and cannot separate anything regardless).",
 "novelty": "Low. The structural core is published. Suzuki, 'Weil's quadratic form via the screw function', arXiv:2606.09096 (submitted 2026-06-08, revised 2026-09-23; I checked the abstract) builds exactly this: the window Weil form on [-a,a] handled through the screw function and de Branges spaces, unifying Yoshida 1992, Bombieri 2001/2003, Connes-Consani 2023 and Connes-Consani-Moscovici, and taking a -> infinity. Earlier papers: Suzuki arXiv:2206.03682 (screw function for zeta, RH equivalents including a Weil-positivity analog), arXiv:2209.04658 (screw line), and Matsumoto-Suzuki arXiv:2409.00888. Other citations in the proposal (Lagarias, Burnol, Rodgers-Tao, Polymath15, Yoshida, Bombieri, Connes-Consani archimedean) are standard but were not re-verified here, because the web-search budget is exhausted. Possibly new, but minor: the parity slope-jump sign rule (linear, heuristic), the counterfeit and adversary horizon numbers, and the 2-point horizon law.",
 "what_is_real": "(a) The numerics are sound and independently reproduced. E's Weil-negativity threshold is about 19.8 in the even sector and about 21.3 in the odd sector, and it happens where E has no atom. zeta_K stays positive through x = 26. Two different Galerkin discretizations agree, and the independent code recovers the certified zeta KWin margin, so this is a good cross-validation of the project's bcore pipeline.\n(b) Calibration fact worth recording: local Euler data plus unitary purity, with the conductor-20 Gamma_C archimedean part, loses positivity by x = 7-8. E survives to 19.8. Positivity at these scales therefore comes from global FE balance, not local multiplicativity. This is a concrete, checkable instance of the class-P / fooling barrier, not a new barrier.\n(c) Easy Lean lemma: lambda_min(x) is non-increasing in x (nesting). It is useful as plumbing only.\nNot real: the flow as a mechanism, 'c_E(6) is the Lemma O witness' (counterfactuals on non-L-functions), and the horizon law.",
 "next_step_if_survives": "It does not survive. The single most informative next step is to read Suzuki arXiv:2606.09096 in full and map the project's window-form machinery onto his screw-function operators, to see whether his a -> infinity conjecture carries any structure that is not linear in the coefficients. Separately, if the D horizon is still wanted as a control: run an Arb / high-precision (dps >= 40) version of the Fourier-side form for D at x in {28, 31, 35}, since float64 cannot resolve D beyond x ~ 20."
}
```
