# Hodge index WAVE2: angle `local`

conjecture1_proved = False. Mechanism alive: False. Survived adversarial review: False.

# Local angle: place-by-place Hodge-Riemann with a product formula

conjecture1_proved = False. I did not modify the repo. Scripts are in `/private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hodge2/local/`:
- `lcore.py`: place decomposition; adds D to bcore.
- `t1_sanity.py`: reproduces the known values.
- `t2_local.py`: min-eigenvector decomposition and the S* certificate.
- `t3_xloc.py`: horizon scan.
- `t4_bisect_part.py`: bisection and prime groupings.
- `t5_purity.py`: local Toeplitz tests.
- `t6_robust.py`: N-robustness checks.

## 1. Making the angle precise

Window x = e^{2A}, f supported in [-A, A], Galerkin space of Neumann cos/sin modes. The Weil form splits by place:

Q = Pole + Arch - sum_p W_p (- X for counterfeits)

where:
- W_p = sum_k c(p^k) p^{-k/2} [g(k log p) + g(-k log p)], with g = f * f~.
- X collects the terms with n not a prime power. X = 0 exactly when a(n) is multiplicative (Lemma O).

**Definition (PSHR(x), place-separable Hodge-Riemann).** There exist real numbers lambda_p, mu_p, c_p with sum lambda_p = sum mu_p = 1 and sum c_p = 0 such that, for every place p (and the block X for counterfeits), the local form

Q_p = lambda_p Arch + mu_p Pole + c_p Gram - W_p

is PSD. The c_p are the product-formula transfers. PSHR(x) implies W(x), since Q = sum_p Q_p.

The optimal certificate is S*(x) = max over (lambda, mu) of sum_p lambda_min(Q_p). It is a concave program, and lambda_min(Q) >= S*.

**Rigidity lemma (why scalar gluing is forced).** Suppose a transfer at p has to be p-local, meaning its u-space support lies in {k log p : k in Z}. Suppose also that the transfers must sum to zero on the band |u| < log x. By unique factorization, the points k log p (k >= 1) are pairwise distinct across primes. Every coefficient with k != 0 must therefore vanish on its own, and only the scalars c_p survive.

Two ways to loosen this, and why neither helps:
- Allowing arbitrary (multiplier) transfers makes PSHR vacuous: take tau_p = W_p - W/m.
- Allowing out-of-band terms (k log p > log x) changes nothing on the window.

So PSHR is the most general non-vacuous "local Hodge-Riemann plus product formula" statement. The only other freedom would be a structured split of Arch.

**Local purity (LP_p), the local Hodge-Riemann at p.** Let s_p(k) = c(p^k)/log p and s_p(0) = d. LP_p says the Toeplitz matrix [s_p(|i-j|)] is PSD with rank <= d. By Caratheodory-Toeplitz, this is equivalent to the local Satake parameters being unitary.
- For zeta and zeta_K it holds, with alpha = roots of unity.
- The Euler product enters nonlinearly here: Newton's identities turn a(p^k) into power sums.

## 2. Euler-product usage

- **PSHR** uses multiplicativity only to make the prime side place-local (X = 0). The rigidity lemma is unique factorization.
- **LP** is the genuinely nonlinear local input (unitary Satake parameters).
- **The problem.** PSHR is additive over places, so it pays triangle-inequality losses. Section 4 shows that the actual positivity needs coherent cancellation across every prime below x.

## 3. Counterfeit controls

- Pole+Arch is **identical** for zeta_K and E (same Gamma_C and conductor 20, and the pole terms do not depend on the residue). So the whole zeta_K-vs-E question lives in the finite places.
- **E**:
  - Non-local block X: c_E(6) = 3.584, c_E(14) = 5.278, c_E(21) = 12.18, c_E(36) = -7.17.
  - Local impurity at p = 3: s_3 = (2, 0, 6, 0, 2), Toeplitz lambda_min = -4 at order 2 (n = 9). Formally alpha^2 = 3, i.e. |alpha| = sqrt3, a wrong-weight local root.
  - The same failure recurs at 7 (n = 49) and 23 (n = 529).
- **D**:
  - Impure at p = 2 (n = 4): s_2 = (1, 0.284, -2.081), lambda_min = -1.156. The same happens at 3, 7, 13 and 23.
  - Non-local block X: c_D(6) = 1.936, c_D(12) = -0.763, and so on.
- **zeta_K**: every tested p is pure (split primes (2, 2, 2, ...), inert primes (2, 0, 2, 0), ramified primes (2, 1, 1, ...)); X = 0.
- **Weights:** c_E(n) >= 0 for every n < 36 and at every prime power up to 2000; the first negative values are at n = 36, 54, 80. So any Mertens / 3-4-1-type positivity that needs only c(n) >= 0 is E-blind below 36.

## 4. Tests run and outcomes

**T0 sanity (checks bcore).**
- zeta_K, x = 20, even, 32 modes: lambda_min = +4.645e-3.
- E, x = 20, even: -4.42e-5.
- Both match `scan_neumann.txt`.
- zeta and D sit at float noise (~1e-15) for x >= 5, because of near-null saturation. For them I only used small x or structural data.

**T1: min-eigenvector anatomy.**

zeta_K, even sector, at v = argmin Q:

| x | Pole+Arch | W_2 | W_3 | W_5 | W_7 | lambda_min Q |
|---|---|---|---|---|---|---|
| 10 | 3.69 | 1.00 | 1.40 | 0.42 | 0.48 | 0.375 |
| 20 | 4.76 | 1.27 | 1.93 | 0.62 | 0.91 | 4.7e-3 |
| 28 | 5.16 | 1.36 | 2.06 | 0.68 | 1.00 | 7.0e-5 |

- Every prime pulls the same way in the critical direction.
- Odd sector: Pole+Arch has one negative eigenvalue for x >= 14 (-0.93 at x = 20, -1.63 at x = 28). zeta has n_- = 1 at x = 5 and 2 at x = 10 per parity. In those directions the primes must supply positivity, so "the Gamma factor without primes is positive" and "every sub-Euler-product is positive" are both false.

**T2: the certificate S*(x), one-parameter version.**
- zeta_K: -1.61 (x = 10), -1.98 (x = 14), -2.28 (x = 20), -4.0 (x = 28), while lambda_min(Q) stays > 0.
- E: -1.20 (x = 10) down to -3.9 (x = 28).
- **The prediction fails for zeta_K.**

**T3: horizons of PSHR (two-parameter split, bisection, 16 to 24 modes).**

| function | x_loc | Weil horizon |
|---|---|---|
| zeta | 3.00 (dies as the 2nd prime enters) | none |
| zeta_K | 7.229 (just after p = 7) | none known |
| D | 5.10 | ~31 |
| E | 9.0-9.1 (just after n = 9, its impure local factor) | 19.82 |

- zeta at x = 3.02: S* = -0.059 (16 modes) and -0.071 (24 modes), while lambda_min(Q) ~ +2e-8.
- E outlives zeta_K, so PSHR is anti-correlated with arithmetic truth.

**T4: prime groupings.** Over all 15 set partitions:
- zeta_K at x = 20 (both sectors) and at x = 12 (even sector): only the one-block grouping {2+3+5+7} certifies.
- Every finer grouping fails badly; for example {2}{3}{5+7} gives -1.9.
- Positivity is a fully coherent, all-primes phenomenon from x ~ 12 on.

**T5: LP.** Correct separation (zeta_K pure; E and D impure), but at n = 9 and n = 4 respectively, far below the Weil horizons of 19.8 and 31. Local impurity is compatible with 27 further units of Weil positivity for D. There is also a direction problem: purity bounds each W_p between -d log p ||f||^2 and d log p (2r/(1-r)) ||f||^2, with r = p^{-1/2}. That is again a per-place bound whose sum over p < x is exactly the loss that T2 measures.

## 5. What survives, and the lesson

- **No-go (numerical; Lean-certifiable at x = 3.02):** place-separable positivity fails for zeta at every tested window x > 3 (checked up to x = 8). Its reach is the one-prime window. This parallels the classical fact that p-local positivity (Mertens 3-4-1) reaches only Re s = 1, the half-plane of absolute convergence.
- **Principle:** lambda_min(Q_x) for zeta is ~2e-8 at x = 3 and ~1e-38 at x = 20. Any mechanism that proves W(x) by summing local inequalities pays a definite loss (S* - lambda_min ~ -0.07 already at x = 3.02) and is doomed. A "Hodge index for Spec Z" has to be an **exact SOS identity** whose squares are global objects, as the zero side sum |F(gamma)|^2 is. It cannot be local positivity glued by a product formula. By the rigidity lemma, the product formula can only glue scalars.
- **Usable byproducts:**
  1. Kernel certificates of E's and D's local impurity: Toeplitz 3x3 matrices with eigenvalues -4 and -1.156. These are a Lemma O companion.
  2. The quantitative fact that the zeta_K / E difference lives entirely in the finite places.
  3. The x_loc ladder (3, 5.10, 7.23, 9.1) as a calibration table for future mechanisms.

## 6. Literature

Web search budget was exhausted this session.
- **Checked via the project's reports:**
  - Connes-Consani, arXiv:2006.13771 (archimedean positivity at x = 2, pole-free, which is Yoshida 1992; full class negative at x ~ 2.1-2.5).
  - CCM, arXiv:2310.18423.
  - Weil 1952.
- **Unverified:**
  - Burnol's local Weil distributions / conductor operator (CRAS 2000).
  - Lagarias 1999, Acta Arith. (RH <=> Re xi'/xi > 0 on Re s > 1/2).
  - Bombieri 2000, Rend. Lincei.
  - Krein's extension theorem (1940).
  - Mertens 1898.
- I know of no published statement of the scalar-gluing rigidity or of the x_loc horizons.

## 7. Odds

- PSHR as a route to RH: effectively 0 (refuted).
- A local-global mechanism with exact (SOS) gluing: under 0.3%.
- Deliverables short of RH: the no-go certificate, the rigidity lemma, the impurity witnesses, and the calibration ladder.


## Adversarial verdict

```json
{
 "angle": "local (skeptic review): place-by-place Hodge-Riemann (PSHR) glued by a scalar product formula, plus local purity (LP) via Caratheodory-Toeplitz",
 "survives": false,
 "fatal_flaws": [
  "PSHR is strictly stronger than W(x) and fails as soon as there are two places. Reproduced with independent u-space code: at x=3.02, S* = -5.61e-2 (N=16, even sector) while lambda_min(Q) = +5.8e-8. S* goes to 0- as x -> 3+ (-1.38e-3 at 3.001, -1.32e-2 at 3.005). The proposal already declares this: alive=false.",
  "The failure is generic, not arithmetic. Q_x is near-null (lambda_min ~ 1e-8 at x=3), so any split into two or more PSD summands with few free parameters must make the same near-null vector null in every summand, and that almost never happens. The no-go therefore tells us nothing specific about local structure or the Euler product.",
  "The 'most general non-vacuous gluing' claim is false as stated. The rigidity lemma only rules out transfers supported on {k log p}. It does not touch absolutely continuous kernel splits of the archimedean distribution, Arch = sum_p K[h_p] with K[h](g) = integral of g(u)h(u) du. Those cannot cancel the prime deltas, so they are non-vacuous, and they strictly contain the scalar/proportional ansatz tested here. They are also the shape of Connes' semilocal cutoff. The no-go covers a narrow ansatz only.",
  "PSHR is not counterfeit-sensitive. Its horizons (zeta 3, D ~5.1-5.3, zeta_K ~7.1-7.4, E ~8.9-9.3) track when a fresh edge place enters and bear no relation to x_E ~ 19.82 or x_D ~ 31. E outlives zeta_K.",
  "LP (Toeplitz PSD of rank <= d for s_p(k) = c(p^k)/log p) is local temperedness, i.e. the Ramanujan/Satake-unitarity condition. It is a necessary structural property, not a positivity mechanism. For E and D it just restates non-Eulerity (Lemma O), since D and E have no local factors at all. It predicts nothing about where W fails: it trips at n=9 for E and n=4 for D. Minor correction: PSD Toeplitz of rank <= d gives unit-circle atoms with positive weights summing to d, not necessarily d unit-weight Satake parameters.",
  "Small factual error: the first negative c_E(n) are at n = 36, 54, 84, 126, 189 (recomputed), not '36, 54, 80'."
 ],
 "linearity_or_classP_violation": "PSHR uses the Euler product only to make the prime side place-local, so that the non-prime-power block X = 0 (Lemma O, which is nonlinear). But positivity of each local block is then tested with the same linear archimedean/pole budget, and the no-go at x=3.02 is a pure near-null-geometry fact that would hold for any L-function with a near-null window. LP is genuinely nonlinear (Newton identities turn a(p^k) into power sums) and separates zeta_K from E and D, but it is a local tautology: it cannot see the global scale x at which W fails. Neither piece violates the class-P / fooling lemma, because neither claims to prove W. Neither piece escapes it either.",
 "counterfeit_check": "This is my own independent code (myform2.py, u-space arch via the digamma integral representation, no bcore). Sanity values match the project to four digits:\n- zeta, x=2, N=16: 1.3528e-3 (certified KWin margin 1.33e-3).\n- zeta_K, x=20, even, N=32: 4.6451e-3.\n- E, x=20, even, N=32: -4.4206e-5.\n- E, x=19.5: +7.76e-4, consistent with x_E ~ 19.82.\n\nPSHR horizons, bracketed. A positive S* is certified, because the ascent gives a lower bound. A negative S* is only indicative, except for zeta, which is a concave 2-D grid.\n- zeta_K: S* >= +0.273 at 7.1, ascent value -0.056 at 7.4.\n- E: +0.226 at 8.9, -0.353 at 9.3 (after n=9 enters p=3).\n- D: +1.0e-3 at 5.0, -1.5e-3 at 5.3.\n\nAll of these fail far below x_E and x_D, so PSHR is counterfeit-blind. LP Toeplitz witnesses reproduced exactly:\n- E: s_3 = (2, 0, 6), lambda_min = -4.0 at n=9, repeating at 49 and 529.\n- D: s_2 = (1, 0.2841, -2.0807), lambda_min = -1.1556 at n=4, repeating at 9, 49 and 529.\n- zeta_K: pure at every tested p.\n- Non-prime-power weights: c_E(6) = 3.584, c_E(14) = 5.278, c_D(6) = 1.936.",
 "numerics_reproduced": "Yes, with independent code. Values match to 2-4 digits:\n- zeta S*(3.02) = -0.0561 (proposal: -0.059 / -0.071).\n- The zeta_K, E and D horizon brackets match the proposal's 7.229, 9.0-9.1 and 5.10.\n- The LP witnesses match exactly.\n\nOne rigor point in the proposal's favour. A Galerkin subspace gives an upper bound on each lambda_min(Q_p). So S*_N < 0 implies PSHR fails for the full test class, and the no-go runs in the sound direction.\n\nTo certify it, add a dual certificate: density matrices rho_2 and rho_3 with equal Arch- and Pole-expectations and alpha + beta - tr(rho_2 W_2) - tr(rho_3 W_3) < 0. That is finite and Lean-checkable over Q.\n\nScripts are in /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hodge2/local_skeptic/:\n- myform.py, myform2.py: independent window forms.\n- check1.py, check2.py: sanity values.\n- sstar.py: concave 2-D S* for zeta.\n- hor.py, hor.out: horizon brackets.",
 "novelty": "Low.\n- The rigidity lemma is just Q-linear independence of the {log p}, i.e. unique factorization. It is folklore.\n- LP is local temperedness (Ramanujan-Petersson, and a Selberg-class-type axiom), recast through Caratheodory-Toeplitz. It is standard.\n- 'p-local positivity reaches only the region of absolute convergence' is classical (Mertens 3-4-1).\n\nThe certified-style x_loc ladder and the explicit S* no-go at x=3.02 are new as numbers, but only for a narrow ansatz.\n\nLiterature could not be verified this session: the web search budget was exhausted, so no calls were possible. From memory, and UNVERIFIED:\n- Connes, Selecta Math. 1999 (semilocal trace formula; positivity is equivalent to RH, and positivity at finite S is open).\n- Connes-Consani arXiv:2006.13771 (archimedean Weil positivity), cross-checked in the project's own reports.\n- Burnol, CRAS 2000.\n- Yoshida 1992, Adv. Stud. Pure Math. 21.\n- Bombieri 2000, Rend. Lincei.\n- Lagarias 1999, Acta Arith.\n\nNo citation was newly verified.",
 "what_is_real": "Worth keeping:\n1. A certifiable no-go: PSHR with scalar/proportional gluing fails for zeta at x=3.02, with S* ~ -0.056 against lambda_min(Q) ~ +6e-8. It can be made rigorous with a finite dual certificate.\n2. Pole+Arch is identical for zeta_K and E, so their whole difference lives in the finite places. This is useful for any future mechanism.\n3. Kernel-checkable LP impurity witnesses for E (3x3 Toeplitz, lambda_min = -4 at n=9) and D (lambda_min = -1.156 at n=4), as a Lemma O companion.\n4. A calibration principle, stated precisely: because Q_x is near-null, any sufficient condition that splits Q into two or more PSD pieces must preserve the near-null vector exactly in every piece. A lossy local-inequality proof is hopeless. The zero-side identity sum |f^(gamma)|^2 is the only known exact SOS.\n\nNot real: PSHR or LP as a source of W(x), any counterfeit prediction near 19.82 or 31, and the claim that scalar gluing is the most general non-vacuous product formula.",
 "next_step_if_survives": "The proposal does not survive. The most informative next step is to test the gap the rigidity lemma leaves: kernel-split PSHR.\n\nLook for absolutely continuous kernels h_p(u), each on a spline basis in u, and pole weights mu_p, with sum_p h_p = the archimedean kernel and sum mu_p = 1, such that each mu_p Pole + K[h_p] - W_p is PSD. Start with zeta at x = 3.02 and x = 5, then run zeta_K versus E at x = 15-22.\n\nThis is an SDP and needs cvxpy or scipy, which the venv lacks. It is the real Connes-semilocal-type local-global question. It is non-vacuous, because smooth kernels cannot cancel prime deltas. The near-null argument no longer kills it trivially, because there are many free parameters.\n\nIf it is feasible for zeta_K and becomes infeasible for E near 19.8, that is a genuine lead. If it fails for zeta at x = 3.02 as well, the local angle is closed for good. Separately, certify the x = 3.02 no-go with a rational dual certificate for Lean."
}
```
