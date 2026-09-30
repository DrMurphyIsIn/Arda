# Hodge index for Spec Z, wave 2: synthesis of li, mobius, dfi, local and jensen, cross-referenced with wave 1

**Bottom line.** None of the five wave-2 angles gives a reason for Weil positivity. Together with wave 1 (arakelov, squareroot, amplify, flow, reflection), that makes ten angles with no mechanism left standing. Every failure falls into one of three classes:

- **Linear or asymptotic.** The argument uses the coefficients linearly, or only in a limit where they stop mattering. The same argument then goes through for E and D, so it cannot separate them from zeta.
- **Circular.** The argument is an RH-equivalent criterion. It separates zeta from E and D only because it reads off their off-line zeros.
- **Lossy splitting.** The argument splits Q_x into separately positive pieces. zeta's window form is near-null (lambda_min about 1e-8 at x = 3 and about 1e-38 at x = 20), so any split that loses anything is killed at once.

A proof would have to be an exact sum-of-squares identity that couples the Euler product to the functional equation across all primes at once. `conjecture1_proved = False`.

## 1. What died, and why (one line each)

- **li, M1 and M2 (diagonal Li; Gram/Schoenberg-Li).** Both are equivalent to RH. K(i,j) = W(g_i * g_j~) is the Weil form restricted to the Laguerre span, so it adds no input.
- **li, M3 (Schur-Hadamard over places).** It is ill-defined. Li coefficients are taken at s = 1, the pole. There the product over primes diverges (the sum of log p/(p-1) is infinite). Every finite block has psi(1) < 0, so no finite block can be conditionally negative definite. Regularising restores the explicit formula.
- **mobius, M1 (Halász, Matomäki-Radziwiłł, Tao).** These theorems give no power saving. They do not change under sparse changes at the primes, and they never see the functional equation.
- **mobius, M2 (mollified Nyman-Beurling).** It is equivalent to RH (Littlewood). It separates only through off-line zeros, and its resolution is exponentially coarser than the windows: log N* ≈ 5 against log x_E ≈ 3.
- **dfi (amplification).** Transfer from the family to one member needs Q_d ≥ 0 for the dropped members, which is GRH for the family. The averaged form is linear in c_L, and averaging pushes the counterfeit horizon out the wrong way: about 20 for a single E, about 663 for a 5-member family, beyond 3000 for 21 members.
- **local, PSHR (place-separable, scalar gluing).** It is strictly stronger than W(x) and fails for zeta at x = 3.02: S* = -0.056 while lambda_min(Q) = +6e-8. Its horizons (zeta 3, D ~5, zeta_K ~7.2, E ~9) do not track counterfeits.
- **local, LP (Carathéodory-Toeplitz purity).** This is local temperedness. It does separate E (trips at n = 9) and D (trips at n = 4), but it knows nothing about the scale x.
- **jensen (GORZ).** It is counterfeit-blind. Its tail-dominance lemma, gamma_F(m) = gamma_1(m)(1 + O(e^{-cm/log m})), makes the Hermite limit depend only on a_1 = 1. Jensen polynomials first fail at d ≈ 0.6 t^2 log t (E at 381/382, D at ~2.1e4). That is zero verification, not a mechanism.

Wave 1 died in the same classes:

- LEB (arakelov): local purity is not enough.
- Sign barrier (reflection): c_E(n) ≥ 0 for n < 36 and E is still negative.
- Theorem A (amplify): a cone restatement of RH.
- flow: blind to counterfeits.

## 2. Survivors: true statements ranked by (value if true) × (tractability)

None survives as a mechanism. Here is what is real.

| # | Statement | Status | Gap | RH in disguise? |
|---|---|---|---|---|
| 1 | **Kernel-split semilocal SDP (KS-PSHR).** Look for absolutely continuous kernels h_p (a spline in u) with sum_p h_p = Arch, and pole weights mu_p ≥ 0 with sum mu_p = 1, such that each mu_p·Pole + K[h_p] − W_p is PSD. The local skeptic showed that the rigidity lemma does *not* exclude this: smooth kernels cannot cancel prime deltas, so the construction is non-vacuous, and it has many free parameters, so the near-null argument does not kill it trivially. It is Connes' semilocal question as a finite SDP. | Untested; the venv has no SDP solver. | Feasibility for zeta at x = 3.02 and 5; zeta_K versus E at x = 15–22. | Not as posed. The all-x version would be a genuine local-global theorem, not a restatement. |
| 2 | **EFW (wave 1): Euler-FE window rigidity.** mu(x) = inf of lambda_min over data with (i) Euler shape plus purity, (ii) the Guinand-Weil identity truncated at x, and (iii) Gamma, q and pole fixed. | Untested. | The optimisation at conductor 20, x ∈ [5, 25]. | Not as posed. |
| 3 | **Prime-power projection result (new, run in this synthesis).** Let E_pp be E's weights with the non-prime-power block X removed (c_E(6) = 3.584, c_E(14) = 5.278, c_E(21) = 12.178). E_pp stays Weil-positive well past x_E. At x = 22 it gives +0.906 even / +0.457 odd, while E gives −5.0e-4 / −2.6e-3. It first fails in the odd sector at **x ≈ 27.76**, stable between N = 16 and N = 24 modes. Conversely, zeta_K's prime-power weights plus E's block X are already negative at x = 15 (−1.06). | Float64 Galerkin, 16–24 modes per sector. Negative values are genuine Rayleigh-Ritz witnesses. | Arb certification. | No. It is anatomy. |
| 4 | **Counterfeit calibration dictionary.** Li: E first goes negative at n = 5713 and D at n = 328997 (Voros-predicted); the Gram matrix goes indefinite at N = 27 for E and N = 149 for D; zeta_K is PSD through N = 158. Jensen onset: E at d = 381/382. Nyman-Beurling turns up for E at N* ~ 200. Twisted counterfeit: E⊗χ_{−19} is negative at x = 28 while the 67-member family average is +4.5. | Main numbers reproduced independently (E Gram 27; E Jensen 382; E-family averages). Not reproduced: D's Gram 149, D's Jensen onset, and D's Nyman-Beurling upturn below 1e5. | Arb and kernel certificates. | No. These are negative controls. |
| 5 | **Barriers.** (a) Moment-functional barrier, asymptotic form only: GORZ-type hyperbolicity holds for every F with a_1 = 1, a functional equation and polynomial growth. (b) Amplification barrier: positive family average does not imply positive members, with certified E-family instances. (c) Near-null calibration rule: any sufficient condition built from two or more PSD pieces must keep zeta's near-null vector null in every piece. | (a) proof sketch plus numerics; (b) numeric; (c) elementary. | Write-up; formalise (a). | No. |

**How item 3 reads against wave 1.** Prime-power support alone is not the discriminator. The non-Euler block X accounts for about 8 units of x (19.8 → 27.8). E_pp still fails, and it is locally impure: c_E(9)/log 3 = 6, which breaks the purity bound d = 2. Wave 1's LEB shows that purity alone fails at x ≈ 6 under adversarial choice. So neither "support on prime powers" nor "local purity" works alone. Only the conjunction with global FE balance can work, which is exactly what EFW tests. This is the first quantitative split of E's failure into a part caused by missing multiplicativity (X) and a part caused by impurity.

## 3. RH criteria that fail for E and D by construction

**None was found, and here is why.** Every RH-equivalent found in waves 1 and 2 is statable for a single L-function: Li, Gram-Li, Nyman-Beurling, Jensen, and Theorem A. Such a criterion fails for E and D only because they have off-line zeros. The most sensitive one we have is **Gram-Li PSD**: K_N = [λ_i + λ_j − λ_{i−j}] is PSD for all N. It flags E at N = 27 and D at N = 149, roughly 200 to 2000 times earlier than diagonal Li. It is a zero detector: Bombieri 2000 gives its negative index as half the number of off-line zeros. There is no map from N to x.

A criterion that fails for counterfeits *by construction* has to be a statement about a class, with the Euler product as a hypothesis. The precise candidate is:

> **Conjecture (EFW-KS).** For every datum 𝒟 that is Euler-pure (c(p^k) = log p · Σ_i α_{p,i}^k with |α| = 1, and c = 0 off prime powers), satisfies the functional equation and the Gamma/q/pole constraints, and satisfies the Guinand-Weil identity for window-supported tests, the kernel-split semilocal SDP of §2 row 1 is feasible at every x.

For zeta this implies W(x) for all x. E and D are excluded at step (i), which is an input and not a zero readout. It is open whether it holds even at x = 20. If it failed at some finite x, that would be the strongest barrier yet: the full conjunction would still not be enough at finite scale.

## 4. Build lanes (two)

**Lane A: certified barrier and counterfeit ledger (kernel-checkable, low risk).**

1. PSHR no-go at x = 3.02, as a rational dual certificate: density matrices ρ_2 and ρ_3 with matched Arch/Pole expectations and a negative value.
2. LP impurity witnesses: 3×3 Toeplitz matrices, lambda_min = −4 for E at n = 9 and −1.156 for D at n = 4. These accompany Lemma O.
3. E Gram-Li indefinite at N = 27, in Arb.
4. E⊗χ_{−19} Weil-negative at x = 28, through FWindow with conductor 7220.
5. E_pp negative at x = 28 in the odd sector, plus positive at x = 22 in both sectors.
6. Wave 1's LEB witness and sign barrier.
7. Close the D gap: all D numbers beyond x ≈ 20 are still float64. Certify D at x ∈ {28, 31, 35} in Arb with dps ≥ 40, and redo Gram-Li for D at N = 148/149.

**Lane B: one combined SDP experiment (EFW-KS).**

1. Install cvxpy (or use scipy with a hand-written log-barrier).
2. Solve the kernel-split SDP for zeta at x = 3.02 and 5. If it is infeasible there, the local angle is closed for good.
3. If it is feasible, run zeta_K versus E_pp versus E at x ∈ [15, 28], then add Euler-purity constraints on free Satake angles (wave 1's EFW).
4. Pass criterion: feasible for zeta_K through 28, infeasible for E near 19.8 and for E_pp near 27.8. Any certified feasible point is a Lean-checkable positivity certificate at that x.

## 5. Bottom line

- **Odds that any of the ten angles leads to RH:** below 0.5%.
- **Odds that KS-PSHR is feasible for zeta at x = 3.02:** about 30–40%. The SDP has many free parameters, and the proportional (scalar-gluing) version fails only by about 0.056.
- **Odds that it stays feasible for zeta_K through x ≈ 20 while failing for E:** about 10–15%.
- **Odds that this then becomes a provable all-x statement:** below 2%.
- **Odds that Lane A is kernel-certified within weeks:** about 60–70%.

What the project gets for certain is a certified map of which inputs cannot work: linear formulas, asymptotics, zero readouts, lossy local splittings, sign conditions, local purity, and family averaging. There is also one new split of E's failure: missing multiplicativity accounts for about 8 of the ≈28 units, and the rest is impurity together with the functional equation.

The positive half of a Hodge index theorem for Spec Z would be an exact identity whose terms are Euler-local and whose sum is the functional equation. Lane B is the one finite question left that probes whether such an identity can exist at finite scale.

The web-search budget ran out in wave 2, so every citation except those the proposers marked verified (GORZ PNAS 2019, Farmer arXiv:2008.07206, Suzuki arXiv:2301.05779) is from memory. The prime-power projection script is at `/private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hodge2/synth/pp.py` (bisection in `pp2.py`).