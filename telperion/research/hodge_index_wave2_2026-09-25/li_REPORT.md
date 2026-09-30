# Hodge index WAVE2: angle `li`

conjecture1_proved = False. Mechanism alive: True. Survived adversarial review: False.

# ANGLE li: Li's criterion as positivity at all scales

conjecture1_proved = False. Nothing here proves RH. Every number below was computed in this session. Scripts and data are in `/private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hodge2/li/`.

## 0. Summary

1. **Controls in Li coordinates**, computed from exact Taylor coefficients of log xi, not from zero sums:
   - **E first goes negative at n = 5713** (lambda_5712 = 118.615, lambda_5713 = -643.927).
   - **D first goes negative at n = 328997** (lambda_328996 = 1385.31, lambda_328997 = -2379.97).
   - zeta_K is positive for all n <= 14000.
   - Both indices are predicted exactly by the Voros single-zero formula: trend minus 2 Re w^n, with w from the leading off-line zero.
   - So the diagonal Li test is a pure zero-location detector with resolution about (2 beta - 1)/(2|rho|^2). Any proof of lambda_n >= 0 has to encode zero locations to that resolution.
2. **Schoenberg-Li strengthening (M2)**:
   - lambda_{-n} = lambda_n.
   - K(i,j) = lambda_i + lambda_j - lambda_{i-j} is the Weil form on the Bombieri-Lagarias Laguerre span.
   - So RH <=> lambda is conditionally negative definite on Z <=> lambda_n = integral of (1 - cos n theta) against a positive measure (Levy-Khintchine).
   - **Certified in arb**:
     - E becomes indefinite at N = 27. A second negative pair appears at N = 70, 71, matching E's second off-line zero at 0.93767 + 29.98340i.
     - D becomes indefinite at N = 149.
     - zeta_K is PSD through N = 158 and zeta through N = 144.
   - The Gram test catches E about 212x earlier than the diagonal test, and D about 2208x earlier.
3. **Euler-product mechanism M3 (Schur-Hadamard local-global)**:
   - This is the right shape: multiplicativity turns Schoenberg Toeplitz matrices into Hadamard products over places, and Schur's theorem would give PSD if every local block were conditionally negative definite.
   - The naive blocks are not: lambda^(p)_1 = -log p/(p-1) < 0.
   - The counterfeits fail at the factorization step: Lambda_E is supported on composite m from m = 6, and it breaks the local Ramanujan bound 2 log m from m = 84.
   - M3 reduces to Weil's problem. It is refuted in naive form and kept only as a structural target.

## 1. Setup and validation

- Definitions:
  - xi_zeta = (1/2) s(s-1) pi^{-s/2} Gamma(s/2) zeta(s).
  - xi_K = s(s-1) (sqrt20/2pi)^s Gamma(s) zeta(s) L(s, chi_-20).
  - xi_E: the same gamma factor, times E = (1/2)(zeta L_-20 + L_-4 L_5). This matches the lattice sum (x^2+5y^2)^{-s}/2 at s = 3.
  - xi_D = (5/pi)^{s/2} Gamma((s+1)/2) D(s).
  - All four satisfy xi(s) = xi(1-s). This was checked numerically to 1e-34.
- Li coefficients: log xi(1/(1-z)) = const + sum lambda_n z^n / n. The coefficients are extracted by the trapezoid rule on |z| = r, where r is below the innermost singularity |w|^{-1}.
- Two extractors:
  - float64 FFT with python-flint evaluations, for large n;
  - arbitrary-precision DFT (600 to 4200 bits, r = 0.5 / 0.45 / 0.8 / 0.85) for n <= 700.
- The principal-log part is unwrapped separately from the analytic log-Gamma part.
- Validation on zeta:
  - lambda_1 = 0.0230957089661210338143102479064952916219...
  - lambda_2 = 0.0923457352280466703857...
  - lambda_100 = 118.60377537679
  - lambda_1000 = 2326.05316
  - Independent radii agree to 5e-10 (float, n <= 1000) and to 1e-528 / 1e-1200 (high precision).

## 2. Diagonal Li: controls

| function | first negative lambda_n | leading off-line zero | log\|w\| | cross-check |
|---|---|---|---|---|
| E | **5713** | 0.932969697485 + 15.668249531278 i | 1.76053e-3 | r = 0.998 / 0.997 agree to 2e-5 |
| D | **328997** | 0.808517182457 + 85.699348485378 i | 4.20053e-5 | r = 1-5.5e-5 / 1-5e-5 (M = 2^22) agree to 7.6e-3 |
| zeta_K | none for n <= 14000 | none | none | matches trend |
| zeta | none for n <= 1500 | none | none | matches Keiper/Voros |

Model check. The model is lambda_n ~ T(n) - 2 Re w^n, with T(n) = (n/2)[d(log n + gamma - 1 - log 2pi) + log q].
- It gives 5713 for E and 328997 for D. The D prediction moves only to 328995-328999 under a +/- sqrt(n) log n perturbation.
- Residual rms for E: 4 at n ~ 1e3, 15 at 5e3, 1121 at 1.4e4. The growth comes from E's other off-line zeros.
- Residual rms for D: 3.5 at 1e3, 108 at 1e5, 5958 at 2e5.

Lesson: the diagonal Li sequence is blind to E until n ~ 5700, although E already fails Weil positivity at log x ~ 3. Li rungs are an extremely late detector.

## 3. M2: Schoenberg / Gram-Li

- **Identity (proved):** pairing rho with 1-rho gives lambda_{-n} = lambda_n. Hence K(i,j) = sum_rho (1 - w^i)(1 - w^{-j}) = Weil form on span{g_i}. This is the polarization of 2 lambda_n = W(g_n * g_n~).
- **RH case:** all |w| = 1, so lambda_n = sum_rho (1 - cos n theta_rho). That makes lambda a conditionally negative definite function on Z, and every e^{-t lambda} is positive definite. It is also a 1-cocycle norm, ||(U^n - 1) v||^2 / 2, with U = the Cayley transform of a Hilbert-Polya operator. That last form is Hilbert-Polya repackaged and adds nothing.
- **Certified inertia.** LDL^T was done in arb at 2200-4500 bits. The input balls were inflated by twice the discrepancy between the two radii.
  - E: negative pivots at N = 27, 28 (d_27 = -6.326e-63 +/- 1.7e-67) and at 70, 71. That gives 4 negative eigenvalues by N = 80, which is 2 off-line quartets, matching Bombieri 2000's count.
  - D: pivots positive through 148, then d_149 = -7.597e-569 and d_150 = -4.374e-572.
  - zeta: positive definite through N = 144.
  - zeta_K: positive definite through N = 158.
  - Precision limits the depth, not the sign: pivots decay like 10^{-2.3 j} to 10^{-3.1 j}, so precision needs to be about twice the pivot's digit count.
- **Scaling:** E's two detections sit at gamma = 15.67 and 29.98, at N = 27 and 70. At fixed beta ~ 0.93 that fits N ~ gamma^1.47. D at N = 149 is lower than that law predicts (about 330). The likely reasons are a smaller beta and a sparser degree-1 zero density; this is not proven.
- **Float64 detection:** E only shows up near N ~ 410. D shows nothing up to N = 12000 (noise ~ 1e-7). This is the same near-null saturation as the window forms, and high precision is mandatory.

## 4. M3: Schur-Hadamard local-global (the Euler-product mechanism)

- **Claim shape.** On the Euler disc |z - 1/2| < 1/2, log xi(1/(1-z)) = arch + sum_m (Lambda(m)/log m) m^{-1/(1-z)}. The identity m^{-s(z)} = m^{-1} sum_n L_n^{(-1)}(log m) z^n gives the local terms lambda^(m)_n = -Lambda(m)/m * L^{(1)}_{n-1}(log m). Then e^{-t lambda} = product over places of e^{-t lambda^(v)}, so T_t = T_t^inf o (Hadamard product over p of T_t^(p)). If every block (or a regrouping of blocks) were conditionally negative definite, Schur's theorem would give RH.
- **Where the Euler product enters:** exactly in the Hadamard factorization over primes. A sum of Euler products such as E, or D, has no such factorization.
- **Counterfeit failure (computed):**
  - Lambda_E is nonzero at composite m = 6, 14, 21, 36, ...
  - max |Lambda_E|/log m is 4 (m = 84), 20 (756), 80 (8694) and 552 (95256).
  - For D the same ratio grows from 1.34 to 30.6 by m = 1e5.
  - The mechanism gives no x-location for the failure.
- **Refutation of the naive form:** lambda^(p)_1 = -log p/(p-1) < 0, so the diagonal of K^(p) is negative. Only the pole mass, spread as the prime number theorem measure, can offset it. At that point the block condition is the arithmetic side of Weil's explicit formula, so it is circular.

## 5. Literature

- Li 1997.
- Bombieri-Lagarias 1999 (formula (1.3) and the arithmetic formula, as quoted in Suzuki 2023, arXiv 2301.05779, which was read).
- Bombieri 2000 (negative-eigenvalue count).
- Voros 2006/2016/2022 and erratum arXiv 1403.4558.
- Lagarias 2007.
- Brown 2005.
- Palojarvi 2020.
- Ernvall-Hytonen et al., arXiv 1410.4384 (numerics only on shifts of zeta).
- Suzuki 2023 (Li coefficients as norms in a model space, under RH).

Not found:
- the conditional-negative-definite / Schoenberg phrasing;
- first-negative indices for Epstein E or Davenport-Heilbronn D;
- certified Gram-Li thresholds.

Novelty is UNVERIFIED because the web-search budget ran out. A likely prior-art risk is Bucur, Ernvall-Hytonen, Odzak, Smajlovic 2016 (LMS J. Comput. Math. 19), who studied Li numerics for RH-violating series; I could not read it.

## 6. Recommendations

1. Add Gram-Li rungs next to the kernel-checked Li ladder. They are finite, certified by arb LDL^T, and about 200-2000x more sensitive than diagonal rungs. Open issue: a theorem that turns "K_N PSD" into an explicit zero-free region; the dependence on neighbouring zeros makes that non-trivial.
2. Register E (5713 / 27) and D (328997 / 149) as Li-coordinate negative controls.
3. Do not pursue diagonal lambda_n >= 0 as a mechanism.
4. M3 is worth keeping only as a target: find a regrouping of places whose blocks are individually conditionally negative definite, with E's composite-support defect as the kill test.

## Files

- Engines: `eng.py`, `li.py`, `hp.py`, `ldl.py`, `ldl3.py`, `lam_mang.py`
- Data: `lam_E_a.npy`, `lam_D_big1.npy`, `lam_D_big2.npy`, `lam_K_a.npy`, `hp4k_*.pkl`
- All in `/private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hodge2/li/`
- No background processes are left running.


## Adversarial verdict

```json
{
 "angle": "li -- adversarial skeptic of Li / Schoenberg-Li / Schur-Hadamard local-global",
 "survives": false,
 "fatal_flaws": [
  "M1 (lambda_n >= 0) and M2 (K_N PSD for all N, i.e. lambda conditionally negative definite on Z, i.e. a Levy-Khintchine form with a positive zero measure) are each equivalent to RH, so they are criteria and explain nothing. As a proof strategy M2 is circular: K(i,j) = W(g_i * g_j~) is the Weil functional restricted to the Bombieri-Lagarias Laguerre span, and 'all K_N PSD' is Weil positivity on that span. The Schoenberg/Levy rewording adds no input. The proposer says as much for M1 but still presents M2 as a 'strengthening'. It is not stronger than RH. It is a finer finite detector of the same condition.",
  "M3 is not merely 'refuted in naive form'; it is ill-defined. Li coefficients are Taylor coefficients at z=0, which is s=1, the pole. The Euler-product expansion log xi = arch + sum_m Lambda(m)/log m * m^{-s} converges only for Re s > 1, i.e. |z-1/2| < 1/2, and z=0 lies on the boundary of that disc. So the termwise local coefficients lambda^(p)_n exist, but their sum over p diverges: lambda^(p)_1 = -log p/(p-1) and sum_p log p/(p-1) = +infinity. The 'Hadamard product over places' of T_t^(p) = [e^{-t lambda^(p)_{i-j}}] therefore does not converge. It can only be defined with the pole term (and the prime number theorem) as a counterterm, and that regularised object is exactly the Bombieri-Lagarias arithmetic formula, i.e. the explicit formula. The pole has to be spread against the primes before any block can be conditionally negative definite, and that is Weil's problem. The circularity is structural, not an artefact of a bad regrouping.",
  "Schur-product obstruction is sharp. A conditionally negative definite psi on Z with psi(0)=0 must have Re psi(n) >= 0. Every finite prime block has psi(1) < 0, so no finite set of primes forms a conditionally negative definite block. Any admissible block must contain the pole plus infinitely many primes. The '~1%' odds for a good regrouping are not supported.",
  "The counterfeit control is vacuous as a mechanism test. Any RH-equivalent criterion fails for E and D because they have off-line zeros. M3's claimed failure point, that Lambda_E has composite support and breaks the Ramanujan bound at m=84, just restates that E has no Euler product. It does not show which step of a positivity argument breaks, and it predicts no x.",
  "Mismatch with the stated target. The Laguerre test functions g_n are not compactly supported, so Gram-Li PSD at level N is not W(x) for any window x. The mechanism gives no prediction of x_E ~ 19.82 or x_D ~ 31, and nobody has turned N into x. It does not address 'positivity at all scales' in the sense of the task."
 ],
 "linearity_or_classP_violation": "The Euler product enters M1/M2 only through the log in lambda_n, and it enters only as a detector: E and D fail because they have off-line zeros, not because any step of an argument uses multiplicativity. Neither M1 nor M2 has a proof step at all, so the fooling lemma is not engaged; there is nothing to fool. M3 is the only candidate where multiplicativity is used nonlinearly, through the Hadamard factorisation over primes. But that factorisation diverges at the Li base point s=1. Making it converge requires the pole counterterm, which puts back the linear explicit formula (a linear object that D satisfies). So the nonlinear step cannot be carried out without collapsing into the Weil functional. No linearity-barrier violation is exhibited: the proposal neither passes the barrier nor gives a counterexample to it.",
 "counterfeit_check": "Reproduced with my own code in /private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/hodge2/li_skeptic/ (sk.py, lam.py, gram.py, vor.py). These are independent mpmath evaluations of zeta, L_-20, L_-4 and L_5, Cauchy extraction at 140 digits on two circles (r=0.5 with M=520, r=0.45 with M=480), agreeing to 1e-107 for n <= 90.\n- E Gram: negative pivots at N=27 and 28 on both radii. d_27 = -6.3262e-63, which matches the claimed value exactly.\n- zeta_K Gram: no negative pivot through N=40 (d_27 = +2.383e-63, d_40 = +6.26e-103).\n- E's zero 0.932969697485414 + 15.668249531278i is confirmed by findroot (|E| ~ 4e-30).\n- Voros single-zero model (trend minus 2 Re w^n): gives first-negative n = 5713 for E and 328997 for D (D using the stated zero). The proposer's stored E/D/K arrays agree with that and with each other: two E runs agree to 4e-4, two D runs to 2e-3 at n ~ 329k, and K min = 0.342.\nCaveat found: zeta's own Gram pivots decay much faster (d_27 ~ 3.6e-91, about 10^{-3.4} per step). At 140 digits my run showed spurious 'negative' zeta pivots at N = 35/36 or 36/37, and the location moved with the radius. That is noise, and it shows the zeta side needs real ball arithmetic. The proposer's arb-certified 'zeta PSD through 144' could not be re-checked at that depth here. There is no x-location to compare with 19.82 or 31, because the mechanism predicts none.",
 "numerics_reproduced": "Yes, independently, at the depth checked.\n- zeta: lambda_1 = 0.0230957089661210338143102479065 and lambda_2 = 0.0923457352280467, both match.\n- zeta_K: lambda_1 = 0.342474624606957.\n- E: lambda_1 = 0.583080537136759.\n- E Gram indefinite at N=27 (d_27 = -6.3262e-63), zeta_K PSD through 40, Voros indices 5713 (E) and 328997 (D). Stored arrays are consistent.\n- Not reproduced: the certified D Gram threshold N=149 (needs ~600+ digits) and zeta/zeta_K PSD beyond N=40.",
 "novelty": "Low as mathematics.\n- Known: Li 1997; Bombieri-Lagarias 1999 (J. Number Theory 77), which covers Li's criterion for general multisets, 2 lambda_n = W(g_n*g_n~) and the arithmetic formula; Bombieri 2000 (Rend. Mat. Acc. Lincei s.9 v.11), which gives the negative-index count of the Weil form; Lagarias 2007 (Ann. Inst. Fourier 57); Voros's single-zero asymptotics.\n- The 'CND / Schoenberg / Levy-Khintchine' phrasing is a one-line reformulation of the polarised BL identity. I would not claim novelty for it even if it is unprinted.\n- Possibly new, as numerics only: the specific counterfeit indices (E: 5713 / Gram 27; D: 328997 / Gram 149).\n- Prior-art risk not cleared: Bucur, Ernvall-Hytonen, Odzak, Smajlovic, LMS J. Comput. Math. 19 (2016), on Li-type criteria for Dirichlet series with real coefficients. My web-search budget was exhausted (0 searches available), so I could not verify whether it treats Epstein or Davenport-Heilbronn. Flagged UNVERIFIED.",
 "what_is_real": "1. A verified numerical dictionary between Li coordinates and the counterfeits:\n   - diagonal Li first goes negative at E: 5713 and D: 328997, both predicted by Voros from the leading off-line zero;\n   - Gram-Li goes indefinite at E: N=27 (second pair at 70/71) and D: N=149;\n   - zeta_K, with the same gamma factor and conductor as E, stays PSD past E's threshold.\n2. The practical lesson: Gram-Li detects off-line zeros about 200x (E) to 2000x (D) earlier than diagonal Li. Diagonal Li rungs are a very late detector (E is invisible until n ~ 5700 even though it fails Weil at log x ~ 3).\n3. Near-null saturation also shows up in Li-Gram coordinates, and more strongly for zeta than for zeta_K/E: pivots fall about 10^{-3.4} per step versus 10^{-2.3}. Certification therefore needs ball arithmetic and precision roughly 2x the pivot digit count, since plain high-precision runs produce spurious negatives.\n4. The structural negative result on M3 is worth recording. Local Li blocks cannot be conditionally negative definite, because psi(1) < 0 for every finite prime set, and the product over places diverges at s=1. The Li base point at the pole is exactly where the Euler product is unusable, so Li coordinates are a poor frame for any Euler-product positivity mechanism.\nNone of this is a mechanism for Weil positivity.",
 "next_step_if_survives": "Does not survive as a mechanism. The most useful single step: register E (Gram 27, diagonal 5713) and D (Gram 149, diagonal 328997) as arb-certified Li-coordinate negative controls, and then answer the one open question that would connect this angle to the target. Is there an explicit map N -> x (for example via the support or decay of the Laguerre g_n, or by projecting the g_n onto window-supported functions) such that 'K_N PSD' implies or is implied by W(x)? A cheap falsifiable test: compute the Weil window form on the span of g_1..g_N truncated to [-(1/2)log x, (1/2)log x], and check whether E's Gram threshold N=27 corresponds to x ~ 19.8. If there is no such correspondence, Gram-Li stays a zero detector unrelated to 'positivity at all scales'."
}
```
