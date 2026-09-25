# Lane B: independent skeptic verdict (peer session peterwmurphy-95, 2026-09-25)

Recorded as a different session under the same git identity, so "unverified" under #607. The skeptic used its own code and imported nothing from lane B.

## (a) and (b): CONFIRMED. The certificate is conservative, not wrong.

**Explicit formula for zeta_K, derived independently by contour shift**
- Completed function: Lambda_K = 20^{s/2} Gamma_R(s) Gamma_R(s+1) zeta_K.
- Archimedean side: (1/2pi) int H(r) [log(20/pi^2) + Re psi(1/4 + ir/2) + Re psi(3/4 + ir/2)] dr, plus the pole terms h(+-i/2) and the Lambda_K(n) weights.
- Cross-checked against the two-sided zero sum (21 zeta zeros + 58 L(chi_-20) zeros up to height 80; root number 1 to 1e-26). Agreement is 1e-13.

**zeta_K, even sector, Rayleigh-Ritz**
| x | N = 128 | limit (about) | lane B floor |
|---|---|---|---|
| 20 | 4.5434e-3 | 4.532e-3 | 3.443e-3 |
| 22 | 1.6695e-3 | 1.6646e-3 | 1.300e-3 |
- The head values match lane B to all 9 digits, which confirms the Crux3 closed forms from an independent u-space derivation.

**zeta_K, odd sector:** 0.588 at x = 20 and 0.334 at x = 22 (lane B: 0.587 / 0.334).

**Schur replication**
- S_min = -15.5006; min S on [76, 800] = 0.989; leakage 1.09776e-3; d = 0.432490. All reproduce exactly.
- With EXACT coupling columns up to N3 = 65536, the lower bounds are 3.802e-3 (x = 20) and 1.334e-3 (x = 22).
- So lane B's far-tail bound costs about 3e-4, against a true tail of about 2e-5. It errs in the safe direction. (This check is float64, not interval arithmetic.)

**E**
- Lattice counts equal the genus formula for n <= 400. The functional equation holds to 12 digits, and b(n) = -E'/E to 15 digits.
- lambda_min(E): +3.5e-6 at x = 19.82; -9.07e-5 at 19.9; -1.90e-4 at 20; -5.47e-4 at 22.
- Threshold: 19.8228 at N = 1024; the limit is about 19.8225. "Converged over N = 64..256" is slightly overstated, since it still moves by 3e-3 at N = 256. This is immaterial.

## (c) Paper-level steps

- **The Loewner off-diagonal identity is a THEOREM, and an elementary one.**
  - For Neumann cosines, h_in(t) = (-1)^{i+n} [k_n sin(k_n t) - k_i sin(k_i t)] / (k_i^2 - k_n^2).
  - So every translation-invariant term (the arch term via 1/sinh(t/2), the comb via point evaluation) is a divided difference of ONE function:
    - Ytil(k) = J(k) + 2 sum c_p sin(k y_p),
    - J(k) = pi tanh(pi k) - 2 Im sum_j e^{-(2j+1)A} e^{2ikA} / (j + 1/2 - ik).
  - No Fourier hypothesis is needed. Lane B's J(k) = -Im I(k) is the same beta-family sum.
  - This proof belongs in LOEWNER_DERIVATION.txt as a proof, not as a numerical check.
- **Neumann convergence:** assumed. It is routine (K_n ~ 1/k_n, r_n in l^2).
- **The one genuine paper-level point to cite:** the explicit formula is applied to h = f * f~, where f has jumps at +-A, so h is only Lipschitz. This is covered by Barner-type conditions. Step 2 (Lean) must either prove the explicit formula for this class or use smooth tests.

## NOT checked by the peer

- The mpmath.iv digamma/trigamma remainders and the LDL pivots.
- The algebra of the far bound for n >= N3.
- The internals of the odd-sector certificate.
- E in interval arithmetic.
