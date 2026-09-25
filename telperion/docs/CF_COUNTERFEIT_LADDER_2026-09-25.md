# Lane A (CF): the counterfeit ladder, zeta_K against the Epstein counterfeit E

2026-09-24. Worktree `arda-cf`, branch `cl/counterfeit-ladder`, island `telperion/examples/rvm_bridge/lean`
(Lean v4.33.0-rc2). Git was used read-only; nothing is committed.

`conjecture1_proved = False`. Everything below is barrier and calibration work. It is one window and one
test function. It is not a positivity mechanism and not a step toward RH.

## Status tags

| tag | meaning |
|---|---|
| KERNEL | Lean theorem, axioms `[propext, Classical.choice, Quot.sound]`, printed in `CF_AxiomGuard.lean` |
| NUMERIC-30 | mpmath at 30 digits, not interval-certified |
| FLOAT | numpy float64, validated against the 30-digit model |

## Normalization (the skeptic's correction, adopted)

`E(s) = (1/2) sum' (x^2+5y^2)^{-s} = (zeta_K + L(chi_-4) L(chi_5))/2`, with `a(1) = 1`.

- In Lean, `aE n` is defined directly by the lattice count, as half of `#{(x,y) in Z^2 : x^2+5y^2 = n}`.
- `aE_eq_half_sum` (KERNEL) checks `2 aE = aK + aG` for `n <= 27`.
- `zeta_K` has weights `c_K(n) = Lambda(n)(1 + chi_-20(n))`. KERNEL: `cK_conv` is the log-derivative identity with `aK = 1 * chi_-20` for `n <= 27`, and `cK_support` says these weights are supported on prime powers.
- For `n <= 27`, every `c_E(n)` is a rational multiple of `log n`:
  - `c_E(4) = 2 log 2`, `c_E(5) = log 5`, `c_E(6) = 2 log 6`, `c_E(9) = 6 log 3`;
  - `c_E(14) = 2 log 14`, `c_E(16) = 2 log 2`, `c_E(21) = 4 log 21`, `c_E(25) = log 5`;
  - all other `c_E(n)` for `n <= 27` are 0.
  - KERNEL: `cE_conv` is the defining identity, and `eq_cE_of_conv` says any `w` satisfying it on `[1,27]` equals `cE` there.

## A1. Numerics

All scripts are copied to `telperion/research/counterfeit_ladder_CF/`. They are new code and share nothing with the geometry angle's `ep_*.py`.
- The arch side is computed in its spatial form: `int_0^{2A} [2e^{-2y}g(0)/y - g(y)/sinh(y/2)] dy + 2 g(0) E1(4A)`.
- This is a different route from the Lorentzian and FWindow closed forms. It was checked against frequency quadrature to about 1e-11.

### x = 28, nine Dirichlet cosines (m = 0..8), E's least eigenvector (NUMERIC-30)

- `Q_E(v)/||v||^2 = -0.1651016`
- `Q_zetaK(v)/||v||^2 = +4.9596347`

This reproduces the prior claim (-0.165 / +4.96), with `||v||^2 = int v^2`. On the nine-mode span, zeta_K's least eigenvalue is only `+1.0e-4`. Positivity for the whole family therefore cannot be certified with crude bounds, so the certificate is stated at the test.

### Zero side (NUMERIC-30 zeros; tail beyond T = 150 estimated from the zero density)

| | arithmetic side | zero side |
|---|---|---|
| E, x = 28 test | -0.4507121 | -0.4506750 |
| zeta_K, x = 28 test | 13.539343 | 13.539380 |
| E, Lean test | -0.4569936 | -0.4569615 |
| zeta_K, Lean test | 13.415059 | 13.415076 |

- The residual of about 4e-5 is at the level of the crude tail model (the tail itself is 5.7e-4).
- E's on-line zeros contribute +1.32; the off-line quadruples contribute -1.77.
- The first quadruple, at `0.93297 + 15.66825 i`, alone contributes -1.825 (confirming the prior -1.825).

### E's zeros to T = 150 (computed independently)

- 128 on-line zeros (sign changes of the Hardy function) and 24 off-line pairs.
- The argument principle on the boxes `[-2,3] x [10k, 10k+10]` counts 176 = 128 + 2·24, and every box matches.
- No zeros with Re > 1 were found below 150.

### zeta_K's zeros to T = 150

- 52 zeta zeros (mpmath) and 124 zeros of `L(chi_-20)`.
- The argument principle agrees on every box, and there are no off-line zeros.

### E's positivity threshold x_E (FLOAT; `thresh_cf.out`, `thresh2_cf.out`)

Setup:
- Both parity sectors were computed.
- Two Galerkin bases were used: Dirichlet (`v(±A) = 0`) and Neumann cosines/sines.
- The Neumann basis converges much faster, because the minimizer does not vanish at `±A`.

Findings:
- The odd sector is far from critical (+0.15 at x = 20). The threshold is set by the even sector.
- Even-sector Neumann basis, `M = 40, 60, 80, 100, 120`:

| x | lambda_min for M = 40, 60, 80, 100, 120 | extrapolated |
|---|---|---|
| 19.8 | +7.9e-5, +5.7e-5, +4.8e-5, +4.3e-5 (tail of the sequence) | about +3e-5 (Aitken and power-law) |
| 19.9 | +1.0e-5, -4.8e-5, -6.6e-5, -7.5e-5, -7.9e-5 | |
| 20.0 | -1.0e-4 to -1.8e-4 | |

- A negative Galerkin value is an upper bound on the true infimum. So E's window form is indefinite at x = 19.9. The value is stable to 1e-11 when the quadrature is doubled.
- **Bracket: 19.8 <~ x_E <= 19.9.**
  - The upper end is a Galerkin witness (FLOAT, not interval-certified).
  - The lower end rests only on extrapolation in M, so it is **not converged/certified**.
- The earlier claim "lambda_min(19) = +0.0024" was an unconverged value. The Neumann values at x = 19 converge to about +0.0021, so E is positive there.

## A2. The kernel certificate (KERNEL, `CF_Cert.lean`)

### Instance

- Window: `A = 9 pi/17`, so `x = e^{18 pi/17} = 27.84`, and the prime side runs over `n <= 27`.
- Modes: nine Dirichlet cosines with `k_i = (2i+1) 17/18`.
- Coefficients: `c = (-33, -2, -37, 23, -30, 12, -37, 100, -25)/100`. This is E's eigenvector at this window, rounded.
- Computed values:
  - `Q_E = -0.17142 ||v||^2`
  - `Q_zetaK = +5.03202 ||v||^2`

### The functional (`CF_Arch.lean`)

`weilFormGC w g = archSideGC g - primeSideD w g`.

`archSideGC` consists of:
- the registry's two pole terms `H_g(0) + H_g(1)`;
- `g(0) log(20/pi^2)`;
- `(1/2pi) int h_g(r) [Re psi(1/4+ir/2) + Re psi(3/4+ir/2)] dr`.

This is the `Gamma_R(s) Gamma_R(s+1) = Gamma_C(s)` factor with conductor 20. zeta_K and E share this arch side exactly; they differ only in `w`.

### Theorems

1. `zetaK_window_pos`: `Re weilFormGC cK (v*v~) >= 3 ||v||^2`. This is item (i), at the test.
2. `epstein_window_negative (w) (hw)`: for any `w` with E's defining identity on `[1,27]`, `Re weilFormGC w (v*v~) <= -(3/20) ||v||^2`. This is item (ii).
   - `hw` is discharged by `cE_conv`, the same pattern as Crux3's `cD_conv`.
   - `window_separation_cE` records that the hypothesis is non-vacuous.
3. `window_separation`: both statements on the same nonzero test. This is item (iii).
4. Negative controls, item (iv):
   - `tabM_tamper`: a log enclosure shifted by 1e-6 is rejected.
   - `certE_tamper`: the same rational E certificate evaluated with zeta_K's weights returns `false`.
   - `certK_tamper`: the zeta_K certificate evaluated with E's weights returns `false`.

### Rigorous losses in the certificate

- `gamma >= H_100 - log 101 = 0.57226`.
- Digamma tails are bounded at N = 300.
- The r² moment uses R = 33.
- `e^{-4bA}` is kept exactly only for j = 0.
- On the zeta_K side, `cosh >= 1` and `e <= 1`.
- The final margins are `-0.023` (E) and `+1.78` (K) in absolute units, with `||v||^2 = 2.666`.

### Supporting files

| file | content |
|---|---|
| `CF_Test.lean` | M-mode Dirichlet test, generic: FreqData with the decay bound for all k > 0 (the lowest mode has k < 1), the autocorrelation blocks, the Lorentzian terms in square form, the pole integral |
| `CF_Arch.lean` | two-sided truncations of the vertical-line digamma series for any 0 < a < 1, the arch identity with exact pole terms, the upper and lower Lorentzian bounds, the M-mode r² moment |
| `CF_EData.lean` | lattice counts (`decide +kernel`), `cE_conv`, `cK_conv`, `chi20 = chi4 chi5` |
| `CF_Num.lean` | the collapse identity `blk_sum_eq`, the M-mode prime checker `mEntry_sound`, exp enclosures, rounded sums |

Build: `lake build CF_AxiomGuard` is green (8788 jobs, 0 warnings in the CF files). The guard prints 54 lines:
- 53 depend only on `[propext, Classical.choice, Quot.sound]`;
- `chi20_eq_mul` depends on no axioms.

There is no `sorry`, no `native_decide` and no `ofReduceBool`. The CF files do not modify `AxiomGuardRvMBridge.lean`. `lakefile.toml` only has `[[lean_lib]]` blocks appended.

## A3. Lemma-O witnesses (KERNEL, `CF_EData.lean` and `CF_LemmaO.lean`)

Verified:
- `cD_six`: `c_D(6) = (1 + kappa^2) log 6`. The synthesis' formula is correct.
- `cD_six_ne_zero`.
- `dh_orbit_six`: any `w` with D's identity on `[1,56]` has `w 6 = (1+kappa^2) log 6 != 0`.
- `cE_six`: `c_E(6) = 2 log 6 = 3.5835`; `epstein_orbit_six`; `vonMangoldt_six`: `Lambda(6) = 0`; `not_isPrimePow_six`.
- The other side of Lemma O: `aE_not_mult` (`aE 6 = 2 != 0 = aE 2 * aE 3`) and `aD_not_mult`. By contrast, `aK_mult_six` holds and `cK_support` holds for all `n`.

## Remaining obligations (stated precisely, not done)

1. **Lemma O in full.** For `a : ArithmeticFunction R` with `a 1 = 1` and `c` defined by `pmul log a = c * a`: `a` is multiplicative iff `c n != 0 -> IsPrimePow n`. Only finite witnesses are proved.
2. **Explicit formula link.** `Re weilFormGC w (v*v~) = sum_rho H_{v*v~}(rho)` for E and zeta_K with Lipschitz tests. This is classical and not formalized; it is checked numerically above to about 4e-5.
3. **zeta_K positivity on the whole nine-mode family.** The span's least eigenvalue is about 1e-4, so this needs a sharp arch treatment (LDL^T) rather than the crude bounds used here. Only the at-the-test statement is proved.
4. **Interval-certified x_E.** Use Arb or iv for a Galerkin upper witness at 19.9, and a certified lower bound. A certified lower bound needs a completeness/tail argument and is not attempted.

## Proposed registry nodes (NOT registered)

Proposed nodes (anchors `CF.window_separation`, `CF.epstein_window_negative`, `CF.dh_orbit_six`, `CF.epstein_orbit_six`) go only through `mission add` and the #607 provenance flow. This lane's review is self-attested.
