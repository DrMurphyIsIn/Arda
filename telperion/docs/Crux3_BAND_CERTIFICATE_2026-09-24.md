# Crux lane 3: a height-local band certificate that Davenport-Heilbronn fails

*Crux lane 3 of the RH crux program, 2026-09-24, worktree `arda-crux3`, branch `cl/crux3`, on the
`rvm_bridge` island (Lean v4.33.0-rc2). This follows up section 4.3 of `RH_CRUX_ROUND2_2026-09-23.md`,
"the first zero-free window certificate that fails for D".*

*`conjecture1_proved = False`. The Riemann Hypothesis is open. Nothing here proves it, reduces it, or
gives a zero-free region. The kernel theorem below is a positivity statement on a two-dimensional
space of test functions at one window.*

---

## 1. The short version

Round 2 found that every window certificate built so far is blind to the Euler product. The
Davenport-Heilbronn function D, which satisfies a functional equation but has zeros off the line,
passes all of them, often by wider margins than zeta. Round 2 proposed a height-local lever:
restrict the Weil form to a band of frequencies near one height r and compare the twisted prime comb
with the archimedean density there.

This lane asked whether that lever separates zeta from D at a scale we can actually certify. It does.

- **The separation (part a).** Take the window `A = 9π/14` (so `x = e^{2A} = e^{9π/7} ≈ 56.78`) and the
  two continuous test functions `cos(763u/9)` and `cos(259u/3)`, cut off at `±A`. Their spectra sit at
  heights 83.2 to 87.9, centred at `r ≈ 85.6`. On their span, zeta's Weil form is at least
  `0.699 ||v||²`, while D's is `-0.655 ||v||²` at `c = (-3, 2)`. Both numbers come from the
  explicit formula, with no zeros used, and both agree with the zero sides: zeta to `5e-9`, D to `2e-5`.
- **The kernel theorem (part b).** `Crux3.band_floor`, on the island's registry vocabulary
  (`WeilForm.weilForm = archSide - primeSide`), is hypothesis-free. Its axioms are
  `[propext, Classical.choice, Quot.sound]`:

  ```lean
  theorem band_floor (c1 c2 : ℝ) :
      (1 / 2 : ℝ) * (∫ x, ‖((bandTest c1 c2 x : ℝ) : ℂ)‖ ^ 2)
        ≤ (WeilForm.weilForm (WeilForm.autocorr (fun u => ((bandTest c1 c2 u : ℝ) : ℂ)))).re
  ```

  Here `bandTest c1 c2 u = c1 cos(763u/9) + c2 cos(259u/3)` for `|u| ≤ 9π/14`, and `0` outside.
  The same certificate appears in round 2's literal form as two further kernel theorems:
  - `band_comb_le`: the band comb constant satisfies `Re primeSide ≤ 1.92 ‖v‖²`;
  - `band_arch_ge`: the band archimedean floor satisfies `Re archSide ≥ 2.49 ‖v‖²`.
- **D's failure (also kernel-checked).** D's own explicit-formula functional takes the value
  `-0.6545762050 ± 3e-11` times `||v||²` at `c = (-3, 2)` (Arb, `arb_cert.py`). The kernel theorem
  `Crux3.dh_band_negative` (module `Crux3_BandDH`, axioms `[propext, Classical.choice, Quot.sound]`)
  proves it is at most `-(1/2) ||v||²`:

  ```lean
  theorem dh_band_negative (w : ℕ → ℝ)
      (hw : ∀ n : ℕ, 1 ≤ n → n ≤ 56 → aD n * Real.log n = ∑ d ∈ n.divisors, w d * aD (n / d)) :
      (weilFormD w (WeilForm.autocorr (fun u => ((bandTest (-3) 2 u : ℝ) : ℂ)))).re
        ≤ -(1 / 2 : ℝ) * ∫ x, ‖((bandTest (-3) 2 x : ℝ) : ℂ)‖ ^ 2
  ```

  `weilFormD w = archSideD - primeSideD w` is D's explicit-formula functional: gamma factor
  `Γ_R(s+1)`, conductor 5, no pole. It is defined off-registry (section 4.4). The only hypothesis, `hw`,
  is the defining identity of the coefficients of `-D'/D` (`-D' = D · (-D'/D)` read coefficientwise),
  so the theorem applies to D's true weights. `Crux3.band_separation` puts both sides on the same
  nonzero test in one statement, and `band_separation_cD` instantiates it at the closed-form weights
  `cD`, which satisfy the identity (`cD_conv`), so the hypothesis is not vacuous. D's zero side accounts for the value: the off-line quadruple
  `0.8085 ± 85.699i` contributes `-1.046`, and all the on-line zeros together contribute `+0.390`.
- **The round-2 target itself (part c, a partial no-go).** At `x = 40`, the window round 2 named, no
  height-local band detects D's off-line zero. Every band of up to 16 modes near 85.7 leaves D's form
  positive, with least eigenvalue at least `+0.095`. D's negative direction at `x = 40` is spread across
  all frequencies. It is visible to the full window from `x ≈ 31`, but only to height-local bands from
  `x ≈ 42`. So round 2's specific target, `κ_ζ(40) = 0` beside `κ_D(40) ≥ 2`, cannot be reached
  height-locally. The first height-local separation appears at `x ≈ 42`, and a robust one (margins
  over 0.6, two modes) at `x ≈ 57`.

## 2. Setting and conventions

Tests `f` are supported in `[-A, A]`; `F(t) = ∫ f(u) e^{itu} du`; the window is `x = e^{2A}`, so
only `n < x` enter the prime side. The Weil form is

  `Q(f) = Pole(f) + (1/2π) ∫ |F(t)|² Ω(t) dt − Σ_{n<x} (w(n)/√n) (g(log n) + g(−log n))`,

where `g = f ⋆ f̃`. For zeta, `w = Λ`, `Ω_ζ(t) = Re ψ(1/4 + it/2) − log π`, and the pole term is
`F(i/2)F(−i/2) + c.c.`. For D, `w = c_D` (the Dirichlet coefficients of `−D'/D`), `Ω_D(t) = Re ψ(3/4 + it/2) + log(5/π)`, and there is no pole.

D has conductor 5 and gamma factor `Γ((s+1)/2)`. Its weights `c_D(n)` are signed and are not supported on
prime powers: for example `c_D(2) = κ log 2 = 0.197` (zeta: 0.693), `c_D(4) = −(2 + κ²) log 2 = −1.442`
(zeta: 0.693) and `c_D(6) = (1 + κ²) log 6 = 1.936` (zeta: 0), with `κ = 0.2841`. The
explicit formula for D follows from its functional equation `Λ_D(s) = Λ_D(1 − s)` in the same way as
for zeta. It was checked here against D's zeros, computed to height 300 with the argument-principle
count matching at every checkpoint up to 200, and it reproduces round 2's κ-certify values exactly:
`−2.5877383e−4` and `−1.0854653e−3` at `x = 40`, `N = 60`.

## 3. Part (a): numerics

All numerics are single-process mpmath/numpy/python-flint. The scripts are in
`telperion/research/Crux3_band_certificate/`.

### 3.1 The instance

| quantity | zeta | D |
|---|---|---|
| least Rayleigh quotient of Q on V (units of `‖v‖²`) | **+0.69889** | **−0.65462** |
| zero-side value, same eigenvector | 0.6988851 (2000 zeros + tail) | −0.65464 (zeros to 200 + tail) |
| arch part on V, eigenvalues | [2.596, 2.617] | [4.206, 4.226] |
| comb part on V, top eigenvalue `A_B(r)` | 1.919 | 4.863 |
| `Ω(85.56)` | 2.611 | 4.221 |
| pointwise comb mass `A_L = Σ 2|w(n)|/√n`, n ≤ 56 | 24.38 | 29.12 |

In the language of round 2, section 4.3, the band comb constant is `A_B^ζ(r) = 1.919 < Ω_ζ ≈ 2.60` at
`r = 85.6`, `B ≈ 2.3`, `L = 2.02`. The band is cleared by the archimedean density with room `0.68`.
For D, `A_B^D(r) = 4.863 > Ω_D ≈ 4.21`, so the band is not cleared. Pointwise, the comb can reach
24.4. Height-locally it reaches 1.9. This is round 2's convergent finding (the comb acts through its
compression) made height-local.

### 3.2 Where the separation lives

The band modes are Dirichlet cosines, `k A = π(m + 1/2)`, so every test is continuous and orthogonal.
`window_scan.py` scans windows `A = qπ` with rational q (denominator at most 40) for 2- and 3-mode
bands. The best separations `min(λ_ζ, −λ_D)` are about 0.65 to 0.70:

| window A | x | modes | κ | λ_ζ (pole dropped) | λ_D |
|---|---|---|---|---|---|
| 17π/26 | 60.8 | 2 | 84.88, 86.41 | 0.796 | −0.703 |
| **9π/14** | **56.8** | **2** | **84.78, 86.33** | **0.698** | **−0.655** |
| 7π/10 | 81.3 | 2 | 85.00, 86.43 | 0.617 | −0.807 |
| 23π/34 | 70.1 | 3 | 83.52, 85.00, 86.48 | 0.659 | −0.850 |

The certificate uses `9π/14` because it is the smallest window among the robust two-mode instances,
so it needs the fewest primes: 24 prime powers `n ≤ 56`.

### 3.3 Detection horizons: full window against height-local

For D's first off-line zero (`γ = 85.699`, `β = 0.3085`):

| test space | first window where D's form goes indefinite |
|---|---|
| full window, all frequencies (κ-certify, round 2) | `x ≈ 31` |
| height-local, at most 6 free complex modes near γ (`horizon.py`) | **`x ≈ 42.1`** |
| two Dirichlet cosines with robust margins | `x ≈ 57` |

At `x = 40`, `optx2.py` gives D's least band eigenvalue as `+0.113, +0.111, +0.110, +0.103, +0.095` for
`d = 4, 6, 8, 12, 16` modes near 86. At `x = 33` it is `+0.46` or more. Between `x ≈ 31` and `x ≈ 42`,
D's negative eigenvector is delocalised. At `x = 40` it puts mass on `|m| = 9, 12, 17, 23` (heights 15
to 40) as well as on `m = 50, 51` (height 86). The window's surplus degrees of freedom at low
frequency are what make it negative. A band test cannot use them.

Mechanism. For a real test, the off-line quadruple contributes `4 Re F(γ₀ + iβ)² ≈ 4(F(γ₀)² − β²F'(γ₀)²)`.
It is negative once F has a steep zero near γ₀, with `βL` of order one and resolution `π/L`
comparable to D's local zero spacing (about 1.4 at height 86). The on-line zeros nearby still cost
`Σ F(γ)²`. With only a few modes, that balance tips at `x ≈ 42`. Round 2's κ-certify identity
`∫ F(t − iδ) conj F(t + iδ) dt = ∫ |F|²` says the same thing. A uniform density of off-line pairs is
invisible. Only a resolved, isolated pair can be seen.

The height-local horizons for all four of D's off-line zeros below 200 (`horizon.py`, at most 6 free
complex modes near γ):

| γ | β = Re ρ − 1/2 | first x where a band near γ detects the zero | x / (γ/2) |
|---|---|---|---|
| 85.699 | 0.3085 | 42.1 | 0.98 |
| 176.702 | 0.2243 | 96.1 | 1.09 |
| 114.163 | 0.1508 | 76.5 | 1.34 |
| 166.479 | 0.0744 | 140.7 | 1.69 |

The horizon scales like `γ/2`, stretched as β shrinks. This matches the resolution argument above,
which needs `βL` of order one.

## 4. Part (b): the kernel theorem

### 4.1 Modules

All seven are new, registered as `lean_lib`s, imported by `AxiomGuardRvMBridge`, and printed there.
The guard gives 1030 reports, 54 of them from Crux3, all within `[propext, Classical.choice, Quot.sound]`,
with no `sorryAx`.

| module | content |
|---|---|
| `Crux3_BandAnalytic` | `FreqData.weil_re_ge`: the frequency-side lower bound of `archSide − primeSide` for any continuous even real test with `K/(1+r²)` transform decay |
| `Crux3_BandTest` | the band test (`bandV = wPair ∘ clamp`), its `FreqData` instance, and closed forms of the autocorrelation and of each Lorentzian term |
| `Crux3_BandNum` | exact-rational ball arithmetic; log, √, cos and sin enclosures; the per-entry prime-side checker `entryOK` and `entry_sound` |
| `Crux3_BandTable` | the 57-entry table; `tab_ok` (`decide +kernel`); negative control `tab_tamper`; `lam_tab` (Λ(n) = μₙ log n) |
| `Crux3_BandCert` | the instance, `log π ≤ 1.1448`, the rational sums, `quad_nonneg`, **`band_floor`**, and the round-2-form pair `band_comb_le` / `band_arch_ge` |
| `Crux3_BandDHData` | D's coefficients `aD`, `κ`; the closed forms `cD n` (polynomial in κ times prime logs); the defining identity `cD_conv` on `[1, 56]`; uniqueness `eq_cD_of_conv` |
| `Crux3_BandDH` | D's functional `weilFormD`; the digamma majorant `psiD_le`; `archD_band_le`; the D prime-side checker (`kap_InB`, `cdBall_sound`, `dEntry_sound`, `dtab_ok`, negative control `dtab_tamper`); **`dh_band_arch_le`**, **`dh_band_comb_ge`**, **`dh_band_negative`**, **`band_separation`**, `band_separation_cD` |

### 4.2 The analytic chain (`FreqData.weil_re_ge`)

This is ZhuSymbol's smooth-test proof, redone for continuous tests. The band tests are Lipschitz,
not smooth, so they lie outside `IsWeilTest`. The functional `archSide − primeSide` is still defined on
their autocorrelations, and the proof never needs the zero side.

- **Poles.** `weilKernel g 0 = weilKernel g 1 = |F(i/2)|² ≥ 0`, from Zeta23's `EF.paperFT_weilTest`, which
  needs only continuity and compact support. Both terms are dropped.
- **Digamma floor.** `psiR r ≥ −γ + H_N − Σ_{j≤N} lz(j + 1/4, r)`, with `lz(b, r) = b/(b² + (r/2)²)`. This is
  RvMBridge30's `psiR_ge_series` with `M = 0`. The series tail is non-negative and is dropped.
- **Lorentzian Parseval.** `∫ |F|² lz(b, ·) = 2π ∫ g(y) e^{−2b|y|} dy`. Here `lz(b, ·)` is the cosine
  transform of `e^{−2b|y|}`, obtained from Mathlib's `integral_exp_mul_complex_Ioi`. Fubini and Zeta23's
  cosine-form inversion `Taper.integral_mul_cos_of_paperFT_eq` finish it.
- **Plancherel.** `∫ |F|² = 2π g(0)`, by the same inversion at 0.
- **Prime side.** It is a finite sum, since `supp g ⊆ [−2A, 2A]`.

The result, for every N:

  `Re W(v ⋆ ṽ) ≥ (−γ + H_N − log π) g(0) − Σ_{j≤N} ∫ g e^{−2(j+1/4)|y|} − Σ_{n<e^{2A}} 2Λ(n)/√n g(log n)`.

### 4.3 Closed forms and numerics

For Dirichlet cosines, write `σ = s₁s₂`. Then:

- `g(y) = c₁² gD(k₁, y) + 2c₁c₂ gX(y) + c₂² gD(k₂, y)` on `[0, 2A]`, where
  `gD = (2A − y) cos(ky)/2 + sin(ky)/(2k)` and `gX = σ(k₁ sin k₂y − k₂ sin k₁y)/(k₁² − k₂²)`.
- The Lorentzian terms are `Jd(k, b) = 2A·2b/(4b² + k²) + 2k²(1 + e^{−4bA})/(4b² + k²)²` and
  `Jx(b) = 2σ k₁k₂ (1 + e^{−4bA})/((4b² + k₁²)(4b² + k₂²))`. The factor `e^{−4bA}` is bounded crudely by
  `[0, 1]`; it costs less than 0.02.
- With `N = 100` the certified form has least eigenvalue 0.611, against the true 0.699. The dropped
  series tail costs about 0.085.

The prime side is handled by an exact-rational checker, `decide +kernel`, using:

- `log n` from `exp(q) = exp(q/8)⁸` and Mathlib's `Real.exp_bound`;
- `1/√n` from squares;
- `cos` and `sin` of `k log n` by reduction mod 2π (π to 20 digits), then KWin's Taylor remainders;
- ball arithmetic with rational centres and radii throughout.

The resulting prime sums are `P₁₁ = −3.549021094655 ± 2e−12`, `P₂₂ = 3.711146727560 ± 2e−12`, and
`P₁₂ = 1.103195928957 ± 2e−12`. These agree with Arb to every printed digit.

The final 2×2 form `[[a, b], [b, d]] − (A/2) I` has `a ≥ 7.598`, `d ≥ 0.3699` and `|b| ≤ 1.0942`, so
`ad − b² > 1.6`. The inputs are `γ ≤ 0.58112` (RvMBridge30), `log π ≤ 1.1448` (proved in the file) and
`π` to 20 digits. Kernel time is seconds and peak memory is about 6 GB, dominated by the Mathlib import.
That fits the 16 GB hosted CI runner.

The negative control `tab_tamper` checks that the `n = 2` entry, with its log lower bound raised by
`1e−12`, is **rejected** by the same checker.

### 4.4 D's side (`Crux3_BandDHData`, `Crux3_BandDH`)

D's functional is defined off-registry, mirroring the registry's `archSide` and `primeSide`:

- `archSideD g = g(0) log(5/π) + (1/2π) ∫ h_g(r) Re ψ(3/4 + ir/2) dr`. There are no pole terms, because D
  is entire.
- `primeSideD w g = Σ_n w(n)/√n (g(log n) + g(−log n))`.
- `weilFormD w = archSideD − primeSideD w`.

The weights are never typed in as numbers. The theorems take any `w : ℕ → ℝ` satisfying

  `a(n) log n = Σ_{d | n} w(d) a(n/d)`  for `1 ≤ n ≤ 56`,

where `a(n) = 1, κ, −κ, −1, 0` according to `n mod 5` and `κ = (√(10 − 2√5) − 2)/(√5 − 1)`. The identity is
triangular (`a(1) = 1`), so it forces `w(1) = 0` and `w = cD` on `[1, 56]` (`w_one_of_conv`,
`eq_cD_of_conv`). Each `cD n` is a closed form: a polynomial in κ of degree at most 5, times the logs of the
primes dividing n. The closed forms are generated symbolically (`dh_symbolic.py`, `gen_dh.py`) and each is
proved against the identity (`cD_conv`, one lemma per n).

The archimedean side needs an upper bound (`archD_band_le`). It holds for every band test, every
`N ≥ 1` and every `R ≥ 2k₂`, and has three ingredients:

- **Digamma majorant (`psiD_le`).**
  `Re ψ(3/4 + ir/2) ≤ −γ + H_N − Σ_{j≤N} lz(j + 3/4, r) + (3/4)/N + (r/2)²/(2N²)`.
  It comes from the series, with the tail bounded by telescoping: `Σ 1/(n+N+1)² ≤ 1/N` and
  `Σ 1/(n+N+1)³ ≤ 1/(2N²)`.
- **Lorentzian Parseval**, the same as for zeta, now at `b = j + 3/4`, with closed forms `lorTermB_bandV`.
- **The r² moment.** Beyond `r² ≥ 4k₂²` the band transform decays like `K'/r²` (`Fsq_bandV_far`, from the
  Dirichlet closed form). So `Fsq · r² ≤ R² Fsq + 2K'²/(R² + r²)`, and `∫ Fsq r² ≤ 2πR² g(0) + 2πK'²/R`.

At `c* = (−3, 2)`, with `N = 300` and `R = 175`:

| piece (units of `‖v‖²`) | certified bound | stated in Lean | true value |
|---|---|---|---|
| `Re archSideD` | ≤ 4.3188 | ≤ 4.33 (`dh_band_arch_le`) | 4.2085 |
| `Re primeSideD` | ≥ 4.8630 | ≥ 4.86 (`dh_band_comb_ge`) | 4.8631 |
| `Re weilFormD` | ≤ −0.5443 | ≤ −1/2 (`dh_band_negative`) | −0.6546 |

The arch majorant loses 0.110. The main costs are the input `γ > 1/2` (0.077) and the r² tail (0.043).

The prime side reuses zeta's checker with a new weight ball `2 · cdBall(dtab n) · (1/√n)`:
- κ comes from kernel-checked square-root brackets (`kap_InB`);
- the prime logs come from `exp(q/8)⁸` enclosures (`lp_InB`);
- the 57-entry table is checked by `dtab_ok` (`decide +kernel`), with a tampered entry rejected by
  `dtab_tamper`.

The resulting sums are `PD₁₁ = 4.93723086`, `PD₂₂ = −1.23949216` and `PD₁₂ = −7.35011920`. The other inputs are:
- `γ > 1/2` (Mathlib);
- `log π ≥ 1.1447` and `log 5 ≤ 1.609437912434102`, both proved in the file;
- `H₃₀₀` and the 301-term Lorentzian sums, by exact rational arithmetic.

Peak memory is 7.1 GB, and the module builds in about 20 s.

**Scope.** `weilFormD` is the arithmetic side of D's explicit formula. That it equals `Σ_ρ h(γ_ρ)` over
D's zeros is the classical explicit formula for D. That identity is not formalized. It is checked
numerically in section 3.1: `−0.65464` from the zeros against `−0.65462` from the arithmetic side.

## 5. What the result means, and what it does not

1. **It is the first window certificate in the program that D fails.** Every earlier window
   certificate (Zhu at `x = 4.95`, κ-certify up to `11.006`, KWin/KWin2 up to `2L = 1`) certifies a
   statement that also holds for D. D's window forms are positive definite for `x < 31`. This one
   certifies a statement that is false for D, and it is false because of D's off-line zero at 85.7.
   Its validity rests on zeta's weights `Λ(n)`, `n ≤ 56`, not only on the shape of the functional
   equation.
2. **It is an instance, not a route.** The certificate uses only `Λ(n)` for `n ≤ 56` and `Γ_R(s)`. By the
   fooling identity, the window form of any one-prime surgery `ζ(s)(1 + c p^{−s} + p·p^{−2s})` at a prime
   `p > 57` is `Q_ζ + 2 log p · Id`, so the certificate passes verbatim. Yet the surgered function has
   off-line zeros. `Crux2_unified_barrier.semilocal_barrier_full` shows that no fixed-window certificate
   can avoid this. Round 2 called this the honest limit, and it holds here.
3. **In zero language it is local.** `Q_ζ(v) = Σ_γ F(γ)²` weights zeta's zeros near height 85.6, all of
   which are verified on the line (to `3e12`). The theorem's content is that the arithmetic data alone
   certifies the inequality. D's arithmetic data cannot, and it fails for a reason that can be checked
   independently.
4. **Non-smooth tests.** The registry's `WindowFloor` quantifies over smooth tests. `band_floor` is a
   statement about the same functional on Lipschitz tests. Reading it as `Σ_ρ` would need the explicit
   formula for Lipschitz tests (by mollification; paper-level). Neither the theorem nor its use here
   relies on that reading.
5. **The round-2 target `x = 40` is not reachable height-locally** (section 3.3). A certificate of
   `κ_ζ(40) = 0` would have to be a full-window certificate, with `λ*(40) ≈ 1e−109` (Galerkin
   `N = 60`; the Landau-Widom extrapolation gives about `1e−190`). That remains infeasible, as round 2
   said.

## 6. Status tags

- THEOREM-kernel-checked (zeta): `Crux3.band_floor`, `band_comb_le`, `band_arch_ge`, and the 29
  supporting declarations printed in `AxiomGuardRvMBridge`.
- THEOREM-kernel-checked (D, the negative control): `Crux3.dh_band_negative`, `band_separation`,
  `band_separation_cD`, `dh_band_arch_le`, `dh_band_comb_ge`, and 17 supporting declarations. The only hypothesis is the
  defining identity of D's weights.
- THEOREM-certified-computation: D's value `−0.6545762050 ± 3e−11` at `c = (−3, 2)`, and zeta's
  closed-form lower bound, both from `arb_cert.py` (python-flint, 256 bits). D's closed forms are the same
  paper-level Galerkin identities as zeta's. They are validated by the zero side (section 3.1) and by
  exact agreement with κ-certify's independent code.
- COMPUTED: the detection horizons (section 3.3), the window scans, and the eigenvector structure at
  `x = 40`.
- Not formalized: the explicit formula that links `weilFormD` to D's zeros (and `weilForm` to zeta's for
  Lipschitz tests). Both links are checked numerically against the zero sides (section 3.1).

`conjecture1_proved = False`.
