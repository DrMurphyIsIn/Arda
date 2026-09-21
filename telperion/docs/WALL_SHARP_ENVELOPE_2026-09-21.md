# The sharp envelope of the Wall (2026-09-21): the band's upper edge with the exact prime constant

**Status line.** `conjecture1_proved = False`. Nothing here proves RH. This memo records
`telperion/examples/rvm_bridge/lean/E6Bridge16.lean` (namespace `RvMBridge16`, imports E6Bridge10
and E6Bridge11; axioms exactly `[propext, Classical.choice, Quot.sound]`, no `sorry`), the
sharpening of E6Bridge11's envelope `envelopeC` (which carries `e^{9 + 2 X(lam)}`, `X ∋ 16 e^{16 lam}`),
and the numerics behind it (`seam_b_small_lam.py --band-edge`). Verdict on the lead's targets
(`envelopeC'(1) <= 1e9`, `envelopeC'(0.5) <= 1e6`): NOT reachable, the first not by any c-uniform
argument, the second not with the island's Chebyshev constants (section 3). What is proved is the
sharpest c-uniform envelope of the method, with its constant an explicit convergent series.

## 1. The theorem

```lean
def primeAbsTerm (lam : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / Real.sqrt n
    * (|1 - (Real.log n) ^ 2 / (4 * lam)| * Real.exp (-(Real.log n) ^ 2 / (8 * lam)))
def primeAbs (lam : ℝ) : ℝ := 2 * ∑' n : ℕ, primeAbsTerm lam n
def tailRadius (lam : ℝ) : ℝ := Real.sqrt ((16 + 2 * primeAbs lam) / lam)
def envelopeCsharp (lam : ℝ) : ℝ :=
  2 * Real.pi * Real.exp (primeAbs lam + 1 / 2) + tailRadius lam + 3 / Real.sqrt lam + 1

theorem gaussian_positivity_envelope_sharp (c lam : ℝ) (hlam : 0 < lam)
    (hc : envelopeCsharp lam ≤ |c|) :
    0 ≤ (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re

theorem band_upper_edge :
    ∀ lam : ℝ, 0 < lam → ∀ c : ℝ, envelopeCsharp lam ≤ |c| →
      0 ≤ (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re
```

`primeAbs lam` is a real number defined by a convergent series (summability proved,
`summable_primeAbsTerm`), not an obligation. It is the EXACT size of the c-uniform prime side in
units of `A = 1/(8 sqrt(2 pi) lam^{3/2})`: the prime side of the Gaussian test is
`2A Σ Λ(n) n^{-1/2} cos(c log n)(1 - (log n)^2/(4 lam)) e^{-(log n)^2/(8 lam)}` and the only bound
valid for every centre is `|cos| <= 1` (Lean: `norm_autocorrGauss_add_neg_le`,
`norm_primeSide_le_primeAbs`: `‖primeSide f‖ <= A primeAbs lam`).

`#print axioms` (probe `Probes/E6Bridge16_probe.lean`, verbatim): every one of

    gaussian_positivity_envelope_sharp, band_upper_edge, re_weilForm_gauss_nonneg_sharp,
    envelopeCsharp_le_crude, integral_sq_mul_cexp_gaussian_fourier', fourier_autocorrGauss,
    weilKernel_zero_eq_gaussTest, weilKernel_one_eq_gaussTest, norm_gaussTest_half, norm_poles_le,
    norm_primeSide_le_primeAbs, summable_primeAbsTerm, primeAbs_le_crude,
    re_digamma_quarter_ge_log', integral_indicator_bumpR_tail_le', integral_bumpR_mul_psiR_ge_capped

depends on axioms: `[propext, Classical.choice, Quot.sound]`.

## 2. What was sharpened (each step is now exact or has a c-free, lam-free loss)

| step | E6Bridge11 (crude) | E6Bridge16 (sharp) |
|---|---|---|
| prime side | `16 A e^{16 lam}` (AM-GM) | `A primeAbs lam` (exact, `|cos| <= 1` only) |
| pole terms `W(0) + W(1)` | `4 A e^{2 lam} sqrt(32 pi lam)` (norm of the integrand) | EVALUATED: `W(0) = gaussTest c lam (i/2)`, `W(1) = gaussTest c lam (-i/2)`, modulus `(c^2 + 1/4) e^{-2 lam (c^2 - 1/4)}`; `<= 0.13 A` once `c^2 >= 6/lam + 1` (`norm_poles_le`) |
| Stirling on `Re psi(1/4 + ir/2)` | `log(|r|/2) - 5` | `log(|r|/2) - 20/r^2` (`re_digamma_quarter_ge_log'`) |
| bump tail beyond `|r - c| >= L` | `L = 2/sqrt lam`, tail `e^{-4}` | `L = tailRadius`, tail `e^{-16 - 2 primeAbs}` (`integral_indicator_bumpR_tail_le'`) |
| archimedean floor | `theta = log((|c|-L)/2) - 5`, unbounded in `c` | CAPPED at the needed `Theta = log pi + primeAbs + 0.31` (`integral_bumpR_mul_psiR_ge_capped`), so no term grows with `|c|` |
| result | `c1 = 2 e^{9 + 2X} + 2/sqrt lam` | `c1' = 2 pi e^{primeAbs + 1/2} + tailRadius + 3/sqrt lam + 1` |

The pole evaluation is the Gaussian Fourier transform of `f = phi * phi~` at a COMPLEX
frequency (`fourier_autocorrGauss`: `∫ f(u) e^{iwu} du = gaussTest c lam w` for every `w : ℂ`, the
second moment by parts with the majorant `|x|^2 e^{-a x^2 + |Im w||x|}`), which is also the
identity `weilKernel f s = gaussTest c lam (gammaOf s)` for the non-compactly-supported test.

Assembly: `F/A >= Theta - log pi - primeAbs - 0.13 - (Theta + 5) e^{-16 - 2P} 2 sqrt 2
>= 0.31 - 0.13 - 6.7 . 3 e^{-16} > 0` once `log((|c| - L)/2) - 20/(|c| - L)^2 >= Theta`, i.e.
`|c| - L >= 2 pi e^{P + 1/2}` (the `1/2` pays for `20/(|c|-L)^2 <= 0.19`).

## 3. The numbers (seam_b_small_lam.py --band-edge --sieve 10000000; P_abs to 1e-9 for lam <= 1)

```
  lam      P_abs  tail-bar      c1sharp   2pi e^Pabs   envelopeC(crude)
  0.1     1.3958  9.5e-137        66.03        25.37          3.155e+86
  0.2      3.038   3.2e-66        234.3        131.1         2.453e+368
  0.3     4.6032   1.0e-42       1050.0        627.1        4.549e+1727
  0.4     6.6309   5.9e-31       7869.0       4764.0        2.178e+8417
  0.5     8.7374   6.7e-24     6.457e+4     3.916e+4       6.356e+41498
  0.6     11.101   3.4e-19     6.859e+5      4.16e+5      1.658e+205286
  0.7     13.779   7.9e-16     9.983e+6     6.055e+6     1.306e+1016447
  0.8     16.788   2.7e-13     2.025e+8     1.228e+8     6.365e+5034047
  1.0     23.718   9.2e-10    2.071e+11    1.256e+11   1.205e+123494302
  1.5     48.925    5.0e-5    1.833e+22    1.112e+22 4.266e+368130547147
  2.0      89.62     0.012    8.644e+39    5.243e+39 1.984e+1097381692229395
```

(`tail-bar` = PNT estimate of the Lambda-sum beyond `n = 1e7`; at `lam = 2` the sum is only
converged to 1e-2, everything else is exact to the digits shown. `P_abs` reproduces the landscape
memo's `P_abs/f(0)` column: 0.25, 0.80, 1.40, 3.04, 8.7, 23.7 at 0.02, 0.05, 0.1, 0.2, 0.5, 1.)

**Why the targets are unreachable.**

* `envelopeC'(1) <= 1e9` is impossible for ANY argument that bounds the prime side uniformly in
  `c`: the archimedean side is `A (log(|c|/2) - log pi) + o(A)` and the c-uniform prime side is
  exactly `A P_abs(1) = 23.7 A`, so `|c| >= 2 pi e^{23.7} = 1.26e11` is the floor of the method;
  `c1sharp(1) = 2.07e11` is within a factor `e^{1/2}` of it. Beating 1e9 at `lam = 1` needs the
  cancellation in `cos(c log n)`, which is not c-uniform.
* `envelopeC'(0.5) <= 1e6` needs `P_proved(0.5) <= 11.9`; the exact value is `8.74`, and the sharp
  form here gives `6.5e4`. But a CLOSED-FORM proof of `P_abs(0.5) <= 11.9` is out of reach with the
  island's inputs: the only route is Abel summation against a Chebyshev bound, and the design
  numerics (scratch, Abel bound `∫ psi~(u) (-K'(u))_+ du` with the kink at `u = 2 sqrt lam`
  handled exactly) give `P_proved(0.5) = 2 . 15.1 = 30.2` with Mathlib's
  `Chebyshev.psi_le : psi x <= (log 4) x + 2 sqrt x log x` (c1 ~ 1e14), and `2 . 6.2 = 12.3`
  even with the ideal Rosser-Schoenfeld `psi x <= 1.04 x` (c1 ~ 2e6, still above 1e6). The
  `2 sqrt x log x` term of Mathlib's bound alone doubles the estimate at the relevant `n ~ 10-100`.
  Zeta23.Chebyshev has `sum_vonMangoldt_le : psi x <= (log 4 + 4) x` and
  `sum_vonMangoldt_div_sqrt_le_precise`; neither is sharper. And a Lean proof of the Abel-route
  bound would additionally need partial-range Gaussian integrals (erf), which have no closed form;
  every whole-line majorant tried costs another factor 2-3 in `P` (memo scratch: `~46` at
  `lam = 0.5`).

So: `primeAbs` is left as the explicit series (a NUMBER, evaluated above to 1e-9 for `lam <= 1`),
and the only closed-form bound that closes is the crude one, `primeAbs lam <= 16 e^{16 lam}`
(`primeAbs_le_crude`), giving `envelopeCsharp_le_crude`. Bounding `primeAbs` sharply in closed
form is what does NOT close.

## 4. The band, and the ladder

With the ladder height `T = 640000` (E6Bridge12's certified window strip `|c| <= T - D`):

* `lam_*` with `c1sharp(lam_*) = T`: `lam_* = 0.597` (`P_abs = 11.0`). For `lam <= 0.597` the sharp
  envelope covers `|c| >= T`, so the band `T - D < |c| < c1sharp(lam)` is EMPTY there and the whole
  line at that width is covered by {small-lam foothold, ladder strip, envelope} PROVIDED the
  ladder instrument certifies `|c| <= T - D` at that width. It does not: E6Bridge12's
  `gaussian_positivity_of_window*` require `1 <= lam` (`hlam`), and their thresholds at height `c`
  (PROXY constants: `constB(c) = Σ m(rho) e^{1/2}(2c^2 + 13/4)/(1 + gamma^2) ~ 0.0462 e^{1/2}
  (2c^2 + 13/4)` using `Σ_rho 1/(1 + gamma^2) = 0.0462`) are

```
         c      constB~  lamThr(d=.25)  lamThr(d=.5)  lam_dom~
     100.0       1523.0       8.012e+6      2.003e+6     2.418
    1000.0     1.523e+5       8.011e+8      2.003e+8     2.994
   10000.0     1.523e+7      8.011e+10     2.003e+10     3.594
  100000.0     1.523e+9      8.011e+12     2.003e+12     4.204
  640000.0    6.239e+10      3.281e+14     8.203e+13     4.697
```

  (`lamThr` = `lamThreshold c 2 1 delta`, single-near-zero form; `lam_dom` = the width where
  `tailEnvelope = e^{-7.5 (lam - 1)} constB c` drops below a windowSum proxy
  `(4/2pi) log(c/2pi) . mean_{|x| <= 2} x^2 e^{-2 lam x^2}`.)
* OVERLAP TEST: "Gaussian positivity at width lam for ALL c, unconditionally + ladder" needs some
  lam with (i) `c1sharp(lam) <= T` and (ii) the ladder certifying `|c| <= T - D` at that lam.
  (i) forces `lam <= 0.6`; (ii) forces `lam >= 1` by the theorem's hypothesis and `lam >= 4.7` by
  the dominance proxy at `c ~ T`. At `lam = 1` the envelope needs `|c| >= 2.07e11 = 3.2e5 . T`.
  There is NO overlap, by five orders of magnitude in `c` at `lam = 1`, and it diverges: raising `T`
  to `2e11` pushes `lam_dom(T)` to `~5.9`, where `P_abs ~ 1e3` and `c1sharp ~ e^{1000}`. The band
  is unbounded along the diagonal, as the wall map says.

## 5. What is and is not claimed

* PROVED, unconditionally: `band_upper_edge` with the explicit `envelopeCsharp`; the exact pole
  terms; the exact prime constant as a series; the Gaussian Fourier transform of `f` at complex
  frequencies.
* NOT closed: any closed-form bound on `primeAbs` sharper than `16 e^{16 lam}`; the lead's numeric
  targets (unreachable, section 3); a c-dependent (non-uniform) improvement using `cos(c log n)`
  cancellation (not a c-uniform statement, out of scope).
* This is the upper edge of the fixed-width residual band. The Wall proper is `lam` of order one
  with `|c|` between the ladder strip and `envelopeCsharp lam`, unbounded along the diagonal.
  `conjecture1_proved = False`.
