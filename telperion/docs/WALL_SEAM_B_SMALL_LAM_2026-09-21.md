# The Wall, seam B: the unconditional small-width region (2026-09-21)

**Status line.** `conjecture1_proved = False`. Nothing here proves RH. This memo records a
Yoshida-type UNCONDITIONAL positivity theorem for the Gaussian-derivative test of the Wall,
kernel-checked on the rvm_bridge island (`telperion/examples/rvm_bridge/lean/E6Bridge11.lean`,
namespace `RvMBridge11`, axioms exactly `[propext, Classical.choice, Quot.sound]`, no `sorryAx`),
plus the numerics behind it (`telperion/examples/rvm_bridge/seam_b_small_lam.py`). It covers the
region `0 < lam <= lam0` of the two-parameter Wall for EVERY centre `c`; the Wall proper is
`lam > lam0` with `c -> infinity`.

## 1. The seam

The Wall functional is the zero side of the explicit formula for the Gaussian-derivative
transform `h(z) = (z - c) e^{-lam (z - c)^2}` (E6Bridge6.gaussTest):

    F(c, lam) := Re zeroSide (gaussTest c lam)
               = Re Sum_rho m(rho) (gamma_rho - c)^2 exp(-2 lam (gamma_rho - c)^2),
    gamma_rho = (rho - 1/2)/i.

A parallel file is proving `RH <-> forall c, forall lam > 0, F(c, lam) >= 0`. By the explicit
formula for the test `phi(u) = K u e^{-u^2/(4 lam)} e^{-icu}` (E6Bridge8.gaussPhi, `paperFT phi =
h`), with `f := phi * phi~ = WeilExplicit.autocorr phi`,

    F(c, lam) = Re [archSide f - primeSide f].

That identity for the NON-compactly-supported `phi` is outside the E8 class (IsWeilTest needs
compact support); it is being proved in a parallel file and is restated here VERBATIM as a
named hypothesis, never assumed silently:

```lean
def GaussianExplicitFormula : Prop := ∀ (c lam : ℝ), 0 < lam →
  (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re
    = (WeilExplicit.archSide (WeilExplicit.autocorr (RvMBridge8.gaussPhi c lam))
        - WeilExplicit.primeSide (WeilExplicit.autocorr (RvMBridge8.gaussPhi c lam))).re
```

## 2. Paper analysis: is lam0 absolute? YES.

**The autocorrelation in closed form** (Lean: `autocorr_gaussPhi`). With `b = 1/(4 lam)`,

    f(u) = |K|^2 e^{-icu} int (w^2 - u^2/4) e^{-2b w^2} dw . e^{-b u^2/2}
         = A (1 - u^2/(4 lam)) e^{-u^2/(8 lam)} e^{-icu},      A := 1/(8 sqrt(2 pi) lam^{3/2}).

Check: `f(0) = A = ||phi||_2^2 = (1/2pi) int |h(r)|^2 dr` (Plancherel). Majorant (Lean:
`norm_autocorrGauss_le`): `|1 - 2s| e^{-s} <= 2 e^{-s/2}` gives `|f(u)| <= 2A e^{-u^2/(16 lam)}`.

**The prime side** `Sum_n Lambda(n) n^{-1/2} (f(log n) + f(-log n))` is exponentially small in
`1/lam`: with `Lambda(n) <= log n <= 2 sqrt n` and `e^{-(log n)^2/(16 lam)} <= n^{-sigma}`,
`sigma := log 2/(16 lam)`, one gets (Lean: `norm_primeSide_le`, valid once `sigma >= 2`)

    |primeSide f| <= 8A 2^{2 - sigma} (pi^2/6) <= 64 A e^{-(log 2)^2/(16 lam)}.

**The archimedean side.** `archSide f = W(0) + W(1) - f(0) log pi + (1/2pi) int W(1/2 + ir) Re psi(1/4 + ir/2) dr`
with `W = weilKernel f`. On the line (Lean: `weilKernel_autocorrGauss_line`, one integration by
parts against Mathlib's `fourierIntegral_gaussian` and E6Bridge8's first moment)

    W(1/2 + ir) = |h(r)|^2 = (r - c)^2 e^{-2 lam (r - c)^2} =: B(r),   int B = 2 pi A.

So the integral term is `A . <Re psi(1/4 + i r/2)>_B`, the bump-average of `Re psi`. The two
inputs on `Re psi` (both from Zeta23):

* `Re psi(1/4 + it) >= -5` for ALL t (Lean: `re_digamma_quarter_ge`, from the real digamma
  series on vertical lines, `Zeta23.MuFields.re_digamma_vertical`: every series term is >= 0,
  `a/(a^2+t^2) <= 4`, `gamma_Euler < 2/3`).
* `Re psi(1/4 + i r/2) >= 2` for `|r| >= R0 := 41` (Lean: `re_digamma_quarter_ge_two`, from
  `Zeta23.StirlingVert.re_digamma_stirling'`: `|Re psi(a + it) - log|t|| <= 5/t^2`; at `|t| >= 20.5`
  this is `>= log 20.5 - 0.012 >= 3 - 1`).

Pointwise `Re psi >= 2 - 7 . 1_{|r| < R0}`, so with `B <= 1/(2 lam)` (Lean: `bumpR_le`, `y e^{-y} <= 1`)

    int B Re psi >= 2 (2 pi A) - 7 . 2 R0 . 1/(2 lam) = 4 pi A - 7 R0/lam       (Lean: `integral_bumpR_mul_psiR_ge`).

**The pole terms are c-UNIFORM and small.** This was the flagged worry: they do NOT grow with
`|c|`. `W(0) = paperFT f (i/2) = G(i/2)` with `G = gaussTest`, and `|G(i/2)| = (c^2 + 1/4)
e^{lam/2 - 2 lam c^2}`, which DECAYS in `c` (maximum `~ 1/(2 lam e)` at `c^2 = 1/(2 lam)`). The
Lean proof does not even evaluate them: `|W(0)|, |W(1)| <= int |f(u)| e^{|u|/2} du <= 2A e^{2 lam}
sqrt(32 pi lam)` (Lean: `norm_weilKernel_zero_le`, `norm_weilKernel_one_le`; AM-GM
`|u|/2 <= u^2/(32 lam) + 2 lam`). Relative to `A` this is `O(sqrt lam)`, uniformly in `c`.

**Why the centre never hurts.** All `c`-dependence of the archimedean side sits in where the
bump `B` is centred; the lower bounds on `Re psi` are `r`-pointwise and the bump's mass inside
`|r| < R0` is `<= R0/lam` regardless of `c`. (For large `|c|` the bump sits where
`Re psi ~ log(|c|/2)`, which only helps; the numerics show `F/A` growing like `log c`.)

**Assembly** (Lean: `re_archSide_ge`, `re_weilForm_gauss_nonneg`):

    F/A >= (2 - log pi) - 4 e^{2 lam} sqrt(32 pi lam) - 64 e^{-(log 2)^2/(16 lam)}
           - 7 R0 . 8 sqrt(2 pi) sqrt(lam) / (2 pi),

every term explicit and c-free. The right side is `>= 0.25` at `lam = 1e-7` (using
`log pi <= 2 log 2 < 1.3863`, `sqrt lam <= 1/3000`, `e^{2 lam} <= 3`, `sqrt(32 pi) <= 11`,
`sqrt(2 pi) <= 2.51`, `e^{-x} <= 1/x`), and is nonnegative for `lam <= 8.0e-7` (script). So

    lam0 := 1e-7 is ABSOLUTE (no dependence on c).

The constants are crude by design (the elementary route above); the honest theorem shape is
"absolute lam0", not "lam0(c)".

## 3. Numerics (seam_b_small_lam.py, mpmath dps 20, primes to 10^6, digamma quadrature)

Prime-side evaluation of `F = arch - prime` (columns: `A`; `arch`; its three pieces
`poles = 2 Re G(i/2)`, `-f(0) log pi`, `psi-int = (1/2pi) int B Re psi`; `prime`; `F`; `F/A`).

```
         c     lam            A           arch        poles     -f0logpi        psi-int          prime   F=arch-prime        F/A
       0.0   0.005      141.047      67.439153    -0.501252     -161.461      229.40157   -0.019337866      67.458491   0.478268
       0.0    0.01      49.8678      6.1549148    -0.502506     -57.0851      63.742565     -1.3272214      7.4821363   0.150039
       0.0    0.02      17.6309     -4.3284533    -0.505025     -20.1826      16.359218     -4.4636446     0.13519133 0.00766785
       0.0    0.05      4.46031     -3.5852657    -0.512658     -5.10585      2.0332423     -3.5852666   8.4103782e-7  1.8856e-7
       0.0     0.1      1.57696      -2.201055    -0.525636     -1.80519     0.12977132      -2.201055  1.7702006e-15 1.12254e-15
       0.0     0.2     0.557539     -1.3704479    -0.552585    -0.638231    -0.17963115     -1.3704479 -4.2351647e-20 -7.59618e-20
       0.0     0.5     0.141047    -0.93640527    -0.642013    -0.161461    -0.13293139    -0.93640527 -8.1713268e-18 -5.79332e-17
       0.0     1.0    0.0498678    -0.95607841    -0.824361   -0.0570851   -0.074632631    -0.95607834  -7.0101201e-8 -1.40574e-6
       1.0   0.005      141.047      67.815623      1.50857     -161.461      227.76822   -0.014875439      67.830498   0.480906
       1.0    0.01      49.8678      6.9683363      1.51677     -57.0851      62.536706     -1.0207876      7.9891239   0.160206
       1.0    0.02      17.6309     -3.1822938      1.53212     -20.1826      15.468233     -3.3800884     0.19779452  0.0112186
       1.0    0.05      4.46031     -2.0841946       1.5699     -5.10585      1.4517533     -2.0842002   5.5765509e-6 1.25026e-6
       1.0     0.1      1.57696    -0.46123873      1.60732     -1.80519    -0.26336722    -0.46123873  1.7859322e-13 1.13252e-13
       1.0     0.2     0.557539     0.55233157      1.60048    -0.638231    -0.40992167     0.55233157  1.7787692e-20 3.1904e-20
       1.0     0.5     0.141047     0.81544522       1.1778    -0.161461    -0.20089022     0.81544522 -1.8211208e-18 -1.29114e-17
       1.0     1.0    0.0498678     0.12977939     0.266501   -0.0570851   -0.079636461     0.12977939  2.4337454e-10  4.8804e-9
 14.134725   0.005      141.047      98.029735      54.2588     -161.461      205.23206    0.018010509      98.011724   0.694885
 14.134725    0.01      49.8678       32.33483      7.22987     -57.0851      82.190108      1.2361476      31.098682   0.623623
 14.134725    0.02      17.6309      12.325592     0.120315     -20.1826      32.387923      4.1631709      8.1624208    0.46296
 14.134725    0.05      4.46031      3.4356211   1.95191e-7     -5.10585      8.5414714      3.0216928     0.41392837  0.0928026
 14.134725     0.1      1.57696      1.2475754 -1.72665e-15     -1.80519      3.0527662      1.2439784   0.0035969957 0.00228097
 14.134725     0.2     0.557539     0.44658868  6.63725e-33    -0.638231        1.08482      0.4465884   2.7275863e-7 4.89219e-7
 14.134725     0.5     0.141047     0.11379227  6.40794e-86    -0.161461     0.27525344     0.11379227  2.0089135e-14 1.42428e-13
 14.134725     1.0    0.0498678    0.040326257 -1.91546e-171   -0.0570851     0.097411401    0.040326252   4.2008395e-9 8.42395e-8
      50.0   0.005      141.047      288.08401    6.1753e-8     -161.461      449.54518    0.019241566      288.06476    2.04233
      50.0    0.01      49.8678       102.6645  5.39925e-19     -57.0851      159.74964      1.3201214      101.34437    2.03226
      50.0    0.02      17.6309      36.434878 -7.47584e-41     -20.1826      56.617524      4.2798007      32.155077    1.82379
      50.0    0.05      4.46031      9.2378103 3.61876e-106     -5.10585      14.343661      1.6559989      7.5818114    1.69984
      50.0     0.1      1.57696      3.2684428 -3.1827e-214     -1.80519      5.0736335    -0.10490529      3.3733481    2.13915
      50.0     0.2     0.557539      1.1559888 1.19573e-431    -0.638231      1.7942201    0.037019544      1.1189693    2.00698
      50.0     0.5     0.141047     0.29250819 1.13094e-1082    -0.161461     0.45396936     0.16820628     0.12430192   0.881278
      50.0     1.0    0.0498678     0.10342475 2.36701e-2168   -0.0570851     0.16050989    0.055856005    0.047568745   0.953897
    1000.0   0.005      141.047      715.08253            0     -161.461       876.5437   0.0079910247      715.07454    5.06975
    1000.0    0.01      49.8678      252.82172            0     -57.0851      309.90687     0.54793341      252.27379    5.05885
    1000.0    0.02      17.6309      89.386309            0     -20.1826      109.56895      1.6782033      87.708105    4.97467
    1000.0    0.05      4.46031      22.613196            0     -5.10585      27.719047    0.022106743       22.59109    5.06491
    1000.0     0.1      1.57696      7.9949781            0     -1.80519      9.8001689    -0.44961065      8.4445888    5.35499
    1000.0     0.2     0.557539      2.8266527            0    -0.638231       3.464884    -0.17933662      3.0059893    5.39153
    1000.0     0.5     0.141047     0.71509301            0    -0.161461     0.87655418  0.00028904386     0.71480396    5.06783
    1000.0     1.0    0.0498678     0.25282358            0   -0.0570851     0.30990872     0.07727196     0.17555162    3.52034
   10000.0   0.005      141.047      1039.8666            0     -161.461      1201.3278  -0.0084528017      1039.8751    7.37252
   10000.0    0.01      49.8678       367.6484            0     -57.0851      424.73354    -0.57939998       368.2278    7.38408
   10000.0    0.02      17.6309      129.98334            0     -20.1826      150.16599     -1.7094739      131.69281    7.46942
   10000.0    0.05      4.46031      32.883474            0     -5.10585      37.989324      0.8314989      32.051975    7.18604
   10000.0     0.1      1.57696      11.626064            0     -1.80519      13.431254      1.3834623      10.242601    6.49517
   10000.0     0.2     0.557539      4.1104342            0    -0.638231      4.7486655     0.46032734      3.6501069    6.54682
   10000.0     0.5     0.141047      1.0398667            0    -0.161461      1.2013279    -0.083949649      1.1238164    7.96765
   10000.0     1.0    0.0498678     0.36764842            0   -0.0570851     0.42473356    -0.071122805     0.43877122    8.79869
  100000.0   0.005      141.047      1364.6404            0     -161.461      1526.1016   -0.0036244664       1364.644    9.67507
  100000.0    0.01      49.8678      482.47323            0     -57.0851      539.55838     -0.2491613       482.7224    9.68004
  100000.0    0.02      17.6309      170.58005            0     -20.1826      190.76269    -0.96446601      171.54451    9.72975
  100000.0    0.05      4.46031      43.153718            0     -5.10585      48.259568     -1.6123712      44.766089    10.0365
  100000.0     0.1      1.57696      15.257143            0     -1.80519      17.062334     -1.1493382      16.406481    10.4039
  100000.0     0.2     0.557539      5.3942147            0    -0.638231      6.0324461    -0.53662491      5.9308397    10.6375
  100000.0     0.5     0.141047      1.3646404            0    -0.161461      1.5261016    -0.12035015      1.4849905    10.5283
  100000.0     1.0    0.0498678     0.48247323            0   -0.0570851     0.53955838   0.0024083269     0.48006491    9.62675
```

Reading the table:

* `F >= 0` everywhere on the grid, for all seven centres and all eight widths. At `c = 0` and
  `c = 1` the values for `lam >= 0.05` are the tiny true zero-side values: `F(0, 0.05) = 8.4e-7 =
  2 gamma_1^2 e^{-2 . 0.05 . gamma_1^2}` to three digits (`gamma_1 = 14.1347`), `F(0, 0.1) =
  1.77e-15` likewise. This is a two-sided consistency check of the whole prime-side pipeline
  (digamma quadrature, pole terms, Lambda-sum) at relative accuracy `1e-9` against the zero side.
* The negative entries (`-4e-20`, `-8e-18`, `-7e-8` at `c = 0`; `-2e-18` at `c = 1`) are NOT
  precision noise (they are identical at dps 40) and NOT a real signal: they are the truncation of
  the Lambda-sum at `n = 10^6`. The script's `ptail-bar` column (tail of the prime sum beyond
  `10^6`, PNT density, integrand in absolute value) is `7.95e-18` at `lam = 0.5` and `7.0e-8` at
  `lam = 1`, matching them digit for digit. The true `F(0, 1)` is `~ 2 gamma_1^2 e^{-2 gamma_1^2} ~ 1e-171`.
* The `c`-dependence is monotone and HELPFUL: `F/A` at `lam = 0.005` goes `0.48, 0.48, 0.69, 2.04,
  5.07, 7.37, 9.68` for `c = 0, 1, 14.1, 50, 10^3, 10^4, 10^5`, i.e. `F/A ~ log(c/2) - log pi`
  for large `c`, exactly the bump-average of `Re psi`. The pole terms are negligible for `|c| >=
  50` (they decay like `e^{-2 lam c^2}`) and at most `1.6` in absolute value on the grid.
* The Lean threshold `lam0 = 1e-7` is far inside the region where the prime-side lower bound
  holds (`8.0e-7` with the same constants) and astronomically inside the region where `F >= 0`
  numerically (all of `lam <= 1` on this grid). The gap between `1e-7` and where positivity could
  conceivably fail is the price of elementary constants, not of the mechanism.

## 4. Zero-side cross-check (first 2000 zeros, mpmath.zetazero, plus density tail)

See section 7. The `c = 0`, `lam >= 0.05` rows above are already an exact-zero-side check,
and `c <= 1000` with `lam >= 0.005` is fully covered by the first 2000 zeros since the bump `B`
lives within `|r - c| <= 7/sqrt(2 lam) <= 70`.

## 5. The Lean deliverable

File: `telperion/examples/rvm_bridge/lean/E6Bridge11.lean` (imports E6Bridge8,
Zeta23.GammaFacts.{StirlingVert, Mu}, Zeta23.Analytic.Stirling, Zeta23.WeilEF.VerticalLine).
Probe: `Probes/E6Bridge11_probe.lean`. Not added to lakefile.toml / AxiomGuardRvMBridge.lean
(house rule for this task); the olean was produced with `lake env lean -o` for the probe.

Delivered theorems (signatures verbatim):

```lean
theorem re_weilForm_gauss_nonneg (c lam : ℝ) (hlam : 0 < lam) (hlam0 : lam ≤ lam₀) :
    0 ≤ (archSide (autocorr (RvMBridge8.gaussPhi c lam))
          - primeSide (autocorr (RvMBridge8.gaussPhi c lam))).re
-- UNCONDITIONAL; lam₀ := 1 / 10000000

theorem gaussian_positivity_small_lam_of (hEF : GaussianExplicitFormula) :
    ∃ lam₀ > 0, ∀ c lam : ℝ, 0 < lam → lam ≤ lam₀ →
      0 ≤ (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re

theorem gaussian_positivity_small_lam_explicit_of (hEF : GaussianExplicitFormula)
    (c lam : ℝ) (hlam : 0 < lam) (hle : lam ≤ lam₀) :
    0 ≤ (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re
```

`#print axioms` (probe output, verbatim): every one of

    re_weilForm_gauss_nonneg, gaussian_positivity_small_lam_of,
    gaussian_positivity_small_lam_explicit_of, autocorr_gaussPhi, norm_autocorrGauss_le,
    norm_primeSide_le, norm_weilKernel_zero_le, norm_weilKernel_one_le,
    integral_sq_mul_cexp_gaussian_fourier, weilKernel_autocorrGauss_line,
    re_digamma_quarter_ge, re_digamma_quarter_ge_two, integrable_bumpR_mul_psiR,
    integral_bumpR, integral_bumpR_mul_psiR_ge, re_archSide_ge, integral_sq_mul_exp_neg_mul_sq

depends on axioms: `[propext, Classical.choice, Quot.sound]`. No `sorry` anywhere in the file.

The ONLY obligation is `GaussianExplicitFormula` (a `def : Prop`, section 1), consumed as a
hypothesis of the two `_of` theorems. Nothing else is assumed.

Lemma list for the guard (all in `RvMBridge11`): `gaussA_pos`, `integral_sq_mul_exp_neg_mul_sq`,
`integral_sq_mul_cexp_neg_mul_sq`, `re_digamma_quarter_ge`, `re_digamma_quarter_ge_two`,
`gaussPhi_mul_conj`, `autocorr_gaussPhi_eq_integral`, `integral_sq_sub_mul_cexp`,
`gaussK_mul_conj`, `autocorr_gaussPhi`, `autocorr_gaussPhi_funext`, `autocorrGauss_zero`,
`abs_one_sub_two_mul_exp_le`, `norm_autocorrGauss_le`, `prime_term_bound`, `norm_primeSide_le`,
`norm_integral_autocorrGauss_mul_exp_le`, `weilKernel_zero_eq`, `weilKernel_one_eq`,
`norm_weilKernel_zero_le`, `norm_weilKernel_one_le`, `integral_sq_mul_cexp_gaussian_fourier`,
`weilKernel_line_eq`, `cpow_pi_div_a`, `weilKernel_autocorrGauss_line`, `psiR`, `psiR_eq`,
`psiR_ge`, `psiR_ge_two`, `continuous_psiR`, `bumpR_nonneg`, `continuous_bumpR`,
`integrable_bumpR`, `integrable_bumpR_mul_psiR`, `bumpR_le`, `integral_bumpR`, `R₀_pos`,
`setIntegral_bumpR_le`, `integral_bumpR_mul_psiR_ge`, `integral_archIntegrand_eq`,
`re_archSide_ge`, `re_weilForm_gauss_nonneg`, `gaussian_positivity_small_lam_of`,
`gaussian_positivity_small_lam_explicit_of`.

Upstream inputs consumed as black boxes: `Zeta23.StirlingVert.re_digamma_stirling'`,
`Zeta23.MuFields.re_digamma_vertical`, `Zeta23.Stirling.differentiableAt_digamma`,
`Zeta23.WeilEF.digamma_growth_strip`; from E6Bridge8: `integral_mul_cexp_gaussian_fourier`,
`integrable_abs_pow_mul_exp_quadratic_abs`, `integrable_mul_cexp_quadratic`, `gaussB_pos`;
Mathlib: `fourierIntegral_gaussian`, `integral_gaussian`, `integral_mul_deriv_eq_deriv_mul_of_integrable`,
`integral_eq_zero_of_hasDerivAt_of_integrable`, `hasSum_zeta_two`,
`ArithmeticFunction.vonMangoldt_le_log`, `Real.eulerMascheroniConstant_lt_two_thirds`.

## 6. What this is and is not

* It IS Yoshida-type unconditional positivity: H. Yoshida, "On Hermitian forms attached to zeta
  functions", in *Zeta Functions in Geometry*, Adv. Stud. Pure Math. 21 (1992), 281–325, proved
  positivity of Weil's Hermitian form for test functions concentrated in a sufficiently small
  window, unconditionally (the prime side is empty or negligible below `log 2`). CITATION STATUS:
  bibliographic data verified through two secondary sources (arXiv:2206.03682, and the 2026
  "Certified Weil positivity beyond the unit window" preprint which attributes to Yoshida strict
  positivity on small windows with a uniform lower constant); the primary text was NOT accessed
  from this session, so the exact statement/normalisation in Yoshida is marked UNRESOLVED. Our
  test is a Gaussian (not compactly supported), our window parameter is `lam`, and our proof is
  self-contained on the island; the attribution is to the mechanism, not to a theorem reused.
* It covers the region `lam <= lam0` of the Wall for every `c`. The Wall proper, where RH lives,
  is `lam > lam0` with `c -> infinity`: for `lam` of order one the pair contribution of an off-line
  zero near `c` is not dominated by anything unconditional (that is E6Bridge7's dominance
  analysis run backwards), and no `c`-uniform lower bound of the kind above can exist there
  (it would prove RH).
* It says NOTHING about the zeros; `re_weilForm_gauss_nonneg` is a statement about the E8
  functional on one explicit test, and the transfer to the zero side is exactly the named
  hypothesis. `conjecture1_proved = False`.

## 7. Zero-side cross-check results

`mpmath.zetazero(k)`, `k <= 2000` (`gamma_2000 = 2515.286`), each zero counted with its mirror
`-gamma`, density tail `(1/2pi) log(|r|/2pi)` beyond `gamma_2000` (it is identically 0 on this
grid: the bump's support `|r - c| <= 7/sqrt(2 lam) <= 70` never reaches `2515` for `c <= 1000`).

```
         c     lam   F (prime side)   zero side (2000)   rel.diff
       0.0   0.005        67.458491          67.458491  3.054e-20
       0.0    0.01        7.4821363          7.4821363  8.151e-20
       0.0    0.02       0.13519133         0.13519133  1.355e-18
       0.0    0.05     8.4103782e-7       8.4103782e-7  6.186e-14
       0.0     0.1    1.7702006e-15      1.7702162e-15   8.825e-6
       0.0     0.2   -4.2351647e-20      7.8423804e-33       -1.0
       0.0     0.5   -8.1713268e-18      6.8188739e-85       -1.0
       0.0     1.0    -7.0101201e-8     1.1636452e-171       -1.0
       1.0   0.005        67.830498          67.830498  2.398e-20
       1.0    0.01        7.9891239          7.9891239  7.634e-20
       1.0    0.02       0.19779452         0.19779452  8.554e-19
       1.0    0.05     5.5765509e-6       5.5765509e-6  7.909e-15
       1.0     0.1    1.7859322e-13      1.7859323e-13   1.006e-7
       1.0     0.2    1.7787692e-20      1.8487316e-28       -1.0
       1.0     0.5   -1.8211208e-18      2.0507924e-73       -1.0
       1.0     1.0    2.4337454e-10     2.4378187e-148       -1.0
 14.134725   0.005        98.011724          98.011724  1.659e-20
 14.134725    0.01        31.098682          31.098682  1.917e-20
 14.134725    0.02        8.1624208          8.1624208  2.491e-20
 14.134725    0.05       0.41392837         0.41392837  8.595e-20
 14.134725     0.1     0.0035969957       0.0035969957  2.631e-18
 14.134725     0.2     2.7275863e-7       2.7275863e-7  2.665e-14
 14.134725     0.5    2.0089135e-14      2.0088842e-14  -1.454e-5
 14.134725     1.0     4.2008395e-9      2.0088723e-14       -1.0
      50.0   0.005        288.06476          288.06476  4.516e-21
      50.0    0.01        101.34437          101.34437 -3.209e-21
      50.0    0.02        32.155077          32.155077  3.372e-21
      50.0    0.05        7.5818114          7.5818114 -1.073e-20
      50.0     0.1        3.3733481          3.3733481 -1.205e-20
      50.0     0.2        1.1189693          1.1189693 -3.028e-21
      50.0     0.5       0.12430192         0.12430192  3.865e-18
      50.0     1.0      0.047568745        0.047568747   3.929e-8
    1000.0   0.005        715.07454          715.07454        0.0
    1000.0    0.01        252.27379          252.27379  2.579e-21
    1000.0    0.02        87.708105          87.708105 -2.472e-20
    1000.0    0.05         22.59109           22.59109 -1.008e-19
    1000.0     0.1        8.4445888          8.4445888 -1.268e-19
    1000.0     0.2        3.0059893          3.0059893 -2.074e-19
    1000.0     0.5       0.71480396         0.71480396  1.138e-19
    1000.0     1.0       0.17555162         0.17555162    2.95e-9
```

Agreement is to `1e-19` relative wherever the prime-side value is above the Lambda-sum
truncation bar (section 3), and where it is not (`rel.diff = -1.0`), the zero side gives the true
value (`1e-28` to `1e-171`), i.e. `0` to within the bar. Both sides are positive throughout.
Since the first 2000 zeros are on the line, the zero side is termwise nonnegative, so this is a
check of the PRIME-SIDE pipeline (and of the explicit-formula identity for the Gaussian test,
numerically), not an independent test of positivity.
