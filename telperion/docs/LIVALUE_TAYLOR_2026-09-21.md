# LiValue: the Taylor bookkeeping and the assembly (E6Bridge19, 2026-09-21)

*Module `telperion/examples/rvm_bridge/lean/E6Bridge19.lean` (namespace `RvMBridge19`, imports
`E6Bridge15`), probe `Probes/E6Bridge19_probe.lean`. Every delivered theorem is kernel-checked with
axioms exactly `[propext, Classical.choice, Quot.sound]`, no `sorry`. The analytic heart and one
segment fact are carried as named `def : Prop` hypotheses (section 3). Nothing here says anything
about whether RH holds. **`conjecture1_proved = False`.***

## 0. What was open, what is closed now

E6Bridge15 proved the convergence half of the Bombieri-Lagarias explicit formula on Li's test class
(node `RH_bl_explicit_formula`, B7) and left one obligation,

    LiValue n : liLimit n = archSide n + finiteSide n        (value half, BL 1999 Theorem 2).

E6Bridge19 proves `LiValue n` for every `0 < n` modulo two named Props:

    liValue_of (hP : XiDerivPartialFraction) (hR : NoRealZeroInUnitInterval) (n) (hn : 0 < n) : LiValue n
    bl_explicit_formula_of_partialFraction hP hR n hn :
        Tendsto (liZeroSum n) atTop (nhds (archSide n + finiteSide n))       -- the node, verbatim

The whole value half is therefore reduced to the global partial fraction of `xi'/xi` (the partner
module E6Bridge18) plus the elementary fact that `zeta` has no zero on the real segment `(0, 1)`.

## 1. The two named Props (verbatim)

```lean
def xi (s : ℂ) : ℂ := s * (s - 1) / 2 * completedRiemannZeta₀ s + 1 / 2      -- Zeta23.WeilEF.xi, verbatim

def XiDerivPartialFraction : Prop := ∀ s : ℂ, ¬ IsNontrivialZero s →
  deriv (logDeriv xi) s = -∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2

def LambdaDerivPartialFraction : Prop := ∀ s : ℂ, s ≠ 0 → s ≠ 1 → ¬ IsNontrivialZero s →
  deriv (logDeriv completedRiemannZeta) s
    = -∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2 + 1 / s ^ 2 + 1 / (s - 1) ^ 2

def NoRealZeroInUnitInterval : Prop := ∀ σ : ℝ, 0 < σ → σ < 1 → riemannZeta (σ : ℂ) ≠ 0
```

The Lambda form as first proposed (without the pole terms, at every non-zero `s`) is FALSE near
`s = 0, 1`: `completedRiemannZeta` has simple poles there, `logDeriv` behaves like `-1/s`, and the
derivative like `+1/s^2`. The corrected Lambda form above is proved EQUIVALENT to the xi form
(`xiDerivPartialFraction_iff`): off `{0, 1}` by the pole bookkeeping
`deriv (logDeriv Λ) s = deriv (logDeriv xi) s + 1/s^2 + 1/(s-1)^2`, at `0` by continuity of both
sides (the zero series is analytic on the zero-free ball, section 2) and at `1` by the symmetry
`s ↦ 1 - s` of both sides. Whichever form E6Bridge18 lands plugs in (`liValue_of_lambda`).

`NoRealZeroInUnitInterval` is used ONLY to integrate `deriv (logDeriv xi)` along the real segment
`[0, 1]` (section 3, deliverable 2). Neither Mathlib nor Zeta23 on this pin has the real-segment
nonvanishing (`riemannZeta_ne_zero_of_one_le_re` stops at `Re s = 1`); the classical proof is the
alternating series `(1 - 2^{1-σ}) ζ(σ) = Σ (-1)^{n+1} n^{-σ} > 0`. An alternative that avoids it
entirely: integrate along `0 → it → 1 + it → 1` (the lines `Re s = 0, 1` contain no nontrivial zero
and some height `t ∈ (0,1)` misses the finitely many ordinates), three FTC pieces instead of one.

## 2. Deliverable (1): power sums from the derivative

```lean
def powerSum (j : ℕ) : ℂ := ∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℂ) / ρ ^ j
theorem summable_powerSum {j : ℕ} (hj : 2 ≤ j) : Summable (fun ρ : ℂ => (zeroMult ρ : ℂ) / ρ ^ j)
theorem powerSum_conj (j : ℕ) : conj (powerSum j) = powerSum j                    -- the power sums are real
theorem powerSum_eq_taylor (hP : XiDerivPartialFraction) (k : ℕ) :
    ((k : ℂ) + 1) * powerSum (k + 2) = -(iteratedDeriv k (deriv (logDeriv xi)) 0) / (k.factorial : ℂ)
theorem powerSum_eq_neg_taylor (hP) (k) :
    powerSum (k + 2) = -(iteratedDeriv (k + 1) (logDeriv xi) 0) / ((k + 1).factorial : ℂ)
```

Mechanism. `exists_zero_radius` produces `r > 0` with `r ≤ |ρ|` for every nontrivial zero, as the
minimum of `1` and the norms of the finitely many zeros with `|Im ρ| < 1`
(`zetaSeam.finite_window`): no numerics, no first-zero bound. On the ball `|s| < r/2` the family
`zterm k ρ s = m(ρ) (-1)^k (k+1)! (s - ρ)^{-(k+2)}` is termwise differentiable with the uniform
summable bound `zbound k` (a finite-support part on the small zeros plus the local-count majorant
`m(ρ) C_k / (1 + |γ_ρ|^2)` of E6Bridge6), and the generic lemma `iteratedDeriv_tsum_ball`
(induction on `k` through `hasDerivAt_tsum_of_isPreconnected`) gives
`iteratedDeriv k (Σ' zterm 0) 0 = Σ' zterm k · 0 = (k+1)! powerSum (k+2)`. The hypothesis
identifies `deriv (logDeriv xi)` with `-Σ' zterm 0` on the ball (no zeros there), and
`Filter.EventuallyEq.iteratedDeriv_eq` transports the iterated derivative.

## 3. Deliverable (2): the paired first power sum

```lean
def pairedPowerSum (j : ℕ) : ℂ := ∑' ρ : ℂ, (zeroMult ρ : ℂ) * (((1 / ρ ^ j).re : ℝ) : ℂ)
theorem summable_pairedPowerSum {j : ℕ} (hj : 1 ≤ j) : Summable (...)          -- |Re ρ^{-j}| ≤ 1/|ρ|^2, j ≥ 1
theorem pairedPowerSum_eq_powerSum {j : ℕ} (hj : 2 ≤ j) : pairedPowerSum j = powerSum j
theorem logDeriv_xi_one_sub (s : ℂ) : logDeriv xi (1 - s) = -logDeriv xi s          -- everywhere
theorem tsum_inv_add_inv_one_sub (hP) (hR) :
    HasSum (fun ρ => (zeroMult ρ : ℂ) / ρ + (zeroMult ρ : ℂ) / (1 - ρ)) (logDeriv xi 1 - logDeriv xi 0)
theorem pairedPowerSum_one_eq (hP : XiDerivPartialFraction) (hR : NoRealZeroInUnitInterval) :
    pairedPowerSum 1 = -logDeriv xi 0
```

Mechanism. FTC for `σ ↦ logDeriv xi σ` on `[0, 1]` (`xi ≠ 0` there under `hR`; `xi(0) = xi(1) = 1/2`),
the integrand is `-Σ' zterm 0 ρ σ`, and the interchange is the dominated-convergence theorem for
parametric interval integrals with the constant-in-`σ` bound `m(ρ)/(Im ρ)^2` (every zero has
`Im ρ ≠ 0` under `hR`). Mathlib's interchange needs a countable index: it is run over the subtype of
nontrivial zeros (`zeros_countable`, a countable union of finite windows) and transported back to
the `ℂ`-indexed family via `hasSum_subtype_iff_of_support_subset`. Each term integrates to
`-(m/(1-ρ) + m/ρ)`. The reflection `ρ ↦ 1 - conj ρ` (`RvMBridge6.zeroMult_reflect`) makes the
antisymmetric family `refTerm ρ = m(ρ)(1/(1-ρ) - 1/conj ρ)` sum to `0` (`tsum_refTerm`), which folds
`Σ' m(1/ρ + 1/(1-ρ))` into `2 Σ' m Re(1/ρ)`; the antisymmetry at `s = 0` closes.

## 4. Deliverable (3): the closed forms at s = 1

```lean
theorem eta_eq (j : ℕ) : BombieriLagarias.eta j = -(iteratedDeriv j (logDeriv riemannZeta₁) 1) / j!
theorem tsum_odd_inv_pow {m : ℕ} (hm : 2 ≤ m) : ∑' n, 1 / (2 * (n : ℂ) + 1) ^ m = (1 - 1 / 2 ^ m) * riemannZeta m
theorem iteratedDeriv_psiHalf (k : ℕ) : iteratedDeriv (k + 1) (fun s => Complex.digamma (s / 2)) 1
    = -2 * (-1) ^ (k + 1) * (k + 1)! * (1 - 1 / 2 ^ (k + 2)) * riemannZeta (k + 2)
def archCoeff (k : ℕ) : ℂ := iteratedDeriv k (fun s => -(log π)/2 + (1/2) * digamma (s/2)) 1 / k!
theorem archCoeff_zero : archCoeff 0 = -(log π)/2 - log 2 - γ/2
theorem archCoeff_succ (k) : archCoeff (k + 1) = (-1)^(k+2) * (1 - 1/2^(k+2)) * riemannZeta (k+2)
theorem logDeriv_xi_eventuallyEq_one : logDeriv xi =ᶠ[𝓝 1] closedFn        -- 1/s + (-(log π)/2 + ψ(s/2)/2) + logDeriv ζ₁
def taylorOne (k : ℕ) : ℂ := iteratedDeriv k (logDeriv xi) 1 / k!
theorem taylorOne_eq (k : ℕ) : taylorOne k = (-1) ^ k + archCoeff k - BombieriLagarias.eta k
```

Mechanism. Mathlib's `riemannZeta₁ = (s-1) ζ(s)` (entire, `ζ₁(1) = 1`, `ζ₁'(1) = γ`) gives
`zetaLogDerivReg =ᶠ[𝓝 1] -logDeriv ζ₁` including at the point, so `eta j` is honest Taylor data of an
analytic function. The digamma tower comes from Zeta23's `DigammaSeries.digamma_series` at `z = s/2`:
`ψ(s/2) = -γ - 2/s + Σ' (1/(n+1) - 2/(s+2n+2))`, differentiated termwise on the ball `|s - 1| < 1/2`
with the same `iteratedDeriv_tsum_ball` machinery (bound `2 k!/(n+1)^2`; the `k = 0` term is
`s/((n+1)(s+2n+2))`), and the odd-index zeta sum via `tsum_even_add_odd`. `ψ(1/2) = -γ - 2 log 2` is
Mathlib's `digamma_one_half`. The identity `logDeriv xi = 1/s + 1/(s-1) + logDeriv Λ` and Zeta23's
`logDeriv_completedZeta` + `RvM.logDeriv_Gammaℝ` hold on a punctured neighbourhood of `1`
(`riemannZeta_eventually_ne_zero_nhds_one`); both sides are analytic at `1`, so the identity extends.

## 5. Deliverable (4): assembly

```lean
theorem taylorZero_eq (k) : taylorZero k = (-1) ^ (k + 1) * taylorOne k     -- antisymmetry, iteratedDeriv_comp_neg
theorem pairedPowerSum_succ_eq (hP) (hR) (m) : pairedPowerSum (m + 1) = -taylorZero m
theorem liLimit_eq_sum (n) : liLimit n = ∑ m ∈ range n, ((-1)^m * C(n,m+1)) * pairedPowerSum (m+1)
theorem liLimit_eq_taylorOne (hP) (hR) (n) : liLimit n = ∑ m ∈ range n, C(n,m+1) * taylorOne m
theorem liValue_of (hP) (hR) (n) (hn : 0 < n) : LiValue n
```

`liLimit n = Σ_{j=1}^n C(n,j) d_{j-1}` with `d_k = (-1)^k + A_k - η_k`; the `(-1)^k` column sums
to `1` (`Int.alternating_sum_range_choose_of_ne`), the `A_k` column is
`-(n/2)(γ + log π + 2 log 2) + Σ_{j=2}^n (-1)^j C(n,j)(1 - 2^{-j}) ζ(j)` (`sum_choose_archCoeff`,
reindexing `range n ↔ Icc 2 n`), and the `η` column is `finiteSide n` (`sum_choose_eta`). This is
EXACTLY `archSide n + finiteSide n` as `RHDefs` writes them; no sign or normalisation was adjusted.

## 6. Numerical verification (mpmath, dps = 30; script in the session scratchpad)

`archSide n + finiteSide n` computed from the closed forms (η_j by a Cauchy integral on `|s-1| = 1/2`)
against (a) Li's `λ_n = (1/(n-1)!) d^n/ds^n [s^{n-1} log ξ(s)]` at `s = 1` (independent of every
bookkeeping step here) and (b) the first 2000 zeros, paired real parts, with the crude tail
`n^2 (log(T/2π) + 1)/(2π T)`, `T = γ_2000 ≈ 2515`:

| n | archSide + finiteSide | Li generating function | diff | zeros + tail | diff |
|---|---|---|---|---|---|
| 1 | 0.023095708966121 | 0.023095708966121 | 1.1e-31 | 0.0230958070 | 9.8e-8 |
| 2 | 0.092345735228047 | 0.092345735228047 | 6.2e-31 | 0.0923461272 | 3.9e-7 |
| 3 | 0.207638920554325 | 0.207638920554325 | 2.9e-30 | 0.2076398026 | 8.8e-7 |
| 4 | 0.368790479492242 | 0.368790479492242 | 9.8e-30 | 0.3687920477 | 1.6e-6 |
| 5..8 | 0.5755427145, 0.8275660123, 1.1244601176, 1.4657556771 | same | ≤ 1.4e-27 | | |

`η_0 = -0.5772156649... = -γ` (1e-38). `Σ_ρ Re(1/ρ) = 1 + γ/2 - (log 4π)/2 = 0.0230957089...` matches
the zeros to 1e-7. The zeros+tail residual is the tail estimate's own error, not the bookkeeping.

## 7. Footguns met

* `hasSum_integral_of_dominated_convergence` and `tsum_intervalIntegral_eq_of_summable_norm` need
  `[Countable ι]`; `ℂ` is not countable. Pass to the subtype of zeros and transport back.
* `tsum_even_add_odd` must be given `f` explicitly (`?f (2*k)` is not a unification pattern; it
  times out at `whnf` otherwise).
* `convert` on `HasDerivAt` goals produces instance-diamond side goals; use `HasDerivAt.congr_deriv`
  with a `funext`-proved function identity instead.
* `neg_pow` fires on `(-1)^k` first (giving `(-1)^k * 1^k`); apply it as `neg_pow ρ`.
* `rw [hfun]` with `hfun : logDeriv xi = fun s => ...` rewrites every occurrence including the ones
  inside the right-hand side; `set g := ...` first, or use `congr_of_eventuallyEq`.
* `simp_rw [div_eq_mul_one_div]` loops; `simp [dterm]` on a two-branch recursive definition can hit
  the recursion limit (`rfl` closes the succ branch).
* The CI sorry-scan matches the bare word; write "no `sorry`" in comments.

## 8. What is NOT done

* `XiDerivPartialFraction` itself (E6Bridge18, the Hadamard/partial-fraction analytic heart).
* `NoRealZeroInUnitInterval` (elementary; or replace the segment by the L-shaped path, section 1).
* Registration: E6Bridge19 is not in `lakefile.toml` defaultTargets nor in `AxiomGuardRvMBridge`
  (not to be edited by this session); the olean was emitted by hand for the probe.
