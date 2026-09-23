# Hadamard factorisation for the dbn island (obligation L3) -- plan, 2026-09-23

Status line for every reader: this is classical complex analysis, not RH.
`conjecture1_proved = False`.

## 1. Target

`DBNDeBruijnReduction.ApproxHadamard : ∀ δ > 0, ∀ k, Nonempty (EvenHadamardData (Gδ δ k))`
where (`DBNStep.lean`)

    structure EvenHadamardData (f : ℂ → ℂ) where
      c : ℂ ; m : ℕ ; τ : ℕ → ℂ
      tendsto_prod : ∀ z, Tendsto (fun n ↦ c * z^(2m) * ∏ k ∈ range n, (1 - z^2 * τ k^2)) atTop (𝓝 (f z))

with the adapter `EvenHadamardData.ofHasProd`.  Inputs already on the island:
`differentiable_Gδ`, `Gδ_neg` (even), `Gδ_zero_re_pos` (not identically zero),
`norm_Gδ_le_exp_rpow_norm : ‖Gδ δ N z‖ ≤ ΦBoundConst/π * exp((2/3) ((9 + N|δ| + ‖z‖)/2)^(3/2))`
(order 3/2 < 2).

General theorem to prove (module `DBNHadamard.lean`):

    theorem evenHadamardData_of_order_lt_two {f : ℂ → ℂ} (hf : Differentiable ℂ f)
        (heven : ∀ z, f (-z) = f z) (hne : ∃ z, f z ≠ 0) {A B ρ : ℝ}
        (hA : 1 ≤ A) (hB : 0 ≤ B) (hρ₀ : 0 < ρ) (hρ : ρ < 2)
        (hgrowth : ∀ z, ‖f z‖ ≤ A * Real.exp (B * ‖z‖ ^ ρ)) : Nonempty (EvenHadamardData f)

(the normalisations `1 ≤ A`, `0 ≤ B`, `0 < ρ` are free for the approximants and cost nothing).

## 2. Survey result (Mathlib de5ce8a9, 2026-08-11; upstream master checked 2026-09-23)

No Hadamard / Weierstrass factorisation anywhere in Mathlib (pin or master).  What IS there
and is used below:

* Jensen: `AnalyticOnNhd.circleAverage_log_norm` (formula), `AnalyticOnNhd.sum_divisor_le`
  (zero count `≤ log(M/‖f c‖)/log(R/r)`), `MeromorphicOn.circleAverage_log_norm`.
* Divisors / orders: `MeromorphicOn.divisor`, `AnalyticOnNhd.divisor_apply`,
  `analyticOrderAt`, `analyticOrderNatAt`, `analyticOrderAt_mul`, `analyticOrderAt_pow`,
  `analyticOrderAt_comp_of_deriv_ne_zero`, `AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero`,
  `divisor_ball_support_finite`, `divisor_sphere_support_finite`.
* Normal forms: `toMeromorphicNFOn`, `meromorphicOrderAt_toMeromorphicNFOn`,
  `MeromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE`, `toMeromorphicNFAt_eq_self`,
  `MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff`, `MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt`,
  `meromorphicOrderAt_div`.
* Products: `multipliable_one_add_of_summable`, `tprod_one_add_ne_zero_of_summable`,
  `hasProdLocallyUniformlyOn_one_add` (Mathlib/Analysis/Normed/Module/MultipliableUniformlyOn.lean),
  `hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn`, `TendstoLocallyUniformlyOn.differentiableOn`,
  `Multipliable.tprod_subtype_mul_tprod_subtype_compl`, `Function.Injective.hasProd_iff`,
  `summable_sigma_of_nonneg`.
* Harmonic / Poisson: `AnalyticAt.harmonicAt_re`, `HarmonicOnNhd.circleAverage_eq` (mean value),
  `HarmonicOnNhd.circleAverage_poissonKernel_smul` (Poisson formula, kernel `poissonKernel`),
  `circleAverage_mono`, `abs_circleAverage_le_circleAverage_abs`, `circleAverage_congr_codiscreteWithin`,
  `MeromorphicOn.circleIntegrable_log_norm`.
* Growth to coefficients: `Complex.borelCaratheodory` (sup of Re on the open ball),
  `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` (Cauchy estimate),
  `is_const_of_deriv_eq_zero`.
* Logarithm of a zero-free entire function: `Differentiable.isExactOn_univ` (primitives on ℂ).

## 3. Route (genus zero in z², minimum modulus replaced by Jensen in the mean)

Let `f` be even entire, not identically zero, `‖f z‖ ≤ A exp(B ‖z‖^ρ)`, `1 ≤ ρ < 2` (we may assume
`ρ ≥ 1` by enlarging).  Fix `p` with `ρ < p < 2` (`p = (ρ+2)/2`).

L3a (counting).  Jensen's inequality at a centre `c` with `f c ≠ 0`: the number of zeros
(with multiplicity) in `closedBall 0 r` is `≤ C r^ρ + C'`.  Dyadic decomposition gives
`Σ_{s ≠ 0, f s = 0} ord_s(f) ‖s‖^(-q) < ∞` for every `q > ρ` (used with `q = p` and `q = 2`).

L3b (product).  Evenness: `ord_{-s} f = ord_s f` (`analyticOrderAt_comp_of_deriv_ne_zero` with
negation) and `ord_0 f = 2m` is even.  Choose one representative `s` of each pair `±s`
(`re s > 0`, or `re s = 0 ∧ im s > 0`), list each with multiplicity `ord_s f` as a sequence
`τ k = s⁻¹` (an injection of the countable sigma type into ℕ, padded with `τ k = 0`).  Then
`P₀ z = ∏' k, (1 - z² τ_k²)` converges (`Σ ‖τ k‖² < ∞`), is entire (locally uniform), `P₀ 0 = 1`,
`log ‖P₀ z‖ ≤ K ‖z‖^p` with `K = (1 + 2/p) Σ ‖τ k‖^p` (from `log(1+x) ≤ (1 + 1/α) x^α`,
`α = p/2`), and `ord_z P₀ = #{k | z² τ_k² = 1} = ord_z f` for `z ≠ 0`.

L3c (quotient).  `P z = z^(2m) P₀ z` has the divisor of `f`; `g := toMeromorphicNFOn (f / P) univ`
has order 0 everywhere, so it is entire and zero-free, and `f = g * P` everywhere.  A primitive `H`
of `g'/g` gives `g = exp ∘ H` after adjusting the constant.

L3d (THE WALL, bypassed).  Classically one needs `log ‖P₀‖ ≥ -r^p` on circles avoiding the zeros.
Instead: `(Re H)⁺ = (log ‖g‖)⁺ ≤ (log ‖f‖)⁺ + (log ‖P₀‖)⁻` on `|z| = R ≥ 1` (off the finitely many
zeros on the circle, which a codiscrete congruence removes), and Jensen's FORMULA for `P₀`
(`P₀ 0 = 1`, all divisor terms `≥ 0`) gives `circleAverage (log ‖P₀‖) ≥ 0`, hence
`circleAverage (log ‖P₀‖)⁻ ≤ circleAverage (log ‖P₀‖)⁺ ≤ K R^p`.  With the mean value property
`circleAverage (Re H) = Re H 0` we get `circleAverage |Re H| 0 R ≤ 2 (log A + (B + K) R^p) + |Re H 0|`.

L3e (linear).  Poisson formula for the harmonic `Re H` on `closedBall 0 R`: the kernel is
`≤ 3` on `‖w‖ < R/2`, so `|Re H w| ≤ 3 circleAverage |Re H|` there.  Borel-Caratheodory on
`ball 0 (R/2)` bounds `‖H‖` on `closedBall 0 (R/4)` by `O(R^p)`; two Cauchy estimates give
`‖H'' w‖ ≤ O(R^p)/R²` for `‖w‖ ≤ R/16`, so `H'' = 0` and `H z = a + b z`.  Evenness of `g`
forces `b = 0`, so `g` is constant and `f = c z^(2m) P₀`, which is `EvenHadamardData.ofHasProd`.

## 4. Module split (all `import Mathlib` only unless stated; each axiom-clean, no `sorry`)

| module | content | interface |
|---|---|---|
| `DBNHadamardCount.lean` | L3a | `summable_zero_multiplicity_rpow` |
| `DBNHadamardProduct.lean` | L3b product half | `evenProduct`, `hasProd_evenProduct`, `differentiable_evenProduct`, `norm_evenProduct_le`, `analyticOrderNatAt_evenProduct` |
| `DBNHadamardMean.lean` | L3c log + L3d | `exists_exp_eq_of_ne_zero`, `circleAverage_abs_re_le` |
| `DBNHadamardLinear.lean` | L3e | `eq_linear_of_circleAverage_abs_re_le` |
| `DBNHadamard.lean` | evenness of orders, representatives, enumeration, quotient, assembly | `evenHadamardData_of_order_lt_two` |
| `DBNHadamardApprox.lean` | `approxHadamard : ApproxHadamard`, `debruijn_real_zeros` | imports the island |

Exact interface statements are in the module headers.  Guard: every theorem gets a
`#print axioms` line in `AxiomGuardDBN.lean`.

## 5. What this does and does not prove

Proved (when done): de Bruijn's theorem `∀ t ≥ 1/2, ∀ z, H t z = 0 → z.im = 0`, i.e. the
de Bruijn-Newman constant satisfies `Λ ≤ 1/2`.  This says nothing about the zeros of `H 0`
inside the strip, which is where RH lives.  `conjecture1_proved = False`.
