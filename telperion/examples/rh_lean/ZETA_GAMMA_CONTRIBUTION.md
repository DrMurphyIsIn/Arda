# ζ / Γ-derivative numerics: precise Mathlib contribution spec

Grounded in three CI API probes against **Mathlib v4.32.0** (not memory). This is
a *spec + strategy*, honest about what is done, what already exists upstream, and
what remains genuine analytic-formalization work. It ships **no proofs of the
blocked lemmas**.

## What already exists in Mathlib v4.32.0 (probe-confirmed)

| Fact | Name |
|---|---|
| `3 < π`, `π < 4` | `Real.pi_gt_three`, `Real.pi_lt_four` (the decimal `pi_gt_314` etc. do **not** exist) |
| `Γ(1/2) = √π` | `Real.Gamma_one_half_eq` |
| **`1/2 < γ < 2/3`** | `Real.one_half_lt_eulerMascheroniConstant`, `Real.eulerMascheroniConstant_lt_two_thirds` — **both bounds already present** |
| `γ = lim eulerMascheroniSeq`, `seq n < γ < seq' n` | `Real.tendsto_eulerMascheroniSeq`, `eulerMascheroniSeq_lt_eulerMascheroniConstant`, `eulerMascheroniConstant_lt_eulerMascheroniSeq'` |
| `log 2` decimal bounds | `Real.log_two_lt_d9`, `Real.log_two_gt_d9` |
| Γ differentiable | `Real.differentiableAt_Gamma`, `Real.GammaSeq` |
| completed ζ + representation | `completedRiemannZeta`, `completedRiemannZeta_eq`, `completedRiemannZeta₀`, `completedRiemannZeta_one_sub` |
| Jacobi theta | `jacobiTheta` |

**Done in-kernel here:** `Real.sqrt` brackets (`SqrtBracketCertificate`) and
`1.7 ≤ Γ(1/2) ≤ 2` (`GammaHalfBracketCertificate`, from `Γ(1/2)=√π` + `3<π<4`).

## The genuine gaps (probe-confirmed MISSING)

Nothing named `digamma`, `deriv_Gamma`, `deriv_logGamma`, `hasDerivAt_Gamma`;
no `hurwitzZeta`; no numeric bound lemma on `riemannZeta`/`completedRiemannZeta`.
So the deep numerics reduce to **two** self-contained upstream contributions:

### Contribution A — the Γ-derivative / digamma API (medium)

The values `deriv Real.Gamma (1/2)` and `a_k` are opaque without a derivative
*formula*. Needed:

```lean
noncomputable def Real.digamma (x : ℝ) : ℝ := deriv Real.Gamma x / Real.Gamma x
theorem Real.deriv_Gamma (x : ℝ) (hx : ∀ n : ℕ, x ≠ -n) :
    deriv Real.Gamma x = Real.digamma x * Real.Gamma x           -- from Gamma_ne_zero
theorem Real.digamma_one_half :
    Real.digamma (1/2) = -Real.eulerMascheroniConstant - 2 * Real.log 2
```
The first two are light (once `Gamma_ne_zero` is located). **`digamma_one_half`
is the real work** — it needs the digamma reflection/series, which Mathlib does
not have; this is the crux of Contribution A. Once it lands, `Γ'(1/2)` brackets
immediately from the *existing* `1/2 < γ < 2/3` and `log 2` bounds:

```
Γ'(1/2) = √π · (−γ − 2 log 2) ∈ √π · (−2.053, −1.886) ⊂ (−4.11, −3.20)
```
i.e. `Real.deriv_Gamma`-then-bracket is a Telperion `nlinarith` job over
`GammaHalf` + `one_half_lt_eulerMascheroniConstant` + `log_two_*` — **all present**.
*So the only missing analytic lemma for `Γ'(1/2)` numerics is `digamma_one_half`.*

### Contribution B — a ζ(1/2) numeric bound (harder)

`riemannZeta (1/2)` has no numeric API. The convergent handle that DOES exist is
`completedRiemannZeta₀` (entire; `completedRiemannZeta_eq` ties it to `riemannZeta`)
built on `jacobiTheta`. Strategy:
1. `completedRiemannZeta₀ s = ∫_1^∞ (…)·(θ(x)−1) dx` — needs the Mellin/theta
   integral form exposed as an equational lemma (Mathlib has the analytic content
   via `jacobiTheta`; a usable integral identity may need extraction).
2. Bound the integrand by `θ(x)−1 ≤ 2·e^{−πx}/(1−e^{−πx})` (geometric tail on the
   theta series) — a new inequality lemma.
3. Rigorous rational bound of `∫_1^∞ x^{−3/4}·(geom tail) dx` → `completedRiemannZeta₀(1/2)`
   bracket → `ζ(1/2)` via `completedRiemannZeta_eq` (dividing by the *bracketed*
   `π^{-1/4}Γ(1/4)` — which reintroduces `Γ(1/4)`, itself un-closed-form).

Step 3's `Γ(1/4)` dependency is why `ζ(1/2)` is strictly harder than `Γ'(1/2)`.

### `a_k` (research-scale)

`a_k = [z^{2k}] ξ(1/2+z)` needs *derivatives* `ζ^{(j)}(1/2)`, `Γ^{(j)}(1/4)` — i.e.
Contribution A generalized to all orders **plus** B with derivatives. This is a
multi-file upstream project, realistically its own Mathlib PR series.

## Honest status

- **Reachable now, verified:** `√`, `Γ(1/2)` in-kernel; γ/log2/π bounds already
  upstream.
- **One focused analytic lemma from `Γ'(1/2)`:** `Real.digamma_one_half` (the
  digamma special value). Everything else for `Γ'(1/2)` numerics is present.
- **`ζ(1/2)`:** two/three new analytic lemmas (theta tail + integral bound + the
  `Γ(1/4)` handle). Genuinely a focused formalization, not a session task.
- **`a_k`:** research-scale.

This document is the spec; the blocked lemmas are **not** proved here
(`conjecture1_proved=False`). Writing them correctly needs an environment where
Lean can be iterated locally — the CI-only, review-bound path can *start* these
but not responsibly land novel analytic proofs blind.
