# RH zero-free formalization — session consolidation (2026-09-01)

`conjecture1_proved = False`. This is classical-analysis formalization, NOT progress on RH. This doc ties
together the full arc of the zero-free-region work on `rh-research-artifacts` and states the honest ceiling.

## Headline result (kernel-verified, sorry-free, merged)

**`riemannZeta_zero_free_poly`** (`telperion/examples/zero_free_bridge/lean/ZeroFreeElementary.lean`, PR #180):

```lean
∃ c > 0, ∀ β γ : ℝ, riemannZeta (β + γ*I) = 0 → 2 ≤ γ → β ≤ 1 - c / γ^5
```

i.e. `Re s > 1 - c/|t|^5` is **zero-free** for `ζ` — the project's **first fully UNCONDITIONAL** zeta
zero-free region. Prior results were only the boundary (`ζ(1+it)≠0`, already in Mathlib via
`riemannZeta_ne_zero_of_one_le_re`) or CONDITIONAL on the Hadamard machinery.

## The key idea: go AROUND the Hadamard wall

The sharp de la Vallée Poussin region `1 - c/log|t|` needs the sum-over-zeros expansion of `ζ'/ζ`, hence
the Hadamard factorization of `ξ` — which requires **Jensen's formula → n(r)=O(r log r) → canonical
products**, and every one of those is ABSENT from Mathlib v4.32.0 (verified: 0 hits). That backbone is a
`PrimeNumberTheoremAnd`-scale effort, out of incremental scope.

Instead, the elementary route uses only tools that are present or already built:

| Ingredient | Source | Lemma |
|---|---|---|
| `\|ζ(σ)³ζ(σ+it)⁴ζ(σ+2it)\| ≥ 1` | Mathlib `DirichletCharacter.norm_LFunction_product_ge_one` (mod 1, `LFunction_modOne_eq`) | `zeta_norm_product_ge_one` |
| `\|ζ(σ)\| ≤ 2/(σ-1)` (pole) | Mathlib `riemannZeta_residue_one` | `zeta_pole_bound` |
| `\|ζ(σ+it)\| ≤ C·\|t\|` (crude growth) | **Phase 2** (this branch) | `zeta_strip_bound` |
| `\|ζ(σ+iγ)\| ≤ (σ-β)·sup\|ζ'\|` | Cauchy est. + segment mean-value | `zeta_sphere_bound`→`zeta_deriv_bound`→`zeta_hcauchy` |

Choosing `σ = 2-β` collapses the optimization to INTEGER powers, avoiding fractional-power calculus. The
far-from-line case is handled by `riemannZeta_ne_zero_of_one_le_re`.

## The full verified chain (all sorry-free)

1. **Input R** (PR #177): `zeta_repr_R1` (Abel-summation fractional-part representation on `Re s>1`) +
   `zeta_fract_repr` (unconditional, assembled from R1+R2+R3 via `zeta_fract_repr_of`).
2. **Phase 2** (`StripBound.lean`): `zeta_strip_bound` — the crude strip growth bound, unconditional.
3. **Elementary region** (`ZeroFreeElementary.lean`, PR #180): the 4 bounds + assembly `zeta_zero_free_poly_of`
   + `riemannZeta_zero_free_poly`.
4. **Phase-4 conditional dVP core** (`ZeroFreeRegion.lean`): `dlvp_core_estimate` + `dlvp_region_gap` — the
   quantitative dVP estimate, conditional on the Borel-Caratheodory log-derivative bounds (the Hadamard
   frontier, isolated as hypotheses); arithmetic independently verified to reproduce the classical `0.01436`.
   Also `BorelCaratheodory.lean` (12 thm) green — the missing-from-v4.32.0 BC theorem.

## Honest ceiling (do not lose)

- Polynomial rate `|t|^{-5}` is **WEAKER** than dVP's `1 - c/log|t|`. The crude `|ζ| ≤ C|t|` growth (not the
  sharp `log|t|`) is exactly what costs the rate. Unconditional + Hadamard-free is what made it in-scope.
- NOT a proof of RH; NOT a step toward it. `conjecture1_proved = False`.

## Upgrade paths (for the next session)

1. **Improve the rate to near-dVP**: replace the crude `|ζ| ≤ C|t|` with the sharp near-line
   `|ζ(σ+it)| ≪ log|t|` (Euler-Maclaurin, `N ∼ |t|`). Feeds the SAME elementary skeleton → improves the
   exponent from `|t|^{-5}` toward the log-region. This is the highest-value, in-scope next step.
2. **Sharp dVP `1 - c/log|t|`**: still needs the Hadamard backbone (Jensen → canonical products → `ζ'/ζ`
   partial fraction). A distinct `PrimeNumberTheoremAnd`-scale sub-project; or wait for that to land in
   Mathlib, after which `dlvp_core_estimate`'s three BC hypotheses collapse to a short derivation.
3. **Upstream** `riemannZeta`-independent pieces (`residue_logDeriv`, Borel-Caratheodory) to Mathlib.

## Lean gotchas hit this session (v4.32.0)

`div_le_div_iff` removed → `div_le_iff₀`+`div_mul_eq_mul_div`+`le_div_iff₀`; `pow_le_pow_left` → `gcongr`;
`norm_add_le _ _` needs explicit args (else `SeminormedAddGroup ?m` stuck); `open` does not cross imports
(filter notation `𝓝`/`∀ᶠ`); `nlinarith` is degree ≤ 2 (`γ^5 ≥ 32` via `gcongr`); implicit args on applied
lemmas become metavars (`zeta_strip_2t_bound (β := β)`); `Complex.norm_ofNat`/`Complex.norm_real` don't hit
`‖(2:ℂ)‖` — use `simp`; a common subterm rewrite (`he0`) hits ALL occurrences.
