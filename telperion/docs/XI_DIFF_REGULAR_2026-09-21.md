# Obligation 1 of the derivative partial fraction: the entire extension is PROVED, the growth bound named (E6Bridge20, 2026-09-21)

Status. `E6Bridge20.lean` (namespace `RvMBridge20`, imports E6Bridge15, E6Bridge18,
Zeta23.WeilEF.XiLogDeriv) proves, kernel-checked with axioms exactly
`[propext, Classical.choice, Quot.sound]` and no `sorry`, the two structural clauses of
`RvMBridge18.XiDiffRegular` (part A of the lead's plan): the regularised difference

    xiDiffReg s = deriv (logDeriv xi) s + Σ' m(ρ)/(s - ρ)²

extends across the nontrivial zeros to an ENTIRE function `xiDiffExt`, agreeing with `xiDiffReg`
off the zeros, and satisfying the functional equation `xiDiffExt (1 - s) = xiDiffExt s`. The third
clause, logarithmic growth, is carried as the named obligation `XiDiffExtGrowth` (def : Prop), with
a half-plane form `XiDiffExtGrowthRight` (Re s ≥ 1/2 only) proved sufficient. Assembly:
`xiDiffRegular_of : XiDiffExtGrowth → XiDiffRegular`, `xiDiffRegular_of_right`.
conjecture1_proved = False.

## What is proved and how

1. `xi_eq_zero_iff : xi s = 0 ↔ IsNontrivialZero s`. In the strip, ξ = s(s-1)/2·Λ and Zeta23's
   `completedZeta_zeros_strip`; for Re s ≥ 1, ζ and Γ_ℝ do not vanish and ξ(1) = 1/2; for Re s ≤ 0
   the functional equation `xi_one_sub`.
2. `analyticOrderAt_xi_eq : analyticOrderAt xi s = (zeroMult s : ℕ∞)` for EVERY s. At a zero:
   `analyticOrderAt_congr` + `analyticOrderAt_mul` (the factor s(s-1)/2 has order 0) +
   `completedZeta_zeros_strip.2` (order of Λ = order of ζ); the cast back from `toNat` uses that ξ
   is not locally zero anywhere (`analyticOrderAt_xi_ne_top`: identity theorem
   `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero` on ℂ against ξ(1) = 1/2).
   Off the zeros the order is 0 and so is the divisor.
3. `exists_ball_rest s₀`: the rest sum Σ'_{ρ≠s₀} m(ρ)/(w-ρ)² is `DifferentiableOn` a ball around s₀
   containing no other zero. Weierstrass M-test `differentiableOn_tsum_of_summable_norm` with the
   majorant `indicator(nearZeros s₀) (4m/ε²) + m·(13/4 + 2(|Im s₀|+1)²)/(1+|γ_ρ|²)`: the finitely
   many zeros within ordinate distance 2 (Zeta23 `zetaSeam.finite_window`) are at distance ≥ ε
   from s₀ (a ball avoiding the finite closed set), the others are handled by E6Bridge18's
   `norm_polTerm_le_majorant` uniformly in w (|Im w - Im s₀| ≤ 1) and E6Bridge6's local-count
   majorant.
4. `deriv_logDeriv_xi_local`: with ξ = (z-s₀)^m·u near s₀ (Mathlib
   `AnalyticAt.analyticOrderAt_eq_natCast`, u analytic, u(s₀) ≠ 0), on the punctured ball
   logDeriv ξ = m/(z-s₀) + logDeriv u (`logDeriv_mul`, `logDeriv_fun_pow`), hence
   deriv (logDeriv ξ) w = -m/(w-s₀)² + deriv (logDeriv u) w whenever (w-s₀)^m ≠ 0 (this covers
   w = s₀ when m = 0, i.e. s₀ not a zero).
5. `exists_local_form s₀`: r > 0 and H := deriv (logDeriv u) + rest sum, differentiable on the ball,
   with xiDiffReg = H on the punctured ball and at s₀ when s₀ is not a zero
   (`Summable.tsum_eq_add_tsum_ite` splits off the s₀ term m/(w-s₀)², which cancels the double pole
   EXACTLY).
6. `xiDiffExt s := if IsNontrivialZero s then limUnder (𝓝[≠] s) xiDiffReg else xiDiffReg s`;
   `xiDiffExt_eventuallyEq`: near every s₀, xiDiffExt = H (at a zero the punctured limit is H(s₀)
   by continuity, `Filter.Tendsto.limUnder_eq`); hence `xiDiffExt_differentiable`
   (`Filter.EventuallyEq.differentiableAt_iff`).
7. `xiDiffExt_one_sub`: logDeriv ξ(1-z) = -logDeriv ξ(z) for all z (chain rule on ξ(1-z) = ξ(z)),
   so deriv (logDeriv ξ)(1-s) = deriv (logDeriv ξ)(s) off the zeros (`HasDerivAt.unique`); the sum
   is invariant under ρ ↦ 1-ρ (`Equiv.tsum_eq` with m(1-ρ) = m(ρ) from E6Bridge6's
   `zeroMult_reflect` and E6Bridge15's `zeroMult_conj`); at a zero both sides are continuous and
   agree on a punctured neighbourhood (`tendsto_nhds_unique`).
8. `xiDiffExtGrowth_of_right`: a bound on Re s ≥ 1/2 transfers to all s by the functional equation,
   with constant C(1 + log 2) (log(2 + ‖1-s‖) ≤ log(2 + ‖s‖) + log 2).

## The obligation (growth), where it stopped and why

```lean
def XiDiffExtGrowth : Prop := ∃ C : ℝ, ∀ s : ℂ, ‖xiDiffExt s‖ ≤ C * (1 + Real.log (2 + ‖s‖))
def XiDiffExtGrowthRight : Prop :=
  ∃ C : ℝ, ∀ s : ℂ, 1 / 2 ≤ s.re → ‖xiDiffExt s‖ ≤ C * (1 + Real.log (2 + ‖s‖))
theorem xiDiffRegular_of (h : XiDiffExtGrowth) : XiDiffRegular
theorem xiDiffRegular_of_right (h : XiDiffExtGrowthRight) : XiDiffRegular
```

Content of the obligation (parts B and C of the plan), all on Re s ≥ 1/2:
- 1/2 ≤ Re s ≤ 2, |Im s| ≥ 6: Landau's local partial fraction (Zeta23
  `WeilEF.zeta_logDeriv_partial_fraction`: ζ'/ζ = Σ_{near} 1/(s-ρ) + O(log|t|) on discs of radius 3/2
  about 2 + it) plus logDeriv Γ_ℝ = O(log|t|) (Stirling) give logDeriv ξ − Σ_{near} 1/(w-ρ) = O(log|t|)
  on a disc of radius 1/2 about s; Cauchy's estimate bounds its derivative by O(log|t|); the far
  sum Σ_{|γ-t|>2} m/(s-ρ)² is O(log|t|) by the local count. None of the Cauchy-transfer or Stirling
  steps is on this island for the derivative.
- Re s ≥ 2: 1/s², 1/(s-1)², ψ'(s/2) = O(1/|s|) and the Dirichlet series of (ζ'/ζ)' (absolutely
  convergent, bounded); the sum is O(1) since |s-ρ| ≥ 1.
- The compact remainder 1/2 ≤ Re s ≤ 2, |Im s| < 6: continuity of the entire xiDiffExt.

The parallel agent `xi-decay` owns obligation 2 (`XiLogDerivDerivDecay`); nothing of it is
duplicated here.

## Files

- `telperion/examples/rvm_bridge/lean/E6Bridge20.lean`
- `telperion/examples/rvm_bridge/lean/Probes/E6Bridge20_probe.lean` (all green)
- `telperion/examples/rvm_bridge/lean/Probes/E6Bridge20_obligation_probe.lean` (expected FAILS)
- this memo

lakefile.toml, AxiomGuardRvMBridge.lean and existing modules untouched; olean emitted by hand.
Guard lines for the integrator:

```lean
#print axioms RvMBridge20.xiDiffExt_differentiable
#print axioms RvMBridge20.xiDiffExt_eq
#print axioms RvMBridge20.xiDiffExt_one_sub
#print axioms RvMBridge20.exists_local_form
#print axioms RvMBridge20.analyticOrderAt_xi_eq
#print axioms RvMBridge20.xiDiffRegular_of
```

## Pin footguns hit

- `logDeriv_mul` and `logDeriv_fun_pow` need `(f := ...)` made explicit, otherwise the
  higher-order unifier picks the wrong factorisation.
- `(hd1.add hd2).deriv` produces a `Pi.add` function; rewrite the lambda to `f + g` by `rfl` first.
- `Filter.Eventually.eventually_nhds` yields a membership, not an `EventuallyEq`; re-annotate with
  `have hz' : f =ᶠ[𝓝 z] g := hz` before using `.deriv_eq`.
- `ENat.coe_toNat` is deprecated for `ENat.natCast_toNat`; `Set.diff_subset` for `Set.sdiff_subset`.
- The triangle inequality `norm_sub_le_norm_sub_add_norm_sub a b c : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖`:
  choose the middle point as the ball centre's neighbour, not the centre.

## Probe output (lake env lean Probes/E6Bridge20_probe.lean)

```
'RvMBridge20.xiDiffExt_differentiable' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge20.xiDiffExt_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge20.xiDiffExt_one_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge20.exists_local_form' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge20.exists_ball_rest' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge20.xi_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge20.analyticOrderAt_xi_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge20.deriv_logDeriv_xi_local' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge20.xiDiffExtGrowth_of_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge20.xiDiffRegular_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge20.xiDiffRegular_of_right' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Obligation probe output (lake env lean Probes/E6Bridge20_obligation_probe.lean), all EXPECTED

```
Probes/E6Bridge20_obligation_probe.lean:8:29: error: unsolved goals     (XiDiffExtGrowth by simp, C = 1)
Probes/E6Bridge20_obligation_probe.lean:16:2: warning: aesop: failed to prove the goal after exhaustive search.
Probes/E6Bridge20_obligation_probe.lean:14:34: error: unsolved goals    (XiDiffExtGrowthRight by aesop)
Probes/E6Bridge20_obligation_probe.lean:19:31: error: unsolved goals    (not XiDiffExtGrowth)
Probes/E6Bridge20_obligation_probe.lean:24:39: error: unsolved goals    (XiDiffRegular from the extension alone)
```
