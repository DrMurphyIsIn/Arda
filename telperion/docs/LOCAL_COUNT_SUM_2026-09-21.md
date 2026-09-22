# The local-count sum Σ_ρ m(ρ)/(1 + (Im ρ - a)²) = O(log(2 + |a|)) -- LocalCountSum discharged (E6Bridge23, 2026-09-21)

Status. `E6Bridge23.lean` (namespace `RvMBridge23`, imports E6Bridge22) proves

```lean
theorem local_count_sum : RvMBridge22.LocalCountSum
-- i.e. ∃ C, ∀ a : ℝ, ∑' ρ : ℂ, lcTerm a ρ ≤ C * (1 + Real.log (2 + |a|)),
--      lcTerm a ρ := (zeroMult ρ : ℝ) / (1 + (ρ.im - a)^2)
```

kernel-clean: axioms exactly `[propext, Classical.choice, Quot.sound]`, no `sorry`, no named
obligation on this side. With E6Bridge22's assembly, the growth bound of the entire extension and
the derivative partial fraction of ξ'/ξ now rest on StripDerivBound alone:

```lean
theorem xiDiffExtGrowthRight_of_strip (h2 : RvMBridge22.StripDerivBound) : RvMBridge20.XiDiffExtGrowthRight
theorem xiLogDerivDerivEq_of_strip (h2 : RvMBridge22.StripDerivBound) : RvMBridge18.XiLogDerivDerivEq
```

Nothing here bears on RH. conjecture1_proved = False.

## The argument

The textbook Σ_ρ 1/(1 + (t - γ)²) = O(log t) from the local zero count, done on finite partial
sums so that no fiberwise tsum machinery is needed.

**Input.** `Zeta23.RvM.zeta_local_zero_count : ∃ A₀, 1 ≤ A₀ ∧ ∀ t, Ncount t (t+1) ≤ A₀ log(|t| + 3)`,
with `Ncount T₁ T₂ = ∑ᶠ ρ ∈ zerosIn T₁ T₂, zeroMult ρ` the multiplicity count over the half-open
ordinate window (T₁, T₂]. This is the only zero-theoretic input.

**Fibers.** For a Finset u of points, drop the non-zeros (`lcTerm = 0` there), and regroup the rest
by k := ⌈Im ρ - a⌉ ∈ ℤ (`Finset.sum_fiberwise_of_maps_to`). The ceiling, not the floor, so that the
fiber sits in exactly one half-open unit window: k - 1 < Im ρ - a ≤ k, i.e. ρ ∈ zerosIn (a+k-1) (a+k).

* `one_add_sq_le_of_ceil`: on the fiber, 1 + k² ≤ 4 (1 + (Im ρ - a)²), so
  `lcTerm_le_fiber_weight : lcTerm a ρ ≤ m(ρ) · 4/(1 + k²)`.
* `sum_zeroMult_fiber_le`: the multiplicity sum over the fiber is ≤ Ncount (a+k-1) (a+k)
  (subset of the finite window `Zeta23.zerosIn_finite`, `finsum_mem_eq_finite_toFinset_sum`; the
  registry multiplicity `WeilExplicit.zeroMult` equals `Zeta23.zeroMult` on the carrier via
  `RvMBridge4.zeroMult_eq_mult`).
* Hence the fiber contributes ≤ wcount A₀ a k := 4/(1+k²) · A₀ log(|a| + |k| + 4)
  (|a + k - 1| + 3 ≤ |a| + |k| + 4).

**The ℤ-series.** log(|a| + |k| + 4) ≤ log(2 + |a|) + log(|k| + 4) since |a|+|k|+4 ≤ (2+|a|)(|k|+4), so
wcount A₀ a k ≤ 4A₀ (log(2+|a|) · wt k + wlog k) with wt k = 1/(1+k²), wlog k = log(|k|+4)/(1+k²).

* `summable_wt`: eventually (k ≠ 0) wt k ≤ 1/k², `Real.summable_one_div_int_pow`.
* `summable_wlog`: eventually wlog k ≤ 6 |k|^{-3/2}, `Real.summable_abs_int_rpow`. The pointwise
  bound `log_div_le_rpow` comes from log(y+4) ≤ 6√y for y ≥ 1 (`log_add_four_le`: log t ≤ t - 1 at
  t = √(y+4) and y + 4 ≤ 9y) and y^{-3/2} = 1/(y√y).

**Assembly.** `sum_lcTerm_le`: every finite sum ≤ Σ'_k wcount A₀ a k (`Summable.sum_le_tsum`);
`tsum_wcount_le`: that ≤ 4A₀ (log(2+|a|) S1 + S2) with S1 = Σ' wt, S2 = Σ' wlog (absolute constants,
nonnegative); `Real.tsum_le_of_sum_le` gives the tsum bound; C := 4A₀ (S1 + S2) since
log(2+|a|) S1 + S2 ≤ (S1 + S2)(1 + log(2+|a|)).

## Signatures

```lean
theorem sum_lcTerm_le (A₀ : ℝ) (hA₀ : 0 ≤ A₀)
    (hloc : ∀ t : ℝ, (Ncount t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) (a : ℝ) (u : Finset ℂ) :
    ∑ ρ ∈ u, lcTerm a ρ ≤ ∑' k : ℤ, wcount A₀ a k
lemma sum_zeroMult_fiber_le (a : ℝ) (k : ℤ) (u : Finset ℂ)
    (hu : ∀ ρ ∈ u, IsNontrivialZero ρ ∧ ⌈ρ.im - a⌉ = k) :
    ∑ ρ ∈ u, (WeilExplicit.zeroMult ρ : ℝ) ≤ (Ncount (a + k - 1) (a + k) : ℝ)
lemma log_div_le_rpow {y : ℝ} (hy : 1 ≤ y) : Real.log (y + 4) / (1 + y ^ 2) ≤ 6 * y ^ (-(3 / 2 : ℝ))
```

## Verification

`lake env lean E6Bridge23.lean` clean; `lake env lean Probes/E6Bridge23_probe.lean` prints the axiom
list above for the eight delivered names and shows the target is neither simp/aesop-closable nor
simp-refutable (expected failures). The module is not yet in `lakefile.toml` defaultTargets nor in
AxiomGuardRvMBridge (not edited by this agent); its olean was emitted with `lake env lean -o` for
the probe. To wire: add `"E6Bridge23"` to defaultTargets, a `[[lean_lib]] name = "E6Bridge23"`
stanza, and the names above to the guard.

## What is NOT here

Nothing about StripDerivBound (the Landau-Cauchy disc bound on the strip), which is now the single
remaining obligation of the E6Bridge18/20/22 chain. Nothing about RH. conjecture1_proved = False.
