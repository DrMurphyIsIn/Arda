# StripDerivBound DISCHARGED: the Landau-Cauchy bound on the strip (E6Bridge24, 2026-09-21)

Status. `E6Bridge24.lean` (namespace `RvMBridge24`, imports E6Bridge22, Zeta23.WeilEF.Landau,
Zeta23.GammaFacts.StirlingVert, Zeta23.RvM.GammaSide) proves `RvMBridge22.StripDerivBound`
kernel-clean, axioms exactly `[propext, Classical.choice, Quot.sound]`, no `sorry`:

```lean
theorem stripDerivBound : StripDerivBound
theorem xiDiffExtGrowthRight_of_localCount (h1 : LocalCountSum) : XiDiffExtGrowthRight
theorem xiLogDerivDerivEq_of_localCount (h1 : LocalCountSum) : RvMBridge18.XiLogDerivDerivEq
```

So the growth bound of the entire extension, obligation 1 of E6Bridge18, and the derivative
partial fraction of ξ'/ξ now rest on ONE remaining input, `LocalCountSum` (the classical
Σ_ρ m(ρ)/(1+(γ−a)²) = O(log(2+|a|)), owned by xi-decay's E6Bridge23). Composed with E6Bridge19's
Taylor assembly (probe `E6Bridge22_taylor_probe`), the B7 value half needs only LocalCountSum and
xi-taylor's `NoRealZeroInUnitInterval`. conjecture1_proved = False.

## The target

```
∃ C, ∀ s, 1/4 ≤ Re s → Re s ≤ 9/4 → 5 ≤ |Im s| → ¬ IsNontrivialZero s →
  ‖deriv (logDeriv xi) s + Σ_{ρ ∈ window s} m(ρ)/(s−ρ)²‖ ≤ C (1 + log(2 + |Im s|))
```

with `window s` the nontrivial zeros with |Im ρ − Im s| ≤ 2.

## Two adjustments to the lead's plan

1. **Landau's window vs ours.** Zeta23's `zeta_logDeriv_partial_fraction` at height t collects the
   zeros in the closed ball of radius 22/25·91/50 ≈ 1.6016 about 2+it, and the estimate holds on the
   ball of radius 3/2 about 2+it. At a circle point w (|w − s| ≤ 1/2) with t = Im w, Landau's set Z
   is NOT contained in `window s` (1.6016 + 0.5 > 2), so the symmetric difference has two parts,
   both bounded: zeros in Z outside the window have |Im ρ − Im w| > 3/2 (term ≤ 2/3), zeros in
   the window outside Z are at distance > 1.6 from 2+it while w is within 3/2 of it (term ≤ 10);
   the multiplicities are bounded by Landau's own count and by the window count.
2. **Low heights.** Landau needs |t| ≥ 6 at every circle point, i.e. |Im s| ≥ 13/2, but the target
   starts at |Im s| = 5. For |Im s| ≤ 7 no Landau is used: off the zeros the target equals
   `xiDiffExt s − Σ_{ρ ∉ window s} m/(s−ρ)²`, bounded by the compact bound of the entire xiDiffExt
   on 1/4 ≤ Re s ≤ 9/4, |Im s| ≤ 7 and E6Bridge22's far-sum comparison (the local-count sum at a
   fixed height is bounded by (13/4 + 2a²)·Σ m/(1+|γ|²)).

## The proof, section by section

- **A. Window count** (`exists_window_bound`): Σ_{window s} m ≤ 5A₀ log(|Im s| + 6). The window is
  covered by five unit windows (Im ρ ∈ (a+k, a+k+1], k = −3..1, via ⌈Im ρ − a⌉); each unit window's
  multiplicity is a Finset subset of Zeta23's `zerosIn`, hence ≤ `Ncount` ≤ A₀ log(|t|+3)
  (`Zeta23.RvM.zeta_local_zero_count`), with WeilExplicit.zeroMult = Zeta23.zeroMult on the strip.
- **B. Digamma** (`norm_digamma_le_log`): ‖ψ(z)‖ ≤ log(2+|Im z|) + π + 7/2 for 0 < Re z ≤ 2,
  |Im z| ≥ 1, from `Zeta23.StirlingVert.digamma_stirling` (‖ψ(w) − log w + 1/(2w)‖ ≤ 3/(Im w)²)
  and ‖log z‖ ≤ log‖z‖ + π.
- **C. Landau repackaged** (`landau_window`): a finite set Z of nontrivial zeros with the count and
  remainder bounds, plus the two membership facts used in the symmetric-difference estimate.
- **D. The disc function.** `Fwin s w := logDeriv xi w − Σ_{window s} m/(w−ρ)`; `FwinExt` takes the
  punctured limit at zeros. `logDeriv_xi_local` (from E6Bridge20's unit factor) gives
  logDeriv ξ = m₀/(z−w₀) + logDeriv u near a zero w₀, so Fwin = logDeriv u − Σ_{window∖{w₀}} near
  w₀, analytic: `FwinExt_differentiableOn (s) : DifferentiableOn ℂ (FwinExt s) (ball s (1/2))`.
  `deriv_FwinExt`: deriv (FwinExt s) s = the target. `exists_radius`: an r ∈ (1/4, 1/2) whose circle
  avoids the finitely many zeros in the disc (`Set.Ioo_infinite`, `exists_notMem_finset` on the
  image of the window under dist · s). `norm_deriv_FwinExt_le`: Cauchy
  (`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`, `DifferentiableOn.diffContOnCl`).
- **E. Reflection** (`Fwin_one_sub`): Fwin (1−s) (1−w) = −Fwin s w (E6Bridge20's
  `logDeriv_xi_one_sub`, `window (1−s) = image (1 − ·) (window s)`, `zeroMult_one_sub`).
- **F. The core estimate** (`Fwin_bound_core`): for |w − s| ≤ 1/2, 1/2 ≤ Re w ≤ 7/2, |Im w| ≥ 6, w
  not a zero, ‖Fwin s w‖ ≤ K(1 + log(2+|Im s|)). Fwin s w = [1/w + 1/(w−1)] + [−(log π)/2 +
  (1/2)ψ(w/2)] + [ζ'/ζ(w) − Σ_Z] + Σ_{Z∖W} − Σ_{W∖Z} (E6Bridge18's `logDeriv_xi_eq`, Zeta23's
  `logDeriv_completedZeta` and `RvM.logDeriv_Gammaℝ`, `Finset.sum_sdiff` twice); the five pieces
  are bounded by 1/3, (log π)/2 + (π+7/2)/2 + L/2, C(log 2 + L), (2/3)C(log 2 + L), 10A(log 3 + L),
  with L = log(2+|Im s|) (log(|Im w|+3) ≤ L + log 2, log(|Im s|+6) ≤ L + log 3).
- **G. Sphere bound and high heights** (`sphere_bound`, `target_bound_high`): for Re w < 1/2 the
  reflection reduces to the core at 1−w (Re(1−w) ∈ (1/2, 5/4]); then Cauchy with 1/r ≤ 4 gives
  the target ≤ 4K(1+L) for |Im s| ≥ 13/2.
- **H. Low heights** (`target_bound_low`): as in adjustment 2.
- **I. Assembly** (`stripDerivBound`): C = K_low + 4K.

## Files

- `telperion/examples/rvm_bridge/lean/E6Bridge24.lean`
- `telperion/examples/rvm_bridge/lean/Probes/E6Bridge24_probe.lean` (all green)
- `telperion/examples/rvm_bridge/lean/Probes/E6Bridge24_obligation_probe.lean` (expected FAILS on
  LocalCountSum, and that StripDerivBound alone does not give the growth)
- this memo

lakefile.toml, AxiomGuardRvMBridge.lean and existing modules untouched; olean emitted by hand.
Guard lines for the integrator:

```lean
#print axioms RvMBridge24.stripDerivBound
#print axioms RvMBridge24.xiDiffExtGrowthRight_of_localCount
#print axioms RvMBridge24.xiLogDerivDerivEq_of_localCount
#print axioms RvMBridge24.Fwin_bound_core
#print axioms RvMBridge24.FwinExt_differentiableOn
#print axioms RvMBridge24.exists_window_bound
```

## Pin footguns hit

- `DifferentiableAt.sum` concludes with the Pi-form sum `∑ i ∈ u, A i`; rewrite the pointwise sum
  to that form first (`funext; simp [Finset.sum_apply]`) and pass `(𝕜 := ℂ)`, `(u := ...)`,
  `(A := ...)` explicitly, or the instance search sticks on `NormedSpace ?m ?m`.
- `HasDerivAt.div` states its function as `c / d` (Pi division); `congr_deriv` still unifies, but
  use `hasDerivAt_id'` so that no `id` survives into the `ring` goal.
- `mem_ball_self` needs the `Metric.` prefix here (ambiguity once more namespaces are open).
- `Complex.div_im`/`div_re` simp normal forms are fragile; write w/2 as `((1/2 : ℝ) : ℂ) * w` and
  use `re_ofReal_mul` / `im_ofReal_mul`.
- The final constant assembly: keep it as `a + b·L ≤ (a + b)(1 + L)` with `nlinarith` on the
  small lemma, not one big `nlinarith` over the whole expression (heartbeat timeout).
- Landau's ball radius 22/25·91/50 = 1.6016 is above 8/5; state the inclusion as ≤ 161/100.

## Probe output (lake env lean Probes/E6Bridge24_probe.lean)

```
'RvMBridge24.stripDerivBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge24.xiDiffExtGrowthRight_of_localCount' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge24.xiLogDerivDerivEq_of_localCount' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge24.exists_window_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge24.norm_digamma_le_log' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge24.landau_window' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge24.FwinExt_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge24.deriv_FwinExt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge24.exists_radius' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge24.norm_deriv_FwinExt_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge24.Fwin_one_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge24.Fwin_bound_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge24.sphere_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge24.target_bound_high' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge24.target_bound_low' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Obligation probe output (lake env lean Probes/E6Bridge24_obligation_probe.lean), all EXPECTED

```
Probes/E6Bridge24_obligation_probe.lean:10:34: error: unsolved goals   (growth from StripDerivBound alone)
Probes/E6Bridge24_obligation_probe.lean:16:27: error: unsolved goals   (LocalCountSum, C = 1, simp)
Probes/E6Bridge24_obligation_probe.lean:23:2: error: Tactic `aesop` failed, made no progress  (LocalCountSum, aesop)
Probes/E6Bridge24_obligation_probe.lean:26:29: error: unsolved goals   (not LocalCountSum)
```
