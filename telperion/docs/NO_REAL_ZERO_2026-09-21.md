# No real zero of zeta in (0, 1): E6Bridge25 (2026-09-21)

*Module `telperion/examples/rvm_bridge/lean/E6Bridge25.lean` (namespace `RvMBridge25`, imports
`E6Bridge19`, `E6Bridge22`, `Zeta23.FromPNTPlus.ZetaBounds`), probe `Probes/E6Bridge25_probe.lean`.
All eight delivered theorems: axioms exactly `[propext, Classical.choice, Quot.sound]`, no `sorry`,
no named Prop introduced. Nothing here says anything about whether RH holds.
**`conjecture1_proved = False`.***

## 1. What is proved

```lean
theorem re_riemannZeta_neg_of_unit_interval {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) : (riemannZeta σ).re < 0
theorem riemannZeta_ne_zero_of_unit_interval {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) : riemannZeta σ ≠ 0
theorem noRealZeroInUnitInterval : RvMBridge19.NoRealZeroInUnitInterval          -- E6Bridge19's Prop, verbatim
theorem liValue_of_partialFraction (hP : RvMBridge18.XiLogDerivDerivEq) (n) (hn : 0 < n) : LiValue n
theorem liValue_of_growth (h : RvMBridge20.XiDiffExtGrowthRight) (n) (hn : 0 < n) : LiValue n
theorem liValue_of_two (h1 : RvMBridge22.LocalCountSum) (h2 : RvMBridge22.StripDerivBound) (n) (hn) : LiValue n
theorem bl_explicit_formula_of_two h1 h2 n hn :
    Tendsto (liZeroSum n) atTop (nhds (archSide n + finiteSide n))                -- the node, verbatim
```

So the rh node `RH_bl_explicit_formula` (B7) now rests on exactly the two inequalities of E6Bridge22,
`LocalCountSum` and `StripDerivBound`; the real-segment fact that E6Bridge19 carried is gone.

## 2. The proof (not the Dirichlet-eta route)

The brief proposed the alternating series `(1 - 2^{1-σ}) ζ(σ) = Σ (-1)^{n+1} n^{-σ}`, which needs
either the analytic continuation of the eta series to `Re s > 0` or a real-analytic identity theorem,
neither available on this pin (Mathlib has `riemannZeta` series only for `Re s > 1`, and no
`dirichletEta`). Not needed: the island already carries the summation-by-parts representation of
the PrimeNumberTheoremAnd port (`Zeta0EqZeta`, `riemannZeta0`, valid for `Re s > 0`, `s ≠ 1`):

    ζ(s) = Σ_{n ≤ N} n^{-s} − N^{1−s}/(1−s) − N^{−s}/2 + s ∫_N^∞ (⌊x⌋ + 1/2 − x) x^{−s−1} dx.

At `N = 1`: `ζ(s) = 1/2 + 1/(s−1) + s·J(s)`, `J(s) = ∫_1^∞ (⌊x⌋ + 1/2 − x) x^{−s−1} dx`. For real
`σ > 0`, `|⌊x⌋ + 1/2 − x| ≤ 1/2` (`ZetaSum_aux1_3`) and `∫_1^∞ x^{−σ−1} dx = 1/σ`
(`integral_Ioi_rpow_of_lt`), so `‖J(σ)‖ ≤ 1/(2σ)` (`norm_tail_integral_le`, via
`norm_integral_le_of_norm_le` with the integrable majorant `(1/2) x^{−σ−1}`). Hence for `0 < σ < 1`

    Re ζ(σ) = 1/2 − 1/(1−σ) + σ·Re J(σ) ≤ 1/2 − 1/(1−σ) + 1/2 = 1 − 1/(1−σ) < 0.

Zeta23's own `norm_riemannZeta_le_of_re_pos` uses the cruder `‖J‖ ≤ 1/σ` (`ZetaBnd_aux1b`), which
only gives the sign for `σ > 1/3`; the factor `1/2` is what closes the whole interval. Total: 90
lines of Lean, no new analysis.

## 3. Probe checks

Beyond the axiom audit: the sign statement is exercised at `σ = 1/2` (`Re ζ(1/2) < 0`, so it is not
a junk-value artefact), contrasted with Mathlib's `riemannZeta_re_pos_of_one_lt` at `σ = 2`
(`Re ζ(2) > 0`, so the hypotheses are load-bearing); the node statement type-checks verbatim modulo
the two inequalities; `LiValue 0` is still false (the `0 < n` is not absorbed).

## 4. Not done

* `LocalCountSum` and `StripDerivBound` themselves (E6Bridge22, agent fourier).
* Registration: E6Bridge25 is not in `lakefile.toml` defaultTargets nor `AxiomGuardRvMBridge.lean`
  (not to be edited by this session); the olean was emitted by hand for the probe.
