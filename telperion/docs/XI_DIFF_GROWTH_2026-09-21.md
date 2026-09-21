# The growth bound of the entire extension: framework and right half-plane PROVED, two inequalities named (E6Bridge22, 2026-09-21)

Status. `E6Bridge22.lean` (namespace `RvMBridge22`, imports E6Bridge20 and E6Bridge21) reduces
`RvMBridge20.XiDiffExtGrowthRight` to TWO named real inequalities and proves everything else,
kernel-checked with axioms exactly `[propext, Classical.choice, Quot.sound]`, no `sorry`:

- `xiDiffExtGrowthRight_of_two (h1 : LocalCountSum) (h2 : StripDerivBound) : XiDiffExtGrowthRight`
- `xiLogDerivDerivEq_of_two h1 h2 : RvMBridge18.XiLogDerivDerivEq` (the derivative partial
  fraction of ξ'/ξ, with E6Bridge18's Liouville skeleton, E6Bridge20's entire extension and
  E6Bridge21's real-axis decay all composed in)
- `rightDerivBound : RightDerivBound` (region C's derivative bound, DISCHARGED)

conjecture1_proved = False. Nothing here bears on RH.

## A correction to the plan

On Re s ≥ 2 the sum `Σ m(ρ)/(s-ρ)²` is NOT O(1): near the ordinate of a zero the term is of size
1/(Re s − β)² ≈ 1, and there are O(log t) zeros per unit height, so the sum is O(log|Im s|). The
plan's "≤ Σ m/(1+|γ|²)·C" bound is false uniformly in Im s. Both regions B and C therefore rest on
the same classical inequality, stated once as `LocalCountSum`.

## The two obligations

```lean
def lcTerm (a : ℝ) (ρ : ℂ) : ℝ := (WeilExplicit.zeroMult ρ : ℝ) / (1 + (ρ.im - a) ^ 2)
def LocalCountSum : Prop :=
  ∃ C : ℝ, ∀ a : ℝ, ∑' ρ : ℂ, lcTerm a ρ ≤ C * (1 + Real.log (2 + |a|))

def StripDerivBound : Prop :=
  ∃ C : ℝ, ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 9 / 4 → 5 ≤ |s.im| → ¬ IsNontrivialZero s →
    ‖deriv (logDeriv xi) s + ∑ ρ ∈ window s, (WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2‖
      ≤ C * (1 + Real.log (2 + |s.im|))
```

`window s` is the Finset of nontrivial zeros with |Im ρ − Im s| ≤ 2 (finite by Zeta23
`zetaSeam.finite_window`). Summability of `lcTerm a` for every a is PROVED (`summable_lcTerm`,
by the majorant (13/4 + 2a²)/(1+|γ_ρ|²) and E6Bridge6's local-count summability).

- **LocalCountSum** is the textbook `Σ_ρ 1/(1+(t−γ)²) = O(log t)`: from Zeta23's
  `RvM.zeta_local_zero_count` (N(t, t+1] ≤ A₀ log(|t|+3)), regroup the sum into unit windows
  [a+k, a+k+1) with weights ≤ 1/(1+(|k|−1)²) and sum `A₀ log(|a|+|k|+3)/(1+(|k|−1)²)` over k ∈ ℤ.
  The Lean cost is the fiberwise regrouping of a tsum over ℂ (`HasSum.tsum_fiberwise`) and the
  identification of each fiber sum with Zeta23's `Ncount` (a finsum over `zerosIn`).
- **StripDerivBound** is Landau's local partial fraction (`Zeta23.WeilEF.zeta_logDeriv_partial_fraction`,
  |t| ≥ 6, on the disc of radius 3/2 about 2+it, remainder O(log(|t|+3))) plus the Stirling bound
  for logDeriv Γ_ℝ and the rational factors, transferred to the DERIVATIVE by Cauchy's estimate on
  a disc of radius 1/2 about s, with the window mismatch (Landau's window is |γ−t| ≤ 1.6 about the
  centre; ours is |γ − Im s| ≤ 2) absorbed by the local count. Two Lean obstacles: the remainder
  R(w) = logDeriv ξ(w) − Σ_window m/(w−ρ) has junk values at the window zeros (it must be replaced
  by logDeriv(ξ/Π(w−ρ)^m), analytic on the disc, before Cauchy applies), and for 1/4 ≤ Re s < 1/2
  the disc leaves Landau's ball, so the functional equation must be used pointwise
  (R(w) = −R̃(1−w)). It is stated on the closed region 1/4 ≤ Re s ≤ 9/4, |Im s| ≥ 5 (a superset
  whose interior contains region B) so that the bound passes to the zeros by continuity.

## What is proved

1. `summable_lcTerm (a)`.
2. `norm_polTerm_le_lcTerm_right (hs : 2 ≤ s.re) (ρ) : ‖polTerm s ρ‖ ≤ lcTerm s.im ρ` (|s−ρ|² ≥ 1 +
   (Im s − Im ρ)² since Re s − Re ρ ≥ 1) and `norm_tsum_polTerm_le_right`.
3. `norm_polTerm_le_lcTerm_far (hρ : ρ ∉ window s) : ‖polTerm s ρ‖ ≤ 2 lcTerm s.im ρ` and
   `norm_tsum_far_le (s) : ‖Σ'_{ρ ∉ window s} polTerm s ρ‖ ≤ 2 Σ' lcTerm s.im`
   (`Summable.sum_add_tsum_compl`, `Summable.tsum_subtype_le`).
4. `bound_of_bound_off_zeros`: a continuous bound on an open set valid off the zeros holds on all
   of it (E6Bridge20's punctured balls of non-zeros around each zero, `ge_of_tendsto` along 𝓝[≠]).
5. `growth_compact` (region A: `IsCompact.bddAbove_image` on the rectangle
   `Icc (1/2) 2 ×ℂ Icc (-6) 6`), `growth_right (h1) (h3)` (region C), `growth_strip_off_zeros (h1) (h2)`
   and `growth_strip (h1) (h2)` (region B, then closed by 4.), `xiDiffExtGrowthRight_of (h1 h2 h3)`
   (constant max of the three, log(2+|Im s|) ≤ log(2+‖s‖)).
6. **Region C's derivative bound, `rightDerivBound`**: `deriv_logDeriv_xi_of_one_lt_re` (complex
   argument, E6Bridge21's real-axis proof verbatim): deriv (logDeriv ξ)(s) = −1/s² − 1/(s−1)² +
   (1/4)ψ'(s/2) + (ζ'/ζ)'(s) on Re s > 1; then ‖1/s²‖ ≤ 1/4, ‖1/(s−1)²‖ ≤ 1,
   ‖ψ'(z)‖ ≤ Σ 1/(n+1/2)² for Re z ≥ 1 (`norm_deriv_digamma_le`, E6Bridge21's
   `hasSum_trigamma_of_re_pos` and `norm_trigTerm_le`), and ‖(ζ'/ζ)'(s)‖ ≤ Σ_n ‖term(log·Λ)(2) n‖
   for Re s ≥ 2 (`norm_deriv_logDeriv_zeta_le`, E6Bridge21's `deriv_logDeriv_zeta_eq`).

## Files

- `telperion/examples/rvm_bridge/lean/E6Bridge22.lean`
- `telperion/examples/rvm_bridge/lean/Probes/E6Bridge22_probe.lean` (all green)
- `telperion/examples/rvm_bridge/lean/Probes/E6Bridge22_obligation_probe.lean` (expected FAILS)
- this memo

lakefile.toml, AxiomGuardRvMBridge.lean and existing modules untouched; olean emitted by hand.
E6Bridge21 (xi-decay's module) is imported; it is built but not yet in `defaultTargets`, so the
integrator wires E6Bridge21 before E6Bridge22. Guard lines:

```lean
#print axioms RvMBridge22.rightDerivBound
#print axioms RvMBridge22.xiDiffExtGrowthRight_of_two
#print axioms RvMBridge22.xiLogDerivDerivEq_of_two
#print axioms RvMBridge22.growth_compact
#print axioms RvMBridge22.bound_of_bound_off_zeros
#print axioms RvMBridge22.norm_tsum_far_le
```

## Pin footguns hit

- `∑' ρ : ((↑S : Set ℂ)ᶜ), f ρ` parses `ᶜ` on a Type; write `↥(((S : Finset ℂ) : Set ℂ)ᶜ)`.
- `tsum_subtype_le` is the protected `Summable.tsum_subtype_le f β h hf` (f and the set explicit).
- `rw [← tsum_mul_left]` rewrites the wrong side when both sides carry a scalar; use the forward
  form on the subtype sum.
- `positivity` on `2 + |s.im| ≠ 0` needs the goal beta-reduced (`show`) first.

## Probe output (lake env lean Probes/E6Bridge22_probe.lean)

```
'RvMBridge22.rightDerivBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge22.xiDiffExtGrowthRight_of_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge22.xiLogDerivDerivEq_of_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge22.xiDiffExtGrowthRight_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge22.growth_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge22.growth_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge22.growth_strip' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge22.bound_of_bound_off_zeros' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge22.norm_tsum_far_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge22.norm_tsum_polTerm_le_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge22.summable_lcTerm' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge22.deriv_logDeriv_xi_of_one_lt_re' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge22.norm_deriv_digamma_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge22.norm_deriv_logDeriv_zeta_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Obligation probe output (lake env lean Probes/E6Bridge22_obligation_probe.lean), all EXPECTED

```
Probes/E6Bridge22_obligation_probe.lean:8:27: error: unsolved goals     (LocalCountSum, C = 1, simp)
Probes/E6Bridge22_obligation_probe.lean:16:2: error: Tactic `aesop` failed, made no progress  (LocalCountSum, aesop)
Probes/E6Bridge22_obligation_probe.lean:19:29: error: unsolved goals    (StripDerivBound, simp)
Probes/E6Bridge22_obligation_probe.lean:25:29: error: unsolved goals    (not LocalCountSum)
Probes/E6Bridge22_obligation_probe.lean:29:31: error: unsolved goals    (not StripDerivBound)
Probes/E6Bridge22_obligation_probe.lean:34:34: error: unsolved goals    (growth from rightDerivBound alone)
```

## Composition with E6Bridge19 (xi-taylor), added after its landing

`Probes/E6Bridge22_taylor_probe.lean` (imports E6Bridge19 and E6Bridge22) checks that the two
interfaces coincide definitionally and closes the chain to the B7 value half:

```
'probe_xi_defeq' depends on axioms: [propext, Classical.choice, Quot.sound]            (RvMBridge19.xi = RvMBridge18.xi := rfl)
'probe_partialFraction_iff' depends on axioms: [propext, Classical.choice, Quot.sound] (XiDerivPartialFraction ↔ XiLogDerivDerivEq := Iff.rfl)
'probe_liValue_of_two' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`probe_liValue_of_two (h1 : LocalCountSum) (h2 : StripDerivBound) (hR : RvMBridge19.NoRealZeroInUnitInterval)
(n) (hn : 0 < n) : RvMBridge15.LiValue n`. With E6Bridge15's `bl_explicit_formula_of`, the node
RH_bl_explicit_formula therefore rests on exactly three named real facts: the local-count sum, the
Landau-Cauchy strip bound, and the absence of real zeros of ζ in (0, 1). conjecture1_proved = False.
