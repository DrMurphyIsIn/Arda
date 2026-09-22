# Audit testimony: E6Bridge23, E6Bridge25, E6Bridge26, the B7 last mile, 2026-09-21

TWO CLASSICAL FACTS DISCHARGED (THE LOCAL-COUNT SUM; NO REAL ZERO OF ZETA IN (0, 1)) AND THE
BOMBIERI-LAGARIAS NODE B7 REDUCED TO StripDerivBound ALONE. NOT A PROOF OF ANYTHING ABOUT THE
RIEMANN HYPOTHESIS. E6Bridge23 proves `LocalCountSum` from Zeta23's local zero count; E6Bridge25
proves `NoRealZeroInUnitInterval` from the summation-by-parts representation of zeta; E6Bridge26
composes them with E6Bridge19/22/25 so that the rh node RH_bl_explicit_formula rests on the single
named inequality `StripDerivBound`. Nothing is concluded about where the zeros are.
conjecture1_proved = False.

Auditor: blind adversarial auditor (separate agent). Worktree /Users/peterwmurphy/arda-goal-weil,
island telperion/examples/rvm_bridge/lean, Lean v4.33.0-rc2, Zeta23 pinned at
fbdc36bbf17d20af3fd0447c6d1a8a02773c9844. Artifacts: E6Bridge23.lean (282 lines, RvMBridge23,
imports E6Bridge22), E6Bridge25.lean (129 lines, RvMBridge25, imports E6Bridge19, E6Bridge22,
Zeta23.FromPNTPlus.ZetaBounds), E6Bridge26.lean (29 lines, RvMBridge26, imports E6Bridge23,
E6Bridge25); memos LOCAL_COUNT_SUM_2026-09-21.md and NO_REAL_ZERO_2026-09-21.md. Probes:
Probes/Audit23_Axioms.lean, Probes/Audit23_Probes.lean, plus mpmath. No git state changed; no
other file edited.

Overall verdict: PASS for all three modules. No defect found.

## Kernel (all three): PASS

`lake build`: `Build completed successfully (8873 jobs)`. All three in defaultTargets (lakefile
line 9) and lean_libs; guard 23 + 9 + 2 RvMBridge23/25/26 lines. Probes/Audit23_Axioms.lean prints
axioms for all 27 + 8 + 2 = 37 declarations plus `Zeta23.RvM.zeta_local_zero_count` and
`Zeta0EqZeta`: 39 of 39 read `[propext, Classical.choice, Quot.sound]`, no sorryAx. Token greps:
only comment phrases ("partial fraction", "partial sum") and a lemma name; no code hit. E6Bridge26
is imported by E6Bridge27 and the guard. `#check local_count_sum : RvMBridge22.LocalCountSum`;
`noRealZeroInUnitInterval : RvMBridge19.NoRealZeroInUnitInterval`; `bl_explicit_formula_of_strip :
StripDerivBound → ∀ n, 0 < n → Tendsto (liZeroSum n) atTop (𝓝 (archSide n + finiteSide n))`.

## (A) E6Bridge23, LocalCountSum: PASS

(2) Input: `Zeta23.RvM.zeta_local_zero_count : ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ t : ℝ, (Ncount t (t+1) : ℝ) ≤
A₀ * Real.log (|t| + 3)` (LocalCount.lean:266-267), for all real t with 1 ≤ A₀; `local_count_sum`
obtains ⟨A₀, hA₀1, hloc⟩ from it and passes hloc verbatim to `sum_lcTerm_le` (whose hypothesis is
exactly that shape), with hA₀ : 0 ≤ A₀ from 1 ≤ A₀.
(3) Fibering: k := ⌈Im ρ - a⌉ gives k - 1 < Im ρ - a ≤ k (Int.ceil_lt_add_one, Int.le_ceil), i.e.
a + k - 1 < Im ρ ≤ a + k, which is Zeta23's `zerosIn T₁ T₂ = {IsNontrivialZero ∧ T₁ < Im ∧ Im ≤ T₂}`
(Statement.lean:46) at T₁ = a + k - 1, T₂ = a + k; `sum_zeroMult_fiber_le` bounds the fiber's
multiplicity sum by Ncount (a + k - 1) (a + k) via the finite window and the E8/Zeta23
multiplicity identification (`zeroMult_cast_eq`).
(4) Fiber weight `one_add_sq_le_of_ceil`: for k ≥ 1, x > k - 1 ≥ 0 so x² ≥ (k-1)² and 1 + k² ≤
4 + 4(k-1)² ⟺ 3k² - 8k + 7 ≥ 0, true (discriminant negative; the file's nlinarith hint (3k-4)²);
for k ≤ 0, x ≤ k ≤ 0 so x² ≥ k² and 1 + k² ≤ 1 + x² ≤ 4(1 + x²). My `audit_fiber_pos` and
`audit_fiber_nonpos` (axiom-clean) re-prove both cases; k = 1 is the k ≥ 1 case with x ∈ (0, 1].
Numerically the ratio (1 + k²)/(1 + x²) on ceil(x) = k peaks at 2.4975 (k = 2), so the constant 4
has room. Hence lcTerm ≤ m · 4/(1 + k²) on the fiber.
(5) `wcount_le`: log(|a| + |k| + 4) ≤ log((2 + |a|)(|k| + 4)) = log(2 + |a|) + log(|k| + 4) since
(2 + |a|)(|k| + 4) ≥ |a| + |k| + 4 (my `audit_log_split`, axiom-clean); and |a + k - 1| + 3 ≤ |a| +
|k| + 4 links hloc at t = a + k - 1 to wcount.
(6) S1 = Σ' 1/(1 + k²) summable over ℤ by comparison with 1/k² (`Real.summable_one_div_int_pow`);
S2 = Σ' log(|k| + 4)/(1 + k²): `log_add_four_le`: log(y + 4) = 2 log √(y+4) ≤ 2(√(y+4) - 1) ≤ 6√y
for y ≥ 1 (since y + 4 ≤ 9y), hence log(y + 4)/(1 + y²) ≤ 6√y/y² = 6 y^{-3/2} (`log_div_le_rpow`),
summable by `Real.summable_abs_int_rpow` with exponent 3/2 > 1. Re-derived; at y = 1, log 5 =
1.609 ≤ 6.
(7) `sum_lcTerm_le`: every finite sum is regrouped by fibers (`Finset.sum_fiberwise_of_maps_to`),
each fiber ≤ wcount A₀ a k, then `Summable.sum_le_tsum`; `tsum_wcount_le`: Σ' wcount ≤
4A₀(log(2+|a|) S1 + S2); `Real.tsum_le_of_sum_le` (nonnegative terms, uniform finite-sum bound)
gives Σ' lcTerm a ≤ that ≤ 4A₀(S1 + S2)(1 + log(2 + |a|)), so C = 4A₀(S1 + S2). Correct.
Consequences `xiDiffExtGrowthRight_of_strip`, `xiLogDerivDerivEq_of_strip` are compositions with
E6Bridge22 (probe consumes the latter).

## (B) E6Bridge25, no real zero in (0, 1): PASS

(2) Representation: Zeta23 `Zeta0EqZeta {N} (0 < N) {s} (0 < Re s) (s ≠ 1) : ζ₀ N s = riemannZeta s`
(ZetaBounds.lean:1150-1151) with `riemannZeta0 N s = Σ_{n ∈ range (N+1)} 1/n^s + (-N^{1-s})/(1-s) +
(-N^{-s})/2 + s ∫_{Ioi N} (⌊x⌋ + 1/2 - x)/x^{s+1}` (lines 520-523). At N = 1, real σ ∈ (0, 1): the
range-2 sum is 0^{-s} + 1^{-s} = 0 + 1 (zero_cpow with s ≠ 0), so ζ(σ) = 1 - 1/(1-σ) - 1/2 + σ J =
1/2 + 1/(σ-1) + σJ, exactly what the file's `simp only` produces and the header states. The
hypotheses 0 < Re σ and σ ≠ 1 are discharged from 0 < σ < 1.
(3) `norm_tail_integral_le`: |⌊x⌋ + 1/2 - x| ≤ 1/2 (Zeta23 `ZetaSum_aux1_3`, ZetaBounds.lean:654),
|x^{-(σ+1)}| = x^{-σ-1} for x > 0 (`norm_cpow_eq_rpow_re_of_pos`), and ∫_1^∞ x^{-σ-1} dx = 1/σ by
Mathlib `integral_Ioi_rpow_of_lt` whose exponent condition -σ - 1 < -1 is σ > 0 (probe 6); so
‖J(σ)‖ ≤ 1/(2σ). Numerically |J| = 0.046, 0.077, 0.077 at σ = 0.1, 0.5, 0.9 against 5, 1, 0.556.
(4) Re ζ(σ) = 1/2 - 1/(1-σ) + σ Re J ≤ 1/2 - 1/(1-σ) + σ‖J‖ ≤ 1 - 1/(1-σ) < 0 since 1/(σ-1) =
-1/(1-σ) and 1/(1-σ) > 1 for 0 < 1 - σ < 1 (my `audit_sign`, axiom-clean). Hence
`riemannZeta_ne_zero_of_unit_interval` and `noRealZeroInUnitInterval` (a term-mode instance of
E6Bridge19's Prop). The memo is right that Zeta23's cruder |J| ≤ 1/σ would only give the sign for
σ > 1/3, and that the Dirichlet-eta route is not needed.
(5) Exercised: `re_riemannZeta_neg_of_unit_interval` at σ = 1/2 and `riemannZeta ((1/2:ℝ):ℂ) ≠ 0`
elaborate; mpmath Re ζ(1/2) = -1.4603545 < 0 and Re ζ(2) = 1.6449341 > 0 (Mathlib's
`riemannZeta_ne_zero_of_one_lt_re` at 2 elaborates as the contrast); the theorem does not apply at
σ = 2 (`Audit23_Probes.lean:50:53: unsolved goals`). ζ(σ) lies below the bound 1 - 1/(1-σ) at σ =
0.1, 0.5, 0.9 (-0.603 ≤ -0.111; -1.460 ≤ -1.0; -9.430 ≤ -9.0).
`liValue_of_two h1 h2 n hn := liValue_of (xiLogDerivDerivEq_of_two h1 h2) noRealZeroInUnitInterval n hn`
and `bl_explicit_formula_of_two` are compositions (my probe re-composes `liValue_of_two` from
E6Bridge19/22 and this module's fact).

## (C) E6Bridge26, assembly: PASS

`liValue_of_strip h2 n hn := RvMBridge25.liValue_of_two RvMBridge23.local_count_sum h2 n hn` and
`bl_explicit_formula_of_strip h2 n hn := RvMBridge25.bl_explicit_formula_of_two
RvMBridge23.local_count_sum h2 n hn`: exactly compositions of named proved inputs, no tactic
block (probe 1 re-composes the first). Byte comparison of `bl_explicit_formula_of_strip` against
missions/rh/lean/Statements/RH_bl_explicit_formula.lean's `theorem bl_explicit_formula (n : ℕ)
(hn : 0 < n) : Tendsto (BombieriLagarias.liZeroSum n) atTop (𝓝 (BombieriLagarias.archSide n +
BombieriLagarias.finiteSide n))`: after stripping the single hypothesis `(h2 :
RvMBridge22.StripDerivBound)`, the namespace prefix `RvMBridge15.` and the proof tail, the two are
IDENTICAL (the registry vocabulary was shown byte-identical to RvMBridge15.BombieriLagarias in the
E6Bridge15 audit). So B7 = StripDerivBound → node, verbatim.

## Overclaim (all three files and both memos): PASS

Grep (prove(s/d) RH/Riemann, RH is/holds/proved, progress toward, goal node proved,
conjecture1_proved = True, B7 proved/closed, node proved): the only hits are the two disclaimers
(E6Bridge25 line 26 and NO_REAL_ZERO line 6 "Nothing here says anything about whether RH holds").
E6Bridge23 line 20 and E6Bridge26 line 10 carry "Nothing here bears on RH. conjecture1_proved =
False." / "NOT a proof of anything about RH." LOCAL_COUNT_SUM lines 12-20 and NO_REAL_ZERO lines
17-23, 55 state that StripDerivBound is the single remaining obligation.

## Probe inventory

- Probes/Audit23_Axioms.lean: 39 axiom prints, 3 #check.
- Probes/Audit23_Probes.lean: `audit_fiber_pos`, `audit_fiber_nonpos`, `audit_log_split`,
  `audit_sign` (axiom-clean); consumption of both discharged facts, the strip chain, the
  re-composed assembly, the log inequality, the σ = 1/2 instances and the ζ(2) contrast, the
  exponent condition (all elaborate); 1 expected failure (σ = 2).
- mpmath: Re ζ(1/2), Re ζ(2); the representation, |J| against 1/(2σ) and ζ against 1 - 1/(1-σ)
  at σ = 0.1, 0.5, 0.9; log(5) ≤ 6; the fiber-weight ratio on ceil(x) = k for k ∈ {-3,-1,0,1,2,3,5}.
- Probes/E6Bridge23_probe.lean, E6Bridge25_probe.lean are the authors' own and were not relied on.
