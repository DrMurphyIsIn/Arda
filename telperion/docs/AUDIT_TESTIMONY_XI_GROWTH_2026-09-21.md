# Audit testimony: E6Bridge22, the growth bound reduced to two classical inequalities, 2026-09-21

THE GROWTH BOUND OF THE ENTIRE EXTENSION REDUCED TO TWO NAMED CLASSICAL INEQUALITIES (THE
LOCAL-COUNT SUM AND THE LANDAU-CAUCHY STRIP BOUND). NOT A PROOF OF ANYTHING ABOUT THE RIEMANN
HYPOTHESIS. E6Bridge22 proves the right half-plane derivative bound outright, the two sum
comparisons, the compact-region bound, the passage across the zeros by continuity, and the
three-region assembly, so that `XiDiffExtGrowthRight` and hence the derivative partial fraction
`XiLogDerivDerivEq` (through E6Bridge18/20/21) rest on `LocalCountSum` and `StripDerivBound`
alone. Nothing is concluded about where the zeros are. conjecture1_proved = False.

Auditor: blind adversarial auditor (separate agent). Worktree /Users/peterwmurphy/arda-goal-weil,
island telperion/examples/rvm_bridge/lean, Lean v4.33.0-rc2, Zeta23 pinned at
fbdc36bbf17d20af3fd0447c6d1a8a02773c9844. Artifact: E6Bridge22.lean (484 lines, namespace
RvMBridge22, imports E6Bridge20 and E6Bridge21); memo XI_DIFF_GROWTH_2026-09-21.md. Probes:
Probes/Audit22_Axioms.lean, Probes/Audit22_Probes.lean. No git state changed; no other file edited.

Overall verdict: PASS. No defect found. The plan correction (the Re s ≥ 2 sum is O(log t), not
O(1)) is right; both sum comparisons re-derive with their exact factors; the continuity passage is
sound; the right half-plane bound is a correct assembly of E6Bridge21's pieces; the three regions
cover Re s ≥ 1/2 with the strip obligation stated on a superset; both obligations are honest and
the memo states the two Lean obstacles.

## 1. Kernel: PASS

`lake build`: `Build completed successfully (8863 jobs)`. E6Bridge22 in defaultTargets (lakefile
line 9) and a lean_lib (line 192); guard 28 RvMBridge22 lines. Probes/Audit22_Axioms.lean prints
axioms for all 36 declarations: 36 of 36 read `[propext, Classical.choice, Quot.sound]`, no
sorryAx. Token grep (excluding the phrase "partial fraction"): zero hits. Imported by E6Bridge24,
the guard and the author's three probes. `#check`: `xiDiffExtGrowthRight_of_two : LocalCountSum →
StripDerivBound → XiDiffExtGrowthRight`; `xiLogDerivDerivEq_of_two : LocalCountSum →
StripDerivBound → XiLogDerivDerivEq`; `rightDerivBound : RightDerivBound`.

## 2. Plan correction and the right comparison: PASS

For Re s ≥ 2 and a strip zero (β < 1), (Re s - β)² ≥ 1, so each term m/|s - ρ|² ≤ m ≤ 1·m and is
of size ≈ 1 when the ordinate matches; with O(log t) zeros per unit height the sum is O(log|Im s|),
not O(1): the memo's correction (line 17-18) is right. `norm_polTerm_le_lcTerm_right` (2 ≤ Re s):
|s - ρ|² = (Re s - β)² + (Im s - γ)² ≥ 1 + (Im s - γ)², so m/|s-ρ|² ≤ lcTerm (Im s) ρ =
m/(1 + (γ - Im s)²); my `audit_right_compare` (axiom-clean) re-proves the inequality.
`norm_tsum_polTerm_le_right` sums it (`norm_tsum_le_tsum_norm`, `tsum_le_tsum`).

## 3. The far comparison, factor 2: PASS

Off the window (|γ - Im s| > 2), |s - ρ|² ≥ (γ - Im s)² =: d² > 4, and 1/d² ≤ 2/(1 + d²) ⟺
1 + d² ≤ 2d² ⟺ d² ≥ 1 (holds with room); my `audit_far_factor` (axiom-clean) re-proves it.
`norm_polTerm_le_lcTerm_far`, then `norm_tsum_far_le : ‖Σ'_{windowᶜ} polTerm‖ ≤ 2 Σ' lcTerm`
via `tsum_subtype_le` (nonnegative terms).

## 4. bound_of_bound_off_zeros: PASS

At a zero s₀ ∈ U, E6Bridge20's `exists_local_form` gives a ball around s₀ with no other zero;
B - ‖xiDiffExt‖ is continuous at s₀ (B continuous, xiDiffExt entire); on the punctured
neighbourhood U ∩ ball \ {s₀} every point is a non-zero where the hypothesis gives ≥ 0;
`ge_of_tendsto` along 𝓝[≠] s₀ gives ≥ 0 at s₀. This uses isolation of the zeros (each zero has a
punctured neighbourhood free of zeros), which is exactly what `exists_local_form` supplies; the
closure step "closure of U \ zeros ⊇ U" is realised pointwise by this punctured-limit argument, and
countability (E6Bridge17) is not needed. Sound.

## 5. rightDerivBound: PASS

`deriv_logDeriv_xi_of_one_lt_re` (complex argument, same proof as E6Bridge21's real case):
(logDeriv ξ)' = -1/s² - 1/(s-1)² + (1/4)ψ'(s/2) + (ζ'/ζ)'(s) on Re s > 1. For Re s ≥ 2:
‖s‖ ≥ 2 so ‖1/s²‖ ≤ 1/4; ‖s - 1‖ ≥ Re(s - 1) ≥ 1 so ‖1/(s-1)²‖ ≤ 1; Re(s/2) ≥ 1 so
`norm_deriv_digamma_le`: ‖ψ'(z)‖ ≤ Σ 1/(n + 1/2)² =: trigConst using ‖z + n‖ ≥ Re z + n ≥ n + 1
≥ n + 1/2 (E6Bridge21 `norm_trigTerm_le`, `hasSum_trigamma_of_re_pos`); and
`norm_deriv_logDeriv_zeta_le`: ‖(ζ'/ζ)'(s)‖ = ‖L(logMul Λ)(s)‖ ≤ Σ ‖term at 2‖ =: dirConst since
|n^{-s}| = n^{-Re s} ≤ n^{-2} (`norm_term_le_of_two_le_re`, rpow monotone) and the σ = 2 terms are
absolutely summable. Total constant 1/4 + 1 + trigConst/4 + dirConst. Re-derived; correct.

## 6. The assembly: PASS

Regions: (A) 1/2 ≤ Re s ≤ 2, |Im s| ≤ 6 compact (`growth_compact`, image of a compact set under a
continuous function bounded); (B) 1/2 ≤ Re s ≤ 2, |Im s| ≥ 6 ⊆ stripOpen = {1/4 < Re < 9/4,
5 < |Im|} (open), whose points satisfy StripDerivBound's closed region 1/4 ≤ Re ≤ 9/4, 5 ≤ |Im|
(probe 7 checks the inclusion); off the zeros ‖xiDiffExt‖ ≤ ‖bracket‖ + ‖far‖ ≤ C₂(1 + L) +
2C₁(1 + L) (`growth_strip_off_zeros`), then `bound_of_bound_off_zeros` (`growth_strip`); (C) Re s
≥ 2 (`growth_right`: RightDerivBound + LocalCountSum). Together they cover Re s ≥ 1/2; constants
are combined by max (all made ≥ 0), and log(2 + |Im s|) ≤ log(2 + ‖s‖) (`abs_im_le_norm'`)
converts to the target's ‖s‖. `xiDiffExtGrowthRight_of h1 h2 h3`, then `xiDiffExtGrowthRight_of_two
h1 h2` with `rightDerivBound`, then `xiLogDerivDerivEq_of_two` through E6Bridge20's
`xiDiffRegular_of_right`, E6Bridge18's `xi_logDeriv_deriv_eq_of` and E6Bridge21's decay
(probe 3 re-composes both).

## 7. Obligation honesty: PASS

`LocalCountSum` and `StripDerivBound` are `def : Prop` (#print of the latter matches the brief
verbatim), consumed only as hypotheses. Not automation-closable: simp with C = 1
(`Audit22_Probes.lean:6:27: unsolved goals`), aesop (`7:52: made no progress`), simp (`8:29:
unsolved goals`), aesop (`9:29: unsolved goals`). RightDerivBound alone does not give the growth
(`12:62: Application type mismatch`, the two slots are not the same Prop). The memo names the two
Lean obstacles for StripDerivBound (lines 48-52): the remainder R(w) = logDeriv ξ(w) - Σ_window
m/(w - ρ) has junk values at the window zeros and must be replaced by logDeriv(ξ/Π(w-ρ)^m) before
Cauchy's estimate applies; and for 1/4 ≤ Re s < 1/2 the disc leaves Landau's ball, so the
functional equation must be used pointwise. It also states LocalCountSum as the textbook
Σ 1/(1 + (t - γ)²) = O(log t) from Zeta23's local count (line 39) and records its expected-failure
probes (line 123 ff.).

## 8. Overclaim: PASS

Grep over E6Bridge22.lean and the memo (prove(s/d) RH/Riemann, RH is/holds/proved, progress
toward, goal node proved, conjecture1_proved = True, growth bound proved, partial fraction
proved): zero hits. File line 33: "TWO obligations remain: LocalCountSum and StripDerivBound.
conjecture1_proved = False. Nothing here bears on RH."; memo line 13 the same.

## Probe inventory

- Probes/Audit22_Axioms.lean: 36 axiom prints, 3 #check, 2 #print.
- Probes/Audit22_Probes.lean: `audit_far_factor`, `audit_right_compare` (axiom-clean); the two
  chains, rightDerivBound, summability at every centre, the region inclusion (all elaborate);
  5 expected failures (four automation attempts; RightDerivBound alone).
- Probes/E6Bridge22_probe.lean, E6Bridge22_obligation_probe.lean, E6Bridge22_taylor_probe.lean
  are the author's own and were not relied on.
