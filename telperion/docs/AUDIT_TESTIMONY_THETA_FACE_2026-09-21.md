# Audit testimony: E6Bridge17, the plain Gaussian face Theta and its heat monotonicity, 2026-09-21

EQUIVALENCES AND A MONOTONICITY INSTRUMENT FOR THE PLAIN GAUSSIAN FACE. NOT A PROOF OF THE
RIEMANN HYPOTHESIS. E6Bridge17 proves RH ↔ (Theta ≥ 0 at every centre and width), the termwise
and summed heat identity between widths, the downward inheritance of positivity in the width, and
the dichotomy "RH or the free widths are bounded". No side of any equivalence is asserted; a
certified free width bounds Lambda_Theta from below and that is a wall, not a crossing.
conjecture1_proved = False.

Auditor: blind adversarial auditor (separate agent). Worktree /Users/peterwmurphy/arda-goal-weil,
island telperion/examples/rvm_bridge/lean, Lean v4.33.0-rc2, Zeta23 pinned at
fbdc36bbf17d20af3fd0447c6d1a8a02773c9844. Artifact: E6Bridge17.lean (950 lines, namespace
RvMBridge17, imports E6Bridge14 plus Mathlib's Gaussian Fourier and Polish-space files); memo
WALL_THETA_FACE_2026-09-21.md; survey docs/research/FIXED_WIDTH_LENS_HEAT_2026-09-21.md; synthesis
docs/FIXED_WIDTH_SURVEY_SYNTHESIS_2026-09-21.md. Probes: Probes/Audit17_Axioms.lean,
Probes/Audit17_Probes.lean, plus mpmath. No git state changed; no other file edited.

Overall verdict: PASS. No defect found in the artifact. The heat identity is correct for complex
centres with the file's prefactor direction (verified by hand and numerically); the interchange of
sum and integral has a summable majorant over a countable index; the monotonicity uses the
hypothesis on the whole line, as it must; the converse's generic-centre choice is exactly what the
positive zero-offset summand forces; the memo carries the two required statements. One
documentation note (not a defect): the synthesis's recommended sentence "Lambda_Theta ≥ lam_cert
asserts nothing detectable about zeros above the ladder" is carried by the wall map (WALL_MAP
line 227), not by this memo, which instead says the face "does not remove the wall".

## 1. Kernel: PASS

`lake build`: `Build completed successfully (8855 jobs)`. E6Bridge17 in defaultTargets (lakefile
line 9) and a lean_lib (line 158); guard 52 RvMBridge17 lines. Probes/Audit17_Axioms.lean prints
axioms for all 65 declarations: 65 of 65 read `[propext, Classical.choice, Quot.sound]`, no sorryAx.
Token grep for `sorry|admit|native_decide|axiom|opaque|unsafe|implemented_by|extern|partial|
set_option`: one hit, the header's backticked mention at line 9. Only the guard and the author's
probe import E6Bridge17. `#check` of the four main theorems matches the brief verbatim.

## 2. The heat identity for complex γ: PASS

By hand: ∫ K_σ(c - c') e^{-2 lam (γ - c')²} dc' with K_σ the Gaussian of variance σ² is a Gaussian
integral in c' with quadratic coefficient A = 1/(2σ²) + 2 lam and complex linear term; completing
the square gives √(π/A)/√(2πσ²) · e^{-2 lam' (γ - c)²} with 1/(4 lam') = 1/(4 lam) + σ² (variances
add), and √(π/A)/√(2πσ²) = √(lam'/lam). So ∫ = √(lam'/lam) G_{c,lam'}(γ), equivalently
G_{c,lam'}(γ) = √(lam/lam') ∫, which is the file's `plainGauss_heat` (prefactor √(lam/lam') on the
integral side). Direction settled numerically at γ = 3 + 0.2i, c = 2.5, lam = 1, lam' = 0.5
(σ² = 0.25, 1/(4 lam') - 1/(4 lam) - σ² = 0): √(lam/lam') · I = G_{c,lam'}(γ) with |diff| = 0.0 at 20
digits, whereas √(lam'/lam) · I is off by 0.405; and I = √(lam'/lam) G_{c,lam'} to 8.5e-22. In Lean:
`heat_integrand_eq` writes the integrand as a single exponential of
-(2 lam²/(lam - lam')) c'² + (c/σ² + 4 lam γ) c' + const (`heat_A_eq`: 1/(2σ²) + 2 lam =
2 lam²/(lam - lam')), and Mathlib's `integral_cexp_quadratic` is applied with the real part of the
quadratic coefficient 2 lam²/(lam - lam') > 0 (`hbre`, from 0 < lam' < lam); `real_gauss_heat`
is the real specialisation, consumed by probe 6.

## 3. The summed identity: PASS

Majorant: ‖heatF‖ = K_σ(c - c') · m · |G_{c',lam}(γ_ρ)| with |G| = e^{2 lam (y² - (x - c')²)} ≤
e^{lam/2} e^{-2 lam (x - c')²} on the strip (y² ≤ 1/4), so ∫‖heatF‖ dc' ≤ m e^{lam/2} · √(lam'/lam)
e^{-2 lam' (Im ρ - c)²} by `real_gauss_heat` (`integral_norm_heatF_le`). Summability: e^{-2 lam'
(x - c)²} ≤ |G_{c,lam'}(γ_ρ)| ≤ plainC c lam'/(1 + |γ_ρ|²) (`norm_plainGauss_mul_le` on the strip),
and the local-count majorant `summable_mult_div_one_add_normSq` of E6Bridge6 closes it
(`summable_integral_norm_heatF`). Countability: `nontrivialZeros_countable` writes the zero set
as ⋃_{n ∈ ℤ} (zeros ∩ {n < Im ≤ n + 1}), each finite by Zeta23 `zetaSeam.finite_window`, via the
integer part `WeilEF.key`; `NZ` gets a `Countable` instance and `tsum_pterm_NZ`/`tsum_pterm_re_NZ`
move the sums to that index (support ⊆ NZ since `pterm = 0` off the nontrivial zeros, which also
handles zeroMult = 0). `theta_heat` then interchanges by `integral_tsum_of_summable_integral_norm`
(the Polish import supplies the measurability side) and takes real parts. Probe 7 confirms both
countability facts.

## 4. theta_pos_mono: PASS

Theta c lam' = √(lam/lam') ∫ K_σ(c - c') Theta c' lam dc' with K_σ ≥ 0 (`heatKernel_nonneg`), so
`hpos : ∀ c, 0 ≤ Theta c lam` is applied at EVERY c' ∈ ℝ inside the integral. The whole-line
requirement is structural: a band-restricted hypothesis |c'| ≤ T does not suffice (probe 5,
`Audit17_Probes.lean:38:75: error: not a positivity goal`), which is the survey's and memo's point
that a certified width needs one whole-line certificate (ladder + envelope + band).

## 5. The converse: PASS

`re_plainGauss`: Re G = e^{2 lam (y² - x²)} cos(4 lam x y) (from -2 lam (x + iy)² = -2 lam (x² - y²)
- 4i lam x y). At x = 0 the summand is +m e^{2 lam y²} > 0 (my `audit_re_plainGauss_axis`,
axiom-clean; mpmath 1.0202 = e^{2·0.01}), so E6Bridge14's centre-at-ordinate trick indeed does not
transfer, as the memo states. `exists_generic_centre'` picks c in the interval |c - Im ρ₀| < |1/2 -
Re ρ₀| avoiding `badSet' = badSet ∪ window ordinates` (finite), so the maximiser ρ₁ of phi_c on the
window (E6Bridge7 `exists_maximiser_gap`) has x₁ = Im ρ₁ - c ≠ 0 (`hcord`) and y₁ ≠ 0 (M > 0);
`exists_lam_cos_neg_one` gives lam ≥ lam₁ with cos(4 lam x₁ y₁) = -1 via lam = (π + 2πk)/(4x₁y₁)
with k chosen by the sign of x₁y₁; the pair term is 2 m₁ e^{2 lam M} · (-1) (`theta_le_pair_add_tail`
via `zeroSide_pair_split`), and the tail is the plain majorant `pmajorant` (window part e^{2 lam
(M - η)} · count, lam = 1 tail sum `pconstB`), with the same threshold arithmetic as E6Bridge7
(K = m₁ ≥ 1, no |w|² factor). `rh_iff_theta_positivity` composes forward (`theta_nonneg_of_rh`, on
the line every summand is m e^{-2 lam (Im ρ - c)²} ≥ 0) with this converse and `rh_of_all_on_line`.

## 6. Non-vacuity and load-bearing: PASS

`ThetaFree lam` is closed neither by simp (`Audit17_Probes.lean:6:64: simp made no progress`) nor
by aesop (`7:37: unsolved goals`). `not_thetaFree_of_offline` gives Λ > 0 with ¬ThetaFree lam for
every lam ≥ Λ (one negative width from the converse at lam₀ = 1, then `thetaFree_mono`), and
`thetaWidths_bddAbove_of_offline`, `rh_or_thetaWidths_bddAbove` follow (probe 3 consumes them).
Monotonicity cannot be reversed: positivity at the smaller width does not give it at the larger
(probe 4 fails at `30:9`). Abstract reason: the identity expresses Theta at the SMALLER width as a
positive average of Theta at the larger width; going up is a backward heat step, ill-posed, and
in the presence of an off-line zero Theta is positive for small widths (the on-line background
dominates) yet negative at some large width (the converse), so no upward implication can hold.

## 7. Memo honesty: PASS, with one documentation note

Present: line 77 "In words: RH <-> Lambda_Theta = infinity"; line 95 "Pushing the certified lower
bound to infinity is RH. That is a wall, not a crossing."; line 8 "Nothing here proves RH. The
face gives RH a new equivalent shape and a new instrument (width monotonicity); it does not remove
the wall."; section 6 names what is NOT delivered (effective Theta dominance, the Theta versions
of the region instruments). Note: the synthesis (FIXED_WIDTH_SURVEY_SYNTHESIS line 160) recommends
that the WALL MAP addendum carry the sentence "Lambda_Theta ≥ lam_cert asserts nothing detectable
about zeros above the ladder at any reachable lam_cert"; that sentence is in the wall map
(WALL_MAP_2026-09-21.md line 227) and not in this memo. The Theta memo's own wording ("does not
remove the wall", "a wall, not a crossing") does not contradict it, but the explicit
non-detectability statement would belong here too if the memo is read standalone. Not a defect
of the artifact.

## 8. Overclaim: PASS

Grep over E6Bridge17.lean and the memo (prove(s/d) RH/Riemann, RH is/holds/proved, progress
toward, goal node proved, conjecture1_proved = True, crossing the wall, closes RH, removes the
wall): the only hit is the negation at memo line 8 "Nothing here proves RH." File lines 26-27:
"conjecture1_proved = False. RH <-> Lambda_Theta = infinity ... certified widths bound Lambda_Theta
from below and that is a wall, not a crossing."

## Probe inventory

- Probes/Audit17_Axioms.lean: 65 axiom prints, 4 #check.
- Probes/Audit17_Probes.lean: `audit_re_plainGauss_axis` (axiom-clean); equivalence, monotonicity,
  off-line bound, real heat step, countability (all elaborate); 4 expected failures (ThetaFree by
  simp / aesop; monotonicity reversed; band-restricted hypothesis).
- mpmath: heat identity at γ = 3 + 0.2i, c = 2.5, lam = 1, lam' = 0.5 in both prefactor
  directions; the zero-offset summand.
- Probes/E6Bridge17_probe.lean is the author's own and was not relied on.
