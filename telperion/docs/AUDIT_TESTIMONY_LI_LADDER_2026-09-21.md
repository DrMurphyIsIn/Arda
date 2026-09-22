The artifact is a low-height zero box (no zero below |Im| = sqrt 3 / 2) and a Li ladder priced in height (zeros on the line up to T buy rungs n + 1 <= 3 pi T / 2), plus the hypothesis-free rung 0; finite inequalities and conditional implications; NOT a proof of anything about RH.

# Audit testimony: LowHeightBox + LiLadderHeight (li_positivity island)

Auditor: auditor-forward (blind, adversarial). Date: 2026-09-21. Branch mm/li-face.
Island: telperion/examples/li_positivity/lean, Lean v4.34.0-rc1, upstream LiCriterion rev 35df682f.
Files: LowHeightBox.lean (310 lines, namespace LowHeightBox, 17 declarations),
LiLadderHeight.lean (618 lines, namespace LiLadderHeight, 39 declarations + top-level li_rung0_kernel).
Probes: Probes/AuditLi_Axioms.lean, Probes/AuditLi_Probes.lean (directory created by me).
conjecture1_proved = False.

## 1. Verdict

PASS for both modules. One-sentence verdicts:
- LowHeightBox: the sharp bound |J(s)| <= 1/(2 Re s) by unit-cell midpoint reflection is
  correct and hypothesis-free, and Boxes 1 and 2 follow from it and the functional equation
  exactly as the brief derives them.
- LiLadderHeight: the paired zero sum is a pure composition of hypothesis-free upstream theorems,
  Lemmas A, A', B and Theorems C, D are correct with the factor-3 case split honest, rung 0 is
  the registry statement byte for byte with no hypothesis, and the height-4000 composition
  carries the capstone's conclusion shape verbatim with the real-zero residual discharged by Box 1.

No blocking findings. Two notes (section 8) that are not defects.

## 2. Kernel evidence (my own runs)

Probes/AuditLi_Axioms.lean: 69 `#print axioms` (17 LowHeightBox, 39 LiLadderHeight,
li_rung0_kernel, and 13 inputs: xi_hasFiniteOrder, xi_order_le_one,
xi_weighted_genus_one_of_hadamard_order_one, xi_factorization_prod_with_multiplicity_of_hadamard_order_one,
weighted_paired_sum_formula_of_standard_hypotheses, summable_weighted_Li_paired_summand_of_weighted_genus,
modulus_one_minus_one_div_on_critical_line, pairedZero_val, zero_pairing, li_criterion_rh_iff,
ZeroFreeBridge.zeta_fract_repr, riemannZeta_conj, AllZeros_h4000.all_nontrivial_zeros_up_to_height_4000_of_bands).
All 69 report `[propext, Classical.choice, Quot.sound]`; no sorryAx anywhere.

    'li_rung0_kernel' depends on axioms: [propext, Classical.choice, Quot.sound]

Token grep (sorry/admit/native_decide/axiom/opaque/unsafe/implemented_by/extern/partial/set_option)
on both files: only LiLadderHeight.lean:10, the docstring phrase "no `sorry`". No tokens.
Built .olean files for both modules exist; I built only my probes with `lake env lean`.

## 3. Registry byte comparison

missions/rh/lean/Statements/RH_li_rung0_kernel.lean (sha256 337db1dc44959b04, status open):

    theorem li_rung0_kernel :
        0 ≤ (LiCriterion.taylorCoeff LiCriterion.riemannXi 0).re := by sorry

LiLadderHeight.lean line 616: same name at top level (outside the namespace), statement text
byte-IDENTICAL (python comparison), proof
`LiLadderHeight.re_taylorCoeff_nonneg_of_termwise 0 LiLadderHeight.re_liPairedSummand_zero_nonneg`.
Node file missions/rh/nodes/RH_li_rung0_kernel.toml points at this artifact.

## 4. Upstream inputs re-read (LiCriterion snapshot)

- `NontrivialZero := {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}` (Basic.lean:100).
- `liSummand n ρ = 1 - (1 - 1/ρ)^(-(n+1 : ℤ))` (2780); `liPairedSummand n ρ = liSummand n ρ +
  liSummand n (pairedZero ρ)` (2787); `pairedZero_val : (pairedZero ρ).val = 1 - ρ.val` (1655,
  from zero_pairing at 1614).
- `taylorCoeff f n = deriv^[n] (logDeriv (phi f)) 0 / n!`, `phi f z = f (1/(1-z))` (525, 379);
  `riemannXi s = (1/2) s (s-1) completedRiemannZeta₀ s + 1/2` (1236).
- `weighted_paired_sum_formula_of_standard_hypotheses (hgenus) (hhad) : ∀ n, taylorCoeff riemannXi n
  = 2⁻¹ * ∑' ρ, m(ρ) * liPairedSummand n ρ` (GenusOnePairedSumFormula.lean:1719); the two
  hypotheses are exactly the conclusions of the two `_of_hadamard_order_one` bridges, which take
  only `xi_hasFiniteOrder` and `xi_order_le_one` (XiOrderBridge.lean:51, 58, both closed terms).
  So `taylorCoeff_eq_half_tsum_paired` is a hypothesis-free composition. Confirmed by kernel.
- `modulus_one_minus_one_div_on_critical_line ρ (ρ ≠ 0) : ρ.re = 1/2 → ‖1 - 1/ρ‖ = 1` (1887).
- `ZeroFreeBridge`: `fractIntegrand s x = {x} / x^(s+1)`, `fractIntegral s = ∫_{x>1}`,
  `stripRHS s = s/(s-1) - s * fractIntegral s`, `stripDomain = {0 < Re} \ {1}`,
  `zeta_fract_repr : s ∈ stripDomain → riemannZeta s = stripRHS s` (StripRepr.lean:42-52,
  StripReprAssembled.lean:26). The old bound `zeta_repr_integral_bound` is 1/Re s (ZeroFreeBridge:517);
  the new file proves the sharp 1/(2 Re s).
- h4000 capstone: 89 band/segment hypotheses plus
  `hγ : ∀ ρ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 4000 → 55/16 ≤ |ρ.im|`, conclusion
  `∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 4000 → ρ.re = 1 / 2`. The `hall` hypothesis of
  `li_rungs_of_bands_4000*` is this conclusion verbatim.

## 5. LowHeightBox mathematics, re-derived by hand

(a) Per-cell inequality. On [n+1, n+2) with midpoint c = n + 3/2, {x} = x - (n+1) = (x - c) + 1/2.
The kernel g(x) = x^(-(σ+1)) is decreasing for σ > 0, so (x - c)(g(x) - g(c)) <= 0 pointwise
(`sub_mul_rpow_le`, both cases x <= c and x > c checked via `Real.rpow_le_rpow_of_nonpos`).
Hence ∫_cell (x - c) g <= g(c) ∫_cell (x - c) = 0 (`integral_cell_centred`: ∫_1^2-type integral of a
centred linear function vanishes). So ∫_cell {x} g <= (1/2) ∫_cell g. Checked.
(b) Summing cells: [1, ∞) = ⊔ cells (`Ici_one_eq_iUnion_cell` via ⌊x - 1⌋₊), pairwise disjoint,
both integrands integrable on [1, ∞) (|{x} g| <= g, and g integrable for σ > 0 by
`integrableOn_Ioi_rpow_of_lt`), `hasSum_integral_iUnion` twice and `hasSum_le` termwise. The half
kernel integrates to (1/2)·1/σ = 1/(2σ). Checked. This is the sharp bound the skeptic's item 7
said was missing from the island; it is now present and hypothesis-free.
(c) Complex J: ‖{x}/x^(s+1)‖ = {x} x^(-(Re s + 1)) (`norm_cpow_eq_rpow_re_of_pos`), so
‖J(s)‖ <= ∫ {x} x^(-(σ+1)) <= 1/(2σ). Checked.
(d) At a zero in the strip: 0 = s/(s-1) - s J(s) gives 1/|s-1| = |J| <= 1/(2σ), so 2σ <= |s-1|
(`two_re_le_norm_sub_one`; s ≠ 0, s ≠ 1 from 0 < σ < 1). Checked.
(e) Reflection: riemannZeta s = Λ(s)/Γℝ(s) for s ≠ 0 (`riemannZeta_def_of_ne_zero`), Γℝ(s) ≠ 0
for Re s > 0 (`Gammaℝ_eq_zero_iff` gives s = -2n), so Λ(s) = 0, and Λ(1-s) = Λ(s) gives
riemannZeta(1-s) = 0 (1 - s ≠ 0 since Re(1-s) = 1 - σ > 0). Checked. The reflected point has
Re = 1 - σ ∈ (0,1), and applying (d) to it gives 2(1-σ) <= ‖(1-s) - 1‖ = ‖s‖.
(f) Box 2: squaring, 4σ² <= (σ-1)² + t² and 4(1-σ)² <= σ² + t²; adding,
3σ² + 3(1-σ)² <= 2t², i.e. 3(2(σ-1/2)² + 1/2) <= 2t², i.e. (σ-1/2)² <= t²/3 - 1/4. Re-proved
abstractly in my probe 2 by nlinarith. Box 1: right side >= 0 forces t² >= 3/4 (probe 3).
Checked. Both tight at σ = 1/2, t² = 3/4; consistent with the first zero (probe/numerics).
(g) Real-axis corollary: a real zero has |Im| = 0 < sqrt 3 / 2. Checked.

## 6. LiLadderHeight mathematics, re-derived by hand

(a) Normal form. u = 1 - 1/ρ = (ρ-1)/ρ, and 1 - 1/(1-ρ) = -ρ/(1-ρ) = ρ/(ρ-1) = u⁻¹. With the
upstream zpow exponent -(n+1): liSummand n ρ = 1 - (u^(n+1))⁻¹ and liSummand n (1-ρ) =
1 - ((u⁻¹)^(n+1))⁻¹ = 1 - u^(n+1). Sum 2 - u^N - (u^N)⁻¹ (`liPairedSummand_eq_two_sub_pow_sub_inv`);
`liPairedSummand_eq_w` rewrites with w = u⁻¹ = ρ/(ρ-1), the brief's form. Checked.
(b) Polar real part: u^N = exp(N log u), Re exp(z) = e^{Re z} cos(Im z), so Re(u^N + u^{-N}) =
(e^{N log|u|} + e^{-N log|u|}) cos(N arg u) = 2 cosh(N log|u|) cos(N arg u). Checked;
numerically to 7e-59 relative on 3000 random (ρ, n) with |Im ρ| up to 30, n up to 40.
(c) Lemma A. g(t) = sinh t cos t - cosh t sin t has g(0) = 0 and g' = -2 sinh t sin t <= 0 on
[0, π], so g <= 0 there; f(t) = cosh t cos t has f' = g <= 0, f(0) = 1, so f <= 1 on [0, π].
For |a| <= |b| <= π/2: cos b = cos|b| <= cos|a| (cos antitone on [0, π]), cosh a > 0, so
cosh a cos b <= cosh|a| cos|a| <= 1. Checked.
(d) Lemma A' (the factor 3). For π/2 < |b| <= 3π/2, cos b = cos|b| <= 0
(`Real.cos_nonpos_of_pi_div_two_le_of_le`, valid on [π/2, 3π/2]) and cosh a > 0, so the product
is <= 0 <= 1 with no condition on a. Case split at |b| <= π/2 is exhaustive. Checked; my probe 5
re-proves the second case abstractly, and probe 6 shows the window cannot reach 2π
(cosh 1 · cos 2π = cosh 1 > 1).
(e) Lemma B, upper half. Re u = 1 - β/(β²+γ²) > 0 when γ² >= 1 > β(1-β), so arg u ∈ (-π/2, π/2)
and tan(arg u) = Im u / Re u = γ/(γ² - β(1-β)). Also tan(arctan(β/γ) + arctan((1-β)/γ)) has the
same value by the addition formula (product β(1-β)/γ² < 1), so the angle identity holds
(`arg_one_sub_inv_eq`, |Im| >= 1). Then |arg u| <= |β/γ| + |(1-β)/γ| = 1/|γ| via |arctan x| <= |x|.
Checked; numerically |arg u| - 1/|γ| <= -6.8e-7 and the identity holds to 6e-17.
(f) Lemma B, lower half. |log|u|| = (1/2)|log(B/A)| with A = β²+γ², B = (β-1)²+γ²; each of
log(B/A), log(A/B) <= (ratio - 1) = ±(1-2β)/(A or B) <= 1/γ², so |log|u|| <= 1/(2γ²). And
|sin(arg u)| = |Im u|/|u| = |γ|/(A|u|) with A|u| = sqrt(AB) <= 2γ² (A, B <= 2γ² when γ² >= 1
and 0 < β < 1), so |arg u| >= |sin arg u| >= 1/(2|γ|) >= 1/(2γ²) >= |log|u||. Checked;
numerically |log|u|| - |arg u| <= -0.0198 on |Im| >= 1. The skeptic's item 4 warning (the
brief's arctan x >= (π/4)x route needs γ >= max(β, 1-β)) is moot: the file uses the sin route,
which needs only γ² >= 1. Below height 1 the inequality does fail near the strip edge for
γ <= 0.28 (numerics: γ = 0.28, β → 0 gives |log r| = 1.310 > |θ| = 1.301), so the |Im| >= 1
hypothesis is genuinely used, not decorative.
(g) Theorem C. With |Im ρ| >= max(1, 2N/(3π)): |N arg u| <= N/|γ| <= 3π/2 and
|N log|u|| <= |N arg u|, so Lemma A' gives cosh·cos <= 1 and the term 2 - 2cosh·cos >= 0.
Checked. Numerically the minimum of the term over β ∈ (0,1), γ ∈ [threshold, threshold + 40] is
positive for N = 1, 2, 3, 5, 10, 20, 50, 200 (smallest 6.0e-4 at N = 1, tending to 0 from above).
Sharpness of the method: at γ = 3.144 (N = 20, β = 0.3), below the threshold 4.244, the term is
-0.157; at γ = 7.94 (N = 50), below 10.61, it is -0.025. So the constant 2/(3π) cannot be
lowered past 1/(2π) by any termwise argument; the file claims only 2/(3π).
(h) On-line zeros: |u| = 1 (upstream lemma), log 1 = 0, cosh 0 = 1, term 2(1 - cos) >= 0. Checked.
(i) Re through the tsum: `Complex.re_tsum` with the upstream summability
(`summable_weighted_paired`, hypothesis-free by the same two bridges); m(ρ) is a natural number,
so Re(m · term) = m · Re term. `tsum_nonneg` closes Theorem D's termwise step. Checked.
(j) Theorem D. Zeros with |Im| <= T are on the line by hypothesis (the hypothesis ranges over all
ρ with riemannZeta ρ = 0, 0 < Re < 1, |Im| <= T, real zeros included); zeros with |Im| > T have
|Im| >= T >= 1 and >= 2(n+1)/(3π) from n + 1 <= 3πT/2 (probe 7). Checked.
(k) Rung 0. N = 1: 2 - u - u⁻¹ with u = (ρ-1)/ρ: 2 - (ρ-1)/ρ - ρ/(ρ-1) = [2ρ(ρ-1) - (ρ-1)² - ρ²]/(ρ(ρ-1))
= -1/(ρ(ρ-1)) = 1/(ρ(1-ρ)). Re(1/z) = Re z/|z|² and Re(ρ(1-ρ)) = β(1-β) + γ² >= 0 (probe 8).
Checked; numerically the identity holds to 1e-25 and λ₁ = 0.0230957 > 0.
(l) Height-4000 composition. `line_hyp_of_upper_half`: Im < 0 reflects by `riemannZeta_conj`
(conj ρ is a zero with Im > 0 and the same Re); Im = 0 is excluded by `NoRealZeroInStrip`, a
`def : Prop`, discharged by `noRealZeroInStrip` from Box 1; Im > 0 is `hall`. Then Theorem D at
T = 4000. Reach: n + 1 <= 6000π; with π > 3.1415 (`Real.pi_gt_d4`), n <= 18848 works and
n = 18849 is refused (probes 9 and 13). Checked. The composition is stated against the capstone's
CONCLUSION as an abstract hypothesis; the capstone's own 90 hypotheses (89 bands plus hγ with
55/16 <= |Im|) are NOT discharged here and the file does not claim they are.

## 7. Probes (Probes/AuditLi_Probes.lean)

Expected successes, all elaborated: rung 0 by name (1); Box 2 and Box 1 algebra re-derived
abstractly (2, 3); Box 1 applied to an upstream NontrivialZero, so the hypothesis shapes agree (4);
the cos <= 0 half of the factor-3 split (5); the 2π counterexample showing the window is maximal
for the method (6); the Theorem D threshold arithmetic (7); the rung-0 numerator sign (8);
consumption of the height-4000 ladder at rung 18848 (9); Lemma A at the corner (10).
Expected failures, each failing at the intended point:

    Probes/AuditLi_Probes.lean:54:38: error: Application type mismatch   -- rung-0 lemma at rung 1
    Probes/AuditLi_Probes.lean:59:42: error: unsolved goals               -- Theorem D at T = 1/2
    Probes/AuditLi_Probes.lean:64:39: error: unsolved goals               -- rung 18849 beyond reach

## 8. Notes (not defects)

- The registry node toml says `closure_clean = false` and `status = "open"`; the artifact is
  kernel-clean, so those fields await the grant pass. The readback's "ELABORATION-RISK" flag on
  deriv^[0]/riemannXi is resolved: the statement elaborates and is proved.
- The height-4000 composition is conditional on the capstone's conclusion; it does NOT supersede the
  per-rung Arb certificates until the capstone's band hypotheses are themselves in the kernel.
  The file says this ("Conditional; proves nothing about RH").

## 9. Overclaim grep

LowHeightBox.lean, LiLadderHeight.lean, LI_FACE_BRIEF: no "RH proved/holds" or similar.
LowHeightBox.lean:26-28 "Nothing here proves, or bears on, whether RH holds ... conjecture1_proved
= False." LiLadderHeight.lean:57-59 "conjecture1_proved = False. Nothing here proves, or approaches,
the Riemann Hypothesis: ... the uniform `forall n` IS RH". Line 615 repeats the flag.

## 10. What this does and does not establish

Established, hypothesis-free: no zero of zeta in the strip has |Im| < sqrt 3 / 2 (folklore-level,
new to the island); every such zero satisfies (Re - 1/2)² <= Im²/3 - 1/4; Li's λ₁ >= 0 in the
upstream vocabulary. Established conditionally: rungs n + 1 <= 3πT/2 from zeros on the line up to
T >= 1, and rungs 0..18848 from the height-4000 capstone's conclusion. Nothing evaluates the
sign of λ_n for all n by proof, and that uniform statement is RH itself. NOT a proof of anything
about RH. conjecture1_proved = False.
