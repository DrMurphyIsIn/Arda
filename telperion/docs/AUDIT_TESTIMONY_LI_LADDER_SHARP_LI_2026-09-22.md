The artifact is the li-island twin of the sharpened Li ladder (zeros on the line up to T >= 1 buy rungs n + 1 <= 2 pi (T - 1/2); at height 4000, rungs 0..25128 under the capstone's conclusion); finite conditional implications; NOT a proof of anything about RH.

# Audit testimony: LiLadderSharp (li_positivity island)

Auditor: auditor-forward (blind, adversarial). Date: 2026-09-22. Branch mm/li-face.
Island: telperion/examples/li_positivity/lean, Lean v4.34.0-rc1, upstream LiCriterion rev 35df682f.
File: LiLadderSharp.lean (163 lines, namespace LiLadderHeight, 7 declarations, imports LiLadderHeight).
Probes: Probes/AuditLiSharp_Axioms.lean, Probes/AuditLiSharp_Probes.lean. conjecture1_proved = False.
Companion: the rvm-island twin E6Bridge29 was audited in AUDIT_TESTIMONY_LI_LADDER_SHARP_2026-09-22.md;
the mathematics is identical and the numeric sharpness check there applies verbatim (the pair term
is the same function of (beta, gamma, N) on both islands).

## 1. Verdict

PASS. One sentence: the window lemma, the combined bound and the three-case Theorem C'' are the
same correct arguments as on the rvm island, built on LiLadderHeight's Lemmas A, A', B, Theorem D''
and the height-4000 composition reuse LiLadderHeight's tsum and residual plumbing unchanged, the
count 25128 is exactly the integer reach of 7999 pi and needs Real.pi_gt_d6, and both registry
nodes are byte-identical.

## 2. Kernel evidence (my runs)

Probes/AuditLiSharp_Axioms.lean: 18/18 `#print axioms` = `[propext, Classical.choice, Quot.sound]`
(7 LiLadderSharp declarations, mechanically extracted, plus the consumed LiLadderHeight lemmas
cosh_mul_cos_le_one, cosh_mul_cos_le_one_of_le_three_pi_div_two, abs_arg_base_le,
abs_log_norm_one_sub_inv_le, abs_log_norm_le_abs_arg, re_liPairedSummand_eq,
re_liPairedSummand_nonneg_of_onLine, re_taylorCoeff_nonneg_of_termwise, line_hyp_of_upper_half,
noRealZeroInStrip, and Mathlib's Real.pi_gt_d6). Verbatim from Probes/AuditLiSharp_Probes.lean:

    'LiLadderHeight.li_rungs_of_bands_4000_upto_sharp' depends on axioms: [propext, Classical.choice, Quot.sound]

Token grep (sorry/admit/native_decide/axiom/opaque/unsafe/implemented_by/extern/partial/set_option):
nothing. Built .olean exists; only my probes were built.

## 3. Registry byte comparison (python)

- RH_li_ladder_height_sharp: `li_rung_of_zeros_on_line_below_sharp (T : ℝ) (hT : 1 ≤ T) (hline : ∀ ρ : ℂ,
  riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ T → ρ.re = 1 / 2) (n : ℕ) (hn : (n + 1 : ℝ) ≤
  2 * π * (T - 1 / 2)) : 0 ≤ (taylorCoeff riemannXi n).re` BYTE-IDENTICAL (status draft,
  depends_on RH_li_ladder_height).
- RH_li_rungs_of_height_4000_sharp: `li_rungs_of_bands_4000_upto_sharp (hall : ∀ ρ : ℂ, riemannZeta ρ
  = 0 → 0 < ρ.im → ρ.im ≤ 4000 → ρ.re = 1 / 2) : ∀ n : ℕ, n ≤ 25128 → 0 ≤ (taylorCoeff riemannXi n).re`
  BYTE-IDENTICAL (status draft, depends_on RH_li_ladder_height_sharp, RH_zeta_zero_im_ge).

## 4. Mathematics re-derived by hand

(a) Lemma A''. d = 2 pi - |b| in [0, pi/2) (probe 2); cos b = cos|b| = cos(2 pi - d) = cos d
(`Real.cos_two_pi_sub`, `Real.cos_abs`); |a| <= d <= |d| and |d| <= pi/2, so LiLadderHeight's
Lemma A applies. Checked.
(b) Lemma B''. |arg u| <= 1/|Im z| and |log|u|| <= 1/(2 (Im z)^2) (LiLadderHeight, |Im z| >= 1);
with g = |Im z|: 1/g + 1/(2g^2) = (2g+1)/(2g^2) <= 1/(g - 1/2) iff (2g+1)(g-1/2) <= 2g^2 iff
-1/2 <= 0 (probe 3). Checked.
(c) Theorem C''. a = N log|u|, b = N arg u, N = n + 1. |a| <= |b| from Lemma B's lower half;
|a| + |b| <= N/(|Im| - 1/2) <= 2 pi from B'' and n + 1 <= 2 pi (|Im| - 1/2). Split: |b| <= 3 pi/2
is Lemma A' (which itself splits at pi/2); |b| > 3 pi/2 gives |b| <= 2 pi and |a| <= 2 pi - |b|
from the sum bound and |a| >= 0, then Lemma A''. Exhaustive; re-composed abstractly in probe 1.
Checked. (The rvm twin splits into three explicit cases; here the first two are packaged in
Lemma A'. Same logic.)
(d) Theorem D''. Zeros with |Im| <= T on the line (LiLadderHeight); zeros with |Im| > T >= 1
satisfy n + 1 <= 2 pi (T - 1/2) <= 2 pi (|Im| - 1/2) by monotonicity. Then
`re_taylorCoeff_nonneg_of_termwise`. Checked.
(e) Height 4000. `line_hyp_of_upper_half 4000 hall noRealZeroInStrip` (audited with
LiLadderHeight) feeds D'' at T = 4000: n + 1 <= 2 pi (4000 - 1/2) = 7999 pi. Arithmetic:
7999 pi = 25129.5996; so n + 1 <= 25129 is fine and n + 1 = 25130 is not. Hence the exact
integer reach is n <= 25128. Proving 25129 <= 7999 pi needs pi > 3.141592 (7999 * 3.141592 =
25129.594); pi > 3.1415 gives only 25128.86 < 25129, too weak, as the lead noted. My probe 4 proves
both 25129 <= 7999 pi (from pi_gt_d6) and 7999 pi < 25130 (from pi_lt_d6), so the count is
exactly right; probe 9 shows pi_gt_d4 fails; probes 7 and 8 show rung 25129 is refused through
both forms. Checked. Versus LiLadderHeight's 18848: the sharp rate dominates for T >= 2 (probe 6).

## 5. Numerics

Identical to the rvm twin (same pair term): no negative term above threshold N/(2 pi) + 1/2 on
a 401 x 601 grid, first failures below it at gaps 0.605, 0.185, 0.076, 0.038 for N = 5, 20, 50,
100, minimum above tending to 0 at beta -> 0 (AUDIT_TESTIMONY_LI_LADDER_SHARP_2026-09-22.md
section 5; research/li_face_numerics.md section 2).

## 6. Probes (Probes/AuditLiSharp_Probes.lean)

Expected successes, all elaborated: three-case re-composition (1); deficit range (2); B''
algebra (3); exactness pair 25129 <= 7999 pi and 7999 pi < 25130 (4); consumption at rung 25128
(5); sharp dominates old rate for T >= 2 (6). Expected failures, each at the intended point:

    Probes/AuditLiSharp_Probes.lean:36:45: unsolved goals      -- rung 25129 via the `upto` form
    Probes/AuditLiSharp_Probes.lean:41:43: linarith failed     -- rung 25129 via the real form (25130 <= 7999 pi false)
    Probes/AuditLiSharp_Probes.lean:44:53: linarith failed     -- pi_gt_d4 too weak for 25129 <= 7999 pi
    Probes/AuditLiSharp_Probes.lean:49:48, 49:70: unsolved goals -- T = 1/2

## 7. Overclaim grep

LiLadderSharp.lean lines 30-32: "conjecture1_proved = False. Nothing here proves, or approaches,
the Riemann Hypothesis: ... the uniform `forall n` IS RH ... and is not touched." No other RH
language. Note the capstone's own 89 band hypotheses and hγ remain undischarged and unclaimed.

## 8. What this does and does not establish

Established, conditionally: rungs n + 1 <= 2 pi (T - 1/2) from zeros on the line up to T >= 1;
rungs 0..25128 from the height-4000 capstone's conclusion. Nothing unconditional is new here.
NOT a proof of anything about RH. conjecture1_proved = False.
