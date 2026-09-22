The artifact is the sharpened exchange rate of the Li ladder on the rvm island (zeros on the line up to T >= 1 buy 0 <= Re liLimit N for N <= 2 pi (T - 1/2), and the closed forms archSide N + finiteSide N); a finite conditional implication; NOT a proof of anything about RH.

# Audit testimony: E6Bridge29 (rvm_bridge island)

Auditor: auditor-forward (blind, adversarial). Date: 2026-09-22.
Island: telperion/examples/rvm_bridge/lean, Lean v4.33.0-rc2, Zeta23 pinned fbdc36bb.
File: E6Bridge29.lean (147 lines, namespace RvMBridge29, 8 declarations, imports E6Bridge28).
Probes (mine): Probes/Audit29_Auditor_Axioms.lean, Probes/Audit29_Probes.lean. The author's
Probes/Audit29_Axioms.lean (9 lines) was read but not relied on. conjecture1_proved = False.

## 1. Verdict

PASS. One sentence: the last window 3 pi/2 < |b| <= 2 pi is closed by reflecting to the deficit
d = 2 pi - |b| in [0, pi/2) and applying E6Bridge28's Lemma A, the combined bound
|theta| + |log r| <= 1/(|gamma| - 1/2) follows from E6Bridge28's two bounds by an elementary
inequality, and the three-case Theorem C'' together with the unchanged regrouping gives the
registry node RH_li_ladder_liLimit_sharp with a byte-identical statement; numerics confirm the
rate N <= 2 pi (|Im| - 1/2) is the true termwise threshold up to o(1).

## 2. Kernel evidence (my runs)

Probes/Audit29_Auditor_Axioms.lean: 17/17 `#print axioms` = `[propext, Classical.choice, Quot.sound]`
(8 RvMBridge29 declarations, mechanically extracted, plus the consumed E6Bridge28 lemmas
cosh_mul_cos_le_one_of_abs_le, abs_arg_wOf_le, abs_log_norm_wOf_le, le_abs_arg_wOf, pair_re_eq,
pow_add_inv_pow_eq_cosh, pair_re_nonneg_of_on_line, liLimit_re_nonneg_of_pairs, and
RvMBridge27.liValue). Verbatim from Probes/Audit29_Probes.lean:

    'RvMBridge29.liLimit_re_nonneg_of_line_below_sharp' depends on axioms: [propext, Classical.choice, Quot.sound]

Token grep (sorry/admit/native_decide/axiom/opaque/unsafe/implemented_by/extern/partial/set_option):
nothing. Built .olean exists; E6Bridge29 is in lakefile defaultTargets and imported by
AxiomGuardRvMBridge.lean:176. Only my probes were built.

## 3. Registry byte comparison

missions/rh/lean/Statements/RH_li_ladder_liLimit_sharp.lean (sha256 76ff63f4de699718):

    theorem liLimit_re_nonneg_of_line_below_sharp (T : ℝ) (hT : 1 ≤ T)
        (hline : ∀ ρ, IsNontrivialZero ρ → |ρ.im| ≤ T → ρ.re = 1 / 2) (N : ℕ)
        (hN : (N : ℝ) ≤ 2 * Real.pi * (T - 1 / 2)) : 0 ≤ (liLimit N).re := by sorry

E6Bridge29 line 134: byte-IDENTICAL (python). Node toml: status draft, closure_clean false,
depends_on RH_li_ladder_liLimit.

## 4. Mathematics re-derived by hand

(a) Lemma A'' (window). For 3 pi/2 < |b| <= 2 pi put d = 2 pi - |b|; then 0 <= d < pi/2.
cos b = cos|b| = cos(2 pi - d) = cos d. With |a| <= d = |d| <= pi/2, Lemma A (E6Bridge28,
|a| <= |d| <= pi/2) gives cosh a cos d <= 1. The file's `hd1 : d < pi/2` and `hda : |a| <= |d|`
are exactly these steps; the edge |b| = 2 pi forces a = 0 and gives equality cosh 0 cos 2 pi = 1
(my probe 4). Checked; probe 2 re-proves the deficit range abstractly.
(b) Lemma B''. From E6Bridge28: |theta| <= 1/|gamma| and |log r| <= 1/(2 gamma^2) for
|gamma| >= 1. With g = |gamma| > 1/2: 1/g + 1/(2 g^2) = (2g + 1)/(2 g^2) <= 1/(g - 1/2) iff
(2g + 1)(g - 1/2) <= 2 g^2 iff 2g^2 - 1/2 <= 2g^2. True. Checked; probe 3 re-proves the
inequality abstractly. (The brief's "(2g+1)(2g-1) <= 4g^2" is the same inequality doubled.)
(c) Theorem C''. Set a = N log r, b = N theta. From E6Bridge28's Lemma B (|gamma| >= 1):
|a| <= |b|. From B'': |a| + |b| <= N/(|gamma| - 1/2) <= 2 pi using N <= 2 pi (|gamma| - 1/2).
Cases on |b|: (i) |b| <= pi/2: Lemma A. (ii) pi/2 < |b| <= 3 pi/2: cos b <= 0, cosh a > 0, product
<= 0 <= 1. (iii) |b| > 3 pi/2: |a| + |b| <= 2 pi and |a| >= 0 give |b| <= 2 pi and
|a| <= 2 pi - |b|, so Lemma A'' applies. Exhaustive. The term is 2 - 2 cosh a cos b >= 0.
Checked; probe 1 re-composes the three cases abstractly from |a| <= |b| and |a| + |b| <= 2 pi.
Note that |a| <= |b| is only used in case (i); cases (ii) and (iii) need only the sum bound.
(d) Theorem D''. Zeros with |Im| <= T are on the line (E6Bridge28's on-line lemma); zeros
with |Im| > T >= 1 satisfy N <= 2 pi (T - 1/2) <= 2 pi (|Im| - 1/2) (probe 7). Then the
regrouping `liLimit_re_nonneg_of_pairs` (audited in E6Bridge28) closes. Closed form via
RvMBridge27.liValue for N >= 1. Checked.
(e) Comparison with E6Bridge28's rate 3 pi T / 2: 2 pi (T - 1/2) >= 3 pi T / 2 iff T >= 2
(probe 5), so the sharp rate dominates from height 2 on; at T = 4000 it gives N <= 25130
versus 18849.

## 5. Numeric sharpness check (mpmath, dps 25; 401 betas incl. 1e-9 and 1 - 1e-9; 601 gammas)

Threshold thr(N) = N/(2 pi) + 1/2. Minimum of the pair term over beta in (0,1), gamma in
[max(1, thr), thr + 6], and the first gamma below thr (scanning down in steps of 0.0005 at the
strip edges beta -> 0, 1) where the term goes negative:

    N=  5 thr=1.2958 min=0.4445    first fail at gamma=0.6908 (gap 0.605)
    N= 10 thr=2.0915 min=1.329     first fail at gamma=1.7500 (gap 0.342)
    N= 20 thr=3.6831 min=0.5938    first fail at gamma=3.4986 (gap 0.185)
    N= 50 thr=8.4577 min=0.04479   first fail at gamma=8.3817 (gap 0.076)
    N=100 thr=16.4155 min=0.005709 first fail at gamma=16.3775 (gap 0.038)

(N = 1, 2, 3: min 0.02, 0.080, 0.178; no failure found at any gamma >= 0.05.) No negative term
above the threshold on the grid; the minimum above it sits at the strip edge beta -> 0 and tends
to 0 as N grows, and the first failure below it approaches the threshold with gap -> 0. This
matches the research memo (research/li_face_numerics.md, section 2): gamma_min(N) =
N/(2 pi) + 1/2 + o(1), attained as beta -> 0. The theorem's rate is therefore sharp for the
termwise method up to o(1); the residual gap is the slack in arctan x <= x and log(1+x) <= x.

## 6. Probes (Probes/Audit29_Probes.lean)

Expected successes, all elaborated: the three-case split re-composed (1); deficit in [0, pi/2)
(2); Lemma B'' inequality (3); window lemma at its equality edge a = 0, b = 2 pi (4); sharp rate
dominates the old one for T >= 2 (5); consumption at T = 3, N = 15 (6); threshold arithmetic (7).
Expected failures, each at the intended point:

    Probes/Audit29_Probes.lean:49:8:  linarith failed   -- N = 16 at T = 3 (5 pi < 16)
    Probes/Audit29_Probes.lean:53:49: unsolved goals    -- T = 1/2
    Probes/Audit29_Probes.lean:58:37, 59:62             -- window lemma offered b = pi (strict 3 pi/2 < |b| refused)

## 7. Overclaim grep

E6Bridge29.lean lines 20-22: "NOTHING here proves anything about RH: the theorems consume zero
localisation (a hypothesis) and produce sign information about finitely many Li coefficients.
conjecture1_proved = False." No other RH language. The research memo's line 3 carries the same flag.

## 8. What this does and does not establish

Established, conditionally: 0 <= Re(liLimit N) = Re(archSide N + finiteSide N) for
1 <= N <= 2 pi (T - 1/2) from zeros on the line up to T >= 1. Nothing unconditional is new
here (rungs 1..5 remain E6Bridge28's), nothing evaluates the sign for all N, and that uniform
statement is RH. NOT a proof of anything about RH. conjecture1_proved = False.
