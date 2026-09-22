# Audit testimony: E6Bridge8 (O1' GaussianApprox) and E6Bridge9 (assembly), 2026-09-21

THIS IS NOT A PROOF OF THE RIEMANN HYPOTHESIS. What is kernel-checked here is Weil's
criterion, a classical theorem (Weil 1952; Bombieri 2000): Weil positivity of the E8
primes-side functional on Hermitian autocorrelations over the smooth compactly supported test
class is EQUIVALENT to Mathlib's `RiemannHypothesis`. Neither side of the equivalence is proved;
the MIRRORMERE goal statement is now RH-equivalent BY THEOREM and remains open exactly as RH is.
conjecture1_proved = False.

Auditor: blind adversarial auditor (separate agent). Worktree /Users/peterwmurphy/arda-goal-weil,
island telperion/examples/rvm_bridge/lean, Lean v4.33.0-rc2, Zeta23 pinned at
fbdc36bbf17d20af3fd0447c6d1a8a02773c9844. Artifacts: E6Bridge8.lean (646 lines, RvMBridge8),
E6Bridge9.lean (40 lines, RvMBridge9); memos WEIL_O1_GAUSSIAN_APPROX_2026-09-21.md and
PHASE0_GAUSSIAN_OBLIGATIONS_2026-09-21.md section B. Probes written by the auditor:
Probes/Audit8_Axioms.lean, Probes/Audit8_Witness.lean, plus mpmath checks recorded below.
No git state changed; no other file edited.

Overall verdict: PASS. No defect found. O1' is discharged by a genuine, nonzero, smooth,
compactly supported witness family with a correct Gaussian transform identity, a correct
dominated-convergence limit on the strip, and an n-uniform bound; the assembly theorems are
one-line compositions of previously audited inputs and are byte-identical to the registry
statements; no file or memo claims RH or progress toward it.

## 1. Kernel: PASS

`lake build`: `Build completed successfully (8837 jobs).` E6Bridge8 and E6Bridge9 are in
lakefile.toml defaultTargets (line 9) and declared as lean_libs (lines 79, 87);
AxiomGuardRvMBridge.lean carries 43 lines naming RvMBridge8/RvMBridge9.
Probes/Audit8_Axioms.lean prints axioms for all 47 declarations of E6Bridge8 and all 3 of
E6Bridge9 (every theorem/lemma/def line, extracted mechanically): 50 of 50 lines read
`depends on axioms: [propext, Classical.choice, Quot.sound]`. No sorryAx.
Token grep on both files for `sorry|admit|native_decide|axiom|opaque|unsafe|implemented_by|
extern|partial|set_option`: zero hits in either file (exit 1 both).

## 2. O1' honesty: PASS

(a) Witness is a Weil test and nonzero. `gaussTests c lam n u = gaussPhi c lam u * cutoff n u`
with `cutoff n u = bump (u/(n+1))`, `bump : ContDiffBump 0` of radii 1, 2 (E6Bridge8.lean:235-241).
`isWeilTest_gaussTests` (line 296): smooth by `contDiff_gaussPhi` times `contDiff_cutoff`,
compact support by `hasCompactSupport_cutoff` on [-2(n+1), 2(n+1)]. My own
`audit_gaussTests_ne_zero (hlam) (n) : gaussTests c lam n ≠ 0` (Audit8_Witness.lean) is
axiom-clean: at u = 1 the cutoff is 1 (`cutoff_eq_one`, |1| ≤ n+1), the exponential is nonzero,
and `gaussK_ne_zero` finishes. The conjunction IsWeilTest ∧ ≠ 0 elaborates for every n.

(b) Transform identity and conventions. Zeta23 `paperFT f z = ∫ f u * exp(I z u)` (Defs.lean:44);
Mathlib `fourierIntegral_gaussian (hb : 0 < b.re) t : ∫ cexp(I t x) cexp(-b x^2) = (π/b)^(1/2)
cexp(-t^2/(4b))` (Gaussian/FourierTransform.lean:200-202), same sign e^{+i t x}. The file's
`integral_mul_cexp_gaussian_fourier : ∫ x e^{-b x^2} e^{i w x} = (i w/(2b)) (π/b)^{1/2} e^{-w^2/(4b)}`
is one integration by parts of that (u = e^{iwx}, v = e^{-bx^2}). By hand: differentiating
Mathlib's identity in t gives ∫ i x e^{itx} e^{-bx^2} = (π/b)^{1/2} e^{-t^2/(4b)} (-2t/(4b)), so
∫ x e^{-bx^2} e^{itx} = (i t/(2b)) (π/b)^{1/2} e^{-t^2/(4b)}, matching. mpmath at 30 digits,
b = 1/4, w = 1 + i/2: lhs = 1.91334535315448285448862309661 + 3.21850757306776758247090303354 i,
rhs identical, |diff| = 2.0e-31. `paperFT_gaussPhi : paperFT (gaussPhi c lam) z = gaussHalf c lam z`
also checked at lam = 1, c = 0.7, z = 0.3 + 0.4i: |diff| = 0.0 at 30 digits. The constant
K = (2 lam i (π/b)^{1/2})^{-1} with b = 1/(4 lam) equals -i/(4 sqrt(π) lam^{3/2}), the value
PHASE0 section B derived independently.

(c) DCT limit. On |Im z| ≤ 1/2, `norm_cexp_I_mul_le`: ‖e^{izu}‖ = e^{-u Im z} ≤ e^{|u|/2}
(line 308-321). Majorant ‖K‖ |u| e^{-b u^2 + |u|/2} (`norm_gaussTests_mul_le`, uses |cutoff| ≤ 1),
integrable by `integrable_majorant` (from `integrable_abs_pow_mul_exp_quadratic_abs`, b > 0).
`paperFT_gaussTests_tendsto` applies `tendsto_integral_of_dominated_convergence`; the integrand
is eventually constant in n at each u (`cutoff_eq_one` once n + 1 ≥ |u|). The strip restriction
is load-bearing: the same bound for arbitrary z fails (Audit8_Witness.lean:38:28 unsolved goals,
expected).

(d) n-uniform bound. `#check @exists_paperFT_gaussTests_bound : ∀ {c lam}, 0 < lam → ∃ M, 0 ≤ M ∧
∀ (n : ℕ) (z : ℂ), |z.im| ≤ 1/2 → ‖paperFT (gaussTests c lam n) z‖ ≤ 2 * M / (1 + ‖z‖)`: the ∃ M is
outside ∀ n (Audit8_Witness probe 3 re-extracts it in that form). M = max(M0, M1) with
M0 = ∫ ‖K‖ |u| e^{-bu^2+|u|/2} and M1 = ∫ derivMajorant, and `derivMajorant c lam B u` (lines 461-465)
mentions only c, lam, B, u. The n-dependence of g_n' = phi' chi_n + phi chi'(u/(n+1))/(n+1) is
killed by |chi_n| ≤ 1 and |chi'(.)| · |1/(n+1)| ≤ B · 1 (lines 483-491, `h1n : |1/(n+1)| ≤ 1`),
B a global bound on |bump'| from `exists_deriv_bump_bound`. The 1/|z| comes from one
integration by parts (`I_mul_paperFT_eq`, valid for compactly supported g with continuous
derivative); cases ‖z‖ ≤ 1 / ‖z‖ > 1 give 2M/(1+‖z‖). Then C = 4M^2 and (1+‖z‖)^2 ≥ 1 + normSq z.
The final C in GaussianApprox is 4 M^2, again n-free.

(e) Exact type. `RvMBridge8.gaussian_approx : RvMBridge6.GaussianApprox` (#check) and
`example : RvMBridge6.GaussianApprox := RvMBridge8.gaussian_approx` elaborates with no error
(Audit8_Axioms.lean and Audit8_Witness.lean probe 4).

## 3. Assembly: PASS

E6Bridge9 has exactly three theorems, each a term-mode composition with no tactic block:
- `gaussian_transfer := RvMBridge6.gaussianTransfer_of_approx RvMBridge8.gaussian_approx`
- `weil_positivity_implies_rh hpos := RvMBridge7.weil_positivity_implies_rh_of_approx
  RvMBridge8.gaussian_approx hpos`
- `zeta_comb_membership_iff_rh := ⟨weil_positivity_implies_rh, RvMBridge5.rh_implies_weil_positivity⟩`
No new mathematics. The forward direction of the iff is RvMBridge5.rh_implies_weil_positivity
(audited 2026-09-20, PASS); the converse is the chain E6Bridge6 → E6Bridge7 (O2) → E6Bridge8 (O1').
I re-composed the iff from those four named inputs in my own probe (Audit8_Witness probe 4,
elaborates clean).
Byte comparison of the three theorem lines against
missions/mirrormere/lean/Statements/MM_{gaussian_transfer,weil_positivity_implies_rh,
zeta_comb_membership_iff_rh}.lean (island `:=` tail vs registry `:= by sorry` tail stripped):
`gaussian_transfer: IDENTICAL`, `weil_positivity_implies_rh: IDENTICAL`,
`zeta_comb_membership_iff_rh: IDENTICAL`. The registry's own MMDefs.lean mirrors of
`RvMBridge6.{hermitianTransform, zeroSide, gaussTest, GaussianTransfer, GaussianDominance,
GaussianApprox}` and `Zeta23.{paperFT, gammaOf, IsNontrivialZero}` are whitespace-normalised
IDENTICAL to the E6Bridge6 and Zeta23 sources (9 of 9), so the registry sentence means what
the island proves.

## 4. Overclaim check: PASS

Grep over E6Bridge8.lean, E6Bridge9.lean and both memos for wording claiming RH, progress
toward RH, or the goal node proved (patterns: "prove(s/d) (the) RH/Riemann", "RH is/holds/
proved", "progress toward", "goal node proved", "conjecture1_proved = True", "closes RH"):
the only hit is a negation, memo O1 line 9 "Nothing about zeta, zeros or RH is proved here."
Every RH mention in E6Bridge9 is the disclaimer: lines 15-19 "What this is NOT: a proof of RH.
zeta_comb_membership_iff_rh says the MIRRORMERE goal statement ... is EQUIVALENT to Mathlib's
RiemannHypothesis; it says nothing about whether either side holds. The goal node stays draft
and RH-hard, now for a proved reason. conjecture1_proved = False." Memo O1 lines 130-132:
"This is an implication, not RH: conjecture1_proved = False." E6Bridge8 line 4: "no zeta, no
zeros, nothing about RH (conjecture1_proved = False is untouched)". PHASE0 line 4: "Measures,
never claims. No Lean. conjecture1_proved = False." Registry: the goal node
MM_zeta_comb_membership stays kind = goal, status = draft; the two dictionary nodes are
kind = lemma. Nothing says more than the correct reading. One staleness, not an overclaim:
memo O1 line 10 says "The Weil converse still carries O2 (GaussianDominance)", written before
E6Bridge7; its final section, added later, records O2 closed.

## 5. Mathematics: PASS, no gap

Paper O1' and the Lean lemma for each step:
1. Gaussian transform at complex argument: ∫ u e^{-bu^2} e^{iwu} du = (iw/(2b)) sqrt(π/b)
   e^{-w^2/(4b)} for all w ∈ ℂ, from the Gaussian Fourier integral by one integration by parts
   (or by differentiating in w). [`integral_mul_cexp_gaussian_fourier`, then `paperFT_gaussPhi`
   with b = 1/(4 lam), K normalising to (z-c) e^{-lam (z-c)^2} = gaussHalf.]
2. gaussTest = h(z) conj(h(conj z)). [`gaussTest_eq_half_mul_conj`, same as my Audit6 probe.]
3. Truncation: g_n = phi · chi(u/(n+1)) is C_c^∞. [`isWeilTest_gaussTests`.]
4. DCT on the strip: |g_n(u) e^{izu}| ≤ ‖K‖|u| e^{-bu^2+|u|/2} integrable, integrand → phi(u)e^{izu}
   pointwise, so paperFT g_n z → gaussHalf z. [`paperFT_gaussTests_tendsto`.]
5. One integration by parts for 1/|z|: |z| |paperFT g_n z| ≤ ∫ |g_n'| e^{|u|/2}, with |g_n'|
   ≤ |phi'| + |phi| B uniformly in n; combined with the trivial bound, ≤ 2M/(1+|z|); squared for
   the Hermitian transform, ≤ 4M^2/(1+|z|^2). [`I_mul_paperFT_eq`, `norm_deriv_gaussTests_mul_le`,
   `norm_mul_paperFT_gaussTests_le`, `norm_paperFT_gaussTests_le`,
   `exists_paperFT_gaussTests_bound`, `gaussian_approx`.]
Gaps: none. Remarks: the O1 docstring in E6Bridge6 mentions a C/(1+x^2)^2 decay via two
integrations by parts; O1' as stated needs only C/(1+|z|^2), which one integration by parts
delivers (PHASE0 section B says the same). The strip bound e^{|u|/2} is exactly where
|Im z| ≤ 1/2 enters, and my probe confirms the bound is not provable off the strip.

## Probe inventory

- Probes/Audit8_Axioms.lean: 50 axiom prints, 3 #check lines, 1 shape example.
- Probes/Audit8_Witness.lean: `audit_gaussTests_ne_zero` (axiom-clean), IsWeilTest ∧ ≠ 0,
  n-free constant extraction, GaussianApprox/GaussianTransfer/iff re-composition (all success),
  1 expected failure (strip bound off the strip).
- mpmath (30 digits): Gaussian identity at b = 1/4, w = 1 + i/2 (|diff| 2e-31);
  paperFT_gaussPhi at lam = 1, c = 0.7, z = 0.3 + 0.4i (|diff| 0).
- Probes/E6Bridge8_probe.lean and E6Bridge8_converse_probe.lean are the author's own and were
  not relied on.
