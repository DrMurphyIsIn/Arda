# Audit testimony: E6Bridge16, the sharp envelope of the Wall, 2026-09-21

AN UNCONDITIONAL c-UNIFORM ENVELOPE. NOT A PROOF OF THE RIEMANN HYPOTHESIS. E6Bridge16 proves,
with no hypothesis about zeros, that the Gaussian zero sum F(c, lam) is nonnegative for every
width lam > 0 once |c| ≥ envelopeCsharp lam, an explicit threshold whose only non-closed-form
ingredient is the convergent series primeAbs lam; and two height corollaries restating this for
|c| ≥ T. Nothing is concluded about where the zeros are. conjecture1_proved = False.

Auditor: blind adversarial auditor (separate agent). Worktree /Users/peterwmurphy/arda-goal-weil,
island telperion/examples/rvm_bridge/lean, Lean v4.33.0-rc2, Zeta23 pinned at
fbdc36bbf17d20af3fd0447c6d1a8a02773c9844. Artifact: E6Bridge16.lean (877 lines, namespace
RvMBridge16, imports E6Bridge10 and E6Bridge11) and memo WALL_SHARP_ENVELOPE_2026-09-21.md.
Probes: Probes/Audit16_Axioms.lean, Probes/Audit16_Probes.lean, plus mpmath/sieve checks
recorded below. No git state changed; no other file edited.

Overall verdict: PASS. No defect found. The complex-frequency transform, the evaluated pole
terms, the exact prime constant, the capped archimedean floor and the assembly all re-derive
correctly with every constant checked; the numerics reproduce the memo's table; the two height
corollaries are correct restatements, the log form losing exactly a factor 2 as its extra log 2
records; the memo's crossing widths are right for the exact form and it does not overclaim.

## 1. Kernel: PASS

`lake build`: `Build completed successfully (8855 jobs)` (newer modules have since been added to
defaultTargets; E6Bridge16 is at lakefile line 9 and a lean_lib at line 148). Guard carries 27
RvMBridge16 lines. Probes/Audit16_Axioms.lean prints axioms for all 30 declarations: 30 of 30
read `[propext, Classical.choice, Quot.sound]`, no sorryAx. Token grep for `sorry|admit|
native_decide|axiom|opaque|unsafe|implemented_by|extern|partial|set_option`: one hit, line 667
`set_option maxHeartbeats 1600000 in` on the sharp assembly theorem, an elaboration budget, not a
soundness option. Only the guard and the author's probe import E6Bridge16.

## 2. fourier_autocorrGauss: PASS

`∫ f(u) e^{iwu} du = gaussTest c lam w` for every w ∈ ℂ, f = autocorrGauss c lam = autocorr
(gaussPhi c lam) (E6Bridge11 `autocorr_gaussPhi_funext`). Derivation: f(u) = A(1 - u²/(4 lam))
e^{-u²/(8 lam)} e^{-icu}; with W = w - c and a = 1/(8 lam) the integrand is A e^{iWu} e^{-au²} -
A/(4 lam) · u² e^{-au²} e^{iWu}; Mathlib `fourierIntegral_gaussian` gives the first integral
√(π/a) e^{-W²/(4a)} and `integral_sq_mul_cexp_gaussian_fourier'` (second moment by parts, with
the majorant |x|² e^{-ax² + |Im W||x|} for complex W) the second; the normalisation
`gaussA_mul_sqrt : A √(8π lam) · 4 lam = 1` collapses the result to W² e^{-2 lam W²}. This is the
analytic continuation of |h|² = h(w) conj(h(conj w)) with h = paperFT (gaussPhi) from E6Bridge8,
consistent with the conj-on-second-factor convention of `autocorr` (mpmath: the direct integral at
w = 0.3 + 0.4i, c = 0.7, lam = 1 differs from (w-c)² e^{-2 lam (w-c)²} by 4.2e-22, and from
h(w) conj(h(conj w)) by the same 4.2e-22). Specialised to real r it is E6Bridge11's line formula,
and to w = ±i/2 the pole terms (probe 6 consumes both).

## 3. The pole terms: PASS

`weilKernel_zero_eq_gaussTest`: W(0) = ∫ f e^{-u/2} = ∫ f e^{i(i/2)u} = gaussTest c lam (i/2);
likewise W(1) at -i/2. `norm_gaussTest_half`: |(si - c)|² = c² + 1/4 and Re(-2 lam (si - c)²) =
-2 lam (c² - s²) = -2 lam (c² - 1/4) for s = ±1/2, so the modulus is (c² + 1/4) e^{-2 lam (c² - 1/4)}
(mpmath at c² = 6/lam + 1 for lam ∈ {0.1, 0.5, 1, 2, 5}: formula and direct value agree to all
digits). `norm_poles_le`: for c² ≥ 6/lam + 1 the two terms sum to ≤ 0.13 A: the proof bounds
20 e^{-6} √(2π) √lam e^{-lam/2} ≤ 20 · (1/400) · 2.51 · 1 = 0.1255 ≤ 0.13; numerically the actual
ratio 2|W|/A at the threshold is 4.1e-4 (lam = 0.1), 5.5e-4 (0.5), 4.0e-4 (1), 1.5e-4 (2),
3.7e-6 (5), far inside 0.13, and it decays in c² beyond the threshold since 6/lam + 1 ≥ 1/(2 lam),
the maximiser of x e^{-2 lam x}. The condition c² ≥ 6/lam + 1 follows from |c| ≥ 3/√lam + 1
(`hc2`: (3/√lam + 1)² ≥ 9/lam + 1 ≥ 6/lam + 1).

## 4. The prime bound: PASS

`norm_autocorrGauss_add_neg_le`: |f(u) + f(-u)| ≤ |f(u)| + |f(-u)| = 2A |1 - u²/(4 lam)|
e^{-u²/(8 lam)} (the e^{∓icu} phases have modulus 1; equivalently f(u) + f(-u) = 2A(1 - x)e^{..}
cos(cu) and |cos| ≤ 1). Times Λ(n)/√n and summed: ‖primeSide f‖ ≤ Σ Λ(n)/√n · 2A · term = 2A Σ
primeAbsTerm = A · primeAbs (`norm_primeSide_le_primeAbs`, via `norm_tsum_le_tsum_norm` and
`tsum_le_tsum`), the factor 2 being the ± log n pair and primeAbs carrying it as `2 * ∑'`.
Summability: `primeAbsTerm_le`: for n ≥ 2, Λ(n)/√n ≤ log n/√n ≤ 2 (from log √n ≤ √n - 1),
|1 - 2s| e^{-s} ≤ 2 e^{-s/2} with s = (log n)²/(8 lam), and e^{-(log n)²/(16 lam)} ≤ e^{16 lam}
n^{-2} (AM-GM), so primeAbsTerm ≤ 4 e^{16 lam}/n²; n ∈ {0, 1} give Λ = 0. Hence
`summable_primeAbsTerm` and `primeAbs_le_crude : primeAbs ≤ 16 e^{16 lam}` (Σ 1/n² ≤ 2). Sieve
evaluation (Λ by smallest-prime-factor sieve to n = 2·10⁶): primeAbs(0.5) = 8.7374,
primeAbs(1) = 23.7185, matching the memo's 8.7374 and 23.718; series tails at the cutoff are
≤ 1.4e-23 and 3.7e-12.

## 5. The archimedean floor: PASS

`re_digamma_quarter_ge_log'`: from Zeta23 `re_digamma_stirling' (0 < a ≤ 1) (1/2 ≤ |t|)`,
|Re ψ(a + it) - log|t|| ≤ 5/t², at a = 1/4, t = r/2 (|r| ≥ 2 gives |t| ≥ 1): 5/(r/2)² = 20/r², so
Re ψ(1/4 + ir/2) ≥ log(|r|/2) - 20/r². Tail mass: `integral_indicator_bumpR_tail_le'` with a free
L ≥ 0: bumpR c lam r ≤ e^{-lam L²} bumpR c (lam/2) r for |r - c| ≥ L, so the tail is ≤ e^{-lam L²}
2π A(lam/2) = e^{-lam L²} 2√2 · 2πA; with L = tailRadius, lam L² = 16 + 2P (`tailRadius_sq`), the
tail is e^{-16 - 2P} · 2√2 · 2πA. Capped floor: `integral_bumpR_mul_psiR_ge_capped` with any
0 ≤ Θ ≤ log((|c| - L)/2) - 20/(|c| - L)²: pointwise Bψ ≥ ΘB - (Θ + 5) 1_{tail} B (inside the window
|r| ≥ |c| - L ≥ 2 and ψ ≥ log(|r|/2) - 20/r² ≥ Θ, using monotonicity of log and 20/r² ≤ 20/(|c|-L)²;
outside ψ ≥ -5). The assembly takes Θ = log π + P + 0.31 and needs |c| - L ≥ 2π e^{P + 1/2} ≥ 10.3
(so 20/(|c| - L)² ≤ 0.19 and log((|c| - L)/2) ≥ log π + P + 1/2, whence Θ ≤ ... with 0.5 - 0.19 =
0.31): that is why envelopeCsharp carries 2π e^{P+1/2} + tailRadius + 3/√lam + 1. Final inequality:
Re(arch - prime) ≥ ΘA - (Θ+5) e^{-16-2P} A(lam/2) - A log π - 0.13A - PA; with (Θ + 5) e^{-2P} ≤ 6.7
(since e^{2P} ≥ 1 + 2P and Θ + 5 ≤ P + 6.7), e^{-16} ≤ 1/8·10⁶ (e^{16} = 8.886·10⁶), A(lam/2) =
2√2 A ≤ 3A, the tail is ≤ 2.5e-6 A, so F/A ≥ 0.31 - 0.13 - 2.5e-6 > 0. Every constant re-derived.
The centre enters only through |c| - L and the pole condition, so c < 0 is covered (probe 3
instantiates a negative centre).

## 6. Non-vacuity and load-bearing: PASS

`audit_envelopeCsharp_pos : 0 < lam → 0 < envelopeCsharp lam` (axiom-clean). The theorem is not
applicable at c = 0 (`Audit16_Probes.lean:17:58: error: linarith failed`, since envelopeCsharp lam
≤ 0 is false). Numerics from the definition (sieve to 2·10⁶): envelopeCsharp(0.5) = 6.457·10⁴ and
envelopeCsharp(1) = 2.071·10¹¹, matching the memo table's 6.457e4 and 2.071e11 to all printed
digits. The theorem's conclusion is consumed by both height corollaries (probe 3) and
`band_upper_edge` is the same statement with the quantifiers explicit.

## 7. Memo honesty and the height corollaries: PASS

Crossing widths for the EXACT form envelopeCsharp lam = T: at lam = 0.597, primeAbs = 11.027 and
envelopeCsharp = 6.37·10⁵ ≈ 640000 (memo: 11.03, lam_* = 0.597); at lam = 1.065, primeAbs = 26.34
and envelopeCsharp = 2.84·10¹² ≈ 3·10¹² (memo: 26.4, lam_* = 1.065). Confirmed. The memo's
"needs lam ≥ 1 for the ladder instrument; no overlap" is consistent with E6Bridge12's `hlam : 1 ≤
lam` hypotheses (audited 2026-09-21) and with envelopeCsharp(1) = 2.07·10¹¹ ≫ 640000. The LOG form
`gaussian_positivity_above_height_log` requires primeAbs + 1/2 + log 2 ≤ log(T/(2π)) and hadd
(additive terms ≤ the exponential term): from hadd, envelopeCsharp ≤ 2 · 2π e^{P+1/2}, and
log(2 · 2π e^{P+1/2}) = log(2π) + P + 1/2 + log 2 ≤ log T gives envelopeCsharp ≤ T; the extra
log 2 is exactly the doubling, as my own `audit_log_form` (axiom-clean) re-proves. Nuance, not an
overclaim: the log form is a factor 2 weaker than the exact form, so its crossing widths are
slightly smaller (it needs primeAbs ≤ 10.34 at T = 640000, lam ≈ 0.57, and ≤ 25.70 at 3·10¹², lam
≈ 1.05); the memo's lam_* table refers to the exact form, which is what
`gaussian_positivity_above_height` uses. The memo states the lead's targets are unreachable by any
c-uniform argument (the exact absolute prime sum forces ≥ 2π e^{23.7} at lam = 1) and that a
sharp closed-form bound on primeAbs does not close; both are stated as limits of the method, not
as theorems about zeros.

## 8. Overclaim: PASS

Grep over E6Bridge16.lean and the memo (prove(s/d) RH/Riemann, RH is/holds/proved, progress
toward, goal node proved, conjecture1_proved = True, crossing the wall, closes RH): the only hit
is the negation at memo line 3 "Nothing here proves RH." File lines 41-42: "Proves nothing about
RH. conjecture1_proved = False."; memo section 5 "What is and is not claimed" lists the
unconditional results and the non-closed items separately. No wording says more.

## Probe inventory

- Probes/Audit16_Axioms.lean: 30 axiom prints, 3 #check.
- Probes/Audit16_Probes.lean: `audit_envelopeCsharp_pos`, `audit_log_form` (axiom-clean); height
  corollaries for positive and negative centres, primeAbs summability and crude bound, transform
  specialisations (all elaborate); 1 expected failure (c = 0).
- mpmath/sieve: complex-frequency transform, pole modulus and 0.13 ratio at five widths, primeAbs
  and envelopeCsharp at 0.5, 0.597, 1, 1.065, the exact- and log-form crossing thresholds.
- Probes/E6Bridge16_probe.lean is the author's own and was not relied on.
