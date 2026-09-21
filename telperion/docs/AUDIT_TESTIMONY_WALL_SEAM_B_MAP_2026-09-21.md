# Audit testimony: E6Bridge11 (seam B, small width) and E6Bridge13 (the Wall map), 2026-09-21

AN UNCONDITIONAL SMALL-WIDTH THEOREM PLUS AN EQUIVALENCE. NOT A PROOF OF THE RIEMANN
HYPOTHESIS. E6Bridge11 proves, with no hypothesis, that the primes-side Weil functional of the
Gaussian-derivative autocorrelation is nonnegative for every centre c and every width
0 < lam ≤ lam₀ = 10^-7 (and, in its envelope form, for every lam once |c| is large); E6Bridge13
composes this with seam A to state RH as equivalent to Gaussian positivity on widths strictly
above lam₀. Neither side of the equivalence is asserted. conjecture1_proved = False.

Auditor: blind adversarial auditor (separate agent). Worktree /Users/peterwmurphy/arda-goal-weil,
island telperion/examples/rvm_bridge/lean, Lean v4.33.0-rc2, Zeta23 pinned at
fbdc36bbf17d20af3fd0447c6d1a8a02773c9844. Artifacts: E6Bridge11.lean (1489 lines at audit time,
namespace RvMBridge11, imports E6Bridge8, E6Bridge10 and four Zeta23 files) and E6Bridge13.lean
(52 lines); memo WALL_SEAM_B_SMALL_LAM_2026-09-21.md (extended during the audit to cover the
envelope form). Probes: Probes/Audit11_Axioms.lean, Probes/Audit11_Probes.lean, plus mpmath checks
recorded below. No git state changed; no other file edited.

Overall verdict: PASS. No defect found. Every constant and every inequality direction in the
c-uniform small-width bound re-derives correctly; the mechanism uses c only through a modulus-1
phase and a translation-invariant bump, so no step assumes c large or c ≥ 0; the archimedean and
prime sides are the seam A objects, not redefined; E6Bridge13 adds no mathematics; the
equivalence's converse genuinely needs the above-threshold hypothesis; nothing overclaims.

## 1. Kernel: PASS

`lake build`: `Build completed successfully (8845 jobs).` Both files in defaultTargets (lakefile
line 9); guard carries 44 RvMBridge11 lines and 4 RvMBridge13 lines. Probes/Audit11_Axioms.lean
prints axioms for every mechanically extracted declaration (66 in E6Bridge11, 3 in E6Bridge13,
plus R₀ and lam₀): 70 of 70 read `[propext, Classical.choice, Quot.sound]`, no sorryAx. Token
grep for `sorry|admit|native_decide|axiom|opaque|unsafe|implemented_by|extern|partial|set_option`:
zero hits in either file. Only E6Bridge13, the guard and the author's probe import E6Bridge11.
`#check`: `re_weilForm_gauss_nonneg : ∀ (c lam : ℝ), 0 < lam → lam ≤ RvMBridge11.lam₀ → 0 ≤
(archSide (autocorr (gaussPhi c lam)) - primeSide (autocorr (gaussPhi c lam))).re`;
`rh_iff_gaussian_positivity_above_lam₀ : RiemannHypothesis ↔ ∀ (c lam : ℝ), RvMBridge11.lam₀ < lam
→ 0 ≤ (zeroSide (gaussTest c lam)).re`; `lam₀ = 1 / 10000000`.

## 2. c-uniformity of re_weilForm_gauss_nonneg: PASS (every constant re-derived)

Closed form (`autocorr_gaussPhi`, lines 310-352): f(u) = A (1 - u²/(4 lam)) e^{-u²/(8 lam)} e^{-icu},
A = 1/(8 √(2π) lam^{3/2}). Derivation: with b = 1/(4 lam), phi(v) conj phi(v-u) = |K|² v(v-u)
e^{-b(v² + (v-u)²)} e^{-icu}; shift v = w + u/2 gives v² + (v-u)² = 2w² + u²/2 and v(v-u) = w² - u²/4;
∫(w² - u²/4) e^{-2b w²} dw = √(π/2b)(1/(4b) - u²/4); |K|² = 1/(16 π lam³); assembling gives the
stated A and factor (1 - u²/(4 lam)). mpmath (25 digits): |direct autocorr - closed form| =
3.6e-27 at (c, lam) = (0.7, 0.3) and 7.8e-26 at (-5, 0.05); f(0) = A to 1e-25. The phase e^{-icu}
is the ONLY place c enters f, and it has modulus 1 (`norm_autocorrGauss_le` drops it via
`(-(I c u)).re = 0`), so the majorant |f(u)| ≤ 2A e^{-u²/(16 lam)} is c-free: |1 - 2s| e^{-s} ≤
2 e^{-s/2} with s = u²/(8 lam) (`abs_one_sub_two_mul_exp_le`, from 1 + 2s ≤ 2 e^{s/2}).

Prime side (`prime_term_bound`, `norm_primeSide_le`): |f(±log n)| ≤ 2A e^{-(log n)²/(16 lam)};
for n ≥ 2, (log n)²/(16 lam) ≥ σ log n with σ = log 2/(16 lam), so e^{-...} ≤ n^{-σ} = n^{-(σ-2)}
n^{-2} ≤ 2^{-(σ-2)} n^{-2} once σ ≥ 2; Λ(n)/√n ≤ log n/√n ≤ 2; term ≤ 8A 2^{-(σ-2)}/n²; Σ 1/n² =
π²/6 ≤ 2 (`hasSum_zeta_two`); total ≤ 16A 2^{-(σ-2)} = 64A 2^{-σ} = 64A e^{-(log 2)²/(16 lam)}.
Every step c-free.

Pole terms (`norm_integral_autocorrGauss_mul_exp_le`, lines 512-565): for |k| ≤ 1/2, |f(u)| e^{ku}
≤ 2A e^{-u²/(16 lam)} e^{|u|/2} and |u|/2 ≤ 2 lam + u²/(32 lam) (AM-GM, (|u| - 8 lam)² ≥ 0), so the
integrand is ≤ 2A e^{2 lam} e^{-u²/(32 lam)} and ∫ = 2A e^{2 lam} √(32 π lam) (`integral_gaussian`).
weilKernel f 0 and f 1 are exactly these integrals at k = ∓1/2 (`weilKernel_zero_eq`,
`weilKernel_one_eq`). c-free.

Line transform (`weilKernel_autocorrGauss_line`, lines 717-807): weilKernel f (1/2 + i r) =
∫ f(u) e^{iru} du = (r-c)² e^{-2 lam (r-c)²} = bumpR c lam r, by the second Gaussian moment at
real frequency (`integral_sq_mul_cexp_gaussian_fourier`, one integration by parts against
Mathlib's `fourierIntegral_gaussian` and E6Bridge8's first-moment identity). This is consistent
with E6Bridge8: paperFT (autocorr phi) = paperFT phi · conj(paperFT phi) = |(r-c) e^{-lam (r-c)²}|²
on the real axis, and with the conjugation convention of `autocorr` (conj on the second factor,
argument v - u). mpmath: |W(1/2 + i r) - bumpR(r)| = 6.5e-27 and 0.0 at the two test points.
"Plancherel by hand": ∫ bumpR = √(π/(2 lam))/(4 lam) = 2πA (`integral_bumpR`); mpmath
|∫B - 2πA| ≤ 4.1e-25. Also f(0) = A = (1/2π)∫|h|², consistent.

Digamma bounds. Zeta23 `re_digamma_vertical (0 < a) (a < 1) (t) : Re ψ(a + I t) = -γ - a/(a²+t²)
+ Σ_n (1/(n+1) - (n+1+a)/((n+1+a)² + t²))` (Mu.lean:79-83). With a = 1/4: a/(a²+t²) ≤ 4, each
series term ≥ 0 (since (n+1+a)/((n+1+a)²+t²) ≤ 1/(n+1+a) ≤ 1/(n+1)), γ < 2/3, so Re ψ ≥ -2/3 - 4 >
-5 (`re_digamma_quarter_ge`). Zeta23 `re_digamma_stirling' (0 < a) (a ≤ 1) (1/2 ≤ |t|) :
|Re ψ(a + I t) - log|t|| ≤ 5/t²` (StirlingVert.lean:588-589). With t = r/2 and |r| ≥ 41: |t| ≥
20.5 > e³ so log|t| ≥ 3, and 5/t² ≤ 1, so Re ψ ≥ 2 (`re_digamma_quarter_ge_two`). Variable
convention: archIntegrand uses ψ(1/4 + (r/2) I); `psiR_eq` rewrites it to ((1/4:ℝ):ℂ) + I *
((r/2:ℝ):ℂ), i.e. t = r/2, matching both Zeta23 lemmas. mpmath: min Re ψ(1/4 + it) on [-40, 40] =
-4.227 ≥ -5; Re ψ(1/4 + 20.5 i) = 3.020 ≥ 2. Both lemmas are pointwise in r and know nothing of c.

Archimedean lower bound (`integral_bumpR_mul_psiR_ge`): pointwise Bψ ≥ 2B - 7·1_{|r|<R₀} B (inside:
ψ ≥ -5 = 2 - 7; outside: ψ ≥ 2), integrate: ≥ 2·2πA - 7 ∫_{|r|<R₀} B ≥ 4πA - 7 R₀/lam using
B ≤ 1/(2 lam) (`bumpR_le`, y e^{-y} ≤ 1) on an interval of length 2R₀. The bump's position c is
irrelevant: the only c-dependence would help (Re ψ ~ log(|c|/2) near r ~ c) and is not used.

Assembly (`re_archSide_ge`, `re_weilForm_gauss_nonneg`, lines 1010-1118): Re(arch - prime) ≥
A(2 - log π) - 2·2A e^{2 lam}√(32π lam) - 7R₀/(2π lam) - 64A e^{-(log 2)²/(16 lam)}. The Lean
closes at lam ≤ 10^-7 with: log π ≤ 2 log 2 ≤ 1.3863 (so first term ≥ 0.6137A); √lam ≤ 1/3000,
e^{2 lam} ≤ 3, √(32π) ≤ 11, so poles ≤ 4·3·11/3000 A = 0.044A; 7·41/(2π lam) ≤ 0.32A ⟺
287 √(2π) √lam ≤ 0.08π, and 287·2.51/3000 = 0.2401 ≤ 0.2513 (tight, valid); (log 2)²/(16 lam) ≥
64000 so 64 e^{-x} ≤ 64/x ≤ 0.001A. Sum: 0.6137 - 0.044 - 0.32 - 0.001 = 0.2487 > 0. All inequality
directions checked by hand. mpmath with exact constants: F/A ≥ 0.553 at lam = 10^-7, 1.3e-4 at
8·10^-7, -0.10 at 10^-6, matching the memo's "nonnegative for lam ≤ 8.0e-7". The side condition
σ ≥ 2 holds since log 2/(16·10^-7) ≈ 4.3·10^5.

Consistency with WALL_LANDSCAPE: the arch side itself is negative at c = 0 for lam ≥ 0.02 (the
memo's own table shows arch = -4.33 at (0, 0.02)); lam₀ = 10^-7 is 2·10^5 times smaller, where
the bound gives 0.55A. No conflict. No step assumes c ≥ 0 or c large: probe instantiates the
theorem at c = -123456789 and c = 0 (both elaborate).

Envelope form (section L, not in the brief; audited because it is a further unconditional
claim): `re_weilForm_gauss_nonneg_of_large_c` and `gaussian_positivity_envelope` say F(c, lam) ≥ 0
for every lam > 0 once |c| ≥ envelopeC lam = 2 e^{9 + 2X} + 2/√lam, X = 4 e^{2 lam}√(32π lam) +
16 e^{16 lam}. Mechanism: the c-uniform prime bound |prime| ≤ 16 e^{16 lam} A
(`norm_primeSide_le_uniform`, via (log n)²/(16 lam) ≥ 2 log n - 16 lam); Re ψ(1/4 + ir/2) ≥
log(|r|/2) - 5 for |r| ≥ 2 (`re_digamma_quarter_ge_log`, from the same Stirling lemma with
5/t² ≤ 5); bump mass outside |r - c| < L = 2/√lam is ≤ e^{-4} ∫ bumpR at width lam/2 = e^{-4}
2π·2√2 A (`integral_indicator_bumpR_tail_le`, `gaussA_half`); inside, |r| ≥ |c| - L via
`abs_sub_abs_le_abs_sub`, so ψ ≥ θ := log((|c| - L)/2) - 5 ≥ 4 + 2X. I re-derived the closing:
θ(1 - 2√2 e^{-4}) - 5·2√2 e^{-4} - 1.3863 - X ≥ 0.948(4 + 2X) - 1.645 - X > 0. Consistent with
E6Bridge7's dominance (both elaborate side by side in my probe): dominance picks lam AFTER c, and
envelopeC lam grows doubly exponentially in lam, so an off-line zero at height γ₀ is never
inside the envelope region for the lam dominance chooses. The memo, as extended during this
audit, documents this form in its section 4b.

## 3. Honest values: PASS

E6Bridge11 defines none of `archSide, primeSide, autocorr, weilKernel, archIntegrand, zeroMult,
IsWeilTest, zeroSide, gaussTest, gaussPhi` (grep exit 1); it consumes WeilExplicit's and
E6Bridge8's. The objects archSide (autocorr (gaussPhi c lam)) and primeSide (...) are those the
seam A audit certified honest (integrable archimedean integrand, summable prime family,
integrable kernel integrand; AUDIT_TESTIMONY_WALL_SEAM_A section 2(e)). Here they are in fact
computed: `autocorr_gaussPhi` gives the closed form, `integrable_bumpR_mul_psiR` the archimedean
integrability, and `norm_primeSide_le` bounds a summable tsum by `norm_tsum_le_tsum_norm`.

## 4. E6Bridge13: PASS

`gaussianExplicitFormula` is literally `intro c lam hlam; rw [RvMBridge10.zeroSide_gaussTest_eq c
lam hlam]` (E6Bridge13.lean:25-27); E6Bridge11 section K also proves it the same way. The wall
map is the case split: forward from seam A's `rh_iff_gaussian_positivity.mp` at lam > lam₀ > 0;
converse via `rh_iff_gaussian_positivity.mpr` with `le_or_gt lam lam₀`, the free half from
`gaussian_positivity_small_lam` and the other half from the hypothesis. I re-composed both
directions from the named inputs in my probe (elaborates). Deleting the above-threshold
hypothesis (trying the small-width theorem at lam > lam₀) fails:
`Audit11_Probes.lean:37:60: error: Application type mismatch` (lam₀ < lam is not lam ≤ lam₀).

## 5. Non-vacuity: PASS

`0 < lam₀` and `∃ lam, 0 < lam ∧ lam ≤ lam₀` elaborate. Positivity on the region is not
automation-trivial: `simp [zeroSide, gaussTest]` → `41:43: error: unsolved goals`; `positivity` on
the primes-side form → `45:2: error: failed to prove positivity`. The threshold is load-bearing:
`re_weilForm_gauss_nonneg c 1 one_pos (by norm_num)` fails (`51:40: unsolved goals`, 1 ≤ 10^-7).
The memo states the true threshold is numerically much larger ("F ≥ 0 on the whole tested grid
lam ≤ 1") as numerics, with the theorem's lam₀ = 10^-7 called "crude by design"; it does not
claim the larger threshold as a theorem.

## 6. Overclaim: PASS

Grep over E6Bridge11.lean, E6Bridge13.lean and the memo: the only hits are negations
("Nothing here proves RH", memo line 3; "(it would prove RH)", memo line 348, explaining why no
c-uniform bound can exist at lam of order one). Disclaimers: E6Bridge11 line 43 "Proves nothing
about RH. conjecture1_proved = False."; E6Bridge13 lines 15-16 "NOT a proof of RH: an equivalence
says nothing about whether either side holds." Yoshida 1992: memo section 6 gives the citation and
says "the primary text was NOT accessed from this session, so the exact statement/normalisation in
Yoshida is marked UNRESOLVED", attributing the mechanism, not a reused theorem. Confirmed.

## 7. Paper re-derivation and lemma map: PASS, no gap

1. f = phi ⋆ phi~ in closed form [`gaussPhi_mul_conj`, `autocorr_gaussPhi_eq_integral`,
   `integral_sq_sub_mul_cexp`, `gaussK_mul_conj`, `autocorr_gaussPhi`]; majorant
   [`norm_autocorrGauss_le`].
2. Prime side ≤ 64A e^{-(log 2)²/(16 lam)} [`prime_term_bound`, `norm_primeSide_le`].
3. Pole terms ≤ 2A e^{2 lam}√(32π lam) each [`norm_integral_autocorrGauss_mul_exp_le`,
   `norm_weilKernel_zero_le`, `norm_weilKernel_one_le`].
4. Line transform = bump, mass 2πA [`integral_sq_mul_cexp_gaussian_fourier`,
   `weilKernel_autocorrGauss_line`, `integral_bumpR`].
5. Re ψ ≥ -5 and ≥ 2 beyond 41 [`re_digamma_quarter_ge`, `re_digamma_quarter_ge_two`, `psiR_ge`,
   `psiR_ge_two`]; ∫Bψ ≥ 4πA - 7R₀/lam [`bumpR_le`, `setIntegral_bumpR_le`,
   `integral_bumpR_mul_psiR_ge`; integrability `integrable_bumpR_mul_psiR` via Zeta23
   `digamma_growth_strip`].
6. Assembly [`integral_archIntegrand_eq`, `re_archSide_ge`, `re_weilForm_gauss_nonneg`]; transfer
   to the zero side by the seam A identity [`gaussianExplicitFormula`,
   `gaussian_positivity_small_lam(_explicit)`]; wall map [E6Bridge13].
Gaps: none. Remark: the Lean's closing constant 0.2487 is weaker than the exact-constant value
0.553 because it rounds each factor; both are positive, and the theorem's lam₀ is stated as
crude.

## Probe inventory

- Probes/Audit11_Axioms.lean: 70 axiom prints, 2 #check, 1 #print.
- Probes/Audit11_Probes.lean: 8 elaboration successes (lam₀ > 0, region nonempty, c = -123456789
  and c = 0 instances, discharge re-proof, wall map re-composition, envelope and dominance side by
  side), 4 expected failures (hypothesis above lam₀ deleted; simp; positivity; lam = 1).
- mpmath (25 digits): closed form, f(0) = A, ∫B = 2πA, line transform, digamma bounds, assembly at
  lam = 10^-7, 8·10^-7, 10^-6.
- Probes/E6Bridge11_probe.lean is the author's own and was not relied on.
