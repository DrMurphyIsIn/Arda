# Audit testimony: E6Bridge18 (derivative partial-fraction skeleton) and E6Bridge20 (entire extension), 2026-09-21

A CONSTANT-FREE PARTIAL-FRACTION SKELETON MODULO TWO NAMED ANALYTIC OBLIGATIONS (LOGARITHMIC
GROWTH OF THE EXTENSION ON Re s ≥ 1/2; REAL-AXIS DECAY OF (ξ'/ξ)'). NOT A PROOF OF ANYTHING ABOUT
THE RIEMANN HYPOTHESIS. E6Bridge18 proves summability of the double-pole zero sum, its decay along
the real axis, Liouville with logarithmic growth, and the assembly of the identity
(ξ'/ξ)'(s) = -Σ m(ρ)/(s-ρ)² from the two obligations; E6Bridge20 proves the entire extension of
the regularised difference across the zeros, its functional equation, and the reduction of the
growth obligation to the half-plane. Nothing is concluded about where the zeros are.
conjecture1_proved = False.

Auditor: blind adversarial auditor (separate agent). Worktree /Users/peterwmurphy/arda-goal-weil,
island telperion/examples/rvm_bridge/lean, Lean v4.33.0-rc2, Zeta23 pinned at
fbdc36bbf17d20af3fd0447c6d1a8a02773c9844. Artifacts: E6Bridge18.lean (355 lines, RvMBridge18,
imports E6Bridge6) and E6Bridge20.lean (592 lines, RvMBridge20, imports E6Bridge15, E6Bridge18,
Zeta23.WeilEF.XiLogDeriv); memos XI_PARTIAL_FRACTION_2026-09-21.md and
XI_DIFF_REGULAR_2026-09-21.md. Probes: Probes/Audit18_Axioms.lean, Probes/Audit18_Probes.lean.
No git state changed; no other file edited.

Overall verdict: PASS. No defect found. ξ matches Zeta23's definition text and is 1/2 at both
poles of the completed zeta; the Liouville lemma is a correct Cauchy-estimate argument and is not
vacuous; the summability majorant and the Tannery decay re-derive; the order of ξ equals the
divisor multiplicity everywhere; the local double pole is cancelled exactly by the sum's own term
so the extension is entire; the functional equation carries the correct sign; the half-plane
reduction's constant is right; the two obligations are honest, non-closable, and the memos state
what remains.

## 1. Kernel: PASS

`lake build`: `Build completed successfully (8859 jobs)`. Both files in defaultTargets (lakefile
line 9) and lean_libs (lines 167, 175); guard carries 20 RvMBridge18 and 32 RvMBridge20 lines.
Probes/Audit18_Axioms.lean prints axioms for all 26 + 37 = 63 declarations: 63 of 63 read
`[propext, Classical.choice, Quot.sound]`, no sorryAx. Token greps (excluding the phrase "partial
fraction"): only the backticked `sorry` mentions in the headers (E6Bridge18 line 41, E6Bridge20
line 9). E6Bridge18 is imported by E6Bridge20, E6Bridge21, the guard and probes; E6Bridge20 by
E6Bridge22, the guard and probes. `#check`: `xi_logDeriv_deriv_eq_of : XiDiffRegular →
XiLogDerivDerivDecay → XiLogDerivDerivEq`; `xiDiffRegular_of_right : XiDiffExtGrowthRight →
XiDiffRegular`.

## 2. ξ versus Zeta23's ξ; ξ(0) = ξ(1) = 1/2; the zero set: PASS

Zeta23/WeilEF/Effective.lean:521: `def xi (s : ℂ) : ℂ := s * (s - 1) / 2 * completedRiemannZeta₀ s
+ 1/2`; E6Bridge18: `s * (s - 1) / 2 * completedRiemannZeta₀ s + 1 / 2` (#print), identical up to
spacing. `completedRiemannZeta₀` is entire (Mathlib `differentiable_completedZeta₀`), so ξ is
entire (`xi_differentiable`); `xi_eq` gives ξ = s(s-1)/2 · Λ off {0, 1}. At s = 1 and s = 0 the
factor s(s-1)/2 vanishes so ξ = 1/2: `xi_one` in the file, and my `audit_xi_zero`, `audit_xi_one`
(axiom-clean). `xi_eq_zero_iff`: for Re s ≥ 1, Λ = Γℝ · ζ near s (Zeta23
`completedZeta_eventuallyEq_mul`, Re s > 0) with both factors nonzero, and ξ(1) = 1/2; for Re s ≤ 0
by ξ(1 - s) = ξ(s) (`xi_one_sub` from Mathlib `completedRiemannZeta₀_one_sub`); in the strip
by Zeta23 `completedZeta_zeros_strip : (Λ ρ = 0 ↔ IsNontrivialZero ρ) ∧ analyticOrderAt Λ ρ =
analyticOrderAt ζ ρ` (XiLogDeriv.lean:95-97). So ξ's zeros are exactly the nontrivial zeros,
and ξ ≠ 0 off the strip and at 0, 1.

## 3. Liouville with logarithmic growth: PASS

`eq_const_of_log_growth`: C ≥ 0 from the bound at 0; for each z and R > 0, Cauchy's estimate
`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` gives ‖G'(z)‖ ≤ max_{|w-z|=R} ‖G w‖ / R ≤
C(1 + log(2 + ‖z‖ + R))/R (using ‖w‖ ≤ ‖z‖ + R and log monotone); the right side → 0 as R → ∞ by
`Real.tendsto_pow_log_div_mul_add_atTop 1 (-(2+a)) 1` composed with R ↦ 2 + a + R, which is
exactly log(2 + a + R)/R → 0 (the lemma's shape log x^n/(b x + c) at n = 1, b = 1, c = -(2+a)), plus
C/R → 0; hence G' ≡ 0 and `is_const_of_deriv_eq_zero`. Non-vacuity: my `audit_id_no_log_bound :
¬ ∃ C, ∀ z, ‖z‖ ≤ C(1 + log(2 + ‖z‖))` (axiom-clean), proved by applying the file's own lemma to
the identity function and reading off 1 = 0.

## 4. Summability: PASS

`norm_polTerm_le_majorant`: for a nontrivial zero with |Im ρ - Im s| ≥ 1, ‖s - ρ‖² ≥ (Im ρ - Im s)²
=: d² ≥ 1 and 1 + |γ_ρ|² ≤ 5/4 + t² ≤ 5/4 + 2 d² + 2 a² ≤ (13/4 + 2a²) d² (a = Im s, using d² ≥ 1), so
m/‖s-ρ‖² ≤ m (13/4 + 2a²)/(1 + |γ_ρ|²). Re-derived; correct. The finitely many zeros within
ordinate distance 1 (`finite_zeros_near` ⊆ Zeta23 `finite_window`) are absorbed as an indicator
in `polBound`; `summable_polBound` is `summable_of_ne_finset_zero` + E6Bridge6's local-count
majorant. Non-zeros give polTerm = 0. As the file notes, the "not a zero" hypothesis of
`summable_inv_sub_sq` is unused (at a zero the offending term is the junk value 0); probe 6
confirms `summable_polTerm s` for every s.

## 5. Decay of the sum: PASS

`norm_polTerm_le_real`: for real σ ≥ 2 and a strip zero, ‖σ - ρ‖² = (σ - Re ρ)² + Im ρ² ≥ 1 + Im ρ²
and 1 + |γ_ρ|² ≤ 5/4 + Im ρ² ≤ (5/4)(1 + Im ρ²), so the term is ≤ (5/4) m/(1 + |γ_ρ|²), summable.
Pointwise `polTerm_tendsto_zero`: ‖term‖ ≤ m/(σ - 1)² → 0 (Re ρ < 1). `tsum_inv_sub_sq_tendsto` is
Tannery (`tendsto_tsum_of_dominated_convergence`) with the bound holding eventually (σ ≥ 2).

## 6. The extension: PASS

`analyticOrderAt_xi_ne_top`: if ξ were locally zero at some s, the identity theorem on the
connected plane (`eqOn_zero_of_preconnected_of_eventuallyEq_zero`) would give ξ(1) = 0,
contradicting ξ(1) = 1/2. `analyticOrderAt_xi_eq_of_zero`: at a nontrivial zero ρ ≠ 0, 1,
`analyticOrderAt_mul` with the factor s(s-1)/2 of order 0 and Zeta23's
`completedZeta_zeros_strip` gives order(ξ) = order(ζ) = Zeta23.zeroMult = WeilExplicit.zeroMult
(`zeroMult_eq_of_strip`), cast through `ENat.natCast_toNat` using ≠ ⊤. Off the zeros
`analyticOrderAt_xi_eq` gives 0 = zeroMult (`analyticOrderAt_eq_zero` from ξ ≠ 0), so the identity
holds on AND off the strip (probe 6: order at 2 is 0). `exists_unit_factor`: Mathlib
`analyticOrderAt_eq_natCast` yields ξ = (z - s₀)^m u with u analytic, u(s₀) ≠ 0.
`deriv_logDeriv_xi_local`: on the ball, logDeriv ξ = m/(z - s₀) + logDeriv u (m = 0 case: ξ = u),
so (logDeriv ξ)' = -m/(w - s₀)² + (logDeriv u)'. `tsum_polTerm_eq` splits the tsum (indexed by
ρ : ℂ once, weight zeroMult) as polTerm w s₀ + Σ restTerm, and polTerm w s₀ = m/(w - s₀)² with
m = zeroMult s₀ = the order of ξ at s₀: the double pole is cancelled EXACTLY. `exists_ball_rest`:
the rest sum is differentiable on a ball avoiding all other zeros (`exists_ball_avoid` from the
finite `nearZeros`, then the Weierstrass M-test `differentiableOn_tsum_of_summable_norm` with the
majorant 4m/ε² on the finite near set plus the local-count majorant with A = 13/4 + 2(|Im s₀| + 1)²).
`exists_local_form`: xiDiffReg = (logDeriv u)' + rest =: H on the punctured ball, and at s₀ itself
when s₀ is not a zero. `xiDiffExt` is the punctured limit at zeros and xiDiffReg elsewhere;
`xiDiffExt_eventuallyEq` shows it equals H near every point (at a zero via `Tendsto.limUnder_eq`
from the continuity of H), hence `xiDiffExt_differentiable` on all of ℂ. Probe 7 confirms
`xiDiffExt_eq` is not available at a zero (application type mismatch), i.e. the extension's value
there is the limit, not the junk regularised value.

## 7. Functional equation: PASS

`logDeriv_xi_one_sub`: from ξ(1 - z) = ξ(z), differentiating u ↦ ξ(1 - u) gives -ξ'(1 - z) = ξ'(z),
so logDeriv ξ(1 - z) = -logDeriv ξ(z). `deriv_logDeriv_xi_one_sub`: differentiating
u ↦ logDeriv ξ(1 - u) = -logDeriv ξ(u) at s gives -(logDeriv ξ)'(1 - s) = -(logDeriv ξ)'(s), i.e.
(logDeriv ξ)'(1 - s) = +(logDeriv ξ)'(s) (chain-rule sign squared); my `audit_fe_sign`
(axiom-clean) re-proves this abstractly for any differentiable f with f(1 - z) = -f(z). The sum:
1 - ρ = reflect(conj ρ), so `zeroMult_one_sub` = `zeroMult_reflect` ∘ `zeroMult_conj`
(E6Bridge6, E6Bridge15), and ((1 - s) - ρ)² = (s - (1 - ρ))²; reindexing by `oneSubEquiv` gives
`tsum_polTerm_one_sub`. At zeros `xiDiffExt_one_sub` uses continuity of both sides (xiDiffExt is
differentiable) and agreement on the punctured neighbourhood.

## 8. Reduction to Re s ≥ 1/2: PASS

`xiDiffExtGrowth_of_right`: C ≥ 0 from the bound at s = 2; for Re s < 1/2 apply the bound at 1 - s
(Re ≥ 1/2), use `xiDiffExt_one_sub`, and ‖1 - s‖ ≤ 1 + ‖s‖ gives 2 + ‖1 - s‖ ≤ 2(2 + ‖s‖), so
log(2 + ‖1 - s‖) ≤ log(2 + ‖s‖) + log 2, whence C(1 + L + log 2) ≤ C(1 + log 2)(1 + L) since
C log 2 · L ≥ 0. Constant C(1 + log 2), as claimed.

## 9. Obligation honesty: PASS

`XiDiffExtGrowthRight` and `XiLogDerivDerivDecay` are `def : Prop` (#print of the former:
`∃ C, ∀ s, 1/2 ≤ s.re → ‖xiDiffExt s‖ ≤ C(1 + log(2 + ‖s‖))`), consumed only as hypotheses of
`xiDiffRegular_of_right` and `xi_logDeriv_deriv_eq_of`. Not automation-closable: simp with C = 1
(`Audit18_Probes.lean:20:34: unsolved goals`), aesop (`21:34: unsolved goals`), simp
(`22:66: simp made no progress`), aesop (`23:66: aesop failed, made no progress`). The full chain
`xi_logDeriv_deriv_eq_of (xiDiffRegular_of_right h1) h2 : XiLogDerivDerivEq` elaborates from
exactly the two (probe 4). The memos state what remains: XI_PARTIAL_FRACTION lines 46-64
(Landau's local partial fraction transferred to the derivative by Cauchy on 1/2 ≤ Re s ≤ 2,
Dirichlet series + Stirling on Re s ≥ 2, functional equation on the left; the decay of
-1/σ² - 1/(σ-1)² + (1/4)ψ'(σ/2) + (ζ'/ζ)'(σ) with ψ' = O(1/σ) and the Dirichlet series O(2^{-σ}));
XI_DIFF_REGULAR lines 56-77 ("The obligation (growth), where it stopped and why", the Re s ≥ 2 and
strip pieces, and that the decay obligation belongs to a parallel agent). Both carry
"conjecture1_proved = False" and record their expected-failure probes.

## 10. Overclaim: PASS

Grep over both files and both memos (prove(s/d) RH/Riemann, RH is/holds/proved, progress
toward, goal node proved, conjecture1_proved = True, Hadamard product proved, LiValue proved):
zero hits. E6Bridge18 line 42 "conjecture1_proved = False; nothing here bears on RH";
E6Bridge20 line 34 "conjecture1_proved = False. Nothing here bears on RH."

## Probe inventory

- Probes/Audit18_Axioms.lean: 63 axiom prints, 2 #check, 2 #print.
- Probes/Audit18_Probes.lean: `audit_xi_zero`, `audit_xi_one`, `audit_id_no_log_bound`,
  `audit_fe_sign` (axiom-clean); chain consumption, summability at every s, extension off zeros,
  order at 2 (all elaborate); 5 expected failures (four automation attempts on the obligations;
  `xiDiffExt_eq` at a zero).
- Probes/E6Bridge18_probe.lean, E6Bridge18_obligation_probe.lean, E6Bridge20_probe.lean,
  E6Bridge20_obligation_probe.lean are the authors' own and were not relied on.

## 11. Addendum: E6Bridge21, obligation 2 (real-axis decay) DISCHARGED: PASS

Artifact: E6Bridge21.lean (409 lines, namespace RvMBridge21, imports E6Bridge18,
Zeta23.Analytic.Stirling, Zeta23.RvM.GammaSide, Mathlib LSeries.Deriv and LSeries.Dirichlet).
Probes: Probes/Audit21_Axioms.lean, Probes/Audit21_Probes.lean, plus mpmath.

Status of the skeleton after this module: obligation 2 (`XiLogDerivDerivDecay`) is a THEOREM
(`xi_logDeriv_deriv_decay`), so `xi_logDeriv_deriv_eq_of_regular : XiDiffRegular →
XiLogDerivDerivEq`; with E6Bridge20 the single remaining obligation is `XiDiffExtGrowthRight`
(E6Bridge22 in flight, not audited here).

- Kernel: `lake build` green (8859 jobs); all 33 declarations print
  `[propext, Classical.choice, Quot.sound]`; token grep: only the header's own axiom line (30);
  guard 33 RvMBridge21 lines; E6Bridge21 imported by E6Bridge22, the guard and the author's probe.
  `#check xi_logDeriv_deriv_decay : RvMBridge18.XiLogDerivDerivDecay`,
  `xi_logDeriv_deriv_eq_of_regular : XiDiffRegular → XiLogDerivDerivEq`.
- (a) Signs and normalisation. Zeta23 `logDeriv_completedZeta (hs1) (hζ) (0 < Re s) : logDeriv Λ s
  = logDeriv Γℝ s + logDeriv ζ s` (XiLogDeriv.lean:67-69) and `RvM.logDeriv_Gammaℝ (0 < Re s) :
  logDeriv Γℝ s = -(log π)/2 + (1/2) ψ(s/2)` (GammaSide.lean:65-66); Mathlib
  `LSeries_vonMangoldt_eq_deriv_riemannZeta_div (1 < Re s) : L ↗Λ s = -deriv ζ s / ζ s`
  (Dirichlet.lean:436-437), so `logDeriv_zeta_eq : logDeriv ζ s = -L(Λ)(s)`. Hence
  `logDeriv_xi_eq_of_one_lt_re`: logDeriv ξ = s⁻¹ + (s-1)⁻¹ + (-(log π)/2 + ψ(s/2)/2) - L(Λ)(s),
  the constant -(log π)/2 differentiating to 0 and ψ(s/2)/2 to (1/4)ψ'(s/2) (chain rule, `hψ`, `h3`).
- (b) The L-series derivative. Mathlib `LSeries_hasDerivAt (h : abscissaOfAbsConv f < Re s) :
  HasDerivAt (LSeries f) (-LSeries (logMul f) s) s` (Deriv.lean:80-81) with
  `LSeries.logMul f n := log n * f n` (Deriv.lean:42, complex log); the abscissa of Λ is ≤ 1
  (`abscissa_vonMangoldt_le_one` from `LSeriesSummable_vonMangoldt`). So deriv(-L(Λ)) =
  +L(logMul Λ) (`deriv_logDeriv_zeta_eq`, `neg_neg`). Numerically (sieve to 2·10⁵):
  L(logMul Λ)(3) = 0.17228 = the numerical derivative of ζ'/ζ at 3 (0.17228), both positive.
- (c) Trigamma across the integers. Zeta23 `Stirling.hasSum_trigamma (z ∈ integerComplement) :
  HasSum (fun n => 1/(z+n)²) (deriv digamma z)`. `hasSum_trigamma_of_re_pos (1/2 < Re z)` extends
  it to integer z: the series side is continuous on Re w > 1/2 by `continuousOn_tsum` with the
  uniform majorant ‖1/(w+n)²‖ ≤ 1/(n + 1/2)² (from ‖w + n‖ ≥ Re(w + n) ≥ n + 1/2, valid for
  Re w ≥ 1/2, no ε needed; summable by comparison with 4/(n+1)²); the digamma side is continuous
  (digamma analytic on Re z > 0, `continuousAt_deriv_digamma`); the two agree on the punctured ball
  of radius 1/2 (no other integer within 1/2, `eq_of_intCast_near`), so `tendsto_nhds_unique`
  gives equality at z. Sound.
- (d) Telescoping. For a ≥ 1, 1/a² ≤ 1/(a - 1/2) - 1/(a + 1/2) = 1/(a² - 1/4) (my `audit_telescope`,
  axiom-clean); summed, Σ_{i<N} 1/(x+i)² ≤ 1/(x - 1/2) - 1/(x + N - 1/2) (`sum_range_inv_sq_le`),
  hence Σ' ≤ 1/(x - 1/2) (`tsum_inv_sq_real_le`) and `norm_deriv_digamma_real_le (1 ≤ x) :
  ‖ψ'(x)‖ ≤ 1/(x - 1/2)`. mpmath: ψ'(1) = 1.6449 ≤ 2, ψ'(2) = 0.6449 ≤ 0.6667, ψ'(5) = 0.2213 ≤
  0.2222, ψ'(20) = 0.05127 ≤ 0.05128. Then `digamma_deriv_tendsto_zero`: ψ'(σ/2) → 0.
- (e) Tannery for L(logMul Λ)(σ) → 0. Term n = 0 is 0 (`LSeries.term_zero`); n = 1 is 0 since
  log 1 = 0 (`term_logMul_one`); n ≥ 2: ‖term‖ = ‖logMul Λ n‖/n^σ → 0 (`term_tendsto_zero`, base
  n > 1); for σ ≥ 2 each term is dominated by its σ = 2 value (`norm_term_le_of_two_le`, n^σ ≥ n²),
  and the σ = 2 terms are absolutely summable (`LSeriesSummable_logMul_of_lt_re`, abscissa < 2).
  `zeta_logDeriv_deriv_tendsto_zero` then applies `tendsto_tsum_of_dominated_convergence`.
- Termwise formula. `deriv_logDeriv_xi_real (2 ≤ σ) : deriv (logDeriv ξ) σ = -1/σ² - 1/(σ-1)² +
  (1/4) ψ'(σ/2) + deriv (logDeriv ζ) σ`, obtained by differentiating the Re s > 1 identity on the
  open set (`Filter.EventuallyEq.deriv_eq`) with the four HasDerivAt pieces. mpmath check with
  ξ(s) = s(s-1)/2 · Λ(s) (Λ with poles; equivalently s(s-1)/2 · Λ₀ + 1/2, the two agreeing to
  1e-26): direct numerical derivative of ξ'/ξ versus the termwise formula, |diff| = 1.6e-27 at
  σ = 3 and 8.1e-28 at σ = 7. (A first attempt of mine that wrongly added +1/2 to the Λ form
  disagreed by 0.018; the file is right and my construction was wrong.)
- Assembly `xi_logDeriv_deriv_decay`: the four pieces' limits (rational terms → 0,
  (1/4)ψ'(σ/2) → 0, (ζ'/ζ)'(σ) → 0) added, and `congr'` with the termwise formula eventually
  (σ ≥ 2). Probes: `xi_logDeriv_deriv_decay`, `xi_logDeriv_deriv_eq_of_regular`, the termwise
  formula at σ = 3, both sign lemmas, the trigamma series at the integer 2, the bound at x = 1
  all elaborate.
- Overclaim: header lines 7 and 29-30 "nothing here bears on RH; conjecture1_proved = False",
  "no named obligation remains on this side" (true: obligation 2 only). No wording says more.
