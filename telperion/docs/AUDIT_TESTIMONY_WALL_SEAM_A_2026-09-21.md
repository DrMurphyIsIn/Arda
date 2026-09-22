# Audit testimony: E6Bridge10, the two-parameter Wall (seam A), 2026-09-21

EQUIVALENCES ONLY. NOT A PROOF OF THE RIEMANN HYPOTHESIS AND NOT A PROOF OF EITHER SIDE OF ANY
EQUIVALENCE. E6Bridge10 proves that Mathlib's `RiemannHypothesis` is equivalent to a
two-parameter Gaussian positivity statement, and that the Gaussian-weighted zero sum equals an
explicit archimedean-minus-prime expression; no side of any `↔` is asserted, and no `=` involves
RH. conjecture1_proved = False.

Auditor: blind adversarial auditor (separate agent). Worktree /Users/peterwmurphy/arda-goal-weil,
island telperion/examples/rvm_bridge/lean, Lean v4.33.0-rc2, Zeta23 pinned at
fbdc36bbf17d20af3fd0447c6d1a8a02773c9844. Artifact: E6Bridge10.lean (577 lines, namespace
RvMBridge10, `import E6Bridge9` only) and memo WALL_SEAM_A_GAUSSIAN_IFF_2026-09-21.md.
Probes written by the auditor: Probes/Audit10_Axioms.lean, Probes/Audit10_Probes.lean.
No git state changed; no other file edited.

Overall verdict: PASS. No defect found. Every limit passage is a genuine dominated-convergence
or Tannery argument with an n-uniform integrable or summable majorant; the E8 definitions on the
non-compactly-supported limit test are honest values (I proved their integrability and
summability from the file's own majorants); the RH equivalence is a two-line composition of
already audited inputs with no circularity; the prime-side inequality is not closable by
automation and is refuted by any off-line zero; the file and memo claim nothing beyond the
equivalences.

## 1. Kernel: PASS

`lake build`: `Build completed successfully (8839 jobs).` E6Bridge10 is in defaultTargets
(lakefile.toml line 9) and a lean_lib (line 97); the guard carries 42 RvMBridge10 lines.
Probes/Audit10_Axioms.lean prints axioms for all 49 declarations (every theorem/lemma/def line;
a 50th mechanical match, "theorem of E6Bridge9). -/" at line 104, is a docstring continuation
and not a declaration): 49 of 49 read `[propext, Classical.choice, Quot.sound]`, no sorryAx.
Token grep for `sorry|admit|native_decide|axiom|opaque|unsafe|implemented_by|extern|partial|
set_option`: zero hits (exit 1).
`#check` output:
```
RvMBridge10.rh_iff_gaussian_positivity : RiemannHypothesis ↔ RvMBridge10.GaussianPositivity
RvMBridge10.zeroSide_gaussTest_eq : ∀ (c lam : ℝ), 0 < lam →
    RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam) =
      WeilExplicit.archSide (WeilExplicit.autocorr (RvMBridge8.gaussPhi c lam)) -
        WeilExplicit.primeSide (WeilExplicit.autocorr (RvMBridge8.gaussPhi c lam))
RvMBridge10.rh_iff_gaussian_prime_le_arch : RiemannHypothesis ↔ ∀ (c lam : ℝ), 0 < lam →
      (primeSide (autocorr (gaussPhi c lam))).re ≤ (archSide (autocorr (gaussPhi c lam))).re
```

## 2. The Gaussian explicit formula (zeroSide_gaussTest_eq): PASS

(a) Autocorrelation majorant. `norm_gaussTests_le` (line 165): ‖g_n u‖ ≤ ‖phi u‖ via
`Complex.norm_real` on the coerced cutoff and `abs_cutoff_le_one` (E6Bridge8), so the complex
coercion of the real bump is handled by its norm, correctly. `norm_phi_mul_phi_le`
(lines 179-209): ‖phi v‖ ‖phi (v-u)‖ = ‖K‖² |v||v-u| e^{-b v²} e^{-b (v-u)²}; with
|v||v-u| ≤ (v² + (v-u)²)/2 = (v - u/2)² + u²/4 and v² + (v-u)² = 2(v-u/2)² + u²/2 this is
≤ vMaj lam u v := ‖K‖² ((v-u/2)² + u²/4) e^{-2b (v-u/2)²} e^{-(b/2) u²}. I re-derived both
identities by hand; they are correct. `integrable_vMaj` (b > 0) and `integral_vMaj` (shift
w = v - u/2, then I2 + (u²/4) I0) give `autocorrMaj lam u = ‖K‖² (I2 + I0 u²/4) e^{-(b/2)u²}`,
and `norm_autocorr_gaussTests_le` (line 293): ‖autocorr (g n) u‖ ≤ autocorrMaj lam u for every
n, with no n in the majorant. `autocorr_gaussTests_tendsto` is DCT in v with that majorant and
an eventually-constant integrand (cutoff = 1 once n+1 ≥ max(|v|, |v-u|)).

(b) Prime side. `primeBound lam k = Λ(k)/√k · 2 autocorrMaj lam (log k)` dominates each term
(`norm_primeTerm_le`, using autocorrMaj_neg for the -log k term). `summable_primeBound`
(lines 341-393): for k ≥ ⌈e^{12/b}⌉ + 1, (b/2)(log k)² ≥ 6 log k because (b/2) log k ≥ 6, so
e^{-(b/2)(log k)²} ≤ k^{-6}; Λ(k)/√k ≤ Λ(k) ≤ log k ≤ k; (log k)² ≤ k²; I2 + I0 k²/4 ≤ (I2+I0/4) k²
for k ≥ 1; product ≤ k · 2‖K‖²(I2+I0/4) k² k^{-6} = D k^{-3}. Re-derived by hand: correct. The
finitely many small k are absorbed by `Summable.of_norm_bounded_eventually` over `cofinite`
(lines 348-352), and Σ k^{-3} is `Real.summable_nat_pow_inv`. `primeSide_gaussTests_tendsto` is
Tannery (`tendsto_tsum_of_dominated_convergence`) with that majorant.

(c) Archimedean side. `kernelMaj lam u = autocorrMaj lam u · e^{|u|/2}` dominates the kernel
integrand for |Re s - 1/2| ≤ 1/2 (`norm_kernel_term_le`), integrable because the Gaussian
e^{-(b/2)u²} beats e^{|u|/2} (`integrable_kernelMaj` from `integrable_abs_pow_mul_exp_quadratic_abs`
with k = 1/2); the three needed points s = 0, 1, 1/2 + ir all satisfy the strip condition
(`archSide_gaussTests_tendsto`, `archIntegral_gaussTests_tendsto`). The digamma integral's
majorant `archBound C r = ‖C/(1+r²) · logDeriv Γℝ(1/2 + r I)‖ + ‖C/(1+r²) · logDeriv Γℝ(1/2 - r I)‖
+ C/(1+r²) log π`. Zeta23's lemma has exactly these hypotheses (#check):
`Continuous φ → 0 ≤ C → (∀ t, ‖φ t‖ ≤ C/(1+t²)) → 1/2 ≤ σ → σ ≤ 3/2 → Integrable (fun t => φ t *
logDeriv Γℝ (σ + t I))`; `integrable_archBound` applies it to φ = C/(1+t²) itself (continuous,
norm ≤ C/(1+t²), σ = 1/2), then `.comp_neg` for the -r factor and `integrable_inv_one_add_sq` for
the log π term. So the lemma applies as written. `norm_archIntegrand_le` goes through E6Bridge4's
`archIntegrand_eq` and `gammaBracket_eq` and the n-uniform line bound
`exists_paperFT_autocorr_gaussTests_bound` (from the strip bound of E6Bridge8 through
`weilKernel_autocorr` and gammaOf(1/2 + ir) = r).

(d) Uniqueness of limits. `zeroSide_gaussTest_eq` (lines 543-556): hR is
`zeroSide_gaussTests_tendsto`, the sequence n ↦ zeroSide (hermitianTransform (gaussTests c lam n))
→ zeroSide (gaussTest c lam); hL is n ↦ weilForm (autocorr (gaussTests c lam n)) → arch - prime,
rewritten by `funext` with `weilForm_autocorr_eq_zeroSide (isWeilTest_gaussTests c lam n)` into
the SAME sequence; then `tendsto_nhds_unique hR hL`. Same sequence on both sides, verified.

(e) Honest values on f = autocorr (gaussPhi c lam), a non-compactly-supported function
(Probes/Audit10_Probes.lean, all axiom-clean `[propext, Classical.choice, Quot.sound]`):
- `audit_integrable_autocorr_integrand`: Integrable (fun v => phi v * conj (phi (v - u))), so
  `autocorr phi u` is a genuine Bochner integral, not the junk 0.
- `audit_norm_autocorr_gaussPhi_le`: ‖autocorr phi u‖ ≤ autocorrMaj lam u.
- `audit_aesm_autocorr_gaussPhi`: autocorr phi is AEStronglyMeasurable (limit of continuous).
- `audit_integrable_kernel_integrand`: the weilKernel integrand of f is integrable for
  |Re s - 1/2| ≤ 1/2 (so weilKernel f 0, f 1 and f (1/2 + ir) are honest).
- `audit_summable_primeSide_gaussPhi`: the primeSide family of f is Summable (so its tsum is
  honest), bounded by primeBound.
- `audit_integrable_archIntegrand_gaussPhi`: Integrable (archIntegrand f), as the ae-limit of the
  truncations' integrands under archBound with `le_of_tendsto`.
Hence archSide f and primeSide f in the theorem are genuine values.

## 3. rh_iff_gaussian_positivity: PASS, no circularity

Forward (`rh_implies_gaussian_positivity`, lines 68-90): `Zeta23.RH_implies_on_line` gives
gammaOf ρ = Im ρ (`gammaOf_eq_im_of_rh`); `gaussTest_ofReal` makes the summand m(ρ) times the
real (x-c)² e^{-2 lam (x-c)²} ≥ 0; non-zeros vanish by `zeroMult_eq_zero_of_not_nontrivial`;
`summable_gauss_zeroSide` + `Complex.hasSum_re` + `HasSum.nonneg`. Converse
(`gaussian_positivity_implies_rh`, lines 93-98): `rh_of_all_on_line`, then for an off-line zero
`RvMBridge7.gaussian_dominance` gives Re zeroSide < 0 contradicting GaussianPositivity by
`linarith`. My probe re-composes the iff from exactly these two (elaborates). Import graph:
E6Bridge10 imports only E6Bridge9 (line 38); the only files importing E6Bridge10 are
AxiomGuardRvMBridge.lean and Probes/E6Bridge10_probe.lean, so nothing in E6Bridge5-9 depends on
it. No circularity.

## 4. Non-vacuity: PASS

`audit_offline_refutes (ρ₀) (h₀ : IsNontrivialZero ρ₀) (hre : ρ₀.re ≠ 1/2) : ¬ GaussianPositivity`
is axiom-clean, so GaussianPositivity is not a tautology. The prime-side inequality resists
automation: `simp [primeSide, archSide]` → `Audit10_Probes.lean:97:94: error: unsolved goals`;
rewriting to `0 ≤ (zeroSide (gaussTest c lam)).re` then `positivity` →
`103:2: error: failed to prove positivity/nonnegativity/nonzeroness`. It is not a triviality of its
shape: from GaussianPositivity neither `Re prime ≤ 0` (`111:2: linarith failed`) nor the doubled
variant `2 Re prime ≤ Re arch` (`117:2: linarith failed`) follows by the same rewrite. Actual
falsity of a modified prime side cannot be exhibited without numerical values of the sides; what
is shown is that the inequality's content is exactly the sign of the Gaussian zero sum and that
nothing weaker or stronger is implied.

## 5. Overclaim: PASS

Grep over E6Bridge10.lean and the memo (prove(s/d) RH/Riemann, RH is/holds/proved, progress
toward, goal node proved, conjecture1_proved = True, crossing the wall, closes RH): the only hit
is the negation at memo line 9 "Nothing here proves RH." Disclaimers present: file lines 33-36
"WHAT THIS IS NOT: a proof of RH, or of either side ... not a crossing. conjecture1_proved =
False."; memo lines 9-10 and 194-195 "Not a proof of RH, and not a proof of Gaussian positivity
or of arch >= prime for any (c, lam). Every delivered theorem is an ↔ or an =; neither side of
any ↔ is asserted." The memo's "What it is NOT" section correctly records that both sides are
real (`gauss_zeroSide_real`) so stating real parts loses nothing. No wording says more.

## 6. Mathematics: PASS, no gap

Paper: (i) E8 for each truncation g_n gives weilForm (autocorr g_n) = zeroSide (H_{g_n});
(ii) zero side → zeroSide (G_{c,lam}) by Tannery with the n-uniform strip bound C/(1+|γ|²) and the
local count; (iii) autocorr g_n → autocorr phi pointwise with a Gaussian majorant uniform in n;
(iv) prime side → by Tannery against Λ(k)/√k · Gaussian(log k), summable; (v) archimedean side →
by DCT in u (kernel at s = 0, 1, 1/2 + ir) and DCT in r (digamma growth against C/(1+r²));
(vi) uniqueness of limits. Lean: (i) `weilForm_autocorr_eq_zeroSide`; (ii)
`zeroSide_gaussTests_tendsto` with `exists_hermitian_gaussTests_bound`; (iii)
`norm_autocorr_gaussTests_le`, `autocorr_gaussTests_tendsto`; (iv) `summable_primeBound`,
`primeSide_gaussTests_tendsto`; (v) `weilKernel_gaussTests_tendsto`,
`archIntegral_gaussTests_tendsto`, `archSide_gaussTests_tendsto`; (vi) `zeroSide_gaussTest_eq`.
Gaps: none. Remark: the convolution theorem for the non-compactly-supported phi is never used
(the memo records this); the archimedean side of f is reached only as a limit, which is why the
honest-value probes in section 2(e) were worth running, and they pass.

## Probe inventory

- Probes/Audit10_Axioms.lean: 49 genuine axiom prints (+1 docstring false match), 4 #check.
- Probes/Audit10_Probes.lean: 7 axiom-clean theorems (off-line refutation; 6 honest-value facts
  on autocorr (gaussPhi)), 1 iff re-composition (success), 4 expected failures (automation and
  shape variants).
- Probes/E6Bridge10_probe.lean is the author's own and was not relied on.
