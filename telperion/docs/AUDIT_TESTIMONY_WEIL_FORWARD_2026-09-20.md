# Audit testimony: E6Bridge5, the forward half of Weil's criterion (2026-09-20)

Auditor: blind adversarial auditor (separate agent, no prior context on the artifact).
Worktree: /Users/peterwmurphy/arda-goal-weil, island telperion/examples/rvm_bridge/lean,
Lean v4.33.0-rc2, Zeta23 pinned at fbdc36bbf17d20af3fd0447c6d1a8a02773c9844 (lakefile.toml and
lake-manifest.json agree). Artifact: E6Bridge5.lean (untracked in git at audit time), 130 lines.
Probe files written by the auditor: Probes/Audit_Axioms.lean, Probes/Audit_Nonvacuous.lean,
Probes/Audit_Trivial.lean, Probes/Audit_NoRH.lean. No file outside those and this report was
edited; no state-changing git command was run.

Overall verdict: PASS. No defect found. The theorem `RvMBridge5.rh_implies_weil_positivity`
is a kernel-checked, axiom-clean proof that Mathlib's `RiemannHypothesis` implies
`0 <= (weilForm (autocorr g)).re` for every smooth compactly supported g, on definitions that
match the MIRRORMERE registry (MMDefs.lean) verbatim. The hypothesis is load-bearing, the test
class is inhabited by nonzero functions, automation cannot close the hypothesis-free sentence,
and the docstrings claim nothing beyond the forward half. conjecture1_proved = False.

## 1. Kernel: PASS

`lake build` on the island: `Build completed successfully (8829 jobs).`

`lake env lean Probes/Audit_Axioms.lean` output, verbatim:

```
'RvMBridge5.rh_implies_weil_positivity' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge5.autocorr_eq_weilTest' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge5.isWeilTest_autocorr' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge5.eq_half_add_im_of_rh' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge5.weilKernel_autocorr_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge5.term_re_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'WeilExplicit.autocorr' depends on axioms: [propext, Classical.choice, Quot.sound]
'WeilExplicit.weilForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge4.limit_explicit_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.RH_implies_on_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.EF.paperFT_weilTest' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx` anywhere. The inputs named in the header (E8 explicit formula, on-line lemma,
transform factorisation) were printed independently and are also clean.

Token grep on E6Bridge5.lean for `sorry|admit|native_decide|axiom|opaque|unsafe|implemented_by|
set_option|extern|partial|decide`: the only hit is line 10, the phrase `#print axioms` inside
the header comment. Same grep on E6Bridge4.lean: only line 10, same phrase. The upstream Zeta23
file ExplicitFormula.lean sets `backward.isDefEq.respectTransparency false`; that is an
elaboration option in the pinned dependency, not in the artifact, and does not touch the
kernel check (informational only).

The AxiomGuardRvMBridge.lean diff adds `import E6Bridge5` and `#print axioms` for the six
RvMBridge5 declarations; the lakefile diff adds `E6Bridge5` to defaultTargets and a lean_lib.

## 2. Definitions faithful: PASS

Independent derivation. `autocorr g u = ∫ v, g v * conj (g (v - u))` (E6Bridge5.lean:55-56).
The Hermitian autocorrelation is (g ⋆ g~)(u) with g~(t) = conj(g(-t)). Mathlib's
`convolution_def` (Mathlib/Analysis/Convolution.lean:421) reads
`(f ⋆[L, μ] g) x = ∫ t, L (f t) (g (x - t))`, so
(g ⋆ g~)(u) = ∫ t, g t * g~(u - t) = ∫ t, g t * conj(g(-(u - t))) = ∫ t, g t * conj(g(t - u)).
That is exactly `autocorr` with v = t. The conjugate is on the SECOND factor and the argument is
`v - u`, not `u - v`; both were checked against the source. Hermitian symmetry follows by the
substitution v -> v + u: autocorr g (-u) = conj (autocorr g u).

Zeta23 conventions (ExplicitFormula.lean:48,52):
`def tilde (g) := fun u => conj (g (-u))`, `def weilTest (f g) := f ⋆[mul ℝ ℂ] tilde g`.
The Lean lemma `autocorr_eq_weilTest` (E6Bridge5.lean:69-74) closes by `neg_sub` after
unfolding, which is precisely the step -(u - v) = v - u above.

Transform on the line. Zeta23's `paperFT f z = ∫ u, f u * exp(I * z * u)` (Defs.lean:44) and
`paperFT_weilTest : paperFT (weilTest f g) z = paperFT f z * conj (paperFT g (conj z))`
(ExplicitFormula.lean:189-191). For z = r real, conj r = r, giving h(r) * conj(h(r)) = |h(r)|^2.
E6Bridge4's `weilKernel_line : weilKernel g (1/2 + r I) = paperFT g r` (E6Bridge4.lean:138)
carries the E8 transform onto that. The Lean lemma `weilKernel_autocorr_line`
(E6Bridge5.lean:96-100) does exactly this chain with `Complex.conj_ofReal` and
`Complex.mul_conj'`. No dropped conjugate, no argument swap.

Registry match. The E6Bridge5 definitions of `autocorr` and `weilForm` are character-for-character
identical to MMDefs.lean:255-256 and :265 (mirrormere registry), and to the design memo on
branch mm/w3c-goal-weil-membership (MM_w3c_goal_weil_membership_DESIGN_2026-09-18.md lines
102-105), which is the memo whose section 6 numeric read-back reported 1.5708. The six E8
definitions in E6Bridge4 match MMDefs.lean:209-239 and RHDefs.lean:135-165 verbatim. The theorem
line matches Statements/MM_rh_implies_weil_positivity.lean:5 (modulo layout).

## 3. Statement not vacuous, not weakened: PASS

(a) Inhabited by a nonzero function. Probes/Audit_Nonvacuous.lean proves, with a
`ContDiffBump (0:ℝ)` of radii 1 and 2 coerced to ℂ:

```
theorem audit_isWeilTest_inhabited_nonzero : ∃ g : ℝ → ℂ, WeilExplicit.IsWeilTest g ∧ g ≠ 0
theorem audit_autocorr_ne_zero : ∃ g : ℝ → ℂ, WeilExplicit.IsWeilTest g ∧ WeilExplicit.autocorr g ≠ 0
```

Both print `depends on axioms: [propext, Classical.choice, Quot.sound]`. The second shows that
the autocorrelation of a real test function is not the zero function (its value at 0 is the
positive integral of f^2), so the theorem is not evaluating `weilForm` at 0. Note the smoothness
index in `IsWeilTest` is `((⊤ : ℕ∞) : WithTop ℕ∞)` = C^∞, not `⊤ : WithTop ℕ∞` = analytic; the
bump lemma `ContDiffBump.contDiff` elaborated at that index, which confirms the class is C^∞
(an analytic compactly supported class would be {0} and the sentence vacuous).

(b) Hypothesis-free sentence is not closed by automation. Probes/Audit_Trivial.lean, error
lines verbatim:

```
Probes/Audit_Trivial.lean:7:2: error: `simp` made no progress
Probes/Audit_Trivial.lean:10:64: error: unsolved goals            (simp with all defs unfolded)
Probes/Audit_Trivial.lean:16:2: warning: aesop: failed to prove the goal after exhaustive search.
Probes/Audit_Trivial.lean:15:64: error: unsolved goals
Probes/Audit_Trivial.lean:21:2: error: failed to prove positivity/nonnegativity/nonzeroness
Probes/Audit_Trivial.lean:27:2: error: failed to prove positivity/nonnegativity/nonzeroness   (after unfold weilForm)
Probes/Audit_Trivial.lean:32:2: error: `exact?` could not close the goal.
Probes/Audit_Trivial.lean:35:53: error: unsolved goals            (weilForm f = 0 by simp)
```

(c) The conclusion is not trivially true for a junk reason. `weilForm f` unfolds to
`archSide f - primeSide f` with the E8 definitions (`#print WeilExplicit.weilForm` in
Audit_Axioms: `fun f => WeilExplicit.archSide f - WeilExplicit.primeSide f`). The final example
in Audit_Trivial.lean elaborates with no error:

```
example (g) (hg : IsWeilTest g) :
    HasSum (fun ρ : ℂ => (zeroMult ρ : ℂ) * weilKernel g ρ) (weilForm g) :=
  (RvMBridge4.limit_explicit_formula g hg).2
```

so `weilForm f` IS the zero-side sum whenever f is a test function, and by
`isWeilTest_autocorr` the autocorrelation of a test function is a test function. Every Bochner
integral in play (autocorr, weilKernel, the archimedean integral) has a continuous compactly
supported or proven-integrable integrand (E6Bridge4.integrable_archIntegrand), so none is a junk
0. Numerics were not reproduced; the definitions the memo's 1.5708 read-back used are the ones
above, verbatim.

## 4. Hypothesis load-bearing: PASS

Probes/Audit_NoRH.lean, the author's proof of `term_re_nonneg` with `hRH` deleted:

```
Probes/Audit_NoRH.lean:10:94: error: unsolved goals
  ... hz : IsNontrivialZero ρ
  ⊢ RiemannHypothesis
```

The rewrite `rw [← eq_half_add_im_of_rh _ hz]` leaves `RiemannHypothesis` as an unsolvable
side goal; that is the only place ρ is moved onto the line, and the square-modulus lemma
`weilKernel_autocorr_line` applies only at points of the form 1/2 + r I with r real.
Automation on the hypothesis-free summand sentence also fails:

```
Probes/Audit_NoRH.lean:20:2: error: failed to prove positivity/nonnegativity/nonzeroness
Probes/Audit_NoRH.lean:23:74: error: unsolved goals     (simp with defs)
Probes/Audit_NoRH.lean:28:2: warning: aesop: failed to prove the goal after exhaustive search.
Probes/Audit_NoRH.lean:40:83: error: unsolved goals     (square-modulus form at a general σ + r I)
```

What IS provable without RH (Audit_NoRH.lean line 33, elaborates clean):
`weilKernel (autocorr g) ρ = paperFT g (gammaOf ρ) * conj (paperFT g (conj (gammaOf ρ)))`.
This is a square modulus only when `conj (gammaOf ρ) = gammaOf ρ`, i.e. ρ on the line. So the
sign of the real part of each summand comes from `RH_implies_on_line` and nowhere else.

## 5. Scope honesty: PASS

E6Bridge5.lean:41-42: "No RH progress is claimed: this is the forward half of Weil's criterion
(RH implies positivity), not the converse. conjecture1_proved = False."
E6Bridge5.lean:2-3: "the forward half of Weil's criterion on this island's vocabulary".
lakefile.toml comment for E6Bridge5: "Proves nothing about RH itself".
No docstring in the file claims RH, the converse, or positivity unconditionally. The lakefile
comment also says the theorem "discharges the hypothesis hpos carried by
weil_negative_refutes_rh"; that theorem was not in scope and I did not verify the claim, but it
is a claim about wiring, not about RH. No overclaim found.

## 6. Mathematics: PASS, no gap between paper and Lean

Paper argument (ten lines):
1. For g in C_c^∞, f := g ⋆ g~ is again C_c^∞ (convolution of C^∞ compact-support with L^1_loc).
2. E8 explicit formula for f: Σ_ρ m(ρ) H_f(ρ) = archSide f - primeSide f as a HasSum over ρ ∈ ℂ,
   m(ρ) the divisor multiplicity, supported on the nontrivial zeros.
3. H_f(s) = h_f((s - 1/2)/i) with h_f = paperFT f, and h_{g⋆g~}(z) = h_g(z) conj(h_g(conj z)).
4. Under RH each ρ with m(ρ) ≠ 0 is 1/2 + iγ, γ real, so (ρ - 1/2)/i = γ is real.
5. Hence H_f(ρ) = h_g(γ) conj(h_g(γ)) = |h_g(γ)|^2 ≥ 0, and m(ρ) H_f(ρ) is a nonneg real.
6. For ρ not a nontrivial zero, m(ρ) = 0 and the term is 0.
7. Taking real parts termwise preserves HasSum (Re is a continuous linear map).
8. A HasSum of nonnegative reals has a nonnegative sum.
9. Therefore 0 ≤ Re(archSide f - primeSide f) = Re(weilForm (autocorr g)).
10. Nothing about the converse; positivity is derived from RH, not the other way.

Lean text against each line: (1) `isWeilTest_autocorr` via
`HasCompactSupport.contDiff_convolution_left` and `weilTest_hasCompactSupport`; (2)
`RvMBridge4.limit_explicit_formula`; (3) `weilKernel_line` + `paperFT_weilTest`; (4)
`eq_half_add_im_of_rh` from `RH_implies_on_line`; (5) `weilKernel_autocorr_line` with
`Complex.conj_ofReal` (conjugation of the real r) and `Complex.mul_conj'`; the cast of
`zeroMult` from ℕ through ℝ to ℂ is done by `push_cast; ring` then `Complex.ofReal_re` and
`positivity` on `0 ≤ (n:ℝ) * ‖h‖^2`; (6) the `by_cases hz : IsNontrivialZero ρ` negative branch
uses `zeroMult_eq_zero_of_not_nontrivial`, which covers both ρ off the strip (divisor supported
in its domain) and ρ in the strip with ζ(ρ) ≠ 0 (analyticOrderAt = 0); the case
analyticOrderAt = ⊤ would give toNat = 0 and is harmless for a nonnegativity claim; (7)
`Complex.hasSum_re`; (8) `HasSum.nonneg`; (9) `unfold weilForm` then `exact`.

Residual observations, none a defect:
- The conclusion is stated on `.re`. Under the HasSum every term is real, so the imaginary part
  of `weilForm (autocorr g)` is 0 as well; the registry sentence asks only for the real part and
  the proof delivers exactly that.
- `IsNontrivialZero` is Zeta23's strip definition (ζ ρ = 0 ∧ 0 < Re ρ < 1); Mathlib's
  `RiemannHypothesis` quantifies over zeros that are neither trivial nor 1. The bridge
  `RH_implies_on_line` (Statement.lean:137) uses `IsNontrivialZero.not_trivial`, and it is
  axiom-clean; strip zeros are never at -2(n+1) or 1.

## Probe inventory

- Probes/Audit_Axioms.lean: axiom prints and definition prints (section 1).
- Probes/Audit_Nonvacuous.lean: two axiom-clean theorems (section 3a).
- Probes/Audit_Trivial.lean: seven expected failures plus one expected success (section 3b, 3c).
- Probes/Audit_NoRH.lean: six expected failures plus one expected success (section 4).
- Probes/E6Bridge5_probe.lean is the author's own probe and was not relied on.
