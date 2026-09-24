# Audit testimony: AND_edge_clear_glue (anduril), blind auditor A2, 2026-09-23

- pass: true
- axioms_clean: true
- statement_byte_identical: true (identical once whitespace is ignored; the gate passes on the canonical path)
- conjecture1_proved = False

## 1. My own reading of the registry statement (written before I opened the artifact)

Registry file: `telperion/missions/anduril/lean/Statements/AND_edge_clear_glue.lean` (imports Mathlib only; does not use ANDDefs; `open Complex`).

    theorem hnzl_discharged (T0 T1 : ℝ) :
        ∀ y ∈ Set.uIcc T0 T1, riemannZeta (((-1 : ℝ) : ℂ) + ↑y * I) ≠ 0

In plain words: take any two real numbers T0 and T1 and any real y between them, in either order. Then Mathlib's `riemannZeta` is not zero at s = -1 + iy. T0 and T1 are free, so this says the same thing as "ζ(-1 + iy) ≠ 0 for every real y". The statement has no hypotheses. It is also not vacuous, because `Set.uIcc T0 T1` always contains T0. For example, T0 = T1 = y gives exactly the claim at y.

## 2. Statement match and incompleteness markers

- Gate on the canonical path: `R.load_campaign(Path('telperion/missions/anduril'))`, then `node = c.nodes['AND_edge_clear_glue']`, then `V.statement_matches(artifact_text, V._normalized_statement(node, root))`. Result: **True**. The normalized needle is exactly the theorem header above.
- My own check, collapsing whitespace only: the header appears exactly once in `EdgeClearGlue.lean`, and the next thing after it is ` := fun y _ => ...`. So the artifact does not strengthen or weaken the conclusion. The artifact theorem sits in `namespace EdgeClearGlue` and has `open Complex` in force, as the statement file does.
- `V.artifact_incompleteness_markers` found nothing (`[]`) in EdgeClearGlue, ZetaZeroConfinement, TuringBand, RHInBoxCore, RHInBoxAnalytic, BoxLocalization, XiLineZeros, LambdaLineReal, BoxArgPrincipleZeta, BlaschkeBox, BoxArgPrinciple, WindingCount and DiffractionCore. The only match for the word in the artifact is the docstring "No `sorry`." on line 39.

## 3. Build and axioms

- `leanlock.sh lake build EdgeClearGlue` finished with "Build completed successfully (8735 jobs)". The only warnings are unused-simp-argument lints in DiffractionCore.
- My probe `Probes/AuditProbe_AND_edge_clear_glue_A2.lean` has been deleted. It restated the registry statement word for word outside every namespace and closed it with `EdgeClearGlue.hnzl_discharged T0 T1`. It also checked y = 0 through `hnzl_discharged 0 0 0` and checked "every real y" through `fun y => hnzl_discharged y y y`. All of these elaborated. `#print axioms` returned `[propext, Classical.choice, Quot.sound]` for `hnzl_discharged`, the restatement, `riemannZeta_neg_one` and `ZetaZeroConfinement.zeta_zero_re_mem_strip`.

## 4. Hidden hypotheses and oracles

The proof follows this chain: `hnzl_discharged` uses `riemannZeta_neg_one_add_mul_I_ne_zero`, which splits into two cases.

- **y ≠ 0**: `riemannZeta_ne_zero_of_re_nonpos`, then `ZetaZeroConfinement.zeta_zero_re_mem_strip`, then `zeta_zero_reflect` and `zeta_zero_iff_completed_zero_of_im_ne`. These rest on Mathlib's `riemannZeta_ne_zero_of_one_le_re`, `completedRiemannZeta_one_sub` and `Gammaℝ_eq_zero_iff`.
- **y = 0**: `riemannZeta_neg_one`, which uses Mathlib's `riemannZeta_neg_nat_eq_bernoulli` and `bernoulli_two`.

None of these has an Arb, hmem, hArbT, hLine or oracle binder. The zero-free-region inputs (the dVP region, and the hγ assumption in `zero_in_band`) sit in other theorems of the same file and do not reach this one.

I scanned the import closure, including the zero_free_bridge modules DlvpTheta and DlvpZetaZeroFree, for `axiom`, `opaque`, `unsafe`, `native_decide`, `ofReduceBool`, `implemented_by`, `extern`, `sorry`, `admit` and any redefinition of `riemannZeta`. Nothing matched in code. The axiom print settles the question independently of the scan.

## 5. Mathematical check

- **y = 0**: ζ(-1) = -B₂/2 = -1/12 ≠ 0. mpmath gives -0.08333…
- **y ≠ 0**: s = -1 + iy has Re s = -1 ≤ 0 and Im s ≠ 0. Any zero off the real axis has 0 < Re < 1. The trivial zeros -2, -4, … are real and even, so none of them has Re = -1. A second argument through the functional equation gives the same answer: ζ(-1 + iy) = χ(s)·ζ(2 - iy). Here ζ(2 - iy) ≠ 0 because Re = 2 > 1, and sin(πs/2) never vanishes because s/2 is never an integer.
- Spot checks of |ζ(-1 + iy)| with mpmath at 11 heights from 0 to 279999.5 gave values from 0.0833 up to 1.3e7, all well away from zero.
- The statement covers every real y and is not vacuous (see section 1).

## 6. What this establishes and what it does not

**Establishes:** one unconditional fact about Mathlib's ζ, checked by the kernel: it has no zero on the vertical line Re s = -1. That fact removes the `hnzl` (H2b) Arb input from the band statements. It is glue for a finite verification up to a fixed height.

**Does not establish:**
- anything about zeros in the critical strip, or RH
- the other Arb inputs of a band (hnzb, hnzt, hins, which still need the SlabClear facts)
- that any band's count is correct

conjecture1_proved = False.
