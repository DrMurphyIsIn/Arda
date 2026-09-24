# Audit testimony: AND_g2_reflected_band_kernel (anduril), blind auditor A2, 2026-09-23

- pass: true
- axioms_clean: true
- statement_byte_identical: true (identical once whitespace is normalized; the hardened gate passes when given the statement's proposition body; see section 2)
- conjecture1_proved = False

Worktree: /Users/peterwmurphy/arda-cl-arb (read-only apart from this file and a temporary probe, which has been deleted). I did no git operations and made no registry edits.

## 1. Read-back of the registry statement (written before I read the artifact)

Statement file `missions/anduril/lean/Statements/AND_g2_reflected_band_kernel.lean` (sha256 tag 38e9d3ea99483138):

> There is a list of two real numbers, strictly increasing, with every entry in [14, 22], such that
> Mathlib's `completedRiemannZeta` (Lambda(s) = pi^(-s/2) Gamma(s/2) zeta(s)) vanishes at
> s = 1/2 + i t for each entry t.

Put plainly, it says there are at least two distinct zeros of the completed zeta function on the critical line with ordinates in [14, 22]. The theorem has no binders or hypotheses, so the whole claim is unconditional. The node title matches this: "two zeros of completedRiemannZeta on the critical line with heights in [14, 22] ... no Arb or oracle input ... Finite verification only, NOT RH". `depends_on = ["AND_checkline_correct"]`, status `draft`.

## 2. Statement comparison and the hardened gate

- Theorem header up to `:= by`, whitespace collapsed: the artifact (`ReflectedBand_t14_Kernel.lean`) and the statement file match exactly.
  `theorem pilot_kernel : ∃ xs : List ℝ, xs.length = 2 ∧ xs.IsChain (· < ·) ∧ (∀ t ∈ xs, (14 : ℝ) ≤ t ∧ t ≤ (22 : ℝ)) ∧ (∀ t ∈ xs, completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0)`
- `V.statement_matches(artifact, V.normalize_lean(<raw statement file>))` returns **False**. This is an artifact of the calling convention, not a mismatch. The raw file begins with the DO-NOT-EDIT header and `import Mathlib`. `normalize_lean` strips comments but keeps the `import Mathlib` line, so it becomes part of the search needle, and the artifact has no `import Mathlib` directly before the theorem.
- The same gate given the proposition body (header and import/open lines dropped, the same derivation `verify._normalized_statement` performs) returns **True**.
- The canonical path the grant gate uses, `V.statement_matches(artifact, V._normalized_statement(node, campaign.root))` with the node loaded from `missions/anduril`, returns **True**.
- Name resolution under the artifact's `open DIntvProd ZetaReflection XiLineZeros`: my probe restated the theorem with no opens and with `_root_.completedRiemannZeta`, then closed it with `ReflectedBand_t14_Kernel.pilot_kernel`. It elaborated, so the artifact's `completedRiemannZeta` is Mathlib's root constant and has not been shadowed.
- `V.artifact_incompleteness_markers` returned `[]` for the artifact and for every module in its local import closure (38 modules, including the new ones: KernelBandEnclosures, KernelGammaEnvelope, ForgeZeta22, ForgePhi22, ForgeZ22Terms, AxiomGuardArbKernel).

## 3. Build and axioms

- `leanlock.sh lake build ReflectedBand_t14_Kernel AxiomGuardArbKernel` finished with "Build completed successfully (8696 jobs)" and EXIT=0. There were 0 error lines, only linter warnings.
- The AxiomGuardArbKernel output shows `pilot_kernel`, `gLine14/15/22_encl`, the KernelGammaEnvelope lemmas, the ForgeZeta22 lemmas and the ForgePhi22 lemmas all at `[propext, Classical.choice, Quot.sound]`. `okK` is at `[propext]`.
- My own probe (`lake env lean Probes/AuditProbe_g2k_A2.lean`, deleted afterwards) gave:
  `'ReflectedBand_t14_Kernel.pilot_kernel' depends on axioms: [propext, Classical.choice, Quot.sound]`.
  There is no `sorryAx`, no `Lean.ofReduceBool` and no custom axiom.

## 4. No hypotheses, no oracle input

- `#check @ReflectedBand_t14_Kernel.pilot_kernel` prints only the existential conclusion. The theorem has no binders.
- The closure grep found no `axiom`, `opaque`, `sorry`, `native_decide`, `implemented_by` or `extern` in comment-stripped code across the 38-module local closure.
- Declarations binding `hmem*`, `hArb` or `hLine` occur in only two places:
  - `CheckBand` (lines 36 and 156): these are the generic soundness lemmas. `pilot_kernel` discharges their `hmem` from the proved `KernelBandEnclosures.gLine14/15/22_encl`.
  - `ReflectedBand_t14.pilot` (hmem0/1/2): this is the Arb-conditional sibling. `pilot_kernel` imports it but uses only `ReflectedBand_t14.grid` (`![14, 15, 22]`), never `pilot`.
- Since `#print axioms` is clean and the type has no hypotheses, no Arb or oracle datum can enter the proof.

## 5. Independent numerics (mpmath, 50 digits)

I reimplemented `gLine` from the Lean definition, `XiLineZeros.gLine t = (completedRiemannZeta (1/2 + t i)).re`, as Re(pi^(-s/2) Gamma(s/2) zeta(s)). The dyadic box `(lo, hi, e)` means `[lo * 2^e, hi * 2^e]`, per `DIntv.memR`.

| t | gLine(t) (mpmath) | box dK | contains | excludes 0 |
|---|---|---|---|---|
| 14 | -2.05140834889e-6 | [-0.5, -7.276e-12] = [-2^-1, -2^-37] | yes | yes |
| 15 | +6.26590862439e-6 | [7.276e-12, 4.0] = [2^-37, 2^2] | yes | yes |
| 22 | -3.18691370150e-8 | [-8.0, -2.776e-17] = [-2^3, -2^-55] | yes | yes |

- The imaginary part of Lambda at these points is about 1e-57, which is numerical noise, as expected since Lambda is real on the line.
- The box endpoints agree with the Lean statements of `gLine14_encl` ([-1/2, -1/137438953472]), `gLine15_encl` ([1/137438953472, 4]) and `gLine22_encl` ([-8, -1/36028797018963968]).
- The true values sit well inside every box: at least 2.4e5 times the inner edge and at least 2.4e5 times smaller than the outer edge.
- Signs are (neg, pos, neg), so by the IVT there is one zero in (14, 15) and one in (15, 22).
- Zeros of Z(t) in [14, 22]: a sign-change scan at step 1e-3 finds exactly two, at 14.134725141734693790... and 21.022039638771554992... These match `mp.zetazero(1)` and `mp.zetazero(2)`. The next zero, 25.0108..., lies outside the range.
- Cross-check against the docstring's S(t) ranges, using Z(t) from mpmath:
  - Z(14) = -0.10563, inside [-0.1224, -0.0893].
  - Z(15) = 0.71994, inside [0.654, 0.769].
  - Z(22) = -0.98392, inside [-1.819, -0.1567].

## 6. What is established and what is not

What is established: a kernel-checked, hypothesis-free, axiom-clean proof that Lambda has at least two zeros on the critical line with ordinates in [14, 22]. These are the first two nontrivial zeros, 14.1347... and 21.0220..., which the proof locates only as lying in (14, 15) and (15, 22). The method is finite interval arithmetic plus the IVT on the real-valued function t -> Lambda(1/2 + i t).

What is not established:
- RH, or anything about zeros off the line.
- That these are the only zeros in [14, 22]. The statement is a lower count (two), not an exact count.
- Anything about heights above 22.

This is finite verification only. conjecture1_proved = False.

## Issues and notes

- Minor, about process rather than the artifact: calling `statement_matches` with `normalize_lean(<raw statement file>)` returns False because `import Mathlib` stays in the needle. The canonical gate (`_normalized_statement`) returns True. Scripts that call the gate should go through `_normalized_statement`.
