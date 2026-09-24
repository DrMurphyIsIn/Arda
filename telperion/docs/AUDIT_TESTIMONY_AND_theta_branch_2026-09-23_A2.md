# Audit testimony: AND_theta_branch (anduril), blind auditor A2, 2026-09-23

- pass: true
- axioms_clean: true
- statement_byte_identical: true (modulo whitespace; canonical gate `statement_matches` = True)
- conjecture1_proved = False

## 1. Read-back of the registry statement (written before reading the artifact)

For every real t > 0 there is a real number Λ such that:
(a) the sequence n ↦ ThetaGap.imLnVal (1/4) (t/2) n = (t/2)·log n − Σ_{k=0..n} arctan((t/2)/(1/4+k))
converges to Λ. This is the Gauss-product (Γ(z) = lim n! n^z / (z(z+1)…(z+n))) continuous branch of
Im log Γ(1/4 + it/2); and
(b) |Λ − (t/2)·log π − thetaMain t| ≤ 1/t, where
thetaMain t = (t/2)·log t − (t/2)·log(2π) − t/2 − π/8 is the Riemann–Siegel main term.
In words, the Riemann–Siegel theta, defined through the Gauss branch, is within 1/t of its main term at
every positive height. No hypotheses other than t > 0.

## 2. Statement identity and the gate

- The statement file has no `sorry` stub beyond the generated `:= by sorry` body. Its text is identical,
  modulo whitespace, to the declaration of `RSDesignTheta.gaussBranch_theta_sub_thetaMain_le` in
  telperion/examples/zeta_reflection/lean/RSTheta.lean (lines 512-514).
- Canonical path: `R.load_campaign(Path('telperion/missions/anduril'))`, then node `AND_theta_branch`, then
  `V.statement_matches(RSTheta.lean text, V._normalized_statement(node, root))` returned **True**.
- `V.artifact_incompleteness_markers` returned `[]` on every local module in the import closure:
  RSTheta, ThetaConverge, ThetaValue, ArctanTaylor (zeta_reflection) and DlvpTheta (zero_free_bridge, pulled in
  transitively through zzl_core). Everything else in the closure is Mathlib.

## 3. Build and axioms

- `leanlock.sh lake build RSTheta`: exit 0, "Build completed successfully (8661 jobs)". Only linter
  warnings, and no "declaration uses" warning.
- My own probe (`#print axioms RSDesignTheta.gaussBranch_theta_sub_thetaMain_le`) printed
  `[propext, Classical.choice, Quot.sound]`, which is within the allowed set. `#check` shows the elaborated
  type is exactly the registry proposition. I have deleted the probe.

## 4. Hidden hypotheses and trust escapes

- The theorem's only binder is `ht : 0 < t`. The proof calls `ThetaConverge.convergence_obligation`
  (a Cauchy-sequence limit, with Γ ≠ 0 discharged in place) and `theta_sub_thetaMain` (derived from
  `theta_bracket` and then `lam_bracket`, using an elementary convex-trapezoid argument).
- Grep over the 5 local closure modules found no `axiom`, `opaque`, `unsafe`, `extern`, `implemented_by`,
  `native_decide`, `ofReduceBool` or `hArb`/`hLine` binders in code. The only `hmem` hits are a local `have`
  (interval membership) inside `trapezoid_convex`. It is not an oracle hypothesis. The clean axiom print
  corroborates this.

## 5. Vocabulary mirrors and numerics

- The ANDDefs mirrors match the island definitions line-for-line and character-for-character:
  `ThetaGap.imLnVal` (ThetaValue.lean:180-181, namespace ThetaGap) and `ZeroFreeBridge.thetaMain`
  (DlvpTheta.lean:243-244, namespace ZeroFreeBridge). In the probe, `rfl` against the mirror bodies also
  typechecked for both.
- mpmath (dps 40), θ(t) = Im loggamma(1/4 + it/2) − (t/2) log π (it agrees with mp.siegeltheta), with thetaMain
  reimplemented from the Lean definition:

  | t | θ − thetaMain | 1/t | ok |
  |---|---|---|---|
  | 1 | 0.04409 | 1 | yes |
  | 10 | 0.0020846 | 0.1 | yes |
  | 100 | 2.0833e-4 | 0.01 | yes |
  | 10000 | 2.0833e-6 | 1e-4 | yes |

  The difference is about 1/(48t), inside the artifact's claimed [−1/(2t), 3/(16t)]. The branch check at
  t = 1 and t = 10 is a Richardson extrapolation of imLnVal(1/4, t/2, n) with n = 2·10^4 and n = 4·10^4.
  It matches Im loggamma to about 1e-10 and 2e-8 respectively, so the Gauss branch is the principal
  continuous branch.

## 6. What this does and does not establish

What it establishes: a height-uniform, kernel-checked inequality. The Gauss-branch Riemann–Siegel theta
exists and is within 1/t of the RS main term at every t > 0. Rigorous theta phase boxes then cost O(1)
per height.

What it does not establish: anything about zeros of ζ, the Riemann Hypothesis, or conjecture1. It is one
special-function brick for the finite-verification ladder. conjecture1_proved = False.

Remarks (non-blocking): the node toml is still `status = "draft"`, and I did not edit the registry.
