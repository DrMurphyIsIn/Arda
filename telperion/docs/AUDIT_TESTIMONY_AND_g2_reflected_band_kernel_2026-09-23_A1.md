# Audit testimony: AND_g2_reflected_band_kernel (anduril), blind auditor A1, 2026-09-23

- node: `telperion/missions/anduril/nodes/AND_g2_reflected_band_kernel.toml` (status `draft`, depends_on `AND_checkline_correct`)
- statement: `telperion/missions/anduril/lean/Statements/AND_g2_reflected_band_kernel.lean`
- artifact: `telperion/examples/zeta_reflection/lean/ReflectedBand_t14_Kernel.lean`, theorem `ReflectedBand_t14_Kernel.pilot_kernel`
- auditor context: blind. I did not read author notes, PRs or other auditors' testimony before fixing this verdict.

## Verdict fields

- pass = true
- axioms_clean = true
- statement_byte_identical = true (identical modulo whitespace; see check 2 for a caveat about how the gate was invoked)
- conjecture1_proved = False

## 1. Read-back of the registry statement (written before reading the artifact)

There is a list of exactly two real numbers, strictly increasing, each lying in the closed
interval [14, 22], and for each such t Mathlib's `completedRiemannZeta` (Lambda(s) =
pi^(-s/2) Gamma(s/2) zeta(s), analytically continued; the point 1/2 + it is never 0 or 1) vanishes
at s = 1/2 + i t. Put simply, Lambda has at least two distinct zeros on the critical line with
ordinates in [14, 22]. The statement takes no hypotheses. It says nothing about multiplicity, about
zeros off the line, or about any height outside [14, 22].

## 2. Statement comparison and hardened gate

- The theorem text in the artifact (`theorem pilot_kernel : ... :=`) and the statement file (after
  the generated header and `import Mathlib`) are identical once whitespace is collapsed. The
  normalized text is:
  `theorem pilot_kernel : ∃ xs : List ℝ, xs.length = 2 ∧ xs.IsChain (· < ·) ∧ (∀ t ∈ xs, (14 : ℝ) ≤ t ∧ t ≤ (22 : ℝ)) ∧ (∀ t ∈ xs, completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0)`
- Caveat on the invocation: the literal call from my brief,
  `V.statement_matches(artifact_text, V.normalize_lean(statement_text))`, returns **False**. The
  reason is that `normalize_lean` of the whole statement file keeps the `import Mathlib` line, so
  the needle begins `import Mathlib theorem pilot_kernel ...`, and that text can never occur in an
  artifact. This comes from how the call was written. It says nothing about the artifact. The
  registry's own gate path, `V._normalized_statement(node, root)` (it drops the sentinel header
  and the import/open lines), returns the needle above, and
  `V.statement_matches(artifact_text, that_needle)` returns **True**. `grant_status` uses that
  path. I also checked that the proposition proved matches the text: a probe elaborated the
  statement with no `open`s (so `completedRiemannZeta` resolves to Mathlib's root constant) and
  accepted `ReflectedBand_t14_Kernel.pilot_kernel` as its proof. The artifact's
  `open DIntvProd ZetaReflection XiLineZeros` therefore does not shadow anything.
- `V.artifact_incompleteness_markers` returned `[]` on the artifact and on each of the 38 other
  local modules in the closure of `ReflectedBand_t14_Kernel` + `AxiomGuardArbKernel` (ArctanTaylor,
  CertVerify, CheckBand, DIntvCorrect, DIntvDef, EMZeta, EMZetaComplex, EMZetaTail, ForgeLogBracket,
  ForgePhi14Terms, ForgePhi15Terms, ForgePhi22, ForgePhiFold14, ForgePhiFold15, ForgeRate, ForgeTail,
  ForgeTailTerms, ForgeThetaBox, ForgeZ14Terms, ForgeZ15Terms, ForgeZ22Terms, ForgeZeta14,
  ForgeZeta15, ForgeZeta22, KernelBandEnclosures, KernelGammaEnvelope, LambdaLineReal (zzl),
  ReflectedBand_t14, TaylorKernels, ThetaConverge, ThetaValue, TrigReduce, TrigReduceOperating,
  XiLineZeros (zzl), ZeroHypBand_t14, ZeroSignDecomp_t14, ZetaEMSum, AxiomGuardArbKernel).
- `V.artifact_coverage_error` for the artifact returned `None` (it is a default target).

## 3. Build and axioms

- `leanlock.sh lake build ReflectedBand_t14_Kernel AxiomGuardArbKernel` finished with
  `Build completed successfully (8696 jobs)`, exit 0, and no errors (linter warnings only).
- The AxiomGuardArbKernel output reports `pilot_kernel`, the three memberships `gLine14/15/22_encl`,
  the Gamma_R envelope lemmas and the ForgeZeta22/ForgePhi22 lemmas. Every line is within
  {propext, Classical.choice, Quot.sound}. `okK` depends on [propext] only.
- My own probe (`Probes/AuditProbe_g2k_A1.lean`, deleted after use) printed:
  `'ReflectedBand_t14_Kernel.pilot_kernel' depends on axioms: [propext, Classical.choice, Quot.sound]`.
  The probe's clean-context restatement gave the same axiom set.

## 4. Hypothesis-freeness / no oracle input

- `#check @ReflectedBand_t14_Kernel.pilot_kernel` shows a bare `∃ xs, ...` with no binders.
- The three memberships are theorems with no binders:
  `gLine14_encl : -(1/2) ≤ gLine 14 ∧ gLine 14 ≤ -(1/137438953472)`,
  `gLine15_encl : 1/137438953472 ≤ gLine 15 ∧ gLine 15 ≤ 4`,
  `gLine22_encl : -8 ≤ gLine 22 ∧ gLine 22 ≤ -(1/36028797018963968)`.
- `hmem`/`hArb`/`hLine`/`henc` binders appear in the closure only in `CheckBand.checkLine_correct`
  (whose `hmem` is discharged inside `pilot_kernel` by the proved memberships),
  `ReflectedBand_t14.pilot` (the Arb-conditional sibling: `pilot_kernel` uses only its `grid`) and
  `XiLineZeros.lambda_zero_*` (not used). None of them reaches the conclusion as an open assumption,
  and the absence of binders together with the clean axiom set confirms this.
- A grep of the closure for `axiom`/`opaque`/`unsafe`/`implemented_by`/`extern`/`native_decide`/
  `ofReduceBool`/`ofReduceNat`/`skipKernelTC`/`sorryAx` found matches only in comments and docstrings
  (and in the `#print axioms` idiom). There were no declarations.

## 5. Independent numerics (mpmath, 40 digits)

gLine is defined as `(completedRiemannZeta (1/2 + t I)).re`. I reimplemented it as
Re(pi^(-s/2) Gamma(s/2) zeta(s)). Each box `(lo, hi, e)` denotes [lo 2^e, hi 2^e] (`DIntv.memR`).

| t  | gLine(t) (mpmath)   | box                         | contains | excludes 0 |
|----|---------------------|-----------------------------|----------|------------|
| 14 | -2.05140834889e-6   | [-0.5, -7.276e-12]          | yes      | yes        |
| 15 | +6.26590862439e-6   | [7.276e-12, 4.0]            | yes      | yes        |
| 22 | -3.1869137015e-8    | [-8.0, -2.776e-17]          | yes      | yes        |

- Im Lambda at these points is at most 1e-46 (it is real on the line, as expected).
- Zeros: findroot gives 14.1347251417347 and 21.0220396387716, which agree with
  `mp.zetazero(1)` and `mp.zetazero(2)`. They fall in (14, 15) and (15, 22), as the IVT chain
  requires. On an 8000-point grid the only sign changes in [14, 22] are at 14.135 and 21.023, and
  `nzeros(22) - nzeros(14) = 2`. The next zero, 25.0109, lies outside the band.
- The mantissas decode as follows: -68719476736 = -2^36, 549755813888 = 2^39, and
  -288230376151711744 = -2^58, with exponents -37, -37 and -55. These give exactly the rational
  bounds in the membership theorems.

## 6. What this establishes and what it does not

It establishes a kernel-checked proof, with no hypotheses and axioms only in {propext,
Classical.choice, Quot.sound}, that Mathlib's `completedRiemannZeta` has at least two distinct
zeros on the critical line with ordinates in [14, 22]. Kernel-proved interval enclosures of
Re Lambda at t = 14, 15, 22 are combined with the IVT. No Arb or oracle input is involved.

It does not establish RH or anything about zeros off the line. It does not show that these are all
the zeros in [14, 22] (the statement is a lower bound, "at least 2"), and it says nothing about
multiplicity or simplicity. It is a finite verification at low height. conjecture1_proved = False.

## Issues noted (non-blocking)

1. The gate invocation in the brief (`normalize_lean` of the whole statement file) returns False
   because the `import Mathlib` line stays in the needle. The registry path
   (`_normalized_statement`) returns True. Future briefs should call `_normalized_statement`, or
   strip the header and import lines first.
2. The node is still `status = "draft"`. This audit made no registry edits and ran no git
   operations.
