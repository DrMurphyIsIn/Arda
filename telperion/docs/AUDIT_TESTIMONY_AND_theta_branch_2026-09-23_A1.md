# Audit testimony: AND_theta_branch (anduril), blind auditor A1, 2026-09-23

- pass: true
- axioms_clean: true
- statement_byte_identical: true (modulo whitespace; canonical gate `V.statement_matches` = True)
- conjecture1_proved = False

## (1) Read-back of the registry statement (written before opening the artifact)

For every real t > 0 there is a real Lambda such that the Gauss-product partial values
n -> (t/2) log n - sum_{k=0}^{n} arctan((t/2)/(1/4 + k)) (`ThetaGap.imLnVal (1/4) (t/2)`)
converge to Lambda, and |Lambda - (t/2) log pi - thetaMain t| <= 1/t, where
thetaMain t = (t/2) log t - (t/2) log(2 pi) - t/2 - pi/8. Lambda is the continuous-branch
Im log Gamma(1/4 + it/2), so the claim is |theta(t) - RS main term| <= 1/t at every
positive height. This is a uniform analytic phase bound. It is not a zero count and not RH.

## (2) Statement gate

- Canonical path: `R.load_campaign(Path('telperion/missions/anduril'))`, node `AND_theta_branch`,
  `V.statement_matches(RSTheta.lean text, V._normalized_statement(node, root))` gives True.
- A whitespace-normalized comparison of the Statements file against the artifact theorem header
  also gives an exact match.
- `V.artifact_incompleteness_markers` returns [] for all 5 local closure modules: RSTheta,
  ThetaConverge, ThetaValue, ArctanTaylor, DlvpTheta (zero_free_bridge, reached through zzl_core).

## (3) Build and axioms

- `leanlock.sh lake build RSTheta`: Build completed successfully (8661 jobs). The log has no
  "declaration uses" warnings and no errors.
- Own probe (`Probes/AuditProbe_AND_theta_branch_A1.lean`, deleted afterwards):
  `#print axioms RSDesignTheta.gaussBranch_theta_sub_thetaMain_le` gives
  [propext, Classical.choice, Quot.sound].
- The same probe re-elaborated the registry statement text outside the namespace, as an
  `example` typed by that theorem. It type-checked.

## (4) Hidden hypotheses

- The theorem's only hypothesis is `ht : 0 < t`.
- It calls `ThetaConverge.convergence_obligation` (its hypotheses 0 < x and Gamma != 0 are
  discharged in the proof) and `theta_sub_thetaMain` -> `theta_bracket` -> `lam_bracket`.
- No hmem/hArb/hLine binders reach the theorem. The only `hmem` is a local `have` at
  RSTheta:102.
- The tokens axiom, opaque, native_decide, ofReduceBool, implemented_by, extern and the word
  sorry appear in the closure only inside docstrings.

## (5) Vocabulary and numerics

- The ANDDefs mirrors are character-identical to the island definitions, `ThetaGap.imLnVal`
  (ThetaValue.lean:180-181) and `ZeroFreeBridge.thetaMain` (DlvpTheta.lean:243-244).
- The artifact imports the real island definitions. It does not redefine or shadow them.
- mpmath check at dps 40, with thetaMain reimplemented from its Lean definition. Here
  theta = Im loggamma(1/4 + it/2) - (t/2) log pi, which equals mpmath `siegeltheta`:

  | t | theta - thetaMain | 1/t |
  |---|---|---|
  | 1 | 0.04409 | 1 |
  | 10 | 2.085e-3 | 0.1 |
  | 100 | 2.083e-4 | 0.01 |
  | 10000 | 2.083e-6 | 1e-4 |

  The gap behaves like 1/(48t), inside the artifact's claimed bracket [-1/(2t), 3/(16t)].
- Partial sums of imLnVal converge to Im loggamma: at t = 10, n = 1e5 is within 4e-5.

## (6) Establishes / does not establish

- Establishes (kernel-checked, no `sorry`, standard axioms): convergence of the Gauss-branch
  theta series, and a height-uniform bound |theta(t) - thetaMain(t)| <= 1/t for all t > 0.
- Does not establish: any zero location, any finite-verification height, or RH.
  conjecture1_proved = False.
