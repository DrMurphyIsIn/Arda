# Audit testimony: AND_edge_clear_glue (anduril), blind auditor A1, 2026-09-23

- pass: true
- axioms_clean: true
- statement_byte_identical: true (modulo whitespace; canonical gate True)
- conjecture1_proved = False

## 1. Read-back of the registry statement (done before reading the artifact)

`theorem hnzl_discharged (T0 T1 : ℝ) : ∀ y ∈ Set.uIcc T0 T1, riemannZeta (((-1 : ℝ) : ℂ) + ↑y * I) ≠ 0`
(with `open Complex`, so `I = Complex.I`). In words: for any two reals T0, T1 and every real y
in the closed unordered interval between them, the Riemann zeta function does not vanish at
s = -1 + iy. T0 and T1 are arbitrary and T0 = T1 = y is allowed, so this is the same as saying
zeta has no zero on the whole vertical line Re s = -1. It carries no hypotheses and no Arb or
oracle input. It is true: zeros off the real axis lie in 0 < Re s < 1; the zeros on the real
axis are the trivial zeros -2, -4, ..., and -1 is not one of them (zeta(-1) = -1/12).

## 2. Statement gate (canonical path)

- `R.load_campaign(Path('telperion/missions/anduril'))`, node `AND_edge_clear_glue`.
- `V._normalized_statement` = `theorem hnzl_discharged (T0 T1 : ℝ) : ∀ y ∈ Set.uIcc T0 T1, riemannZeta (((-1 : ℝ) : ℂ) + ↑y * I) ≠ 0`
- `V.statement_matches(artifact, normalized)` = True. My own comparison (whitespace collapsed,
  from the `theorem` keyword up to `:=`) also shows the two texts are identical.
- `V.artifact_incompleteness_markers` = [] for EdgeClearGlue.lean, ZetaZeroConfinement.lean,
  TuringBand.lean and RHInBoxAnalytic.lean.
- The artifact declares the theorem inside `namespace EdgeClearGlue`, so its full name is
  `EdgeClearGlue.hnzl_discharged`. The file also has `open Complex`, so `I` means the same thing in both files.

## 3. Build and axioms

- `leanlock.sh lake build EdgeClearGlue`: Build completed successfully (8735 jobs), exit 0.
  The only warnings came from the unused-simp-argument linter.
- Probe (`#print axioms`; deleted afterwards): `EdgeClearGlue.hnzl_discharged`,
  `EdgeClearGlue.riemannZeta_neg_one` and `ZetaZeroConfinement.zeta_zero_re_mem_strip` each depend on
  [propext, Classical.choice, Quot.sound].
- `#check`: `∀ (T0 T1 y : ℝ), y ∈ Set.uIcc T0 T1 → riemannZeta (↑(-1) + ↑y * I) ≠ 0`, with no other binders.
  The probe also re-elaborated the registry statement text against the proof, and
  instantiated it at T0 = T1 = y (every real y, `Set.left_mem_uIcc`) and at y = 0. All of these compiled.

## 4. Hidden hypotheses and trust

- The proof term is `fun y _ => riemannZeta_neg_one_add_mul_I_ne_zero y`. It does not use the
  interval membership and it has no hmem/hArb/hLine binder.
- `zeta_zero_re_mem_strip` takes only `(him : ρ.im ≠ 0) (hz : riemannZeta ρ = 0)`. It uses
  `zeta_zero_reflect` and Mathlib's `riemannZeta_ne_zero_of_one_le_re`.
- I searched EdgeClearGlue, ZetaZeroConfinement, DlvpZetaZeroFree, TuringBand, RHInBoxAnalytic,
  RHInBoxCore and DiffractionCore for axiom/opaque/unsafe/native_decide/ofReduceBool/
  implemented_by/extern/sorry/admit in code. I found none; the only matches are prose in docstrings.
  The `#print axioms` result above shows that nothing reaching the theorem uses a non-standard axiom.

## 5. Mathematical check

- y = 0: `riemannZeta_neg_one` is proved from `riemannZeta_neg_nat_eq_bernoulli 1` and `bernoulli_two`.
  mpmath gives zeta(-1) = -0.08333... = -1/12.
- y != 0: Re s = -1 ≤ 0 and Im s ≠ 0, so the strip theorem rules out a zero. This matches the known
  mathematics: trivial zeros are only at -2, -4, ... on the real axis.
- Numerical sanity check (untrusted): over y in [-100, 100] with step 0.05, the smallest value of |zeta(-1+iy)| is
  0.08333 (1/12), reached at y = 0.
- The quantifier over `Set.uIcc T0 T1` covers every real y, because T0 = T1 = y is allowed. The statement is not
  vacuous: `Set.uIcc` is never empty, and the probe instantiated it at every y.

## 6. What this establishes and what it does not

Establishes: zeta has no zero on the line Re s = -1. This is exactly the H2b / `hnzl` conjunct of the
Turing band `hArbT` binder, for all T0 and T1, with no hypotheses. So that conjunct no longer needs an Arb input.
Does not establish: the other conjuncts (hnzb, hnzt, hins still depend on the SlabClear numerical
facts), any band count, any zero on the critical line, or RH. This supports a finite verification up to a fixed height.
conjecture1_proved = False.
