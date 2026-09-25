# Audit testimony: RH_dbn_debruijn_real_zeros (blind auditor A1)

- node: `RH_dbn_debruijn_real_zeros` (rh campaign, Route C / C3, de Bruijn 1950)
- auditor: A1 (blind; no author context consulted before the verdict)
- date: 2026-09-23
- artifact: `telperion/examples/dbn/lean/DBNHadamardApprox.lean`, theorem `dbn_debruijn_real_zeros`
- pass: true
- axioms_clean: true
- statement_byte_identical: true (byte-identical modulo whitespace)
- conjecture1_proved = False

## 1. Read-back (written before reading the artifact)

For every real t with t >= 1/2, and every complex z, if DBN.H t z = 0 then Im z = 0.
Here DBN.H t z is the integral over u in (0, oo) of e^{t u^2} Phi(u) cos(z u), with the
Polymath15 / Rodgers-Tao kernel Phi(u) = sum over n >= 1 of
(2 pi^2 n^4 e^{9u} - 3 pi n^2 e^{5u}) exp(-pi n^2 e^{4u}). In words: for every t >= 1/2 all
zeros of H_t are real, meaning the de Bruijn-Newman constant satisfies Lambda <= 1/2. This is
de Bruijn's 1950 theorem. It is not as strong as RH: RH is equivalent to Lambda <= 0, which is
the statement about H_0.

## 2. Statement gate (canonical path)

- `R.load_campaign(Path('missions/rh')).nodes['RH_dbn_debruijn_real_zeros']` gives normalized
  statement `theorem dbn_debruijn_real_zeros : ∀ t : ℝ, 1 / 2 ≤ t → ∀ z : ℂ, DBN.H t z = 0 → z.im = 0`.
- `V.statement_matches(artifact_text, normalized)` = True. My own whitespace-stripped
  comparison of the Statements file and the artifact signature = True.
- `V.artifact_incompleteness_markers` returns [] on all 21 island modules (the whole dbn
  closure plus AxiomGuardDBN and the unrelated C2/C4 modules). An independent grep finds no
  `axiom`, `opaque`, `extern`, `implemented_by` or `native_decide`, no `sorry` and no `admit`.
- The RHDefs DBN block (thetaMoment, Phi, HIntegrand, H) is line-for-line identical to
  DBNDefs.lean lines 40-41, 211-214, 408-409 and 413. The registry DBN.H is therefore the island's DBN.H.

## 3. Build and axioms

- `leanlock.sh lake build --no-build`: "All targets up-to-date (8759 jobs)". The AxiomGuard output
  lists `dbn_debruijn_real_zeros` with [propext, Classical.choice, Quot.sound].
- My own probe (`Probes/AuditProbe_C3_A1.lean`, now deleted) printed
  `'dbn_debruijn_real_zeros' depends on axioms: [propext, Classical.choice, Quot.sound]`.
  An `example` with the exact registry type elaborated against `dbn_debruijn_real_zeros`.

## 4. Semantic checks

- The statement is exactly de Bruijn's theorem: t >= 1/2 and ALL zeros real, with no side hypotheses.
  It is not vacuous. If H_t were identically 0 or undefined (Bochner value 0), the conclusion
  would be false at non-real z, so the kernel-checked proof rules both out.
- It is not RH-strength. The final type carries no hypotheses. Its closure discharges the two
  obligations of DBNDeBruijnReduction, and neither is RH:
  `H0ZeroFreeOffStrip := ∀ z, 1 < z.im^2 → H 0 z ≠ 0` (the |Im| > 1 strip, proved as
  `H0_zero_strip` in DBNStrip) and `ApproxHadamard` (even Hadamard data for every approximant
  Gδ δ k = ∫ cosh(δu)^k Phi(u) cos(zu)).
- The Hadamard factorisation is proved, not assumed. `approxHadamard` is a theorem obtained
  from `evenHadamardData_of_order_lt_two` (differentiable + even + not identically 0 + growth
  A exp(B|z|^ρ) with ρ = 3/2 < 2). `EvenHadamardData` is a structure with a genuine
  `tendsto_prod` field, so it is not vacuous. No Hadamard hypothesis or axiom appears in the closure.

## 5. Numerics (mpmath, dps 40, 64 x 24-point Gauss-Legendre on u in [0, 1.6], Phi(1.6) ~ 1e-814)

- Kernel sanity: H_0(z) equals xi(1/2 + iz/2)/8 to 12 digits at z = 0, 10+0.3i, 35-0.7i and 0.5i.
- Argument principle for H_{1/2} on the boxes Re in [0,60], Im in [0.1,1] and Im in [-1,-0.1]:
  winding 0 in both (|value| ~ 1e-40), min |H| on the boundary 8.7e-10 (not near 0), and 344
  adaptive evaluations. Positive control: H_{1/2}(z)(z - (30+0.5i)) gives winding 1.0.
- Thin box Re in [0.5,60], |Im| <= 0.05: winding 3 for t = 0 and for t = 1/2.
  The H_{1/2} real zeros are 27.980, 41.668 and 49.728, shifted inward from the H_0 zeros.
- The H_0 real zeros are 2*gamma_k for k = 1..3: 28.26945028346940, 42.04407927754310 and
  50.02171516029140. Each matches 2*Im(zetazero(k)) to 1e-36.

## 6. Verdict

ESTABLISHES that, for the island's Polymath15 DBN.H, H_t has only real zeros for every t >= 1/2
(de Bruijn 1950, Lambda <= 1/2). The proof is unconditional, kernel-checked, axioms-clean, and
the statement is byte-identical to the registry.
DOES NOT ESTABLISH anything about the zeros of H_0 inside |Im z| <= 1, Lambda <= 0, or RH.
Registry note, not a proof defect: the node toml still reads status = "draft" and its title
says "STATED ONLY, not proved". This audit does not edit the registry.

conjecture1_proved = False
