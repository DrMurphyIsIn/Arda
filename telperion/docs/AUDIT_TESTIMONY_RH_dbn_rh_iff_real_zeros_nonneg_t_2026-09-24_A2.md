# Audit testimony: RH_dbn_rh_iff_real_zeros_nonneg_t (A2, blind)

- Auditor: A2 (blind, no author context), 2026-09-24
- Node: `RH_dbn_rh_iff_real_zeros_nonneg_t` (mission rh), depends_on `RH_dbn_rh_iff_H0_real_zeros` (C4), `RH_dbn_real_zeros_upset` (M1b)
- Artifact: `telperion/examples/dbn/lean/DBNM1RHIff.lean`, theorem `dbn_rh_iff_real_zeros_nonneg_t`

## Verdict

- pass = true
- axioms_clean = true (`[propext, Classical.choice, Quot.sound]`)
- statement_byte_identical = true
- conjecture1_proved = False

## (1) Independent read-back (done before opening the artifact)

Statement file `missions/rh/lean/Statements/RH_dbn_rh_iff_real_zeros_nonneg_t.lean` (imports `Statements.RHDefs`):

  (for all rho : C, riemannZeta rho = 0 -> 0 < Re rho -> Re rho < 1 -> Re rho = 1/2)
  iff (for all t : R, 0 <= t -> for all z : C, DBN.H t z = 0 -> Im z = 0).

Left side: strip-form RH over Mathlib `riemannZeta`. Right side: every zero of H_t is real for every t >= 0 (classically Lambda <= 0, i.e. RH again). This is an equivalence of two restatements of one open conjecture. The left side is character-for-character the left side of the C4 statement `RH_dbn_rh_iff_H0_real_zeros`. The RHDefs `DBN` block (thetaMoment, Phi, HIntegrand, H) matches `DBNDefs.lean` lines 40-41, 211-214, 408-409 and 413 exactly; only the namespace wrapper lines differ.

## (2) Canonical gate

- `V.statement_matches(artifact, V._normalized_statement(node, root))` = True
- raw theorem header (from `theorem` to the proof body) is byte-identical between the statement file and the artifact
- `V.artifact_incompleteness_markers` = [] on the artifact and on all 19 modules of its dbn-island import closure (DBNDefs, DBNGKernel, DBNHadamard*, DBNHeatApprox, DBNHurwitz, DBNM1Approx, DBNM1Parametric, DBNM1RHIff, DBNRealZerosIff, DBNRealZerosIffFinal, DBNStep, DBNXi, DBNXiCos, DBNXiIBP, DBNXiRiemann)

## (3) Build and kernel probe

- `lake build --no-build` reports "All targets up-to-date (8807 jobs)", exit 0.
- Probe `#print axioms dbn_rh_iff_real_zeros_nonneg_t` gives the standard three only. The C4 and upset theorems also give the standard three.
- An `example` restating the registry statement verbatim, with the proof term `dbn_rh_iff_real_zeros_nonneg_t`, elaborates.
- The constants used in the theorem's type include Mathlib's root `riemannZeta` and the island's `DBN.H`. The island has no shadowing definition of either and no `axiom` or `opaque`.
- The probe file was deleted afterwards. Probe files belonging to other auditors were left in place.

## (4) Proves neither side

The proof is `rw [dbn_rh_iff_H0_real_zeros]`, then:
- (->) `dbn_real_zeros_upset 0 t ht h0`;
- (<-) specialisation at `t = 0`.

C4 and upset both carry no hypotheses; their signatures were checked with `#check`. `RiemannHypothesis` does not appear in DBNM1RHIff, DBNM1Parametric, DBNRealZerosIff or DBNRealZerosIffFinal. No RH-strength input enters as a hypothesis.

## (5) Establishes / does not establish

Establishes: strip-RH is equivalent to "all zeros of H_t are real for every t >= 0", with no `sorry` and axiom-clean. This is the sInf-free form of the C10 wall.

Does not establish: either side. That means no RH, no Lambda <= 0 and no bound on Lambda below de Bruijn's 1/2. Lambda is not defined on the island. conjecture1_proved = False.
