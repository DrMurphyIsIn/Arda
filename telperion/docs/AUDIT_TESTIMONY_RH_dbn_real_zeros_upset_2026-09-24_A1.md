# Audit testimony: RH_dbn_real_zeros_upset (rh), blind auditor A1, 2026-09-24

- pass: true
- axioms_clean: true
- statement_byte_identical: true
- conjecture1_proved = False

## 1. Read-back (from the statement file and RHDefs, before the artifact)

`telperion/missions/rh/lean/Statements/RH_dbn_real_zeros_upset.lean`:

    theorem dbn_real_zeros_upset :
        ∀ t0 t : ℝ, t0 ≤ t → (∀ z : ℂ, DBN.H t0 z = 0 → z.im = 0) →
        ∀ z : ℂ, DBN.H t z = 0 → z.im = 0

Here `DBN.H t z = ∫_{u>0} e^{t u²} Φ(u) cos(z u) du`, with Φ the Polymath15 / Rodgers-Tao
theta series. RHDefs copies `thetaMoment`, `Φ`, `HIntegrand` and `H` verbatim from
`examples/dbn/lean/DBNDefs.lean`. I checked this by comparing the text. In words: for any real
`t0 ≤ t`, if every zero of `H_{t0}` is real, then every zero of `H_t` is real. This is the
up-set (forward heat-flow) half of de Bruijn's theorem. It makes no claim about where the zeros
of `H_0` are.

## 2. Canonical gate

- `R.load_campaign(Path('telperion/missions/rh'))`: node found, status `draft`.
- `V.statement_matches(artifact, V._normalized_statement(node, root))` against
  `examples/dbn/lean/DBNM1Parametric.lean`: **True**.
- The raw statement text appears in the artifact byte for byte (1 occurrence), followed by ` := by`.
- `V.artifact_incompleteness_markers`: **none** in the artifact or in any file of its local import
  closure. That closure is {DBNDefs, DBNStep, DBNHurwitz, DBNHeatApprox, DBNHadamard,
  DBNHadamardCount, DBNHadamardLinear, DBNHadamardMean, DBNHadamardProduct, DBNM1Approx,
  DBNM1Parametric}. Its external imports are Mathlib and Lc.LiCriterion.Basic.

## 3. Build and kernel checks

- `leanlock.sh lake build --no-build` (all default targets, including AxiomGuardDBN): exit 0,
  "All targets up-to-date (8807 jobs)".
- Probe `Probes/AuditProbe_RH_dbn_real_zeros_upset_A1.lean`, deleted after use:
  - `#print axioms dbn_real_zeros_upset` gives `[propext, Classical.choice, Quot.sound]`.
  - `#print axioms dbn_debruijn_parametric` gives the same three axioms.
  - An `example` that restates the registry statement verbatim is closed by `dbn_real_zeros_upset`.
  - An `example` of the Y = 0 instance of `dbn_debruijn_parametric` elaborates.
  - `H_zero_ne_zero t : H t 0 ≠ 0` holds, so `H_t` is never identically zero.

## 4. Y = 0 specialisation and non-vacuity

The proof instantiates `dbn_debruijn_parametric t0 0`. That theorem gives
`(Im z)² ≤ max (0 − 2(t − t0)) 0 = 0`, from which `Im z = 0`. It is exactly the Y = 0 case.

The parametric theorem is proved for real. It iterates a shift-average step lemma over reweighted
approximants that carry even Hadamard data. Hurwitz's theorem then transfers the bound to the
locally uniform limit `H (t0 + s)`. That limit is not identically zero (`H_zero_ne_zero`), so
Hurwitz applies.

The hypothesis `h0` is actually used. The proof does not rely on a degenerate definition, and the
conclusion does not hold without the hypothesis (at `t = 0` the conclusion alone is RH). With
`t0 = 1/2`, combining this with de Bruijn's theorem gives nothing new. The implication itself is
still a genuine theorem.

## 5. Verdict

**Established:** `RH_dbn_real_zeros_upset` as stated. It is kernel-checked, uses only the three
standard axioms, and contains no `sorry`.

**Not established:** anything about the zeros of `H_0`, the de Bruijn-Newman constant (it is not
defined on this island), `Λ ≤ 0`, or RH. The theorem is conditional on the caller's hypothesis
about `H_{t0}`. conjecture1_proved = False.
