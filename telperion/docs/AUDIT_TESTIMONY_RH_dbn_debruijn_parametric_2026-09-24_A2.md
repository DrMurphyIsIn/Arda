# Audit testimony: RH_dbn_debruijn_parametric (A2, blind)

Auditor A2, no author context. I did not read the A1 testimony. conjecture1_proved = False.

**Verdict: pass = true, axioms_clean = true, statement_byte_identical = true.**

## 1. My read-back, done before I opened the artifact

The statement file is `missions/rh/lean/Statements/RH_dbn_debruijn_parametric.lean`. The DBN
block of `RHDefs` defines

    H t z = ∫_{u>0} e^{t u²} Φ(u) cos(z u) du,
    Φ(u) = Σ_{n≥1} (2π² n⁴ e^{9u} − 3π n² e^{5u}) e^{−π n² e^{4u}}.

This is the standard de Bruijn-Newman family. The theorem says: for every real `t0` and `Y`,
if every zero of `H_{t0}` satisfies `(Im z)² ≤ Y`, then for every `t ≥ t0` every zero of
`H_t` satisfies `(Im z)² ≤ max(Y − 2(t − t0), 0)`. That is de Bruijn 1950 Thm 13 (Polymath15
Thm 3.2), with no restriction on `t0` or `Y`. It is conditional on the caller's hypothesis
about `H_{t0}`, so it does not bound Λ and does not prove RH.

The node's DBN definitions in RHDefs (lines 100-114) match `examples/dbn/lean/DBNDefs.lean`
lines 40-41, 211-214, 408-409 and 413 byte for byte (checked with `diff`).

## 2. Canonical gate

I ran `R.load_campaign(Path('missions/rh'))` and `V._normalized_statement(node, root)`.

- `V.statement_matches(DBNM1Parametric.lean, stmt)` returned **True**.
- The statement text in the artifact (lines 132-134, `:=` removed) is **byte-identical** to
  lines 4-6 of the node file (`by sorry` removed). Checked with `diff`.
- `V.artifact_incompleteness_markers` returned `[]` for the artifact, and `[]` for every file
  in its dbn-island import closure: DBNDefs, DBNHadamard, DBNHadamardCount,
  DBNHadamardLinear, DBNHadamardMean, DBNHadamardProduct, DBNHeatApprox, DBNHurwitz,
  DBNM1Approx, DBNM1Parametric, DBNStep.

## 3. Build and axioms

- `leanlock.sh lake build --no-build` reported "All targets up-to-date (8807 jobs)".
- My probe `Probes/AuditProbe_RH_dbn_debruijn_parametric_A2.lean` (deleted afterwards) gave:
  - `#print axioms dbn_debruijn_parametric` returned `[propext, Classical.choice, Quot.sound]`.
  - An `example` that restates the registry statement verbatim, proved by
    `dbn_debruijn_parametric`, elaborated.
  - An `example` at `t0 = -5, t = 0` also elaborated.
  - These returned the same three standard axioms: `m1_norm_W_le_growth`,
    `m1_tendstoLocallyUniformly_G`, `m1_evenHadamardData_W`, `hurwitz_ne_zero_of_entire` and
    `H_zero_ne_zero`.

## 4. Negative t0

The growth bound is proved, not assumed. `DBN.m1_norm_W_le_growth` is stated for all
`(t0 δ : ℝ) (N : ℕ)` and has no hypotheses. It gives
`‖m1W t0 δ N z‖ ≤ A·exp(B‖z‖^{3/2})`, which is order at most 3/2 < 2.

`m1_evenHadamardData_W t0 δ N` also takes no hypothesis on `t0`, and neither do `m1W_zero`
and `m1W_succ`. `m1_tendstoLocallyUniformly_G` needs only `0 ≤ s`. The main proof never
requires `0 ≤ t0`.

**Numerical check** (mpmath at 40 digits, single process). I used Gauss-Legendre quadrature
with 40 panels × 48 nodes on u ∈ [0, 2].

- Calibration: `8·H_0(0)` = 0.497120778188, which equals ξ(1/2). The zeros of `H_0` sit at
  2γ₁ and 2γ₂.
- Setup: `t0 = 0`, `Y = 1`, `t = 0.3`. The bound is `(Im z)² ≤ 0.4`, that is `|Im z| ≤ 0.632`.
- `H_0.3` changes sign on the real line at three points in [20, 50]: 28.0958, 41.8183 and
  49.8457.
- Argument-principle winding numbers for `H_0.3`:

| Box | Winding number | Largest step |
|---|---|---|
| [20,50]×[0.05,1] | 0 | 1.07 rad < π |
| [20,50]×[−1,−0.05] | 0 | 1.07 rad < π |
| [20,50]×[−1,1] | **3** | 0.12 rad |

So all three zeros of `H_0.3` in the box are real, which is consistent with the conclusion.

## 5. Verdict

The artifact **establishes** the registry node RH_dbn_debruijn_parametric. The theorem is
kernel-checked from the three standard axioms, for all real `t0` and `Y`. It is conditional
on the caller's hypothesis about `H_{t0}`. It does not prove RH and does not bound the de
Bruijn-Newman constant. conjecture1_proved = False.
