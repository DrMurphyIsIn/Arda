# Audit testimony: RH_dbn_debruijn_parametric (blind auditor A1, 2026-09-24)

- pass: **true**
- axioms_clean: **true** (`propext`, `Classical.choice`, `Quot.sound` only)
- statement_byte_identical: **true**
- conjecture1_proved = False

## 1. What I read before opening the artifact

`missions/rh/lean/Statements/RH_dbn_debruijn_parametric.lean` (with `Statements/RHDefs.lean`, namespace `DBN`) says this. Take any real `t0` and `Y`. If every zero of `H_{t0}` has `(Im z)^2 <= Y`, then for every `t >= t0`, every zero of `H_t` has `(Im z)^2 <= max(Y - 2(t - t0), 0)`.

Here `H_t(z) = int_0^inf e^{t u^2} Phi(u) cos(z u) du`, and `Phi` is the standard de Bruijn-Newman kernel. This is de Bruijn's theorem (1950, Thm 13), also stated as Polymath15 Thm 3.2.

- It is conditional: the caller must supply what is known about `H_{t0}`.
- It says nothing about where the zeros of `H_0` lie. It does not imply RH.
- If `Y < 0`, the hypothesis claims `H_{t0}` has no zeros at all. That is false for the true `H_{t0}`, so the theorem is vacuous in that case, which is harmless.
- The RHDefs `DBN` block is a verbatim copy of `examples/dbn/lean/DBNDefs.lean`, lines 40-41, 211-214, 408-409 and 413. I compared them.

## 2. Canonical gate

- The node loads from `R.load_campaign(missions/rh)` with status `draft`.
- `V.statement_matches(DBNM1Parametric.lean, V._normalized_statement(node, root))` returns **True**.
- The raw statement text is byte-identical: I diffed the registry file lines 4-6 against artifact lines 132-134, after dropping the proof tails.
- `V.artifact_incompleteness_markers` finds nothing, both on the artifact and on all 11 files in its dbn-island import closure. Those files are DBNDefs, DBNStep, DBNHurwitz, DBNHeatApprox, DBNHadamard, DBNHadamardCount, DBNHadamardLinear, DBNHadamardMean, DBNHadamardProduct, DBNM1Approx and DBNM1Parametric.
- The closure does not include DBNStrip, DBNXi or any registry theorem.
- A search of the island for `axiom`, `opaque`, `implemented_by` and `extern` declarations found none.

## 3. Build and axioms

`lake build --no-build` reports "All targets up-to-date" for both the whole island (8807 jobs) and DBNM1Parametric.

My probe was `Probes/AuditProbe_RH_dbn_debruijn_parametric_A1.lean`, deleted after use. It printed the three standard axioms for each of:
- `dbn_debruijn_parametric`
- `DBN.m1_norm_W_le_growth`
- `DBN.m1_evenHadamardData_W`
- `DBN.m1_tendstoLocallyUniformly_G`

An `example` restating the registry proposition verbatim compiled with `:= dbn_debruijn_parametric`.

## 4. Negative t0

The growth bound is proved, not assumed. `m1_norm_W_le_growth (t0 δ : ℝ) (N : ℕ)` has no sign hypothesis on `t0` and proves `‖m1W t0 δ N z‖ ≤ A exp(B ‖z‖^(3/2))`. My probe instantiated it at `t0 = -5`, and it compiled.

`m1W_zero : m1W t0 δ 0 = H t0` shows that this bound covers `H_{t0}` itself. `m1_evenHadamardData_W` feeds the order-3/2 bound into `evenHadamardData_of_order_lt_two`, with `ρ = 3/2 < 2` discharged by `norm_num`. The proof then takes the step lemma, iterates it, and applies Hurwitz to reach `H(t0+s)`. That limit is non-zero because of `H_zero_ne_zero`, which holds for every real `t`.

Numerics (float64 Gauss-Legendre quadrature, single process):
- **Quadrature check:** against `ξ(1/2 + iz/2)/8` in mpmath, the relative error was at most 1e-12.
- **Setup:** `t0 = 0`, `Y = 1`, `t = 0.3`, so the bound is `(Im z)^2 <= 0.4`.
- **Boxes above the axis:** the argument principle gives winding number 0 on the box Re [0.5, 60], Im [0.05, 3], and 0 on Re [0.5, 60], Im [0.633, 3].
- **Box across the axis:** the box Re [0.5, 60], Im [-0.5, 0.5] gives winding number 3.
- **Real axis:** there are 3 real sign changes, at about 28.10, 41.82 and 49.85. So the zeros of `H_0.3` in this range are real, which is consistent with the bound.
- **Accuracy margin:** the smallest `|H|` on any contour was about 1e-9, well above the quadrature error.

## 5. Verdict

**ESTABLISHES** the node as stated, for every real `t0` and `Y`, with no `sorry` and standard axioms only. It is a conditional contraction result. It does not locate the zeros of `H_0` and does not prove RH. conjecture1_proved = False.
