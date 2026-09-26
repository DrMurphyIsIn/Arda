# Audit testimony: RH_dbn_real_zeros_upset (blind auditor A2, 2026-09-24)

conjecture1_proved = False

| field | value |
|---|---|
| pass | true |
| axioms_clean | true |
| statement_byte_identical | true |
| artifact | `telperion/examples/dbn/lean/DBNM1Parametric.lean`, theorem `dbn_real_zeros_upset` |

## 1. Independent read-back (done before opening the artifact)

`missions/rh/lean/Statements/RH_dbn_real_zeros_upset.lean`: for all real `t0 <= t`, if every
complex zero of `DBN.H t0` is real, then every complex zero of `DBN.H t` is real. With the
RHDefs `DBN` block, `H t z = ∫_{u>0} e^{t u^2} Φ(u) cos(z u) du` and
`Φ(u) = Σ_{n>=1} (2π² n⁴ e^{9u} − 3π n² e^{5u}) e^{−π n² e^{4u}}`. That is the standard
Polymath15 / de Bruijn `H_t`, so the statement is de Bruijn's forward-in-time propagation of
real zeros (1950, Thm 13). The set of times with only real zeros is therefore an up-set.
This does not define Λ and bounds nothing.
RHDefs `DBN` block vs island `DBNDefs.lean` lines 40-41, 211-214, 408-409 and 413: identical
except for blank lines and the namespace wrapper.

## 2. Canonical gate

- `R.load_campaign(missions/rh)` loads the node (status draft).
- `V.statement_matches(artifact, V._normalized_statement(node, root))` = **True**.
- Raw bytes: the statement lines (without the trailing `:= by sorry` / `:= by`) are byte-identical (`cmp`).
- `V.artifact_incompleteness_markers` found none in the artifact or in any module of its 11-module
  import closure on the dbn island (DBNDefs, DBNStep, DBNHurwitz, DBNHeatApprox, DBNHadamard*
  x5, DBNM1Approx, DBNM1Parametric).
- No shadowing redefinition of `DBN.H`, and no notation, macro or `set_option` escapes in the closure.

## 3. Build and kernel

- `leanlock.sh lake build --no-build`: "All targets up-to-date (8807 jobs)".
- Probe, deleted after the run: `#print axioms dbn_real_zeros_upset` gives `[propext, Classical.choice, Quot.sound]`.
  An `example` restating the registry statement verbatim, closed by `dbn_real_zeros_upset`,
  elaborates.

## 4. Y = 0 specialisation and non-vacuity

- The probe re-derived `(Im z)^2 <= max (0 − 2(t − t0)) 0` directly from `dbn_debruijn_parametric t0 0`.
  The artifact's proof is the same instantiation, and it collapses `max` via `t0 <= t`.
- The content is genuine: M1a runs through iterated shift-average steps and Hurwitz on the
  locally uniform limit. It is not a trivial rewrite.
- `DBN.H_zero_ne_zero : ∀ t, H t 0 ≠ 0` (standard three axioms) means `H_t0` is never
  identically zero. So the hypothesis is not automatically false (which would make the
  implication vacuous), and the conclusion is not automatically true.
- With `t0 = 1/2` it adds nothing beyond de Bruijn's classical result. Also, the hypothesis at
  `t0` is supplied by the caller and is not proved anywhere on the island.

## 5. Verdict

The artifact ESTABLISHES the registry statement: kernel-checked, standard axioms only, no `sorry`.
It does NOT establish RH, `Λ <= 0`, or any fact about where the zeros of `H_0` lie.
conjecture1_proved = False.
