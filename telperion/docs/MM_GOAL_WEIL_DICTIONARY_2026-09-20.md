# MIRRORMERE goal node: Weil positivity plus a proved-or-not RH dictionary (2026-09-20)

*Registry work only. Nothing here proves, approaches or claims RH. Every node touched or
added is `status = draft`. `conjecture1_proved = False`.*

Branch `mm/goal-weil-equivalence` (cut from main at e3f69f9d7). Campaign `mirrormere`,
statement island `telperion/missions/mirrormere/lean` (leanprover/lean4:v4.32.0, Mathlib
v4.32.0). Session `goal-weil-dictionary-2026-09-20`.

---

## 1. What changed, and why

### The circularity that was there

The campaign goal `MM_zeta_comb_membership` was registered on 2026-09-14 as

```lean
theorem zeta_comb_membership : RiemannHypothesis := by sorry
```

with the title explaining that the intended target, Fourier-quasicrystal membership of the
zeta zero comb, is "RH-equivalent via the island's `zeta_FQ_iff_RH` dictionary". That
dictionary entry is `CharacterizationStatements.zeta_FQ_iff_RH` on the quasicrystal island,
which is a `def ... : Prop` over opaque variables. It is a recorded program conjecture, not a
theorem. So the goal node's identification with Mathlib's `RiemannHypothesis` was by fiat:
the registry said "the goal is RH" because a definition said so, and no kernel-checked
statement connected the program's own vocabulary to RH.

A prior team run (branch `mm/w3c-goal-weil-membership`, memo
`telperion/docs/MM_w3c_goal_weil_membership_DESIGN_2026-09-18.md`) authored the concrete
replacement statement in the program's diffraction vocabulary, but that branch never landed,
and it explicitly refused to register the RH-equivalence as anything ("it would be RH <-> RH").
That refusal left the equivalence as prose in a title.

### The fix

Two things, both registry-level:

1. The goal statement is re-authored to the concrete Weil-positivity form from the team
   branch (ported verbatim, see section 2). The vocabulary it needs, namespace
   `WeilExplicit`, is mirrored into `MMDefs.lean`: six definitions byte-identical to
   `telperion/missions/rh/lean/Statements/RHDefs.lean` lines 118-167 on main (verified with
   `diff`), plus the two AUTHORED definitions `autocorr` and `weilForm`, all with the source
   file's elaboration context (`noncomputable section`, `open MeasureTheory Complex`).

2. The RH-equivalence stops being assumed and becomes three draft `lemma` nodes whose
   statements are exactly the two halves of Weil's criterion on this vocabulary and their
   conjunction as an `Iff` against Mathlib's `RiemannHypothesis`. They are proved-or-not
   objects in the registry: if the rvm_bridge agents prove them and they are granted, the
   goal node is RH-hard for a kernel-checked reason. If not, the registry shows an open
   dictionary instead of a silent identification. Either way the goal node itself stays
   `kind = goal`, `status = draft`, never attempted.

The goal node's title keeps the team branch's text and appends one sentence: "The
RH-equivalence is NOT assumed: it is registered as the three dictionary nodes
MM_rh_implies_weil_positivity, MM_weil_positivity_implies_rh,
MM_zeta_comb_membership_iff_rh (2026-09-20)." `depends_on` is unchanged; `updated` is
2026-09-20.

What is deliberately NOT done here: no proof links, no `mission audit`, no `mission grant`.
The converse half is classical analysis (Weil 1952; Bombieri 2000 on C_c^infinity) and is not
RH-hard, but it has never been formalized in this repository and nobody has proved it yet.
The forward half discharges the hypothesis `hpos` that `weil_negative_refutes_rh` on the
`weil_form_enclosure` island has been carrying undischarged. Proofs are in flight on the
rvm_bridge island (files `E6Bridge5.lean` and `E6Bridge6.lean`, other agents). When they
land, the cross-island containment gate (precedent: `MM_zeta_ordinates_not_uniformly_discrete`
linked to `../../examples/rvm_bridge/lean/W2cAssembly.lean`) is the route.

---

## 2. The four statements, verbatim (post-header body as written to disk)

Every file below was produced by the registry writer
(`telperion.missions.statements.write_statement` for the goal node,
`telperion mission add --statement-file` for the three new nodes), so each carries the
`DO NOT EDIT BY HAND` header with its sha256 pin. The writer appended `:= by sorry`.

`lean/Statements/MM_zeta_comb_membership.lean` (node `MM_zeta_comb_membership`, kind goal,
draft; header sha256 8359dbcd312c0011):

```lean
import Mathlib
import Statements.MMDefs

theorem zeta_comb_membership :
    ∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g →
      0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re := by sorry
```

`lean/Statements/MM_rh_implies_weil_positivity.lean` (node `MM_rh_implies_weil_positivity`,
kind lemma, draft; sha256 bbc7d281bc379a43):

```lean
import Mathlib
import Statements.MMDefs

theorem rh_implies_weil_positivity (hRH : RiemannHypothesis) : ∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g → 0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re := by sorry
```

`lean/Statements/MM_weil_positivity_implies_rh.lean` (node `MM_weil_positivity_implies_rh`,
kind lemma, draft; sha256 495d1d8aa1d2491d):

```lean
import Mathlib
import Statements.MMDefs

theorem weil_positivity_implies_rh (hpos : ∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g → 0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re) : RiemannHypothesis := by sorry
```

`lean/Statements/MM_zeta_comb_membership_iff_rh.lean` (node
`MM_zeta_comb_membership_iff_rh`, kind lemma, draft, `depends_on` the two above;
sha256 10ecc16b57dabff7):

```lean
import Mathlib
import Statements.MMDefs

theorem zeta_comb_membership_iff_rh : (∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g → 0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re) ↔ RiemannHypothesis := by sorry
```

The vocabulary, for reading the statements (from `MMDefs.lean`, namespace `WeilExplicit`):

| name | status | meaning |
|---|---|---|
| `IsWeilTest g` | mirrored | `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ HasCompactSupport g` (C^infinity, compact support; NOT the analytic index) |
| `weilKernel g s` | mirrored | `∫ u, g u * exp ((s - 1/2) u)`, the zero-side transform |
| `zeroMult ρ` | mirrored | order of zeta at ρ on the open strip |
| `archIntegrand`, `archSide g` | mirrored | archimedean side of the E8 limit explicit formula |
| `primeSide g` | mirrored | `∑' n, Λ(n)/√n * (g (log n) + g (-log n))` |
| `autocorr g u` | AUTHORED | `∫ v, g v * conj (g (v - u))`, the Hermitian autocorrelation |
| `weilForm f` | AUTHORED | `archSide f - primeSide f`, the Weil functional read from the primes side |

By `RvMBridge4.limit_explicit_formula` (kernel-checked on main, node
`RH_limit_explicit_formula`), `weilForm f` equals the zero-side sum `∑_ρ zeroMult ρ *
weilKernel f ρ`, so the goal says that sum is nonnegative on every Hermitian autocorrelation.
That is Weil's criterion, hence the three dictionary nodes.

---

## 3. Vacuity checks

The team branch's probe file `lean/Probes/MM_zeta_comb_membership_WIP_PROBE.lean` was
restored into this worktree unchanged (it is outside `Statements.lean`, so it is not part of
the lake default target and is not axiom-guarded) and elaborated against the rebuilt
`Statements.MMDefs` on this island. It compiles. Its live checks, all of which passed here:

| probe | what it establishes | result |
|---|---|---|
| `test_class_nonvacuous` | `∃ g, IsWeilTest g ∧ g ≠ 0` (a `ContDiffBump` witness), so the goal's quantifier is not vacuous | passes |
| `smoothness_index_is_not_analytic` | `((⊤ : ℕ∞) : WithTop ℕ∞) ≠ ⊤` by `decide`: the class is C^infinity, not analytic-with-compact-support = {0} | passes |
| `degenerate_witness_is_contentless` | `(weilForm (autocorr 0)).re = 0` by `simp`: g = 0 satisfies the conclusion trivially, which is why nonvacuity above matters | passes |
| `autocorr_hermitian` | `autocorr g (-u) = conj (autocorr g u)`, unconditional, no sorry: the reason the statement takes `.re` | passes |
| `autocorr_zero_nonneg` | `0 ≤ (autocorr g 0).re`, unconditional, no sorry | passes |
| `instance_of_enclosure` | one certified positive enclosure gives the conclusion at that single g (hypotheses explicit) | passes |
| `neg_enclosure_refutes_rh` | a certified negative value refutes RH GIVEN the forward criterion as hypothesis `hcrit` (now node `MM_rh_implies_weil_positivity`) | passes |

The only `sorry` warning the compiler emitted is at line 46, the probe's own WIP restatement
`mm_goal_wip` of the goal, which is intentional. The probe file's section 2 records the
trivial-close battery (simp, simp_all, aesop, norm_num, positivity, and the two junk-value
probes `weilForm f = 0` and `autocorr g = 0`) as comments with the 2026-09-18 compiler output:
none closed the statement. Those were not re-run live here; the file is byte-identical to the
team branch and the vocabulary block it depends on is byte-identical too.

The mirrored six definitions were diffed against `RHDefs.lean` lines 118-167 of the worktree
HEAD (= main e3f69f9d7) before porting; the only differences are the leading comment block
and the trailing `end WeilExplicit`, which the branch's MMDefs also carries after the two
AUTHORED defs. Byte-identical def bodies.

---

## 4. Commands run, with their verbatim final lines

All from `/Users/peterwmurphy/arda-goal-weil/telperion` unless noted; Python is the system
`python3` with `PYTHONPATH=src` (the same invocation `telperion-test.yml` uses for the
registry gate). No `timeout` wrapper anywhere (not installed on this macOS).

Baseline build before any edit (`cd missions/mirrormere/lean && lake build`):

```
Build completed successfully (8675 jobs).
```

Rebuild after porting `MMDefs.lean`, re-authoring the goal, adding the three nodes and
listing them in `Statements.lean` (`cd missions/mirrormere/lean && lake build`):

```
✔ [8677/8678] Built Statements (4.1s)
Build completed successfully (8678 jobs).
```

Registry verifier:

```
$ PYTHONPATH=src python3 -m telperion.cli mission verify mirrormere
verify [mirrormere]: OK
$ PYTHONPATH=src python3 -m telperion.cli mission verify mirrormere --deep-lean
verify [mirrormere]: OK
```

Missions test battery (`PYTHONPATH=src python3 -m pytest -q tests/test_missions_*.py`):

```
FAILED tests/test_missions_mirror_drift.py::test_mirrormere_island_copies_are_verbatim
1 failed, 127 passed, 1 skipped in 18.47s
```

Probe file (`cd missions/mirrormere/lean && lake env lean Probes/MM_zeta_comb_membership_WIP_PROBE.lean`):

```
Probes/MM_zeta_comb_membership_WIP_PROBE.lean:46:8: warning: declaration uses `sorry`
```

(exit 0; the warning is the probe's own WIP restatement of the goal, by design.)

Ledger (`mission attempt`, session `goal-weil-dictionary-2026-09-20`, verdict `Stalled`,
the only honest value in the ledger vocabulary Proved/Refuted/NoGo/Stalled for "authored,
nothing proved"):

```
attempt recorded: MM_zeta_comb_membership [Stalled]
attempt recorded: MM_rh_implies_weil_positivity [Stalled]
attempt recorded: MM_weil_positivity_implies_rh [Stalled]
attempt recorded: MM_zeta_comb_membership_iff_rh [Stalled]
```

---

## 5. The one failing test, stated plainly

`test_missions_mirror_drift.py::test_mirrormere_island_copies_are_verbatim` was ALREADY
failing on this machine before any edit (baseline run: `hardyZ` in
`examples/rvm_bridge/lean/.lake/packages/Zeta23/...`), because the scan globs
`examples/*/lean/**/*.lean` and picks up the untracked, gitignored Zeta23 package under
`.lake`. CI does not have that directory, so that component does not fire there.

After this work the gate reports six drifted rows. Five are the same untracked `.lake`
false positives (`hardyZ`, three `zeroMult`, one `autocorr` in Zeta23, which are different
mathematics under colliding names). ONE is a tracked file and WILL fire in CI:

```
autocorr in telperion/examples/weil_form_enclosure/lean/WeilFormDefs.lean
```

That island declares, in namespace `WeilForm` (not `WeilExplicit`),
`noncomputable abbrev autocorr (g : ℝ → ℂ) : ℝ → ℂ := crossCorr g g`, which unfolds to the
same integral as the registry's `autocorr` but is not textually identical, and the drift
checker matches by bare declaration name. It is not a mathematical drift; it is a name
collision the name-keyed checker cannot tell apart. I did not touch it: `WeilFormDefs.lean`
is outside the file set this task allows me to edit. The integrator has three options:
rename the `WeilForm` abbrev (e.g. `autocorrDiag`), make the checker namespace-aware, or
make the enclosure island spell `autocorr` exactly as the registry does. This must be settled
before merge or the registry gate in `telperion-test.yml` goes red.

Also observed, not mine: `telperion/missions/mirrormere/lean/lake-manifest.json` shows as
untracked in `git status`; it was present before this session started.

---

## 6. Converse: the reduction and its obligations (later on 2026-09-20)

Status update since section 1: `MM_rh_implies_weil_positivity` (the forward half) is now
PROVED, audited, linked and granted by the integrator on the rvm_bridge island
(`E6Bridge5.lean`). The converse half was attacked in `E6Bridge6.lean` (namespace
`RvMBridge6`, 26 guarded theorems, axioms `[propext, Classical.choice, Quot.sound]`, no
sorry; memo `telperion/docs/WEIL_CONVERSE_ATTACK_2026-09-20.md`) and is proved MODULO two
named analytic obligations. The registry now records exactly that shape, nothing more.

### 6.1 Vocabulary mirrored into MMDefs.lean

Two new blocks, both verbatim, both inside the file's `noncomputable section`:

- `namespace Zeta23`: `paperFT` (Zeta23/Defs.lean:44), `gammaOf` (Zeta23/Defs.lean:105),
  `IsNontrivialZero` (Zeta23/Statement.lean:38), from the vendored package
  anthropics/formal-math at commit fbdc36bbf17d20af3fd0447c6d1a8a02773c9844 (the rvm_bridge
  lake-manifest pin); with `open Complex MeasureTheory Set` and `open scoped ComplexConjugate`
  as the sources declare. Diffed identical to the package lines.
- `namespace RvMBridge6`: `hermitianTransform`, `zeroSide`, `gaussTest` (E6Bridge6.lean
  81-99), `GaussianTransfer`, `GaussianDominance` (284-311), `GaussianApprox` (560-572), with
  their docstrings, under `open Zeta23 Complex MeasureTheory Filter Topology`, `open scoped
  ComplexConjugate`, `open WeilExplicit`. The name-keyed drift gate compares these against
  E6Bridge6.lean on disk and passes, so the six are verbatim by test, not by eye.

### 6.2 The four new nodes (all `lemma`, all `draft`)

| node | statement | deps | link |
|---|---|---|---|
| `MM_weil_positivity_implies_rh_of_gaussian` | `theorem weil_positivity_implies_rh_of (hO1 : GaussianTransfer) (hO2 : GaussianDominance) (hpos : ∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g → 0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re) : RiemannHypothesis` (preamble `open RvMBridge6`) | MM_gaussian_transfer, MM_gaussian_dominance | `../../examples/rvm_bridge/lean/E6Bridge6.lean`, lean_module, direct |
| `MM_gaussian_transfer` | `theorem gaussian_transfer : RvMBridge6.GaussianTransfer` | MM_gaussian_approx | none |
| `MM_gaussian_approx` | `theorem gaussian_approx : RvMBridge6.GaussianApprox` | none | none |
| `MM_gaussian_dominance` | `theorem gaussian_dominance : RvMBridge6.GaussianDominance` | none | none |

The reduction node's statement spells the obligations unqualified with `open RvMBridge6` in
the preamble because the grant gate matches by textual containment after dropping `open`
lines and collapsing whitespace, and the artifact writes them unqualified inside its
namespace. Checked at link time with the gate's own functions:

```
statement_matches: True
incompleteness_markers: []
```

Not audited, not granted: the reduction node waits for a blind read-back by another seat.

`MM_weil_positivity_implies_rh` now depends additionally on the three nodes
MM_weil_positivity_implies_rh_of_gaussian, MM_gaussian_transfer, MM_gaussian_dominance, and
its title carries "REDUCED 2026-09-20 to the two Gaussian obligations".

### 6.3 What is and is not proved

- Proved (E6Bridge6, kernel): the reduction itself; O1 from O1' (`gaussianTransfer_of_approx`,
  Tannery against the local zero count); the explicit formula for Hermitian autocorrelations
  with the zero side isolated and real; the reflection symmetry; the pair term of an off-line
  zero isolated; the strip lemma; summability of the Gaussian-weighted zero sum.
- Not proved, stated as `def : Prop` and consumed only as hypotheses: O2 `GaussianDominance`
  (the analytic heart: finite argmax, generic centre, tail split, phase choice; this is where
  the attack stopped) and O1' `GaussianApprox` (complex-argument Gaussian transform plus the
  truncation-uniform integration by parts; stopped at the Fourier side). Neither uses RH;
  neither is RH-hard; both are open here.
- The goal node is unchanged: kind goal, status draft, RH-hard.

### 6.4 Commands run, verbatim final lines

```
$ cd missions/mirrormere/lean && lake build          (after the MMDefs mirror)
Build completed successfully (8678 jobs).
$ cd missions/mirrormere/lean && lake build          (after the four new modules)
Build completed successfully (8682 jobs).
$ PYTHONPATH=src python3 -m pytest -q tests/test_missions_mirror_drift.py
6 passed in 11.70s
$ PYTHONPATH=src python3 -m telperion.cli mission verify mirrormere
verify [mirrormere]: OK
$ PYTHONPATH=src python3 -m telperion.cli mission verify mirrormere --deep-lean
verify [mirrormere]: OK
$ PYTHONPATH=src python3 -m pytest -q tests/test_missions_*.py
129 passed, 1 skipped in 13.75s
```

Ledger: four `Stalled` entries, session `goal-weil-dictionary-2026-09-20`, one per new node;
the reduction node's reads "proof artifact linked, awaiting blind audit", the obligation
nodes' carry the memo's section 4 stopping points. conjecture1_proved = False.
