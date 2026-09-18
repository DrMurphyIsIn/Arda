# MM torus-section ladder T1 -- MM_torus_section_dictionary + MM_torus_section_n2_rigidity

Session `mm-torus-ladder-t1-2026-09-18`. Branch `mm/torus-ladder-t1` (base
`origin/rh/million-turing`). Island: `telperion/examples/quasicrystal` (Lean
v4.32.0, Mathlib v4.32.0).

**conjecture1_proved = False.** No RH progress is claimed here, and neither of the
two nodes below is counted as a win -- see the grade section.

## 1. What was delivered

One new artifact, `telperion/examples/quasicrystal/lean/TorusSectionLadder.lean`,
sorry-free, registered as a `lean_lib` and a `defaultTarget`, guarded in
`AxiomGuardQC.lean`. It contains:

| Theorem | Registry node | Route |
|---|---|---|
| `Quasicrystal.torus_section_dictionary` | `MM_torus_section_dictionary` (draft) | `simp [twoFreq, linearTorusForm, torusOrbit, Fin.sum_univ_two]` |
| `Quasicrystal.torus_section_n2_rigidity` | `MM_torus_section_n2_rigidity` (open) | `simp only [<- torus_section_dictionary]; exact twoFreq_realRooted_iff ...` |
| `Quasicrystal.expSum_eq_linearTorusForm_torusOrbit` | (none -- vocabulary anchor only) | `rfl` |

Both node theorems are stated VERBATIM from the registry statement files
`telperion/missions/mirrormere/lean/Statements/MM_torus_section_{dictionary,n2_rigidity}.lean`
(same names, same binder lists). The three ladder definitions (`torusOrbit`,
`linearTorusForm`, `expSum`) are MIRRORED verbatim from `MMDefs.lean:69-76` into the
module's own `Quasicrystal` namespace, following the `E6Bridge.lean` precedent, so
the registry's normalized-containment grant gate matches the artifact.

The general-N identity `expSum = linearTorusForm on torusOrbit` is recorded as
`rfl` -- exactly the zero-content statement the 2026-09-14 blind audit flagged. It
is kept as an explicit vocabulary anchor and is deliberately NOT a node.

## 2. Grade (adversarial verdict, recorded rather than hidden)

Both nodes are **simp-grade vocabulary bridges, not mathematics**:

- The dictionary is a Fin-2 sum unfolding across two vocabularies. The audit's
  "non-rfl" note is technically correct (it is not definitional -- `Fin.sum_univ_two`
  plus `Matrix.cons_val_zero`/`cons_val_one` fire), but `simp` closes it in one line.
- `torus_section_n2_rigidity` is a one-line rewrite into the island's already-proved
  `twoFreq_realRooted_iff` (`TwoFreqRigidity.lean:92-94`). All mathematical content
  lives there. Its registry `kind = "milestone"` is **inflated**: it is a lemma.

They are delivered because the ladder's vocabulary needs them and the registry
consumes them (the T1 track of `QC_TORUS_SECTION_LADDER_MEMO_2026-09-14`, sections
5-6), not because they advance anything. Both attempts are logged in
`attempts.jsonl` with that verdict written out.

## 3. Registry actions taken (and deliberately not taken)

- `telperion mission link` recorded on BOTH nodes: artifact
  `../../examples/quasicrystal/lean/TorusSectionLadder.lean`, kind `lean_module`,
  via `direct`. `set_proof` does not gate on status, so the draft node accepts the
  link.
- `telperion mission attempt` recorded for both (verdict `Proved`, with the
  simp-grade verdict spelled out in the detail field).
- **No grant.** Two independent blocks:
  1. `MM_torus_section_dictionary` is still `draft` (its statement was REVISED after
     the 2026-09-14 audit refuted the original general-N form); `grant_status`
     refuses any node whose status is not `open`. The re-audit is the author item
     `mm-dictionary-reaudit` and must land first.
  2. The artifact lives on the climb branch while the registry lives on `main`, so
     the grant is deferred to the branch reconcile, matching every other
     climb-linked MIRRORMERE node (e.g. `MM_twofreq_realrooted_iff`).
- The containment gate was nevertheless dry-run offline against the artifact for
  both nodes: `stmt_in_artifact = True` in each case, so the grant is a formality
  once status and branch allow it.

## 4. Telperion certificate-kind verdict

No new emitter kind was built, and none is missing for this shape. The shape here is
"a variable-map / reparametrization between two vocabularies over an underlying
certificate", which the registry already classifies:
`VarMapAdapterEmitter` (MapSpec-driven substitution rewrite, `STRUCTURALLY_NONVACUOUS`,
"no new identity") and `ReparamAdapterEmitter` (cast-rewrite adapter,
`STRUCTURALLY_NONVACUOUS`, "no new identity"). Both stances say in as many words
what this bridge is: structural, carrying no independent identity. Staffing a
generator to emit a single one-line `simp` lemma would manufacture ceremony, not
verification.

The certificate-bearing neighbour already exists and is untouched:
`SelfInversiveRigidityEmitter` (`examples/selfinversive_rigidity/generate.py`) emits
exact equal-modulus rigidity INSTANCES against `twoFreq_realRooted_iff`, and its
drift gate is green (`check: OK (regeneration matches frozen output byte-for-byte)`).
The concrete future hook, if the ladder ever needs it: point that emitter's profile
at `torus_section_n2_rigidity` instead, which is exactly a `VarMapAdapter` over the
existing family -- no new kind, a target swap.

## 5. Build and guard evidence

`lake build` (all defaultTargets, island): `Build completed successfully (3116 jobs).`
`lake build TorusSectionLadder`: `Built TorusSectionLadder`, clean on first pass.
`lake env lean AxiomGuardQC.lean`: 45 theorems printed, zero `sorryAx`, zero
`ofReduceBool`. The three new lines:

```
'Quasicrystal.expSum_eq_linearTorusForm_torusOrbit' depends on axioms: [propext, Classical.choice, Quot.sound]
'Quasicrystal.torus_section_dictionary' depends on axioms: [propext, Classical.choice, Quot.sound]
'Quasicrystal.torus_section_n2_rigidity' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 6. Notes for the next hand

- **COLLISION, must be resolved at reconcile.** `TorusSectionLadder.lean` was
  assigned to BOTH this item and `mm-euler-factor-offline` (the T2 negative control,
  memo section 4b), and the two were executed in parallel in separate worktrees.
  The sibling's version of the same path declares `namespace TorusSectionLadder` and
  carries `euler_factor_section_offline` + witnesses (observed in a guard run against
  the SHARED `.lake` at `~/arda-million/.../quasicrystal/lean/.lake`, which both
  islands symlink); this version declares `namespace Quasicrystal` and carries the T1
  bridges. The two branches therefore conflict on this file and on the same
  `lean_lib` name, and while both are live they clobber each other's olean in the
  shared build cache. Resolution is a straight union -- the file already imports
  `TwoFreqRigidity` and carries the ladder vocabulary, so the T2 rung appends with no
  new lakefile plumbing beyond its `#print axioms` lines -- but the namespaces must be
  reconciled first (the registry statements for T1 are `open Quasicrystal`, so the T1
  theorems must stay resolvable as `Quasicrystal.torus_section_*`). My guard output
  below was re-run after a clean rebuild of MY source to make sure it reflects this
  branch and not the sibling's cached olean.
- The v4.32 simp spellings did fire as predicted (`Matrix.cons_val_zero`,
  `Matrix.cons_val_one`, `Matrix.head_cons` are reached through the default simp set
  via `Fin.sum_univ_two`); the risk flagged in the work item did not materialize.
- CI: the island is built by the `selfinversive-rigidity-compiles` job, which runs
  `lake build SelfInversiveRigidityInstances` only. Adding `TorusSectionLadder` to
  `defaultTargets` does not put it in that job's path; a reconcile PR should either
  widen that step to a bare `lake build` or add a guard step. Flagged, not done here
  (CI edits are out of this item's scope).
