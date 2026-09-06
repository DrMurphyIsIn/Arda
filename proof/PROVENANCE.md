# Provenance

This repository began as a **snapshot** of an active proof campaign (origin
below) and has since become a live development surface in its own right: new
work lands here directly via reviewed PRs, gated by the same `lean-verify` CI.
For the modules that were imported, the origin remains the provenance record;
for post-snapshot modules, this repository's PR history is the record.

## Post-snapshot development in this repository

Since the `b2996c79` import (2026-08-15), the following landed natively here
(so the "byte-identical to origin" claim below applies to the *imported*
modules at the snapshot, not to these):

- `proof/formalization/R3Cert/`: the capped-joint g-step layer (`GStepCore`,
  `GLemmaConfig`/`GLemmaAssembly`, `CappedJointConfig`/`CappedJointSkeleton`/
  `CappedJointAchievable`) and related frontier modules — the commit series
  `2aa7c98` → `8fb4f8d` (ending in PR #19; the g-lemma port + closure landed
  via PR #20, merged 2026-08-21), plus the `e1d25e4` reframe.
- `telperion/`: the Positivstellensatz emitter family, the Chvátal–Gomory
  integer-rounding emitter, the Handelman/Putinar certificate finders, and the
  honesty gates (nonvacuity, witnessed-bound) — PRs #8–#10, #17, #18 plus
  direct commits (e.g. the Handelman finder, `16dbc2d`).

All of it is recorded in this repository's history with green CI.

## Origin

- Origin: a private research monorepo (the proof lived under an
  `experiments/…/laplacian_ratio/` subtree)
- Origin branch: `experiment/laplacian-fischer-cavity`
- **Snapshot commit: `b2996c79`** (2026-08-15)
- CI evidence at the snapshot commit: the origin's `lean-verify` CI job —
  **success** (full `lake build` of all 90 R3Cert modules,
  Lean v4.32.0 + pinned Mathlib; no `sorry`, no added axioms). The same job
  has run green on every milestone commit of the campaign (17+ verdicts for
  the R47 arc alone).

## What was changed in the import (and nothing else)

1. Restructure: `formalization/` kept verbatim (design `.md` docs relocated to
   `docs/design/`); Python modules moved to `verification/` as a package;
   `verify_20260814.py` → `verify.py`.
2. Mechanical import rewrite: the dotted prefix
   `experiments.graph_hunter.laplacian_ratio` → `verification` (and the
   corresponding path strings in docstrings/docs). No logic changes.
3. Vendored two small shared modules the hunter imports
   (`tree_search.py`, `objective.py`, from `experiments/graph_hunter/` at the
   same commit; headers note this).
4. Excluded: personal correspondence (`outreach/` letters/replies/submission
   draft) and the in-revision paper (`paper_laplacian_ratio_maximizer.*` —
   held out pending the post-campaign rewrite). The two technical companion
   notes from `outreach/` (`kelmans_confluence`, `matching_bridge`) ARE
   included, relocated to `docs/notes/`.
5. One stale test assertion updated: `tests/test_lr.py::test_conjecture1_status_map`
   asserted the pre-2026-08-14 wording of the R7 ledger entry ("OPEN"); the origin
   ledger superseded that entry (R7' architecture) without updating the test. The
   assertion now accepts either wording while still enforcing the honesty
   invariant (`conjecture1_proved is False`, no unqualified "proven").
6. Fresh git history (single import commit): the origin history interleaves
   unrelated work from the host monorepo and the excluded correspondence.

The Lean project (`formalization/lakefile.toml`, `lean-toolchain`,
`lake-manifest.json`, `R3Cert.lean`, `R3Cert/*.lean`) is **byte-identical** to
the origin at the snapshot commit.

## Re-import procedure (historical)

This repository is now the primary development surface; new work lands here
directly via reviewed, CI-gated PRs. The procedure below is retained as a record
of how the imported modules were brought over from the origin, at a
lean-verify-green commit `<C>`:

```bash
git archive <C> experiments/graph_hunter/laplacian_ratio | tar -x -C /tmp/stage
# re-apply steps 1-4 above (restructure, import rewrite, vendoring, exclusions),
# update the snapshot commit + pipeline ID in this file, single commit here.
```

Planned re-import milestones: the `R47Rate` port green; the `R7'` assembly
green; the dispatched independent review.
