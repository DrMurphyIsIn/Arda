# Provenance

This repository is a **snapshot** of an active proof campaign. Until the
campaign completes, the source of truth is the origin repository; this package
is re-imported at green milestones.

## Origin

- Origin repository: `gitlab.com/DrMurphyIsIn/arda-trading` (private research
  monorepo; the proof lived under `experiments/graph_hunter/laplacian_ratio/`)
- Origin branch: `experiment/laplacian-fischer-cavity`
- **Snapshot commit: `b2996c79`** (2026-08-15)
- CI evidence at the snapshot commit: GitLab pipeline **2762803858** — job
  `lean-verify` **success** (full `lake build` of all 90 R3Cert modules,
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

## Re-import procedure (until cutover)

From the origin repository, at a lean-verify-green commit `<C>`:

```bash
git archive <C> experiments/graph_hunter/laplacian_ratio | tar -x -C /tmp/stage
# re-apply steps 1-4 above (restructure, import rewrite, vendoring, exclusions),
# update the snapshot commit + pipeline ID in this file, single commit here.
```

Planned re-import milestones: the `R47Rate` port green; the `R7'` assembly
green; the dispatched independent review.
