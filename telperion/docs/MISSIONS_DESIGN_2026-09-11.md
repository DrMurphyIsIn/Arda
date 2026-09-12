# Telperion Missions — Internal Campaign Registry (Design, 2026-09-11)

Status: APPROVED design, pre-implementation.
Branch: `feat/missions-registry`. Base: `main` @ `98f99fc`.

## Context and intent

Prove2Me (prove2.me; Chen–Marwaha–Lu–Yuen–Peng, arXiv:2608.28433)
demonstrated an architecture for large-scale collaborative formalization:
missions decomposed into milestone theorems with authoritative statements,
a reusable kernel-checked library, reductions that import open
sorry-statements, a live open-leaves frontier, claim/attempt history, and
read-back audits of statement faithfulness. **This project absorbs that
architecture into Telperion itself — fully self-hosted, files + git, no
external service in control.** The operator's direction (2026-09-11): do
not act as a solver for the external platform; internalize the ideas.

What it replaces/mechanizes: the hand-written campaign layer
(`PROOF_STATUS.md`, `PROOF_ASSEMBLY.md`, relay docs) that parallel Claude
sessions currently coordinate through by convention. Those documents
remain as narrative; the registry becomes the tracking truth.

Decisions locked during brainstorming:

| Decision | Choice |
|---|---|
| Substrate | **Files + git** — versioned data in-repo; CI enforces invariants; no daemon |
| Pilot campaigns | **Both BG and RH**, machinery first, then two migration passes |
| V1 organs | Registry + open-leaves; verified library + reductions; claims + attempt ledger; read-back audits |
| Placement | **Public Arda repo, campaigns in-tree** (registry reveals nothing PROOF_ASSEMBLY.md doesn't already) |
| Deferred | Credit/trust scoring; discussion layer; any external-platform export |

## 1. Data model & file layout

```
telperion/missions/
├── bg/
│   ├── mission.toml              # campaign manifest
│   ├── nodes/<slug>.toml         # one file per node
│   ├── claims/<slug>.toml        # transient session claims (committed)
│   ├── attempts.jsonl            # append-only work ledger
│   └── lean/                     # campaign statement package (§2)
├── rh/                           # same shape
└── fixtures live under telperion/tests/, not here
```

`mission.toml`: `name`, `title`, `description`, `goal_node` (slug of the
main theorem), `environment` (toolchain + Mathlib rev, §2), `sources`
(paper references).

`nodes/<slug>.toml` (slug = Lean name with `.` → `_`):

- `name` — full Lean name, e.g. `BG.master_inequality`
- `title` — one line, human
- `kind` — `goal | milestone | lemma | definition`
- `status` — `draft | open | proved | refuted | deprecated`
- `depends_on` — list of node slugs (edges of the DAG)
- `statement_module` — module in the campaign's statement package
- `proof` — absent until linked; then `{artifact, artifact_kind: lean_module | frozen_cert, via: direct | reduction, closure_clean: bool}`
- `source` — where in the literature/prose docs this statement comes from
- `readback` — absent until audited; then `{text, auditor, date}` (§8)
- `deprecated_reason` — required iff status is `deprecated`
- `created`, `updated` — ISO dates

Why one file per node: with 4+ live sessions, claim = **add** a file,
attempt = **append** a line, status change = one-file edit — git merges
stay trivial and review diffs stay legible.

## 2. Statement packages and environments

Prove2Me's core mechanism internalized: every node owns
`missions/<campaign>/lean/Statements/<Slug>.lean` containing the
statement with a `:= sorry` body and a DO-NOT-EDIT provenance header
generated from the node file (same discipline as emitted certificates —
regeneration diffs flag hand edits).

**Environments (forced into v1 by repo reality).** The repo now has
toolchain islands — `proof/` and most examples on `leanprover/lean4:v4.32.0`,
the `li_positivity`/RvM island on v4.34 (unified by #483), the prove2me
compat example on v4.33.1. Therefore:

- Each campaign's statement package pins **one** environment, declared in
  `mission.toml` and written into `lean/lean-toolchain` +
  `lakefile.toml`. BG pins the `proof/` island (v4.32.0). RH pins the
  v4.34 island where its active work lives.
- **Artifact verification runs in the artifact's own home package** (its
  island's existing CI build); the registry's statement-match check (§3)
  is *syntactic* (normalized text via the comparator machinery), so a
  proved artifact on one island can discharge a registry node whose
  statement package lives on another. No cross-island olean imports are
  ever needed.
- Reduction proofs (§3) import statement modules and therefore live in
  the campaign's statement package, on its environment.

CI builds each statement package: a statement that does not elaborate
cannot enter the graph.

## 3. Status machine & the kernel gate

```
draft ──(read-back recorded)──────────────> open
open ──(verified artifact linked)─────────> proved | refuted
any ──(with deprecated_reason)────────────> deprecated
```

- `proved`/`refuted` are **granted only by verification** (CI job §7 +
  `mission verify` locally): the linked artifact must kernel-check in its
  home package AND its stated theorem must match the registry statement
  under normalized comparison. The registry can never claim more than CI
  can rebuild — the kernel stays the sole authority, exactly Prove2Me's
  trust model and Telperion's.
- **Reductions.** A node may link a proof `via: reduction`: a Lean proof
  in the campaign statement package that imports the sorry-statement
  modules of *other open nodes* (its children) and derives this node's
  statement. Deliberate divergence from Prove2Me: they auto-resolve
  parents when children land; we keep Telperion's honesty discipline —
  the node shows `proved (via reduction, closure_clean: false)` until CI
  can rebuild its entire import closure sorry-free, and only then flips
  `closure_clean: true`. A conditional result is never displayed as an
  unconditional one.
- `refuted` mirrors `proved` with a disproof artifact (statement match =
  the negation, normalized). The 2026-09-11 Hnorm refutation becomes the
  first refuted node at migration.
- `deprecated` requires a reason string; dead statements stay legible
  (Prove2Me's deprecation-with-history, internalized).
- Claims (§4) are advisory metadata, not statuses.

## 4. Claims & multi-session protocol

`claims/<slug>.toml`: `session` (id or human name), `started` (ISO),
`ttl_hours` (default 24), `note` (optional intent). Claim = commit the
file; release = delete it. A claim past TTL is claimable-over; the new
claim records `superseded` with the old session id. `open-leaves` hides
freshly-claimed nodes by default (`--all` shows them). CI treats claim
problems (claim on a non-open node, expired claims) as **warnings**, not
failures — claims coordinate, they do not lock. The existing
arda-collision-guard conventions continue to protect git-level races.

## 5. Attempt ledger & no-repeat

`attempts.jsonl` per campaign, reusing the bridge's `AttemptLedger`
record shape (`telperion.prove2me.ledger`): node slug, session, route
tried (emitter name, tactic approach, or `reduction`), verdict
(`Proved | Refuted | NoGo | Stalled`), detail, date. `NoGo` carries the
refutation reason so no session re-walks a dead path — the scattered
`*_nogo*.py` convention as queryable data. The math-level `RouteLedger`
(`telperion.ledger`) is untouched: it records proof-route *mathematics*
(which certificates fail and why); attempts record *work history*. The
per-node CLI view renders both.

## 6. CLI, queries, and MCP surface

`telperion mission …` (argparse subtree, same idiom as `p2m`):

| Verb | Does |
|---|---|
| `status [campaign]` | one-glance tree with statuses — the generated successor of PROOF_STATUS.md's tables |
| `open-leaves [campaign]` | the live frontier: open nodes all of whose dependencies are proved (or which have none), minus fresh claims; `--all` includes claimed |
| `claim <slug> --session S [--ttl H]` / `release <slug>` | claim protocol (§4) |
| `add <campaign> <name>` | scaffold node file + statement file (status `draft`) |
| `audit <slug>` | record a read-back (§8): `--text` + `--auditor`, or emit the statement for an independent session to render |
| `link <slug> --artifact PATH --kind K --via V` | attach a proof/disproof artifact; verification happens in `verify`/CI, never here |
| `attempt <slug> --route R --verdict V --detail D` | ledger append |
| `verify [campaign]` | run every CI invariant (§7) locally |
| `graph [campaign]` | DOT export of the dependency DAG with statuses |

Two read-only MCP tools in the existing server: `mission_status`,
`mission_open_leaves`. No daemon; every verb is a file read/write.

## 7. CI invariants (and `mission verify`)

One new CI job, identical to local `mission verify`:

1. Every node/mission/claim file parses and validates against the schema.
2. The dependency graph is acyclic; `depends_on` targets exist.
3. Each campaign statement package `lake build`s green.
4. Status coherence: every `proved`/`refuted` node's artifact exists,
   kernel-checks in its home package, and matches the registry statement
   (normalized comparison; negation for `refuted`); every reduction's
   `closure_clean` flag is recomputed, never trusted.
5. Statement files carry current provenance headers (regeneration diff
   is empty).
6. Claims hygiene (warnings): TTL, claimed-but-not-open.
7. Ledgers parse; every `deprecated` node has a reason.

Failure is loud. The one-glance `status` output is generated from the
same data CI validated, so the display cannot drift from the truth.

## 8. Read-back audits

Before `draft → open`, a node needs a recorded read-back: an independent
natural-language rendering of what the formal statement actually says,
stored in the node file (`readback.text/auditor/date`). The renderer must
not be the statement's author (an independent session, or the operator).
Where both sides are Lean (statement vs. a source formalization), the
comparator machinery does the matching mechanically; for
statement-vs-paper the read-back is prose. This is the gate that catches
"formalized the wrong statement" before proof effort is spent — the
discipline Prove2Me's captain docs identify as the single most important
thing, internalized as a hard transition requirement.

## 9. Migration: BG and RH

Machinery ships first; migrations are separate plan tasks.

**BG** (`missions/bg/`, env = `proof/` island v4.32.0): PROOF_ASSEMBLY.md
strata become nodes. PROVEN entries (Φ ≤ 1 hinge, merge layer,
capped-joint g-step closure, near-star spine, …) link their existing
`proof/` Lean modules and must earn `proved` through the real gate — a
genuine re-audit of our own claims, not a rubber stamp. OPEN entries
(the master inequality, R2 multi-hub maximality) become the first open
leaves. The Hnorm refutation (2026-09-11, `R47HnormFalse52` line of work)
becomes the first `refuted` node. Existing prose docs gain pointers; the
registry is henceforth the tracking truth.

**RH** (`missions/rh/`, env = v4.34 island): zero-free ladder and Li
ladder proved-nodes link their merged artifacts; the drafted
Borel–Carathéodory theorem becomes a flagship open leaf; the dVP +
zeta_log_bound cascade (freshly unified onto v4.34 by #483) nodes link
accordingly.

Migration fidelity rule: a claim in the prose docs that cannot pass the
§7 gate migrates as `open` (or `draft`), never as `proved` — discrepancies
are findings, and surfacing them is a feature of the migration.

## 10. Testing

Pure pytest, fully offline: schema and status-machine unit tests; a
golden fixture campaign under `telperion/tests/fixtures/missions/`
exercising every transition (including the comparator gate rejecting a
mismatched artifact and a reduction flipping `closure_clean`); CLI tests
via `main([...])`; DOT export smoke. Statement-package `lake build` and
artifact checks are CI-tier (like every other Lean gate in the repo),
with the golden fixture using a stub verifier in unit tests.

## Relationship to the paused solver bridge (PR #481)

The bridge is paused, not deleted. Its `ledger.py` record shape is reused
here verbatim; its triage/registry-enumeration machinery is untouched and
orthogonal. If the operator ever resumes it, prove2.me becomes just
another place a mission's open leaves could be *exported to* — the
internal registry remains the master. That direction of data flow is the
structural form of "no external service controls our work."

## Risks

- **Migration overclaiming**: the §9 fidelity rule plus the real §7 gate
  make the registry strictly more honest than the prose it replaces; the
  cost is that migration may downgrade some prose "PROVEN" labels until
  artifacts are properly linked — that is intended behavior.
- **Claim staleness across crashed sessions**: TTL + claim-over handles
  it; worst case a leaf is hidden from `open-leaves` for `ttl_hours`.
- **Environment drift** (islands moving, as #483 just did): environments
  are per-campaign data, not code constants; moving a campaign to a new
  island is a one-line manifest change plus a statement-package re-pin,
  gated by CI.
- **Two sources of truth during transition**: prose docs vs registry.
  Mitigated by generating PROOF_STATUS.md's summary tables from the
  registry once migration lands, and by dating the prose docs as
  narrative-only from that commit forward.
