# Telperion Missions Registry Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build the internal, self-hosted campaign registry (Prove2Me's architecture absorbed into Telperion): per-node files + git substrate, kernel-gated status machine, per-campaign statement packages, claims, attempt ledger, read-back audits, CLI/MCP surface — then migrate the BG and RH campaigns into it.

**Architecture:** A `telperion.missions` subpackage of small focused modules (schema / registry / claims / attempts / statements / verify), driven by a `telperion mission …` CLI subtree and validated by one invariant battery that runs identically in CI and locally. All state is files in `telperion/missions/<campaign>/`; statuses `proved`/`refuted` are grantable only by the verify gate.

**Tech Stack:** Python stdlib only (tomllib where available + a closed-loop mini-TOML fallback reader; hand-rolled deterministic TOML writer), pytest, existing argparse/FastMCP idioms. Lean statement packages pin per-campaign toolchain islands.

**Spec:** `telperion/docs/MISSIONS_DESIGN_2026-09-11.md` (read it first — this plan implements it section by section).

## Global Constraints

- **No new runtime dependencies.** `pyproject.toml` dependencies stay `["sympy>=1.12"]`. TOML: read via `import tomllib` (function-local, repo convention per `status.py:22`) with fallback to the in-module mini reader; write via the in-module deterministic emitter.
- **Statuses exactly**: `draft | open | proved | refuted | deprecated`. `proved`/`refuted` set ONLY by `verify`-gated code paths — the CLI `link` verb never writes those statuses directly.
- **One file per node**; claim = add file; attempt = append jsonl line; deterministic serialization (sorted keys) for stable diffs.
- **Environments are per-campaign data** in `mission.toml`, never code constants. BG env: `leanprover/lean4:v4.32.0` + the mathlib rev used by `proof/formalization`. RH env: `leanprover/lean4:v4.34.0-rc1` + the mathlib rev used by `telperion/examples/li_positivity/lean`.
- **The bridge (`telperion.prove2me`) is NOT on this branch** (PR #481 unmerged): do not import from it. `missions/attempts.py` reimplements the same record shape standalone.
- **Honest reduction rule**: `closure_clean` is recomputed, never trusted; a reduction-proved node with an unclean closure must display as conditional.
- Commit style: `feat(missions): …` / `test(missions): …` / `docs(missions): …`, trailers per session convention.
- Tests: run from `telperion/`: `python3 -m pytest tests/test_missions_*.py -v`. Tests never invoke `lake` and never touch the network; Lean builds are CI/migration-tier.
- Dates in files are ISO strings; no floats anywhere in schema.

## File Structure

```
telperion/src/telperion/missions/
├── __init__.py       # public re-exports
├── schema.py         # dataclasses, statuses, TOML read/write, per-file validation
├── registry.py       # Campaign load, DAG checks, open_leaves, transitions, status render, DOT
├── claims.py         # claim/release/TTL/claim-over
├── attempts.py       # append-only jsonl work ledger (standalone; bridge-shape-compatible)
├── statements.py     # Lean statement file generation, provenance header, regen diff, package scaffold
└── verify.py         # the invariant battery (spec §7) + statement normalization/matching
telperion/src/telperion/cli.py        # + mission subtree
telperion/src/telperion/mcp_server.py # + mission_status / mission_open_leaves
telperion/missions/bg/ , telperion/missions/rh/   # created by migration tasks 9-10
telperion/tests/test_missions_{schema,registry,claims,attempts,statements,verify,cli}.py
telperion/tests/fixtures/missions/demo/           # golden fixture campaign
```

All commands below run from `telperion/` inside the repo unless stated.

---

### Task 1: `schema.py` — dataclasses, statuses, TOML I/O, validation

**Files:**
- Create: `src/telperion/missions/__init__.py`, `src/telperion/missions/schema.py`
- Test: `tests/test_missions_schema.py`

**Interfaces:**
- Produces (every later task consumes):
  - `STATUSES = ("draft", "open", "proved", "refuted", "deprecated")`
  - `KINDS = ("goal", "milestone", "lemma", "definition")`
  - `@dataclass Proof(artifact: str, artifact_kind: str, via: str, closure_clean: bool = False)` — `artifact_kind in ("lean_module", "frozen_cert")`, `via in ("direct", "reduction")`
  - `@dataclass Readback(text: str, auditor: str, date: str)`
  - `@dataclass Node(name: str, title: str, kind: str, status: str, depends_on: tuple[str, ...], statement_module: str, source: str = "", proof: Proof | None = None, readback: Readback | None = None, refutation_statement: str = "", deprecated_reason: str = "", created: str = "", updated: str = "")`
  - `@dataclass MissionManifest(name: str, title: str, description: str, goal_node: str, environment_toolchain: str, environment_mathlib_rev: str, sources: tuple[str, ...] = ())`
  - `@dataclass Claim(node: str, session: str, started: str, ttl_hours: int = 24, note: str = "", superseded: str = "")`
  - `slug_of(name: str) -> str` (Lean name, `.` → `_`)
  - `loads_toml(text: str) -> dict` / `dumps_toml(doc: dict) -> str` (round-trip closed loop)
  - `load_node(path) -> Node`, `save_node(node, path)`, same pairs for manifest and claim
  - `SchemaError(Exception)` with the offending path + field in the message

- [ ] **Step 1: Write the failing tests** (`tests/test_missions_schema.py`):

```python
"""Schema round-trip, validation, and the closed-loop TOML fallback."""
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from telperion.missions.schema import (  # noqa: E402
    Claim, MissionManifest, Node, Proof, Readback, SchemaError,
    dumps_toml, load_node, loads_toml, save_node, slug_of,
)


def node(**kw):
    base = dict(name="BG.master_inequality", title="Master inequality",
                kind="milestone", status="draft", depends_on=("BG_g_step",),
                statement_module="Statements.BG_master_inequality",
                created="2026-09-11", updated="2026-09-11")
    base.update(kw)
    return Node(**base)


def test_slug_of_replaces_dots():
    assert slug_of("BG.master_inequality") == "BG_master_inequality"


def test_node_roundtrip_via_files(tmp_path):
    n = node(proof=Proof("proof/formalization/PotentialFinal.lean",
                         "lean_module", "direct", True),
             readback=Readback("says phi <= 1 on branches", "operator", "2026-09-11"))
    p = tmp_path / "n.toml"
    save_node(n, p)
    assert load_node(p) == n


def test_toml_dump_is_deterministic_and_sorted(tmp_path):
    n1, n2 = node(), node()
    assert dumps_toml(loads_toml(dumps_toml({"b": 1, "a": ["x", "y"]}))) == \
           dumps_toml({"a": ["x", "y"], "b": 1})
    p1, p2 = tmp_path / "a.toml", tmp_path / "b.toml"
    save_node(n1, p1); save_node(n2, p2)
    assert p1.read_text() == p2.read_text()


def test_mini_reader_parses_what_writer_emits():
    doc = {"name": "X.y", "n": 3, "flag": True, "deps": ["a", "b"],
           "proof": {"artifact": "p.lean", "closure_clean": False}}
    assert loads_toml(dumps_toml(doc)) == doc


def test_invalid_status_raises(tmp_path):
    with pytest.raises(SchemaError, match="status"):
        node(status="pending")


def test_deprecated_requires_reason():
    with pytest.raises(SchemaError, match="deprecated_reason"):
        node(status="deprecated")
    node(status="deprecated", deprecated_reason="superseded by BG.v2")  # ok


def test_proved_requires_proof():
    with pytest.raises(SchemaError, match="proof"):
        node(status="proved")
```

- [ ] **Step 2: Run to verify failure.** `python3 -m pytest tests/test_missions_schema.py -v` — Expected: FAIL, `ModuleNotFoundError: telperion.missions`.

- [ ] **Step 3: Implement.** `__init__.py` re-exports the schema names. `schema.py` core (validation runs in `__post_init__`; dataclasses are frozen):

```python
"""Missions registry schema: one small file per node/manifest/claim.

TOML I/O is a CLOSED LOOP: `dumps_toml` emits a restricted, deterministic
subset (sorted keys; str/int/bool, lists of strings, one level of nested
tables), and `loads_toml` reads via stdlib tomllib when available (Python
3.11+, the CI environment — repo convention, see status.py) with an
in-module fallback parser that accepts exactly what `dumps_toml` emits.
Round-trip is tested; hand-written files are read by tomllib in CI.
"""
from __future__ import annotations

from dataclasses import dataclass, field, asdict
from pathlib import Path

STATUSES = ("draft", "open", "proved", "refuted", "deprecated")
KINDS = ("goal", "milestone", "lemma", "definition")
ARTIFACT_KINDS = ("lean_module", "frozen_cert")
VIAS = ("direct", "reduction")


class SchemaError(Exception):
    """A mission file violates the schema; message names path/field."""


def slug_of(name: str) -> str:
    return name.replace(".", "_")


def dumps_toml(doc: dict) -> str:
    def scalar(v):
        if isinstance(v, bool):
            return "true" if v else "false"
        if isinstance(v, int):
            return str(v)
        if isinstance(v, str):
            return '"' + v.replace("\\", "\\\\").replace('"', '\\"') + '"'
        raise SchemaError(f"unsupported TOML scalar: {type(v).__name__}")

    lines, tables = [], []
    for k in sorted(doc):
        v = doc[k]
        if isinstance(v, dict):
            tables.append((k, v))
        elif isinstance(v, (list, tuple)):
            lines.append(f"{k} = [" + ", ".join(scalar(x) for x in v) + "]")
        else:
            lines.append(f"{k} = {scalar(v)}")
    for name, tbl in tables:
        lines.append("")
        lines.append(f"[{name}]")
        for k in sorted(tbl):
            v = tbl[k]
            if isinstance(v, (list, tuple)):
                lines.append(f"{k} = [" + ", ".join(scalar(x) for x in v) + "]")
            else:
                lines.append(f"{k} = {scalar(v)}")
    return "\n".join(lines) + "\n"


def loads_toml(text: str) -> dict:
    try:
        import tomllib
        return tomllib.loads(text)
    except ModuleNotFoundError:
        return _mini_parse(text)


def _mini_parse(text: str) -> dict:
    """Parse exactly the subset dumps_toml emits (fallback for Python < 3.11)."""
    import ast
    doc: dict = {}
    target = doc
    for raw in text.splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("[") and line.endswith("]"):
            target = doc.setdefault(line[1:-1], {})
            continue
        key, _, val = line.partition(" = ")
        val = val.strip()
        if val in ("true", "false"):
            target[key] = val == "true"
        elif val.startswith("["):
            target[key] = list(ast.literal_eval(val))
        elif val.startswith('"'):
            target[key] = ast.literal_eval(val)
        else:
            target[key] = int(val)
    return doc
```

then the dataclasses (frozen, `__post_init__` validation: status/kind/artifact_kind/via membership; `deprecated` ⇒ nonempty `deprecated_reason`; `proved`/`refuted` ⇒ `proof is not None`; tuple coercion for list fields) and `load_node/save_node/load_manifest/save_manifest/load_claim/save_claim` (nested `Proof`/`Readback` map to `[proof]`/`[readback]` tables; `None` fields omitted on save, absent tables load as `None`; `SchemaError` wraps failures with the file path).

- [ ] **Step 4: Run to verify pass.** All PASS.
- [ ] **Step 5: Commit.** `git add src/telperion/missions tests/test_missions_schema.py && git commit -m "feat(missions): schema, statuses, deterministic TOML I/O"`

---

### Task 2: `registry.py` — campaign load, DAG, open leaves, transitions, renders

**Files:**
- Create: `src/telperion/missions/registry.py`
- Test: `tests/test_missions_registry.py`
- Create: `tests/fixtures/missions/demo/` (mission.toml + 4 node files, written in Step 1)

**Interfaces:**
- Consumes: Task 1 schema.
- Produces:
  - `@dataclass Campaign(root: Path, manifest: MissionManifest, nodes: dict[str, Node])` (keyed by slug)
  - `load_campaign(root: Path) -> Campaign` (raises `SchemaError` on unknown `depends_on` targets or duplicate names)
  - `assert_acyclic(campaign) -> None` (raises `SchemaError` naming a cycle)
  - `open_leaves(campaign, claims: dict[str, Claim] | None = None, include_claimed: bool = False) -> list[Node]` — open nodes whose every dependency is `proved`; fresh claims excluded unless `include_claimed`
  - `promote_to_open(campaign, slug) -> Node` — the ONLY draft→open path; raises unless a readback is recorded
  - `deprecate(campaign, slug, reason) -> Node`
  - `set_proof(campaign, slug, proof: Proof) -> Node` — records the link but forces status to stay non-proved (status flip is verify's job, Task 6)
  - `render_status(campaign, claims=None) -> str` (one-glance tree), `render_dot(campaign) -> str`
  - All mutators save the node file and bump `updated`.

- [ ] **Step 1: Write the demo fixture + failing tests.** Fixture: `demo/mission.toml` (goal `Demo.goal`, env toolchain `leanprover/lean4:v4.32.0`, rev `v4.32.0`) and nodes `Demo_goal` (goal, draft, depends_on Demo_lemma_a+Demo_lemma_b), `Demo_lemma_a` (open, readback recorded), `Demo_lemma_b` (draft), `Demo_dead` (deprecated with reason). Tests:

```python
def test_load_campaign_and_unknown_dep_raises(tmp_path): ...
    # copy fixture, load, assert 4 nodes; then write a node with
    # depends_on=("Nope",) and assert SchemaError names it

def test_assert_acyclic_detects_cycle(tmp_path): ...
    # a -> b -> a via edited fixture copies; SchemaError message contains both slugs

def test_open_leaves_requires_deps_proved(): ...
    # lemma_a open with no deps -> IS a leaf; goal draft -> not;
    # after lemma_a proved + goal opened, goal is a leaf only when b proved too

def test_promote_to_open_requires_readback(): ...
    # Demo_lemma_b (draft, no readback) -> raises; after readback recorded -> open

def test_set_proof_never_sets_proved(): ...
    # set_proof on open node leaves status "open", proof recorded

def test_render_status_contains_tree_and_statuses(): ...
    # output has campaign title, one line per node, status glyphs
```

(Write them as real executable tests against the fixture copied into `tmp_path` — `shutil.copytree`; each ellipsis above is filled in with the 3-6 line body implied by its comment.)

- [ ] **Step 2: Run to verify failure.** `ModuleNotFoundError`/`ImportError`.
- [ ] **Step 3: Implement** `registry.py` (~150 lines): load = read `mission.toml` + every `nodes/*.toml`; DAG check by DFS with an explicit stack; `open_leaves` per the interface; mutators load-modify-save with `updated = date.today().isoformat()`; renders are pure string builders (status glyphs: `draft ·  open ○  proved ✓  refuted ✗  deprecated †` — plus `(reduction, closure_clean=false)` annotation when applicable; note: glyphs in generated OUTPUT strings are fine, they never enter QuantConnect).
- [ ] **Step 4: Run to verify pass.**
- [ ] **Step 5: Commit.** `feat(missions): campaign registry, DAG, open-leaves, renders`

---

### Task 3: `claims.py` — claim / release / TTL / claim-over

**Files:**
- Create: `src/telperion/missions/claims.py`
- Test: `tests/test_missions_claims.py`

**Interfaces:**
- Consumes: schema `Claim`, registry `Campaign`/`open_leaves`.
- Produces:
  - `load_claims(root: Path) -> dict[str, Claim]` (keyed by node slug; `claims/*.toml`)
  - `claim(root, slug, session, ttl_hours=24, note="", _now=None) -> Claim` — raises `ClaimError` if node unclaimed-able (already freshly claimed by another session) or not `open`; a STALE claim (age > ttl) is claimed-over: new claim records `superseded=<old session>`
  - `release(root, slug, session) -> None` — only the claiming session (or a claim-over) removes it
  - `is_stale(claim, _now=None) -> bool`
  - `ClaimError(Exception)`

- [ ] **Step 1: Failing tests** — five: fresh claim written as file; second session claiming fresh raises `ClaimError`; stale claim (started 2 days ago, ttl 24h) is claimed-over with `superseded` recorded; release by owner deletes file; release by stranger raises. Time injection via `_now` (a `datetime`), never wall-clock sleeps.
- [ ] **Step 2: Verify failure.**  - [ ] **Step 3: Implement** (~70 lines; ISO parse with `datetime.fromisoformat`).
- [ ] **Step 4: Verify pass.**  - [ ] **Step 5: Commit.** `feat(missions): advisory claims with TTL and claim-over`

---

### Task 4: `attempts.py` — append-only work ledger

**Files:**
- Create: `src/telperion/missions/attempts.py`
- Test: `tests/test_missions_attempts.py`

**Interfaces:**
- Consumes: nothing (standalone; deliberately bridge-shape-compatible, but the bridge is unmerged — do NOT import `telperion.prove2me`).
- Produces:
  - `@dataclass(frozen=True) Attempt(node: str, session: str, route: str, verdict: str, detail: str, date: str)` — verdict in `("Proved", "Refuted", "NoGo", "Stalled")`
  - `AttemptLog(path)` with `.append(a)`, `.records() -> list[Attempt]`, `.for_node(slug) -> list[Attempt]`, `.nogo_digest(slug) -> str` (rendered no-repeat block), corrupt-trailing-line tolerance (skip + policy comment, same as the bridge's ledger)

- [ ] **Step 1: Failing tests** — round-trip; for_node filter; nogo_digest contains NoGo details and omits Stalled; truncated trailing line skipped (two valid records survive).
- [ ] **Step 2-5:** fail → implement (~60 lines) → pass → commit `feat(missions): attempt ledger with no-repeat digest`.

---

### Task 5: `statements.py` — statement files, provenance, package scaffold

**Files:**
- Create: `src/telperion/missions/statements.py`
- Test: `tests/test_missions_statements.py`

**Interfaces:**
- Consumes: schema, registry.
- Produces:
  - `statement_path(root, node) -> Path` = `root/lean/Statements/<Slug>.lean`
  - `render_statement(node, statement: str, manifest) -> str` — the file content: provenance header (`-- DO NOT EDIT BY HAND — generated by telperion mission; node <slug>; sha256 <input-hash>`), `import`/`open` lines passed through from the statement text, the statement ending `:= by sorry` (normalized: if the given statement lacks a body, append it)
  - `write_statement(root, node, statement, manifest) -> Path`
  - `regen_diff(root, node, manifest) -> str` — "" when the on-disk file matches regeneration (input-hash check, same discipline as emitted certs)
  - `scaffold_package(root, manifest) -> list[Path]` — writes `lean/lean-toolchain` (= `manifest.environment_toolchain`), `lean/lakefile.toml` (mathlib rev = `manifest.environment_mathlib_rev`, lib name `Statements`), `lean/Statements.lean` root importing every statement module
  - Statement text lives in the node's own `.lean` file only (single source); the node file stores just `statement_module`.

- [ ] **Step 1: Failing tests** — render contains header + hash + `:= by sorry`; write→regen_diff == ""; hand-edit the file → regen_diff nonempty naming the node; scaffold writes toolchain/lakefile with the manifest's env verbatim; root module imports all statements sorted.
- [ ] **Step 2-5:** fail → implement (~110 lines) → pass → commit `feat(missions): statement files with provenance + env-pinned package scaffold`.

---

### Task 6: `verify.py` — the invariant battery (the kernel gate's bookkeeping half)

**Files:**
- Create: `src/telperion/missions/verify.py`
- Test: `tests/test_missions_verify.py`

**Interfaces:**
- Consumes: everything above.
- Produces:
  - `normalize_lean(text: str) -> str` — strip `--`/`/- -/` comments, collapse whitespace, drop a trailing `:= by sorry`/`:= sorry`
  - `statement_matches(artifact_text: str, node_statement: str) -> bool` — normalized containment (the artifact contains the node's normalized statement)
  - `refutation_matches(artifact_text, node) -> bool` — uses `node.refutation_statement` when set (normalized containment), else requires `¬` + the normalized proposition
  - `recompute_closures(campaign) -> dict[str, bool]` — fixpoint: a reduction node's closure is clean iff every dependency is `proved` AND its own closure is clean (direct-proved nodes are clean by definition); WRITES the recomputed flags back to node files
  - `verify_campaign(root: Path, deep_lean: bool = False) -> VerifyReport` — dataclass with `errors: list[str]`, `warnings: list[str]`, `ok: bool`; runs spec §7 items 1,2,4,5,6,7 (schema, DAG, status coherence incl. artifact-file existence + statement/refutation match + closure recompute + provenance regen empty + claims hygiene as warnings + ledger parse + deprecated reasons). `deep_lean=True` additionally runs `lake build` on the statement package (migration/CI tier; never in unit tests — inject `runner`)
  - **The gate**: `grant_status(campaign, slug) -> Node` — the ONLY code path that sets `proved`/`refuted`: re-runs the coherence checks for that node and flips status accordingly; raises `GateError` on any mismatch

- [ ] **Step 1: Failing tests** (the heart of the system — be thorough):

```python
def test_gate_grants_proved_on_matching_artifact(tmp_path): ...
    # artifact file containing the node statement verbatim-modulo-comments
    # -> grant_status flips open->proved
def test_gate_rejects_mismatched_statement(tmp_path): ...
    # artifact proves a DIFFERENT statement -> GateError, status stays open
def test_gate_refuted_via_refutation_statement(tmp_path): ...
def test_closure_fixpoint(tmp_path): ...
    # A reduction-proved via children B,C; B proved direct, C open
    # -> closure_clean False; after C proved -> recompute flips True
def test_verify_report_flags_missing_artifact_and_stale_claims(tmp_path): ...
def test_normalize_strips_comments_and_sorry(): ...
```

(each body 5-12 lines against fixture copies; artifact files are plain `.lean` text files in tmp_path — no lake anywhere.)

- [ ] **Step 2-5:** fail → implement (~180 lines) → pass → commit `feat(missions): invariant battery and the proved/refuted gate`.

---

### Task 7: CLI subtree `telperion mission …`

**Files:**
- Modify: `src/telperion/cli.py` (follow the existing `sub.add_parser`/`set_defaults(fn=…)` idiom; imports inside functions)
- Test: `tests/test_missions_cli.py`

**Interfaces:**
- Consumes: all Task 1-6 interfaces exactly as named.
- Produces verbs: `status [CAMPAIGN]`, `open-leaves [CAMPAIGN] [--all]`, `claim SLUG --session S [--ttl H] [--note N]`, `release SLUG --session S`, `add CAMPAIGN NAME --title T --kind K [--deps a,b] --statement-file F|--statement TEXT`, `audit SLUG --text T --auditor A`, `link SLUG --artifact P --kind K --via V`, `attempt SLUG --session S --route R --verdict V --detail D`, `verify [CAMPAIGN] [--deep-lean]`, `grant SLUG` (runs the Task-6 gate), `graph [CAMPAIGN]`. Root option `--missions-root` (default `telperion/missions` resolved from repo root; tests pass tmp roots).
- Campaign discovery: subdirectories of the missions root containing `mission.toml`.

- [ ] **Step 1: Failing tests** — using a tmp copy of the demo fixture: `status` exit 0 + node lines; `open-leaves` lists `Demo_lemma_a` only; `claim`+`open-leaves` hides it, `--all` shows; `add` creates node+statement files (draft); `audit` records readback then `open-leaves` unaffected until promote… (promotion happens inside `audit`? No — `audit` records; `add`→`audit`→auto-promote? Per spec §3 readback recording IS the draft→open trigger: make `audit` record AND promote via `promote_to_open`); `link` records proof but status stays open; `grant` flips to proved when artifact matches (artifact = tmp .lean containing the statement); `verify` exit 0 on clean fixture, exit 1 with an injected mismatch.
- [ ] **Step 2-5:** fail → implement (~180 lines of cmd_ functions + parser wiring) → pass, plus `python3 -m pytest tests/ -k missions -v` all green → commit `feat(missions): telperion mission CLI subtree`.

---

### Task 8: MCP tools + fixture consolidation + docs stub

**Files:**
- Modify: `src/telperion/mcp_server.py` (+2 tools, `_cli` delegation idiom)
- Create: `docs/MISSIONS_HOWTO.md` (one page: the verbs, the status machine, the claim protocol, for future sessions)
- Test: `tests/test_missions_mcp.py` (importorskip("mcp"), assert the two functions exist — same pattern as `test_prove2me_mcp.py` on the bridge branch, reimplemented here)

- [ ] **Step 1:** tools:

```python
@mcp.tool()
def mission_status(campaign: str = "") -> str:
    """One-glance status tree of an internal mission campaign (all campaigns
    when empty): node statuses, reductions' closure_clean, claims."""
    args = ["mission", "status"] + ([campaign] if campaign else [])
    code, out = _cli(args)
    return out.strip() or f"exit {code}"


@mcp.tool()
def mission_open_leaves(campaign: str = "", include_claimed: bool = False) -> str:
    """The live frontier: open nodes whose dependencies are all proved,
    minus freshly-claimed ones (include_claimed=True shows those too)."""
    args = ["mission", "open-leaves"] + ([campaign] if campaign else [])
    if include_claimed:
        args.append("--all")
    code, out = _cli(args)
    return out.strip() or f"exit {code}"
```

- [ ] **Step 2:** HOWTO doc (~80 lines, written fresh from the spec's §3-§6 — statuses, gate rule, claim etiquette, verbs table).
- [ ] **Step 3:** run `python3 -m pytest tests/ -k missions -v`; commit `feat(missions): MCP frontier tools + HOWTO`.

---

### Task 9: BG migration

**Files:**
- Create: `telperion/missions/bg/mission.toml`, `nodes/*.toml`, `lean/` (scaffolded), statement files
- Modify: `PROOF_STATUS.md` (add a generated-summary marker section + pointer)

**Procedure (judgment-heavy; the sources are the prose docs):**

- [ ] **Step 1: Author the manifest.** Env: toolchain `leanprover/lean4:v4.32.0`; mathlib rev = read it from `proof/formalization/lakefile.toml` (the `rev =` line) and copy verbatim. Goal node `BG.conjecture1` (kind goal, status draft — it is NOT proved; the registry must say so).
- [ ] **Step 2: Author nodes from `telperion/PROOF_ASSEMBLY.md` + `STATUS.md`.** Minimum node set (names indicative — read the docs and use the real Lean names where modules exist): the Φ≤1 hinge (`phi_le_one`, proved, artifact `proof/formalization/...PotentialFinal.lean`), H1 bridge/matching, merge layer, (L)/(B) classification, R5/R6 shedding, capped-joint g-step closure (`gstep_le_one_achievable`), near-star spine, R2 double-near-star family bound — each PROVEN-in-prose entry gets `link` + `grant`; the master inequality and R2 maximality as `open` after read-back; the Hnorm refutation as `refuted` with `refutation_statement` set and its kernel artifact linked (from the 2026-09-11 `bg/multihub-hnorm` work — locate the committed Lean file via `git log --all --oneline --grep=Hnorm` and the memory's `R47HnormFalse52` name).
- [ ] **Step 3: Read-backs.** Every node gets a readback (auditor: this session, text = one-sentence independent rendering checked against the prose doc's own description — where they disagree, STOP and flag).
- [ ] **Step 4: The honesty pass.** `telperion mission verify bg --deep-lean` (this builds the BG statement package — first real lake run). Apply the migration fidelity rule: any prose-PROVEN node whose artifact fails `grant` stays `open` and gets an `attempt` ledger entry `NoGo: migration gate mismatch — <detail>`. **Report every downgrade prominently — they are findings.**
- [ ] **Step 5: Generated summary.** Add to `PROOF_STATUS.md` a marked block (`<!-- missions:bg:begin -->` … `end`) containing `telperion mission status bg` output and a note that the registry is now the tracking truth.
- [ ] **Step 6: Commit** `feat(missions): BG campaign migrated to the registry` (+ separate commit if downgrades required doc corrections).

---

### Task 10: RH migration

Same procedure as Task 9 with: env toolchain `leanprover/lean4:v4.34.0-rc1`, mathlib rev from `telperion/examples/li_positivity/lean/lakefile.toml`; sources = the RH prose docs (`telperion/docs/RH_*` handoffs, `STATUS.md` RH section). Minimum nodes: zero-free region ladder (γ⁻⁵ then polylog, proved w/ artifacts), zeta log bound (proved), Li ladder rungs summary node (proved, artifact from the merged #411 work), dVP + zeta_log_bound v4.34 unification nodes (from #483), Borel–Carathéodory theorem (open — flagship leaf), `RH.conjecture` goal node (draft/open, obviously unproved). Honesty pass + generated summary block + commit `feat(missions): RH campaign migrated to the registry`.

---

## Self-Review Notes

- **Spec coverage:** §1 schema/layout (T1,T2), §2 statement packages+env (T5, envs exercised in T9/T10), §3 status machine+gate+honest reductions (T2 transitions, T6 gate+closure fixpoint), §4 claims (T3), §5 attempts (T4), §6 CLI+MCP (T7,T8), §7 invariants (T6, CI wiring rides the existing test job since `verify` is pytest-covered; a dedicated CI job invocation is added in T9 alongside the first real campaign), §8 read-backs (T2 promote gate + T7 audit verb), §9 migrations (T9,T10 with the fidelity rule verbatim), §10 testing (every task TDD; fixture campaign in T2).
- **Bridge non-dependency:** T4 explicitly reimplements the ledger shape; nothing imports `telperion.prove2me` (unmerged on this branch).
- **Known judgment areas, named:** T9/T10 node sets are indicative — the implementer reads the prose docs and uses real module/lemma names; disagreements between prose and gate results are REPORTED, not smoothed over. T7 makes `audit` the draft→open trigger (spec §3's "read-back recorded" transition) — single verb, no separate promote command.
- **Type consistency check:** `Claim.node`/slug keying, `Proof` field names, and `verify.grant_status` naming are used identically in T1/T2/T3/T6/T7.

---

## Post-review tickets (2026-09-12)

- **deep-lean statement-package CI workflow:** Wire `mission verify --deep-lean` into GitHub Actions as a required job on the campaigns that have Lean statement packages (BG, RH). The job should lake-build each campaign's `lean/` statement package and fail the workflow on any elaboration error. This closes the gap between the shallow gate (syntactic containment) and real Lean kernel authority for the statements themselves.

- **`Proof.environment` field for durable cross-island closure semantics:** Add an optional `environment` field to the `Proof` schema (e.g. `environment = "zero_free_bridge/v4.32"`) that names the Lean island and toolchain revision where the artifact was kernel-checked. `recompute_closures` and `verify_campaign` should surface this when `closure_clean = false` on a direct-proved node, so the registry explains *why* the flag is false rather than leaving it implicit in the readback prose. This enables future automation to re-derive `closure_clean` once cross-island CI wiring is in place.

- **`AttemptLog` corrupt-line counting surfaced as verify warning:** `verify_campaign` currently raises an error if `log.records()` throws, which is appropriate for total parse failure. Add partial fault tolerance: count lines that fail JSON parsing individually (skip them), and surface the count as a `warnings` entry rather than an `errors` entry when the ledger is mostly readable. A fully unreadable ledger remains an error.

- **`BGDefs`/`RHDefs` drift check wiring into verify/CI:** The campaigns' Lean statement packages import from `BGDefs`/`RHDefs` definition modules. If those modules drift from the node statement files (e.g. a constant is renamed), `regen_diff` will catch statement-file drift but not definition-file drift. Add a `verify_campaign` check (or a separate `verify --check-defs` flag) that imports the campaign's `Defs` module and confirms that every `proved`/`open` node's statement file can be elaborated against the current `Defs` — catching drift before it blocks a `--deep-lean` lake build.
