# Prove2Me Solver Bridge — Design (2026-09-11)

Status: APPROVED design, pre-implementation.
Branch: `feat/prove2me-bridge`. Base: `main` @ `e821902`.

## Context

[Prove2Me](https://prove2.me) (Chen, Marwaha, Lu, Yuen, Peng — Columbia;
arXiv:2608.28433) is an open collaborative platform for Lean 4
formalization: captains post *missions* (a root theorem plus curated
*milestones* with authoritative formal statements), solvers connect AI
agents that submit proofs, and the Lean kernel is the sole admission
gate. Verified results enter a public reusable library; contributors
get permanent public credit and a trust score. It is the harness behind
Anthropic's Fermat's Last Theorem formalization.

Telperion and Prove2Me independently converged on the same trust model
— an untrusted generator behind a kernel gate ("a defective certificate
is a compile error, never a false theorem" / "a wrong proof cannot
enter the library"). This project connects them: Telperion becomes a
solver backend for Prove2Me, targeting exactly the milestones where a
certificate engine beats tactic-grinding LLM provers — inequalities,
identities, enclosures, valuations, finite dispatch, Positivstellensatz
shapes. As of this writing Telperion has **136 emitter modules / 133
emitter classes**, all subclassing `workflow.Emitter` and all forced by
CI (`emitter_sensitivity.py`) to declare their certificate stance.

This is sub-project B of a two-part program. Sub-project A (an internal
Prove2Me-inspired mission registry / verified library / multi-session
harness for our own campaigns) is deliberately deferred and will be
designed after this bridge produces firsthand operational experience
with Prove2Me's architecture.

## Decisions already made

| Decision | Choice |
|---|---|
| Direction order | Solver bridge (B) first; internal platform (A) after |
| Autonomy | **Fully autonomous**, including submissions; hard local-verify gate before any `POST /verify` |
| Machinery placement | Real code (`src/telperion/prove2me/`) + CLI + MCP + a `prove2me-solver` claude-plugin skill |
| Selection doctrine | **Certificate-first triage**: attempt only milestones scored as matching an emitter shape |
| Phase 2 (out of scope now) | Headless daemon loop; captain tooling; sub-project A |

## Goals

1. Autonomously discover, triage, prove, and submit Prove2Me milestones
   whose formal statements fit a Telperion certificate shape.
2. Enforce platform etiquette and safety invariants in code, not vibes.
3. Accumulate an attempt ledger that improves triage over time and
   seeds sub-project A.
4. Publicly demonstrate the certificate engine's edge (trust score,
   theorem pages) — evidence for the Telperion superiority program.

## Non-goals

- General-purpose Lean proving of non-certificate-shaped milestones.
- A background daemon (phase 2; requires Agent SDK embedding).
- Mission-captain workflows (proposing missions) beyond what
  `POST /submit-problem` needs for reduction children.
- Any change to existing emitters or the trust model.

## Architecture

```
claude-plugin skill: prove2me-solver          (orchestration + etiquette)
        │ drives via CLI/MCP
        ▼
telperion p2m …  /  mcp_server p2m_* tools    (surface)
        │
        ├── prove2me/api.py        auth, endpoints, throttle, version gate
        ├── prove2me/workspace.py  $HOME/prove2me_workspace, toolchain pin,
        │                          scratch Lean projects, library imports
        ├── prove2me/triage.py     registry-driven shape filter + ranking
        └── prove2me/attempt.py    probe→certify→emit→lake build→verify→explain
                │
                └── existing Telperion pipeline (certify/emit/freeze, 133 emitters)
```

A Claude session invokes the skill and runs the loop; autonomy comes
from the session, not a daemon. All network writes flow through
`api.py` — one audited module.

### 1. `api.py` — platform client

- Auth chain per platform spec: credentials → `POST /login` →
  `POST /agent/api-key` (30-day key) → `POST /agent/refresh` (hourly
  access tokens). Tokens cached with expiry under
  `$HOME/prove2me_workspace/`; `credentials.json` is gitignored there
  and never enters this repo.
- Typed wrappers for: `GET /missions`, `GET /missions/:id/milestones`,
  `GET /theorems/:id`, `GET /theorems/:id/graph`,
  `GET /theorems/:id/submissions`, `GET /milestones/:id/history`,
  `POST /verify`, `GET /verify?submission_id=`,
  `PATCH /submissions/:id`, `POST /missions/:id/comments`,
  `POST /rate`, `POST /submit-problem`, `POST /submit-definition`,
  `GET /publish-jobs`.
- **Version gate** (platform rule): every `/login`, `/refresh`,
  `/agent/refresh` response carries a `version` field; mismatch with
  `api.SKILL_VERSION` (a module constant updated whenever we re-vendor
  their skill.md) raises `ProtocolDrift` ("refetch
  https://prove2.me/skill.md") instead of proceeding.
- **Throttle + backoff**: client-side rate limit on all calls;
  exponential backoff on 429/5xx; a circuit breaker halts the loop
  after 5 consecutive server errors (configurable; spam prevention is
  a safety property of an autonomous agent).

### 2. `workspace.py` — toolchain and scratch projects

- Clones/updates the official Prove2Me workspace repo at
  `$HOME/prove2me_workspace` (`Definitions/`, `Theorems/`,
  `Solutions/` layout per their skill.md).
- Selects a platform-pinned toolchain — prefer **Lean 4.33.1** (their
  newest of 4.33.1 / 4.30.0 / 4.29.0-rc3) with its fixed Mathlib rev.
  Telperion's own examples stay on v4.32.0; the two pins never mix.
- Materializes per-attempt scratch Lean projects that import platform
  library theorems (reuse is encouraged and scored by the platform).
- Emitted proofs use Mathlib-stable tactic cores (`ring`,
  `positivity`, `norm_num`, `linarith`, `linear_combination`,
  `omega`, `interval_cases`), so no emitter changes are expected for
  the pin difference. This is verified, not assumed — see the compat
  smoke test in Implementation order.

### 3. `triage.py` — certificate-first selection, mechanized

Two stages.

**Stage 1 — structural filter (pure code, cheap).** For every open
milestone, classify the `formal_statement` against the emitter set:
inequality / equality / valuation / enclosure / infeasibility /
finite-dispatch / tail-quantifier goals over ℕ/ℤ/ℚ/ℝ with
polynomial-or-rational content. The filter is **registry-driven**: it
enumerates `workflow.Emitter` subclasses and matches against each
emitter's declared goal shape, so newly landed emitters widen the
attemptable set with zero triage edits. (This inherits the
`emitter_sensitivity` CI discipline: an emitter that fails to declare
itself fails CI, so the registry cannot silently rot.)

**Stage 2 — scouting + lift (session LLM).** For stage-1 survivors,
the driving session performs the platform's mandated reconnaissance —
rejection history (`/milestones/:id/history`), prior submissions,
audit flags, mission comments — then drafts the **lift**: a Telperion
family module translating the Lean statement into sympy
(`InequalityFamily` or the matching emitter's input shape). The lift
is the genuinely hard step; its safety net is structural — a wrong
lift fails `certify` or the local kernel build and never reaches the
platform. `telperion p2m lift <milestone-id>` scaffolds the family
file with the formal statement embedded verbatim for faithfulness
checking.

Output: a ranked attempt queue persisted as JSON in the workspace.
Ranking = shape-match confidence × first-proof availability (open leaf
with no accepted proof) × estimated effort × realized emitter win rate
from the ledger (§5).

### 4. `attempt.py` — the solve/submit pipeline

Wraps the existing Telperion workflow with platform glue:

```
probe → certify → emit → local lake build (HARD GATE)
      → POST /verify → poll → PATCH explanation + citation
```

Hard invariants, enforced in code (each is a named check with a test):

- **I1 — no submission without a green local build** against the
  platform-pinned toolchain.
- **I2 — never import the target theorem itself** (it exists server-side
  as `sorry`); importing *other* platform theorems is encouraged.
- **I3 — zero `sorry` in the submitted file**; the submitted theorem is
  named `solution` and matches `formal_statement` binders exactly.
- **I4 — every accepted submission gets its explanation + exact source
  citation attached** (`PATCH /submissions/:id`); faithfulness to the
  cited source over impression, per platform rules.
- **I5 — no blind resubmission**: a rejection is ledgered with the
  server verdict, and the milestone is re-triaged or dropped.

Submission types: direct proof (primary), disproof (when `diagnose`
returns an exact counterexample — Telperion's FALSE verdict becomes a
negation certificate), reduction sketch (only when the lift yields a
Telperion-provable child set; no speculative decompositions).

### 5. Attempt ledger

`$HOME/prove2me_workspace/telperion_ledger.jsonl`, one record per
attempt: milestone id, mission id, emitter(s), lift hash, verdict,
server output, wall time, submission id. Consumed by:

- triage ranking (realized per-emitter win rate);
- the no-repeat rule (never re-attempt a captain-rejected path);
- `telperion p2m status` (credit earned at a glance).

The record shape is deliberately the seed of sub-project A's mission
registry so A can import it wholesale.

### 6. CLI, MCP, skill

- CLI (existing argparse pattern in `cli.py`):
  `telperion p2m login | missions | triage | lift <id> | attempt <id>
  | submit <id> | status | ledger`, all with `--no-submit` dry-run
  (submit-family commands refuse network writes under it).
- MCP: the same operations as `p2m_*` tools in the existing
  `mcp_server.py`.
- Skill `claude-plugin/skills/prove2me-solver/SKILL.md`: orchestrates
  the loop; encodes what can't live in code — scout-before-attempt,
  faithful-translation-over-impression, explanation quality, citation
  norms, when to rate/comment, when to stop (circuit breaker
  tripped, queue empty, or verdicts trending rejected).

## Error handling

- Typed exceptions per failure class (`AuthError`, `ProtocolDrift`,
  `VerifyRejected`, `RateLimited`, `PlatformDown`).
- Circuit breaker (§api.py) halts autonomous loops rather than
  degrading into API spam.
- `CertificationError` and `diagnose` verdicts keep their existing
  Telperion semantics: FALSE → consider disproof path; NOT_POLYA →
  re-triage with remedy hints; misuse → fix the lift.

## Testing

Existing pytest layout, no live network in CI:

1. **api.py**: recorded fixture responses (auth chain, version gate,
   throttle, circuit breaker).
2. **Golden triage corpus**: real formal statements fetched once from
   the platform's ~138 completed missions, committed as fixtures;
   stage-1 filter benchmarked for precision/recall against hand
   labels. This measures the certificate-first doctrine directly.
3. **attempt.py**: end-to-end in `--no-submit` mode on a known-good
   family; invariant tests I1–I5 each have a violating case that must
   refuse.
4. **Compat smoke test** (first implementation task): emit one
   known-good example (Bernoulli) under Lean 4.33.1 + platform Mathlib
   and `lake build` it green.

**Acceptance test for the project**: one real open milestone taken
from `p2m triage` through autonomous submission to a "Proved" verdict
on the platform, with explanation and citation attached, ledgered.

## Implementation order

1. Compat smoke test (de-risks the toolchain assumption before any
   API work).
2. `api.py` + auth + fixtures.
3. `workspace.py` + registration dry run.
4. Stage-1 triage + golden corpus.
5. `attempt.py` + invariants + `--no-submit` e2e.
6. CLI/MCP surface.
7. Skill + first live autonomous attempt (acceptance).

## Risks

- **Lift fidelity**: a lift can be *provable but unfaithful* (proves a
  different statement than the milestone intends). Mitigation: the
  binder-exactness rule (I3) means the kernel checks our theorem
  against the captain's authoritative `formal_statement` — a wrong
  target fails type-check server-side; faithfulness of *reductions* is
  additionally guarded by embedding the verbatim statement in the lift
  scaffold.
- **Toolchain drift**: platform bumps pins. Mitigation: version gate +
  workspace re-sync; the pin lives in one place (`workspace.py`).
- **Low stage-1 yield**: certificate-shaped milestones may be scarce
  among the open set. The golden corpus measures this early; if yield
  is low, the answer is more emitters (standing order) — not diluting
  the doctrine.
- **Reputational surface of autonomous text** (explanations,
  comments): templates in the skill keep generated prose factual,
  cited, and minimal.

## Implementation deviations (recorded at final review, 2026-09-11)

Recorded where the implementation diverged from the design spec during
the final-review fix wave. All deviations are deliberate and narrower
than the spec, not wider.

- **VerifyRejected exception replaced by ledgered record verdicts.**
  The design listed `VerifyRejected` as a typed exception in the error
  hierarchy. The implementation instead ledgers specific verdict strings
  (`Rejected`, `BuildFailed`, `CertifyRefused`, `SubmittedUnknown`,
  `PollTimeout`) and returns `AttemptRecord` from `run_attempt`.
  `SubmittedUnknown` is appended when `verify()` succeeds but a
  subsequent 5xx burst prevents resolving the verdict — the exception
  is then re-raised so the caller surfaces it, while the ledger records
  the fact that a submission was sent (no-repeat rule fires).
  `PollTimeout` replaces the former `("Rejected", "poll timeout")` so
  the two failure modes are distinguishable in ledger queries and
  `win_rate` denominators.

- **`submit` folded into `attempt` (I5); `ledger` CLI folded into
  `status`.** The spec listed `telperion p2m submit` and `telperion p2m
  ledger` as distinct subcommands. The implementation folds submission
  into `attempt` (controlled by `--no-submit`) and the ledger view into
  `status`, keeping the surface minimal and consistent with I5 (a
  rejection is re-triaged from the same `attempt` flow, not a separate
  submit command).

- **Ranking implements confidence × win-rate-prior with
  `status == open` as availability proxy; effort and first-proof factors
  deferred.** The spec listed four ranking factors (shape-match
  confidence, first-proof availability, estimated effort, realized
  win rate). The implementation uses a confidence × win-rate-prior
  composite, with `status == "open"` as the availability gate. Effort
  estimation and first-proof leaf detection are deferred to live tuning
  once the ledger has enough data to calibrate them.

- **Disproof submissions not yet supported (I3 verbatim gate) —
  escalate instead.** The spec described a disproof path (negate and
  resubmit when `diagnose` returns FALSE). I3's verbatim gate means a
  disproof requires a different `formal_statement` target, which the
  current bridge does not compose automatically. When `diagnose` returns
  FALSE the skill instructs the agent to STOP and escalate to the user
  with the counterexample rather than attempting an autonomous disproof.
