# AXLE for Telperion — consolidated handoff (2026-09-04)

Three mining rounds of Axiom Math's AXLE (arXiv 2606.26442, `axle.axiommath.ai`) into
Telperion, plus a full negative-control build-out. All live on `merge/rh-to-main-4`.

## What landed (rounds 1-3)

**Round 1-2 (endpoint layer, hardened this session):** `verify` (structured, warm env,
returncode + non-vacuous `axioms_clean`), `gap_fill`, `repair` (self-updating from
mathlib `@[deprecated]`, 3642 renames), `cert_meta` (`type_hash` + `proof_hash`),
`bundle`, `normalize`, `theorem2sorry`.

**Negative control (the thesis, fully realized):** generic kernel-gated harness with the
positive control as a STRUCTURAL invariant (`okay = kernel_rejects AND true_compiles`,
non-settable). **All 25 certificate-sensitive emitters wired** — 26/26 two-sided controls
green vs real Lean; `neg_control_unwired_emitters() == []`. The emitter-sensitivity
REGISTRY is complete (72 emitters classified CS/SN, evidence-based) with a CI gate; the
`NEG_CONTROL_DECLARED_UNWIRED` honesty state exists for any future CS-without-adapter.

**Round 3 (system design, from the arXiv paper):** delivered best-of-both across parallel
sessions —
- #1 signature/statement-match gate (`statement_match.py`, batch + `def_identity_check`,
  applied to the BG spine audit),
- #2 warm tier via batching (LSP persistent-server path investigated + deferred),
- #3 bundle topological sort + `type_hash` structural dedup,
- #4 per-cert dependency extraction (`cert_deps.py`: `extract_deps`/`DepGraph`/`minimal_snippet`),
- #5 first-class `Environment` registry (`environment.py`: discovers 30 built envs, `resolve()`),
- #6 mechanical verify-guarded proof simplifier (`simplify.py`: unused-`have` pruning + rollback).

## Verification

- 26/26 negative controls green vs real Lean; all classification/gate tests green.
- Round-3 #5/#6 verified against the live tree (env discovery + simplifier rollback e2e).
- verify #3 behaviors (returncode, vacuity) confirmed vs Lean.
- NOT run to completion: the full 1193-test suite — blocked by a hanging
  `tests/test_bellman_rigidity.py` (pure-Python `telperion.bg`, no per-test timeout;
  unrelated to AXLE). Re-run with `--timeout=180` to get past it; that test needs a fix.

## State

- **Single source of truth:** `merge/rh-to-main-4` (imports clean; rounds 1/2/3 all present).
- `bg/scl-lean` has diverged with the parallel session's own commits — pull
  `merge/rh-to-main-4` in at a clean stopping point.
- The superseded integration fork `feat/telperion-axle-harden` was consolidated away
  (all its commits were already contained in `merge/rh-to-main-4`).

## Open follow-ups

- Fix / timeout-guard the hanging `test_bellman_rigidity.py` so the full suite completes.
- The persistent-server (LSP) warm tier (#2) was deferred in favor of batching — revisit
  if the per-cell gap-fill loop's cold-start cost dominates.
- AXLE mining is done; further Telperion expansion would come from the paper's operational
  layer (fair-share queueing, multi-tenant serving) only if Telperion becomes a service.

conjecture1_proved = False.
