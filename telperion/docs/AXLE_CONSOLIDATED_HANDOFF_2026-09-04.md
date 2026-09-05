# AXLE for Telperion — consolidated handoff (2026-09-04, final)

Three mining rounds of Axiom Math's AXLE (arXiv 2606.26442, `axle.axiommath.ai`) into
Telperion, a full negative-control build-out, and the test-suite cleanup that let the
whole suite run to completion. All merged to `main`.

## 1. What landed

### Rounds 1-2 — the endpoint/utility layer (hardened)
`verify` (structured, warm pre-built env, returncode backstop + non-vacuous
`axioms_clean` via `axioms_checked`), `gap_fill`, `repair` (self-updating from mathlib
`@[deprecated]`, 3642 renames, seed merged under the JSON), `cert_meta`
(`type_hash` + `proof_hash`), `bundle`, `normalize`, `theorem2sorry`.

### Negative control — the thesis, fully realized
Generic kernel-gated harness (`negative_control_harness.py`) with the positive control
as a STRUCTURAL invariant: `GenericNegativeControlResult.okay = kernel_rejects AND
true_compiles`, a computed property with no settable field — a rejection-for-the-wrong-
reason cannot masquerade as a passing control. **All 25 certificate-sensitive emitters
wired; 26/26 two-sided controls green vs real Lean; `neg_control_unwired_emitters() == []`.**
The emitter-sensitivity REGISTRY is complete (72 emitters classified CS/SN, evidence-based,
30 via a review-checked classification pass) with a CI gate; `NEG_CONTROL_DECLARED_UNWIRED`
is the honest state for any future CS-without-adapter.

### Round 3 — system design from the arXiv paper (best-of-both across parallel sessions)
- #1 signature/statement-match gate — `statement_match.py` (batch + `def_identity_check`),
  applied to the BG spine audit.
- #2 warm tier — batching (`statement_match` batch mode); the LSP persistent-server path
  was investigated and deferred in favor of batching.
- #3 bundle topological sort + `type_hash` structural dedup.
- #4 per-cert dependency extraction — `cert_deps.py` (`extract_deps`/`DepGraph`/`minimal_snippet`).
- #5 first-class `Environment` registry — `environment.py` (discovers built envs, `resolve()`).
- #6 mechanical verify-guarded proof simplifier — `simplify.py` (unused-`have` pruning + rollback).

Docs: `AXLE_THIRD_TOUR_2026-09-04.md` (the round-3 mining) is the design source.

## 2. Verification

- 26/26 negative controls green vs real Lean; all classification/gate tests green.
- Round-3 #5/#6 verified against the built tree (env discovery + simplifier rollback e2e).
- verify #3 behaviors (returncode, vacuity) confirmed vs Lean.
- **Full 1254-test suite runs to completion, 100% green** after the two enumeration
  fixes below (see `TEST_SUITE_HEALTH_2026-09-04.md`).

## 3. Test-suite fixes (the blockers that hid the green)

Two `telperion.bg` tests hung the full suite indefinitely (no per-test timeout). Both
were slow ENUMERATIONS, not correctness bugs, and both fixes were proven MATH-NEUTRAL
before merge:

- **bellman** (`value_function`): the `max_trees` budget was enforced only after each
  outer sweep, so `combinations_with_replacement(pool, 3)` reached ~1e9 tuples first.
  Fix: enforce the existing budget DURING enumeration. (PR #212, merged.)
- **ehrhart** (`matching_polytope_ehrhart_bruteforce`): `product(range(t+1), repeat=|edges|)`
  = ~2e8 points at s=4. Fix: backtracking with early pruning; proven identical to the
  naive count on the tractable s=2,3 cases. (PR #214, merged.)

## 4. State

- **Single source of truth: `main`** (== `merge/rh-to-main-4`). Rounds 1/2/3, the
  negative-control coverage, and both fixes are all present; imports clean.
- Superseded integration fork `feat/telperion-axle-harden` was consolidated away
  (fully contained in `main`).
- PRs from this effort — #211 (handoff), #212 (bellman), #214 (ehrhart) — all merged.

## 5. Open follow-ups

- The persistent-server (LSP) warm tier (#2) was deferred in favor of batching — revisit
  if the per-cell gap-fill loop's cold-start cost dominates.
- The full suite has no per-test timeout by default; run with `--timeout=180` (needs
  `pytest-timeout`) if a future slow/hanging test is suspected.
- Further AXLE mining is exhausted for a library; the paper's operational layer
  (fair-share queueing, multi-tenant serving) applies only if Telperion becomes a service.

## 6. Methodology notes (the discipline that mattered)

- **Verify before claiming.** Every "green" here is backed by a run against the real Lean
  kernel or the actual tests, not asserted.
- **Don't fix math blind.** Both suite fixes were performance issues with provably-identical
  results (validated against the naive reference / the DP). A genuine value discrepancy
  would have been left with a diagnosis, not forced to pass.
- **PR, not direct-to-main.** Branch protection blocks direct pushes to `main`; changes
  land via reviewable PRs.

conjecture1_proved = False.
