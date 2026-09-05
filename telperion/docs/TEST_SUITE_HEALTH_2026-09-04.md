# Telperion test-suite health (2026-09-04)

## Status: the full suite runs to completion, 100% green

`python3 -m pytest tests/` — **1254 tests, all passing** (2 environment-gated skips
for a fresh clone with no built mathlib). Verified against `main` after PRs #212 and
#214.

## Running it

The suite has **no per-test timeout by default**. Lean-backed tests need a built env
(the `examples/*/lean/.lake` mathlib cache); in a fresh clone those skip cleanly via
`tests/lean_env.py::lean_env_ready`. For a defensive full run:

```
pip install pytest-timeout        # once
PYTHONPATH=src PATH="$HOME/.elan/bin:$PATH" \
  python3 -m pytest tests/ --timeout=180 --timeout-method=signal -rfE --durations=25
```

`--timeout` is the safety net: if a future test loops or a Lean call wedges, it
fails-fast at 180s instead of hanging the whole run. (Two such hangs were fixed below;
the flag is cheap insurance against the next one.)

Slow-but-legitimate tests: the 26 kernel-gated negative controls (`test_certificate_
sensitivity.py::test_generic_negative_control_holds`) each do two real Lean
elaborations, ~333s total; the full suite is ~25 min warm.

## Two enumeration fixes (2026-09-04)

Both were `telperion.bg` tests that hung the suite indefinitely — slow ENUMERATIONS,
not correctness bugs. Both fixes were proven **math-neutral** before merging (identical
counts to the original on the tractable cases), so no risk of a silently-wrong result
entering a proof-critical path.

### 1. `bellman.value_function` (PR #212)
`pool` grows every sweep (~1881 trees after sweep 1), so
`combinations_with_replacement(pool, 3)` reached ~1e9 tuples — each calling `_size` —
while the `max_trees` guard was checked only AFTER each outer sweep, never firing inside
that loop. Fix: enforce the existing `max_trees` budget DURING enumeration (break out of
the inner loops when `len(allT) > max_trees`). No new math. Validated: all 7
`test_bellman_rigidity` tests pass in ~7.5s (were hanging), so `max_trees=2000` suffices.

### 2. `ehrhart_bg.matching_polytope_ehrhart_bruteforce` (PR #214)
`product(range(t+1), repeat=|edges|)` = `(t+1)^|edges|` points (~2.14e8 at s=4), then
filter — so the s=4 case timed out (>120s). Fix: backtrack edge-by-edge and PRUNE a
partial assignment the moment either endpoint's running sum would exceed `t` (valid
because `x >= 0`). The counted set (every `L_P(t)`) is IDENTICAL to the naive
enumeration — verified equal on the tractable s=2,3 cases, with the DP agreeing on all
three. s=4 now runs in ~3s; all 6 `test_ehrhart_bg` tests pass in ~4.8s.

## If a full-suite hang recurs

1. Re-run with `--timeout=60 -v` to pinpoint the offending test.
2. The `--timeout-method=signal` traceback shows the exact line it was stuck in.
3. Diagnose before fixing: distinguish a slow enumeration (safe to prune/bound, but only
   with a proof the result is unchanged) from a genuine value bug (leave it, report it —
   do not force a test to pass by changing the math).

conjecture1_proved = False.
