# Warm verify tier — findings + the batching win (2026-09-04)

The AXLE third tour proposed a fast warm-env verify tier (the `#5` `lean_server` spike,
shipped fallback-guarded because the persistent-server protocol was unvalidated on
Lean 4.32.0). With a live built env now available, here is what validation found and
what was shipped.

## Finding: `lean --stdin` is single-shot

Confirmed empirically on the pinned 4.32.0 toolchain (built `examples/log_combination/lean`):

- `lake env lean --stdin` **accepts a whole file on stdin** and emits the same
  `<stdin>:L:C: error:` diagnostics `verify._parse_output` already parses. Good.
- But it **reads to EOF, elaborates once, and exits** — it is *single-shot*. A process
  cannot be driven snippet-by-snippet against a resident environment. So
  `lean_server.LeanServer`'s stdin-framing loop does not actually warm-repeat: each call
  is effectively a fresh `import Mathlib` load (~4–8s). The dominant cost is loading the
  Mathlib oleans into a process, and `--stdin` re-pays it every call.
- The *only* way to amortise the load across **separate** verify calls is a persistent
  process that stays alive — i.e. the LSP (`lean --server`, JSON-RPC/`didOpen`) or the
  community `repl` tool (not present in the env). That is a real build; it remains the
  documented next step (`lean_server._start_lsp` sketch).

## Shipped: batching (the robust warm-tier win)

Where many checks are done at once — an audit, or `gap_fill` over a cell family — the
practical win is **one Mathlib load for all of them**, not a persistent server:

| | 3 checks |
|---|---|
| separate (`import Mathlib` × 3) | **14.4s** |
| batched (one load) | **4.3s** |

`statement_match_check(..., batch=True)` (default) now emits all `__sigmatch` theorems in
one file, elaborates once, and only re-runs per-decl to *attribute* a mismatch on failure.
The BG spine gate runs 3 checks in **5.5s** (one load) via `scripts/bg_spine_audit.py`.
This captures the bulk of the latency win for the audit/gap-fill hot paths without the
unvalidated persistent-server protocol.

## Recommendation

- **Now:** batching (shipped) covers the many-checks-at-once case, which is the audit and
  the per-cell-family gap-fill.
- **Next (real persistent tier):** wire the LSP path in `lean_server` (`didOpen` a virtual
  doc, map `publishDiagnostics` → the shared `_parse_output` contract) and benchmark
  sub-second *separate*-call repeats. Worth it once the gap-fill loop is interactive
  (one gap at a time) rather than batched. Until then, batching is the right tier.

conjecture1_proved = False.
