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

## Finding: the LSP (`lean --server`) does NOT warm-repeat either (validated 2026-09-04)

The natural "persistent tier" candidate is the Lean 4 LSP server. Validated empirically
(minimal JSON-RPC client, built env):

- The LSP **surfaces everything** the cold path needs, as diagnostics mappable to
  `_parse_output`: **errors** (severity 1), **`sorry`** (severity 2, `declaration uses
  \`sorry\``), and **`#print axioms`** output (severity 3 info, `'foo' depends on axioms:
  …` / `does not depend on any axioms`). So the *contract* works.
- BUT the LSP uses a **per-file-worker** model: each `didOpen` of a DIFFERENT file spawns a
  worker that **re-elaborates the imports independently**. Measured, waiting for *true*
  completion (`$/lean/fileProgress` `processing == []`, not the premature first
  `publishDiagnostics`): warm docs land at **~7.5s ≈ cold** — no cross-file env sharing.
- A first, naive probe showed "0.2s warm" — that was an **artifact of breaking on an early,
  still-empty `publishDiagnostics`** before elaboration finished. Corrected: no speedup.

So neither `lean --stdin` (single-shot) nor `lean --server` (per-file re-elaboration) shares
a loaded Mathlib across many DIFFERENT snippets. The ONLY mechanism that does is a REPL that
runs many commands against one resident environment — `leanprover-community/repl` — which is
**not in the toolchain** and would be a real build-dependency add.

## Recommendation

- **Now (shipped):** BATCHING — one Mathlib load for many checks. Covers the audit and the
  at-once gap-fill hot paths (the actual usage). This is the right and only robust tier
  without a new dependency.
- **Deferred (real persistent tier):** add `leanprover-community/repl` as a Lake dependency
  and drive it (`{"cmd": …}` → messages/env) for sub-second *separate*-call repeats. Worth it
  only once the loop is genuinely interactive one-at-a-time; the LSP is NOT the shortcut it
  appeared to be.

conjecture1_proved = False.
