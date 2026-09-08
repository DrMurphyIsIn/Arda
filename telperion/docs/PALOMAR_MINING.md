# Palomar certificate mining — distilling Palomar into Telperion

`src/telperion/palomar_mine.py` is the systematic distiller: it turns the Palomar
registry (Lean-verified, comparator-checked formalizations) into ranked *candidate
Telperion emitter shapes* for this project's two research fronts — Riemann (`rh`)
and Brualdi–Goldwasser (`bg`) — plus a proof-complexity front (`pvsnp`).

## Design

Split into a PURE offline-testable core and a thin network layer (same
untrusted-input / testable-core discipline as the emitters):

- **`classify_entry(entry, topics=None)`** — matches an entry's title/abstract/MSC
  against the topic lexicons (`TOPIC_KEYWORDS`) and the shape rules (`SHAPE_RULES`),
  returning a `MiningCandidate` (topics, shapes, trust-boundary flag, score) or `None`.
  Each shape carries either an EXISTING Telperion `kind` (maps onto proven tooling) or
  `None` (a candidate NEW shape to design).
- **`mine(entries, topics, min_score)`** — classify + rank (score desc).
- **`mining_report(candidates)`** — markdown, split into "new candidate shapes" vs
  "map onto existing emitters".
- **`fetch_registry(url)`** — thin urllib GET of `recent.json`.
- **`poll(state_path, topics, fetch=…)`** — the recurring subroutine: fetch, diff
  against the seen-state file, classify only NEW entries, persist the enlarged seen-set,
  return the new candidates. `fetch` is injectable so the loop is unit-tested offline.

Nothing here trusts Palomar: a candidate is a lead for a human/agent to build and
CI-verify, never an emitter itself.

## Shape rules (math vocabulary → emitter family)

| matched vocabulary | family | Telperion `kind` |
|---|---|---|
| Li-Keiper / Li's criterion | Li positivity ladder | NEW |
| explicit formula / pair correlation / von Mangoldt / Weil | explicit-formula / Weil positivity | NEW |
| Jensen / Laguerre / Turán / real-root / log-concave / Newton | real-rootedness / hyperbolicity | `interlacing` |
| SOS / semidefinite / PSD / Gram / low-rank | SOS / PSD positivity | `psd_form` |
| eigenvalue / spectral / Hermitian / inertia / signature | Hermitian eigenvalue / inertia | `rank_trace_scalar` |
| argument principle / winding / residue / zero-count / Turing | argument-principle / winding | `argument_principle` |
| permanent / matching / immanant / spanning tree / cavity | permanent / matching (BG cavity) | NEW |
| Nullstellensatz / Handelman / Putinar / Chvátal–Gomory | Positivstellensatz / integer rounding | `handelman` |
| interval arithmetic / enclosure / exact-arith / finite / decide | finite-decide / enclosure | `finite_decide` |
| spectral theorem / self-adjoint / PVM / Stone / Cayley | Hilbert–Pólya infrastructure | NEW |

## CLI

```
telperion palomar-mine --topic rh                 # live: fetch + report (RH)
telperion palomar-mine --topic bg --min-score 3   # BG, thin candidates pruned
telperion palomar-mine --file recent.json --json  # offline JSON (a saved registry)
telperion palomar-mine --poll --topic rh,bg --state palomar-seen.json
```

`--poll` is the recurring form: on each run it surfaces only entries new since the
last run. Schedule it (cron / the `/loop` skill) to turn "new Palomar entry" into
"surfaced candidate emitter" automatically. Suggested cadence: daily.

## Current leads

See `PALOMAR_RH_SOURCES.md` and `PALOMAR_BG_SOURCES.md` for the curated, roadmap-tagged
lead lists (the standout: Track-2 Li's criterion is already formalized upstream —
reuse it; and Davenport–Heilbronn is the negative control for the RH certificate families).
