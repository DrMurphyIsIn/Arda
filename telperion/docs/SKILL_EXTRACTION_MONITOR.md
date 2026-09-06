# Skill-extraction monitor — design + evidence-first findings

Mechanizes the [cross-pollination standing order](CROSS_POLLINATION_STANDING_ORDER.md):
continuously watch BG + RH proof work, surface shapes an existing (or new) Telperion
emitter could discharge, and feed a proposal queue for offline certification + CI
kernel confirmation.

## Architecture (proposer, not mechanical daemon)

The judgment step — "is this recurring hand-written pattern a generalizable shape?"
— is LLM-shaped, and the trust boundary is binding. So the monitor is a **scheduled
proposer agent** wrapping a deterministic **extraction+dedup core**:

```
 new proof commit (BG or RH repo)
        │  (git post-commit trigger, or low-freq schedule)
        ▼
 [1] shape_scout.py   ← deterministic core (this dir, stdlib-only)
        │   extract theorem goals · classify into emitter SHAPE ·
        │   dedup vs emitter-GENERATED files (telperion provenance header)
        ▼
 CANDIDATE queue (hand-written, emitter-shaped, non-trivial)
        │
 [2] agent triage     ← LLM: cluster candidates into a would-be FAMILY;
        │                pick/propose an emitter kind; draft an InequalityFamily
        ▼
 [3] offline certify  ← REAL dedup: does the emitter actually REPRODUCE the goal?
        │                (exact Fraction/sympy; no Lean build)  emitter-shaped
        │                ≠ emitter-reproducible — this step is the true filter.
        ▼
 telperion/candidates/  ← QUARANTINE (untrusted).  Never auto-registered.
        │
 [4] CI kernel gate    ← rh-compiles / lean-verify-*: the ONLY trusted step.
        ▼
 human promotes to the shared emitter set
```

The proposer stays strictly untrusted: it drafts candidate families into a
quarantine dir, never hand-writes emitted Lean, never registers a trusted emitter.
The kernel is the sole arbiter.

## The core: `tools/shape_scout.py`

Stdlib-only. Walks Lean roots, extracts each theorem's goal (depth-0 bracket scan
for the goal-opening `:` … `:=`), strips Lean comments first (so `theorem` inside a
docstring is never mistaken for a declaration), classifies the goal into a shape,
and buckets:

- **COVERED** — in an emitter-generated file (telperion provenance header). Done.
- **CANDIDATE** — hand-written, emitter-shaped, non-trivial. The proposal queue.
- **TRIVIAL** — all-numeric constant fact (norm_num/decide), no big integer. Filtered.
- **STRUCTURAL** — not inequality/identity-shaped (encoder, def-bridge, ∀-over-
  inductive). No emitter reaches it — the `hConfine` bucket.

Shape → emitter map covers: `identity`→IdentityEmitter, `polya_ineq`→DirectPolya/
bilinear, `sos_psd`→SOS/WorstCorner, `bracket`→IntervalBracket, `valuation`→padic,
`trig_nonneg`, `interlacing`, `unimodal`, `witness`, `monotone`.

## Measured evidence (2026-08-30, first run)

Run against RH (`rh_lean/RH`, 25 files) and BG (`laplacian_ratio/formalization`,
240 files) corpora.

| corpus | scanned | covered | candidate | trivial | structural |
|---|---|---|---|---|---|
| RH | 116 | 22 | **54** | 30 | 10 |
| BG | 7137 | 1944 | **3777** | 371 | 1045 |

Genuine cross-pollination gold surfaced in the RH corpus (the BG modules riding in
the RH gate): `deficit_v23_k*` (valuation → emit_padic), `tie_collective_balance`
(identity → IdentityEmitter), `log_*_enclosure` / `bg_omega_enclosure` (bracket →
IntervalBracket), `hankel_jensen_xi_n0_H*` (PSD).

### False-positive classes (measured, and status)

1. **Prose/extraction noise** — `theorem`/`lemma` inside docstrings (BG's `Lean`
   artifact). Was ~23% of BG raw candidates. **FIXED** by `_strip_comments`
   (BG theorem count 7167→7137; noise class eliminated).
2. **All-numeric triviality** — rational-constant comparisons closable by
   `norm_num`. Was ~77% of RH raw candidates. **FIXED** by `is_trivial` (keeps
   large-integer valuation/identity facts, which emit_padic/IdentityEmitter handle
   better than raw norm_num).
3. **Definitional recursion equations** over inductive types (`rho0_node`,
   `realize_node` with `Branch.node`) misclassified as rational identities.
   **RESIDUAL** — next filter; cleanly detectable by constructor-presence
   (RHS/LHS mentions a data constructor ⇒ definitional `rfl`/`simp`, not an emitter
   target).

## Gating decision (before wiring the schedule)

1. Add the constructor/definitional filter (FP class 3).
2. Wire step [3] — the offline certify round-trip — as the true dedup. "Emitter-
   shaped" (structural) ≠ "emitter-reproducible" (certified). Only a candidate an
   emitter actually reproduces offline enters quarantine.
3. Trigger on new proof commits, not every session (cache-window economics); the
   monitor writes only to `candidates/`, never to proof branches (parallel-session
   collision safety).

The deterministic core is viable today; the schedule is a thin wrapper once 1–3 land.
