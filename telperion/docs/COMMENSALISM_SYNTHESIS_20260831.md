# The RH–BG–(P/NP) commensalism: state of the arc (2026-08-31)

Durable synthesis of the cross-pollination reassessment. One-line thesis:

> **Three proof programs — the Riemann Hypothesis, Brualdi–Goldwasser, and P-vs-NP
> (SoS-3XOR) — reduce their pointwise obligations to ONE box-positivity / SOS
> certificate engine. Each program's easy *atoms* share the engine (probed green);
> each program's hard *construction* stays open in its own lane.**

`conjecture1_proved = False` for all three. Nothing here proves, or approaches
proving, any of the three conjectures. This is shared *machinery* and honest scope.

## Three programs, one engine

| program | pointwise obligation | shared certificate | probe (evidence) | HARD open frontier (owned lane) |
|---|---|---|---|---|
| **RH** | ζ zero-free region `(1+x)^n ≥ 0` on `{1±x}` | Handelman box witness | `bg-handelman-shared-engine` ✓ | full zero-free region beyond the boundary; the region past R1 |
| **BG** | bulk-discharge `φ_v ≤ F*` on the field box `h∈(0,1]` | Handelman / Bernstein box-positivity | `bg-handelman-shared-engine` ✓ | the tight **field-dependent** universal `τ` |
| **P/NP** | SoS pseudo-expectation `0 ≤ pe(s²)` | exact-rational PSD moment matrix = SOS Gram | `sos_pe_probe.py` ✓ | SoS degree lower bound for UNSAT expanders |

The engine is the same object: nonnegative combinations of box-constraint products
(Handelman) / PSD Gram (SOS) — `emit_handelman`, `emit_sos`, `emit_constrained_sos`,
`cone`, `worst_corner`. RH built and extended it (`emit_zero_free_cosine` reusing
`HandelmanEmitter`); BG and P/NP consume the same shape.

## The arithmetic tie is BG-internal (precise)

`621/64 = 27·23` is a **BG-internal** three-way convergence: classical-BG brooms ↔
Φ¹¹ near-star tie (`64·243·23 = 621·576`) ↔ Lean `{4,5}` balanced-capped — all sharing
the *same* `23`. The parallel BG session proved the reconciliation exactly:
`R(s) [Φ¹¹] ≡ total(5)^(2s+1)/total(s)^11 [broom ratio]`, upgrading `c=5` to a closed
all-`c` single-crossing proof (`BG_23ADIC_RECONCILIATION_20260831.md`).

**RH shares the ENGINE, not the 23** — there is no `23` in `(1+x)^n`. So: **two
programs (BG, Φ¹¹) meet at the 23-adic tie; all three meet at the box-positivity
engine.** (Not three-way 23-adic — the BG owner's correction, incorporated.)

## Certificate-level reason the BG maximum sits at c=5

`c=5` is the UNIQUE cherry-count where the box-positivity certificate is *both*
low-degree *and* carries the exact 23-adic tie: `1+2c=11` makes `rhoB^11 = 621/64`
rational, so the 11th root cancels. For `c≠5` you get one or the other, never both —
the RH `IntervalBracket` route gives degree-3 positivity but loses the `23`; the
11th-power (`emit_padic`) route preserves `23^(1+2c)` but at degree ×11
(`bg_c6_bracket_handelman.py`). So `emit_padic` is the tie-preserving route reserved
for `c=5`; the bracket extends the gate to all `c` for positivity only.

## The monitor auto-discovers this

The skill-extraction monitor (`tools/shape_scout.py`) — the mechanized
cross-pollination standing order — was run over 18,040 theorems of live work
(`MONITOR_RUN_20260831.md`). Unsupervised, it: recovered the known RH→BG channels
(`emit_padic` via `deficit_v23`, `emit_bracket` via `rhoB_sqrt2`), firewalled the 50
tree→hub `R47R7*` obligations as STRUCTURAL (no false emit), and **surfaced the P/NP
link itself** (`Hsq:hsq_of_subsetForm` = `0 ≤ pe(s²)` → SOS). The third program
entered the picture because the monitor found it.

## What is NOT claimed

- No conjecture is proved or approached. `conjecture1_proved = False` throughout.
- The probed atoms are **individually easy** — feasibility/engine demonstrations, not
  hard results. Each program's hard construction is open research in its own lane.
- CANDIDATE (shape-matched) ≠ certified ≠ closed. The STRUCTURAL cores (BG tree→hub,
  the tight `τ`) are the real open work and no emitter reaches them.

## Artifact index

- **Map:** `…/laplacian_ratio/RH_EMITTER_TO_BG_OBLIGATION_MAP.md`
- **Standing order:** `telperion/docs/CROSS_POLLINATION_STANDING_ORDER.md`
- **Monitor + run:** `tools/shape_scout.py`, `docs/SKILL_EXTRACTION_MONITOR.md`,
  `docs/MONITOR_RUN_20260831.md` (branch `feat/skill-extraction-monitor`)
- **Probes:** `docs/probes/bg_discharge_handelman_probe.py`,
  `bg_c6_bracket_handelman.py` (branch `probe/bg-handelman-shared-engine`);
  `docs/probes/sos_pe_probe.py` (this branch)
- **BG lanes:** `BG_STAR_OF_BROOMS_HANDOFF.md`, `BG_23ADIC_RECONCILIATION_20260831.md`,
  `HANDOFF_TREE_TO_HUB_20260831.md`, `examples/bg_bulk_discharge`
- **Memory:** `rh-bg-shared-endgame-2026-08-31`, `telperion-cross-pollination-standing-order`

## The compounding loop (how this arc was produced)

A memory update seeded the BG session's Φ¹¹↔broom reconciliation → that closed the
map's bridge row and validated the Handelman probe → the probe became a kernel-gated
warm-up + narrowed the tight-`τ` crux → the monitor auto-found the P/NP link → the
SoS probe validated it. Bidirectional cross-pollination, mechanized and honest.
