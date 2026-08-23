# Convex-hinge certificate — status & Lean-emit design (2026-08-22)

The reusable primitive under BG G1 Stage-II class floors (lemma 2) AND the R7
ledger — both use the folded hinge `φ(y) = c·(y − t0)₊` (the R3 `phi_le_one`
hinge). See `proof/docs/design/TELPERION_G1_R7_SKILLS_20260822.md`.

## Shipped (this branch) — exact certificate core, tested

`telperion/hinge.py`:
- `hinge_floor_certificate(c, t0, k)` — the context-free class-floor shape
  `Σᵢ (yᵢ − t0)₊ ≥ (Σᵢ yᵢ − k·t0)₊` for the convex hinge (`c ≥ 0`); None if the
  slope is not convex. Tightness at equal children on the linear branch recorded.
- `verify_hinge_floor` — independent exact re-check (convexity precondition +
  posPart-subadditivity direction at a hostile sample set incl. the tight point).
- `hinge_floor_theorem(cert)` — emits the Lean **statement** (correct) + a
  discharge via `posPart` subadditivity.

Tested (`tests/test_hinge.py`, 3 green): certifies the floor, rejects negative
slope, records equal-children tightness. Exact rationals — no Lean needed here.

## Why this is the right primitive
The G1_STAGE2 audit (2026-08-22) shows the class floor is Jensen on a **convex**
hinge — "clean through the knee", structurally *easier* than the already-closed
non-convex g-step cap. `posPart` subadditivity `(Σ zᵢ)₊ ≤ Σ (zᵢ)₊` (with
`zᵢ = yᵢ − t0`) IS that Jensen fact, exact and kernel-checkable. It discharges
R7 `HypFloors`' per-class floor cores and is reused wherever the hinge appears.

## DONE — Lean discharge is kernel-verified on main
The discharge landed via `posPart_def` + `sup_le` (`Σzᵢ ≤ Σzᵢ⁺` termwise by
`le_posPart`; `0 ≤ Σzᵢ⁺` by `positivity`) — compiled **first try**:
- **Telperion emitter + example**: `telperion/examples/hinge_floor/` (arities
  k=2..5), `hinge-floor-compiles` CI green (#75, on main).
- **Native R3Cert port** (general-arity Finset, for the live proof):
  `proof/formalization/R3Cert/HingeProfileFloor.lean` — `posPart_sum_le` by Finset
  induction over the two-term `(a+b)⁺ ≤ a⁺ + b⁺`, plus `hinge_profile_floor` and
  `hinge_profile_floor_mul` (#77, on main). Consumed by the crux session's
  `full_slack_ge_floor` composition (kernel-checked on main).

## Next (this skill program)
- L2: wire `hinge_floor` into the real G1 class-floor family (needs the G1 `φ`,
  cavity-recursion defs — coordinate; parallel sessions own `slack_ledger_*`).
- L3: the domination-ratio unimodality via `unimodal_max_family` /
  `monotone_tail_family` (single-crossing rational fn).
- R7 `HypAmortizedHub` via `cone_family`; `HypDominationSweeps` via
  `finite_decide_family`.
