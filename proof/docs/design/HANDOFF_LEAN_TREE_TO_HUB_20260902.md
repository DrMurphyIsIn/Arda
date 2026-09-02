# Handoff: close the Lean tree→hub layer (to the hnorm / tree→hub lane) — 2026-09-02

**To:** the parallel session that owns the `R47R7*` / `hnorm` Lean lane.
**From:** the branch-model / Telperion session (operator-directed take-over, then hand-back for execution).
**Branch:** `bg/lean-tree-to-hub` (off `main`; spec + plan committed, no Lean written yet).

## What this is

A brainstormed, approved **spec** + a task-by-task **implementation plan** to drive the tree→hub layer to closure.
The layer already proves `tree_to_hub_sized` given `StraightProgress_sized`, with every step proven *modulo*
Obligation A. This work:

- **Stage 1 (achievable):** prove the existence-finder assembly (`R47R7Lift` + `R47R7Finder` + `R47R7Closure`,
  new files, self-building via the glob) so the whole layer rests on **one clean `ObligationA` hypothesis**.
- **Stage 2 (gated research):** isolate the exact finder-move inequality (Python), probe whether the cavity /
  invariant-price-interval machinery discharges it (**go/no-go gate**), then either formalize it in Lean or ship a
  sharpened-obstruction doc.

## Read these, in order

1. `proof/docs/design/LEAN_TREE_TO_HUB_CLOSURE_20260902.md` — the design spec (what & why).
2. `proof/docs/design/LEAN_TREE_TO_HUB_PLAN_20260902.md` — the task-by-task plan (how; Tasks 0–6, build-cycle steps, reuse map, go/no-go gates).

## The three things that matter most (read before starting)

1. **`ObligationA` is tied to the finder's CHOSEN move, NOT `∀ valid A,B`.** The universal form is *false* — a fixed
   `(A=child₁, B=child₂)` decomposition decreases `Aobj` in 285/1320 cases (verified this session). Define
   `ObligationA := ∀ t (h : strDefect t ≠ 0), Aobj t ≤ Aobj (finderStep t h)`. Task 4 Step 2 is the
   model-faithfulness gate (must be 0 violations on the *finder* move, unlike the naive form).

2. **The lifting hinges on `A`'s root degree NOT changing.** The whole-tree root degree *does* change under the move
   (why `node_Ztot_child_mono` alone didn't close it originally) — but the finder applies the move *inside* `A`, and
   `pushInto A B` keeps `A`'s own root degree (B goes to a descendant hub). That is what makes `Aobj_lift` (via
   `node_Ztot_child_mono`) applicable. Confirm `udeg A = udeg (pushInto A B)` early (Task 1 note).

3. **Stage 2 may legitimately end NO-GO.** If the cavity reduction doesn't close (Task 5), ship the obstruction doc
   and STOP — Stage 1 is the banked result. Do not force Task 6. `conjecture1_proved = False` unless Task 6 fully
   lands with green CI.

## Mechanics

- **CI-only Lean** (no local `lake build` — SoC watchdog; this Mac runs the live trading daemons). Task 0 adds a
  `fast-lean-check` workflow (warm cache, target modules only, ~5 min/iter); the full `proof-lean` is the merge gate.
- **New files only** — no edits to your `R47R7*` files (the one shared-file touch, `AxiomGuard.lean`, is flagged in
  Task 3 Step 2 to coordinate with you).
- Python harness lives in `proof/verification/`, re-anchored to `kelmans_mixed_load.pi_literal`.

## Status at hand-off

Spec + plan + this handoff committed on `bg/lean-tree-to-hub`. **No Lean or Python implementation started** — the
lane is yours to execute. Ping the originating session if the `finderStep` decomposition or the cavity-probe
reduction needs the branch-model / Telperion context (the invariant interval `I=[456/3703,3/7]`, the gated certs
`BroomVsCherryCertificate` / `LeafExchangeCertificate` / `ExtremalityPriceMapCertificate` /
`NearBroomUnimodalityCertificate`, and the `bg_upper_bound.py` reduction ledger).
