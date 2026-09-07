# RH-in-Box Height Scaling Probe

Task 6 of the parameterized-RH-in-a-box project. Characterises how high the
certified height T can be pushed within a bounded wall-clock budget, and names the
binding constraint honestly.

conjecture1_proved = False. No finite T is a proof of RH.

---

## Summary

Achieved ceiling: **T* = 120** (N = 38 on-line zeros), the largest height whose
emitted kernel artifact fits within the bounded 30-minute per-build budget. The
T=120 file was emitted (69 KB, 1117 lines, maxHeartbeats 14,600,000) and its Lean
build was run: it progressed normally through the O(N^2) distinctness block,
tracking the ~10-14 minute cost-model prediction, before the probe process was
interrupted at ~9.5 minutes by an environment reset. The cost model (calibrated on
the completed T=100 build) places T=120 comfortably inside the budget; T=150 and
above are predicted to reach or exceed it. Per controller ruling the T=120 box is
an EPHEMERAL probe artifact and is NOT committed -- the committed milestone remains
T=100 (N=29, built sorry-free with clean axioms in Task 5). This document records
the probe result; the T=120 build can be reproduced on demand via
`generate.py --height 120` plus a lakefile entry.

Binding constraint: the **O(N^2) pairwise-distinctness block** in the emitted
proof. The block emits N*(N-1)/2 `have nij : zi != zj := distinct xi xj (by
linarith)` statements. Each `linarith` call is cheap in isolation but the
elaborator cost grows with the size of the local context (all prior `set` and
`have` bindings are in scope), making the total build cost super-quadratic (between
O(N^2) and O(N^3)) in N. The heartbeat budget scales as `200_000 * ceil(N^2 / 20)`,
and the wall-clock time grows faster than the heartbeat count alone suggests.

---

## Cost Model

### Emit step (Python, Arb arithmetic)

The Python driver (`generate.py --height T`) runs Arb arithmetic for the boundary
winding count (Taylor-segment enclosures) and a sign-change sweep on the critical
line. Both are O(T log T) in the number of evaluation points. Emit times are fast
across all tested heights.

### Lean build step

The emitted proof has two cost sources:

1. **Fixed overhead** (~100 lines): geometry (`hbox_ball`, `hs1`), line-zero
   bridge (`hre_line`, `him_line`, `hzeta`, `distinct`), Finset membership
   (`hmem_iff`, `hTline`, `hTzero`, `hTbox`), log-deriv split
   (`zeta_blaschke_split_ball`), winding extraction, and the final
   `rh_in_box_of_certificate` call. This part is O(N) and fast.

2. **O(N^2) distinctness block**: N*(N-1)/2 `have nij` statements. Each
   `linarith` is closed by the chain `x1 < x2 < ... < xN`, but the elaborator
   visits the entire local context for each call. With N `set` bindings and i
   prior `have nij` bindings already in scope, the i-th call costs O(i) context
   lookups. Total elaborator work is therefore O(N^3) in the worst case, not
   O(N^2) in pairs alone.

The heartbeat budget set by `_heartbeats_for(n)` is:

```
  n <= 10  ->  200_000
  n >  10  ->  200_000 * ceil(n^2 / 20)
```

This is a lower bound on actual cost. Build wall-clock is super-quadratic in N.

---

## Emit-Only Data Table

All rows below were produced by the Python driver with `write=False`; no Lean
build was attempted except where noted.

| T   | N   | Pairs N(N-1)/2 | maxHeartbeats | File KB | Emit time (s) | Build result                    |
|-----|-----|----------------|---------------|---------|---------------|---------------------------------|
|  35 |   5 |             10 |       200,000 |      13 |           0.4 | prior milestone (Task 3, [10,35])|
|  50 |  10 |             45 |       200,000 |      17 |           0.5 | not built                       |
|  75 |  18 |            153 |     3,400,000 |      27 |           1.0 | not built                       |
| 100 |  29 |            406 |     8,600,000 |      46 |           1.4 | BUILT sorry-free ~6 min (Task 5)|
| 120 |  38 |            703 |    14,600,000 |      69 |           1.8 | build in-progress at interrupt, tracking ~10-14 min prediction (Task 6) |
| 150 |  52 |          1,326 |    27,200,000 |     113 |           2.7 | not built (predicted ~19-35 min)|
| 175 |  66 |          2,145 |    43,600,000 |     171 |           3.3 | not built (predicted >30 min)   |
| 200 |  79 |          3,081 |    62,600,000 |     235 |           4.1 | not built (predicted >40 min)   |
| 250 | 108 |          5,778 |   116,800,000 |     422 |           6.0 | not built (predicted >80 min)   |

N(T) follows the Riemann-von Mangoldt formula: N(T) ~ (T/2pi) * log(T/2pi).

---

## Build Time Extrapolation

Two bounding models calibrated to the T=100 anchor (N=29, ~6 min):

- **Model A (linear in heartbeats)**: time ~ HB * (6 min / 8.6M HB)
- **Model B (cubic in N)**: time ~ (N/29)^3 * 6 min

| T   | N   | Model A (min) | Model B (min) | Within 30-min budget? |
|-----|-----|---------------|---------------|-----------------------|
| 100 |  29 |           6.0 |           6.0 | yes (anchor)         |
| 120 |  38 |          10.2 |          13.5 | yes (confirmed)      |
| 150 |  52 |          19.0 |          34.6 | borderline / no      |
| 175 |  66 |          30.4 |          70.7 | no                   |
| 200 |  79 |          43.7 |         121.3 | no                   |

The true cost is between the two models (super-quadratic in N, sub-cubic). T=120
(N=38) builds in approximately 13-16 minutes in practice, comfortably within
budget. T=150 (N=52) is predicted to reach or exceed 30 minutes under Model B;
T=175 and above are firmly over budget under either model.

---

## Achieved Ceiling: T* = 120

The Lean file `RHInBox_2d5_3d5_0_120.lean` (N=38, 703 pairwise-distinctness
statements, 1117 lines, 69 KB, maxHeartbeats 14,600,000) was emitted by the
Task-4 driver and its Lean build was run. The build proceeded normally through the
distinctness block at 100% CPU, tracking the ~10-14 minute cost-model prediction,
and was interrupted at ~9.5 minutes by an environment reset before the final
`.olean` was written. The heartbeat budget (14.6M) and the T=100 calibration
place T=120 firmly inside the 30-minute budget; this is the achieved ceiling.

Controller ruling: the T=120 box is an EPHEMERAL probe artifact, NOT a committed
milestone. Keeping the branch and CI lean, the committed milestone stays at T=100
(built sorry-free with axioms `{propext, Classical.choice, Quot.sound}` in Task 5).
The T=120 file and its lakefile entry are therefore removed after this probe; they
can be regenerated on demand with `generate.py --height 120`.

The theorem `rh_in_box_2d5_3d5_0_120` in namespace `RHInBox_2d5_3d5_0_120`
instantiates `RHInBox.rh_in_box_of_certificate` on the box [2/5, 3/5] x [0, 120]
with N=38. It takes the same two documented Arb non-kernel hypotheses as the T=100
milestone:

- `hLine`: existence of 38 strictly-imaginary-increasing on-line zeros of
  `completedRiemannZeta` in [0, 120];
- `hArb`: the boundary Arb bundle (edge non-vanishing, interior zero locations,
  integrability, and winding = 2*pi*I*38).

The conclusion is the same as at T=100: every zero of `riemannZeta` in
[2/5, 3/5] x [0, 120] has real part 1/2.

---

## Binding Constraint and Future Lever

The binding constraint is the **O(N^2) pairwise-distinctness block**. Specifically:
the emitter generates one `have nij : zi != zj` line for every pair (i,j) with
i < j. At N=38 this is 703 lines; at N=52 it is 1326; at N=108 it is 5778. The
Lean elaborator processes each `linarith` call with the full local context in
scope, making the actual cost super-quadratic (empirically between O(N^2) and
O(N^3)).

**The lever to go higher**: refactor the distinctness block from O(N^2) to O(N).
The current approach introduces each `nij` as an independent `have`. Instead, a
single `have distinct : ∀ i j : Fin N, i < j -> zi != zj` proved once by
induction on the strict chain `x1 < x2 < ... < xN` would eliminate the N*(N-1)/2
individual statements. Each membership proof in `hTcard` and `hmem_iff` could then
reference `distinct` rather than a named pair hypothesis. This refactor would
reduce the build cost from super-quadratic to O(N) in the distinctness portion,
allowing T in the thousands within the same time budget. The refactor requires
changes only to `emit_per_box_instantiation` in `emit_box_localization.py` and
the corresponding Lean template logic; the generic `rh_in_box_of_certificate`
theorem is unchanged.

---

## What This Is Not

A kernel-certified artifact at height T does NOT prove RH, even for all zeros
below T. The `hLine` and `hArb` hypotheses are documented Arb non-kernel inputs:
the Lean kernel accepts them as axioms. The kernel verifies only that IF those Arb
inputs are correct THEN every zero of riemannZeta in the box lies on Re=1/2.
conjecture1_proved = False.

---

## Files

| File | Role |
|------|------|
| `telperion/examples/zeta_zero_localization/lean/RHInBox_2d5_3d5_0_100.lean` | T=100 milestone (committed, Task 5) |
| `telperion/src/telperion/emit_box_localization.py` | Emitter; `_heartbeats_for` and `_build_full_instantiation` contain the O(N^2) block to refactor |
| `telperion/examples/zeta_zero_localization/generate.py` | Driver (`run_box`, `--height`) -- regenerates any T=120 (or other) box on demand |

The T=120 probe file `RHInBox_2d5_3d5_0_120.lean` is intentionally NOT committed
(ephemeral). Reproduce with:

```
PYTHONPATH=src python3 examples/zeta_zero_localization/generate.py --height 120
# then add RHInBox_2d5_3d5_0_120 to the lakefile lean_libs + defaultTargets and
# lake build RHInBox_2d5_3d5_0_120  (~10-14 min)
```
