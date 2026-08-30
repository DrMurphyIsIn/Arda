# bg_caterpillar_concavity — the density knife-edge (route-b piece 2, kernel-gated)

Emitter-generated, Mathlib-only frozen Lean (`lean/BGCaterpillarConcavity.lean`, kernel-checked by
`telperion-lean-e2e` via `lake build`; regenerated stdlib-only by `generate.py` from frozen enclosures).
`conjecture1_proved = False` — **not** a proof of Brualdi–Goldwasser.

## What it certifies

`F(a)` = the infinite length-2-arm caterpillar cavity (Bethe) free-energy density with `a` arms per hub —
the **`k=0` "phonon" direction** of the structural Hessian, the arm-count knife-edge. `ρ* = exp(max_a F(a))`,
the maximizer the ~7-arm caterpillar. Two facts, kernel-gated by `norm_num`:

- **(strict max)** `a=7` strictly maximizes `F` over integer arm-counts: `F(7) > F(6)`, `F(7) > F(8)`;
- **(concave)** `F(a-1) + F(a+1) < 2 F(a)` for `a = 6, 7, 8`.

The concavity margins are ~`10⁻⁵` (the "barely-true" knife-edge). The `F(a)` are transcendental (logs of
quadratic surds from the exact cavity fixed point); the certificate **consumes rigorous rational enclosures**
`F(a) ∈ [lo_a, hi_a]` (80-digit interval numerics — the transcendental import, exactly the `turan`/`jensen`/
`hankel_jensen` trust model, enclosure half-width ~`10⁻¹⁵`) and kernel-gates the rational inequalities between
them.

## Where it sits in the route-(b) reduction (W15–W20 fusion)

The structural Hessian of the caterpillar is negative-definite iff `[h₀<0]` **and**
`[2Σ_{r≥1}|h_r| < |h₀|]`. The second condition — the phonon gap "never collapses", so every non-`k=0` mode
is gapped *below* this one — is **monomer-dimer strong spatial mixing** (Bayati–Gamarnik–Katz–Nagaraj–Tetali,
STOC 2007), a known uniform correlation-decay theorem. This example discharges the **first** condition
(piece 2: the `k=0` mode is a strict, concave max). Together they certify the caterpillar as a strict *local*
max of the density in every structural direction.

**Honest ceiling.** This is the local half. The **global** step — that no distant, non-caterpillar structure
is a competing local max — remains open (so far numerical, W17). So this is a proven *reduction* piece, not a
proof of BG. `conjecture1_proved = False`.
