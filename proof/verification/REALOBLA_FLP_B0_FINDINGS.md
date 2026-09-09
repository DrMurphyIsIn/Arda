# B0 de-risk: the FLP (leaf-path-extension) move for `StraightProgress_sized`

**Script:** `proof/verification/realobla_flp_derisk.py` (+ the 2x2 / characterization probes inline below).
Exact rational arithmetic; `Aobj` engine anchored in `telperion/scratch/a3_derisk.py` (matches unrooted
`per(L)/prod deg`, root-invariant, self-checked). Enumeration: all non-isomorphic unrooted trees `n = 2..14`.

## What was measured

The Lean-proven Type-L move (`aobj_flp_context_lift_crest`) is the leaf-onto-leaf **sibling** path-extension:
a node `u = node(leaf :: leaf :: crest)` (two BARE-LEAF children) becomes `node(stem :: crest)`,
`stem = node[leaf]` (one leaf stacked under the other). Vertex-preserving; drops `strDefect` by exactly 1
(when `u` flips non-piece->piece at its parent); `Aobj` non-decreasing with the closed-form increment
`P*(n^2 + n*Q + 4*Q)/(2(n+1)(n+2)) >= 0`.

**Population = the GENUINE hard core:** trees with `min strDefect over roots > 0` — the defect-minimal
rootings, where a mere re-root cannot discharge `StraightStep_sized` and a real structural move is required.
This is the correct load-bearing population (a re-root IS a valid `StraightStep_sized`, so non-minimal
rootings are trivial). 504 genuine trees for `n <= 14`.

## Decisive results (n <= 14, 504 genuine trees)

| Move | Coverage | Notes |
|------|----------|-------|
| **(A) sibling-leaf FLP** — the *actual Lean cert* | **394 / 504 = 78.2%** | drop always exactly 1; **0 Aobj violations**; closed-form increment == direct cavity increment on every witness |
| **(B) broad size-1** — any pendant leaf onto any vertex | **495 / 504 = 98.2%** | |
| true whole-hub **Type-W** (needs moved size >= 2) | **9 / 504 = 1.8%** | the genuine residual |

**The 78% -> 98% gap is MOVE-GENERALITY, not population** (verified on the *same* genuine set). The 101
"B-but-not-A" trees are ALL discharged by relocating a pendant leaf onto **another BARE LEAF** (target
degree = 1 in **101/101** cases) — just a **non-sibling / distant** one (parent->target distance 2..7),
not a sibling of `u`. So the Type-L family is UNIFORM — *leaf-onto-leaf path-extension* — and splits:

- **sibling** (both leaves children of one node): **78.2%** — covered by the current Lean cert.
- **distant** (target leaf elsewhere in the tree): lifts coverage to **98.2%** — needs an EXTENDED cert
  (remove a leaf from `par_w` + attach under a distant leaf `v`; two local cavity effects, both leaf ops).
- **whole-hub Type-W** (moved size >= 2): **1.8%** — the genuine open core (Case-B, k-star relocation).

## Reconciliation with the prior "92% / 8%" figure

The earlier `a7_taxonomy` sweep reports Type-L ~92% because it measures a DIFFERENT thing: (i) over the
FIXED-rooting population (all rooted trees with `strDefect(root) > 0`, most discharged by re-root), and
(ii) with the BROADER classifier `minsz == 1` (any size-1 leaf relocation anywhere in the deepest-defect
subtree, i.e. move (B), not the sibling cert). Neither "92%" nor "8%" describes the *currently-proven*
Lean move. On the genuine core the honest split is **78 / 20 / 2** (sibling-FLP / distant-leaf / whole-hub).

## Soundness gates (all PASS -> GO)

- Aobj-decrease violations on sibling-FLP witnesses: **0** (every witness raises or ties `Aobj`).
- Closed-form increment `!=` direct cavity increment: **0** (the three cone-cert quantities
  `F2_num = n^2+nQ+4Q`, `P`, `Q` reproduce the exact `Aobj(after)-Aobj(before)` on every witness).
- `strDefect` drop histogram on Type-L witnesses: `{1: 394}` — always exactly 1 (Nat-recursion friendly).

## State of the Lean packaging (already done) and the true open residual

The local step is ALREADY packaged and kernel-clean in `R3Cert/BGSCLFlpStepAt.lean`:
- `FlpStepAt` — a depth-closed MULTI-flip sibling move class (completes `2m` sibling leaves -> `m` stems at
  one site in one composite step; `m=1` is the single sibling FLP).
- `FlpStepAt.props` / `FlpStepAt.straightStep` — every `FlpStepAt` step is a `StraightStep_sized`
  UNCONDITIONALLY (usize=, strDefect<, Aobj<=, all invariants), axiom-clean.
- `straightProgress_sized_of_coverage` / `hnorm_of_coverage` — reduce `StraightProgress_sized` (hence Hnorm)
  to a pure COVERAGE statement: exhibit `R` refining `StraightStep_sized` covering every positive-defect
  tree. (`FlpStepAt` refines it; the Lean comment measures its class at **52.4% of all trees, n<=12**.)

So **B1 (local step) is complete; the sole open piece of Hnorm is COVERAGE.** This B0 de-risk measures
exactly that coverage on the load-bearing genuine core and shows the path to close it:

1. `FlpStepAt` (sibling multi-flip) covers **78.2%** of the genuine core (n<=14) — consistent with the
   Lean's 52.4%-of-all-trees figure (different population).
2. **The highest-value next move class is the DISTANT leaf-onto-leaf extension** — target is ALWAYS a bare
   leaf (101/101), so it is the same path-extension G-machinery with a two-site (remove-leaf + extend-leaf)
   cavity increment. Adding it to `R` lifts coverage **78% -> 98%** of the genuine core.
3. The genuine whole-hub **Type-W** residual is then only **1.8%** (9 trees, n<=14) — the Case-B k-star
   relocation, the parity-blocked open core.

Recommended sequencing: build a `DistantLeafStepAt` move class (mirroring `FlpStepAt`, riding the same G1/G2
gains) + its coverage lemma -> union with `FlpStepAt` for `R` -> `hnorm_of_coverage` closes Hnorm modulo the
1.8% Type-W. That 1.8% is the residual to attack last (whole-hub, moved size >= 2).
