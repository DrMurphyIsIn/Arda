# Phase 3 design: the SPR de-branching move and its `Aobj`-monotonicity

## Context

The size-preserving tree→hub reduction (`R47R7Sized.tree_to_hub_sized`) rests on one obligation:

```lean
StraightProgress_sized := ∀ t, strDefect t ≠ 0 → ∃ t', StraightStep_sized t t'
StraightStep_sized t t' := usize t = usize t' ∧ Aobj t ≤ Aobj t' ∧ strDefect t' < strDefect t
```

Phase 0 (empirical, `PHASE0_STRAIGHTPROGRESS_FINDINGS.md`) established a strong GO: over all trees
`n ≤ 12` and all rootings (2438 non-backbone cases, 0 failures), a **single** SPR (subtree
prune-and-regraft) move — "pull an off-backbone branch onto the spine" — always exists, drops
`strDefect` by exactly 1, and **strictly** raises `Aobj` on every genuinely-structural case (30/30,
no ties). This doc scopes the Lean formalization of that move and its `Aobj`-monotonicity.

## The move (rooted-`UTree` form)

A defect (`strDefect > 0`) forces, at the deepest offending node, a child list with **≥ 2 non-piece
children** (`npCount cs ≥ 2`; a canonical backbone layer has ≤ 1, the tail). The witnessing move is
an SPR edge relocation `remove (u,v); add (a,b)` that reduces that node's non-piece count and pushes
the pruned branch toward the caterpillar/hub-backbone profile (a high-degree branch vertex sheds
degree; an interior spine vertex gains it). It is a **global vertex relocation**, not a single
child-replacement.

## Two isolated hard obligations

Phase 3 is a research-formalization campaign, not a single file. It decomposes into two genuinely
hard, independent obligations, plus tractable scaffolding.

### Obligation A — SPR `Aobj`-monotonicity (the Kelmans content)

`Aobj (spr-de-branch t) ≥ Aobj t`. This is the **Kelmans transformation's effect on the
matching/permanent partition function, for ARBITRARY trees**. Status of the surrounding literature
and repo:
- Csikvári proves the Kelmans transformation does not decrease the largest matching *root*, and GTS
  is monotone for many parameters — but **toward the star**, for the **unnormalized** `per(L)`. For
  the normalized `Aobj = per(L)/∏deg` the direction differs (the star ≈ minimum), so the literature
  does **not** supply this.
- The repo's own `kelmans_*.py` certs (cap-3/16 36-cell, vertex-budget) prove `Aobj`-monotone moves
  only on **backbone-form** states — never on arbitrary trees. Extending the cell-certificate method
  to the general de-branching move is new work.
- **Empirical margin (Phase 0):** strict on all 30 genuine cases, e.g. `n=10 Aobj 50/9 → 335/54`
  (`+35/54`). No boundary/equality edge case on the structural step.

The move is NOT a single `node_Ztot_child_mono` instance (it changes two child lists at once: remove
`B` from `N`, enrich a sibling/descendant). The proof needs the cavity effect of relocating a subtree
between a node and a deeper position — the core Kelmans computation. `R47R7DegMono.node_Ztot_child_mono_deg`
(degree-changing child monotonicity) is the propagation primitive; the local cavity inequality at the
relocation site is the missing cert.

### Obligation B — `Aobj` root-invariance (the address-graph iso)

The witnessing move uses re-rooting freedom (2138/2438 Phase-0 witnesses were reroot-only; the genuine
30 combine SPR + a rooting choice). `Aobj` root-invariance is **not proven**: `R47RootInvariance`
proves the *algebraic* engine (`permanent_submatrix_equiv`, `piRatio_eq_of_transport`,
`Aobj_root_invariant` **conditional** on a `GraphTransport` hypothesis) but leaves the *combinatorial*
seam — constructing, for two re-rootings of the same abstract tree, the vertex `Equiv` /
`SimpleGraph.Iso` transporting adjacency + degree — as a typed hypothesis. Discharging that seam is a
self-contained combinatorial obligation.

## Available infrastructure

- `R47R7DegMono.node_Ztot_child_mono_deg` / `Aobj_tail_child_replace_le_deg` (#173) — degree-changing
  child monotonicity (the up-propagation primitive).
- `R47R6SpineMono.Ztot_node_snoc` — the linear-nonnegative cavity decomposition.
- `R47RootInvariance` — the algebraic engine for Obligation B (needs the iso seam).
- `R47R7DeepPerm.deepPerm_Aobj` + `R47R7Sized.deepPerm_usize` — Aobj/usize invariance under child
  reordering (helps normalise the move's target order).
- `R47R7Decode` / `strDefect` machinery — the structural recognisers and defect accounting.

## Sub-plan (multi-PR campaign)

1. **Structural scaffolding.** Define the concrete `debranch : UTree → UTree` (relocate a chosen
   non-piece branch at the deepest offending node) and prove the *tractable* halves:
   `usize (debranch t) = usize t` (size-preservation) and `strDefect (debranch t) < strDefect t`
   (defect −1). Isolate `Aobj t ≤ Aobj (debranch t)` as the single remaining lemma → reduces
   `StraightProgress_sized` to Obligation A (+ B where re-rooting is used).
2. **Obligation B (root-invariance seam).** Construct the address-graph `SimpleGraph.Iso` for
   re-rooting and discharge `Aobj_root_invariant` unconditionally. Self-contained; unblocks the
   reroot witnesses.
3. **Obligation A (Kelmans cert).** The hard core. Attack the local cavity inequality for the
   relocation via the cell-certificate method (generalising the cap-3/16 approach from backbone
   states to the de-branch site), using `node_Ztot_child_mono_deg` for up-propagation. Likely its own
   multi-step campaign; Phase 0's strict margin says there is no equality edge case to guard.

## Honest assessment

Phase 3's two cores (A: general-tree Kelmans monotonicity; B: root-invariance combinatorial seam) are
**genuine research-formalization**, each plausibly several PRs. This is the same mathematical wall that
makes Brualdi–Goldwasser open — the reduction has faithfully pushed the whole tree→hub layer down to
exactly the Kelmans monotonicity + root-invariance, with all structural scaffolding (schema, decode,
deep-perm anchor, size-preservation, degree-changing propagation) already machine-checked. The next
concrete brick is sub-plan step 1 (structural scaffolding) which isolates Obligation A as a single
clean lemma. `conjecture1_proved = False`.
