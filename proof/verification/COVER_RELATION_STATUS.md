# `Hnorm` coverage status: `CoverR` map + the two remaining pieces

`Hnorm` is reduced (kernel-clean, `R47CoverRelation.hnorm_of_coverR_coverage`) to ONE obligation:
`∀ t, strDefect t ≠ 0 → ∃ t', CoverR t t'`, where `CoverR = FlpStepAt ∪ AdjLeafStep` (both proven to refine
`StraightStep_sized`).  This note measures exactly how far `CoverR` gets and pins what remains.

## Coverage measurement (rooted trees, the `StraightProgress_sized` population, n ≤ 12)

Over all **19,099** rooted defective trees (`strDefect(root) > 0`), with the EXACT Lean move conditions:
- `FlpStepAt` fires at a node with a child `node(perm(2m≥2 leaves ++ all-cherry crest))` and a non-piece
  sibling (`1 ≤ npCount` of the other children);
- `AdjLeafStep` fires at a node with a bare-leaf child and a child `node(flpLeaf :: nonempty-cherries)` and
  `1 ≤ npCount Other`.

| coverage | fraction |
|---|---|
| **`CoverR` fires directly** (FlpStepAt or AdjLeafStep) | **62.7%** (11,966) |
| **`CoverR` OR a reroot lowers defect** | **99.3%** (18,974) |
| **residual** (neither `CoverR` nor reroot) | **0.7%** (125) |

The residual is unmistakable — e.g. `((),(),(node(3-star, 3-star)))`: a node carrying two equal `k`-stars,
the **symmetric whole-hub (Case-B)** family.

## The two remaining pieces (in priority order)

### 1. A `RerootStep` class: 62.7% → 99.3%
A re-rooting to a lower-`strDefect` rooting is a valid `StraightStep_sized` (same vertices ⇒ `usize` equal;
`Aobj` is a graph invariant ⇒ equal; `strDefect` lower).  Adding it to `CoverR` jumps direct coverage to
**99.3%**.  Feasibility: the root-invariance CAPSTONE exists (`BGSCLObligationB.Aobj_root_invariant_of_iso`,
engine `R47RootInvariance` — `per(lapl)/∏deg` is a vertex-labeling invariant), but producing the concrete
`SimpleGraph.Iso` for a specific SPR re-rooting (and defining the reroot on `UTree` + the `strDefect`-drop
selection) is genuine downstream infrastructure, not a one-liner.  This is the highest-leverage next build.

### 2. The whole-hub (Case-B) residual: the last 0.7%
The 125 residual trees are the symmetric/asymmetric two-`k`-star family.  Their `Aobj`-monotone straightening
move fails the local `G1` lift-gain (`REALOBLB_TYPEW_B0_FINDINGS.md`): the whole-hub relocation lowers the
acted node's `Ztot(dtSub)`, so it cannot lift context-independently.  Closing it needs a GLOBAL monomer-dimer
inequality (the `Aobj = Σ_matchings ∏ 1/(d_u d_v)` reformulation is the foundation;
`AOBJ_MATCHING_POLYNOMIAL_REFORMULATION.md`).  Genuine open research.

## UPDATE (2026-09-10): RootShiftStep folded in — `CoverR` is now 3 classes

`CoverR := FlpStepAt ∨ AdjLeafStep ∨ RootShiftStep` (all three proven `StraightStep_sized`, kernel-clean).
`RootShiftStep` = the single-edge root-shift `node(node ds :: rest) → node(ds ++ [node rest])` when it lowers
`strDefect` (`Aobj` equal by `Aobj_rootShift` — proven directly in the cavity model, NO graph-iso; `usize`
equal).  Coverage with the single-shift reroot: **89.6%** (rooted defective, n<12) vs 67.3% for
`FlpStepAt ∨ AdjLeafStep`.

**DONE (2026-09-10):** `CompRerootStep` — the COMPOSITE reroot — is built and folded in:
`CoverR := FlpStepAt ∨ AdjLeafStep ∨ CompRerootStep`.  `RerootRel := ReflTransGen` of {single shift-to-front
∨ child-permutation} reaches ANY rerooting; `Aobj`/`usize` are invariant by composition (`Aobj_rootShift` +
`Aobj_node_perm`); `CompRerootStep := RerootRel ∧ strDefect drops` is a `StraightStep_sized`.  So `CoverR`
now covers the full **99.3%** (every 'a reroot lowers defect' tree + the two direct classes), leaving only
the **0.7%** whole-hub (Case-B) core.

## UPDATE (2026-09-11): coverage reduced to the reroot-minimal core; `hcore` characterized exactly

`coverR_coverage_of_minimalCore` (kernel-clean) discharges the reroot half with NO path construction:
`Hnorm ⟸ hcore`, where **`hcore` := every reroot-minimal defective tree has a `FlpStepAt`/`AdjLeafStep` move**
(`RerootMinimal t := ∀ t', RerootRel t t' → strDefect t ≤ strDefect t'`).  So the WHOLE proof of Conjecture 1
now rests on the single obligation `hcore`.

`hcore` characterized exactly (reroot-minimal defective trees, n≤12, 1079 of them):
- **`hcore` holds for 88.4%** (954) — ALL via `FlpStepAt`.
- **residual 11.6%** (125, all first at n=12) — the whole-hub family `((),(),(node(X,Y)))` (root = two leaves +
  a node with ≥2 non-piece children); needs the whole-hub (Case-B) move.
- **`AdjLeafStep` fires 0%** on the reroot-minimal core — it is REDUNDANT for `hcore` (`FlpStepAt` subsumes it
  there; the earlier "+20 trees" was on the looser min-over-roots measure).  It remains a valid, correct class
  but is not load-bearing for `hcore`.

So `hcore` sharpens to: **"every reroot-minimal defective tree has a `FlpStepAt` move, EXCEPT the whole-hub
Case-B family."**  Two genuine paths remain: (a) prove `FlpStepAt` coverage of the non-whole-hub
reroot-minimal trees (structural, a6-locality-adjacent — the 88.4%); (b) the whole-hub Case-B move for the
11.6% residual (global monomer-dimer / Heilmann-Lieb — the one true open research nut).

## Status

`Hnorm` reduced (kernel-clean) to `hcore` — a single structural obligation on reroot-minimal defective
trees.  `hcore` = `FlpStepAt` coverage (88.4%, structural) + the whole-hub Case-B residual (11.6%, the open
research problem).  `conjecture1_proved = False`.
