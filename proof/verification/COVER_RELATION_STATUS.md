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

## UPDATE (2026-09-11): `hcore` splits by "has a `FlpStepAt` site" — path (a) is the CONSTRUCTOR, not a theorem

The residual is characterized EXACTLY: all 125 (reroot-minimal defective, no `FlpStepAt` site, n≤12) have a
BRANCHING node (≥2 non-piece non-cherry children) and `strDefect = 1`.  The distinguishing marker is precisely
"∃ `FlpStepAt` site".  So `hcore` splits by excluded middle on that marker:
- **has-site → `FlpStepAt` fires** — this is just the `FlpStepAt.here` CONSTRUCTOR (+ `.lift` to embed).
  MECHANICAL — there is no hard "88.4% structural theorem"; that fraction is exactly "has a site", and for
  those the move exists by construction.
- **no-site → the whole-hub (Case-B) move** — the residual (a branching-defect tree), needing the
  Aobj-nondecreasing de-branch/Case-B move.

**So `hcore`'s ENTIRE non-mechanical content is the whole-hub.**  The proof of Conjecture 1 reduces to ONE
genuine research lemma:

> **(whole-hub)** A reroot-minimal defective tree with NO `FlpStepAt` site (∴ a branching-defect / whole-hub
> form; all such have `strDefect = 1`) admits an `Aobj`-nondecreasing, `strDefect`-reducing move — the
> Case-B / de-branch relocation.

This move's `Aobj`-monotonicity fails the local `G1` lift-gain (`REALOBLB_TYPEW_B0_FINDINGS.md`), so it needs
the GLOBAL monomer-dimer / Heilmann-Lieb argument (foundation: `Aobj = Σ_matchings ∏ 1/(d_u d_v)`,
`AOBJ_MATCHING_POLYNOMIAL_REFORMULATION.md`; the isolated symmetric base is already proven Aobj-neutral in
`BGSCLRealOblBSymBase.lean`).

## CORRECTION (2026-09-11): what `hcore` actually reduces, and the SECOND open Hnorm layer

Verified by type-checking (`conjecture1_of_Hnorm (hnorm_of_coverR_coverage hcov)` FAILS): my `CoverR` /
`CompRerootStep` / `hcore` chain feeds **`tree_to_hub_sized`**, whose output is
`∃ s, usize(backboneU s) = usize t ∧ Aobj t ≤ Aobj(backboneU s)` — a **general** backbone (usize-shape).
The well-posed capstone `conjecture1_of_layers_fixedN` needs
`∃ s, Balanced s ∧ Capped s ∧ stateSize s = usize t ∧ Aobj t ≤ Aobj(backboneU s)` — i.e. the witness must ALSO
be **Balanced** (arms ∈ {4,5}) and **Capped** (≥5 arms/hub).  `usize_backbone` bridges usize↔stateSize, but
NOTHING here upgrades a general backbone to Balanced+Capped.

**So the earlier claim "Conjecture 1 rests on `hcore` alone" was INCORRECT.**  There are (at least) TWO open
`Hnorm` layers:

1. **Size-preserving coverage** (tree → general defect-0 backbone): reduced — kernel-clean — to `hcore`,
   which splits into the `FlpStepAt` constructor (has-site) + the whole-hub Case-B residual (no-site).  This
   is the genuine, real progress of this branch.
2. **The Balanced+Capped normalization** (general backbone → Balanced+Capped hub-state, size-preservingly and
   `Aobj`-non-decreasingly = arm-balance to load 4/5 + de-load/cap to ≥5 arms).  This is a SEPARATE layer,
   NOT provided by `tree_to_hub_sized` (general backbone) NOR by `hnorm_of_rewrite` (Balanced+Capped but
   size-CHANGING, so it feeds only the ill-posed single-tie `conjecture1_of_layers`).  Per the program
   history this is the genuinely-hard "cross-boundary / aligned-n" residual.

## CORRECTION 2 (2026-09-11): the capstone `Hnorm` is ALIGNED-N scoped — unsatisfiable for small/non-aligned n

A Balanced+Capped hub-state has `hubSize = 1 + 11a + 9b + 2c` per hub (a load-5, b load-4 arms) with
`a+b ≥ 5` (Capped) — so the **minimum Balanced+Capped state size is 46**.  Checked: of the sizes `n ≤ 70`,
**48 have NO Balanced+Capped hub-state** (all of 2..45, plus 47, 49, 51, 53).  For those `n`, the capstone's
`Hnorm` (`∃ Balanced+Capped s, stateSize s = usize t ∧ ...`) is **UNSATISFIABLE** — the hypothesis of
`conjecture1_of_layers_fixedN` cannot be provided.

So the capstone reduction is inherently **aligned-n scoped**: it can only prove Conjecture 1 for `n` where a
Balanced+Capped state exists (n≥46, specific residues).  Small and non-aligned `n` are a SEPARATE residual
(finite check for small n + the non-aligned-n layer) — the program's known "aligned-n scoping / off-lattice
tie is a placeholder" open item.  My recent summaries ("Conjecture 1 rests on `hcore`/`Hnorm`") glossed over
this; the honest statement is "Conjecture 1 FOR ALIGNED n rests on the aligned `Hnorm`".

## Status (fully corrected)

`Hdom`: CLOSED (kernel-clean).  `Hnorm` is genuinely reduced ONLY for the size-preserving-general-backbone
target (`tree_to_hub_sized`, my `CoverR`/`hcore` work — real, kernel-clean).  Reaching the WELL-POSED capstone
needs, beyond `hcore`: **(ii)** the Balanced+Capped size-preserving normalization, AND is inherently
**aligned-n scoped** (Hnorm unsatisfiable off-lattice / for n<46).  So Conjecture 1 rests on: `hcore`/whole-hub
+ Balanced+Capped normalization + the aligned-n scoping (small/non-aligned n separate).  NOT `hcore` alone,
NOT even a single extra layer.  `conjecture1_proved = False`.
