# `hwh` status: the tree->cherry-backbone straightening (the open BG core)

**Date:** 2026-09-11  **Branch:** `bg/hnorm-multi-reformulation`  **Status:** `conjecture1_proved = False`.

## Where `hwh` sits

After the n=52 refutation and the broadened-capstone salvage, the entire BG reduction rests on ONE open
mathematical obligation (all connective steps kernel-checked):

```
conjecture1 (broadened)  <==  hwh  +  HdomMulti
                              │        └── HdomMulti: tie dominates every backbone of its size
                              │            (tautological for the multi-hub backbone argmax)
                              └── hwh: every reroot-minimal defective tree with no FlpStepAt site
                                  has a CoverR straightening move
      hwh  ==>  HnormMulti  ==>  conjecture1_of_HnormMulti_of_wholehub   (R47HnormMulti.lean)
```

`hwh` is equivalently: **every tree is `Aobj`-dominated by a hub-backbone (cherry-backbone) of its own
size** -- i.e. the per-size `Aobj`-maximizer over all trees is a multi-hub cherry-backbone. This is the
open Brualdi-Goldwasser structural core (Pant 2026).

## Empirical status: `hwh` HOLDS via local moves (exhaustive n<=14)

`proof/verification/hwh_viability.py` (reuses the `strDefect`/`Aobj`/SPR machinery of
`phase0_straightprogress_sized.py`, which mirrors the Lean `strDefect` in `R47R7Straighten.lean` and the
exact cavity `Aobj`). Question tested: for every rooted tree with `strDefect > 0`, is there a
SIZE-PRESERVING local move (SPR<=1 + free reroot) to a tree with strictly lower `strDefect` and `Aobj` not
decreased?

**Result: `viable_all = True` for ALL non-isomorphic trees n <= 14 (0 failures).** Iterating such moves
drives any tree to a hub-backbone without decreasing `Aobj`, so `hwh`/`HnormMulti` holds on this range.

## Why it is hard: the move is ADAPTIVE (no fixed-move certificate)

Move taxonomy over the viable moves (n<=14): **`to_maxhub: 165, other: 339`.** Only ~1/3 of the required
moves attach a piece to the max-degree hub; the other ~2/3 are heterogeneous SPR relocations. There is NO
single fixed structural move that is unconditionally `Aobj`-monotone (corroborating the prior finding that
the straightening "resists the averaging certificate"). The three formalized `CoverR` classes
(`FlpStepAt` ~88%, `AdjLeafStep`, `CompRerootStep`) cover ~99.3%; the residual needs an ADAPTIVELY chosen
move, which is exactly why `hwh` is not closed by a finite disjunction of fixed moves.

## Route-3 sharpening: the move class is PIECE / SUB-STAR RELOCATION (503/504)

`hwh_viability.py` further restricts the move and re-tests exhaustively (n<=14):
- **single-LEAF relocation** (detach one leaf, reattach elsewhere): viable for **495/504** defective trees.
- **single-PIECE relocation** (detach a leaf / cherry / arm-of-cherries, reattach its anchor): viable for
  **503/504**.

So the adaptive straightening move is NOT arbitrary -- it collapses almost entirely to a clean,
finitely-describable class (relocate a small piece). The SOLE exception up to n=14 is the **n=13
triple-3-star**: center vertex of degree 3 joined to three 3-stars (each a degree-4 vertex with 3 leaves),
`Aobj = 49/8`; `strDefect = 1`. A viable size-preserving move still exists there (relocate a whole 3-star
sub-arm: `Aobj 49/8 -> ~6.133`, defect 1->0), but the moved object is a 3-STAR (a vertex with 3 leaves),
one notch larger than an arm-of-cherries. So the covering menu up to n=14 is:
  { relocate a leaf | cherry | arm-of-cherries | small star } -- a finite family of piece-relocations.

This reduces the `hwh` proof to two concrete sub-problems:
1. **Piece-relocation monotonicity + destination rule.** For a piece relocation, `Aobj` changes by a
   computable amount (degree of the source hub drops by 1, the destination's rises by 1; `per(L)/prod deg`
   shifts accordingly). The open crux is a DETERMINISTIC destination rule provably giving `Aobj`-non-decrease
   whenever the move reduces defect -- the "adaptive" part is exactly the destination choice.
2. **Finite exceptional structures** (triple-3-star type) needing a sub-star relocation -- a separate,
   characterizable finite menu.

The three formalized `CoverR` classes already discharge `FlpStepAt` (~88%, the canonical leaf-path-extension),
`AdjLeafStep`, `CompRerootStep` (~99.3% total). The route-3 finding says the residual is covered by
piece/sub-star relocations -- so extending `CoverR` with a proven-monotone piece-relocation class (plus the
finite exceptional menu) is the concrete formalization path.

## The destination rule: deterministic, but its monotonicity is structure-coupled

Testing deterministic destination rules for leaf relocation (exhaustive n<=14, over the 497 trees with a
defect-reducing leaf move):

| rule | monotone fraction |
|------|-------------------|
| relocate to MAX receiving degree ("consolidate to the big hub") | 196/497 = 39.4% |
| relocate to MIN receiving degree (among defect-reducing) | **495/497 = 99.6%** |
| relocate maximizing source degree | 495/497 = 99.6% |
| any viable move exists | 495/497 = 99.6% |

So **min-receiving-degree EXACTLY matches "a monotone move exists"** -- it is the deterministic selector for
the leaf-relocation class (the naive consolidate-to-big-hub rule is wrong). The 2/497 residual trees have a
defect-reducing leaf move but no monotone one, and need a cherry/arm relocation instead.

But there is NO clean degree-only monotonicity lemma underneath it. The candidate universal lemma
"relocating a leaf to a strictly-lower-degree vertex never decreases Aobj" is **FALSE** -- 15522
counterexamples (n<=13); first at n=6: leaf moved from a degree-2 vertex onto a degree-1 leaf drops Aobj
3.5 -> 19/6. The min-degree rule works ONLY when combined with the defect-reduction constraint (which
restricts the destination to a consolidating position). So the monotonicity is genuinely COUPLED to the
structural defect condition -- it is not separable into a standalone degree inequality. This is exactly why
the straightening "resists the averaging certificate": the correct move is a deterministic function of the
tree (min-degree defect-reducing relocation), but proving its Aobj-non-decrease requires the joint
structure, not a local degree bound.

## Honest verdict / what a proof needs

`hwh` is strongly evidenced (exhaustive n<=14) but is the genuine open BG core. A proof needs a UNIFORM
existence argument: *for every non-backbone tree, some size-preserving `Aobj`-non-decreasing defect-reducing
move exists.* The obstruction to a fixed certificate is that the witnessing move depends adaptively on the
tree. Candidate proof strategies (all open):
- an exchange/potential argument bounding the `Aobj` change of the best defect-reducing relocation from
  below by 0 (the "averaging certificate" that empirically fails as stated -- needs a sharper potential);
- a structural induction peeling the deepest non-piece child, with an amortized `Aobj` accounting;
- identifying a FINITE menu of move classes whose union provably covers every tree (extending `CoverR`),
  with per-class monotonicity -- requires characterizing the ~2/3 "other" moves into clean classes.

No closure is claimed. `conjecture1_proved = False`.

## Reproduce

```
python3 proof/verification/hwh_viability.py                 # viability + move taxonomy, n<=14
python3 -c "import phase0_straightprogress_sized as P; P.analyze(n_max=13)"   # detailed per-tree moves
```
