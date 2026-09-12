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
