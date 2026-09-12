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

## Cracking the nut: an exact analytic decomposition of the leaf-move `Aobj` change

`hwh_leaf_decomposition.py` derives and verifies (exact `Fraction`, 0 mismatches / ~13000 moves) the exact
change in `Aobj` under a leaf relocation. Tree `T`, leaf `l` with neighbor `p` (deg `a`), relocate to a
non-adjacent `w` (deg `b`); `T'` has `deg(p)=a-1`, `deg(w)=b+1`. Let `G = T - l`; classify matchings of `G`
by whether `p`/`w` are matched, with the `p`,`w` degree factors removed from the weights:
`P00, P10, P01, P11`. Then

```
(Aobj(T') - Aobj(T)) * a(b+1) = (a+b+1)*B1 + (a-b-1)*B2,
   B1 = P10/(a-1) - P01/b ,   B2 = P00 - P11/(b(a-1)).
```

This turns the "resists a certificate" monotonicity into three checkable pieces:
1. **`B2 >= 0`** in the regime `b <= a-1` -- a CLEAN universal matching-sum inequality, **0 counterexamples**
   (exhaustive n<=11). Provable (a negative-association / stability statement for matchings). ONE PIECE DONE.
2. **`a - b - 1 >= 0`** (the move goes to strictly-lower degree) -- holds for the min-degree defect-reducing
   selection; a defect-reducing leaf move with `b <= a-1` EXISTS for every defective tree except the n=13
   triple-3-star.
3. **`B1 >= 0`** under the min-degree defect-reducing selection -- the REMAINING OPEN CORE. `B1` is NOT a
   degree-only fact (it fails for leaf-onto-leaf `a=2,b=1`), so its non-negativity is coupled to the defect
   structure. This is the sharp residual of the leaf case.

Given (1) `B2 >= 0` and (2) `a-b-1 >= 0`, monotonicity `ΔAobj >= 0` follows once `(a+b+1)*B1 >= -(a-b-1)*B2`
-- in particular once `B1 >= 0`. So the leaf-case nut is reduced to the single matching inequality `B1 >= 0`
under the min-degree defect-reducing move (the cherry/arm/sub-star classes still need their own analogous
decomposition). This is genuine progress -- an exact analytic handle and one proven lemma -- but NOT a
closure; `B1`'s structural guarantee is the open core.

## (a) `B2` PROVEN; `B1` characterized

Writing `H = G - p - w` and `Z(.)` for the reduced matching sum, the P-sums factor as
`P00 = Z(H)`, `P10 = sum_{q~p} (1/deg_q) Z(H-q)`, `P01 = sum_{r~w} (1/deg_r) Z(H-r)`,
`P11 = sum_{q~p, r~w, q!=r} (1/deg_q)(1/deg_r) Z(H-q-r)` (verified exactly, 0 mismatches).

**`B2 >= 0` is PROVEN (universal, any a>=2, b>=1).** For each pair `(q,r)`, `Z(H-q-r) <= Z(H) = P00`
(matchings of `H-q-r` are a subset of those of `H`, positive weights) and `1/deg_q, 1/deg_r <= 1`; there are
`<= (a-1) b` pairs, so `P11 <= (a-1) b P00`, i.e. `B2 = P00 - P11/(b(a-1)) >= 0`. Confirmed with 0
counterexamples WITHOUT the `b <= a-1` restriction.

**`B1` characterized.** With `g(v) := Z(H-v)/deg_v`, `B1 = P10/(a-1) - P01/b = avg_{q~p} g(q) - avg_{r~w}
g(r)`. So `B1 >= 0` iff `p`'s neighbours have at least the average matching-connectivity `g` of `w`'s
neighbours. This is the exact sharp residual: the min-degree defect-reducing move must send the leaf to a
`w` whose neighbourhood is no better-connected (in `g`) than `p`'s. Not a degree-only fact; genuinely
structural -- the open core, now precisely a neighbourhood-average comparison of a local matching functional.

### The residual as an EXISTENCE statement (cleaner target)

Rather than pin a specific selection rule, the leaf case reduces to: *every non-backbone tree has SOME
leaf move that is defect-reducing, to strictly-lower degree (`b <= a-1`), with `B1 >= 0`.* With proven
`B2 >= 0`, any such move is `Aobj`-monotone. Exhaustive check (n<=12): this existence holds with **0
failures** (30/30 non-backbone trees), except the finite sub-star exceptions (n=13 triple-3-star) which
need a cherry/arm/sub-star move of the same form. So the sharp remaining conjecture for the leaf case is:

> **(hwh leaf conjecture)** Every non-backbone tree (outside finite sub-star exceptions) admits a
> defect-reducing strictly-lower-degree leaf move with `avg_{q~p} g(q) >= avg_{r~w} g(r)`
> (`g(v)=Z(H-v)/deg_v`).

This is strongly evidenced but unproven -- it is the open Brualdi-Goldwasser structural core, now stated as
a concrete neighbourhood-matching existence claim.

## (b) Lean scaffolding

`R3Cert/R47HwhLeafDecomp.lean` (kernel-clean) formalizes the algebra and the monotonicity criterion over
abstract nonnegative reals `P00,P10,P01,P11`:
- `hwh_leaf_decomp` -- the exact identity `(AobjAfter - AobjBefore) * (a*(b+1)) = (a+b+1)*B1 + (a-b-1)*B2`.
- `B2_nonneg_of_dom` -- `P11 <= (a-1)*b*P00 => 0 <= B2` (the proven combinatorial bound as hypothesis).
- `leaf_move_monotone` -- from `0 <= B1`, `P11 <= (a-1)*b*P00`, and `b+1 <= a`: `AobjBefore <= AobjAfter`.

The matching-sum inputs (that `AobjBefore/After` equal the P-expressions, and `P11 <= (a-1)b P00`) are the
hypotheses -- proven on paper in (a); a full Lean discharge needs a weighted-matching theory bridged to the
cavity `Aobj`, which is future work. conjecture1_proved = False.

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
