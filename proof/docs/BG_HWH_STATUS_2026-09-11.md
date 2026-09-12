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

### General piece classes (cherry / arm / sub-star)

`hwh_piece_decomposition.py` + `R3Cert/R47HwhPieceDecomp.lean` extend the decomposition from a leaf to ANY
rigid piece `K` (anchor `c`, degree `dc`) via two cavity scalars `Z = Ztot(dtSub K)` and `rho = phi/dc`
(`phi` = matchings of `K` with `c` unmatched). Exact identity (verified 0 mismatches for leaf/cherry/arm-1..3;
kernel-clean `hwh_piece_decomp`):

```
(AobjAfter - AobjBefore) * a(b+1)
   = rho*(a-b-1)*P00 + (Z*(b+1)+rho*a)/(a-1)*P10 - (Z*a+rho*(b+1))/b*P01 - Z*(a-b-1)/(b*(a-1))*P11.
```

Leaf `Z=rho=1` recovers the `B1/B2` form (`hwh_piece_decomp_leaf`); cherry `Z=3/2, rho=1/2`; arm-`j`
`Z=(3/2)^j(1+j/(3(j+1))), rho=(3/2)^j/(j+1)`. NOTE: the clean `B2 >= 0` split is special to the leaf --
for a general piece the `P00,P11` coefficient needs `rho*(a-1)*b*P00 >= Z*P11` (for the cherry, a 3x
stronger bound that does NOT hold unconditionally), so monotonicity uses the full right-hand side
(`piece_move_monotone`). This extends coverage to all piece classes; the open core (`B1`-type existence)
is unchanged.

### Adjacent `p ~ w` case (mechanical coverage)

The leaf/piece decompositions above assume `p,w` non-adjacent. `hwh_adj_decomposition.py` +
`R3Cert/R47HwhAdjDecomp.lean` cover the ADJACENT case: `G = T - leaf` contains the edge `p-w`; a matching
using it contributes `Z(H) = P00` (before `P00/(ab)`, after `P00/((a-1)(b+1))`). Over the P-sums restricted
to matchings NOT using `p-w`:

```
(AobjAfter - AobjBefore) * a(b+1) = (a+b+1)*B1 + (a-b-1)*B2adj,   B2adj = P00 - (P00+P11)/(b(a-1)).
```

Verified exact (0 mismatches, 5940 adjacent leaf-moves). `B2adj >= 0` is provable (adjacent counting
`q != w, r != p` gives `P11 <= (a-2)(b-1) P00`, hence `P00+P11 <= (a-1)b P00`) -- 0 counterexamples.
Kernel-clean `hwh_adj_decomp`, `B2adj_nonneg`, `adj_move_monotone`. The open input is again `B1 >= 0`.

**Grid complete.** The adjacent GENERAL-piece case (`R3Cert/R47HwhAdjPieceDecomp.lean`, verified exact for
cherry/arm) folds the `Z,rho` piece scalars into the `p-w`-edge correction:

```
(AobjAfter - AobjBefore) * a(b+1)
  = (a-b-1)*(rho*P00 - Z*(P00+P11)/(b(a-1))) + (Z*(b+1)+rho*a)/(a-1)*P10 - (Z*a+rho*(b+1))/b*P01.
```

The full mechanical grid (leaf/piece x non-adjacent/adjacent) is now derived, exactly verified, and
kernel-clean: `R47HwhLeafDecomp`, `R47HwhPieceDecomp`, `R47HwhAdjDecomp`, `R47HwhAdjPieceDecomp`. Every
branch bottoms out at the same open input `B1 >= 0`.

## Research attempt on `B1` existence: every natural certificate FAILS

Attacking the `B1`-existence conjecture as a research problem, all standard certificate strategies were
tried and exhaustively falsified:

| strategy | result |
|---|---|
| degree-only lemma `deg_w < deg_p => Aobj nondecr` | FALSE (15522 counterexamples, first n=6) |
| deterministic rule: min receiving degree | monotone 99.6% but NOT a degree-certifiable fact |
| deterministic rule: max-degree source forces `B1>=0` | FALSE (29/369; existence fails on 14 trees) |
| "any lower-degree defect-reducing move is monotone" | FALSE (233/3662 decrease `Aobj`) |
| **averaging certificate** `sum_moves B1 >= 0` (=> some move has `B1>=0`) | holds n<=12 (30/30) but **FAILS at n=13 (4/131)** |

The averaging certificate failing precisely at n=13 (the triple-3-star obstruction) is the crux: the
straightening genuinely "resists the averaging certificate," so a proof of `B1` existence cannot come from
degrees, a fixed rule, or a uniform average -- it needs per-structure reasoning that handles the triple-3-star
family. This is a NEGATIVE result: the natural certificates provably do not suffice, so closing `hwh`
requires a genuinely different idea (a correlation/FKG inequality on the matching measure, or a Kelmans-type
structural induction). The conjecture remains open; no closure is claimed.

## Partial progress toward closing the core (2026-09-12)

Two honest, kernel-clean partial advances (neither claims the full `B1`):

**(1) `B1 >= 0` on a structural slice** (`R3Cert/R47HwhB1Partial.lean`). When the target `w` has no
neighbours in `H` (`P01 = 0` -- e.g. `w` a degree-1 vertex adjacent to `p`), `B1 = P10/(a-1) >= 0`
outright (`B1_nonneg_of_P01_zero`). The canonical instance is the CHERRY-FORMING move (relocate a leaf
onto an adjacent sibling leaf, `b=1`, `p~w`): there `P01 = P11 = 0`, so `B1 >= 0` and `B2adj =
P00(a-2)/(a-1) >= 0` UNCONDITIONALLY, hence the move never decreases `Aobj` (`cherry_forming_monotone`;
verified 0 decreases / 3230 moves). A fully-proven slice of the open straightening.

**(2) The `B2` matching-sum lemma, from an actual matching theory** (`R3Cert/R47MatchingSum.lean`). A
self-contained weighted-matching-sum theory `Zsum`/`ZsumAvoid` DISCHARGES the essential content of the
`B2` hypothesis rather than assuming it: `ZsumAvoid_antitone` (deletion monotonicity -- avoiding more
vertices never increases the nonneg-weighted matching sum, since those matchings are a subfamily),
`B2_termwise` (`Z(H-q-r) <= Z(H)`), `B2_bound_of_terms` (a sum of `<= K` terms, each a coefficient in
`[0,1]` times a value `<= P00`, is `<= K*P00`). `B2_bound` COMPOSES these into the actual inequality: with `P00 := ZsumAvoid {p,w}` and
`P11 := sum_{(q,r) in pairs} (1/deg_q)(1/deg_r) ZsumAvoid {p,q,w,r}` and degrees `>= 1`,

    P11 <= pairs.card * P00,

which is `P11 <= (a-1)b P00` once `pairs.card <= (a-1)b`.  So the `B2` HYPOTHESIS of `R47HwhLeafDecomp`
is now a THEOREM over the matching theory -- no longer assumed.  The only residual is the DEFINITIONAL
identification that the marked-vertex matching-classified `P00,P11` equal these `ZsumAvoid` expressions
(the matchings-using-a-fixed-edge <-> matchings-of-the-rest bijection) -- standard matching combinatorics,
and the separate cavity-`Aobj` <-> matching-sum bridge.  The mathematical content of `B2` (deletion
monotonicity + counting) is proven, not hypothesized.

## Next step on the general kernel: g-DOMINANCE (2026-09-12)

Using `B1 = avg_{q~p} g(q) - avg_{r~w} g(r)` (`g(v) = Z(H-v)/deg_v`), a proven sufficient condition
strictly broader than the `P01=0` slice (`R47HwhB1Partial.B1_nonneg_of_gdominance`):

> if there is a threshold `M` with `g(q) >= M` for every `p`-neighbour `q` and `g(r) <= M` for every
> `w`-neighbour `r`, then `avg_{q~p} g >= M >= avg_{r~w} g`, hence `B1 >= 0`.

Kernel-clean averaging argument. Verified: g-dominance => B1 >= 0 (sound, 106/106); non-vacuous (covers
~69% of defect-reducing lower-degree leaf moves; EVERY defective tree tested has >= 1 g-dominant
straightening move). This SHARPENS the open kernel from "does a `B1 >= 0` move exist" to the concrete,
checkable:

> **(sharpened hwh kernel)** does every non-backbone tree admit a defect-reducing, strictly-lower-degree
> move that is g-DOMINANT (`p`'s neighbours `g`-dominate `w`'s, `g(v)=Z(H-v)/deg_v`)?

Still open, but now a threshold/level-set statement about a local matching functional -- a more tractable
target than the raw average comparison (it removes the averaging and asks for a clean level-set separation).

**Testing the sharpened conjecture (n<=14): g-dominant-move EXISTENCE FAILS on a small symmetric residual.**
Exhaustive check of "does a g-dominant defect-reducing lower-degree leaf move exist":
- non-adjacent moves only: fails on 21/504 defective trees;
- allowing adjacent moves too: fails on **9/504** trees.
The 9 survivors are exactly the highly-symmetric high-degree multi-hubs -- the triple-3-star family and
kin (`[4,4,4,3,...]`, `[4,4,4,4,...]`, `[5,4,4,3,...]`, `[3,2,2,...,2,...]`). So g-dominance is a genuine
sufficient condition covering ~98% of trees (all but 9 at n<=14), but it does NOT close the kernel: those 9
symmetric trees have `B1 >= 0` only via the raw AVERAGE (not a level-set separation), which is the
irreducible open core. This precisely localizes the remaining difficulty to a small, sharply-characterized
symmetric family -- the same obstruction that broke the averaging certificate at n=13.

## The kernel localizes to ONE explicit tree family (2026-09-12)

Classifying the 9 g-dominant-leaf failures by whether a monotone PIECE (sub-star) move covers them:
**8 of 9 have a monotone piece move**; the sole survivor at n<=14 is the **n=13 triple-3-star**
(`[4,4,4,3,...]`: a degree-3 centre joined to three degree-4 hubs, each with 3 leaves; `Aobj = 49/8`).

So the certificate stack -- g-dominant leaf moves (~98%) + piece/sub-star moves -- covers 503/504 defective
trees at n<=14. The entire open kernel localizes to the **balanced multi-3-star family** (the triple-3-star
and its size-`n` generalizations): the unique structure where every certificate to date (degree,
min-degree, max-source, averaging, g-dominance, and the restricted piece search) breaks. Note `hwh` HOLDS
for the triple-3-star (a monotone straightening move exists -- its specific sub-star relocation, part of
the exhaustive `viable_all = True` verification); what is open is a UNIFORM certificate that works for the
whole symmetric family without per-tree case analysis.

**This is the honest end state of the localization:** the open Brualdi-Goldwasser kernel, after the full
reduction + decomposition + `B2` + matching theory + `B1` slices + g-dominance, is exactly the
symmetric-multi-star obstruction -- a single, sharply-characterized family. Proving the uniform certificate
for it is the genuine open research problem; every member is individually monotone (verified), but no
tool developed here certifies the family uniformly. `conjecture1_proved = False`.

## UNIFORM CERTIFICATE for the symmetric-multi-star family (2026-09-12)

The localized obstruction -- the balanced multi-star `ST(k,m)` (centre degree `k`, `k` hubs each with `m`
leaves; includes the triple-3-star `ST(3,3)`) -- is now handled UNIFORMLY, kernel-checked
(`R3Cert/R47HwhSymStarCert.lean`, `symstar_uniform_cert.py`).

Closed forms (verified exact against the cavity engine): `Aobj(ST(k,m)) = 2*alpha^(k-1)`,
`alpha=(2m+1)/(m+1)`; the DE-BRANCHING move (detach an arm, re-attach it as a pendant path via a leaf-leaf
edge) gives `Aobj(ST_move) = tau2*alpha^(k-2) + (nu2*alpha^(k-2)+(k-2)tau2*alpha^(k-3))/((k-1)(m+1))` with
`tau2=(20m^2-2m-1)/(4m(m+1))`, `nu2=(10m-3)/(4m)`. Monotonicity `Aobj(ST_move) >= Aobj(ST)` reduces (factor
`alpha^(k-3)>0`, clear `(k-1)(m+1)>0`) to

    F_num(k,m) = (k-3)*(2m+1)(4m^3+2m^2-7m-1) + (2m+1)(8m^3+4m^2-11m-3) >= 0,   linear in k.

Both cubics are positive for `m>=2` (shift `m=t+2`: `4t^3+26t^2+49t+25`, `8t^3+52t^2+101t+55`, all
coefficients `>0`) and `k>=3`, so `F_num >= 0` -- `symstar_move_certificate` (kernel-clean). Hence the
de-branching move is `Aobj`-monotone on the ENTIRE balanced multi-star family, so this symmetric obstruction
is uniformly NOT a counterexample to `hwh` -- the family the averaging/g-dominance certificates could not
reach is now closed by an explicit Positivstellensatz certificate (shifted nonneg-coefficient positivity,
Telperion-shaped).

**Non-balanced extension (3-hub), 2026-09-12** (`R3Cert/R47HwhSymStar3Cert.lean`): the full 3-hub family
with ARBITRARY hub sizes `m1,m2,m3 >= 2` is now certified. The de-branching move (detach hub1 onto hub2,
spectator hub3) gives `Aobj(MS_move)-Aobj(MS) = N(m1,m2,m3)/(12 m1(m1+1)(m2+1)(m3+1))` (closed form verified
exact), and under `m_i = t_i+2` the numerator `N` has ALL NON-NEGATIVE COEFFICIENTS (constant term 495), so
`N >= 0` -- `symstar3_move_certificate` (kernel-clean). This covers the non-balanced symmetric residual
variants (`[4,3,3]`, `[5,4,4]`, `[5,3,2]`, ...) at hub-count 3, not just the balanced `ST(3,m)`.

Remaining scope: balanced `ST(k,m)` (all `k`) + general 3-hub are certified. General non-balanced `k >= 4`
follows the same de-branching move + shifted-nonneg-coefficient method (the move is verified monotone on all
non-balanced multi-stars tested); its `k`-uniform closed form is the natural next increment.

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
