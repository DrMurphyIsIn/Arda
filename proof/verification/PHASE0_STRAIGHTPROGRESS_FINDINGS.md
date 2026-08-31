# Phase-0 de-risk: is `StraightProgress_sized` locally dischargeable?

**Verdict: LOCAL-MOVE VIABLE.**

Exhaustive over all non-isomorphic unrooted trees on `n = 2..12` vertices, under **all**
rootings (root at each vertex). Exact rational arithmetic (`fractions.Fraction`);
`Aobj = per(L)/prod deg` computed via the matching-sum identity reused from
`kelmans_mixed_load.pi_literal` (itself anchored against a brute-force permanent).
Script: `proof/verification/phase0_straightprogress_sized.py`.

## The obligation

For every rooted tree `t` on `n` vertices with `strDefect(t) > 0` (a non-backbone
rooting), does there exist another rooted tree `t'` on the **same** `n` vertices,
reachable by a **local** move (SPR distance <= 1, plus free re-rooting), with

    strDefect(t') < strDefect(t)   AND   Aobj(t') >= Aobj(t) ?

Iterating drives `strDefect` to 0 (a hub-backbone) without decreasing `Aobj`.

## Results

| n | nonisom. trees |
|---|---|
| 2..6 | 1,1,2,3,6 |
| 7 | 11 |
| 8 | 23 |
| 9 | 47 |
| 10 | 106 |
| 11 | 235 |
| 12 | 551 |

- **Non-backbone rooted trees tested (strDefect>0): 2438** (cumulative n<=12).
- **Failures: 0.** A witnessing local move exists in *every* case.
- Witness `strDefect` drop: **always exactly 1** (histogram `{1: 2438}`). The move is a
  single straightening step, never a multi-step jump. This matches a Nat-recursion on
  `strDefect` in Lean.
- Aobj on the witness: **300 strict increases, 2138 ties.** Ties are all `reroot_only`
  moves (same graph, `Aobj` identical by root-invariance).

### The decisive subset: genuinely non-backbone graphs

A tree is *genuinely* non-backbone iff **no** rooting achieves `strDefect = 0`. These
are the only cases that a mere re-root cannot discharge — they need a real structural
(SPR) move. They first appear at **n = 10**.

- Genuine non-backbone graphs tested: **30** (n<=12; first at n=10).
- **Genuine failures: 0.**
- Witnessing SPR moves on the genuine subset: **30 strict `Aobj` increases, 0 ties.**
  Every genuine straightening move *strictly* raises `Aobj`. No tie ever occurs where a
  real structural change is required.

## Witnessing move family

Across all genuine cases the witness is a single **subtree-prune-and-regraft (SPR)**
step: remove one edge and reattach the pruned component by one new edge to a vertex of
the other component (`spr` = 30, `spr_plus_reroot` = 270 counting per-rooting variants).
Structurally it is exactly the "relocate an off-spine branch / de-branch a high-defect
node onto the backbone" straightening move — the degree sequence consistently moves
*toward* a caterpillar/hub-backbone profile (a high-degree branch vertex loses degree,
an interior spine vertex gains it), e.g.

    n=10  remove (0,1) add (1,2)   degseq [3,3,3,3,1,1,1,1,1,1] -> [3,3,3,2,2,1,1,1,1,1]
          Aobj 50/9 -> 335/54   (delta = +35/54)   defect 1 -> 0

    n=11  remove (0,1) add (0,6)   degseq [3,3,3,3,2,...] -> [3,3,3,2,2,2,...]
          Aobj 530/81 -> 361/54  (delta = +23/162)  defect 1 -> 0

    n=12  remove (0,1) add (3,7)   degseq [3,3,3,3,3,1,...] -> [3,3,3,2,2,2,2,1,...]
          Aobj 1910/243 -> 211/24 (delta = +1811/1944) defect 1 -> 0

## Implications for the Lean formalization

1. **`StraightProgress_sized` IS locally dischargeable.** No stuck configuration needs a
   global / multi-hub / vertex-budget fallback anywhere up to n=12. The straightening
   half can be a single local step + Nat-recursion on `strDefect` (each step drops it by
   exactly 1).
2. **The move to formalize is a single SPR (prune-and-regraft) step** that pulls an
   off-backbone branch down onto the spine, reducing the count of non-piece children at
   the deepest offending node. The de-branching directions match a Kelmans-style
   edge relocation toward the caterpillar/hub-backbone shape.
3. **Monotonicity is genuinely strict on the structural cases** (30/30 strict `Aobj`
   increase); ties only arise from the trivial reroot-only moves where the graph is
   unchanged. So the `Aobj(t') >= Aobj(t)` inequality is safe (never violated) and is in
   fact strict whenever a real move is needed — a comfortable margin for the Lean
   inequality bricks (no boundary/equality edge case to guard on the structural step).

## Scope / bound

Exhaustive and exact through **n = 12** (551 unrooted trees at n=12; ~14 s runtime,
2438 non-backbone rootings, 30 genuine structural cases). No failures at any size. This
is empirical evidence, not a proof, but it is a strong GO signal: the local move is
viable and its family is identified.
