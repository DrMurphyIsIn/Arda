# BG `hwh` / HnormMulti at larger n (2026-09-24)

Script: `proof/verification/hwh_coverage_large_n.py` (commands in its docstring). Exact `fractions.Fraction`
for every claim below; floats appear only as a prefilter in the coverage/search code and every failure or
witness is re-decided exactly. `conjecture1_proved = False`.

## Summary

1. **HnormMulti holds, exhaustively and exactly, for every n <= 100.** For each n in 4..100 the maximum of
   `Aobj` over ALL n-vertex trees equals the maximum over backbones (minDefect 0), and every maximizer is a
   backbone. This is an exact exhaustive computation, not a search (method below), cross-checked against
   brute-force enumeration of all trees and of all backbones for every n <= 18.
2. **The single-SPR coverage test from `hwh_viability.py` is exhaustively clean for n <= 23 but FAILS at larger
   n.** The smallest failure found is at n = 25 (exact, and confirmed by the repo's independent networkx engine).
   n = 24 has not been run exhaustively. Many more failures show up for n = 25..64. Every failure has minDefect 1
   and sits at 75-87% of the best backbone of its size. So these break the local-move proof route only. They are
   not counterexamples to HnormMulti, and not to the Lean `StraightProgress_sized`, which lets `t'` be any
   same-size tree.
3. **All three Pant families are backbones.** T(3,3,3) (n=21, tied) and T(3,4,3) (n=23) are per-size maximizers.
   Every other member is strictly below the exact maximum of its size. T(6,6,6,6) = 44887.39 < max(52) = 45108.55.
4. **The large-n search found nothing that beats the best backbone.** It ran 1440 annealing runs for n in
   20..64 and never hit a non-backbone local maximum. That fits item 1, which already rules such trees out
   exactly.

Wall clock: about 45 minutes of compute on a shared 32-core machine (load 30-55 from other jobs). The biggest
pieces were exhaustive coverage n=23 (24 min, 16 workers), n=22 (9 min), the all-trees + backbone DP to
n=100 (12 min, single core), and the annealing search (12 min).

## Definitions (reused exactly)

`Aobj`, `strDefect`, the piece recognizers and SPR moves are the ones in `phase0_straightprogress_sized.py` /
`hwh_viability.py`, which mirror Lean `R47R7Straighten.strDefect`. A tree is a **backbone** when
min over roots of strDefect = 0. Such a tree is a spine whose vertices carry leaves, cherries and arms (a vertex
whose children are all cherries). That is the `backboneU s` shape (`strDefect_decode_sized`). **Coverage** at T
(the viability test) means: some tree T' at SPR distance 1 on the same vertex set has
minDefect(T') < minDefect(T) and Aobj(T') >= Aobj(T). `sanity` checks the fast engines against `pi_literal` and
`min_defect_over_roots` on all 200 trees with n <= 10, and checks the tree-enumeration counts against A000055.
It also reproduces the 1793 defective trees / 0 failures for n <= 15.

## 1. Exhaustive coverage (single SPR + free reroot)

Every non-isomorphic tree was enumerated (WROM level sequences, the same enumeration as
`networkx.nonisomorphic_trees`). Witness moves are confirmed in exact arithmetic.

| n | trees | backbones | defective | covered (strict / tie) | FAIL |
|---|---|---|---|---|---|
| 16 | 19320 | 15083 | 4237 | 4237 / 0 | 0 |
| 17 | 48629 | 35193 | 13436 | 13424 / 12 | 0 |
| 18 | 123867 | 82465 | 41402 | 41388 / 14 | 0 |
| 19 | 317955 | 193074 | 124881 | 124844 / 37 | 0 |
| 20 | 823065 | 452860 | 370205 | 370071 / 134 | 0 |
| 21 | 2144505 | 1061813 | 1082692 | 1082254 / 438 | 0 |
| 22 | 5623756 | 2491538 | 3132218 | 3131164 / 1054 | 0 |
| 23 | 14828074 | 5845472 | 8982602 | 8979694 / 2908 | 0 |

Exhaustive: 0 failures for all n <= 23. n = 24 (39.2M trees) was not run; it needs about an hour with
`coverage 24 24 16`.

### Coverage failures at n >= 25 (sampled, not exhaustive)

The witnesses below are re-verified by `python3 hwh_coverage_large_n.py witness`, both in this file's exact
engine and in the repo's networkx engine (`P.spr_neighbors`, `P.min_defect_over_roots`, `P.Aobj`).

- **n = 25** (`WITNESS_25`): minDefect 1, Aobj = 208849/1536 ~ 135.9694. There are 192 labeled SPR moves that
  lower minDefect, and the best of them reaches 44640889/331776 ~ 134.5513 (ratio 0.98957). So no move covers
  it. The best backbone at n = 25 is 175.558. Rooted at a degree-3 vertex the shape is
  `[[C], [[C]], [X,X]]` with `X = [[C],[[C]]]` (`C` = cherry). Edges:
  `[(0, 3), (1, 22), (1, 24), (1, 5), (2, 24), (2, 7), (3, 21), (4, 9), (4, 13), (5, 10), (6, 10), (7, 11), (8, 14), (8, 15), (9, 16), (12, 16), (12, 22), (12, 21), (14, 18), (15, 19), (15, 22), (17, 23), (17, 20), (19, 23)]`
- n = 29 (`WITNESS_29`): Aobj 533138359/1769472 ~ 301.298. Best defect-reducing SPR is 299.269.
- n = 34 (`WITNESS_34`): Aobj 4520118907/5242880 ~ 862.144. Best defect-reducing SPR is 851.896. Shape:
  centre + cherry + arm(3) + three copies of X.

How the failures were found:
- The annealing search, n = 20..64 (next section), found 265 failures among the 67500 near-top non-backbones
  it tested. The first came at n = 34, and failures appeared at every n from 36 to 64. 84 of these (the first
  three per n) were re-checked over all SPR moves in exact arithmetic, and all 84 are confirmed. The other 181
  were decided in floating point with a 1e-9 relative margin. In the 84 checked, the best defect-reducing move
  reached 0.9881-0.99995 of Aobj(T).
- A denser near-top search at n = 23..35 (`search-small`, 6000 per n) confirmed every failure exactly. The
  first failures were 1 at n=29, 2 at n=30, 1 at n=31, 2 at n=32, 4 at n=33, 5 at n=34 and 11 at n=35.
- The same search with `HWH_NEAR_FRAC=0.6` at n = 24..29 tested about 17k near-top trees per n and found
  0 failures.
- Taking leaf-deletion descendants (up to 8 deletions) of the failing trees gave about 220k distinct trees for
  n = 21..36. Failures: 1 at n=25, 1 at n=26, 9 at n=27, and more at larger n. There were none at n <= 24
  (4689 defective n=24 trees tested).
- A probe of random trees (Pruefer / preferential / uniform attachment) plus backbones with 1-2 random SPR
  moves found 0 failures at every n = 23..40 (11k-20k defective trees per n). The 2000 random trees per n in
  the main search (n = 20..64) were never among the checked failures: all 84 exactly checked came from the
  near-top set. So failures are rare, and they concentrate among high-Aobj trees with minDefect 1.

**What this means.** The local reading of `hwh` does not hold for all n. That reading is "every defective tree
has one size-preserving SPR move (plus reroot) that lowers the defect without lowering Aobj", which
`hwh_viability.py` tests and which the move-class assembly (`R47HwhAssembly`, via the `FlpStepAt` /
piece / symstar classes) is built to supply. Any single-SPR move-class family therefore cannot give
`Hcoverage` for every n. The Lean `StraightProgress_sized` itself (`R47R7Sized.lean`) is not refuted: its `t'`
is any same-size tree. For each fixed n it is equivalent to HnormMulti at n, since the best backbone of size n,
rooted at a defect-0 root, is a valid `t'` exactly when it dominates every tree. Section 2 verifies that for
n <= 100. A proof would need non-local steps (multi-move or "jump to the best backbone"), or a coverage
argument that allows longer move sequences.

## 2. Exact per-size maximizer (HnormMulti directly), n <= 100

**Method (exhaustive, exact).** Take a pendant subtree rooted at v, with parent p. It enters `Aobj` only
through the pair (S_v, r_v):
`Aobj(T) = S_v * (Z(rest) + r_v * Z(rest - p)/d_p)` with `S_v = prod S_c (d_v+R)/d_v` and `r_v = 1/(d_v+R)`,
where `R = sum r_c` over the children. Since `Z(rest)` and `Z(rest-p)` are positive, Aobj is strictly
increasing in both S_v and r_v. So a subtree that is strictly Pareto-dominated in (S, r) by another subtree of
the same size can never appear in a maximizer.

The DP builds the exact Pareto frontier of pendant subtrees for each size. It uses an unbounded knapsack over
child multisets, and within each (child count k, total size) state it prunes by strict dominance:
`R2 <= R1` and `P2 (k+R2) > P1 (k+R1)`. This is valid for every continuation because `(K+R2)/(K+R1)` is
nondecreasing in K >= k. Exact ties are kept. Every rooting of every tree is then evaluated.

The backbone-only DP uses the same machinery, restricted by the Lean characterisation: strDefect(v) = 0 iff
v has at most one non-piece child and that child has strDefect 0. Frontier sizes stay small (at most about 55
per size up to n = 100), which is why this runs to n = 100 in minutes.

**Result.** For every n = 4..100: exact max over all trees = exact max over backbones, and all maximizers
are backbones. The maximizer is unique up to isomorphism for every n except n = 21. There, the subdivided
star (a centre with 10 cherries, the Wu-Dong-Lai candidate) ties with T(3,3,3).

In the shape notation below, each spine vertex is written `L<leaves>C<cherries>A[arm sizes]` (arm size =
number of cherries) and spine vertices are joined by `-`. Only n = 31 (T(5,5,4)) has a spine longer than one
vertex. Every other maximizer is one centre with cherries and arms (a star of cherry-stars), and for large n
the arm sizes settle at 4-5.

| n | max Aobj (float of exact value) | maximizer(s) |
|---|---|---|
| 4 | 2.5 | L1C1 |
| 5 | 3 | L0C2 |
| 6 | 3.625 | L0C1A[1] |
| 7 | 4.5 | L0C3 |
| 8 | 5.375 | L0C2A[1] |
| 9 | 6.75 | L0C4 |
| 10 | 8.125 | L0C2A[2] |
| 11 | 10.125 | L0C5 |
| 12 | 12.234375 | L0C3A[2] |
| 13 | 15.1875 | L0C6 |
| 14 | 18.509765625 | L0C3A[3] |
| 15 | 22.78125 | L0C7 |
| 16 | 27.90703125 | L0C4A[3] |
| 17 | 34.171875 | L0C8 |
| 18 | 42.1453125 | L0C4A[4] |
| 19 | 51.2578125 | L0C9 |
| 20 | 63.502734375 | L0C4A[5] |
| 21 | 76.88671875 | L0C10, L0C3A[3, 3] |
| 22 | 95.7524414062 | L0C5A[5] |
| 23 | 116.130981445 | L0C4A[3, 3] |
| 24 | 144.162597656 | L0C5A[6] |
| 25 | 175.558007812 | L0C4A[4, 3] |
| 26 | 217.126524633 | L0C6A[6] |
| 27 | 265.387324219 | L0C4A[4, 4] |
| 28 | 326.682743617 | L0C6A[7] |
| 29 | 400.689642857 | L0C5A[4, 4] |
| 30 | 491.616983414 | L0C7A[7] |
| 31 | 604.453177316 | L0C5-L0C5A[4] |
| 32 | 739.283821106 | L0C7A[8] |
| 33 | 911.828430176 | L0C5A[5, 5] |
| 34 | 1111.85403442 | L0C8A[8] |
| 35 | 1375.51391029 | L0C6A[5, 5] |
| 36 | 1679.49220323 | L0C4A[4, 4, 4] |
| 37 | 2072.33734131 | L0C7A[5, 5] |
| 38 | 2538.05731609 | L0C5A[4, 4, 4] |
| 39 | 3122.60048022 | L0C7A[6, 5] |
| 40 | 3830.08148523 | L0C5A[5, 4, 4] |
| 41 | 4705.12516909 | L0C7A[6, 6] |
| 42 | 5780.07771584 | L0C6A[5, 4, 4] |
| 43 | 7084.83270654 | L0C8A[6, 6] |
| 44 | 8725.18781233 | L0C6A[5, 5, 4] |
| 45 | 10664.57337 | L0C8A[7, 6] |
| 46 | 13170.8371135 | L0C6A[5, 5, 5] |
| 47 | 16118.8595085 | L0C5A[4, 4, 4, 4] |
| 48 | 19861.8234486 | L0C7A[5, 5, 5] |
| 49 | 24331.099634 | L0C5A[5, 4, 4, 4] |
| 50 | 29932.2588694 | L0C7A[6, 5, 5] |
| 51 | 36732.7809945 | L0C6A[5, 4, 4, 4] |
| 52 | 45108.5496192 | L0C7A[6, 6, 5] |
| 53 | 55461.4027915 | L0C6A[5, 5, 4, 4] |
| 54 | 67979.3842645 | L0C7A[6, 6, 6] |
| 55 | 83738.6239861 | L0C6A[5, 5, 5, 4] |
| 56 | 102559.685149 | L0C5A[4, 4, 4, 4, 4] |
| 57 | 126432.495734 | L0C6A[5, 5, 5, 5] |
| 58 | 154846.878227 | L0C5A[5, 4, 4, 4, 4] |
| 59 | 190766.202528 | L0C7A[5, 5, 5, 5] |
| 60 | 233807.261203 | L0C6A[5, 4, 4, 4, 4] |
| 61 | 287546.127451 | L0C8A[5, 5, 5, 5] |
| 62 | 353081.375694 | L0C6A[5, 5, 4, 4, 4] |
| 63 | 433446.031813 | L0C8A[6, 5, 5, 5] |
| 64 | 533199.691434 | L0C6A[5, 5, 5, 4, 4] |
| 65 | 653453.584214 | L0C5A[4, 4, 4, 4, 4, 4] |
| 66 | 805198.998045 | L0C6A[5, 5, 5, 5, 4] |
| 67 | 986784.051311 | L0C5A[5, 4, 4, 4, 4, 4] |
| 68 | 1215947.46652 | L0C6A[5, 5, 5, 5, 5] |
| 69 | 1490142.23783 | L0C5A[5, 5, 4, 4, 4, 4] |
| 70 | 1835215.82858 | L0C7A[5, 5, 5, 5, 5] |
| 71 | 2250428.29914 | L0C6A[5, 5, 4, 4, 4, 4] |
| 72 | 2767159.23327 | L0C8A[5, 5, 5, 5, 5] |
| 73 | 3398974.45369 | L0C6A[5, 5, 5, 4, 4, 4] |
| 74 | 4171574.28317 | L0C8A[6, 5, 5, 5, 5] |
| 75 | 5133684.07105 | L0C6A[5, 5, 5, 5, 4, 4] |
| 76 | 6294773.4803 | L0C5A[5, 4, 4, 4, 4, 4, 4] |
| 77 | 7753698.13224 | L0C6A[5, 5, 5, 5, 5, 4] |
| 78 | 9507246.94763 | L0C5A[5, 5, 4, 4, 4, 4, 4] |
| 79 | 11710815.705 | L0C6A[5, 5, 5, 5, 5, 5] |
| 80 | 14359123.5055 | L0C5A[5, 5, 5, 4, 4, 4, 4] |
| 81 | 17677502.8017 | L0C7A[5, 5, 5, 5, 5, 5] |
| 82 | 21687004.5002 | L0C5A[5, 5, 5, 5, 4, 4, 4] |
| 83 | 26659327.5166 | L0C8A[5, 5, 5, 5, 5, 5] |
| 84 | 32758844.9079 | L0C6A[5, 5, 5, 5, 4, 4, 4] |
| 85 | 40192810.4459 | L0C8A[6, 5, 5, 5, 5, 5] |
| 86 | 49484207.2759 | L0C6A[5, 5, 5, 5, 5, 4, 4] |
| 87 | 60703200.542 | L0C5A[5, 5, 4, 4, 4, 4, 4, 4] |
| 88 | 74748652.9216 | L0C6A[5, 5, 5, 5, 5, 5, 4] |
| 89 | 91694641.5421 | L0C5A[5, 5, 5, 4, 4, 4, 4, 4] |
| 90 | 112911671.026 | L0C6A[5, 5, 5, 5, 5, 5, 5] |
| 91 | 138508051.764 | L0C5A[5, 5, 5, 5, 4, 4, 4, 4] |
| 92 | 170447262.956 | L0C7A[5, 5, 5, 5, 5, 5, 5] |
| 93 | 209220760.118 | L0C5A[5, 5, 5, 5, 5, 4, 4, 4] |
| 94 | 257074577.776 | L0C8A[5, 5, 5, 5, 5, 5, 5] |
| 95 | 316033570.339 | L0C5A[5, 5, 5, 5, 5, 5, 4, 4] |
| 96 | 387819096.459 | L0C5A[5, 5, 4, 4, 4, 4, 4, 4, 4] |
| 97 | 477418735.651 | L0C6A[5, 5, 5, 5, 5, 5, 4, 4] |
| 98 | 585885448.944 | L0C5A[5, 5, 5, 4, 4, 4, 4, 4, 4] |
| 99 | 721249741.694 | L0C6A[5, 5, 5, 5, 5, 5, 5, 4] |
| 100 | 885105626.188 | L0C5A[5, 5, 5, 5, 4, 4, 4, 4, 4] |

Selected exact values:

| n | exact max Aobj |
|---|---|
| 23 | 951345/8192 |
| 36 | 48154400451/28672000 |
| 38 | 166334124267/65536000 |
| 52 | 370829981399553/8220835840 |
| 64 | 62977069015968447/118111600640 |

At n = 52 the maximizer (centre + 7 cherries + arms 6,6,5) has arms bigger than 5. That puts it outside the
Balanced+Capped single-hub class, and it beats T(6,6,6,6) (1180837892027061/26306674688 ~ 44887.39) and the old
`tieArgmax(52)` ~ 44779.58. The n = 52 value was independently recomputed with `bg_maximizer_family.aobj`.

## 3. Pant's families

All three families use the paper's definition (core path x_1..x_m, with a_i pendant paths of length 2 at x_i;
this matches arXiv 2605.14176 and `_pant_check.py`). Every member with n <= 64 has minDefect 0, so every one
is a backbone. Aobj compared with the exact per-size maximum:

| family | n | Aobj / max_n |
|---|---|---|
| T(3,3,3) | 21 | 1 (tied maximizer) |
| T(3,4,3) | 23 | 1 (unique maximizer) |
| T(3,5,3) .. T(3,24,3) | 25..63 | 0.9971 falling to 0.9146 |
| T(3,3,3,3) .. T(7,7,7,7) | 28..60 | 0.979, 0.9956, 0.9955, 0.9951, 0.9884 |
| T(3,3,4,3) .. T(7,7,8,7) | 30..62 | 0.9836, 0.9952, 0.9950, 0.9954, 0.9859 |

(T(6,6,6,6), n=52: 0.995097.)

## 4. Large-n adversarial search, n = 20..64

**4(a) Best backbone per n.** The backbone DP in section 2 computes this exactly and exhaustively over all
backbones of each size. It is not a heuristic search over hub lists.

**4(b) Annealing over all trees.** For each n there were 32 runs: 16 from random trees (Pruefer, preferential
and uniform attachment) and 16 from seeds perturbed by 1-6 random SPR moves (the DP maximizer, every Pant tree
of that size, and T(6,6,6,6) at n=52). Each run makes 60000 random SPR moves with Metropolis acceptance on
log Aobj (T 0.4 down to 0.001), then does first-improvement SPR ascent to a strict local maximum.

- No tree beat the best backbone in floating point (`float_beats = 0` for every n). This is consistent with
  section 2, which excludes it exactly.
- Every local maximum reached was a backbone: 0 non-backbone local maxima across all 1440 runs.
- Annealing reaches the exact maximum at 21 of the 45 sizes. Elsewhere it stalls at backbone local maxima
  at 0.9715-0.9998 of the maximum. That is why section 2 is the result to rely on, not the search.
- The best non-backbone seen per n reached 0.88-0.963 of the best backbone.

**4(c) Coverage on visited non-backbones.** Coverage was run on up to 1500 non-backbones per n with
Aobj >= 0.75 x best backbone. (A 5% band would have been nearly empty. Non-backbones within 5% of the best backbone appeared only at
n = 49, 53, 55, 57, 58, 60, 62, 64, peaking at 0.9631. A 1-SPR neighbourhood scan of the n=52 maximizer contains
no non-backbone at all.) It was also run on 2000
random trees per n.

| n | best found / best backbone | best non-backbone seen / best backbone | near-top tested | random tested | FAIL |
|---|---|---|---|---|---|
| 20 | 1.000000000 | 0.8799 | 1500 | 2000 | 0 |
| 21 | 1.000000000 | 0.9109 | 1500 | 2000 | 0 |
| 22 | 1.000000000 | 0.8827 | 1500 | 2000 | 0 |
| 23 | 1.000000000 | 0.9119 | 1500 | 2000 | 0 |
| 24 | 1.000000000 | 0.8864 | 1500 | 2000 | 0 |
| 25 | 1.000000000 | 0.9109 | 1500 | 2000 | 0 |
| 26 | 0.975186314 | 0.8888 | 1500 | 2000 | 0 |
| 27 | 1.000000000 | 0.9097 | 1500 | 2000 | 0 |
| 28 | 0.982565012 | 0.8929 | 1500 | 2000 | 0 |
| 29 | 1.000000000 | 0.9062 | 1500 | 2000 | 0 |
| 30 | 0.986941581 | 0.8979 | 1500 | 2000 | 0 |
| 31 | 1.000000000 | 0.9086 | 1500 | 2000 | 0 |
| 32 | 0.992687386 | 0.9013 | 1500 | 2000 | 0 |
| 33 | 1.000000000 | 0.9114 | 1500 | 2000 | 0 |
| 34 | 0.998522806 | 0.9067 | 1500 | 2000 | 1 |
| 35 | 1.000000000 | 0.9155 | 1500 | 2000 | 0 |
| 36 | 1.000000000 | 0.9045 | 1500 | 2000 | 6 |
| 37 | 0.981055901 | 0.9207 | 1500 | 2000 | 3 |
| 38 | 1.000000000 | 0.9078 | 1500 | 2000 | 2 |
| 39 | 0.984891486 | 0.9262 | 1500 | 2000 | 2 |
| 40 | 1.000000000 | 0.9116 | 1500 | 2000 | 3 |
| 41 | 0.989132241 | 0.9323 | 1500 | 2000 | 4 |
| 42 | 1.000000000 | 0.9161 | 1500 | 2000 | 9 |
| 43 | 0.994296785 | 0.9382 | 1500 | 2000 | 6 |
| 44 | 1.000000000 | 0.9159 | 1500 | 2000 | 2 |
| 45 | 0.999803276 | 0.9453 | 1500 | 2000 | 7 |
| 46 | 0.980626975 | 0.9202 | 1500 | 2000 | 5 |
| 47 | 1.000000000 | 0.9477 | 1500 | 2000 | 2 |
| 48 | 0.984223252 | 0.9253 | 1500 | 2000 | 25 |
| 49 | 1.000000000 | 0.9522 | 1500 | 2000 | 16 |
| 50 | 0.988464033 | 0.9311 | 1500 | 2000 | 6 |
| 51 | 1.000000000 | 0.9368 | 1500 | 2000 | 12 |
| 52 | 0.993144133 | 0.9370 | 1500 | 2000 | 8 |
| 53 | 1.000000000 | 0.9579 | 1500 | 2000 | 9 |
| 54 | 0.997921991 | 0.9429 | 1500 | 2000 | 10 |
| 55 | 0.981818219 | 0.9605 | 1500 | 2000 | 17 |
| 56 | 0.971526765 | 0.9478 | 1500 | 2000 | 8 |
| 57 | 0.984662338 | 0.9631 | 1500 | 2000 | 5 |
| 58 | 1.000000000 | 0.9504 | 1500 | 2000 | 8 |
| 59 | 0.988160313 | 0.9448 | 1500 | 2000 | 30 |
| 60 | 0.977080981 | 0.9533 | 1500 | 2000 | 13 |
| 61 | 0.992653658 | 0.9366 | 1500 | 2000 | 14 |
| 62 | 0.979921322 | 0.9561 | 1500 | 2000 | 13 |
| 63 | 0.997280800 | 0.9423 | 1500 | 2000 | 8 |
| 64 | 0.982940645 | 0.9588 | 1500 | 2000 | 11 |

## Honest scope

- **Exhaustive and exact:** HnormMulti (the per-size maximizer is a backbone) for every n <= 100; single-SPR
  coverage for every n <= 23; the best backbone per n <= 100.
- **Sampled:** everything in section 4, the coverage failure census at n >= 25, and the absence of failures
  at n = 24.
- The DP's correctness rests on the monotonicity identity and the pruning lemma stated in section 2, plus the
  brute-force cross-check for n <= 18. Neither is kernel-checked.
- Nothing here proves HnormMulti for all n. The exact data up to n = 100 shows a very regular maximizer family
  (one centre, cherries, arms of 4-5 cherries). `conjecture1_proved = False`.
