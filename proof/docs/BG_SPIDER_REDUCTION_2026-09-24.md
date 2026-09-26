# BG spider reduction, part B1 (2026-09-24)

Branch `bg/reduction`. Lean files, all in namespace `R3Cert.BGSCL`:
`proof/formalization/R3Cert/BGSpiderReduction.lean`, `BGSpiderCells.lean`, `BGSpiderLowDegree.lean`.
Script: `proof/verification/bg_spider_reduction.py`. `conjecture1_proved = False`.

## The claim

For every tree T on n vertices there is a two-level spider S on n vertices with pi(S) >= pi(T). A
two-level spider is a centre carrying leaves, cherries and arms, where arm_j is a vertex whose j >= 1
other neighbours are all cherries. The "atoms" are the leaf, the cherry and the arms, so a tree is a
spider exactly when some root has only atom children.

Earlier notes listed n = 31 (Pant's T(5,5,4)) as a two-hub exception. It is not one. Root it at the
middle core vertex x_2 and its children are 5 cherries, x_1 (which is arm_5) and x_3 (which is arm_4), so
it is the spider centre + C^5 + arm_5 + arm_4. The old label came from how the shape printer chose a
root. As far as anything computed shows, **no n needs an exception**.

## Status

| range | result | how it is established |
|---|---|---|
| n >= 492, any tree | dominated by a spider (strictly, unless the tree is a spider centred at its max-degree vertex) | **Lean, kernel-checked, no hypotheses**: `spider_dominates_of_maxDegreeRoot` |
| 91 <= n, some vertex of degree >= 24 | same | **Lean**: `spider_dominates_highDegree_uncond` |
| n <= 100 | max over all trees = max over spiders; every maximizer is a spider | exact DP (`hwh_coverage_large_n.py`, Fraction) |
| n <= 520 | max over all trees <= exact best spider M(n) | `certified 520`: exhaustive frontier DP in floats with conservative pruning (tol 1e-9), then 3695 candidates rechecked exactly in Fractions; no tree exceeds M(n) (3130 s). The lead is running an independent interval-arithmetic check (`bg_certified_interval.py`, bg/registry-fidelity) |

Taken together these cover every n. Two qualifications, both stated precisely:

1. The bridge to the matching objective is proved in `BGSpiderBridge.lean`:
   `Aobj_toU_node : Aobj (toU (Branch.node cs)) = piRoot cs`, and
   `spider_dominates_of_maxDegreeRoot_Aobj` states the result for `Aobj`. The inverse direction
   (UTree -> Branch) and the rerooting are being done by the lead in `BGMaximizer.lean`.
2. "Every tree can be rooted at a vertex of maximum degree" (which gives the hypothesis
   `∀ c ∈ cs, maxCh c + 1 ≤ cs.length`) is the obvious combinatorial step outside the formal statement.
   The spider built is always the arm_5/arm_4 spider with q = 5(n-1) mod 11 copies of arm_4 and
   a = ((n-1)-9q)/11 copies of arm_5.

## The argument

Notation. A planted branch b has summary (T_b, y_b). `bell b = log T_b - |b|F*` with
`F* = log(621/64)/11`, and `V_mu(b) = bell b + mu*y_b`.

- **Lagrangian identity** (`phiRoot_eq`): `log pi - (n-1)F* = sum_i bell b_i + log(1 + S/k)`.
- **Spider floor** (`phiRoot_spider_ge`, `bell_arm4_ge`): the arm_5/arm_4 spider has
  `log pi - (n-1)F* >= log(26/23) - 10/960`. The copies of arm_4 have y = 3/19 > 3/23, and they absorb
  the residue of n-1 mod 11.
- **High degree, k >= 24** (`BGSpiderReduction` + `BGSpiderCells`). Use the tangent at t = 26/23, which
  gives price mu = 23/(26k) <= 23/624. On that range arm_5 is the V_mu envelope, and every non-atom sits
  below it by at least 1/75 (observed minimum 0.014520, at node[cherry x5, arm_4]). This is reduced
  through the proven subaction `ρwit` (`isSubaction_ρwit`, `bell_add_ρwit_le`) to three per-vertex cores,
  all proved:
  - `surchargeCore_proved`: uniform tangent at the all-cherry point plus a per-child ρwit-class bound.
  - `atomCell0Core_proved` and `atomCellMuCore_proved`: 22 per-K tangent certificates with degree-6
    Taylor log enclosures. Tightest margin 7.3e-4, at K = 6.
  The gap (>= 1/75) is larger than the slack (<= 10/960).
- **Low degree, k <= 23** (`BGSpiderLowDegree`). This follows the lead's linear-deficit route. Define
  `rateG α c = bell c + α|c|` for an atom child and `-ρwit c` otherwise. The per-vertex cell
  `RateCellCap D α`, `(log(1+S/d) - F*) + ρwit(node) + α + Σ rateG ≤ 0` under a degree cap D, telescopes
  (`bell_add_ρwit_le_rateCap`) to the **linear deficit** `bell b + ρwit b <= -α|b|` for every non-atom
  capped branch. At the root this gives
  `log pi - (n-1)F* <= [log(1+S/k) + Σ rateG] - α(n-1) <= R_k - α(n-1)`.
  - Rates by cap: D = 23 with α = 1/3700 (root degree 6..23); D = 5, 4, 3, 2 with α = 1/2100, 1/660,
    1/420, 1/135 (root degree 5, 4, 3, 2).
  - Certificates: 32 rate cells and 22 root cells, all tangent certificates with rational envelopes.
    Tightest rate-cell margin 2.8e-4, at (D=23, K=5).
  - The rate binds at near-atom vertices of degree 6, not at hub-of-hubs.
  - R_k ranges from 0.208 (k = 23) to 0.319 (k = 2). Each root cell's own threshold on n-1 is between
    28 and 491, so the uniform threshold is n-1 >= 491.

## Other computations

- Branch envelope (`envelope 80 19`): an exact Pareto-frontier DP over planted branches of size <= 80,
  agreeing with brute-force enumeration for sizes <= 19 (the A000081 counts). On mu in [0, 1/2] the
  supremum of V_mu over all branches equals the supremum over atoms.
- `cells`, `gen-cells`, `gen-rate`: every rational constant used in Lean is re-derived and re-checked
  exactly with fractions.
- Float DP (`maxcheck`): max over all trees minus exact M(n) is at most 1e-13 for every n <= 500.

## Reproduce

```
cd proof/formalization && lake build R3Cert.BGSpiderLowDegree && lake env lean AxiomGuard.lean
cd proof/verification
python3 bg_spider_reduction.py gen-cells
python3 bg_spider_reduction.py gen-rate
python3 bg_spider_reduction.py certified 520     # about 52 min
python3 bg_spider_reduction.py envelope 80 19
```

## What is left (honest scope)

- The finite range n <= 491 rests on computation, not Lean: the exact DP for n <= 100 and the certified
  DP for n <= 520. The certified DP uses floats with near-tie retention and then an exact recheck of
  every candidate. That makes it exact provided the float error stays below the 1e-9 pruning tolerance.
  The error is about 1e-13 per the double-precision estimate, but no formal interval analysis was done.
- Error analysis behind the certified DP (n <= 520). Every stored log value is a sum over at most n
  vertices of local terms log((d+R)/d). Each local term carries about (1+n) ulp of rounding, because
  relative errors in y and R grow by at most one ulp per child along a path. The absolute error is
  therefore at most about 5e-11, which is below the 1e-9 pruning tolerance by a factor of 20 or more.
  So a discarded state is beaten exactly, in every continuation, by a retained one, and the exact
  maximizer survives into the candidate set (candidates are taken within 1e-8 of the float optimum).
  This bound is a written estimate, not a formal interval analysis; the lead's interval-arithmetic run
  is the independent check.
- The max-degree rooting step (the lead is handling it).
