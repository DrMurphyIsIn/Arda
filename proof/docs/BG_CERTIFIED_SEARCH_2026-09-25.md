# Certified search for the Brualdi-Goldwasser maximizer, n ≤ 491 (2026-09-25)

Script: `proof/verification/bg_certified_interval.py`. Output: `proof/verification/bg_certified_interval_N491.json`.
`conjecture1_proved = False` is the campaign flag; this document covers only the finite range.

## Why this exists

The Lean theorem `BGMax.bg_spider_reduction` (`R3Cert/BGMaximizer.lean`) proves the following for every
tree on n ≥ 492 vertices: some spider on the same number of vertices has π at least as large. Here π is
`per(L)/∏deg`. So the maximizer question for n ≥ 492 reduces to the spider optimization (BGSpiderOpt).
This search settles every n ≤ 491 directly. For each n it:

1. computes the exact maximum of π over all trees on n vertices, and
2. lists every tree that attains it, and checks that each one is a spider.

It runs over all trees with no degree cap, so it doesn't rely on the Lean high-degree theorem either.

## The search

Rooted trees are built bottom-up.

- **Planted branch.** A planted branch b (a subtree hanging from a parent) is summarised by T_b and y_b. If its root has
  children c with d = #children + 1 and R = Σ y_c, then

  T_b = (∏ T_c)(d + R)/d  and  y_b = 1/(d + R).

- **Tree value.** For a tree rooted at a vertex with k children, π = (∏ T_c)(k + R)/k. This is `piRoot`, and it equals `Aobj`
  (`BGMax.Aobj_eq_piRoot`).
- **Partial root state.** A state at key (k, s) has k children so far with sizes summing to s. It stores lp = log ∏ T_c
  and R = Σ y_c.
- **Growth.** Items (planted branches) of size m are built from the states at (k, m−1). Items are then added to
  states in rounds of increasing size m, any number per round. Within a round, items are added in
  non-decreasing item id.

## Discarding is exact

**Lemma I (items).** Fix a pendant subtree p of size m inside a tree. Then π = T_p·(A + y_p·B), where A > 0
and B ≥ 0 do not depend on p.

*Proof.* Split the matchings on whether the edge from p's root to its parent is used. If it isn't, the
contribution is T_p·Z(rest). If it is, the contribution is U_p·Z(rest − parent)/(d_p·d_parent), and
U_p/(T_p·d_p) = y_p.

So an item with T′ > T and y′ ≥ y is strictly better than the other in every tree that uses it.

**Lemma S (states).** Fix the key (k, s) and let D = max(k, 1). Every completion of a state is either a final root, or
becomes an item that then sits in a tree. Either way its value has the form

  e^{lp} · E · ((c + R)·A + B),  with c ≥ D, E > 0, A > 0, B ≥ 0,

where c, A, B, E depend only on the completion. So suppose lp′ > lp and lp′ + log(D + R′) > lp + log(D + R). Then
the primed state is strictly better in every completion:

- If R′ ≥ R, it's immediate.
- If R′ < R, then log(c + R′) − log(c + R) increases in c, so the inequality at c = D covers every c ≥ D.

**Rounding.** Every float quantity is stored as a guaranteed enclosure [lo, hi]. The rounding is outward:
`nextafter` after every add, divide and multiply, and 4 ulps after every libm `log`. Both lemmas are applied to
the enclosures, with the loser's upper bounds against the winner's lower bounds. So every discarded
object is *provably strictly* beaten. The discard decisions need no error analysis.

**Exhaustiveness with canonical order.** Adding items in non-decreasing id order avoids generating
duplicate multisets. When a state q discards a state p, q inherits p's "smallest id allowed next". That
permission only adds generated states, so it can never make the search unsound. By induction on the
multiset built in sorted id order, every multiset of surviving items is dominated by some surviving
state at its key. Lemma S is preserved when the same item is added to both states. The dominator
chosen by the sweep (the running-max element) is itself never discarded.

**Final step.** For each n, every root state whose upper bound reaches the best lower bound is rebuilt and
evaluated exactly in `fractions.Fraction`. By the two lemmas, every exact maximizer survives to this
step. The maximizers are then re-expanded to edge lists and tested for the spider shape. A tree is a
spider if some vertex has only leaves, cherries and arms as its branches.

## Controls

- Exact brute force over all non-isomorphic trees agrees for every n ≤ 18.
- Exact brute force over trees of maximum degree ≤ 3 agrees with the capped search for every n ≤ 18.
- The exact maxima agree with the independent spider optimization (`bg_spider_opt_4_2400.json`) for every
  n ≤ 120. They also agree with the earlier float DP of the B1 agent (`bg_spider_reduction.py certified 520`,
  conservative tolerance pruning, 3,695 candidates rechecked exactly, no tree above the best spider).

## Result

The run was `python3 bg_certified_interval.py 491`, on all trees with no degree cap. It took 952 s on one core
and kept 12,331,366 states, and it wrote `bg_certified_interval_N491.json`.

- Every n in 2..491 is covered.
- For every n in 2..491, **every tree attaining the exact maximum of per(L)/∏deg is a spider**. At most 9
  root states per n reached the final exact recheck.
- The exact maximum equals the value of the spider-family maximizer from `bg_spider_opt_4_2400.json`, as
  exact fractions, for every n in 4..491. So the explicit table and rule of
  `BG_SPIDER_OPTIMIZATION_2026-09-24.md` give the Brualdi-Goldwasser maximizer for all n ≤ 491.

Combined with `BGMax.bg_spider_reduction` (Lean, n ≥ 492), the maximizer is identified for every n. For n ≥ 492 the
optimal spider is W(n) (`BGSpiderRule`). That optimization is being formalized as `StructProp 492` + `CandProp 492`.
Until then it rests on the exact computation and certificate of B2.
