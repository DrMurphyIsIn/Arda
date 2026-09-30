# Emitter design: `concave_pooled_induction` (2026-09-29)

`ConcavePooledInductionEmitter`, kind `concave_pooled_induction`, module
`src/telperion/emit_concave_pooled_induction.py`.

`conjecture1_proved = False`. This kind certifies bounds for explicit rational tree recursions. It
says nothing about the Brualdi-Goldwasser conjecture, RH, or any other open problem.

## Credit

The method is **concave-witness induction**, from the draft *"The maximum Laplacian ratio of a tree
for all n >= 303: concave witnesses and one-variable certificates"* (28 September 2026). It was
communicated to us by **Professor John L. Goldwasser**; the author is his London colleague, and
their name will be added once they give permission. The draft uses the induction to close the
Brualdi-Goldwasser ceiling. This kind packages the method generically. We have not formalized the
Laplacian-ratio instance (the draft's Sections 4-9); that is on hold until the author agrees. None
of the draft's data is in this repository.

## Why this kind exists

The 2026-09-29 corrections to `bg/envelope.py` and `bg/sibling_coupling.py` withdrew an earlier
claim that no single-variable envelope can be inductive for a branching recursion. The draft's
concave witness is a counterexample to that claim. `super_solution.py` now says when a local pass
is also a global certificate: the potential depends on one scalar message, it is concave in that
message, and the per-node inequality holds at the pooled mean for every child count. Jensen then
gives `sum_c U(y_c) <= m U(mean)`, and induction from the leaves closes the argument. This kind
is that argument, checked by the kernel.

## Setting and claim

Finite rooted trees. A node `v` with `m >= 1` children carries a message and a profit:

    R = sum_c y_c,    y_v = h(m, R),    l(v) = sum_c l(c) + g(m, R)

A leaf carries `(y_leaf, l_leaf)`. The functions `h` and `g` are rational in `(m, R)` with
rational coefficients. The claim is

    l(b) + alpha |b| <= U(y_b)    for every finite rooted tree b

(or for every tree whose child counts are at most `M`, when no tail is certified). Here `|b|` is
the vertex count and `alpha` is the size-proportional deficit. The deficit is only a
reparametrization: `l + alpha |.|` obeys the same recursion with `g + alpha` and `l_leaf + alpha`,
so it enters every obligation as an additive constant.

## The witness and why min-of-pieces

`U` is concave and piecewise linear on `I = [x_0, x_K]`, with rational nodes and **strictly**
decreasing slopes. A repeated slope is refused, because a redundant node should be merged. In Lean,
`U` is **defined** as `minPieces A B x = min_k (A k * x + B k)`, a function on all of `R`. Two
things follow:

* Jensen comes free. For every piece `k`, `sum_i U(y_i) <= sum_i p_k(y_i) = m p_k(mean)`, because
  `p_k` is affine. Taking the minimum over `k` gives `sum_i U(y_i) <= m U(mean)`
  (`minPieces_jensen`). The kernel needs no concavity argument at all.
* When the slopes are strictly decreasing, the minimum equals the interpolant on `I`. The kernel
  re-checks this at every node (`<inst>_node<j> : U x_j = v_j`, by `le_minPieces` + `fin_cases` +
  `norm_num`).

## Obligations (what the certificate contains)

1. **Concavity.** Slopes strictly decreasing, checked exactly in Python and re-checked in the
   kernel through the node table.
2. **Base.** `lo <= y_leaf <= hi` and `l_leaf + alpha <= U(y_leaf)`.
3. **Explicit child counts** `m = 1..M`. For each `m`, the range of `R = m * ybar`, which is
   `[m lo, m hi]`, is split into cells. Each cell uses a piece `j` for the left side:
   `m U(ybar) <= a_j R + m b_j`, which holds for any `j` since `U <= p_j` everywhere. The generator
   picks the piece that is active on the cell. The right side `U(h)` is a minimum, so the
   certificate proves, for **every** piece `k`,

       a_j R + m b_j + g(m, R) + alpha <= a_k h(m, R) + b_k,

   and it also proves the closure conditions `lo <= h(m, R)` and `h(m, R) <= hi`. Every one of
   these is a one-variable rational inequality. Multiplying through by the common denominator `D`
   (certified strictly positive on the cell) gives a polynomial `N(R) >= 0` on `[s, t]`. That is
   certified by exact Bernstein coefficients:
   `N = sum_i c_i (R - s)^i (t - R)^(d - i)` with every `c_i >= 0`. The identity is re-expanded
   exactly as a check. The untrusted generator bisects a cell whose coefficients are not all
   nonnegative, to depth 10.
4. **Tail** `m >= M + 1`. This needs `h` and `g` free of `m`, `lo >= 0` and `hi > 0`. Take a
   piece with `b_j <= 0`. Since `m >= M + 1` and `R = m ybar <= m hi`:

       m U(ybar) <= a_j R + m b_j <= a_j R + (M + 1) b_j          (mode M1)
       m U(ybar) <= a_j R + m b_j <= (a_j + b_j / hi) R           (mode Rhi)

   So it suffices to check `LHS_mode(R) + g(R) + alpha <= U(h(R))`, together with closure, for all
   `R >= (M + 1) lo`. That is a single variable with no `m`. The generator first tries the whole
   half-line as one cell. Failing that, it covers `[start, B]` and `[B, oo)` for growing `B`. The
   unbounded cell uses the Taylor expansion at `s`, `N(s + u) = sum_i c_i u^i`, with every
   `c_i >= 0`.

   This tail is **not** the node-condition tail of the draft's Lemma 3.4, which uses `U = 0` near
   the small messages that large `m` produces. It is our own sufficient condition, and it is the
   one the certificate checks. Without a tail (`tail=False`, required whenever `h` or `g` depends
   on `m`), the conclusion carries `b.AllDeg (fun m => m <= M)`, and nothing is claimed beyond `M`.

## The Lean

The file is self-contained: `import Mathlib` only.

* **Generic** (emitted once per file, in `namespace ConcavePooled`): `PTree` (`leaf |
  node m (cs : Fin (m+1) -> PTree)`, so an internal node always has at least one child); `size`,
  `msg`, `ell` and `AllDeg`; `pooled_induction_core`; and `minPieces` with `minPieces_le`,
  `le_minPieces` and `minPieces_jensen`. The core takes abstract `h g : N -> R -> R`, a carried
  `U`, a pooling `V`, Jensen for `V`, `U <= V` on `I`, the base, closure, and the step hypothesis
  `m V(yb) + g m (m yb) + alpha <= U (h m (m yb))` for admissible `m`. From these it proves, for
  every admissible tree, `lo <= msg`, `msg <= hi`, and `ell + alpha * size <= U msg`. The proof
  is structural induction. The mean of the children lies in `I` by `Finset.sum_le_sum`, and the
  step is applied at that mean.
* **Per instance**:
  * the witness and the recursion: `A`, `B`, `U`, `h`, `g`;
  * the lemmas `piece<j>` and `node<j>`, and `base`;
  * for each cell, one lemma per piece and one for each closure side. Each has the same shape:
    `field_simp; ring` to reach `N/D`, then `linarith` over the Bernstein products;
  * a per-cell aggregate against `U` (`le_minPieces` + `fin_cases`);
  * `step<m>` and `clos<m>`, split over the cells with `le_or_gt`;
  * `tail` and `tail_clos`;
  * `hstep` and `hclos`, using `Nat.lt_or_ge` plus `interval_cases m`;
  * `U_le_max`;
  * the main theorem `<inst>`;
  * the corollary `<inst>_uniform : ell + alpha * size <= max_j v_j`.
* The emitted proofs use no `sorry`, no `native_decide`, no `decide` and no new axiom. The kernel
  proves the main theorem outright, and its only hypothesis is `hb` in bounded mode. Soundness
  therefore does not depend on the Python checks. Python only decides whether we emit at all.

## The dogfood (`examples/concave_pooled_induction/`)

1. **`matching_density`** is a classical recursion with a statement we have not seen in print.
   For the subtree `T_u` rooted at `u`, let `y_u = Z(T_u - u) / Z(T_u)`, where `Z` counts
   matchings. This is the probability that `u` is unmatched in a uniform random matching of
   `T_u`. It satisfies `y_leaf = 1` and `y_v = 1 / (1 + sum_c y_c)`, since
   `Z(T_v) = Z(T_v - v) (1 + sum_c y_c)`. The Lean does not define `Z`; the theorem is about this
   recursion. With `g = -1/(1+R)` and `l_leaf = -1`, `ell(b) = -sum_{u in b} y_u`. With
   `alpha = 3/5` and the witness `U = interp{(0,0), (1/2,-1/8), (1,-3/10)}`, `M = 2`, and the tail
   for `m >= 3`, the corollary `matching_density_uniform` states:

       sum_{u in T} y_u  >=  (3/5) |T|     for every finite rooted tree T.

   The path shows that the best constant is at most `1/phi = 0.618...`, because the path's `y`s
   are Fibonacci ratios. An untrusted LP with a fine grid and 25 child counts gave 0.61803..., numerically `1/phi`,
   as the best `alpha` a concave witness can certify. The certificate has 8 cells: 2 for `m = 1`,
   3 for `m = 2`, and 3 in the tail, the last of which is `[1, oo)`, all using piece 0 in mode Rhi.
2. **`path_density`** is the same recursion restricted to child count `<= 1` (paths), in bounded
   mode. It is also the negative-control instance.
3. **`synthetic_mdep`** is clearly synthetic, with no combinatorial meaning: `h = m/(m + 2R)` and
   `g = -1/(1+R)`, bounded child count `<= 2`, `alpha = 1/2`. It exists so that the m-dependent
   rendering and two distinct denominators are exercised in compiled Lean.

The build output is 134 theorems, and every one prints `[propext, Classical.choice, Quot.sound]`,
except `PTree.allDeg_true`, which uses no axioms. The build takes about 40 s on the loaded machine,
with the Mathlib packages reflinked.

## Negative control

`negctrl_adapters/adapter_concave_pooled_induction.py` forges `path_density` with
`alpha = 13/20 > 1/phi`. The resulting claim is false: on a path of 100 vertices,
`ell + (13/20) n > 0 >= U`. Layer 1 refuses it (`obligation FALSE at m = 1, R = 1/2`). The adapter
builds it with `check=False`, which produces the same cell algebra with the sign checks skipped.
The kernel then rejects four cell `key` lemmas with "linarith failed", because those cells carry
negative Bernstein coefficients. The true twin, `alpha = 3/5`, compiles clean. This was run by
hand against `examples/concave_pooled_induction/lean` and gave `okay=True`. In the test suite the
lean-gated parametrization in `test_certificate_sensitivity` skips when the shared
`log_combination` env is not built.

## Refusals

A float anywhere; fewer than two nodes; nodes not strictly increasing; slopes not strictly
decreasing; `M < 1`; `y_leaf` outside `I`; a failing base; a foreign symbol in `h` or `g`; a
denominator or common denominator not certified positive on a cell; a cell or closure obligation
still uncertified at depth 10 (reported with an exact violating point when the probe finds one);
a tail with m-dependent `h`/`g`, with `lo < 0`, with `hi <= 0`, or with no `b_j <= 0`; a supplied
layout that does not cover its domain; a cell whose stored algebra differs from its exact
recomputation; a mode that does not match its `m`; a polynomial of degree above 12.

## Not supported (stated plainly)

* **Atom children**, meaning exempt children with exact, unpooled values: not implemented. They
  would need a second, unpooled sum in the step hypothesis.
* **A carried `U` different from the pooling `V`**: the generic theorem supports it, but the
  emitter always instantiates `U = V`.
* **Non-rational `g` or `h`**, for example `log` cells: out of scope. The sibling kind
  `mobius_tangent_cell` covers Mobius/log cells. The route here is a rational upper bound for `g`
  plus a separate lemma.
* **A tail for m-dependent recursions**: none. Those claims are bounded-degree only.

## CI

    python examples/concave_pooled_induction/generate.py --check
    cd examples/concave_pooled_induction/lean && lake build

Tests: `tests/test_emit_concave_pooled_induction.py` and
`tests/test_negctrl_concave_pooled_induction.py`.
