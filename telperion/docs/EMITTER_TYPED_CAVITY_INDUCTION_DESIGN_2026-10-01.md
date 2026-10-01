# Emitter design: `typed_cavity_induction` (2026-10-01)

`TypedCavityInductionEmitter`, kind `typed_cavity_induction`, module
`src/telperion/emit_typed_cavity_induction.py`.

`conjecture1_proved = False`. This kind certifies, for one explicit rational tree recursion and
one explicit finite table, a bound that holds on every finite rooted tree. It says nothing about
the Brualdi-Goldwasser conjecture, RH, or any other open problem.

## What it certifies

Some bounds on tree recursions have no single-scalar witness. The extremal value at a node
depends on what kind of node it is (its degree, the size of its children's messages), and a
proof has to carry a small table: "a tree of type `τ` has value at most `B_τ` and message in
`[ylo_τ, yhi_τ]`". The proof is then an induction in which every parent step, for every way of
choosing the children's types, lands back inside the table. Balister, Bollobás and Gerke's
treatment of the generalized Randić index is the classical example: their Lemma 4 is exactly
this induction, with types given by root degree. This kind packages the method: a finite type
table is certified as an **inductive invariant over every finite rooted tree**, with the
infinitely many parent steps reduced to finitely many exact checks.

## Overlap check: why a new kind and not a face

* `concave_pooled_induction` carries ONE scalar witness `U(msg)` and pools all children at their
  mean. It has no type table, and it cannot express "children of different kinds contribute
  differently". Its Jensen step needs concavity of a single function; a type table needs none.
* `affine_hull_dominance` proves exact maxima for each size `n <= N`: it is bounded in size, not
  a statement about all trees.
* `telescope` / `fwd_telescope` use one potential with no message caps.
* `per_size_dominance_sweep` and `gap_budget_multiplicity` work on listed configurations or one
  multiset with a knapsack; neither runs a tree induction.

None of these can state "this table is preserved by every parent step". The Lean core needed
here (a structural induction consuming a step hypothesis quantified over child-type
assignments, and the reduction from assignments to count vectors) does not exist in any of
them, so this is a new kind. It reuses the `PolyCert` Bernstein/Taylor machinery of
`concave_pooled_induction` for every interval cell.

## Setting and claim

Finite rooted trees. A node with `m >= 1` children `c_1..c_m` has

    R = y(c_1) + ... + y(c_m),     y = h(m, R),     l = l(c_1) + ... + l(c_m) + g(m, R),

and a leaf has the fixed pair `(y_leaf, l_leaf)`. `h` and `g` are rational functions of
`(m, R)` with rational coefficients.

**Types.** A finite list. Each type has a predicate on `(m, R)`: a degree range
`klo <= m <= khi` (`khi` may be open) and a bin `rlo <= R < rhi` (either end may be open). The
degree ranges form consecutive groups covering every `m >= 0`, and inside a group the bins
partition the real line, so the type of a tree is a function `tp(m, R)`. A leaf has type
`tp(0, 0)`. Each type carries a bound `B` and a message interval `[ylo, yhi]`. An **exact atom**
type carries `(E, Y)`. It is the table entry `B = E`, `ylo = yhi = Y`, so its message is pinned
(every step landing in it must produce exactly `Y`, which the closure obligations check). Its
value is bounded above by `E`.

**Claim (the inductive invariant).** For every finite rooted tree `b` (or every tree whose nodes
all have at most `D` children, in bounded mode):

    l(b) <= B[type b]     and     ylo[type b] <= y(b) <= yhi[type b].

**Corollaries.** The uniform bound `l(b) <= max_τ B_τ`. An optional **join** closes a tree at a
root with a fixed number `K` of children, a rational `gJ(R)` and a constant `C`:
`sum_i l(b_i) + gJ(sum_i y(b_i)) <= C` for every `K`-tuple of trees. This is how a statement
about half-trees becomes a statement about trees (see the BBG instance).

## The three devices

A parent step says: if child `i` satisfies the invariant of its type `t_i`, the parent satisfies
the invariant of `tp(m, R)`. Write `n_t` for the number of children of type `t`. The children
give `sum l <= S := sum_t n_t B_t` and `R in [sum_t n_t ylo_t, sum_t n_t yhi_t]`.

**(i) Enumeration, `1 <= m <= M_enum`.** For every multiset of child types (count vector `n`,
`sum n = m`) and every parent bin that meets the reachable `R`-interval, three one-variable
rational inequalities on the cell `[s, t]` where they meet:

    S + g(m, R) <= B_parent,      ylo_parent <= h(m, R),      h(m, R) <= yhi_parent.

When `s = t` (every message is exact, as in the BBG instances) the cell is a point, checked by
`norm_num`. Otherwise the inequality is multiplied by its denominator, which is certified
strictly positive, giving `N(R) >= 0`. `N` is certified by exact Bernstein coefficients on
`[s, t]`, and the cell is bisected (to depth 10) when needed. In Lean, `linarith` closes each cell
from the product facts `0 <= (R - s)^i (t - R)^(d-i)`.

**(ii) Tangent band, `M_enum < m <= M_tail`.** Take a linear majorant `g(m, R) <= a_m + s_m R` on
`R in [m ymin, m ymax]`. By default this is exact when `g` is affine in `R`, and otherwise the
tangent at the midpoint, which is valid where `g` is concave. The majorant is certified by
Bernstein cells. It makes the multiset sum **separable**:

    sum l + g <= sum_i (B_{t_i} + s_m y_i) + a_m <= m mu_m + a_m,
    mu_m = max_t (B_t + s_m y*_t)        (y* = yhi if s_m >= 0, else ylo).

So the value obligation is ONE linear inequality per degree and parent bin,
`m mu_m + a_m <= B_parent`. The closure cells of `h(m, .)` are certified per parent bin.

**(iii) Analytic tail, every `m > M_tail` at once.** Take a uniform majorant
`g(m, R) <= a_T + s_T R` for all real `m >= K0 = M_tail + 1` and `R >= K0 ymin`. This needs
`ymin >= 0`. It is certified as a two-variable polynomial inequality: with `u = m - K0 >= 0`,
`N(K0 + u, R) = sum_j u^j N_j(R)`, and every `N_j` carries its own Bernstein certificate (bounded
`R`-cell) or Taylor certificate (the unbounded last cell). With `mu_T <= 0` we get
`m mu_T <= K0 mu_T`, so ONE inequality uniform in `m`, `K0 mu_T + a_T <= B_parent`, holds per tail
bin. The two-variable closure cells of `h` are certified per tail bin. The tail group must be
the last degree group and must contain every `m >= K0`.

Without a tail (`max_children = D`) the claim is stated for `PTree.AllDeg (fun k => k <= D)`, and
nothing is claimed beyond `D`.

## The Lean (self-contained; only `import Mathlib`)

Generic, emitted once per file in namespace `TypedCavity`:

* `PTree` (`leaf` | `node m (cs : Fin (m+1) -> PTree)`), `size`, `msg`, `ell`, `typ` (the type of
  a tree), `AllDeg`;
* `Inv B ylo yhi t l y := l <= B t ∧ ylo t <= y ∧ y <= yhi t` (an `abbrev`);
* `typed_induction_core`: structural induction. It takes `Inv` of the leaf type and a step
  hypothesis "for every `k`, every `τ : Fin k -> T` and every `y l : Fin k -> ℝ`, if each child
  satisfies `Inv` then the parent satisfies `Inv` of `tp k (∑ y)`";
* `sum_by_type`, `count_sum` (`Finset.sum_fiberwise`) and `step_of_counts` /
  `join_of_counts`: a step stated for every **count vector** `c : Fin n -> ℕ` with `∑ c = k`
  gives the step for every assignment of child types;
* `separable_bound` (the tangent device) and `msg_sum_range`.

Per instance:

* `h`, `g`, the table `B`, `ylo`, `yhi` (as `![...]`, with `rfl` lemmas per entry);
* the type map `tp` as nested `if`s over degree groups, then over bins, with one lemma per
  (group, bin);
* the base;
* one lemma per cell obligation;
* one lemma per (degree, multiset), which splits `R` over the parent bins;
* one count dispatch per enumerated degree (`generalize` the counts, nested `interval_cases`,
  `push_cast`, then `linarith` from the multiset lemma);
* one band step per band degree, the tail step, `hstep` (`interval_cases` on the degree, plus
  `Nat.lt_or_ge` for the tail);
* the main theorem `<nm> : Inv B ylo yhi (b.typ tp h y0) (b.ell g h l0 y0) (b.msg h y0)`, the
  corollary `<nm>_uniform : b.ell ... <= max B`, and `<nm>_join` when a join is given.

## The dogfood (`examples/typed_cavity_induction/`)

**First instance (published): Balister-Bollobás-Gerke.** P. Balister, B. Bollobás and S. Gerke,
*The generalized Randić index of trees*, J. Graph Theory 56 (2007) 270-286. A half-tree is a
tree with one dangling edge at its root (a planted rooted tree). The dangling edge counts in the
root degree but contributes no term. For `c_T = R_{-α}(T) - β ñ(T)`, their recursion (2) reads
`c_T = sum_i (c_{T_i} + (d(v_0) d(v_i))^{-α}) - β`. At `α = γ = 1` a half-tree node with `m`
children has degree `d = m + 1`. With the message `y = 1/d`, (2) is this kind's recursion:

    h(m, R) = 1/(m + 1),     g(m, R) = R/(m + 1) - β,     leaf (y, l) = (1, -β).

The types are the root degrees `d = 1..Δ`, with `d = 1` the exact leaf atom `(-β, 1)`. The table
is their `c_d` from (4)-(5): `c_1 = -β`, `c_d = (d-1) max_{k<d} (c_k + 1/(kd)) - β`. The
theorem is their Lemma 4 for maximum degree `Δ`, `c_T <= c_{d(T)}`, in bounded mode
`max_children = Δ - 1`. Every message is exact, so every enumeration cell is a point. The join
at `K = Δ`, with `gJ(R) = R/Δ - β`, closes a tree at a vertex of degree `Δ`. Its constant
`C = (β + Δ c_Δ)/(Δ - 1)` is their Theorem 6.

* `Δ = 3`, `β_3 = 7/27` (published): table `(-7/27, -1/54, 1/27)`, `C = 5/27`. The paper prints
  `R_{-1}(T) <= (7/27) n + 11/54`, and `5/27 = 10/54` implies it. BBG's extremal construction
  (three copies of the half-tree `[2, 1]` joined at one vertex) attains `10/54`; the tests check
  this.
* `Δ = 4`, `β_4 = 139/528` (published): table `(-139/528, -7/264, 3/176, 5/132)`,
  `C = 73/528`, exactly the printed `R_{-1}(T) <= (139/528) n + 73/528`.

The hand-written companion `lean/TypedCavityInductionRandic.lean` (not generated) restates both
instances in terms of `R_{-1}` itself:

* `randic` (half-tree `R_{-1}` from its edges), `treeRandic` and `treeSize`;
* `msg_eq` (`msg = 1/deg`), `ell_eq` (`ell = R_{-1} - β n`, i.e. recursion (2)) and `join_eq`;
* `halftree_delta3` / `halftree_delta4` (Lemma 4, uniform form);
* `bbg_theorem6_delta3` / `bbg_theorem6_delta4`: every tree rooted at a vertex of degree `Δ`
  whose branches have maximum degree `<= Δ` satisfies `R_{-1}(T) <= β_Δ n + C`.

Rooting an unrooted tree at a vertex of maximum degree is not formalized; it is stated in the
file header.

**Second instance (synthetic, of our own design; no combinatorial meaning).** It exercises every
device:

    h(m, R) = 1/(1 + R),     g(m, R) = R/(1 + R) + 1/(4(m + 1)) - 3/5,     leaf (1, -3/5).

There are eight types: the leaf (exact); child counts 1 and 2, each split into two bins of `R`;
one band type for `m = 3..4`; and two tail types for `m >= 5`, split at `R = 1`. The certificate
uses enumeration for `m = 1, 2` (44 count vectors; interval messages, so mostly Bernstein
cells), midpoint tangents for the band (`m = 3`: `s = 4/25`; `m = 4`: `s = 1/9`), and the tail
with `s_T = 4/49`, `a_T = -283/5880`, `mu_T = -127/245`. Its tangent is a genuine two-variable
certificate, because `g` depends on `m`: every cell has a `u^1` part, and there are five
`R`-cells, the last one unbounded.

The generated file has 585 theorems and the companion 11. `#print axioms` on
`typed_induction_core`, `bbg3`, `bbg3_join`, `bbg4`, `bbg4_join`, `synth`, `synth_uniform` and
the four companion theorems gives `[propext, Classical.choice, Quot.sound]`. There is no `sorry`,
`admit` or `native_decide`.

## Negative control

`negctrl_adapters/adapter_typed_cavity_induction.py` lowers `β_3` to `7/27 - 1/1000` and
recomputes the table by (4)-(5). The claim is then false, not merely unproved:

* `c_3 = 4/3 - 5β` is attained by `[3, 2, 1]`.
* Joining two copies of a half-tree at a new root doubles the excess of `c_T` over `β - 2/9`.
* That excess, `14/9 - 6β`, is positive below `7/27`.

Layer 1 refuses the forgery: the degree-3 step with two degree-3 children is false by `3/500`.
The adapter mints the forgery with `check=False`, which keeps the same certificate algebra and
skips the sign checks. In the kernel, that point cell's `norm_num` cannot prove a false rational
inequality, so the main theorem does not elaborate. The true twin at `7/27` compiles clean. The
lean-gated test `tests/test_negctrl_typed_cavity_induction.py` runs both through
`generic_negative_control`.

## Refusals

`typed_cavity_certificate` raises `TypedCavityRefusal` on:

* a float anywhere, or a non-rational `h`/`g`/`gJ` (or one in symbols other than `m`, `R`);
* degree groups that overlap, leave a gap or do not end open; bins in a group that do not
  partition the line; `ylo > yhi`; more than 8 types;
* a failing base;
* any enumeration, band, tail, closure or join obligation that is FALSE at a probed point
  (reported with the exact point and value), or whose certificate stays negative to the
  subdivision limit;
* a band degree with `m mu_m + a_m > B_parent`;
* a tail with `ymin < 0`, `mu_T > 0`, `K0 mu_T + a_T > B_parent`, or a tail group that does not
  cover `m >= K0`;
* `M_enum` outside `0..6`, or `M_tail < max(M_enum, 1)`;
* a polynomial of degree above 12.

## Not supported in v1 (stated plainly), and v2

* **Rational recursions only.** v1 has no parameter boxes, no interval arithmetic and no
  logarithms.
* **v2: parameter boxes.** v2 would let the recursion depend on a parameter `λ` ranging over a
  box (or a list of boxes, possibly reaching an endpoint such as `λ = 0`). The cell obligations
  then become polynomial inequalities in `(λ, R)` on a box, certified by the same two-variable
  Bernstein/Taylor certificates the tail already uses. Transcendental terms (for example
  `log(1 + λ X)`) would enter through polynomial **Taylor enclosures with signed remainders**:
  an order-`n` lower and upper polynomial in `λ X` valid on `[0, ∞)`, scaled by `λ` where the
  margin vanishes at `λ = 0`, and proved once as a generic lemma. The type table's bounds would
  then be polynomials in `λ`, not constants.
* At most 8 types (the count dispatch uses `Fin.sum_univ_<n>`), and `M_enum <= 6`. Larger
  tables need a Pareto-pruned dispatch (a monotonicity lemma per child) rather than full
  multiset enumeration.
* The tail domain is `R >= K0 ymin`; the coupling `R <= m ymax` is not used.
* An exact atom's value is an upper bound only.

## CI

* `telperion-lean-e2e.yml` job `typed-cavity-induction-compiles`, with its paths filter and
  outputs line: `generate.py --check`, then `lake build` of both modules.
* `telperion.toml` check `typed_cavity_induction` (group `quick`): the drift net in
  `telperion-test`, run under both `sympy==1.12` and the latest sympy.
* Unit tests: `tests/test_emit_typed_cavity_induction.py` and
  `tests/test_negctrl_typed_cavity_induction.py`.
