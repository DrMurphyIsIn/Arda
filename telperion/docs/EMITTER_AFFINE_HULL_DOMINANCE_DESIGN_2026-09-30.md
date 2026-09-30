# Emitter design: `affine_hull_dominance` (2026-09-30)

`AffineHullDominanceEmitter`, kind `affine_hull_dominance`, module
`src/telperion/emit_affine_hull_dominance.py`.

`conjecture1_proved = False`. This kind certifies exact maxima of explicit tree recursions over
all trees on a bounded number of vertices. It says nothing about any open problem.

## What it certifies

Some tree invariants are computed by a recursion over planted branches, where each branch carries
a small vector of numbers instead of a single one. The running example is the Randic-weighted
matching sum

    pi(T) = sum over matchings M of T of  prod_{uv in M} 1 / (deg u * deg v).

A planted branch is a rooted tree whose root will be joined to one parent. If its root has `c`
children with states `(Z_i, W_i)`, put

    P = prod_i Z_i,    Q = sum_i W_i prod_{j != i} Z_j,    Z = P + Q/d,    W = P/d,   d = c + 1,

and at a root with `k` children `pi = P + Q/k`. A single vertex is `(Z, W) = (1, 1)`.

The emitter proves, for every `n = 2..N`,

    M_n = max { pi(T) : T a tree on n vertices }  =  (an explicit rational),

as `IsGreatest`. It also proves that every tree attaining `M_n` has every branch state and every
partial bundle state on the kept hull points (defined below), and it checks an explicit list of
maximizers, one rooting per isomorphism class.

## The general shape

The emitter works in any dimension `D`. A **bundle** is the multiset of branches hanging below
one vertex. Branches and bundles both carry a state in `Q^D`, and the recursion has four parts:

| part | formula | example (matching sum) |
|---|---|---|
| empty bundle | `e` | `(1, 0)` |
| bundle plus child | `(x (*) z)_i = sum_{j,l} T[i][j][l] x_j z_l` | `(P, Q) (*) (Z, W) = (PZ, QZ + PW)` |
| planting, `c` children | `(P_c x)_i = sum_j P_c[i][j] x_j` | `P_c = [[1, 1/(c+1)], [1/(c+1), 0]]` |
| root value, `k` children | `pi = F_k . x` | `F_k = (1, 1/k)` |

In Lean a tree is `RTree.node (children : List RTree)`. We have `bundle [] = e`,
`bundle (t :: l) = bundle l (*) branch t`, `branch (node l) = P_{|l|} (bundle l)` and
`pi (node l) = F_{|l|} . bundle l`. A tree on `n` vertices can be rooted at any vertex, so `M_n`
is the maximum of `pi` over rooted trees of size `n`. The recursion **defines** the quantity.
That the matching recursion computes the matching sum is the classical cavity identity. We do not
formalize it; the tests check it against direct matching enumeration on every tree with at most
8 vertices.

## The key lemma and why dual form

Every map has **nonnegative coefficients** and is multilinear. With the rest of the tree fixed,
`pi` is therefore a nonnegative linear functional of the state of any one branch or bundle, and
a nonnegative covector pulls back to a nonnegative covector through `(*)` and `P_c`. Take a
candidate state that is dominated componentwise by a convex combination of states of the same
**class** (the same number of vertices, and for bundles the same child count, which fixes the
planting degree). Swapping it out never lowers `pi`. If the domination is strict, the candidate
can never occur in a maximizer.

The Lean proof states domination in **dual** form:

    Dom  K x  :=  for all a >= 0 there is p in K with a.x <= a.p
    SDom K x  :=  for all a > 0  there is p in K with a.x <  a.p

This keeps the generic proof short:

* **Transitivity is one line.** If `x` is dominated by a candidate list and every candidate is
  dominated by `K`, then `x` is dominated by `K`. Double convex combinations never appear.
* **One step of the recursion is a pull-back.** `a . (x (*) z) = b . x` with
  `b_j = sum_{i,l} a_i T[i][j][l] z_l`, and `b >= 0` when `z >= 0`. The other argument and
  `P_c` work the same way (`dot_mul_left`, `dot_mul_right`, `dot_plant`).
* **The primal witness implies both forms.** Weights `w >= 0` with `sum w = 1`,
  `x <= sum w_k K_k`, strict in at least one coordinate, give `Dom` and `SDom`
  (`exists_ge_combo`, `witOK_sound`). This is the only place convex weights appear.

The strict part needs strictly positive covectors to pull back to strictly positive ones. The
**sign conditions** (`Rec.Signs`, decided per instance) guarantee it. Fix a distinguished
coordinate `z0`. Then `e >= 0` with `e[z0] > 0`; `T >= 0` with `T[z0][z0][z0] > 0`; every
coordinate `j` has some `T[i][j][z0] > 0` and some `T[i][z0][j] > 0`; and for every `c < N`,
`P_c >= 0`, `P_c[z0][z0] > 0`, and every column of `P_c` has a positive entry. Under these
conditions every true state is nonnegative with a positive `z0` coordinate. That lets
`pullL_pos`, `pullR_pos` and `pullP_pos` carry strict positivity through each step.

## The certificate

For every bundle class `(s, c)` with `s < N`, and every branch class `m < N`, the certificate
lists:

* **Kept points.** These are the candidates that maximize some strictly positive covector over
  the class: hull vertices, plus points in the relative interior of hull edges. Ties are kept and
  equal values are merged.
* **One witness per candidate,** in the checker's own enumeration order. A witness is `kept i`
  (the candidate equals kept point `i`) or `dom w` (rational convex weights over the kept list,
  with componentwise domination that is strict in some coordinate).

The **Lean checker** `Cert.Valid` builds the candidate lists itself, so no candidate can be left
out:

* `candB s c` is `e` for the class `(0, 0)`. Otherwise it is
  `kept(s - j, c - 1) (*) keptBranch(j)` for every `j = 1..s`.
* `candH m` is `P_c (kept(m - 1, c))` for every `c = 0..m-1`.

`Cert.Valid` also checks that every kept point is nonnegative and positive at `z0`. It is closed
by **one `decide +kernel`**, which does exact rational arithmetic in the kernel with the standard
axioms only.

For each `n`, two more checks are decided:

* **`hV`**: every kept root bundle `p` of `(n - 1, k)` has `F_k . p <= M_n`.
* **Attainment**: the listed maximizer trees have `n` vertices and `pi = M_n`.

Why this is enough. `inv_bundle` and `inv_branch` show, by mutual structural induction on
`RTree`, that every true state is weakly dominated by its class's kept list. With `hV` this gives
the upper bound (`pi_le`), and the attaining tree gives equality (`isGreatest_pi`).

`kept_bundle` and `kept_branch` prove a sharper dichotomy: either a subtree is kept all the way
down (`KeptT`/`KeptL`), or its state is strictly dominated. Strict domination propagates to the
root, so a tree containing a strictly dominated subtree has `pi < M_n` when `F_k > 0`. Hence
`kept_of_pi_eq`: every maximizer is kept all the way down.

## The Lean (self-contained; only `import Mathlib`)

The generic part is emitted once per file, about 640 lines in the `HullDom` namespace. It
contains:

* the recursion, the tree type, and the dual-form domination predicates;
* the witness checker, the pull-back lemmas, and the four one-step transport lemmas
  (`mul_dom`, `mul_sdom_left`, `mul_sdom_right`, `plant_dom` / `plant_sdom`);
* the two mutual inductions;
* `pi_le`, `kept_of_pi_eq` and `isGreatest_pi`.

Each instance then emits:

* `<nm>_R` (the recursion) and the kept tables `<nm>_KBt` / `<nm>_KHt`;
* the witness tables `<nm>_WBt` / `<nm>_WHt` and the certificate `<nm>_C`;
* `<nm>_signs` and `<nm>_valid`, both by decide;
* `<nm>_F_nn` / `<nm>_F_pos`;
* for each `n`: `<nm>_hV_n`, `<nm>_listed_n`, `<nm>_max_n` (`IsGreatest`) and `<nm>_kept_n`;
* the main theorem `<nm>`, the conjunction of all `IsGreatest` statements.

## The dogfood (`examples/affine_hull_dominance/`)

`generate.py --check` regenerates the file byte for byte. The Lake project pins Mathlib v4.32.0.

| instance | D | N | kept points | candidates (`dom` witnesses) | `M_N` | maximizers |
|---|---|---|---|---|---|---|
| `matching_sum` | 2 | 14 | 222 | 1290 (897) | `M_14 = 9477/512` | unique for every `n <= 14` |
| `randic_sum` | 3 | 12 | 209 | 700 (245) | `M_12 = 103/24` | 2 at `n = 7, 8`; 4 at `n = 9` |
| `synthetic` | 2 | 12 | 181 | 536 (156) | `M_12 = 103451/15552` | unique (the path) |

The three instances are:

* **`matching_sum`**: the Randic-weighted matching sum. Its values are
  `M_2..M_14 = 2, 2, 5/2, 3, 29/8, 9/2, 43/8, 27/4, 65/8, 81/8, 783/64, 243/16, 9477/512`.
* **`randic_sum`**: `1 + sum_{uv in E} 1/(deg u deg v)`. The recursion is three-dimensional:
  `(Z, W, V) = (1, edge sum inside the branch, 1/deg(root))`, with `F_k = (1, 1, 1/k)`.
  The `+ 1` is deliberate. `Z` is identically 1, so it does not change the maximizers, and it
  makes `F_k` strictly positive, which the maximizer theorem needs. Without the `+ 1` the emitter
  still certifies the value (`maximizers=False`); the tests cover that path. The ties at
  `n = 7, 8, 9` show that hull-edge points are kept.
* **`synthetic`**: a recursion made up for test coverage, with no claimed combinatorial meaning.
  It uses the matching bilinear map with `P_c = [[1, 2/(c+1)^2], [1/(c+2), 0]]` and
  `F_k = (1, 2/k^2)`, which gives larger hulls (up to 9 kept points in one class).

The file has 199 theorems, and every main and maximizer theorem prints
`[propext, Classical.choice, Quot.sound]`. **`lake build` of the whole file took 61 s** on a
loaded Apple-silicon machine with `OMP_NUM_THREADS=1`.

The tests cross-check the certified values and maximizer lists against brute force over every
tree with at most 9 vertices, for all three recursions. The maximizer lists are compared up to
isomorphism.

## Negative control

`negctrl_adapters/adapter_affine_hull_dominance.py` uses the matching sum at `N = 6`, where the
true value is `M_6 = 29/8`. The forgery:

* removes every maximizing root bundle from the kept lists of `(5, k)`, one per root vertex of
  the maximizer;
* gives the candidates that produced them a convex witness that does not dominate them;
* claims the second-best value, `7/2`, as `M_6`.

The claim is **false**, since a tree attains `29/8`. Layer 1 (`verify_certificate`) refuses it.
The forged value is still attained by a tree, and `hV` still holds. The only wrong objects are
the forged witnesses, so `decide` on `Cert.Valid` fails and the kernel rejects the file. The
true twin compiles with the standard axioms. The lane ran the generic harness by hand against
`examples/affine_hull_dominance/lean`: the forged file was rejected and the true twin compiled
clean.

## Refusals

`hull_dominance_certificate` / `hull_recursion` raise `ValueError("REFUSED: ...")` on:

* a float, or a non-rational entry;
* shape errors (`dim`, `e`, `T` indices, `P`, `F`, `z0`);
* a planting or root entry that depends on another symbol;
* any failing sign condition: a negative coefficient, a `z0` entry that is not positive, or a
  coordinate or column with no positive entry;
* `maximizers=True` with a root covector that is not strictly positive;
* `N` outside `[2, 16]`;
* a class with more than 4000 candidates;
* too many tied trees (the payload cap).

`verify_certificate` re-checks every witness exactly, in the Lean enumeration order, before
emission.

## Not proved, and not supported (stated plainly)

* **Completeness of the maximizer list up to isomorphism is not a kernel theorem.** The kernel
  proves that every maximizer is kept all the way down and that every listed tree attains
  `M_n`. The step "these are all the isomorphism classes" is computed by the generator's payload
  propagation, which is complete by the same exchange argument, and it is checked by brute force
  in the tests for `n <= 9`.
* The recursion must be multilinear with nonnegative coefficients and satisfy the sign
  conditions. Signed recursions and recursions with non-rational coefficients are out of scope.
* States are exact rationals. For `D >= 3` the kept set is found by exact LPs (sympy's
  `simplex`); for `D = 2` by the exact monotone chain. Classes are meant to be small, so the
  kernel check takes seconds to minutes.
* Classes are indexed by size and child count. That covers recursions whose planting depends
  only on the child count, not on any other data of the subtree.

## CI

The `affine-hull-dominance-compiles` job in `.github/workflows/telperion-lean-e2e.yml`, and the
`[[check]] affine_hull_dominance` entry (group `quick`) in `telperion.toml`.
