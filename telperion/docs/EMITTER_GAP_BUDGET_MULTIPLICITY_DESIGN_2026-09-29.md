# `gap_budget_multiplicity`: pruning a multiset optimisation by a tangent-price gap budget (2026-09-29)

`conjecture1_proved = False`. This kind proves finite pruning consequences of one elementary
inequality per instance. It says nothing about the zeros of zeta or about the Brualdi-Goldwasser
Laplacian-ratio problem. The dogfood is a classical toy problem.

Module: `src/telperion/emit_gap_budget_multiplicity.py`. Dogfood:
`examples/gap_budget_multiplicity/` (`generate.py`, `lean/GapBudgetMultiplicity.lean`).

## The idea in one paragraph

Suppose you are maximising over multisets of "atoms" (parts, item sizes, child types), and the
objective is a sum of per-atom values plus possibly a concave function of an average. Put a price
`tau` on the fixed resource and take the tangent of the concave part. Every configuration's value is
then at most a constant `C` minus the sum of per-atom **gaps** `gamma(k) >= 0`. A known good
configuration, the benchmark with value `B`, leaves a budget `theta = C - B`. Any configuration that
is at least as good as the benchmark has to fit its gaps inside that budget. So an atom with gap
`g > theta` cannot appear at all, an atom with gap `g > 0` can appear at most `floor(theta / g)`
times, and the joint counts of the surviving positive-gap atoms have to solve a small knapsack.
That is the pruning pattern the kind certifies.

## The model

- Atoms are natural numbers `k`, drawn from the alphabet `[kmin, kmax]`, or from `[kmin, oo)` when
  a tail is certified.
- A configuration is a `Multiset ℕ`, written `m`.
- The value is `Phi(m) = sum_{k in m} w(k)`, plus optionally `c * log(sum_{k in m} y(k) / M)`.
- The normalisation is `sum_{k in m} ell(k) = M`, where `M` may involve natural parameters (like
  `t` in `N = 3t + 4`) in the separable case.
- The concave part is limited to `c * log x` with `c > 0`. That is the only family with an emitted
  tangent lemma. Anything else is refused, including `c < 0`, which is convex, so the tangent bound
  would run the wrong way.
- The gap is `gamma(k) = tau * ell(k) - w(k) - (c / x0 / M) * y(k)`. The budget is
  `theta = tau * M + c * log x0 - c - B`. In the separable case (`c = 0`) these reduce to
  `tau * ell(k) - w(k)` and `tau * M - B`.
- Expressions are written in a small DSL: `K` is the atom label, `gb_log(q)` is `log` of a positive
  rational, `gb_logk(s)` is `log(k + s)`, and the rest are rational polynomials. `sp.log` is refused
  on purpose. Sympy rewrites `log(1/3)` to `-log 3` on its own, which would drift away from the
  Lean text.

## What the kernel checks

The generic core is emitted once per file:

| lemma | content | proof |
|---|---|---|
| `gapBudget_log_tangent` | `c log x <= c log x0 + (c/x0)(x - x0)` for `c >= 0` | `Real.log_le_sub_one_of_pos` at `x/x0` |
| `gapBudget_of_sep` | `sum ell = M`, `B <= sum w` imply `sum gamma <= tau M - B` | `Multiset.sum_map_sub` / `sum_map_mul_left` |
| `gapBudget_of_concave` | the same with the concave part: `<= tau M + c log x0 - c/x0 x0 - B` | the above plus the tangent |
| `gapBudget_count_mul_le` | if every gap is `>= 0`, then `count a * g <= theta` for any `g <= gamma a` | split by `filter (. = a)`, `Multiset.filter_eq'` |
| `gapBudget_nat_cap` | `x g <= theta < (cap+1) g` implies `x <= cap` | `nlinarith` |
| `gapBudget_knapsack` | `sum_{a in A} count a * g a <= theta` | `Finset.sum_multiset_map_count`, `sum_filter_of_ne` |

Each instance then emits:

- the model `def`s `nm_w`, `nm_ell`, (`nm_y`) and `nm_gap`, where `nm_gap` is literally the gap
  term the core lemma expects, so the lemma's hypothesis `hγ` is `fun _ => rfl`;
- one gap lemma `g_k <= nm_gap k` per listed atom. A rational gap takes the exact route (`simp only`
  followed by `ring_nf`, an equality). An irrational gap consumes an `enclosure_tree` theorem. The
  log atoms are `Real.log_two_gt_d9`, the Taylor estimate, and the `Real.log_mul` fold. This is
  REUSED from `emit_enclosure_tree`, not re-implemented, and shared subtrees are proved once per
  file;
- the tail lemma `nm_tail : K0 <= k -> g_tail <= nm_gap k`, when there is a tail;
- the `theta` enclosure, when `theta` is irrational;
- `nm_bench`: the benchmark satisfies every hypothesis of the main theorem and attains `B` exactly.
  This makes the main theorem non-vacuous and applicable to every optimum;
- `nm`, the main theorem: from `hA` (atoms in the alphabet), `hl` (the normalisation), `hdom`
  (concave case only: positive mean) and `hB : B <= Phi(m)`, it concludes the exclusions
  `count k = 0`, the caps `count k <= cap`, the tail statement `(∀ k ∈ m, k < K0)` (or a per-atom
  tail cap), and the knapsack `[count a1, ...] ∈ [explicit list]`.

The knapsack is decided over the naturals. The rational bounds are cleared by a common denominator,
and the statement is written as `∀ x ∈ List.range (cap+1), ...` for `decide`. The nested
`∀ x ≤ cap` form has no `Decidable` instance past two binders. Rationals are never decided in the
kernel.

## The tail (infinite alphabets)

For `k >= K0` the gap must have the shape `P k - c_t log(k + s) + d` with `c_t >= 0`, which is
convex. The same tangent lemma at `K0 + s` gives
`gamma(k) >= gamma(K0) + (P - c_t/(K0+s)) (k - K0)`. So the tail inherits the anchor bound
`g_{K0}` once a certified `P_lo >= c_t/(K0+s)` exists. In the dogfood, `P = log 3 / 3 = 0.366...`
against `1/5`.

## Where the numbers come from, and rounding

- `theta_hi` is the enclosure's upper end rounded UP to the grid `1/D` (default `D = 10^6`).
- `g_k` is the lower end rounded DOWN.
- A caller may CLAIM `gap_lo = {k: g}` or `theta_hi`. The enclosure fold refuses any claim it does
  not imply, and an exact gap accepts no other bound.
- Rounding only loosens the statements, and the kernel re-derives every one of them.

## Refusals

Each refusal has a test in `tests/test_emit_gap_budget_multiplicity.py`.

- **Bad input.** Floats, bools, non-rational constants, and `sp.log`/`exp`.
- **Non-concave or degenerate concave part.** A family other than `log`, `c < 0`, `c = 0`, or
  `x0 <= 0`.
- **Log-domain violations.** `log(k + s)` with `k + s <= 0` at an atom, or `gb_log(q)` with
  `q <= 0`, `q = 1`, `q < 1/2`, or `q > 340`.
- **Benchmark problems.** An atom outside the alphabet, a non-natural or repeated multiplicity, a
  normalisation `!= M`, or a mean `<= 0`.
- **A budget that is not uniform or not consistent.** A `theta` that depends on a parameter or on
  `k`, or a certified `theta < 0`.
- **Gap problems.** A gap that is negative, or not provably `>= 0`, at a listed atom ("the price
  does not dominate").
- **Forged claims.** A claimed bound the fold does not imply.
- **Tail problems.** A tail not of the certified shape, a slope not certified, or a missing or
  stray `tail_start`.
- **Oversized input.** More than 48 listed atoms, or a knapsack box above 4096 points.
- **Pointless or inconsistent certificates.** A budget that prunes nothing, a benchmark that
  violates its own derived caps or knapsack (a self-check that catches inconsistent input), unknown
  spec keys, or non-identifier names.

## Dogfood

The main dogfood is the classical maximum product of positive parts with a fixed sum `N`. The
objective is `Phi = sum log k`, the normalisation is `sum k = N`, and the price is
`tau = log 3 / 3`. That gives the gap `gamma(k) = k log 3 / 3 - log k`, which is `>= 0` with
equality only at 3. The results hold uniformly in `t`:

| instance | benchmark | theta | certified pruning |
|---|---|---|---|
| `maxprod_mod0` (`N = 3t`) | `3^t` | 0 | no 1s, 2s or 4s, every part `< 5`, so all parts are 3 |
| `maxprod_mod2` (`N = 3t+2`) | `{2} + 3^t` | `gamma(2)` | no 1s or 4s, at most one 2, parts `< 5` |
| `maxprod_mod1` (`N = 3t+4`) | `{4} + 3^t` | `gamma(4) = 2 gamma(2)` | no 1s, `<= 2` twos, `<= 1` four, parts `< 5`, `(n2, n4)` in `{(0,0),(0,1),(1,0),(2,0)}` |

A second, small instance exercises the concave step: 10 items of size 1..6, with
`Phi = sum -k^2/9 + 12 log(mean k)`. The optimum `2^8 3^2` is the benchmark.

- With the tangent at the benchmark mean `x0 = 11/5`, `theta = 2/99`, which is exactly rational
  because the log terms cancel. That prunes 1, 4, 5 and 6 and caps the 3s at 2.
- With the tangent at `x0 = 2`, `theta = 14/9 + 12 log(10/11)`, which needs enclosures of `log 2`
  and `log(11/5)`. The caps are `(n1, n2, n4) <= (1, 9, 2)`, with a decided 21-vector knapsack.

`generate.py` appends a cross-check that is not emitter output: `maxprod_mod1_classical` states the
`N = 3t+4` result in product form (`m.sum = 3t+4`, `4 * 3^t <= m.prod`) and proves it by feeding
the emitted theorem (`Real.log_multiset_prod`, `Nat.cast_multiset_prod`).

The build has 59 emitted theorems plus the cross-check. `#print axioms` shows
`[propext, Classical.choice, Quot.sound]` on all 18 checked names, and there are no warnings. It
builds in about 40 s from warm Mathlib oleans.

## Negative control

`negctrl_adapters/adapter_gap_budget_multiplicity.py` takes `maxprod_mod2` and raises the gap bound
at 2 to `1/20`. The truth is `0.03926...`, and `1/20` is above `theta_hi`. With that bound the main
theorem claims `count 2 = 0`, which is FALSE: the benchmark `{2} + 3^t` meets every hypothesis and
contains one 2. Layer 1 refuses the claim. The adapter mints the forgery by hand, and the kernel
rejects it at the forged enclosure's `linarith`. The true twin compiles clean. Both sides were
checked by hand through `generic_negative_control` against the dogfood env.

A second forgery, `make_false_cert_cap`, keeps every gap bound and `theta_hi` honest and changes
only the derived cap at 2, from `floor(theta_hi / g_2) = 1` to 0. The kernel rejects it at the
`norm_num` side condition of `gapBudget_nat_cap 0`. The lean-gated
`test_cap_forgery_is_kernel_rejected` covers it; the harness keys only one adapter per emitter.

A skeptic review found that a `(log(k + s))^2` term used to slip past the tail-shape check. It is
now refused, and the refusal is pinned by `test_refuses_a_tail_with_a_power_of_log_k`.

## Limitations (stated plainly)

- The main theorem is conditional pruning. It does not identify the optimum among the survivors.
- `hdom` (a positive mean) is a hypothesis of the concave main theorem. It is not derived, even
  when `y > 0` on the alphabet.
- Atoms are natural-number labels. A general finite alphabet has to be indexed by naturals, with
  `w`, `ell`, `y` given as DSL polynomials in `k`. Tabulated data is not supported yet.
- The only concave family is `c log x`. `log(1 + x)` is covered by shifting `y` when `ell = 1`.
- `tau` must be supplied by the caller. It is not optimised.
- The tail shape is limited to one `log(k + s)` term with an affine remainder.
- Exact-route gap lemmas rely on `simp only` + `ring_nf` closing a rational equality. That covers
  every dogfood case, but it is not guaranteed for an arbitrary DSL expression. The kernel would
  then reject rather than accept.
