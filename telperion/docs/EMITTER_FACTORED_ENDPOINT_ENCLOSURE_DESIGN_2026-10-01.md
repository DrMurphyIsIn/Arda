# Emitter design: `factored_endpoint_enclosure` (2026-10-01)

`FactoredEndpointEnclosureEmitter`, kind `factored_endpoint_enclosure`, module
`src/telperion/emit_factored_endpoint_enclosure.py`. It comes with an extension of
`transcendental_enclosure`: a new face, `log_taylor`.

`conjecture1_proved = False`. This kind certifies elementary real inequalities in one or two
variables. It says nothing about the Brualdi-Goldwasser conjecture, RH, or any other open problem.

## The problem

Many inequalities we want are tight at an endpoint. The function has zero margin at a point `l = s`
on the boundary of the domain, and the quantity we actually care about is a quotient that is
`0/0` there. Take `(1 + l)^(1/l) <= e` near `l = 0`. Written as `(1/l) log(1 + l) <= 1`, it is the
statement `0 <= F` for `F(l) = l - log(1 + l)`, and the quantity of interest is `F / l`. At
`l = 0`, `F` vanishes, `F / l` is undefined, and interval arithmetic on `F / l` blows up on any box
that touches `0`.

The existing kinds handle this badly. `transcendental_enclosure` encloses `log(1 + x)` on a box,
but with no factoring. `enclosure_tree` encloses constants. `mobius_tangent_cell` covers one
variable with logs by tangent cells, and its own documentation says that a claim tight to order 2
or more at the bisection cap is refused. Its example is the Pade bound near `x = 0`. That refusal
is the gap this kind fills.

## The shape

Variables `l` (the parameter with the endpoint) and, optionally, `x`. The claim is

    0 <= F(l, x)      for every l in [A, B], x in [C, D]          (a CLOSED box)

where the endpoint `s` sits at the edge of the domain: `s <= A` (side `right`) or `s >= B`
(side `left`). `F` is a rational function of `(l, x)` plus `log(1 + u_i)` atoms with polynomial
`u_i`. Over a positive denominator,

    D F = N0 + sum_i kappa_i log(1 + u_i)        (D, N0, kappa_i, u_i polynomials).

## The certificate

1. **Taylor with signed remainder.** Each log atom is replaced by its Taylor polynomial `T_n(u)`,
   with the order chosen so that the remainder has the sign we need for every `u >= 0`. An odd
   order gives `log(1 + u) <= T_n(u)`, used when `kappa_i <= 0`. An even order gives
   `T_n(u) <= log(1 + u)`, used when `kappa_i >= 0`. So

       Q := N0 + sum_i kappa_i T_{n_i}(u_i) <= D F       on the domain.

   With no log atoms, `Q = D F` exactly. This is the closed-form route.
2. **Factorization.** `Q = (sigma (l - s))^k H` is an exact polynomial identity, with
   `sigma = +1` on the right side and `-1` on the left. `H` comes from exact polynomial division,
   or it is supplied by the caller and checked. If the claimed power does not divide `Q`, the
   certificate is refused.
3. **Box signs.** The domain is covered by bisection. On each box we check four things with exact
   rational tensor-Bernstein coefficients: `H >= 0`, each `u_i >= 0`, each `sigma_i kappa_i >= 0`,
   and each irreducible factor of `D` is `> 0`. A box that touches `l = s` is an ordinary box:
   `H` is a polynomial, so nothing is singular there any more.

If no order works, the orders are searched upward to 16. When a box sign fails at the depth
limit, the generator evaluates `F` to 60 digits on a 9 x 9 rational grid. If `F < 0` at some grid
point, the claim is reported FALSE at that exact point. Otherwise it is reported OBSTRUCTED.

### Why the endpoint stops being a problem

`0 <= (sigma (l - s))^k` holds on the closed box, so `0 <= H` and `Q = t^k H <= D F` give
`0 <= D F`, and `D > 0` gives `0 <= F`. This holds at `l = s` too. The quotient `F / t^k` is never
evaluated. Only `H` is, and `H` is a polynomial with an honest enclosure on every box.

## Lean

The generic section is emitted once per file.

* `factored_endpoint_core` is the one generic lemma. It works for any type `α` and any box
  predicate `Box`. From `0 <= t`, `0 < D`, `Q <= D F`, `Q = t^k H` and `0 <= H` on the box, it
  proves `0 <= F` on the box, endpoint included. One-variable instances use `α = ℝ`, and
  two-variable instances use `α = ℝ × ℝ`.
* `factored_endpoint_quot` gives the quotient corollary `0 <= F / t^k`.
* The `log_taylor` section, namespace `FEELogTaylor`, comes from `transcendental_enclosure` (see
  below). It holds the generic `log_le_T` / `T_le_log`, and `upper_<n>` / `lower_<n>` for each
  order used in the file.

Per instance we emit:

* the definitions `<nm>_F` (the caller's `F`, logs printed as `Real.log (1 + u)`), `<nm>_D`,
  `<nm>_Q`, `<nm>_H`;
* `<nm>_fac`, the identity `Q = t^k H`, by `ring`;
* per box `i`:
  * `<nm>_b<i>_H`: `0 <= H`, by `linarith` over the Bernstein products
    `(l-a)^i (b-l)^(p-i) [(x-c)^j (d-x)^(q-j)]`;
  * `<nm>_b<i>_D`: `0 < D`, from per-factor Bernstein facts and `mul_pos` / `pow_pos`;
  * `<nm>_b<i>_low`: `Q <= D F`. `D F = N0 + sum kappa log` is proved by `field_simp; ring`.
    Each atom contributes `0 <= u` and `0 <= sigma kappa` (Bernstein), the Taylor lemma, and
    `mul_nonneg`, and `linarith` closes the goal;
  * `<nm>_b<i>`: the core lemma applied to the box;
* `<nm>`, which states `∀ l ∈ Set.Icc A B, [∀ x ∈ Set.Icc C D,] 0 ≤ <nm>_F l [x]`. The proof
  follows the bisection tree with `le_total`;
* `<nm>_quot`, which states `0 ≤ <nm>_F l [x] / t ^ k` for `l ≠ s`. It is stated only off the
  endpoint, because at `l = s` Lean's `F / 0 = 0` would make it vacuous.

No proof uses `sorry`, `admit`, `native_decide` or `polyrith`. The tactics are `ring`,
`field_simp`, `linarith`, `norm_num`, and the generic lemmas.

## Decision: extend `transcendental_enclosure`, do not duplicate

`transcendental_enclosure` already had the tangent bound `log(1 + x) <= x`, its `_upper` theorem,
via `Real.log_le_sub_one_of_pos`. That is the order-1 case of the bounds this kind needs. Writing
a second log-Taylor prover inside the new module would have left two places that each own
"`log(1 + u)` against a polynomial for `u >= 0`".

**Decision:** we added a face `log_taylor` to `transcendental_enclosure` and made its Lean
generator, `log_taylor_lean(ns, orders)`, the single source. The new kind imports it.

* `T n u = sum_{j<n} (-1)^j u^(j+1)/(j+1)` is defined once.
* `log_le_T` (odd `n`) and `T_le_log` (even `n`) are proved once for every `n`. `T n - log(1 + .)`
  vanishes at `0`. By the geometric sum (`geom_sum_mul_neg`), its derivative is
  `-(-t)^n / (1 + t)`, and the mean value theorem (`exists_hasDerivAt_eq_slope`) gives the sign.
  These are the general remainder-sign forms. For example, `log(1 + u) >= u - u^2/2` is
  `lower_2`, and `log(1 + u) <= u - u^2/2 + u^3/3` is `upper_3`.
* Each requested order then gets its explicit polynomial statement, `upper_<n>` / `lower_<n>`.

The existing `log` face is unchanged. The example `examples/transcendental_enclosure` gains a third
instance, `log1p_taylor`, with orders 1..5, and is regenerated. Its input hash moves because the
emitter's source changed.

We kept the box-plus-factorization logic out of `transcendental_enclosure`. That kind's statements
are rational enclosures of a transcendental expression, and the new statements are signs of
two-variable functions on box covers, with a factorization and a generic core. Those are a
different shape, so they get a new kind.

## Dogfood (`examples/factored_endpoint_enclosure/`)

All instances are classical or synthetic.

| instance | claim | `k` | log order | boxes |
|---|---|---|---|---|
| `log_exp` | `0 <= l - log(1 + l)` on `[0, 1/10]`. This is `(1/l) log(1 + l) <= 1`, i.e. `(1 + l)^(1/l) <= e`. | 1 | 3 (upper) | 1 |
| `log_sharp` | `l - log(1 + l) >= (117/250) l^2` on `[0, 1/10]` (margin about 1/1000 at `l = 1/10`) | 2 | 5 (upper) | 1 |
| `rational` | `(1 + l)^-2 >= 1 - 2l + 3l^2 - 4l^3` on `[0, 1]`: `D F = l^4 (5 + 4l)`, `H = 5 + 4l` | 4 | none | 1 |
| `synth2` | `l (x - l)^2 + l^2 x >= 0` on `[0, 1/2] x [1/8, 1]`: `H = (x - l)^2 + l x` | 1 | none | 3 |
| `pade` | `log(1 + l) <= l (6 + l)/(6 + 4l)` on `[0, 1/3]`: `D = 3 + 2l`, `H = 1/12 - l/10 - 2l^2/5` | 4 | 5 (upper) | 1 |

The dogfood has 54 theorems. Every capstone, the core lemma and the Taylor lemmas print axioms
`[propext, Classical.choice, Quot.sound]`.

On `sin`: Telperion has no `sin` enclosure, so `sin(l)/l >= 1 - l^2/6` is not an instance. The
rational instance stands in for it, as the spec allowed. A `sin` route needs a `sin_taylor` face
with the same remainder-sign proof, which Mathlib's alternating-series bounds would support.
`F` containing `sin` (or `exp`, or any non-log function) is refused.

`pade` is the case `mobius_tangent_cell` refuses. With order 3 the factorization by `l^4` succeeds,
but `H = -2/3 < 0`. The search moves on to order 5, where `H > 0` on `[0, 1/3]`.

## Negative controls

* **Registered adapter** (`negctrl_adapters/adapter_factored_endpoint_enclosure.py`). The forgery
  is `l - log(1 + l) >= (47/100) l^2` on `[0, 1/10]`. The true minimum of `(l - log(1 + l))/l^2`
  there is `0.468982...` at `l = 1/10`, so the claim is FALSE by about 1/1000. Layer 1 refuses it:
  "FALSE: the claim fails at l = 1/10". The adapter mints it with `check=False` and one box, so
  only the constant differs from the true twin `117/250`. The kernel rejects it, because
  `linarith failed` in the box lemma `0 <= H`, where `H(1/10) < 0`. The true twin compiles.
* **Two-variable pair** (run by the tests with the same harness). The claim is
  `l (x - l)^2 + l^2 x - m l >= 0` on `[0, 1/2] x [1/4, 1]`, where `min H = 3/64` at `(1/8, 1/4)`.
  `m = 3/64 + 1/1000` is false by exactly `1/1000` and is kernel-rejected.
  `m = 3/64 - 1/1000` compiles (5 boxes).

## Refusals

The certificate refuses:

* floats;
* functions other than `log`;
* a non-polynomial log argument;
* a log that is not linear in the cleared numerator (products, powers, or nested logs);
* a log in the denominator;
* free symbols other than `l` and `x`, and non-integer powers;
* an endpoint inside the domain, a bad `side`, or an empty or reversed range;
* `k` outside `1..12`;
* a Taylor order of the wrong parity, or the wrong number of orders;
* a `k` that does not divide `Q`;
* a supplied `H` that does not match;
* a cofactor not certified `>= 0` at the depth limit (FALSE with a located point, or OBSTRUCTED).
  This includes a log argument with `u < 0` somewhere and a denominator that changes sign;
* a polynomial degree above 12.

`verify_certificate` re-checks every identity, every Bernstein form and the tiling, independently.

## Scope

* The Taylor-with-signed-remainder route covers `log(1 + u)` atoms. The mean-value route
  (`omega` enclosed by derivative bounds on the hull) is not implemented. Nor are `sin` or `exp`
  atoms.
* Every box is closed and has rational corners, and the domain is a single rectangle.
* One endpoint factor `(l - s)^k` per instance. A factor in `x`, or several vanishing atoms with
  different orders, is not supported.
