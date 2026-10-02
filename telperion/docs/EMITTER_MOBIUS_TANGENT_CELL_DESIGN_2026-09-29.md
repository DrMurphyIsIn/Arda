# `mobius_tangent_cell` -- tangent-line cells with a Mobius term, convex majorant at two endpoints (2026-09-29)

`conjecture1_proved = False`. Everything below is an elementary one-variable real inequality with
rational data. Nothing here says anything about the zeros of zeta, and nothing here is a step on the
Brualdi-Goldwasser maximizer question; the dogfood deliberately uses unrelated classical bounds.

**Technique.** Tangent-line cells, a Mobius term kept when convex and linearised when concave, and a
convex majorant checked at the two cell endpoints.

Module: `src/telperion/emit_mobius_tangent_cell.py`. Kind: `mobius_tangent_cell`.

## Statement family

    F(x) = a + b x + sum_i kappa_i log(alpha_i + beta_i x) + sigma / (B + A x)  <=  0    on [P, Q]

All data rational; `kappa_i > 0`; `alpha_i + beta_i x > 0` and `B + A x > 0` at both endpoints (both
are affine, so on all of `[P, Q]`). `sigma` has either sign or is 0 (no Mobius term). Several log
terms are supported (a positive combination of concave terms is concave).

The problem may be given in three ways (the family spec dict):

* the template fields `{a, b, logs: [(kappa, alpha, beta), ...], sigma, B, A, p, q}`;
* two sides `{lhs, rhs, var, p, q}` (sympy expressions); `F = lhs - rhs` is split EXACTLY: every
  log atom must be `c log(affine)`, the rest goes through `sp.apart` and must be `affine + at most
  one simple pole`; a negative denominator on the interval is normalised (sign moved into `sigma`);
  the emitted `<name>_sides` theorem then states the original `lhs <= rhs`;
* a prebuilt `{problem: MobiusTangentProblem}`.

Optional: `breakpoints` (interior cell boundaries to start from), `max_depth`, `max_cells`.

## The certificate (per cell `[p, q]`, rational tangent point `t`)

1. **Logs.** For each log term, `u = alpha + beta t > 0` and a rational `H >= log u`; then
   `log y <= H + (y - u)/u` (concavity: `Real.log_le_sub_one_of_pos` at `y/u` plus `Real.log_div`).
2. **The constant `H`.** `u = 2^n v` with `v in [2/3, 4/3)`;
   `log u = n log 2 + log v`, `log v <= -S + r` with `(S, r)` the exact order-`N` box of
   `Real.abs_log_sub_add_sum_range_le` at `x = 1 - v` (`|x| <= 1/3`), and `log 2 < 0.6931471808`
   (`Real.log_two_lt_d9`, `n > 0`) or `log 2 > 0.6931471803` (`Real.log_two_gt_d9`, `n < 0`). `H` is
   rounded UP to a multiple of `10^-15` (sound: only makes `H` bigger). The generator uses the LEAST
   order `N` whose `H` lets the cell pass. `u = 1` is `Real.log_one`.
3. **Mobius term.** `s/w` with `w = B + A x > 0`: `(s/w)'' = 2 s A^2 / w^3`.
   * `sigma >= 0`: convex; kept. Mode `convex`.
   * `sigma < 0`: concave; replaced by its tangent at `c = B + A t`:
     `s/w <= s/c - s (w - c)/c^2`, because the difference is `-s (w - c)^2 / (w c^2) >= 0`. Mode
     `tangent`.
   * `sigma = 0`: mode `none`.
4. **Majorant.** `Psi_t(x) = m + k x [+ sigma/(B + A x) in convex mode]`, with `m, k` exact rationals
   collecting `a, b`, the log tangents and (tangent mode) the Mobius tangent. `Psi_t` is convex (linear
   plus a convex term), so `Psi_t(p) <= 0` and `Psi_t(q) <= 0` imply `Psi_t <= 0` on `[p, q]`, hence
   `F <= 0` there.
5. **Tiling.** Cells `[p_0, q_0], [p_1, q_1], ...` with `p_0 = P`, `q_last = Q`, `q_j = p_(j+1)`.
   The union theorem is a `rcases le_or_gt x q_j` chain: the kernel itself checks there is no gap.

Layer 1 (`verify_certificate`) recomputes every cell from the problem: the tangent point lies in the
cell, each log bound equals its exact recomputation at its recorded order (orders `0..40`), `m`, `k`,
`Psi(p)`, `Psi(q)` equal the recomputation, both endpoint values are `<= 0`, and the tiling has no
gap or overlap. For a sides problem it re-checks `lhs - rhs == F` symbolically and that every sides
denominator is constant or affine with a fixed sign.

## Lean skeleton

Three generic lemmas, emitted once per family (prefixed `<first instance>_mtc_`), each proved from
Mathlib alone:

* `log_tangent (u y H) : 0 < u -> 0 < y -> log u <= H -> log y <= H + (y - u)/u`;
* `mobius_tangent (s w c d) : s <= 0 -> 0 < w -> 0 < c -> d = c^2 -> s/w <= s/c - s (w - c)/d`
  (`field_simp; ring` on the exact difference, then `div_nonneg`);
* `convex_endpoint (m k s A B p q x) : 0 <= s -> p <= x <= q -> 0 < B + A p -> 0 < B + A q ->
  Psi(p) <= 0 -> Psi(q) <= 0 -> m + k x + s/(B + A x) <= 0`, via the Cauchy-Schwarz form of the
  convexity of `1/w` along the chord: with `u = q - x`, `v = x - p`,
  `(u + v)^2 wp wq <= (u wq + v wp)(u wp + v wq)` (difference `u v (wp - wq)^2`), then the weighted
  sum `u Psi(p) + v Psi(q) <= 0`.

Per `log u <= H`: `Real.abs_log_sub_add_sum_range_le hx N`, the split proved BACKWARDS
(`rw [<- Real.log_pow, <- Real.log_mul ..]; norm_num`, so no literal of the goal is rewritten -- the
forward rewrite `2 = 2^1 * 1` also hit `Real.log 2` and failed), `generalize`,
`norm_num [Finset.sum_range_succ]`, `linarith`.

Per cell: `hy_i : 0 < alpha_i + beta_i x` by `linarith`; the log tangent instance;
`mul_le_mul_of_nonneg_left` by `kappa_i`; the Mobius lemma instance with all numeric side
conditions by `norm_num`; one closing `linarith`.

Per sides theorem: rewrite each sides log argument into the template's literal
`alpha + beta * x` (`congr 1; ring`, since `ring` treats `Real.log _` as an atom), then
`field_simp; ring` for `lhs - rhs = F`, then `linarith`.

## Refusals (the forge face)

`kappa < 0` (the log is then convex: e.g. `log(1 + x) >= 2x/(2 + x)` does NOT fit and is refused),
`kappa = 0`, no log term, floats, `p >= q`, a log argument or Mobius denominator not `> 0` at an
endpoint (sign change, or a pole in the interval), a non-affine log argument, a rational part that
is not `affine + one simple pole` (two poles, a double pole, a quadratic polynomial part), a
non-affine or sign-changing sides denominator, unknown spec keys, tangent point outside its cell,
log order outside `0..40`, any recorded datum not matching the recomputation, a positive majorant
endpoint value, a tiling with a gap or overlap, and -- at the bisection cap -- a claim that is false
(the message says so when a float evaluation is positive) or tight to order `>= 2`.

## Negative control (`negctrl_adapters/adapter_mobius_tangent_cell.py`)

TRUE twin: `log x <= 2 (x - 1)/(x + 1)` on `[1/4, 1/2]` in template form
(`-2 + 0 x + log(0 + 1 x) + 4/(1 + 1 x) <= 0`), one convex cell at `t = 7/16` (u < 2/3: the
`Real.log_two_gt_d9` path). Compiles, axioms `[propext, Classical.choice, Quot.sound]`.
FALSE twin: the constant moved to `-19/10`; `F(1/2) = 0.0735... > 0`, so the statement is false.
Layer 1 refuses it; the adapter keeps the honest cells by hand; the kernel rejects the cell's
closing `linarith` (checked by hand in the dogfood project; the harness run is lean-gated).

## Dogfood (`examples/mobius_tangent_cell/`)

`generate.py [--check]` writes `lean/MobiusTangentCell.lean` (48 theorems: 3 generic, 20 log
constants, 17 cells, 4 unions, 4 sides); `lean/AxiomGuardMobiusTangentCell.lean` pins the axiom list
of the union / sides theorems with `#guard_msgs`, so `lake build` fails on any drift (checked: a
wrong expected list makes the guard fail). Build: about 40 s on the loaded dev Mac, Mathlib cached.

| instance | claim | cells | Mobius mode |
|---|---|---|---|
| `pade_log1p` | `log(1 + x) <= x (6 + x)/(6 + 4x)` on `[1/4, 1]` (the [2/1] Pade bound) | 11 | convex (`sigma = 27`, `B + A x = 24 + 16x`) |
| `logmean_lower` | `log x <= 2 (x - 1)/(x + 1)` on `[1/10, 1/2]` | 2 | convex; tangent args < 2/3 (`n < 0` split) |
| `concave_mobius` | `log(1/4 + x) + (1/2) log(3 + x) <= x + 1/(2(1 + x)) - 8/25` on `[0, 2]` | 3 | tangent (`sigma = -1`), two log terms |
| `no_mobius` | `log(1 + x) <= (9/10) x + 1/10` on `[-1/2, 1/2]` | 1 | none (`sigma = 0`); tangent at u = 1 (`Real.log_one`) |

`concave_mobius` (true with margin about 0.012) and `no_mobius` are SYNTHETIC coverage instances,
included only so that every emitted proof path (two log terms, the concave negative-`sigma` branch,
the no-Mobius mode, the `u = 1` constant) is compiled in CI; they are not from the literature.

**What does not fit, stated plainly.** The Pade bound on the full `[0, 1]` is NOT certified: `F`
vanishes to order 4 at `x = 0`, while the tangent majorant exceeds `F` by a quadratic term in
`x - t`, so every cell containing 0 has a positive majorant endpoint value, and the generator
refuses at the bisection cap (a test pins this). The same holds for the log-mean bound at `x = 1`
(order 3). The companion lower bound `log(1 + x) >= 2x/(2 + x)` has a convex log term
(`kappa = -1`) and is refused.

## What it does NOT do

* Strict inequalities (only `<= 0` is stated).
* Neighbourhoods of points where `F` is tight to order `>= 2` (see above); cover those with another
  emitter (e.g. a Taylor/series argument) and join the pieces by hand.
* More than one Mobius term, higher-order poles, non-affine log arguments, convex (negative
  coefficient) logs.
* The tangent point search is a fixed candidate list (midpoint, quarter points, endpoints) plus
  bisection; there is no optimisation of `t`, so cell counts are not minimal.

## CI (to be wired centrally)

    cd telperion && python examples/mobius_tangent_cell/generate.py --check
    cd telperion/examples/mobius_tangent_cell/lean && lake exe cache get && lake build

(`lake build` builds both default targets, `MobiusTangentCell` and `AxiomGuardMobiusTangentCell`.)
