# Emitter design: `single_crossing_ladder` (2026-09-30)

`SingleCrossingLadderEmitter`, kind `single_crossing_ladder`, module
`src/telperion/emit_single_crossing_ladder.py`.

`conjecture1_proved = False`. This kind certifies elementary one-variable facts about an explicit
family of log-sums. It says nothing about the Brualdi-Goldwasser conjecture, RH, or any other open
problem.

## The shape

A parametric family of functions of a real parameter `x`, members `j = a, a+1, ..., J+1`:

    F_j(x) = sum_i kappa_i(j) * log(1 + beta_i(j) * x),      x in S = [0, X] or [0, oo),

with `kappa_i`, `beta_i` rational functions of `j`. Every log vanishes at `x = 0`, so all members
tie at the anchor. The kind certifies three things.

(a) **Single crossing.** For each consecutive pair, `D_j = F_j - F_{j+1}` has exactly one zero
`lambda_j` on `S ∩ (0, oo)`. It lies in a rational bracket `(lo_j, hi_j)`; `F_j` is ahead before it
and `F_{j+1}` after it. A pair may instead be *dominated*: `F_{j+1} > F_j` on all of `S ∩ (0, oo)`,
with breakpoint `0`.

(b) **Increasing breakpoints.** Dominated pairs come first, and the brackets increase,
`hi_j < lo_{j+1}`.

(c) **The ladder.** On `(lambda_{j-1}, lambda_j)`, open at the ends of the window, `F_j` is the
unique maximum of `F_a, ..., F_{J+1}`. The kind also states, for each winning member, the rational
corollary on `[hi_{j-1}, lo_j]`.

## Overlap check: why a new kind and not a face

We checked the kinds and faces that already exist, including those added on 2026-09-29.

* `unimodal` proves an integer-sequence peak `f(n) <= f(s*)` from a Polya-certified successor
  ratio. The ladder is about a *real parameter* and which member of the family wins at each value.
  The two are related (unimodality in `j` is what extends a ladder past a finite window), but
  nothing in the ratio machinery certifies a crossing in `x`.
* `monotone_tail` (both the ratio face and the piecewise-linear node face) and `eventual_threshold`
  (including the quadratic sign-race face) are about integer tails and integer thresholds. The
  sign race certifies the sign pattern of an integer quadratic. Here the sign change is of a
  polynomial in a *real* variable, and it feeds a derivative argument for a transcendental
  function.
* `finite_argmax` compares constant rationals, and `domination_ratio` checks a multi-affine
  box inequality. Neither has a parameter-dependent winner or a crossing.
* `log_combination` encloses one constant log combination. We reuse `enclosure_tree` (its sibling)
  for the bracket values, not as the shape.

The certificate needs its own generic Lean core: a mean-value / intermediate-value single-crossing
theorem for a function whose derivative has a single sign change, and an order-theoretic ladder
lemma. No existing kind's core could be extended to state these, so this is a new kind rather
than a face. It reuses what it can: the Bernstein/Taylor `PolyCert` machinery of
`concave_pooled_induction` for the sign cells, and `enclosure_tree` log atoms for the bracket
values.

## The certificate

For each pair `j`:

* **Factorisation.** Merge the `(kappa, beta)` of `F_j - F_{j+1}` by `beta`, then set
  `P = prod (1 + beta x)` over the surviving `beta` and `N = D' * P`, a polynomial with exact
  rational coefficients. `P > 0` on `S`, because every log argument is positive there. That is
  checked for every member: `beta >= 0` on an unbounded domain, `1 + beta X > 0` on `[0, X]`.
* **One sign change of `N`** (`+ -> -`). A cover of `[0, a_c]` by cells on which `N > 0`
  (strictly positive Bernstein coefficients), a *crossing cell* `[a_c, b_c]` on which `N' < 0`
  (so `N` falls through zero exactly once), and a cover of `[b_c, X]`, or of `[b_c, oo)` ending in
  a Taylor cell, on which `N < 0`. The crossing cell is a dyadic interval around the numerically
  located root of `N`, shrunk until the certificates pass. A second positive root of `N` in `S`,
  which means a possible double crossing, is refused. So is `N(0) = 0`.
* **Bracket values.** `D(lo) > 0` and `D(hi) < 0` come from `enclosure_tree` log atoms. Each
  `log q` is taken directly by the Taylor estimate when `|1 - q| <= 1/3`, or by the fold
  `q = (3/2)^e r` with Taylor atoms only. The Mathlib `log 2` bracket (width `1e-9`) is avoided on
  purpose: the arm ladder's `D(lo_6)` is about `7e-12`. The enclosure certificate is asked for the
  sign itself (`lo = 0` or `hi = 0`), so a wrong bracket is refused at certify time.
* **Dominated pairs.** One cover of all of `S` with `N < 0`, and `N(0) < 0`.

## Lean

The generic section is emitted once per file, and every theorem in it is proved without `sorry`:

| theorem | content |
|---|---|
| `logSum_zero`, `hasDerivAt_logSum` | the member and its derivative, by list induction |
| `hasDerivAt_polyEval` | Horner form, derivative `polyDeriv` |
| `up_of_deriv`, `down_of_deriv` | strict monotonicity from the derivative sign (`exists_hasDerivAt_eq_slope`) |
| `sign_change_of_cell` | the cell data gives `∃ s > 0`, `N > 0` on `(0, s)`, `N < 0` on `(s, ...)` (`intermediate_value_Ioo'`) |
| `single_crossing_core` | `D 0 = 0`, `D' P = N`, `P > 0`, one sign change of `N`, `D lo > 0 > D hi` give `∃! c ∈ (lo, hi)` in the strong form: `D > 0` before `c`, `D < 0` after it |
| `dominated_core` | `N < 0` gives `D < 0` on `S ∩ (0, oo)` |
| `ladder_core` | crossings plus nondecreasing breakpoints give the unique maximum on each interval (`Nat.le_induction` up and down the window) |

The domain `S` is any `Set.OrdConnected` set containing `0`: `Set.Ici 0` or `Set.Icc 0 X`.

Each instance adds the following:

* `<nm>_terms`, `<nm>_F`, `<nm>_S`, and `<nm>_argpos` (every log argument is positive on `S`,
  checked member by member with `interval_cases`);
* per pair: `_P_pos`; `_fac` (`D' * P = N` by `field_simp; ring`); one lemma per sign cell (`simp
  only [polyEval]; linarith [product facts]`); `_C` for the crossing cell; `_sign`; the log atoms,
  `_vlo` and `_vhi` (`norm_num` + `linarith` over the atoms); and `_cross` or `_dom`;
* `<nm>_brackets_increasing` (`norm_num`);
* the capstone `<nm>`. It asserts that there exists `Λ : ℕ → ℝ` with `Λ j = 0` for dominated
  pairs, `lo_j < Λ j < hi_j` and `F j (Λ j) = F (j+1) (Λ j)` for crossing pairs, `Λ`
  nondecreasing, and the ladder. `Λ` is built from the crossing points by nested `if`s;
* `<nm>_best_j`: for each winning member, the rational-interval corollary.

## Dogfood

`examples/single_crossing_ladder/`, with a lake project on Mathlib v4.32.0 and a `generate.py
--check` drift gate. It has 133 theorems, all `[propext, Classical.choice, Quot.sound]`.

* **The arm ladder.** An arm with `j` cherries (`2j+1` vertices) has matching-sum weight
  `c^j (1 + lambda j/((j+1)(2+lambda)))`, where `c = 1 + lambda/2`. Its per-vertex log-weight is

      F_j(lambda) = [j log((2+lambda)/2) + log((j+1 + lambda j/(2+lambda))/(j+1))]/(2j+1)
                  = ((j-1)/(2j+1)) log(1 + lambda/2) + (1/(2j+1)) log(1 + (2j+1)/(2j+2) lambda).

  Members `j = 1..7` on `[0, oo)`. Pairs 1 and 2 are dominated, so arms 1 and 2 are never best.
  Pairs 3..6 cross at `lambda_3..lambda_6`, with 1e-5 brackets `(0.43050, 0.43051)`,
  `(0.87247, 0.87248)`, `(1.19239, 1.19240)` and `(1.43559, 1.43560)`. Each `N_j` is a quadratic
  with a positive constant term and a negative leading coefficient, and each needs one cell per
  side. The breakpoints
  keep increasing, towards `1 + sqrt 5`, where the arms give way to the cherry rate
  `(1/2) log(1 + lambda/2)`. That limit is outside the finite window certified here.
* **A synthetic bounded instance** (no combinatorial meaning), `F_0 = 0` and
  `F_1 = log(1+x) - (3/2) log(1+x/10) - (1/2) log(1+2x)`, on `S = [0, 2]`. The difference crosses
  once there, near `0.9713`, and again near `4.3153`, so on `[0, oo)` the claim is false and is
  refused.

## Negative controls

* **Wrong breakpoint bracket** (the registered adapter, `adapter_single_crossing_ladder`). The
  A_3/A_4 bracket is shifted to `(0.43052, 0.43053)`, which misses `lambda_3 = 0.4305018...`, so
  `D(lo) > 0` is false. Layer 1 refuses it. The forged certificate (`check=False`: honest cells,
  honest claim-free log atoms, wrong bracket) fails in `_p3_vlo` with "linarith failed". The true
  twin compiles.
* **Double crossing** (`DOUBLE_DIP_ADAPTER`, run in `tests/test_negctrl_single_crossing_ladder.py`).
  The synthetic family on `[0, oo)` is claimed single. Layer 1 refuses it because `N` has two
  sign changes. The forged tail cell `N < 0` on `[3/8, oo)` fails its `linarith`. The true twin on
  `[0, 2]` compiles.

## Scope and limits

* The ladder is certified over the *finite* window of members. The claim that no member beyond
  the window ever wins needs a separate argument (for the arms, unimodality of `j -> F_j`). This
  kind does not certify it.
* Breakpoints are pinned only to their rational brackets.
* Members must be log-sums of affine arguments normalised to `1` at the anchor `x = 0`. For
  another anchor, shift the variable. The pattern of `N` must be `+ -> -` (a crossing) or `-`
  throughout (dominated), with `N(0) != 0`.
* Log arguments at the bracket ends must exceed `1/2` (the fold range), polynomial degrees are
  at most 10, and a window has at most 24 pairs.
