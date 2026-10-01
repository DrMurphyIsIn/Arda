# Design: three small extensions to existing emitters (2026-10-01)

`conjecture1_proved = False`. Nothing here bears on the Brualdi-Goldwasser conjecture, on RH, or
on any other open problem. Every dogfood below is classical or synthetic.

This note covers a bundle of extensions to three EXISTING emitter kinds. No new kind is
registered. Each extension states a new face, or widens the class of certificates, of a kind that
already existed, and each is backward compatible. The original specs build the same
certificates, and the original examples regenerate to the same Lean apart from the input-hash
header line, because the hash folds in the emitter's source.

| extension | kind | new face | dogfood | negative control |
|---|---|---|---|---|
| minimum at a kink | `curvature_boundary` (mode `"kink"`) | `IsLeast (f '' Icc a b) (f κ)`, `v ≤ f x`, `0 ≤ f x` when `v ≥ 0`, and the same for a closed form with `\|affine\|` | `\|x - 1/3\| + x²` on `[0,1]` (min 1/9), cubic pieces on `[-1,2]`, `x²/2 + \|x\|x/2 + \|x\|/2` on `[-1,1]` | claimed minimum 1/9 + 1/1000 (registered adapter) |
| leaf-exempt children | `concave_pooled_induction` (`exempt_leaves=True`) | `ell + α·size ≤ U(msg)` on every NON-LEAF tree of child count `≤ M` | matching message, `Σ_u (1 - y_u) ≥ (27/100)\|T\| - 83/500`, which the single leaf violates | flat witness lowered by 1/1000, false at the root with two leaf children |
| log term in `g` | `concave_pooled_induction` | same face as before, with `g` containing `κ log(a0 + b1 R)` | `g = -1/(1+R) + (1/5) log(1 + R/2)`, α = 1/2, every tree | log enclosures forged to `H - 1/1000` |
| multivariate identity | `rational_identity` (dict spec with `domain`) | `∀ x y : ℚ, c_x < x → c_y < y → lhs = rhs` | partial fractions in one and two variables | partial fraction plus 1/1000 |
| identity modulo a minimal polynomial | `rational_identity` (dict spec with `modulus`) | `∀ t : ℝ, m(t) = 0 → lhs = rhs`, and its instance at the real root of a quadratic `m` | in ℚ(√5) = ℚ[t]/(t² - t - 1): `t² = t + 1`, `t^n = F_n t + F_(n-1)` (n = 3..8), `t^n + (1-t)^n = L_n` (n = 2..6), `(2t - 1)² = 5` | `t^5 = 5t + 4` (wrong; the remainder is -1) |

Log bounds on `[0, ∞)` for `transcendental_enclosure` are NOT part of this bundle. They are left
to the `factored_endpoint_enclosure` branch, which may extend that emitter.

---

## 1. `curvature_boundary`: minimum at a kink

**Face.** A function `f` is given on `[a, b]` by a polynomial `L` up to a rational kink
`a < κ < b` and by a polynomial `R` after it, with `L(κ) = R(κ)`. If `L' ≤ 0` on `[a, κ]` and
`R' ≥ 0` on `[κ, b]`, then

```
IsLeast (f '' Set.Icc a b) (f κ),     ∀ x ∈ Icc a b, f κ ≤ f x,     f κ = v,
```

and `∀ x ∈ Icc a b, 0 ≤ f x` when `v ≥ 0`. If a closed form `f_expr` is given, for example
`|x - 1/3| + x²`, it is proved equal to the piecewise `f` on `[a, b]` (`<name>_expr_eq`), and the
minimum and `IsLeast` statements are restated for it.

**Certificate.** Each derivative sign is a one-variable polynomial sign check. `-L' ≥ 0` on
`[a, κ]` and `R' ≥ 0` on `[κ, b]` are certified by nonnegative Bernstein coefficients. This is
the `PolyCert` machinery of `concave_pooled_induction`, bisected up to depth 8. Continuity at
the kink and any claimed value are checked exactly. Each `Abs` argument must be affine and must
keep one sign on each side of the kink. On each side it is replaced by `±arg`, and the result
must equal that side's piece exactly.

**Lean.** The pieces are `Polynomial ℝ` values, `Σ C c_i * X ^ i`. The derivative is computed
by `simp only [derivative_add, derivative_C_mul_X_pow, eval_*]` followed by `norm_num`. Each
sign lemma is closed by `linarith` over the Bernstein product facts. Monotonicity on each side
comes from Mathlib's `antitoneOn_of_deriv_nonpos` / `monotoneOn_of_deriv_nonneg`, with
`Polynomial.deriv`, `.continuous` and `.differentiable`. It is transported to
`f := if x ≤ κ then L.eval x else R.eval x` by `AntitoneOn.congr` / `MonotoneOn.congr`, using
continuity at `κ`. The generic lemma `kink_min_of_anti_mono` is emitted once per file, and only
when a kink instance is present. Files with only endpoint instances are unchanged.

**Refusals.** `κ` not strictly inside `(a, b)`; a float; pieces that are not polynomials in `x`;
`L(κ) ≠ R(κ)`; a derivative sign that fails, reported with an exact point when one is found; a
cover that does not close by depth 8; a claimed value other than `f(κ)`; a closed form that
disagrees with the pieces, has a non-affine `Abs` argument, or has an `Abs` that changes sign
on one side.

**Not covered.** More than one kink. A strictly convex function whose one-sided derivatives at
the kink are only enclosed: here the pieces are polynomials and the signs are exact.

## 2. `concave_pooled_induction`: leaf-exempt children and a log term in `g`

### 2a. Leaf-exempt children (`exempt_leaves=True`)

**Face.** For every NON-LEAF finite rooted tree `b` with child count `≤ M`:

```
lo ≤ msg b ≤ hi  ∧  ell b + α·size b ≤ U (msg b).
```

The leaf itself is not claimed: `y_leaf` need not lie in `I` and the base `l_leaf + α ≤ U(y_leaf)`
is not required.

**Generic Lean core** (`exempt_induction_core`, emitted once per file when used). A node with
`m + 1` children is split by `Finset.filter` into the set `S` of non-leaf children, of size `p`,
and its complement of `k` leaves. Every child sum splits as
`Σ_i f(cs i) = Σ_{i ∈ S} f(cs i) + k · f(leaf)`. Jensen runs only over `S`, through
`minPieces_jensen_on`, Jensen on a nonempty sub-family. The pooled mean is
`yb = (Σ_S msg)/p`, or `lo` when `p = 0`. The step hypothesis is quantified over `(p, k)`:

```
∀ p k, 1 ≤ p + k → ok (p + k) → ∀ yb ∈ [lo, hi],
  p·V(yb) + k·(l0 + α) + g (p+k) (p·yb + k·y0) + α ≤ U (h (p+k) (p·yb + k·y0)),
```

and the closure hypothesis has the same form.

**Certificate.** For each child mix `1 ≤ p`, `p + k ≤ M`, the cells cover `R' = p·yb ∈ [p·lo, p·hi]`.
The existing `_build_cell` gains a shift: `h`, `g` are evaluated at `R' + k·y0`, and the constant
`k(l0 + α)` is added on the left. The all-leaves mixes `(0, k)` are pure numbers, checked
exactly (`AtomCase`) and closed in Lean by `norm_num` plus `le_minPieces`. `tail` must be
`False`, so the claim is for bounded child count only.

**Why it matters (the dogfood).** The dogfood uses the matching message `y = 1/(1+R)`,
`y_leaf = 1`, with profit `-Σ_u (1 - y_u)` (`g = -R/(1+R)`, `l_leaf = 0`), child count `≤ 2`, and
α = 27/100. The certificate proves `Σ_u (1 - y_u) ≥ (27/100)|T| - 83/500` for every non-leaf
tree. The witness is concave on the non-leaf message range `[1/3, 3/4]`, with three nodes. The
one-vertex tree has `ell + α = 27/100 > 83/500`, so it violates the bound. A certificate that
pools the leaves covers that tree and therefore needs `max U ≥ U(1) ≥ 27/100`, so it can never
give this uniform bound. The emitted `*_leaf_breaks` lemma records this. Without exemption the
same spec is refused ("y_leaf outside I", and with `I` widened, "base fails"). The claim was
checked numerically first, on 3000 random trees and by exhaustive enumeration up to 13 vertices
(maximum of `ell + αn` over non-leaf trees 0.1633 ≤ 83/500).

**Not covered.** Exempt atoms other than leaves. The generic core is written for the leaf, and
general listed finite subtrees would need a decidable classifier on `PTree` plus exact
`(y, l, size)` lemmas per atom. That is a straightforward generalization, but it is not done
here. Also not covered: a tail (`m ≥ M + 1`) in exempt mode.

### 2b. A log term in `g`

**Face.** Unchanged. `g(m, R)` may now contain terms `κ log(a0 + b1 R)`, with κ, a0, b1 rational,
`κ > 0`, `a0 > 0`, `b1 ≥ 0`, and the log argument independent of `m`. Both modes accept them, as
does the tail.

**Certificate.** On every cell each log is replaced by its tangent majorant at the cell's tangent
point. That point is the midpoint `R0`, or `s + 1` on the unbounded tail cell:
`κ log y ≤ κ(H + (y - u)/u)`, with `u = a0 + b1(R0 + shift)`. The rational `H ≥ log u` comes from
the `mobius_tangent_cell` machinery (`log_upper`: `u = 2^n v`, the order-12 Taylor box, Mathlib's
`log 2` bounds). The majorant is affine in `R`, so the cell obligation stays one polynomial
inequality. In Lean, `log_tangent_le` (the mobius lemma, emitted once per file when needed) gives
`hk : κ log y ≤ κ(H + (y-u)/u)`. Each `Real.log u ≤ H` is its own lemma (`<name>_logH<i>`, proved
by the mobius Taylor-box proof). The cell's `linarith` combines `hk` with the Bernstein identity.

**Refusals.** `κ ≤ 0`, since a convex log has no tangent upper bound; this is also outside the
mobius template. Also refused: a non-affine or `m`-dependent log argument, `a0 ≤ 0` or `b1 < 0`,
a non-constant coefficient, `lo < 0` or `y_leaf < 0` (the log argument must stay positive), and a
nested or multiplied log.

**Dogfood.** The matching-density recursion with the synthetic profit
`g = -1/(1+R) + (1/5) log(1 + R/2)` and α = 1/2, with the original witness, for every finite
rooted tree with tail. A fourth instance combines both extensions: leaf-exempt, `g` with a log,
α = 1/5, and a flat witness 1/10.

## 3. `rational_identity`: multivariate identities and identities modulo a minimal polynomial

The univariate ray form `(lhs, rhs, c0)` is unchanged. A spec that returns a `dict` selects an
extension mode, and `"symbols"` may override the family symbols for that instance.

**Multivariate** (`{"lhs", "rhs", "domain": {sym: c}}`). The face is
`∀ x y : ℚ, c_x < x → c_y < y → lhs = rhs`. The certificate is exact cancellation, plus a
positivity audit of every denominator atom on the open box. The atoms are the renderer's own
subterms, so `field_simp` matches its `≠ 0` hypotheses syntactically. Two routes are accepted.
An AFFINE atom must have all coefficients of `D(c + t)` nonnegative and not all zero; `linarith`
then proves `0 < D` from the rays. A POSITIVITY-EVIDENT atom is a positive constant plus
positive multiples of even-power monomials; `positivity` proves it. The Lean proof is the `≠ 0`
haves, then `field_simp`, then `ring`.

**Modulo a minimal polynomial** (`{"lhs", "rhs", "modulus": m}`). `m` is monic in the first
symbol and irreducible over ℚ, which is checked. `lhs` and `rhs` are polynomials. The
certificate is the exact division `lhs - rhs = q·m` with zero remainder. The face is
`∀ t : ℝ, m(t) = 0 → lhs = rhs`, so the identity holds at every root, closed by
`linear_combination q * h`. For a quadratic `m` with discriminant `d`, the root lemma
`m((-b + √d)/2) = 0` (by `Real.sq_sqrt` and `linear_combination (1/4) * hs`) is emitted once per
modulus, and each identity is instantiated there (`<name>_at_root`). For example,
`((1 + √5)/2)^5 = 5·(1 + √5)/2 + 3`.

**Refusals.** A non-identity; a box on which a denominator cannot be certified positive; a
reducible or non-monic modulus; a nonzero remainder; a variable denominator in the modular mode
(state `1/t = t - 1` as `t(t - 1) = 1`); undeclared symbols; floats; both or neither of
`domain` and `modulus`.

## 4. Negative controls

Each extension has a forged-false twin that the Layer-1 self-check refuses. The adapter mints
it with the checks skipped, so only the load-bearing value is wrong, and the kernel rejects it
while the true twin compiles:

- kink: the claimed minimum is 1/9 + 1/1000. It is false, since `f(1/3) = 1/9`. The registered
  adapter `adapter_curvature_boundary` fails at the kink-value `norm_num`.
- leaf-exempt: the flat witness is lowered from 1/12 to 1/12 - 1/1000. This is false by exactly
  1/1000 at the root with two leaf children. The all-leaves step's `norm_num` fails.
- log term: every `log u ≤ H` is forged to `H - 1/1000`, which is false. The cells are rebuilt on
  the true twin's layout, so only the log facts are wrong, and the Taylor-box `linarith` fails.
- multivariate: the two-variable partial fraction plus 1/1000. `ring` fails after `field_simp`.
- modular: `t^5 = 5t + 4` modulo `t² - t - 1`, with remainder -1. `linear_combination` fails.

`CurvatureBoundaryEmitter` had no adapter, and its kink control is now registered. The stance
gains `neg_control=ADAPTER`. The four other controls are module-level `NegativeControlAdapter`
objects that are not registered, because the registry holds one adapter per emitter.
`EXEMPT_ADAPTER` and `LOG_ADAPTER` live in `adapter_concave_pooled_induction.py`;
`MULTIVARIATE_ADAPTER` and `MODULAR_ADAPTER` live in `adapter_rational_identity.py`. Their kernel
runs are lean-gated tests: `tests/test_negctrl_concave_pooled_ext.py` and
`tests/test_negctrl_rational_identity_ext.py`.

## 5. Files

- `src/telperion/emit_curvature_boundary.py`: `kink_minimum_certificate`, `_emit_kink`, and
  `_KINK_ABSTRACT`.
- `src/telperion/emit_concave_pooled_induction.py`: `LogPart`, `AtomCase`, `_split_logs`,
  `_exempt_cells`, `_GENERIC_LOG`, `_GENERIC_EXEMPT`, `_emit_instance_exempt`, and the specs
  `LEAF_EXEMPT_SPEC`, `LEAF_EXEMPT_FLAT_SPEC`, `LOG_PROFIT_SPEC`, `LEAF_EXEMPT_LOG_SPEC`.
- `src/telperion/emit_rational_identity.py`: `ExtendedIdentityCert`,
  `extended_identity_certificate`, `_emit_extended`.
- Examples:
  - `examples/curvature_boundary/generate.py`: three kink instances added.
  - `examples/concave_pooled_induction/generate_ext.py`: writes
    `lean/ConcavePooledInductionExt.lean`, a second `lean_lib`.
  - `examples/rational_identity/generate_ext.py`: writes `lean/RationalIdentityExt.lean`, a new
    lake project and a new CI job.
- Tests:
  - `tests/test_curvature_boundary_kink.py`
  - `tests/test_concave_pooled_ext.py`
  - `tests/test_rational_identity_ext.py`
  - `tests/test_negctrl_curvature_boundary.py`
  - `tests/test_negctrl_concave_pooled_ext.py`
  - `tests/test_negctrl_rational_identity_ext.py`
