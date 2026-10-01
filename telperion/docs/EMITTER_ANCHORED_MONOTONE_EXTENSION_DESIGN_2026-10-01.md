# Emitter design: `anchored_monotone_extension` (2026-10-01)

`AnchoredMonotoneExtensionEmitter`, kind `anchored_monotone_extension`, module
`src/telperion/emit_anchored_monotone_extension.py`.

`conjecture1_proved = False`. This kind certifies, for one explicit recursion and one explicit
normalizer, an inequality that holds on every finite rooted tree. It says nothing about the
Brualdi-Goldwasser conjecture, RH, or any other open problem. The dogfood instances are classical
(the hard-core recursion) or synthetic (a matching-type sum recursion).

## The shape

The objects are finite rooted trees; a node has `k >= 0` children, and `k = 0` is a leaf. A
*parametric recursion* in a real parameter `λ` (written `lam` in specs and `x` in Lean) attaches
to every tree `b` a value `T_b(λ)` and a message `y_b(λ)`:

    A_b    = ∏_c y_c          (product mode)     or     A_b = Σ_c y_c     (sum mode)
    T_b(λ) = (∏_c T_c(λ)) · g(λ, A_b)
    y_b(λ) = h(λ, A_b)

Here `g` and `h` are rational functions of `(λ, A)` with rational coefficients. The *normalizer*
is `N(λ, n) = ψ(λ)^(ρ n)`, where `ψ` is a rational function of `λ` and `ρ > 0` is rational. It
determines the per-vertex budget `c(λ) = ρ λ ψ'(λ) / ψ(λ)`, so that `λ ∂_λ log N(λ, n) = n c(λ)`.

The kind certifies three things for every tree `b` with `n_b` vertices.

1. **The derivative prelude.** For `λ ≥ λ0`, `T_b` is positive and differentiable. Its
   log-derivative `D_b` satisfies an explicit recursion,

       D_b = Σ_c D_c + (g_λ + g_A A') / g,        E_b = (h_λ + h_A A') / h,
       A'  = A · Σ_c E_c   (product mode)    or    A' = Σ_c y_c E_c   (sum mode),

   where `E_b` is the log-derivative of the message. `D_b` and `E_b` are *defined* by this
   recursion and *proved* to be `d/dλ log T_b` and `d/dλ log y_b`.

2. **The monotonicity step.** On `[λ0, ∞)`, `λ D_b ≤ n_b c(λ)`. Consequently
   `log T_b − ρ n_b log ψ` and `T_b / N(λ, n_b)` are antitone on `[λ0, ∞)`.

3. **The anchor and the extension.** If `T_b(λa) ≤ N(λa, n_b)` for every tree at one point
   `λa ≥ λ0`, then `T_b(λ) ≤ N(λ, n_b)` for every tree and every `λ ≥ λa`. The anchor comes in
   one of two ways. It can be a *node check* at `λ0`: if `g(λ0, A)^q ≤ ψ(λ0)^p` on the aggregate
   range, where `ρ = p/q`, the anchor follows by induction. Or it can be a *hypothesis* passed
   through to the final theorem (`hanchor`), for an anchor certified by another emitter or by
   hand.

## Overlap check: why a new kind and not a face

We checked the kinds and faces that already exist.

* `monotone_tail`, `lattice_box` and `unimodal` all use an anchor-plus-monotone argument, but
  over the integers: a step `b(m+1) ≤ b(m)` and a base value. None has a real parameter, a
  derivative, or a family indexed by trees.
* `single_crossing_ladder` has generic `up_of_deriv` / `down_of_deriv` lemmas for one explicit
  log-sum on an interval. Its face is a crossing between two members of a family, not an
  anchored bound, and its functions are explicit closed forms, not tree recursions.
* `curvature_boundary` reduces to endpoints by curvature, not by the sign of a derivative plus an
  anchor.
* `concave_pooled_induction` and `affine_hull_dominance` are tree inductions, but for a fixed
  parameter. Neither differentiates in a parameter.

The extension step on its own would be thin: it is close to Mathlib's
`antitoneOn_of_hasDerivWithinAt_nonpos` plus an `exp`/`log` round trip. What makes the kind
worth having is its input, the derivative of a parametric tree recursion. That needs a generic
core of its own: a tree recursion, a chain rule through an aggregate of the children's messages,
and an inductive invariant whose per-node content is finite. No existing core can state this, so
it is a new kind.

## The certificate

**Input** (`anchored_monotone_extension_certificate`): `mode` (`"prod"` or `"sum"`), `g`, `h`,
`psi`, `rho`, `lam0`, the auxiliary row `mu`, `kappa` (rational in `λ`), and `anchor`
(`{"kind": "node"}` or `{"kind": "hypothesis", "at": λa}`).

**The two-row invariant.** The induction carries two inequalities at every tree:

    row 0 (target):     λ D_b                 ≤ n_b c(λ)
    row 1 (auxiliary):  λ D_b + μ(λ) · λ E_b  ≤ n_b c(λ) + κ(λ)

At a node, both rows become `Σ_c (λ D_c + m_c · λ E_c) + (node terms)`, where the child weight
`m_c` equals `K · A` (product mode) or `K · y_c` (sum mode), with `K = g_A/g + ι μ h_A/h` for row
`ι`. If `0 ≤ m_c ≤ μ`, the child term is the convex combination `(1 − m_c/μ)` of row 0 and
`(m_c/μ)` of row 1 at the child. It is then bounded by `n_c c + (m_c/μ) κ`. The sum of the
`m_c` is `K · W`, where `W = k·A` (product mode) or `W = A` (sum mode; `y_c ≤ A` because the
messages are positive). What remains is one inequality in the node variables `(λ, A, k)`.

**The obligations.** After clearing positive denominators, every per-node condition is a
polynomial inequality:

| name | statement | variables |
|---|---|---|
| `gN`, `gD`, `hN`, `hD` | the numerators and denominators of `g`, `h` are `> 0` | `λ ≥ λ0`, `A` in range |
| `hle` (product mode) | `hN ≤ hD`, so messages stay in `(0, 1]` and `A ∈ [0, 1]` | same |
| `pN`, `pD`, `mN`, `mD`, `kD` | `ψ`, `μ` and the denominator of `κ` are positive | `λ ≥ λ0` |
| `K0`, `K1` | `K ≥ 0` (cleared: `KN_ι = mD·Dh·Gq + ι·mN·Dg·Hq ≥ 0`) | `λ`, `A` |
| `K0le`, `K1le` | `A·K ≤ μ` (cleared: `A·KN_ι ≤ mN·Dg·Dh`) | `λ`, `A` |
| `res0`, `res1` | the cleared residual `Q_ι ≥ 0` | `λ`, `A`, `k` (product mode) |
| `anchor` (node mode) | `pN(λ0)^p · gD(λ0, A)^q − gN(λ0, A)^q · pD(λ0)^p ≥ 0` | `A` |

Here `Gx`, `Gq`, `Dg` (and `Hx`, `Hq`, `Dh` for `h`) are the cleared partials of `g`:
`λ g_λ/g = λ Gx/Dg` and `g_A/g = Gq/Dg`. The residual is

    Q_ι = ρ λ Px Dg Dh mD mN kD + ι kN Dg Dh mD mN pN pD − λ Gx Dh mD mN kD pN pD
          − ι mN² λ Hx Dg kD pN pD − kN mD KN_ι W pN pD,

with `Px = pN' pD − pN pD'`. That this cleared form is equivalent to the semantic residual is
proved once, generically, in Lean (`resid_of_Q`, one `field_simp; ring`). The Python side
computes exactly the polynomials the Lean definitions expand to.

**Positivity certificates.** Each obligation is certified on a box by an exact product-basis
expansion with nonnegative coefficients. A half-line `[s, ∞)` uses the Taylor basis `(v − s)^i`;
a bounded variable (`A ∈ [0, 1]`) uses the Bernstein basis `(v − s)^i (t − v)^(d − i)`. A strict
inequality also needs a positive coefficient on every index whose unbounded part is zero; those
terms sum to a positive constant on the box. If a cell fails, it is bisected (`λ` and `A`
alternately, a half-line `[s, ∞)` split at `2s + 1`) down to depth 8. `verify_certificate`
recomputes every obligation from the recursion data and re-expands every cell.

**Refusals.** The certificate is refused for: floats; symbols other than `lam` / `A`; a mode
other than `prod` / `sum`; `λ0 < 0`; `ρ ≤ 0`; an anchor point below `λ0`; any obligation with no
nonnegative certificate down to the subdivision limit; and degree or size caps. When an
obligation fails, a coarse exact grid search looks for a point where it is false and reports it
(`FALSE at (lam, A, k) = ...`). A too-small normalizer is refused at `res0` this way.
`check=False` builds the same algebra with every sign check skipped. It exists for hand-forged
negative controls only, so that the kernel is the arbiter.

## Lean

A generic section is emitted once per file (namespace `AnchoredMonotone`). Everything in it is
re-derived from Mathlib.

* `RTree` (a node with `Fin k → RTree` children) and `RTree.size`.
* `p2`, `p2dx`, `p2da`: a two-variable polynomial as a coefficient list `[(i, j, c), ...]` and
  its partial-derivative lists. `hasDerivAt_p2` is the chain rule along `t ↦ (t, U t)`, by list
  induction; `hasDerivAt_rq` is the quotient version (`HasDerivAt.fun_div`).
* `hasDerivAt_prod_log` (`HasDerivAt.fun_finsetProd`, `Finset.prod_erase_mul`) and
  `Rec.hasDerivAt_agg`: the derivative of the aggregate in both modes.
* `Rec.y`, `Rec.T`, `Rec.E`, `Rec.D`: the recursion and the log-derivative recursion, by
  structural recursion on the tree.
* **`Rec.hasDeriv_rec`** (the derivative prelude): under pointwise well-posedness `Rec.Good x`,
  every message is positive (and `≤ 1` in product mode), every `T_b` is positive, and
  `HasDerivAt (R.y b) (R.y b x * R.E b x) x` and `HasDerivAt (R.T b) (R.T b x * R.D b x) x`.
  `Rec.hasDerivAt_log_T` restates the second as `HasDerivAt (log ∘ T_b) (D_b x) x`.
* `Rec.Checks`: the obligations as a structure of polynomial hypotheses.
* **`Rec.invariant`**: from `Checks`, both rows on every tree for `x ≥ x0`. It uses
  `child_step` (the convex combination) and `resid_of_Q` (the cleared residual).
* **`Rec.logratio_antitone`** and **`Rec.ratio_antitone`**:
  `antitoneOn_of_hasDerivWithinAt_nonpos` on `Set.Ici x0` with `interior_Ici`, then
  `Real.rpow_def_of_pos` and `Real.exp_le_exp`.
* **`Rec.anchored_extension`** (anchor at `xa ≥ x0` ⇒ the bound on `[xa, ∞)`) and
  **`Rec.anchor_of_node`** (the node check ⇒ the anchor at `x0`, by induction on `log T_b`).

Per instance the emitter prints the data (`<nm>_R : Rec`, `<nm>_N : Norm`, `<nm>_I : Aux`),
evaluation lemmas for every coefficient list and its derivative lists (`simp only; push_cast;
ring`), and one lemma per obligation. Each obligation lemma is `simp only` with the evaluation
lemmas, then one `linarith` per cell over the product-basis facts (`mul_nonneg` / `pow_nonneg`
of `0 ≤ x − s`, `0 ≤ t − x`, ...); bisected covers become `rcases le_or_gt` splits. These are
assembled into `<nm>_checks`. The capstones follow:

* `<nm>_logderiv`: `HasDerivAt (fun t => log (T b t)) (D b x) x` for `x ≥ λ0`.
* `<nm>_deriv_bound`: `x * D b x ≤ b.size * C x`.
* `<nm>_antitone`: `AntitoneOn (fun t => T b t / ψ t ^ (ρ * b.size)) (Set.Ici λ0)`.
* `<nm>` (the extension, with `hanchor` in hypothesis mode).
* When `ρ = 1` and `ψ` is a polynomial: `<nm>_pow` and `<nm>_antitone_pow`, which state the same
  with a natural-number power, e.g. `T b x ≤ (1 + x) ^ b.size`.
* Optional `<nm>_sanity<i>` lemmas evaluate `T` on small trees. They pin down that the recursion
  is the intended function.

## Dogfood

`examples/anchored_monotone_extension/` (`generate.py --check`; a lake project on Mathlib v4.32.0,
same pins as the other examples). It has 136 theorems, all on `[propext, Classical.choice,
Quot.sound]`, with no `sorry`, `admit` or `native_decide`.

* **`hardcore`** (classical). The hard-core (independent-set) partition function on rooted trees.
  With `q_b = Z(b, root unoccupied)/Z(b)` and `P = ∏_c q_c`, we have `Z_b = (∏_c Z_c)(1 + λP)`
  and `q_b = 1/(1 + λP)` (product mode). The normalizer is `ψ = 1 + λ`, `ρ = 1`, with threshold
  `λ0 = 0`. The auxiliary row is `μ = 1`, `κ = −λ/(1 + λ)`: it is the root-deleted forest,
  `λ d/dλ log Z(b − root) ≤ (n_b − 1) c`. The residuals are
  `res0 = x(x + 1)(ax + 1)(akx − a + 1)` and `res1 = 0`. The anchor is the node check
  `g(0, A) = 1 ≤ ψ(0) = 1`. The capstones are
  `hardcore_pow : ∀ b x, 0 ≤ x → T b x ≤ (1 + x) ^ b.size` and
  `hardcore_antitone_pow`. The sanity lemmas give `T(leaf) = 1 + x` and `T(edge) = 1 + 2x`.
  The bound itself is elementary (each vertex contributes at most a factor `1 + λ`). The point of
  the instance is the route: the derivative recursion, the two-row invariant and the anchor.
* **`matching_sum`** (synthetic matching-type sum recursion). `R = Σ_c y_c`,
  `T_b = (∏_c T_c)(1 + λR)`, `y_b = 1/(1 + λR)`, with our own normalizer `(1 + λ)^n` on the
  threshold half-line `[1, ∞)`. The residual `res0 = x(x + 1)(ax + 1)(1 + a(x − 1))` is
  nonnegative for every aggregate exactly from `x = 1` on. The same certificate on `[0, ∞)` is
  refused, so the threshold is load-bearing. The node anchor at `λ = 1` would need
  `1 + A ≤ 2`, which fails because the sum aggregate is unbounded, so this instance passes the
  anchor through as a hypothesis:
  `matching_sum_pow (hanchor : ∀ b, T b 1 ≤ 2 ^ b.size) : ∀ b x, 1 ≤ x → T b x ≤ (1 + x) ^ b.size`.
  The sanity lemmas give `T(leaf) = 1` and `T(edge) = 1 + x`.
* **`hardcore_cube_root`**. The hard-core recursion again, with the normalizer written as
  `((1 + λ)^3)^(n/3)` (`ρ = 1/3`). It exercises the real-power path and the anchor node check
  with `p ≠ q` (`g(0, A)^3 ≤ ψ(0)`).

**Numerical verification first.** `tests/test_emit_anchored_monotone_extension.py` models the
recursion and the derivative recursion independently with mpmath, over all 85 rooted trees with
at most 7 vertices. It checks:

* the models count independent sets and matchings at `λ = 1` (brute force);
* `D_b` matches a finite difference of `log T_b`;
* both invariant rows hold on a grid of `λ ≥ λ0`;
* `T_b/(1 + λ)^n` is nonincreasing and `≤ 1`.

Before the emitter was built, a sympy brute force over all rooted trees with at most 9 vertices
found no violation of either claim, and confirmed that the too-small normalizer fails.

## Negative control

`negctrl_adapters/adapter_anchored_monotone_extension.py` runs the hard-core recursion against the
too-small normalizer `(1 + 3λ/4)^n`. This claim is genuinely false: a single vertex has
`Z = 1 + λ`. Layer 1 refuses it at `res0`, with the located violation `(λ, A, k) = (64, 1, 0)`.
At the leaf point the residual is `−x(3x + 4)(x + 1)/4 < 0`.

The forged certificate (`check=False`) keeps every other obligation honest. Only the `res0` cell
carries negative coefficients, and its `linarith` cannot close: the kernel reports exactly one
error, in `forged_res0`. The true twin `(1 + λ)^n` compiles clean
(`generic_negative_control`: `kernel_rejects = True`, `true_compiles = True`). A Lean-gated unit
test also compiles a bisected cover, since the dogfood itself needs no splits.

## Scope and limits

* The two-row invariant is a sufficient condition. A recursion whose derivative bound needs more
  than one auxiliary row, or weights that are not a convex combination of the two rows, is
  refused. It is not proved false.
* Product mode needs messages in `(0, 1]`, so that `A ∈ [0, 1]`. Sum mode lets `A` range over
  `[0, ∞)` and treats the child count as free. Both are relaxations, and both are sound.
* `μ`, `κ` and `ψ` depend on `λ` only. The node maps may be any rational functions whose
  numerators and denominators are certified positive on the domain.
* A hypothesis-mode anchor is exactly as strong as whatever discharges it. The emitted theorem
  states the hypothesis explicitly.
