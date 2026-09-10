<!-- Concrete build scope for the first post-Brick-0 increment of the Jensen-Polya campaign
(JENSEN_CAMPAIGN_2026-09-10.md). Brick 0 (the d=2 seed) is DONE on main. This scopes Brick 1
(d=3 rungs) + Brick 3 (the gamma(m>=5) enclosure backend). conjecture1_proved = False; this build
does NOT approach RH — it adds finite rungs + a reusable real-rootedness certificate shape. -->

# Jensen campaign — Brick 1 + Brick 3 concrete build scope (2026-09-10)

Prereq: **Brick 0 is already on `origin/main`** (`telperion/examples/jensen_hyperbolicity/`, landed
`dddcf22e`, CI-wired `jensen-hyperbolicity-compiles`, axiom-clean, no `sorry`). This doc scopes the
first genuinely new increment. Ceiling unchanged: the uniform-in-`d` threshold `N(d)` **is** RH and
is out of scope; these bricks are finite-rung + refutation tooling. `conjecture1_proved = False`.

## Current backend reach (what bounds "new rungs")

`J^{d,n}(x) = Σ_{k=0}^d C(d,k)·α(n+k)·xᵏ`, where `α(m)` = coeff of `t^{2m}` in `Ξ(t)=ξ(½+it)`.
The rigorous `acb_series` path (`rh_jensen/coefficients.py::_xi_series_coeffs`) yields **`α(0..4)`**
(series index `2m ≤ 9`); `enclose_coeff_box(n,d)` **raises `NotImplementedError`** the moment any
required `α(k)` has `2k>9` (i.e. `k≥5`). Consequence for the two near-term bricks:

| target | needs `α(...)` | reachable **now**? |
|---|---|---|
| `J^{2,n}`, n=0,1,2 | α(0..4) | ✅ (this is the shipped seed) |
| **`J^{3,0}`** | α(0..3) | ✅ **yes — new rung, no Brick 3** |
| **`J^{3,1}`** | α(1..4) | ✅ **yes — new rung, no Brick 3** |
| `J^{2,n≥3}`, `J^{3,n≥2}`, any `J^{4..8,·}` | α(≥5) | ❌ needs **Brick 3** |

So **Brick 1 produces new certified rungs immediately** (`J^{3,0}`, `J^{3,1}`) against the existing
backend; Brick 3 then unlocks everything beyond. They are independent and can be built in parallel.

---

## Brick 1 — the `d=3` (cubic) rungs

### Recommended route: sign-alternation certificate (NOT the discriminant bridge)

The campaign spec proposes a `hyperbolic_deg3_of_discrim_nonneg` bridge (`Δ ≥ 0 ⟹ roots.card = 3`).
That is real, Mathlib-absent work (status doc item (b): no discriminant→real-roots classification
over ℝ for `d≥3`) and it is **not** `nlinarith`-shaped — the box→`Δ≥0` step is, but the classification
theorem is not. A cleaner, Mathlib-gap-free, and **degree-generic** certificate is available:

> **Real-rootedness by sign alternation.** If `p : ℝ[X]` has `natDegree = d` and there exist
> `x₀ < x₁ < … < x_d` (rationals) with `p(xᵢ)` strictly alternating in sign, then by IVT `p` has a
> root in each open interval `(xᵢ, xᵢ₊₁)` — `d` roots in disjoint intervals, hence **distinct** —
> so `d ≤ p.roots.card`. With `p.roots.card ≤ p.natDegree = d` (`Polynomial.card_roots_le_degree`),
> `p.roots.card = d`. **Hyperbolic.**

This needs only IVT (`intermediate_value_Icc`) + `card_roots_le_natDegree` + a small
"`k` disjoint sign-change intervals ⟹ `k` distinct roots" lemma. **No discriminant, no
transcendental root arithmetic, no Mathlib gap.** The certificate *data* is `d+1` rational sample
points with a certified sign pattern — each sign check is a rational polynomial evaluation closed by
`norm_num`/`nlinarith`. It **generalizes to every `d`** for the generic (distinct-root) case, so it
also seeds Brick 2's generic instances (the Hermite–Bézoutian PSD engine remains needed for the
tie/repeated-root and non-generic completeness — sign alternation certifies *distinct* real roots
only, and requires strict separation).

Ship the general lemma once: `real_rooted_of_sign_alternation (p) (xs) (halt) : p.roots.card = p.natDegree`.
The `d=2` seed's explicit-factorization bridge stays as-is (it also covers the repeated-root `Δ=0`
tie); `d=3` onward uses sign alternation.

### Files / work
- **Lean** `examples/jensen_hyperbolicity/lean/JensenBridge.lean` (or a new `SignAlternation.lean`):
  add `real_rooted_of_sign_alternation`; `#print axioms` clean `[propext, Classical.choice, Quot.sound]`.
- **Emitter** `src/telperion/emit_jensen_polynomial_hyperbolicity.py` + `rh_jensen/jensen.py`:
  extend `render_box` to `d=3` — build `J^{3,n}` from the four `α`-boxes, choose the `d+1` rational
  sample points, emit the certified sign pattern + the `real_rooted_of_sign_alternation` invocation,
  and keep the existing **refusal gate** (emit nothing unless the sign alternation is witnessed — the
  honest negative control, mirroring the `Δ-margin ≤ 0` refusal).
- **Generate** `examples/jensen_hyperbolicity/generate.py`: `--grid` adds `d=3, n=0,1`.
- **Guard/CI**: `AxiomGuardJensenHyperbolicity` line for each new theorem; the existing
  `jensen-hyperbolicity-compiles` job already builds the example (no new job).
- **Tests** `tests/rh_jensen/`: `J^{3,0}`/`J^{3,1}` emit + AXLE statement-match + a **forge test**
  (perturb one sample sign → certificate must be refused / kernel-rejected).

### Acceptance
Kernel-clean `jensen_box_hyperbolic_deg3_0`, `_1` (`roots.card = 3`), axioms `= {propext, choice,
Quot.sound}`, AXLE example compiles, forge test refused, `generate.py --grid --check` green.

---

## Brick 3 — the `α(m ≥ 5)` rigorous enclosure backend (blocker (a))

### The gap
`enclose_coeff_box` raises for `2k>9` because `acb_series` returns only 10 ζ terms. A naive finite
Vandermonde solve is **unsound**: it drops the tail `α(m+3)+…` (≈1e-28 at the used points), which
dwarfs the acb ball radius (≈1e-169), so reporting only the ball radius understates uncertainty.

### Design: solve-center + Cauchy-tail radius (NOT a symmetric Cauchy box)
A bare Cauchy bound `|α(k)| ≤ M(R)/R^{2k}` gives a wide interval centered at 0 — too crude to keep
the hyperbolicity margin positive. Instead:
1. **Center** from the finite extraction (subtract the rigorous `α(0..4)` series part, then
   evaluate/solve for the target `α(m)` center).
2. **Radius** = acb input-propagation radius **+** a rigorous Cauchy bound on the *dropped* tail,
   `Σ_{k>m} M(R)/R^{2k} = M(R)·R^{-2(m+1)}/(1−R^{-2})` for `R>1`, added explicitly to the ball so the
   returned `[lo,hi]` **provably contains** `α(m)` including the tail.

The one genuinely new sub-piece: a **rigorous max-modulus** `M(R) ≥ max_{|t|=R} |Ξ(t)|`, computed by
Arb ball arithmetic on the circle `|t|=R` (subdivide the circle into arcs, cover each arc by a ball,
`acb`-evaluate `Ξ` on each covering ball, take the sup of the outward radii). This reuses the Li
ladder's Arb enclosure backend (`examples/li_positivity/generate.py`) and `_xi_series_coeffs`.

### Files / work
- **`rh_jensen/coefficients.py`**: add `enclose_xi_coeff_cauchy(m, R, prec_bits)` (center+tail as
  above) and a `max_modulus_xi(R, prec_bits)` helper; route `enclose_coeff_box` to it when `2k>9`
  (remove the `NotImplementedError` for the now-covered range; keep it as the honest fallback if `R`
  is mis-chosen so the tail bound doesn't converge).
- **Tests** `tests/rh_jensen/test_coefficients.py`: **cross-check** — for `α(0..4)` both the
  `acb_series` path and the new Cauchy path must produce intervals whose intersection is non-empty
  and both contain the series value (nonvacuity + soundness); assert the Cauchy interval for a target
  `α(5)` is tight enough that `render_box`'s `J^{2,3}` sign/discriminant margin is `> 0`.

### Acceptance
`enclose_coeff_box(3,2)` (needs α(5)) returns a sound, tight box; `J^{2,3}` and `J^{3,2}` emit and
kernel-verify; the cross-check test proves the new path agrees with the series path on the overlap.

---

## Sequencing

1. **Brick 1 first** — self-contained, ships `J^{3,0}`/`J^{3,1}` against today's backend, and lands
   the reusable `real_rooted_of_sign_alternation` lemma that Brick 2 also consumes.
2. **Brick 3 in parallel** — unlocks `α(m≥5)`, immediately widening both `d=2` and `d=3` grids
   (`J^{2,n≥3}`, `J^{3,n≥2}`).
3. **Brick 2 after** (separate hard session) — the Hermite–Bézoutian PSD engine for `d=4..8`
   completeness (ties / non-generic), the campaign's genuinely research-grade brick.
4. **Brick 4** — register the `jensen_hyperbolic` kind + `jensen_nonhyperbolic_refutes_rh` refutation
   atom through `certify.py` + `emitter_sensitivity.py` + negctrl adapter.

## Honesty

Every rung is a finite `(d,n)` instance. Sign-alternation and Hermite-PSD certify *specific*
polynomials real-rooted; the doubly-uniform "all `n`, all `d`" object is RH and is never touched.
Any imported `n₀(d)` used to discharge a finite obligation enters as a documented, undischarged
analytic hypothesis. `conjecture1_proved = False`.
