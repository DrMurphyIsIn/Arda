# MM_speiser_box_probe: design memo for the derivative Euler-Maclaurin machinery

*Authored 2026-09-22 on worktree `arda-goal-weil`, branch `mm/gauss-window`. Design memo,
not a proof. Nothing in this memo, in the island it describes, or in the machinery it
plans, proves or bears on the Riemann Hypothesis. The node is explicitly NOT the Speiser
wall (Speiser 1935: `zeta'` non-vanishing on the whole open left strip is equivalent to
RH); it is one finitely-checkable box, and no finite union of boxes exhausts a strip.*

**`conjecture1_proved = False`.**

Triage verdict, stated once: **design, not provable this session; not grantable; not
nogo.** The artifact is honest and complete modulo exactly two named numeric obligations.
Both need an instrument that does not exist in the repository (a derivative-order
Euler-Maclaurin evaluator, and for N1 a uniform-in-`s` instrument class). The campaign
docs already classify this as blocked on missing machinery (`WALL_BACKLOG_MAP_2026-09-18`
row F4 / op R4; `RH_ASCENT_PLAN_2026-09-18` F3-6, 2-4 weeks, defer past week 4). This memo
turns that classification into an exact theorem list, a mathematical route with the
Mathlib and island lemmas that carry it, line estimates per obligation, and a compute plan
with certificate shapes and the trust seam at every stage.

---

## 0. Where the node stands (registry and island, read-only facts)

| Item | Value |
|---|---|
| Node | `MM_speiser_box_probe`, campaign `mirrormere`, kind `milestone`, status `open`, `depends_on = []`, created 2026-09-16, updated 2026-09-20 |
| Statement | `missions/mirrormere/lean/Statements/MM_speiser_box_probe.lean` (authored, not an island extract): `∀ s : ℂ, 1/4 ≤ s.re → s.re ≤ 3/8 → 6 ≤ s.im → s.im ≤ 10 → deriv riemannZeta s ≠ 0` |
| Artifact | `examples/speiser_box_probe/lean/SpeiserBoxProbe/SpeiserBox.lean`, `closure_clean = false`, `via = direct` |
| Island | `examples/speiser_box_probe/lean/`, 436 lines in 5 files (`GridNonvanishing` 69, `SpeiserBox` 233, `Cert` 76 generated, `AxiomGuardSpeiserBoxProbe` 48, root 10). Mathlib pin `leanprover/lean4:v4.32.0`, mathlib rev `81a5d257c8...` |
| Build state | No `.lake` in this worktree or any sibling (`find` over `~/` found none). Compiled in a now-gone session. |
| Warm Mathlib at the identical rev | `~/arda-gw-finite`, `~/arda-anduril-mod2pi`, `~/arda-million` under `telperion/examples/zeta_reflection/lean/.lake`. I diffed `lake-manifest.json` package by package: all 11 entries match (9 external revs identical; `LambdaLineReal`, `ZeroFreeBridge` are in-repo path deps). |
| Attempts | 2026-09-16 (routes-roadmap E9): Stalled, statement registered draft. 2026-09-20 (mm-e9-speiser-box): Stalled, winding route replaced by the grid-modulus Lipschitz-net kind `grid_modulus_nonvanishing`; numeric winding number 0, min `|zeta'|` on box 0.1911 at corner `3/8 + 6i`. |
| Readback | blind-auditor-2, 2026-09-16, no flags; auditor did not compute the winding number. |
| Backlog | `WALL_BACKLOG_MAP` row 60: BLOCKED-ON missing machinery, op R4 (author `MM_winding_second_derivative`, then re-dep the probe). R4 has NOT been executed: the node still has `depends_on = []`. |

### 0.1 What the island already proves, kernel-clean (17 axiom-guarded declarations)

* `nonvanishing_of_grid` (`GridNonvanishing.lean`): the mean-value instrument. `f` holomorphic
  on convex `R`, `‖deriv f‖ ≤ M` on `R`, `G ⊆ R` a `δ`-net, `‖f‖ ≥ L` on `G`, `M * δ < L`
  gives `∀ z ∈ R, f z ≠ 0`. Proof is `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`.
* Geometry: `convex_box`, `gridSet_subset_box`, `box_covered` (eight points at `re = 5/16`,
  `im = 25/4, ..., 39/4` form a `13/50`-net; half-diagonal `sqrt 17 / 16 < 13/50`).
* Holomorphy: `zeta_deriv_analyticOnNhd`, `hasDerivWithinAt_zeta_deriv` from Mathlib's
  `differentiableAt_riemannZeta` via `DifferentiableOn.analyticOnNhd` and `AnalyticOnNhd.deriv`.
* Capstone `speiser_box_probe_of_numeric (hM : SecondDerivBoundOnBox) (hL : GridModulusLowerBound)`
  discharges the node statement; the gap `(3/10) * (13/50) = 39/500 < 1/10` is re-derived by
  `norm_num` inside the proof.
* `Cert.lean`: 5 generated rational theorems (`speiser_box_cert` and its four conjuncts),
  family `SpeiserBoxCert`, input-hash `8eb59fecce110ebe`.

### 0.2 The two open obligations, verbatim

```lean
def SecondDerivBoundOnBox : Prop :=
  ∀ z ∈ box, ‖deriv (deriv riemannZeta) z‖ ≤ 3 / 10            -- N1

def GridModulusLowerBound : Prop :=
  ∀ g ∈ gridSet, (1 : ℝ) / 10 ≤ ‖deriv riemannZeta g‖          -- N2
```

with `gridModulusLowerBound_of_points h1 ... h8 : GridModulusLowerBound` already proved
for the eight expanded point inequalities. Observed values (mpmath, evidence only):
`sup |zeta''|` on the box `0.2823` (artifact text), `0.2872` (cert sidecar, 8 x 40 sweep),
`0.2811` (my 9 x 81 sweep) -- the sup is near the corner `1/4 + 6i` and is NOT well pinned
by coarse sweeps; the margin to `3/10` is 4-6 percent. `min |zeta'|` on the grid `0.20198`
at `t = 25/4`, rising to `0.38536` at `t = 39/4`; margin to `1/10` is a factor 2.

---

## 1. Why neither obligation closes without new machinery (and why the two hinted shortcuts fail)

Every kernel evaluator in the repository evaluates `zeta` itself at a single point:
`ZetaReflection.em_zeta_strip3_enclosure` (`EMZetaTail.lean:1169`) plus the forge
(`ForgeZ14Terms`/`ForgeZ15Terms`, 9.6k lines each, ~196 generated lines per Dirichlet
term; `ForgeZeta14` assembles 49 terms into a `zeta(1/2 + 14i)` box). Nothing evaluates
`zeta'` or `zeta''`, and nothing is uniform in `s`.

* **N2** needs `zeta'` at eight points. There is no `zeta'` evaluator. The saw-Bernoulli
  identity must be differentiated in `s` (once), and the term generator must emit
  `log n * n^(-s)` brackets (the log part exists: `ForgeLogBracket.log_nat_bracket`).
* **N1** needs `zeta''` uniformly on a continuum. Beyond the second derivative of the
  identity, this is a NEW instrument class: every existing kernel evaluator is single-point.
  The triangle inequality on the Dirichlet sum is useless here (at `sigma = 1/4` the
  absolute sum of `log^2 n * n^(-sigma)` over `n < 100` is `518`, versus a target of
  `0.3`). A Cauchy estimate off a crude `|zeta|` bound gives `M` of order `10^2`-`10^4` and
  a `10^5`-`10^9`-point grid, as the artifact's own note records.

Two hinted shortcuts were checked and are rejected, for the record:

1. **Fractional-part / `LowHeightBox` machinery** (`li_positivity`, Mathlib `v4.34.0-rc1`,
   a different pin from this island's `v4.32.0`). It is order-0 Euler-Maclaurin,
   `zeta(s) = s/(s-1) - s * J(s)` with `J(s) = ∫_1^∞ {x} x^(-s-1)`. Differentiating gives
   `|J| ≤ 1/(2 sigma) ≈ 1.6` and `|s J'| ≤ |s|/sigma^2 ≈ 100` at `sigma = 5/16`; as an
   evaluator with cut `N` its tail is `~32 N^(-5/16)` and needs `N ~ 10^9`. Mathematically
   incapable of `|zeta'| ≥ 0.1` or `|zeta''| ≤ 0.3`, independent of the pin mismatch.
2. **Argument-principle certificate** (`examples/winding_box_zero/WindingBoxZero.cert.lean`).
   It is an Arb-trust sidecar with zero kernel theorems. A kernel winding certificate for
   `zeta'` needs a kernel evaluator of `zeta''/zeta'` along the whole contour -- strictly
   MORE machinery than the grid-modulus route. This is exactly why the 09-20 session
   replaced it.

---

## 2. The exact theorems to prove, in the island's vocabulary

The machinery lives naturally on the `zeta_reflection` island (same pin; that is where
`EMZetaTail`, `ZetaEMSum`, `TrigReduce`, `ForgeLogBracket`, `TaylorKernels`, `CertVerify`
and the forge live). The probe island then path-requires it (the `LambdaLineReal` pattern
in `zeta_reflection/lean/lakefile.toml`). Names below are proposals; the lead fixes them
when authoring the machinery node.

### 2.1 Part A -- the elementary finite part and its derivatives (module `EMZetaDeriv.lean`)

```lean
namespace ZetaReflection

/-- The order-3 finite part in elementary Dirichlet form (the RHS of
    `ZetaEMSum.emZetaFinite3_eq_dirichlet`), taken as a definition so it is
    visibly holomorphic in `s` away from `s = 1`. -/
noncomputable def dirichletFinite3 (N : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s))
    + (N : ℂ) ^ (1 - s) / (s - 1) + (N : ℂ) ^ (-s) / 2
    + (bernoulli 2 : ℂ) * (s * (N : ℝ) ^ (-s - 1)) / 2

/-- The order-3 remainder as a function of `s`: everything `zeta` is not. -/
noncomputable def emRem3 (N : ℕ) (s : ℂ) : ℂ := riemannZeta s - dirichletFinite3 N s

theorem emRem3_norm_le {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) (hs1 : s.re < 1) :
    ‖emRem3 N s‖ ≤ (1 / 12) * ‖s * (s + 1) * (s + 2)‖ * (N : ℝ) ^ (-(s.re + 2)) / (s.re + 2) / 6
  -- from em_zeta_strip3_enclosure + emZetaFinite3_eq_dirichlet; s ≠ 0, 1, -1, -2 are
  -- automatic from 0 < s.re < 1.

theorem differentiableOn_dirichletFinite3 (N : ℕ) :
    DifferentiableOn ℂ (dirichletFinite3 N) {s | s ≠ 1}

/-- k-th derivative of the Dirichlet block: `(-log n)^k n^(-s)`. -/
theorem iteratedDeriv_dirichletSum (N k : ℕ) (s : ℂ) :
    iteratedDeriv k (fun s => ∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s)) s
      = ∑ n ∈ Finset.Ico 1 N, (-(Real.log n : ℂ)) ^ k * (n : ℂ) ^ (-s)

/-- k-th derivative of the boundary block `N^(-s) * g(s)`, `g(s) = N/(s-1) + 1/2 + B2 s/(2N)`,
    by Leibniz: `∑ j, choose k j * (-log N)^(k-j) N^(-s) * g^(j)(s)`, with `g^(j)` explicit. -/
theorem iteratedDeriv_boundaryBlock (N k : ℕ) (hN : 1 ≤ N) {s : ℂ} (hs1 : s ≠ 1) : ...
```

### 2.2 Part B -- derivative bounds on the remainder (module `EMZetaDerivTail.lean`)

Two admissible routes; the recommendation is B-ii as primary with B-i as the tighter
alternative if the constants get tight (Section 3.2 has the numbers).

**B-ii (Cauchy estimate, recommended).** `emRem3 N` is holomorphic on `{s ≠ 1}` (Mathlib
`differentiableAt_riemannZeta` minus Part A). On any closed disc `closedBall s r` inside
`{0 < re < 1}` the bound of `emRem3_norm_le` holds on the sphere, so Mathlib's

```lean
Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le   -- Liouville.lean:44, at the pin
  (n : ℕ) (hR : 0 < R) (hf : DiffContOnCl ℂ f (ball c R)) (hC : ∀ z ∈ sphere c R, ‖f z‖ ≤ C) :
  ‖iteratedDeriv n f c‖ ≤ n.factorial * C / R ^ n
```

gives, with `n = 1, 2`,

```lean
theorem emRem3_deriv_norm_le {N : ℕ} (hN : 1 ≤ N) {s : ℂ} {r : ℝ} (hr : 0 < r)
    (hlo : r < s.re) (hhi : s.re + r < 1) :
    ‖deriv (emRem3 N) s‖ ≤ (1 / 72) * Ctail N s r / r
theorem emRem3_deriv2_norm_le ... : ‖deriv (deriv (emRem3 N)) s‖ ≤ 2 * (1 / 72) * Ctail N s r / r ^ 2
```

where `Ctail N s r := sup over the sphere of ‖w(w+1)(w+2)‖ N^(-(w.re+2))/(w.re+2)`, which is
bounded by the explicit monotone envelope `(‖s‖+r+2)^3 * N^(-(s.re - r + 2)) / (s.re - r + 2)`.
No new integral theory at all: `em_tail3_bound` is reused verbatim through `emRem3_norm_le`.

**B-i (differentiate under the `Ioi` integral).** Apply
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` (`ParametricIntegral.lean:288` at the pin)
to `s ↦ ∫ x in Ioi N, saw₃ x * (emTailCoeff3 s * x^(-s-3))`, integrand derivative
`saw₃ x * ((c₃'(s) - c₃(s) log x) x^(-s-3))`, and again for the second derivative with
`c₃'' - 2 c₃' log x + c₃ log² x`. Needs the log-weighted tail kernels

```
∫_N^∞ log^k x * x^(-a-1) dx = N^(-a) * [1/a ; log N/a + 1/a² ; log² N/a + 2 log N/a² + 2/a³]   (k = 0,1,2)
```

proved by `integral_Ioi_of_hasDerivAt_of_tendsto` with the explicit antiderivative, plus
integrability of `log^k x * x^(-a-1)` on `Ioi N` (`a > 0`). Tighter by a factor ~4 than B-ii
at `N = 100`, at roughly 4x the Lean cost (this is the shape `EMZetaTail.lean` paid 1241
lines for at order 0).

### 2.3 Part C -- the point evaluator for `zeta'` (N2)

Per grid point `g = ⟨5/16, t⟩`, `t ∈ {25/4, ..., 39/4}`, with cut `N`:

```lean
theorem dz_re_<t> : lo ≤ (deriv (dirichletFinite3 N) g).re ∧ ... ≤ hi     -- forge-generated
theorem dz_im_<t> : ...
theorem abs_zeta_deriv_lower_<t> : (1 : ℝ) / 10 ≤ ‖deriv riemannZeta g‖ := by
  -- deriv riemannZeta = deriv (dirichletFinite3 N) + deriv (emRem3 N)
  -- ‖·‖ ≥ ‖D'‖ - ‖R'‖ ≥ sqrt(lo_re² + lo_im² [corner-min]) - emRem3_deriv_norm_le
```

The generated term theorems are the `re_term_n`/`im_term_n` of `ForgeZ14Terms` with two
changes: the amplitude is `n^(-5/16) = exp(-(5/16) log n)` (from `ForgeLogBracket.exp_le_rat`
/ `rat_le_exp`, the same lemmas that already prove `thetaT14_n`), and each term carries an
extra `log n` factor bracketed by `log_nat_bracket` and multiplied in by `mul_encl`. The
assembly is `ForgeZeta14.reSum/imSum` (a `Finset.sum_range_succ` unroll + `linarith` over
the term brackets) plus a `ForgeTailTerms.tail_re_im`-style boundary-derivative lemma.

Then `N2 := gridModulusLowerBound_of_points abs_zeta_deriv_lower_25_4 ... _39_4`.

### 2.4 Part D -- the uniform instrument for `zeta''` (N1): Taylor cells with a triangle remainder

This is the new instrument class. The cell lemma (generic, handwritten once):

```lean
/-- Taylor-cell bound.  `f` is `K`-times differentiable on a convex `C ∋ s₀`; the first
    `K` derivatives at `s₀` are enclosed; the `K`-th derivative is bounded on `C` by `B`.
    Then on `C`, `‖f s‖ ≤ ∑_{k<K} ‖f^(k)(s₀)‖ δ^k / k! + B δ^K / K!` for `δ ≥ sup ‖s - s₀‖`. -/
theorem norm_le_of_taylor_cell {f : ℂ → ℂ} {C : Set ℂ} {s₀ : ℂ} {δ B : ℝ} {K : ℕ}
    (hC : Convex ℝ C) (hs₀ : s₀ ∈ C) (hδ : ∀ s ∈ C, ‖s - s₀‖ ≤ δ)
    (hf : ∀ s ∈ C, ContDiffAt ℂ K f s)          -- or DifferentiableOn of each iteratedDeriv
    (hB : ∀ s ∈ C, ‖iteratedDeriv K f s‖ ≤ B) :
    ∀ s ∈ C, ‖f s‖ ≤ (∑ k ∈ Finset.range K, ‖iteratedDeriv k f s₀‖ * δ ^ k / k.factorial)
                       + B * δ ^ K / K.factorial
```

Proof: restrict to the segment `u ↦ f (s₀ + u • (s - s₀))`, `u ∈ [0,1]`, and apply Mathlib
`taylor_mean_remainder_bound` (`Taylor.lean:390` at the pin) to the real-variable
composite, or iterate `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` `K` times on the
successive derivatives. The `iteratedDerivWithin`-to-`iteratedDeriv` bookkeeping is the
fiddly part.

Applied with `f = deriv (deriv riemannZeta) = D'' + R''` where `D = dirichletFinite3 N`:

* the point values `iteratedDeriv k D'' s₀ = D^(2+k)(s₀)`, `k < K`, are Dirichlet
  polynomials with weights `(-log n)^(2+k)` plus explicit boundary derivatives -- evaluated
  by the Part C forge with `kmax = 1 + K`, all sharing ONE set of `n^(-s₀)` trig/amplitude
  brackets per cell;
* the remainder bound `B` is the triangle inequality at `sigma = 1/4` (the segment stays in
  the box by convexity, so no `sigma` allowance is needed):
  `‖D^(2+K)(s)‖ ≤ S_{2+K}(N) + boundary bound`, `S_k(N) := ∑_{n<N} log^k n * n^(-1/4)`, a
  rational upper bound proved once per `(N, K)` by `norm_num`/`decide` over `log n` brackets;
* `R''` is bounded uniformly on the box by `emRem3_deriv2_norm_le` at the worst corner
  (`sigma = 1/4`, `t = 10`), one theorem;
* the cells are a finite rectangular cover of the box, produced by an adaptive planner
  (Section 3.3) and proved to cover by a `box_covered`-style case split.

```lean
theorem secondDerivBoundOnBox_of_cells (hcells : ∀ i, ∀ z ∈ cell i, ‖deriv (deriv riemannZeta) z‖ ≤ 3/10)
    (hcover : box ⊆ ⋃ i, cell i) : SecondDerivBoundOnBox
```

### 2.5 Part E -- composition

```lean
theorem speiser_box_probe : ∀ s : ℂ, 1/4 ≤ s.re → s.re ≤ 3/8 → 6 ≤ s.im → s.im ≤ 10 →
    deriv riemannZeta s ≠ 0 :=
  speiser_box_probe_of_numeric N1_proof N2_proof
```

which is the registered statement verbatim; the statement file's placeholder is then
replaced by the island link (`mission link`, lead only).

---

## 3. The numbers that make the route viable (mpmath, evidence only, dps 20-30)

### 3.1 Sizes on the box (coarse sweep)

`sup |zeta'| ≈ 0.42`, `sup |zeta''| ≈ 0.28-0.29`, `sup |zeta'''| ≈ 0.20`,
`sup |zeta''''| ≈ 0.16`, `sup |zeta^(5)| ≈ 0.13`. At `s₀ = 5/16 + 8i`:
`zeta''(s₀) ≈ 0.0027 + 0.1489i`.

### 3.2 Remainder derivative bounds at the worst corner `s = 1/4 + 10i`

| N | `|R|` (order 0, existing) | B-i `|R'|` | B-i `|R''|` | B-ii `|R'|` (r = 3/16) | B-ii `|R''|` (r = 3/16) |
|---|---|---|---|---|---|
| 50 | 9.6e-4 | 4.5e-3 | 2.1e-2 | 1.2e-2 | 1.2e-1 |
| 100 | 2.0e-4 | 1.1e-3 | 5.8e-3 | 2.8e-3 | 3.0e-2 |
| 200 | 4.2e-5 | 2.6e-4 | 1.6e-3 | 6.6e-4 | 7.1e-3 |
| 400 | 8.9e-6 | 6.0e-5 | 4.1e-4 | 1.6e-4 | 1.7e-3 |

Budgets: N2 has `0.202 - 0.100 = 0.10` to spend, so `N = 50` with either route is
comfortable. N1 has only `0.300 - 0.287 = 0.013` at `M = 3/10`; B-ii needs `N ≥ 200`
(`7.1e-3`), B-i needs `N ≥ 100` (`5.8e-3`). Raising `M` to `3/8` (the gap
`(3/8)(13/50) = 39/400 < 1/10` still closes with the existing grid, `Cert.lean` regenerates
with one constant changed) widens the N1 budget to `0.088` and lets B-ii work at `N = 100`;
recommended, since `3/10` was chosen before anyone priced the machinery.

### 3.3 Cell counts for N1 (adaptive planner, `K` point derivatives + triangle remainder)

Triangle sums `S_k(N) = ∑_{n<N} log^k n * n^(-1/4)`:
`N = 50`: `S_4 = 2.2e3, S_5 = 7.6e3, S_6 = 2.7e4, S_7 = 9.4e4, S_8 = 3.4e5`;
`N = 100`: `S_4 = 8.1e3, S_5 = 3.3e4, S_6 = 1.4e5, S_7 = 5.7e5, S_8 = 2.4e6`.

Cells needed (planner splits the longer side until the cell bound clears `M`, with
`2e-3` slack for enclosure widths):

| M | N | K = 3 | K = 4 | K = 5 | K = 6 |
|---|---|---|---|---|---|
| 3/10 | 100 | 636 | 103 | 34 | 17 |
| 3/10 | 200 | 1441 | 182 | 53 | -- |
| 3/8 | 50 | -- | 33 | 16 | 11 |
| 3/8 | 100 | 447 | 77 | 31 | 16 |

Two findings that shape the plan. (a) Order matters far more than `M`: the `S_{2+K} δ^K/K!`
term dominates, so `K = 5` or `6` is the right order and `K ≤ 3` is hopeless
(`K = 2` needs `> 10^5` cells, which is the "10^5-10^9 grid" of the artifact note). (b) The
exact-corner enclosure of the linear Taylor term (`|a + b w|` is convex in `w`, so its max
over a rectangle is at a corner) changes nothing (34 vs 35 cells); skip it.

**Baseline choice: `M = 3/8`, `N = 50`, `K = 5`: 16 cells, each needing `D^(2..6)(s₀)`
(five Dirichlet-polynomial enclosures over 49 shared term brackets with `log^k n`
weights, `k = 2..6`) and the one-off rational `S_7(50) ≤ 9.4e4` bound.** If `M` must stay
`3/10`: `N = 100`, `K = 5`, 34 cells, with route B-i for the remainder.

### 3.4 Generated-Lean volume (at the current forge cost of ~196 lines per term)

* N2: 8 points x 49 terms = 392 term enclosures, ~77k lines + 8 assembly modules
  (~300 lines each, `ForgeZeta14` shape). Four times the existing `ForgeZ14Terms` corpus.
* N1 baseline: 16 cells x 49 terms = 784 term enclosures, ~155k lines + 16 cell modules.
  `M = 3/10` fallback: 34 x 99 = 3366 term enclosures, ~660k lines.
* Optimisation, if the volume bites: the trig brackets `cos/sin(t log n)` at a new
  `t' = t + Δ` follow from those at `t` by the addition formula with `cos/sin(Δ log n)`
  computed by a short Taylor bracket (`|Δ log n| ≤ 0.6 * 3.9 < 2.4`, two doublings at most)
  instead of the 22-doubling climb -- roughly 15-25 lines per term instead of ~196. Not
  needed for the baseline; needed for the `M = 3/10` fallback.

Compile times for the forge modules are NOT recorded anywhere I could find (no timing in
the docs); the existing 9.6k-line term files build inside the current `zeta_reflection`
default target. Treat the wall-clock figures in Section 6 as estimates to be measured at J4.

---

## 4. Lemmas available at the pin (verified by grep in `~/arda-gw-finite/.../.lake/packages/mathlib`)

Mathlib (`v4.32.0`, rev `81a5d257c8`):

| Lemma | Where | Use |
|---|---|---|
| `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` | `Analysis/Complex/Liouville.lean:44` | Part B-ii, `n = 1, 2` |
| `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` | `Liouville.lean:76` | Part B-ii, first derivative |
| `hasDerivAt_integral_of_dominated_loc_of_deriv_le` | `Analysis/Calculus/ParametricIntegral.lean:288` | Part B-i |
| `integral_Ioi_of_hasDerivAt_of_tendsto`, `integral_Ioi_rpow_of_lt` | `SpecialFunctions/ImproperIntegrals.lean` | Part B-i kernels |
| `taylor_mean_remainder_bound` | `Analysis/Calculus/Taylor.lean:390` | Part D cell lemma |
| `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` | `Analysis/Calculus/MeanValue.lean` | Part D (iterated alternative), already used by `nonvanishing_of_grid` |
| `HasDerivAt.const_cpow` | `SpecialFunctions/Pow/Deriv.lean:214` | Part A, `n^(-s)` derivative |
| `HasDerivAt.sum`, `deriv_sum` | `Analysis/Calculus/Deriv/Add.lean` | Part A |
| `iteratedDeriv_eq_iterate`, `Complex.taylorSeries_eq_on_ball` | `Analysis/Complex/TaylorSeries.lean` | Part A/D bookkeeping |
| `Complex.norm_cpow_eq_rpow_re_of_pos` | `Pow/Deriv.lean` | amplitude `|n^(-s)| = n^(-sigma)` |
| `differentiableAt_riemannZeta`, `riemannZeta` API | Mathlib NumberTheory | already used by the island |

Not at the pin (do not plan on them): `Complex.norm_iteratedDeriv_le` (bare),
`Complex.norm_deriv_le_aux`, `hasDerivAt_const_cpow` (unprimed form), `HasSum.hasDerivAt`.

Island (`zeta_reflection`, same pin):

| Lemma | Where | Use |
|---|---|---|
| `em_zeta_strip3`, `em_zeta_strip3_enclosure` | `EMZetaTail.lean:1128, 1169` | the order-0 identity and enclosure |
| `em_tail3_bound`, `emTailCoeff3` | `EMZetaTail.lean:561, 555` | tail envelope reused by B-ii |
| `emZetaFinite3_eq_dirichlet` | `ZetaEMSum.lean:29` | elementary finite part (hyps `s ≠ 0`, `s ≠ 1`, `N ≥ 1`, `re s < 1`) |
| `em_zeta_strip` (K = 1) | `EMZetaComplex.lean:732` | not needed; superseded |
| `ForgeTailTerms.tail_re_im`, `tail_eq_wB` | `ForgeTailTerms.lean:25, 47` | boundary block Re/Im, extend to derivatives |
| `ForgeLogBracket.log_nat_bracket`, `exp_le_rat`, `rat_le_exp`, `mul_encl` | `ForgeLogBracket.lean` | `log n` brackets, `n^(-5/16)` amplitude, products |
| `TrigReduce.cos/sin_base_interval`, `cos/sin_double_interval`, `cos/sin_encl_bracket`, `add_encl` | `TrigReduce.lean` | the climb |
| `ZeroHypBand_t14.term_re/term_im` | `ZeroHypBand_t14.lean:98` | template for `(n:ℂ)^(-s)` Re/Im at general `sigma` (currently `1/2`-specific; generalise) |
| `ForgeZeta14.reSum/imSum`, `zt14_*` | `ForgeZeta14.lean` | assembly template |
| `trig_forge.py` | `examples/zeta_reflection/` | the generator (exact `Fraction` interval arithmetic, dyadic scale 60, self-check + corruption self-check) |

Island (`speiser_box_probe`): everything in Section 0.1, unchanged.

---

## 5. Named obligations with honest line estimates

| # | Obligation | Statement (short) | Handwritten Lean | Generated | Risk |
|---|---|---|---|---|---|
| A1 | `dirichletFinite3`, `emRem3`, `emRem3_norm_le` | reuse of existing identities | 60-100 | -- | low |
| A2 | `differentiableOn_dirichletFinite3`, `iteratedDeriv_dirichletSum` | `(-log n)^k n^(-s)` | 120-200 | -- | low-medium (cpow derivative API) |
| A3 | `iteratedDeriv_boundaryBlock` for `k ≤ 7` (Leibniz on `N^(-s) g(s)`) | explicit | 200-300 | -- | medium (algebra volume) |
| B-ii | `emRem3_deriv_norm_le`, `emRem3_deriv2_norm_le` + monotone envelope | Cauchy | 200-350 | -- | low (Mathlib lemma is exact fit; `DiffContOnCl` on the ball is the only fiddle) |
| B-i (alt) | differentiated tail identity + 3 log-kernels + integrability | direct | 900-1500 | -- | medium-high |
| C1 | general-`sigma` term Re/Im lemmas (`term_re/im` with `sigma = 5/16`), `log^k`-weighted term shape, per-point assembly template | evaluator | 250-400 | 8 x ~10k | low (mechanical, mirrors existing) |
| C2 | Python: `emit_deriv_point(sigma, t, N, kmax)` in `trig_forge.py` with self-check and corruption check | generator | 600-1000 Python | -- | low |
| D1 | `norm_le_of_taylor_cell` (generic Taylor-cell lemma) | instrument | 300-500 | -- | medium-high (`iteratedDerivWithin` bookkeeping) |
| D2 | triangle bound `S_{2+K}(N)` rational + boundary-derivative bound, uniform `R''` bound at worst corner | remainder | 200-300 | one `norm_num` sum | low |
| D3 | cell planner (Python) + per-cell module template + `box ⊆ ⋃ cells` cover | cells | 150-250 + 300 Python | 16 x ~10k | low |
| E | capstone composition, AxiomGuard extension, `Cert` regeneration with `M = 3/8` | wiring | 80-150 | -- | low |

Totals: **handwritten Lean ~1600-2500 (B-ii) or ~2300-3700 (B-i)**, Python ~1000-1300,
generated Lean ~230k lines baseline (up to ~750k in the `M = 3/10` fallback without the
addition-formula optimisation). The prior triage figure "~3500" is the B-i total; B-ii is
the cheaper path and should be tried first. Multiply by 1.5 for the usual Lean-derivative
friction and this is a 2-4 week single-agent project, matching `RH_ASCENT_PLAN` F3-6.

---

## 6. Compute plan

Rules honoured: one lake build per island at a time (orchestrator serialises;
`zeta_reflection` builds first, then `speiser_box_probe` which path-requires it); no git
from the agent; after any island build `rm -rf <island>/.lake/build/ir` per the ascent plan.

| Job | Inputs | What runs | Wall-clock / cores (estimates, unmeasured where marked) | Emits | Composes into | Trust seam after the job |
|---|---|---|---|---|---|---|
| J0 restore builds | `~/arda-gw-finite/telperion/examples/zeta_reflection/lean/.lake` (manifest verified identical) | `cp -Rc` the `.lake` into this worktree's `zeta_reflection/lean/`; `cp -Rc` its `packages/` into `speiser_box_probe/lean/.lake/packages/`; `lake build` the probe island (~450 lines); `lake env lean AxiomGuardSpeiserBoxProbe.lean` | 5-15 min, 1-8 cores | axiom printout: 17 declarations, `{propext, Classical.choice, Quot.sound}` | re-verifies the existing island | unchanged: N1, N2 open hypotheses |
| J1 Part A | `EMZetaTail`, `ZetaEMSum` | author `EMZetaDeriv.lean`; `lake build` on `zeta_reflection` | 2-3 days authoring; build minutes | A1-A3 theorems | Parts B-D | none new |
| J2 Part B-ii | J1 | author `EMZetaDerivTail.lean` | 2-3 days; build minutes | `emRem3_deriv_norm_le`, `emRem3_deriv2_norm_le` with explicit envelope in `(N, s, r)` | C, D | none new |
| J3 forge extension | `trig_forge.py` | `emit_deriv_point`; mpmath candidate producer; `--self-check` corruption run | 2-4 days | per-term `re/im_term_n` with `log^k n` weights; per-point assembly | J4, J5 | mpmath is a candidate producer only; every emitted bound is a kernel `norm_num` goal |
| J4 N2 numerics | J2, J3; 8 points, `N = 50`, `kmax = 1` | generate 8 term modules + 8 assembly modules; one `lake build` (modules parallelise inside it) | generation seconds; build est. 20-60 min wall on 8-32 cores (MEASURE here: this calibrates J5) | `abs_zeta_deriv_lower_<t>` x 8, each `(1:ℝ)/10 ≤ ‖deriv riemannZeta ⟨5/16, t⟩‖` | `gridModulusLowerBound_of_points` gives `GridModulusLowerBound` | **N2 discharged**; N1 still an open hypothesis of the capstone |
| J5 N1 numerics | J1-J3; planner output (cell list JSON: centres, half-extents, `K = 5`, `N = 50`, `M = 3/8`) | planner (mpmath, seconds); 16 term modules (`kmax = 6`) + 16 cell modules + `S_7` rational bound + uniform `R''` bound + cover lemma; one `lake build` | build est. 1-3 h wall on 32 cores (scale from J4; fallback config ~4x) | `abs_zeta_deriv2_le_cell_<i>` x 16, `box_subset_cells`, `secondDerivBoundOnBox_of_cells` | `SecondDerivBoundOnBox` | **N1 discharged** |
| J6 capstone | J4, J5 | `speiser_box_probe := speiser_box_probe_of_numeric N1 N2`; extend AxiomGuard; regenerate `Cert.lean` with `M = 3/8` (`generate.py --check`); probe-island `lake build` | minutes | axiom printout on all headline theorems | the registered statement, verbatim | **no hypotheses remain**; axioms `{propext, Classical.choice, Quot.sound}`; the mpmath sidecar stays evidence-only |

Certificate shapes, precisely:

* N2 point certificate: `(t, N, [term brackets (lo_re, hi_re, lo_im, hi_im, log-weight k = 0, 1)], D'-box (lo_re, hi_re, lo_im, hi_im), R'-envelope rational, floor 1/10)`; kernel content = the two `D'` boxes and the inequality `sqrt(min corner²) - envelope ≥ 1/10` (as a squared rational inequality, no `sqrt`).
* N1 cell certificate: `(cell rectangle, s₀, K, N, [D^(2..6)(s₀) boxes], δ rational ≥ half-diagonal, S_7 rational bound, R''-envelope, claimed M)`; kernel content = `∑_{k<K} ‖D^(2+k)(s₀)‖ δ^k/k! + S_7 δ^5/120 + R'' ≤ 3/8` via `norm_le_of_taylor_cell`.
* Cover certificate: the cell list tiles `[1/4, 3/8] x [6, 10]` (rational endpoint comparisons, `box_covered` shape).
* The existing `SpeiserBoxCert` gap certificate, regenerated once for `M = 3/8`.

Registry actions (lead only; recorded here as recommendations): execute `WALL_BACKLOG_MAP`
R4 -- `mission add MM_winding_second_derivative --campaign mirrormere --kind lemma` -- with
a title that says what it now is: "derivative-order Euler-Maclaurin evaluator for `zeta'`
and `zeta''` on `0 < re s < 1` (Parts A-B) plus the Taylor-cell uniform instrument
(Part D); grid-modulus route, not a winding integrand". Then
`MM_speiser_box_probe --deps MM_winding_second_derivative`. Log this memo as an attempt on
the probe with verdict Stalled and route "design memo; machinery node authored".

---

## 7. What the node would and would NOT establish

Would establish, kernel-checked, no hypotheses: `deriv riemannZeta` has no zero in the
closed rectangle `[1/4, 3/8] x [6, 10]`. As an instrument result: the first kernel-checked
`zeta'` and `zeta''` enclosures in the repository, the first uniform-in-`s` bound of a
`zeta`-derivative on a 2-D region, and a reusable Taylor-cell instrument.

Would NOT establish:

* anything about the Riemann Hypothesis. The Speiser equivalence consumes the whole open
  strip `0 < re s < 1/2`; a box, or any finite union of boxes, decides nothing.
  `conjecture1_proved = False` before, during and after.
* a zero COUNT for `zeta'` anywhere (the grid-modulus instrument certifies zero-freeness
  only; a genuine winding certificate would need strictly more machinery).
* anything surprising about `zeta'`: the box is far from every known zero of `zeta'` (the
  lowest lies near `2.46 + 23.3i`, right of the line, where the zeros of `zeta'` are known
  to cluster); the 09-20 attempt already observed winding number 0 and
  `min |zeta'| = 0.1911` numerically. The value of the node is the instrument, not the fact.
* the RH-equivalent nodes (`RH_conjecture`, `MM_zeta_comb_membership`) are out of scope and
  untouched.

---

## 8. Risks and footguns

* `SecondDerivBoundOnBox` hardcodes `3/10`. Either keep it and pay for `N = 100` plus route
  B-i (34 cells), or change the constant to `3/8` in `SpeiserBox.lean` and regenerate
  `Cert.lean` (the gap `39/400 < 1/10` still closes; the artifact's own prose says `M` is a
  tunable, not a cliff). Recommend `3/8`; it is a 6-line edit plus `generate.py`.
* The observed `sup |zeta''|` differs between sweeps (0.2811 / 0.2823 / 0.2872). It sits at
  or near the corner `1/4 + 6i`; the planner must refine cells there and must not trust a
  coarse sweep for the margin. At `M = 3/8` this ceases to matter.
* Part D's `norm_le_of_taylor_cell` is the only genuinely new Lean idea; the
  `iteratedDerivWithin`/`taylorWithinEval` API is awkward. Budget for it first, since if it
  slips, N1 has no route.
* `ZeroHypBand_t14.term_re/im` are stated for `sigma = 1/2`; the general-`sigma` versions
  are a mechanical rewrite but must exist before any generation.
* Island plumbing: `zeta_reflection/lean/lakefile.toml` exposes modules as `lean_lib`
  roots; the new modules must be added as roots or the path-require from the probe island
  will not see them. One build per island; do not start the probe build while
  `zeta_reflection` builds.
* CI greps for the bare placeholder word in comments; write "no `sorry`" style only.
* No emoji anywhere; QuantConnect and the CI reject them.
* The `.lake` copies must be reflink (`cp -Rc`) and the manifest revs re-checked before
  trusting the build (done for `arda-gw-finite`: all 11 entries match).

---

*Design memo only. Nothing above proves the node; N1 and N2 remain open hypotheses of the
kernel-checked capstone `speiser_box_probe_of_numeric` until J5 and J4 land. Nothing above
proves, advances or bears on RH. `conjecture1_proved = False`.*
