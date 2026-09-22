# C3, de Bruijn 1950: design memo for `RH_dbn_debruijn_real_zeros`

*Authored 2026-09-22 for the rh campaign. DESIGN ONLY: no Lean was written, the node
stays `draft`, its statement file ends in the by-design placeholder, and nothing in this
memo is evidence for or against the Riemann Hypothesis.*
**`conjecture1_proved = False`. Nothing here proves RH.** RH-equivalent nodes
(`RH_conjecture`, `MM_zeta_comb_membership`) are out of scope and untouched.

This memo does five things: it fixes the exact theorem in the island's vocabulary
(section 1), it fixes the mathematical route and reconciles it with the triage wording
(section 2), it inventories what Mathlib at the pinned rev and the `dbn` island already
supply (section 3), it names every obligation with an honest line estimate (section 4),
and it gives the compute plan, the registry decisions (the `depends_on` edge) and the trust
seam (sections 5 to 7). Section 8 records the checks that were actually run.

---

## 0. Triage summary and two corrections

The node is the unconditional `Lambda <= 1/2` half of de Bruijn-Newman theory. It is real
F2 effective-constant content, it leaves `RiemannHypothesis` exactly as open as before,
and it is in scope. It is not a one-session provable: the statement is fine and the island's
entry lemmas exist, but the zero-location apparatus (Hadamard-type factorization, strip
contraction under the backward heat operator, Hurwitz closure) is absent from Mathlib and is
a first formalization anywhere. Total priced below at about 4500 lines, in the roadmap's
3000-6000 band and its 1-3 month window.

Two triage statements are corrected here, with evidence in section 8:

1. **Island bring-up does not need a fresh Mathlib build.** `examples/dbn/lean/lake-manifest.json`
   pins exactly the same package revs (Mathlib `de5ce8a9`, LiCriterion `35df682f`, and all
   transitive deps) as `examples/li_positivity/lean/lake-manifest.json`, and the
   `li_positivity` island in THIS worktree has `.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean`
   and a built `Lc` library. A reflink copy of that `packages` directory (14 GB, APFS clone is
   near-instant) into `examples/dbn/lean/.lake/packages` leaves only `DBNDefs` and
   `AxiomGuardDBN` to compile. Section 5, job J0.
2. **The route is strip contraction, and the discretization matters.** The triage phrase
   "e^{tu^2} Phi(u) is a locally-uniform limit of functions whose cosine transforms have
   only real zeros" is exactly right, but the approximants must be the kernels
   `Phi(u) cosh(delta u)^N` (vertical-shift averages on the function side), not
   `(1 + t u^2/N)^N Phi(u)` (the operator `1 - eps D^2`): the latter only PRESERVES a zero
   strip and fails to contract it at multiple zeros (section 2.3). The C2 identity
   `H_0 = xi/8` is not an input; what is needed from the zeta side is only the
   absolutely-convergent half-plane, i.e. Euler-product nonvanishing (section 2.1).

---

## 1. The statement (as registered)

Node `RH_dbn_debruijn_real_zeros`, kind `milestone`, status `draft`, currently
`depends_on = ["RH_dbn_H0_eq_xi"]` (section 6 recommends changing this). Generated
statement `missions/rh/lean/Statements/RH_dbn_debruijn_real_zeros.lean`:

```lean
theorem dbn_debruijn_real_zeros :
    ∀ t : ℝ, 1 / 2 ≤ t → ∀ z : ℂ, DBN.H t z = 0 → z.im = 0 := by <by-design placeholder>
```

(The generated file ends in the placeholder tactic, quoted here without spelling it so the
CI grep stays quiet.)

Vocabulary, from `examples/dbn/lean/DBNDefs.lean` (all axiom-clean per `AxiomGuardDBN.lean`):

```lean
noncomputable def Φ (u : ℝ) : ℝ :=
  ∑' n : ℕ+, (2 * π ^ 2 * n ^ 4 * exp (9 u) - 3 * π * n ^ 2 * exp (5 u)) * exp (-π n^2 exp (4 u))
noncomputable def HIntegrand (t : ℝ) (z : ℂ) (u : ℝ) : ℂ := (exp (t u^2) : ℂ) * (Φ u : ℂ) * cos (z u)
noncomputable def H (t : ℝ) (z : ℂ) : ℂ := ∫ u in Set.Ioi (0 : ℝ), HIntegrand t z u
```

So `H t z = ∫_0^∞ e^{tu²} Φ(u) cos(zu) du` in the Polymath15 / Rodgers-Tao convention. The
statement is correct as written and is NOT changed by this memo. In classical language it is
de Bruijn's theorem: for `t >= 1/2` every zero of `H_t` is real; equivalently (once `Lambda`
is defined, which is a later node) `Lambda <= 1/2`.

Island theorems the proof starts from: `differentiable_H` (H_t entire, all t), `H_neg`
(even), `H_ofReal_im` (real on the real axis), `integrableOn_HIntegrand`,
`integrableOn_exp_quad_mul_exp_neg_exp` (the majorant `e^{a u²} e^{b u} e^{-(π/2) e^{4u}}`),
`abs_Φ_le` (decay for `u >= 0`), `Φ_even`, `continuous_Φ`, `Φ_eq`, `hasDerivAt_H`.

---

## 2. The mathematical route

### 2.0 Shape

The theorem is the composition of three facts, with citations in section 2.5.

* **(I) Zero strip of `H_0`.** Every zero of `H_0` lies in the closed strip `|Im z| <= 1`.
* **(II) Strip contraction.** Multiplying the kernel by `e^{tu²}` contracts a horizontal
  zero strip `|Im z| <= Δ` to `|Im z| <= sqrt(max(Δ² - 2t, 0))`. With `Δ = 1` and
  `t >= 1/2` the strip collapses to the real axis.
* **(III) Closure.** The contraction is proved for approximants and transferred to `H_t` by
  locally uniform convergence plus a Hurwitz-type argument.

Nothing in (I)-(III) uses that `H_0` is `xi/8`; nothing in (I)-(III) says anything about
zeros of `H_0` inside the strip, which is where RH lives.

### 2.1 Fact (I) without C2: the absolutely-convergent half-plane

Write `a_n(u) := (2π²n⁴e^{9u} - 3πn²e^{5u}) e^{-πn²e^{4u}}`, so `Φ = Σ_{n>=1} a_n` for every
real `u` by definition, and `H_0(z) = (1/2) ∫_ℝ Φ(u) e^{izu} du` by evenness of `Φ`.

For each `n` and each `k` with `k - Im z > 0`, the substitution `x = πn² e^{4u}` turns
`∫_ℝ e^{ku} e^{-πn²e^{4u}} e^{izu} du` into a Gamma integral:
`(1/4) (πn²)^{-(k+iz)/4} Γ((k+iz)/4)`. With `s := 1/2 + iz/2`, so `(9+iz)/4 = 2 + s/2` and
`(5+iz)/4 = 1 + s/2`, and `Γ(s/2+2) = (s/2)(s/2+1)Γ(s/2)`, `Γ(s/2+1) = (s/2)Γ(s/2)`:

```
∫_ℝ a_n(u) e^{izu} du = (1/4)(πn²)^{-s/2} Γ(s/2) [ 2(s/2)(s/2+1) - 3(s/2) ]
                       = (1/8) s (s-1) π^{-s/2} Γ(s/2) n^{-s}.
```

Summing needs `Σ_n ∫ |a_n(u)| e^{-(Im z) u} du < ∞`. With `y := -Im z`, the same Gamma
computation bounds the `n`-th term by `C_y n^{-(1+y)/2}`, summable iff `y > 1`. Hence, for
`Im z < -1` (equivalently `Re s > 1`), Tonelli/Fubini gives

```
H_0(z) = (1/16) s (s-1) π^{-s/2} Γ(s/2) ζ(s),   s = 1/2 + iz/2,  Re s > 1,
```

using `zeta_eq_tsum_one_div_nat_cpow` for `ζ(s) = Σ n^{-s}`. On `Re s > 1`: `s ≠ 0, 1`,
`Γ(s/2) ≠ 0` (`Complex.Gamma_ne_zero_of_re_pos`), `π^{-s/2} ≠ 0`, and `ζ(s) ≠ 0`
(`riemannZeta_ne_zero_of_one_lt_re`, the Euler product). So `H_0 ≠ 0` on `Im z < -1`, and by
`H_neg` on `Im z > 1`. This is fact (I): **every zero of `H_0` has `|Im z| <= 1`**, and as a
by-product `H_0 ≢ 0`.

Sanity check against C2: summing the display over `n` gives `(1/16)·2ξ(s)·... = ξ(s)/8` with
`ξ(s) = (1/2)s(s-1)π^{-s/2}Γ(s/2)ζ(s)`, the C2 normalization. This memo does NOT prove C2:
the identity above is only claimed on `Re s > 1`, where it is a termwise Mellin computation
with no analytic continuation, no theta functional equation and no integration by parts.

If C2 (`RH_dbn_H0_eq_xi`) lands first, fact (I) can instead be read off `xi`'s zero set via
`riemannZeta_ne_zero_of_one_le_re` and `completedRiemannZeta_one_sub`; that is an
alternative, not a requirement.

### 2.2 Fact (II): the discrete de Bruijn step

Let `f` be a real, even entire function with a zero set closed under `z ↦ -z` and `z ↦ conj z`
and with a convergent even product representation (section 2.4 says exactly which class).
For `δ > 0` define the vertical-shift average

```
(T_δ f)(z) := (1/2) (f(z + iδ) + f(z - iδ)).
```

On the kernel side this is multiplication by `cosh(δu)`: if `f(z) = ∫_0^∞ F(u) cos(zu) du`
with `F` even and real then `(T_δ f)(z) = ∫_0^∞ F(u) cosh(δu) cos(zu) du`, because
`cos((z+iδ)u) + cos((z-iδ)u) = 2 cos(zu) cosh(δu)`. This stays entirely inside the island's
one-sided `Ioi 0` cosine vocabulary.

**Lemma (discrete step).** If all zeros of `f` lie in `|Im z| <= Δ` and `f ≢ 0`, then all
zeros of `T_δ f` lie in `|Im z| <= sqrt(max(Δ² - δ², 0))`.

*Proof.* `T_δ f` is again real and even, so it suffices to rule out a zero `w = x + iy` with
`y > 0` and `y² > Δ² - δ²`. From `f(w+iδ) = -f(w-iδ)`:

* If `f(w+iδ) = 0` then also `f(w-iδ) = 0`, so `y + δ <= Δ`, hence `y² <= (Δ-δ)² <= Δ² - δ²`
  (the last step because `δ <= Δ` is forced by `y + δ <= Δ`). Contradiction.
* Otherwise `|f(w+iδ)| = |f(w-iδ)| ≠ 0`. Expand both sides as the product over zeros. Every
  zero contributes through one of the following factor groups, each evaluated at
  `Y = y + δ` on the left and `Y = y - δ` on the right:
  - the factor `z^{2m}` (zero at the origin): `|w ± iδ|² = x² + (y ± δ)²`, strictly increasing
    in `Y`;
  - a real pair `±x_k`: `|w±iδ - x_k| |w±iδ + x_k|`, each factor strictly increasing in `Y`;
  - a non-real quadruple `±z_k, ±conj z_k` with `z_k = x_k + i y_k` (a pair when `x_k = 0`):
    with `a := x - x_k` (and `a' := x + x_k` for the mirror pair) the squared modulus of the
    conjugate pair is `P(Y) := (a² + (Y - y_k)²)(a² + (Y + y_k)²) = (a² + y_k² + S)² - 4y_k²S`
    with `S = Y²`, a convex parabola in `S` with vertex `S* = y_k² - a²`.
  All groups are non-decreasing in `S` past their vertex, and the origin and real groups are
  strictly increasing for `Y > 0`. If every non-real group had `P(S_+) > P(S_-)` with
  `S_± = (y ± δ)²`, the two products could not be equal. So some non-real group has
  `P(S_+) <= P(S_-)` with `S_+ > S_-`, which by symmetry of the parabola forces
  `S_+ + S_- <= 2S*` (or `S_+ < S*`, which is stronger), i.e.
  `y² + δ² <= y_k² - a² <= Δ²`. So `y² <= Δ² - δ²`. Contradiction. QED.

Iterating `N` times with `δ² = 2t/N` contracts `Δ²` by `2t` in total. With `Δ = 1` and
`t >= 1/2` the final strip is `sqrt(max(1 - 2t, 0)) = 0`: **every approximant
`G_N(z) := ∫_0^∞ Φ(u) cosh(u sqrt(2t/N))^N cos(zu) du` has only real zeros**, for every
`N >= 1`. This is exactly the triage's "functions whose cosine transforms have only real
zeros".

The same lemma with `Δ = 0` is the heat-flow monotonicity (real zeros at `t_0` imply real
zeros at every `t >= t_0`). That corollary is what the foundations memo needs to define
`Lambda` as a genuine threshold; it comes for free but is NOT part of this node.

### 2.3 Why not `1 - eps D^2` (footgun, recorded)

`(1 + t u²/N)^N Φ` on the kernel side is `(1 - (t/N) D²)^N` on the function side, and
`1 - εD²` = `(1 - √ε D)(1 + √ε D)` preserves any horizontal strip by the Gauss-Lucas
imaginary-part argument. But it does not contract: for `p = (z - iΔ)³(z + iΔ)³`, `p''` also
vanishes at `±iΔ`, so `p - εp''` still has zeros on `|Im z| = Δ`. Contraction only appears in
the `N → ∞` limit with an uncontrolled `o(1)`, which would need quantitative root-continuity.
The shift average `T_δ` contracts exactly at every finite step (`p = z² + Δ²` gives
`T_δ p = z² + Δ² - δ²`; the triple-zero example gives `T_δ p(±iΔ) = δ³[(2Δ-δ)³ - (2Δ+δ)³] ≠ 0`).

### 2.4 Fact (III): the class, the products, and closure

The discrete-step lemma needs `|f(w+iδ)| / |f(w-iδ)|` as a product over zeros, i.e. a
Hadamard-type factorization. For EVEN real entire `f` of order `< 2` this is the easy genus:
`Σ |z_k|^{-2} < ∞` over the zeros, so the paired product `∏_k (1 - z²/z_k²)` (one factor per
`±z_k` pair, or equivalently a genus-0 product in the variable `z²`) converges locally
uniformly with no exponential convergence factors, and

```
f(z) = c · z^{2m} · ∏_k (1 - z²/z_k²),   c ∈ ℝ \ {0}.
```

Evenness kills the linear exponent (`e^{az}` even forces `a = 0`), so no separate reality
argument for the exponent is needed. Everything the lemma touches is then a modulus of a
finite or absolutely convergent product of the factor groups in section 2.2.

Growth class: for every `N`, `t` and `z = x + iy`,
`|G_N(z)| <= ∫_0^∞ |Φ(u)| e^{tu²} e^{|y| u} du <= exp(C_t (1 + |y|) log(2 + |y|))` using
`abs_Φ_le` and `cosh(δu)^N <= e^{Nδ²u²/2} = e^{tu²}` (from `cosh x <= e^{x²/2}`). So `G_N`
and `H_t` are of order 1, uniformly in `N`; the factorization theorem is invoked with any
fixed exponent `ρ ∈ (1, 2)`, say `ρ = 3/2`.

Convergence: `cosh(u sqrt(2t/N))^N → e^{tu²}` pointwise with the domination above, so by
dominated convergence `G_N → H_t` uniformly on every closed ball (the majorant is
`integrableOn_exp_quad_mul_exp_neg_exp t (11 + R)` up to the constant `ΦBoundConst`).

Closure (Hurwitz, maximum-modulus form): if `G_N → H_t` locally uniformly, each `G_N` is
zero-free on the open set `U = {Im z ≠ 0}`, and `H_t ≢ 0`, then `H_t` is zero-free on `U`.
Proof: at a putative zero `w ∈ U` pick a closed disk in `U` on whose boundary circle
`|H_t| >= m > 0` (zeros of `H_t ≢ 0` are isolated); for large `N`, `|G_N| >= m/2` on the
circle, so by the maximum principle applied to `1/G_N` on the disk
(`Complex.norm_le_of_forall_mem_frontier_norm_le`) `|G_N(w)| >= m/2`, contradicting
`G_N(w) → H_t(w) = 0`. No argument principle or Rouche is needed.

`H_t ≢ 0` and `G_N ≢ 0`: if either transform vanished identically then its (continuous,
integrable, even) kernel would vanish a.e. by Fourier uniqueness (`Continuous.fourier_inversion`
or the `Integrable` variant), so `Φ = 0` a.e., so `H_0 ≡ 0`, contradicting section 2.1.

### 2.5 Citations

* N. G. de Bruijn, *The roots of trigonometric integrals*, Duke Math. J. 17 (1950) 197-226.
  The `t >= 1/2` theorem is cited as Theorem 13 by the roadmap and the foundations memo;
  the strip-contraction mechanism (zeros in `|Im z| <= Δ` are pulled to the real axis by
  `e^{λu²}` once `λ >= Δ²/2`) is de Bruijn's. The implementer must confirm the theorem
  numbering against the Duke paper before quoting it in a docstring; this memo does not.
* H. Ki, Y.-O. Kim, J. Lee, *On the de Bruijn-Newman constant*, Adv. Math. 222 (2009)
  281-306, section 2: modern statement of de Bruijn's theorem, and the sharpening
  `Lambda < 1/2` (OUT OF SCOPE here).
* Polymath15, *Effective approximation of heat flow evolution of the Riemann xi function, and
  a new upper bound for the de Bruijn-Newman constant*, arXiv:1904.12438, section 1: the
  statement that the zeros of `H_t` lie in `|Im z| <= sqrt(max(1 - 2t, 0))`.
* B. Rodgers, T. Tao, *The de Bruijn-Newman constant is non-negative*, Forum Math. Pi 8
  (2020) e6: `Lambda >= 0` (OUT OF SCOPE; not used).
* G. Pólya, *Über trigonometrische Integrale mit nur reellen Nullstellen*, J. reine angew.
  Math. 158 (1927) 6-18: universal factors; the classical background for section 2.2, not
  a dependency of the proof as designed.
* Zero-dynamics form of the contraction (`d(y_max²)/dt <= -2` under the backward heat
  flow): T. Tao, *Heat flow and zeroes of polynomials* (blog, 2017) and Csordas-Smith-Varga,
  Constr. Approx. 10 (1994). Recorded for orientation; the design uses the static discrete
  step of section 2.2 instead, precisely to avoid root-continuity and ODE machinery.

---

## 3. What exists

### 3.1 Mathlib at the pinned rev `de5ce8a9` (grep of the built copy at `examples/li_positivity/lean/.lake/packages/mathlib`)

Present and load-bearing:

| Need | Mathlib name (verified by grep) |
|---|---|
| Euler-product nonvanishing | `riemannZeta_ne_zero_of_one_lt_re` (`NumberTheory/LSeries/Dirichlet.lean:328`); also `riemannZeta_ne_zero_of_one_le_re` |
| Dirichlet series | `zeta_eq_tsum_one_div_nat_cpow` |
| Gamma integral and nonvanishing | `Complex.Gamma_eq_integral`, `GammaIntegral`, `Complex.Gamma_ne_zero_of_re_pos`, `Complex.Gamma_add_one` |
| Change of variables `x = e^{4u}` | `integral_comp_exp_Ioi` (`IntegralEqImproper.lean:1163`), `integral_comp_rpow_Ioi_of_pos` |
| Sum/integral interchange | `MeasureTheory.integral_tsum`, `hasSum_integral_of_dominated_convergence` |
| Dominated convergence | `MeasureTheory.tendsto_integral_of_dominated_convergence` |
| Differentiation under the integral | `hasDerivAt_integral_of_dominated_loc_of_deriv_le` (already used by `hasDerivAt_H`) |
| Locally uniform limits are holomorphic | `TendstoLocallyUniformlyOn.differentiableOn`, `.deriv` (`Analysis/Complex/LocallyUniformLimit.lean`) |
| Maximum modulus (for Hurwitz) | `Complex.norm_le_of_forall_mem_frontier_norm_le` (`AbsMax.lean:405`) |
| Identity theorem | `AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero` and the `Meromorphic/IsolatedZeros.lean` API |
| Jensen / zero counting | `AnalyticOnNhd.sum_divisor_le` (`JensenFormula.lean:391`), `MeromorphicOn.circleAverage_log_norm` |
| Divisors of entire functions | `MeromorphicOn.divisor`, `Function.locallyFinsuppWithin` (`Meromorphic/Divisor.lean`) |
| Local factorization | `MeromorphicOn.extract_zeros_poles` (`CanonicalDecomposition.lean`) |
| Infinite products, locally uniform | `HasProdLocallyUniformlyOn`, `MultipliableLocallyUniformlyOn`, `hasProdLocallyUniformlyOn_one_add`, `multipliableUniformlyOn_nat_one_add` (`Normed/Module/MultipliableUniformlyOn.lean`) |
| Log-derivative of products | `logDeriv_tprod_eq_tsum` (`LogDerivUniformlyOn.lean`), `Meromorphic/LogDeriv.lean` |
| Borel-Caratheodory | `Analysis/Complex/BorelCaratheodory.lean` |
| Primitives on ℂ (log of a zero-free entire function) | `Analysis/Complex/HasPrimitives.lean` |
| Removable singularities | `Analysis/Complex/RemovableSingularity.lean` |
| Fourier uniqueness | `Continuous.fourier_inversion` / `MeasureTheory.Integrable.fourier_inversion` |
| Gaussian transform (not needed on this route, noted) | `fourierIntegral_gaussian` |

Absent (grep returns nothing, excluding Hurwitz-zeta hits):

* Hurwitz's theorem on zeros of locally uniform limits; Rouche; the argument principle.
* Hadamard / Weierstrass factorization of entire functions of finite order; the minimum
  modulus lemma; "order of growth" as a concept.
* Laguerre-Pólya class, Hermite-Biehler, Pólya universal factors, any "Fourier transform with
  only real zeros" API.
* Continuity of polynomial roots in the coefficients (not needed on this route).

Watch item: `Mathlib/Analysis/Complex/ValueDistribution/` (Kebekus, 2026) is the upstream
program most likely to supply a Hadamard factorization. Before starting L3 (section 4),
re-grep a current Mathlib for `Hadamard` / `Weierstrass` products; if it has landed, the
island's Mathlib pin would have to move together with `li_positivity` and LiCriterion, which
is a lead decision.

### 3.2 The `dbn` island

`DBNDefs.lean` (30 theorems, axiom-clean) supplies exactly the entry hypotheses listed in
section 1 and nothing about zeros. `AxiomGuardDBN.lean` is the CI guard and must be
extended with every new theorem. The island is not built in any `~/arda-*` worktree
(checked: no `examples/dbn/lean/.lake` anywhere), but see section 0 item 1.

`DBNFlowNoGo.lean` in the sibling `arda-wall-route-c-debruijn` is abstract wall no-go material
and is not reused.

---

## 4. Obligations, with line estimates

All new files live in `examples/dbn/lean/`, import `DBNDefs`, and are added to
`lakefile.toml` `defaultTargets` and to `AxiomGuardDBN.lean`. Every header states
`conjecture1_proved = False` and that nothing in the file proves RH. Comments must write
"no `sorry`" rather than the bare word.

| # | Obligation | Output (island vocabulary) | Lines |
|---|---|---|---|
| L0 | Island bring-up (compute only) | `lake build` green, `AxiomGuardDBN` clean | 0 |
| L1a | Two-sided fold: `H 0 z = (1/2) ∫_ℝ Φ(u) e^{izu} du`; Schwarz reflection `conj (H t z) = H t (conj z)` | `DBNStrip.lean` | 200 |
| L1b | Termwise Gamma integral of `a_n` on `Im z < -1` (substitution `x = πn²e^{4u}`, `Complex.Gamma_add_one` twice) | `DBNStrip.lean` | 300 |
| L1c | Tonelli bound `Σ_n ∫ abs (a_n) e^{yu} <= C_y Σ n^{-(1+y)/2}` and Fubini; half-plane identity `H 0 z = (1/16) s(s-1) π^{-s/2} Γ(s/2) ζ(s)` for `Im z < -1` | `DBNStrip.lean` | 350 |
| L1d | **`H0_zero_strip : ∀ z, H 0 z = 0 → z.im ^ 2 <= 1`** and `H0_ne_zero : ∃ z, H 0 z ≠ 0` | `DBNStrip.lean` | 100 |
| L2a | Approximants `G t N z := ∫_0^∞ Φ(u) cosh(u √(2t/N))^N cos(zu) du`; integrable, entire, even, real on ℝ; growth bound uniform in `N` | `DBNHeatApprox.lean` | 350 |
| L2b | Shift identity `∫_0^∞ F cosh(δu) cos(zu) = (1/2)(g(z+iδ) + g(z-iδ))` for even real integrable `F` with superexponential decay; iterate to `G t N = T_δ^N (H 0)` | `DBNHeatApprox.lean` | 200 |
| L2c | `cosh x <= exp (x²/2)`; `cosh(u√(2t/N))^N → e^{tu²}`; `G t N → H t` uniformly on closed balls (dominated convergence) | `DBNHeatApprox.lean` | 300 |
| L2d | `G t N ≢ 0`, `H t ≢ 0` via Fourier uniqueness from `H0_ne_zero` | `DBNHeatApprox.lean` | 200 |
| L2e | Hurwitz (maximum-modulus form) for locally uniform limits zero-free on an open set | `DBNHurwitz.lean` | 250 |
| L3a | Zero counting from growth: `n(r) <= C r^{ρ'}` via `AnalyticOnNhd.sum_divisor_le`; `Σ abs (z_k)^{-2} < ∞`; enumeration of the divisor of an entire function as a sequence with multiplicity, closed under `±` and `conj` | `DBNHadamard.lean` | 450 |
| L3b | Even canonical product `∏ (1 - z²/z_k²)`: locally uniform convergence (`hasProdLocallyUniformlyOn_one_add`), entire, zero set and multiplicities equal the divisor | `DBNHadamard.lean` | 350 |
| L3c | Quotient `f / P` entire and zero-free (removable singularities / divisor arithmetic); `= exp h` with `h` entire (`HasPrimitives`) | `DBNHadamard.lean` | 250 |
| L3d | Minimum-modulus lemma for the paired product on a sequence of circles `r_j → ∞` avoiding the zeros: `log abs (P z) >= -r_j^{ρ'}` (the hard classical step; genus 0 in `z²` keeps it to Titchmarsh 8.71 difficulty) | `DBNHadamard.lean` | 600 |
| L3e | `Re h <= C r^{ρ'}` on those circles, Borel-Caratheodory, Cauchy estimates: `h` is a polynomial of degree `<= 1`; evenness forces degree 0. **`hadamard_even : f = c * z^{2m} * ∏ (1 - z²/z_k²)`** for even real entire `f` of order `< 2` | `DBNHadamard.lean` | 300 |
| L4 | **Discrete step lemma** (section 2.2) on the class of L3e: zeros of `T_δ f` in `abs (im) <= sqrt (max (Δ² - δ²) 0)`; the parabola-in-`S` inequality for one factor group; product-over-groups bookkeeping | `DBNStep.lean` | 500 |
| L5 | Induction on `N`: zeros of `G t N` in `abs (im) <= sqrt (max (1 - 2t) 0)`; Hurwitz to `H t`; restate as the registry shape | `DBNDeBruijn.lean` | 300 |
| L6 | Extend `AxiomGuardDBN.lean`; docstrings; the free corollary `real_zeros_mono : (∀ z, H t₀ z = 0 → z.im = 0) → t₀ <= t → ∀ z, H t z = 0 → z.im = 0` (NOT required for the node, but it is what a later `Lambda` node needs) | guard + `DBNDeBruijn.lean` | 100 |

**Total: about 4500 lines** (range 3500-6000 depending mostly on L3d and the divisor
enumeration in L3a). Roughly: strip input L1 ~950, approximants and closure L2 ~1300,
factorization L3 ~1950, step lemma L4 ~500, assembly L5-L6 ~400. Matches the roadmap's
"3000-6000 (given as 4000)" and its 1-3 month window; L3 alone is 4-6 weeks of one careful
session-stream and is the item to start first because everything downstream is blocked on it.

Parallelizable now (independent of L3): L1 (needs only DBNDefs and Mathlib), L2a-L2e.
L4 can be developed against an abstract structure `EvenHadamardData f` (zeros sequence,
product identity, growth) and only wired to L3e at the end, so L3 and L4 can also run in
parallel.

Lean footguns anticipated (from the island and the sibling islands): `rw` on definitions
with inline `match` fails, use the `_eq` lemmas; `Ioi` integrals of `ofReal` need
`integral_ofReal`; the `ℕ+` indexing in `Φ` means every `tsum` manipulation goes through
`summable_thetaTerm_pnat` / `thetaMoment_eq_two_mul_pnat`; the `HIntegrand` cast pattern
`((x : ℝ) : ℂ)` must be kept exactly or `push_cast; ring` stops closing goals.

---

## 5. Compute plan

One `lake build` per island at a time; the orchestrator serialises. No job here starts a
second build.

| Job | Inputs | Command (from `examples/dbn/lean`) | Wall-clock, cores | Emits | Composes into |
|---|---|---|---|---|---|
| J0 island bring-up | `examples/li_positivity/lean/.lake/packages` (built; manifest revs identical, section 8) | `mkdir -p .lake && cp -Rc ../../li_positivity/lean/.lake/packages .lake/packages && lake build` then `lake env lean AxiomGuardDBN.lean \| tee axioms.out; ! grep -q sorryAx axioms.out` | 5-15 min, 32 cores (only `DBNDefs` + guard compile; if lake decides to refetch, expect the 16 min Mathlib build instead) | built island, `axioms.out` | precondition of every other job |
| J1 strip input | J0 | `lake build DBNStrip` | 3-8 min per iteration | `.olean` + `#print axioms DBN.H0_zero_strip` line | fact (I); registry node `RH_dbn_H0_zero_strip` (section 6) |
| J2 approximants + Hurwitz | J0 | `lake build DBNHeatApprox DBNHurwitz` | 3-8 min per iteration | oleans + guard lines | fact (III) |
| J3 factorization | J0 | `lake build DBNHadamard` | 5-15 min per iteration (heaviest file) | `hadamard_even` guard line | fact (II) precondition |
| J4 step lemma | J0 (+ J3 at wiring time) | `lake build DBNStep` | 3-8 min | `step_lemma` guard line | fact (II) |
| J5 assembly | J1-J4 | `lake build DBNDeBruijn && lake env lean AxiomGuardDBN.lean` | 5 min | `#print axioms DBN.debruijn_real_zeros` = `[propext, Classical.choice, Quot.sound]` | the node's statement, verbatim shape |
| J6 numerical plausibility (optional, cheap, proves nothing) | none | mpmath script: zeros of `G_{1/2,N}` for `N <= 8` on `abs z <= 40`, and `H_0` nonvanishing on a grid with `Im z < -1` | 2-5 min, 1 core | a text log in `docs/` | no certificate role; a sanity check on section 2.1 normalization and 2.2 direction |

Certificate shape: there is no numeric certificate on this route; each job's artifact is a
compiled Lean theorem plus its `#print axioms` line in `axioms.out`. The node's proof
artifact is the single theorem `DBN.debruijn_real_zeros` whose statement matches the
generated `Statements/RH_dbn_debruijn_real_zeros.lean` exactly; the lead records the attempt
and runs `mission verify` / `grant`.

---

## 6. Registry decisions (for the lead; this memo runs no registry writes)

1. **Drop the `depends_on` edge `RH_dbn_debruijn_real_zeros -> RH_dbn_H0_eq_xi`.** The
   statement mentions only `DBN.H`, and the proof designed here consumes only the
   absolutely-convergent half-plane (section 2.1), not the representation theorem. Keeping the
   edge would registry-block C3 on C2 for no mathematical reason.
2. **Add a lemma node `RH_dbn_H0_zero_strip`** with statement
   `∀ z : ℂ, DBN.H 0 z = 0 → z.im ^ 2 ≤ 1` (kind `lemma`, `depends_on = []`), and make C3
   depend on it. It is provable now from `DBNDefs` plus Mathlib (obligation L1, ~950 lines,
   a genuine one-to-two-session item) and is the clean seam between the zeta side and the
   heat-flow side. It is NOT a wall statement and says nothing about zeros inside the strip.
3. Optionally add an infrastructure node for `hadamard_even` (L3e) so that the multi-week
   item has its own audit trail; the lead's call.
4. `promote_to_open` on C3 waits for the lead's `mission audit` (blind readback) as usual.
5. `Lambda` remains undefined in the island and the registry (foundations memo section 5).
   L6's monotonicity corollary is the up-set half of what its definition needs; Newman's
   lower bound is still absent and is a different node.

---

## 7. What the node would and would not establish; trust seam

Would establish, axiom-clean: for every real `t >= 1/2`, every complex zero of `H_t` is
real. Together with the L6 corollary: the set `{t | all zeros of H_t real}` is a non-empty
up-set containing `[1/2, ∞)`.

Would NOT establish: anything about `H_0` (i.e. about RH); C2 (`H_0 = xi/8`); C4
(`RH ↔ real zeros of H_0`); the definition or any value of `Lambda`; Ki-Kim-Lee's
`Lambda < 1/2`; Rodgers-Tao's `Lambda >= 0`; Newman's `Lambda > -∞`. Proving this node moves
no wall and leaves `RiemannHypothesis` exactly as open as before. `conjecture1_proved = False`.

Trust seam after J5: the final theorem carries no hypotheses. The mathematical inputs
consumed from Mathlib are the Euler product (`riemannZeta_ne_zero_of_one_lt_re`), Gamma
nonvanishing, Jensen's formula, Borel-Caratheodory, the maximum principle, Fourier inversion
and the locally-uniform-limit API; all are theorems at the pin, none are axioms. The only
registry seam is the new node `RH_dbn_H0_zero_strip` until L1 lands, after which the C3 proof
is self-contained on the island. If C2 lands first, the seam can be discharged from `xi`
instead (section 2.1, last paragraph), but nothing here depends on that.

---

## 8. Checks actually run (2026-09-22, worktree `arda-goal-weil`, branch `mm/gauss-window`)

* Node and statement read: `missions/rh/nodes/RH_dbn_debruijn_real_zeros.toml` (draft,
  edge to `RH_dbn_H0_eq_xi`), `missions/rh/lean/Statements/RH_dbn_debruijn_real_zeros.lean`
  (shape as quoted in section 1). `mission status rh` lists the node as
  `(milestone, draft) -> RH_dbn_H0_eq_xi`; `attempts.jsonl` has zero entries for it.
* Island read: `examples/dbn/lean/DBNDefs.lean` (30 theorems, names in section 1),
  `AxiomGuardDBN.lean`, `lakefile.toml` (toolchain `leanprover/lean4:v4.34.0-rc1`,
  LiCriterion rev `35df682f`).
* Manifest comparison: `diff` of `(name, rev)` over all packages in
  `examples/dbn/lean/lake-manifest.json` vs `examples/li_positivity/lean/lake-manifest.json`
  is empty (Mathlib `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11`, LiCriterion
  `35df682f3b709ffe5fbcfdd452dfa964bd622b87`, batteries, aesop, Qq, proofwidgets,
  importGraph, LeanSearchClient, plausible, Cli all identical).
  `examples/li_positivity/lean/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean`
  exists; `.../packages/LiCriterion/.lake/build/lib/lean/Lc` exists; `packages` is 14 GB.
  No `examples/dbn/lean/.lake` exists in any of the `~/arda-*` worktrees. 32 cores.
* Mathlib greps at the pin: every name in the section 3.1 table was found by `grep -rn`;
  every item in the "absent" list returned nothing (Hurwitz hits are all Hurwitz-zeta).
* Hand checks of the discrete step lemma: `p = z² + Δ²` gives `T_δ p = z² + Δ² - δ²`;
  `p = z(z² + Δ²)` gives `T_δ p = z(z² + Δ² - 3δ²)` (real zero attracts, still within the
  bound); `p = (z² + Δ²)³` has `T_δ p(iΔ) = δ³[(2Δ-δ)³ - (2Δ+δ)³] ≠ 0` while
  `p - εp''` vanishes at `iΔ` (section 2.3). The parabola argument in section 2.2 was
  checked on the vertex/symmetry cases separately.
* Hand check of the section 2.1 normalization: the termwise transform sums to `ξ(s)/8` at
  `s = 1/2 + iz/2`, consistent with the C2 statement `H 0 z = (1/8) riemannXi (1/2 + I z/2)`.
* Not run: any `lake build` (house rule: the orchestrator serialises per island, and J0 was
  not requested); any registry write; any numerics (J6 is optional and was not executed).
