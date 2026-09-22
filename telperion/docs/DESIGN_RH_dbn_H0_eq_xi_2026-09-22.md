# Design memo: `RH_dbn_H0_eq_xi` (Route C / C2), H_0(z) = (1/8) xi(1/2 + iz/2)

*Authored 2026-09-22 on worktree `arda-goal-weil`, branch `mm/gauss-window`, for the lead's
scheduling queue. This is a DESIGN MEMO, not a proof. Nothing was proved in Lean while writing it;
no `lake build` was started; no registry mutation was made. Every numerical claim below was
re-run in this session (section 4) rather than copied from the 2026-09-17 foundations note.*

**`conjecture1_proved = False`. Nothing in this memo, in the `dbn` island, or in the node it
designs proves the Riemann Hypothesis, bounds the de Bruijn-Newman constant, or says anything
about the zeros of `H_t`. The node is a representation theorem (an identity between two entire
functions). Its consumer `RH_dbn_rh_iff_H0_real_zeros` (C4) is wall-grade and out of scope; this
node is not RH-equivalent.**

---

## 0. Triage verdict (unchanged from the queue entry, with one correction)

Nothing is granted or grantable today. The only Lean content for the node is the generated stub
`missions/rh/lean/Statements/RH_dbn_H0_eq_xi.lean` (`by sorry`, by design), the node has no
linked artifact, `attempts.jsonl` has no entry for it, and the island itself says twice (the
`DBNDefs` header and the `AxiomGuardDBN` header) that `H_0 = xi/8` is NOT proved there. The
mathematics is classical (Titchmarsh 10.1, Polymath15 eq. (3)) and the registered normalisation
is correct (re-verified, section 4). What is missing is a formalisation project of roughly
950-1550 new Lean lines across several sessions, on an island that is not built anywhere yet.

**Correction to the queue triage.** The triage lists "a twice-differentiated tsum under an
integral" and "dominated convergence for differentiating the theta sum under the integral" as
new work. Neither is needed. The island's `hasDerivAt_thetaMoment` already differentiates the
theta series termwise (with the uniform bound on a preconnected neighbourhood), so
`g'' - g = 8 Phi` is a *pointwise* identity in `u` obtained by applying that lemma twice, and
the two integrations by parts are performed on `g` as a function, never term by term. No
interchange of `tsum` and `integral` occurs anywhere on the route below. This removes the single
most unpleasant obligation from the estimate; it does not change the order of magnitude.

---

## 1. The exact theorem, in the island's vocabulary

Registered statement (generated, sha `000e927caef49a0a`):

```lean
theorem dbn_H0_eq_xi (z : ℂ) :
    DBN.H 0 z = (1 / 8 : ℂ) * LiCriterion.riemannXi (1 / 2 + Complex.I * z / 2)
```

with, verbatim from `examples/dbn/lean/DBNDefs.lean` and the pinned upstream
`Lc/LiCriterion/Basic.lean:1236` (rev `35df682f`):

```lean
DBN.Φ (u : ℝ) : ℝ :=
  ∑' n : ℕ+, (2 * Real.pi ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u)
      - 3 * Real.pi * (n : ℝ) ^ 2 * Real.exp (5 * u)) * Real.exp (-Real.pi * (n : ℝ) ^ 2 * Real.exp (4 * u))
DBN.HIntegrand (t : ℝ) (z : ℂ) (u : ℝ) : ℂ := ↑(Real.exp (t * u ^ 2)) * ↑(Φ u) * Complex.cos (z * u)
DBN.H (t : ℝ) (z : ℂ) : ℂ := ∫ u in Set.Ioi (0 : ℝ), HIntegrand t z u
LiCriterion.riemannXi (s : ℂ) : ℂ := (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s + (1 / 2 : ℂ)
```

Three facts about the statement that the proof must respect:

1. `riemannXi` is built on `completedRiemannZeta₀` (Mathlib's entire `Λ₀`), not on
   `completedRiemannZeta`. So the statement needs **no** `s ≠ 0, 1` hypothesis and is the
   *entire* xi. The check at `z = i`: `1/2 + i·i/2 = 0`, `riemannXi 0 = 1/2`, so the statement
   asserts `H 0 i = 1/16`, i.e. `∫_0^∞ Φ(u) cosh(u) du = 1/16`. Verified numerically (section 4).
2. `H 0 z` is a Bochner integral over `Ioi 0` of a `ℂ`-valued integrand with `exp (0 * u^2) = 1`;
   the even-extension form `(1/2)∫_ℝ` is not used and must not be introduced.
3. `z` is an arbitrary complex number, so every boundary-term limit and every integrability
   claim below must be proved for complex `z` (the island already does this for the integrand:
   `integrableOn_HIntegrand`, via `norm_cos_le_exp_norm`).

Unfolding the Mathlib side once (all `rfl` or one-line):

```
completedRiemannZeta₀ s = completedHurwitzZetaEven₀ 0 s            -- RiemannZeta.lean:64, rfl
                        = (hurwitzEvenFEPair 0).Λ₀ (s / 2) / 2      -- HurwitzZetaEven.lean:302-303
(hurwitzEvenFEPair 0).Λ₀ = mellin (hurwitzEvenFEPair 0).f_modif     -- AbstractFuncEq.lean:376
mellin f s = ∫ t in Ioi 0, (t : ℂ) ^ (s - 1) • f t                  -- MellinTransform.lean:91
```

and for `P := hurwitzEvenFEPair 0` (HurwitzZetaEven.lean:254-277): `P.f = ofReal ∘ evenKernel 0`,
`P.k = 1/2`, `P.ε = 1`, `P.f₀ = 1` (the `if a = 0` branch), `P.g₀ = 1`, and

```
P.f_modif = (Ioi 1).indicator (fun x ↦ P.f x - 1) + (Ioo 0 1).indicator (fun x ↦ P.f x - ↑(x ^ (-(1/2))))
```

(AbstractFuncEq.lean:247-249, with `P.ε * ↑(x ^ (-P.k)) • P.g₀ = ↑(x ^ (-1/2))`).
`evenKernel 0 x = ∑_{n ∈ ℤ} exp(-π n² x)` for `x > 0` by `hasSum_int_evenKernel 0 hx`
(HurwitzZetaEven.lean:163), which is exactly the island's `thetaMoment 0 u` at `x = e^{4u}`.

---

## 2. The mathematical route (Route C2, hand-checked)

Notation: `θ(x) = ∑_{n∈ℤ} e^{-πn²x}`, `ψ(x) = ∑_{n≥1} e^{-πn²x} = (θ(x) - 1)/2`,
`x = e^{4u}`, `g(u) := e^{u} ψ(e^{4u})`.

**(1) Riemann's symmetric integral for `Λ₀`.** For every `s ∈ ℂ` (no strip restriction, because
`Λ₀` is the Mellin transform of the *modified* kernel, which decays at both ends):

```
Λ₀(s) := completedRiemannZeta₀ s = ∫_1^∞ ψ(x) (x^{s/2 - 1} + x^{(1-s)/2 - 1}) dx.
```

Derivation from Mathlib's definition: split `mellin f_modif (s/2)` over `Ioi 1` and `Ioo 0 1`
(the point `1` is null and `f_modif 1 = 0` anyway); on `Ioi 1` the integrand is
`x^{s/2-1}(θ(x) - 1) = 2 x^{s/2-1} ψ(x)`; on `Ioo 0 1` substitute `x ↦ 1/y` and use the theta
functional equation `θ(1/y) = y^{1/2} θ(y)` (this is `P.h_feq`, i.e.
`evenKernel_functional_equation`), which turns `θ(1/y) - y^{1/2}` into `y^{1/2}(θ(y) - 1)` and
the measure `x^{s/2-1} dx` into `y^{-s/2-1} dy`; the piece becomes `2 ∫_1^∞ y^{-s/2-1/2} ψ(y) dy`.
Divide by 2. This unfolding is **not in Mathlib** (Mathlib never expands `f_modif` into two
`Ioi 1` integrals; `WeakFEPair.hasMellin` only identifies `Λ s` with `mellin (f - f₀)` for
`re s > k`) and is the first real chunk.

**(2) xi is already entire.** `riemannXi s = (1/2) s (s-1) Λ₀(s) + 1/2` for all `s`; nothing to
do. (The island's `riemannXi_eq_completedRiemannZeta` is the bridge to the *textbook* xi and is
not needed on this route.)

**(3) Change of variables `x = e^{4u}`.** At `s = 1/2 + iz/2`: `s/2 - 1 = -3/4 + iz/4`,
`(1-s)/2 - 1 = -3/4 - iz/4`, so `x^{s/2-1} + x^{(1-s)/2-1} = 2 x^{-3/4} cos((z/4) log x)`, and
`s(s-1) = -(z² + 1)/4`. With `dx = 4 e^{4u} du`, `x^{-3/4} = e^{-3u}`, `log x = 4u`:

```
Λ₀(1/2 + iz/2) = ∫_0^∞ ψ(e^{4u}) · 2 e^{-3u} cos(zu) · 4 e^{4u} du = 8 ∫_0^∞ g(u) cos(zu) du,
xi(1/2 + iz/2) = 1/2 - (z² + 1) ∫_0^∞ g(u) cos(zu) du.
```

Mathlib tool: `integral_comp_exp_Ioi (g) (a) : ∫ x in Ioi a, exp x • g (exp x) = ∫ y in Ioi (exp a), g y`
(IntegralEqImproper.lean:1163), applied with `a = 0` after the rescaling `u ↦ 4u`
(`integral_comp_mul_left_Ioi` or the `smul`-measure lemma), plus the cpow identity
`((e^{4u} : ℝ) : ℂ) ^ w = exp (w * 4u)` from `cpow_def_of_ne_zero` and `Complex.ofReal_exp`.

**(4) Two integrations by parts on `Ioi 0`.** Using `z² cos(zu) = -(d/du)² cos(zu)`:

```
z² ∫ g cos = -[g · (cos)'] + ∫ g' (cos)' = [g' cos]_0^∞ ... = -g'(0) - ∫ g'' cos,
```

where the first boundary term vanishes at `0` because `(cos(zu))' = -z sin(zu)` is `0` at `u = 0`
and at `∞` because `g` decays super-exponentially against `|sin(zu)| ≤ e^{|z|u}`; the second
gives `-g'(0)` at `0` (since `cos 0 = 1`) and `0` at `∞`. Hence

```
(z² + 1) ∫_0^∞ g cos(zu) du = -g'(0) - ∫_0^∞ (g'' - g)(u) cos(zu) du.
```

Mathlib tool: `integral_Ioi_mul_deriv_eq_deriv_mul` (IntegralEqImproper.lean:1385), stated for
`u v : ℝ → A` with `[NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]`, so `A = ℂ` is fine;
it needs `HasDerivAt` on `Ioi 0`, `IntegrableOn (u * v')` and `(u' * v)`, and the two limits
`Tendsto (u * v) (𝓝[>] 0) (𝓝 a')`, `Tendsto (u * v) atTop (𝓝 b')`.

**(5) The kernel identity `g'' - g = 8 Φ`.** With `x = e^{4u}`, `dx/du = 4x`:

```
g'  = e^{u}(ψ + 4xψ'),
g'' = e^{u}(ψ + 24xψ' + 16x²ψ''),
g'' - g = e^{u}(24 x ψ'(x) + 16 x² ψ''(x)) = ∑_{n≥1} (16π² n⁴ e^{9u} - 24π n² e^{5u}) e^{-πn² e^{4u}} = 8 Φ(u),
```

using `ψ' = -π ∑ n² e^{-πn²x}`, `ψ'' = π² ∑ n⁴ e^{-πn²x}`. On the island this is pointwise
algebra from `hasDerivAt_thetaMoment 0` and `hasDerivAt_thetaMoment 1` plus `Φ_eq`
(`Φ u = π² e^{9u} θ₂(u) - (3/2) π e^{5u} θ₁(u)`), once `g` is written as
`g u = e^{u} (thetaMoment 0 u - 1) / 2`.

**(6) `g'(0) = -1/2`.** `g'(0) = ψ(1) + 4ψ'(1)`. Differentiating `θ(1/x) = x^{1/2}θ(x)` at
`x = 1` gives `-4ψ'(1) = 1/2 + ψ(1)`. On the island: `thetaMoment_fe_deriv1 0` reads
`-4π θ₁(0) = -2 θ₀(0) + 4π θ₁(0)`, i.e. `θ₁(0) = θ₀(0)/(4π)`, and `g'(0) = (θ₀(0) - 1)/2 - 2π θ₁(0)
= (θ₀(0) - 1)/2 - θ₀(0)/2 = -1/2`.

**Assembly.** `xi(1/2 + iz/2) = 1/2 + g'(0) + ∫ (g'' - g) cos = 1/2 - 1/2 + 8 ∫ Φ cos = 8 H_0(z)`.

Citations: Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., section 10.1 (eq. for
`Ξ(t)` as `4 ∫_1^∞ d/dx[x^{3/2}ψ'(x)] x^{-1/4} cos((t/2) log x) dx`); Polymath15,
arXiv:1904.12438, section 1 eqs. (1)-(3); Rodgers-Tao, Forum Math. Pi 8 (2020) e6, section 1;
Riemann 1859 for the symmetric integral (1); `telperion/docs/DBN_FOUNDATIONS_C2C4_2026-09-17.md`
section 2 for the earlier paper-and-mpmath derivation via Titchmarsh's form (the route here goes
through `Λ₀` directly because that is what the Lean vocabulary exposes).

---

## 3. Inventory: what exists, what does not

### 3.1 Available on the `dbn` island (`DBNDefs.lean`, 569 lines, axiom-clean per the guard)

| lemma | role on the route |
|---|---|
| `thetaMoment k u`, `summable_thetaMoment`, `summable_thetaTerm` | the working series; `thetaMoment 0 u = θ(e^{4u})` |
| `hasDerivAt_thetaMoment k u : HasDerivAt (thetaMoment k) (-4π e^{4u} thetaMoment (k+1) u) u` | steps (5), (6): all derivatives of `g` |
| `continuous_thetaMoment` | continuity of `g`, `g'` at `0⁺` for the boundary limits in (4) |
| `ofReal_thetaMoment_zero : ↑(thetaMoment 0 u) = jacobiTheta₂ 0 (I e^{4u})` | identification with Mathlib's `evenKernel 0` in (1) |
| `thetaMoment_zero_fe`, `thetaMoment_fe_deriv1`, `thetaMoment_fe_deriv2` | (1) (the `Ioo 0 1` half) and (6) |
| `thetaMoment_eq_two_mul_pnat (hk : 0 < k)` | `ℤ`-sum to `ℕ+`-sum; **needs a `k = 0` sibling** (`θ₀ = 1 + 2ψ`) |
| `Φ_eq`, `summable_Φ_term`, `Φ_neg` | (5) |
| `abs_Φ_le`, `ΦBoundConst`, `summable_ΦBoundConst_term` | template for the decay bounds on `g`, `g'`, `g''` |
| `integrableOn_exp_quad_mul_exp_neg_exp a b` | the universal majorant; reused for every integrability obligation |
| `norm_cos_le_exp_norm`, `norm_sin_le_exp_norm` | complex-`z` growth control of the boundary terms |
| `integrableOn_HIntegrand 0 z`, `H_ofReal`, `hasDerivAt_H`, `differentiable_H` | right-hand side; not needed for the identity but useful for the `z = i` sanity lemma |
| `riemannXi_eq_completedRiemannZeta` | not on the route (textbook-xi bridge) |

### 3.2 Available in Mathlib (pin `de5ce8a9`)

| lemma | file:line | role |
|---|---|---|
| `completedRiemannZeta₀`, `completedHurwitzZetaEven₀` | RiemannZeta.lean:64, HurwitzZetaEven.lean:302 | unfolding |
| `hurwitzEvenFEPair 0` fields, `hurwitzEvenFEPair_zero_symm` | HurwitzZetaEven.lean:254-283 | `f₀ = g₀ = ε = 1`, `k = 1/2` |
| `WeakFEPair.Λ₀ = mellin f_modif`, `f_modif` | AbstractFuncEq.lean:376, 247 | unfolding |
| `IsStrongFEPair.hasMellin` + `isStrongFEPair_toStrongFEPair` | AbstractFuncEq.lean:484, 313 | **gives `MellinConvergent P.f_modif s` for every `s`** (the `mellinConvergent` lemma itself is `private`; go through `hasMellin`) |
| `hf_modif_int`, `hf_modif_top`, `hf_modif_FE` | AbstractFuncEq.lean:256, 287, 269 | local integrability, decay, FE of the modified kernel |
| `evenKernel_def`, `hasSum_int_evenKernel`, `evenKernel_functional_equation` | HurwitzZetaEven.lean:77, 163, 132 | `evenKernel 0 = θ` and its FE |
| `integral_comp_exp_Ioi`, `integrableOn_comp_exp_Ioi` | IntegralEqImproper.lean:1163, 1173 | step (3) |
| `integral_comp_rpow_Ioi (hp : p ≠ 0)` | IntegralEqImproper.lean:1131 | step (1), inversion `p = -1` on the `Ioo 0 1` indicator piece |
| `integral_Ioi_mul_deriv_eq_deriv_mul` | IntegralEqImproper.lean:1385 | step (4), twice |
| `integral_Ioi_of_hasDerivAt_of_tendsto` | IntegralEqImproper.lean:787 | alternative single-IBP form |
| `cpow_def_of_ne_zero`, `cpow_add`, `Complex.ofReal_exp` | Pow/Complex.lean:38, 82 | cpow of positive real base as `exp` |
| `HasMellin`, `MellinConvergent`, `hasMellin_add/sub` | MellinTransform.lean:160, 45, 163 | splitting the Mellin integral |

### 3.3 Not in Mathlib, not on the island (the new work)

* **N1.** Riemann's two-`Ioi 1`-integral formula for `(hurwitzEvenFEPair 0).Λ₀`, for all `s`
  (section 2 step (1)). Mathlib stops at `Λ₀ = mellin f_modif`.
* **N2.** The inversion substitution `Ioo 0 1 → Ioi 1` on an indicator integrand. Mathlib has
  `integral_comp_rpow_Ioi` on `Ioi 0` only; the `Ioo 0 1` piece must be carried as
  `(Ioo 0 1).indicator` through the substitution and the indicator re-expressed as
  `(Ioi 1).indicator` on the far side. Mechanical but fiddly.
* **N3.** Decay bounds `|g(u)|, |g'(u)|, |g''(u)| ≤ C e^{c u} exp(-(π/2) e^{4u})` for `u ≥ 0`.
  Only `abs_Φ_le` exists; the proof template transfers (same `n² ≥ 1`, `e^{4u} ≥ 1` trick) but
  each of `θ₀ - 1`, `θ₁`, `θ₂` needs its own bound (or one bound for `thetaMoment k` on `ℕ+`).
* **N4.** The four boundary limits of step (4) (two at `0⁺`, two at `∞`) for complex `z`.
* **N5.** A `k = 0` version of `thetaMoment_eq_two_mul_pnat` (`thetaMoment 0 u = 1 + 2 ∑_{ℕ+}`),
  because the `n = 0` term is `1`, not `0`.

---

## 4. Numerical audit (run 2026-09-22, mpmath, 30 digits; script in the session scratchpad)

| check | result |
|---|---|
| `g'' - g - 8Φ` at `u = 0.05, 0.2, 0.4` | `0, 0, 9.6e-35` |
| `g'(0) + 1/2` | `0` |
| `Λ₀(1/2 + 3i/2) - ∫_1^∞ ψ(x)(x^{s/2-1} + x^{(1-s)/2-1}) dx` | `-4.9e-32` |
| `Λ₀(1/2 + 3i/2) - 8 ∫_0^∞ g(u) cos(3u) du` | `-4.9e-32` |
| `H_0(z) - xi(1/2 + iz/2)/8` at `z = 0, 3, 0.5 + 0.7i` | `0, 6e-33, 6e-33` |
| `∫_0^∞ Φ(u) cosh(u) du - 1/16` (the `z = i`, `xi(0) = 1/2` check) | `0` |

These are audit evidence for the *normalisation of the statement*, not for the proof. The lead's
`mission audit` testimony can cite this table; it is the "independent auditor" input the
WALL_BACKLOG_MAP F1 row asks for before `promote_to_open`.

---

## 5. Named obligations, proposed sub-node decomposition, honest line estimates

Proposed new island modules (all `import DBNDefs`, all added to `AxiomGuardDBN.lean`; suggested
file names, the lead may rename):

| id | module / main lemma (Lean vocabulary) | content | est. lines | needs |
|---|---|---|---|---|
| **A** | `DBNXiRiemann.lean`: `DBN.psi x := ∑' n : ℕ+, exp(-π n² x)`; `evenKernel_zero_eq_thetaMoment`; `completedRiemannZeta₀_eq_integral_psi (s : ℂ) : completedRiemannZeta₀ s = ∫ x in Ioi 1, (psi x : ℂ) * ((x:ℂ)^(s/2-1) + (x:ℂ)^((1-s)/2-1))` | N1, N2, N5; splitting `mellin f_modif`, inversion on `Ioo 0 1`, the FE, integrability of both pieces via `IsStrongFEPair.hasMellin` | 350-500 | Mathlib only + `DBNDefs` |
| **B** | `DBNXiCos.lean`: `DBN.g u := exp u * psi (exp (4*u))`; `g_eq_thetaMoment : g u = exp u * (thetaMoment 0 u - 1) / 2`; `completedRiemannZeta₀_half_add_eq (z : ℂ) : completedRiemannZeta₀ (1/2 + I*z/2) = 8 * ∫ u in Ioi 0, (g u : ℂ) * Complex.cos (z*u)` | step (3): `u ↦ 4u` rescale, `integral_comp_exp_Ioi`, cpow-to-exp, `x^{iz/4} + x^{-iz/4} = 2cos` | 150-250 | A |
| **C** | `DBNGKernel.lean`: `DBN.g' u`, `DBN.g'' u` (closed forms in `thetaMoment 0/1/2`); `hasDerivAt_g`, `hasDerivAt_g'`; `g''_sub_g_eq : g'' u - g u = 8 * Φ u`; `g'_zero : g' 0 = -1/2`; `abs_g_le`, `abs_g'_le`, `abs_g''_le` (u ≥ 0); `integrableOn_g_mul_cos`, `integrableOn_g'_mul_sin`, `integrableOn_g''_mul_cos` | steps (5), (6), N3; decay + integrability against complex `cos(zu)`, `sin(zu)` | 250-400 | `DBNDefs` |
| **D** | `DBNXiIBP.lean`: `integral_g_cos_ibp (z : ℂ) : (z^2 + 1) * ∫ u in Ioi 0, (g u:ℂ) * cos(z*u) = -(g' 0 : ℂ) - ∫ u in Ioi 0, ((g'' u - g u : ℝ) : ℂ) * cos(z*u)` | step (4), N4: two applications of `integral_Ioi_mul_deriv_eq_deriv_mul`, four `Tendsto` side conditions | 200-300 | C |
| **E** | `DBNXi.lean`: `dbn_H0_eq_xi` (the registered statement, verbatim), plus the sanity corollary `H_zero_I : H 0 I = 1/16` | assembly: `H 0 z` with `exp 0 = 1`, `riemannXi` unfold, B + D + C | 50-100 | A-D |

Total: **1000-1550 lines**, 4-6 sessions if A and C run in parallel (they are independent), then
B, then D, then E. The critical path is A → B → E and C → D → E; A and D are the risky items.
Recommended registry shape (lead does `mission add/link`; suggested slugs):
`RH_dbn_xi_riemann_integral` (A), `RH_dbn_xi_cos_integral` (B, deps A),
`RH_dbn_g_kernel_identities` (C), `RH_dbn_g_double_ibp` (D, deps C), and re-point
`RH_dbn_H0_eq_xi.depends_on = [B, D]`. Each is a `lemma`; none is RH-adjacent.

Per-obligation risk notes:

* **A** is the only obligation whose *shape* is uncertain. The clean path is: (i) obtain
  `MellinConvergent P.f_modif (s/2)` from `(isStrongFEPair_toStrongFEPair P).hasMellin (s/2)`
  (`P.toStrongFEPair.f = P.f_modif` is `rfl`); (ii) write `f_modif` as the sum of its two
  indicator pieces and split the Bochner integral with `integral_add` (each piece is the
  restriction of an integrable function to a measurable set, hence integrable); (iii) on
  `Ioi 1`, rewrite `evenKernel 0 x - 1 = 2 psi x` pointwise; (iv) on the `Ioo 0 1` piece apply
  `integral_comp_rpow_Ioi` with `p = -1` and `hf_modif_FE`/`evenKernel_functional_equation`,
  then re-express the transported indicator. If (iv) fights the indicator too hard, the fallback
  is to substitute `x = e^{v}` over all of `Ioi 0` first (`integral_comp_exp_Ioi` with
  `a → -∞` is not available; use `integral_comp_exp` on `ℝ` via `Real.exp` as a measurable
  equivalence, then split at `v = 0` with `integral_Iic_add_Ioi`) and reflect `v ↦ -v` on the
  negative half; that trades indicator gymnastics for one extra `integral_comp_neg`.
* **D**: `integral_Ioi_mul_deriv_eq_deriv_mul` wants `IntegrableOn (u * v')` and
  `IntegrableOn (u' * v)` as *pointwise products of functions*, so C must state its
  integrability lemmas in exactly that `Pi.mul` shape or D must `simpa` them into it. The
  `𝓝[>] 0` limits come from continuity within `Ici 0` (`continuous_thetaMoment` gives full
  continuity, which is stronger than needed). The `atTop` limits: bound
  `‖g(u) · z sin(zu)‖ ≤ C |z| e^{(c+‖z‖)u} exp(-(π/2)e^{4u})` and use the `Tendsto ... atTop (𝓝 0)`
  form of the argument already inside `integrableOn_exp_quad_mul_exp_neg_exp` (extract it as a
  standalone lemma `tendsto_exp_lin_mul_exp_neg_exp`; ~30 lines, shared by all four limits).
* **C**: three decay bounds of identical shape. Write one lemma
  `abs_thetaMoment_pnat_le (k) (hu : 0 ≤ u) : ∑'_{ℕ+} (n²)^k e^{-πn²e^{4u}} ≤ C_k exp(-(π/2)e^{4u})`
  by the `abs_Φ_le` template and derive the three from it; do not prove three copies.

---

## 6. What the node would and would not establish

**Would establish** (once A-E are green and axiom-clean): the identity of two entire functions,
`DBN.H 0 = (1/8) · LiCriterion.riemannXi ∘ (1/2 + I·/2)`, in the pinned vocabulary shared with
the `li_positivity` island. Consequences that then become one-liners: `H 0` is entire (already
known independently via `differentiable_H`), `H 0` is real on the real axis (already
`H_ofReal_im`), zeros of `H 0` correspond bijectively to zeros of `riemannXi` under
`z ↦ 1/2 + iz/2`, and `H 0 i = 1/16`. It unblocks C3 (`RH_dbn_debruijn_real_zeros`, de Bruijn's
`t ≥ 1/2` theorem, which needs `H_0` to be *the* xi only to interpret its conclusion) and
supplies the `t = 0` anchor of C4.

**Would NOT establish**: anything about where the zeros of `H_0` or `H_t` lie; any bound on the
de Bruijn-Newman constant (which is deliberately not even defined on the island before C3);
de Bruijn's theorem; Newman's conjecture / Rodgers-Tao; RH or any RH-equivalent statement. C4
(`RH_dbn_rh_iff_H0_real_zeros`) is a *change of variables applied to RH*; it is wall-grade
(WALL_BACKLOG_MAP F0) and stays out of scope regardless of this node's status.
**`conjecture1_proved = False` before, during, and after this work.**

---

## 7. Compute plan

The island is not built anywhere: no `.lake` under `telperion/examples/dbn` in this worktree or in
any of the `~/arda-*` siblings (the only sibling with extra `dbn` source,
`~/arda-wall-route-c-debruijn`, has `DBNFlowNoGo.lean` but no build). Bootstrap is cheap because
the manifests agree.

**Job 0 -- bootstrap the `dbn` island build (lead/orchestrator schedules; ONE build on the island
at a time).**

* Inputs: `examples/li_positivity/lean/.lake` (14 GB, contains `Mathlib.olean` and
  `Lc/LiCriterion/Basic.olean`, both verified present); `examples/dbn/lean/{lakefile.toml,
  lake-manifest.json, lean-toolchain}`. Manifest check done this session: all 10 packages
  (`mathlib de5ce8a9`, `LiCriterion 35df682f`, `batteries 01bc479e`, `aesop`, `Qq`,
  `proofwidgets`, `importGraph`, `LeanSearchClient`, `plausible`, `Cli`) match rev-for-rev;
  toolchain `leanprover/lean4:v4.34.0-rc1` on both.
* Steps: `cp -Rc examples/li_positivity/lean/.lake examples/dbn/lean/.lake` (APFS reflink,
  seconds, no extra disk); `rm -rf examples/dbn/lean/.lake/build` (drop li_positivity's own
  module oleans so the trace state is clean; the `packages/` builds are what we want);
  `cd examples/dbn/lean && lake build` (compiles `DBNDefs` and `AxiomGuardDBN` only);
  `lake env lean AxiomGuardDBN.lean | tee axioms.out; ! grep -q sorryAx axioms.out`.
* Expected: 3-10 min wall-clock (one 569-line module importing all of Mathlib; single-module
  elaboration is not parallel, so cores beyond ~4 are idle). NOT a 16-minute Mathlib rebuild. If
  `lake build` decides to rebuild Mathlib, stop: the manifest or toolchain drifted; do not let
  it run.
* Certificate emitted: `axioms.out` with every `DBNDefs` theorem at `[propext, Classical.choice,
  Quot.sound]`. This is the island's baseline, and a prerequisite for every job below.

**Jobs A, C (parallel-safe on the mathematics; serialised on the island build).**

* Inputs: Job 0 baseline; `DBNDefs.lean`; this memo section 5.
* Each is a single new module compiled by `lake build DBNXiRiemann` / `lake build DBNGKernel`;
  expected 1-4 min per compile, several compile-edit cycles per session; 1-2 sessions each.
* Certificate: the module plus its `#print axioms` lines appended to `AxiomGuardDBN.lean`, all
  at `[propext, Classical.choice, Quot.sound]`, no `sorry` (CI scan), registered as lemma nodes
  and linked `--kind lean_module --via direct` by the lead.

**Jobs B, D, E (sequential after their inputs).** Same shape; B after A (1 session), D after C
(1-2 sessions), E after B and D (well under a session). E's module contains the registered
statement verbatim so the verify gate's normalised-containment match succeeds.

**Job N -- numerical audit artifact (any time, seconds, 1 core).** Re-run the section 4 script
and file its output with the `mission audit` testimony. It is evidence about the statement's
normalisation, not a certificate, and must not be linked as a proof artifact.

**Composition into the node.** `E.dbn_H0_eq_xi` imports A-D; the registry node's statement
module is matched by the verify gate against `DBNXi.lean`; the lead then `mission link` and
`mission grant`. Sub-nodes A-D become granted lemma nodes on the way; `RH_dbn_debruijn_real_zeros`
and `RH_dbn_rh_iff_H0_real_zeros` keep their existing `depends_on = ["RH_dbn_H0_eq_xi"]`.

**Trust seam after completion.** No hypotheses remain: the statement is unconditional and the
expected axiom closure is `[propext, Classical.choice, Quot.sound]`. What the reader must still
trust is (i) the Mathlib pin `de5ce8a9` (definition of `completedRiemannZeta₀` via the
Hurwitz FE-pair machinery), (ii) the upstream `LiCriterion.riemannXi` definition at `35df682f`
(that it is "the" xi is a *convention*, established by `riemannXi_eq_completedRiemannZeta`
and by `xi(0) = 1/2`), and (iii) the `dbn` island's `Φ`/`H` definitions being the Polymath15
objects (a convention, documented in `DBN_FOUNDATIONS_C2C4_2026-09-17.md` section 1 and
cross-checked numerically in section 4 above). None of these is a mathematical gap.

---

## 8. Blockers to record on the node (for the lead)

1. Island not built anywhere; Job 0 must run before any attempt. Not started here.
2. No proof artifact, no attempt, no readback/audit: `promote_to_open` will refuse (F1 row).
   `mission audit RH_dbn_H0_eq_xi --auditor "<independent>" --text "<cite section 4 table>"`
   first.
3. N1-N5 (section 3.3) are the genuine new infrastructure; A is the only one with shape risk.
4. Roadmap C2 row and ASCENT F6-2 both price this at "months"; with the parallel A/C plan and
   the removed tsum-interchange obligation, 4-6 focused sessions is the honest lower estimate,
   and "months" remains the honest upper one.
5. This node gates C3 (real math, no wall risk) and C4 (wall-grade F0, out of scope). Do not let
   C4's status leak into scheduling decisions about this node in either direction.

`conjecture1_proved = False`. Nothing here proves RH.
