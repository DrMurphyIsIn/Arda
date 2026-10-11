# Stage S1 notes: the exact u-space Weil identity (2026-10-11)

Branch `mm/arch-s1`, island `telperion/examples/rvm_bridge/lean` (Lean v4.33.0-rc2).
Plan: `ARCHIMEDEAN_CONCEPTUAL_BLUEPRINT_2026-10-11.md`, section 4, row S1.
`conjecture1_proved = False`. Nothing here is RH progress. No registry nodes were touched.

## What is proved

All theorems below are kernel-checked with axioms exactly `[propext, Classical.choice, Quot.sound]`
(`lake build ArchS1_Identity && lake env lean ArchS1_Guard.lean`). No `sorry`, no `axiom`.

Files:

| file | lines | content |
|---|---|---|
| `ArchS1_Kernel.lean` | 144 | the kernel k, its closed form, truncations, CC's tau |
| `ArchS1_Identity.lean` | 331 | truncated identity, the N → ∞ limit, the identity and corollaries |
| `ArchS1_Guard.lean` | 23 | `#print axioms` for 13 top-level theorems |

Build time: about 20 s per module on the loaded machine (17 s Kernel, 18 s Identity).

### The kernel (`ArchS1_Kernel`)

```lean
def kb (n : ℕ) : ℝ := 2 * n + 1 / 2
def kTrunc (N : ℕ) (u : ℝ) : ℝ := ∑ n ∈ Finset.range N, expK (kb n) u     -- expK b u = exp (-b|u|)
def archK (u : ℝ) : ℝ := Real.exp (3 / 2 * |u|) / (Real.exp (2 * |u|) - 1)

theorem hasSum_archK {u : ℝ} (hu : u ≠ 0) : HasSum (fun n : ℕ => expK (kb n) u) (archK u)
theorem tsum_expK_kb (u : ℝ) : ∑' n : ℕ, expK (kb n) u = archK u          -- every u, incl. u = 0 (both 0)
theorem tendsto_kTrunc {u : ℝ} (hu : u ≠ 0) : Tendsto (fun N => kTrunc N u) atTop (𝓝 (archK u))
theorem archK_eq_tau {u : ℝ} (hu : 0 < u) :
    archK u = Real.exp (u / 2) / 2 * (1 / (1 + Real.exp u) + 1 / (Real.exp u - 1))   -- CC (39)
```

`kb 0 = 1/2` is the a-term of the digamma series and `kb (n+1) = bN n` (E6Bridge32's 2n + 5/2).

### The identity (`ArchS1_Identity`, namespace `ArchS1`)

```lean
theorem archSide_autocorr_dirichlet_identity {g : ℝ → ℂ} (hg : IsWeilTest g) :
    (archSide (autocorr g)).re
      = (weilKernel (autocorr g) 0 + weilKernel (autocorr g) 1).re
        + (psiR 0 - Real.log Real.pi) * mass g
        + (1 / 2) * ∫ z : ℝ × ℝ, ‖g z.1 - g z.2‖ ^ 2 * archK (z.1 - z.2) ∂(volume.prod volume)

theorem integrable_dirichlet {g : ℝ → ℂ} (hg : IsWeilTest g) :
    Integrable (fun z : ℝ × ℝ => ‖g z.1 - g z.2‖ ^ 2 * archK (z.1 - z.2)) (volume.prod volume)
```

Corollaries and companions:

* `arch_integral_dirichlet`: the archimedean integral alone,
  (1/2π)∫ hsq g · psiR = psiR 0 · mass g + ½∫∫|g(v) − g(w)|² k(v − w).
* `archSide_autocorr_dirichlet_identity'`: the same identity with the poles written as
  2 Re(ĝ(−i/2) · conj ĝ(i/2)) and the constant as `(Complex.digamma (1/4)).re - log π`.
* `re_poles_eq`: Re(h(i/2) + h(−i/2)) = 2 Re(paperFT g (−I/2) · conj (paperFT g (I/2))).
* `archSide_autocorr_dirichlet_identity_poleFree`: with `paperFT g (I / 2) = 0` the pole term is gone.
* `weilForm_autocorr_dirichlet_identity`: with tsupport g ⊆ [−L, L] and 2L ≤ log 2, the same right
  side equals `(weilForm (autocorr g)).re` (via E6Bridge31 `weilForm_autocorr_eq_archSide`).
* `psiR_zero : psiR 0 = (Complex.digamma (1 / 4)).re`; numerically psiR 0 − log π = −5.37218.
* `truncated_identity`: (1/2π)∫ hsq · phiN N = cN N · mass g + ½∫∫|Δg|² k_{N+1}, every N.

The hypothesis is only `IsWeilTest g`. No support bound is needed: the proof picks some L from
compact support internally, because E6Bridge33's `Eb_eq_half` is stated with one.

## How the proof goes

1. Truncation. E6Bridge32's `integral_hsq_mul_phiN` and E6Bridge33's `Eb_eq_half`, applied to each
   b ∈ {1/2, 5/2, …, 2N + 1/2}, give `truncated_identity`. Its constant is E6Bridge34's `cN N`.
2. r side. phiN N → psiR pointwise because Zeta23's `re_digamma_vertical` series is exact.
   Dominated convergence uses the bound hsq · (|psiR| + |γ + 4|), from −γ − 4 ≤ phiN N ≤ psiR.
3. Constant. cN N = phiN N 0, so cN N → psiR 0.
4. u side. |Δg|² k_{N+1} increases to |Δg|² k at every point; on the diagonal both are 0.
   The lintegral monotone convergence theorem, bounded by the r-side limit, gives integrability.
   Mathlib's `integral_tendsto_of_tendsto_of_monotone` then identifies the limit.

The 1/(2|u|) singularity of k needs no local Lipschitz estimate. Integrability follows from
the finiteness of the r side.

## What is open

* Nothing inside S1's scope.
* Not done, and not asked for: an explicit quantitative bound such as
  ∫∫|Δg|² k ≤ C(L)·‖g'‖². It is not needed by S1; S3/S4 may want one.
* Not wired: `defaultTargets` and `AxiomGuardRvMBridge.lean` are untouched per the conventions.
  The coordinator should add `ArchS1_Kernel` and `ArchS1_Identity` at merge.
  `ArchS1_Guard` is registered as its own `lean_lib` (like `KWin2_GuardHeavy`).

## Lean footguns hit

* `Real.exp_lt_one_of_neg` and `Real.exp_lt_one` do not exist at this Mathlib pin. Use
  `(Real.exp_lt_exp.mpr h).trans_eq Real.exp_zero`.
* `convert h using 1` on a `HasSum` goal descended into the `AddCommMonoid` instance and produced
  an instance-equality goal. Rewrite the target value with an explicit `have hv : archK u = …` instead.
* `field_simp` on a goal with both `x * x` and `exp (2u)` leaves junk. Rewrite exp(2u) = x·x,
  then `generalize Real.exp u = x` before `field_simp`.
* `field_simp` on `2 b / (b^2 + 0^2) = 2 / b` leaves `b^2 = b^2 + 0^2`; it needs a trailing `ring`.
* `HasCompactSupport g` unfolds to `IsCompact (tsupport g)`. `IsCompact.isBounded hg.2` with
  `subset_closedBall 0` and `Real.closedBall_eq_Icc` gives the Icc bound.
