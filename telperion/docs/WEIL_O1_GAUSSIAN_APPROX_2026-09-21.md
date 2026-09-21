# Weil converse, obligation O1' (GaussianApprox): DISCHARGED (2026-09-21)

Status: `RvMBridge8.gaussian_approx : RvMBridge6.GaussianApprox` is kernel-checked on the
rvm_bridge island (Lean v4.33.0-rc2, Mathlib via the Zeta23 pin) with axioms exactly
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`, no named sub-obligations left.
By `RvMBridge6.gaussianTransfer_of_approx`, `RvMBridge6.GaussianTransfer` (O1) is therefore
also unconditional (probe `probe_gaussianTransfer`, same axiom list).

This is pure Fourier analysis about test functions. Nothing about zeta, zeros or RH is proved
here. conjecture1_proved = False. The Weil converse carried O2 when this memo was started (O2 was discharged the same day in E6Bridge7; see the final section) (GaussianDominance).

## Files

- `telperion/examples/rvm_bridge/lean/E6Bridge8.lean` (namespace `RvMBridge8`, `import E6Bridge6`).
- `telperion/examples/rvm_bridge/lean/Probes/E6Bridge8_probe.lean` (axiom audit + two probes).
- This memo.

Not touched: `lakefile.toml`, `AxiomGuardRvMBridge.lean`, E6Bridge5/6/7. The integrator wires
`E6Bridge8` as a `lean_lib` in `defaultTargets` and adds the guard lines below. For the probe run
I emitted the olean by hand (`lake env lean -o .lake/build/lib/lean/E6Bridge8.olean ...`); a
`lake build` after wiring reproduces it.

## The obligation (E6Bridge6, verbatim)

```lean
def GaussianApprox : Prop :=
  ∀ (c lam : ℝ), 0 < lam → ∃ g : ℕ → (ℝ → ℂ), (∀ n, IsWeilTest (g n)) ∧
    (∃ C : ℝ, ∀ n (z : ℂ), |z.im| ≤ 1 / 2 →
      ‖hermitianTransform (g n) z‖ ≤ C / (1 + Complex.normSq z)) ∧
    (∀ z : ℂ, |z.im| ≤ 1 / 2 →
      Tendsto (fun n => hermitianTransform (g n) z) atTop (𝓝 (gaussTest c lam z)))
```

## The witness and the proof

Put b := 1/(4 lam) (`gaussB`), S := (pi/b)^(1/2), K := (2 lam i S)^(-1) (`gaussK`) and

    phi(u) := K u exp(-b u^2 - i c u)                         (`gaussPhi`)
    h(z)   := (z - c) exp(-lam (z - c)^2)                     (`gaussHalf`)
    g_n(u) := phi(u) * chi(u/(n+1))                           (`gaussTests`)

with chi = `bump`, the `ContDiffBump (0:ℝ)` with rIn = 1, rOut = 2 (so chi(u/(n+1)) = 1 for
|u| <= n+1 and = 0 for |u| >= 2(n+1); the n+1 avoids u/0 = 0 at n = 0, which would make g_0 = phi
non-compactly supported).

1. Transform identity, every z (no strip): `paperFT_gaussPhi : paperFT (gaussPhi c lam) z =
   gaussHalf c lam z`. One integration by parts (`integral_mul_deriv_eq_deriv_mul_of_integrable`
   with u = exp(i w x), v = exp(-b x^2)) against Mathlib's `fourierIntegral_gaussian` gives
   `integral_mul_cexp_gaussian_fourier`: ∫ x e^{-b x^2} e^{i w x} = (i w/(2b)) S e^{-w^2/(4b)}.
   Integrability of x e^{-b x^2 + c x} for complex c: `integrable_mul_cexp_quadratic`, from the
   majorant lemma below with |x| <= e^{|x|}.
2. Gaussian shape: `gaussTest_eq_half_mul_conj : gaussTest c lam z = h z * conj (h (conj z))`
   (re-proof of the blind auditor's Audit6_GaussShape inside the library).
3. `isWeilTest_gaussTests`: smooth product (ofRealCLM.contDiff for the cast, ContDiffBump.contDiff)
   times a compactly supported factor (`HasCompactSupport.intro` on [-2(n+1), 2(n+1)]).
4. Pointwise limit on the strip, `paperFT_gaussTests_tendsto`: dominated convergence with
   majorant ‖K‖ |u| e^{-b u^2 + |u|/2} (`norm_cexp_I_mul_le`: ‖e^{i z u}‖ <= e^{|u|/2} for
   |Im z| <= 1/2; `cutoff_eq_one` makes the integrand eventually constant in n).
5. Uniform bound, `exists_paperFT_gaussTests_bound`: ∃ M >= 0, ∀ n z in the strip,
   ‖paperFT (g n) z‖ <= 2M/(1+‖z‖). Two ingredients:
   - trivial bound M0 = ∫ ‖K‖ |u| e^{-b u^2 + |u|/2} (`norm_paperFT_gaussTests_le`);
   - one integration by parts in u, `I_mul_paperFT_eq : I z paperFT g z = -∫ g' e^{i z u}` for any
     compactly supported g with continuous derivative, then ‖z‖ ‖paperFT (g n) z‖ <= M1 :=
     ∫ derivMajorant (`norm_mul_paperFT_gaussTests_le`), where g_n' = phi' chi_n + phi chi'(u/(n+1))/(n+1)
     is bounded by ‖K‖ e^{-b u^2}(1 + 2b u^2 + |c||u|) + ‖K‖ |u| e^{-b u^2} B with B a global bound on
     |chi'| (`exists_deriv_bump_bound`, from Continuous.bounded_above_of_compact_support).
   Then min(M0, M1/‖z‖) <= 2 max(M0,M1)/(1+‖z‖) by the cases ‖z‖ <= 1, ‖z‖ > 1.
6. Assembly (`gaussian_approx`): C := 4M^2; ‖hermitianTransform (g n) z‖ = ‖paperFT (g n) z‖
   ‖paperFT (g n) (conj z)‖ <= (2M/(1+‖z‖))^2 <= 4M^2/(1+normSq z) since (1+‖z‖)^2 >= 1+‖z‖^2 =
   1 + normSq z; the limit is Tendsto.mul with conj continuous, rewritten by step 2.

Majorant toolkit (section A): `integrable_exp_quadratic` (e^{-b x^2 + k x}),
`integrable_exp_quadratic_abs` (e^{-b x^2 + k |x|}), `abs_pow_le_exp` (|x|^m <= e^{m|x|}),
`integrable_abs_pow_mul_exp_quadratic_abs` (|x|^m e^{-b x^2 + k|x|}).

## Probe output (lake env lean Probes/E6Bridge8_probe.lean)

```
'RvMBridge8.gaussian_approx' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge8.integral_mul_cexp_gaussian_fourier' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge8.paperFT_gaussPhi' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge8.gaussTest_eq_half_mul_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge8.isWeilTest_gaussTests' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge8.paperFT_gaussTests_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge8.I_mul_paperFT_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge8.norm_mul_paperFT_gaussTests_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge8.norm_paperFT_gaussTests_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge8.exists_paperFT_gaussTests_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge8.integrable_mul_cexp_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge8.integrable_abs_pow_mul_exp_quadratic_abs' depends on axioms: [propext, Classical.choice, Quot.sound]
'probe_gaussianTransfer' depends on axioms: [propext, Classical.choice, Quot.sound]
'probe_gaussTests_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`probe_gaussianTransfer : RvMBridge6.GaussianTransfer` is the composition with E6Bridge6's Tannery
transfer; `probe_gaussTests_ne_zero` shows the witness family is not the zero function.

## Lines for AxiomGuardRvMBridge (integrator)

```lean
#print axioms RvMBridge8.gaussian_approx
#print axioms RvMBridge8.paperFT_gaussPhi
#print axioms RvMBridge8.integral_mul_cexp_gaussian_fourier
#print axioms RvMBridge8.paperFT_gaussTests_tendsto
#print axioms RvMBridge8.exists_paperFT_gaussTests_bound
#print axioms RvMBridge8.I_mul_paperFT_eq
```

## Pin footguns hit (v4.33.0-rc2 Mathlib)

- A bare `π` in a theorem statement is auto-bound as an implicit variable; write `Real.pi`.
- `le_or_lt` is gone (use `le_or_gt`); `push_neg` is deprecated (use `not_le.mp` or `push Not`).
- `fun_prop` has no ContDiff lemma for `Complex.ofReal`; use `Complex.ofRealCLM.contDiff`.
- `ContDiff.continuous_deriv` wants `1 <= n` in `WithTop ℕ∞`; go through `contDiff_infty.mp h 1`.
- After `field_simp` a cpow factor is reordered inside the base, so `ring` cannot close it:
  `generalize` the cpow term first.
- Elaborating `cutoff 0 1 = 1` against `cutoff_eq_one` without explicit `(n := 0) (u := 1)`
  hits the heartbeat limit (the ContDiffBump coercion is a large term).

## Composition with E6Bridge7 (added after the lead reported O2 closed)

`Probes/E6Bridge8_converse_probe.lean` (imports E6Bridge7 and E6Bridge8) plugs
`gaussian_approx` into `RvMBridge7.weil_positivity_implies_rh_of_approx`:

```
'probe_weil_positivity_implies_rh' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge7.weil_positivity_implies_rh_of_approx' depends on axioms: [propext, Classical.choice, Quot.sound]
```

so the kernel accepts `(∀ g, IsWeilTest g → 0 ≤ (weilForm (autocorr g)).re) → RiemannHypothesis`
with no hypotheses beyond Weil positivity itself. This is an implication, not RH:
conjecture1_proved = False. The E6Bridge7 olean used was the one present in the build directory at
the time of the run (checked newer than its source); the integrator's `lake build` re-verifies it.
