# Stage S2 notes: the pole-free parametrisation (2026-10-11)

Branch `mm/arch-s2`, island `telperion/examples/rvm_bridge/lean`.
Module `ArchS2_QTrick.lean` (354 lines) and guard `ArchS2_Guard.lean` (41 lines).
`conjecture1_proved = False`.  Nothing here is RH progress.

## What S2 proves

S2 is Connes-Consani Lemma 3.3 and Remark 6.12, written in the island's own variable and Fourier convention.
Every statement uses the project definitions: `WeilExplicit.IsWeilTest`, `autocorr`, `archSide`, `weilKernel`, Zeta23's `paperFT`, and `RvMBridge31.hsq` and `mass`.
Nothing is redefined.

### The convention, checked in Lean

The project transform is Zeta23's `paperFT f z = ∫ f(u) e^{izu} du`.
So the pole condition `paperFT g (I/2) = 0` is the integral of g against e^{-u/2}.
This is the lemma `paperFT_I_half`.

The operator that annihilates this functional is Q h = h' - h/2.
Integration by parts gives `paperFT (Q h) z = -(I z + 1/2) · paperFT h z` for every complex z.
At z = I/2 the factor is I·(I/2) + 1/2 = 0.
CC write g = h/2 - h', which is the same operator up to sign.
The squared-modulus identities do not see the sign.

### Theorems

All of them live in namespace `ArchS2`.

**(a) The parametrisation.**
```lean
theorem poleFree_iff_exists_lift {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) :
    paperFT g (I / 2) = 0 ↔
      ∃ h : ℝ → ℂ, IsWeilTest h ∧ tsupport h ⊆ Set.Icc (-L) L ∧
        ∀ u, g u = deriv h u - h u / 2
```
The witness is explicit:
```lean
def qLift (g : ℝ → ℂ) (L : ℝ) (u : ℝ) : ℂ :=
  Complex.exp ((u : ℂ) / 2) * ∫ t in (-L)..u, g t * Complex.exp (-(t : ℂ) / 2)
```
(the integral is packaged as `tiltPrim g L u`).
It is smooth by the fundamental theorem of calculus and `contDiff_infty_iff_deriv`.
It vanishes for u ≤ -L with no hypothesis.
It vanishes for u ≥ L exactly because the full integral of g e^{-t/2} is the pole functional.
No sign condition on L is needed, since the case split covers L < 0.

Supporting statements:
* `lift_unique`: two smooth compactly supported lifts of the same g are equal.  The proof shows (h₁ - h₂)e^{-u/2} has zero derivative, so it is constant, and it vanishes outside a compact set.
* `isWeilTest_of_lift`, `tsupport_lift_subset`, `tsupport_of_lift`: Q h is a test function, and its closed support lies inside that of h.
* `poleFree_of_lift`: Q h is pole-free.  This direction needs no support hypothesis on g.

**(b) Transform identities.**
```lean
theorem paperFT_lift {g h : ℝ → ℂ} (hh : IsWeilTest h) (hgh : ∀ u, g u = deriv h u - h u / 2)
    (z : ℂ) : paperFT g z = -(I * z + 1 / 2) * paperFT h z
theorem hsq_lift ... (r : ℝ) : hsq g r = (r ^ 2 + 1 / 4) * hsq h r
theorem integral_lift ... : ∫ u : ℝ, g u = -(1 / 2) * ∫ u : ℝ, h u
theorem paperFT_zero_lift_iff ... : paperFT g 0 = 0 ↔ ∫ u : ℝ, h u = 0
```
Here `hsq g r = ‖paperFT g r‖²`.
CC's second condition ĝ(0) = 0 (CC Thm 1) is therefore ∫ h = 0, the constant direction ξ₀.

**(c) One condition kills both pole terms.**
```lean
theorem poles_vanish_of_lift ... :
    weilKernel (autocorr g) 0 = 0 ∧ weilKernel (autocorr g) 1 = 0
theorem archSide_autocorr_lift ... :
    archSide (autocorr g) = -(mass g : ℂ) * (Real.log Real.pi : ℂ)
      + (1 / (2 * (Real.pi : ℂ))) * ((∫ r : ℝ, (r ^ 2 + 1 / 4) * hsq h r * psiR r : ℝ) : ℂ)
theorem poleFree_window_lift (hg : IsWeilTest g) (hsupp : tsupport g ⊆ Set.Icc (-L) L)
    (h0 : paperFT g (I / 2) = 0) :
    weilKernel (autocorr g) 0 = 0 ∧ weilKernel (autocorr g) 1 = 0 ∧
      archSide (autocorr g) = ... (the same formula with h = qLift g L)
```
The vanishing of the poles reuses `RvMBridge31.poles_vanish`.
That lemma already shows ĝ(i/2) = 0 kills both h(i/2) = ĝ(i/2)·conj ĝ(-i/2) and h(-i/2) = ĝ(-i/2)·conj ĝ(i/2).
S2 transports it to the lift form.

### Axioms

`lake env lean ArchS2_Guard.lean` prints `[propext, Classical.choice, Quot.sound]` for all 38 declarations.
There is no `sorry` and no `axiom`.
`lake build ArchS2_QTrick` succeeds (3752 jobs) with zero warnings in the module.

## Open items

* **Mass identity not proved.**  The relation ‖g‖² = ‖h'‖² + ¼‖h‖² is not proved.  It follows from (b) by Plancherel, or directly because the cross term Re∫h'·conj h vanishes.  S4 may want it to turn ‖g‖² into an h-norm.
* **Lift as a linear map not built.**  The lift is not packaged as a linear map or as an L² isometry onto a weighted space.  Only the pointwise statements exist.
* **Wiring left to the coordinator.**  `AxiomGuardRvMBridge.lean` and `defaultTargets` are untouched, per the conventions.
* **CC's sign not stated.**  The blueprint writes CC's variant as g = h/2 - h'.  It is not stated separately, because it is the lift of -h.

## Lean footguns met

* **`fun_prop` and `ofReal`.**  `fun_prop` cannot prove `ContDiff ℝ ⊤ (fun u : ℝ => (u : ℂ))` on this pin.  Use `Complex.ofRealCLM.contDiff` and then `.div_const`, `.neg` and `.cexp`.
* **`convert ... using 1` on `HasDerivAt` products.**  It produced junk goals about instances.  `HasDerivAt.congr_deriv` is reliable.
* **Pointwise operations after `.sub` and `.neg`.**  These derivative combinators leave `(h₁ - h₂) u` and `(-fun y => ↑y) u`.  Run `simp only [Pi.sub_apply, Pi.neg_apply]` before `linear_combination` or `ring`.
* **`HasCompactSupport.div_const` does not exist.**  Get compactness of Q h from `tsupport_lift_subset` and `IsCompact.of_isClosed_subset` instead.
* **Simp lemma name.**  The name is `image_eq_zero_of_notMem_tsupport` (`notMem`, not `nmem`).
