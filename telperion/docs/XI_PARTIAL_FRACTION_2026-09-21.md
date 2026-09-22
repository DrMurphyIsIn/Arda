# The derivative partial fraction of ξ'/ξ without the Hadamard product (E6Bridge18, 2026-09-21)

Status. `E6Bridge18.lean` (namespace `RvMBridge18`, imports E6Bridge6) fixes the interface the
Taylor agent builds on, proves the summability half outright, proves the constant-free skeleton
(log-growth Liouville, real-axis decay of the sum, assembly), and carries the two analytic inputs
as named `def : Prop` obligations. Axioms of everything proved: exactly
`[propext, Classical.choice, Quot.sound]`; no `sorry`. conjecture1_proved = False.

## Which function: ξ (entire), not Λ

`xi s := s (s - 1)/2 * completedRiemannZeta₀ s + 1/2` (Zeta23.WeilEF.xi's exact formula, restated
because that Zeta23 module's olean is not built on this island). `xi_differentiable` (entire),
`xi_eq : xi s = s (s-1)/2 * completedRiemannZeta s` off {0, 1}, and
`logDeriv_xi_eq : logDeriv xi s = 1/s + 1/(s-1) + logDeriv completedRiemannZeta s`
(off {0,1}, Λ(s) ≠ 0). So the Taylor agent recovers the Λ form by subtracting the two pole terms,
and the ζ form via Zeta23.WeilEF.logDeriv_completedZeta. No pole terms appear in the interface.

## The interface (names fixed; do not rename)

```lean
def XiLogDerivDerivEq : Prop :=
  ∀ s : ℂ, ¬ IsNontrivialZero s →
    deriv (logDeriv xi) s = -∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2

theorem summable_inv_sub_sq (s : ℂ) (_hs : ¬ IsNontrivialZero s) :
    Summable (fun ρ : ℂ => (WeilExplicit.zeroMult ρ : ℂ) / (s - ρ) ^ 2)        -- PROVED

theorem xi_logDeriv_deriv_eq_of (h1 : XiDiffRegular) (h2 : XiLogDerivDerivDecay) :
    XiLogDerivDerivEq                                                           -- PROVED modulo h1, h2
```

Deviation from the requested statement: the identity is delivered as `xi_logDeriv_deriv_eq_of`
(modulo the two obligations) and as the Prop `XiLogDerivDerivEq` of exactly the requested shape,
for the Taylor agent to consume as a hypothesis. `summable_inv_sub_sq` needs no hypothesis on s
(kept for interface fidelity; at a zero the offending term is Lean's junk 0).

## The constant-free argument, piece by piece

Let `xiDiffReg s := deriv (logDeriv xi) s + Σ' m(ρ)/(s-ρ)²`.

1. **Summability (PROVED)**, `summable_inv_sub_sq`. For a nontrivial zero ρ with |Im ρ - Im s| ≥ 1,
   `|1/(s-ρ)²| ≤ (13/4 + 2 (Im s)²)/(1 + |γ_ρ|²)` (norm_polTerm_le_majorant), the local-count
   majorant of E6Bridge6 (`summable_mult_div_one_add_normSq`, Zeta23 `zero_sum_inv_sq`); the finitely
   many zeros within ordinate distance 1 (`zetaSeam.finite_window`) enter the majorant `polBound` as
   an indicator.
2. **Entire extension with log growth (OBLIGATION `XiDiffRegular`)**:
   `∃ G, Differentiable ℂ G ∧ (∀ s, ¬IsNontrivialZero s → G s = xiDiffReg s) ∧ ∃ C, ∀ s, ‖G s‖ ≤ C (1 + log (2 + ‖s‖))`.
   Content: at a zero ρ₀ of order m, logDeriv ξ = m/(s-ρ₀) + analytic, so deriv (logDeriv ξ) =
   -m/(s-ρ₀)² + analytic, cancelled by the m/(s-ρ₀)² term of the sum (removable singularity), and
   the growth bound from Landau's local partial fraction (Zeta23 `WeilEF.zeta_logDeriv_partial_fraction`,
   |t| ≥ 6, |Re s - 2| ≤ 3/2) with Cauchy's estimate on a disc of radius 1/2, the local count for the
   far sum, Dirichlet series + Stirling for Re s ≥ 2, the functional equation ξ(1-s) = ξ(s) on the
   left, and continuity on the compact remainder.
3. **Liouville with logarithmic growth (PROVED)**, `eq_const_of_log_growth`: an entire G with
   ‖G z‖ ≤ C(1 + log(2 + ‖z‖)) is constant. Cauchy's estimate (`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`)
   on the circle of radius R about z gives ‖G'(z)‖ ≤ C(1 + log(2 + ‖z‖ + R))/R → 0
   (`Real.tendsto_pow_log_div_mul_add_atTop`), so G' = 0 and `is_const_of_deriv_eq_zero`. The probe
   checks the lemma is not vacuous (the identity function admits no such bound).
4. **The constant is 0.** Sum half (PROVED), `tsum_inv_sub_sq_tendsto`: Σ' m(ρ)/(σ-ρ)² → 0 as
   σ → +∞ along the real axis, by Tannery against the majorant (5/4) m/(1 + |γ|²) valid for σ ≥ 2.
   Log-derivative half (OBLIGATION `XiLogDerivDerivDecay`):
   `Tendsto (fun σ : ℝ => deriv (logDeriv xi) σ) atTop (𝓝 0)`. Content: deriv (logDeriv ξ)(σ) =
   -1/σ² - 1/(σ-1)² + (1/4) ψ'(σ/2) + (ζ'/ζ)'(σ), with ψ' = O(1/σ) and the Dirichlet series of
   (ζ'/ζ)' = O(2^{-σ}). Both are Mathlib-adjacent (LSeries derivatives, digamma asymptotics) but
   not on this island yet.
5. **Assembly (PROVED)**, `xi_logDeriv_deriv_eq_of`: G constant, G(σ) = xiDiffReg(σ) → 0 for
   σ ≥ 1 (no nontrivial zero has Re ≥ 1), so G ≡ 0 and the identity holds off the zeros.

## Where it stopped and why

The two obligations are exactly the analytic inputs the plan lists as steps 2 to 3 (removable
singularity at the zeros and the growth bound) and the ξ half of step 5. Both need infrastructure
absent from the island: the order-m local form of logDeriv near a zero (Mathlib's
`analyticOrderAt_eq_natCast` gives ξ = (s-ρ₀)^m u with u(ρ₀) ≠ 0; the logDeriv consequence on a
punctured neighbourhood and the removable-singularity gluing are not written), the Cauchy-estimate
transfer of Landau's O(log t) remainder to its derivative, and the LSeries/digamma asymptotics for
the decay. None was started; nothing is claimed beyond the kernel output below.

## Files

- `telperion/examples/rvm_bridge/lean/E6Bridge18.lean`
- `telperion/examples/rvm_bridge/lean/Probes/E6Bridge18_probe.lean` (all green)
- `telperion/examples/rvm_bridge/lean/Probes/E6Bridge18_obligation_probe.lean` (expected FAILS)
- this memo

lakefile.toml, AxiomGuardRvMBridge.lean and existing modules untouched; olean emitted by hand for
the probe run. Guard lines for the integrator:

```lean
#print axioms RvMBridge18.summable_inv_sub_sq
#print axioms RvMBridge18.xi_logDeriv_deriv_eq_of
#print axioms RvMBridge18.eq_const_of_log_growth
#print axioms RvMBridge18.tsum_inv_sub_sq_tendsto
#print axioms RvMBridge18.logDeriv_xi_eq
```

## Probe output (lake env lean Probes/E6Bridge18_probe.lean)

```
'RvMBridge18.summable_inv_sub_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge18.xi_logDeriv_deriv_eq_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge18.eq_const_of_log_growth' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge18.tsum_inv_sub_sq_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge18.logDeriv_xi_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge18.xi_differentiable' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge18.xi_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'probe_id_not_log_bounded' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Obligation probe output (lake env lean Probes/E6Bridge18_obligation_probe.lean), all EXPECTED

```
Probes/E6Bridge18_obligation_probe.lean:11:2: error: unsolved goals            (XiDiffRegular, G = 0 witness)
Probes/E6Bridge18_obligation_probe.lean:17:2: error: Tactic `aesop` failed, made no progress  (XiDiffRegular by aesop)
Probes/E6Bridge18_obligation_probe.lean:20:34: error: unsolved goals           (XiLogDerivDerivDecay by simp)
Probes/E6Bridge18_obligation_probe.lean:25:29: error: unsolved goals           (not XiDiffRegular)
Probes/E6Bridge18_obligation_probe.lean:31:2: error: `simp` made no progress   (not XiLogDerivDerivDecay)
Probes/E6Bridge18_obligation_probe.lean:37:2: error: `simp` made no progress   (identity from summability alone)
```
