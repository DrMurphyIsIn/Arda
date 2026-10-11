# Stage S3 notes: structural positivity L = W∞ + D ≥ 0 (CC Cor 2.3) (2026-10-11)

Branch `mm/arch-s3`, island `telperion/examples/rvm_bridge/lean` (Lean v4.33.0-rc2).
Plan: `ARCHIMEDEAN_CONCEPTUAL_BLUEPRINT_2026-10-11.md`, section 4, row S3.
`conjecture1_proved = False`. Nothing here is RH progress. No registry nodes were touched.

## 1. The statement, derived before proving

### 1.1 CC's objects (arXiv:2006.13771, sections 1-2)

* CC (48): for ρ ≥ 1, δ(ρ) = 4ρ^{1/2} ∫₀¹ cos(2πρt) cos(2πt) (−log t) dt.
  With ∫₀¹ cos(2πat)(−log t) dt = Si(2πa)/(2πa) this is CC (49).
* CC Prop 2.2(ii): δ(ρ⁻¹) = δ(ρ).  In the additive variable u = log ρ the kernel is the even function
  δ(e^{|u|}).  We take (48) at e^{|u|} ≥ 1 as the definition, so evenness is built in.
* CC Prop 2.2(iii) / Cor 2.3: L(f) = ∫ f(ρ⁻¹)(δ(ρ) − τ(ρ)) d*ρ = Tr(ϑ_m(f) P P̂ P) ≥ 0 for f = g∗g*,
  and equivalently ℓ(t) := 2θ'(t) + δ̂(t) ≥ 0 for all real t (CC (52)).
* In our conventions 2θ'(t) = psiR t − log π (blueprint 2.1), and δ̂(t) = ∫ δ(e^{|u|}) cos(tu) du.

### 1.2 Our statement

For `g` with `IsWeilTest g` (any support), with hsq g r = |paperFT g r|²:

```
archW g := (1/2π) ∫ hsq g r · (psiR r − log π) dr          -- W∞(g∗g*), the archimedean term
Dfun g  := Re ∫ autocorr g u · δ(e^{|u|}) du                -- D(g∗g*) = ⟨g, K_δ g⟩
Lfun g  := archW g + Dfun g
ell r   := psiR r − log π + deltaHat r                      -- CC's 2θ' + δ̂
```

* (S3-a, Fourier form) Lfun g = (1/2π) ∫ hsq g r · ell r dr.
* (S3-b, u-space form, via S1) Lfun g = (psiR 0 − log π)‖g‖² + ½∫∫|g(v) − g(w)|² k(v − w) + Dfun g.
* (S3-c, link to the Weil form) Re archSide(autocorr g) = Re(poles) + archW g; on the pole-free class
  inside the window (2L ≤ log 2) Re weilForm(autocorr g) = archW g.
* (S3-main, CC Cor 2.3) 0 ≤ Lfun g for every IsWeilTest g, by the manifest-positivity identity below.

### 1.3 The manifest-positivity identity (replaces the 2-D HS identity)

The blueprint's M2 is ‖A T_g‖²_HS = W∞ + D with A = (1 − P) u P.  ϑ(g) is diagonal in the Mellin
variable, so the HS norm is the integral over t of |ĝ(t)|² times the Mellin diagonal of A*A:

```
ell t = ∫_{a > 1} |Φ_t(a)|² da/a,      Φ_t(a) = 2 ∫_a^∞ s^{−1/2 + it} cos(2πs) ds.        (★)
```

Φ_t(1/λ)·λ^{it} is exactly A applied to the generalised eigenvector λ^{it} of ϑ (CC (27): u has kernel
2λ^{−1/2}μ^{1/2}cos(2πμ/λ); P = 1_{[1,∞)}).  (★) is the pointwise form of Prop 2.2(iii), and it makes
ell ≥ 0 manifest: it is a squared L²-norm.  Integrating (★) against hsq g gives back the HS identity.

Numerical check of (★) [N-here, mpmath, `ell_norm2.py` in the session scratchpad; NOT certified]:

| t | psiR t − log π + δ̂(t) | ∫₁^∞ \|Φ_t\|² da/a (tail-corrected) |
|---|---|---|
| 0 | 0.0490716 | 0.0490707 |
| 0.5 | 0.0493233 | 0.0493242 |
| 2 | 0.0533443 | 0.0533458 |

Agreement is at the 1e-6 level of the tail correction.  |Φ_t(0⁺)| = 1 (u is unitary).

Also checked [N-here]: (log Ψ)'(½ + it) = psiR t − log π to 15 digits, where
Ψ(z) = 2∫₀^∞ s^{z−1}cos(2πs) ds = Gammaℂ(z)·cos(πz/2) = Gammaℝ(z)/Gammaℝ(1 − z) and |Ψ| = 1 on the line.
So 2θ' is the phase derivative of the unitary u in the Mellin picture, and (★) says
"Hankel diagonal of u = phase derivative + δ̂".

## 2. Milestones

### M1: DONE (commit f1d6cd7ee, `ArchS3_Delta.lean`, 571 lines)

All theorems kernel-checked, axioms exactly `[propext, Classical.choice, Quot.sound]`
(`lake build ArchS3_Delta && lake env lean ArchS3_Guard.lean`, 16 guarded theorems). No `sorry`, no `axiom`.
Build time about 21 s.

```lean
def sincInt (c : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, Real.sinc (c * t)                 -- Si(c)/c
def ccDelta (ρ : ℝ) : ℝ := 4 * √ρ * ∫ t in 0..1, cos(2πρt) * cos(2πt) * (-log t)   -- CC (48)
def deltaK (u : ℝ) : ℝ := 2 * exp(|u|/2) * (sincInt (2π(e^{|u|} + 1)) + sincInt (2π(e^{|u|} - 1)))
def deltaHat (r : ℝ) : ℝ := ∫ u, deltaK u * cos(r u)
def archW g := (1/(2π)) * ∫ r, hsq g r * (psiR r - log π)
def Dfun g  := (∫ u, autocorr g u * deltaK u).re
def Lfun g  := archW g + Dfun g
def ell r   := psiR r - log π + deltaHat r

theorem integral_cos_mul_neg_log (c) : ∫ t in 0..1, cos(c t) * (-log t) = ∫ t in 0..1, sinc(c t)
theorem ccDelta_eq (ρ) : ccDelta ρ = 2 * √ρ * (sincInt (2π(ρ+1)) + sincInt (2π(ρ-1)))     -- CC (49)
theorem deltaK_eq_ccDelta (u) : deltaK u = ccDelta (exp |u|)
lemma   deltaK_zero : deltaK 0 = 2 * (sincInt (4π) + 1)                                    -- CC (50)
lemma   abs_Si_le (hc : 0 ≤ c) : |∫ s in 0..c, sinc s| ≤ 4
theorem abs_deltaK_le (u) : |deltaK u| ≤ 8 * exp(-(1/2)|u|)
lemma   continuous_deltaK, integrable_deltaK, deltaK_neg, continuous_deltaHat, abs_deltaHat_le
theorem pairing_deltaK (hg : IsWeilTest g) :
    ∫ u, autocorr g u * deltaK u = (1/(2π)) * ∫ r, hsq g r * deltaHat r
theorem Lfun_eq_integral_ell (hg) : Lfun g = (1/(2π)) * ∫ r, hsq g r * ell r               -- S3-a
theorem archW_eq_dirichlet (hg) : archW g = (psiR 0 - log π) * mass g + ½ ∫∫ |g v - g w|² archK (v-w)
theorem Lfun_eq_dirichlet (hg) : Lfun g = (psiR 0 - log π) * mass g + ½ ∫∫ |Δg|² archK + Dfun g  -- S3-b
theorem re_archSide_eq_poles_add_archW (hg) : Re archSide (autocorr g) = Re(poles) + archW g     -- S3-c
theorem re_weilForm_eq_archW (hg) (hsupp) (2L ≤ log 2) (paperFT g (I/2) = 0) :
    Re weilForm (autocorr g) = archW g
theorem Lfun_nonneg_of_ell_nonneg (hell : ∀ r, 0 ≤ ell r) (hg) : 0 ≤ Lfun g             -- Cor 2.3 (ii) ⇒ (i)
```

Hypotheses are only `IsWeilTest g`; no support bound is needed except in `re_weilForm_eq_archW`.

### M2: STOPPED by the decision rule (not started in Lean)

M2 is (★) for every t (or its integrated HS form).  It needs three things.

1. **Ψ as an integral.**  Ψ(z) = 2∫₀^∞ s^{z−1}cos(2πs) ds = Gammaℂ(z)cos(πz/2) on 0 < Re z < 1.
   * Mathlib has the algebraic identity `Gammaℝ s / Gammaℝ (1 - s) = Gammaℂ s * cos (π s / 2)` (Deligne.lean).
   * The Mellin transform of cos on the critical strip is ABSENT.  Only `GammaIntegral` (e^{−x}) and
     `integral_cpow_mul_exp_neg_mul_Ioi` (Re r > 0) exist.  Getting to Re r = 0 needs contour rotation or an
     Abel limit of conditionally convergent improper integrals.  Estimate 500-800 lines.
2. **The phase derivative.**  (log Ψ)' = psiR − log π on the line.  It is cheap from the Gammaℝ identity and
   `Complex.digamma`, about 150-250 lines.
3. **The oscillatory identity itself:** ∫₁^∞|Φ_t|² d*a = (log Ψ)'(½+it) + δ̂(t).  This is the analytic heart.
   * CC's own derivation is not rigorous here.  (38) → (39) uses the distributional Fourier transform of −log|t|
     "with this definition of the principal value".  The identification of W_R with ∫f̂·2θ' is (163), quoted
     from Connes-Marcolli [18].
   * So a rigorous proof has to be written before it can be formalised.
   * My first attempt split it into the Δ square, ∫₀¹|G_t|² d*a with G_t(a) = 2∫₀^a s^{−½+it}cos(2πs) ds,
     plus the rest.  That split is FALSE.  At t = 0, ∫₀¹|G_t|² d*a = 5.2326 but δ̂(0) = 5.4213 [N-here].
     The reason is that (48) is valid only for ρ ≥ 1, and the symmetric extension δ(1/ρ) is not (48) at 1/ρ.
   * Any rigorous route found so far needs a cutoff limit R → ∞ of conditionally convergent oscillatory double
     integrals, with Si asymptotics (Si(x) → π/2, which is itself absent from Mathlib).
   * Estimate 1500-3000 lines, high variance, and no paper proof in hand.

**M2 total: about 2700-4500 lines, centred near the 4000 threshold.**  It needs absent Mathlib infrastructure:
the Mellin transform of cos on the critical strip, the Dirichlet integral, and limits of oscillatory improper
integrals.  Its core step has no rigorous source proof to transcribe.  Under the decision rule
(stop if M2 > ~4000 lines or needs absent infrastructure) this is a STOP.

### M3: not started

Given M2 it is one line: `Lfun_nonneg_of_ell_nonneg` with `ell r = ∫ |Φ_r|² ≥ 0`.

## 3. The S3' alternative (estimate only, not started)

S3' proves `∀ r, 0 ≤ ell r` by certified numerics plus large-r asymptotics.  M1 already reduces CC Cor 2.3 to
exactly this one-variable statement (`Lfun_nonneg_of_ell_nonneg`).  So S3' needs no further plumbing.

| piece | content | est. lines |
|---|---|---|
| large r | psiR r − log π ≥ log(r/2π) − c, and \|δ̂(r)\| ≤ C/r² from the derivative jump of δ(e^u) at 0 (CC (50)) plus decay, or crudely \|δ̂\| ≤ ‖δ‖₁ | 300-500 |
| certified Si | Taylor enclosure on [0, X₀], asymptotic Si(x) = π/2 − cos x/x − sin x/x² + R with \|R\| bound beyond | 300-500 |
| certified δ̂ on [0, R₀] | δ(e^u) = e^{−u/2}(1 + small oscillating part); closed-form transform of the main part, piecewise bounds on the rest, tail ≤ 16 e^{−U/2}/(…) for u ≥ U | 500-800 + data |
| psiR lower bound | reuse E6Bridge30 `psiR_ge_rational` / `psiR_ge_series` and `psiR_mono` | 100-200 |
| t-grid | Lipschitz in r, coarse grid where the slack is large (ℓ(10) ≈ 0.358), fine near r = 0 (slack 0.049) | 200-400 + data |

**S3' total: about 1400-2400 lines plus certificate data.**  The tightest precision need is at r = 0:
psiR(0) − log π = −5.37218 against δ̂(0) = 5.42125 [N-here], so δ̂ is needed to about 1e-3 relative there.
This matches the blueprint's 1500-line estimate.

## 4. Open items

* M2 and M3 (above).
* Not wired: `defaultTargets` and `AxiomGuardRvMBridge.lean` are untouched, per the conventions.
  `ArchS3_Delta` and `ArchS3_Guard` are registered as their own `lean_lib`s at the end of the lakefile.
* Not proved: δ > 0 (needs Si > 0), the derivative jump δ'(1⁺) = 1 (S4 wants it), and evenness of
  `ccDelta` under ρ ↦ 1/ρ (we define the kernel through e^{|u|}, so it is not needed).

## 5. Lean footguns hit

* `hasDerivAt_id t` is stated for `id`, not `fun s => s`.  After rewriting a function to `fun s => s`, use
  `(hasDerivAt_id' t).congr_deriv (by simp)`.
* `HasDerivAt.neg` leaves `(-fun s => …) t` in the derivative.  Run `simp only [Pi.neg_apply]` before
  `field_simp` or `ring`.
* `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'` cannot infer `f` from a
  `Continuous (sinc ∘ (fst * snd))` proof.  Pass `(f := fun c t => Real.sinc (c * t))` explicitly.
* `le_or_lt` is gone at this pin; use `le_or_gt`.
* `rwa [← abs_of_pos h] at this` rewrites every occurrence of the term, including inside `sincInt c`.
  Rewrite the goal with `abs_of_pos h` instead.
* `linarith` failed on an identity with atoms `cos c / c` and `-cos c / c`.  `linear_combination hF` closed it.
* `Real.log 0 = 0` in Mathlib, so the primitive −(t·sinc(ct))·log t vanishes at both ends of [0, 1] with no
  limit argument.  `Real.continuous_mul_log` gives its continuity at 0.
