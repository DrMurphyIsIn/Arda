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

### M2 (first pass): stopped by the original decision rule, then resumed

The first pass stopped after M1 (commit 86e71feac).  The 2-D HS identity needed infrastructure absent from Mathlib,
and CC's (38)-(39) has no rigorous proof to transcribe (formal principal value; (163) quoted from Connes-Marcolli).
The lead then lifted the 4000-line rule and asked for the conceptual M2.  The rigorous route below needs no
principal value, no Si asymptotics and no contour rotation.

### M2 resumed (lead, 2026-10-11): the stop rule is lifted; rigorous route found

**Proof sketch of (★)** (z = ½ + it, w = z̄ = 1 − z, C(s) = 2cos 2πs, C_ε(s) = C(s)e^{−εs}, ε ∈ (0,1]).
Every integral below converges absolutely because of the damping; ε → 0 is taken only at the end.

* Damped objects: P(a) = a^{z−1}C_ε(a), Q = conj P, Φ_ε(a) = ∫_a^∞ P, Ψ_ε = ∫_0^∞ P,
  Ψ'_ε = ∫_0^∞ log·P.  Closed forms: Ψ_ε = Γ(z)((ε−2πi)^{−z} + (ε+2πi)^{−z}) (complex Gamma integral,
  by analytic continuation in r from Mathlib's real-r formula), Ψ'_ε = its z-derivative (Mellin derivative).
* (A) IBP on (1,∞) with v = log a: N_ε := ∫₁^∞|Φ_ε|² da/a = 2Re U(1,∞), where U(A) = ∫_A log a·P(a)·conj Φ_ε(a) da.
* (B) Quadrant symmetry: Ψ'_ε conj Ψ_ε = U(0,∞) + U₂, U₂ = ∫ log a P(a) ∫_0^a Q; swapping the order gives
  conj U₂ = V := ∫ P(a) ∫_a^∞ log s Q(s).  Hence 2Re U(0,∞) = Re(Ψ'_ε conj Ψ_ε) + Re(U(0,∞) − V).
* (C1) Substituting s = ρa: U(0,∞) − V = ∫₁^∞ (−log ρ) ρ^{w−1} J_ε(ρ) dρ with
  J_ε(ρ) = ∫₀^∞ C_ε(a)C_ε(ρa) da = 2κ/(κ² + 4π²(ρ−1)²) + 2κ/(κ² + 4π²(ρ+1)²), κ = ε(1+ρ).
  Call its real part R_ε.
* (C2) The same substitution: 2Re U(0,1) = −2Re∫₁^∞ ρ^{w−1} I_ε(ρ) dρ, I_ε(ρ) = ∫₀¹ (−log a) C_ε(a)C_ε(ρa) da.
* Assembly: N_ε = Re(Ψ'_ε conj Ψ_ε) + R_ε + 2Re∫₁^∞ ρ^{w−1} I_ε(ρ) dρ  (exact, every ε > 0).
* Limits ε → 0:
  * N_ε → N = ∫₁^∞|Φ_t|² d*a by dominated convergence, |Φ_ε(a)| ≤ (2 + 2|z−1|)/π · a^{−1/2} (one IBP).
  * Re(Ψ'_ε conj Ψ_ε) → Re(Ψ' conj Ψ) = psiR t − log π, because Ψ = Γℝ(z)/Γℝ(1−z) has |Ψ| = 1 on the line
    and its log-derivative is −log π + (ψ(z/2) + ψ((1−z)/2))/2.
  * R_ε → 0 by dominated convergence: log ρ · J_ε(ρ) ≤ (1 + 5 log ρ)/ρ, and → 0 pointwise for ρ > 1.
  * I_ε(ρ) → ccDelta(ρ)/√ρ, dominated via |∫₀¹(−log a)cos(ωa)e^{−κa}da| ≤ 4(2/ω)^{3/4}; then
    2Re∫₁^∞ ρ^{−½−it} ccDelta(ρ)ρ^{−½} dρ = deltaHat t by ρ = e^u and evenness.
  * Hence N = psiR t − log π + deltaHat t = ell t.
* Undamped Φ_t(a) := Ψ − ∫₀^a s^{z−1}C(s) ds equals lim_{R→∞} ∫_a^R s^{z−1}C(s) ds (the improper integral A e_t).

Numerical checks of every new identity [N-here, mpmath]:

| identity | t, ε | left | right |
|---|---|---|---|
| ∫₀¹(1 − \|Φ_t\|²) d*a = δ̂(t) (undamped Δ part) | 0 | 5.421254 | 5.421255 |
| same | 0.5 | 3.381329 | 3.381328 |
| same | 2 | 1.214903 | 1.214901 |
| N_ε − L_ε = Re(Ψ'_εΨ̄_ε) + R_ε (L_ε = ∫₀¹(\|Ψ_ε\|² − \|Φ_ε\|²) d*a) | 0.5, 0.3 | −3.3172521366 | −3.3172521364 |
| same | 0, 0.5 | −5.8806021445 | −5.8806021447 |
| L_ε = 2Re∫₁^∞ ρ^{−z} I_ε(ρ) dρ | 0.5, 0.3 | 3.33017865 | 3.33017865 |
| same | 0, 0.5 | 5.88721659 | 5.88721659 |

(The first attempt at a damped-Δ check used a crude oscillatory quadrature truncated at ρ = 100 and did not agree.
Redone with the closed form ∫₀¹(−log a)e^{ca} da = −Ein(−c)/c it agrees to 1e-9.)

### M2a, M2b, M2c, M3: DONE

All kernel-checked, axioms exactly `[propext, Classical.choice, Quot.sound]`
(`lake build ArchS3_Limits && lake env lean ArchS3_Guard.lean`, 59 guard lines). No `sorry`, no `axiom`, no warnings
in the ArchS3 modules.

| milestone | file | lines | commit | content |
|---|---|---|---|---|
| M1 | `ArchS3_Delta.lean` | 571 | f1d6cd7ee | δ via CC (48), L = W∞ + D in Fourier and u-space form |
| M2a | `ArchS3_Mellin.lean` | 508 | 4430d82f7 | complex-rate Gamma integral, damped Mellin transforms of cos, Ψ = Γℝ(z)/Γℝ(1−z), \|Ψ\| = 1, Re(Ψ'Ψ̄) = psiR − log π |
| M2b | `ArchS3_Phi.lean` | 376 | ede4639ea | Φ_t as the improper integral A e_t, tail bound K_t a^{−1/2}, square-integrability |
| M2c.1 | `ArchS3_Quadrant.lean` | 595 | dc9c34f8d | the exact damped identity (IBP, quadrant swap, s = ρa substitution + Fubini) |
| M2c.2 + M3 | `ArchS3_Limits.lean` | 757 | 8fb7b4f80 | ε → 0 limits, ell = ∫\|Φ\|², CC Cor 2.3 |
| guard | `ArchS3_Guard.lean` | 73 | | 59 `#print axioms` lines |

M2 + M3: 2236 lines.  M1 + M2 + M3: 2807 lines (guard excluded).  The blueprint estimated 2500-4000 for S3.

Main statements (namespace `ArchS3`, `zt t = 1/2 + t I`):

```lean
-- M2a
theorem gInt_eq (hz : 0 < z.re) (hr : 0 < r.re) :
    ∫ s in Ioi 0, (s:ℂ)^(z-1) * cexp (-(r*s)) = (1/r)^z * Gamma z            -- complex rate r
theorem integral_cosD (hε : 0 < ε) (hz : 0 < z.re) :
    ∫ s in Ioi 0, (s:ℂ)^(z-1) * cosD ε s = PsiE ε z                          -- cosD ε s = 2cos(2πs)e^{-εs}
theorem integral_log_cosD ... = dPsiE ε z
theorem Psi_eq_Gammaℝ (hz : 0 < z.re) : Psi z = Gammaℝ z / Gammaℝ (1 - z)
theorem norm_Psi_zt (t) : ‖Psi (zt t)‖ = 1
theorem re_dPsi_mul_conj_Psi (t) : (dPsi (zt t) * conj (Psi (zt t))).re = psiR t - log π
-- M2b
def Phi (t a : ℝ) : ℂ := Psi (zt t) - ∫ s in 0..a, (s:ℂ)^(zt t - 1) * cosD 0 s
theorem tendsto_integral_Phi (ha : 0 < a) :
    Tendsto (fun R => ∫ s in a..R, (s:ℂ)^(zt t - 1) * cosD 0 s) atTop (𝓝 (Phi t a))
theorem tendsto_integral_Psi (t) : Tendsto (fun R => ∫ s in 0..R, ...) atTop (𝓝 (Psi (zt t)))
theorem norm_Phi_le (ha : 0 < a) : ‖Phi t a‖ ≤ Kt t * a ^ (-1/2 : ℝ)
def Nnorm (t : ℝ) : ℝ := ∫ a in Ioi 1, ‖Phi t a‖ ^ 2 / a
-- M2c
theorem damped_identity (hε : 0 < ε) :
    ∫ a in Ioi 1, ‖PhiE t ε a‖^2 / a
      = (dPsiE ε (zt t) * conj (PsiE ε (zt t))).re
        + (∫ ρ in Ioi 1, (-(log ρ:ℂ)) * (ρ:ℂ)^(conj (zt t) - 1) * Jd ε ρ).re
        + 2 * (∫ ρ in Ioi 1, (ρ:ℂ)^(conj (zt t) - 1) * Id ε ρ).re
theorem ell_eq_Nnorm (t : ℝ) : ell t = Nnorm t           -- psiR t − log π + δ̂(t) = ∫_1^∞ |Φ_t|² da/a
-- M3
theorem ell_nonneg (t : ℝ) : 0 ≤ ell t
theorem Lfun_eq_integral_Nnorm (hg : IsWeilTest g) : Lfun g = (1/(2π)) * ∫ r, hsq g r * Nnorm r
theorem cc_cor_2_3 (hg : IsWeilTest g) : 0 ≤ Lfun g     -- CC Corollary 2.3, any support
theorem cc_cor_2_3_dirichlet (hg) :
    0 ≤ (psiR 0 - log π) * mass g + ½ ∫∫ |g v - g w|² archK (v - w) + Dfun g
theorem weilForm_add_Dfun_nonneg (hg) (hsupp : tsupport g ⊆ Icc (-L) L) (hL : 2L ≤ log 2)
    (h0 : paperFT g (I/2) = 0) : 0 ≤ (weilForm (autocorr g)).re + Dfun g
```

**What this is.**
* `ell_eq_Nnorm` is CC Prop 2.2(iii) and formula (52), made rigorous pointwise in the Mellin variable:
  2θ'(t) + δ̂(t) is the squared norm of A e_t, with A = (1 − P)uP.
* `Lfun_eq_integral_Nnorm` is the HS identity ‖A T_g‖²_HS = W∞ + D in its Mellin-diagonal form.
* `cc_cor_2_3` is CC Corollary 2.3, proved structurally rather than numerically: W∞ + D ≥ 0 for every test function
  of any support.

**What this is NOT.**
* It is not Weil positivity.  D is an extra positive-type term that the Weil form does not contain.
* W∞ ≥ 0 on the pole-free window still needs S4 (D∘Q = −2·Id + K^δ) and spectral information on K_I (S5-S11).
* `conjecture1_proved = False`.

## 3. The S3' alternative (estimate only; superseded, since S3 itself is done)

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

* M2 and M3 are done.
* Not done: the 2-D HS form ‖A T_g‖²_HS as a double integral.  The Mellin-diagonal form `Lfun_eq_integral_Nnorm`
  replaces it.
* Not done: Ψ as an improper integral off the critical line.  Only Re z = 1/2 is stated, although M2a has the
  damped transform for every Re z > 0.
* Not wired: `defaultTargets` and `AxiomGuardRvMBridge.lean` are untouched, per the conventions.
  `ArchS3_Delta` and `ArchS3_Guard` are registered as their own `lean_lib`s at the end of the lakefile.
* Not proved: δ > 0 (needs Si > 0), the derivative jump δ'(1⁺) = 1 (S4 wants it), and evenness of
  `ccDelta` under ρ ↦ 1/ρ (we define the kernel through e^{|u|}, so it is not needed).

## 5. Lean footguns hit

M2/M3:
* Mathlib's `integral_cpow_mul_exp_neg_mul_Ioi` only takes a REAL rate.  The complex-rate version follows from
  `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` on Re r > 0.  Analyticity comes from
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le`, agreement near 1 from `Tendsto.frequently` along `ofReal`.
* `Integrable.const_mul`, `.sub` and `.norm` return `Integrable`, not `IntegrableOn`.  So `.mono_set` and
  `.congr_fun` fail by dot notation.  Call `IntegrableOn.mono_set (…) h` and `IntegrableOn.congr_fun (…) h hs` explicitly.
* `∫ s in A, f s + g s` parses with the integral swallowing `+ g s`.  Parenthesise `(c * ∫ s in A, f s) + …`.
* `ContinuousAt.comp` with a product-variable inner function mis-unifies (`HMul.hMul p.1`).  Pass `(g := …)` and a
  separate `have` for the inner `ContinuousAt (fun q => q.1 * q.2) p`.
* `(by fun_prop : Continuous f).intervalIntegrable` has type `∀ a b, …`; apply it to the endpoints.
* `HasDerivAt.norm_sq` gives `2 * ⟪f x, f'⟫_ℝ`.  For ℂ, `Complex.inner w z = (z * conj w).re`.
* `integral_comp_exp_Ioi` (IntegralEqImproper) does the ρ = e^u substitution on (1, ∞) directly.
* `integral_re` is stated with `RCLike.re`.  `simp only [RCLike.re_to_complex] at h` turns it into `.re`.
* In `by rw [norm_one]; linarith` used as the argument of `.trans`, the target has a metavariable.  `rw` closes it by
  unification and `linarith` then fails with "no goals".  State the intermediate bound with an explicit `have`.

M1:

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
