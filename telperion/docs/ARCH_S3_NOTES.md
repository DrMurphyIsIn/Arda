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

## 2. Milestones

(filled in as they land)
