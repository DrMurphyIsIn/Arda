/-  StirlingBinet.lean -- A2 Theorem 2: the Stirling/Binet enclosure of `log Γℝ`.

    GOAL (ANDÚRIL A2 theorem 2): a COMPUTABLE enclosure of `log Γℝ(z)` -- both `Re` and the
    CONTINUOUS-BRANCH `Im` -- for `Re z ≥ 1/4`, via the Stirling series with the Binet remainder
    bound, plus the shift trick `z ← z + m` to reach the accurate region.  Serves BOTH the Γℝ
    vertical edges (H4 edges 4,5) AND `θ` for the later A3 Riemann–Siegel era (via
    `DiffractionCore.theta_eq_argChangeVert_gammaR`).  Only the `K = 4` instance is needed first.

    STRATEGY.  The consumer is `LogBranches.argChangeVert_eq_im_log_sub`, which converts the
    box-edge argument change into `Im L(top) − Im L(bottom)` for any branch `L` with
    `deriv L = logDeriv Γℝ`.  Because the argument-change quantity is an integral of
    `logDeriv Γℝ` (`DiffractionCore.argChangeVert`), the RELEVANT enclosure is of `logDeriv Γℝ`
    itself: an EXPLICIT finite Stirling/Binet approximant with a kernel-checkable error envelope.
    This file builds that enclosure bottom-up on the corpus's existing Binet machinery
    (`ZeroFreeBridge.*` in `DlvpTheta`, re-exported through `DiffractionCore`):

      logDeriv Γℝ(z) = −(log π)/2 + (1/2)·ψ(z/2)                         [Mathlib/corpus]
      ψ(w)           = log w + μ(w),        μ(w) := ψ(w) − log w          [Binet remainder]
      ψ(w)           = ψ(w+m) − Σ_{k<m} (w+k)⁻¹                          [shift trick]
      ‖μ(w+m)‖       ≤ 1/(Re w + m − 1)     for  Re w + m ≥ 2            [Binet K=1 bound]

    So for `Re z ≥ 1/4`, choosing `m` with `Re(z/2) + m ≥ 2`, `logDeriv Γℝ(z)` decomposes into an
    EXPLICIT finite part (`−(log π)/2 + (1/2)·log((z/2)+m) − (1/2)·Σ_{k<m} ((z/2)+k)⁻¹`) plus a
    remainder whose norm is `≤ (1/2)/(Re(z/2)+m−1)` -- a rational envelope the interval evaluator
    checks.  The `K = 1` remainder (order `1/w`) is the fully-discharged instance; the higher
    Bernoulli-weighted `K` terms sharpen the rate but the ARCHITECTURE is identical and the
    consumer only needs a valid envelope.  `StirlingBinetWip.lean` carries the `K ≥ 2` Bernoulli
    tail (NOT guard-imported).

    conjecture1_proved = False.  This is a finite computable enclosure, NOT a proof of RH.
-/
import DiffractionCore

open Complex

namespace ZetaReflection

/-- Real part of a halving: `(z/2).re = z.re/2`.  Small arithmetic helper used throughout to
    push the `Re z` hypotheses through the `z ← z/2` argument of `Γℝ`. -/
theorem div_two_re (z : ℂ) : (z / 2).re = z.re / 2 := by
  rw [show z / 2 = z * (2⁻¹ : ℝ) by push_cast; ring, Complex.mul_re]
  simp
  ring

/-! ## 1.  The Binet remainder `μ(w) := ψ(w) − log w` and its `K = 1` enclosure.

`μ` is the object the Stirling series expands: `ψ(w) = log w − 1/(2w) − Σ_{j≥1} B_{2j}/(2j w^{2j})`,
so `μ(w) = ψ(w) − log w` is `O(1/w)`.  The corpus already proves the effective `K = 1` envelope
`‖μ(w)‖ ≤ 1/(Re w − 1)` for real `w ∈ [2,3]` UNCONDITIONALLY, and for complex `Re w ≥ 2` MODULO
the anchor `ψ(w+N) − log(w+N) → 0` (discharged on the reals; the complex identity-theorem lift is
`DlvpTheta` brick 3b′-iii, future work).  We package `μ` and re-export the bounds in the shape the
Γℝ enclosure consumes. -/

/-- The Binet remainder of the digamma function: `μ(w) = ψ(w) − log w`. -/
noncomputable def binetRem (w : ℂ) : ℂ := Complex.digamma w - Complex.log w

/-- **`K = 1` Binet enclosure, real argument** (unconditional): `‖μ(w)‖ ≤ 1/(w−1)` for real
    `w ∈ [2, 3]`.  Direct re-export of `ZeroFreeBridge.norm_digamma_sub_log_le_ofReal`. -/
theorem norm_binetRem_le_ofReal {x : ℝ} (hx2 : 2 ≤ x) (hx3 : x ≤ 3) :
    ‖binetRem ((x : ℝ) : ℂ)‖ ≤ 1 / (x - 1) :=
  ZeroFreeBridge.norm_digamma_sub_log_le_ofReal hx2 hx3

/-- **`K = 1` Binet enclosure, complex argument, modulo the anchor**: for `Re w ≥ 2` and the
    right-shift anchor `ψ(w+N) − log(w+N) → 0`, `‖μ(w)‖ ≤ 1/(Re w − 1)`.  Re-export of
    `ZeroFreeBridge.norm_digamma_sub_log_le_of_anchor`. -/
theorem norm_binetRem_le_of_anchor {w : ℂ} (hw : 2 ≤ w.re)
    (hanchor : Filter.Tendsto
      (fun N : ℕ => Complex.digamma (w + N) - Complex.log (w + N))
      Filter.atTop (nhds 0)) :
    ‖binetRem w‖ ≤ 1 / (w.re - 1) :=
  ZeroFreeBridge.norm_digamma_sub_log_le_of_anchor hw hanchor

/-! ## 2.  The shift trick for `ψ`, phrased through `binetRem`.

`ψ(w) = ψ(w+m) − Σ_{k<m} (w+k)⁻¹`, so
`μ(w) = ψ(w) − log w = [ψ(w+m) − log(w+m)] + [log(w+m) − log w] − Σ_{k<m}(w+k)⁻¹`
      = μ(w+m) + Σ_{k<m} log(1+(w+k)⁻¹) − Σ_{k<m}(w+k)⁻¹.
The point: `μ(w+m)` is small (`Re(w+m)` large), the two finite sums are EXPLICIT, so `μ(w)` --
hence `ψ(w)` -- is enclosed by an explicit finite part plus a small remainder even when `Re w` is
only `≥ 1/4`.  We prove the EXACT shift identity for `ψ` (from the corpus `digamma_shift`) and its
`binetRem` consequence. -/

/-- **Exact shift identity for `ψ`** (subtraction form): `ψ(w) = ψ(w+m) − Σ_{k<m} (w+k)⁻¹`
    for `Re w > 0`.  Re-export of `ZeroFreeBridge.digamma_eq_shift_sub`. -/
theorem digamma_eq_shift_sub {w : ℂ} (hw : 0 < w.re) (m : ℕ) :
    Complex.digamma w
      = Complex.digamma (w + m) - ∑ k ∈ Finset.range m, (w + k)⁻¹ :=
  ZeroFreeBridge.digamma_eq_shift_sub hw m

/-- **Shift identity for the Binet remainder**: for `Re w > 0`,
    `μ(w) = μ(w+m) + [log(w+m) − log w] − Σ_{k<m} (w+k)⁻¹`.
    All terms except `μ(w+m)` are EXPLICIT finite data; `μ(w+m)` is the small enclosed tail. -/
theorem binetRem_shift {w : ℂ} (hw : 0 < w.re) (m : ℕ) :
    binetRem w
      = binetRem (w + m)
        + (Complex.log (w + m) - Complex.log w)
        - ∑ k ∈ Finset.range m, (w + k)⁻¹ := by
  unfold binetRem
  rw [digamma_eq_shift_sub hw m]
  ring

/-! ## 3.  The Stirling/Binet decomposition of `logDeriv Γℝ`.

`logDeriv Γℝ(z) = −(log π)/2 + (1/2)·ψ(z/2)` on `Re(z/2) > 0` (corpus `logDeriv_gammaR`).
Writing `ψ(z/2) = log(z/2) + μ(z/2)` gives the Stirling FORM

    logDeriv Γℝ(z) = −(log π)/2 + (1/2)·log(z/2) + (1/2)·μ(z/2),

the explicit main part `−(log π)/2 + (1/2)·log(z/2)` plus the `O(1/z)` Binet remainder. -/

/-- **The Stirling decomposition of `logDeriv Γℝ`** on `Re z > 0`:
    `logDeriv Γℝ(z) = −(log π)/2 + (1/2)·log(z/2) + (1/2)·μ(z/2)`. -/
theorem logDeriv_gammaR_stirling {z : ℂ} (hz : 0 < z.re) :
    logDeriv Complex.Gammaℝ z
      = -(Real.log Real.pi : ℂ) / 2
        + (1 / 2) * Complex.log (z / 2)
        + (1 / 2) * binetRem (z / 2) := by
  have hz2 : 0 < (z / 2).re := by rw [div_two_re]; linarith
  rw [ZeroFreeBridge.logDeriv_gammaR z hz2]
  unfold binetRem
  ring

/-- **The Stirling decomposition with the shift trick baked in** on `Re z > 0`: for any `m`,
    `logDeriv Γℝ(z) = −(log π)/2 + (1/2)·log((z/2)+m) − (1/2)·Σ_{k<m} ((z/2)+k)⁻¹
                        + (1/2)·μ((z/2)+m)`.
    The first three terms are EXPLICIT finite data at the shifted point; `μ((z/2)+m)` is the small
    remainder, enclosed by §4.  This is the form the interval evaluator instantiates:  pick `m`
    with `Re(z/2)+m ≥ 2`, compute the finite part, bound the remainder. -/
theorem logDeriv_gammaR_stirling_shift {z : ℂ} (hz : 0 < z.re) (m : ℕ) :
    logDeriv Complex.Gammaℝ z
      = -(Real.log Real.pi : ℂ) / 2
        + (1 / 2) * Complex.log (z / 2 + m)
        - (1 / 2) * ∑ k ∈ Finset.range m, (z / 2 + k)⁻¹
        + (1 / 2) * binetRem (z / 2 + m) := by
  have hz2 : 0 < (z / 2).re := by rw [div_two_re]; linarith
  rw [logDeriv_gammaR_stirling hz, binetRem_shift hz2 m]
  ring

/-! ## 4.  The remainder ENVELOPE for `Re z ≥ 1/4` via the shift.

Combining §2–§3:  for `Re z ≥ 1/4`, the Binet remainder in the shifted Stirling form,
`(1/2)·μ((z/2)+m)`, is bounded by `(1/2)/(Re(z/2)+m−1)` once `Re(z/2)+m ≥ 2`, PROVIDED the anchor
holds at the shifted point.  The needed shift is small: `Re(z/2) ≥ 1/8`, so `m = 2` already gives
`Re(z/2)+m ≥ 1/8 + 2 ≥ 2`.  We state the envelope in the anchor-parametrised form the evaluator
consumes (the anchor is discharged on real arguments by the corpus squeeze, and on complex
arguments by the future identity-theorem lift -- carried explicitly here, not assumed globally). -/

/-- Real-part lower bound after the shift: `Re z ≥ 1/4` and `2 ≤ m` give `Re(z/2 + m) ≥ 2`. -/
theorem re_shift_ge {z : ℂ} (hz : (1 / 4 : ℝ) ≤ z.re) {m : ℕ} (hm : 2 ≤ m) :
    (2 : ℝ) ≤ (z / 2 + m).re := by
  have hzhalf : (1 / 8 : ℝ) ≤ (z / 2).re := by rw [div_two_re]; linarith
  have hmr : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  simp only [Complex.add_re, Complex.natCast_re]
  linarith

/-- **The Binet remainder envelope at `Re z ≥ 1/4`** (anchor-parametrised).  For `Re z ≥ 1/4`,
    `2 ≤ m`, and the shifted-point anchor `ψ((z/2+m)+N) − log((z/2+m)+N) → 0`, the Stirling
    remainder is bounded:
        ‖(1/2)·μ(z/2 + m)‖ ≤ (1/2) · 1/((z/2 + m).re − 1).
    Together with `logDeriv_gammaR_stirling_shift`, this is the computable enclosure of
    `logDeriv Γℝ(z)`:  explicit finite Stirling part ± this rational envelope. -/
theorem binet_remainder_envelope {z : ℂ} (hz : (1 / 4 : ℝ) ≤ z.re) {m : ℕ} (hm : 2 ≤ m)
    (hanchor : Filter.Tendsto
      (fun N : ℕ => Complex.digamma ((z / 2 + m) + N) - Complex.log ((z / 2 + m) + N))
      Filter.atTop (nhds 0)) :
    ‖(1 / 2 : ℂ) * binetRem (z / 2 + m)‖
      ≤ (1 / 2) * (1 / ((z / 2 + m).re - 1)) := by
  have hre : (2 : ℝ) ≤ (z / 2 + m).re := re_shift_ge hz hm
  have hbound : ‖binetRem (z / 2 + m)‖ ≤ 1 / ((z / 2 + m).re - 1) :=
    norm_binetRem_le_of_anchor hre hanchor
  rw [norm_mul]
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real]
    rw [Real.norm_of_nonneg (by norm_num)]
  rw [hhalf]
  have hnn : (0 : ℝ) ≤ 1 / 2 := by norm_num
  exact mul_le_mul_of_nonneg_left hbound hnn

end ZetaReflection
