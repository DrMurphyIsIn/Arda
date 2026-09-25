/-  ArgGammaR.lean -- brick K6b of the ANDURIL Arb discharge (with the T6 bridge it needs)
    (telperion/docs/ANDURIL_ARB_DISCHARGE_2026-09-23.md, inventory row H2f, bricks K6b and T6).

    THE BINDERS IT DISCHARGES.  Conjuncts 8 and 9 of the `hArbT` binder of every emitted Turing
    band (`TuringBand.BandStatement`, `BandGlue.BandData.EnclHyp`) are

        hAG1 : DiffractionCore.argChangeVert Gammaℝ (-1) T0 T1 ∈ Set.Icc L4 H4,
        hAG2 : DiffractionCore.argChangeVert Gammaℝ 2 T0 T1 ∈ Set.Icc L5 H5,

    the argument changes of the archimedean factor `Γℝ(s) = π^{-s/2} Γ(s/2)` up the two vertical
    edges of the RvM rectangle.  The emitted bands feed them 1e-12-wide Arb enclosures.  This file
    proves them HYPOTHESIS-FREE for every `0 ≤ T0`, `0 ≤ T1`, with explicit elementary endpoints
    (logs and arctans), in the exact binder form:

        argChangeVert Γℝ 2 T0 T1    ∈ [S2 T1 - S2 T0 - e2 T1,  S2 T1 - S2 T0 + e2 T0]    (`hAG2_closed`)
        argChangeVert Γℝ (-1) T0 T1 ∈ [Sm1 T1 - Sm1 T0 - em1 T1, Sm1 T1 - Sm1 T0 + em1 T0] (`hAG1_closed`)

        S2 T  = (1/2) arctan (T/2) + (T/4) log (1 + T²/4) - T/2 - (T/2) log π,   e2 T  = T/(2(4 + T²)),
        Sm1 T = (T/4) log (1/4 + T²/4) + arctan T - T/2 - (T/2) log π,          em1 T = T/(2(1 + T²)),

    plus the sharper `hAG2_mem` / `hAG1_mem` at any Stirling base index `n0` (error
    `y/(4((x+n0)² + y²))` at each edge, `y = T/2`), for the lowest bands.

    THE T6 BRIDGE (`integral_half_re_digamma`).  `RSTheta.lam_bracket` brackets the GAUSS BRANCH
    `Λ(x, y) = lim_n imLnVal x y n` (`gaussLam`), a limit of arctan sums.  The binders are integrals
    of `logDeriv Γℝ`.  The bridge identifies them: for `x > 0` and all `a`, `b`,

        ∫_a^b (1/2) Re ψ(x + i y/2) dy = Λ(x, b/2) - Λ(x, a/2),

    proved WITHOUT any locally-uniform-convergence machinery:
      * finite FTC: `d/dy imLnVal x (y/2) n = (1/2)(log n - Σ_{k≤n} (x+k)/((x+k)² + (y/2)²))`;
      * `ZeroFreeBridge.digamma_shift`: Re ψ(z) = [that sum] + Re(ψ(z + n + 1) - log n);
      * the remainder is at most `(x + 2 + |y|/2)/(2n)` (Binet bound
        `ZeroFreeBridge.norm_digamma_sub_log_le` at `Re ≥ 2` plus `log u ≤ u - 1`), so its
        integral is `O(1/n)`, and uniqueness of limits closes the identity.
    Then `logDeriv Γℝ s = -(log π)/2 + (1/2) ψ(s/2)` gives the σ = 2 edge at `x = 1`, and at σ = -1
    the shift `ψ(z) = ψ(z+1) - 1/z` (`z = -1/2 + i y/2`) gives `x = 1/2` plus the elementary
    `∫ 1/(1 + y²) = arctan T1 - arctan T0`.

    Trust: no hypotheses beyond those stated; axioms [propext, Classical.choice, Quot.sound]
    (see AxiomGuardArgChange.lean).  No `sorry`.

    conjecture1_proved = False.  Elementary enclosures of the Γ-factor edges of a finite zero
    count; nothing here bears on the Riemann Hypothesis. -/
import Mathlib
import DiffractionCore
import RSTheta

open Complex Filter Topology
open ThetaGap RSDesignTheta

namespace ArgGammaR

/-! ## 1. The Gauss-branch limit `Λ(x, y)` -/

/-- The Gauss-branch value `Λ(x, y) = lim_n imLnVal x y n` (informally Im log Γ(x + i y) on the
    branch continuous from the real axis; `ThetaConverge.imLnVal_cauchy` gives the limit for
    `x > 0`, and `ThetaConverge.convergence_obligation` shows it is an argument of Γ(x + i y)). -/
noncomputable def gaussLam (x y : ℝ) : ℝ := limUnder atTop (imLnVal x y)

theorem tendsto_gaussLam {x : ℝ} (hx : 0 < x) (y : ℝ) :
    Tendsto (imLnVal x y) atTop (𝓝 (gaussLam x y)) :=
  (ThetaConverge.imLnVal_cauchy x y hx).tendsto_limUnder

/-- The Stirling bracket centre of `RSTheta.lam_bracket` at base index `n0`. -/
noncomputable def lamC (x y : ℝ) (n0 : ℕ) : ℝ :=
  FA x y n0 + fA x y n0 / 2 - ∑ k ∈ Finset.range (n0 + 1), fA x y k - y

/-- The Stirling bracket width of `RSTheta.lam_bracket` at base index `n0`. -/
noncomputable def lamE (x y : ℝ) (n0 : ℕ) : ℝ := y / (4 * ((x + n0) ^ 2 + y ^ 2))

/-- `lamC - lamE ≤ Λ ≤ lamC` (the height-uniform Stirling bracket, `RSTheta.lam_bracket`). -/
theorem gaussLam_mem {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (n0 : ℕ) :
    lamC x y n0 - lamE x y n0 ≤ gaussLam x y ∧ gaussLam x y ≤ lamC x y n0 :=
  lam_bracket x y hx hy n0 _ (tendsto_gaussLam hx y)

/-! ## 2. The T6 bridge: `∫ (1/2) Re ψ(x + i y/2) dy = Λ(x, b/2) - Λ(x, a/2)` -/

/-- The derivative in `y` of `imLnVal x (y/2) n`. -/
noncomputable def dImLn (x : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  (1 / 2) * (Real.log n - ∑ k ∈ Finset.range (n + 1), (x + k) / ((x + k) ^ 2 + (y / 2) ^ 2))

theorem hasDerivAt_imLnVal_half {x : ℝ} (hx : 0 < x) (n : ℕ) (y : ℝ) :
    HasDerivAt (fun y => imLnVal x (y / 2) n) (dImLn x n y) y := by
  unfold imLnVal dImLn
  have hlin : HasDerivAt (fun y : ℝ => y / 2 * Real.log n) (1 / 2 * Real.log n) y := by
    have := ((hasDerivAt_id y).div_const 2).mul_const (Real.log n)
    simpa using this
  have hsum : HasDerivAt (fun y : ℝ => ∑ k ∈ Finset.range (n + 1), Real.arctan (y / 2 / (x + k)))
      (∑ k ∈ Finset.range (n + 1), (1 / 2) * ((x + k) / ((x + k) ^ 2 + (y / 2) ^ 2))) y := by
    apply HasDerivAt.fun_sum
    intro k _
    have hxk : 0 < x + k := by positivity
    have hq : HasDerivAt (fun y : ℝ => y / 2 / (x + k)) (1 / 2 / (x + k)) y := by
      have := ((hasDerivAt_id y).div_const 2).div_const (x + k)
      simpa using this
    refine hq.arctan.congr_deriv ?_
    field_simp
  refine (hlin.sub hsum).congr_deriv ?_
  rw [mul_sub, Finset.mul_sum]

theorem continuous_dImLn {x : ℝ} (hx : 0 < x) (n : ℕ) : Continuous (dImLn x n) := by
  unfold dImLn
  refine continuous_const.mul (continuous_const.sub ?_)
  refine continuous_finsetSum _ (fun k _ => ?_)
  refine Continuous.div continuous_const (by fun_prop) (fun y => ?_)
  have : 0 < x + k := by positivity
  positivity

/-- Finite FTC: `∫_a^b dImLn = imLnVal x (b/2) n - imLnVal x (a/2) n`. -/
theorem integral_dImLn {x : ℝ} (hx : 0 < x) (n : ℕ) (a b : ℝ) :
    ∫ y in a..b, dImLn x n y = imLnVal x (b / 2) n - imLnVal x (a / 2) n :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hasDerivAt_imLnVal_half hx n y)
    ((continuous_dImLn hx n).intervalIntegrable _ _)

/-- The digamma ray point `x + i y/2`. -/
theorem ray_re (x y : ℝ) : ((x : ℂ) + ((y / 2 : ℝ) : ℂ) * I).re = x := by simp

theorem continuous_half_re_digamma {x : ℝ} (hx : 0 < x) :
    Continuous (fun y : ℝ => (1 / 2 : ℝ) * (Complex.digamma ((x : ℂ) + ((y / 2 : ℝ) : ℂ) * I)).re) := by
  refine continuous_const.mul (Complex.continuous_re.comp ?_)
  refine continuous_iff_continuousAt.mpr fun y => ?_
  have hpath : Continuous (fun y : ℝ => (x : ℂ) + ((y / 2 : ℝ) : ℂ) * I) := by fun_prop
  exact ContinuousAt.comp (g := Complex.digamma)
    (DiffractionCore.digamma_continuousAt_of_re_pos (by rw [ray_re]; exact hx))
    hpath.continuousAt

/-- Real part of `(x + k + i y/2)⁻¹`. -/
theorem re_inv_ray (x y : ℝ) (k : ℕ) :
    (((x : ℂ) + ((y / 2 : ℝ) : ℂ) * I + (k : ℂ))⁻¹).re = (x + k) / ((x + k) ^ 2 + (y / 2) ^ 2) := by
  rw [Complex.inv_re, Complex.normSq_apply]
  have hre : ((x : ℂ) + ((y / 2 : ℝ) : ℂ) * I + (k : ℂ)).re = x + k := by simp
  have him : ((x : ℂ) + ((y / 2 : ℝ) : ℂ) * I + (k : ℂ)).im = y / 2 := by simp
  rw [hre, him]
  ring

/-- **Pointwise split** (`digamma_shift` with `N = n + 1`):
    `(1/2) Re ψ(z) - dImLn x n y = (1/2)(Re ψ(z + n + 1) - log n)`, `z = x + i y/2`. -/
theorem half_re_digamma_sub_dImLn {x : ℝ} (hx : 0 < x) (n : ℕ) (y : ℝ) :
    (1 / 2 : ℝ) * (Complex.digamma ((x : ℂ) + ((y / 2 : ℝ) : ℂ) * I)).re - dImLn x n y
      = (1 / 2 : ℝ) * ((Complex.digamma ((x : ℂ) + ((y / 2 : ℝ) : ℂ) * I + ((n + 1 : ℕ) : ℂ))).re
          - Real.log n) := by
  have hs : 0 < ((x : ℂ) + ((y / 2 : ℝ) : ℂ) * I).re := by rw [ray_re]; exact hx
  have hshift := ZeroFreeBridge.digamma_shift hs (n + 1)
  have hre := congrArg Complex.re hshift
  rw [Complex.add_re, Complex.re_sum] at hre
  have hterm : ∀ k ∈ Finset.range (n + 1),
      (((x : ℂ) + ((y / 2 : ℝ) : ℂ) * I + (k : ℂ))⁻¹).re = (x + k) / ((x + k) ^ 2 + (y / 2) ^ 2) :=
    fun k _ => re_inv_ray x y k
  rw [Finset.sum_congr rfl hterm] at hre
  unfold dImLn
  rw [hre]
  ring

/-- **The remainder bound**: for `n ≥ 1`,
    `|(1/2)(Re ψ(z + n + 1) - log n)| ≤ (x + 2 + |y|/2) / (2 n)`. -/
theorem abs_remainder_le {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 1 ≤ n) (y : ℝ) :
    |(1 / 2 : ℝ) * ((Complex.digamma ((x : ℂ) + ((y / 2 : ℝ) : ℂ) * I + ((n + 1 : ℕ) : ℂ))).re
        - Real.log n)| ≤ (x + 2 + |y| / 2) / (2 * n) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set w : ℂ := (x : ℂ) + ((y / 2 : ℝ) : ℂ) * I + ((n + 1 : ℕ) : ℂ) with hw
  have hwre : w.re = x + n + 1 := by rw [hw]; simp; ring
  have hwim : w.im = y / 2 := by rw [hw]; simp
  have hw2 : 2 ≤ w.re := by rw [hwre]; linarith
  have hbin := ZeroFreeBridge.norm_digamma_sub_log_le hw2
  rw [hwre, show x + n + 1 - 1 = x + n by ring] at hbin
  -- split Re ψ(w) - log n = Re (ψ w - log w) + (log ‖w‖ - log n)
  have hsplit : (Complex.digamma w).re - Real.log n
      = (Complex.digamma w - Complex.log w).re + (Real.log ‖w‖ - Real.log n) := by
    rw [Complex.sub_re, Complex.log_re]; ring
  have h1 : |(Complex.digamma w - Complex.log w).re| ≤ 1 / n := by
    refine le_trans (Complex.abs_re_le_norm _) (le_trans hbin ?_)
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hnorm_lo : (n : ℝ) < ‖w‖ := by
    have := Complex.re_le_norm w
    rw [hwre] at this; linarith
  have hnorm_hi : ‖w‖ ≤ x + n + 1 + |y| / 2 := by
    have := Complex.norm_le_abs_re_add_abs_im w
    rw [hwre, hwim, abs_of_pos (by linarith : (0 : ℝ) < x + n + 1), abs_div,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)] at this
    exact this
  have hnpos : (0 : ℝ) < n := by linarith
  have h2lo : 0 ≤ Real.log ‖w‖ - Real.log n := by
    have := Real.log_le_log hnpos hnorm_lo.le; linarith
  have h2hi : Real.log ‖w‖ - Real.log n ≤ (x + 1 + |y| / 2) / n := by
    rw [← Real.log_div (by linarith) hnpos.ne']
    refine le_trans (Real.log_le_sub_one_of_pos (div_pos (by linarith) hnpos)) ?_
    rw [div_sub_one hnpos.ne', div_le_div_iff_of_pos_right hnpos]
    linarith
  rw [hsplit, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have htri := abs_add_le (Complex.digamma w - Complex.log w).re (Real.log ‖w‖ - Real.log n)
  rw [abs_of_nonneg h2lo] at htri
  have hsum : 1 / (n : ℝ) + (x + 1 + |y| / 2) / n = (x + 2 + |y| / 2) / n := by
    field_simp; ring
  have hfin : (x + 2 + |y| / 2) / (2 * n) = 1 / 2 * ((x + 2 + |y| / 2) / n) := by
    field_simp
  rw [hfin]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  linarith

/-- **The T6 bridge.**  For `x > 0` and all `a`, `b`:
    `∫_a^b (1/2) Re ψ(x + i y/2) dy = Λ(x, b/2) - Λ(x, a/2)`. -/
theorem integral_half_re_digamma {x : ℝ} (hx : 0 < x) (a b : ℝ) :
    ∫ y in a..b, (1 / 2 : ℝ) * (Complex.digamma ((x : ℂ) + ((y / 2 : ℝ) : ℂ) * I)).re
      = gaussLam x (b / 2) - gaussLam x (a / 2) := by
  set I0 := ∫ y in a..b, (1 / 2 : ℝ) * (Complex.digamma ((x : ℂ) + ((y / 2 : ℝ) : ℂ) * I)).re
    with hI0
  set K : ℝ := (x + 2 + (|a| + |b|) / 2) / 2 * |b - a| with hK
  have hbound : ∀ n : ℕ, 1 ≤ n →
      |(imLnVal x (b / 2) n - imLnVal x (a / 2) n) - I0| ≤ K / n := by
    intro n hn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hint1 : IntervalIntegrable
        (fun y : ℝ => (1 / 2 : ℝ) * (Complex.digamma ((x : ℂ) + ((y / 2 : ℝ) : ℂ) * I)).re)
        MeasureTheory.volume a b := (continuous_half_re_digamma hx).intervalIntegrable _ _
    have hint2 : IntervalIntegrable (dImLn x n) MeasureTheory.volume a b :=
      (continuous_dImLn hx n).intervalIntegrable _ _
    have hdiff : I0 - (imLnVal x (b / 2) n - imLnVal x (a / 2) n)
        = ∫ y in a..b, (1 / 2 : ℝ) * ((Complex.digamma ((x : ℂ) + ((y / 2 : ℝ) : ℂ) * I
            + ((n + 1 : ℕ) : ℂ))).re - Real.log n) := by
      rw [hI0, ← integral_dImLn hx n a b, ← intervalIntegral.integral_sub hint1 hint2]
      exact intervalIntegral.integral_congr (fun y _ => half_re_digamma_sub_dImLn hx n y)
    have hC : ∀ y ∈ Set.uIoc a b,
        ‖(1 / 2 : ℝ) * ((Complex.digamma ((x : ℂ) + ((y / 2 : ℝ) : ℂ) * I
            + ((n + 1 : ℕ) : ℂ))).re - Real.log n)‖ ≤ (x + 2 + (|a| + |b|) / 2) / (2 * n) := by
      intro y hy
      have hyab : |y| ≤ |a| + |b| := by
        rcases Set.mem_uIcc.mp (Set.uIoc_subset_uIcc hy) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          exact abs_le.mpr ⟨by linarith [neg_abs_le a, neg_abs_le b, abs_nonneg a, abs_nonneg b],
            by linarith [le_abs_self a, le_abs_self b, abs_nonneg a, abs_nonneg b]⟩
      rw [Real.norm_eq_abs]
      refine le_trans (abs_remainder_le hx hn y) ?_
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hC
    rw [← hdiff, Real.norm_eq_abs] at hnorm
    rw [abs_sub_comm]
    refine le_trans hnorm (le_of_eq ?_)
    rw [hK]
    field_simp
  have hD : Tendsto (fun n => imLnVal x (b / 2) n - imLnVal x (a / 2) n) atTop
      (𝓝 (gaussLam x (b / 2) - gaussLam x (a / 2))) :=
    (tendsto_gaussLam hx _).sub (tendsto_gaussLam hx _)
  have hD' : Tendsto (fun n => imLnVal x (b / 2) n - imLnVal x (a / 2) n) atTop (𝓝 I0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_
      (tendsto_const_div_atTop_nhds_zero_nat K)
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Real.norm_eq_abs]
    exact hbound n hn
  exact tendsto_nhds_unique hD' hD

/-! ## 3. `logDeriv Γℝ` on the two vertical edges -/

/-- `logDeriv Γℝ s = -(log π)/2 + (1/2) ψ(s/2)` whenever `s/2` is not a pole of Γ
    (the `ZeroFreeBridge.logDeriv_gammaR` computation without the `Re (s/2) > 0` restriction). -/
theorem logDeriv_gammaR_of_ne {s : ℂ} (hpole : ∀ m : ℕ, s / 2 ≠ -(m : ℂ)) :
    logDeriv Gammaℝ s = -(Real.log Real.pi : ℂ) / 2 + (1 / 2) * Complex.digamma (s / 2) := by
  have hhalf : HasDerivAt (fun z : ℂ => z / 2) ((1 : ℂ) / 2) s := by
    have h := (hasDerivAt_id s).div_const 2
    norm_num at h
    exact h
  have hΓd : HasDerivAt Gamma (deriv Gamma (s / 2)) (s / 2) :=
    (Complex.differentiableAt_Gamma _ hpole).hasDerivAt
  have hB : HasDerivAt (fun z : ℂ => Gamma (z / 2)) (deriv Gamma (s / 2) * (1 / 2)) s :=
    hΓd.comp s hhalf
  have hBne : Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero hpole
  have hGdef : Gammaℝ = fun z : ℂ => ZeroFreeBridge.gammaRArch z * Gamma (z / 2) := rfl
  rw [hGdef, logDeriv_mul s (ZeroFreeBridge.gammaRArch_ne_zero s) hBne
    (ZeroFreeBridge.gammaRArch_hasDerivAt s).differentiableAt hB.differentiableAt]
  rw [ZeroFreeBridge.logDeriv_gammaRArch]
  have hlogB : logDeriv (fun z : ℂ => Gamma (z / 2)) s = (1 / 2) * Complex.digamma (s / 2) := by
    rw [logDeriv_apply, hB.deriv, Complex.digamma_def, logDeriv_apply]
    field_simp [hBne]
  rw [hlogB]

/-- `σ = 2`: `Re logDeriv Γℝ(2 + i y) = -(log π)/2 + (1/2) Re ψ(1 + i y/2)`. -/
theorem re_logDeriv_gammaR_two (y : ℝ) :
    (logDeriv Gammaℝ (((2 : ℝ) : ℂ) + (y : ℂ) * I)).re
      = -(Real.log Real.pi) / 2
        + (1 / 2 : ℝ) * (Complex.digamma (((1 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I)).re := by
  have hhalf : (((2 : ℝ) : ℂ) + (y : ℂ) * I) / 2 = ((1 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I := by
    push_cast; ring
  have hs : 0 < ((((2 : ℝ) : ℂ) + (y : ℂ) * I) / 2).re := by rw [hhalf]; simp
  rw [ZeroFreeBridge.logDeriv_gammaR _ hs, hhalf]
  have h1 : (-(Real.log Real.pi : ℂ) / 2) = ((-(Real.log Real.pi) / 2 : ℝ) : ℂ) := by
    push_cast; ring
  have h2 : ((1 : ℂ) / 2) = (((1 : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h1, h2, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]

/-- The half point `(-1 + i y)/2 = -1/2 + i y/2` is never a pole of Γ. -/
theorem half_neg_one_ne_pole (y : ℝ) (m : ℕ) : (((-1 : ℝ) : ℂ) + (y : ℂ) * I) / 2 ≠ -(m : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre
  have h2 : (2 * m : ℝ) = 1 := by linarith
  have h3 : (2 * m : ℕ) = 1 := by exact_mod_cast h2
  omega

/-- The shifted point `-1/2 + i y/2` is never a pole of Γ. -/
theorem neg_half_ne_pole (y : ℝ) (m : ℕ) :
    (((-1 / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I) ≠ -(m : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre
  have h2 : (2 * m : ℝ) = 1 := by linarith
  have h3 : (2 * m : ℕ) = 1 := by exact_mod_cast h2
  omega

/-- `σ = -1`: `logDeriv Γℝ(-1 + i y) = -(log π)/2 + (1/2)(ψ(1/2 + i y/2) - (-1/2 + i y/2)⁻¹)`. -/
theorem logDeriv_gammaR_neg_one (y : ℝ) :
    logDeriv Gammaℝ (((-1 : ℝ) : ℂ) + (y : ℂ) * I)
      = -(Real.log Real.pi : ℂ) / 2
        + (1 / 2) * (Complex.digamma (((1 / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I)
          - (((-1 / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I)⁻¹) := by
  rw [logDeriv_gammaR_of_ne (half_neg_one_ne_pole y)]
  have hhalf : (((-1 : ℝ) : ℂ) + (y : ℂ) * I) / 2 = ((-1 / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I := by
    push_cast; ring
  have hshift := Complex.digamma_apply_add_one (((-1 / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I)
    (neg_half_ne_pole y)
  have hp1 : ((-1 / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I + 1 = ((1 / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [hp1] at hshift
  rw [hhalf, hshift]
  ring

/-- Real part of `-(-1/2 + i y/2)⁻¹` is `2/(1 + y²)`. -/
theorem re_neg_inv_neg_half (y : ℝ) :
    (-(((-1 / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I)⁻¹).re = 2 / (1 + y ^ 2) := by
  have hre : (((-1 / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I).re = -1 / 2 := by simp
  have him : (((-1 / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I).im = y / 2 := by simp
  rw [Complex.neg_re, Complex.inv_re, Complex.normSq_apply, hre, him]
  have hden : (-1 / 2 : ℝ) * (-1 / 2) + y / 2 * (y / 2) = (1 + y ^ 2) / 4 := by ring
  have hpos : (0 : ℝ) < 1 + y ^ 2 := by positivity
  rw [hden]
  field_simp
  ring

/-- `σ = -1`: `Re logDeriv Γℝ(-1 + i y) = -(log π)/2 + (1/2) Re ψ(1/2 + i y/2) + 1/(1 + y²)`. -/
theorem re_logDeriv_gammaR_neg_one (y : ℝ) :
    (logDeriv Gammaℝ (((-1 : ℝ) : ℂ) + (y : ℂ) * I)).re
      = -(Real.log Real.pi) / 2
        + (1 / 2 : ℝ) * (Complex.digamma (((1 / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I)).re
        + 1 / (1 + y ^ 2) := by
  rw [logDeriv_gammaR_neg_one]
  have h1 : (-(Real.log Real.pi : ℂ) / 2) = ((-(Real.log Real.pi) / 2 : ℝ) : ℂ) := by
    push_cast; ring
  have h2 : ((1 : ℂ) / 2) = (((1 : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h1, h2, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, sub_eq_add_neg,
    Complex.add_re, re_neg_inv_neg_half]
  ring

theorem continuous_logDeriv_gammaR_neg_one :
    Continuous (fun y : ℝ => logDeriv Gammaℝ (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) := by
  have hfun := funext logDeriv_gammaR_neg_one
  rw [show (fun y : ℝ => logDeriv Gammaℝ (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) = _ from hfun]
  refine continuous_const.add (continuous_const.mul (Continuous.sub ?_ ?_))
  · refine continuous_iff_continuousAt.mpr fun y => ?_
    have hpath : Continuous (fun y : ℝ => ((1 / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I) := by fun_prop
    exact ContinuousAt.comp (g := Complex.digamma)
      (DiffractionCore.digamma_continuousAt_of_re_pos (by simp)) hpath.continuousAt
  · refine Continuous.inv₀ (by fun_prop) (fun y h => ?_)
    have := congrArg Complex.re h
    simp at this

/-! ## 4. The two edge identities -/

/-- **σ = 2 edge, exact** (every `T0`, `T1`):
    `argChangeVert Γℝ 2 T0 T1 = (Λ(1, T1/2) - (T1/2) log π) - (Λ(1, T0/2) - (T0/2) log π)`. -/
theorem argChangeVert_gammaR_two_eq (T0 T1 : ℝ) :
    DiffractionCore.argChangeVert Gammaℝ 2 T0 T1
      = (gaussLam 1 (T1 / 2) - T1 / 2 * Real.log Real.pi)
        - (gaussLam 1 (T0 / 2) - T0 / 2 * Real.log Real.pi) := by
  have hcont := DiffractionCore.continuous_logDeriv_gammaR_vLine (σ := 2) (by norm_num)
  have hInt : IntervalIntegrable (fun y : ℝ => logDeriv Gammaℝ (((2 : ℝ) : ℂ) + (y : ℂ) * I))
      MeasureTheory.volume T0 T1 := hcont.intervalIntegrable _ _
  have hre := intervalIntegral.intervalIntegral_re (𝕜 := ℂ) hInt
  simp only [RCLike.re_to_complex] at hre
  unfold DiffractionCore.argChangeVert
  rw [← hre]
  have hcongr : ∫ y in T0..T1, (logDeriv Gammaℝ (((2 : ℝ) : ℂ) + (y : ℂ) * I)).re
      = ∫ y in T0..T1, (-(Real.log Real.pi) / 2
          + (1 / 2 : ℝ) * (Complex.digamma (((1 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I)).re) :=
    intervalIntegral.integral_congr (fun y _ => re_logDeriv_gammaR_two y)
  rw [hcongr, intervalIntegral.integral_add intervalIntegrable_const
    ((continuous_half_re_digamma (x := 1) (by norm_num)).intervalIntegrable _ _),
    intervalIntegral.integral_const, integral_half_re_digamma (x := 1) (by norm_num), smul_eq_mul]
  ring

/-- **σ = -1 edge, exact** (every `T0`, `T1`):
    `argChangeVert Γℝ (-1) T0 T1 = (Λ(1/2, T1/2) + arctan T1 - (T1/2) log π)
                                  - (Λ(1/2, T0/2) + arctan T0 - (T0/2) log π)`. -/
theorem argChangeVert_gammaR_neg_one_eq (T0 T1 : ℝ) :
    DiffractionCore.argChangeVert Gammaℝ (-1) T0 T1
      = (gaussLam (1 / 2) (T1 / 2) + Real.arctan T1 - T1 / 2 * Real.log Real.pi)
        - (gaussLam (1 / 2) (T0 / 2) + Real.arctan T0 - T0 / 2 * Real.log Real.pi) := by
  have hInt : IntervalIntegrable (fun y : ℝ => logDeriv Gammaℝ (((-1 : ℝ) : ℂ) + (y : ℂ) * I))
      MeasureTheory.volume T0 T1 := continuous_logDeriv_gammaR_neg_one.intervalIntegrable _ _
  have hre := intervalIntegral.intervalIntegral_re (𝕜 := ℂ) hInt
  simp only [RCLike.re_to_complex] at hre
  unfold DiffractionCore.argChangeVert
  rw [← hre]
  have hcongr : ∫ y in T0..T1, (logDeriv Gammaℝ (((-1 : ℝ) : ℂ) + (y : ℂ) * I)).re
      = ∫ y in T0..T1, ((-(Real.log Real.pi) / 2
          + (1 / 2 : ℝ) * (Complex.digamma (((1 / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I)).re)
          + 1 / (1 + y ^ 2)) :=
    intervalIntegral.integral_congr (fun y _ => re_logDeriv_gammaR_neg_one y)
  have hc1 : IntervalIntegrable (fun y : ℝ => -(Real.log Real.pi) / 2
      + (1 / 2 : ℝ) * (Complex.digamma (((1 / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I)).re)
      MeasureTheory.volume T0 T1 :=
    (continuous_const.add (continuous_half_re_digamma (x := 1 / 2) (by norm_num))).intervalIntegrable _ _
  have hc2 : IntervalIntegrable (fun y : ℝ => 1 / (1 + y ^ 2)) MeasureTheory.volume T0 T1 := by
    refine Continuous.intervalIntegrable ?_ _ _
    exact Continuous.div continuous_const (by fun_prop) (fun y => by positivity)
  rw [hcongr, intervalIntegral.integral_add hc1 hc2,
    intervalIntegral.integral_add intervalIntegrable_const
      ((continuous_half_re_digamma (x := 1 / 2) (by norm_num)).intervalIntegrable _ _),
    intervalIntegral.integral_const, integral_half_re_digamma (x := 1 / 2) (by norm_num),
    integral_one_div_one_add_sq, smul_eq_mul]
  ring

/-! ## 5. The hypothesis-free enclosures (K6b) -/

/-- The σ = 2 Γℝ phase main term at base index `n0`: `lamC 1 (T/2) n0 - (T/2) log π`. -/
noncomputable def phase2 (n0 : ℕ) (T : ℝ) : ℝ := lamC 1 (T / 2) n0 - T / 2 * Real.log Real.pi

/-- The σ = -1 Γℝ phase main term at base index `n0`:
    `lamC (1/2) (T/2) n0 + arctan T - (T/2) log π`. -/
noncomputable def phaseM1 (n0 : ℕ) (T : ℝ) : ℝ :=
  lamC (1 / 2) (T / 2) n0 + Real.arctan T - T / 2 * Real.log Real.pi

/-- **K6b, σ = 2, any base index `n0`** (every `0 ≤ T0`, `0 ≤ T1`), exact `hAG2` binder form. -/
theorem hAG2_mem (n0 : ℕ) {T0 T1 : ℝ} (h0 : 0 ≤ T0) (h1 : 0 ≤ T1) :
    DiffractionCore.argChangeVert Gammaℝ 2 T0 T1
      ∈ Set.Icc (phase2 n0 T1 - lamE 1 (T1 / 2) n0 - phase2 n0 T0)
          (phase2 n0 T1 - phase2 n0 T0 + lamE 1 (T0 / 2) n0) := by
  rw [argChangeVert_gammaR_two_eq]
  have hb1 := gaussLam_mem (x := 1) (y := T1 / 2) (by norm_num) (by linarith) n0
  have hb0 := gaussLam_mem (x := 1) (y := T0 / 2) (by norm_num) (by linarith) n0
  unfold phase2
  constructor <;> linarith [hb1.1, hb1.2, hb0.1, hb0.2]

/-- **K6b, σ = -1, any base index `n0`** (every `0 ≤ T0`, `0 ≤ T1`), exact `hAG1` binder form. -/
theorem hAG1_mem (n0 : ℕ) {T0 T1 : ℝ} (h0 : 0 ≤ T0) (h1 : 0 ≤ T1) :
    DiffractionCore.argChangeVert Gammaℝ (-1) T0 T1
      ∈ Set.Icc (phaseM1 n0 T1 - lamE (1 / 2) (T1 / 2) n0 - phaseM1 n0 T0)
          (phaseM1 n0 T1 - phaseM1 n0 T0 + lamE (1 / 2) (T0 / 2) n0) := by
  rw [argChangeVert_gammaR_neg_one_eq]
  have hb1 := gaussLam_mem (x := 1 / 2) (y := T1 / 2) (by norm_num) (by linarith) n0
  have hb0 := gaussLam_mem (x := 1 / 2) (y := T0 / 2) (by norm_num) (by linarith) n0
  unfold phaseM1
  constructor <;> linarith [hb1.1, hb1.2, hb0.1, hb0.2]

/-- The closed-form σ = 2 phase (`n0 = 0`):
    `S2 T = (1/2) arctan (T/2) + (T/4) log (1 + T²/4) - T/2 - (T/2) log π`. -/
noncomputable def S2 (T : ℝ) : ℝ :=
  1 / 2 * Real.arctan (T / 2) + T / 4 * Real.log (1 + T ^ 2 / 4) - T / 2
    - T / 2 * Real.log Real.pi

/-- The closed-form σ = -1 phase (`n0 = 0`):
    `Sm1 T = (T/4) log (1/4 + T²/4) + arctan T - T/2 - (T/2) log π`. -/
noncomputable def Sm1 (T : ℝ) : ℝ :=
  T / 4 * Real.log (1 / 4 + T ^ 2 / 4) + Real.arctan T - T / 2 - T / 2 * Real.log Real.pi

/-- The σ = 2 edge error (`n0 = 0`): `e2 T = T/(2(4 + T²))`. -/
noncomputable def e2 (T : ℝ) : ℝ := T / (2 * (4 + T ^ 2))

/-- The σ = -1 edge error (`n0 = 0`): `em1 T = T/(2(1 + T²))`. -/
noncomputable def em1 (T : ℝ) : ℝ := T / (2 * (1 + T ^ 2))

theorem phase2_zero (T : ℝ) : phase2 0 T = S2 T := by
  unfold phase2 lamC S2 FA fA
  simp only [Nat.cast_zero, add_zero, zero_add, Finset.range_one, Finset.sum_singleton, div_one]
  have h : (1 : ℝ) ^ 2 + (T / 2) ^ 2 = 1 + T ^ 2 / 4 := by ring
  rw [h]
  ring

theorem phaseM1_zero (T : ℝ) : phaseM1 0 T = Sm1 T := by
  unfold phaseM1 lamC Sm1 FA fA
  simp only [Nat.cast_zero, add_zero, zero_add, Finset.range_one, Finset.sum_singleton]
  have h : (1 / 2 : ℝ) ^ 2 + (T / 2) ^ 2 = 1 / 4 + T ^ 2 / 4 := by ring
  rw [h]
  ring

theorem lamE_one_zero (T : ℝ) : lamE 1 (T / 2) 0 = e2 T := by
  unfold lamE e2
  simp only [Nat.cast_zero, add_zero]
  rw [div_div]
  congr 1
  ring

theorem lamE_half_zero (T : ℝ) : lamE (1 / 2) (T / 2) 0 = em1 T := by
  unfold lamE em1
  simp only [Nat.cast_zero, add_zero]
  rw [div_div]
  congr 1
  ring

/-- **K6b, σ = 2, closed form, exact `hAG2` binder form** (hypothesis-free, every `0 ≤ T0`,
    `0 ≤ T1`): `argChangeVert Γℝ 2 T0 T1 ∈ [S2 T1 - S2 T0 - e2 T1, S2 T1 - S2 T0 + e2 T0]`. -/
theorem hAG2_closed {T0 T1 : ℝ} (h0 : 0 ≤ T0) (h1 : 0 ≤ T1) :
    DiffractionCore.argChangeVert Gammaℝ 2 T0 T1
      ∈ Set.Icc (S2 T1 - S2 T0 - e2 T1) (S2 T1 - S2 T0 + e2 T0) := by
  have h := hAG2_mem 0 h0 h1
  rw [phase2_zero, phase2_zero, lamE_one_zero, lamE_one_zero] at h
  exact ⟨by linarith [h.1], h.2⟩

/-- **K6b, σ = -1, closed form, exact `hAG1` binder form** (hypothesis-free, every `0 ≤ T0`,
    `0 ≤ T1`): `argChangeVert Γℝ (-1) T0 T1 ∈ [Sm1 T1 - Sm1 T0 - em1 T1, Sm1 T1 - Sm1 T0 + em1 T0]`. -/
theorem hAG1_closed {T0 T1 : ℝ} (h0 : 0 ≤ T0) (h1 : 0 ≤ T1) :
    DiffractionCore.argChangeVert Gammaℝ (-1) T0 T1
      ∈ Set.Icc (Sm1 T1 - Sm1 T0 - em1 T1) (Sm1 T1 - Sm1 T0 + em1 T0) := by
  have h := hAG1_mem 0 h0 h1
  rw [phaseM1_zero, phaseM1_zero, lamE_half_zero, lamE_half_zero] at h
  exact ⟨by linarith [h.1], h.2⟩

/-- `hAG2` for any enclosure `[L5, H5]` containing the closed-form bracket (the shape a band
    emitter discharges with rational bounds on the logs and arctans at its two edges). -/
theorem hAG2_of_bounds {T0 T1 L5 H5 : ℝ} (h0 : 0 ≤ T0) (h1 : 0 ≤ T1)
    (hL : L5 ≤ S2 T1 - S2 T0 - e2 T1) (hH : S2 T1 - S2 T0 + e2 T0 ≤ H5) :
    DiffractionCore.argChangeVert Gammaℝ 2 T0 T1 ∈ Set.Icc L5 H5 := by
  have h := hAG2_closed h0 h1
  exact ⟨le_trans hL h.1, le_trans h.2 hH⟩

/-- `hAG1` for any enclosure `[L4, H4]` containing the closed-form bracket. -/
theorem hAG1_of_bounds {T0 T1 L4 H4 : ℝ} (h0 : 0 ≤ T0) (h1 : 0 ≤ T1)
    (hL : L4 ≤ Sm1 T1 - Sm1 T0 - em1 T1) (hH : Sm1 T1 - Sm1 T0 + em1 T0 ≤ H4) :
    DiffractionCore.argChangeVert Gammaℝ (-1) T0 T1 ∈ Set.Icc L4 H4 := by
  have h := hAG1_closed h0 h1
  exact ⟨le_trans hL h.1, le_trans h.2 hH⟩

/-! ## 6. Rational instantiation helpers (for band emitters) -/

/-- `S2 T` from bounds on its three transcendental ingredients (`T ≥ 0`). -/
theorem S2_mem_of {T lv hv la ha lp hp : ℝ} (hT : 0 ≤ T)
    (hlog : lv ≤ Real.log (1 + T ^ 2 / 4) ∧ Real.log (1 + T ^ 2 / 4) ≤ hv)
    (hat : la ≤ Real.arctan (T / 2) ∧ Real.arctan (T / 2) ≤ ha)
    (hpi : lp ≤ Real.log Real.pi ∧ Real.log Real.pi ≤ hp) :
    1 / 2 * la + T / 4 * lv - T / 2 - T / 2 * hp ≤ S2 T ∧
      S2 T ≤ 1 / 2 * ha + T / 4 * hv - T / 2 - T / 2 * lp := by
  unfold S2
  have h4 : 0 ≤ T / 4 := by positivity
  have h2 : 0 ≤ T / 2 := by positivity
  have a1 := mul_le_mul_of_nonneg_left hlog.1 h4
  have a2 := mul_le_mul_of_nonneg_left hlog.2 h4
  have b1 := mul_le_mul_of_nonneg_left hpi.1 h2
  have b2 := mul_le_mul_of_nonneg_left hpi.2 h2
  constructor <;> linarith [hat.1, hat.2]

/-- `Sm1 T` from bounds on its three transcendental ingredients (`T ≥ 0`). -/
theorem Sm1_mem_of {T lv hv la ha lp hp : ℝ} (hT : 0 ≤ T)
    (hlog : lv ≤ Real.log (1 / 4 + T ^ 2 / 4) ∧ Real.log (1 / 4 + T ^ 2 / 4) ≤ hv)
    (hat : la ≤ Real.arctan T ∧ Real.arctan T ≤ ha)
    (hpi : lp ≤ Real.log Real.pi ∧ Real.log Real.pi ≤ hp) :
    T / 4 * lv + la - T / 2 - T / 2 * hp ≤ Sm1 T ∧
      Sm1 T ≤ T / 4 * hv + ha - T / 2 - T / 2 * lp := by
  unfold Sm1
  have h4 : 0 ≤ T / 4 := by positivity
  have h2 : 0 ≤ T / 2 := by positivity
  have a1 := mul_le_mul_of_nonneg_left hlog.1 h4
  have a2 := mul_le_mul_of_nonneg_left hlog.2 h4
  have b1 := mul_le_mul_of_nonneg_left hpi.1 h2
  have b2 := mul_le_mul_of_nonneg_left hpi.2 h2
  constructor <;> linarith [hat.1, hat.2]

/-- `arctan y` for large `y > 0`: `π/2 - 1/y ≤ arctan y ≤ π/2 - 1/y + (1/y)³/3`, with rational
    bounds `pl ≤ π ≤ ph`. -/
theorem arctan_mem_large {y pl ph : ℝ} (hy : 0 < y) (hpl : pl ≤ Real.pi) (hph : Real.pi ≤ ph) :
    pl / 2 - 1 / y ≤ Real.arctan y ∧ Real.arctan y ≤ ph / 2 - 1 / y + (1 / y) ^ 3 / 3 := by
  have hinv := Real.arctan_inv_of_pos hy
  have hu : 0 ≤ 1 / y := by positivity
  have h1 := ArctanTaylor.arctan_le_self hu
  have h2 := ArctanTaylor.self_sub_cube_le_arctan hu
  rw [inv_eq_one_div] at hinv
  constructor <;> linarith

/-- The Taylor bracket of `log (1 - x)` (Mathlib's `Real.abs_log_sub_add_sum_range_le`). -/
theorem log_one_sub_mem {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    -(∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) - x ^ (n + 1) / (1 - x) ≤ Real.log (1 - x) ∧
      Real.log (1 - x) ≤ -(∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) + x ^ (n + 1) / (1 - x) := by
  have hx : |x| < 1 := by rw [abs_of_nonneg hx0]; exact hx1
  have h := Real.abs_log_sub_add_sum_range_le hx n
  rw [abs_of_nonneg hx0, abs_le] at h
  constructor <;> linarith [h.1, h.2]

end ArgGammaR
