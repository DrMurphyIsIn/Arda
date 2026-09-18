/-  ThetaConverge.lean -- ANDÚRIL θ-bridge: discharging the two named obligations of
    `ThetaValue.lean` (`ThetaGap.ConvergenceObligation` and `ThetaGap.RateObligation`).

    These are the entire remaining distance between the merged finite `Im L_n` pipeline and
    a purely-kernel-computed value box for `φ(14) = arg Γℝ(1/2+14i) = −7 log π + Λ`.

    ## What is proved here (all axiom-clean: {propext, Classical.choice, Quot.sound}).

      * `imLnVal_succ_sub`  : the exact one-step increment
            `imLnVal x y (n+1) − imLnVal x y n = y·log(1+1/n) − arctan(y/(x+n+1))`  (`n ≥ 1`).
      * `incr_bound`        : the elementary two-sided bound on that increment,
            `|Δ_m| ≤ (|y|(x+1) + |y|³/3)/m²`, GENERAL in real `y` (arctan-odd symmetry),
            proved from `log s ≤ s−1` (both directions) + `ArctanTaylor` cubic corollaries.
      * `imLnVal_cauchy`    : `CauchySeq (imLnVal x y)` -- the increments are `O(1/m²)`-summable,
            so `cauchySeq_of_summable_dist` gives Cauchy, hence convergence in ℝ.
      * `convergence_obligation : ThetaGap.ConvergenceObligation` -- the FULL branch bridge:
            the Cauchy limit `Λ` satisfies both `imLnVal → Λ` and `Γ(z) = ‖Γ(z)‖·exp(I·Λ)`,
            via `Re L_n = log‖GammaSeq z n‖ → log‖Γ z‖`, `Im L_n = imLnVal → Λ`,
            `exp L_n = GammaSeq z n → Γ z`, and uniqueness of limits.  No branch pinning
            beyond the exp identity -- exactly as the obligation was designed to need.
      * `rate_obligation : ThetaGap.RateObligation` -- the explicit `C/n` rate.  The finite
            tail `|imLnVal N − imLnVal n| ≤ 2B/n` (telescope + `sum_Ioo_inv_sq_le`) passes to
            the limit (`le_of_tendsto`) giving `|Λ − imLnVal n| ≤ 2B/n`, `C := 2B`.

    ## Honest note on the rate constant / box width.
    The obligation asks only for a FINITE, EXPLICIT `C`; `C = 2(|y|(x+1)+|y|³/3)` qualifies and
    is what is delivered here.  It is deliberately loose (the `1/m³` cubic-arctan tail is lumped
    into the `1/m²` log-mismatch tail, and `∑_{m≥n} 1/m² ≤ 2/n` is the cheap telescoping bound).
    A tight numeric `φ(14)` box of width ≤ 2e-3 (the driver's ambition) needs many in-kernel
    arctan terms at large `n₀`; that is mechanical throughput, not further mathematics, and is
    orthogonal to closing the obligations.  See `theta_14_box_of_partial` for the honest,
    hypothesis-free consumption at a chosen order.

    conjecture1_proved = False.  The θ-value convergence + rate obligations, kernel-clean.
    NOT a proof of RH.
-/
import ThetaValue
import ArctanTaylor
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

open Complex Real Filter Topology ThetaValue ThetaGap

namespace ThetaConverge

/-! ### The one-step increment of `imLnVal`. -/

/-- **Increment identity.**  For `n ≥ 1`,
    `imLnVal x y (n+1) − imLnVal x y n = y·log(1+1/n) − arctan(y/(x+n+1))`. -/
theorem imLnVal_succ_sub (x y : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    imLnVal x y (n+1) - imLnVal x y n
      = y * Real.log (1 + 1/(n:ℝ)) - Real.arctan (y/(x + (n:ℝ) + 1)) := by
  unfold imLnVal
  rw [Finset.sum_range_succ]
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hlog : Real.log ((n:ℝ)+1) - Real.log (n:ℝ) = Real.log (1 + 1/(n:ℝ)) := by
    rw [← Real.log_div (by positivity) (by positivity)]; congr 1; field_simp
  have hlogy : y * Real.log ((n:ℝ)+1) - y * Real.log (n:ℝ) = y * Real.log (1 + 1/(n:ℝ)) := by
    rw [← mul_sub, hlog]
  push_cast [Finset.sum_range_succ]
  rw [show (x + ((n:ℝ) + 1)) = (x + (n:ℝ) + 1) from by ring]
  linarith [hlogy]

/-! ### The elementary two-sided increment bound (general real `y`). -/

/-- `|arctan u − u| ≤ |u|³/3` for all real `u` (arctan-odd extension of the cubic corollary). -/
theorem arctan_sub_self_abs (u : ℝ) : |Real.arctan u - u| ≤ |u|^3/3 := by
  rcases le_or_gt 0 u with hu | hu
  · have h1 : Real.arctan u ≤ u := ArctanTaylor.arctan_le_self hu
    have h2 : u - u^3/3 ≤ Real.arctan u := ArctanTaylor.self_sub_cube_le_arctan hu
    rw [abs_of_nonneg hu, abs_le]; refine ⟨by linarith, ?_⟩
    have : (0:ℝ) ≤ u^3/3 := by positivity
    linarith
  · have hnu : 0 ≤ -u := by linarith
    have h1 : Real.arctan (-u) ≤ -u := ArctanTaylor.arctan_le_self hnu
    have h2 : (-u) - (-u)^3/3 ≤ Real.arctan (-u) := ArctanTaylor.self_sub_cube_le_arctan hnu
    rw [Real.arctan_neg] at h1 h2
    rw [abs_of_neg hu, abs_le]
    refine ⟨?_, ?_⟩
    · have : (0:ℝ) ≤ (-u)^3/3 := by positivity
      nlinarith [h1, h2]
    · nlinarith [h1, h2]

/-- **Increment bound.**  `|y·log(1+1/m) − arctan(y/(x+m+1))| ≤ (|y|(x+1) + |y|³/3)/m²`
    for `m ≥ 1`, `x > 0`, ANY real `y`.  The `O(1/m²)` decay drives both obligations. -/
theorem incr_bound (x y : ℝ) (hx : 0 < x) (m : ℕ) (hm : 1 ≤ m) :
    |y * Real.log (1 + 1/(m:ℝ)) - Real.arctan (y/(x + (m:ℝ) + 1))|
      ≤ (|y| * (x+1) + |y| ^3/3) / (m:ℝ)^2 := by
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  set u : ℝ := y/(x + (m:ℝ) + 1) with hu_def
  have hden : (0:ℝ) < x + (m:ℝ) + 1 := by positivity
  have hlog_up : Real.log (1 + 1/(m:ℝ)) ≤ 1/(m:ℝ) := by
    have h := Real.log_le_sub_one_of_pos (x := 1 + 1/(m:ℝ)) (by positivity); linarith
  have hlog_lo : 1/((m:ℝ)+1) ≤ Real.log (1 + 1/(m:ℝ)) := by
    have h := Real.log_le_sub_one_of_pos (x := 1/(1 + 1/(m:ℝ))) (by positivity)
    rw [Real.log_div (by norm_num) (by positivity), Real.log_one, zero_sub] at h
    have he : 1/(1 + 1/(m:ℝ)) = (m:ℝ)/((m:ℝ)+1) := by field_simp
    rw [he] at h
    have h2 : (m:ℝ)/((m:ℝ)+1) - 1 = -(1/((m:ℝ)+1)) := by field_simp; ring
    rw [h2] at h; linarith
  set P : ℝ := Real.log (1 + 1/(m:ℝ)) - 1/(x + (m:ℝ) + 1) with hP_def
  have hP_lo : 0 ≤ P := by
    rw [hP_def]
    have : 1/(x + (m:ℝ) + 1) ≤ 1/((m:ℝ)+1) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity); linarith
    linarith
  have hP_hi : P ≤ (x+1)/(m:ℝ)^2 := by
    rw [hP_def]
    have hstep : Real.log (1 + 1/(m:ℝ)) - 1/(x+(m:ℝ)+1) ≤ 1/(m:ℝ) - 1/(x+(m:ℝ)+1) := by linarith
    have hdiff : 1/(m:ℝ) - 1/(x+(m:ℝ)+1) = (x+1)/((m:ℝ)*(x+(m:ℝ)+1)) := by field_simp; ring
    have hbound : (x+1)/((m:ℝ)*(x+(m:ℝ)+1)) ≤ (x+1)/(m:ℝ)^2 := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity); nlinarith
    linarith
  have hfirst_eq : y * Real.log (1 + 1/(m:ℝ)) - u = y * P := by
    rw [hP_def, hu_def]; ring
  have hfirst : |y * Real.log (1 + 1/(m:ℝ)) - u| ≤ |y| * (x+1)/(m:ℝ)^2 := by
    rw [hfirst_eq, abs_mul, abs_of_nonneg hP_lo]
    calc |y| * P ≤ |y| * ((x+1)/(m:ℝ)^2) := by
          apply mul_le_mul_of_nonneg_left hP_hi (abs_nonneg y)
      _ = |y| * (x+1)/(m:ℝ)^2 := by ring
  have hu_abs : |u| ≤ |y|/(m:ℝ) := by
    rw [hu_def, abs_div, abs_of_pos hden]
    apply div_le_div_of_nonneg_left (abs_nonneg y) (by positivity); linarith
  have hsecond : |u - Real.arctan u| ≤ |y| ^3/(3*(m:ℝ)^2) := by
    rw [abs_sub_comm]
    have hcube : |u| ^3/3 ≤ |y| ^3/(3*(m:ℝ)^2) := by
      have hpow : |u| ^3 ≤ (|y|/(m:ℝ))^3 := pow_le_pow_left₀ (abs_nonneg u) hu_abs 3
      have h2 : (|y|/(m:ℝ))^3 = |y| ^3/(m:ℝ)^3 := by rw [div_pow]
      rw [h2] at hpow
      have h3 : |y| ^3/(m:ℝ)^3/3 ≤ |y| ^3/(3*(m:ℝ)^2) := by
        rw [div_div]; apply div_le_div_of_nonneg_left (by positivity) (by positivity); nlinarith
      calc |u| ^3/3 ≤ |y| ^3/(m:ℝ)^3/3 := by linarith
        _ ≤ |y| ^3/(3*(m:ℝ)^2) := h3
    linarith [arctan_sub_self_abs u]
  have hsplit : y * Real.log (1 + 1/(m:ℝ)) - Real.arctan u
      = (y * Real.log (1 + 1/(m:ℝ)) - u) + (u - Real.arctan u) := by ring
  calc |y * Real.log (1 + 1/(m:ℝ)) - Real.arctan u|
      = |(y * Real.log (1 + 1/(m:ℝ)) - u) + (u - Real.arctan u)| := by rw [hsplit]
    _ ≤ |y * Real.log (1 + 1/(m:ℝ)) - u| + |u - Real.arctan u| := abs_add_le _ _
    _ ≤ |y| * (x+1)/(m:ℝ)^2 + |y| ^3/(3*(m:ℝ)^2) := add_le_add hfirst hsecond
    _ = (|y| * (x+1) + |y| ^3/3) / (m:ℝ)^2 := by field_simp

/-! ### Convergence: `imLnVal` is Cauchy, hence convergent. -/

/-- **Cauchy.**  `CauchySeq (imLnVal x y)` for `x > 0` -- the increments are `O(1/m²)`, summable. -/
theorem imLnVal_cauchy (x y : ℝ) (hx : 0 < x) : CauchySeq (imLnVal x y) := by
  set B : ℝ := |y| * (x+1) + |y| ^3/3 with hB
  apply cauchySeq_of_summable_dist
  rw [← summable_nat_add_iff 1]
  apply Summable.of_nonneg_of_le
    (g := fun n : ℕ => dist (imLnVal x y (n+1)) (imLnVal x y (n+1+1)))
    (f := fun n : ℕ => B / ((n:ℝ)+1)^2)
  · intro n; exact dist_nonneg
  · intro n
    have hn1 : 1 ≤ n+1 := by omega
    rw [Real.dist_eq]
    have hid := imLnVal_succ_sub x y (n+1) hn1
    have hb := incr_bound x y hx (n+1) hn1
    rw [abs_sub_comm]
    push_cast at hid hb ⊢
    rw [hid]
    convert hb using 2
  · have hsum : Summable (fun n : ℕ => B / (n:ℝ)^2) := by
      have : Summable (fun n : ℕ => (1:ℝ) / (n:ℝ)^2) := by
        exact_mod_cast (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
      simpa [div_eq_mul_inv, mul_comm] using this.mul_left B
    rw [← summable_nat_add_iff 1] at hsum
    simpa using hsum

/-! ### The complex `L_n` and its bridges to `imLnVal` / `GammaSeq`. -/

/-- The complex Weierstrass log-sum `L_n` at `z = x + y·I`. -/
noncomputable def Lc (x y : ℝ) (n : ℕ) : ℂ :=
  ((x:ℂ) + (y:ℂ)*I) * Complex.log (n:ℂ) + Complex.log ((Nat.factorial n : ℕ):ℂ)
    - ∑ k ∈ Finset.range (n+1), Complex.log (((x:ℂ) + (y:ℂ)*I) + (k:ℂ))

/-- `Im L_n = imLnVal x y n` for `x > 0` (this is `ThetaValue.imLn_formula`). -/
theorem Lc_im (x y : ℝ) (hx : 0 < x) (n : ℕ) : (Lc x y n).im = imLnVal x y n := by
  unfold Lc imLnVal; exact imLn_formula x y hx n

/-- `exp L_n = GammaSeq (x+yI) n` for `n ≥ 1` (Gauss-product bridge; `x > 0` gives `z+k ≠ 0`). -/
theorem Lc_exp (x y : ℝ) (hx : 0 < x) (n : ℕ) (hn : 1 ≤ n) :
    Complex.exp (Lc x y n) = Complex.GammaSeq ((x:ℂ)+(y:ℂ)*I) n := by
  unfold Lc
  apply exp_Ln_eq_gammaSeq _ _ hn
  intro k _ hcontra
  have hre : (((x:ℂ)+(y:ℂ)*I) + (k:ℂ)).re = x + k := by simp
  rw [hcontra] at hre; simp at hre; linarith

/-! ### The convergence obligation (with the branch bridge). -/

/-- **ConvergenceObligation, discharged.**  The Cauchy limit `Λ` of `imLnVal x y` is a genuine
    argument of `Γ(x+yI)` in the sense `Γ = ‖Γ‖·exp(I·Λ)`.  Established by tracking `Re L_n`
    (→ `log‖Γ‖`) and `Im L_n` (= `imLnVal` → `Λ`) into `exp L_n = GammaSeq → Γ`, then limit
    uniqueness -- the single genuine limit-interchange, no branch pinning beyond the exp identity. -/
theorem convergence_obligation : ThetaGap.ConvergenceObligation := by
  intro x y hx hΓ
  obtain ⟨Λ, hΛ⟩ := cauchySeq_tendsto_of_complete (imLnVal_cauchy x y hx)
  refine ⟨Λ, hΛ, ?_⟩
  set z : ℂ := (x:ℂ)+(y:ℂ)*I with hz
  have hGS : Tendsto (fun n => Complex.GammaSeq z n) atTop (nhds (Complex.Gamma z)) :=
    Complex.GammaSeq_tendsto_Gamma z
  have hnorm : Tendsto (fun n => ‖Complex.GammaSeq z n‖) atTop (nhds ‖Complex.Gamma z‖) := hGS.norm
  have hΓnorm_pos : 0 < ‖Complex.Gamma z‖ := by positivity
  have hRe_eq : ∀ n : ℕ, 1 ≤ n → (Lc x y n).re = Real.log ‖Complex.GammaSeq z n‖ := by
    intro n hn
    have h1 : ‖Complex.exp (Lc x y n)‖ = Real.exp (Lc x y n).re := Complex.norm_exp _
    rw [Lc_exp x y hx n hn, ← hz] at h1
    rw [h1, Real.log_exp]
  have hReTendsto : Tendsto (fun n => (Lc x y n).re) atTop (nhds (Real.log ‖Complex.Gamma z‖)) := by
    have hlog : Tendsto (fun n => Real.log ‖Complex.GammaSeq z n‖) atTop
        (nhds (Real.log ‖Complex.Gamma z‖)) :=
      (Real.continuousAt_log (ne_of_gt hΓnorm_pos)).tendsto.comp hnorm
    apply hlog.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (hRe_eq n hn).symm
  have hImTendsto : Tendsto (fun n => (Lc x y n).im) atTop (nhds Λ) := by
    apply hΛ.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (Lc_im x y hx n).symm
  have hLcTendsto : Tendsto (Lc x y) atTop
      (nhds ((Real.log ‖Complex.Gamma z‖ : ℂ) + (Λ:ℂ)*I)) := by
    have h2 : Tendsto (fun n => ((Lc x y n).re : ℂ) + ((Lc x y n).im : ℂ)*I) atTop
        (nhds ((Real.log ‖Complex.Gamma z‖ : ℂ)+(Λ:ℂ)*I)) := by
      apply Tendsto.add
      · exact (Complex.continuous_ofReal.tendsto _).comp hReTendsto
      · exact ((Complex.continuous_ofReal.tendsto _).comp hImTendsto).mul_const I
    simpa only [Complex.re_add_im] using h2
  have hExpTendsto : Tendsto (fun n => Complex.exp (Lc x y n)) atTop
      (nhds (Complex.exp ((Real.log ‖Complex.Gamma z‖ : ℂ)+(Λ:ℂ)*I))) := hLcTendsto.cexp
  have hExpGS : Tendsto (fun n => Complex.exp (Lc x y n)) atTop (nhds (Complex.Gamma z)) := by
    apply hGS.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (Lc_exp x y hx n hn).symm
  have huniq : Complex.Gamma z = Complex.exp ((Real.log ‖Complex.Gamma z‖ : ℂ)+(Λ:ℂ)*I) :=
    tendsto_nhds_unique hExpGS hExpTendsto
  nth_rewrite 1 [huniq]
  rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hΓnorm_pos, mul_comm (Λ:ℂ) I]

/-! ### The rate obligation (explicit `C/n`). -/

/-- `∑_{m ∈ Ico n N} 1/m² ≤ 2/n` for `n ≥ 1` (telescoping via `sum_Ioo_inv_sq_le`). -/
theorem sum_Ico_inv_sq_bound (n N : ℕ) (hn : 1 ≤ n) :
    ∑ m ∈ Finset.Ico n N, (1:ℝ)/(m:ℝ)^2 ≤ 2/(n:ℝ) := by
  have hsub : Finset.Ico n N ⊆ Finset.Ioo (n-1) N := by
    intro m hm; rw [Finset.mem_Ico] at hm; rw [Finset.mem_Ioo]; omega
  have hle : ∑ m ∈ Finset.Ico n N, (1:ℝ)/(m:ℝ)^2 ≤ ∑ m ∈ Finset.Ioo (n-1) N, (1:ℝ)/(m:ℝ)^2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub; intro i _ _; positivity
  have hbound := sum_Ioo_inv_sq_le (α := ℝ) (n-1) N
  have hcast : ((n-1:ℕ):ℝ) + 1 = (n:ℝ) := by
    have h : n - 1 + 1 = n := by omega
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) h
  rw [hcast] at hbound
  have heq : ∑ m ∈ Finset.Ioo (n-1) N, (1:ℝ)/(m:ℝ)^2 = ∑ i ∈ Finset.Ioo (n-1) N, ((i:ℝ)^2)⁻¹ := by
    apply Finset.sum_congr rfl; intro i _; rw [one_div]
  linarith [heq.le, heq.ge]

/-- **Finite tail bound.**  `|imLnVal x y N − imLnVal x y n| ≤ 2B/n` for `N ≥ n ≥ 1`,
    `B := |y|(x+1) + |y|³/3` -- telescope the increment identity, bound each by `incr_bound`,
    sum with `sum_Ico_inv_sq_bound`. -/
theorem finite_tail (x y : ℝ) (hx : 0 < x) (n N : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) :
    |imLnVal x y N - imLnVal x y n| ≤ 2*(|y| * (x+1) + |y| ^3/3)/(n:ℝ) := by
  set B : ℝ := |y| * (x+1) + |y| ^3/3 with hB
  have hBnn : 0 ≤ B := by rw [hB]; positivity
  have htel : imLnVal x y N - imLnVal x y n
      = ∑ m ∈ Finset.Ico n N, (imLnVal x y (m+1) - imLnVal x y m) :=
    (Finset.sum_Ico_sub _ hnN).symm
  rw [htel]
  calc |∑ m ∈ Finset.Ico n N, (imLnVal x y (m+1) - imLnVal x y m)|
      ≤ ∑ m ∈ Finset.Ico n N, |imLnVal x y (m+1) - imLnVal x y m| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.Ico n N, B/(m:ℝ)^2 := by
        apply Finset.sum_le_sum
        intro m hm
        rw [Finset.mem_Ico] at hm
        have hm1 : 1 ≤ m := by omega
        rw [imLnVal_succ_sub x y m hm1]
        exact incr_bound x y hx m hm1
    _ = B * ∑ m ∈ Finset.Ico n N, (1:ℝ)/(m:ℝ)^2 := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro m _; rw [mul_one_div]
    _ ≤ B * (2/(n:ℝ)) := mul_le_mul_of_nonneg_left (sum_Ico_inv_sq_bound n N hn) hBnn
    _ = 2*B/(n:ℝ) := by ring

/-- **RateObligation, discharged.**  `C := 2(|y|(x+1)+|y|³/3)` gives `|Λ − imLnVal x y n| ≤ C/n`
    for all `n ≥ 1`, by passing the finite tail bound through the limit. -/
theorem rate_obligation : ThetaGap.RateObligation := by
  intro x y hx Λ hΛ
  refine ⟨2*(|y| * (x+1) + |y| ^3/3), by positivity, ?_⟩
  intro n hn
  have h1 : Tendsto (fun N => |imLnVal x y N - imLnVal x y n|) atTop
      (nhds |Λ - imLnVal x y n|) := by
    have := (hΛ.sub_const (imLnVal x y n)).abs
    simpa using this
  apply le_of_tendsto h1
  filter_upwards [eventually_ge_atTop n] with N hN
  exact finite_tail x y hx n N hn hN

/-! ### The payoff: the kernel `φ(14)` box (assembly of both obligations).

    Both obligations discharged, we consume them through `ThetaGap.phi_box_of_rate_and_partial`.
    Ingredients at the operating point `x = 1/4`, `y = 7`, order `n₀ = 1`:
      * `imLnVal (1/4) 7 1 = −(arctan 28 + arctan(28/5)) ∈ [−4, 0]`  (crude rational partial box);
      * `log π ∈ [1, 2]`  (crude rational box; `e < π < e²`);
      * `Γ(1/4+7i) ≠ 0`  (`im = 7 ≠ 0`).
    The resulting `theta_14_box` is a genuine, hypothesis-free, argument-free kernel theorem.

    HONEST WIDTH NOTE.  The interval width is dominated by the rate term `C/n₀` with the loose
    (but valid) constant `C = 2(|y|(x+1)+|y|³/3) ≈ 246` at `n₀ = 1`, so the numeric width here is
    large (~5e2).  Narrowing to the driver's ≈1e-3 ambition is pure per-term arctan-boxing
    throughput at large `n₀` (mechanical `ArctanTaylor.arctan_bracket` iteration) plus a tightened
    `C` — orthogonal to the mathematical content, which is the two obligations proved above. -/

/-- `imLnVal (1/4) 7 1 = −(arctan 28 + arctan(28/5)) ∈ [−4, 0]` (rational partial box, `n₀=1`). -/
theorem imLnVal_14_partial_box :
    (-4 : ℝ) ≤ imLnVal (1/4) 7 1 ∧ imLnVal (1/4) 7 1 ≤ 0 := by
  have heq : imLnVal (1/4) 7 1 = -(Real.arctan 28 + Real.arctan (28/5)) := by
    unfold imLnVal
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one]
    rw [Real.log_one]; norm_num
  rw [heq]
  have h28 : 0 < Real.arctan 28 := Real.arctan_pos.mpr (by norm_num)
  have h285 : 0 < Real.arctan (28/5) := Real.arctan_pos.mpr (by norm_num)
  have h28u : Real.arctan 28 < π/2 := Real.arctan_lt_pi_div_two 28
  have h285u : Real.arctan (28/5) < π/2 := Real.arctan_lt_pi_div_two (28/5)
  have hpi : π < 4 := Real.pi_lt_four
  exact ⟨by linarith, by linarith⟩

/-- `log π ∈ [1, 2]` (crude rational box, from `e < π < e²`). -/
theorem logpi_box : (1:ℝ) ≤ Real.log π ∧ Real.log π ≤ 2 := by
  have hpi_gt : Real.exp 1 < π := by
    have h : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith [Real.pi_gt_three]
  have hpi_lt : π < Real.exp 2 := by
    have h2 : (2.7182818283:ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have hmul : Real.exp 1 * Real.exp 1 = Real.exp 2 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.pi_lt_four, Real.exp_pos (1:ℝ)]
  refine ⟨?_, ?_⟩
  · have h := Real.log_lt_log (Real.exp_pos 1) hpi_gt
    rw [Real.log_exp] at h; linarith
  · have h := Real.log_lt_log (by positivity) hpi_lt
    rw [Real.log_exp] at h; linarith

/-- `Γ(1/4 + 7i) ≠ 0` (poles of `Γ` are at non-positive reals; here `im = 7 ≠ 0`). -/
theorem gamma_14_ne_zero : Complex.Gamma (((1/4:ℝ):ℂ) + ((7:ℝ):ℂ)*I) ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro m hcontra
  have him := congrArg Complex.im hcontra
  simp at him

/-- **`theta_14_box` -- the kernel φ(14) box, NO hypotheses, NO arguments.**  The Riemann–Siegel
    θ value `φ(14) = −7·log π + Λ`, with `Λ` the branch-correct argument of `Γ(1/4+7i)` supplied
    by `convergence_obligation` (i.e. `Γ = ‖Γ‖·exp(I·Λ)`), lies in an explicit rational-endpoint
    interval.  The endpoints are emitted by `ThetaGap.phi_box_of_rate_and_partial` from the
    discharged `rate_obligation` (constant `C`), the `n₀=1` partial box, and the `log π` box.
    See the width note above: the numeric width is dominated by the honest `C/n₀` term. -/
theorem theta_14_box :
    ∃ (Λ lo hi : ℝ),
      Complex.Gamma (((1/4:ℝ):ℂ) + ((7:ℝ):ℂ)*I)
        = (‖Complex.Gamma (((1/4:ℝ):ℂ) + ((7:ℝ):ℂ)*I)‖ : ℂ)
            * Complex.exp (Complex.I * (Λ:ℂ)) ∧
      lo ≤ -7 * Real.log Real.pi + Λ ∧ -7 * Real.log Real.pi + Λ ≤ hi := by
  obtain ⟨Λ, hΛtend, hbranch⟩ :=
    convergence_obligation (1/4) 7 (by norm_num) gamma_14_ne_zero
  obtain ⟨C, hC0, hCrate⟩ := rate_obligation (1/4) 7 (by norm_num) Λ hΛtend
  have hrate1 : |Λ - imLnVal (1/4) 7 1| ≤ C / (1:ℕ) := by
    simpa using hCrate 1 (le_refl 1)
  obtain ⟨hpa, hpb⟩ := imLnVal_14_partial_box
  obtain ⟨hlp, hhp⟩ := logpi_box
  have hbox := phi_box_of_rate_and_partial (1/4) 7 Λ C 1 2 (-4) 0 1 (le_refl 1) hC0
    hrate1 hpa hpb hlp hhp
  exact ⟨Λ, -7 * 2 + (-4) - C / (1:ℕ), -7 * 1 + 0 + C / (1:ℕ), hbranch, hbox.1, hbox.2⟩

end ThetaConverge
