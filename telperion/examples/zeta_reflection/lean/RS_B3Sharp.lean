/-  RS_B3Sharp.lean -- lane RS, brick B3 SHARPENED (RSC0 Phase 2): the same C0-corrected
    Riemann-Siegel remainder as `RS_B3Bound` / `RSSeam_B3Bound`, with smaller kernel-checked constants.
    New theorems only; imports `RSSeam_B3Bound` (hence `RS_B3Bound`) read-only and edits nothing.

    ## The headlines (no `sorry`, no `native_decide`, no new axioms)

      `RSInt.rs_remainder_C0_alpha'` : for t >= 4250 (a = sqrt(t/2pi) >= 26), 0 < p = rsFrac t,
      cos(2 pi p) ≠ 0, and every phase phi with |phi - rsThetaMain t| <= 1/t,
          |2 Re(e^{i phi} rsRem t) - (-1)^(N+1) a^(-1/2) Psi(p)| <= (3/20) a^(-3/2);
      `RSInt.rs_remainder_C0'` : the same in t, <= (3/5) t^(-3/4).
      `RSSeam.rs_remainder_C0_alpha_seam'` : for t >= 509, <= (21/100) a^(-3/2);
      `RSSeam.rs_remainder_C0_seam'` : the same in t, <= (21/25) t^(-3/4).
      The old statements (2/5 and 2 at t >= 10000; 13/20 and 13/5 at t >= 509) are re-derived from
      the new ones as `*_of_sharp` corollaries at the end of the file.

    ## What is sharper than `RS_B3Bound` (same architecture, elementary steps)

      * the saddle exponent E is split as E = E1 + E2 with E1 = -2 pi i w^3/(3a) - w/(2a) EXACT and
        |E2| <= pi |w|^4/a^2 + |w|^2/(2a^2) (Mathlib's log-Taylor remainders of orders 4 and 2), and
        |e^E - 1| <= |E| + |E|^2 e^{|E|} (`norm_rsPhi_sub_one_le'`);
      * on the steepest-descent line |E1| = (sqrt2/2)|v| |1 - 8 pi v^2/3| / a EXACTLY (`rsEone_line`):
        the linear and cubic terms have OPPOSITE signs, and |1 - x| <= 41/40 - (5/4)x + (5/8)x^2;
        the main term then integrates against the FULL Gaussian e^{-4 pi v^2} to (49/120)/(2 pi a);
      * only the second-order remainder pays for e^{|E|}, with e^{-(4 pi - 37/10) v^2};
      * absolute Gaussian moments int |v|^j e^{-b v^2} = b^{-(j+1)/2} Gamma((j+1)/2) (`gaussMom_eq`);
      * one near-zone lemma (|v| <= a/3) for every a >= a0 >= 9, the far zone reused verbatim from
        `RSSeam.norm_E1_integrand_far`;
      * |rsJ p| <= 4/5 by completing the square on the midline (was 4) (`norm_rsJ_le'`).
      Budget: |rsE1| <= (7/100)/a (a >= 26) and (9/100)/a (a >= 9); phase 4/(5 pi a^2) <= (1/100)/a
      resp. (3/100)/a; 2 (7/100) + 1/100 = 3/20 and 2 (9/100) + 3/100 = 21/100; (2 pi)^(3/4) <= 4.

    The numeric lemmas bound a|rsE1| by 0.0689 (a >= 26) and 0.0821 (a >= 9).  Untrusted design
    numerics (closed forms 0.0688 and 0.0770): ~/rh-team/rsc0/out/phase2/lean_numerics.py.

    Not yet `lean_lib`s (lakefile.toml untouched): compile with `lake env lean`; a landing PR adds
    append-only `[[lean_lib]]` entries for RS_B3Sharp and RS_BridgeSharp (and RS_AxiomGuardSharp).

    conjecture1_proved = False.  An explicit finite-height remainder inequality; nothing here bears on
    the Riemann Hypothesis.
-/
import RSSeam_B3Bound

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

namespace RSInt

/-! ## 1. Absolute Gaussian moments -/

/-- `gaussMom b j = ∫ |v|^j e^{-b v^2} dv`. -/
def gaussMom (b : ℝ) (j : ℕ) : ℝ := ∫ v : ℝ, |v| ^ j * Real.exp (-b * v ^ 2)

theorem integrable_abs_pow_mul_exp {b : ℝ} (hb : 0 < b) (j : ℕ) :
    Integrable (fun v : ℝ => |v| ^ j * Real.exp (-b * v ^ 2)) := by
  have hj : (-1 : ℝ) < j := by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith
  have h := integrable_rpow_mul_exp_neg_mul_sq hb hj
  simp only [Real.rpow_natCast] at h
  refine h.abs.congr (Eventually.of_forall fun v => ?_)
  simp only [abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]

theorem gaussMom_eq {b : ℝ} (hb : 0 < b) (j : ℕ) :
    gaussMom b j = b ^ (-((j : ℝ) + 1) / 2) * Real.Gamma (((j : ℝ) + 1) / 2) := by
  unfold gaussMom
  have hj : (-1 : ℝ) < j := by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith
  have h1 : (fun v : ℝ => |v| ^ j * Real.exp (-b * v ^ 2)) =
      fun v => (fun r : ℝ => r ^ j * Real.exp (-b * r ^ 2)) |v| := by
    ext v; simp only [sq_abs]
  rw [h1, integral_comp_abs (f := fun r : ℝ => r ^ j * Real.exp (-b * r ^ 2))]
  have h2 := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := (j : ℝ)) (b := b) (by norm_num) hj hb
  have h3 : ∫ x in Ioi (0 : ℝ), (fun r : ℝ => r ^ j * Real.exp (-b * r ^ 2)) x =
      ∫ x in Ioi (0 : ℝ), x ^ (j : ℝ) * Real.exp (-b * x ^ (2 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    simp only [Real.rpow_natCast, Real.rpow_two]
  rw [h3, h2]
  ring

theorem gaussMom_odd {b : ℝ} (hb : 0 < b) (m : ℕ) :
    gaussMom b (2 * m + 1) = (m.factorial : ℝ) / b ^ (m + 1) := by
  rw [gaussMom_eq hb]
  have e1 : (((2 * m + 1 : ℕ) : ℝ) + 1) / 2 = (m : ℝ) + 1 := by push_cast; ring
  have e2 : -(((2 * m + 1 : ℕ) : ℝ) + 1) / 2 = -(((m + 1 : ℕ) : ℝ)) := by push_cast; ring
  rw [e1, e2, Real.Gamma_nat_eq_factorial, Real.rpow_neg hb.le, Real.rpow_natCast]
  field_simp

theorem gaussMom_even {b : ℝ} (hb : 0 < b) (m : ℕ) :
    gaussMom b (2 * m) = Real.Gamma ((m : ℝ) + 1 / 2) / (b ^ m * Real.sqrt b) := by
  rw [gaussMom_eq hb]
  have e1 : (((2 * m : ℕ) : ℝ) + 1) / 2 = (m : ℝ) + 1 / 2 := by push_cast; ring
  have e2 : -(((2 * m : ℕ) : ℝ) + 1) / 2 = -((m : ℝ) + 1 / 2) := by push_cast; ring
  rw [e1, e2, Real.rpow_neg hb.le, Real.rpow_add hb, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  field_simp

theorem Gamma_three_halves' : Real.Gamma (1 + 1 / 2) = Real.sqrt π / 2 := by
  rw [show (1 : ℝ) + 1 / 2 = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    Real.Gamma_one_half_eq]
  ring

theorem Gamma_five_halves' : Real.Gamma (2 + 1 / 2) = 3 * Real.sqrt π / 4 := by
  rw [show (2 : ℝ) + 1 / 2 = (1 + 1 / 2) + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    Gamma_three_halves']
  ring

theorem Gamma_seven_halves' : Real.Gamma (3 + 1 / 2) = 15 * Real.sqrt π / 8 := by
  rw [show (3 : ℝ) + 1 / 2 = (2 + 1 / 2) + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    Gamma_five_halves']
  ring

theorem gaussMom_0 (b : ℝ) : gaussMom b 0 = Real.sqrt (π / b) := by
  unfold gaussMom
  simp only [pow_zero, one_mul]
  exact integral_gaussian b

theorem gaussMom_1 {b : ℝ} (hb : 0 < b) : gaussMom b 1 = 1 / b := by
  have := gaussMom_odd hb 0
  simpa using this

theorem gaussMom_2 {b : ℝ} (hb : 0 < b) : gaussMom b 2 = Real.sqrt (π / b) / (2 * b) := by
  have h := gaussMom_even hb 1
  rw [show 2 * 1 = 2 by rfl] at h
  rw [h, Real.sqrt_div' π hb.le]
  have hG : Real.Gamma (((1 : ℕ) : ℝ) + 1 / 2) = Real.sqrt π / 2 := by
    rw [Nat.cast_one]; exact Gamma_three_halves'
  rw [hG, pow_one]
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  field_simp

theorem gaussMom_3 {b : ℝ} (hb : 0 < b) : gaussMom b 3 = 1 / b ^ 2 := by
  have := gaussMom_odd hb 1
  simpa using this

theorem gaussMom_4 {b : ℝ} (hb : 0 < b) : gaussMom b 4 = 3 * Real.sqrt (π / b) / (4 * b ^ 2) := by
  have h := gaussMom_even hb 2
  rw [show 2 * 2 = 4 by rfl] at h
  rw [h, Real.sqrt_div' π hb.le]
  have hG : Real.Gamma (((2 : ℕ) : ℝ) + 1 / 2) = 3 * Real.sqrt π / 4 := by
    rw [show ((2 : ℕ) : ℝ) = 2 by norm_num]; exact Gamma_five_halves'
  rw [hG]
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  field_simp

theorem gaussMom_5 {b : ℝ} (hb : 0 < b) : gaussMom b 5 = 2 / b ^ 3 := by
  have := gaussMom_odd hb 2
  simpa [Nat.factorial] using this

theorem gaussMom_6 {b : ℝ} (hb : 0 < b) :
    gaussMom b 6 = 15 * Real.sqrt (π / b) / (8 * b ^ 3) := by
  have h := gaussMom_even hb 3
  rw [show 2 * 3 = 6 by rfl] at h
  rw [h, Real.sqrt_div' π hb.le]
  have hG : Real.Gamma (((3 : ℕ) : ℝ) + 1 / 2) = 15 * Real.sqrt π / 8 := by
    rw [show ((3 : ℕ) : ℝ) = 3 by norm_num]; exact Gamma_seven_halves'
  rw [hG]
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  field_simp

theorem gaussMom_7 {b : ℝ} (hb : 0 < b) : gaussMom b 7 = 6 / b ^ 4 := by
  have := gaussMom_odd hb 3
  simpa [Nat.factorial] using this

/-- Integrals of polynomials in `|v|` against a Gaussian, term by term. -/
theorem integrable_poly_gauss {b : ℝ} (hb : 0 < b) (n : ℕ) (c : ℕ → ℝ) :
    Integrable (fun v : ℝ => (∑ j ∈ Finset.range n, c j * |v| ^ j) * Real.exp (-b * v ^ 2)) := by
  have e : (fun v : ℝ => (∑ j ∈ Finset.range n, c j * |v| ^ j) * Real.exp (-b * v ^ 2)) =
      fun v => ∑ j ∈ Finset.range n, c j * (|v| ^ j * Real.exp (-b * v ^ 2)) := by
    ext v; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => ?_; ring
  rw [e]
  exact integrable_finsetSum _ fun j _ => (integrable_abs_pow_mul_exp hb j).const_mul _

theorem integral_poly_gauss {b : ℝ} (hb : 0 < b) (n : ℕ) (c : ℕ → ℝ) :
    ∫ v : ℝ, (∑ j ∈ Finset.range n, c j * |v| ^ j) * Real.exp (-b * v ^ 2) =
      ∑ j ∈ Finset.range n, c j * gaussMom b j := by
  have e : (fun v : ℝ => (∑ j ∈ Finset.range n, c j * |v| ^ j) * Real.exp (-b * v ^ 2)) =
      fun v => ∑ j ∈ Finset.range n, c j * (|v| ^ j * Real.exp (-b * v ^ 2)) := by
    ext v; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => ?_; ring
  rw [e, integral_finsetSum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]; rfl
  · intro j _; exact (integrable_abs_pow_mul_exp hb j).const_mul _

/-! ## 2. The saddle exponent split into its exact linear-plus-cubic part and a remainder -/

/-- The linear-plus-cubic part of the saddle exponent, `E1(a, w) = -2 pi i w^3/(3a) - w/(2a)`. -/
def rsEone (a : ℝ) (w : ℂ) : ℂ := -(2 * ↑π * I * w ^ 3 / (3 * a)) - w / (2 * a)

theorem logTaylor_two (u : ℂ) : logTaylor 2 u = u := by
  simp [logTaylor, Finset.sum_range_succ]

theorem logTaylor_four (u : ℂ) : logTaylor 4 u = u - u ^ 2 / 2 + u ^ 3 / 3 := by
  simp [logTaylor, Finset.sum_range_succ]
  ring

/-- **The amplitude, second order.**  For `|w| <= a/2`, with `B = pi |w|^4/a^2 + |w|^2/(2a^2)`:
    `|rsPhi a w - 1| <= |E1| + B + (|E1| + B)^2 e^{|E1| + B}`. -/
theorem norm_rsPhi_sub_one_le' {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : ‖w‖ ≤ a / 2) :
    ‖rsPhi a w - 1‖ ≤ ‖rsEone a w‖ + (π * ‖w‖ ^ 4 / a ^ 2 + ‖w‖ ^ 2 / (2 * a ^ 2)) +
      (‖rsEone a w‖ + (π * ‖w‖ ^ 4 / a ^ 2 + ‖w‖ ^ 2 / (2 * a ^ 2))) ^ 2 *
        Real.exp (‖rsEone a w‖ + (π * ‖w‖ ^ 4 / a ^ 2 + ‖w‖ ^ 2 / (2 * a ^ 2))) := by
  set u : ℂ := w / a with hu
  have ha0 : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  have hnu : ‖u‖ = ‖w‖ / a := by
    rw [hu, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  have hu2 : ‖u‖ ≤ 1 / 2 := by rw [hnu, div_le_iff₀ ha]; linarith
  have hu1 : ‖u‖ < 1 := by linarith
  have hinv : (1 - ‖u‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have h1u : 1 + u ≠ 0 := by
    intro h
    have : u = -1 := by linear_combination h
    rw [this, norm_neg, norm_one] at hu1; linarith
  set B : ℝ := π * ‖w‖ ^ 4 / a ^ 2 + ‖w‖ ^ 2 / (2 * a ^ 2) with hB
  set E : ℂ := -(2 * ↑π * a ^ 2 * I) * (Complex.log (1 + u) - logTaylor 3 u) -
    1 / 2 * Complex.log (1 + u) with hE
  set E2 : ℂ := -(2 * ↑π * a ^ 2 * I) * (Complex.log (1 + u) - logTaylor 4 u) -
    1 / 2 * (Complex.log (1 + u) - logTaylor 2 u) with hE2
  have hsplit : E = rsEone a w + E2 := by
    have hw' : w = u * a := by rw [hu]; field_simp
    rw [hE, hE2, rsEone, logTaylor_four, logTaylor_three, logTaylor_two, hw']
    field_simp
    ring
  have hn : ‖(2 * ↑π * a ^ 2 * I : ℂ)‖ = 2 * π * a ^ 2 := by
    rw [norm_mul, Complex.norm_I, mul_one,
      show (2 * (π : ℂ) * (a : ℂ) ^ 2 : ℂ) = ((2 * π * a ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hE2b : ‖E2‖ ≤ B := by
    have hT4 := Complex.norm_log_sub_logTaylor_le 3 hu1
    have hT2 := Complex.norm_log_sub_logTaylor_le 1 hu1
    have hnu0 : 0 ≤ ‖u‖ := norm_nonneg _
    have e1 : ‖-(2 * ↑π * a ^ 2 * I) * (Complex.log (1 + u) - logTaylor 4 u)‖ ≤
        2 * π * a ^ 2 * (‖u‖ ^ 4 / 2) := by
      rw [norm_mul, norm_neg, hn]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc ‖Complex.log (1 + u) - logTaylor 4 u‖ ≤ ‖u‖ ^ (3 + 1) * (1 - ‖u‖)⁻¹ / (3 + 1) := by
            exact_mod_cast hT4
        _ ≤ ‖u‖ ^ 4 / 2 := by
            have : ‖u‖ ^ (3 + 1) * (1 - ‖u‖)⁻¹ ≤ ‖u‖ ^ 4 * 2 :=
              mul_le_mul_of_nonneg_left hinv (by positivity)
            norm_num at this ⊢
            linarith
    have e2 : ‖(1 / 2 : ℂ) * (Complex.log (1 + u) - logTaylor 2 u)‖ ≤ 1 / 2 * ‖u‖ ^ 2 := by
      rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by simp]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      calc ‖Complex.log (1 + u) - logTaylor 2 u‖ ≤ ‖u‖ ^ (1 + 1) * (1 - ‖u‖)⁻¹ / (1 + 1) := by
            exact_mod_cast hT2
        _ ≤ ‖u‖ ^ 2 := by
            have : ‖u‖ ^ (1 + 1) * (1 - ‖u‖)⁻¹ ≤ ‖u‖ ^ 2 * 2 :=
              mul_le_mul_of_nonneg_left hinv (by positivity)
            norm_num at this ⊢
            linarith
    calc ‖E2‖ ≤ ‖-(2 * ↑π * a ^ 2 * I) * (Complex.log (1 + u) - logTaylor 4 u)‖ +
          ‖(1 / 2 : ℂ) * (Complex.log (1 + u) - logTaylor 2 u)‖ := norm_sub_le _ _
      _ ≤ 2 * π * a ^ 2 * (‖u‖ ^ 4 / 2) + 1 / 2 * ‖u‖ ^ 2 := add_le_add e1 e2
      _ = B := by rw [hB, hnu]; field_simp
  have hEb : ‖E‖ ≤ ‖rsEone a w‖ + B := by
    rw [hsplit]; exact (norm_add_le _ _).trans (by linarith)
  have hB0 : 0 ≤ B := by positivity
  rw [rsPhi_eq_exp ha h1u, ← hE]
  have hexp := Complex.norm_exp_sub_sum_le_norm_mul_exp E 2
  have hsum : ∑ m ∈ Finset.range 2, E ^ m / (m.factorial : ℂ) = 1 + E := by
    simp [Finset.sum_range_succ]
  rw [hsum] at hexp
  have hR : ‖cexp E - (1 + E)‖ ≤ (‖rsEone a w‖ + B) ^ 2 * Real.exp (‖rsEone a w‖ + B) :=
    hexp.trans (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hEb 2) (Real.exp_le_exp.mpr hEb)
      (Real.exp_pos _).le (by positivity))
  have e : cexp E - 1 = E + (cexp E - (1 + E)) := by ring
  rw [e]
  calc ‖E + (cexp E - (1 + E))‖ ≤ ‖E‖ + ‖cexp E - (1 + E)‖ := norm_add_le _ _
    _ ≤ (‖rsEone a w‖ + B) + (‖rsEone a w‖ + B) ^ 2 * Real.exp (‖rsEone a w‖ + B) :=
        add_le_add hEb hR

/-- On the steepest-descent line `w = v(1+i)` the linear-plus-cubic part is EXACTLY
    `|E1| = (sqrt2/2) |v| |1 - 8 pi v^2/3| / a` (the two terms have opposite signs). -/
theorem rsEone_line {a : ℝ} (ha : 0 < a) (v : ℝ) :
    ‖rsEone a ((v : ℂ) * (1 + I))‖ = Real.sqrt 2 / 2 * |v| * |1 - 8 * π * v ^ 2 / 3| / a := by
  have ha0 : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  have h3 : ((v : ℂ) * (1 + I)) ^ 3 = (v : ℂ) ^ 3 * (2 * I - 2) := by
    linear_combination ((v : ℂ) ^ 3 * (3 + I)) * I_sq
  have e : rsEone a ((v : ℂ) * (1 + I)) =
      -((1 + I) * (((v / (2 * a)) * (1 - 8 * π * v ^ 2 / 3) : ℝ) : ℂ)) := by
    unfold rsEone
    rw [h3]
    push_cast
    linear_combination (-(4 * ↑π * (v : ℂ) ^ 3 / (3 * (a : ℂ)))) * I_sq
  rw [e, norm_neg, norm_mul, norm_one_add_I, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * a)]
  ring

/-! ## 3. The near-zone majorant (|v| <= a/3, every a >= a0 >= 9) -/

theorem sqrt_two_le_1415 : Real.sqrt 2 ≤ 1415 / 1000 := by
  calc Real.sqrt 2 ≤ Real.sqrt ((1415 / 1000) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
    _ = 1415 / 1000 := Real.sqrt_sq (by norm_num)

theorem sqrt_two_le_141422 : Real.sqrt 2 ≤ 141422 / 100000 := by
  calc Real.sqrt 2 ≤ Real.sqrt ((141422 / 100000) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
    _ = 141422 / 100000 := Real.sqrt_sq (by norm_num)

/-- Coefficients of `41/40 - (10 pi/3) r^2 + (40 pi^2/9) r^4`, the majorant of `|1 - 8 pi r^2/3|`. -/
def cMain (j : ℕ) : ℝ :=
  if j = 0 then 41 / 40 else if j = 2 then -(10 * π / 3) else if j = 4 then 40 * π ^ 2 / 9 else 0

/-- Coefficients of `r + 4 pi r^3` (the remainder `E2` on the line, divided by `|v| a^{-2}`). -/
def cEtwo (j : ℕ) : ℝ := if j = 1 then 1 else if j = 3 then 4 * π else 0

/-- Coefficients of `r P0(r)^2`, `P0(r) = (sqrt2/2)(1 + (8 pi/3) r^2) + (r + 4 pi r^3)/a0`. -/
def cS (a0 : ℝ) (j : ℕ) : ℝ :=
  if j = 1 then 1 / 2 else if j = 2 then Real.sqrt 2 / a0 else if j = 3 then 8 * π / 3 + 1 / a0 ^ 2
  else if j = 4 then Real.sqrt 2 / a0 * (20 * π / 3)
  else if j = 5 then 32 * π ^ 2 / 9 + 8 * π / a0 ^ 2
  else if j = 6 then Real.sqrt 2 / a0 * (32 * π ^ 2 / 3)
  else if j = 7 then 16 * π ^ 2 / a0 ^ 2 else 0

theorem sum_cMain (r : ℝ) :
    ∑ j ∈ Finset.range 5, cMain j * r ^ j = 41 / 40 - 10 * π / 3 * r ^ 2 + 40 * π ^ 2 / 9 * r ^ 4 := by
  simp [Finset.sum_range_succ, cMain]
  ring

theorem sum_cEtwo (r : ℝ) : ∑ j ∈ Finset.range 4, cEtwo j * r ^ j = r + 4 * π * r ^ 3 := by
  simp [Finset.sum_range_succ, cEtwo]

theorem sum_cS (a0 r : ℝ) :
    ∑ j ∈ Finset.range 8, cS a0 j * r ^ j =
      r * (Real.sqrt 2 / 2 * (1 + 8 * π / 3 * r ^ 2) + (r + 4 * π * r ^ 3) / a0) ^ 2 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp [Finset.sum_range_succ, cS]
  linear_combination (-(r * (1 + 8 * π / 3 * r ^ 2) ^ 2 / 4)) * hs

theorem qMain_nonneg (r : ℝ) : 0 ≤ 41 / 40 - 10 * π / 3 * r ^ 2 + 40 * π ^ 2 / 9 * r ^ 4 := by
  nlinarith [sq_nonneg (π * r ^ 2 - 3 / 8), Real.pi_pos]

theorem abs_one_sub_le_quad (x : ℝ) : |1 - x| ≤ 41 / 40 - 5 / 4 * x + 5 / 8 * x ^ 2 := by
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg (x - 1 / 5), sq_nonneg (x - 9 / 5)]

theorem amgm_sqrt_two (r q : ℝ) : Real.sqrt 2 / 2 * r * q ≤ r ^ 2 / 4 + q ^ 2 / 2 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h := sq_nonneg (r - Real.sqrt 2 * q)
  have e : (r - Real.sqrt 2 * q) ^ 2 = r ^ 2 - 2 * Real.sqrt 2 * r * q + Real.sqrt 2 ^ 2 * q ^ 2 := by
    ring
  rw [e, hs] at h
  linarith

theorem coef_le_37_10 : 1 / 4 + 4 * Real.sqrt 2 * π / 9 + (4 * π / 9 + 1 / 81) ≤ 37 / 10 := by
  have h1 := sqrt_two_le_1415
  have h2 := Real.pi_lt_d4
  have h4 : Real.sqrt 2 * π ≤ 1415 / 1000 * 3.1416 :=
    mul_le_mul h1 h2.le Real.pi_pos.le (by norm_num)
  norm_num at h2 h4 ⊢
  linarith

/-- The first-order quantity `e1 + B` (`|E1| + |E2|`-bound on the line) is `O(|v|/a)`. -/
theorem near_eta_le_lin {a0 a v : ℝ} (h9 : 9 ≤ a0) (ha : a0 ≤ a) :
    Real.sqrt 2 / 2 * |v| * |1 - 8 * π * v ^ 2 / 3| / a +
        (π * (4 * v ^ 4) / a ^ 2 + 2 * v ^ 2 / (2 * a ^ 2)) ≤
      |v| * (Real.sqrt 2 / 2 * (1 + 8 * π / 3 * |v| ^ 2) + (|v| + 4 * π * |v| ^ 3) / a0) / a := by
  have ha00 : 0 < a0 := by linarith
  have ha0 : 0 < a := by linarith
  have hX0 : 0 ≤ 8 * π * v ^ 2 / 3 := by positivity
  have h1X : |1 - 8 * π * v ^ 2 / 3| ≤ 1 + 8 * π * v ^ 2 / 3 := by
    rw [abs_le]; constructor <;> linarith
  have he1u : Real.sqrt 2 / 2 * |v| * |1 - 8 * π * v ^ 2 / 3| / a ≤
      Real.sqrt 2 / 2 * |v| * (1 + 8 * π * v ^ 2 / 3) / a := by gcongr
  have h4abs : |v| ^ 4 = v ^ 4 := by
    rw [show |v| ^ 4 = (|v| ^ 2) ^ 2 by ring, sq_abs]; ring
  have hB' : π * (4 * v ^ 4) / a ^ 2 + 2 * v ^ 2 / (2 * a ^ 2) =
      |v| * (|v| + 4 * π * |v| ^ 3) / a ^ 2 := by
    rw [show |v| * (|v| + 4 * π * |v| ^ 3) = |v| ^ 2 + 4 * π * |v| ^ 4 by ring, sq_abs, h4abs]
    field_simp
    ring
  have h2 : |v| * (|v| + 4 * π * |v| ^ 3) / a ^ 2 ≤ |v| * (|v| + 4 * π * |v| ^ 3) / (a0 * a) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    rw [sq]; exact mul_le_mul_of_nonneg_right ha ha0.le
  have e3 : |v| * (Real.sqrt 2 / 2 * (1 + 8 * π / 3 * |v| ^ 2) + (|v| + 4 * π * |v| ^ 3) / a0) / a =
      Real.sqrt 2 / 2 * |v| * (1 + 8 * π * v ^ 2 / 3) / a +
        |v| * (|v| + 4 * π * |v| ^ 3) / (a0 * a) := by
    rw [sq_abs]
    field_simp
  rw [e3, hB']
  linarith

/-- ... and at most `(37/10) v^2 + 1/(2 a0^2)` on `|v| <= a/3`, so `e^{e1+B}` costs only part of the
    Gaussian. -/
theorem near_eta_le_sq {a0 a v : ℝ} (h9 : 9 ≤ a0) (ha : a0 ≤ a) (hv : |v| ≤ a / 3) :
    Real.sqrt 2 / 2 * |v| * |1 - 8 * π * v ^ 2 / 3| / a +
        (π * (4 * v ^ 4) / a ^ 2 + 2 * v ^ 2 / (2 * a ^ 2)) ≤
      37 / 10 * v ^ 2 + 1 / (2 * a0 ^ 2) := by
  have ha00 : 0 < a0 := by linarith
  have ha0 : 0 < a := by linarith
  have ha9 : 9 ≤ a := by linarith
  have hX0 : 0 ≤ 8 * π * v ^ 2 / 3 := by positivity
  have h1X : |1 - 8 * π * v ^ 2 / 3| ≤ 1 + 8 * π * v ^ 2 / 3 := by
    rw [abs_le]; constructor <;> linarith
  have he1u : Real.sqrt 2 / 2 * |v| * |1 - 8 * π * v ^ 2 / 3| / a ≤
      Real.sqrt 2 / 2 * |v| * (1 + 8 * π * v ^ 2 / 3) / a := by gcongr
  have hra : |v| / a ≤ 1 / 3 := by rw [div_le_iff₀ ha0]; linarith
  have h1 : Real.sqrt 2 / 2 * |v| * (1 + 8 * π * v ^ 2 / 3) / a =
      Real.sqrt 2 / 2 * |v| / a + 4 * Real.sqrt 2 * π / 3 * v ^ 2 * (|v| / a) := by ring
  have h21 : Real.sqrt 2 / 2 * |v| / a ≤ Real.sqrt 2 / 2 * |v| / a0 :=
    div_le_div_of_nonneg_left (by positivity) ha00 ha
  have h22 := amgm_sqrt_two |v| (1 / a0)
  have e : Real.sqrt 2 / 2 * |v| * (1 / a0) = Real.sqrt 2 / 2 * |v| / a0 := by ring
  have e' : |v| ^ 2 / 4 + (1 / a0) ^ 2 / 2 = v ^ 2 / 4 + 1 / (2 * a0 ^ 2) := by
    rw [sq_abs]; field_simp
  rw [e, e'] at h22
  have h3 : 4 * Real.sqrt 2 * π / 3 * v ^ 2 * (|v| / a) ≤ 4 * Real.sqrt 2 * π / 3 * v ^ 2 * (1 / 3) :=
    mul_le_mul_of_nonneg_left hra (by positivity)
  have hva : v ^ 2 / a ^ 2 ≤ 1 / 9 := by
    have : (|v| / a) ^ 2 ≤ (1 / 3) ^ 2 := pow_le_pow_left₀ (by positivity) hra 2
    rw [div_pow, sq_abs] at this; linarith
  have ha81 : (81 : ℝ) ≤ a ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 9) ha9 2
    norm_num at this; linarith
  have hia : 1 / a ^ 2 ≤ 1 / 81 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have eB : π * (4 * v ^ 4) / a ^ 2 + 2 * v ^ 2 / (2 * a ^ 2) =
      v ^ 2 * (1 / a ^ 2) + 4 * π * v ^ 2 * (v ^ 2 / a ^ 2) := by
    field_simp; ring
  have k1 := mul_le_mul_of_nonneg_left hia (sq_nonneg v)
  have k2 := mul_le_mul_of_nonneg_left hva (by positivity : (0 : ℝ) ≤ 4 * π * v ^ 2)
  have k := mul_le_mul_of_nonneg_right coef_le_37_10 (sq_nonneg v)
  rw [eB]
  linarith

/-- The three algebraic identities/inequalities that assemble the pointwise bound. -/
theorem near_T1 {a r y Q G : ℝ} (ha : 0 < a) (hr : 0 < r) (hG : 0 ≤ G) (hyQ : y ≤ Q) :
    G * (Real.sqrt 2 / 2 * r * y / a) * Real.sqrt 2 / (2 * π * r) ≤ 1 / (2 * π * a) * (Q * G) := by
  have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have e : G * (Real.sqrt 2 / 2 * r * y / a) * Real.sqrt 2 / (2 * π * r) =
      1 / (2 * π * a) * (y * G) * ((Real.sqrt 2 * Real.sqrt 2) / 2) := by
    field_simp
  rw [e, hss, div_self two_ne_zero, mul_one]
  have : 0 ≤ 1 / (2 * π * a) := by positivity
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hyQ hG) this

theorem near_T2 {a v G : ℝ} (ha : 0 < a) (hv : v ≠ 0) :
    G * (π * (4 * v ^ 4) / a ^ 2 + 2 * v ^ 2 / (2 * a ^ 2)) * Real.sqrt 2 / (2 * π * |v|) =
      Real.sqrt 2 / (2 * π * a ^ 2) * ((|v| + 4 * π * |v| ^ 3) * G) := by
  have hvpos : 0 < |v| := abs_pos.mpr hv
  have h4abs : |v| ^ 4 = v ^ 4 := by
    rw [show |v| ^ 4 = (|v| ^ 2) ^ 2 by ring, sq_abs]; ring
  rw [← sq_abs v, ← h4abs]
  field_simp
  ring

theorem near_T3 {a a0 r v η P G : ℝ} (ha : 0 < a) (hr : 0 < r) (hG : 0 ≤ G) (hη0 : 0 ≤ η)
    (hη1 : η ≤ r * P / a) (hηe : Real.exp η ≤ Real.exp (1 / (2 * a0 ^ 2)) * Real.exp (37 / 10 * v ^ 2))
    (hGe : G * Real.exp (37 / 10 * v ^ 2) = Real.exp (-(4 * π - 37 / 10) * v ^ 2)) :
    G * (η ^ 2 * Real.exp η) * Real.sqrt 2 / (2 * π * r) ≤
      Real.sqrt 2 * Real.exp (1 / (2 * a0 ^ 2)) / (2 * π * a ^ 2) *
        (r * P ^ 2 * Real.exp (-(4 * π - 37 / 10) * v ^ 2)) := by
  have hsq : η ^ 2 ≤ (r * P / a) ^ 2 := pow_le_pow_left₀ hη0 hη1 2
  have hR3 : η ^ 2 * Real.exp η ≤
      (r * P / a) ^ 2 * (Real.exp (1 / (2 * a0 ^ 2)) * Real.exp (37 / 10 * v ^ 2)) :=
    mul_le_mul hsq hηe (Real.exp_pos _).le (sq_nonneg _)
  have hD : 0 < 2 * π * r := by positivity
  calc G * (η ^ 2 * Real.exp η) * Real.sqrt 2 / (2 * π * r)
      ≤ G * ((r * P / a) ^ 2 * (Real.exp (1 / (2 * a0 ^ 2)) * Real.exp (37 / 10 * v ^ 2))) *
          Real.sqrt 2 / (2 * π * r) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hR3 hG) (Real.sqrt_nonneg 2)) hD.le
    _ = Real.sqrt 2 * Real.exp (1 / (2 * a0 ^ 2)) / (2 * π * a ^ 2) *
          (r * P ^ 2 * (G * Real.exp (37 / 10 * v ^ 2))) := by
        field_simp
    _ = _ := by rw [hGe]

/-- **Pointwise bound near the saddle point, sharpened.**  For `9 <= a0 <= a` and `|v| <= a/3`:
    the integrand of `rsE1` is at most
      (1/(2 pi a)) (41/40 - (10 pi/3) v^2 + (40 pi^2/9) v^4) e^{-4 pi v^2}            (main)
    + (sqrt2/(2 pi a^2)) (|v| + 4 pi |v|^3) e^{-4 pi v^2}                               (E2)
    + (sqrt2 e^{1/(2 a0^2)}/(2 pi a^2)) |v| P0(|v|)^2 e^{-(4 pi - 37/10) v^2}           (second order),
    written as polynomials in `|v|` (`sum_cMain`, `sum_cEtwo`, `sum_cS`). -/
theorem norm_E1_integrand_near' {a0 a p v : ℝ} (h9 : 9 ≤ a0) (ha : a0 ≤ a) (hv : |v| ≤ a / 3) :
    ‖cexp (2 * ↑π * I * ((v : ℂ) * (1 + I)) ^ 2) / rsD (p + (v : ℂ) * (1 + I)) *
        (rsPhi a ((v : ℂ) * (1 + I)) - 1) * (1 + I)‖ ≤
      1 / (2 * π * a) *
          ((∑ j ∈ Finset.range 5, cMain j * |v| ^ j) * Real.exp (-(4 * π) * v ^ 2)) +
        Real.sqrt 2 / (2 * π * a ^ 2) *
          ((∑ j ∈ Finset.range 4, cEtwo j * |v| ^ j) * Real.exp (-(4 * π) * v ^ 2)) +
        Real.sqrt 2 * Real.exp (1 / (2 * a0 ^ 2)) / (2 * π * a ^ 2) *
          ((∑ j ∈ Finset.range 8, cS a0 j * |v| ^ j) * Real.exp (-(4 * π - 37 / 10) * v ^ 2)) := by
  have ha0 : 0 < a := by linarith
  rw [sum_cMain, sum_cEtwo, sum_cS]
  have hq0 := qMain_nonneg |v|
  have h1 : 0 ≤ 1 / (2 * π * a) * ((41 / 40 - 10 * π / 3 * |v| ^ 2 + 40 * π ^ 2 / 9 * |v| ^ 4) *
      Real.exp (-(4 * π) * v ^ 2)) :=
    mul_nonneg (by positivity) (mul_nonneg hq0 (Real.exp_pos _).le)
  have h2 : 0 ≤ Real.sqrt 2 / (2 * π * a ^ 2) *
      ((|v| + 4 * π * |v| ^ 3) * Real.exp (-(4 * π) * v ^ 2)) := by positivity
  have h3 : 0 ≤ Real.sqrt 2 * Real.exp (1 / (2 * a0 ^ 2)) / (2 * π * a ^ 2) *
      (|v| * (Real.sqrt 2 / 2 * (1 + 8 * π / 3 * |v| ^ 2) + (|v| + 4 * π * |v| ^ 3) / a0) ^ 2 *
        Real.exp (-(4 * π - 37 / 10) * v ^ 2)) := by positivity
  rcases eq_or_ne v 0 with rfl | hv0
  · have h0 : rsPhi a (((0 : ℝ) : ℂ) * (1 + I)) = 1 := by simp [rsPhi]
    rw [h0, sub_self, mul_zero, zero_mul, norm_zero]
    linarith
  have hvpos : 0 < |v| := abs_pos.mpr hv0
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnv : ‖(v : ℂ) * (1 + I)‖ = Real.sqrt 2 * |v| := norm_w_eq v
  have hn2 : ‖(v : ℂ) * (1 + I)‖ ^ 2 = 2 * v ^ 2 := by rw [hnv, mul_pow, hs2, sq_abs]
  have hn4 : ‖(v : ℂ) * (1 + I)‖ ^ 4 = 4 * v ^ 4 := by
    have : ‖(v : ℂ) * (1 + I)‖ ^ 4 = (‖(v : ℂ) * (1 + I)‖ ^ 2) ^ 2 := by ring
    rw [this, hn2]; ring
  have hna : ‖(v : ℂ) * (1 + I)‖ ≤ a / 2 := by
    rw [hnv]
    calc Real.sqrt 2 * |v| ≤ 3 / 2 * (a / 3) :=
          mul_le_mul sqrt_two_le_three_halves hv (abs_nonneg _) (by norm_num)
      _ = a / 2 := by ring
  have hphi := norm_rsPhi_sub_one_le' ha0 hna
  rw [rsEone_line ha0 v, hn2, hn4] at hphi
  have hη1 := near_eta_le_lin (v := v) h9 ha
  have hη2 := near_eta_le_sq h9 ha hv
  have hη0 : 0 ≤ Real.sqrt 2 / 2 * |v| * |1 - 8 * π * v ^ 2 / 3| / a +
      (π * (4 * v ^ 4) / a ^ 2 + 2 * v ^ 2 / (2 * a ^ 2)) := by positivity
  have hexpη : Real.exp (Real.sqrt 2 / 2 * |v| * |1 - 8 * π * v ^ 2 / 3| / a +
      (π * (4 * v ^ 4) / a ^ 2 + 2 * v ^ 2 / (2 * a ^ 2))) ≤
      Real.exp (1 / (2 * a0 ^ 2)) * Real.exp (37 / 10 * v ^ 2) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have hG0 : 0 < Real.exp (-(4 * π) * v ^ 2) := Real.exp_pos _
  have hGe : Real.exp (-(4 * π) * v ^ 2) * Real.exp (37 / 10 * v ^ 2) =
      Real.exp (-(4 * π - 37 / 10) * v ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hexpw : ‖cexp (2 * ↑π * I * ((v : ℂ) * (1 + I)) ^ 2)‖ = Real.exp (-(4 * π) * v ^ 2) :=
    norm_exp_gauss_diag v
  have him : ((p : ℂ) + (v : ℂ) * (1 + I)).im = v := by simp
  have hD : 2 * π * |v| ≤ ‖rsD (p + (v : ℂ) * (1 + I))‖ := by
    have := norm_rsD_ge_two_pi_im (p + (v : ℂ) * (1 + I)); rwa [him] at this
  have hT1 := near_T1 (G := Real.exp (-(4 * π) * v ^ 2)) ha0 hvpos hG0.le
    (abs_one_sub_le_quad (8 * π * v ^ 2 / 3))
  have hQ' : 41 / 40 - 5 / 4 * (8 * π * v ^ 2 / 3) + 5 / 8 * (8 * π * v ^ 2 / 3) ^ 2 =
      41 / 40 - 10 * π / 3 * |v| ^ 2 + 40 * π ^ 2 / 9 * |v| ^ 4 := by
    have h4abs : |v| ^ 4 = v ^ 4 := by
      rw [show |v| ^ 4 = (|v| ^ 2) ^ 2 by ring, sq_abs]; ring
    rw [sq_abs, h4abs]; ring
  rw [hQ'] at hT1
  have hT2 := near_T2 (G := Real.exp (-(4 * π) * v ^ 2)) ha0 hv0
  have hT3 := near_T3 (a0 := a0) ha0 hvpos hG0.le hη0 hη1 hexpη hGe
  calc ‖cexp (2 * ↑π * I * ((v : ℂ) * (1 + I)) ^ 2) / rsD (p + (v : ℂ) * (1 + I)) *
        (rsPhi a ((v : ℂ) * (1 + I)) - 1) * (1 + I)‖
      = Real.exp (-(4 * π) * v ^ 2) * ‖rsPhi a ((v : ℂ) * (1 + I)) - 1‖ * Real.sqrt 2 /
          ‖rsD (p + (v : ℂ) * (1 + I))‖ := by
        rw [norm_mul, norm_mul, norm_div, hexpw, norm_one_add_I]; ring
    _ ≤ Real.exp (-(4 * π) * v ^ 2) * ((Real.sqrt 2 / 2 * |v| * |1 - 8 * π * v ^ 2 / 3| / a +
          (π * (4 * v ^ 4) / a ^ 2 + 2 * v ^ 2 / (2 * a ^ 2))) +
          (Real.sqrt 2 / 2 * |v| * |1 - 8 * π * v ^ 2 / 3| / a +
            (π * (4 * v ^ 4) / a ^ 2 + 2 * v ^ 2 / (2 * a ^ 2))) ^ 2 *
          Real.exp (Real.sqrt 2 / 2 * |v| * |1 - 8 * π * v ^ 2 / 3| / a +
            (π * (4 * v ^ 4) / a ^ 2 + 2 * v ^ 2 / (2 * a ^ 2)))) * Real.sqrt 2 /
          (2 * π * |v|) := by
        gcongr
    _ = Real.exp (-(4 * π) * v ^ 2) * (Real.sqrt 2 / 2 * |v| * |1 - 8 * π * v ^ 2 / 3| / a) *
          Real.sqrt 2 / (2 * π * |v|) +
        Real.exp (-(4 * π) * v ^ 2) * (π * (4 * v ^ 4) / a ^ 2 + 2 * v ^ 2 / (2 * a ^ 2)) *
          Real.sqrt 2 / (2 * π * |v|) +
        Real.exp (-(4 * π) * v ^ 2) *
          ((Real.sqrt 2 / 2 * |v| * |1 - 8 * π * v ^ 2 / 3| / a +
            (π * (4 * v ^ 4) / a ^ 2 + 2 * v ^ 2 / (2 * a ^ 2))) ^ 2 *
          Real.exp (Real.sqrt 2 / 2 * |v| * |1 - 8 * π * v ^ 2 / 3| / a +
            (π * (4 * v ^ 4) / a ^ 2 + 2 * v ^ 2 / (2 * a ^ 2)))) * Real.sqrt 2 /
          (2 * π * |v|) := by ring
    _ ≤ _ := by rw [hT2]; linarith

/-! ## 4. The error integral, sharpened -/

theorem sqrt_pi_div_four_pi : Real.sqrt (π / (4 * π)) = 1 / 2 := by
  rw [show π / (4 * π) = (1 / 2) ^ 2 by rw [div_eq_iff (by positivity)]; ring]
  exact Real.sqrt_sq (by norm_num)

theorem sum_cMain_gauss : ∑ j ∈ Finset.range 5, cMain j * gaussMom (4 * π) j = 49 / 120 := by
  have hb : (0 : ℝ) < 4 * π := by positivity
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cMain]
  norm_num
  rw [gaussMom_0, gaussMom_2 hb, gaussMom_4 hb, sqrt_pi_div_four_pi]
  field_simp
  ring

theorem sum_cEtwo_gauss : ∑ j ∈ Finset.range 4, cEtwo j * gaussMom (4 * π) j = 1 / (2 * π) := by
  have hb : (0 : ℝ) < 4 * π := by positivity
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cEtwo]
  norm_num
  rw [gaussMom_1 hb, gaussMom_3 hb]
  field_simp
  ring

theorem sum_cS_gauss (a0 : ℝ) {b : ℝ} (hb : 0 < b) :
    ∑ j ∈ Finset.range 8, cS a0 j * gaussMom b j =
      1 / 2 * (1 / b) + Real.sqrt 2 / a0 * (Real.sqrt (π / b) / (2 * b)) +
        (8 * π / 3 + 1 / a0 ^ 2) * (1 / b ^ 2) +
        Real.sqrt 2 / a0 * (20 * π / 3) * (3 * Real.sqrt (π / b) / (4 * b ^ 2)) +
        (32 * π ^ 2 / 9 + 8 * π / a0 ^ 2) * (2 / b ^ 3) +
        Real.sqrt 2 / a0 * (32 * π ^ 2 / 3) * (15 * Real.sqrt (π / b) / (8 * b ^ 3)) +
        16 * π ^ 2 / a0 ^ 2 * (6 / b ^ 4) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cS]
  norm_num
  rw [gaussMom_1 hb, gaussMom_2 hb, gaussMom_3 hb, gaussMom_4 hb, gaussMom_5 hb, gaussMom_6 hb,
    gaussMom_7 hb]
  ring

/-- **The error integral, sharpened.**  For `9 <= a0 <= a`, with the Gaussian moments left
    symbolic (`sum_cMain_gauss = 49/120`, `sum_cEtwo_gauss = 1/(2 pi)`, `sum_cS_gauss`). -/
theorem norm_rsE1_le' {a0 a p : ℝ} (h9 : 9 ≤ a0) (ha : a0 ≤ a) :
    ‖rsE1 a p‖ ≤ 1 / (2 * π * a) * (∑ j ∈ Finset.range 5, cMain j * gaussMom (4 * π) j) +
      Real.sqrt 2 / (2 * π * a ^ 2) * (∑ j ∈ Finset.range 4, cEtwo j * gaussMom (4 * π) j) +
      Real.sqrt 2 * Real.exp (1 / (2 * a0 ^ 2)) / (2 * π * a ^ 2) *
        (∑ j ∈ Finset.range 8, cS a0 j * gaussMom (4 * π - 37 / 10) j) +
      5 * Real.exp (-(π * a ^ 2 / 18)) * Real.sqrt (π / (π / 2)) := by
  have ha9 : 9 ≤ a := le_trans h9 ha
  have ha0 : 0 < a := by linarith
  have hb1 : (0 : ℝ) < 4 * π := by positivity
  have hb2 : (0 : ℝ) < 4 * π - 37 / 10 := by linarith [Real.pi_gt_d2]
  have hA : Integrable (fun v : ℝ => 1 / (2 * π * a) *
      ((∑ j ∈ Finset.range 5, cMain j * |v| ^ j) * Real.exp (-(4 * π) * v ^ 2))) :=
    (integrable_poly_gauss hb1 5 cMain).const_mul _
  have hB : Integrable (fun v : ℝ => Real.sqrt 2 / (2 * π * a ^ 2) *
      ((∑ j ∈ Finset.range 4, cEtwo j * |v| ^ j) * Real.exp (-(4 * π) * v ^ 2))) :=
    (integrable_poly_gauss hb1 4 cEtwo).const_mul _
  have hC : Integrable (fun v : ℝ => Real.sqrt 2 * Real.exp (1 / (2 * a0 ^ 2)) / (2 * π * a ^ 2) *
      ((∑ j ∈ Finset.range 8, cS a0 j * |v| ^ j) * Real.exp (-(4 * π - 37 / 10) * v ^ 2))) :=
    (integrable_poly_gauss hb2 8 (cS a0)).const_mul _
  have hD : Integrable (fun v : ℝ => 5 * Real.exp (-(π * a ^ 2 / 18)) *
      Real.exp (-(π / 2) * v ^ 2)) :=
    (integrable_exp_neg_mul_sq (by positivity)).const_mul _
  have hAB : Integrable (fun v : ℝ => 1 / (2 * π * a) *
      ((∑ j ∈ Finset.range 5, cMain j * |v| ^ j) * Real.exp (-(4 * π) * v ^ 2)) +
      Real.sqrt 2 / (2 * π * a ^ 2) *
      ((∑ j ∈ Finset.range 4, cEtwo j * |v| ^ j) * Real.exp (-(4 * π) * v ^ 2))) := hA.add hB
  have hABC : Integrable (fun v : ℝ => 1 / (2 * π * a) *
      ((∑ j ∈ Finset.range 5, cMain j * |v| ^ j) * Real.exp (-(4 * π) * v ^ 2)) +
      Real.sqrt 2 / (2 * π * a ^ 2) *
      ((∑ j ∈ Finset.range 4, cEtwo j * |v| ^ j) * Real.exp (-(4 * π) * v ^ 2)) +
      Real.sqrt 2 * Real.exp (1 / (2 * a0 ^ 2)) / (2 * π * a ^ 2) *
      ((∑ j ∈ Finset.range 8, cS a0 j * |v| ^ j) * Real.exp (-(4 * π - 37 / 10) * v ^ 2))) :=
    hAB.add hC
  have hint : Integrable (fun v : ℝ => 1 / (2 * π * a) *
      ((∑ j ∈ Finset.range 5, cMain j * |v| ^ j) * Real.exp (-(4 * π) * v ^ 2)) +
      Real.sqrt 2 / (2 * π * a ^ 2) *
      ((∑ j ∈ Finset.range 4, cEtwo j * |v| ^ j) * Real.exp (-(4 * π) * v ^ 2)) +
      Real.sqrt 2 * Real.exp (1 / (2 * a0 ^ 2)) / (2 * π * a ^ 2) *
      ((∑ j ∈ Finset.range 8, cS a0 j * |v| ^ j) * Real.exp (-(4 * π - 37 / 10) * v ^ 2)) +
      5 * Real.exp (-(π * a ^ 2 / 18)) * Real.exp (-(π / 2) * v ^ 2)) := hABC.add hD
  have hpt : ∀ v : ℝ, ‖cexp (2 * ↑π * I * ((v : ℂ) * (1 + I)) ^ 2) /
      rsD (p + (v : ℂ) * (1 + I)) * (rsPhi a ((v : ℂ) * (1 + I)) - 1) * (1 + I)‖ ≤
      1 / (2 * π * a) *
        ((∑ j ∈ Finset.range 5, cMain j * |v| ^ j) * Real.exp (-(4 * π) * v ^ 2)) +
      Real.sqrt 2 / (2 * π * a ^ 2) *
        ((∑ j ∈ Finset.range 4, cEtwo j * |v| ^ j) * Real.exp (-(4 * π) * v ^ 2)) +
      Real.sqrt 2 * Real.exp (1 / (2 * a0 ^ 2)) / (2 * π * a ^ 2) *
        ((∑ j ∈ Finset.range 8, cS a0 j * |v| ^ j) * Real.exp (-(4 * π - 37 / 10) * v ^ 2)) +
      5 * Real.exp (-(π * a ^ 2 / 18)) * Real.exp (-(π / 2) * v ^ 2) := by
    intro v
    have n1 : 0 ≤ 1 / (2 * π * a) *
        ((∑ j ∈ Finset.range 5, cMain j * |v| ^ j) * Real.exp (-(4 * π) * v ^ 2)) := by
      rw [sum_cMain]
      exact mul_nonneg (by positivity) (mul_nonneg (qMain_nonneg _) (Real.exp_pos _).le)
    have n2 : 0 ≤ Real.sqrt 2 / (2 * π * a ^ 2) *
        ((∑ j ∈ Finset.range 4, cEtwo j * |v| ^ j) * Real.exp (-(4 * π) * v ^ 2)) := by
      rw [sum_cEtwo]; positivity
    have n3 : 0 ≤ Real.sqrt 2 * Real.exp (1 / (2 * a0 ^ 2)) / (2 * π * a ^ 2) *
        ((∑ j ∈ Finset.range 8, cS a0 j * |v| ^ j) * Real.exp (-(4 * π - 37 / 10) * v ^ 2)) := by
      rw [sum_cS]; positivity
    have n4 : 0 ≤ 5 * Real.exp (-(π * a ^ 2 / 18)) * Real.exp (-(π / 2) * v ^ 2) := by positivity
    rcases le_total |v| (a / 3) with hv | hv
    · have := norm_E1_integrand_near' (p := p) h9 ha hv
      linarith
    · have := RSSeam.norm_E1_integrand_far (p := p) ha9 hv
      linarith
  unfold rsE1 lineUp
  simp only [ofReal_zero, zero_add]
  refine le_trans (norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)) (le_of_eq ?_)
  rw [integral_add hABC hD, integral_add hAB hC, integral_add hA hB, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_poly_gauss hb1,
    integral_poly_gauss hb1, integral_poly_gauss hb2, integral_gaussian]

/-! ## 5. Numerics -/

theorem IS_mono {a0 β σ q r βU σU qU rU : ℝ} (ha0 : 0 < a0) (hβ0 : 0 ≤ β) (hσ0 : 0 ≤ σ)
    (hq0 : 0 ≤ q) (hr0 : 0 ≤ r) (hβ : β ≤ βU) (hσ : σ ≤ σU) (hq : q ≤ qU) (hr : r ≤ rU) :
    1 / 2 * β + r / a0 * (σ * β / 2) + (8 * q / 3 + 1 / a0 ^ 2) * β ^ 2 +
        r / a0 * (20 * q / 3) * (3 * σ * β ^ 2 / 4) + (32 * q ^ 2 / 9 + 8 * q / a0 ^ 2) * (2 * β ^ 3) +
        r / a0 * (32 * q ^ 2 / 3) * (15 * σ * β ^ 3 / 8) + 16 * q ^ 2 / a0 ^ 2 * (6 * β ^ 4) ≤
      1 / 2 * βU + rU / a0 * (σU * βU / 2) + (8 * qU / 3 + 1 / a0 ^ 2) * βU ^ 2 +
        rU / a0 * (20 * qU / 3) * (3 * σU * βU ^ 2 / 4) +
        (32 * qU ^ 2 / 9 + 8 * qU / a0 ^ 2) * (2 * βU ^ 3) +
        rU / a0 * (32 * qU ^ 2 / 3) * (15 * σU * βU ^ 3 / 8) + 16 * qU ^ 2 / a0 ^ 2 * (6 * βU ^ 4) := by
  have hβU : 0 ≤ βU := hβ0.trans hβ
  have hσU : 0 ≤ σU := hσ0.trans hσ
  have hqU : 0 ≤ qU := hq0.trans hq
  have hrU : 0 ≤ rU := hr0.trans hr
  gcongr

theorem IS_reshape (a0 b s r q : ℝ) :
    1 / 2 * (1 / b) + r / a0 * (s / (2 * b)) + (8 * q / 3 + 1 / a0 ^ 2) * (1 / b ^ 2) +
        r / a0 * (20 * q / 3) * (3 * s / (4 * b ^ 2)) + (32 * q ^ 2 / 9 + 8 * q / a0 ^ 2) * (2 / b ^ 3) +
        r / a0 * (32 * q ^ 2 / 3) * (15 * s / (8 * b ^ 3)) + 16 * q ^ 2 / a0 ^ 2 * (6 / b ^ 4) =
      1 / 2 * (1 / b) + r / a0 * (s * (1 / b) / 2) + (8 * q / 3 + 1 / a0 ^ 2) * (1 / b) ^ 2 +
        r / a0 * (20 * q / 3) * (3 * s * (1 / b) ^ 2 / 4) +
        (32 * q ^ 2 / 9 + 8 * q / a0 ^ 2) * (2 * (1 / b) ^ 3) +
        r / a0 * (32 * q ^ 2 / 3) * (15 * s * (1 / b) ^ 3 / 8) + 16 * q ^ 2 / a0 ^ 2 * (6 * (1 / b) ^ 4) := by
  ring

theorem sum_cS_gauss_le {a0 : ℝ} (ha0 : 0 < a0) :
    ∑ j ∈ Finset.range 8, cS a0 j * gaussMom (4 * π - 37 / 10) j ≤
      1 / 2 * (10000 / 88660) + 141422 / 100000 / a0 * (5953 / 10000 * (10000 / 88660) / 2) +
        (8 * (31416 / 10000) / 3 + 1 / a0 ^ 2) * (10000 / 88660) ^ 2 +
        141422 / 100000 / a0 * (20 * (31416 / 10000) / 3) *
          (3 * (5953 / 10000) * (10000 / 88660) ^ 2 / 4) +
        (32 * (31416 / 10000) ^ 2 / 9 + 8 * (31416 / 10000) / a0 ^ 2) * (2 * (10000 / 88660) ^ 3) +
        141422 / 100000 / a0 * (32 * (31416 / 10000) ^ 2 / 3) *
          (15 * (5953 / 10000) * (10000 / 88660) ^ 3 / 8) +
        16 * (31416 / 10000) ^ 2 / a0 ^ 2 * (6 * (10000 / 88660) ^ 4) := by
  have hb : (0 : ℝ) < 4 * π - 37 / 10 := by linarith [Real.pi_gt_d2]
  rw [sum_cS_gauss a0 hb]
  have hβ : 1 / (4 * π - 37 / 10) ≤ 10000 / 88660 := by
    rw [div_le_div_iff₀ hb (by norm_num)]
    have := Real.pi_gt_d4
    norm_num at this ⊢
    linarith
  have hs : Real.sqrt (π / (4 * π - 37 / 10)) ≤ 5953 / 10000 := by
    calc Real.sqrt (π / (4 * π - 37 / 10)) ≤ Real.sqrt ((5953 / 10000) ^ 2) := by
          apply Real.sqrt_le_sqrt
          rw [div_le_iff₀ hb]
          have := Real.pi_gt_d4
          norm_num at this ⊢
          linarith
      _ = 5953 / 10000 := Real.sqrt_sq (by norm_num)
  have hpi : π ≤ 31416 / 10000 := by
    have := Real.pi_lt_d4
    norm_num at this ⊢
    linarith
  rw [IS_reshape a0 (4 * π - 37 / 10) (Real.sqrt (π / (4 * π - 37 / 10))) (Real.sqrt 2) π]
  exact IS_mono ha0 (one_div_pos.mpr hb).le (Real.sqrt_nonneg _)
    Real.pi_pos.le (Real.sqrt_nonneg _) hβ hs hpi sqrt_two_le_141422

theorem IS_9_le : ∑ j ∈ Finset.range 8, cS 9 j * gaussMom (4 * π - 37 / 10) j ≤ 3171 / 10000 :=
  (sum_cS_gauss_le (by norm_num)).trans (by norm_num)

theorem IS_26_le : ∑ j ∈ Finset.range 8, cS 26 j * gaussMom (4 * π - 37 / 10) j ≤ 2816 / 10000 :=
  (sum_cS_gauss_le (by norm_num)).trans (by norm_num)

theorem far_seam_le {a : ℝ} (ha : 9 ≤ a) :
    5 * Real.exp (-(π * a ^ 2 / 18)) * Real.sqrt (π / (π / 2)) ≤ 1 / 200 / a := by
  have ha0 : 0 < a := by linarith
  have hpi1 := Real.pi_gt_d2
  set x := π * a ^ 2 / 18 with hx
  have ha2 : 81 ≤ a ^ 2 := by nlinarith
  have hx14 : 14 ≤ x := by
    rw [hx, le_div_iff₀ (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_right hpi1.le (sq_nonneg a)]
  have hax : a ≤ x := by
    have h28 : 28 ≤ π * a := by nlinarith
    rw [hx]
    nlinarith
  have hexp : Real.exp (-x) ≤ 40320 / x ^ 8 := by
    rw [Real.exp_neg]
    have h8 := Real.pow_div_factorial_le_exp x (by linarith) 8
    have hpos : 0 < x ^ 8 / (Nat.factorial 8) := by positivity
    calc (Real.exp x)⁻¹ ≤ (x ^ 8 / (Nat.factorial 8))⁻¹ := inv_anti₀ hpos h8
      _ = 40320 / x ^ 8 := by norm_num [Nat.factorial]
  have hs2 : Real.sqrt (π / (π / 2)) = Real.sqrt 2 := by
    congr 1; field_simp
  rw [hs2, le_div_iff₀ ha0]
  have hx0 : 0 < x := by linarith
  calc 5 * Real.exp (-x) * Real.sqrt 2 * a ≤ 5 * (40320 / x ^ 8) * (3 / 2) * x := by
        gcongr
        exact sqrt_two_le_three_halves
    _ = 302400 / x ^ 7 := by field_simp; ring
    _ ≤ 1 / 200 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        have : (14 : ℝ) ^ 7 ≤ x ^ 7 := pow_le_pow_left₀ (by norm_num) hx14 7
        nlinarith

theorem far_main_le {a : ℝ} (ha : 26 ≤ a) :
    5 * Real.exp (-(π * a ^ 2 / 18)) * Real.sqrt (π / (π / 2)) ≤ 1 / 100000 / a := by
  have ha0 : 0 < a := by linarith
  have hpi1 := Real.pi_gt_d2
  set x := π * a ^ 2 / 18 with hx
  have ha2 : 676 ≤ a ^ 2 := by nlinarith
  have hx117 : 117 ≤ x := by
    rw [hx, le_div_iff₀ (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_right hpi1.le (sq_nonneg a)]
  have hax : a ≤ x := by
    have h81 : 81 ≤ π * a := by nlinarith
    rw [hx]
    nlinarith
  have hexp : Real.exp (-x) ≤ 120 / x ^ 5 := by
    rw [Real.exp_neg]
    have h5 := Real.pow_div_factorial_le_exp x (by linarith) 5
    have hpos : 0 < x ^ 5 / (Nat.factorial 5) := by positivity
    calc (Real.exp x)⁻¹ ≤ (x ^ 5 / (Nat.factorial 5))⁻¹ := inv_anti₀ hpos h5
      _ = 120 / x ^ 5 := by norm_num [Nat.factorial]
  have hs2 : Real.sqrt (π / (π / 2)) = Real.sqrt 2 := by
    congr 1; field_simp
  rw [hs2, le_div_iff₀ ha0]
  have hx0 : 0 < x := by linarith
  calc 5 * Real.exp (-x) * Real.sqrt 2 * a ≤ 5 * (120 / x ^ 5) * (3 / 2) * x := by
        gcongr
        exact sqrt_two_le_three_halves
    _ = 900 / x ^ 4 := by field_simp; ring
    _ ≤ 1 / 100000 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        have : (117 : ℝ) ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) hx117 4
        nlinarith

theorem main_term_le {a : ℝ} (ha : 0 < a) : 1 / (2 * π * a) * (49 / 120) ≤ 65 / 1000 / a := by
  rw [show 1 / (2 * π * a) * (49 / 120) = 49 / (240 * π) / a by field_simp; ring]
  apply div_le_div_of_nonneg_right _ ha.le
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have := Real.pi_gt_d4
  norm_num at this ⊢
  linarith

theorem etwo_term_le {a A c : ℝ} (hA : 0 < A) (ha : A ≤ a)
    (hc : 141422 / 100000 / (4 * 9869 / 1000) * (1 / A) ≤ c) :
    Real.sqrt 2 / (2 * π * a ^ 2) * (1 / (2 * π)) ≤ c / a := by
  have ha0 : 0 < a := by linarith
  have e : Real.sqrt 2 / (2 * π * a ^ 2) * (1 / (2 * π)) =
      Real.sqrt 2 / (4 * π ^ 2) * (1 / a) / a := by
    field_simp; ring
  rw [e]
  apply div_le_div_of_nonneg_right _ ha0.le
  have hpp : (9869 / 1000 : ℝ) ≤ π ^ 2 := by
    have := Real.pi_gt_d4
    norm_num at this
    nlinarith
  have h1a : 1 / a ≤ 1 / A := one_div_le_one_div_of_le hA ha
  have hr2 := sqrt_two_le_141422
  calc Real.sqrt 2 / (4 * π ^ 2) * (1 / a) ≤ 141422 / 100000 / (4 * (9869 / 1000)) * (1 / A) := by
        gcongr
    _ ≤ c := by linarith

theorem second_term_le {a A d D IS ISU c : ℝ} (hA : 0 < A) (ha : A ≤ a) (hd : Real.exp d ≤ D)
    (hIS : IS ≤ ISU) (hISU : 0 ≤ ISU)
    (hc : 141422 / 100000 * D * ISU / (2 * (31415 / 10000)) * (1 / A) ≤ c) :
    Real.sqrt 2 * Real.exp d / (2 * π * a ^ 2) * IS ≤ c / a := by
  have ha0 : 0 < a := by linarith
  have hK : 0 ≤ Real.sqrt 2 * Real.exp d / (2 * π * a ^ 2) := by positivity
  refine (mul_le_mul_of_nonneg_left hIS hK).trans ?_
  have e : Real.sqrt 2 * Real.exp d / (2 * π * a ^ 2) * ISU =
      Real.sqrt 2 * Real.exp d * ISU / (2 * π) * (1 / a) / a := by
    field_simp
  rw [e]
  apply div_le_div_of_nonneg_right _ ha0.le
  have h1a : 1 / a ≤ 1 / A := one_div_le_one_div_of_le hA ha
  have hr2 := sqrt_two_le_141422
  have hD0 : 0 ≤ D := (Real.exp_pos d).le.trans hd
  have hpi : (31415 / 10000 : ℝ) ≤ π := by
    have := Real.pi_gt_d4
    norm_num at this
    linarith
  calc Real.sqrt 2 * Real.exp d * ISU / (2 * π) * (1 / a) ≤
      141422 / 100000 * D * ISU / (2 * (31415 / 10000)) * (1 / A) := by
        gcongr
    _ ≤ c := hc

/-- Numerics, seam: for `a >= 9` the right side of `norm_rsE1_le'` (with `a0 = 9`) is at most
    `(9/100)/a` (0.0821 as bounded here). -/
theorem E1_sharp_const_seam {a : ℝ} (ha : 9 ≤ a) :
    1 / (2 * π * a) * (∑ j ∈ Finset.range 5, cMain j * gaussMom (4 * π) j) +
      Real.sqrt 2 / (2 * π * a ^ 2) * (∑ j ∈ Finset.range 4, cEtwo j * gaussMom (4 * π) j) +
      Real.sqrt 2 * Real.exp (1 / (2 * 9 ^ 2)) / (2 * π * a ^ 2) *
        (∑ j ∈ Finset.range 8, cS 9 j * gaussMom (4 * π - 37 / 10) j) +
      5 * Real.exp (-(π * a ^ 2 / 18)) * Real.sqrt (π / (π / 2)) ≤ 9 / 100 / a := by
  have ha0 : 0 < a := by linarith
  rw [sum_cMain_gauss, sum_cEtwo_gauss]
  have he : Real.exp (1 / (2 * 9 ^ 2)) ≤ 162 / 161 := by
    have := Real.exp_bound_div_one_sub_of_interval' (x := 1 / (2 * 9 ^ 2)) (by norm_num) (by norm_num)
    have e : (1 : ℝ) / (1 - 1 / (2 * 9 ^ 2)) = 162 / 161 := by norm_num
    linarith
  have t1 := main_term_le ha0
  have t2 := etwo_term_le (c := 399 / 100000) (by norm_num : (0 : ℝ) < 9) ha (by norm_num)
  have t3 := second_term_le (c := 81 / 10000) (by norm_num : (0 : ℝ) < 9) ha he IS_9_le
    (by norm_num) (by norm_num)
  have t4 := far_seam_le ha
  have hsum : 65 / 1000 / a + 399 / 100000 / a + 81 / 10000 / a + 1 / 200 / a ≤ 9 / 100 / a := by
    rw [show 65 / 1000 / a + 399 / 100000 / a + 81 / 10000 / a + 1 / 200 / a =
      (65 / 1000 + 399 / 100000 + 81 / 10000 + 1 / 200) / a by ring]
    exact div_le_div_of_nonneg_right (by norm_num) ha0.le
  linarith

/-- Numerics, `a >= 26`: the right side of `norm_rsE1_le'` (with `a0 = 26`) is at most `(7/100)/a`
    (0.0689 as bounded here). -/
theorem E1_sharp_const_main {a : ℝ} (ha : 26 ≤ a) :
    1 / (2 * π * a) * (∑ j ∈ Finset.range 5, cMain j * gaussMom (4 * π) j) +
      Real.sqrt 2 / (2 * π * a ^ 2) * (∑ j ∈ Finset.range 4, cEtwo j * gaussMom (4 * π) j) +
      Real.sqrt 2 * Real.exp (1 / (2 * 26 ^ 2)) / (2 * π * a ^ 2) *
        (∑ j ∈ Finset.range 8, cS 26 j * gaussMom (4 * π - 37 / 10) j) +
      5 * Real.exp (-(π * a ^ 2 / 18)) * Real.sqrt (π / (π / 2)) ≤ 7 / 100 / a := by
  have ha0 : 0 < a := by linarith
  rw [sum_cMain_gauss, sum_cEtwo_gauss]
  have he : Real.exp (1 / (2 * 26 ^ 2)) ≤ 1352 / 1351 := by
    have := Real.exp_bound_div_one_sub_of_interval' (x := 1 / (2 * 26 ^ 2)) (by norm_num)
      (by norm_num)
    have e : (1 : ℝ) / (1 - 1 / (2 * 26 ^ 2)) = 1352 / 1351 := by norm_num
    linarith
  have t1 := main_term_le ha0
  have t2 := etwo_term_le (c := 139 / 100000) (by norm_num : (0 : ℝ) < 26) ha (by norm_num)
  have t3 := second_term_le (c := 246 / 100000) (by norm_num : (0 : ℝ) < 26) ha he IS_26_le
    (by norm_num) (by norm_num)
  have t4 := far_main_le ha
  have hsum : 65 / 1000 / a + 139 / 100000 / a + 246 / 100000 / a + 1 / 100000 / a ≤ 7 / 100 / a := by
    rw [show 65 / 1000 / a + 139 / 100000 / a + 246 / 100000 / a + 1 / 100000 / a =
      (65 / 1000 + 139 / 100000 + 246 / 100000 + 1 / 100000) / a by ring]
    exact div_le_div_of_nonneg_right (by norm_num) ha0.le
  linarith

theorem norm_rsE1_le_main {a p : ℝ} (ha : 26 ≤ a) : ‖rsE1 a p‖ ≤ 7 / 100 / a :=
  (norm_rsE1_le' (p := p) (a0 := 26) (by norm_num) ha).trans (E1_sharp_const_main ha)

theorem norm_rsE1_le_seam' {a p : ℝ} (ha : 9 ≤ a) : ‖rsE1 a p‖ ≤ 9 / 100 / a :=
  (norm_rsE1_le' (p := p) (a0 := 9) le_rfl ha).trans (E1_sharp_const_seam ha)

/-! ## 6. The tau = 2 Mordell integral: `|rsJ p| <= 4/5` (completing the square on the midline) -/

theorem exp_pi_div_four_le : Real.exp (π / 4) ≤ (64 / (64 - 3.1416)) ^ 16 := by
  have hpi := Real.pi_lt_d4
  have hx : Real.exp (π / 64) ≤ 1 / (1 - π / 64) :=
    (Real.exp_bound_div_one_sub_of_interval' (x := π / 64) (by positivity)
      (by linarith [Real.pi_lt_d2])).le
  have hy : 1 / (1 - π / 64) ≤ 64 / (64 - 3.1416) := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have h16 : Real.exp (π / 4) = Real.exp (π / 64) ^ 16 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [h16]
  exact pow_le_pow_left₀ (Real.exp_pos _).le (hx.trans hy) 16

/-- **`|rsJ p| <= 4/5` uniformly in `p ∈ (0, 1)`** (was 4 in `norm_rsJ_le`): on the midline,
    `-4 pi (c + v) v = pi c^2 - 4 pi (v + c/2)^2`, so `|rsJ p| <= (sqrt2/4) e^{pi c^2} <= (sqrt2/4) e^{pi/4}`. -/
theorem norm_rsJ_le' {p : ℝ} (hp : 0 < p) (hp1 : p < 1) : ‖rsJ p‖ ≤ 4 / 5 := by
  rw [rsJ_eq_mid hp hp1]
  unfold lineUp
  set c : ℝ := 1 / 2 - p with hc
  have hcb : c ^ 2 ≤ 1 / 4 := by
    have h1 : -(1 / 2) < c := by linarith
    have h2 : c < 1 / 2 := by linarith
    nlinarith
  have hbound : ∀ v : ℝ, ‖cexp (2 * ↑π * I * ((c : ℂ) + v * (1 + I)) ^ 2) /
      rsD (p + ((c : ℂ) + v * (1 + I))) * (1 + I)‖ ≤
      Real.sqrt 2 / 2 * Real.exp (π * c ^ 2) * Real.exp (-(4 * π) * (v + c / 2) ^ 2) := by
    intro v
    have hpt : (p : ℂ) + ((c : ℂ) + v * (1 + I)) = (1 / 2 : ℂ) + v * (1 + I) := by
      rw [hc]; push_cast; ring
    rw [hpt, norm_mul, norm_div, norm_one_add_I, Complex.norm_exp]
    have hre : (2 * (π : ℂ) * I * ((c : ℂ) + v * (1 + I)) ^ 2).re = -(4 * π * (c + v) * v) := by
      simp [pow_two, mul_re, mul_im]; ring
    rw [hre]
    have hD := two_le_norm_rsD_midline v
    have hexp : Real.exp (-(4 * π * (c + v) * v)) =
        Real.exp (π * c ^ 2) * Real.exp (-(4 * π) * (v + c / 2) ^ 2) := by
      rw [← Real.exp_add]; congr 1; ring
    calc Real.exp (-(4 * π * (c + v) * v)) / ‖rsD ((1 / 2 : ℂ) + v * (1 + I))‖ * Real.sqrt 2
        ≤ Real.exp (-(4 * π * (c + v) * v)) / 2 * Real.sqrt 2 := by gcongr
      _ = Real.sqrt 2 / 2 * Real.exp (π * c ^ 2) * Real.exp (-(4 * π) * (v + c / 2) ^ 2) := by
          rw [hexp]; ring
  have hg : Integrable (fun v : ℝ => Real.exp (-(4 * π) * v ^ 2)) :=
    integrable_exp_neg_mul_sq (by positivity)
  have hint : Integrable (fun v : ℝ => Real.sqrt 2 / 2 * Real.exp (π * c ^ 2) *
      Real.exp (-(4 * π) * (v + c / 2) ^ 2)) :=
    (hg.comp_add_right (c / 2)).const_mul _
  refine le_trans (norm_integral_le_of_norm_le hint (Eventually.of_forall hbound)) ?_
  rw [integral_const_mul]
  have hshift : ∫ v : ℝ, Real.exp (-(4 * π) * (v + c / 2) ^ 2) = 1 / 2 := by
    have h := integral_add_right_eq_self (μ := volume)
      (fun v : ℝ => Real.exp (-(4 * π) * v ^ 2)) (c / 2)
    rw [h, integral_gaussian, sqrt_pi_div_four_pi]
  rw [hshift]
  have hec : Real.exp (π * c ^ 2) ≤ Real.exp (π / 4) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have h5 := hec.trans exp_pi_div_four_le
  have hr2 := sqrt_two_le_141422
  calc Real.sqrt 2 / 2 * Real.exp (π * c ^ 2) * (1 / 2)
      ≤ 141422 / 100000 / 2 * (64 / (64 - 3.1416)) ^ 16 * (1 / 2) := by gcongr
    _ ≤ 4 / 5 := by norm_num

/-! ## 7. The sharpened C0 remainder bound, `a >= 26` (t >= 4250) -/

theorem rsAlpha_ge_26 {t : ℝ} (ht : 4250 ≤ t) : 26 ≤ rsAlpha t := by
  unfold rsAlpha
  rw [Real.le_sqrt (by norm_num) (by positivity), le_div_iff₀ (by positivity)]
  nlinarith [Real.pi_lt_d4]

/-- **The C0-corrected Riemann-Siegel remainder, sharpened, `a`-form.**  For `t >= 4250`,
    `0 < p = rsFrac t`, `cos(2 pi p) ≠ 0`, and any phase `phi` with `|phi - rsThetaMain t| <= 1/t`:
        |2 Re(e^{i phi} rsRem t) - (-1)^(N+1) a^(-1/2) Psi(p)| <= (3/20) a^(-3/2),   a = sqrt(t/2pi). -/
theorem rs_remainder_C0_alpha' {t : ℝ} (ht : 4250 ≤ t) (hp : 0 < rsFrac t)
    (hcos : Real.cos (2 * π * rsFrac t) ≠ 0) {φ : ℝ} (hφ : |φ - rsThetaMain t| ≤ 1 / t) :
    |2 * (cexp (I * φ) * rsRem t).re -
        (-1 : ℝ) ^ (rsNn t + 1) * (rsAlpha t) ^ (-(1 / 2 : ℝ)) * rsPsi (rsFrac t)| ≤
      3 / 20 * (rsAlpha t) ^ (-(3 / 2 : ℝ)) := by
  have ht0 : 0 < t := by linarith
  rw [rs_remainder_exact ht0 hp hcos φ]
  have ha26 : 26 ≤ rsAlpha t := rsAlpha_ge_26 ht
  have hta : t = 2 * π * rsAlpha t ^ 2 := t_eq_rsAlpha ht0.le
  set a := rsAlpha t with ha_def
  have ha0 : 0 < a := by linarith
  have hJ : ‖rsJ (rsFrac t)‖ ≤ 4 / 5 := norm_rsJ_le' hp rsFrac_lt_one
  have hE : ‖rsE1 a (rsFrac t)‖ ≤ 7 / 100 / a := norm_rsE1_le_main ha26
  have hA : |2 * (cexp (-(↑π / 8 * I)) * (cexp (I * (φ - rsThetaMain t)) - 1) *
      rsJ (rsFrac t)).re| ≤ 2 * (|φ - rsThetaMain t| * (4 / 5)) := by
    rw [abs_mul, abs_two]
    gcongr
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_mul]
    have h1 : ‖cexp (-(↑π / 8 * I))‖ = 1 := by rw [Complex.norm_exp]; simp
    have h2 : ‖cexp (I * (φ - rsThetaMain t)) - 1‖ ≤ |φ - rsThetaMain t| := by
      have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := φ - rsThetaMain t)
      push_cast at this; rwa [Real.norm_eq_abs] at this
    rw [h1, one_mul]
    exact mul_le_mul h2 hJ (norm_nonneg _) (abs_nonneg _)
  have hB : |2 * (cexp (I * (φ - rsThetaMain t - π / 8)) * rsE1 a (rsFrac t)).re| ≤
      2 * (7 / 100 / a) := by
    rw [abs_mul, abs_two]
    gcongr
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul]
    have h1 : ‖cexp (I * (φ - rsThetaMain t - π / 8))‖ = 1 := by rw [Complex.norm_exp]; simp
    rw [h1, one_mul]; exact hE
  have hδ : |φ - rsThetaMain t| ≤ 1 / (2 * π * a ^ 2) := by rw [← hta]; exact hφ
  have h8 : 8 / 5 * |φ - rsThetaMain t| ≤ 1 / 100 / a := by
    have h1 : 8 / 5 * |φ - rsThetaMain t| ≤ 8 / 5 * (1 / (2 * π * a ^ 2)) := by linarith
    refine h1.trans ?_
    rw [show 8 / 5 * (1 / (2 * π * a ^ 2)) = 4 / (5 * π * a ^ 2) by field_simp; ring,
      div_le_div_iff₀ (by positivity) ha0]
    have : 80 ≤ π * a := by nlinarith [Real.pi_gt_d2]
    nlinarith
  rw [abs_mul, abs_mul]
  have hsign : |(-1 : ℝ) ^ (rsNn t + 1)| = 1 := by simp
  rw [hsign, one_mul, abs_of_pos (Real.rpow_pos_of_pos ha0 _)]
  have hapos := Real.rpow_pos_of_pos ha0 (-(1 / 2 : ℝ))
  calc a ^ (-(1 / 2 : ℝ)) * |2 * (cexp (-(↑π / 8 * I)) * (cexp (I * (φ - rsThetaMain t)) - 1) *
        rsJ (rsFrac t)).re + 2 * (cexp (I * (φ - rsThetaMain t - π / 8)) *
        rsE1 a (rsFrac t)).re|
      ≤ a ^ (-(1 / 2 : ℝ)) * (2 * (|φ - rsThetaMain t| * (4 / 5)) + 2 * (7 / 100 / a)) := by
        gcongr
        exact (abs_add_le _ _).trans (add_le_add hA hB)
    _ ≤ a ^ (-(1 / 2 : ℝ)) * (3 / 20 / a) := by
        gcongr
        have e : (3 : ℝ) / 20 / a = 1 / 100 / a + 2 * (7 / 100 / a) := by ring
        rw [e]; linarith
    _ = 3 / 20 * a ^ (-(3 / 2 : ℝ)) := by
        rw [show (-(3 / 2 : ℝ)) = -(1 / 2) + -1 by norm_num, Real.rpow_add ha0, Real.rpow_neg_one]
        ring

/-- **HEADLINE (sharpened): the explicit C0-corrected Riemann-Siegel remainder bound, t >= 4250.**
        |2 Re(e^{i phi} rsRem t) - (-1)^(N+1) (t/2pi)^(-1/4) Psi(p)| <= (3/5) t^(-3/4). -/
theorem rs_remainder_C0' {t : ℝ} (ht : 4250 ≤ t) (hp : 0 < rsFrac t)
    (hcos : Real.cos (2 * π * rsFrac t) ≠ 0) {φ : ℝ} (hφ : |φ - rsThetaMain t| ≤ 1 / t) :
    |2 * (cexp (I * φ) * rsRem t).re -
        (-1 : ℝ) ^ (rsNn t + 1) * (t / (2 * π)) ^ (-(1 / 4 : ℝ)) * rsPsi (rsFrac t)| ≤
      3 / 5 * t ^ (-(3 / 4 : ℝ)) := by
  have ht0 : 0 < t := by linarith
  have h := rs_remainder_C0_alpha' ht hp hcos hφ
  rw [rsAlpha_rpow_neg_half ht0.le, rsAlpha_rpow_neg_three_halves ht0] at h
  have ht34 := Real.rpow_pos_of_pos ht0 (-(3 / 4 : ℝ))
  calc _ ≤ 3 / 20 * ((2 * π) ^ (3 / 4 : ℝ) * t ^ (-(3 / 4 : ℝ))) := h
    _ ≤ 3 / 20 * (4 * t ^ (-(3 / 4 : ℝ))) := by gcongr; exact two_pi_rpow_three_quarters_le
    _ = 3 / 5 * t ^ (-(3 / 4 : ℝ)) := by ring

/-! ## 8. The old headlines re-derived from the sharpened ones -/

/-- `rs_remainder_C0_alpha`'s statement (2/5, t >= 10000) from `rs_remainder_C0_alpha'`. -/
theorem rs_remainder_C0_alpha_of_sharp {t : ℝ} (ht : 10000 ≤ t) (hp : 0 < rsFrac t)
    (hcos : Real.cos (2 * π * rsFrac t) ≠ 0) {φ : ℝ} (hφ : |φ - rsThetaMain t| ≤ 1 / t) :
    |2 * (cexp (I * φ) * rsRem t).re -
        (-1 : ℝ) ^ (rsNn t + 1) * (rsAlpha t) ^ (-(1 / 2 : ℝ)) * rsPsi (rsFrac t)| ≤
      2 / 5 * (rsAlpha t) ^ (-(3 / 2 : ℝ)) := by
  have h := rs_remainder_C0_alpha' (by linarith) hp hcos hφ
  have hpos : 0 < (rsAlpha t) ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_pos_of_pos (rsAlpha_pos (by linarith)) _
  linarith

/-- `rs_remainder_C0`'s statement (2 t^(-3/4), t >= 10000) from `rs_remainder_C0'`. -/
theorem rs_remainder_C0_of_sharp {t : ℝ} (ht : 10000 ≤ t) (hp : 0 < rsFrac t)
    (hcos : Real.cos (2 * π * rsFrac t) ≠ 0) {φ : ℝ} (hφ : |φ - rsThetaMain t| ≤ 1 / t) :
    |2 * (cexp (I * φ) * rsRem t).re -
        (-1 : ℝ) ^ (rsNn t + 1) * (t / (2 * π)) ^ (-(1 / 4 : ℝ)) * rsPsi (rsFrac t)| ≤
      2 * t ^ (-(3 / 4 : ℝ)) := by
  have h := rs_remainder_C0' (by linarith) hp hcos hφ
  have hpos : 0 < t ^ (-(3 / 4 : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
  linarith

end RSInt

namespace RSSeam

open RSInt

/-! ## 9. The seam, sharpened: t >= 509 (a >= 9) -/

/-- **SEAM (sharpened), `a`-form.**  For `t >= 509`, `0 < p = rsFrac t`, `cos(2 pi p) ≠ 0`, and any
    phase `phi` with `|phi - rsThetaMain t| <= 1/t`:
        |2 Re(e^{i phi} rsRem t) - (-1)^(N+1) a^(-1/2) Psi(p)| <= (21/100) a^(-3/2). -/
theorem rs_remainder_C0_alpha_seam' {t : ℝ} (ht : 509 ≤ t) (hp : 0 < rsFrac t)
    (hcos : Real.cos (2 * π * rsFrac t) ≠ 0) {φ : ℝ} (hφ : |φ - rsThetaMain t| ≤ 1 / t) :
    |2 * (cexp (I * φ) * rsRem t).re -
        (-1 : ℝ) ^ (rsNn t + 1) * (rsAlpha t) ^ (-(1 / 2 : ℝ)) * rsPsi (rsFrac t)| ≤
      21 / 100 * (rsAlpha t) ^ (-(3 / 2 : ℝ)) := by
  have ht0 : 0 < t := by linarith
  rw [rs_remainder_exact ht0 hp hcos φ]
  have ha9 : 9 ≤ rsAlpha t := rsAlpha_ge_9 ht
  have hta : t = 2 * π * rsAlpha t ^ 2 := t_eq_rsAlpha ht0.le
  set a := rsAlpha t with ha_def
  have ha0 : 0 < a := by linarith
  have hJ : ‖rsJ (rsFrac t)‖ ≤ 4 / 5 := norm_rsJ_le' hp rsFrac_lt_one
  have hE : ‖rsE1 a (rsFrac t)‖ ≤ 9 / 100 / a := norm_rsE1_le_seam' ha9
  have hA : |2 * (cexp (-(↑π / 8 * I)) * (cexp (I * (φ - rsThetaMain t)) - 1) *
      rsJ (rsFrac t)).re| ≤ 2 * (|φ - rsThetaMain t| * (4 / 5)) := by
    rw [abs_mul, abs_two]
    gcongr
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_mul]
    have h1 : ‖cexp (-(↑π / 8 * I))‖ = 1 := by rw [Complex.norm_exp]; simp
    have h2 : ‖cexp (I * (φ - rsThetaMain t)) - 1‖ ≤ |φ - rsThetaMain t| := by
      have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := φ - rsThetaMain t)
      push_cast at this; rwa [Real.norm_eq_abs] at this
    rw [h1, one_mul]
    exact mul_le_mul h2 hJ (norm_nonneg _) (abs_nonneg _)
  have hB : |2 * (cexp (I * (φ - rsThetaMain t - π / 8)) * rsE1 a (rsFrac t)).re| ≤
      2 * (9 / 100 / a) := by
    rw [abs_mul, abs_two]
    gcongr
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul]
    have h1 : ‖cexp (I * (φ - rsThetaMain t - π / 8))‖ = 1 := by rw [Complex.norm_exp]; simp
    rw [h1, one_mul]; exact hE
  have hδ : |φ - rsThetaMain t| ≤ 1 / (2 * π * a ^ 2) := by rw [← hta]; exact hφ
  have h8 : 8 / 5 * |φ - rsThetaMain t| ≤ 3 / 100 / a := by
    have h1 : 8 / 5 * |φ - rsThetaMain t| ≤ 8 / 5 * (1 / (2 * π * a ^ 2)) := by linarith
    refine h1.trans ?_
    rw [show 8 / 5 * (1 / (2 * π * a ^ 2)) = 4 / (5 * π * a ^ 2) by field_simp; ring,
      div_le_div_iff₀ (by positivity) ha0]
    have : 28 ≤ π * a := by nlinarith [Real.pi_gt_d2]
    nlinarith
  rw [abs_mul, abs_mul]
  have hsign : |(-1 : ℝ) ^ (rsNn t + 1)| = 1 := by simp
  rw [hsign, one_mul, abs_of_pos (Real.rpow_pos_of_pos ha0 _)]
  have hapos := Real.rpow_pos_of_pos ha0 (-(1 / 2 : ℝ))
  calc a ^ (-(1 / 2 : ℝ)) * |2 * (cexp (-(↑π / 8 * I)) * (cexp (I * (φ - rsThetaMain t)) - 1) *
        rsJ (rsFrac t)).re + 2 * (cexp (I * (φ - rsThetaMain t - π / 8)) *
        rsE1 a (rsFrac t)).re|
      ≤ a ^ (-(1 / 2 : ℝ)) * (2 * (|φ - rsThetaMain t| * (4 / 5)) + 2 * (9 / 100 / a)) := by
        gcongr
        exact (abs_add_le _ _).trans (add_le_add hA hB)
    _ ≤ a ^ (-(1 / 2 : ℝ)) * (21 / 100 / a) := by
        gcongr
        have e : (21 : ℝ) / 100 / a = 3 / 100 / a + 2 * (9 / 100 / a) := by ring
        rw [e]; linarith
    _ = 21 / 100 * a ^ (-(3 / 2 : ℝ)) := by
        rw [show (-(3 / 2 : ℝ)) = -(1 / 2) + -1 by norm_num, Real.rpow_add ha0, Real.rpow_neg_one]
        ring

/-- **SEAM HEADLINE (sharpened): t >= 509.**
        |2 Re(e^{i phi} rsRem t) - (-1)^(N+1) (t/2pi)^(-1/4) Psi(p)| <= (21/25) t^(-3/4). -/
theorem rs_remainder_C0_seam' {t : ℝ} (ht : 509 ≤ t) (hp : 0 < rsFrac t)
    (hcos : Real.cos (2 * π * rsFrac t) ≠ 0) {φ : ℝ} (hφ : |φ - rsThetaMain t| ≤ 1 / t) :
    |2 * (cexp (I * φ) * rsRem t).re -
        (-1 : ℝ) ^ (rsNn t + 1) * (t / (2 * π)) ^ (-(1 / 4 : ℝ)) * rsPsi (rsFrac t)| ≤
      21 / 25 * t ^ (-(3 / 4 : ℝ)) := by
  have ht0 : 0 < t := by linarith
  have h := rs_remainder_C0_alpha_seam' ht hp hcos hφ
  rw [rsAlpha_rpow_neg_half ht0.le, rsAlpha_rpow_neg_three_halves ht0] at h
  have ht34 := Real.rpow_pos_of_pos ht0 (-(3 / 4 : ℝ))
  calc _ ≤ 21 / 100 * ((2 * π) ^ (3 / 4 : ℝ) * t ^ (-(3 / 4 : ℝ))) := h
    _ ≤ 21 / 100 * (4 * t ^ (-(3 / 4 : ℝ))) := by gcongr; exact two_pi_rpow_three_quarters_le
    _ = 21 / 25 * t ^ (-(3 / 4 : ℝ)) := by ring

/-- `rs_remainder_C0_alpha_seam`'s statement (13/20, t >= 509) from the sharpened seam. -/
theorem rs_remainder_C0_alpha_seam_of_sharp {t : ℝ} (ht : 509 ≤ t) (hp : 0 < rsFrac t)
    (hcos : Real.cos (2 * π * rsFrac t) ≠ 0) {φ : ℝ} (hφ : |φ - rsThetaMain t| ≤ 1 / t) :
    |2 * (cexp (I * φ) * rsRem t).re -
        (-1 : ℝ) ^ (rsNn t + 1) * (rsAlpha t) ^ (-(1 / 2 : ℝ)) * rsPsi (rsFrac t)| ≤
      13 / 20 * (rsAlpha t) ^ (-(3 / 2 : ℝ)) := by
  have h := rs_remainder_C0_alpha_seam' ht hp hcos hφ
  have hpos : 0 < (rsAlpha t) ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_pos_of_pos (rsAlpha_pos (by linarith)) _
  linarith

/-- `rs_remainder_C0_seam`'s statement (13/5 t^(-3/4), t >= 509) from the sharpened seam. -/
theorem rs_remainder_C0_seam_of_sharp {t : ℝ} (ht : 509 ≤ t) (hp : 0 < rsFrac t)
    (hcos : Real.cos (2 * π * rsFrac t) ≠ 0) {φ : ℝ} (hφ : |φ - rsThetaMain t| ≤ 1 / t) :
    |2 * (cexp (I * φ) * rsRem t).re -
        (-1 : ℝ) ^ (rsNn t + 1) * (t / (2 * π)) ^ (-(1 / 4 : ℝ)) * rsPsi (rsFrac t)| ≤
      13 / 5 * t ^ (-(3 / 4 : ℝ)) := by
  have h := rs_remainder_C0_seam' ht hp hcos hφ
  have hpos : 0 < t ^ (-(3 / 4 : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
  linarith

end RSSeam
