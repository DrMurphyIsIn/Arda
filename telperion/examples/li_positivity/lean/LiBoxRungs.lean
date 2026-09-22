/- LI RUNGS 0..4, HYPOTHESIS-FREE (li_positivity island, brief LI_FACE_BRIEF_2026-09-21 section 4).

   Main results (no hypotheses, Mathlib + upstream `LiCriterion` vocabulary only):

     `liPairedSummand_re_nonneg` : for every nontrivial zero rho and every n <= 4,
                                    0 <= Re (liPairedSummand n rho);
     `li_rung0` .. `li_rung4`     : 0 <= Re (taylorCoeff riemannXi n)   for n = 0, 1, 2, 3, 4.

   ROUTE (algebraic, no polar coordinates).  With w = rho/(rho - 1) the pair term is
   2 - w^N - w^(-N) (N = n + 1), and w + 1/w = 2 - z where z := 1/(rho (1 - rho)).  Hence the pair
   term is a polynomial Q_N(z) (Chebyshev-type: Q_N(2 - 2 cos t) = 2 - 2 cos (N t)):

       Q_1 = z,  Q_2 = 4z - z^2,  Q_3 = 9z - 6z^2 + z^3,  Q_4 = 16z - 20z^2 + 8z^3 - z^4,
       Q_5 = 25z - 50z^2 + 35z^3 - 10z^4 + z^5.

   Box 2 (LowHeightBox) gives Re (rho (1 - rho)) = beta(1-beta) + gamma^2 >= 1, i.e. z lies in the
   closed disk |z - 1/2| <= 1/2, equivalently  (Re z)^2 + (Im z)^2 <= Re z.  On that disk
   Re Q_N(z) >= 0 for N <= 5, certified by an explicit identity with nonnegative coefficients in
   the variables d = Re z - |z|^2 >= 0, B = (Im z)^2 >= 0, s = |z|^2 >= 0 (found by LP, checked by
   `ring`).  N = 6 has no such certificate and the pair term is genuinely negative at box points
   (brief section 4), so rungs 0..4 are the honest reach of this method.

   The rung statements then follow from the upstream paired sum formula
   (`weighted_paired_sum_formula_of_standard_hypotheses` fed with `xi_hasFiniteOrder`,
   `xi_order_le_one`): Re passes through the tsum when the series is summable, and a tsum of
   nonnegative reals is nonnegative; if it were not summable the tsum is 0 and the claim is trivial.

   Nothing here proves, or bears on, whether RH holds: Li's criterion needs ALL rungs; these are the
   first five.  conjecture1_proved = False.
-/
import Mathlib
import LowHeightBox
import Lc.LiCriterion.XiOrderBridge

open Complex LiCriterion

namespace LowHeightBox

/-! ## The rung polynomials. -/

/-- `Q_1`. -/
noncomputable def Q1 (z : ℂ) : ℂ := z
/-- `Q_2`. -/
noncomputable def Q2 (z : ℂ) : ℂ := 4 * z - z ^ 2
/-- `Q_3`. -/
noncomputable def Q3 (z : ℂ) : ℂ := 9 * z - 6 * z ^ 2 + z ^ 3
/-- `Q_4`. -/
noncomputable def Q4 (z : ℂ) : ℂ := 16 * z - 20 * z ^ 2 + 8 * z ^ 3 - z ^ 4
/-- `Q_5`. -/
noncomputable def Q5 (z : ℂ) : ℂ := 25 * z - 50 * z ^ 2 + 35 * z ^ 3 - 10 * z ^ 4 + z ^ 5

/-- `z(rho) = 1 / (rho (1 - rho))`. -/
noncomputable def zOf (ρ : ℂ) : ℂ := 1 / (ρ * (1 - ρ))

/-! ## The pair term in terms of `w = rho/(rho-1)`. -/

/-- `liPairedSummand n rho = 2 - w^(n+1) - w^(-(n+1))` with `w = rho/(rho-1)`. -/
theorem liPairedSummand_eq_pow (n : ℕ) (ρ : NontrivialZero) :
    liPairedSummand n ρ
      = 2 - (ρ.val / (ρ.val - 1)) ^ (n + 1) - ((ρ.val - 1) / ρ.val) ^ (n + 1) := by
  have h0 : ρ.val ≠ 0 := ρ.ne_zero
  have h1 : ρ.val - 1 ≠ 0 := sub_ne_zero.mpr ρ.ne_one
  have h1' : 1 - ρ.val ≠ 0 := sub_ne_zero.mpr (Ne.symm ρ.ne_one)
  simp only [liPairedSummand, liSummand, pairedZero_val]
  have e1 : (1 - 1 / ρ.val) = (ρ.val - 1) / ρ.val := by field_simp
  have e2 : (1 - 1 / (1 - ρ.val)) = ρ.val / (ρ.val - 1) := by
    field_simp
    ring
  rw [e1, e2, show (-(n + 1 : ℤ)) = -((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
    zpow_neg, zpow_natCast, ← inv_pow, ← inv_pow, inv_div, inv_div]
  ring

/-- `z(rho) = 2 - w - 1/w` with `w = rho/(rho-1)`. -/
theorem zOf_eq (ρ : NontrivialZero) :
    zOf ρ.val = 2 - ρ.val / (ρ.val - 1) - (ρ.val - 1) / ρ.val := by
  have h0 : ρ.val ≠ 0 := ρ.ne_zero
  have h1 : ρ.val - 1 ≠ 0 := sub_ne_zero.mpr ρ.ne_one
  have h1' : 1 - ρ.val ≠ 0 := sub_ne_zero.mpr (Ne.symm ρ.ne_one)
  unfold zOf
  field_simp
  ring

/-- `w * (1/w) = 1`. -/
theorem w_mul_v (ρ : NontrivialZero) : ρ.val / (ρ.val - 1) * ((ρ.val - 1) / ρ.val) = 1 := by
  have h0 : ρ.val ≠ 0 := ρ.ne_zero
  have h1 : ρ.val - 1 ≠ 0 := sub_ne_zero.mpr ρ.ne_one
  field_simp

theorem liPairedSummand_zero_eq (ρ : NontrivialZero) : liPairedSummand 0 ρ = Q1 (zOf ρ.val) := by
  rw [liPairedSummand_eq_pow, zOf_eq]
  simp only [Q1]
  ring

theorem liPairedSummand_one_eq (ρ : NontrivialZero) : liPairedSummand 1 ρ = Q2 (zOf ρ.val) := by
  rw [liPairedSummand_eq_pow, zOf_eq]
  simp only [Q2]
  have hv := w_mul_v ρ
  linear_combination (2 : ℂ) * hv

theorem liPairedSummand_two_eq (ρ : NontrivialZero) : liPairedSummand 2 ρ = Q3 (zOf ρ.val) := by
  rw [liPairedSummand_eq_pow, zOf_eq]
  simp only [Q3]
  have hv := w_mul_v ρ
  set w := ρ.val / (ρ.val - 1)
  set v := (ρ.val - 1) / ρ.val
  linear_combination (3 * v + 3 * w) * hv

theorem liPairedSummand_three_eq (ρ : NontrivialZero) :
    liPairedSummand 3 ρ = Q4 (zOf ρ.val) := by
  rw [liPairedSummand_eq_pow, zOf_eq]
  simp only [Q4]
  have hv := w_mul_v ρ
  set w := ρ.val / (ρ.val - 1)
  set v := (ρ.val - 1) / ρ.val
  linear_combination (4 * v ^ 2 + 6 * v * w + 4 * w ^ 2 - 2) * hv

theorem liPairedSummand_four_eq (ρ : NontrivialZero) :
    liPairedSummand 4 ρ = Q5 (zOf ρ.val) := by
  rw [liPairedSummand_eq_pow, zOf_eq]
  simp only [Q5]
  have hv := w_mul_v ρ
  set w := ρ.val / (ρ.val - 1)
  set v := (ρ.val - 1) / ρ.val
  linear_combination (5 * v ^ 3 + 10 * v ^ 2 * w + 10 * v * w ^ 2 - 5 * v + 5 * w ^ 3 - 5 * w) * hv

/-! ## Real parts of the rung polynomials on the disk `(Re z)^2 + (Im z)^2 <= Re z`. -/

theorem re_Q1_nonneg {z : ℂ} (hz : z.re ^ 2 + z.im ^ 2 ≤ z.re) : 0 ≤ (Q1 z).re := by
  simp only [Q1]
  nlinarith [sq_nonneg z.re, sq_nonneg z.im]

theorem re_Q2_nonneg {z : ℂ} (hz : z.re ^ 2 + z.im ^ 2 ≤ z.re) : 0 ≤ (Q2 z).re := by
  have hre : (Q2 z).re = -z.re ^ 2 + 4 * z.re + z.im ^ 2 := by
    simp only [Q2, sub_re, mul_re, re_ofNat, im_ofNat, pow_succ, pow_zero, one_re, one_im, mul_im]
    ring
  rw [hre]
  nlinarith [sq_nonneg z.im]

theorem re_Q3_nonneg {z : ℂ} (hz : z.re ^ 2 + z.im ^ 2 ≤ z.re) : 0 ≤ (Q3 z).re := by
  have hre : (Q3 z).re
      = z.re ^ 3 - 6 * z.re ^ 2 - 3 * z.re * z.im ^ 2 + 9 * z.re + 6 * z.im ^ 2 := by
    simp only [Q3, sub_re, mul_re, re_ofNat, im_ofNat, pow_succ, pow_zero, one_re, one_im, mul_im,
      add_re]
    ring
  rw [hre]
  obtain ⟨d, hd0, hde⟩ : ∃ d : ℝ, 0 ≤ d ∧ d = z.re - (z.re ^ 2 + z.im ^ 2) :=
    ⟨_, by linarith, rfl⟩
  obtain ⟨s, hs0, hse⟩ : ∃ s : ℝ, 0 ≤ s ∧ s = z.re ^ 2 + z.im ^ 2 := ⟨_, by positivity, rfl⟩
  obtain ⟨B, hB0, hBe⟩ : ∃ B : ℝ, 0 ≤ B ∧ B = z.im ^ 2 := ⟨_, sq_nonneg _, rfl⟩
  have key : z.re ^ 3 - 6 * z.re ^ 2 - 3 * z.re * z.im ^ 2 + 9 * z.re + 6 * z.im ^ 2
      = 15 * B + 4 * d ^ 3 + 12 * d ^ 2 * s + 3 * d ^ 2 + 12 * d * s ^ 2 + 3 * d * s + 9 * d
        + 4 * s ^ 3 := by
    rw [hde, hse, hBe]; ring
  rw [key]
  positivity

theorem re_Q4_nonneg {z : ℂ} (hz : z.re ^ 2 + z.im ^ 2 ≤ z.re) : 0 ≤ (Q4 z).re := by
  have hre : (Q4 z).re
      = -z.re ^ 4 + 8 * z.re ^ 3 + 6 * z.re ^ 2 * z.im ^ 2 - 20 * z.re ^ 2 - 24 * z.re * z.im ^ 2
        + 16 * z.re - z.im ^ 4 + 20 * z.im ^ 2 := by
    simp only [Q4, sub_re, mul_re, re_ofNat, im_ofNat, pow_succ, pow_zero, one_re, one_im, mul_im,
      add_re]
    ring
  rw [hre]
  obtain ⟨d, hd0, hde⟩ : ∃ d : ℝ, 0 ≤ d ∧ d = z.re - (z.re ^ 2 + z.im ^ 2) :=
    ⟨_, by linarith, rfl⟩
  obtain ⟨s, hs0, hse⟩ : ∃ s : ℝ, 0 ≤ s ∧ s = z.re ^ 2 + z.im ^ 2 := ⟨_, by positivity, rfl⟩
  obtain ⟨B, hB0, hBe⟩ : ∃ B : ℝ, 0 ≤ B ∧ B = z.im ^ 2 := ⟨_, sq_nonneg _, rfl⟩
  set P : ℝ := -z.re ^ 4 + 8 * z.re ^ 3 + 6 * z.re ^ 2 * z.im ^ 2 - 20 * z.re ^ 2
        - 24 * z.re * z.im ^ 2 + 16 * z.re - z.im ^ 4 + 20 * z.im ^ 2 with hP
  have key : 14 * s * P
      = 433 * B ^ 2 + 112 * B * d ^ 2 * s + 438 * B * d ^ 2 + 224 * B * d * s ^ 2
        + 408 * B * d * s + 44 * B * d + 112 * B * s ^ 3 + 44 * B * s + 5 * d ^ 4 + 44 * d ^ 3
        + 20 * d * s ^ 3 + 180 * d * s + 15 * s ^ 4 + 27 * s ^ 2 := by
    rw [hP, hde, hse, hBe]; ring
  have hcert : 0 ≤ 14 * s * P := by rw [key]; positivity
  rcases eq_or_lt_of_le hs0 with hs' | hs'
  · -- s = 0 forces z = 0, where P = 0
    have ha : z.re = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
    have hb : z.im = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
    rw [hP, ha, hb]; norm_num
  · exact (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < 14 * s)).mp hcert

theorem re_Q5_nonneg {z : ℂ} (hz : z.re ^ 2 + z.im ^ 2 ≤ z.re) : 0 ≤ (Q5 z).re := by
  have hre : (Q5 z).re
      = z.re ^ 5 - 10 * z.re ^ 4 - 10 * z.re ^ 3 * z.im ^ 2 + 35 * z.re ^ 3
        + 60 * z.re ^ 2 * z.im ^ 2 - 50 * z.re ^ 2 + 5 * z.re * z.im ^ 4 - 105 * z.re * z.im ^ 2
        + 25 * z.re - 10 * z.im ^ 4 + 50 * z.im ^ 2 := by
    simp only [Q5, sub_re, mul_re, re_ofNat, im_ofNat, pow_succ, pow_zero, one_re, one_im, mul_im,
      add_re]
    ring
  rw [hre]
  obtain ⟨d, hd0, hde⟩ : ∃ d : ℝ, 0 ≤ d ∧ d = z.re - (z.re ^ 2 + z.im ^ 2) :=
    ⟨_, by linarith, rfl⟩
  obtain ⟨s, hs0, hse⟩ : ∃ s : ℝ, 0 ≤ s ∧ s = z.re ^ 2 + z.im ^ 2 := ⟨_, by positivity, rfl⟩
  obtain ⟨B, hB0, hBe⟩ : ∃ B : ℝ, 0 ≤ B ∧ B = z.im ^ 2 := ⟨_, sq_nonneg _, rfl⟩
  set P : ℝ := z.re ^ 5 - 10 * z.re ^ 4 - 10 * z.re ^ 3 * z.im ^ 2 + 35 * z.re ^ 3
        + 60 * z.re ^ 2 * z.im ^ 2 - 50 * z.re ^ 2 + 5 * z.re * z.im ^ 4 - 105 * z.re * z.im ^ 2
        + 25 * z.re - 10 * z.im ^ 4 + 50 * z.im ^ 2 with hP
  have key : s ^ 2 * P
      = 68 * B ^ 3 + 72 * B ^ 2 * d ^ 2 + 16 * B ^ 2 * d * s ^ 2 + 128 * B ^ 2 * d * s
        + 16 * B ^ 2 * s ^ 3 + 4 * B ^ 2 * s + 4 * B * d ^ 4 + 70 * B * d ^ 2 * s
        + 4 * B * d * s ^ 3 + 11 * B * d * s ^ 2 + 14 * B * d * s + 3 * B * s ^ 2
        + 2 * d ^ 4 * s + 3 * d ^ 3 * s ^ 2 + 14 * d ^ 3 * s + d ^ 2 * s ^ 2 + 11 * d * s ^ 2
        + s ^ 5 := by
    rw [hP, hde, hse, hBe]; ring
  have hcert : 0 ≤ s ^ 2 * P := by rw [key]; positivity
  rcases eq_or_lt_of_le hs0 with hs' | hs'
  · have ha : z.re = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
    have hb : z.im = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
    rw [hP, ha, hb]; norm_num
  · exact (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < s ^ 2)).mp hcert

/-! ## The box puts `z(rho)` in the disk. -/

/-- Box 2 gives `Re (rho (1 - rho)) >= 1` for every nontrivial zero. -/
theorem re_mul_one_sub_ge_one (ρ : NontrivialZero) : 1 ≤ (ρ.val * (1 - ρ.val)).re := by
  have hbox := zeta_zero_confined ρ.val ρ.property.1 ⟨ρ.property.2.1, ρ.property.2.2⟩
  simp only [mul_re, sub_re, sub_im, one_re, one_im, zero_sub, mul_neg, sub_neg_eq_add]
  nlinarith [hbox, sq_nonneg (ρ.val.re - 1 / 2)]

/-- `z(rho)` lies in the closed disk `|z - 1/2| <= 1/2`. -/
theorem zOf_mem_disk (ρ : NontrivialZero) :
    (zOf ρ.val).re ^ 2 + (zOf ρ.val).im ^ 2 ≤ (zOf ρ.val).re := by
  have hq := re_mul_one_sub_ge_one ρ
  set q := ρ.val * (1 - ρ.val) with hqdef
  have hqne : q ≠ 0 := by
    intro h; rw [h, zero_re] at hq; norm_num at hq
  have hm : 0 < normSq q := normSq_pos.mpr hqne
  have hz : zOf ρ.val = q⁻¹ := by rw [zOf, one_div]
  rw [hz, inv_re, inv_im, normSq_apply] at *
  have hsum : (q.re / (q.re * q.re + q.im * q.im)) ^ 2 + (-q.im / (q.re * q.re + q.im * q.im)) ^ 2
      = 1 / (q.re * q.re + q.im * q.im) := by
    field_simp
  rw [hsum]
  exact (div_le_div_iff_of_pos_right hm).mpr hq

/-- **Termwise nonnegativity, hypothesis-free**: for every nontrivial zero and every `n <= 4`,
    the paired Li summand has nonnegative real part. -/
theorem liPairedSummand_re_nonneg (n : ℕ) (hn : n ≤ 4) (ρ : NontrivialZero) :
    0 ≤ (liPairedSummand n ρ).re := by
  have hz := zOf_mem_disk ρ
  interval_cases n
  · rw [liPairedSummand_zero_eq]; exact re_Q1_nonneg hz
  · rw [liPairedSummand_one_eq]; exact re_Q2_nonneg hz
  · rw [liPairedSummand_two_eq]; exact re_Q3_nonneg hz
  · rw [liPairedSummand_three_eq]; exact re_Q4_nonneg hz
  · rw [liPairedSummand_four_eq]; exact re_Q5_nonneg hz

/-! ## From termwise nonnegativity to the rungs. -/

/-- The upstream paired sum formula with its two order inputs discharged (hypothesis-free). -/
theorem taylorCoeff_eq_half_tsum_paired (n : ℕ) :
    taylorCoeff riemannXi n
      = (2⁻¹ : ℂ) * ∑' ρ : NontrivialZero,
          (analyticOrderNatAt riemannXi ρ.val : ℂ) * liPairedSummand n ρ :=
  weighted_paired_sum_formula_of_standard_hypotheses
    (xi_weighted_genus_one_of_hadamard_order_one xi_hasFiniteOrder xi_order_le_one)
    (xi_factorization_prod_with_multiplicity_of_hadamard_order_one xi_hasFiniteOrder
      xi_order_le_one) n

/-- If every paired summand at rung `n` has nonnegative real part, so does the rung. -/
theorem taylorCoeff_re_nonneg_of_termwise (n : ℕ)
    (h : ∀ ρ : NontrivialZero, 0 ≤ (liPairedSummand n ρ).re) :
    0 ≤ (taylorCoeff riemannXi n).re := by
  rw [taylorCoeff_eq_half_tsum_paired]
  set f : NontrivialZero → ℂ :=
    fun ρ => (analyticOrderNatAt riemannXi ρ.val : ℂ) * liPairedSummand n ρ with hf
  have hterm : ∀ ρ, 0 ≤ (f ρ).re := by
    intro ρ
    simp only [hf, mul_re, natCast_re, natCast_im, zero_mul, sub_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (h ρ)
  have htsum : 0 ≤ (∑' ρ, f ρ).re := by
    by_cases hs : Summable f
    · rw [Complex.re_tsum hs]
      exact tsum_nonneg hterm
    · rw [tsum_eq_zero_of_not_summable hs]
      simp
  have h2 : (2⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) := by push_cast; ring
  rw [h2, re_ofReal_mul]
  positivity

theorem li_rung0 : 0 ≤ (taylorCoeff riemannXi 0).re :=
  taylorCoeff_re_nonneg_of_termwise 0 (liPairedSummand_re_nonneg 0 (by norm_num))

theorem li_rung1 : 0 ≤ (taylorCoeff riemannXi 1).re :=
  taylorCoeff_re_nonneg_of_termwise 1 (liPairedSummand_re_nonneg 1 (by norm_num))

theorem li_rung2 : 0 ≤ (taylorCoeff riemannXi 2).re :=
  taylorCoeff_re_nonneg_of_termwise 2 (liPairedSummand_re_nonneg 2 (by norm_num))

theorem li_rung3 : 0 ≤ (taylorCoeff riemannXi 3).re :=
  taylorCoeff_re_nonneg_of_termwise 3 (liPairedSummand_re_nonneg 3 (by norm_num))

theorem li_rung4 : 0 ≤ (taylorCoeff riemannXi 4).re :=
  taylorCoeff_re_nonneg_of_termwise 4 (liPairedSummand_re_nonneg 4 (by norm_num))

/-- Rungs `0..4` packaged for `LiLadder`-style consumers: `∀ n < 5, 0 ≤ Re (taylorCoeff riemannXi n)`. -/
theorem li_rungs_lt_five : ∀ n : ℕ, n < 5 → 0 ≤ (taylorCoeff riemannXi n).re :=
  fun n hn => taylorCoeff_re_nonneg_of_termwise n (liPairedSummand_re_nonneg n (by omega))

end LowHeightBox
