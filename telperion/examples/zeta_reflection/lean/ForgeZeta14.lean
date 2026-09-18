import ForgeZ14Terms
import ForgeTailTerms
import ForgeTail
import ZetaEMSum
import Mathlib.NumberTheory.Bernoulli
open TrigReduce Real Complex ZetaReflection ForgeZ14Terms
set_option maxHeartbeats 4000000
namespace ForgeZeta14

theorem reSum :
    ((-534327119243293113 / 1152921504606846976) : ℝ) ≤ (∑ n ∈ Finset.Ico 1 50, (((n:ℕ):ℂ) ^ (-((1/2:ℂ) + (14:ℂ)*Complex.I)))).re
      ∧ (∑ n ∈ Finset.Ico 1 50, (((n:ℕ):ℂ) ^ (-((1/2:ℂ) + (14:ℂ)*Complex.I)))).re ≤ (-519299332030709023 / 1152921504606846976) := by
  rw [Complex.re_sum, Finset.sum_Ico_eq_sum_range]
  rw [show (50-1) = 49 from rfl,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  have b2 := re_term_2
  norm_num at b2
  have b3 := re_term_3
  norm_num at b3
  have b4 := re_term_4
  norm_num at b4
  have b5 := re_term_5
  norm_num at b5
  have b6 := re_term_6
  norm_num at b6
  have b7 := re_term_7
  norm_num at b7
  have b8 := re_term_8
  norm_num at b8
  have b9 := re_term_9
  norm_num at b9
  have b10 := re_term_10
  norm_num at b10
  have b11 := re_term_11
  norm_num at b11
  have b12 := re_term_12
  norm_num at b12
  have b13 := re_term_13
  norm_num at b13
  have b14 := re_term_14
  norm_num at b14
  have b15 := re_term_15
  norm_num at b15
  have b16 := re_term_16
  norm_num at b16
  have b17 := re_term_17
  norm_num at b17
  have b18 := re_term_18
  norm_num at b18
  have b19 := re_term_19
  norm_num at b19
  have b20 := re_term_20
  norm_num at b20
  have b21 := re_term_21
  norm_num at b21
  have b22 := re_term_22
  norm_num at b22
  have b23 := re_term_23
  norm_num at b23
  have b24 := re_term_24
  norm_num at b24
  have b25 := re_term_25
  norm_num at b25
  have b26 := re_term_26
  norm_num at b26
  have b27 := re_term_27
  norm_num at b27
  have b28 := re_term_28
  norm_num at b28
  have b29 := re_term_29
  norm_num at b29
  have b30 := re_term_30
  norm_num at b30
  have b31 := re_term_31
  norm_num at b31
  have b32 := re_term_32
  norm_num at b32
  have b33 := re_term_33
  norm_num at b33
  have b34 := re_term_34
  norm_num at b34
  have b35 := re_term_35
  norm_num at b35
  have b36 := re_term_36
  norm_num at b36
  have b37 := re_term_37
  norm_num at b37
  have b38 := re_term_38
  norm_num at b38
  have b39 := re_term_39
  norm_num at b39
  have b40 := re_term_40
  norm_num at b40
  have b41 := re_term_41
  norm_num at b41
  have b42 := re_term_42
  norm_num at b42
  have b43 := re_term_43
  norm_num at b43
  have b44 := re_term_44
  norm_num at b44
  have b45 := re_term_45
  norm_num at b45
  have b46 := re_term_46
  norm_num at b46
  have b47 := re_term_47
  norm_num at b47
  have b48 := re_term_48
  norm_num at b48
  have b49 := re_term_49
  norm_num at b49
  constructor <;> linarith [b2.1, b2.2, b3.1, b3.2, b4.1, b4.2, b5.1, b5.2, b6.1, b6.2, b7.1, b7.2, b8.1, b8.2, b9.1, b9.2, b10.1, b10.2, b11.1, b11.2, b12.1, b12.2, b13.1, b13.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b17.1, b17.2, b18.1, b18.2, b19.1, b19.2, b20.1, b20.2, b21.1, b21.2, b22.1, b22.2, b23.1, b23.2, b24.1, b24.2, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b29.1, b29.2, b30.1, b30.2, b31.1, b31.2, b32.1, b32.2, b33.1, b33.2, b34.1, b34.2, b35.1, b35.2, b36.1, b36.2, b37.1, b37.2, b38.1, b38.2, b39.1, b39.2, b40.1, b40.2, b41.1, b41.2, b42.1, b42.2, b43.1, b43.2, b44.1, b44.2, b45.1, b45.2, b46.1, b46.2, b47.1, b47.2, b48.1, b48.2, b49.1, b49.2]

theorem imSum :
    ((-153165783456503289 / 576460752303423488) : ℝ) ≤ (∑ n ∈ Finset.Ico 1 50, (((n:ℕ):ℂ) ^ (-((1/2:ℂ) + (14:ℂ)*Complex.I)))).im
      ∧ (∑ n ∈ Finset.Ico 1 50, (((n:ℕ):ℂ) ^ (-((1/2:ℂ) + (14:ℂ)*Complex.I)))).im ≤ (-291253049851712901 / 1152921504606846976) := by
  rw [Complex.im_sum, Finset.sum_Ico_eq_sum_range]
  rw [show (50-1) = 49 from rfl,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  have b2 := im_term_2
  norm_num at b2
  have b3 := im_term_3
  norm_num at b3
  have b4 := im_term_4
  norm_num at b4
  have b5 := im_term_5
  norm_num at b5
  have b6 := im_term_6
  norm_num at b6
  have b7 := im_term_7
  norm_num at b7
  have b8 := im_term_8
  norm_num at b8
  have b9 := im_term_9
  norm_num at b9
  have b10 := im_term_10
  norm_num at b10
  have b11 := im_term_11
  norm_num at b11
  have b12 := im_term_12
  norm_num at b12
  have b13 := im_term_13
  norm_num at b13
  have b14 := im_term_14
  norm_num at b14
  have b15 := im_term_15
  norm_num at b15
  have b16 := im_term_16
  norm_num at b16
  have b17 := im_term_17
  norm_num at b17
  have b18 := im_term_18
  norm_num at b18
  have b19 := im_term_19
  norm_num at b19
  have b20 := im_term_20
  norm_num at b20
  have b21 := im_term_21
  norm_num at b21
  have b22 := im_term_22
  norm_num at b22
  have b23 := im_term_23
  norm_num at b23
  have b24 := im_term_24
  norm_num at b24
  have b25 := im_term_25
  norm_num at b25
  have b26 := im_term_26
  norm_num at b26
  have b27 := im_term_27
  norm_num at b27
  have b28 := im_term_28
  norm_num at b28
  have b29 := im_term_29
  norm_num at b29
  have b30 := im_term_30
  norm_num at b30
  have b31 := im_term_31
  norm_num at b31
  have b32 := im_term_32
  norm_num at b32
  have b33 := im_term_33
  norm_num at b33
  have b34 := im_term_34
  norm_num at b34
  have b35 := im_term_35
  norm_num at b35
  have b36 := im_term_36
  norm_num at b36
  have b37 := im_term_37
  norm_num at b37
  have b38 := im_term_38
  norm_num at b38
  have b39 := im_term_39
  norm_num at b39
  have b40 := im_term_40
  norm_num at b40
  have b41 := im_term_41
  norm_num at b41
  have b42 := im_term_42
  norm_num at b42
  have b43 := im_term_43
  norm_num at b43
  have b44 := im_term_44
  norm_num at b44
  have b45 := im_term_45
  norm_num at b45
  have b46 := im_term_46
  norm_num at b46
  have b47 := im_term_47
  norm_num at b47
  have b48 := im_term_48
  norm_num at b48
  have b49 := im_term_49
  norm_num at b49
  constructor <;> linarith [b2.1, b2.2, b3.1, b3.2, b4.1, b4.2, b5.1, b5.2, b6.1, b6.2, b7.1, b7.2, b8.1, b8.2, b9.1, b9.2, b10.1, b10.2, b11.1, b11.2, b12.1, b12.2, b13.1, b13.2, b14.1, b14.2, b15.1, b15.2, b16.1, b16.2, b17.1, b17.2, b18.1, b18.2, b19.1, b19.2, b20.1, b20.2, b21.1, b21.2, b22.1, b22.2, b23.1, b23.2, b24.1, b24.2, b25.1, b25.2, b26.1, b26.2, b27.1, b27.2, b28.1, b28.2, b29.1, b29.2, b30.1, b30.2, b31.1, b31.2, b32.1, b32.2, b33.1, b33.2, b34.1, b34.2, b35.1, b35.2, b36.1, b36.2, b37.1, b37.2, b38.1, b38.2, b39.1, b39.2, b40.1, b40.2, b41.1, b41.2, b42.1, b42.2, b43.1, b43.2, b44.1, b44.2, b45.1, b45.2, b46.1, b46.2, b47.1, b47.2, b48.1, b48.2, b49.1, b49.2]

-- exact rational B = N/(s-1)+1/2+b2 s/(2N): Bre=70357 / 188400, Bim=-166901 / 47100
theorem zt14_Bval :
    ((50:ℂ) / ((1/2 + (14:ℝ)*I) - 1) + 1 / 2 + (bernoulli 2 : ℂ) * (1/2 + (14:ℝ)*I) / (2 * (50:ℂ)))
      = ((70357 / 188400 : ℝ) : ℂ) + ((-166901 / 47100 : ℝ) : ℂ) * I := by
  rw [show (bernoulli 2 : ℂ) = 6⁻¹ by rw [bernoulli_two]; norm_num]
  have hdiv : (50:ℂ) / ((1/2 + (14:ℝ)*I) - 1) = ((-20 / 157 : ℝ):ℂ) + ((-560 / 157:ℝ):ℂ)*I := by
    have hne : ((1/2 + (14:ℝ)*I) - 1) ≠ 0 := by intro h; have := congrArg Complex.im h; simp at this
    rw [div_eq_iff hne]; apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im] <;> norm_num
  rw [hdiv]; apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im, Complex.inv_re, Complex.inv_im, Complex.normSq] <;> norm_num
theorem zt14_Tre :
    ((34507470019300599 / 72057594037927936) : ℝ) ≤ (((50:ℕ):ℂ)^(1-((1/2:ℂ) + (14:ℂ)*Complex.I))/(((1/2:ℂ) + (14:ℂ)*Complex.I)-1) + ((50:ℕ):ℂ)^(-((1/2:ℂ) + (14:ℂ)*Complex.I))/2 + (bernoulli 2:ℂ)*(((1/2:ℂ) + (14:ℂ)*Complex.I)*(((50:ℕ):ℝ))^(-((1/2:ℂ) + (14:ℂ)*Complex.I)-1))/2).re
      ∧ (((50:ℕ):ℂ)^(1-((1/2:ℂ) + (14:ℂ)*Complex.I))/(((1/2:ℂ) + (14:ℂ)*Complex.I)-1) + ((50:ℕ):ℂ)^(-((1/2:ℂ) + (14:ℂ)*Complex.I))/2 + (bernoulli 2:ℂ)*(((1/2:ℂ) + (14:ℂ)*Complex.I)*(((50:ℕ):ℝ))^(-((1/2:ℂ) + (14:ℂ)*Complex.I)-1))/2).re ≤ (552804411908631293 / 1152921504606846976) := by
  rw [(ForgeTailTerms.tail_re_im ((1/2:ℂ) + (14:ℂ)*Complex.I) 50 (by norm_num) (by intro h; have := congrArg Complex.im h; simp at this) (70357 / 188400) (-166901 / 47100) (by have h := zt14_Bval; convert h using 2 <;> push_cast <;> ring)).1]
  have hP := re_term_50
  have hQ := im_term_50
  norm_num at hP hQ ⊢
  obtain ⟨hplo,hphi⟩ := hP; obtain ⟨hqlo,hqhi⟩ := hQ
  constructor <;> nlinarith [hplo,hphi,hqlo,hqhi]
theorem zt14_Tim :
    ((179402701777766013 / 1152921504606846976) : ℝ) ≤ (((50:ℕ):ℂ)^(1-((1/2:ℂ) + (14:ℂ)*Complex.I))/(((1/2:ℂ) + (14:ℂ)*Complex.I)-1) + ((50:ℕ):ℂ)^(-((1/2:ℂ) + (14:ℂ)*Complex.I))/2 + (bernoulli 2:ℂ)*(((1/2:ℂ) + (14:ℂ)*Complex.I)*(((50:ℕ):ℝ))^(-((1/2:ℂ) + (14:ℂ)*Complex.I)-1))/2).im
      ∧ (((50:ℕ):ℂ)^(1-((1/2:ℂ) + (14:ℂ)*Complex.I))/(((1/2:ℂ) + (14:ℂ)*Complex.I)-1) + ((50:ℕ):ℂ)^(-((1/2:ℂ) + (14:ℂ)*Complex.I))/2 + (bernoulli 2:ℂ)*(((1/2:ℂ) + (14:ℂ)*Complex.I)*(((50:ℕ):ℝ))^(-((1/2:ℂ) + (14:ℂ)*Complex.I)-1))/2).im ≤ (90043072445746405 / 576460752303423488) := by
  rw [(ForgeTailTerms.tail_re_im ((1/2:ℂ) + (14:ℂ)*Complex.I) 50 (by norm_num) (by intro h; have := congrArg Complex.im h; simp at this) (70357 / 188400) (-166901 / 47100) (by have h := zt14_Bval; convert h using 2 <;> push_cast <;> ring)).2]
  have hP := re_term_50
  have hQ := im_term_50
  norm_num at hP hQ ⊢
  obtain ⟨hplo,hphi⟩ := hP; obtain ⟨hqlo,hqhi⟩ := hQ
  constructor <;> nlinarith [hplo,hphi,hqlo,hqhi]
theorem zt14_emf_re :
    ((17792401065516471 / 1152921504606846976) : ℝ) ≤ (emZetaFinite3 ((1/2:ℂ) + (14:ℂ)*Complex.I) 50).re
      ∧ (emZetaFinite3 ((1/2:ℂ) + (14:ℂ)*Complex.I) 50).re ≤ (16752539938961135 / 576460752303423488) := by
  rw [ZetaEMSum.emZetaFinite3_eq_dirichlet (by intro h; have := congrArg Complex.re h; simp at this) (by intro h; have := congrArg Complex.im h; simp at this) (by norm_num) (by norm_num)]
  rw [show (∑ n ∈ Finset.Ico 1 50, (((n:ℕ):ℂ) ^ (-((1/2:ℂ) + (14:ℂ)*Complex.I)))) + ((50:ℕ):ℂ)^(1-((1/2:ℂ) + (14:ℂ)*Complex.I))/(((1/2:ℂ) + (14:ℂ)*Complex.I)-1) + ((50:ℕ):ℂ)^(-((1/2:ℂ) + (14:ℂ)*Complex.I))/2 + (bernoulli 2:ℂ)*(((1/2:ℂ) + (14:ℂ)*Complex.I)*(((50:ℕ):ℝ))^(-((1/2:ℂ) + (14:ℂ)*Complex.I)-1))/2
      = (∑ n ∈ Finset.Ico 1 50, (((n:ℕ):ℂ) ^ (-((1/2:ℂ) + (14:ℂ)*Complex.I)))) + (((50:ℕ):ℂ)^(1-((1/2:ℂ) + (14:ℂ)*Complex.I))/(((1/2:ℂ) + (14:ℂ)*Complex.I)-1) + ((50:ℕ):ℂ)^(-((1/2:ℂ) + (14:ℂ)*Complex.I))/2 + (bernoulli 2:ℂ)*(((1/2:ℂ) + (14:ℂ)*Complex.I)*(((50:ℕ):ℝ))^(-((1/2:ℂ) + (14:ℂ)*Complex.I)-1))/2) by ring]
  rw [Complex.add_re]
  have hs := reSum
  have ht := zt14_Tre
  constructor <;> [linarith [hs.1, ht.1]; linarith [hs.2, ht.2]]
theorem zt14_emf_im :
    ((-126928865135240565 / 1152921504606846976) : ℝ) ≤ (emZetaFinite3 ((1/2:ℂ) + (14:ℂ)*Complex.I) 50).im
      ∧ (emZetaFinite3 ((1/2:ℂ) + (14:ℂ)*Complex.I) 50).im ≤ (-111166904960220091 / 1152921504606846976) := by
  rw [ZetaEMSum.emZetaFinite3_eq_dirichlet (by intro h; have := congrArg Complex.re h; simp at this) (by intro h; have := congrArg Complex.im h; simp at this) (by norm_num) (by norm_num)]
  rw [show (∑ n ∈ Finset.Ico 1 50, (((n:ℕ):ℂ) ^ (-((1/2:ℂ) + (14:ℂ)*Complex.I)))) + ((50:ℕ):ℂ)^(1-((1/2:ℂ) + (14:ℂ)*Complex.I))/(((1/2:ℂ) + (14:ℂ)*Complex.I)-1) + ((50:ℕ):ℂ)^(-((1/2:ℂ) + (14:ℂ)*Complex.I))/2 + (bernoulli 2:ℂ)*(((1/2:ℂ) + (14:ℂ)*Complex.I)*(((50:ℕ):ℝ))^(-((1/2:ℂ) + (14:ℂ)*Complex.I)-1))/2
      = (∑ n ∈ Finset.Ico 1 50, (((n:ℕ):ℂ) ^ (-((1/2:ℂ) + (14:ℂ)*Complex.I)))) + (((50:ℕ):ℂ)^(1-((1/2:ℂ) + (14:ℂ)*Complex.I))/(((1/2:ℂ) + (14:ℂ)*Complex.I)-1) + ((50:ℕ):ℂ)^(-((1/2:ℂ) + (14:ℂ)*Complex.I))/2 + (bernoulli 2:ℂ)*(((1/2:ℂ) + (14:ℂ)*Complex.I)*(((50:ℕ):ℝ))^(-((1/2:ℂ) + (14:ℂ)*Complex.I)-1))/2) by ring]
  rw [Complex.add_im]
  have hs := imSum
  have ht := zt14_Tim
  constructor <;> [linarith [hs.1, ht.1]; linarith [hs.2, ht.2]]
theorem zt14_zeta_re :
    ((16293603109527569 / 1152921504606846976) : ℝ) ≤ (riemannZeta ((1/2:ℂ) + (14:ℂ)*Complex.I)).re
      ∧ (riemannZeta ((1/2:ℂ) + (14:ℂ)*Complex.I)).re ≤ (8750969458477793 / 288230376151711744) := by
  have hef := zt14_emf_re
  have htail : |(riemannZeta ((1/2:ℂ) + (14:ℂ)*Complex.I)).re - (emZetaFinite3 ((1/2:ℂ) + (14:ℂ)*Complex.I) 50).re| ≤ (13 / 10000) := by
    calc |(riemannZeta ((1/2:ℂ) + (14:ℂ)*Complex.I)).re - (emZetaFinite3 ((1/2:ℂ) + (14:ℂ)*Complex.I) 50).re|
        = |(riemannZeta ((1/2:ℂ) + (14:ℂ)*Complex.I) - emZetaFinite3 ((1/2:ℂ) + (14:ℂ)*Complex.I) 50).re| := by rw [Complex.sub_re]
      _ ≤ ‖riemannZeta ((1/2:ℂ) + (14:ℂ)*Complex.I) - emZetaFinite3 ((1/2:ℂ) + (14:ℂ)*Complex.I) 50‖ := Complex.abs_re_le_norm _
      _ ≤ (13 / 10000) := ForgeTail.zeta_tail_t14
  rw [abs_le] at htail
  constructor <;> [linarith [hef.1, htail.1]; linarith [hef.2, htail.2]]
theorem zt14_zeta_im :
    ((-128427663091229467 / 1152921504606846976) : ℝ) ≤ (riemannZeta ((1/2:ℂ) + (14:ℂ)*Complex.I)).im
      ∧ (riemannZeta ((1/2:ℂ) + (14:ℂ)*Complex.I)).im ≤ (-109668107004231189 / 1152921504606846976) := by
  have hef := zt14_emf_im
  have htail : |(riemannZeta ((1/2:ℂ) + (14:ℂ)*Complex.I)).im - (emZetaFinite3 ((1/2:ℂ) + (14:ℂ)*Complex.I) 50).im| ≤ (13 / 10000) := by
    calc |(riemannZeta ((1/2:ℂ) + (14:ℂ)*Complex.I)).im - (emZetaFinite3 ((1/2:ℂ) + (14:ℂ)*Complex.I) 50).im|
        = |(riemannZeta ((1/2:ℂ) + (14:ℂ)*Complex.I) - emZetaFinite3 ((1/2:ℂ) + (14:ℂ)*Complex.I) 50).im| := by rw [Complex.sub_im]
      _ ≤ ‖riemannZeta ((1/2:ℂ) + (14:ℂ)*Complex.I) - emZetaFinite3 ((1/2:ℂ) + (14:ℂ)*Complex.I) 50‖ := Complex.abs_im_le_norm _
      _ ≤ (13 / 10000) := ForgeTail.zeta_tail_t14
  rw [abs_le] at htail
  constructor <;> [linarith [hef.1, htail.1]; linarith [hef.2, htail.2]]

end ForgeZeta14