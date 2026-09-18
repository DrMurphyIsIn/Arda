import ForgePhiFold14
import ForgePhiFold15
import ForgeRate
import TrigReduce
import CertVerify
import ForgeLogBracket
import TaylorKernels
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real ThetaGap
namespace ForgeThetaBox
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

theorem logpibox : ((153643043/134217728):ℝ) ≤ Real.log Real.pi ∧ Real.log Real.pi ≤ ((307286091/268435456):ℝ) := by
  obtain ⟨hpl, hph⟩ := CertVerify.pi_bracket
  have hExpLo : Real.exp (153643043/134217728) ≤ Real.pi := by
    have h := ForgeLogBracket.exp_le_rat (q := (153643043/134217728)) (f := (19425315/134217728)) (E1hi := (2.7182818286)) (seriesUp := (32058734896338220065116414025316636313190532931921172019825548570954680312570126495805081892913965661740879378399023359/27739012362261713365444444230501104118776136446407674454235598556588988127134036270435643443438980611127866105175998464)) (k := 1) (N := 14)
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) Real.exp_one_lt_d9.le (by norm_num) (by unfold TaylorKernels.expSeries TaylorKernels.expRem; norm_num [Finset.sum_range_succ])
    have hn : (2.7182818286 : ℝ) ^ 1 * (32058734896338220065116414025316636313190532931921172019825548570954680312570126495805081892913965661740879378399023359/27739012362261713365444444230501104118776136446407674454235598556588988127134036270435643443438980611127866105175998464) ≤ (3.14159265358979323846:ℝ) := by norm_num
    exact le_trans h (le_trans hn hpl)
  have hExpHi : Real.pi ≤ Real.exp (307286091/268435456) := by
    have h := ForgeLogBracket.rat_le_exp (q := (307286091/268435456)) (f := (38850635/268435456)) (E1lo := (2.7182818283)) (seriesLo := (189709386167077142048127067852342437310884584573107931212200659688987055279213055594109448208274080785117723169387001526394345419/164147179454289074120587000589978145333501070304494836968756989969535043875146040706984759513216574720353100627990314176168853504)) (k := 1) (N := 14)
      (by norm_num) (by rw [abs_le]; constructor <;> norm_num) (by norm_num) Real.exp_one_gt_d9.le (by norm_num) (by norm_num) (by unfold TaylorKernels.expSeries TaylorKernels.expRem; norm_num [Finset.sum_range_succ])
    have hn : (3.14159265358979323847:ℝ) ≤ (2.7182818283 : ℝ) ^ 1 * (189709386167077142048127067852342437310884584573107931212200659688987055279213055594109448208274080785117723169387001526394345419/164147179454289074120587000589978145333501070304494836968756989969535043875146040706984759513216574720353100627990314176168853504) := by norm_num
    exact le_trans (le_trans hph hn) h
  exact CertVerify.ln_of_exp_bracket Real.pi_pos hExpLo hExpHi

theorem trigA_14 :
    (-145286302571/1000000000000:ℝ) ≤ Real.cos (6859/4000) ∧ Real.cos (6859/4000) ≤ (-71626625391/500000000000) ∧ (988314953779/1000000000000:ℝ) ≤ Real.sin (6859/4000) ∧ Real.sin (6859/4000) ≤ (989815566673/1000000000000) := by
  have hy : |(6859/64000:ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num
  obtain ⟨hc0lo, hc0hi⟩ := TrigReduce.cos_base_interval (y := (6859/64000)) hy (clo := 994250223569/1000000000000) (chi := 24856599141/25000000000) (by norm_num) (by norm_num)
  obtain ⟨hs0lo, hs0hi⟩ := TrigReduce.sin_base_interval (y := (6859/64000)) hy (slo := 106965396447/1000000000000) (shi := 106968034927/1000000000000) (by norm_num) (by norm_num)
  have hcd1 := TrigReduce.cos_double_interval (y := (6859/64000)) (clo := 994250223569/1000000000000) (chi := 24856599141/25000000000) (clo' := 977067014133/1000000000000) (chi' := 488560833371/500000000000) hc0lo hc0hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd1 := TrigReduce.sin_double_interval (y := (6859/64000)) (clo := 994250223569/1000000000000) (chi := 24856599141/25000000000) (slo := 106965396447/1000000000000) (shi := 106968034927/1000000000000) (slo' := 106350369331/500000000000) (shi' := 26588615651/125000000000) hc0lo hc0hi hs0lo hs0hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*(6859/64000) = (2:ℝ)^1 * (6859/64000) by ring] at hcd1 hsd1
  obtain ⟨hc1lo, hc1hi⟩ := hcd1
  obtain ⟨hs1lo, hs1hi⟩ := hsd1
  have hcd2 := TrigReduce.cos_double_interval (y := (2:ℝ)^1 * (6859/64000)) (clo := 977067014133/1000000000000) (chi := 488560833371/500000000000) (clo' := 227329975053/250000000000) (chi' := 181906700647/200000000000) hc1lo hc1hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd2 := TrigReduce.sin_double_interval (y := (2:ℝ)^1 * (6859/64000)) (clo := 977067014133/1000000000000) (chi := 488560833371/500000000000) (slo := 106350369331/500000000000) (shi := 26588615651/125000000000) (slo' := 83129150251/200000000000) (shi' := 207842499531/500000000000) hc1lo hc1hi hs1lo hs1hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^1 * (6859/64000)) = (2:ℝ)^2 * (6859/64000) by ring] at hcd2 hsd2
  obtain ⟨hc2lo, hc2hi⟩ := hcd2
  obtain ⟨hs2lo, hs2hi⟩ := hsd2
  have hcd3 := TrigReduce.cos_double_interval (y := (2:ℝ)^2 * (6859/64000)) (clo := 227329975053/250000000000) (chi := 181906700647/200000000000) (clo' := 326862680921/500000000000) (chi' := 130900477403/200000000000) hc2lo hc2hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd3 := TrigReduce.sin_double_interval (y := (2:ℝ)^2 * (6859/64000)) (clo := 227329975053/250000000000) (chi := 181906700647/200000000000) (slo := 83129150251/200000000000) (shi := 207842499531/500000000000) (slo' := 188977476527/250000000000) (shi' := 2362996459/3125000000) hc2lo hc2hi hs2lo hs2hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^2 * (6859/64000)) = (2:ℝ)^3 * (6859/64000) by ring] at hcd3 hsd3
  obtain ⟨hc3lo, hc3hi⟩ := hcd3
  obtain ⟨hs3lo, hs3hi⟩ := hsd3
  have hcd4 := TrigReduce.cos_double_interval (y := (2:ℝ)^3 * (6859/64000)) (clo := 326862680921/500000000000) (chi := 130900477403/200000000000) (clo' := -145286302571/1000000000000) (chi' := -71626625391/500000000000) hc3lo hc3hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd4 := TrigReduce.sin_double_interval (y := (2:ℝ)^3 * (6859/64000)) (clo := 326862680921/500000000000) (chi := 130900477403/200000000000) (slo := 188977476527/250000000000) (shi := 2362996459/3125000000) (slo' := 988314953779/1000000000000) (shi' := 989815566673/1000000000000) hc3lo hc3hi hs3lo hs3hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^3 * (6859/64000)) = (2:ℝ)^4 * (6859/64000) by ring] at hcd4 hsd4
  obtain ⟨hc4lo, hc4hi⟩ := hcd4
  obtain ⟨hs4lo, hs4hi⟩ := hsd4
  rw [show (2:ℝ)^4 * (6859/64000) = (6859/4000:ℝ) by norm_num] at hc4lo hc4hi hs4lo hs4hi
  exact ⟨hc4lo, hc4hi, hs4lo, hs4hi⟩

theorem trigB_14 :
    (-337877485237/1000000000000:ℝ) ≤ Real.cos (191289/100000) ∧ Real.cos (191289/100000) ≤ (-83797671147/250000000000) ∧ (37596679869/40000000000:ℝ) ≤ Real.sin (191289/100000) ∧ Real.sin (191289/100000) ≤ (94230508271/100000000000) := by
  have hy : |(191289/1600000:ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num
  obtain ⟨hc0lo, hc0hi⟩ := TrigReduce.cos_base_interval (y := (191289/1600000)) hy (clo := 992842585353/1000000000000) (chi := 496431933589/500000000000) (by norm_num) (by norm_num)
  obtain ⟨hs0lo, hs0hi⟩ := TrigReduce.sin_base_interval (y := (191289/1600000)) hy (slo := 11926876961/100000000000) (shi := 119272855723/1000000000000) (by norm_num) (by norm_num)
  have hcd1 := TrigReduce.cos_double_interval (y := (191289/1600000)) (clo := 992842585353/1000000000000) (chi := 496431933589/500000000000) (clo' := 971472798579/1000000000000) (chi' := 971557317497/1000000000000) hc0lo hc0hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd1 := TrigReduce.sin_double_interval (y := (191289/1600000)) (clo := 992842585353/1000000000000) (chi := 496431933589/500000000000) (slo := 11926876961/100000000000) (shi := 119272855723/1000000000000) (slo' := 236830227141/1000000000000) (shi' := 236843417567/1000000000000) hc0lo hc0hi hs0lo hs0hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*(191289/1600000) = (2:ℝ)^1 * (191289/1600000) by ring] at hcd1 hsd1
  obtain ⟨hc1lo, hc1hi⟩ := hcd1
  obtain ⟨hs1lo, hs1hi⟩ := hsd1
  have hcd2 := TrigReduce.cos_double_interval (y := (2:ℝ)^1 * (191289/1600000)) (clo := 971472798579/1000000000000) (chi := 971557317497/1000000000000) (clo' := 221879699189/250000000000) (chi' := 177569448473/200000000000) hc1lo hc1hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd2 := TrigReduce.sin_double_interval (y := (2:ℝ)^1 * (191289/1600000)) (clo := 971472798579/1000000000000) (chi := 971557317497/1000000000000) (slo := 236830227141/1000000000000) (shi := 236843417567/1000000000000) (slo' := 57518530887/125000000000) (shi' := 230106955439/500000000000) hc1lo hc1hi hs1lo hs1hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^1 * (191289/1600000)) = (2:ℝ)^2 * (191289/1600000) by ring] at hcd2 hsd2
  obtain ⟨hc2lo, hc2hi⟩ := hcd2
  obtain ⟨hs2lo, hs2hi⟩ := hsd2
  have hcd3 := TrigReduce.cos_double_interval (y := (2:ℝ)^2 * (191289/1600000)) (clo := 221879699189/250000000000) (chi := 177569448473/200000000000) (clo' := 575379229189/1000000000000) (chi' := 18017045361/31250000000) hc2lo hc2hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd3 := TrigReduce.sin_double_interval (y := (2:ℝ)^2 * (191289/1600000)) (clo := 221879699189/250000000000) (chi := 177569448473/200000000000) (slo := 57518530887/125000000000) (shi := 230106955439/500000000000) (slo' := 816780437183/1000000000000) (shi' := 51074956459/62500000000) hc2lo hc2hi hs2lo hs2hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^2 * (191289/1600000)) = (2:ℝ)^3 * (191289/1600000) by ring] at hcd3 hsd3
  obtain ⟨hc3lo, hc3hi⟩ := hcd3
  obtain ⟨hs3lo, hs3hi⟩ := hsd3
  have hcd4 := TrigReduce.cos_double_interval (y := (2:ℝ)^3 * (191289/1600000)) (clo := 575379229189/1000000000000) (chi := 18017045361/31250000000) (clo' := -337877485237/1000000000000) (chi' := -83797671147/250000000000) hc3lo hc3hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd4 := TrigReduce.sin_double_interval (y := (2:ℝ)^3 * (191289/1600000)) (clo := 575379229189/1000000000000) (chi := 18017045361/31250000000) (slo := 816780437183/1000000000000) (shi := 51074956459/62500000000) (slo' := 37596679869/40000000000) (shi' := 94230508271/100000000000) hc3lo hc3hi hs3lo hs3hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^3 * (191289/1600000)) = (2:ℝ)^4 * (191289/1600000) by ring] at hcd4 hsd4
  obtain ⟨hc4lo, hc4hi⟩ := hcd4
  obtain ⟨hs4lo, hs4hi⟩ := hsd4
  rw [show (2:ℝ)^4 * (191289/1600000) = (191289/100000:ℝ) by norm_num] at hc4lo hc4hi hs4lo hs4hi
  exact ⟨hc4lo, hc4hi, hs4lo, hs4hi⟩

theorem cossin_14 (Λ : ℝ) (hΛ : Filter.Tendsto (imLnVal (1/4) (14/2)) Filter.atTop (nhds Λ)) :
    (-36/100 : ℝ) ≤ Real.cos (Λ - (14/2)*Real.log Real.pi)
    ∧ Real.cos (Λ - (14/2)*Real.log Real.pi) ≤ (-6/100 : ℝ)
    ∧ (-100/100 : ℝ) ≤ Real.sin (Λ - (14/2)*Real.log Real.pi)
    ∧ Real.sin (Λ - (14/2)*Real.log Real.pi) ≤ (-93/100 : ℝ) := by
  have hrate := ForgeRate.rate_at (1/4) (14/2) (by norm_num) Λ hΛ 200 (by norm_num)
  rw [abs_le] at hrate
  norm_num at hrate
  obtain ⟨him_lo, him_hi⟩ := ForgePhiFold14.imbox
  obtain ⟨hlp_lo, hlp_hi⟩ := logpibox
  set φ : ℝ := Λ - (14/2)*Real.log Real.pi with hφ
  have hφlo : (-191289/100000:ℝ) ≤ φ := by
    rw [hφ]; nlinarith [hrate.1, hrate.2, him_lo, him_hi, hlp_lo, hlp_hi]
  have hφhi : φ ≤ (-6859/4000:ℝ) := by
    rw [hφ]; nlinarith [hrate.1, hrate.2, him_lo, him_hi, hlp_lo, hlp_hi]
  obtain ⟨hcaL, hcaH, hsaL, hsaH⟩ := trigA_14
  obtain ⟨hcbL, hcbH, hsbL, hsbH⟩ := trigB_14
  obtain ⟨hpl, hph⟩ := CertVerify.pi_bracket
  have hmphi_lo : (6859/4000:ℝ) ≤ -φ := by linarith [hφhi]
  have hmphi_hi : -φ ≤ (191289/100000:ℝ) := by linarith [hφlo]
  have hcos_eq : Real.cos φ = Real.cos (-φ) := by rw [Real.cos_neg]
  have h0a : (0:ℝ) ≤ (6859/4000:ℝ) := by norm_num
  have hbpi : (191289/100000:ℝ) ≤ Real.pi := by linarith [hpl]
  have hab : (6859/4000:ℝ) ≤ (191289/100000:ℝ) := by norm_num
  have hc_up : Real.cos (-φ) ≤ Real.cos (6859/4000) := Real.cos_le_cos_of_nonneg_of_le_pi h0a (by linarith [hpl]) hmphi_lo
  have hc_lo : Real.cos (191289/100000) ≤ Real.cos (-φ) := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) hbpi hmphi_hi
  have hsin_eq : Real.sin φ = - Real.sin (-φ) := by rw [Real.sin_neg, neg_neg]
  have hsA' : Real.sin (6859/4000) = Real.sin (Real.pi - 6859/4000) := by rw [Real.sin_pi_sub]
  have hsB' : Real.sin (191289/100000) = Real.sin (Real.pi - 191289/100000) := by rw [Real.sin_pi_sub]
  have hsP' : Real.sin (-φ) = Real.sin (Real.pi - (-φ)) := by rw [Real.sin_pi_sub]
  have hlow1 : Real.sin (Real.pi - 191289/100000) ≤ Real.sin (Real.pi - (-φ)) := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [hpl, hph]) (by linarith [hpl, hph]) (by linarith)
  have hsin_ge_b : Real.sin (191289/100000) ≤ Real.sin (-φ) := by rw [hsB', hsP']; exact hlow1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hcos_eq]; linarith [hc_lo, hcbL]
  · rw [hcos_eq]; linarith [hc_up, hcaH]
  · rw [hsin_eq]; linarith [Real.sin_le_one (-φ)]
  · rw [hsin_eq]; linarith [hsin_ge_b, hsbL]

theorem trigA_15 :
    (137513171173/500000000000:ℝ) ≤ Real.cos (129139/100000) ∧ Real.cos (129139/100000) ≤ (275869447297/1000000000000) ∧ (960845351849/1000000000000:ℝ) ≤ Real.sin (129139/100000) ∧ Real.sin (129139/100000) ≤ (192253010339/200000000000) := by
  have hy : |(129139/1600000:ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num
  obtain ⟨hc0lo, hc0hi⟩ := TrigReduce.cos_base_interval (y := (129139/1600000)) hy (clo := 996740586329/1000000000000) (chi := 199349001381/200000000000) (by norm_num) (by norm_num)
  obtain ⟨hs0lo, hs0hi⟩ := TrigReduce.sin_base_interval (y := (129139/1600000)) hy (slo := 80623818959/1000000000000) (shi := 1259760433/15625000000) (by norm_num) (by norm_num)
  have hcd1 := TrigReduce.cos_double_interval (y := (129139/1600000)) (clo := 996740586329/1000000000000) (chi := 199349001381/200000000000) (clo' := 986983592869/1000000000000) (chi' := 493500608791/500000000000) hc0lo hc0hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd1 := TrigReduce.sin_double_interval (y := (129139/1600000)) (clo := 996740586329/1000000000000) (chi := 199349001381/200000000000) (slo := 80623818959/1000000000000) (shi := 1259760433/15625000000) (slo' := 160722065161/1000000000000) (shi' := 2511319843/15625000000) hc0lo hc0hi hs0lo hs0hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*(129139/1600000) = (2:ℝ)^1 * (129139/1600000) by ring] at hcd1 hsd1
  obtain ⟨hc1lo, hc1hi⟩ := hcd1
  obtain ⟨hs1lo, hs1hi⟩ := hsd1
  have hcd2 := TrigReduce.cos_double_interval (y := (2:ℝ)^1 * (129139/1600000)) (clo := 986983592869/1000000000000) (chi := 493500608791/500000000000) (clo' := 29633538287/31250000000) (chi' := 474171403509/500000000000) hc1lo hc1hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd2 := TrigReduce.sin_double_interval (y := (2:ℝ)^1 * (129139/1600000)) (clo := 986983592869/1000000000000) (chi := 493500608791/500000000000) (slo := 160722065161/1000000000000) (shi := 2511319843/15625000000) (slo' := 6345201653/20000000000) (shi' := 317270495077/1000000000000) hc1lo hc1hi hs1lo hs1hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^1 * (129139/1600000)) = (2:ℝ)^2 * (129139/1600000) by ring] at hcd2 hsd2
  obtain ⟨hc2lo, hc2hi⟩ := hcd2
  obtain ⟨hs2lo, hs2hi⟩ := hsd2
  have hcd3 := TrigReduce.cos_double_interval (y := (2:ℝ)^2 * (129139/1600000)) (clo := 29633538287/31250000000) (chi := 474171403509/500000000000) (clo' := 499027637/625000000) (chi' := 798708159247/1000000000000) hc2lo hc2hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd3 := TrigReduce.sin_double_interval (y := (2:ℝ)^2 * (129139/1600000)) (clo := 29633538287/31250000000) (chi := 474171403509/500000000000) (slo := 6345201653/20000000000) (shi := 317270495077/1000000000000) (slo' := 75212310449/125000000000) (shi' := 150440595943/250000000000) hc2lo hc2hi hs2lo hs2hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^2 * (129139/1600000)) = (2:ℝ)^3 * (129139/1600000) by ring] at hcd3 hsd3
  obtain ⟨hc3lo, hc3hi⟩ := hcd3
  obtain ⟨hs3lo, hs3hi⟩ := hsd3
  have hcd4 := TrigReduce.cos_double_interval (y := (2:ℝ)^3 * (129139/1600000)) (clo := 499027637/625000000) (chi := 798708159247/1000000000000) (clo' := 137513171173/500000000000) (chi' := 275869447297/1000000000000) hc3lo hc3hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd4 := TrigReduce.sin_double_interval (y := (2:ℝ)^3 * (129139/1600000)) (clo := 499027637/625000000) (chi := 798708159247/1000000000000) (slo := 75212310449/125000000000) (shi := 150440595943/250000000000) (slo' := 960845351849/1000000000000) (shi' := 192253010339/200000000000) hc3lo hc3hi hs3lo hs3hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^3 * (129139/1600000)) = (2:ℝ)^4 * (129139/1600000) by ring] at hcd4 hsd4
  obtain ⟨hc4lo, hc4hi⟩ := hcd4
  obtain ⟨hs4lo, hs4hi⟩ := hsd4
  rw [show (2:ℝ)^4 * (129139/1600000) = (129139/100000:ℝ) by norm_num] at hc4lo hc4hi hs4lo hs4hi
  exact ⟨hc4lo, hc4hi, hs4lo, hs4hi⟩

theorem trigB_15 :
    (8069001409/125000000000:ℝ) ≤ Real.cos (30099/20000) ∧ Real.cos (30099/20000) ≤ (13187504309/200000000000) ∧ (19941601031/20000000000:ℝ) ≤ Real.sin (30099/20000) ∧ Real.sin (30099/20000) ≤ (199584672227/200000000000) := by
  have hy : |(30099/320000:ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num
  obtain ⟨hc0lo, hc0hi⟩ := TrigReduce.cos_base_interval (y := (30099/320000)) hy (clo := 995572340301/1000000000000) (chi := 497790246837/500000000000) (by norm_num) (by norm_num)
  obtain ⟨hs0lo, hs0hi⟩ := TrigReduce.sin_base_interval (y := (30099/320000)) hy (slo := 23479974781/250000000000) (shi := 46960732287/500000000000) (by norm_num) (by norm_num)
  have hcd1 := TrigReduce.cos_double_interval (y := (30099/320000)) (clo := 995572340301/1000000000000) (chi := 497790246837/500000000000) (clo' := 982328569543/1000000000000) (chi' := 98236103877/100000000000) hc0lo hc0hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd1 := TrigReduce.sin_double_interval (y := (30099/320000)) (clo := 995572340301/1000000000000) (chi := 497790246837/500000000000) (slo := 23479974781/250000000000) (shi := 46960732287/500000000000) (slo' := 93504053771/500000000000) (shi' := 23376594517/125000000000) hc0lo hc0hi hs0lo hs0hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*(30099/320000) = (2:ℝ)^1 * (30099/320000) by ring] at hcd1 hsd1
  obtain ⟨hc1lo, hc1hi⟩ := hcd1
  obtain ⟨hs1lo, hs1hi⟩ := hsd1
  have hcd2 := TrigReduce.cos_double_interval (y := (2:ℝ)^1 * (30099/320000)) (clo := 982328569543/1000000000000) (chi := 98236103877/100000000000) (clo' := 929938837079/1000000000000) (chi' := 232516605247/250000000000) hc1lo hc1hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd2 := TrigReduce.sin_double_interval (y := (2:ℝ)^1 * (30099/320000)) (clo := 982328569543/1000000000000) (chi := 98236103877/100000000000) (slo := 93504053771/500000000000) (shi := 23376594517/125000000000) (slo' := 91851703387/250000000000) (shi' := 91857022691/250000000000) hc1lo hc1hi hs1lo hs1hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^1 * (30099/320000)) = (2:ℝ)^2 * (30099/320000) by ring] at hcd2 hsd2
  obtain ⟨hc2lo, hc2hi⟩ := hcd2
  obtain ⟨hs2lo, hs2hi⟩ := hsd2
  have hcd3 := TrigReduce.cos_double_interval (y := (2:ℝ)^2 * (30099/320000)) (clo := 929938837079/1000000000000) (chi := 232516605247/250000000000) (clo' := 364786240707/500000000000) (chi' := 7300470949/10000000000) hc2lo hc2hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd3 := TrigReduce.sin_double_interval (y := (2:ℝ)^2 * (30099/320000)) (clo := 929938837079/1000000000000) (chi := 232516605247/250000000000) (slo := 91851703387/250000000000) (shi := 91857022691/250000000000) (slo' := 13666634597/20000000000) (shi' := 85433132337/125000000000) hc2lo hc2hi hs2lo hs2hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^2 * (30099/320000)) = (2:ℝ)^3 * (30099/320000) by ring] at hcd3 hsd3
  obtain ⟨hc3lo, hc3hi⟩ := hcd3
  obtain ⟨hs3lo, hs3hi⟩ := hsd3
  have hcd4 := TrigReduce.cos_double_interval (y := (2:ℝ)^3 * (30099/320000)) (clo := 364786240707/500000000000) (chi := 7300470949/10000000000) (clo' := 8069001409/125000000000) (chi' := 13187504309/200000000000) hc3lo hc3hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd4 := TrigReduce.sin_double_interval (y := (2:ℝ)^3 * (30099/320000)) (clo := 364786240707/500000000000) (chi := 7300470949/10000000000) (slo := 13666634597/20000000000) (shi := 85433132337/125000000000) (slo' := 19941601031/20000000000) (shi' := 199584672227/200000000000) hc3lo hc3hi hs3lo hs3hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^3 * (30099/320000)) = (2:ℝ)^4 * (30099/320000) by ring] at hcd4 hsd4
  obtain ⟨hc4lo, hc4hi⟩ := hcd4
  obtain ⟨hs4lo, hs4hi⟩ := hsd4
  rw [show (2:ℝ)^4 * (30099/320000) = (30099/20000:ℝ) by norm_num] at hc4lo hc4hi hs4lo hs4hi
  exact ⟨hc4lo, hc4hi, hs4lo, hs4hi⟩

theorem cossin_15 (Λ : ℝ) (hΛ : Filter.Tendsto (imLnVal (1/4) (15/2)) Filter.atTop (nhds Λ)) :
    (5/100 : ℝ) ≤ Real.cos (Λ - (15/2)*Real.log Real.pi)
    ∧ Real.cos (Λ - (15/2)*Real.log Real.pi) ≤ (35/100 : ℝ)
    ∧ (-100/100 : ℝ) ≤ Real.sin (Λ - (15/2)*Real.log Real.pi)
    ∧ Real.sin (Λ - (15/2)*Real.log Real.pi) ≤ (-93/100 : ℝ) := by
  have hrate := ForgeRate.rate_at (1/4) (15/2) (by norm_num) Λ hΛ 200 (by norm_num)
  rw [abs_le] at hrate
  norm_num at hrate
  obtain ⟨him_lo, him_hi⟩ := ForgePhiFold15.imbox
  obtain ⟨hlp_lo, hlp_hi⟩ := logpibox
  set φ : ℝ := Λ - (15/2)*Real.log Real.pi with hφ
  have hφlo : (-30099/20000:ℝ) ≤ φ := by
    rw [hφ]; nlinarith [hrate.1, hrate.2, him_lo, him_hi, hlp_lo, hlp_hi]
  have hφhi : φ ≤ (-129139/100000:ℝ) := by
    rw [hφ]; nlinarith [hrate.1, hrate.2, him_lo, him_hi, hlp_lo, hlp_hi]
  obtain ⟨hcaL, hcaH, hsaL, hsaH⟩ := trigA_15
  obtain ⟨hcbL, hcbH, hsbL, hsbH⟩ := trigB_15
  obtain ⟨hpl, hph⟩ := CertVerify.pi_bracket
  have hmphi_lo : (129139/100000:ℝ) ≤ -φ := by linarith [hφhi]
  have hmphi_hi : -φ ≤ (30099/20000:ℝ) := by linarith [hφlo]
  have hcos_eq : Real.cos φ = Real.cos (-φ) := by rw [Real.cos_neg]
  have h0a : (0:ℝ) ≤ (129139/100000:ℝ) := by norm_num
  have hbpi : (30099/20000:ℝ) ≤ Real.pi := by linarith [hpl]
  have hab : (129139/100000:ℝ) ≤ (30099/20000:ℝ) := by norm_num
  have hc_up : Real.cos (-φ) ≤ Real.cos (129139/100000) := Real.cos_le_cos_of_nonneg_of_le_pi h0a (by linarith [hpl]) hmphi_lo
  have hc_lo : Real.cos (30099/20000) ≤ Real.cos (-φ) := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) hbpi hmphi_hi
  have hsin_eq : Real.sin φ = - Real.sin (-φ) := by rw [Real.sin_neg, neg_neg]
  have hsin_ge_a : Real.sin (129139/100000) ≤ Real.sin (-φ) := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith [hpl, hph]) hmphi_lo
  have hsin_le_b : Real.sin (-φ) ≤ Real.sin (30099/20000) := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith [hpl, hph]) hmphi_hi
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hcos_eq]; linarith [hc_lo, hcbL]
  · rw [hcos_eq]; linarith [hc_up, hcaH]
  · rw [hsin_eq]; linarith [Real.sin_le_one (-φ)]
  · rw [hsin_eq]; linarith [hsin_ge_a, hsaL]

end ForgeThetaBox
