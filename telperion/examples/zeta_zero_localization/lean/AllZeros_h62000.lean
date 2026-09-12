/-  Height-chain step: all nontrivial zeta zeros up to height 62000 on Re = 1/2 --
    `AllZeros_h61000` + a `[61000, 62000]` SEGMENT certificate (35 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h61000
import RHInBoxT_1d4000000_3999999d4000000_243999d4_61029
import RHInBoxT_1d4000000_3999999d4000000_61029_61057
import RHInBoxT_1d4000000_3999999d4000000_61057_61086
import RHInBoxT_1d4000000_3999999d4000000_244343d4_61114
import RHInBoxT_1d4000000_3999999d4000000_61114_61143
import RHInBoxT_1d4000000_3999999d4000000_61143_61171
import RHInBoxT_1d4000000_3999999d4000000_61171_244801d4
import RHInBoxT_1d4000000_3999999d4000000_61200_61229
import RHInBoxT_1d4000000_3999999d4000000_61229_61257
import RHInBoxT_1d4000000_3999999d4000000_61257_245145d4
import RHInBoxT_1d4000000_3999999d4000000_61286_245257d4
import RHInBoxT_1d4000000_3999999d4000000_61314_61343
import RHInBoxT_1d4000000_3999999d4000000_61343_245485d4
import RHInBoxT_1d4000000_3999999d4000000_61371_61400
import RHInBoxT_1d4000000_3999999d4000000_245599d4_61429
import RHInBoxT_1d4000000_3999999d4000000_61429_61457
import RHInBoxT_1d4000000_3999999d4000000_61457_61486
import RHInBoxT_1d4000000_3999999d4000000_61486_61514
import RHInBoxT_1d4000000_3999999d4000000_61514_61543
import RHInBoxT_1d4000000_3999999d4000000_61543_61571
import RHInBoxT_1d4000000_3999999d4000000_123141d2_61600
import RHInBoxT_1d4000000_3999999d4000000_61600_61629
import RHInBoxT_1d4000000_3999999d4000000_246515d4_61657
import RHInBoxT_1d4000000_3999999d4000000_61657_246745d4
import RHInBoxT_1d4000000_3999999d4000000_61686_61714
import RHInBoxT_1d4000000_3999999d4000000_61714_246973d4
import RHInBoxT_1d4000000_3999999d4000000_61743_61771
import RHInBoxT_1d4000000_3999999d4000000_61771_61800
import RHInBoxT_1d4000000_3999999d4000000_61800_61829
import RHInBoxT_1d4000000_3999999d4000000_61829_61857
import RHInBoxT_1d4000000_3999999d4000000_61857_61886
import RHInBoxT_1d4000000_3999999d4000000_61886_61914
import RHInBoxT_1d4000000_3999999d4000000_61914_61943
import RHInBoxT_1d4000000_3999999d4000000_61943_61971
import RHInBoxT_1d4000000_3999999d4000000_61971_62000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h62000

/-- The 35-band NOMINAL partition of `[61000, 62000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 61000
  | 1 => 61029
  | 2 => 61057
  | 3 => 61086
  | 4 => 61114
  | 5 => 61143
  | 6 => 61171
  | 7 => 61200
  | 8 => 61229
  | 9 => 61257
  | 10 => 61286
  | 11 => 61314
  | 12 => 61343
  | 13 => 61371
  | 14 => 61400
  | 15 => 61429
  | 16 => 61457
  | 17 => 61486
  | 18 => 61514
  | 19 => 61543
  | 20 => 61571
  | 21 => 61600
  | 22 => 61629
  | 23 => 61657
  | 24 => 61686
  | 25 => 61714
  | 26 => 61743
  | 27 => 61771
  | 28 => 61800
  | 29 => 61829
  | 30 => 61857
  | 31 => 61886
  | 32 => 61914
  | 33 => 61943
  | 34 => 61971
  | 35 => 62000
  | _ => 62000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((61000:ℝ)) ≤ (61029); norm_num
  · show ((61029:ℝ)) ≤ (61057); norm_num
  · show ((61057:ℝ)) ≤ (61086); norm_num
  · show ((61086:ℝ)) ≤ (61114); norm_num
  · show ((61114:ℝ)) ≤ (61143); norm_num
  · show ((61143:ℝ)) ≤ (61171); norm_num
  · show ((61171:ℝ)) ≤ (61200); norm_num
  · show ((61200:ℝ)) ≤ (61229); norm_num
  · show ((61229:ℝ)) ≤ (61257); norm_num
  · show ((61257:ℝ)) ≤ (61286); norm_num
  · show ((61286:ℝ)) ≤ (61314); norm_num
  · show ((61314:ℝ)) ≤ (61343); norm_num
  · show ((61343:ℝ)) ≤ (61371); norm_num
  · show ((61371:ℝ)) ≤ (61400); norm_num
  · show ((61400:ℝ)) ≤ (61429); norm_num
  · show ((61429:ℝ)) ≤ (61457); norm_num
  · show ((61457:ℝ)) ≤ (61486); norm_num
  · show ((61486:ℝ)) ≤ (61514); norm_num
  · show ((61514:ℝ)) ≤ (61543); norm_num
  · show ((61543:ℝ)) ≤ (61571); norm_num
  · show ((61571:ℝ)) ≤ (61600); norm_num
  · show ((61600:ℝ)) ≤ (61629); norm_num
  · show ((61629:ℝ)) ≤ (61657); norm_num
  · show ((61657:ℝ)) ≤ (61686); norm_num
  · show ((61686:ℝ)) ≤ (61714); norm_num
  · show ((61714:ℝ)) ≤ (61743); norm_num
  · show ((61743:ℝ)) ≤ (61771); norm_num
  · show ((61771:ℝ)) ≤ (61800); norm_num
  · show ((61800:ℝ)) ≤ (61829); norm_num
  · show ((61829:ℝ)) ≤ (61857); norm_num
  · show ((61857:ℝ)) ≤ (61886); norm_num
  · show ((61886:ℝ)) ≤ (61914); norm_num
  · show ((61914:ℝ)) ≤ (61943); norm_num
  · show ((61943:ℝ)) ≤ (61971); norm_num
  · show ((61971:ℝ)) ≤ (62000); norm_num
  · show ((62000:ℝ)) ≤ (62000); norm_num
  · exact le_refl _

/-- The lower edges of the 35 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 243999 / 4
  | 1 => 61029
  | 2 => 61057
  | 3 => 244343 / 4
  | 4 => 61114
  | 5 => 61143
  | 6 => 61171
  | 7 => 61200
  | 8 => 61229
  | 9 => 61257
  | 10 => 61286
  | 11 => 61314
  | 12 => 61343
  | 13 => 61371
  | 14 => 245599 / 4
  | 15 => 61429
  | 16 => 61457
  | 17 => 61486
  | 18 => 61514
  | 19 => 61543
  | 20 => 123141 / 2
  | 21 => 61600
  | 22 => 246515 / 4
  | 23 => 61657
  | 24 => 61686
  | 25 => 61714
  | 26 => 61743
  | 27 => 61771
  | 28 => 61800
  | 29 => 61829
  | 30 => 61857
  | 31 => 61886
  | 32 => 61914
  | 33 => 61943
  | 34 => 61971
  | _ => 61971

/-- The upper edges of the 35 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 61029
  | 1 => 61057
  | 2 => 61086
  | 3 => 61114
  | 4 => 61143
  | 5 => 61171
  | 6 => 244801 / 4
  | 7 => 61229
  | 8 => 61257
  | 9 => 245145 / 4
  | 10 => 245257 / 4
  | 11 => 61343
  | 12 => 245485 / 4
  | 13 => 61400
  | 14 => 61429
  | 15 => 61457
  | 16 => 61486
  | 17 => 61514
  | 18 => 61543
  | 19 => 61571
  | 20 => 61600
  | 21 => 61629
  | 22 => 61657
  | 23 => 246745 / 4
  | 24 => 61714
  | 25 => 246973 / 4
  | 26 => 61771
  | 27 => 61800
  | 28 => 61829
  | 29 => 61857
  | 30 => 61886
  | 31 => 61914
  | 32 => 61943
  | 33 => 61971
  | 34 => 62000
  | _ => 62000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 35 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 62000` (`log 62000 ≤ 12`, `2.7^12 ≥ 62000`). -/
theorem haC_62000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 62000 := by
  have hlog : Real.log 62000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 62000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 62000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[61000, 62000]` segment's band hypothesis: every band `i < 35` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 35 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 35 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[61000, 62000]` SEGMENT: every zero with `61000 ≤ Im ≤ 62000` is on the line. -/
theorem segment_61000_62000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 62000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (61000:ℝ) ≤ ρ.im → ρ.im ≤ 62000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 61000 62000 bndSeg 35 (by norm_num) bndSeg_mono rfl rfl haC_62000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 62000 via the HEIGHT CHAIN**: `[0,61000]` ∘ `[61000,62000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_62000_of_bands
    (hbands_1000 : AllZeros_h1000.BandHyp)
    (hbands_2000 : AllZeros_h2000.BandHyp)
    (hbands_3000 : AllZeros_h3000.BandHyp)
    (hbands_4000 : AllZeros_h4000.BandHyp)
    (hbands_5000 : AllZeros_h5000.BandHyp)
    (hbands_6000 : AllZeros_h6000.BandHyp)
    (hbands_7000 : AllZeros_h7000.BandHyp)
    (hbands_8000 : AllZeros_h8000.BandHyp)
    (hbands_9000 : AllZeros_h9000.BandHyp)
    (hbands_10000 : AllZeros_h10000.BandHyp)
    (hbands_11000 : AllZeros_h11000.BandHyp)
    (hbands_12000 : AllZeros_h12000.BandHyp)
    (hbands_13000 : AllZeros_h13000.BandHyp)
    (hbands_14000 : AllZeros_h14000.BandHyp)
    (hbands_15000 : AllZeros_h15000.BandHyp)
    (hbands_16000 : AllZeros_h16000.BandHyp)
    (hbands_17000 : AllZeros_h17000.BandHyp)
    (hbands_18000 : AllZeros_h18000.BandHyp)
    (hbands_19000 : AllZeros_h19000.BandHyp)
    (hbands_20000 : AllZeros_h20000.BandHyp)
    (hbands_21000 : AllZeros_h21000.BandHyp)
    (hbands_22000 : AllZeros_h22000.BandHyp)
    (hbands_23000 : AllZeros_h23000.BandHyp)
    (hbands_24000 : AllZeros_h24000.BandHyp)
    (hbands_25000 : AllZeros_h25000.BandHyp)
    (hbands_26000 : AllZeros_h26000.BandHyp)
    (hbands_27000 : AllZeros_h27000.BandHyp)
    (hbands_28000 : AllZeros_h28000.BandHyp)
    (hbands_29000 : AllZeros_h29000.BandHyp)
    (hbands_30000 : AllZeros_h30000.BandHyp)
    (hbands_31000 : AllZeros_h31000.BandHyp)
    (hbands_32000 : AllZeros_h32000.BandHyp)
    (hbands_33000 : AllZeros_h33000.BandHyp)
    (hbands_34000 : AllZeros_h34000.BandHyp)
    (hbands_35000 : AllZeros_h35000.BandHyp)
    (hbands_36000 : AllZeros_h36000.BandHyp)
    (hbands_37000 : AllZeros_h37000.BandHyp)
    (hbands_38000 : AllZeros_h38000.BandHyp)
    (hbands_39000 : AllZeros_h39000.BandHyp)
    (hbands_40000 : AllZeros_h40000.BandHyp)
    (hbands_41000 : AllZeros_h41000.BandHyp)
    (hbands_42000 : AllZeros_h42000.BandHyp)
    (hbands_43000 : AllZeros_h43000.BandHyp)
    (hbands_44000 : AllZeros_h44000.BandHyp)
    (hbands_45000 : AllZeros_h45000.BandHyp)
    (hbands_46000 : AllZeros_h46000.BandHyp)
    (hbands_47000 : AllZeros_h47000.BandHyp)
    (hbands_48000 : AllZeros_h48000.BandHyp)
    (hbands_49000 : AllZeros_h49000.BandHyp)
    (hbands_50000 : AllZeros_h50000.BandHyp)
    (hbands_51000 : AllZeros_h51000.BandHyp)
    (hbands_52000 : AllZeros_h52000.BandHyp)
    (hbands_53000 : AllZeros_h53000.BandHyp)
    (hbands_54000 : AllZeros_h54000.BandHyp)
    (hbands_55000 : AllZeros_h55000.BandHyp)
    (hbands_56000 : AllZeros_h56000.BandHyp)
    (hbands_57000 : AllZeros_h57000.BandHyp)
    (hbands_58000 : AllZeros_h58000.BandHyp)
    (hbands_59000 : AllZeros_h59000.BandHyp)
    (hbands_60000 : AllZeros_h60000.BandHyp)
    (hbands_61000 : AllZeros_h61000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 62000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 62000 → ρ.re = 1 / 2 := by
  have hγ61000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 61000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 61000 62000
    (AllZeros_h61000.all_nontrivial_zeros_up_to_height_61000_of_bands
      hbands_1000
      hbands_2000
      hbands_3000
      hbands_4000
      hbands_5000
      hbands_6000
      hbands_7000
      hbands_8000
      hbands_9000
      hbands_10000
      hbands_11000
      hbands_12000
      hbands_13000
      hbands_14000
      hbands_15000
      hbands_16000
      hbands_17000
      hbands_18000
      hbands_19000
      hbands_20000
      hbands_21000
      hbands_22000
      hbands_23000
      hbands_24000
      hbands_25000
      hbands_26000
      hbands_27000
      hbands_28000
      hbands_29000
      hbands_30000
      hbands_31000
      hbands_32000
      hbands_33000
      hbands_34000
      hbands_35000
      hbands_36000
      hbands_37000
      hbands_38000
      hbands_39000
      hbands_40000
      hbands_41000
      hbands_42000
      hbands_43000
      hbands_44000
      hbands_45000
      hbands_46000
      hbands_47000
      hbands_48000
      hbands_49000
      hbands_50000
      hbands_51000
      hbands_52000
      hbands_53000
      hbands_54000
      hbands_55000
      hbands_56000
      hbands_57000
      hbands_58000
      hbands_59000
      hbands_60000
      hbands_61000
      hγ61000)
    (segment_61000_62000 hbands hγ)

end AllZeros_h62000
