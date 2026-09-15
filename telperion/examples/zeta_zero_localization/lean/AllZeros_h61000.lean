/-  Height-chain step: all nontrivial zeta zeros up to height 61000 on Re = 1/2 --
    `AllZeros_h60000` + a `[60000, 61000]` SEGMENT certificate (35 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h60000
import RHInBoxT_1d4000000_3999999d4000000_60000_60029
import RHInBoxT_1d4000000_3999999d4000000_60029_60057
import RHInBoxT_1d4000000_3999999d4000000_60057_60086
import RHInBoxT_1d4000000_3999999d4000000_60086_60114
import RHInBoxT_1d4000000_3999999d4000000_60114_60143
import RHInBoxT_1d4000000_3999999d4000000_60143_60171
import RHInBoxT_1d4000000_3999999d4000000_60171_60200
import RHInBoxT_1d4000000_3999999d4000000_60200_240917d4
import RHInBoxT_1d4000000_3999999d4000000_60229_60257
import RHInBoxT_1d4000000_3999999d4000000_60257_60286
import RHInBoxT_1d4000000_3999999d4000000_60286_60314
import RHInBoxT_1d4000000_3999999d4000000_60314_60343
import RHInBoxT_1d4000000_3999999d4000000_60343_60371
import RHInBoxT_1d4000000_3999999d4000000_60371_60400
import RHInBoxT_1d4000000_3999999d4000000_60400_60429
import RHInBoxT_1d4000000_3999999d4000000_60429_60457
import RHInBoxT_1d4000000_3999999d4000000_60457_60486
import RHInBoxT_1d4000000_3999999d4000000_60486_60514
import RHInBoxT_1d4000000_3999999d4000000_242055d4_60543
import RHInBoxT_1d4000000_3999999d4000000_60543_60571
import RHInBoxT_1d4000000_3999999d4000000_60571_60600
import RHInBoxT_1d4000000_3999999d4000000_60600_60629
import RHInBoxT_1d4000000_3999999d4000000_60629_242629d4
import RHInBoxT_1d4000000_3999999d4000000_60657_60686
import RHInBoxT_1d4000000_3999999d4000000_60686_60714
import RHInBoxT_1d4000000_3999999d4000000_60714_60743
import RHInBoxT_1d4000000_3999999d4000000_60743_60771
import RHInBoxT_1d4000000_3999999d4000000_60771_60800
import RHInBoxT_1d4000000_3999999d4000000_60800_60829
import RHInBoxT_1d4000000_3999999d4000000_60829_121715d2
import RHInBoxT_1d4000000_3999999d4000000_60857_60886
import RHInBoxT_1d4000000_3999999d4000000_60886_60914
import RHInBoxT_1d4000000_3999999d4000000_60914_60943
import RHInBoxT_1d4000000_3999999d4000000_60943_60971
import RHInBoxT_1d4000000_3999999d4000000_60971_61000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h61000

/-- The 35-band NOMINAL partition of `[60000, 61000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 60000
  | 1 => 60029
  | 2 => 60057
  | 3 => 60086
  | 4 => 60114
  | 5 => 60143
  | 6 => 60171
  | 7 => 60200
  | 8 => 60229
  | 9 => 60257
  | 10 => 60286
  | 11 => 60314
  | 12 => 60343
  | 13 => 60371
  | 14 => 60400
  | 15 => 60429
  | 16 => 60457
  | 17 => 60486
  | 18 => 60514
  | 19 => 60543
  | 20 => 60571
  | 21 => 60600
  | 22 => 60629
  | 23 => 60657
  | 24 => 60686
  | 25 => 60714
  | 26 => 60743
  | 27 => 60771
  | 28 => 60800
  | 29 => 60829
  | 30 => 60857
  | 31 => 60886
  | 32 => 60914
  | 33 => 60943
  | 34 => 60971
  | 35 => 61000
  | _ => 61000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((60000:ℝ)) ≤ (60029); norm_num
  · show ((60029:ℝ)) ≤ (60057); norm_num
  · show ((60057:ℝ)) ≤ (60086); norm_num
  · show ((60086:ℝ)) ≤ (60114); norm_num
  · show ((60114:ℝ)) ≤ (60143); norm_num
  · show ((60143:ℝ)) ≤ (60171); norm_num
  · show ((60171:ℝ)) ≤ (60200); norm_num
  · show ((60200:ℝ)) ≤ (60229); norm_num
  · show ((60229:ℝ)) ≤ (60257); norm_num
  · show ((60257:ℝ)) ≤ (60286); norm_num
  · show ((60286:ℝ)) ≤ (60314); norm_num
  · show ((60314:ℝ)) ≤ (60343); norm_num
  · show ((60343:ℝ)) ≤ (60371); norm_num
  · show ((60371:ℝ)) ≤ (60400); norm_num
  · show ((60400:ℝ)) ≤ (60429); norm_num
  · show ((60429:ℝ)) ≤ (60457); norm_num
  · show ((60457:ℝ)) ≤ (60486); norm_num
  · show ((60486:ℝ)) ≤ (60514); norm_num
  · show ((60514:ℝ)) ≤ (60543); norm_num
  · show ((60543:ℝ)) ≤ (60571); norm_num
  · show ((60571:ℝ)) ≤ (60600); norm_num
  · show ((60600:ℝ)) ≤ (60629); norm_num
  · show ((60629:ℝ)) ≤ (60657); norm_num
  · show ((60657:ℝ)) ≤ (60686); norm_num
  · show ((60686:ℝ)) ≤ (60714); norm_num
  · show ((60714:ℝ)) ≤ (60743); norm_num
  · show ((60743:ℝ)) ≤ (60771); norm_num
  · show ((60771:ℝ)) ≤ (60800); norm_num
  · show ((60800:ℝ)) ≤ (60829); norm_num
  · show ((60829:ℝ)) ≤ (60857); norm_num
  · show ((60857:ℝ)) ≤ (60886); norm_num
  · show ((60886:ℝ)) ≤ (60914); norm_num
  · show ((60914:ℝ)) ≤ (60943); norm_num
  · show ((60943:ℝ)) ≤ (60971); norm_num
  · show ((60971:ℝ)) ≤ (61000); norm_num
  · show ((61000:ℝ)) ≤ (61000); norm_num
  · exact le_refl _

/-- The lower edges of the 35 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 60000
  | 1 => 60029
  | 2 => 60057
  | 3 => 60086
  | 4 => 60114
  | 5 => 60143
  | 6 => 60171
  | 7 => 60200
  | 8 => 60229
  | 9 => 60257
  | 10 => 60286
  | 11 => 60314
  | 12 => 60343
  | 13 => 60371
  | 14 => 60400
  | 15 => 60429
  | 16 => 60457
  | 17 => 60486
  | 18 => 242055 / 4
  | 19 => 60543
  | 20 => 60571
  | 21 => 60600
  | 22 => 60629
  | 23 => 60657
  | 24 => 60686
  | 25 => 60714
  | 26 => 60743
  | 27 => 60771
  | 28 => 60800
  | 29 => 60829
  | 30 => 60857
  | 31 => 60886
  | 32 => 60914
  | 33 => 60943
  | 34 => 60971
  | _ => 60971

/-- The upper edges of the 35 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 60029
  | 1 => 60057
  | 2 => 60086
  | 3 => 60114
  | 4 => 60143
  | 5 => 60171
  | 6 => 60200
  | 7 => 240917 / 4
  | 8 => 60257
  | 9 => 60286
  | 10 => 60314
  | 11 => 60343
  | 12 => 60371
  | 13 => 60400
  | 14 => 60429
  | 15 => 60457
  | 16 => 60486
  | 17 => 60514
  | 18 => 60543
  | 19 => 60571
  | 20 => 60600
  | 21 => 60629
  | 22 => 242629 / 4
  | 23 => 60686
  | 24 => 60714
  | 25 => 60743
  | 26 => 60771
  | 27 => 60800
  | 28 => 60829
  | 29 => 121715 / 2
  | 30 => 60886
  | 31 => 60914
  | 32 => 60943
  | 33 => 60971
  | 34 => 61000
  | _ => 61000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 35 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 61000` (`log 61000 ≤ 12`, `2.7^12 ≥ 61000`). -/
theorem haC_61000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 61000 := by
  have hlog : Real.log 61000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 61000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 61000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[60000, 61000]` segment's band hypothesis: every band `i < 35` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 35 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 35 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[60000, 61000]` SEGMENT: every zero with `60000 ≤ Im ≤ 61000` is on the line. -/
theorem segment_60000_61000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 61000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (60000:ℝ) ≤ ρ.im → ρ.im ≤ 61000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 60000 61000 bndSeg 35 (by norm_num) bndSeg_mono rfl rfl haC_61000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 61000 via the HEIGHT CHAIN**: `[0,60000]` ∘ `[60000,61000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_61000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 61000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 61000 → ρ.re = 1 / 2 := by
  have hγ60000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 60000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 60000 61000
    (AllZeros_h60000.all_nontrivial_zeros_up_to_height_60000_of_bands
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
      hγ60000)
    (segment_60000_61000 hbands hγ)

end AllZeros_h61000
