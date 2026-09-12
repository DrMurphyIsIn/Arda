/-  Height-chain step: all nontrivial zeta zeros up to height 56000 on Re = 1/2 --
    `AllZeros_h55000` + a `[55000, 56000]` SEGMENT certificate (35 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h55000
import RHInBoxT_1d4000000_3999999d4000000_55000_55029
import RHInBoxT_1d4000000_3999999d4000000_55029_55057
import RHInBoxT_1d4000000_3999999d4000000_55057_220345d4
import RHInBoxT_1d4000000_3999999d4000000_55086_55114
import RHInBoxT_1d4000000_3999999d4000000_55114_55143
import RHInBoxT_1d4000000_3999999d4000000_55143_55171
import RHInBoxT_1d4000000_3999999d4000000_55171_55200
import RHInBoxT_1d4000000_3999999d4000000_55200_55229
import RHInBoxT_1d4000000_3999999d4000000_220915d4_55257
import RHInBoxT_1d4000000_3999999d4000000_221027d4_55286
import RHInBoxT_1d4000000_3999999d4000000_55286_55314
import RHInBoxT_1d4000000_3999999d4000000_55314_55343
import RHInBoxT_1d4000000_3999999d4000000_55343_55371
import RHInBoxT_1d4000000_3999999d4000000_55371_55400
import RHInBoxT_1d4000000_3999999d4000000_55400_55429
import RHInBoxT_1d4000000_3999999d4000000_55429_55457
import RHInBoxT_1d4000000_3999999d4000000_55457_55486
import RHInBoxT_1d4000000_3999999d4000000_55486_55514
import RHInBoxT_1d4000000_3999999d4000000_55514_55543
import RHInBoxT_1d4000000_3999999d4000000_222171d4_55571
import RHInBoxT_1d4000000_3999999d4000000_55571_55600
import RHInBoxT_1d4000000_3999999d4000000_55600_55629
import RHInBoxT_1d4000000_3999999d4000000_55629_55657
import RHInBoxT_1d4000000_3999999d4000000_55657_55686
import RHInBoxT_1d4000000_3999999d4000000_222743d4_55714
import RHInBoxT_1d4000000_3999999d4000000_55714_222973d4
import RHInBoxT_1d4000000_3999999d4000000_55743_55771
import RHInBoxT_1d4000000_3999999d4000000_55771_55800
import RHInBoxT_1d4000000_3999999d4000000_223199d4_55829
import RHInBoxT_1d4000000_3999999d4000000_55829_55857
import RHInBoxT_1d4000000_3999999d4000000_55857_55886
import RHInBoxT_1d4000000_3999999d4000000_55886_55914
import RHInBoxT_1d4000000_3999999d4000000_55914_55943
import RHInBoxT_1d4000000_3999999d4000000_55943_55971
import RHInBoxT_1d4000000_3999999d4000000_55971_56000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h56000

/-- The 35-band NOMINAL partition of `[55000, 56000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 55000
  | 1 => 55029
  | 2 => 55057
  | 3 => 55086
  | 4 => 55114
  | 5 => 55143
  | 6 => 55171
  | 7 => 55200
  | 8 => 55229
  | 9 => 55257
  | 10 => 55286
  | 11 => 55314
  | 12 => 55343
  | 13 => 55371
  | 14 => 55400
  | 15 => 55429
  | 16 => 55457
  | 17 => 55486
  | 18 => 55514
  | 19 => 55543
  | 20 => 55571
  | 21 => 55600
  | 22 => 55629
  | 23 => 55657
  | 24 => 55686
  | 25 => 55714
  | 26 => 55743
  | 27 => 55771
  | 28 => 55800
  | 29 => 55829
  | 30 => 55857
  | 31 => 55886
  | 32 => 55914
  | 33 => 55943
  | 34 => 55971
  | 35 => 56000
  | _ => 56000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((55000:ℝ)) ≤ (55029); norm_num
  · show ((55029:ℝ)) ≤ (55057); norm_num
  · show ((55057:ℝ)) ≤ (55086); norm_num
  · show ((55086:ℝ)) ≤ (55114); norm_num
  · show ((55114:ℝ)) ≤ (55143); norm_num
  · show ((55143:ℝ)) ≤ (55171); norm_num
  · show ((55171:ℝ)) ≤ (55200); norm_num
  · show ((55200:ℝ)) ≤ (55229); norm_num
  · show ((55229:ℝ)) ≤ (55257); norm_num
  · show ((55257:ℝ)) ≤ (55286); norm_num
  · show ((55286:ℝ)) ≤ (55314); norm_num
  · show ((55314:ℝ)) ≤ (55343); norm_num
  · show ((55343:ℝ)) ≤ (55371); norm_num
  · show ((55371:ℝ)) ≤ (55400); norm_num
  · show ((55400:ℝ)) ≤ (55429); norm_num
  · show ((55429:ℝ)) ≤ (55457); norm_num
  · show ((55457:ℝ)) ≤ (55486); norm_num
  · show ((55486:ℝ)) ≤ (55514); norm_num
  · show ((55514:ℝ)) ≤ (55543); norm_num
  · show ((55543:ℝ)) ≤ (55571); norm_num
  · show ((55571:ℝ)) ≤ (55600); norm_num
  · show ((55600:ℝ)) ≤ (55629); norm_num
  · show ((55629:ℝ)) ≤ (55657); norm_num
  · show ((55657:ℝ)) ≤ (55686); norm_num
  · show ((55686:ℝ)) ≤ (55714); norm_num
  · show ((55714:ℝ)) ≤ (55743); norm_num
  · show ((55743:ℝ)) ≤ (55771); norm_num
  · show ((55771:ℝ)) ≤ (55800); norm_num
  · show ((55800:ℝ)) ≤ (55829); norm_num
  · show ((55829:ℝ)) ≤ (55857); norm_num
  · show ((55857:ℝ)) ≤ (55886); norm_num
  · show ((55886:ℝ)) ≤ (55914); norm_num
  · show ((55914:ℝ)) ≤ (55943); norm_num
  · show ((55943:ℝ)) ≤ (55971); norm_num
  · show ((55971:ℝ)) ≤ (56000); norm_num
  · show ((56000:ℝ)) ≤ (56000); norm_num
  · exact le_refl _

/-- The lower edges of the 35 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 55000
  | 1 => 55029
  | 2 => 55057
  | 3 => 55086
  | 4 => 55114
  | 5 => 55143
  | 6 => 55171
  | 7 => 55200
  | 8 => 220915 / 4
  | 9 => 221027 / 4
  | 10 => 55286
  | 11 => 55314
  | 12 => 55343
  | 13 => 55371
  | 14 => 55400
  | 15 => 55429
  | 16 => 55457
  | 17 => 55486
  | 18 => 55514
  | 19 => 222171 / 4
  | 20 => 55571
  | 21 => 55600
  | 22 => 55629
  | 23 => 55657
  | 24 => 222743 / 4
  | 25 => 55714
  | 26 => 55743
  | 27 => 55771
  | 28 => 223199 / 4
  | 29 => 55829
  | 30 => 55857
  | 31 => 55886
  | 32 => 55914
  | 33 => 55943
  | 34 => 55971
  | _ => 55971

/-- The upper edges of the 35 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 55029
  | 1 => 55057
  | 2 => 220345 / 4
  | 3 => 55114
  | 4 => 55143
  | 5 => 55171
  | 6 => 55200
  | 7 => 55229
  | 8 => 55257
  | 9 => 55286
  | 10 => 55314
  | 11 => 55343
  | 12 => 55371
  | 13 => 55400
  | 14 => 55429
  | 15 => 55457
  | 16 => 55486
  | 17 => 55514
  | 18 => 55543
  | 19 => 55571
  | 20 => 55600
  | 21 => 55629
  | 22 => 55657
  | 23 => 55686
  | 24 => 55714
  | 25 => 222973 / 4
  | 26 => 55771
  | 27 => 55800
  | 28 => 55829
  | 29 => 55857
  | 30 => 55886
  | 31 => 55914
  | 32 => 55943
  | 33 => 55971
  | 34 => 56000
  | _ => 56000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 35 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 56000` (`log 56000 ≤ 12`, `2.7^12 ≥ 56000`). -/
theorem haC_56000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 56000 := by
  have hlog : Real.log 56000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 56000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 56000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[55000, 56000]` segment's band hypothesis: every band `i < 35` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 35 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 35 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[55000, 56000]` SEGMENT: every zero with `55000 ≤ Im ≤ 56000` is on the line. -/
theorem segment_55000_56000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 56000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (55000:ℝ) ≤ ρ.im → ρ.im ≤ 56000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 55000 56000 bndSeg 35 (by norm_num) bndSeg_mono rfl rfl haC_56000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 56000 via the HEIGHT CHAIN**: `[0,55000]` ∘ `[55000,56000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_56000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 56000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 56000 → ρ.re = 1 / 2 := by
  have hγ55000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 55000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 55000 56000
    (AllZeros_h55000.all_nontrivial_zeros_up_to_height_55000_of_bands
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
      hγ55000)
    (segment_55000_56000 hbands hγ)

end AllZeros_h56000
