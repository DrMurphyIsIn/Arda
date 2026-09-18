/-  Height-chain step: all nontrivial zeta zeros up to height 93000 on Re = 1/2 --
    `AllZeros_h92000` + a `[92000, 93000]` SEGMENT certificate (36 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h92000
import RHInBoxT_1d4000000_3999999d4000000_92000_92028
import RHInBoxT_1d4000000_3999999d4000000_92028_92056
import RHInBoxT_1d4000000_3999999d4000000_92056_92083
import RHInBoxT_1d4000000_3999999d4000000_92083_92111
import RHInBoxT_1d4000000_3999999d4000000_92111_368557d4
import RHInBoxT_1d4000000_3999999d4000000_92139_368669d4
import RHInBoxT_1d4000000_3999999d4000000_92167_368777d4
import RHInBoxT_1d4000000_3999999d4000000_92194_368889d4
import RHInBoxT_1d4000000_3999999d4000000_92222_92250
import RHInBoxT_1d4000000_3999999d4000000_368999d4_92278
import RHInBoxT_1d4000000_3999999d4000000_92278_92306
import RHInBoxT_1d4000000_3999999d4000000_369223d4_92333
import RHInBoxT_1d4000000_3999999d4000000_92333_92361
import RHInBoxT_1d4000000_3999999d4000000_92361_92389
import RHInBoxT_1d4000000_3999999d4000000_92389_92417
import RHInBoxT_1d4000000_3999999d4000000_92417_92444
import RHInBoxT_1d4000000_3999999d4000000_92444_92472
import RHInBoxT_1d4000000_3999999d4000000_92472_92500
import RHInBoxT_1d4000000_3999999d4000000_369999d4_370113d4
import RHInBoxT_1d4000000_3999999d4000000_92528_92556
import RHInBoxT_1d4000000_3999999d4000000_92556_92583
import RHInBoxT_1d4000000_3999999d4000000_92583_92611
import RHInBoxT_1d4000000_3999999d4000000_92611_370557d4
import RHInBoxT_1d4000000_3999999d4000000_92639_370669d4
import RHInBoxT_1d4000000_3999999d4000000_92667_92694
import RHInBoxT_1d4000000_3999999d4000000_370775d4_92722
import RHInBoxT_1d4000000_3999999d4000000_92722_92750
import RHInBoxT_1d4000000_3999999d4000000_92750_92778
import RHInBoxT_1d4000000_3999999d4000000_92778_92806
import RHInBoxT_1d4000000_3999999d4000000_92806_371333d4
import RHInBoxT_1d4000000_3999999d4000000_92833_92861
import RHInBoxT_1d4000000_3999999d4000000_92861_92889
import RHInBoxT_1d4000000_3999999d4000000_92889_92917
import RHInBoxT_1d4000000_3999999d4000000_92917_92944
import RHInBoxT_1d4000000_3999999d4000000_92944_92972
import RHInBoxT_1d4000000_3999999d4000000_92972_93000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h93000

/-- The 36-band NOMINAL partition of `[92000, 93000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 92000
  | 1 => 92028
  | 2 => 92056
  | 3 => 92083
  | 4 => 92111
  | 5 => 92139
  | 6 => 92167
  | 7 => 92194
  | 8 => 92222
  | 9 => 92250
  | 10 => 92278
  | 11 => 92306
  | 12 => 92333
  | 13 => 92361
  | 14 => 92389
  | 15 => 92417
  | 16 => 92444
  | 17 => 92472
  | 18 => 92500
  | 19 => 92528
  | 20 => 92556
  | 21 => 92583
  | 22 => 92611
  | 23 => 92639
  | 24 => 92667
  | 25 => 92694
  | 26 => 92722
  | 27 => 92750
  | 28 => 92778
  | 29 => 92806
  | 30 => 92833
  | 31 => 92861
  | 32 => 92889
  | 33 => 92917
  | 34 => 92944
  | 35 => 92972
  | 36 => 93000
  | _ => 93000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((92000:ℝ)) ≤ (92028); norm_num
  · show ((92028:ℝ)) ≤ (92056); norm_num
  · show ((92056:ℝ)) ≤ (92083); norm_num
  · show ((92083:ℝ)) ≤ (92111); norm_num
  · show ((92111:ℝ)) ≤ (92139); norm_num
  · show ((92139:ℝ)) ≤ (92167); norm_num
  · show ((92167:ℝ)) ≤ (92194); norm_num
  · show ((92194:ℝ)) ≤ (92222); norm_num
  · show ((92222:ℝ)) ≤ (92250); norm_num
  · show ((92250:ℝ)) ≤ (92278); norm_num
  · show ((92278:ℝ)) ≤ (92306); norm_num
  · show ((92306:ℝ)) ≤ (92333); norm_num
  · show ((92333:ℝ)) ≤ (92361); norm_num
  · show ((92361:ℝ)) ≤ (92389); norm_num
  · show ((92389:ℝ)) ≤ (92417); norm_num
  · show ((92417:ℝ)) ≤ (92444); norm_num
  · show ((92444:ℝ)) ≤ (92472); norm_num
  · show ((92472:ℝ)) ≤ (92500); norm_num
  · show ((92500:ℝ)) ≤ (92528); norm_num
  · show ((92528:ℝ)) ≤ (92556); norm_num
  · show ((92556:ℝ)) ≤ (92583); norm_num
  · show ((92583:ℝ)) ≤ (92611); norm_num
  · show ((92611:ℝ)) ≤ (92639); norm_num
  · show ((92639:ℝ)) ≤ (92667); norm_num
  · show ((92667:ℝ)) ≤ (92694); norm_num
  · show ((92694:ℝ)) ≤ (92722); norm_num
  · show ((92722:ℝ)) ≤ (92750); norm_num
  · show ((92750:ℝ)) ≤ (92778); norm_num
  · show ((92778:ℝ)) ≤ (92806); norm_num
  · show ((92806:ℝ)) ≤ (92833); norm_num
  · show ((92833:ℝ)) ≤ (92861); norm_num
  · show ((92861:ℝ)) ≤ (92889); norm_num
  · show ((92889:ℝ)) ≤ (92917); norm_num
  · show ((92917:ℝ)) ≤ (92944); norm_num
  · show ((92944:ℝ)) ≤ (92972); norm_num
  · show ((92972:ℝ)) ≤ (93000); norm_num
  · show ((93000:ℝ)) ≤ (93000); norm_num
  · exact le_refl _

/-- The lower edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 92000
  | 1 => 92028
  | 2 => 92056
  | 3 => 92083
  | 4 => 92111
  | 5 => 92139
  | 6 => 92167
  | 7 => 92194
  | 8 => 92222
  | 9 => 368999 / 4
  | 10 => 92278
  | 11 => 369223 / 4
  | 12 => 92333
  | 13 => 92361
  | 14 => 92389
  | 15 => 92417
  | 16 => 92444
  | 17 => 92472
  | 18 => 369999 / 4
  | 19 => 92528
  | 20 => 92556
  | 21 => 92583
  | 22 => 92611
  | 23 => 92639
  | 24 => 92667
  | 25 => 370775 / 4
  | 26 => 92722
  | 27 => 92750
  | 28 => 92778
  | 29 => 92806
  | 30 => 92833
  | 31 => 92861
  | 32 => 92889
  | 33 => 92917
  | 34 => 92944
  | 35 => 92972
  | _ => 92972

/-- The upper edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 92028
  | 1 => 92056
  | 2 => 92083
  | 3 => 92111
  | 4 => 368557 / 4
  | 5 => 368669 / 4
  | 6 => 368777 / 4
  | 7 => 368889 / 4
  | 8 => 92250
  | 9 => 92278
  | 10 => 92306
  | 11 => 92333
  | 12 => 92361
  | 13 => 92389
  | 14 => 92417
  | 15 => 92444
  | 16 => 92472
  | 17 => 92500
  | 18 => 370113 / 4
  | 19 => 92556
  | 20 => 92583
  | 21 => 92611
  | 22 => 370557 / 4
  | 23 => 370669 / 4
  | 24 => 92694
  | 25 => 92722
  | 26 => 92750
  | 27 => 92778
  | 28 => 92806
  | 29 => 371333 / 4
  | 30 => 92861
  | 31 => 92889
  | 32 => 92917
  | 33 => 92944
  | 34 => 92972
  | 35 => 93000
  | _ => 93000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 36 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 93000` (`log 93000 ≤ 12`, `2.7^12 ≥ 93000`). -/
theorem haC_93000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 93000 := by
  have hlog : Real.log 93000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 93000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 93000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[92000, 93000]` segment's band hypothesis: every band `i < 36` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 36 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 36 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[92000, 93000]` SEGMENT: every zero with `92000 ≤ Im ≤ 93000` is on the line. -/
theorem segment_92000_93000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 93000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (92000:ℝ) ≤ ρ.im → ρ.im ≤ 93000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 92000 93000 bndSeg 36 (by norm_num) bndSeg_mono rfl rfl haC_93000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 93000 via the HEIGHT CHAIN**: `[0,92000]` ∘ `[92000,93000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_93000_of_bands
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
    (hbands_62000 : AllZeros_h62000.BandHyp)
    (hbands_63000 : AllZeros_h63000.BandHyp)
    (hbands_64000 : AllZeros_h64000.BandHyp)
    (hbands_65000 : AllZeros_h65000.BandHyp)
    (hbands_66000 : AllZeros_h66000.BandHyp)
    (hbands_67000 : AllZeros_h67000.BandHyp)
    (hbands_68000 : AllZeros_h68000.BandHyp)
    (hbands_69000 : AllZeros_h69000.BandHyp)
    (hbands_70000 : AllZeros_h70000.BandHyp)
    (hbands_71000 : AllZeros_h71000.BandHyp)
    (hbands_72000 : AllZeros_h72000.BandHyp)
    (hbands_73000 : AllZeros_h73000.BandHyp)
    (hbands_74000 : AllZeros_h74000.BandHyp)
    (hbands_75000 : AllZeros_h75000.BandHyp)
    (hbands_76000 : AllZeros_h76000.BandHyp)
    (hbands_77000 : AllZeros_h77000.BandHyp)
    (hbands_78000 : AllZeros_h78000.BandHyp)
    (hbands_79000 : AllZeros_h79000.BandHyp)
    (hbands_80000 : AllZeros_h80000.BandHyp)
    (hbands_81000 : AllZeros_h81000.BandHyp)
    (hbands_82000 : AllZeros_h82000.BandHyp)
    (hbands_83000 : AllZeros_h83000.BandHyp)
    (hbands_84000 : AllZeros_h84000.BandHyp)
    (hbands_85000 : AllZeros_h85000.BandHyp)
    (hbands_86000 : AllZeros_h86000.BandHyp)
    (hbands_87000 : AllZeros_h87000.BandHyp)
    (hbands_88000 : AllZeros_h88000.BandHyp)
    (hbands_89000 : AllZeros_h89000.BandHyp)
    (hbands_90000 : AllZeros_h90000.BandHyp)
    (hbands_91000 : AllZeros_h91000.BandHyp)
    (hbands_92000 : AllZeros_h92000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 93000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 93000 → ρ.re = 1 / 2 := by
  have hγ92000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 92000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 92000 93000
    (AllZeros_h92000.all_nontrivial_zeros_up_to_height_92000_of_bands
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
      hbands_62000
      hbands_63000
      hbands_64000
      hbands_65000
      hbands_66000
      hbands_67000
      hbands_68000
      hbands_69000
      hbands_70000
      hbands_71000
      hbands_72000
      hbands_73000
      hbands_74000
      hbands_75000
      hbands_76000
      hbands_77000
      hbands_78000
      hbands_79000
      hbands_80000
      hbands_81000
      hbands_82000
      hbands_83000
      hbands_84000
      hbands_85000
      hbands_86000
      hbands_87000
      hbands_88000
      hbands_89000
      hbands_90000
      hbands_91000
      hbands_92000
      hγ92000)
    (segment_92000_93000 hbands hγ)

end AllZeros_h93000
