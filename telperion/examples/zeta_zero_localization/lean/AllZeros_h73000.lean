/-  Height-chain step: all nontrivial zeta zeros up to height 73000 on Re = 1/2 --
    `AllZeros_h72000` + a `[72000, 73000]` SEGMENT certificate (36 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h72000
import RHInBoxT_1d4000000_3999999d4000000_72000_72028
import RHInBoxT_1d4000000_3999999d4000000_72028_72056
import RHInBoxT_1d4000000_3999999d4000000_72056_72083
import RHInBoxT_1d4000000_3999999d4000000_72083_72111
import RHInBoxT_1d4000000_3999999d4000000_72111_72139
import RHInBoxT_1d4000000_3999999d4000000_72139_72167
import RHInBoxT_1d4000000_3999999d4000000_72167_72194
import RHInBoxT_1d4000000_3999999d4000000_72194_72222
import RHInBoxT_1d4000000_3999999d4000000_72222_72250
import RHInBoxT_1d4000000_3999999d4000000_72250_72278
import RHInBoxT_1d4000000_3999999d4000000_72278_72306
import RHInBoxT_1d4000000_3999999d4000000_72306_72333
import RHInBoxT_1d4000000_3999999d4000000_289331d4_72361
import RHInBoxT_1d4000000_3999999d4000000_72361_72389
import RHInBoxT_1d4000000_3999999d4000000_72389_72417
import RHInBoxT_1d4000000_3999999d4000000_72417_289777d4
import RHInBoxT_1d4000000_3999999d4000000_72444_72472
import RHInBoxT_1d4000000_3999999d4000000_72472_72500
import RHInBoxT_1d4000000_3999999d4000000_72500_72528
import RHInBoxT_1d4000000_3999999d4000000_72528_72556
import RHInBoxT_1d4000000_3999999d4000000_72556_72583
import RHInBoxT_1d4000000_3999999d4000000_72583_72611
import RHInBoxT_1d4000000_3999999d4000000_72611_72639
import RHInBoxT_1d4000000_3999999d4000000_72639_72667
import RHInBoxT_1d4000000_3999999d4000000_72667_72694
import RHInBoxT_1d4000000_3999999d4000000_72694_72722
import RHInBoxT_1d4000000_3999999d4000000_72722_72750
import RHInBoxT_1d4000000_3999999d4000000_72750_72778
import RHInBoxT_1d4000000_3999999d4000000_72778_145613d2
import RHInBoxT_1d4000000_3999999d4000000_72806_72833
import RHInBoxT_1d4000000_3999999d4000000_72833_72861
import RHInBoxT_1d4000000_3999999d4000000_72861_72889
import RHInBoxT_1d4000000_3999999d4000000_72889_72917
import RHInBoxT_1d4000000_3999999d4000000_72917_72944
import RHInBoxT_1d4000000_3999999d4000000_72944_72972
import RHInBoxT_1d4000000_3999999d4000000_72972_73000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h73000

/-- The 36-band NOMINAL partition of `[72000, 73000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 72000
  | 1 => 72028
  | 2 => 72056
  | 3 => 72083
  | 4 => 72111
  | 5 => 72139
  | 6 => 72167
  | 7 => 72194
  | 8 => 72222
  | 9 => 72250
  | 10 => 72278
  | 11 => 72306
  | 12 => 72333
  | 13 => 72361
  | 14 => 72389
  | 15 => 72417
  | 16 => 72444
  | 17 => 72472
  | 18 => 72500
  | 19 => 72528
  | 20 => 72556
  | 21 => 72583
  | 22 => 72611
  | 23 => 72639
  | 24 => 72667
  | 25 => 72694
  | 26 => 72722
  | 27 => 72750
  | 28 => 72778
  | 29 => 72806
  | 30 => 72833
  | 31 => 72861
  | 32 => 72889
  | 33 => 72917
  | 34 => 72944
  | 35 => 72972
  | 36 => 73000
  | _ => 73000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((72000:ℝ)) ≤ (72028); norm_num
  · show ((72028:ℝ)) ≤ (72056); norm_num
  · show ((72056:ℝ)) ≤ (72083); norm_num
  · show ((72083:ℝ)) ≤ (72111); norm_num
  · show ((72111:ℝ)) ≤ (72139); norm_num
  · show ((72139:ℝ)) ≤ (72167); norm_num
  · show ((72167:ℝ)) ≤ (72194); norm_num
  · show ((72194:ℝ)) ≤ (72222); norm_num
  · show ((72222:ℝ)) ≤ (72250); norm_num
  · show ((72250:ℝ)) ≤ (72278); norm_num
  · show ((72278:ℝ)) ≤ (72306); norm_num
  · show ((72306:ℝ)) ≤ (72333); norm_num
  · show ((72333:ℝ)) ≤ (72361); norm_num
  · show ((72361:ℝ)) ≤ (72389); norm_num
  · show ((72389:ℝ)) ≤ (72417); norm_num
  · show ((72417:ℝ)) ≤ (72444); norm_num
  · show ((72444:ℝ)) ≤ (72472); norm_num
  · show ((72472:ℝ)) ≤ (72500); norm_num
  · show ((72500:ℝ)) ≤ (72528); norm_num
  · show ((72528:ℝ)) ≤ (72556); norm_num
  · show ((72556:ℝ)) ≤ (72583); norm_num
  · show ((72583:ℝ)) ≤ (72611); norm_num
  · show ((72611:ℝ)) ≤ (72639); norm_num
  · show ((72639:ℝ)) ≤ (72667); norm_num
  · show ((72667:ℝ)) ≤ (72694); norm_num
  · show ((72694:ℝ)) ≤ (72722); norm_num
  · show ((72722:ℝ)) ≤ (72750); norm_num
  · show ((72750:ℝ)) ≤ (72778); norm_num
  · show ((72778:ℝ)) ≤ (72806); norm_num
  · show ((72806:ℝ)) ≤ (72833); norm_num
  · show ((72833:ℝ)) ≤ (72861); norm_num
  · show ((72861:ℝ)) ≤ (72889); norm_num
  · show ((72889:ℝ)) ≤ (72917); norm_num
  · show ((72917:ℝ)) ≤ (72944); norm_num
  · show ((72944:ℝ)) ≤ (72972); norm_num
  · show ((72972:ℝ)) ≤ (73000); norm_num
  · show ((73000:ℝ)) ≤ (73000); norm_num
  · exact le_refl _

/-- The lower edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 72000
  | 1 => 72028
  | 2 => 72056
  | 3 => 72083
  | 4 => 72111
  | 5 => 72139
  | 6 => 72167
  | 7 => 72194
  | 8 => 72222
  | 9 => 72250
  | 10 => 72278
  | 11 => 72306
  | 12 => 289331 / 4
  | 13 => 72361
  | 14 => 72389
  | 15 => 72417
  | 16 => 72444
  | 17 => 72472
  | 18 => 72500
  | 19 => 72528
  | 20 => 72556
  | 21 => 72583
  | 22 => 72611
  | 23 => 72639
  | 24 => 72667
  | 25 => 72694
  | 26 => 72722
  | 27 => 72750
  | 28 => 72778
  | 29 => 72806
  | 30 => 72833
  | 31 => 72861
  | 32 => 72889
  | 33 => 72917
  | 34 => 72944
  | 35 => 72972
  | _ => 72972

/-- The upper edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 72028
  | 1 => 72056
  | 2 => 72083
  | 3 => 72111
  | 4 => 72139
  | 5 => 72167
  | 6 => 72194
  | 7 => 72222
  | 8 => 72250
  | 9 => 72278
  | 10 => 72306
  | 11 => 72333
  | 12 => 72361
  | 13 => 72389
  | 14 => 72417
  | 15 => 289777 / 4
  | 16 => 72472
  | 17 => 72500
  | 18 => 72528
  | 19 => 72556
  | 20 => 72583
  | 21 => 72611
  | 22 => 72639
  | 23 => 72667
  | 24 => 72694
  | 25 => 72722
  | 26 => 72750
  | 27 => 72778
  | 28 => 145613 / 2
  | 29 => 72833
  | 30 => 72861
  | 31 => 72889
  | 32 => 72917
  | 33 => 72944
  | 34 => 72972
  | 35 => 73000
  | _ => 73000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 36 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 73000` (`log 73000 ≤ 12`, `2.7^12 ≥ 73000`). -/
theorem haC_73000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 73000 := by
  have hlog : Real.log 73000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 73000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 73000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[72000, 73000]` segment's band hypothesis: every band `i < 36` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 36 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 36 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[72000, 73000]` SEGMENT: every zero with `72000 ≤ Im ≤ 73000` is on the line. -/
theorem segment_72000_73000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 73000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (72000:ℝ) ≤ ρ.im → ρ.im ≤ 73000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 72000 73000 bndSeg 36 (by norm_num) bndSeg_mono rfl rfl haC_73000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 73000 via the HEIGHT CHAIN**: `[0,72000]` ∘ `[72000,73000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_73000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 73000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 73000 → ρ.re = 1 / 2 := by
  have hγ72000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 72000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 72000 73000
    (AllZeros_h72000.all_nontrivial_zeros_up_to_height_72000_of_bands
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
      hγ72000)
    (segment_72000_73000 hbands hγ)

end AllZeros_h73000
