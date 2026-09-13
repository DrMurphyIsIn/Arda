/-  Height-chain step: all nontrivial zeta zeros up to height 97000 on Re = 1/2 --
    `AllZeros_h96000` + a `[96000, 97000]` SEGMENT certificate (36 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h96000
import RHInBoxT_1d4000000_3999999d4000000_383999d4_384113d4
import RHInBoxT_1d4000000_3999999d4000000_96028_96056
import RHInBoxT_1d4000000_3999999d4000000_96056_96083
import RHInBoxT_1d4000000_3999999d4000000_96083_96111
import RHInBoxT_1d4000000_3999999d4000000_96111_384557d4
import RHInBoxT_1d4000000_3999999d4000000_96139_96167
import RHInBoxT_1d4000000_3999999d4000000_384667d4_96194
import RHInBoxT_1d4000000_3999999d4000000_96194_384889d4
import RHInBoxT_1d4000000_3999999d4000000_96222_385001d4
import RHInBoxT_1d4000000_3999999d4000000_96250_96278
import RHInBoxT_1d4000000_3999999d4000000_96278_96306
import RHInBoxT_1d4000000_3999999d4000000_96306_96333
import RHInBoxT_1d4000000_3999999d4000000_96333_96361
import RHInBoxT_1d4000000_3999999d4000000_96361_96389
import RHInBoxT_1d4000000_3999999d4000000_96389_385669d4
import RHInBoxT_1d4000000_3999999d4000000_96417_96444
import RHInBoxT_1d4000000_3999999d4000000_96444_96472
import RHInBoxT_1d4000000_3999999d4000000_96472_96500
import RHInBoxT_1d4000000_3999999d4000000_96500_96528
import RHInBoxT_1d4000000_3999999d4000000_96528_96556
import RHInBoxT_1d4000000_3999999d4000000_96556_96583
import RHInBoxT_1d4000000_3999999d4000000_96583_96611
import RHInBoxT_1d4000000_3999999d4000000_96611_96639
import RHInBoxT_1d4000000_3999999d4000000_96639_96667
import RHInBoxT_1d4000000_3999999d4000000_96667_96694
import RHInBoxT_1d4000000_3999999d4000000_96694_96722
import RHInBoxT_1d4000000_3999999d4000000_386887d4_96750
import RHInBoxT_1d4000000_3999999d4000000_386999d4_96778
import RHInBoxT_1d4000000_3999999d4000000_96778_96806
import RHInBoxT_1d4000000_3999999d4000000_96806_96833
import RHInBoxT_1d4000000_3999999d4000000_96833_96861
import RHInBoxT_1d4000000_3999999d4000000_96861_96889
import RHInBoxT_1d4000000_3999999d4000000_96889_96917
import RHInBoxT_1d4000000_3999999d4000000_96917_387777d4
import RHInBoxT_1d4000000_3999999d4000000_96944_96972
import RHInBoxT_1d4000000_3999999d4000000_387887d4_388001d4

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h97000

/-- The 36-band NOMINAL partition of `[96000, 97000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 96000
  | 1 => 96028
  | 2 => 96056
  | 3 => 96083
  | 4 => 96111
  | 5 => 96139
  | 6 => 96167
  | 7 => 96194
  | 8 => 96222
  | 9 => 96250
  | 10 => 96278
  | 11 => 96306
  | 12 => 96333
  | 13 => 96361
  | 14 => 96389
  | 15 => 96417
  | 16 => 96444
  | 17 => 96472
  | 18 => 96500
  | 19 => 96528
  | 20 => 96556
  | 21 => 96583
  | 22 => 96611
  | 23 => 96639
  | 24 => 96667
  | 25 => 96694
  | 26 => 96722
  | 27 => 96750
  | 28 => 96778
  | 29 => 96806
  | 30 => 96833
  | 31 => 96861
  | 32 => 96889
  | 33 => 96917
  | 34 => 96944
  | 35 => 96972
  | 36 => 97000
  | _ => 97000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((96000:ℝ)) ≤ (96028); norm_num
  · show ((96028:ℝ)) ≤ (96056); norm_num
  · show ((96056:ℝ)) ≤ (96083); norm_num
  · show ((96083:ℝ)) ≤ (96111); norm_num
  · show ((96111:ℝ)) ≤ (96139); norm_num
  · show ((96139:ℝ)) ≤ (96167); norm_num
  · show ((96167:ℝ)) ≤ (96194); norm_num
  · show ((96194:ℝ)) ≤ (96222); norm_num
  · show ((96222:ℝ)) ≤ (96250); norm_num
  · show ((96250:ℝ)) ≤ (96278); norm_num
  · show ((96278:ℝ)) ≤ (96306); norm_num
  · show ((96306:ℝ)) ≤ (96333); norm_num
  · show ((96333:ℝ)) ≤ (96361); norm_num
  · show ((96361:ℝ)) ≤ (96389); norm_num
  · show ((96389:ℝ)) ≤ (96417); norm_num
  · show ((96417:ℝ)) ≤ (96444); norm_num
  · show ((96444:ℝ)) ≤ (96472); norm_num
  · show ((96472:ℝ)) ≤ (96500); norm_num
  · show ((96500:ℝ)) ≤ (96528); norm_num
  · show ((96528:ℝ)) ≤ (96556); norm_num
  · show ((96556:ℝ)) ≤ (96583); norm_num
  · show ((96583:ℝ)) ≤ (96611); norm_num
  · show ((96611:ℝ)) ≤ (96639); norm_num
  · show ((96639:ℝ)) ≤ (96667); norm_num
  · show ((96667:ℝ)) ≤ (96694); norm_num
  · show ((96694:ℝ)) ≤ (96722); norm_num
  · show ((96722:ℝ)) ≤ (96750); norm_num
  · show ((96750:ℝ)) ≤ (96778); norm_num
  · show ((96778:ℝ)) ≤ (96806); norm_num
  · show ((96806:ℝ)) ≤ (96833); norm_num
  · show ((96833:ℝ)) ≤ (96861); norm_num
  · show ((96861:ℝ)) ≤ (96889); norm_num
  · show ((96889:ℝ)) ≤ (96917); norm_num
  · show ((96917:ℝ)) ≤ (96944); norm_num
  · show ((96944:ℝ)) ≤ (96972); norm_num
  · show ((96972:ℝ)) ≤ (97000); norm_num
  · show ((97000:ℝ)) ≤ (97000); norm_num
  · exact le_refl _

/-- The lower edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 383999 / 4
  | 1 => 96028
  | 2 => 96056
  | 3 => 96083
  | 4 => 96111
  | 5 => 96139
  | 6 => 384667 / 4
  | 7 => 96194
  | 8 => 96222
  | 9 => 96250
  | 10 => 96278
  | 11 => 96306
  | 12 => 96333
  | 13 => 96361
  | 14 => 96389
  | 15 => 96417
  | 16 => 96444
  | 17 => 96472
  | 18 => 96500
  | 19 => 96528
  | 20 => 96556
  | 21 => 96583
  | 22 => 96611
  | 23 => 96639
  | 24 => 96667
  | 25 => 96694
  | 26 => 386887 / 4
  | 27 => 386999 / 4
  | 28 => 96778
  | 29 => 96806
  | 30 => 96833
  | 31 => 96861
  | 32 => 96889
  | 33 => 96917
  | 34 => 96944
  | 35 => 387887 / 4
  | _ => 387887 / 4

/-- The upper edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 384113 / 4
  | 1 => 96056
  | 2 => 96083
  | 3 => 96111
  | 4 => 384557 / 4
  | 5 => 96167
  | 6 => 96194
  | 7 => 384889 / 4
  | 8 => 385001 / 4
  | 9 => 96278
  | 10 => 96306
  | 11 => 96333
  | 12 => 96361
  | 13 => 96389
  | 14 => 385669 / 4
  | 15 => 96444
  | 16 => 96472
  | 17 => 96500
  | 18 => 96528
  | 19 => 96556
  | 20 => 96583
  | 21 => 96611
  | 22 => 96639
  | 23 => 96667
  | 24 => 96694
  | 25 => 96722
  | 26 => 96750
  | 27 => 96778
  | 28 => 96806
  | 29 => 96833
  | 30 => 96861
  | 31 => 96889
  | 32 => 96917
  | 33 => 387777 / 4
  | 34 => 96972
  | 35 => 388001 / 4
  | _ => 388001 / 4

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 36 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 97000` (`log 97000 ≤ 12`, `2.7^12 ≥ 97000`). -/
theorem haC_97000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 97000 := by
  have hlog : Real.log 97000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 97000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 97000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[96000, 97000]` segment's band hypothesis: every band `i < 36` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 36 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 36 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[96000, 97000]` SEGMENT: every zero with `96000 ≤ Im ≤ 97000` is on the line. -/
theorem segment_96000_97000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 97000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (96000:ℝ) ≤ ρ.im → ρ.im ≤ 97000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 96000 97000 bndSeg 36 (by norm_num) bndSeg_mono rfl rfl haC_97000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 97000 via the HEIGHT CHAIN**: `[0,96000]` ∘ `[96000,97000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_97000_of_bands
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
    (hbands_93000 : AllZeros_h93000.BandHyp)
    (hbands_94000 : AllZeros_h94000.BandHyp)
    (hbands_95000 : AllZeros_h95000.BandHyp)
    (hbands_96000 : AllZeros_h96000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 97000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 97000 → ρ.re = 1 / 2 := by
  have hγ96000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 96000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 96000 97000
    (AllZeros_h96000.all_nontrivial_zeros_up_to_height_96000_of_bands
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
      hbands_93000
      hbands_94000
      hbands_95000
      hbands_96000
      hγ96000)
    (segment_96000_97000 hbands hγ)

end AllZeros_h97000
