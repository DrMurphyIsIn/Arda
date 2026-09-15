/-  Height-chain step: all nontrivial zeta zeros up to height 95000 on Re = 1/2 --
    `AllZeros_h94000` + a `[94000, 95000]` SEGMENT certificate (36 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h94000
import RHInBoxT_1d4000000_3999999d4000000_94000_376113d4
import RHInBoxT_1d4000000_3999999d4000000_376111d4_376225d4
import RHInBoxT_1d4000000_3999999d4000000_94056_376333d4
import RHInBoxT_1d4000000_3999999d4000000_94083_94111
import RHInBoxT_1d4000000_3999999d4000000_94111_94139
import RHInBoxT_1d4000000_3999999d4000000_94139_376669d4
import RHInBoxT_1d4000000_3999999d4000000_94167_94194
import RHInBoxT_1d4000000_3999999d4000000_94194_94222
import RHInBoxT_1d4000000_3999999d4000000_94222_94250
import RHInBoxT_1d4000000_3999999d4000000_94250_377113d4
import RHInBoxT_1d4000000_3999999d4000000_94278_377225d4
import RHInBoxT_1d4000000_3999999d4000000_94306_94333
import RHInBoxT_1d4000000_3999999d4000000_94333_94361
import RHInBoxT_1d4000000_3999999d4000000_94361_94389
import RHInBoxT_1d4000000_3999999d4000000_94389_94417
import RHInBoxT_1d4000000_3999999d4000000_94417_188889d2
import RHInBoxT_1d4000000_3999999d4000000_94444_94472
import RHInBoxT_1d4000000_3999999d4000000_94472_94500
import RHInBoxT_1d4000000_3999999d4000000_94500_94528
import RHInBoxT_1d4000000_3999999d4000000_378111d4_94556
import RHInBoxT_1d4000000_3999999d4000000_94556_94583
import RHInBoxT_1d4000000_3999999d4000000_94583_94611
import RHInBoxT_1d4000000_3999999d4000000_94611_94639
import RHInBoxT_1d4000000_3999999d4000000_94639_378669d4
import RHInBoxT_1d4000000_3999999d4000000_94667_94694
import RHInBoxT_1d4000000_3999999d4000000_94694_94722
import RHInBoxT_1d4000000_3999999d4000000_94722_94750
import RHInBoxT_1d4000000_3999999d4000000_94750_94778
import RHInBoxT_1d4000000_3999999d4000000_94778_94806
import RHInBoxT_1d4000000_3999999d4000000_94806_94833
import RHInBoxT_1d4000000_3999999d4000000_94833_94861
import RHInBoxT_1d4000000_3999999d4000000_94861_379557d4
import RHInBoxT_1d4000000_3999999d4000000_94889_94917
import RHInBoxT_1d4000000_3999999d4000000_94917_94944
import RHInBoxT_1d4000000_3999999d4000000_94944_94972
import RHInBoxT_1d4000000_3999999d4000000_94972_95000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h95000

/-- The 36-band NOMINAL partition of `[94000, 95000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 94000
  | 1 => 94028
  | 2 => 94056
  | 3 => 94083
  | 4 => 94111
  | 5 => 94139
  | 6 => 94167
  | 7 => 94194
  | 8 => 94222
  | 9 => 94250
  | 10 => 94278
  | 11 => 94306
  | 12 => 94333
  | 13 => 94361
  | 14 => 94389
  | 15 => 94417
  | 16 => 94444
  | 17 => 94472
  | 18 => 94500
  | 19 => 94528
  | 20 => 94556
  | 21 => 94583
  | 22 => 94611
  | 23 => 94639
  | 24 => 94667
  | 25 => 94694
  | 26 => 94722
  | 27 => 94750
  | 28 => 94778
  | 29 => 94806
  | 30 => 94833
  | 31 => 94861
  | 32 => 94889
  | 33 => 94917
  | 34 => 94944
  | 35 => 94972
  | 36 => 95000
  | _ => 95000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((94000:ℝ)) ≤ (94028); norm_num
  · show ((94028:ℝ)) ≤ (94056); norm_num
  · show ((94056:ℝ)) ≤ (94083); norm_num
  · show ((94083:ℝ)) ≤ (94111); norm_num
  · show ((94111:ℝ)) ≤ (94139); norm_num
  · show ((94139:ℝ)) ≤ (94167); norm_num
  · show ((94167:ℝ)) ≤ (94194); norm_num
  · show ((94194:ℝ)) ≤ (94222); norm_num
  · show ((94222:ℝ)) ≤ (94250); norm_num
  · show ((94250:ℝ)) ≤ (94278); norm_num
  · show ((94278:ℝ)) ≤ (94306); norm_num
  · show ((94306:ℝ)) ≤ (94333); norm_num
  · show ((94333:ℝ)) ≤ (94361); norm_num
  · show ((94361:ℝ)) ≤ (94389); norm_num
  · show ((94389:ℝ)) ≤ (94417); norm_num
  · show ((94417:ℝ)) ≤ (94444); norm_num
  · show ((94444:ℝ)) ≤ (94472); norm_num
  · show ((94472:ℝ)) ≤ (94500); norm_num
  · show ((94500:ℝ)) ≤ (94528); norm_num
  · show ((94528:ℝ)) ≤ (94556); norm_num
  · show ((94556:ℝ)) ≤ (94583); norm_num
  · show ((94583:ℝ)) ≤ (94611); norm_num
  · show ((94611:ℝ)) ≤ (94639); norm_num
  · show ((94639:ℝ)) ≤ (94667); norm_num
  · show ((94667:ℝ)) ≤ (94694); norm_num
  · show ((94694:ℝ)) ≤ (94722); norm_num
  · show ((94722:ℝ)) ≤ (94750); norm_num
  · show ((94750:ℝ)) ≤ (94778); norm_num
  · show ((94778:ℝ)) ≤ (94806); norm_num
  · show ((94806:ℝ)) ≤ (94833); norm_num
  · show ((94833:ℝ)) ≤ (94861); norm_num
  · show ((94861:ℝ)) ≤ (94889); norm_num
  · show ((94889:ℝ)) ≤ (94917); norm_num
  · show ((94917:ℝ)) ≤ (94944); norm_num
  · show ((94944:ℝ)) ≤ (94972); norm_num
  · show ((94972:ℝ)) ≤ (95000); norm_num
  · show ((95000:ℝ)) ≤ (95000); norm_num
  · exact le_refl _

/-- The lower edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 94000
  | 1 => 376111 / 4
  | 2 => 94056
  | 3 => 94083
  | 4 => 94111
  | 5 => 94139
  | 6 => 94167
  | 7 => 94194
  | 8 => 94222
  | 9 => 94250
  | 10 => 94278
  | 11 => 94306
  | 12 => 94333
  | 13 => 94361
  | 14 => 94389
  | 15 => 94417
  | 16 => 94444
  | 17 => 94472
  | 18 => 94500
  | 19 => 378111 / 4
  | 20 => 94556
  | 21 => 94583
  | 22 => 94611
  | 23 => 94639
  | 24 => 94667
  | 25 => 94694
  | 26 => 94722
  | 27 => 94750
  | 28 => 94778
  | 29 => 94806
  | 30 => 94833
  | 31 => 94861
  | 32 => 94889
  | 33 => 94917
  | 34 => 94944
  | 35 => 94972
  | _ => 94972

/-- The upper edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 376113 / 4
  | 1 => 376225 / 4
  | 2 => 376333 / 4
  | 3 => 94111
  | 4 => 94139
  | 5 => 376669 / 4
  | 6 => 94194
  | 7 => 94222
  | 8 => 94250
  | 9 => 377113 / 4
  | 10 => 377225 / 4
  | 11 => 94333
  | 12 => 94361
  | 13 => 94389
  | 14 => 94417
  | 15 => 188889 / 2
  | 16 => 94472
  | 17 => 94500
  | 18 => 94528
  | 19 => 94556
  | 20 => 94583
  | 21 => 94611
  | 22 => 94639
  | 23 => 378669 / 4
  | 24 => 94694
  | 25 => 94722
  | 26 => 94750
  | 27 => 94778
  | 28 => 94806
  | 29 => 94833
  | 30 => 94861
  | 31 => 379557 / 4
  | 32 => 94917
  | 33 => 94944
  | 34 => 94972
  | 35 => 95000
  | _ => 95000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 36 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 95000` (`log 95000 ≤ 12`, `2.7^12 ≥ 95000`). -/
theorem haC_95000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 95000 := by
  have hlog : Real.log 95000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 95000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 95000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[94000, 95000]` segment's band hypothesis: every band `i < 36` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 36 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 36 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[94000, 95000]` SEGMENT: every zero with `94000 ≤ Im ≤ 95000` is on the line. -/
theorem segment_94000_95000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 95000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (94000:ℝ) ≤ ρ.im → ρ.im ≤ 95000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 94000 95000 bndSeg 36 (by norm_num) bndSeg_mono rfl rfl haC_95000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 95000 via the HEIGHT CHAIN**: `[0,94000]` ∘ `[94000,95000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_95000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 95000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 95000 → ρ.re = 1 / 2 := by
  have hγ94000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 94000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 94000 95000
    (AllZeros_h94000.all_nontrivial_zeros_up_to_height_94000_of_bands
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
      hγ94000)
    (segment_94000_95000 hbands hγ)

end AllZeros_h95000
