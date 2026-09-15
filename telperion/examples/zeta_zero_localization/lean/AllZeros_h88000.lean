/-  Height-chain step: all nontrivial zeta zeros up to height 88000 on Re = 1/2 --
    `AllZeros_h87000` + a `[87000, 88000]` SEGMENT certificate (36 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h87000
import RHInBoxT_1d4000000_3999999d4000000_347999d4_87028
import RHInBoxT_1d4000000_3999999d4000000_87028_87056
import RHInBoxT_1d4000000_3999999d4000000_87056_87083
import RHInBoxT_1d4000000_3999999d4000000_348331d4_87111
import RHInBoxT_1d4000000_3999999d4000000_87111_87139
import RHInBoxT_1d4000000_3999999d4000000_87139_87167
import RHInBoxT_1d4000000_3999999d4000000_87167_87194
import RHInBoxT_1d4000000_3999999d4000000_87194_87222
import RHInBoxT_1d4000000_3999999d4000000_87222_174501d2
import RHInBoxT_1d4000000_3999999d4000000_87250_87278
import RHInBoxT_1d4000000_3999999d4000000_87278_87306
import RHInBoxT_1d4000000_3999999d4000000_349223d4_87333
import RHInBoxT_1d4000000_3999999d4000000_349331d4_349445d4
import RHInBoxT_1d4000000_3999999d4000000_87361_87389
import RHInBoxT_1d4000000_3999999d4000000_87389_87417
import RHInBoxT_1d4000000_3999999d4000000_87417_87444
import RHInBoxT_1d4000000_3999999d4000000_87444_87472
import RHInBoxT_1d4000000_3999999d4000000_87472_350001d4
import RHInBoxT_1d4000000_3999999d4000000_87500_87528
import RHInBoxT_1d4000000_3999999d4000000_87528_350225d4
import RHInBoxT_1d4000000_3999999d4000000_87556_87583
import RHInBoxT_1d4000000_3999999d4000000_87583_350445d4
import RHInBoxT_1d4000000_3999999d4000000_87611_87639
import RHInBoxT_1d4000000_3999999d4000000_87639_350669d4
import RHInBoxT_1d4000000_3999999d4000000_87667_87694
import RHInBoxT_1d4000000_3999999d4000000_87694_87722
import RHInBoxT_1d4000000_3999999d4000000_87722_87750
import RHInBoxT_1d4000000_3999999d4000000_87750_87778
import RHInBoxT_1d4000000_3999999d4000000_87778_87806
import RHInBoxT_1d4000000_3999999d4000000_87806_87833
import RHInBoxT_1d4000000_3999999d4000000_87833_351445d4
import RHInBoxT_1d4000000_3999999d4000000_87861_87889
import RHInBoxT_1d4000000_3999999d4000000_351555d4_87917
import RHInBoxT_1d4000000_3999999d4000000_87917_87944
import RHInBoxT_1d4000000_3999999d4000000_351775d4_87972
import RHInBoxT_1d4000000_3999999d4000000_87972_88000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h88000

/-- The 36-band NOMINAL partition of `[87000, 88000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 87000
  | 1 => 87028
  | 2 => 87056
  | 3 => 87083
  | 4 => 87111
  | 5 => 87139
  | 6 => 87167
  | 7 => 87194
  | 8 => 87222
  | 9 => 87250
  | 10 => 87278
  | 11 => 87306
  | 12 => 87333
  | 13 => 87361
  | 14 => 87389
  | 15 => 87417
  | 16 => 87444
  | 17 => 87472
  | 18 => 87500
  | 19 => 87528
  | 20 => 87556
  | 21 => 87583
  | 22 => 87611
  | 23 => 87639
  | 24 => 87667
  | 25 => 87694
  | 26 => 87722
  | 27 => 87750
  | 28 => 87778
  | 29 => 87806
  | 30 => 87833
  | 31 => 87861
  | 32 => 87889
  | 33 => 87917
  | 34 => 87944
  | 35 => 87972
  | 36 => 88000
  | _ => 88000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((87000:ℝ)) ≤ (87028); norm_num
  · show ((87028:ℝ)) ≤ (87056); norm_num
  · show ((87056:ℝ)) ≤ (87083); norm_num
  · show ((87083:ℝ)) ≤ (87111); norm_num
  · show ((87111:ℝ)) ≤ (87139); norm_num
  · show ((87139:ℝ)) ≤ (87167); norm_num
  · show ((87167:ℝ)) ≤ (87194); norm_num
  · show ((87194:ℝ)) ≤ (87222); norm_num
  · show ((87222:ℝ)) ≤ (87250); norm_num
  · show ((87250:ℝ)) ≤ (87278); norm_num
  · show ((87278:ℝ)) ≤ (87306); norm_num
  · show ((87306:ℝ)) ≤ (87333); norm_num
  · show ((87333:ℝ)) ≤ (87361); norm_num
  · show ((87361:ℝ)) ≤ (87389); norm_num
  · show ((87389:ℝ)) ≤ (87417); norm_num
  · show ((87417:ℝ)) ≤ (87444); norm_num
  · show ((87444:ℝ)) ≤ (87472); norm_num
  · show ((87472:ℝ)) ≤ (87500); norm_num
  · show ((87500:ℝ)) ≤ (87528); norm_num
  · show ((87528:ℝ)) ≤ (87556); norm_num
  · show ((87556:ℝ)) ≤ (87583); norm_num
  · show ((87583:ℝ)) ≤ (87611); norm_num
  · show ((87611:ℝ)) ≤ (87639); norm_num
  · show ((87639:ℝ)) ≤ (87667); norm_num
  · show ((87667:ℝ)) ≤ (87694); norm_num
  · show ((87694:ℝ)) ≤ (87722); norm_num
  · show ((87722:ℝ)) ≤ (87750); norm_num
  · show ((87750:ℝ)) ≤ (87778); norm_num
  · show ((87778:ℝ)) ≤ (87806); norm_num
  · show ((87806:ℝ)) ≤ (87833); norm_num
  · show ((87833:ℝ)) ≤ (87861); norm_num
  · show ((87861:ℝ)) ≤ (87889); norm_num
  · show ((87889:ℝ)) ≤ (87917); norm_num
  · show ((87917:ℝ)) ≤ (87944); norm_num
  · show ((87944:ℝ)) ≤ (87972); norm_num
  · show ((87972:ℝ)) ≤ (88000); norm_num
  · show ((88000:ℝ)) ≤ (88000); norm_num
  · exact le_refl _

/-- The lower edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 347999 / 4
  | 1 => 87028
  | 2 => 87056
  | 3 => 348331 / 4
  | 4 => 87111
  | 5 => 87139
  | 6 => 87167
  | 7 => 87194
  | 8 => 87222
  | 9 => 87250
  | 10 => 87278
  | 11 => 349223 / 4
  | 12 => 349331 / 4
  | 13 => 87361
  | 14 => 87389
  | 15 => 87417
  | 16 => 87444
  | 17 => 87472
  | 18 => 87500
  | 19 => 87528
  | 20 => 87556
  | 21 => 87583
  | 22 => 87611
  | 23 => 87639
  | 24 => 87667
  | 25 => 87694
  | 26 => 87722
  | 27 => 87750
  | 28 => 87778
  | 29 => 87806
  | 30 => 87833
  | 31 => 87861
  | 32 => 351555 / 4
  | 33 => 87917
  | 34 => 351775 / 4
  | 35 => 87972
  | _ => 87972

/-- The upper edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 87028
  | 1 => 87056
  | 2 => 87083
  | 3 => 87111
  | 4 => 87139
  | 5 => 87167
  | 6 => 87194
  | 7 => 87222
  | 8 => 174501 / 2
  | 9 => 87278
  | 10 => 87306
  | 11 => 87333
  | 12 => 349445 / 4
  | 13 => 87389
  | 14 => 87417
  | 15 => 87444
  | 16 => 87472
  | 17 => 350001 / 4
  | 18 => 87528
  | 19 => 350225 / 4
  | 20 => 87583
  | 21 => 350445 / 4
  | 22 => 87639
  | 23 => 350669 / 4
  | 24 => 87694
  | 25 => 87722
  | 26 => 87750
  | 27 => 87778
  | 28 => 87806
  | 29 => 87833
  | 30 => 351445 / 4
  | 31 => 87889
  | 32 => 87917
  | 33 => 87944
  | 34 => 87972
  | 35 => 88000
  | _ => 88000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 36 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 88000` (`log 88000 ≤ 12`, `2.7^12 ≥ 88000`). -/
theorem haC_88000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 88000 := by
  have hlog : Real.log 88000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 88000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 88000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[87000, 88000]` segment's band hypothesis: every band `i < 36` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 36 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 36 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[87000, 88000]` SEGMENT: every zero with `87000 ≤ Im ≤ 88000` is on the line. -/
theorem segment_87000_88000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 88000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (87000:ℝ) ≤ ρ.im → ρ.im ≤ 88000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 87000 88000 bndSeg 36 (by norm_num) bndSeg_mono rfl rfl haC_88000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 88000 via the HEIGHT CHAIN**: `[0,87000]` ∘ `[87000,88000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_88000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 88000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 88000 → ρ.re = 1 / 2 := by
  have hγ87000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 87000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 87000 88000
    (AllZeros_h87000.all_nontrivial_zeros_up_to_height_87000_of_bands
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
      hγ87000)
    (segment_87000_88000 hbands hγ)

end AllZeros_h88000
