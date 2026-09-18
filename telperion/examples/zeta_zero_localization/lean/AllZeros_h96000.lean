/-  Height-chain step: all nontrivial zeta zeros up to height 96000 on Re = 1/2 --
    `AllZeros_h95000` + a `[95000, 96000]` SEGMENT certificate (36 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h95000
import RHInBoxT_1d4000000_3999999d4000000_379999d4_95028
import RHInBoxT_1d4000000_3999999d4000000_95028_380225d4
import RHInBoxT_1d4000000_3999999d4000000_95056_95083
import RHInBoxT_1d4000000_3999999d4000000_95083_95111
import RHInBoxT_1d4000000_3999999d4000000_95111_95139
import RHInBoxT_1d4000000_3999999d4000000_380555d4_95167
import RHInBoxT_1d4000000_3999999d4000000_95167_95194
import RHInBoxT_1d4000000_3999999d4000000_95194_95222
import RHInBoxT_1d4000000_3999999d4000000_95222_381001d4
import RHInBoxT_1d4000000_3999999d4000000_95250_95278
import RHInBoxT_1d4000000_3999999d4000000_95278_95306
import RHInBoxT_1d4000000_3999999d4000000_95306_95333
import RHInBoxT_1d4000000_3999999d4000000_95333_95361
import RHInBoxT_1d4000000_3999999d4000000_381443d4_95389
import RHInBoxT_1d4000000_3999999d4000000_381555d4_95417
import RHInBoxT_1d4000000_3999999d4000000_95417_95444
import RHInBoxT_1d4000000_3999999d4000000_95444_95472
import RHInBoxT_1d4000000_3999999d4000000_95472_95500
import RHInBoxT_1d4000000_3999999d4000000_95500_95528
import RHInBoxT_1d4000000_3999999d4000000_95528_95556
import RHInBoxT_1d4000000_3999999d4000000_95556_95583
import RHInBoxT_1d4000000_3999999d4000000_95583_95611
import RHInBoxT_1d4000000_3999999d4000000_95611_95639
import RHInBoxT_1d4000000_3999999d4000000_95639_95667
import RHInBoxT_1d4000000_3999999d4000000_382667d4_95694
import RHInBoxT_1d4000000_3999999d4000000_95694_95722
import RHInBoxT_1d4000000_3999999d4000000_95722_383001d4
import RHInBoxT_1d4000000_3999999d4000000_95750_95778
import RHInBoxT_1d4000000_3999999d4000000_95778_95806
import RHInBoxT_1d4000000_3999999d4000000_95806_95833
import RHInBoxT_1d4000000_3999999d4000000_95833_95861
import RHInBoxT_1d4000000_3999999d4000000_95861_95889
import RHInBoxT_1d4000000_3999999d4000000_95889_95917
import RHInBoxT_1d4000000_3999999d4000000_95917_383777d4
import RHInBoxT_1d4000000_3999999d4000000_95944_95972
import RHInBoxT_1d4000000_3999999d4000000_95972_384001d4

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h96000

/-- The 36-band NOMINAL partition of `[95000, 96000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 95000
  | 1 => 95028
  | 2 => 95056
  | 3 => 95083
  | 4 => 95111
  | 5 => 95139
  | 6 => 95167
  | 7 => 95194
  | 8 => 95222
  | 9 => 95250
  | 10 => 95278
  | 11 => 95306
  | 12 => 95333
  | 13 => 95361
  | 14 => 95389
  | 15 => 95417
  | 16 => 95444
  | 17 => 95472
  | 18 => 95500
  | 19 => 95528
  | 20 => 95556
  | 21 => 95583
  | 22 => 95611
  | 23 => 95639
  | 24 => 95667
  | 25 => 95694
  | 26 => 95722
  | 27 => 95750
  | 28 => 95778
  | 29 => 95806
  | 30 => 95833
  | 31 => 95861
  | 32 => 95889
  | 33 => 95917
  | 34 => 95944
  | 35 => 95972
  | 36 => 96000
  | _ => 96000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((95000:ℝ)) ≤ (95028); norm_num
  · show ((95028:ℝ)) ≤ (95056); norm_num
  · show ((95056:ℝ)) ≤ (95083); norm_num
  · show ((95083:ℝ)) ≤ (95111); norm_num
  · show ((95111:ℝ)) ≤ (95139); norm_num
  · show ((95139:ℝ)) ≤ (95167); norm_num
  · show ((95167:ℝ)) ≤ (95194); norm_num
  · show ((95194:ℝ)) ≤ (95222); norm_num
  · show ((95222:ℝ)) ≤ (95250); norm_num
  · show ((95250:ℝ)) ≤ (95278); norm_num
  · show ((95278:ℝ)) ≤ (95306); norm_num
  · show ((95306:ℝ)) ≤ (95333); norm_num
  · show ((95333:ℝ)) ≤ (95361); norm_num
  · show ((95361:ℝ)) ≤ (95389); norm_num
  · show ((95389:ℝ)) ≤ (95417); norm_num
  · show ((95417:ℝ)) ≤ (95444); norm_num
  · show ((95444:ℝ)) ≤ (95472); norm_num
  · show ((95472:ℝ)) ≤ (95500); norm_num
  · show ((95500:ℝ)) ≤ (95528); norm_num
  · show ((95528:ℝ)) ≤ (95556); norm_num
  · show ((95556:ℝ)) ≤ (95583); norm_num
  · show ((95583:ℝ)) ≤ (95611); norm_num
  · show ((95611:ℝ)) ≤ (95639); norm_num
  · show ((95639:ℝ)) ≤ (95667); norm_num
  · show ((95667:ℝ)) ≤ (95694); norm_num
  · show ((95694:ℝ)) ≤ (95722); norm_num
  · show ((95722:ℝ)) ≤ (95750); norm_num
  · show ((95750:ℝ)) ≤ (95778); norm_num
  · show ((95778:ℝ)) ≤ (95806); norm_num
  · show ((95806:ℝ)) ≤ (95833); norm_num
  · show ((95833:ℝ)) ≤ (95861); norm_num
  · show ((95861:ℝ)) ≤ (95889); norm_num
  · show ((95889:ℝ)) ≤ (95917); norm_num
  · show ((95917:ℝ)) ≤ (95944); norm_num
  · show ((95944:ℝ)) ≤ (95972); norm_num
  · show ((95972:ℝ)) ≤ (96000); norm_num
  · show ((96000:ℝ)) ≤ (96000); norm_num
  · exact le_refl _

/-- The lower edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 379999 / 4
  | 1 => 95028
  | 2 => 95056
  | 3 => 95083
  | 4 => 95111
  | 5 => 380555 / 4
  | 6 => 95167
  | 7 => 95194
  | 8 => 95222
  | 9 => 95250
  | 10 => 95278
  | 11 => 95306
  | 12 => 95333
  | 13 => 381443 / 4
  | 14 => 381555 / 4
  | 15 => 95417
  | 16 => 95444
  | 17 => 95472
  | 18 => 95500
  | 19 => 95528
  | 20 => 95556
  | 21 => 95583
  | 22 => 95611
  | 23 => 95639
  | 24 => 382667 / 4
  | 25 => 95694
  | 26 => 95722
  | 27 => 95750
  | 28 => 95778
  | 29 => 95806
  | 30 => 95833
  | 31 => 95861
  | 32 => 95889
  | 33 => 95917
  | 34 => 95944
  | 35 => 95972
  | _ => 95972

/-- The upper edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 95028
  | 1 => 380225 / 4
  | 2 => 95083
  | 3 => 95111
  | 4 => 95139
  | 5 => 95167
  | 6 => 95194
  | 7 => 95222
  | 8 => 381001 / 4
  | 9 => 95278
  | 10 => 95306
  | 11 => 95333
  | 12 => 95361
  | 13 => 95389
  | 14 => 95417
  | 15 => 95444
  | 16 => 95472
  | 17 => 95500
  | 18 => 95528
  | 19 => 95556
  | 20 => 95583
  | 21 => 95611
  | 22 => 95639
  | 23 => 95667
  | 24 => 95694
  | 25 => 95722
  | 26 => 383001 / 4
  | 27 => 95778
  | 28 => 95806
  | 29 => 95833
  | 30 => 95861
  | 31 => 95889
  | 32 => 95917
  | 33 => 383777 / 4
  | 34 => 95972
  | 35 => 384001 / 4
  | _ => 384001 / 4

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 36 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 96000` (`log 96000 ≤ 12`, `2.7^12 ≥ 96000`). -/
theorem haC_96000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 96000 := by
  have hlog : Real.log 96000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 96000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 96000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[95000, 96000]` segment's band hypothesis: every band `i < 36` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 36 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 36 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[95000, 96000]` SEGMENT: every zero with `95000 ≤ Im ≤ 96000` is on the line. -/
theorem segment_95000_96000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 96000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (95000:ℝ) ≤ ρ.im → ρ.im ≤ 96000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 95000 96000 bndSeg 36 (by norm_num) bndSeg_mono rfl rfl haC_96000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 96000 via the HEIGHT CHAIN**: `[0,95000]` ∘ `[95000,96000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_96000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 96000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 96000 → ρ.re = 1 / 2 := by
  have hγ95000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 95000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 95000 96000
    (AllZeros_h95000.all_nontrivial_zeros_up_to_height_95000_of_bands
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
      hγ95000)
    (segment_95000_96000 hbands hγ)

end AllZeros_h96000
