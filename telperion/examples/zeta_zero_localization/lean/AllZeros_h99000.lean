/-  Height-chain step: all nontrivial zeta zeros up to height 99000 on Re = 1/2 --
    `AllZeros_h98000` + a `[98000, 99000]` SEGMENT certificate (38 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h98000
import RHInBoxT_1d4000000_3999999d4000000_98000_98026
import RHInBoxT_1d4000000_3999999d4000000_98026_98053
import RHInBoxT_1d4000000_3999999d4000000_98053_98079
import RHInBoxT_1d4000000_3999999d4000000_98079_98105
import RHInBoxT_1d4000000_3999999d4000000_98105_392529d4
import RHInBoxT_1d4000000_3999999d4000000_98132_98158
import RHInBoxT_1d4000000_3999999d4000000_98158_98184
import RHInBoxT_1d4000000_3999999d4000000_98184_98211
import RHInBoxT_1d4000000_3999999d4000000_98211_98237
import RHInBoxT_1d4000000_3999999d4000000_98237_98263
import RHInBoxT_1d4000000_3999999d4000000_393051d4_98289
import RHInBoxT_1d4000000_3999999d4000000_98289_98316
import RHInBoxT_1d4000000_3999999d4000000_98316_98342
import RHInBoxT_1d4000000_3999999d4000000_98342_98368
import RHInBoxT_1d4000000_3999999d4000000_98368_98395
import RHInBoxT_1d4000000_3999999d4000000_98395_98421
import RHInBoxT_1d4000000_3999999d4000000_98421_98447
import RHInBoxT_1d4000000_3999999d4000000_98447_98474
import RHInBoxT_1d4000000_3999999d4000000_98474_197001d2
import RHInBoxT_1d4000000_3999999d4000000_98500_98526
import RHInBoxT_1d4000000_3999999d4000000_98526_98553
import RHInBoxT_1d4000000_3999999d4000000_98553_98579
import RHInBoxT_1d4000000_3999999d4000000_98579_98605
import RHInBoxT_1d4000000_3999999d4000000_98605_98632
import RHInBoxT_1d4000000_3999999d4000000_98632_98658
import RHInBoxT_1d4000000_3999999d4000000_98658_98684
import RHInBoxT_1d4000000_3999999d4000000_394735d4_394845d4
import RHInBoxT_1d4000000_3999999d4000000_98711_98737
import RHInBoxT_1d4000000_3999999d4000000_98737_98763
import RHInBoxT_1d4000000_3999999d4000000_395051d4_98789
import RHInBoxT_1d4000000_3999999d4000000_98789_395265d4
import RHInBoxT_1d4000000_3999999d4000000_98816_98842
import RHInBoxT_1d4000000_3999999d4000000_98842_98868
import RHInBoxT_1d4000000_3999999d4000000_98868_98895
import RHInBoxT_1d4000000_3999999d4000000_395579d4_98921
import RHInBoxT_1d4000000_3999999d4000000_98921_98947
import RHInBoxT_1d4000000_3999999d4000000_98947_98974
import RHInBoxT_1d4000000_3999999d4000000_98974_99000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h99000

/-- The 38-band NOMINAL partition of `[98000, 99000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 98000
  | 1 => 98026
  | 2 => 98053
  | 3 => 98079
  | 4 => 98105
  | 5 => 98132
  | 6 => 98158
  | 7 => 98184
  | 8 => 98211
  | 9 => 98237
  | 10 => 98263
  | 11 => 98289
  | 12 => 98316
  | 13 => 98342
  | 14 => 98368
  | 15 => 98395
  | 16 => 98421
  | 17 => 98447
  | 18 => 98474
  | 19 => 98500
  | 20 => 98526
  | 21 => 98553
  | 22 => 98579
  | 23 => 98605
  | 24 => 98632
  | 25 => 98658
  | 26 => 98684
  | 27 => 98711
  | 28 => 98737
  | 29 => 98763
  | 30 => 98789
  | 31 => 98816
  | 32 => 98842
  | 33 => 98868
  | 34 => 98895
  | 35 => 98921
  | 36 => 98947
  | 37 => 98974
  | 38 => 99000
  | _ => 99000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((98000:ℝ)) ≤ (98026); norm_num
  · show ((98026:ℝ)) ≤ (98053); norm_num
  · show ((98053:ℝ)) ≤ (98079); norm_num
  · show ((98079:ℝ)) ≤ (98105); norm_num
  · show ((98105:ℝ)) ≤ (98132); norm_num
  · show ((98132:ℝ)) ≤ (98158); norm_num
  · show ((98158:ℝ)) ≤ (98184); norm_num
  · show ((98184:ℝ)) ≤ (98211); norm_num
  · show ((98211:ℝ)) ≤ (98237); norm_num
  · show ((98237:ℝ)) ≤ (98263); norm_num
  · show ((98263:ℝ)) ≤ (98289); norm_num
  · show ((98289:ℝ)) ≤ (98316); norm_num
  · show ((98316:ℝ)) ≤ (98342); norm_num
  · show ((98342:ℝ)) ≤ (98368); norm_num
  · show ((98368:ℝ)) ≤ (98395); norm_num
  · show ((98395:ℝ)) ≤ (98421); norm_num
  · show ((98421:ℝ)) ≤ (98447); norm_num
  · show ((98447:ℝ)) ≤ (98474); norm_num
  · show ((98474:ℝ)) ≤ (98500); norm_num
  · show ((98500:ℝ)) ≤ (98526); norm_num
  · show ((98526:ℝ)) ≤ (98553); norm_num
  · show ((98553:ℝ)) ≤ (98579); norm_num
  · show ((98579:ℝ)) ≤ (98605); norm_num
  · show ((98605:ℝ)) ≤ (98632); norm_num
  · show ((98632:ℝ)) ≤ (98658); norm_num
  · show ((98658:ℝ)) ≤ (98684); norm_num
  · show ((98684:ℝ)) ≤ (98711); norm_num
  · show ((98711:ℝ)) ≤ (98737); norm_num
  · show ((98737:ℝ)) ≤ (98763); norm_num
  · show ((98763:ℝ)) ≤ (98789); norm_num
  · show ((98789:ℝ)) ≤ (98816); norm_num
  · show ((98816:ℝ)) ≤ (98842); norm_num
  · show ((98842:ℝ)) ≤ (98868); norm_num
  · show ((98868:ℝ)) ≤ (98895); norm_num
  · show ((98895:ℝ)) ≤ (98921); norm_num
  · show ((98921:ℝ)) ≤ (98947); norm_num
  · show ((98947:ℝ)) ≤ (98974); norm_num
  · show ((98974:ℝ)) ≤ (99000); norm_num
  · show ((99000:ℝ)) ≤ (99000); norm_num
  · exact le_refl _

/-- The lower edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 98000
  | 1 => 98026
  | 2 => 98053
  | 3 => 98079
  | 4 => 98105
  | 5 => 98132
  | 6 => 98158
  | 7 => 98184
  | 8 => 98211
  | 9 => 98237
  | 10 => 393051 / 4
  | 11 => 98289
  | 12 => 98316
  | 13 => 98342
  | 14 => 98368
  | 15 => 98395
  | 16 => 98421
  | 17 => 98447
  | 18 => 98474
  | 19 => 98500
  | 20 => 98526
  | 21 => 98553
  | 22 => 98579
  | 23 => 98605
  | 24 => 98632
  | 25 => 98658
  | 26 => 394735 / 4
  | 27 => 98711
  | 28 => 98737
  | 29 => 395051 / 4
  | 30 => 98789
  | 31 => 98816
  | 32 => 98842
  | 33 => 98868
  | 34 => 395579 / 4
  | 35 => 98921
  | 36 => 98947
  | 37 => 98974
  | _ => 98974

/-- The upper edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 98026
  | 1 => 98053
  | 2 => 98079
  | 3 => 98105
  | 4 => 392529 / 4
  | 5 => 98158
  | 6 => 98184
  | 7 => 98211
  | 8 => 98237
  | 9 => 98263
  | 10 => 98289
  | 11 => 98316
  | 12 => 98342
  | 13 => 98368
  | 14 => 98395
  | 15 => 98421
  | 16 => 98447
  | 17 => 98474
  | 18 => 197001 / 2
  | 19 => 98526
  | 20 => 98553
  | 21 => 98579
  | 22 => 98605
  | 23 => 98632
  | 24 => 98658
  | 25 => 98684
  | 26 => 394845 / 4
  | 27 => 98737
  | 28 => 98763
  | 29 => 98789
  | 30 => 395265 / 4
  | 31 => 98842
  | 32 => 98868
  | 33 => 98895
  | 34 => 98921
  | 35 => 98947
  | 36 => 98974
  | 37 => 99000
  | _ => 99000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 38 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 99000` (`log 99000 ≤ 12`, `2.7^12 ≥ 99000`). -/
theorem haC_99000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 99000 := by
  have hlog : Real.log 99000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 99000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 99000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[98000, 99000]` segment's band hypothesis: every band `i < 38` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 38 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 38 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[98000, 99000]` SEGMENT: every zero with `98000 ≤ Im ≤ 99000` is on the line. -/
theorem segment_98000_99000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 99000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (98000:ℝ) ≤ ρ.im → ρ.im ≤ 99000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 98000 99000 bndSeg 38 (by norm_num) bndSeg_mono rfl rfl haC_99000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 99000 via the HEIGHT CHAIN**: `[0,98000]` ∘ `[98000,99000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_99000_of_bands
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
    (hbands_97000 : AllZeros_h97000.BandHyp)
    (hbands_98000 : AllZeros_h98000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 99000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 99000 → ρ.re = 1 / 2 := by
  have hγ98000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 98000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 98000 99000
    (AllZeros_h98000.all_nontrivial_zeros_up_to_height_98000_of_bands
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
      hbands_97000
      hbands_98000
      hγ98000)
    (segment_98000_99000 hbands hγ)

end AllZeros_h99000
