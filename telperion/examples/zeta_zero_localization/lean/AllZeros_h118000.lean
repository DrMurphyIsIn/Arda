/-  Height-chain step: all nontrivial zeta zeros up to height 118000 on Re = 1/2 --
    `AllZeros_h117000` + a `[117000, 118000]` SEGMENT certificate (38 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h117000
import RHInBoxT_1d4000000_3999999d4000000_117000_117026
import RHInBoxT_1d4000000_3999999d4000000_117026_117053
import RHInBoxT_1d4000000_3999999d4000000_117053_117079
import RHInBoxT_1d4000000_3999999d4000000_117079_468421d4
import RHInBoxT_1d4000000_3999999d4000000_117105_468529d4
import RHInBoxT_1d4000000_3999999d4000000_117132_117158
import RHInBoxT_1d4000000_3999999d4000000_117158_117184
import RHInBoxT_1d4000000_3999999d4000000_117184_117211
import RHInBoxT_1d4000000_3999999d4000000_117211_117237
import RHInBoxT_1d4000000_3999999d4000000_117237_117263
import RHInBoxT_1d4000000_3999999d4000000_117263_117289
import RHInBoxT_1d4000000_3999999d4000000_117289_117316
import RHInBoxT_1d4000000_3999999d4000000_117316_117342
import RHInBoxT_1d4000000_3999999d4000000_117342_117368
import RHInBoxT_1d4000000_3999999d4000000_117368_117395
import RHInBoxT_1d4000000_3999999d4000000_117395_469685d4
import RHInBoxT_1d4000000_3999999d4000000_117421_117447
import RHInBoxT_1d4000000_3999999d4000000_117447_117474
import RHInBoxT_1d4000000_3999999d4000000_117474_117500
import RHInBoxT_1d4000000_3999999d4000000_117500_117526
import RHInBoxT_1d4000000_3999999d4000000_117526_117553
import RHInBoxT_1d4000000_3999999d4000000_117553_117579
import RHInBoxT_1d4000000_3999999d4000000_117579_117605
import RHInBoxT_1d4000000_3999999d4000000_117605_117632
import RHInBoxT_1d4000000_3999999d4000000_117632_117658
import RHInBoxT_1d4000000_3999999d4000000_470631d4_117684
import RHInBoxT_1d4000000_3999999d4000000_470735d4_117711
import RHInBoxT_1d4000000_3999999d4000000_117711_117737
import RHInBoxT_1d4000000_3999999d4000000_117737_471053d4
import RHInBoxT_1d4000000_3999999d4000000_117763_471157d4
import RHInBoxT_1d4000000_3999999d4000000_117789_117816
import RHInBoxT_1d4000000_3999999d4000000_471263d4_117842
import RHInBoxT_1d4000000_3999999d4000000_117842_117868
import RHInBoxT_1d4000000_3999999d4000000_117868_117895
import RHInBoxT_1d4000000_3999999d4000000_117895_117921
import RHInBoxT_1d4000000_3999999d4000000_117921_117947
import RHInBoxT_1d4000000_3999999d4000000_117947_117974
import RHInBoxT_1d4000000_3999999d4000000_117974_118000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h118000

/-- The 38-band NOMINAL partition of `[117000, 118000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 117000
  | 1 => 117026
  | 2 => 117053
  | 3 => 117079
  | 4 => 117105
  | 5 => 117132
  | 6 => 117158
  | 7 => 117184
  | 8 => 117211
  | 9 => 117237
  | 10 => 117263
  | 11 => 117289
  | 12 => 117316
  | 13 => 117342
  | 14 => 117368
  | 15 => 117395
  | 16 => 117421
  | 17 => 117447
  | 18 => 117474
  | 19 => 117500
  | 20 => 117526
  | 21 => 117553
  | 22 => 117579
  | 23 => 117605
  | 24 => 117632
  | 25 => 117658
  | 26 => 117684
  | 27 => 117711
  | 28 => 117737
  | 29 => 117763
  | 30 => 117789
  | 31 => 117816
  | 32 => 117842
  | 33 => 117868
  | 34 => 117895
  | 35 => 117921
  | 36 => 117947
  | 37 => 117974
  | 38 => 118000
  | _ => 118000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((117000:ℝ)) ≤ (117026); norm_num
  · show ((117026:ℝ)) ≤ (117053); norm_num
  · show ((117053:ℝ)) ≤ (117079); norm_num
  · show ((117079:ℝ)) ≤ (117105); norm_num
  · show ((117105:ℝ)) ≤ (117132); norm_num
  · show ((117132:ℝ)) ≤ (117158); norm_num
  · show ((117158:ℝ)) ≤ (117184); norm_num
  · show ((117184:ℝ)) ≤ (117211); norm_num
  · show ((117211:ℝ)) ≤ (117237); norm_num
  · show ((117237:ℝ)) ≤ (117263); norm_num
  · show ((117263:ℝ)) ≤ (117289); norm_num
  · show ((117289:ℝ)) ≤ (117316); norm_num
  · show ((117316:ℝ)) ≤ (117342); norm_num
  · show ((117342:ℝ)) ≤ (117368); norm_num
  · show ((117368:ℝ)) ≤ (117395); norm_num
  · show ((117395:ℝ)) ≤ (117421); norm_num
  · show ((117421:ℝ)) ≤ (117447); norm_num
  · show ((117447:ℝ)) ≤ (117474); norm_num
  · show ((117474:ℝ)) ≤ (117500); norm_num
  · show ((117500:ℝ)) ≤ (117526); norm_num
  · show ((117526:ℝ)) ≤ (117553); norm_num
  · show ((117553:ℝ)) ≤ (117579); norm_num
  · show ((117579:ℝ)) ≤ (117605); norm_num
  · show ((117605:ℝ)) ≤ (117632); norm_num
  · show ((117632:ℝ)) ≤ (117658); norm_num
  · show ((117658:ℝ)) ≤ (117684); norm_num
  · show ((117684:ℝ)) ≤ (117711); norm_num
  · show ((117711:ℝ)) ≤ (117737); norm_num
  · show ((117737:ℝ)) ≤ (117763); norm_num
  · show ((117763:ℝ)) ≤ (117789); norm_num
  · show ((117789:ℝ)) ≤ (117816); norm_num
  · show ((117816:ℝ)) ≤ (117842); norm_num
  · show ((117842:ℝ)) ≤ (117868); norm_num
  · show ((117868:ℝ)) ≤ (117895); norm_num
  · show ((117895:ℝ)) ≤ (117921); norm_num
  · show ((117921:ℝ)) ≤ (117947); norm_num
  · show ((117947:ℝ)) ≤ (117974); norm_num
  · show ((117974:ℝ)) ≤ (118000); norm_num
  · show ((118000:ℝ)) ≤ (118000); norm_num
  · exact le_refl _

/-- The lower edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 117000
  | 1 => 117026
  | 2 => 117053
  | 3 => 117079
  | 4 => 117105
  | 5 => 117132
  | 6 => 117158
  | 7 => 117184
  | 8 => 117211
  | 9 => 117237
  | 10 => 117263
  | 11 => 117289
  | 12 => 117316
  | 13 => 117342
  | 14 => 117368
  | 15 => 117395
  | 16 => 117421
  | 17 => 117447
  | 18 => 117474
  | 19 => 117500
  | 20 => 117526
  | 21 => 117553
  | 22 => 117579
  | 23 => 117605
  | 24 => 117632
  | 25 => 470631 / 4
  | 26 => 470735 / 4
  | 27 => 117711
  | 28 => 117737
  | 29 => 117763
  | 30 => 117789
  | 31 => 471263 / 4
  | 32 => 117842
  | 33 => 117868
  | 34 => 117895
  | 35 => 117921
  | 36 => 117947
  | 37 => 117974
  | _ => 117974

/-- The upper edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 117026
  | 1 => 117053
  | 2 => 117079
  | 3 => 468421 / 4
  | 4 => 468529 / 4
  | 5 => 117158
  | 6 => 117184
  | 7 => 117211
  | 8 => 117237
  | 9 => 117263
  | 10 => 117289
  | 11 => 117316
  | 12 => 117342
  | 13 => 117368
  | 14 => 117395
  | 15 => 469685 / 4
  | 16 => 117447
  | 17 => 117474
  | 18 => 117500
  | 19 => 117526
  | 20 => 117553
  | 21 => 117579
  | 22 => 117605
  | 23 => 117632
  | 24 => 117658
  | 25 => 117684
  | 26 => 117711
  | 27 => 117737
  | 28 => 471053 / 4
  | 29 => 471157 / 4
  | 30 => 117816
  | 31 => 117842
  | 32 => 117868
  | 33 => 117895
  | 34 => 117921
  | 35 => 117947
  | 36 => 117974
  | 37 => 118000
  | _ => 118000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 38 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 118000` (`log 118000 ≤ 12`, `2.7^12 ≥ 118000`). -/
theorem haC_118000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 118000 := by
  have hlog : Real.log 118000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 118000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 118000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[117000, 118000]` segment's band hypothesis: every band `i < 38` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 38 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 38 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[117000, 118000]` SEGMENT: every zero with `117000 ≤ Im ≤ 118000` is on the line. -/
theorem segment_117000_118000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 118000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (117000:ℝ) ≤ ρ.im → ρ.im ≤ 118000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 117000 118000 bndSeg 38 (by norm_num) bndSeg_mono rfl rfl haC_118000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 118000 via the HEIGHT CHAIN**: `[0,117000]` ∘ `[117000,118000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_118000_of_bands
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
    (hbands_99000 : AllZeros_h99000.BandHyp)
    (hbands_100000 : AllZeros_h100000.BandHyp)
    (hbands_101000 : AllZeros_h101000.BandHyp)
    (hbands_102000 : AllZeros_h102000.BandHyp)
    (hbands_103000 : AllZeros_h103000.BandHyp)
    (hbands_104000 : AllZeros_h104000.BandHyp)
    (hbands_105000 : AllZeros_h105000.BandHyp)
    (hbands_106000 : AllZeros_h106000.BandHyp)
    (hbands_107000 : AllZeros_h107000.BandHyp)
    (hbands_108000 : AllZeros_h108000.BandHyp)
    (hbands_109000 : AllZeros_h109000.BandHyp)
    (hbands_110000 : AllZeros_h110000.BandHyp)
    (hbands_111000 : AllZeros_h111000.BandHyp)
    (hbands_112000 : AllZeros_h112000.BandHyp)
    (hbands_113000 : AllZeros_h113000.BandHyp)
    (hbands_114000 : AllZeros_h114000.BandHyp)
    (hbands_115000 : AllZeros_h115000.BandHyp)
    (hbands_116000 : AllZeros_h116000.BandHyp)
    (hbands_117000 : AllZeros_h117000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 118000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 118000 → ρ.re = 1 / 2 := by
  have hγ117000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 117000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 117000 118000
    (AllZeros_h117000.all_nontrivial_zeros_up_to_height_117000_of_bands
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
      hbands_99000
      hbands_100000
      hbands_101000
      hbands_102000
      hbands_103000
      hbands_104000
      hbands_105000
      hbands_106000
      hbands_107000
      hbands_108000
      hbands_109000
      hbands_110000
      hbands_111000
      hbands_112000
      hbands_113000
      hbands_114000
      hbands_115000
      hbands_116000
      hbands_117000
      hγ117000)
    (segment_117000_118000 hbands hγ)

end AllZeros_h118000
