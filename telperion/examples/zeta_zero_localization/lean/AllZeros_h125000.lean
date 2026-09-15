/-  Height-chain step: all nontrivial zeta zeros up to height 125000 on Re = 1/2 --
    `AllZeros_h124000` + a `[124000, 125000]` SEGMENT certificate (38 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h124000
import RHInBoxT_1d4000000_3999999d4000000_124000_124026
import RHInBoxT_1d4000000_3999999d4000000_124026_124053
import RHInBoxT_1d4000000_3999999d4000000_124053_124079
import RHInBoxT_1d4000000_3999999d4000000_124079_124105
import RHInBoxT_1d4000000_3999999d4000000_496419d4_124132
import RHInBoxT_1d4000000_3999999d4000000_124132_124158
import RHInBoxT_1d4000000_3999999d4000000_124158_124184
import RHInBoxT_1d4000000_3999999d4000000_124184_124211
import RHInBoxT_1d4000000_3999999d4000000_124211_124237
import RHInBoxT_1d4000000_3999999d4000000_124237_124263
import RHInBoxT_1d4000000_3999999d4000000_497051d4_124289
import RHInBoxT_1d4000000_3999999d4000000_124289_124316
import RHInBoxT_1d4000000_3999999d4000000_497263d4_124342
import RHInBoxT_1d4000000_3999999d4000000_497367d4_124368
import RHInBoxT_1d4000000_3999999d4000000_124368_124395
import RHInBoxT_1d4000000_3999999d4000000_124395_497685d4
import RHInBoxT_1d4000000_3999999d4000000_124421_124447
import RHInBoxT_1d4000000_3999999d4000000_124447_124474
import RHInBoxT_1d4000000_3999999d4000000_497895d4_124500
import RHInBoxT_1d4000000_3999999d4000000_124500_124526
import RHInBoxT_1d4000000_3999999d4000000_124526_124553
import RHInBoxT_1d4000000_3999999d4000000_124553_124579
import RHInBoxT_1d4000000_3999999d4000000_498315d4_498421d4
import RHInBoxT_1d4000000_3999999d4000000_124605_124632
import RHInBoxT_1d4000000_3999999d4000000_124632_124658
import RHInBoxT_1d4000000_3999999d4000000_124658_124684
import RHInBoxT_1d4000000_3999999d4000000_124684_124711
import RHInBoxT_1d4000000_3999999d4000000_124711_124737
import RHInBoxT_1d4000000_3999999d4000000_124737_124763
import RHInBoxT_1d4000000_3999999d4000000_124763_124789
import RHInBoxT_1d4000000_3999999d4000000_124789_124816
import RHInBoxT_1d4000000_3999999d4000000_124816_124842
import RHInBoxT_1d4000000_3999999d4000000_124842_124868
import RHInBoxT_1d4000000_3999999d4000000_499471d4_499581d4
import RHInBoxT_1d4000000_3999999d4000000_124895_499685d4
import RHInBoxT_1d4000000_3999999d4000000_124921_124947
import RHInBoxT_1d4000000_3999999d4000000_124947_124974
import RHInBoxT_1d4000000_3999999d4000000_124974_125000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h125000

/-- The 38-band NOMINAL partition of `[124000, 125000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 124000
  | 1 => 124026
  | 2 => 124053
  | 3 => 124079
  | 4 => 124105
  | 5 => 124132
  | 6 => 124158
  | 7 => 124184
  | 8 => 124211
  | 9 => 124237
  | 10 => 124263
  | 11 => 124289
  | 12 => 124316
  | 13 => 124342
  | 14 => 124368
  | 15 => 124395
  | 16 => 124421
  | 17 => 124447
  | 18 => 124474
  | 19 => 124500
  | 20 => 124526
  | 21 => 124553
  | 22 => 124579
  | 23 => 124605
  | 24 => 124632
  | 25 => 124658
  | 26 => 124684
  | 27 => 124711
  | 28 => 124737
  | 29 => 124763
  | 30 => 124789
  | 31 => 124816
  | 32 => 124842
  | 33 => 124868
  | 34 => 124895
  | 35 => 124921
  | 36 => 124947
  | 37 => 124974
  | 38 => 125000
  | _ => 125000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((124000:ℝ)) ≤ (124026); norm_num
  · show ((124026:ℝ)) ≤ (124053); norm_num
  · show ((124053:ℝ)) ≤ (124079); norm_num
  · show ((124079:ℝ)) ≤ (124105); norm_num
  · show ((124105:ℝ)) ≤ (124132); norm_num
  · show ((124132:ℝ)) ≤ (124158); norm_num
  · show ((124158:ℝ)) ≤ (124184); norm_num
  · show ((124184:ℝ)) ≤ (124211); norm_num
  · show ((124211:ℝ)) ≤ (124237); norm_num
  · show ((124237:ℝ)) ≤ (124263); norm_num
  · show ((124263:ℝ)) ≤ (124289); norm_num
  · show ((124289:ℝ)) ≤ (124316); norm_num
  · show ((124316:ℝ)) ≤ (124342); norm_num
  · show ((124342:ℝ)) ≤ (124368); norm_num
  · show ((124368:ℝ)) ≤ (124395); norm_num
  · show ((124395:ℝ)) ≤ (124421); norm_num
  · show ((124421:ℝ)) ≤ (124447); norm_num
  · show ((124447:ℝ)) ≤ (124474); norm_num
  · show ((124474:ℝ)) ≤ (124500); norm_num
  · show ((124500:ℝ)) ≤ (124526); norm_num
  · show ((124526:ℝ)) ≤ (124553); norm_num
  · show ((124553:ℝ)) ≤ (124579); norm_num
  · show ((124579:ℝ)) ≤ (124605); norm_num
  · show ((124605:ℝ)) ≤ (124632); norm_num
  · show ((124632:ℝ)) ≤ (124658); norm_num
  · show ((124658:ℝ)) ≤ (124684); norm_num
  · show ((124684:ℝ)) ≤ (124711); norm_num
  · show ((124711:ℝ)) ≤ (124737); norm_num
  · show ((124737:ℝ)) ≤ (124763); norm_num
  · show ((124763:ℝ)) ≤ (124789); norm_num
  · show ((124789:ℝ)) ≤ (124816); norm_num
  · show ((124816:ℝ)) ≤ (124842); norm_num
  · show ((124842:ℝ)) ≤ (124868); norm_num
  · show ((124868:ℝ)) ≤ (124895); norm_num
  · show ((124895:ℝ)) ≤ (124921); norm_num
  · show ((124921:ℝ)) ≤ (124947); norm_num
  · show ((124947:ℝ)) ≤ (124974); norm_num
  · show ((124974:ℝ)) ≤ (125000); norm_num
  · show ((125000:ℝ)) ≤ (125000); norm_num
  · exact le_refl _

/-- The lower edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 124000
  | 1 => 124026
  | 2 => 124053
  | 3 => 124079
  | 4 => 496419 / 4
  | 5 => 124132
  | 6 => 124158
  | 7 => 124184
  | 8 => 124211
  | 9 => 124237
  | 10 => 497051 / 4
  | 11 => 124289
  | 12 => 497263 / 4
  | 13 => 497367 / 4
  | 14 => 124368
  | 15 => 124395
  | 16 => 124421
  | 17 => 124447
  | 18 => 497895 / 4
  | 19 => 124500
  | 20 => 124526
  | 21 => 124553
  | 22 => 498315 / 4
  | 23 => 124605
  | 24 => 124632
  | 25 => 124658
  | 26 => 124684
  | 27 => 124711
  | 28 => 124737
  | 29 => 124763
  | 30 => 124789
  | 31 => 124816
  | 32 => 124842
  | 33 => 499471 / 4
  | 34 => 124895
  | 35 => 124921
  | 36 => 124947
  | 37 => 124974
  | _ => 124974

/-- The upper edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 124026
  | 1 => 124053
  | 2 => 124079
  | 3 => 124105
  | 4 => 124132
  | 5 => 124158
  | 6 => 124184
  | 7 => 124211
  | 8 => 124237
  | 9 => 124263
  | 10 => 124289
  | 11 => 124316
  | 12 => 124342
  | 13 => 124368
  | 14 => 124395
  | 15 => 497685 / 4
  | 16 => 124447
  | 17 => 124474
  | 18 => 124500
  | 19 => 124526
  | 20 => 124553
  | 21 => 124579
  | 22 => 498421 / 4
  | 23 => 124632
  | 24 => 124658
  | 25 => 124684
  | 26 => 124711
  | 27 => 124737
  | 28 => 124763
  | 29 => 124789
  | 30 => 124816
  | 31 => 124842
  | 32 => 124868
  | 33 => 499581 / 4
  | 34 => 499685 / 4
  | 35 => 124947
  | 36 => 124974
  | 37 => 125000
  | _ => 125000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 38 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 125000` (`log 125000 ≤ 12`, `2.7^12 ≥ 125000`). -/
theorem haC_125000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 125000 := by
  have hlog : Real.log 125000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 125000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 125000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[124000, 125000]` segment's band hypothesis: every band `i < 38` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 38 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 38 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[124000, 125000]` SEGMENT: every zero with `124000 ≤ Im ≤ 125000` is on the line. -/
theorem segment_124000_125000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 125000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (124000:ℝ) ≤ ρ.im → ρ.im ≤ 125000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 124000 125000 bndSeg 38 (by norm_num) bndSeg_mono rfl rfl haC_125000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 125000 via the HEIGHT CHAIN**: `[0,124000]` ∘ `[124000,125000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_125000_of_bands
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
    (hbands_118000 : AllZeros_h118000.BandHyp)
    (hbands_119000 : AllZeros_h119000.BandHyp)
    (hbands_120000 : AllZeros_h120000.BandHyp)
    (hbands_121000 : AllZeros_h121000.BandHyp)
    (hbands_122000 : AllZeros_h122000.BandHyp)
    (hbands_123000 : AllZeros_h123000.BandHyp)
    (hbands_124000 : AllZeros_h124000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 125000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 125000 → ρ.re = 1 / 2 := by
  have hγ124000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 124000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 124000 125000
    (AllZeros_h124000.all_nontrivial_zeros_up_to_height_124000_of_bands
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
      hbands_118000
      hbands_119000
      hbands_120000
      hbands_121000
      hbands_122000
      hbands_123000
      hbands_124000
      hγ124000)
    (segment_124000_125000 hbands hγ)

end AllZeros_h125000
