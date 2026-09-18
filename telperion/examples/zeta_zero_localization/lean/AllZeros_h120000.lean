/-  Height-chain step: all nontrivial zeta zeros up to height 120000 on Re = 1/2 --
    `AllZeros_h119000` + a `[119000, 120000]` SEGMENT certificate (38 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h119000
import RHInBoxT_1d4000000_3999999d4000000_119000_119026
import RHInBoxT_1d4000000_3999999d4000000_119026_119053
import RHInBoxT_1d4000000_3999999d4000000_119053_119079
import RHInBoxT_1d4000000_3999999d4000000_119079_119105
import RHInBoxT_1d4000000_3999999d4000000_119105_119132
import RHInBoxT_1d4000000_3999999d4000000_119132_476633d4
import RHInBoxT_1d4000000_3999999d4000000_119158_119184
import RHInBoxT_1d4000000_3999999d4000000_119184_119211
import RHInBoxT_1d4000000_3999999d4000000_119211_119237
import RHInBoxT_1d4000000_3999999d4000000_119237_119263
import RHInBoxT_1d4000000_3999999d4000000_119263_119289
import RHInBoxT_1d4000000_3999999d4000000_119289_119316
import RHInBoxT_1d4000000_3999999d4000000_477263d4_119342
import RHInBoxT_1d4000000_3999999d4000000_119342_477473d4
import RHInBoxT_1d4000000_3999999d4000000_119368_477581d4
import RHInBoxT_1d4000000_3999999d4000000_119395_119421
import RHInBoxT_1d4000000_3999999d4000000_119421_119447
import RHInBoxT_1d4000000_3999999d4000000_119447_119474
import RHInBoxT_1d4000000_3999999d4000000_119474_119500
import RHInBoxT_1d4000000_3999999d4000000_119500_119526
import RHInBoxT_1d4000000_3999999d4000000_119526_119553
import RHInBoxT_1d4000000_3999999d4000000_478211d4_119579
import RHInBoxT_1d4000000_3999999d4000000_119579_478421d4
import RHInBoxT_1d4000000_3999999d4000000_478419d4_119632
import RHInBoxT_1d4000000_3999999d4000000_119632_119658
import RHInBoxT_1d4000000_3999999d4000000_119658_478737d4
import RHInBoxT_1d4000000_3999999d4000000_119684_119711
import RHInBoxT_1d4000000_3999999d4000000_119711_119737
import RHInBoxT_1d4000000_3999999d4000000_119737_119763
import RHInBoxT_1d4000000_3999999d4000000_119763_479157d4
import RHInBoxT_1d4000000_3999999d4000000_119789_119816
import RHInBoxT_1d4000000_3999999d4000000_119816_479369d4
import RHInBoxT_1d4000000_3999999d4000000_119842_119868
import RHInBoxT_1d4000000_3999999d4000000_119868_119895
import RHInBoxT_1d4000000_3999999d4000000_119895_119921
import RHInBoxT_1d4000000_3999999d4000000_119921_119947
import RHInBoxT_1d4000000_3999999d4000000_119947_119974
import RHInBoxT_1d4000000_3999999d4000000_479895d4_120000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h120000

/-- The 38-band NOMINAL partition of `[119000, 120000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 119000
  | 1 => 119026
  | 2 => 119053
  | 3 => 119079
  | 4 => 119105
  | 5 => 119132
  | 6 => 119158
  | 7 => 119184
  | 8 => 119211
  | 9 => 119237
  | 10 => 119263
  | 11 => 119289
  | 12 => 119316
  | 13 => 119342
  | 14 => 119368
  | 15 => 119395
  | 16 => 119421
  | 17 => 119447
  | 18 => 119474
  | 19 => 119500
  | 20 => 119526
  | 21 => 119553
  | 22 => 119579
  | 23 => 119605
  | 24 => 119632
  | 25 => 119658
  | 26 => 119684
  | 27 => 119711
  | 28 => 119737
  | 29 => 119763
  | 30 => 119789
  | 31 => 119816
  | 32 => 119842
  | 33 => 119868
  | 34 => 119895
  | 35 => 119921
  | 36 => 119947
  | 37 => 119974
  | 38 => 120000
  | _ => 120000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((119000:ℝ)) ≤ (119026); norm_num
  · show ((119026:ℝ)) ≤ (119053); norm_num
  · show ((119053:ℝ)) ≤ (119079); norm_num
  · show ((119079:ℝ)) ≤ (119105); norm_num
  · show ((119105:ℝ)) ≤ (119132); norm_num
  · show ((119132:ℝ)) ≤ (119158); norm_num
  · show ((119158:ℝ)) ≤ (119184); norm_num
  · show ((119184:ℝ)) ≤ (119211); norm_num
  · show ((119211:ℝ)) ≤ (119237); norm_num
  · show ((119237:ℝ)) ≤ (119263); norm_num
  · show ((119263:ℝ)) ≤ (119289); norm_num
  · show ((119289:ℝ)) ≤ (119316); norm_num
  · show ((119316:ℝ)) ≤ (119342); norm_num
  · show ((119342:ℝ)) ≤ (119368); norm_num
  · show ((119368:ℝ)) ≤ (119395); norm_num
  · show ((119395:ℝ)) ≤ (119421); norm_num
  · show ((119421:ℝ)) ≤ (119447); norm_num
  · show ((119447:ℝ)) ≤ (119474); norm_num
  · show ((119474:ℝ)) ≤ (119500); norm_num
  · show ((119500:ℝ)) ≤ (119526); norm_num
  · show ((119526:ℝ)) ≤ (119553); norm_num
  · show ((119553:ℝ)) ≤ (119579); norm_num
  · show ((119579:ℝ)) ≤ (119605); norm_num
  · show ((119605:ℝ)) ≤ (119632); norm_num
  · show ((119632:ℝ)) ≤ (119658); norm_num
  · show ((119658:ℝ)) ≤ (119684); norm_num
  · show ((119684:ℝ)) ≤ (119711); norm_num
  · show ((119711:ℝ)) ≤ (119737); norm_num
  · show ((119737:ℝ)) ≤ (119763); norm_num
  · show ((119763:ℝ)) ≤ (119789); norm_num
  · show ((119789:ℝ)) ≤ (119816); norm_num
  · show ((119816:ℝ)) ≤ (119842); norm_num
  · show ((119842:ℝ)) ≤ (119868); norm_num
  · show ((119868:ℝ)) ≤ (119895); norm_num
  · show ((119895:ℝ)) ≤ (119921); norm_num
  · show ((119921:ℝ)) ≤ (119947); norm_num
  · show ((119947:ℝ)) ≤ (119974); norm_num
  · show ((119974:ℝ)) ≤ (120000); norm_num
  · show ((120000:ℝ)) ≤ (120000); norm_num
  · exact le_refl _

/-- The lower edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 119000
  | 1 => 119026
  | 2 => 119053
  | 3 => 119079
  | 4 => 119105
  | 5 => 119132
  | 6 => 119158
  | 7 => 119184
  | 8 => 119211
  | 9 => 119237
  | 10 => 119263
  | 11 => 119289
  | 12 => 477263 / 4
  | 13 => 119342
  | 14 => 119368
  | 15 => 119395
  | 16 => 119421
  | 17 => 119447
  | 18 => 119474
  | 19 => 119500
  | 20 => 119526
  | 21 => 478211 / 4
  | 22 => 119579
  | 23 => 478419 / 4
  | 24 => 119632
  | 25 => 119658
  | 26 => 119684
  | 27 => 119711
  | 28 => 119737
  | 29 => 119763
  | 30 => 119789
  | 31 => 119816
  | 32 => 119842
  | 33 => 119868
  | 34 => 119895
  | 35 => 119921
  | 36 => 119947
  | 37 => 479895 / 4
  | _ => 479895 / 4

/-- The upper edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 119026
  | 1 => 119053
  | 2 => 119079
  | 3 => 119105
  | 4 => 119132
  | 5 => 476633 / 4
  | 6 => 119184
  | 7 => 119211
  | 8 => 119237
  | 9 => 119263
  | 10 => 119289
  | 11 => 119316
  | 12 => 119342
  | 13 => 477473 / 4
  | 14 => 477581 / 4
  | 15 => 119421
  | 16 => 119447
  | 17 => 119474
  | 18 => 119500
  | 19 => 119526
  | 20 => 119553
  | 21 => 119579
  | 22 => 478421 / 4
  | 23 => 119632
  | 24 => 119658
  | 25 => 478737 / 4
  | 26 => 119711
  | 27 => 119737
  | 28 => 119763
  | 29 => 479157 / 4
  | 30 => 119816
  | 31 => 479369 / 4
  | 32 => 119868
  | 33 => 119895
  | 34 => 119921
  | 35 => 119947
  | 36 => 119974
  | 37 => 120000
  | _ => 120000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 38 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 120000` (`log 120000 ≤ 12`, `2.7^12 ≥ 120000`). -/
theorem haC_120000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 120000 := by
  have hlog : Real.log 120000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 120000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 120000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[119000, 120000]` segment's band hypothesis: every band `i < 38` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 38 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 38 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[119000, 120000]` SEGMENT: every zero with `119000 ≤ Im ≤ 120000` is on the line. -/
theorem segment_119000_120000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 120000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (119000:ℝ) ≤ ρ.im → ρ.im ≤ 120000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 119000 120000 bndSeg 38 (by norm_num) bndSeg_mono rfl rfl haC_120000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 120000 via the HEIGHT CHAIN**: `[0,119000]` ∘ `[119000,120000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_120000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 120000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 120000 → ρ.re = 1 / 2 := by
  have hγ119000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 119000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 119000 120000
    (AllZeros_h119000.all_nontrivial_zeros_up_to_height_119000_of_bands
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
      hγ119000)
    (segment_119000_120000 hbands hγ)

end AllZeros_h120000
