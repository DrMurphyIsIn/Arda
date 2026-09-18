/-  Height-chain step: all nontrivial zeta zeros up to height 134000 on Re = 1/2 --
    `AllZeros_h133000` + a `[133000, 134000]` SEGMENT certificate (38 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h133000
import RHInBoxT_1d4000000_3999999d4000000_531999d4_532105d4
import RHInBoxT_1d4000000_3999999d4000000_133026_133053
import RHInBoxT_1d4000000_3999999d4000000_133053_133079
import RHInBoxT_1d4000000_3999999d4000000_133079_133105
import RHInBoxT_1d4000000_3999999d4000000_532419d4_133132
import RHInBoxT_1d4000000_3999999d4000000_133132_532633d4
import RHInBoxT_1d4000000_3999999d4000000_133158_133184
import RHInBoxT_1d4000000_3999999d4000000_133184_133211
import RHInBoxT_1d4000000_3999999d4000000_133211_133237
import RHInBoxT_1d4000000_3999999d4000000_133237_133263
import RHInBoxT_1d4000000_3999999d4000000_133263_133289
import RHInBoxT_1d4000000_3999999d4000000_533155d4_133316
import RHInBoxT_1d4000000_3999999d4000000_133316_133342
import RHInBoxT_1d4000000_3999999d4000000_133342_133368
import RHInBoxT_1d4000000_3999999d4000000_533471d4_133395
import RHInBoxT_1d4000000_3999999d4000000_133395_133421
import RHInBoxT_1d4000000_3999999d4000000_133421_133447
import RHInBoxT_1d4000000_3999999d4000000_133447_133474
import RHInBoxT_1d4000000_3999999d4000000_133474_133500
import RHInBoxT_1d4000000_3999999d4000000_133500_534105d4
import RHInBoxT_1d4000000_3999999d4000000_133526_534213d4
import RHInBoxT_1d4000000_3999999d4000000_133553_133579
import RHInBoxT_1d4000000_3999999d4000000_133579_133605
import RHInBoxT_1d4000000_3999999d4000000_133605_133632
import RHInBoxT_1d4000000_3999999d4000000_133632_133658
import RHInBoxT_1d4000000_3999999d4000000_133658_133684
import RHInBoxT_1d4000000_3999999d4000000_133684_133711
import RHInBoxT_1d4000000_3999999d4000000_133711_133737
import RHInBoxT_1d4000000_3999999d4000000_534947d4_133763
import RHInBoxT_1d4000000_3999999d4000000_133763_133789
import RHInBoxT_1d4000000_3999999d4000000_535155d4_133816
import RHInBoxT_1d4000000_3999999d4000000_133816_133842
import RHInBoxT_1d4000000_3999999d4000000_133842_133868
import RHInBoxT_1d4000000_3999999d4000000_133868_133895
import RHInBoxT_1d4000000_3999999d4000000_133895_535685d4
import RHInBoxT_1d4000000_3999999d4000000_133921_535789d4
import RHInBoxT_1d4000000_3999999d4000000_133947_133974
import RHInBoxT_1d4000000_3999999d4000000_133974_134000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h134000

/-- The 38-band NOMINAL partition of `[133000, 134000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 133000
  | 1 => 133026
  | 2 => 133053
  | 3 => 133079
  | 4 => 133105
  | 5 => 133132
  | 6 => 133158
  | 7 => 133184
  | 8 => 133211
  | 9 => 133237
  | 10 => 133263
  | 11 => 133289
  | 12 => 133316
  | 13 => 133342
  | 14 => 133368
  | 15 => 133395
  | 16 => 133421
  | 17 => 133447
  | 18 => 133474
  | 19 => 133500
  | 20 => 133526
  | 21 => 133553
  | 22 => 133579
  | 23 => 133605
  | 24 => 133632
  | 25 => 133658
  | 26 => 133684
  | 27 => 133711
  | 28 => 133737
  | 29 => 133763
  | 30 => 133789
  | 31 => 133816
  | 32 => 133842
  | 33 => 133868
  | 34 => 133895
  | 35 => 133921
  | 36 => 133947
  | 37 => 133974
  | 38 => 134000
  | _ => 134000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((133000:ℝ)) ≤ (133026); norm_num
  · show ((133026:ℝ)) ≤ (133053); norm_num
  · show ((133053:ℝ)) ≤ (133079); norm_num
  · show ((133079:ℝ)) ≤ (133105); norm_num
  · show ((133105:ℝ)) ≤ (133132); norm_num
  · show ((133132:ℝ)) ≤ (133158); norm_num
  · show ((133158:ℝ)) ≤ (133184); norm_num
  · show ((133184:ℝ)) ≤ (133211); norm_num
  · show ((133211:ℝ)) ≤ (133237); norm_num
  · show ((133237:ℝ)) ≤ (133263); norm_num
  · show ((133263:ℝ)) ≤ (133289); norm_num
  · show ((133289:ℝ)) ≤ (133316); norm_num
  · show ((133316:ℝ)) ≤ (133342); norm_num
  · show ((133342:ℝ)) ≤ (133368); norm_num
  · show ((133368:ℝ)) ≤ (133395); norm_num
  · show ((133395:ℝ)) ≤ (133421); norm_num
  · show ((133421:ℝ)) ≤ (133447); norm_num
  · show ((133447:ℝ)) ≤ (133474); norm_num
  · show ((133474:ℝ)) ≤ (133500); norm_num
  · show ((133500:ℝ)) ≤ (133526); norm_num
  · show ((133526:ℝ)) ≤ (133553); norm_num
  · show ((133553:ℝ)) ≤ (133579); norm_num
  · show ((133579:ℝ)) ≤ (133605); norm_num
  · show ((133605:ℝ)) ≤ (133632); norm_num
  · show ((133632:ℝ)) ≤ (133658); norm_num
  · show ((133658:ℝ)) ≤ (133684); norm_num
  · show ((133684:ℝ)) ≤ (133711); norm_num
  · show ((133711:ℝ)) ≤ (133737); norm_num
  · show ((133737:ℝ)) ≤ (133763); norm_num
  · show ((133763:ℝ)) ≤ (133789); norm_num
  · show ((133789:ℝ)) ≤ (133816); norm_num
  · show ((133816:ℝ)) ≤ (133842); norm_num
  · show ((133842:ℝ)) ≤ (133868); norm_num
  · show ((133868:ℝ)) ≤ (133895); norm_num
  · show ((133895:ℝ)) ≤ (133921); norm_num
  · show ((133921:ℝ)) ≤ (133947); norm_num
  · show ((133947:ℝ)) ≤ (133974); norm_num
  · show ((133974:ℝ)) ≤ (134000); norm_num
  · show ((134000:ℝ)) ≤ (134000); norm_num
  · exact le_refl _

/-- The lower edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 531999 / 4
  | 1 => 133026
  | 2 => 133053
  | 3 => 133079
  | 4 => 532419 / 4
  | 5 => 133132
  | 6 => 133158
  | 7 => 133184
  | 8 => 133211
  | 9 => 133237
  | 10 => 133263
  | 11 => 533155 / 4
  | 12 => 133316
  | 13 => 133342
  | 14 => 533471 / 4
  | 15 => 133395
  | 16 => 133421
  | 17 => 133447
  | 18 => 133474
  | 19 => 133500
  | 20 => 133526
  | 21 => 133553
  | 22 => 133579
  | 23 => 133605
  | 24 => 133632
  | 25 => 133658
  | 26 => 133684
  | 27 => 133711
  | 28 => 534947 / 4
  | 29 => 133763
  | 30 => 535155 / 4
  | 31 => 133816
  | 32 => 133842
  | 33 => 133868
  | 34 => 133895
  | 35 => 133921
  | 36 => 133947
  | 37 => 133974
  | _ => 133974

/-- The upper edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 532105 / 4
  | 1 => 133053
  | 2 => 133079
  | 3 => 133105
  | 4 => 133132
  | 5 => 532633 / 4
  | 6 => 133184
  | 7 => 133211
  | 8 => 133237
  | 9 => 133263
  | 10 => 133289
  | 11 => 133316
  | 12 => 133342
  | 13 => 133368
  | 14 => 133395
  | 15 => 133421
  | 16 => 133447
  | 17 => 133474
  | 18 => 133500
  | 19 => 534105 / 4
  | 20 => 534213 / 4
  | 21 => 133579
  | 22 => 133605
  | 23 => 133632
  | 24 => 133658
  | 25 => 133684
  | 26 => 133711
  | 27 => 133737
  | 28 => 133763
  | 29 => 133789
  | 30 => 133816
  | 31 => 133842
  | 32 => 133868
  | 33 => 133895
  | 34 => 535685 / 4
  | 35 => 535789 / 4
  | 36 => 133974
  | 37 => 134000
  | _ => 134000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 38 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 134000` (`log 134000 ≤ 12`, `2.7^12 ≥ 134000`). -/
theorem haC_134000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 134000 := by
  have hlog : Real.log 134000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 134000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 134000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[133000, 134000]` segment's band hypothesis: every band `i < 38` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 38 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 38 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[133000, 134000]` SEGMENT: every zero with `133000 ≤ Im ≤ 134000` is on the line. -/
theorem segment_133000_134000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 134000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (133000:ℝ) ≤ ρ.im → ρ.im ≤ 134000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 133000 134000 bndSeg 38 (by norm_num) bndSeg_mono rfl rfl haC_134000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 134000 via the HEIGHT CHAIN**: `[0,133000]` ∘ `[133000,134000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_134000_of_bands
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
    (hbands_125000 : AllZeros_h125000.BandHyp)
    (hbands_126000 : AllZeros_h126000.BandHyp)
    (hbands_127000 : AllZeros_h127000.BandHyp)
    (hbands_128000 : AllZeros_h128000.BandHyp)
    (hbands_129000 : AllZeros_h129000.BandHyp)
    (hbands_130000 : AllZeros_h130000.BandHyp)
    (hbands_131000 : AllZeros_h131000.BandHyp)
    (hbands_132000 : AllZeros_h132000.BandHyp)
    (hbands_133000 : AllZeros_h133000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 134000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 134000 → ρ.re = 1 / 2 := by
  have hγ133000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 133000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 133000 134000
    (AllZeros_h133000.all_nontrivial_zeros_up_to_height_133000_of_bands
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
      hbands_125000
      hbands_126000
      hbands_127000
      hbands_128000
      hbands_129000
      hbands_130000
      hbands_131000
      hbands_132000
      hbands_133000
      hγ133000)
    (segment_133000_134000 hbands hγ)

end AllZeros_h134000
