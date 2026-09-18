/-  Height-chain step: all nontrivial zeta zeros up to height 137000 on Re = 1/2 --
    `AllZeros_h136000` + a `[136000, 137000]` SEGMENT certificate (38 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h136000
import RHInBoxT_1d4000000_3999999d4000000_136000_136026
import RHInBoxT_1d4000000_3999999d4000000_136026_136053
import RHInBoxT_1d4000000_3999999d4000000_136053_136079
import RHInBoxT_1d4000000_3999999d4000000_544315d4_136105
import RHInBoxT_1d4000000_3999999d4000000_136105_544529d4
import RHInBoxT_1d4000000_3999999d4000000_136132_544633d4
import RHInBoxT_1d4000000_3999999d4000000_136158_136184
import RHInBoxT_1d4000000_3999999d4000000_136184_544845d4
import RHInBoxT_1d4000000_3999999d4000000_136211_136237
import RHInBoxT_1d4000000_3999999d4000000_136237_136263
import RHInBoxT_1d4000000_3999999d4000000_545051d4_136289
import RHInBoxT_1d4000000_3999999d4000000_136289_545265d4
import RHInBoxT_1d4000000_3999999d4000000_136316_136342
import RHInBoxT_1d4000000_3999999d4000000_136342_136368
import RHInBoxT_1d4000000_3999999d4000000_136368_136395
import RHInBoxT_1d4000000_3999999d4000000_136395_545685d4
import RHInBoxT_1d4000000_3999999d4000000_136421_136447
import RHInBoxT_1d4000000_3999999d4000000_136447_136474
import RHInBoxT_1d4000000_3999999d4000000_136474_136500
import RHInBoxT_1d4000000_3999999d4000000_136500_136526
import RHInBoxT_1d4000000_3999999d4000000_546103d4_136553
import RHInBoxT_1d4000000_3999999d4000000_136553_136579
import RHInBoxT_1d4000000_3999999d4000000_136579_136605
import RHInBoxT_1d4000000_3999999d4000000_136605_136632
import RHInBoxT_1d4000000_3999999d4000000_136632_546633d4
import RHInBoxT_1d4000000_3999999d4000000_136658_136684
import RHInBoxT_1d4000000_3999999d4000000_546735d4_136711
import RHInBoxT_1d4000000_3999999d4000000_136711_136737
import RHInBoxT_1d4000000_3999999d4000000_136737_136763
import RHInBoxT_1d4000000_3999999d4000000_136763_547157d4
import RHInBoxT_1d4000000_3999999d4000000_136789_136816
import RHInBoxT_1d4000000_3999999d4000000_136816_136842
import RHInBoxT_1d4000000_3999999d4000000_136842_136868
import RHInBoxT_1d4000000_3999999d4000000_136868_136895
import RHInBoxT_1d4000000_3999999d4000000_136895_547685d4
import RHInBoxT_1d4000000_3999999d4000000_136921_136947
import RHInBoxT_1d4000000_3999999d4000000_547787d4_136974
import RHInBoxT_1d4000000_3999999d4000000_136974_548001d4

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h137000

/-- The 38-band NOMINAL partition of `[136000, 137000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 136000
  | 1 => 136026
  | 2 => 136053
  | 3 => 136079
  | 4 => 136105
  | 5 => 136132
  | 6 => 136158
  | 7 => 136184
  | 8 => 136211
  | 9 => 136237
  | 10 => 136263
  | 11 => 136289
  | 12 => 136316
  | 13 => 136342
  | 14 => 136368
  | 15 => 136395
  | 16 => 136421
  | 17 => 136447
  | 18 => 136474
  | 19 => 136500
  | 20 => 136526
  | 21 => 136553
  | 22 => 136579
  | 23 => 136605
  | 24 => 136632
  | 25 => 136658
  | 26 => 136684
  | 27 => 136711
  | 28 => 136737
  | 29 => 136763
  | 30 => 136789
  | 31 => 136816
  | 32 => 136842
  | 33 => 136868
  | 34 => 136895
  | 35 => 136921
  | 36 => 136947
  | 37 => 136974
  | 38 => 137000
  | _ => 137000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((136000:ℝ)) ≤ (136026); norm_num
  · show ((136026:ℝ)) ≤ (136053); norm_num
  · show ((136053:ℝ)) ≤ (136079); norm_num
  · show ((136079:ℝ)) ≤ (136105); norm_num
  · show ((136105:ℝ)) ≤ (136132); norm_num
  · show ((136132:ℝ)) ≤ (136158); norm_num
  · show ((136158:ℝ)) ≤ (136184); norm_num
  · show ((136184:ℝ)) ≤ (136211); norm_num
  · show ((136211:ℝ)) ≤ (136237); norm_num
  · show ((136237:ℝ)) ≤ (136263); norm_num
  · show ((136263:ℝ)) ≤ (136289); norm_num
  · show ((136289:ℝ)) ≤ (136316); norm_num
  · show ((136316:ℝ)) ≤ (136342); norm_num
  · show ((136342:ℝ)) ≤ (136368); norm_num
  · show ((136368:ℝ)) ≤ (136395); norm_num
  · show ((136395:ℝ)) ≤ (136421); norm_num
  · show ((136421:ℝ)) ≤ (136447); norm_num
  · show ((136447:ℝ)) ≤ (136474); norm_num
  · show ((136474:ℝ)) ≤ (136500); norm_num
  · show ((136500:ℝ)) ≤ (136526); norm_num
  · show ((136526:ℝ)) ≤ (136553); norm_num
  · show ((136553:ℝ)) ≤ (136579); norm_num
  · show ((136579:ℝ)) ≤ (136605); norm_num
  · show ((136605:ℝ)) ≤ (136632); norm_num
  · show ((136632:ℝ)) ≤ (136658); norm_num
  · show ((136658:ℝ)) ≤ (136684); norm_num
  · show ((136684:ℝ)) ≤ (136711); norm_num
  · show ((136711:ℝ)) ≤ (136737); norm_num
  · show ((136737:ℝ)) ≤ (136763); norm_num
  · show ((136763:ℝ)) ≤ (136789); norm_num
  · show ((136789:ℝ)) ≤ (136816); norm_num
  · show ((136816:ℝ)) ≤ (136842); norm_num
  · show ((136842:ℝ)) ≤ (136868); norm_num
  · show ((136868:ℝ)) ≤ (136895); norm_num
  · show ((136895:ℝ)) ≤ (136921); norm_num
  · show ((136921:ℝ)) ≤ (136947); norm_num
  · show ((136947:ℝ)) ≤ (136974); norm_num
  · show ((136974:ℝ)) ≤ (137000); norm_num
  · show ((137000:ℝ)) ≤ (137000); norm_num
  · exact le_refl _

/-- The lower edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 136000
  | 1 => 136026
  | 2 => 136053
  | 3 => 544315 / 4
  | 4 => 136105
  | 5 => 136132
  | 6 => 136158
  | 7 => 136184
  | 8 => 136211
  | 9 => 136237
  | 10 => 545051 / 4
  | 11 => 136289
  | 12 => 136316
  | 13 => 136342
  | 14 => 136368
  | 15 => 136395
  | 16 => 136421
  | 17 => 136447
  | 18 => 136474
  | 19 => 136500
  | 20 => 546103 / 4
  | 21 => 136553
  | 22 => 136579
  | 23 => 136605
  | 24 => 136632
  | 25 => 136658
  | 26 => 546735 / 4
  | 27 => 136711
  | 28 => 136737
  | 29 => 136763
  | 30 => 136789
  | 31 => 136816
  | 32 => 136842
  | 33 => 136868
  | 34 => 136895
  | 35 => 136921
  | 36 => 547787 / 4
  | 37 => 136974
  | _ => 136974

/-- The upper edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 136026
  | 1 => 136053
  | 2 => 136079
  | 3 => 136105
  | 4 => 544529 / 4
  | 5 => 544633 / 4
  | 6 => 136184
  | 7 => 544845 / 4
  | 8 => 136237
  | 9 => 136263
  | 10 => 136289
  | 11 => 545265 / 4
  | 12 => 136342
  | 13 => 136368
  | 14 => 136395
  | 15 => 545685 / 4
  | 16 => 136447
  | 17 => 136474
  | 18 => 136500
  | 19 => 136526
  | 20 => 136553
  | 21 => 136579
  | 22 => 136605
  | 23 => 136632
  | 24 => 546633 / 4
  | 25 => 136684
  | 26 => 136711
  | 27 => 136737
  | 28 => 136763
  | 29 => 547157 / 4
  | 30 => 136816
  | 31 => 136842
  | 32 => 136868
  | 33 => 136895
  | 34 => 547685 / 4
  | 35 => 136947
  | 36 => 136974
  | 37 => 548001 / 4
  | _ => 548001 / 4

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 38 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 137000` (`log 137000 ≤ 12`, `2.7^12 ≥ 137000`). -/
theorem haC_137000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 137000 := by
  have hlog : Real.log 137000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 137000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 137000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[136000, 137000]` segment's band hypothesis: every band `i < 38` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 38 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 38 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[136000, 137000]` SEGMENT: every zero with `136000 ≤ Im ≤ 137000` is on the line. -/
theorem segment_136000_137000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 137000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (136000:ℝ) ≤ ρ.im → ρ.im ≤ 137000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 136000 137000 bndSeg 38 (by norm_num) bndSeg_mono rfl rfl haC_137000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 137000 via the HEIGHT CHAIN**: `[0,136000]` ∘ `[136000,137000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_137000_of_bands
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
    (hbands_134000 : AllZeros_h134000.BandHyp)
    (hbands_135000 : AllZeros_h135000.BandHyp)
    (hbands_136000 : AllZeros_h136000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 137000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 137000 → ρ.re = 1 / 2 := by
  have hγ136000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 136000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 136000 137000
    (AllZeros_h136000.all_nontrivial_zeros_up_to_height_136000_of_bands
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
      hbands_134000
      hbands_135000
      hbands_136000
      hγ136000)
    (segment_136000_137000 hbands hγ)

end AllZeros_h137000
