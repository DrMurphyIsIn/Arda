/-  Height-chain step: all nontrivial zeta zeros up to height 111000 on Re = 1/2 --
    `AllZeros_h110000` + a `[110000, 111000]` SEGMENT certificate (38 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h110000
import RHInBoxT_1d4000000_3999999d4000000_110000_110026
import RHInBoxT_1d4000000_3999999d4000000_110026_440213d4
import RHInBoxT_1d4000000_3999999d4000000_110053_110079
import RHInBoxT_1d4000000_3999999d4000000_110079_110105
import RHInBoxT_1d4000000_3999999d4000000_110105_110132
import RHInBoxT_1d4000000_3999999d4000000_110132_110158
import RHInBoxT_1d4000000_3999999d4000000_110158_110184
import RHInBoxT_1d4000000_3999999d4000000_110184_110211
import RHInBoxT_1d4000000_3999999d4000000_110211_110237
import RHInBoxT_1d4000000_3999999d4000000_110237_110263
import RHInBoxT_1d4000000_3999999d4000000_110263_441157d4
import RHInBoxT_1d4000000_3999999d4000000_110289_110316
import RHInBoxT_1d4000000_3999999d4000000_110316_110342
import RHInBoxT_1d4000000_3999999d4000000_110342_110368
import RHInBoxT_1d4000000_3999999d4000000_110368_110395
import RHInBoxT_1d4000000_3999999d4000000_441579d4_110421
import RHInBoxT_1d4000000_3999999d4000000_110421_110447
import RHInBoxT_1d4000000_3999999d4000000_110447_110474
import RHInBoxT_1d4000000_3999999d4000000_110474_110500
import RHInBoxT_1d4000000_3999999d4000000_110500_110526
import RHInBoxT_1d4000000_3999999d4000000_110526_110553
import RHInBoxT_1d4000000_3999999d4000000_442211d4_110579
import RHInBoxT_1d4000000_3999999d4000000_110579_110605
import RHInBoxT_1d4000000_3999999d4000000_110605_442529d4
import RHInBoxT_1d4000000_3999999d4000000_110632_110658
import RHInBoxT_1d4000000_3999999d4000000_110658_110684
import RHInBoxT_1d4000000_3999999d4000000_110684_110711
import RHInBoxT_1d4000000_3999999d4000000_110711_110737
import RHInBoxT_1d4000000_3999999d4000000_110737_110763
import RHInBoxT_1d4000000_3999999d4000000_443051d4_110789
import RHInBoxT_1d4000000_3999999d4000000_110789_443265d4
import RHInBoxT_1d4000000_3999999d4000000_110816_110842
import RHInBoxT_1d4000000_3999999d4000000_110842_443473d4
import RHInBoxT_1d4000000_3999999d4000000_110868_110895
import RHInBoxT_1d4000000_3999999d4000000_110895_110921
import RHInBoxT_1d4000000_3999999d4000000_443683d4_110947
import RHInBoxT_1d4000000_3999999d4000000_110947_110974
import RHInBoxT_1d4000000_3999999d4000000_221947d2_111000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h111000

/-- The 38-band NOMINAL partition of `[110000, 111000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 110000
  | 1 => 110026
  | 2 => 110053
  | 3 => 110079
  | 4 => 110105
  | 5 => 110132
  | 6 => 110158
  | 7 => 110184
  | 8 => 110211
  | 9 => 110237
  | 10 => 110263
  | 11 => 110289
  | 12 => 110316
  | 13 => 110342
  | 14 => 110368
  | 15 => 110395
  | 16 => 110421
  | 17 => 110447
  | 18 => 110474
  | 19 => 110500
  | 20 => 110526
  | 21 => 110553
  | 22 => 110579
  | 23 => 110605
  | 24 => 110632
  | 25 => 110658
  | 26 => 110684
  | 27 => 110711
  | 28 => 110737
  | 29 => 110763
  | 30 => 110789
  | 31 => 110816
  | 32 => 110842
  | 33 => 110868
  | 34 => 110895
  | 35 => 110921
  | 36 => 110947
  | 37 => 110974
  | 38 => 111000
  | _ => 111000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((110000:ℝ)) ≤ (110026); norm_num
  · show ((110026:ℝ)) ≤ (110053); norm_num
  · show ((110053:ℝ)) ≤ (110079); norm_num
  · show ((110079:ℝ)) ≤ (110105); norm_num
  · show ((110105:ℝ)) ≤ (110132); norm_num
  · show ((110132:ℝ)) ≤ (110158); norm_num
  · show ((110158:ℝ)) ≤ (110184); norm_num
  · show ((110184:ℝ)) ≤ (110211); norm_num
  · show ((110211:ℝ)) ≤ (110237); norm_num
  · show ((110237:ℝ)) ≤ (110263); norm_num
  · show ((110263:ℝ)) ≤ (110289); norm_num
  · show ((110289:ℝ)) ≤ (110316); norm_num
  · show ((110316:ℝ)) ≤ (110342); norm_num
  · show ((110342:ℝ)) ≤ (110368); norm_num
  · show ((110368:ℝ)) ≤ (110395); norm_num
  · show ((110395:ℝ)) ≤ (110421); norm_num
  · show ((110421:ℝ)) ≤ (110447); norm_num
  · show ((110447:ℝ)) ≤ (110474); norm_num
  · show ((110474:ℝ)) ≤ (110500); norm_num
  · show ((110500:ℝ)) ≤ (110526); norm_num
  · show ((110526:ℝ)) ≤ (110553); norm_num
  · show ((110553:ℝ)) ≤ (110579); norm_num
  · show ((110579:ℝ)) ≤ (110605); norm_num
  · show ((110605:ℝ)) ≤ (110632); norm_num
  · show ((110632:ℝ)) ≤ (110658); norm_num
  · show ((110658:ℝ)) ≤ (110684); norm_num
  · show ((110684:ℝ)) ≤ (110711); norm_num
  · show ((110711:ℝ)) ≤ (110737); norm_num
  · show ((110737:ℝ)) ≤ (110763); norm_num
  · show ((110763:ℝ)) ≤ (110789); norm_num
  · show ((110789:ℝ)) ≤ (110816); norm_num
  · show ((110816:ℝ)) ≤ (110842); norm_num
  · show ((110842:ℝ)) ≤ (110868); norm_num
  · show ((110868:ℝ)) ≤ (110895); norm_num
  · show ((110895:ℝ)) ≤ (110921); norm_num
  · show ((110921:ℝ)) ≤ (110947); norm_num
  · show ((110947:ℝ)) ≤ (110974); norm_num
  · show ((110974:ℝ)) ≤ (111000); norm_num
  · show ((111000:ℝ)) ≤ (111000); norm_num
  · exact le_refl _

/-- The lower edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 110000
  | 1 => 110026
  | 2 => 110053
  | 3 => 110079
  | 4 => 110105
  | 5 => 110132
  | 6 => 110158
  | 7 => 110184
  | 8 => 110211
  | 9 => 110237
  | 10 => 110263
  | 11 => 110289
  | 12 => 110316
  | 13 => 110342
  | 14 => 110368
  | 15 => 441579 / 4
  | 16 => 110421
  | 17 => 110447
  | 18 => 110474
  | 19 => 110500
  | 20 => 110526
  | 21 => 442211 / 4
  | 22 => 110579
  | 23 => 110605
  | 24 => 110632
  | 25 => 110658
  | 26 => 110684
  | 27 => 110711
  | 28 => 110737
  | 29 => 443051 / 4
  | 30 => 110789
  | 31 => 110816
  | 32 => 110842
  | 33 => 110868
  | 34 => 110895
  | 35 => 443683 / 4
  | 36 => 110947
  | 37 => 221947 / 2
  | _ => 221947 / 2

/-- The upper edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 110026
  | 1 => 440213 / 4
  | 2 => 110079
  | 3 => 110105
  | 4 => 110132
  | 5 => 110158
  | 6 => 110184
  | 7 => 110211
  | 8 => 110237
  | 9 => 110263
  | 10 => 441157 / 4
  | 11 => 110316
  | 12 => 110342
  | 13 => 110368
  | 14 => 110395
  | 15 => 110421
  | 16 => 110447
  | 17 => 110474
  | 18 => 110500
  | 19 => 110526
  | 20 => 110553
  | 21 => 110579
  | 22 => 110605
  | 23 => 442529 / 4
  | 24 => 110658
  | 25 => 110684
  | 26 => 110711
  | 27 => 110737
  | 28 => 110763
  | 29 => 110789
  | 30 => 443265 / 4
  | 31 => 110842
  | 32 => 443473 / 4
  | 33 => 110895
  | 34 => 110921
  | 35 => 110947
  | 36 => 110974
  | 37 => 111000
  | _ => 111000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 38 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 111000` (`log 111000 ≤ 12`, `2.7^12 ≥ 111000`). -/
theorem haC_111000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 111000 := by
  have hlog : Real.log 111000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 111000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 111000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[110000, 111000]` segment's band hypothesis: every band `i < 38` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 38 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 38 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[110000, 111000]` SEGMENT: every zero with `110000 ≤ Im ≤ 111000` is on the line. -/
theorem segment_110000_111000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 111000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (110000:ℝ) ≤ ρ.im → ρ.im ≤ 111000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 110000 111000 bndSeg 38 (by norm_num) bndSeg_mono rfl rfl haC_111000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 111000 via the HEIGHT CHAIN**: `[0,110000]` ∘ `[110000,111000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_111000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 111000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 111000 → ρ.re = 1 / 2 := by
  have hγ110000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 110000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 110000 111000
    (AllZeros_h110000.all_nontrivial_zeros_up_to_height_110000_of_bands
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
      hγ110000)
    (segment_110000_111000 hbands hγ)

end AllZeros_h111000
