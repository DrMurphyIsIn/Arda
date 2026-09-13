/-  Height-chain step: all nontrivial zeta zeros up to height 133000 on Re = 1/2 --
    `AllZeros_h132000` + a `[132000, 133000]` SEGMENT certificate (38 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h132000
import RHInBoxT_1d4000000_3999999d4000000_132000_132026
import RHInBoxT_1d4000000_3999999d4000000_528103d4_132053
import RHInBoxT_1d4000000_3999999d4000000_528211d4_132079
import RHInBoxT_1d4000000_3999999d4000000_132079_132105
import RHInBoxT_1d4000000_3999999d4000000_132105_132132
import RHInBoxT_1d4000000_3999999d4000000_132132_132158
import RHInBoxT_1d4000000_3999999d4000000_132158_132184
import RHInBoxT_1d4000000_3999999d4000000_132184_132211
import RHInBoxT_1d4000000_3999999d4000000_132211_132237
import RHInBoxT_1d4000000_3999999d4000000_132237_132263
import RHInBoxT_1d4000000_3999999d4000000_132263_529157d4
import RHInBoxT_1d4000000_3999999d4000000_132289_132316
import RHInBoxT_1d4000000_3999999d4000000_132316_132342
import RHInBoxT_1d4000000_3999999d4000000_132342_132368
import RHInBoxT_1d4000000_3999999d4000000_132368_132395
import RHInBoxT_1d4000000_3999999d4000000_132395_132421
import RHInBoxT_1d4000000_3999999d4000000_132421_132447
import RHInBoxT_1d4000000_3999999d4000000_529787d4_132474
import RHInBoxT_1d4000000_3999999d4000000_132474_132500
import RHInBoxT_1d4000000_3999999d4000000_132500_132526
import RHInBoxT_1d4000000_3999999d4000000_132526_132553
import RHInBoxT_1d4000000_3999999d4000000_132553_132579
import RHInBoxT_1d4000000_3999999d4000000_132579_132605
import RHInBoxT_1d4000000_3999999d4000000_132605_530529d4
import RHInBoxT_1d4000000_3999999d4000000_132632_132658
import RHInBoxT_1d4000000_3999999d4000000_132658_132684
import RHInBoxT_1d4000000_3999999d4000000_132684_530845d4
import RHInBoxT_1d4000000_3999999d4000000_132711_132737
import RHInBoxT_1d4000000_3999999d4000000_132737_132763
import RHInBoxT_1d4000000_3999999d4000000_531051d4_132789
import RHInBoxT_1d4000000_3999999d4000000_132789_132816
import RHInBoxT_1d4000000_3999999d4000000_132816_132842
import RHInBoxT_1d4000000_3999999d4000000_132842_132868
import RHInBoxT_1d4000000_3999999d4000000_132868_132895
import RHInBoxT_1d4000000_3999999d4000000_132895_531685d4
import RHInBoxT_1d4000000_3999999d4000000_132921_531789d4
import RHInBoxT_1d4000000_3999999d4000000_132947_132974
import RHInBoxT_1d4000000_3999999d4000000_132974_133000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h133000

/-- The 38-band NOMINAL partition of `[132000, 133000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 132000
  | 1 => 132026
  | 2 => 132053
  | 3 => 132079
  | 4 => 132105
  | 5 => 132132
  | 6 => 132158
  | 7 => 132184
  | 8 => 132211
  | 9 => 132237
  | 10 => 132263
  | 11 => 132289
  | 12 => 132316
  | 13 => 132342
  | 14 => 132368
  | 15 => 132395
  | 16 => 132421
  | 17 => 132447
  | 18 => 132474
  | 19 => 132500
  | 20 => 132526
  | 21 => 132553
  | 22 => 132579
  | 23 => 132605
  | 24 => 132632
  | 25 => 132658
  | 26 => 132684
  | 27 => 132711
  | 28 => 132737
  | 29 => 132763
  | 30 => 132789
  | 31 => 132816
  | 32 => 132842
  | 33 => 132868
  | 34 => 132895
  | 35 => 132921
  | 36 => 132947
  | 37 => 132974
  | 38 => 133000
  | _ => 133000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((132000:ℝ)) ≤ (132026); norm_num
  · show ((132026:ℝ)) ≤ (132053); norm_num
  · show ((132053:ℝ)) ≤ (132079); norm_num
  · show ((132079:ℝ)) ≤ (132105); norm_num
  · show ((132105:ℝ)) ≤ (132132); norm_num
  · show ((132132:ℝ)) ≤ (132158); norm_num
  · show ((132158:ℝ)) ≤ (132184); norm_num
  · show ((132184:ℝ)) ≤ (132211); norm_num
  · show ((132211:ℝ)) ≤ (132237); norm_num
  · show ((132237:ℝ)) ≤ (132263); norm_num
  · show ((132263:ℝ)) ≤ (132289); norm_num
  · show ((132289:ℝ)) ≤ (132316); norm_num
  · show ((132316:ℝ)) ≤ (132342); norm_num
  · show ((132342:ℝ)) ≤ (132368); norm_num
  · show ((132368:ℝ)) ≤ (132395); norm_num
  · show ((132395:ℝ)) ≤ (132421); norm_num
  · show ((132421:ℝ)) ≤ (132447); norm_num
  · show ((132447:ℝ)) ≤ (132474); norm_num
  · show ((132474:ℝ)) ≤ (132500); norm_num
  · show ((132500:ℝ)) ≤ (132526); norm_num
  · show ((132526:ℝ)) ≤ (132553); norm_num
  · show ((132553:ℝ)) ≤ (132579); norm_num
  · show ((132579:ℝ)) ≤ (132605); norm_num
  · show ((132605:ℝ)) ≤ (132632); norm_num
  · show ((132632:ℝ)) ≤ (132658); norm_num
  · show ((132658:ℝ)) ≤ (132684); norm_num
  · show ((132684:ℝ)) ≤ (132711); norm_num
  · show ((132711:ℝ)) ≤ (132737); norm_num
  · show ((132737:ℝ)) ≤ (132763); norm_num
  · show ((132763:ℝ)) ≤ (132789); norm_num
  · show ((132789:ℝ)) ≤ (132816); norm_num
  · show ((132816:ℝ)) ≤ (132842); norm_num
  · show ((132842:ℝ)) ≤ (132868); norm_num
  · show ((132868:ℝ)) ≤ (132895); norm_num
  · show ((132895:ℝ)) ≤ (132921); norm_num
  · show ((132921:ℝ)) ≤ (132947); norm_num
  · show ((132947:ℝ)) ≤ (132974); norm_num
  · show ((132974:ℝ)) ≤ (133000); norm_num
  · show ((133000:ℝ)) ≤ (133000); norm_num
  · exact le_refl _

/-- The lower edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 132000
  | 1 => 528103 / 4
  | 2 => 528211 / 4
  | 3 => 132079
  | 4 => 132105
  | 5 => 132132
  | 6 => 132158
  | 7 => 132184
  | 8 => 132211
  | 9 => 132237
  | 10 => 132263
  | 11 => 132289
  | 12 => 132316
  | 13 => 132342
  | 14 => 132368
  | 15 => 132395
  | 16 => 132421
  | 17 => 529787 / 4
  | 18 => 132474
  | 19 => 132500
  | 20 => 132526
  | 21 => 132553
  | 22 => 132579
  | 23 => 132605
  | 24 => 132632
  | 25 => 132658
  | 26 => 132684
  | 27 => 132711
  | 28 => 132737
  | 29 => 531051 / 4
  | 30 => 132789
  | 31 => 132816
  | 32 => 132842
  | 33 => 132868
  | 34 => 132895
  | 35 => 132921
  | 36 => 132947
  | 37 => 132974
  | _ => 132974

/-- The upper edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 132026
  | 1 => 132053
  | 2 => 132079
  | 3 => 132105
  | 4 => 132132
  | 5 => 132158
  | 6 => 132184
  | 7 => 132211
  | 8 => 132237
  | 9 => 132263
  | 10 => 529157 / 4
  | 11 => 132316
  | 12 => 132342
  | 13 => 132368
  | 14 => 132395
  | 15 => 132421
  | 16 => 132447
  | 17 => 132474
  | 18 => 132500
  | 19 => 132526
  | 20 => 132553
  | 21 => 132579
  | 22 => 132605
  | 23 => 530529 / 4
  | 24 => 132658
  | 25 => 132684
  | 26 => 530845 / 4
  | 27 => 132737
  | 28 => 132763
  | 29 => 132789
  | 30 => 132816
  | 31 => 132842
  | 32 => 132868
  | 33 => 132895
  | 34 => 531685 / 4
  | 35 => 531789 / 4
  | 36 => 132974
  | 37 => 133000
  | _ => 133000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 38 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 133000` (`log 133000 ≤ 12`, `2.7^12 ≥ 133000`). -/
theorem haC_133000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 133000 := by
  have hlog : Real.log 133000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 133000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 133000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[132000, 133000]` segment's band hypothesis: every band `i < 38` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 38 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 38 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[132000, 133000]` SEGMENT: every zero with `132000 ≤ Im ≤ 133000` is on the line. -/
theorem segment_132000_133000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 133000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (132000:ℝ) ≤ ρ.im → ρ.im ≤ 133000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 132000 133000 bndSeg 38 (by norm_num) bndSeg_mono rfl rfl haC_133000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 133000 via the HEIGHT CHAIN**: `[0,132000]` ∘ `[132000,133000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_133000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 133000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 133000 → ρ.re = 1 / 2 := by
  have hγ132000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 132000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 132000 133000
    (AllZeros_h132000.all_nontrivial_zeros_up_to_height_132000_of_bands
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
      hγ132000)
    (segment_132000_133000 hbands hγ)

end AllZeros_h133000
