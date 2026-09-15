/-  Height-chain step: all nontrivial zeta zeros up to height 126000 on Re = 1/2 --
    `AllZeros_h125000` + a `[125000, 126000]` SEGMENT certificate (38 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h125000
import RHInBoxT_1d4000000_3999999d4000000_125000_125026
import RHInBoxT_1d4000000_3999999d4000000_125026_125053
import RHInBoxT_1d4000000_3999999d4000000_125053_125079
import RHInBoxT_1d4000000_3999999d4000000_125079_125105
import RHInBoxT_1d4000000_3999999d4000000_125105_125132
import RHInBoxT_1d4000000_3999999d4000000_125132_500633d4
import RHInBoxT_1d4000000_3999999d4000000_125158_125184
import RHInBoxT_1d4000000_3999999d4000000_125184_125211
import RHInBoxT_1d4000000_3999999d4000000_125211_125237
import RHInBoxT_1d4000000_3999999d4000000_500947d4_125263
import RHInBoxT_1d4000000_3999999d4000000_125263_125289
import RHInBoxT_1d4000000_3999999d4000000_125289_125316
import RHInBoxT_1d4000000_3999999d4000000_125316_501369d4
import RHInBoxT_1d4000000_3999999d4000000_125342_125368
import RHInBoxT_1d4000000_3999999d4000000_125368_125395
import RHInBoxT_1d4000000_3999999d4000000_125395_125421
import RHInBoxT_1d4000000_3999999d4000000_125421_125447
import RHInBoxT_1d4000000_3999999d4000000_501787d4_125474
import RHInBoxT_1d4000000_3999999d4000000_125474_125500
import RHInBoxT_1d4000000_3999999d4000000_501999d4_125526
import RHInBoxT_1d4000000_3999999d4000000_125526_125553
import RHInBoxT_1d4000000_3999999d4000000_125553_125579
import RHInBoxT_1d4000000_3999999d4000000_125579_125605
import RHInBoxT_1d4000000_3999999d4000000_125605_125632
import RHInBoxT_1d4000000_3999999d4000000_125632_125658
import RHInBoxT_1d4000000_3999999d4000000_125658_502737d4
import RHInBoxT_1d4000000_3999999d4000000_125684_502845d4
import RHInBoxT_1d4000000_3999999d4000000_125711_125737
import RHInBoxT_1d4000000_3999999d4000000_125737_125763
import RHInBoxT_1d4000000_3999999d4000000_125763_125789
import RHInBoxT_1d4000000_3999999d4000000_125789_125816
import RHInBoxT_1d4000000_3999999d4000000_125816_125842
import RHInBoxT_1d4000000_3999999d4000000_125842_503473d4
import RHInBoxT_1d4000000_3999999d4000000_125868_125895
import RHInBoxT_1d4000000_3999999d4000000_125895_125921
import RHInBoxT_1d4000000_3999999d4000000_125921_125947
import RHInBoxT_1d4000000_3999999d4000000_125947_125974
import RHInBoxT_1d4000000_3999999d4000000_125974_504001d4

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h126000

/-- The 38-band NOMINAL partition of `[125000, 126000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 125000
  | 1 => 125026
  | 2 => 125053
  | 3 => 125079
  | 4 => 125105
  | 5 => 125132
  | 6 => 125158
  | 7 => 125184
  | 8 => 125211
  | 9 => 125237
  | 10 => 125263
  | 11 => 125289
  | 12 => 125316
  | 13 => 125342
  | 14 => 125368
  | 15 => 125395
  | 16 => 125421
  | 17 => 125447
  | 18 => 125474
  | 19 => 125500
  | 20 => 125526
  | 21 => 125553
  | 22 => 125579
  | 23 => 125605
  | 24 => 125632
  | 25 => 125658
  | 26 => 125684
  | 27 => 125711
  | 28 => 125737
  | 29 => 125763
  | 30 => 125789
  | 31 => 125816
  | 32 => 125842
  | 33 => 125868
  | 34 => 125895
  | 35 => 125921
  | 36 => 125947
  | 37 => 125974
  | 38 => 126000
  | _ => 126000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((125000:ℝ)) ≤ (125026); norm_num
  · show ((125026:ℝ)) ≤ (125053); norm_num
  · show ((125053:ℝ)) ≤ (125079); norm_num
  · show ((125079:ℝ)) ≤ (125105); norm_num
  · show ((125105:ℝ)) ≤ (125132); norm_num
  · show ((125132:ℝ)) ≤ (125158); norm_num
  · show ((125158:ℝ)) ≤ (125184); norm_num
  · show ((125184:ℝ)) ≤ (125211); norm_num
  · show ((125211:ℝ)) ≤ (125237); norm_num
  · show ((125237:ℝ)) ≤ (125263); norm_num
  · show ((125263:ℝ)) ≤ (125289); norm_num
  · show ((125289:ℝ)) ≤ (125316); norm_num
  · show ((125316:ℝ)) ≤ (125342); norm_num
  · show ((125342:ℝ)) ≤ (125368); norm_num
  · show ((125368:ℝ)) ≤ (125395); norm_num
  · show ((125395:ℝ)) ≤ (125421); norm_num
  · show ((125421:ℝ)) ≤ (125447); norm_num
  · show ((125447:ℝ)) ≤ (125474); norm_num
  · show ((125474:ℝ)) ≤ (125500); norm_num
  · show ((125500:ℝ)) ≤ (125526); norm_num
  · show ((125526:ℝ)) ≤ (125553); norm_num
  · show ((125553:ℝ)) ≤ (125579); norm_num
  · show ((125579:ℝ)) ≤ (125605); norm_num
  · show ((125605:ℝ)) ≤ (125632); norm_num
  · show ((125632:ℝ)) ≤ (125658); norm_num
  · show ((125658:ℝ)) ≤ (125684); norm_num
  · show ((125684:ℝ)) ≤ (125711); norm_num
  · show ((125711:ℝ)) ≤ (125737); norm_num
  · show ((125737:ℝ)) ≤ (125763); norm_num
  · show ((125763:ℝ)) ≤ (125789); norm_num
  · show ((125789:ℝ)) ≤ (125816); norm_num
  · show ((125816:ℝ)) ≤ (125842); norm_num
  · show ((125842:ℝ)) ≤ (125868); norm_num
  · show ((125868:ℝ)) ≤ (125895); norm_num
  · show ((125895:ℝ)) ≤ (125921); norm_num
  · show ((125921:ℝ)) ≤ (125947); norm_num
  · show ((125947:ℝ)) ≤ (125974); norm_num
  · show ((125974:ℝ)) ≤ (126000); norm_num
  · show ((126000:ℝ)) ≤ (126000); norm_num
  · exact le_refl _

/-- The lower edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 125000
  | 1 => 125026
  | 2 => 125053
  | 3 => 125079
  | 4 => 125105
  | 5 => 125132
  | 6 => 125158
  | 7 => 125184
  | 8 => 125211
  | 9 => 500947 / 4
  | 10 => 125263
  | 11 => 125289
  | 12 => 125316
  | 13 => 125342
  | 14 => 125368
  | 15 => 125395
  | 16 => 125421
  | 17 => 501787 / 4
  | 18 => 125474
  | 19 => 501999 / 4
  | 20 => 125526
  | 21 => 125553
  | 22 => 125579
  | 23 => 125605
  | 24 => 125632
  | 25 => 125658
  | 26 => 125684
  | 27 => 125711
  | 28 => 125737
  | 29 => 125763
  | 30 => 125789
  | 31 => 125816
  | 32 => 125842
  | 33 => 125868
  | 34 => 125895
  | 35 => 125921
  | 36 => 125947
  | 37 => 125974
  | _ => 125974

/-- The upper edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 125026
  | 1 => 125053
  | 2 => 125079
  | 3 => 125105
  | 4 => 125132
  | 5 => 500633 / 4
  | 6 => 125184
  | 7 => 125211
  | 8 => 125237
  | 9 => 125263
  | 10 => 125289
  | 11 => 125316
  | 12 => 501369 / 4
  | 13 => 125368
  | 14 => 125395
  | 15 => 125421
  | 16 => 125447
  | 17 => 125474
  | 18 => 125500
  | 19 => 125526
  | 20 => 125553
  | 21 => 125579
  | 22 => 125605
  | 23 => 125632
  | 24 => 125658
  | 25 => 502737 / 4
  | 26 => 502845 / 4
  | 27 => 125737
  | 28 => 125763
  | 29 => 125789
  | 30 => 125816
  | 31 => 125842
  | 32 => 503473 / 4
  | 33 => 125895
  | 34 => 125921
  | 35 => 125947
  | 36 => 125974
  | 37 => 504001 / 4
  | _ => 504001 / 4

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 38 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 126000` (`log 126000 ≤ 12`, `2.7^12 ≥ 126000`). -/
theorem haC_126000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 126000 := by
  have hlog : Real.log 126000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 126000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 126000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[125000, 126000]` segment's band hypothesis: every band `i < 38` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 38 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 38 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[125000, 126000]` SEGMENT: every zero with `125000 ≤ Im ≤ 126000` is on the line. -/
theorem segment_125000_126000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 126000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (125000:ℝ) ≤ ρ.im → ρ.im ≤ 126000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 125000 126000 bndSeg 38 (by norm_num) bndSeg_mono rfl rfl haC_126000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 126000 via the HEIGHT CHAIN**: `[0,125000]` ∘ `[125000,126000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_126000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 126000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 126000 → ρ.re = 1 / 2 := by
  have hγ125000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 125000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 125000 126000
    (AllZeros_h125000.all_nontrivial_zeros_up_to_height_125000_of_bands
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
      hγ125000)
    (segment_125000_126000 hbands hγ)

end AllZeros_h126000
