/-  Height-chain step: all nontrivial zeta zeros up to height 129000 on Re = 1/2 --
    `AllZeros_h128000` + a `[128000, 129000]` SEGMENT certificate (38 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h128000
import RHInBoxT_1d4000000_3999999d4000000_128000_128026
import RHInBoxT_1d4000000_3999999d4000000_128026_128053
import RHInBoxT_1d4000000_3999999d4000000_512211d4_128079
import RHInBoxT_1d4000000_3999999d4000000_128079_128105
import RHInBoxT_1d4000000_3999999d4000000_128105_512529d4
import RHInBoxT_1d4000000_3999999d4000000_128132_128158
import RHInBoxT_1d4000000_3999999d4000000_128158_512737d4
import RHInBoxT_1d4000000_3999999d4000000_128184_128211
import RHInBoxT_1d4000000_3999999d4000000_128211_128237
import RHInBoxT_1d4000000_3999999d4000000_128237_128263
import RHInBoxT_1d4000000_3999999d4000000_128263_128289
import RHInBoxT_1d4000000_3999999d4000000_128289_513265d4
import RHInBoxT_1d4000000_3999999d4000000_128316_128342
import RHInBoxT_1d4000000_3999999d4000000_513367d4_128368
import RHInBoxT_1d4000000_3999999d4000000_128368_513581d4
import RHInBoxT_1d4000000_3999999d4000000_128395_128421
import RHInBoxT_1d4000000_3999999d4000000_128421_128447
import RHInBoxT_1d4000000_3999999d4000000_513787d4_128474
import RHInBoxT_1d4000000_3999999d4000000_128474_128500
import RHInBoxT_1d4000000_3999999d4000000_128500_128526
import RHInBoxT_1d4000000_3999999d4000000_128526_128553
import RHInBoxT_1d4000000_3999999d4000000_128553_128579
import RHInBoxT_1d4000000_3999999d4000000_128579_128605
import RHInBoxT_1d4000000_3999999d4000000_128605_128632
import RHInBoxT_1d4000000_3999999d4000000_514527d4_128658
import RHInBoxT_1d4000000_3999999d4000000_514631d4_514737d4
import RHInBoxT_1d4000000_3999999d4000000_128684_128711
import RHInBoxT_1d4000000_3999999d4000000_128711_128737
import RHInBoxT_1d4000000_3999999d4000000_128737_128763
import RHInBoxT_1d4000000_3999999d4000000_128763_128789
import RHInBoxT_1d4000000_3999999d4000000_128789_128816
import RHInBoxT_1d4000000_3999999d4000000_128816_128842
import RHInBoxT_1d4000000_3999999d4000000_128842_128868
import RHInBoxT_1d4000000_3999999d4000000_515471d4_128895
import RHInBoxT_1d4000000_3999999d4000000_128895_128921
import RHInBoxT_1d4000000_3999999d4000000_128921_128947
import RHInBoxT_1d4000000_3999999d4000000_128947_128974
import RHInBoxT_1d4000000_3999999d4000000_128974_129000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h129000

/-- The 38-band NOMINAL partition of `[128000, 129000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 128000
  | 1 => 128026
  | 2 => 128053
  | 3 => 128079
  | 4 => 128105
  | 5 => 128132
  | 6 => 128158
  | 7 => 128184
  | 8 => 128211
  | 9 => 128237
  | 10 => 128263
  | 11 => 128289
  | 12 => 128316
  | 13 => 128342
  | 14 => 128368
  | 15 => 128395
  | 16 => 128421
  | 17 => 128447
  | 18 => 128474
  | 19 => 128500
  | 20 => 128526
  | 21 => 128553
  | 22 => 128579
  | 23 => 128605
  | 24 => 128632
  | 25 => 128658
  | 26 => 128684
  | 27 => 128711
  | 28 => 128737
  | 29 => 128763
  | 30 => 128789
  | 31 => 128816
  | 32 => 128842
  | 33 => 128868
  | 34 => 128895
  | 35 => 128921
  | 36 => 128947
  | 37 => 128974
  | 38 => 129000
  | _ => 129000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((128000:ℝ)) ≤ (128026); norm_num
  · show ((128026:ℝ)) ≤ (128053); norm_num
  · show ((128053:ℝ)) ≤ (128079); norm_num
  · show ((128079:ℝ)) ≤ (128105); norm_num
  · show ((128105:ℝ)) ≤ (128132); norm_num
  · show ((128132:ℝ)) ≤ (128158); norm_num
  · show ((128158:ℝ)) ≤ (128184); norm_num
  · show ((128184:ℝ)) ≤ (128211); norm_num
  · show ((128211:ℝ)) ≤ (128237); norm_num
  · show ((128237:ℝ)) ≤ (128263); norm_num
  · show ((128263:ℝ)) ≤ (128289); norm_num
  · show ((128289:ℝ)) ≤ (128316); norm_num
  · show ((128316:ℝ)) ≤ (128342); norm_num
  · show ((128342:ℝ)) ≤ (128368); norm_num
  · show ((128368:ℝ)) ≤ (128395); norm_num
  · show ((128395:ℝ)) ≤ (128421); norm_num
  · show ((128421:ℝ)) ≤ (128447); norm_num
  · show ((128447:ℝ)) ≤ (128474); norm_num
  · show ((128474:ℝ)) ≤ (128500); norm_num
  · show ((128500:ℝ)) ≤ (128526); norm_num
  · show ((128526:ℝ)) ≤ (128553); norm_num
  · show ((128553:ℝ)) ≤ (128579); norm_num
  · show ((128579:ℝ)) ≤ (128605); norm_num
  · show ((128605:ℝ)) ≤ (128632); norm_num
  · show ((128632:ℝ)) ≤ (128658); norm_num
  · show ((128658:ℝ)) ≤ (128684); norm_num
  · show ((128684:ℝ)) ≤ (128711); norm_num
  · show ((128711:ℝ)) ≤ (128737); norm_num
  · show ((128737:ℝ)) ≤ (128763); norm_num
  · show ((128763:ℝ)) ≤ (128789); norm_num
  · show ((128789:ℝ)) ≤ (128816); norm_num
  · show ((128816:ℝ)) ≤ (128842); norm_num
  · show ((128842:ℝ)) ≤ (128868); norm_num
  · show ((128868:ℝ)) ≤ (128895); norm_num
  · show ((128895:ℝ)) ≤ (128921); norm_num
  · show ((128921:ℝ)) ≤ (128947); norm_num
  · show ((128947:ℝ)) ≤ (128974); norm_num
  · show ((128974:ℝ)) ≤ (129000); norm_num
  · show ((129000:ℝ)) ≤ (129000); norm_num
  · exact le_refl _

/-- The lower edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 128000
  | 1 => 128026
  | 2 => 512211 / 4
  | 3 => 128079
  | 4 => 128105
  | 5 => 128132
  | 6 => 128158
  | 7 => 128184
  | 8 => 128211
  | 9 => 128237
  | 10 => 128263
  | 11 => 128289
  | 12 => 128316
  | 13 => 513367 / 4
  | 14 => 128368
  | 15 => 128395
  | 16 => 128421
  | 17 => 513787 / 4
  | 18 => 128474
  | 19 => 128500
  | 20 => 128526
  | 21 => 128553
  | 22 => 128579
  | 23 => 128605
  | 24 => 514527 / 4
  | 25 => 514631 / 4
  | 26 => 128684
  | 27 => 128711
  | 28 => 128737
  | 29 => 128763
  | 30 => 128789
  | 31 => 128816
  | 32 => 128842
  | 33 => 515471 / 4
  | 34 => 128895
  | 35 => 128921
  | 36 => 128947
  | 37 => 128974
  | _ => 128974

/-- The upper edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 128026
  | 1 => 128053
  | 2 => 128079
  | 3 => 128105
  | 4 => 512529 / 4
  | 5 => 128158
  | 6 => 512737 / 4
  | 7 => 128211
  | 8 => 128237
  | 9 => 128263
  | 10 => 128289
  | 11 => 513265 / 4
  | 12 => 128342
  | 13 => 128368
  | 14 => 513581 / 4
  | 15 => 128421
  | 16 => 128447
  | 17 => 128474
  | 18 => 128500
  | 19 => 128526
  | 20 => 128553
  | 21 => 128579
  | 22 => 128605
  | 23 => 128632
  | 24 => 128658
  | 25 => 514737 / 4
  | 26 => 128711
  | 27 => 128737
  | 28 => 128763
  | 29 => 128789
  | 30 => 128816
  | 31 => 128842
  | 32 => 128868
  | 33 => 128895
  | 34 => 128921
  | 35 => 128947
  | 36 => 128974
  | 37 => 129000
  | _ => 129000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 38 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 129000` (`log 129000 ≤ 12`, `2.7^12 ≥ 129000`). -/
theorem haC_129000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 129000 := by
  have hlog : Real.log 129000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 129000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 129000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[128000, 129000]` segment's band hypothesis: every band `i < 38` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 38 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 38 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[128000, 129000]` SEGMENT: every zero with `128000 ≤ Im ≤ 129000` is on the line. -/
theorem segment_128000_129000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 129000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (128000:ℝ) ≤ ρ.im → ρ.im ≤ 129000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 128000 129000 bndSeg 38 (by norm_num) bndSeg_mono rfl rfl haC_129000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 129000 via the HEIGHT CHAIN**: `[0,128000]` ∘ `[128000,129000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_129000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 129000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 129000 → ρ.re = 1 / 2 := by
  have hγ128000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 128000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 128000 129000
    (AllZeros_h128000.all_nontrivial_zeros_up_to_height_128000_of_bands
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
      hγ128000)
    (segment_128000_129000 hbands hγ)

end AllZeros_h129000
