/-  Height-chain step: all nontrivial zeta zeros up to height 115000 on Re = 1/2 --
    `AllZeros_h114000` + a `[114000, 115000]` SEGMENT certificate (38 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h114000
import RHInBoxT_1d4000000_3999999d4000000_114000_114026
import RHInBoxT_1d4000000_3999999d4000000_456103d4_114053
import RHInBoxT_1d4000000_3999999d4000000_114053_114079
import RHInBoxT_1d4000000_3999999d4000000_114079_456421d4
import RHInBoxT_1d4000000_3999999d4000000_114105_114132
import RHInBoxT_1d4000000_3999999d4000000_114132_114158
import RHInBoxT_1d4000000_3999999d4000000_114158_114184
import RHInBoxT_1d4000000_3999999d4000000_114184_114211
import RHInBoxT_1d4000000_3999999d4000000_456843d4_114237
import RHInBoxT_1d4000000_3999999d4000000_114237_114263
import RHInBoxT_1d4000000_3999999d4000000_114263_114289
import RHInBoxT_1d4000000_3999999d4000000_114289_114316
import RHInBoxT_1d4000000_3999999d4000000_114316_457369d4
import RHInBoxT_1d4000000_3999999d4000000_114342_114368
import RHInBoxT_1d4000000_3999999d4000000_114368_114395
import RHInBoxT_1d4000000_3999999d4000000_114395_114421
import RHInBoxT_1d4000000_3999999d4000000_457683d4_457789d4
import RHInBoxT_1d4000000_3999999d4000000_114447_114474
import RHInBoxT_1d4000000_3999999d4000000_457895d4_114500
import RHInBoxT_1d4000000_3999999d4000000_114500_114526
import RHInBoxT_1d4000000_3999999d4000000_114526_114553
import RHInBoxT_1d4000000_3999999d4000000_114553_114579
import RHInBoxT_1d4000000_3999999d4000000_114579_114605
import RHInBoxT_1d4000000_3999999d4000000_114605_114632
import RHInBoxT_1d4000000_3999999d4000000_114632_114658
import RHInBoxT_1d4000000_3999999d4000000_229315d2_114684
import RHInBoxT_1d4000000_3999999d4000000_114684_114711
import RHInBoxT_1d4000000_3999999d4000000_114711_114737
import RHInBoxT_1d4000000_3999999d4000000_114737_459053d4
import RHInBoxT_1d4000000_3999999d4000000_114763_114789
import RHInBoxT_1d4000000_3999999d4000000_114789_114816
import RHInBoxT_1d4000000_3999999d4000000_114816_114842
import RHInBoxT_1d4000000_3999999d4000000_114842_114868
import RHInBoxT_1d4000000_3999999d4000000_114868_459581d4
import RHInBoxT_1d4000000_3999999d4000000_114895_114921
import RHInBoxT_1d4000000_3999999d4000000_459683d4_114947
import RHInBoxT_1d4000000_3999999d4000000_114947_114974
import RHInBoxT_1d4000000_3999999d4000000_114974_115000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h115000

/-- The 38-band NOMINAL partition of `[114000, 115000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 114000
  | 1 => 114026
  | 2 => 114053
  | 3 => 114079
  | 4 => 114105
  | 5 => 114132
  | 6 => 114158
  | 7 => 114184
  | 8 => 114211
  | 9 => 114237
  | 10 => 114263
  | 11 => 114289
  | 12 => 114316
  | 13 => 114342
  | 14 => 114368
  | 15 => 114395
  | 16 => 114421
  | 17 => 114447
  | 18 => 114474
  | 19 => 114500
  | 20 => 114526
  | 21 => 114553
  | 22 => 114579
  | 23 => 114605
  | 24 => 114632
  | 25 => 114658
  | 26 => 114684
  | 27 => 114711
  | 28 => 114737
  | 29 => 114763
  | 30 => 114789
  | 31 => 114816
  | 32 => 114842
  | 33 => 114868
  | 34 => 114895
  | 35 => 114921
  | 36 => 114947
  | 37 => 114974
  | 38 => 115000
  | _ => 115000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((114000:ℝ)) ≤ (114026); norm_num
  · show ((114026:ℝ)) ≤ (114053); norm_num
  · show ((114053:ℝ)) ≤ (114079); norm_num
  · show ((114079:ℝ)) ≤ (114105); norm_num
  · show ((114105:ℝ)) ≤ (114132); norm_num
  · show ((114132:ℝ)) ≤ (114158); norm_num
  · show ((114158:ℝ)) ≤ (114184); norm_num
  · show ((114184:ℝ)) ≤ (114211); norm_num
  · show ((114211:ℝ)) ≤ (114237); norm_num
  · show ((114237:ℝ)) ≤ (114263); norm_num
  · show ((114263:ℝ)) ≤ (114289); norm_num
  · show ((114289:ℝ)) ≤ (114316); norm_num
  · show ((114316:ℝ)) ≤ (114342); norm_num
  · show ((114342:ℝ)) ≤ (114368); norm_num
  · show ((114368:ℝ)) ≤ (114395); norm_num
  · show ((114395:ℝ)) ≤ (114421); norm_num
  · show ((114421:ℝ)) ≤ (114447); norm_num
  · show ((114447:ℝ)) ≤ (114474); norm_num
  · show ((114474:ℝ)) ≤ (114500); norm_num
  · show ((114500:ℝ)) ≤ (114526); norm_num
  · show ((114526:ℝ)) ≤ (114553); norm_num
  · show ((114553:ℝ)) ≤ (114579); norm_num
  · show ((114579:ℝ)) ≤ (114605); norm_num
  · show ((114605:ℝ)) ≤ (114632); norm_num
  · show ((114632:ℝ)) ≤ (114658); norm_num
  · show ((114658:ℝ)) ≤ (114684); norm_num
  · show ((114684:ℝ)) ≤ (114711); norm_num
  · show ((114711:ℝ)) ≤ (114737); norm_num
  · show ((114737:ℝ)) ≤ (114763); norm_num
  · show ((114763:ℝ)) ≤ (114789); norm_num
  · show ((114789:ℝ)) ≤ (114816); norm_num
  · show ((114816:ℝ)) ≤ (114842); norm_num
  · show ((114842:ℝ)) ≤ (114868); norm_num
  · show ((114868:ℝ)) ≤ (114895); norm_num
  · show ((114895:ℝ)) ≤ (114921); norm_num
  · show ((114921:ℝ)) ≤ (114947); norm_num
  · show ((114947:ℝ)) ≤ (114974); norm_num
  · show ((114974:ℝ)) ≤ (115000); norm_num
  · show ((115000:ℝ)) ≤ (115000); norm_num
  · exact le_refl _

/-- The lower edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 114000
  | 1 => 456103 / 4
  | 2 => 114053
  | 3 => 114079
  | 4 => 114105
  | 5 => 114132
  | 6 => 114158
  | 7 => 114184
  | 8 => 456843 / 4
  | 9 => 114237
  | 10 => 114263
  | 11 => 114289
  | 12 => 114316
  | 13 => 114342
  | 14 => 114368
  | 15 => 114395
  | 16 => 457683 / 4
  | 17 => 114447
  | 18 => 457895 / 4
  | 19 => 114500
  | 20 => 114526
  | 21 => 114553
  | 22 => 114579
  | 23 => 114605
  | 24 => 114632
  | 25 => 229315 / 2
  | 26 => 114684
  | 27 => 114711
  | 28 => 114737
  | 29 => 114763
  | 30 => 114789
  | 31 => 114816
  | 32 => 114842
  | 33 => 114868
  | 34 => 114895
  | 35 => 459683 / 4
  | 36 => 114947
  | 37 => 114974
  | _ => 114974

/-- The upper edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 114026
  | 1 => 114053
  | 2 => 114079
  | 3 => 456421 / 4
  | 4 => 114132
  | 5 => 114158
  | 6 => 114184
  | 7 => 114211
  | 8 => 114237
  | 9 => 114263
  | 10 => 114289
  | 11 => 114316
  | 12 => 457369 / 4
  | 13 => 114368
  | 14 => 114395
  | 15 => 114421
  | 16 => 457789 / 4
  | 17 => 114474
  | 18 => 114500
  | 19 => 114526
  | 20 => 114553
  | 21 => 114579
  | 22 => 114605
  | 23 => 114632
  | 24 => 114658
  | 25 => 114684
  | 26 => 114711
  | 27 => 114737
  | 28 => 459053 / 4
  | 29 => 114789
  | 30 => 114816
  | 31 => 114842
  | 32 => 114868
  | 33 => 459581 / 4
  | 34 => 114921
  | 35 => 114947
  | 36 => 114974
  | 37 => 115000
  | _ => 115000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 38 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 115000` (`log 115000 ≤ 12`, `2.7^12 ≥ 115000`). -/
theorem haC_115000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 115000 := by
  have hlog : Real.log 115000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 115000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 115000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[114000, 115000]` segment's band hypothesis: every band `i < 38` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 38 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 38 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[114000, 115000]` SEGMENT: every zero with `114000 ≤ Im ≤ 115000` is on the line. -/
theorem segment_114000_115000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 115000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (114000:ℝ) ≤ ρ.im → ρ.im ≤ 115000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 114000 115000 bndSeg 38 (by norm_num) bndSeg_mono rfl rfl haC_115000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 115000 via the HEIGHT CHAIN**: `[0,114000]` ∘ `[114000,115000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_115000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 115000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 115000 → ρ.re = 1 / 2 := by
  have hγ114000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 114000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 114000 115000
    (AllZeros_h114000.all_nontrivial_zeros_up_to_height_114000_of_bands
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
      hγ114000)
    (segment_114000_115000 hbands hγ)

end AllZeros_h115000
