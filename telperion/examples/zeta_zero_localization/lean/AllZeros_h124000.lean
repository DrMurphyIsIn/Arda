/-  Height-chain step: all nontrivial zeta zeros up to height 124000 on Re = 1/2 --
    `AllZeros_h123000` + a `[123000, 124000]` SEGMENT certificate (38 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h123000
import RHInBoxT_1d4000000_3999999d4000000_123000_123026
import RHInBoxT_1d4000000_3999999d4000000_123026_123053
import RHInBoxT_1d4000000_3999999d4000000_123053_492317d4
import RHInBoxT_1d4000000_3999999d4000000_123079_123105
import RHInBoxT_1d4000000_3999999d4000000_123105_123132
import RHInBoxT_1d4000000_3999999d4000000_123132_123158
import RHInBoxT_1d4000000_3999999d4000000_123158_123184
import RHInBoxT_1d4000000_3999999d4000000_123184_123211
import RHInBoxT_1d4000000_3999999d4000000_492843d4_123237
import RHInBoxT_1d4000000_3999999d4000000_123237_123263
import RHInBoxT_1d4000000_3999999d4000000_123263_123289
import RHInBoxT_1d4000000_3999999d4000000_493155d4_123316
import RHInBoxT_1d4000000_3999999d4000000_123316_123342
import RHInBoxT_1d4000000_3999999d4000000_493367d4_123368
import RHInBoxT_1d4000000_3999999d4000000_123368_123395
import RHInBoxT_1d4000000_3999999d4000000_123395_123421
import RHInBoxT_1d4000000_3999999d4000000_123421_123447
import RHInBoxT_1d4000000_3999999d4000000_123447_123474
import RHInBoxT_1d4000000_3999999d4000000_123474_123500
import RHInBoxT_1d4000000_3999999d4000000_123500_123526
import RHInBoxT_1d4000000_3999999d4000000_123526_123553
import RHInBoxT_1d4000000_3999999d4000000_123553_123579
import RHInBoxT_1d4000000_3999999d4000000_123579_123605
import RHInBoxT_1d4000000_3999999d4000000_123605_123632
import RHInBoxT_1d4000000_3999999d4000000_123632_123658
import RHInBoxT_1d4000000_3999999d4000000_123658_123684
import RHInBoxT_1d4000000_3999999d4000000_123684_494845d4
import RHInBoxT_1d4000000_3999999d4000000_123711_123737
import RHInBoxT_1d4000000_3999999d4000000_494947d4_123763
import RHInBoxT_1d4000000_3999999d4000000_123763_123789
import RHInBoxT_1d4000000_3999999d4000000_123789_123816
import RHInBoxT_1d4000000_3999999d4000000_123816_123842
import RHInBoxT_1d4000000_3999999d4000000_123842_495473d4
import RHInBoxT_1d4000000_3999999d4000000_123868_123895
import RHInBoxT_1d4000000_3999999d4000000_123895_123921
import RHInBoxT_1d4000000_3999999d4000000_123921_495789d4
import RHInBoxT_1d4000000_3999999d4000000_123947_123974
import RHInBoxT_1d4000000_3999999d4000000_123974_124000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h124000

/-- The 38-band NOMINAL partition of `[123000, 124000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 123000
  | 1 => 123026
  | 2 => 123053
  | 3 => 123079
  | 4 => 123105
  | 5 => 123132
  | 6 => 123158
  | 7 => 123184
  | 8 => 123211
  | 9 => 123237
  | 10 => 123263
  | 11 => 123289
  | 12 => 123316
  | 13 => 123342
  | 14 => 123368
  | 15 => 123395
  | 16 => 123421
  | 17 => 123447
  | 18 => 123474
  | 19 => 123500
  | 20 => 123526
  | 21 => 123553
  | 22 => 123579
  | 23 => 123605
  | 24 => 123632
  | 25 => 123658
  | 26 => 123684
  | 27 => 123711
  | 28 => 123737
  | 29 => 123763
  | 30 => 123789
  | 31 => 123816
  | 32 => 123842
  | 33 => 123868
  | 34 => 123895
  | 35 => 123921
  | 36 => 123947
  | 37 => 123974
  | 38 => 124000
  | _ => 124000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((123000:ℝ)) ≤ (123026); norm_num
  · show ((123026:ℝ)) ≤ (123053); norm_num
  · show ((123053:ℝ)) ≤ (123079); norm_num
  · show ((123079:ℝ)) ≤ (123105); norm_num
  · show ((123105:ℝ)) ≤ (123132); norm_num
  · show ((123132:ℝ)) ≤ (123158); norm_num
  · show ((123158:ℝ)) ≤ (123184); norm_num
  · show ((123184:ℝ)) ≤ (123211); norm_num
  · show ((123211:ℝ)) ≤ (123237); norm_num
  · show ((123237:ℝ)) ≤ (123263); norm_num
  · show ((123263:ℝ)) ≤ (123289); norm_num
  · show ((123289:ℝ)) ≤ (123316); norm_num
  · show ((123316:ℝ)) ≤ (123342); norm_num
  · show ((123342:ℝ)) ≤ (123368); norm_num
  · show ((123368:ℝ)) ≤ (123395); norm_num
  · show ((123395:ℝ)) ≤ (123421); norm_num
  · show ((123421:ℝ)) ≤ (123447); norm_num
  · show ((123447:ℝ)) ≤ (123474); norm_num
  · show ((123474:ℝ)) ≤ (123500); norm_num
  · show ((123500:ℝ)) ≤ (123526); norm_num
  · show ((123526:ℝ)) ≤ (123553); norm_num
  · show ((123553:ℝ)) ≤ (123579); norm_num
  · show ((123579:ℝ)) ≤ (123605); norm_num
  · show ((123605:ℝ)) ≤ (123632); norm_num
  · show ((123632:ℝ)) ≤ (123658); norm_num
  · show ((123658:ℝ)) ≤ (123684); norm_num
  · show ((123684:ℝ)) ≤ (123711); norm_num
  · show ((123711:ℝ)) ≤ (123737); norm_num
  · show ((123737:ℝ)) ≤ (123763); norm_num
  · show ((123763:ℝ)) ≤ (123789); norm_num
  · show ((123789:ℝ)) ≤ (123816); norm_num
  · show ((123816:ℝ)) ≤ (123842); norm_num
  · show ((123842:ℝ)) ≤ (123868); norm_num
  · show ((123868:ℝ)) ≤ (123895); norm_num
  · show ((123895:ℝ)) ≤ (123921); norm_num
  · show ((123921:ℝ)) ≤ (123947); norm_num
  · show ((123947:ℝ)) ≤ (123974); norm_num
  · show ((123974:ℝ)) ≤ (124000); norm_num
  · show ((124000:ℝ)) ≤ (124000); norm_num
  · exact le_refl _

/-- The lower edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 123000
  | 1 => 123026
  | 2 => 123053
  | 3 => 123079
  | 4 => 123105
  | 5 => 123132
  | 6 => 123158
  | 7 => 123184
  | 8 => 492843 / 4
  | 9 => 123237
  | 10 => 123263
  | 11 => 493155 / 4
  | 12 => 123316
  | 13 => 493367 / 4
  | 14 => 123368
  | 15 => 123395
  | 16 => 123421
  | 17 => 123447
  | 18 => 123474
  | 19 => 123500
  | 20 => 123526
  | 21 => 123553
  | 22 => 123579
  | 23 => 123605
  | 24 => 123632
  | 25 => 123658
  | 26 => 123684
  | 27 => 123711
  | 28 => 494947 / 4
  | 29 => 123763
  | 30 => 123789
  | 31 => 123816
  | 32 => 123842
  | 33 => 123868
  | 34 => 123895
  | 35 => 123921
  | 36 => 123947
  | 37 => 123974
  | _ => 123974

/-- The upper edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 123026
  | 1 => 123053
  | 2 => 492317 / 4
  | 3 => 123105
  | 4 => 123132
  | 5 => 123158
  | 6 => 123184
  | 7 => 123211
  | 8 => 123237
  | 9 => 123263
  | 10 => 123289
  | 11 => 123316
  | 12 => 123342
  | 13 => 123368
  | 14 => 123395
  | 15 => 123421
  | 16 => 123447
  | 17 => 123474
  | 18 => 123500
  | 19 => 123526
  | 20 => 123553
  | 21 => 123579
  | 22 => 123605
  | 23 => 123632
  | 24 => 123658
  | 25 => 123684
  | 26 => 494845 / 4
  | 27 => 123737
  | 28 => 123763
  | 29 => 123789
  | 30 => 123816
  | 31 => 123842
  | 32 => 495473 / 4
  | 33 => 123895
  | 34 => 123921
  | 35 => 495789 / 4
  | 36 => 123974
  | 37 => 124000
  | _ => 124000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 38 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 124000` (`log 124000 ≤ 12`, `2.7^12 ≥ 124000`). -/
theorem haC_124000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 124000 := by
  have hlog : Real.log 124000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 124000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 124000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[123000, 124000]` segment's band hypothesis: every band `i < 38` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 38 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 38 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[123000, 124000]` SEGMENT: every zero with `123000 ≤ Im ≤ 124000` is on the line. -/
theorem segment_123000_124000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 124000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (123000:ℝ) ≤ ρ.im → ρ.im ≤ 124000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 123000 124000 bndSeg 38 (by norm_num) bndSeg_mono rfl rfl haC_124000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 124000 via the HEIGHT CHAIN**: `[0,123000]` ∘ `[123000,124000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_124000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 124000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 124000 → ρ.re = 1 / 2 := by
  have hγ123000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 123000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 123000 124000
    (AllZeros_h123000.all_nontrivial_zeros_up_to_height_123000_of_bands
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
      hγ123000)
    (segment_123000_124000 hbands hγ)

end AllZeros_h124000
