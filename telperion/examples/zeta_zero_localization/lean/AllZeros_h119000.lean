/-  Height-chain step: all nontrivial zeta zeros up to height 119000 on Re = 1/2 --
    `AllZeros_h118000` + a `[118000, 119000]` SEGMENT certificate (38 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h118000
import RHInBoxT_1d4000000_3999999d4000000_118000_118026
import RHInBoxT_1d4000000_3999999d4000000_118026_118053
import RHInBoxT_1d4000000_3999999d4000000_118053_472317d4
import RHInBoxT_1d4000000_3999999d4000000_118079_118105
import RHInBoxT_1d4000000_3999999d4000000_118105_118132
import RHInBoxT_1d4000000_3999999d4000000_472527d4_118158
import RHInBoxT_1d4000000_3999999d4000000_118158_118184
import RHInBoxT_1d4000000_3999999d4000000_118184_118211
import RHInBoxT_1d4000000_3999999d4000000_472843d4_118237
import RHInBoxT_1d4000000_3999999d4000000_118237_118263
import RHInBoxT_1d4000000_3999999d4000000_118263_118289
import RHInBoxT_1d4000000_3999999d4000000_118289_473265d4
import RHInBoxT_1d4000000_3999999d4000000_118316_473369d4
import RHInBoxT_1d4000000_3999999d4000000_118342_118368
import RHInBoxT_1d4000000_3999999d4000000_118368_118395
import RHInBoxT_1d4000000_3999999d4000000_118395_118421
import RHInBoxT_1d4000000_3999999d4000000_118421_473789d4
import RHInBoxT_1d4000000_3999999d4000000_118447_118474
import RHInBoxT_1d4000000_3999999d4000000_473895d4_118500
import RHInBoxT_1d4000000_3999999d4000000_118500_118526
import RHInBoxT_1d4000000_3999999d4000000_118526_474213d4
import RHInBoxT_1d4000000_3999999d4000000_118553_118579
import RHInBoxT_1d4000000_3999999d4000000_118579_118605
import RHInBoxT_1d4000000_3999999d4000000_118605_474529d4
import RHInBoxT_1d4000000_3999999d4000000_118632_118658
import RHInBoxT_1d4000000_3999999d4000000_118658_118684
import RHInBoxT_1d4000000_3999999d4000000_118684_118711
import RHInBoxT_1d4000000_3999999d4000000_118711_118737
import RHInBoxT_1d4000000_3999999d4000000_474947d4_118763
import RHInBoxT_1d4000000_3999999d4000000_475051d4_118789
import RHInBoxT_1d4000000_3999999d4000000_118789_118816
import RHInBoxT_1d4000000_3999999d4000000_118816_118842
import RHInBoxT_1d4000000_3999999d4000000_118842_118868
import RHInBoxT_1d4000000_3999999d4000000_118868_118895
import RHInBoxT_1d4000000_3999999d4000000_475579d4_118921
import RHInBoxT_1d4000000_3999999d4000000_118921_118947
import RHInBoxT_1d4000000_3999999d4000000_118947_118974
import RHInBoxT_1d4000000_3999999d4000000_475895d4_476001d4

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h119000

/-- The 38-band NOMINAL partition of `[118000, 119000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 118000
  | 1 => 118026
  | 2 => 118053
  | 3 => 118079
  | 4 => 118105
  | 5 => 118132
  | 6 => 118158
  | 7 => 118184
  | 8 => 118211
  | 9 => 118237
  | 10 => 118263
  | 11 => 118289
  | 12 => 118316
  | 13 => 118342
  | 14 => 118368
  | 15 => 118395
  | 16 => 118421
  | 17 => 118447
  | 18 => 118474
  | 19 => 118500
  | 20 => 118526
  | 21 => 118553
  | 22 => 118579
  | 23 => 118605
  | 24 => 118632
  | 25 => 118658
  | 26 => 118684
  | 27 => 118711
  | 28 => 118737
  | 29 => 118763
  | 30 => 118789
  | 31 => 118816
  | 32 => 118842
  | 33 => 118868
  | 34 => 118895
  | 35 => 118921
  | 36 => 118947
  | 37 => 118974
  | 38 => 119000
  | _ => 119000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((118000:ℝ)) ≤ (118026); norm_num
  · show ((118026:ℝ)) ≤ (118053); norm_num
  · show ((118053:ℝ)) ≤ (118079); norm_num
  · show ((118079:ℝ)) ≤ (118105); norm_num
  · show ((118105:ℝ)) ≤ (118132); norm_num
  · show ((118132:ℝ)) ≤ (118158); norm_num
  · show ((118158:ℝ)) ≤ (118184); norm_num
  · show ((118184:ℝ)) ≤ (118211); norm_num
  · show ((118211:ℝ)) ≤ (118237); norm_num
  · show ((118237:ℝ)) ≤ (118263); norm_num
  · show ((118263:ℝ)) ≤ (118289); norm_num
  · show ((118289:ℝ)) ≤ (118316); norm_num
  · show ((118316:ℝ)) ≤ (118342); norm_num
  · show ((118342:ℝ)) ≤ (118368); norm_num
  · show ((118368:ℝ)) ≤ (118395); norm_num
  · show ((118395:ℝ)) ≤ (118421); norm_num
  · show ((118421:ℝ)) ≤ (118447); norm_num
  · show ((118447:ℝ)) ≤ (118474); norm_num
  · show ((118474:ℝ)) ≤ (118500); norm_num
  · show ((118500:ℝ)) ≤ (118526); norm_num
  · show ((118526:ℝ)) ≤ (118553); norm_num
  · show ((118553:ℝ)) ≤ (118579); norm_num
  · show ((118579:ℝ)) ≤ (118605); norm_num
  · show ((118605:ℝ)) ≤ (118632); norm_num
  · show ((118632:ℝ)) ≤ (118658); norm_num
  · show ((118658:ℝ)) ≤ (118684); norm_num
  · show ((118684:ℝ)) ≤ (118711); norm_num
  · show ((118711:ℝ)) ≤ (118737); norm_num
  · show ((118737:ℝ)) ≤ (118763); norm_num
  · show ((118763:ℝ)) ≤ (118789); norm_num
  · show ((118789:ℝ)) ≤ (118816); norm_num
  · show ((118816:ℝ)) ≤ (118842); norm_num
  · show ((118842:ℝ)) ≤ (118868); norm_num
  · show ((118868:ℝ)) ≤ (118895); norm_num
  · show ((118895:ℝ)) ≤ (118921); norm_num
  · show ((118921:ℝ)) ≤ (118947); norm_num
  · show ((118947:ℝ)) ≤ (118974); norm_num
  · show ((118974:ℝ)) ≤ (119000); norm_num
  · show ((119000:ℝ)) ≤ (119000); norm_num
  · exact le_refl _

/-- The lower edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 118000
  | 1 => 118026
  | 2 => 118053
  | 3 => 118079
  | 4 => 118105
  | 5 => 472527 / 4
  | 6 => 118158
  | 7 => 118184
  | 8 => 472843 / 4
  | 9 => 118237
  | 10 => 118263
  | 11 => 118289
  | 12 => 118316
  | 13 => 118342
  | 14 => 118368
  | 15 => 118395
  | 16 => 118421
  | 17 => 118447
  | 18 => 473895 / 4
  | 19 => 118500
  | 20 => 118526
  | 21 => 118553
  | 22 => 118579
  | 23 => 118605
  | 24 => 118632
  | 25 => 118658
  | 26 => 118684
  | 27 => 118711
  | 28 => 474947 / 4
  | 29 => 475051 / 4
  | 30 => 118789
  | 31 => 118816
  | 32 => 118842
  | 33 => 118868
  | 34 => 475579 / 4
  | 35 => 118921
  | 36 => 118947
  | 37 => 475895 / 4
  | _ => 475895 / 4

/-- The upper edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 118026
  | 1 => 118053
  | 2 => 472317 / 4
  | 3 => 118105
  | 4 => 118132
  | 5 => 118158
  | 6 => 118184
  | 7 => 118211
  | 8 => 118237
  | 9 => 118263
  | 10 => 118289
  | 11 => 473265 / 4
  | 12 => 473369 / 4
  | 13 => 118368
  | 14 => 118395
  | 15 => 118421
  | 16 => 473789 / 4
  | 17 => 118474
  | 18 => 118500
  | 19 => 118526
  | 20 => 474213 / 4
  | 21 => 118579
  | 22 => 118605
  | 23 => 474529 / 4
  | 24 => 118658
  | 25 => 118684
  | 26 => 118711
  | 27 => 118737
  | 28 => 118763
  | 29 => 118789
  | 30 => 118816
  | 31 => 118842
  | 32 => 118868
  | 33 => 118895
  | 34 => 118921
  | 35 => 118947
  | 36 => 118974
  | 37 => 476001 / 4
  | _ => 476001 / 4

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 38 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 119000` (`log 119000 ≤ 12`, `2.7^12 ≥ 119000`). -/
theorem haC_119000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 119000 := by
  have hlog : Real.log 119000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 119000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 119000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[118000, 119000]` segment's band hypothesis: every band `i < 38` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 38 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 38 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[118000, 119000]` SEGMENT: every zero with `118000 ≤ Im ≤ 119000` is on the line. -/
theorem segment_118000_119000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 119000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (118000:ℝ) ≤ ρ.im → ρ.im ≤ 119000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 118000 119000 bndSeg 38 (by norm_num) bndSeg_mono rfl rfl haC_119000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 119000 via the HEIGHT CHAIN**: `[0,118000]` ∘ `[118000,119000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_119000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 119000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 119000 → ρ.re = 1 / 2 := by
  have hγ118000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 118000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 118000 119000
    (AllZeros_h118000.all_nontrivial_zeros_up_to_height_118000_of_bands
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
      hγ118000)
    (segment_118000_119000 hbands hγ)

end AllZeros_h119000
