/-  Height-chain step: all nontrivial zeta zeros up to height 132000 on Re = 1/2 --
    `AllZeros_h131000` + a `[131000, 132000]` SEGMENT certificate (38 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h131000
import RHInBoxT_1d4000000_3999999d4000000_131000_131026
import RHInBoxT_1d4000000_3999999d4000000_131026_131053
import RHInBoxT_1d4000000_3999999d4000000_131053_131079
import RHInBoxT_1d4000000_3999999d4000000_131079_524421d4
import RHInBoxT_1d4000000_3999999d4000000_131105_131132
import RHInBoxT_1d4000000_3999999d4000000_131132_131158
import RHInBoxT_1d4000000_3999999d4000000_131158_131184
import RHInBoxT_1d4000000_3999999d4000000_131184_524845d4
import RHInBoxT_1d4000000_3999999d4000000_131211_131237
import RHInBoxT_1d4000000_3999999d4000000_524947d4_131263
import RHInBoxT_1d4000000_3999999d4000000_131263_131289
import RHInBoxT_1d4000000_3999999d4000000_131289_131316
import RHInBoxT_1d4000000_3999999d4000000_131316_131342
import RHInBoxT_1d4000000_3999999d4000000_131342_131368
import RHInBoxT_1d4000000_3999999d4000000_131368_131395
import RHInBoxT_1d4000000_3999999d4000000_131395_131421
import RHInBoxT_1d4000000_3999999d4000000_525683d4_131447
import RHInBoxT_1d4000000_3999999d4000000_131447_131474
import RHInBoxT_1d4000000_3999999d4000000_525895d4_131500
import RHInBoxT_1d4000000_3999999d4000000_131500_131526
import RHInBoxT_1d4000000_3999999d4000000_131526_131553
import RHInBoxT_1d4000000_3999999d4000000_131553_131579
import RHInBoxT_1d4000000_3999999d4000000_131579_131605
import RHInBoxT_1d4000000_3999999d4000000_131605_526529d4
import RHInBoxT_1d4000000_3999999d4000000_131632_263317d2
import RHInBoxT_1d4000000_3999999d4000000_131658_526737d4
import RHInBoxT_1d4000000_3999999d4000000_131684_131711
import RHInBoxT_1d4000000_3999999d4000000_131711_131737
import RHInBoxT_1d4000000_3999999d4000000_131737_131763
import RHInBoxT_1d4000000_3999999d4000000_527051d4_131789
import RHInBoxT_1d4000000_3999999d4000000_131789_131816
import RHInBoxT_1d4000000_3999999d4000000_131816_527369d4
import RHInBoxT_1d4000000_3999999d4000000_131842_131868
import RHInBoxT_1d4000000_3999999d4000000_131868_131895
import RHInBoxT_1d4000000_3999999d4000000_527579d4_131921
import RHInBoxT_1d4000000_3999999d4000000_131921_527789d4
import RHInBoxT_1d4000000_3999999d4000000_131947_527897d4
import RHInBoxT_1d4000000_3999999d4000000_131974_132000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h132000

/-- The 38-band NOMINAL partition of `[131000, 132000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 131000
  | 1 => 131026
  | 2 => 131053
  | 3 => 131079
  | 4 => 131105
  | 5 => 131132
  | 6 => 131158
  | 7 => 131184
  | 8 => 131211
  | 9 => 131237
  | 10 => 131263
  | 11 => 131289
  | 12 => 131316
  | 13 => 131342
  | 14 => 131368
  | 15 => 131395
  | 16 => 131421
  | 17 => 131447
  | 18 => 131474
  | 19 => 131500
  | 20 => 131526
  | 21 => 131553
  | 22 => 131579
  | 23 => 131605
  | 24 => 131632
  | 25 => 131658
  | 26 => 131684
  | 27 => 131711
  | 28 => 131737
  | 29 => 131763
  | 30 => 131789
  | 31 => 131816
  | 32 => 131842
  | 33 => 131868
  | 34 => 131895
  | 35 => 131921
  | 36 => 131947
  | 37 => 131974
  | 38 => 132000
  | _ => 132000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((131000:ℝ)) ≤ (131026); norm_num
  · show ((131026:ℝ)) ≤ (131053); norm_num
  · show ((131053:ℝ)) ≤ (131079); norm_num
  · show ((131079:ℝ)) ≤ (131105); norm_num
  · show ((131105:ℝ)) ≤ (131132); norm_num
  · show ((131132:ℝ)) ≤ (131158); norm_num
  · show ((131158:ℝ)) ≤ (131184); norm_num
  · show ((131184:ℝ)) ≤ (131211); norm_num
  · show ((131211:ℝ)) ≤ (131237); norm_num
  · show ((131237:ℝ)) ≤ (131263); norm_num
  · show ((131263:ℝ)) ≤ (131289); norm_num
  · show ((131289:ℝ)) ≤ (131316); norm_num
  · show ((131316:ℝ)) ≤ (131342); norm_num
  · show ((131342:ℝ)) ≤ (131368); norm_num
  · show ((131368:ℝ)) ≤ (131395); norm_num
  · show ((131395:ℝ)) ≤ (131421); norm_num
  · show ((131421:ℝ)) ≤ (131447); norm_num
  · show ((131447:ℝ)) ≤ (131474); norm_num
  · show ((131474:ℝ)) ≤ (131500); norm_num
  · show ((131500:ℝ)) ≤ (131526); norm_num
  · show ((131526:ℝ)) ≤ (131553); norm_num
  · show ((131553:ℝ)) ≤ (131579); norm_num
  · show ((131579:ℝ)) ≤ (131605); norm_num
  · show ((131605:ℝ)) ≤ (131632); norm_num
  · show ((131632:ℝ)) ≤ (131658); norm_num
  · show ((131658:ℝ)) ≤ (131684); norm_num
  · show ((131684:ℝ)) ≤ (131711); norm_num
  · show ((131711:ℝ)) ≤ (131737); norm_num
  · show ((131737:ℝ)) ≤ (131763); norm_num
  · show ((131763:ℝ)) ≤ (131789); norm_num
  · show ((131789:ℝ)) ≤ (131816); norm_num
  · show ((131816:ℝ)) ≤ (131842); norm_num
  · show ((131842:ℝ)) ≤ (131868); norm_num
  · show ((131868:ℝ)) ≤ (131895); norm_num
  · show ((131895:ℝ)) ≤ (131921); norm_num
  · show ((131921:ℝ)) ≤ (131947); norm_num
  · show ((131947:ℝ)) ≤ (131974); norm_num
  · show ((131974:ℝ)) ≤ (132000); norm_num
  · show ((132000:ℝ)) ≤ (132000); norm_num
  · exact le_refl _

/-- The lower edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 131000
  | 1 => 131026
  | 2 => 131053
  | 3 => 131079
  | 4 => 131105
  | 5 => 131132
  | 6 => 131158
  | 7 => 131184
  | 8 => 131211
  | 9 => 524947 / 4
  | 10 => 131263
  | 11 => 131289
  | 12 => 131316
  | 13 => 131342
  | 14 => 131368
  | 15 => 131395
  | 16 => 525683 / 4
  | 17 => 131447
  | 18 => 525895 / 4
  | 19 => 131500
  | 20 => 131526
  | 21 => 131553
  | 22 => 131579
  | 23 => 131605
  | 24 => 131632
  | 25 => 131658
  | 26 => 131684
  | 27 => 131711
  | 28 => 131737
  | 29 => 527051 / 4
  | 30 => 131789
  | 31 => 131816
  | 32 => 131842
  | 33 => 131868
  | 34 => 527579 / 4
  | 35 => 131921
  | 36 => 131947
  | 37 => 131974
  | _ => 131974

/-- The upper edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 131026
  | 1 => 131053
  | 2 => 131079
  | 3 => 524421 / 4
  | 4 => 131132
  | 5 => 131158
  | 6 => 131184
  | 7 => 524845 / 4
  | 8 => 131237
  | 9 => 131263
  | 10 => 131289
  | 11 => 131316
  | 12 => 131342
  | 13 => 131368
  | 14 => 131395
  | 15 => 131421
  | 16 => 131447
  | 17 => 131474
  | 18 => 131500
  | 19 => 131526
  | 20 => 131553
  | 21 => 131579
  | 22 => 131605
  | 23 => 526529 / 4
  | 24 => 263317 / 2
  | 25 => 526737 / 4
  | 26 => 131711
  | 27 => 131737
  | 28 => 131763
  | 29 => 131789
  | 30 => 131816
  | 31 => 527369 / 4
  | 32 => 131868
  | 33 => 131895
  | 34 => 131921
  | 35 => 527789 / 4
  | 36 => 527897 / 4
  | 37 => 132000
  | _ => 132000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 38 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 132000` (`log 132000 ≤ 12`, `2.7^12 ≥ 132000`). -/
theorem haC_132000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 132000 := by
  have hlog : Real.log 132000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 132000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 132000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[131000, 132000]` segment's band hypothesis: every band `i < 38` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 38 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 38 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[131000, 132000]` SEGMENT: every zero with `131000 ≤ Im ≤ 132000` is on the line. -/
theorem segment_131000_132000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 132000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (131000:ℝ) ≤ ρ.im → ρ.im ≤ 132000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 131000 132000 bndSeg 38 (by norm_num) bndSeg_mono rfl rfl haC_132000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 132000 via the HEIGHT CHAIN**: `[0,131000]` ∘ `[131000,132000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_132000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 132000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 132000 → ρ.re = 1 / 2 := by
  have hγ131000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 131000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 131000 132000
    (AllZeros_h131000.all_nontrivial_zeros_up_to_height_131000_of_bands
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
      hγ131000)
    (segment_131000_132000 hbands hγ)

end AllZeros_h132000
