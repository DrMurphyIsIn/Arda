/-  Height-chain step: all nontrivial zeta zeros up to height 127000 on Re = 1/2 --
    `AllZeros_h126000` + a `[126000, 127000]` SEGMENT certificate (38 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h126000
import RHInBoxT_1d4000000_3999999d4000000_126000_126026
import RHInBoxT_1d4000000_3999999d4000000_126026_126053
import RHInBoxT_1d4000000_3999999d4000000_504211d4_126079
import RHInBoxT_1d4000000_3999999d4000000_504315d4_126105
import RHInBoxT_1d4000000_3999999d4000000_126105_126132
import RHInBoxT_1d4000000_3999999d4000000_504527d4_126158
import RHInBoxT_1d4000000_3999999d4000000_126158_504737d4
import RHInBoxT_1d4000000_3999999d4000000_126184_126211
import RHInBoxT_1d4000000_3999999d4000000_126211_126237
import RHInBoxT_1d4000000_3999999d4000000_504947d4_505053d4
import RHInBoxT_1d4000000_3999999d4000000_126263_126289
import RHInBoxT_1d4000000_3999999d4000000_126289_126316
import RHInBoxT_1d4000000_3999999d4000000_126316_505369d4
import RHInBoxT_1d4000000_3999999d4000000_126342_126368
import RHInBoxT_1d4000000_3999999d4000000_126368_126395
import RHInBoxT_1d4000000_3999999d4000000_126395_126421
import RHInBoxT_1d4000000_3999999d4000000_126421_126447
import RHInBoxT_1d4000000_3999999d4000000_126447_126474
import RHInBoxT_1d4000000_3999999d4000000_126474_126500
import RHInBoxT_1d4000000_3999999d4000000_126500_126526
import RHInBoxT_1d4000000_3999999d4000000_126526_126553
import RHInBoxT_1d4000000_3999999d4000000_126553_126579
import RHInBoxT_1d4000000_3999999d4000000_506315d4_126605
import RHInBoxT_1d4000000_3999999d4000000_126605_126632
import RHInBoxT_1d4000000_3999999d4000000_126632_126658
import RHInBoxT_1d4000000_3999999d4000000_126658_506737d4
import RHInBoxT_1d4000000_3999999d4000000_126684_126711
import RHInBoxT_1d4000000_3999999d4000000_126711_126737
import RHInBoxT_1d4000000_3999999d4000000_126737_126763
import RHInBoxT_1d4000000_3999999d4000000_507051d4_126789
import RHInBoxT_1d4000000_3999999d4000000_126789_126816
import RHInBoxT_1d4000000_3999999d4000000_126816_126842
import RHInBoxT_1d4000000_3999999d4000000_126842_126868
import RHInBoxT_1d4000000_3999999d4000000_126868_126895
import RHInBoxT_1d4000000_3999999d4000000_126895_126921
import RHInBoxT_1d4000000_3999999d4000000_507683d4_507789d4
import RHInBoxT_1d4000000_3999999d4000000_126947_126974
import RHInBoxT_1d4000000_3999999d4000000_126974_127000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h127000

/-- The 38-band NOMINAL partition of `[126000, 127000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 126000
  | 1 => 126026
  | 2 => 126053
  | 3 => 126079
  | 4 => 126105
  | 5 => 126132
  | 6 => 126158
  | 7 => 126184
  | 8 => 126211
  | 9 => 126237
  | 10 => 126263
  | 11 => 126289
  | 12 => 126316
  | 13 => 126342
  | 14 => 126368
  | 15 => 126395
  | 16 => 126421
  | 17 => 126447
  | 18 => 126474
  | 19 => 126500
  | 20 => 126526
  | 21 => 126553
  | 22 => 126579
  | 23 => 126605
  | 24 => 126632
  | 25 => 126658
  | 26 => 126684
  | 27 => 126711
  | 28 => 126737
  | 29 => 126763
  | 30 => 126789
  | 31 => 126816
  | 32 => 126842
  | 33 => 126868
  | 34 => 126895
  | 35 => 126921
  | 36 => 126947
  | 37 => 126974
  | 38 => 127000
  | _ => 127000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((126000:ℝ)) ≤ (126026); norm_num
  · show ((126026:ℝ)) ≤ (126053); norm_num
  · show ((126053:ℝ)) ≤ (126079); norm_num
  · show ((126079:ℝ)) ≤ (126105); norm_num
  · show ((126105:ℝ)) ≤ (126132); norm_num
  · show ((126132:ℝ)) ≤ (126158); norm_num
  · show ((126158:ℝ)) ≤ (126184); norm_num
  · show ((126184:ℝ)) ≤ (126211); norm_num
  · show ((126211:ℝ)) ≤ (126237); norm_num
  · show ((126237:ℝ)) ≤ (126263); norm_num
  · show ((126263:ℝ)) ≤ (126289); norm_num
  · show ((126289:ℝ)) ≤ (126316); norm_num
  · show ((126316:ℝ)) ≤ (126342); norm_num
  · show ((126342:ℝ)) ≤ (126368); norm_num
  · show ((126368:ℝ)) ≤ (126395); norm_num
  · show ((126395:ℝ)) ≤ (126421); norm_num
  · show ((126421:ℝ)) ≤ (126447); norm_num
  · show ((126447:ℝ)) ≤ (126474); norm_num
  · show ((126474:ℝ)) ≤ (126500); norm_num
  · show ((126500:ℝ)) ≤ (126526); norm_num
  · show ((126526:ℝ)) ≤ (126553); norm_num
  · show ((126553:ℝ)) ≤ (126579); norm_num
  · show ((126579:ℝ)) ≤ (126605); norm_num
  · show ((126605:ℝ)) ≤ (126632); norm_num
  · show ((126632:ℝ)) ≤ (126658); norm_num
  · show ((126658:ℝ)) ≤ (126684); norm_num
  · show ((126684:ℝ)) ≤ (126711); norm_num
  · show ((126711:ℝ)) ≤ (126737); norm_num
  · show ((126737:ℝ)) ≤ (126763); norm_num
  · show ((126763:ℝ)) ≤ (126789); norm_num
  · show ((126789:ℝ)) ≤ (126816); norm_num
  · show ((126816:ℝ)) ≤ (126842); norm_num
  · show ((126842:ℝ)) ≤ (126868); norm_num
  · show ((126868:ℝ)) ≤ (126895); norm_num
  · show ((126895:ℝ)) ≤ (126921); norm_num
  · show ((126921:ℝ)) ≤ (126947); norm_num
  · show ((126947:ℝ)) ≤ (126974); norm_num
  · show ((126974:ℝ)) ≤ (127000); norm_num
  · show ((127000:ℝ)) ≤ (127000); norm_num
  · exact le_refl _

/-- The lower edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 126000
  | 1 => 126026
  | 2 => 504211 / 4
  | 3 => 504315 / 4
  | 4 => 126105
  | 5 => 504527 / 4
  | 6 => 126158
  | 7 => 126184
  | 8 => 126211
  | 9 => 504947 / 4
  | 10 => 126263
  | 11 => 126289
  | 12 => 126316
  | 13 => 126342
  | 14 => 126368
  | 15 => 126395
  | 16 => 126421
  | 17 => 126447
  | 18 => 126474
  | 19 => 126500
  | 20 => 126526
  | 21 => 126553
  | 22 => 506315 / 4
  | 23 => 126605
  | 24 => 126632
  | 25 => 126658
  | 26 => 126684
  | 27 => 126711
  | 28 => 126737
  | 29 => 507051 / 4
  | 30 => 126789
  | 31 => 126816
  | 32 => 126842
  | 33 => 126868
  | 34 => 126895
  | 35 => 507683 / 4
  | 36 => 126947
  | 37 => 126974
  | _ => 126974

/-- The upper edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 126026
  | 1 => 126053
  | 2 => 126079
  | 3 => 126105
  | 4 => 126132
  | 5 => 126158
  | 6 => 504737 / 4
  | 7 => 126211
  | 8 => 126237
  | 9 => 505053 / 4
  | 10 => 126289
  | 11 => 126316
  | 12 => 505369 / 4
  | 13 => 126368
  | 14 => 126395
  | 15 => 126421
  | 16 => 126447
  | 17 => 126474
  | 18 => 126500
  | 19 => 126526
  | 20 => 126553
  | 21 => 126579
  | 22 => 126605
  | 23 => 126632
  | 24 => 126658
  | 25 => 506737 / 4
  | 26 => 126711
  | 27 => 126737
  | 28 => 126763
  | 29 => 126789
  | 30 => 126816
  | 31 => 126842
  | 32 => 126868
  | 33 => 126895
  | 34 => 126921
  | 35 => 507789 / 4
  | 36 => 126974
  | 37 => 127000
  | _ => 127000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 38 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 127000` (`log 127000 ≤ 12`, `2.7^12 ≥ 127000`). -/
theorem haC_127000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 127000 := by
  have hlog : Real.log 127000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 127000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 127000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[126000, 127000]` segment's band hypothesis: every band `i < 38` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 38 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 38 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[126000, 127000]` SEGMENT: every zero with `126000 ≤ Im ≤ 127000` is on the line. -/
theorem segment_126000_127000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 127000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (126000:ℝ) ≤ ρ.im → ρ.im ≤ 127000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 126000 127000 bndSeg 38 (by norm_num) bndSeg_mono rfl rfl haC_127000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 127000 via the HEIGHT CHAIN**: `[0,126000]` ∘ `[126000,127000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_127000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 127000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 127000 → ρ.re = 1 / 2 := by
  have hγ126000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 126000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 126000 127000
    (AllZeros_h126000.all_nontrivial_zeros_up_to_height_126000_of_bands
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
      hγ126000)
    (segment_126000_127000 hbands hγ)

end AllZeros_h127000
