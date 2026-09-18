/-  Height-chain step: all nontrivial zeta zeros up to height 104000 on Re = 1/2 --
    `AllZeros_h103000` + a `[103000, 104000]` SEGMENT certificate (38 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h103000
import RHInBoxT_1d4000000_3999999d4000000_103000_103026
import RHInBoxT_1d4000000_3999999d4000000_103026_412213d4
import RHInBoxT_1d4000000_3999999d4000000_103053_103079
import RHInBoxT_1d4000000_3999999d4000000_103079_103105
import RHInBoxT_1d4000000_3999999d4000000_103105_103132
import RHInBoxT_1d4000000_3999999d4000000_412527d4_103158
import RHInBoxT_1d4000000_3999999d4000000_103158_103184
import RHInBoxT_1d4000000_3999999d4000000_103184_103211
import RHInBoxT_1d4000000_3999999d4000000_103211_103237
import RHInBoxT_1d4000000_3999999d4000000_103237_103263
import RHInBoxT_1d4000000_3999999d4000000_103263_103289
import RHInBoxT_1d4000000_3999999d4000000_413155d4_103316
import RHInBoxT_1d4000000_3999999d4000000_103316_103342
import RHInBoxT_1d4000000_3999999d4000000_103342_103368
import RHInBoxT_1d4000000_3999999d4000000_103368_103395
import RHInBoxT_1d4000000_3999999d4000000_206789d2_103421
import RHInBoxT_1d4000000_3999999d4000000_103421_103447
import RHInBoxT_1d4000000_3999999d4000000_413787d4_413897d4
import RHInBoxT_1d4000000_3999999d4000000_103474_103500
import RHInBoxT_1d4000000_3999999d4000000_103500_103526
import RHInBoxT_1d4000000_3999999d4000000_103526_103553
import RHInBoxT_1d4000000_3999999d4000000_103553_414317d4
import RHInBoxT_1d4000000_3999999d4000000_103579_103605
import RHInBoxT_1d4000000_3999999d4000000_414419d4_103632
import RHInBoxT_1d4000000_3999999d4000000_414527d4_103658
import RHInBoxT_1d4000000_3999999d4000000_103658_103684
import RHInBoxT_1d4000000_3999999d4000000_414735d4_103711
import RHInBoxT_1d4000000_3999999d4000000_103711_103737
import RHInBoxT_1d4000000_3999999d4000000_414947d4_103763
import RHInBoxT_1d4000000_3999999d4000000_103763_103789
import RHInBoxT_1d4000000_3999999d4000000_103789_103816
import RHInBoxT_1d4000000_3999999d4000000_103816_103842
import RHInBoxT_1d4000000_3999999d4000000_103842_103868
import RHInBoxT_1d4000000_3999999d4000000_103868_103895
import RHInBoxT_1d4000000_3999999d4000000_103895_415685d4
import RHInBoxT_1d4000000_3999999d4000000_103921_103947
import RHInBoxT_1d4000000_3999999d4000000_103947_103974
import RHInBoxT_1d4000000_3999999d4000000_103974_104000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h104000

/-- The 38-band NOMINAL partition of `[103000, 104000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 103000
  | 1 => 103026
  | 2 => 103053
  | 3 => 103079
  | 4 => 103105
  | 5 => 103132
  | 6 => 103158
  | 7 => 103184
  | 8 => 103211
  | 9 => 103237
  | 10 => 103263
  | 11 => 103289
  | 12 => 103316
  | 13 => 103342
  | 14 => 103368
  | 15 => 103395
  | 16 => 103421
  | 17 => 103447
  | 18 => 103474
  | 19 => 103500
  | 20 => 103526
  | 21 => 103553
  | 22 => 103579
  | 23 => 103605
  | 24 => 103632
  | 25 => 103658
  | 26 => 103684
  | 27 => 103711
  | 28 => 103737
  | 29 => 103763
  | 30 => 103789
  | 31 => 103816
  | 32 => 103842
  | 33 => 103868
  | 34 => 103895
  | 35 => 103921
  | 36 => 103947
  | 37 => 103974
  | 38 => 104000
  | _ => 104000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((103000:ℝ)) ≤ (103026); norm_num
  · show ((103026:ℝ)) ≤ (103053); norm_num
  · show ((103053:ℝ)) ≤ (103079); norm_num
  · show ((103079:ℝ)) ≤ (103105); norm_num
  · show ((103105:ℝ)) ≤ (103132); norm_num
  · show ((103132:ℝ)) ≤ (103158); norm_num
  · show ((103158:ℝ)) ≤ (103184); norm_num
  · show ((103184:ℝ)) ≤ (103211); norm_num
  · show ((103211:ℝ)) ≤ (103237); norm_num
  · show ((103237:ℝ)) ≤ (103263); norm_num
  · show ((103263:ℝ)) ≤ (103289); norm_num
  · show ((103289:ℝ)) ≤ (103316); norm_num
  · show ((103316:ℝ)) ≤ (103342); norm_num
  · show ((103342:ℝ)) ≤ (103368); norm_num
  · show ((103368:ℝ)) ≤ (103395); norm_num
  · show ((103395:ℝ)) ≤ (103421); norm_num
  · show ((103421:ℝ)) ≤ (103447); norm_num
  · show ((103447:ℝ)) ≤ (103474); norm_num
  · show ((103474:ℝ)) ≤ (103500); norm_num
  · show ((103500:ℝ)) ≤ (103526); norm_num
  · show ((103526:ℝ)) ≤ (103553); norm_num
  · show ((103553:ℝ)) ≤ (103579); norm_num
  · show ((103579:ℝ)) ≤ (103605); norm_num
  · show ((103605:ℝ)) ≤ (103632); norm_num
  · show ((103632:ℝ)) ≤ (103658); norm_num
  · show ((103658:ℝ)) ≤ (103684); norm_num
  · show ((103684:ℝ)) ≤ (103711); norm_num
  · show ((103711:ℝ)) ≤ (103737); norm_num
  · show ((103737:ℝ)) ≤ (103763); norm_num
  · show ((103763:ℝ)) ≤ (103789); norm_num
  · show ((103789:ℝ)) ≤ (103816); norm_num
  · show ((103816:ℝ)) ≤ (103842); norm_num
  · show ((103842:ℝ)) ≤ (103868); norm_num
  · show ((103868:ℝ)) ≤ (103895); norm_num
  · show ((103895:ℝ)) ≤ (103921); norm_num
  · show ((103921:ℝ)) ≤ (103947); norm_num
  · show ((103947:ℝ)) ≤ (103974); norm_num
  · show ((103974:ℝ)) ≤ (104000); norm_num
  · show ((104000:ℝ)) ≤ (104000); norm_num
  · exact le_refl _

/-- The lower edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 103000
  | 1 => 103026
  | 2 => 103053
  | 3 => 103079
  | 4 => 103105
  | 5 => 412527 / 4
  | 6 => 103158
  | 7 => 103184
  | 8 => 103211
  | 9 => 103237
  | 10 => 103263
  | 11 => 413155 / 4
  | 12 => 103316
  | 13 => 103342
  | 14 => 103368
  | 15 => 206789 / 2
  | 16 => 103421
  | 17 => 413787 / 4
  | 18 => 103474
  | 19 => 103500
  | 20 => 103526
  | 21 => 103553
  | 22 => 103579
  | 23 => 414419 / 4
  | 24 => 414527 / 4
  | 25 => 103658
  | 26 => 414735 / 4
  | 27 => 103711
  | 28 => 414947 / 4
  | 29 => 103763
  | 30 => 103789
  | 31 => 103816
  | 32 => 103842
  | 33 => 103868
  | 34 => 103895
  | 35 => 103921
  | 36 => 103947
  | 37 => 103974
  | _ => 103974

/-- The upper edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 103026
  | 1 => 412213 / 4
  | 2 => 103079
  | 3 => 103105
  | 4 => 103132
  | 5 => 103158
  | 6 => 103184
  | 7 => 103211
  | 8 => 103237
  | 9 => 103263
  | 10 => 103289
  | 11 => 103316
  | 12 => 103342
  | 13 => 103368
  | 14 => 103395
  | 15 => 103421
  | 16 => 103447
  | 17 => 413897 / 4
  | 18 => 103500
  | 19 => 103526
  | 20 => 103553
  | 21 => 414317 / 4
  | 22 => 103605
  | 23 => 103632
  | 24 => 103658
  | 25 => 103684
  | 26 => 103711
  | 27 => 103737
  | 28 => 103763
  | 29 => 103789
  | 30 => 103816
  | 31 => 103842
  | 32 => 103868
  | 33 => 103895
  | 34 => 415685 / 4
  | 35 => 103947
  | 36 => 103974
  | 37 => 104000
  | _ => 104000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 38 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 104000` (`log 104000 ≤ 12`, `2.7^12 ≥ 104000`). -/
theorem haC_104000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 104000 := by
  have hlog : Real.log 104000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 104000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 104000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[103000, 104000]` segment's band hypothesis: every band `i < 38` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 38 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 38 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[103000, 104000]` SEGMENT: every zero with `103000 ≤ Im ≤ 104000` is on the line. -/
theorem segment_103000_104000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 104000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (103000:ℝ) ≤ ρ.im → ρ.im ≤ 104000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 103000 104000 bndSeg 38 (by norm_num) bndSeg_mono rfl rfl haC_104000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 104000 via the HEIGHT CHAIN**: `[0,103000]` ∘ `[103000,104000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_104000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 104000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 104000 → ρ.re = 1 / 2 := by
  have hγ103000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 103000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 103000 104000
    (AllZeros_h103000.all_nontrivial_zeros_up_to_height_103000_of_bands
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
      hγ103000)
    (segment_103000_104000 hbands hγ)

end AllZeros_h104000
