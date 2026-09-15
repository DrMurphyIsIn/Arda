/-  Height-chain step: all nontrivial zeta zeros up to height 103000 on Re = 1/2 --
    `AllZeros_h102000` + a `[102000, 103000]` SEGMENT certificate (38 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h102000
import RHInBoxT_1d4000000_3999999d4000000_407999d4_102026
import RHInBoxT_1d4000000_3999999d4000000_102026_102053
import RHInBoxT_1d4000000_3999999d4000000_102053_102079
import RHInBoxT_1d4000000_3999999d4000000_102079_102105
import RHInBoxT_1d4000000_3999999d4000000_102105_102132
import RHInBoxT_1d4000000_3999999d4000000_102132_102158
import RHInBoxT_1d4000000_3999999d4000000_204315d2_102184
import RHInBoxT_1d4000000_3999999d4000000_408735d4_102211
import RHInBoxT_1d4000000_3999999d4000000_102211_102237
import RHInBoxT_1d4000000_3999999d4000000_102237_102263
import RHInBoxT_1d4000000_3999999d4000000_102263_102289
import RHInBoxT_1d4000000_3999999d4000000_102289_102316
import RHInBoxT_1d4000000_3999999d4000000_409263d4_102342
import RHInBoxT_1d4000000_3999999d4000000_102342_102368
import RHInBoxT_1d4000000_3999999d4000000_102368_102395
import RHInBoxT_1d4000000_3999999d4000000_102395_409685d4
import RHInBoxT_1d4000000_3999999d4000000_102421_102447
import RHInBoxT_1d4000000_3999999d4000000_102447_102474
import RHInBoxT_1d4000000_3999999d4000000_102474_102500
import RHInBoxT_1d4000000_3999999d4000000_102500_102526
import RHInBoxT_1d4000000_3999999d4000000_102526_102553
import RHInBoxT_1d4000000_3999999d4000000_102553_102579
import RHInBoxT_1d4000000_3999999d4000000_102579_102605
import RHInBoxT_1d4000000_3999999d4000000_102605_102632
import RHInBoxT_1d4000000_3999999d4000000_102632_102658
import RHInBoxT_1d4000000_3999999d4000000_102658_102684
import RHInBoxT_1d4000000_3999999d4000000_102684_102711
import RHInBoxT_1d4000000_3999999d4000000_102711_102737
import RHInBoxT_1d4000000_3999999d4000000_102737_102763
import RHInBoxT_1d4000000_3999999d4000000_102763_102789
import RHInBoxT_1d4000000_3999999d4000000_102789_102816
import RHInBoxT_1d4000000_3999999d4000000_411263d4_102842
import RHInBoxT_1d4000000_3999999d4000000_102842_205737d2
import RHInBoxT_1d4000000_3999999d4000000_102868_205791d2
import RHInBoxT_1d4000000_3999999d4000000_102895_102921
import RHInBoxT_1d4000000_3999999d4000000_102921_102947
import RHInBoxT_1d4000000_3999999d4000000_411787d4_102974
import RHInBoxT_1d4000000_3999999d4000000_102974_103000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h103000

/-- The 38-band NOMINAL partition of `[102000, 103000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 102000
  | 1 => 102026
  | 2 => 102053
  | 3 => 102079
  | 4 => 102105
  | 5 => 102132
  | 6 => 102158
  | 7 => 102184
  | 8 => 102211
  | 9 => 102237
  | 10 => 102263
  | 11 => 102289
  | 12 => 102316
  | 13 => 102342
  | 14 => 102368
  | 15 => 102395
  | 16 => 102421
  | 17 => 102447
  | 18 => 102474
  | 19 => 102500
  | 20 => 102526
  | 21 => 102553
  | 22 => 102579
  | 23 => 102605
  | 24 => 102632
  | 25 => 102658
  | 26 => 102684
  | 27 => 102711
  | 28 => 102737
  | 29 => 102763
  | 30 => 102789
  | 31 => 102816
  | 32 => 102842
  | 33 => 102868
  | 34 => 102895
  | 35 => 102921
  | 36 => 102947
  | 37 => 102974
  | 38 => 103000
  | _ => 103000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((102000:ℝ)) ≤ (102026); norm_num
  · show ((102026:ℝ)) ≤ (102053); norm_num
  · show ((102053:ℝ)) ≤ (102079); norm_num
  · show ((102079:ℝ)) ≤ (102105); norm_num
  · show ((102105:ℝ)) ≤ (102132); norm_num
  · show ((102132:ℝ)) ≤ (102158); norm_num
  · show ((102158:ℝ)) ≤ (102184); norm_num
  · show ((102184:ℝ)) ≤ (102211); norm_num
  · show ((102211:ℝ)) ≤ (102237); norm_num
  · show ((102237:ℝ)) ≤ (102263); norm_num
  · show ((102263:ℝ)) ≤ (102289); norm_num
  · show ((102289:ℝ)) ≤ (102316); norm_num
  · show ((102316:ℝ)) ≤ (102342); norm_num
  · show ((102342:ℝ)) ≤ (102368); norm_num
  · show ((102368:ℝ)) ≤ (102395); norm_num
  · show ((102395:ℝ)) ≤ (102421); norm_num
  · show ((102421:ℝ)) ≤ (102447); norm_num
  · show ((102447:ℝ)) ≤ (102474); norm_num
  · show ((102474:ℝ)) ≤ (102500); norm_num
  · show ((102500:ℝ)) ≤ (102526); norm_num
  · show ((102526:ℝ)) ≤ (102553); norm_num
  · show ((102553:ℝ)) ≤ (102579); norm_num
  · show ((102579:ℝ)) ≤ (102605); norm_num
  · show ((102605:ℝ)) ≤ (102632); norm_num
  · show ((102632:ℝ)) ≤ (102658); norm_num
  · show ((102658:ℝ)) ≤ (102684); norm_num
  · show ((102684:ℝ)) ≤ (102711); norm_num
  · show ((102711:ℝ)) ≤ (102737); norm_num
  · show ((102737:ℝ)) ≤ (102763); norm_num
  · show ((102763:ℝ)) ≤ (102789); norm_num
  · show ((102789:ℝ)) ≤ (102816); norm_num
  · show ((102816:ℝ)) ≤ (102842); norm_num
  · show ((102842:ℝ)) ≤ (102868); norm_num
  · show ((102868:ℝ)) ≤ (102895); norm_num
  · show ((102895:ℝ)) ≤ (102921); norm_num
  · show ((102921:ℝ)) ≤ (102947); norm_num
  · show ((102947:ℝ)) ≤ (102974); norm_num
  · show ((102974:ℝ)) ≤ (103000); norm_num
  · show ((103000:ℝ)) ≤ (103000); norm_num
  · exact le_refl _

/-- The lower edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 407999 / 4
  | 1 => 102026
  | 2 => 102053
  | 3 => 102079
  | 4 => 102105
  | 5 => 102132
  | 6 => 204315 / 2
  | 7 => 408735 / 4
  | 8 => 102211
  | 9 => 102237
  | 10 => 102263
  | 11 => 102289
  | 12 => 409263 / 4
  | 13 => 102342
  | 14 => 102368
  | 15 => 102395
  | 16 => 102421
  | 17 => 102447
  | 18 => 102474
  | 19 => 102500
  | 20 => 102526
  | 21 => 102553
  | 22 => 102579
  | 23 => 102605
  | 24 => 102632
  | 25 => 102658
  | 26 => 102684
  | 27 => 102711
  | 28 => 102737
  | 29 => 102763
  | 30 => 102789
  | 31 => 411263 / 4
  | 32 => 102842
  | 33 => 102868
  | 34 => 102895
  | 35 => 102921
  | 36 => 411787 / 4
  | 37 => 102974
  | _ => 102974

/-- The upper edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 102026
  | 1 => 102053
  | 2 => 102079
  | 3 => 102105
  | 4 => 102132
  | 5 => 102158
  | 6 => 102184
  | 7 => 102211
  | 8 => 102237
  | 9 => 102263
  | 10 => 102289
  | 11 => 102316
  | 12 => 102342
  | 13 => 102368
  | 14 => 102395
  | 15 => 409685 / 4
  | 16 => 102447
  | 17 => 102474
  | 18 => 102500
  | 19 => 102526
  | 20 => 102553
  | 21 => 102579
  | 22 => 102605
  | 23 => 102632
  | 24 => 102658
  | 25 => 102684
  | 26 => 102711
  | 27 => 102737
  | 28 => 102763
  | 29 => 102789
  | 30 => 102816
  | 31 => 102842
  | 32 => 205737 / 2
  | 33 => 205791 / 2
  | 34 => 102921
  | 35 => 102947
  | 36 => 102974
  | 37 => 103000
  | _ => 103000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 38 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 103000` (`log 103000 ≤ 12`, `2.7^12 ≥ 103000`). -/
theorem haC_103000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 103000 := by
  have hlog : Real.log 103000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 103000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 103000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[102000, 103000]` segment's band hypothesis: every band `i < 38` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 38 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 38 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[102000, 103000]` SEGMENT: every zero with `102000 ≤ Im ≤ 103000` is on the line. -/
theorem segment_102000_103000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 103000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (102000:ℝ) ≤ ρ.im → ρ.im ≤ 103000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 102000 103000 bndSeg 38 (by norm_num) bndSeg_mono rfl rfl haC_103000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 103000 via the HEIGHT CHAIN**: `[0,102000]` ∘ `[102000,103000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_103000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 103000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 103000 → ρ.re = 1 / 2 := by
  have hγ102000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 102000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 102000 103000
    (AllZeros_h102000.all_nontrivial_zeros_up_to_height_102000_of_bands
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
      hγ102000)
    (segment_102000_103000 hbands hγ)

end AllZeros_h103000
