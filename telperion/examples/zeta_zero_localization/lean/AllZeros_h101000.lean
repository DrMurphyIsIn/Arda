/-  Height-chain step: all nontrivial zeta zeros up to height 101000 on Re = 1/2 --
    `AllZeros_h100000` + a `[100000, 101000]` SEGMENT certificate (38 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h100000
import RHInBoxT_1d4000000_3999999d4000000_100000_100026
import RHInBoxT_1d4000000_3999999d4000000_100026_400213d4
import RHInBoxT_1d4000000_3999999d4000000_100053_400317d4
import RHInBoxT_1d4000000_3999999d4000000_100079_100105
import RHInBoxT_1d4000000_3999999d4000000_100105_100132
import RHInBoxT_1d4000000_3999999d4000000_100132_100158
import RHInBoxT_1d4000000_3999999d4000000_100158_400737d4
import RHInBoxT_1d4000000_3999999d4000000_100184_100211
import RHInBoxT_1d4000000_3999999d4000000_100211_100237
import RHInBoxT_1d4000000_3999999d4000000_400947d4_100263
import RHInBoxT_1d4000000_3999999d4000000_100263_100289
import RHInBoxT_1d4000000_3999999d4000000_401155d4_100316
import RHInBoxT_1d4000000_3999999d4000000_100316_100342
import RHInBoxT_1d4000000_3999999d4000000_100342_100368
import RHInBoxT_1d4000000_3999999d4000000_100368_100395
import RHInBoxT_1d4000000_3999999d4000000_100395_401685d4
import RHInBoxT_1d4000000_3999999d4000000_100421_100447
import RHInBoxT_1d4000000_3999999d4000000_100447_100474
import RHInBoxT_1d4000000_3999999d4000000_100474_100500
import RHInBoxT_1d4000000_3999999d4000000_100500_100526
import RHInBoxT_1d4000000_3999999d4000000_100526_100553
import RHInBoxT_1d4000000_3999999d4000000_100553_100579
import RHInBoxT_1d4000000_3999999d4000000_100579_100605
import RHInBoxT_1d4000000_3999999d4000000_402419d4_100632
import RHInBoxT_1d4000000_3999999d4000000_100632_100658
import RHInBoxT_1d4000000_3999999d4000000_100658_100684
import RHInBoxT_1d4000000_3999999d4000000_100684_100711
import RHInBoxT_1d4000000_3999999d4000000_100711_100737
import RHInBoxT_1d4000000_3999999d4000000_100737_100763
import RHInBoxT_1d4000000_3999999d4000000_100763_403157d4
import RHInBoxT_1d4000000_3999999d4000000_100789_100816
import RHInBoxT_1d4000000_3999999d4000000_100816_100842
import RHInBoxT_1d4000000_3999999d4000000_100842_100868
import RHInBoxT_1d4000000_3999999d4000000_100868_100895
import RHInBoxT_1d4000000_3999999d4000000_100895_403685d4
import RHInBoxT_1d4000000_3999999d4000000_100921_100947
import RHInBoxT_1d4000000_3999999d4000000_100947_100974
import RHInBoxT_1d4000000_3999999d4000000_100974_101000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h101000

/-- The 38-band NOMINAL partition of `[100000, 101000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 100000
  | 1 => 100026
  | 2 => 100053
  | 3 => 100079
  | 4 => 100105
  | 5 => 100132
  | 6 => 100158
  | 7 => 100184
  | 8 => 100211
  | 9 => 100237
  | 10 => 100263
  | 11 => 100289
  | 12 => 100316
  | 13 => 100342
  | 14 => 100368
  | 15 => 100395
  | 16 => 100421
  | 17 => 100447
  | 18 => 100474
  | 19 => 100500
  | 20 => 100526
  | 21 => 100553
  | 22 => 100579
  | 23 => 100605
  | 24 => 100632
  | 25 => 100658
  | 26 => 100684
  | 27 => 100711
  | 28 => 100737
  | 29 => 100763
  | 30 => 100789
  | 31 => 100816
  | 32 => 100842
  | 33 => 100868
  | 34 => 100895
  | 35 => 100921
  | 36 => 100947
  | 37 => 100974
  | 38 => 101000
  | _ => 101000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((100000:ℝ)) ≤ (100026); norm_num
  · show ((100026:ℝ)) ≤ (100053); norm_num
  · show ((100053:ℝ)) ≤ (100079); norm_num
  · show ((100079:ℝ)) ≤ (100105); norm_num
  · show ((100105:ℝ)) ≤ (100132); norm_num
  · show ((100132:ℝ)) ≤ (100158); norm_num
  · show ((100158:ℝ)) ≤ (100184); norm_num
  · show ((100184:ℝ)) ≤ (100211); norm_num
  · show ((100211:ℝ)) ≤ (100237); norm_num
  · show ((100237:ℝ)) ≤ (100263); norm_num
  · show ((100263:ℝ)) ≤ (100289); norm_num
  · show ((100289:ℝ)) ≤ (100316); norm_num
  · show ((100316:ℝ)) ≤ (100342); norm_num
  · show ((100342:ℝ)) ≤ (100368); norm_num
  · show ((100368:ℝ)) ≤ (100395); norm_num
  · show ((100395:ℝ)) ≤ (100421); norm_num
  · show ((100421:ℝ)) ≤ (100447); norm_num
  · show ((100447:ℝ)) ≤ (100474); norm_num
  · show ((100474:ℝ)) ≤ (100500); norm_num
  · show ((100500:ℝ)) ≤ (100526); norm_num
  · show ((100526:ℝ)) ≤ (100553); norm_num
  · show ((100553:ℝ)) ≤ (100579); norm_num
  · show ((100579:ℝ)) ≤ (100605); norm_num
  · show ((100605:ℝ)) ≤ (100632); norm_num
  · show ((100632:ℝ)) ≤ (100658); norm_num
  · show ((100658:ℝ)) ≤ (100684); norm_num
  · show ((100684:ℝ)) ≤ (100711); norm_num
  · show ((100711:ℝ)) ≤ (100737); norm_num
  · show ((100737:ℝ)) ≤ (100763); norm_num
  · show ((100763:ℝ)) ≤ (100789); norm_num
  · show ((100789:ℝ)) ≤ (100816); norm_num
  · show ((100816:ℝ)) ≤ (100842); norm_num
  · show ((100842:ℝ)) ≤ (100868); norm_num
  · show ((100868:ℝ)) ≤ (100895); norm_num
  · show ((100895:ℝ)) ≤ (100921); norm_num
  · show ((100921:ℝ)) ≤ (100947); norm_num
  · show ((100947:ℝ)) ≤ (100974); norm_num
  · show ((100974:ℝ)) ≤ (101000); norm_num
  · show ((101000:ℝ)) ≤ (101000); norm_num
  · exact le_refl _

/-- The lower edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 100000
  | 1 => 100026
  | 2 => 100053
  | 3 => 100079
  | 4 => 100105
  | 5 => 100132
  | 6 => 100158
  | 7 => 100184
  | 8 => 100211
  | 9 => 400947 / 4
  | 10 => 100263
  | 11 => 401155 / 4
  | 12 => 100316
  | 13 => 100342
  | 14 => 100368
  | 15 => 100395
  | 16 => 100421
  | 17 => 100447
  | 18 => 100474
  | 19 => 100500
  | 20 => 100526
  | 21 => 100553
  | 22 => 100579
  | 23 => 402419 / 4
  | 24 => 100632
  | 25 => 100658
  | 26 => 100684
  | 27 => 100711
  | 28 => 100737
  | 29 => 100763
  | 30 => 100789
  | 31 => 100816
  | 32 => 100842
  | 33 => 100868
  | 34 => 100895
  | 35 => 100921
  | 36 => 100947
  | 37 => 100974
  | _ => 100974

/-- The upper edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 100026
  | 1 => 400213 / 4
  | 2 => 400317 / 4
  | 3 => 100105
  | 4 => 100132
  | 5 => 100158
  | 6 => 400737 / 4
  | 7 => 100211
  | 8 => 100237
  | 9 => 100263
  | 10 => 100289
  | 11 => 100316
  | 12 => 100342
  | 13 => 100368
  | 14 => 100395
  | 15 => 401685 / 4
  | 16 => 100447
  | 17 => 100474
  | 18 => 100500
  | 19 => 100526
  | 20 => 100553
  | 21 => 100579
  | 22 => 100605
  | 23 => 100632
  | 24 => 100658
  | 25 => 100684
  | 26 => 100711
  | 27 => 100737
  | 28 => 100763
  | 29 => 403157 / 4
  | 30 => 100816
  | 31 => 100842
  | 32 => 100868
  | 33 => 100895
  | 34 => 403685 / 4
  | 35 => 100947
  | 36 => 100974
  | 37 => 101000
  | _ => 101000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 38 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 101000` (`log 101000 ≤ 12`, `2.7^12 ≥ 101000`). -/
theorem haC_101000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 101000 := by
  have hlog : Real.log 101000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 101000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 101000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[100000, 101000]` segment's band hypothesis: every band `i < 38` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 38 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 38 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[100000, 101000]` SEGMENT: every zero with `100000 ≤ Im ≤ 101000` is on the line. -/
theorem segment_100000_101000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 101000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (100000:ℝ) ≤ ρ.im → ρ.im ≤ 101000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 100000 101000 bndSeg 38 (by norm_num) bndSeg_mono rfl rfl haC_101000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 101000 via the HEIGHT CHAIN**: `[0,100000]` ∘ `[100000,101000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_101000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 101000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 101000 → ρ.re = 1 / 2 := by
  have hγ100000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 100000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 100000 101000
    (AllZeros_h100000.all_nontrivial_zeros_up_to_height_100000_of_bands
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
      hγ100000)
    (segment_100000_101000 hbands hγ)

end AllZeros_h101000
