/-  Height-chain step: all nontrivial zeta zeros up to height 102000 on Re = 1/2 --
    `AllZeros_h101000` + a `[101000, 102000]` SEGMENT certificate (38 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h101000
import RHInBoxT_1d4000000_3999999d4000000_101000_404105d4
import RHInBoxT_1d4000000_3999999d4000000_101026_101053
import RHInBoxT_1d4000000_3999999d4000000_101053_101079
import RHInBoxT_1d4000000_3999999d4000000_101079_101105
import RHInBoxT_1d4000000_3999999d4000000_404419d4_101132
import RHInBoxT_1d4000000_3999999d4000000_101132_101158
import RHInBoxT_1d4000000_3999999d4000000_101158_101184
import RHInBoxT_1d4000000_3999999d4000000_101184_101211
import RHInBoxT_1d4000000_3999999d4000000_101211_404949d4
import RHInBoxT_1d4000000_3999999d4000000_101237_405053d4
import RHInBoxT_1d4000000_3999999d4000000_101263_101289
import RHInBoxT_1d4000000_3999999d4000000_101289_405265d4
import RHInBoxT_1d4000000_3999999d4000000_101316_101342
import RHInBoxT_1d4000000_3999999d4000000_101342_101368
import RHInBoxT_1d4000000_3999999d4000000_101368_101395
import RHInBoxT_1d4000000_3999999d4000000_101395_101421
import RHInBoxT_1d4000000_3999999d4000000_101421_101447
import RHInBoxT_1d4000000_3999999d4000000_101447_101474
import RHInBoxT_1d4000000_3999999d4000000_101474_406001d4
import RHInBoxT_1d4000000_3999999d4000000_101500_101526
import RHInBoxT_1d4000000_3999999d4000000_101526_406213d4
import RHInBoxT_1d4000000_3999999d4000000_101553_101579
import RHInBoxT_1d4000000_3999999d4000000_101579_101605
import RHInBoxT_1d4000000_3999999d4000000_101605_101632
import RHInBoxT_1d4000000_3999999d4000000_101632_101658
import RHInBoxT_1d4000000_3999999d4000000_101658_101684
import RHInBoxT_1d4000000_3999999d4000000_101684_406845d4
import RHInBoxT_1d4000000_3999999d4000000_101711_101737
import RHInBoxT_1d4000000_3999999d4000000_101737_101763
import RHInBoxT_1d4000000_3999999d4000000_101763_101789
import RHInBoxT_1d4000000_3999999d4000000_101789_407265d4
import RHInBoxT_1d4000000_3999999d4000000_101816_101842
import RHInBoxT_1d4000000_3999999d4000000_101842_101868
import RHInBoxT_1d4000000_3999999d4000000_101868_101895
import RHInBoxT_1d4000000_3999999d4000000_101895_101921
import RHInBoxT_1d4000000_3999999d4000000_101921_101947
import RHInBoxT_1d4000000_3999999d4000000_101947_101974
import RHInBoxT_1d4000000_3999999d4000000_101974_102000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h102000

/-- The 38-band NOMINAL partition of `[101000, 102000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 101000
  | 1 => 101026
  | 2 => 101053
  | 3 => 101079
  | 4 => 101105
  | 5 => 101132
  | 6 => 101158
  | 7 => 101184
  | 8 => 101211
  | 9 => 101237
  | 10 => 101263
  | 11 => 101289
  | 12 => 101316
  | 13 => 101342
  | 14 => 101368
  | 15 => 101395
  | 16 => 101421
  | 17 => 101447
  | 18 => 101474
  | 19 => 101500
  | 20 => 101526
  | 21 => 101553
  | 22 => 101579
  | 23 => 101605
  | 24 => 101632
  | 25 => 101658
  | 26 => 101684
  | 27 => 101711
  | 28 => 101737
  | 29 => 101763
  | 30 => 101789
  | 31 => 101816
  | 32 => 101842
  | 33 => 101868
  | 34 => 101895
  | 35 => 101921
  | 36 => 101947
  | 37 => 101974
  | 38 => 102000
  | _ => 102000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((101000:ℝ)) ≤ (101026); norm_num
  · show ((101026:ℝ)) ≤ (101053); norm_num
  · show ((101053:ℝ)) ≤ (101079); norm_num
  · show ((101079:ℝ)) ≤ (101105); norm_num
  · show ((101105:ℝ)) ≤ (101132); norm_num
  · show ((101132:ℝ)) ≤ (101158); norm_num
  · show ((101158:ℝ)) ≤ (101184); norm_num
  · show ((101184:ℝ)) ≤ (101211); norm_num
  · show ((101211:ℝ)) ≤ (101237); norm_num
  · show ((101237:ℝ)) ≤ (101263); norm_num
  · show ((101263:ℝ)) ≤ (101289); norm_num
  · show ((101289:ℝ)) ≤ (101316); norm_num
  · show ((101316:ℝ)) ≤ (101342); norm_num
  · show ((101342:ℝ)) ≤ (101368); norm_num
  · show ((101368:ℝ)) ≤ (101395); norm_num
  · show ((101395:ℝ)) ≤ (101421); norm_num
  · show ((101421:ℝ)) ≤ (101447); norm_num
  · show ((101447:ℝ)) ≤ (101474); norm_num
  · show ((101474:ℝ)) ≤ (101500); norm_num
  · show ((101500:ℝ)) ≤ (101526); norm_num
  · show ((101526:ℝ)) ≤ (101553); norm_num
  · show ((101553:ℝ)) ≤ (101579); norm_num
  · show ((101579:ℝ)) ≤ (101605); norm_num
  · show ((101605:ℝ)) ≤ (101632); norm_num
  · show ((101632:ℝ)) ≤ (101658); norm_num
  · show ((101658:ℝ)) ≤ (101684); norm_num
  · show ((101684:ℝ)) ≤ (101711); norm_num
  · show ((101711:ℝ)) ≤ (101737); norm_num
  · show ((101737:ℝ)) ≤ (101763); norm_num
  · show ((101763:ℝ)) ≤ (101789); norm_num
  · show ((101789:ℝ)) ≤ (101816); norm_num
  · show ((101816:ℝ)) ≤ (101842); norm_num
  · show ((101842:ℝ)) ≤ (101868); norm_num
  · show ((101868:ℝ)) ≤ (101895); norm_num
  · show ((101895:ℝ)) ≤ (101921); norm_num
  · show ((101921:ℝ)) ≤ (101947); norm_num
  · show ((101947:ℝ)) ≤ (101974); norm_num
  · show ((101974:ℝ)) ≤ (102000); norm_num
  · show ((102000:ℝ)) ≤ (102000); norm_num
  · exact le_refl _

/-- The lower edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 101000
  | 1 => 101026
  | 2 => 101053
  | 3 => 101079
  | 4 => 404419 / 4
  | 5 => 101132
  | 6 => 101158
  | 7 => 101184
  | 8 => 101211
  | 9 => 101237
  | 10 => 101263
  | 11 => 101289
  | 12 => 101316
  | 13 => 101342
  | 14 => 101368
  | 15 => 101395
  | 16 => 101421
  | 17 => 101447
  | 18 => 101474
  | 19 => 101500
  | 20 => 101526
  | 21 => 101553
  | 22 => 101579
  | 23 => 101605
  | 24 => 101632
  | 25 => 101658
  | 26 => 101684
  | 27 => 101711
  | 28 => 101737
  | 29 => 101763
  | 30 => 101789
  | 31 => 101816
  | 32 => 101842
  | 33 => 101868
  | 34 => 101895
  | 35 => 101921
  | 36 => 101947
  | 37 => 101974
  | _ => 101974

/-- The upper edges of the 38 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 404105 / 4
  | 1 => 101053
  | 2 => 101079
  | 3 => 101105
  | 4 => 101132
  | 5 => 101158
  | 6 => 101184
  | 7 => 101211
  | 8 => 404949 / 4
  | 9 => 405053 / 4
  | 10 => 101289
  | 11 => 405265 / 4
  | 12 => 101342
  | 13 => 101368
  | 14 => 101395
  | 15 => 101421
  | 16 => 101447
  | 17 => 101474
  | 18 => 406001 / 4
  | 19 => 101526
  | 20 => 406213 / 4
  | 21 => 101579
  | 22 => 101605
  | 23 => 101632
  | 24 => 101658
  | 25 => 101684
  | 26 => 406845 / 4
  | 27 => 101737
  | 28 => 101763
  | 29 => 101789
  | 30 => 407265 / 4
  | 31 => 101842
  | 32 => 101868
  | 33 => 101895
  | 34 => 101921
  | 35 => 101947
  | 36 => 101974
  | 37 => 102000
  | _ => 102000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 38 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 102000` (`log 102000 ≤ 12`, `2.7^12 ≥ 102000`). -/
theorem haC_102000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 102000 := by
  have hlog : Real.log 102000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 102000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 102000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[101000, 102000]` segment's band hypothesis: every band `i < 38` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 38 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 38 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[101000, 102000]` SEGMENT: every zero with `101000 ≤ Im ≤ 102000` is on the line. -/
theorem segment_101000_102000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 102000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (101000:ℝ) ≤ ρ.im → ρ.im ≤ 102000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 101000 102000 bndSeg 38 (by norm_num) bndSeg_mono rfl rfl haC_102000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 102000 via the HEIGHT CHAIN**: `[0,101000]` ∘ `[101000,102000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_102000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 102000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 102000 → ρ.re = 1 / 2 := by
  have hγ101000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 101000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 101000 102000
    (AllZeros_h101000.all_nontrivial_zeros_up_to_height_101000_of_bands
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
      hγ101000)
    (segment_101000_102000 hbands hγ)

end AllZeros_h102000
