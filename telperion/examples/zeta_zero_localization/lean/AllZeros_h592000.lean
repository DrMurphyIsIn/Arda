/-  Height-chain step: all nontrivial zeta zeros up to height 592000 on Re = 1/2 --
    `AllZeros_h591000` + a `[591000, 592000]` SEGMENT certificate (44 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h591000
import RHInBoxT_1d4000000_3999999d4000000_2363999d4_591023
import RHInBoxT_1d4000000_3999999d4000000_2364091d4_591045
import RHInBoxT_1d4000000_3999999d4000000_591045_2364273d4
import RHInBoxT_1d4000000_3999999d4000000_591068_591091
import RHInBoxT_1d4000000_3999999d4000000_591091_591114
import RHInBoxT_1d4000000_3999999d4000000_591114_591136
import RHInBoxT_1d4000000_3999999d4000000_591136_2364637d4
import RHInBoxT_1d4000000_3999999d4000000_591159_591182
import RHInBoxT_1d4000000_3999999d4000000_2364727d4_591205
import RHInBoxT_1d4000000_3999999d4000000_591205_591227
import RHInBoxT_1d4000000_3999999d4000000_591227_591250
import RHInBoxT_1d4000000_3999999d4000000_2364997d4_2365093d4
import RHInBoxT_1d4000000_3999999d4000000_591273_591295
import RHInBoxT_1d4000000_3999999d4000000_591295_591318
import RHInBoxT_1d4000000_3999999d4000000_591318_591341
import RHInBoxT_1d4000000_3999999d4000000_2365363d4_591364
import RHInBoxT_1d4000000_3999999d4000000_591364_591386
import RHInBoxT_1d4000000_3999999d4000000_591386_591409
import RHInBoxT_1d4000000_3999999d4000000_2365635d4_591432
import RHInBoxT_1d4000000_3999999d4000000_591432_591455
import RHInBoxT_1d4000000_3999999d4000000_2365819d4_2365909d4
import RHInBoxT_1d4000000_3999999d4000000_591477_591500
import RHInBoxT_1d4000000_3999999d4000000_2365999d4_591523
import RHInBoxT_1d4000000_3999999d4000000_591523_591545
import RHInBoxT_1d4000000_3999999d4000000_591545_591568
import RHInBoxT_1d4000000_3999999d4000000_591568_591591
import RHInBoxT_1d4000000_3999999d4000000_591591_591614
import RHInBoxT_1d4000000_3999999d4000000_1183227d2_591636
import RHInBoxT_1d4000000_3999999d4000000_591636_591659
import RHInBoxT_1d4000000_3999999d4000000_591659_591682
import RHInBoxT_1d4000000_3999999d4000000_591682_591705
import RHInBoxT_1d4000000_3999999d4000000_2366819d4_591727
import RHInBoxT_1d4000000_3999999d4000000_591727_591750
import RHInBoxT_1d4000000_3999999d4000000_591750_591773
import RHInBoxT_1d4000000_3999999d4000000_2367091d4_591795
import RHInBoxT_1d4000000_3999999d4000000_591795_591818
import RHInBoxT_1d4000000_3999999d4000000_2367271d4_591841
import RHInBoxT_1d4000000_3999999d4000000_591841_2367457d4
import RHInBoxT_1d4000000_3999999d4000000_591864_591886
import RHInBoxT_1d4000000_3999999d4000000_591886_591909
import RHInBoxT_1d4000000_3999999d4000000_591909_591932
import RHInBoxT_1d4000000_3999999d4000000_591932_591955
import RHInBoxT_1d4000000_3999999d4000000_591955_591977
import RHInBoxT_1d4000000_3999999d4000000_591977_592000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h592000

/-- The 44-band NOMINAL partition of `[591000, 592000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 591000
  | 1 => 591023
  | 2 => 591045
  | 3 => 591068
  | 4 => 591091
  | 5 => 591114
  | 6 => 591136
  | 7 => 591159
  | 8 => 591182
  | 9 => 591205
  | 10 => 591227
  | 11 => 591250
  | 12 => 591273
  | 13 => 591295
  | 14 => 591318
  | 15 => 591341
  | 16 => 591364
  | 17 => 591386
  | 18 => 591409
  | 19 => 591432
  | 20 => 591455
  | 21 => 591477
  | 22 => 591500
  | 23 => 591523
  | 24 => 591545
  | 25 => 591568
  | 26 => 591591
  | 27 => 591614
  | 28 => 591636
  | 29 => 591659
  | 30 => 591682
  | 31 => 591705
  | 32 => 591727
  | 33 => 591750
  | 34 => 591773
  | 35 => 591795
  | 36 => 591818
  | 37 => 591841
  | 38 => 591864
  | 39 => 591886
  | 40 => 591909
  | 41 => 591932
  | 42 => 591955
  | 43 => 591977
  | 44 => 592000
  | _ => 592000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((591000:ℝ)) ≤ (591023); norm_num
  · show ((591023:ℝ)) ≤ (591045); norm_num
  · show ((591045:ℝ)) ≤ (591068); norm_num
  · show ((591068:ℝ)) ≤ (591091); norm_num
  · show ((591091:ℝ)) ≤ (591114); norm_num
  · show ((591114:ℝ)) ≤ (591136); norm_num
  · show ((591136:ℝ)) ≤ (591159); norm_num
  · show ((591159:ℝ)) ≤ (591182); norm_num
  · show ((591182:ℝ)) ≤ (591205); norm_num
  · show ((591205:ℝ)) ≤ (591227); norm_num
  · show ((591227:ℝ)) ≤ (591250); norm_num
  · show ((591250:ℝ)) ≤ (591273); norm_num
  · show ((591273:ℝ)) ≤ (591295); norm_num
  · show ((591295:ℝ)) ≤ (591318); norm_num
  · show ((591318:ℝ)) ≤ (591341); norm_num
  · show ((591341:ℝ)) ≤ (591364); norm_num
  · show ((591364:ℝ)) ≤ (591386); norm_num
  · show ((591386:ℝ)) ≤ (591409); norm_num
  · show ((591409:ℝ)) ≤ (591432); norm_num
  · show ((591432:ℝ)) ≤ (591455); norm_num
  · show ((591455:ℝ)) ≤ (591477); norm_num
  · show ((591477:ℝ)) ≤ (591500); norm_num
  · show ((591500:ℝ)) ≤ (591523); norm_num
  · show ((591523:ℝ)) ≤ (591545); norm_num
  · show ((591545:ℝ)) ≤ (591568); norm_num
  · show ((591568:ℝ)) ≤ (591591); norm_num
  · show ((591591:ℝ)) ≤ (591614); norm_num
  · show ((591614:ℝ)) ≤ (591636); norm_num
  · show ((591636:ℝ)) ≤ (591659); norm_num
  · show ((591659:ℝ)) ≤ (591682); norm_num
  · show ((591682:ℝ)) ≤ (591705); norm_num
  · show ((591705:ℝ)) ≤ (591727); norm_num
  · show ((591727:ℝ)) ≤ (591750); norm_num
  · show ((591750:ℝ)) ≤ (591773); norm_num
  · show ((591773:ℝ)) ≤ (591795); norm_num
  · show ((591795:ℝ)) ≤ (591818); norm_num
  · show ((591818:ℝ)) ≤ (591841); norm_num
  · show ((591841:ℝ)) ≤ (591864); norm_num
  · show ((591864:ℝ)) ≤ (591886); norm_num
  · show ((591886:ℝ)) ≤ (591909); norm_num
  · show ((591909:ℝ)) ≤ (591932); norm_num
  · show ((591932:ℝ)) ≤ (591955); norm_num
  · show ((591955:ℝ)) ≤ (591977); norm_num
  · show ((591977:ℝ)) ≤ (592000); norm_num
  · show ((592000:ℝ)) ≤ (592000); norm_num
  · exact le_refl _

/-- The lower edges of the 44 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 2363999 / 4
  | 1 => 2364091 / 4
  | 2 => 591045
  | 3 => 591068
  | 4 => 591091
  | 5 => 591114
  | 6 => 591136
  | 7 => 591159
  | 8 => 2364727 / 4
  | 9 => 591205
  | 10 => 591227
  | 11 => 2364997 / 4
  | 12 => 591273
  | 13 => 591295
  | 14 => 591318
  | 15 => 2365363 / 4
  | 16 => 591364
  | 17 => 591386
  | 18 => 2365635 / 4
  | 19 => 591432
  | 20 => 2365819 / 4
  | 21 => 591477
  | 22 => 2365999 / 4
  | 23 => 591523
  | 24 => 591545
  | 25 => 591568
  | 26 => 591591
  | 27 => 1183227 / 2
  | 28 => 591636
  | 29 => 591659
  | 30 => 591682
  | 31 => 2366819 / 4
  | 32 => 591727
  | 33 => 591750
  | 34 => 2367091 / 4
  | 35 => 591795
  | 36 => 2367271 / 4
  | 37 => 591841
  | 38 => 591864
  | 39 => 591886
  | 40 => 591909
  | 41 => 591932
  | 42 => 591955
  | 43 => 591977
  | _ => 591977

/-- The upper edges of the 44 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 591023
  | 1 => 591045
  | 2 => 2364273 / 4
  | 3 => 591091
  | 4 => 591114
  | 5 => 591136
  | 6 => 2364637 / 4
  | 7 => 591182
  | 8 => 591205
  | 9 => 591227
  | 10 => 591250
  | 11 => 2365093 / 4
  | 12 => 591295
  | 13 => 591318
  | 14 => 591341
  | 15 => 591364
  | 16 => 591386
  | 17 => 591409
  | 18 => 591432
  | 19 => 591455
  | 20 => 2365909 / 4
  | 21 => 591500
  | 22 => 591523
  | 23 => 591545
  | 24 => 591568
  | 25 => 591591
  | 26 => 591614
  | 27 => 591636
  | 28 => 591659
  | 29 => 591682
  | 30 => 591705
  | 31 => 591727
  | 32 => 591750
  | 33 => 591773
  | 34 => 591795
  | 35 => 591818
  | 36 => 591841
  | 37 => 2367457 / 4
  | 38 => 591886
  | 39 => 591909
  | 40 => 591932
  | 41 => 591955
  | 42 => 591977
  | 43 => 592000
  | _ => 592000

set_option maxHeartbeats 1600000 in
/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 44 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 592000` (`log 592000 ≤ 14`, `2.7^14 ≥ 592000`). -/
theorem haC_592000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 592000 := by
  have hlog : Real.log 592000 ≤ 14 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h14 : Real.exp 14 = (Real.exp 1) ^ 14 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 14 ≤ (Real.exp 1) ^ 14 := pow_le_pow_left₀ (by norm_num) he1 14
    rw [h14]; nlinarith [hpow]
  have hpos : 0 < Real.log 592000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 592000
      ≤ (1 / 4000000) * 14 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[591000, 592000]` segment's band hypothesis: every band `i < 44` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 44 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 44 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[591000, 592000]` SEGMENT: every zero with `591000 ≤ Im ≤ 592000` is on the line. -/
theorem segment_591000_592000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 592000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (591000:ℝ) ≤ ρ.im → ρ.im ≤ 592000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 591000 592000 bndSeg 44 (by norm_num) bndSeg_mono rfl rfl haC_592000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 592000 via the HEIGHT CHAIN**: `[0,591000]` ∘ `[591000,592000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_592000_of_bands
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
    (hbands_132000 : AllZeros_h132000.BandHyp)
    (hbands_133000 : AllZeros_h133000.BandHyp)
    (hbands_134000 : AllZeros_h134000.BandHyp)
    (hbands_135000 : AllZeros_h135000.BandHyp)
    (hbands_136000 : AllZeros_h136000.BandHyp)
    (hbands_137000 : AllZeros_h137000.BandHyp)
    (hbands_138000 : AllZeros_h138000.BandHyp)
    (hbands_139000 : AllZeros_h139000.BandHyp)
    (hbands_140000 : AllZeros_h140000.BandHyp)
    (hbands_141000 : AllZeros_h141000.BandHyp)
    (hbands_142000 : AllZeros_h142000.BandHyp)
    (hbands_143000 : AllZeros_h143000.BandHyp)
    (hbands_144000 : AllZeros_h144000.BandHyp)
    (hbands_145000 : AllZeros_h145000.BandHyp)
    (hbands_146000 : AllZeros_h146000.BandHyp)
    (hbands_147000 : AllZeros_h147000.BandHyp)
    (hbands_148000 : AllZeros_h148000.BandHyp)
    (hbands_149000 : AllZeros_h149000.BandHyp)
    (hbands_150000 : AllZeros_h150000.BandHyp)
    (hbands_151000 : AllZeros_h151000.BandHyp)
    (hbands_152000 : AllZeros_h152000.BandHyp)
    (hbands_153000 : AllZeros_h153000.BandHyp)
    (hbands_154000 : AllZeros_h154000.BandHyp)
    (hbands_155000 : AllZeros_h155000.BandHyp)
    (hbands_156000 : AllZeros_h156000.BandHyp)
    (hbands_157000 : AllZeros_h157000.BandHyp)
    (hbands_158000 : AllZeros_h158000.BandHyp)
    (hbands_159000 : AllZeros_h159000.BandHyp)
    (hbands_160000 : AllZeros_h160000.BandHyp)
    (hbands_161000 : AllZeros_h161000.BandHyp)
    (hbands_162000 : AllZeros_h162000.BandHyp)
    (hbands_163000 : AllZeros_h163000.BandHyp)
    (hbands_164000 : AllZeros_h164000.BandHyp)
    (hbands_165000 : AllZeros_h165000.BandHyp)
    (hbands_166000 : AllZeros_h166000.BandHyp)
    (hbands_167000 : AllZeros_h167000.BandHyp)
    (hbands_168000 : AllZeros_h168000.BandHyp)
    (hbands_169000 : AllZeros_h169000.BandHyp)
    (hbands_170000 : AllZeros_h170000.BandHyp)
    (hbands_171000 : AllZeros_h171000.BandHyp)
    (hbands_172000 : AllZeros_h172000.BandHyp)
    (hbands_173000 : AllZeros_h173000.BandHyp)
    (hbands_174000 : AllZeros_h174000.BandHyp)
    (hbands_175000 : AllZeros_h175000.BandHyp)
    (hbands_176000 : AllZeros_h176000.BandHyp)
    (hbands_177000 : AllZeros_h177000.BandHyp)
    (hbands_178000 : AllZeros_h178000.BandHyp)
    (hbands_179000 : AllZeros_h179000.BandHyp)
    (hbands_180000 : AllZeros_h180000.BandHyp)
    (hbands_181000 : AllZeros_h181000.BandHyp)
    (hbands_182000 : AllZeros_h182000.BandHyp)
    (hbands_183000 : AllZeros_h183000.BandHyp)
    (hbands_184000 : AllZeros_h184000.BandHyp)
    (hbands_185000 : AllZeros_h185000.BandHyp)
    (hbands_186000 : AllZeros_h186000.BandHyp)
    (hbands_187000 : AllZeros_h187000.BandHyp)
    (hbands_188000 : AllZeros_h188000.BandHyp)
    (hbands_189000 : AllZeros_h189000.BandHyp)
    (hbands_190000 : AllZeros_h190000.BandHyp)
    (hbands_191000 : AllZeros_h191000.BandHyp)
    (hbands_192000 : AllZeros_h192000.BandHyp)
    (hbands_193000 : AllZeros_h193000.BandHyp)
    (hbands_194000 : AllZeros_h194000.BandHyp)
    (hbands_195000 : AllZeros_h195000.BandHyp)
    (hbands_196000 : AllZeros_h196000.BandHyp)
    (hbands_197000 : AllZeros_h197000.BandHyp)
    (hbands_198000 : AllZeros_h198000.BandHyp)
    (hbands_199000 : AllZeros_h199000.BandHyp)
    (hbands_200000 : AllZeros_h200000.BandHyp)
    (hbands_201000 : AllZeros_h201000.BandHyp)
    (hbands_202000 : AllZeros_h202000.BandHyp)
    (hbands_203000 : AllZeros_h203000.BandHyp)
    (hbands_204000 : AllZeros_h204000.BandHyp)
    (hbands_205000 : AllZeros_h205000.BandHyp)
    (hbands_206000 : AllZeros_h206000.BandHyp)
    (hbands_207000 : AllZeros_h207000.BandHyp)
    (hbands_208000 : AllZeros_h208000.BandHyp)
    (hbands_209000 : AllZeros_h209000.BandHyp)
    (hbands_210000 : AllZeros_h210000.BandHyp)
    (hbands_211000 : AllZeros_h211000.BandHyp)
    (hbands_212000 : AllZeros_h212000.BandHyp)
    (hbands_213000 : AllZeros_h213000.BandHyp)
    (hbands_214000 : AllZeros_h214000.BandHyp)
    (hbands_215000 : AllZeros_h215000.BandHyp)
    (hbands_216000 : AllZeros_h216000.BandHyp)
    (hbands_217000 : AllZeros_h217000.BandHyp)
    (hbands_218000 : AllZeros_h218000.BandHyp)
    (hbands_219000 : AllZeros_h219000.BandHyp)
    (hbands_220000 : AllZeros_h220000.BandHyp)
    (hbands_221000 : AllZeros_h221000.BandHyp)
    (hbands_222000 : AllZeros_h222000.BandHyp)
    (hbands_223000 : AllZeros_h223000.BandHyp)
    (hbands_224000 : AllZeros_h224000.BandHyp)
    (hbands_225000 : AllZeros_h225000.BandHyp)
    (hbands_226000 : AllZeros_h226000.BandHyp)
    (hbands_227000 : AllZeros_h227000.BandHyp)
    (hbands_228000 : AllZeros_h228000.BandHyp)
    (hbands_229000 : AllZeros_h229000.BandHyp)
    (hbands_230000 : AllZeros_h230000.BandHyp)
    (hbands_231000 : AllZeros_h231000.BandHyp)
    (hbands_232000 : AllZeros_h232000.BandHyp)
    (hbands_233000 : AllZeros_h233000.BandHyp)
    (hbands_234000 : AllZeros_h234000.BandHyp)
    (hbands_235000 : AllZeros_h235000.BandHyp)
    (hbands_236000 : AllZeros_h236000.BandHyp)
    (hbands_237000 : AllZeros_h237000.BandHyp)
    (hbands_238000 : AllZeros_h238000.BandHyp)
    (hbands_239000 : AllZeros_h239000.BandHyp)
    (hbands_240000 : AllZeros_h240000.BandHyp)
    (hbands_241000 : AllZeros_h241000.BandHyp)
    (hbands_242000 : AllZeros_h242000.BandHyp)
    (hbands_243000 : AllZeros_h243000.BandHyp)
    (hbands_244000 : AllZeros_h244000.BandHyp)
    (hbands_245000 : AllZeros_h245000.BandHyp)
    (hbands_246000 : AllZeros_h246000.BandHyp)
    (hbands_247000 : AllZeros_h247000.BandHyp)
    (hbands_248000 : AllZeros_h248000.BandHyp)
    (hbands_249000 : AllZeros_h249000.BandHyp)
    (hbands_250000 : AllZeros_h250000.BandHyp)
    (hbands_251000 : AllZeros_h251000.BandHyp)
    (hbands_252000 : AllZeros_h252000.BandHyp)
    (hbands_253000 : AllZeros_h253000.BandHyp)
    (hbands_254000 : AllZeros_h254000.BandHyp)
    (hbands_255000 : AllZeros_h255000.BandHyp)
    (hbands_256000 : AllZeros_h256000.BandHyp)
    (hbands_257000 : AllZeros_h257000.BandHyp)
    (hbands_258000 : AllZeros_h258000.BandHyp)
    (hbands_259000 : AllZeros_h259000.BandHyp)
    (hbands_260000 : AllZeros_h260000.BandHyp)
    (hbands_261000 : AllZeros_h261000.BandHyp)
    (hbands_262000 : AllZeros_h262000.BandHyp)
    (hbands_263000 : AllZeros_h263000.BandHyp)
    (hbands_264000 : AllZeros_h264000.BandHyp)
    (hbands_265000 : AllZeros_h265000.BandHyp)
    (hbands_266000 : AllZeros_h266000.BandHyp)
    (hbands_267000 : AllZeros_h267000.BandHyp)
    (hbands_268000 : AllZeros_h268000.BandHyp)
    (hbands_269000 : AllZeros_h269000.BandHyp)
    (hbands_270000 : AllZeros_h270000.BandHyp)
    (hbands_271000 : AllZeros_h271000.BandHyp)
    (hbands_272000 : AllZeros_h272000.BandHyp)
    (hbands_273000 : AllZeros_h273000.BandHyp)
    (hbands_274000 : AllZeros_h274000.BandHyp)
    (hbands_275000 : AllZeros_h275000.BandHyp)
    (hbands_276000 : AllZeros_h276000.BandHyp)
    (hbands_277000 : AllZeros_h277000.BandHyp)
    (hbands_278000 : AllZeros_h278000.BandHyp)
    (hbands_279000 : AllZeros_h279000.BandHyp)
    (hbands_280000 : AllZeros_h280000.BandHyp)
    (hbands_281000 : AllZeros_h281000.BandHyp)
    (hbands_282000 : AllZeros_h282000.BandHyp)
    (hbands_283000 : AllZeros_h283000.BandHyp)
    (hbands_284000 : AllZeros_h284000.BandHyp)
    (hbands_285000 : AllZeros_h285000.BandHyp)
    (hbands_286000 : AllZeros_h286000.BandHyp)
    (hbands_287000 : AllZeros_h287000.BandHyp)
    (hbands_288000 : AllZeros_h288000.BandHyp)
    (hbands_289000 : AllZeros_h289000.BandHyp)
    (hbands_290000 : AllZeros_h290000.BandHyp)
    (hbands_291000 : AllZeros_h291000.BandHyp)
    (hbands_292000 : AllZeros_h292000.BandHyp)
    (hbands_293000 : AllZeros_h293000.BandHyp)
    (hbands_294000 : AllZeros_h294000.BandHyp)
    (hbands_295000 : AllZeros_h295000.BandHyp)
    (hbands_296000 : AllZeros_h296000.BandHyp)
    (hbands_297000 : AllZeros_h297000.BandHyp)
    (hbands_298000 : AllZeros_h298000.BandHyp)
    (hbands_299000 : AllZeros_h299000.BandHyp)
    (hbands_300000 : AllZeros_h300000.BandHyp)
    (hbands_301000 : AllZeros_h301000.BandHyp)
    (hbands_302000 : AllZeros_h302000.BandHyp)
    (hbands_303000 : AllZeros_h303000.BandHyp)
    (hbands_304000 : AllZeros_h304000.BandHyp)
    (hbands_305000 : AllZeros_h305000.BandHyp)
    (hbands_306000 : AllZeros_h306000.BandHyp)
    (hbands_307000 : AllZeros_h307000.BandHyp)
    (hbands_308000 : AllZeros_h308000.BandHyp)
    (hbands_309000 : AllZeros_h309000.BandHyp)
    (hbands_310000 : AllZeros_h310000.BandHyp)
    (hbands_311000 : AllZeros_h311000.BandHyp)
    (hbands_312000 : AllZeros_h312000.BandHyp)
    (hbands_313000 : AllZeros_h313000.BandHyp)
    (hbands_314000 : AllZeros_h314000.BandHyp)
    (hbands_315000 : AllZeros_h315000.BandHyp)
    (hbands_316000 : AllZeros_h316000.BandHyp)
    (hbands_317000 : AllZeros_h317000.BandHyp)
    (hbands_318000 : AllZeros_h318000.BandHyp)
    (hbands_319000 : AllZeros_h319000.BandHyp)
    (hbands_320000 : AllZeros_h320000.BandHyp)
    (hbands_321000 : AllZeros_h321000.BandHyp)
    (hbands_322000 : AllZeros_h322000.BandHyp)
    (hbands_323000 : AllZeros_h323000.BandHyp)
    (hbands_324000 : AllZeros_h324000.BandHyp)
    (hbands_325000 : AllZeros_h325000.BandHyp)
    (hbands_326000 : AllZeros_h326000.BandHyp)
    (hbands_327000 : AllZeros_h327000.BandHyp)
    (hbands_328000 : AllZeros_h328000.BandHyp)
    (hbands_329000 : AllZeros_h329000.BandHyp)
    (hbands_330000 : AllZeros_h330000.BandHyp)
    (hbands_331000 : AllZeros_h331000.BandHyp)
    (hbands_332000 : AllZeros_h332000.BandHyp)
    (hbands_333000 : AllZeros_h333000.BandHyp)
    (hbands_334000 : AllZeros_h334000.BandHyp)
    (hbands_335000 : AllZeros_h335000.BandHyp)
    (hbands_336000 : AllZeros_h336000.BandHyp)
    (hbands_337000 : AllZeros_h337000.BandHyp)
    (hbands_338000 : AllZeros_h338000.BandHyp)
    (hbands_339000 : AllZeros_h339000.BandHyp)
    (hbands_340000 : AllZeros_h340000.BandHyp)
    (hbands_341000 : AllZeros_h341000.BandHyp)
    (hbands_342000 : AllZeros_h342000.BandHyp)
    (hbands_343000 : AllZeros_h343000.BandHyp)
    (hbands_344000 : AllZeros_h344000.BandHyp)
    (hbands_345000 : AllZeros_h345000.BandHyp)
    (hbands_346000 : AllZeros_h346000.BandHyp)
    (hbands_347000 : AllZeros_h347000.BandHyp)
    (hbands_348000 : AllZeros_h348000.BandHyp)
    (hbands_349000 : AllZeros_h349000.BandHyp)
    (hbands_350000 : AllZeros_h350000.BandHyp)
    (hbands_351000 : AllZeros_h351000.BandHyp)
    (hbands_352000 : AllZeros_h352000.BandHyp)
    (hbands_353000 : AllZeros_h353000.BandHyp)
    (hbands_354000 : AllZeros_h354000.BandHyp)
    (hbands_355000 : AllZeros_h355000.BandHyp)
    (hbands_356000 : AllZeros_h356000.BandHyp)
    (hbands_357000 : AllZeros_h357000.BandHyp)
    (hbands_358000 : AllZeros_h358000.BandHyp)
    (hbands_359000 : AllZeros_h359000.BandHyp)
    (hbands_360000 : AllZeros_h360000.BandHyp)
    (hbands_361000 : AllZeros_h361000.BandHyp)
    (hbands_362000 : AllZeros_h362000.BandHyp)
    (hbands_363000 : AllZeros_h363000.BandHyp)
    (hbands_364000 : AllZeros_h364000.BandHyp)
    (hbands_365000 : AllZeros_h365000.BandHyp)
    (hbands_366000 : AllZeros_h366000.BandHyp)
    (hbands_367000 : AllZeros_h367000.BandHyp)
    (hbands_368000 : AllZeros_h368000.BandHyp)
    (hbands_369000 : AllZeros_h369000.BandHyp)
    (hbands_370000 : AllZeros_h370000.BandHyp)
    (hbands_371000 : AllZeros_h371000.BandHyp)
    (hbands_372000 : AllZeros_h372000.BandHyp)
    (hbands_373000 : AllZeros_h373000.BandHyp)
    (hbands_374000 : AllZeros_h374000.BandHyp)
    (hbands_375000 : AllZeros_h375000.BandHyp)
    (hbands_376000 : AllZeros_h376000.BandHyp)
    (hbands_377000 : AllZeros_h377000.BandHyp)
    (hbands_378000 : AllZeros_h378000.BandHyp)
    (hbands_379000 : AllZeros_h379000.BandHyp)
    (hbands_380000 : AllZeros_h380000.BandHyp)
    (hbands_381000 : AllZeros_h381000.BandHyp)
    (hbands_382000 : AllZeros_h382000.BandHyp)
    (hbands_383000 : AllZeros_h383000.BandHyp)
    (hbands_384000 : AllZeros_h384000.BandHyp)
    (hbands_385000 : AllZeros_h385000.BandHyp)
    (hbands_386000 : AllZeros_h386000.BandHyp)
    (hbands_387000 : AllZeros_h387000.BandHyp)
    (hbands_388000 : AllZeros_h388000.BandHyp)
    (hbands_389000 : AllZeros_h389000.BandHyp)
    (hbands_390000 : AllZeros_h390000.BandHyp)
    (hbands_391000 : AllZeros_h391000.BandHyp)
    (hbands_392000 : AllZeros_h392000.BandHyp)
    (hbands_393000 : AllZeros_h393000.BandHyp)
    (hbands_394000 : AllZeros_h394000.BandHyp)
    (hbands_395000 : AllZeros_h395000.BandHyp)
    (hbands_396000 : AllZeros_h396000.BandHyp)
    (hbands_397000 : AllZeros_h397000.BandHyp)
    (hbands_398000 : AllZeros_h398000.BandHyp)
    (hbands_399000 : AllZeros_h399000.BandHyp)
    (hbands_400000 : AllZeros_h400000.BandHyp)
    (hbands_401000 : AllZeros_h401000.BandHyp)
    (hbands_402000 : AllZeros_h402000.BandHyp)
    (hbands_403000 : AllZeros_h403000.BandHyp)
    (hbands_404000 : AllZeros_h404000.BandHyp)
    (hbands_405000 : AllZeros_h405000.BandHyp)
    (hbands_406000 : AllZeros_h406000.BandHyp)
    (hbands_407000 : AllZeros_h407000.BandHyp)
    (hbands_408000 : AllZeros_h408000.BandHyp)
    (hbands_409000 : AllZeros_h409000.BandHyp)
    (hbands_410000 : AllZeros_h410000.BandHyp)
    (hbands_411000 : AllZeros_h411000.BandHyp)
    (hbands_412000 : AllZeros_h412000.BandHyp)
    (hbands_413000 : AllZeros_h413000.BandHyp)
    (hbands_414000 : AllZeros_h414000.BandHyp)
    (hbands_415000 : AllZeros_h415000.BandHyp)
    (hbands_416000 : AllZeros_h416000.BandHyp)
    (hbands_417000 : AllZeros_h417000.BandHyp)
    (hbands_418000 : AllZeros_h418000.BandHyp)
    (hbands_419000 : AllZeros_h419000.BandHyp)
    (hbands_420000 : AllZeros_h420000.BandHyp)
    (hbands_421000 : AllZeros_h421000.BandHyp)
    (hbands_422000 : AllZeros_h422000.BandHyp)
    (hbands_423000 : AllZeros_h423000.BandHyp)
    (hbands_424000 : AllZeros_h424000.BandHyp)
    (hbands_425000 : AllZeros_h425000.BandHyp)
    (hbands_426000 : AllZeros_h426000.BandHyp)
    (hbands_427000 : AllZeros_h427000.BandHyp)
    (hbands_428000 : AllZeros_h428000.BandHyp)
    (hbands_429000 : AllZeros_h429000.BandHyp)
    (hbands_430000 : AllZeros_h430000.BandHyp)
    (hbands_431000 : AllZeros_h431000.BandHyp)
    (hbands_432000 : AllZeros_h432000.BandHyp)
    (hbands_433000 : AllZeros_h433000.BandHyp)
    (hbands_434000 : AllZeros_h434000.BandHyp)
    (hbands_435000 : AllZeros_h435000.BandHyp)
    (hbands_436000 : AllZeros_h436000.BandHyp)
    (hbands_437000 : AllZeros_h437000.BandHyp)
    (hbands_438000 : AllZeros_h438000.BandHyp)
    (hbands_439000 : AllZeros_h439000.BandHyp)
    (hbands_440000 : AllZeros_h440000.BandHyp)
    (hbands_441000 : AllZeros_h441000.BandHyp)
    (hbands_442000 : AllZeros_h442000.BandHyp)
    (hbands_443000 : AllZeros_h443000.BandHyp)
    (hbands_444000 : AllZeros_h444000.BandHyp)
    (hbands_445000 : AllZeros_h445000.BandHyp)
    (hbands_446000 : AllZeros_h446000.BandHyp)
    (hbands_447000 : AllZeros_h447000.BandHyp)
    (hbands_448000 : AllZeros_h448000.BandHyp)
    (hbands_449000 : AllZeros_h449000.BandHyp)
    (hbands_450000 : AllZeros_h450000.BandHyp)
    (hbands_451000 : AllZeros_h451000.BandHyp)
    (hbands_452000 : AllZeros_h452000.BandHyp)
    (hbands_453000 : AllZeros_h453000.BandHyp)
    (hbands_454000 : AllZeros_h454000.BandHyp)
    (hbands_455000 : AllZeros_h455000.BandHyp)
    (hbands_456000 : AllZeros_h456000.BandHyp)
    (hbands_457000 : AllZeros_h457000.BandHyp)
    (hbands_458000 : AllZeros_h458000.BandHyp)
    (hbands_459000 : AllZeros_h459000.BandHyp)
    (hbands_460000 : AllZeros_h460000.BandHyp)
    (hbands_461000 : AllZeros_h461000.BandHyp)
    (hbands_462000 : AllZeros_h462000.BandHyp)
    (hbands_463000 : AllZeros_h463000.BandHyp)
    (hbands_464000 : AllZeros_h464000.BandHyp)
    (hbands_465000 : AllZeros_h465000.BandHyp)
    (hbands_466000 : AllZeros_h466000.BandHyp)
    (hbands_467000 : AllZeros_h467000.BandHyp)
    (hbands_468000 : AllZeros_h468000.BandHyp)
    (hbands_469000 : AllZeros_h469000.BandHyp)
    (hbands_470000 : AllZeros_h470000.BandHyp)
    (hbands_471000 : AllZeros_h471000.BandHyp)
    (hbands_472000 : AllZeros_h472000.BandHyp)
    (hbands_473000 : AllZeros_h473000.BandHyp)
    (hbands_474000 : AllZeros_h474000.BandHyp)
    (hbands_475000 : AllZeros_h475000.BandHyp)
    (hbands_476000 : AllZeros_h476000.BandHyp)
    (hbands_477000 : AllZeros_h477000.BandHyp)
    (hbands_478000 : AllZeros_h478000.BandHyp)
    (hbands_479000 : AllZeros_h479000.BandHyp)
    (hbands_480000 : AllZeros_h480000.BandHyp)
    (hbands_481000 : AllZeros_h481000.BandHyp)
    (hbands_482000 : AllZeros_h482000.BandHyp)
    (hbands_483000 : AllZeros_h483000.BandHyp)
    (hbands_484000 : AllZeros_h484000.BandHyp)
    (hbands_485000 : AllZeros_h485000.BandHyp)
    (hbands_486000 : AllZeros_h486000.BandHyp)
    (hbands_487000 : AllZeros_h487000.BandHyp)
    (hbands_488000 : AllZeros_h488000.BandHyp)
    (hbands_489000 : AllZeros_h489000.BandHyp)
    (hbands_490000 : AllZeros_h490000.BandHyp)
    (hbands_491000 : AllZeros_h491000.BandHyp)
    (hbands_492000 : AllZeros_h492000.BandHyp)
    (hbands_493000 : AllZeros_h493000.BandHyp)
    (hbands_494000 : AllZeros_h494000.BandHyp)
    (hbands_495000 : AllZeros_h495000.BandHyp)
    (hbands_496000 : AllZeros_h496000.BandHyp)
    (hbands_497000 : AllZeros_h497000.BandHyp)
    (hbands_498000 : AllZeros_h498000.BandHyp)
    (hbands_499000 : AllZeros_h499000.BandHyp)
    (hbands_500000 : AllZeros_h500000.BandHyp)
    (hbands_501000 : AllZeros_h501000.BandHyp)
    (hbands_502000 : AllZeros_h502000.BandHyp)
    (hbands_503000 : AllZeros_h503000.BandHyp)
    (hbands_504000 : AllZeros_h504000.BandHyp)
    (hbands_505000 : AllZeros_h505000.BandHyp)
    (hbands_506000 : AllZeros_h506000.BandHyp)
    (hbands_507000 : AllZeros_h507000.BandHyp)
    (hbands_508000 : AllZeros_h508000.BandHyp)
    (hbands_509000 : AllZeros_h509000.BandHyp)
    (hbands_510000 : AllZeros_h510000.BandHyp)
    (hbands_511000 : AllZeros_h511000.BandHyp)
    (hbands_512000 : AllZeros_h512000.BandHyp)
    (hbands_513000 : AllZeros_h513000.BandHyp)
    (hbands_514000 : AllZeros_h514000.BandHyp)
    (hbands_515000 : AllZeros_h515000.BandHyp)
    (hbands_516000 : AllZeros_h516000.BandHyp)
    (hbands_517000 : AllZeros_h517000.BandHyp)
    (hbands_518000 : AllZeros_h518000.BandHyp)
    (hbands_519000 : AllZeros_h519000.BandHyp)
    (hbands_520000 : AllZeros_h520000.BandHyp)
    (hbands_521000 : AllZeros_h521000.BandHyp)
    (hbands_522000 : AllZeros_h522000.BandHyp)
    (hbands_523000 : AllZeros_h523000.BandHyp)
    (hbands_524000 : AllZeros_h524000.BandHyp)
    (hbands_525000 : AllZeros_h525000.BandHyp)
    (hbands_526000 : AllZeros_h526000.BandHyp)
    (hbands_527000 : AllZeros_h527000.BandHyp)
    (hbands_528000 : AllZeros_h528000.BandHyp)
    (hbands_529000 : AllZeros_h529000.BandHyp)
    (hbands_530000 : AllZeros_h530000.BandHyp)
    (hbands_531000 : AllZeros_h531000.BandHyp)
    (hbands_532000 : AllZeros_h532000.BandHyp)
    (hbands_533000 : AllZeros_h533000.BandHyp)
    (hbands_534000 : AllZeros_h534000.BandHyp)
    (hbands_535000 : AllZeros_h535000.BandHyp)
    (hbands_536000 : AllZeros_h536000.BandHyp)
    (hbands_537000 : AllZeros_h537000.BandHyp)
    (hbands_538000 : AllZeros_h538000.BandHyp)
    (hbands_539000 : AllZeros_h539000.BandHyp)
    (hbands_540000 : AllZeros_h540000.BandHyp)
    (hbands_541000 : AllZeros_h541000.BandHyp)
    (hbands_542000 : AllZeros_h542000.BandHyp)
    (hbands_543000 : AllZeros_h543000.BandHyp)
    (hbands_544000 : AllZeros_h544000.BandHyp)
    (hbands_545000 : AllZeros_h545000.BandHyp)
    (hbands_546000 : AllZeros_h546000.BandHyp)
    (hbands_547000 : AllZeros_h547000.BandHyp)
    (hbands_548000 : AllZeros_h548000.BandHyp)
    (hbands_549000 : AllZeros_h549000.BandHyp)
    (hbands_550000 : AllZeros_h550000.BandHyp)
    (hbands_551000 : AllZeros_h551000.BandHyp)
    (hbands_552000 : AllZeros_h552000.BandHyp)
    (hbands_553000 : AllZeros_h553000.BandHyp)
    (hbands_554000 : AllZeros_h554000.BandHyp)
    (hbands_555000 : AllZeros_h555000.BandHyp)
    (hbands_556000 : AllZeros_h556000.BandHyp)
    (hbands_557000 : AllZeros_h557000.BandHyp)
    (hbands_558000 : AllZeros_h558000.BandHyp)
    (hbands_559000 : AllZeros_h559000.BandHyp)
    (hbands_560000 : AllZeros_h560000.BandHyp)
    (hbands_561000 : AllZeros_h561000.BandHyp)
    (hbands_562000 : AllZeros_h562000.BandHyp)
    (hbands_563000 : AllZeros_h563000.BandHyp)
    (hbands_564000 : AllZeros_h564000.BandHyp)
    (hbands_565000 : AllZeros_h565000.BandHyp)
    (hbands_566000 : AllZeros_h566000.BandHyp)
    (hbands_567000 : AllZeros_h567000.BandHyp)
    (hbands_568000 : AllZeros_h568000.BandHyp)
    (hbands_569000 : AllZeros_h569000.BandHyp)
    (hbands_570000 : AllZeros_h570000.BandHyp)
    (hbands_571000 : AllZeros_h571000.BandHyp)
    (hbands_572000 : AllZeros_h572000.BandHyp)
    (hbands_573000 : AllZeros_h573000.BandHyp)
    (hbands_574000 : AllZeros_h574000.BandHyp)
    (hbands_575000 : AllZeros_h575000.BandHyp)
    (hbands_576000 : AllZeros_h576000.BandHyp)
    (hbands_577000 : AllZeros_h577000.BandHyp)
    (hbands_578000 : AllZeros_h578000.BandHyp)
    (hbands_579000 : AllZeros_h579000.BandHyp)
    (hbands_580000 : AllZeros_h580000.BandHyp)
    (hbands_581000 : AllZeros_h581000.BandHyp)
    (hbands_582000 : AllZeros_h582000.BandHyp)
    (hbands_583000 : AllZeros_h583000.BandHyp)
    (hbands_584000 : AllZeros_h584000.BandHyp)
    (hbands_585000 : AllZeros_h585000.BandHyp)
    (hbands_586000 : AllZeros_h586000.BandHyp)
    (hbands_587000 : AllZeros_h587000.BandHyp)
    (hbands_588000 : AllZeros_h588000.BandHyp)
    (hbands_589000 : AllZeros_h589000.BandHyp)
    (hbands_590000 : AllZeros_h590000.BandHyp)
    (hbands_591000 : AllZeros_h591000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 592000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 592000 → ρ.re = 1 / 2 := by
  have hγ591000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 591000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 591000 592000
    (AllZeros_h591000.all_nontrivial_zeros_up_to_height_591000_of_bands
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
      hbands_132000
      hbands_133000
      hbands_134000
      hbands_135000
      hbands_136000
      hbands_137000
      hbands_138000
      hbands_139000
      hbands_140000
      hbands_141000
      hbands_142000
      hbands_143000
      hbands_144000
      hbands_145000
      hbands_146000
      hbands_147000
      hbands_148000
      hbands_149000
      hbands_150000
      hbands_151000
      hbands_152000
      hbands_153000
      hbands_154000
      hbands_155000
      hbands_156000
      hbands_157000
      hbands_158000
      hbands_159000
      hbands_160000
      hbands_161000
      hbands_162000
      hbands_163000
      hbands_164000
      hbands_165000
      hbands_166000
      hbands_167000
      hbands_168000
      hbands_169000
      hbands_170000
      hbands_171000
      hbands_172000
      hbands_173000
      hbands_174000
      hbands_175000
      hbands_176000
      hbands_177000
      hbands_178000
      hbands_179000
      hbands_180000
      hbands_181000
      hbands_182000
      hbands_183000
      hbands_184000
      hbands_185000
      hbands_186000
      hbands_187000
      hbands_188000
      hbands_189000
      hbands_190000
      hbands_191000
      hbands_192000
      hbands_193000
      hbands_194000
      hbands_195000
      hbands_196000
      hbands_197000
      hbands_198000
      hbands_199000
      hbands_200000
      hbands_201000
      hbands_202000
      hbands_203000
      hbands_204000
      hbands_205000
      hbands_206000
      hbands_207000
      hbands_208000
      hbands_209000
      hbands_210000
      hbands_211000
      hbands_212000
      hbands_213000
      hbands_214000
      hbands_215000
      hbands_216000
      hbands_217000
      hbands_218000
      hbands_219000
      hbands_220000
      hbands_221000
      hbands_222000
      hbands_223000
      hbands_224000
      hbands_225000
      hbands_226000
      hbands_227000
      hbands_228000
      hbands_229000
      hbands_230000
      hbands_231000
      hbands_232000
      hbands_233000
      hbands_234000
      hbands_235000
      hbands_236000
      hbands_237000
      hbands_238000
      hbands_239000
      hbands_240000
      hbands_241000
      hbands_242000
      hbands_243000
      hbands_244000
      hbands_245000
      hbands_246000
      hbands_247000
      hbands_248000
      hbands_249000
      hbands_250000
      hbands_251000
      hbands_252000
      hbands_253000
      hbands_254000
      hbands_255000
      hbands_256000
      hbands_257000
      hbands_258000
      hbands_259000
      hbands_260000
      hbands_261000
      hbands_262000
      hbands_263000
      hbands_264000
      hbands_265000
      hbands_266000
      hbands_267000
      hbands_268000
      hbands_269000
      hbands_270000
      hbands_271000
      hbands_272000
      hbands_273000
      hbands_274000
      hbands_275000
      hbands_276000
      hbands_277000
      hbands_278000
      hbands_279000
      hbands_280000
      hbands_281000
      hbands_282000
      hbands_283000
      hbands_284000
      hbands_285000
      hbands_286000
      hbands_287000
      hbands_288000
      hbands_289000
      hbands_290000
      hbands_291000
      hbands_292000
      hbands_293000
      hbands_294000
      hbands_295000
      hbands_296000
      hbands_297000
      hbands_298000
      hbands_299000
      hbands_300000
      hbands_301000
      hbands_302000
      hbands_303000
      hbands_304000
      hbands_305000
      hbands_306000
      hbands_307000
      hbands_308000
      hbands_309000
      hbands_310000
      hbands_311000
      hbands_312000
      hbands_313000
      hbands_314000
      hbands_315000
      hbands_316000
      hbands_317000
      hbands_318000
      hbands_319000
      hbands_320000
      hbands_321000
      hbands_322000
      hbands_323000
      hbands_324000
      hbands_325000
      hbands_326000
      hbands_327000
      hbands_328000
      hbands_329000
      hbands_330000
      hbands_331000
      hbands_332000
      hbands_333000
      hbands_334000
      hbands_335000
      hbands_336000
      hbands_337000
      hbands_338000
      hbands_339000
      hbands_340000
      hbands_341000
      hbands_342000
      hbands_343000
      hbands_344000
      hbands_345000
      hbands_346000
      hbands_347000
      hbands_348000
      hbands_349000
      hbands_350000
      hbands_351000
      hbands_352000
      hbands_353000
      hbands_354000
      hbands_355000
      hbands_356000
      hbands_357000
      hbands_358000
      hbands_359000
      hbands_360000
      hbands_361000
      hbands_362000
      hbands_363000
      hbands_364000
      hbands_365000
      hbands_366000
      hbands_367000
      hbands_368000
      hbands_369000
      hbands_370000
      hbands_371000
      hbands_372000
      hbands_373000
      hbands_374000
      hbands_375000
      hbands_376000
      hbands_377000
      hbands_378000
      hbands_379000
      hbands_380000
      hbands_381000
      hbands_382000
      hbands_383000
      hbands_384000
      hbands_385000
      hbands_386000
      hbands_387000
      hbands_388000
      hbands_389000
      hbands_390000
      hbands_391000
      hbands_392000
      hbands_393000
      hbands_394000
      hbands_395000
      hbands_396000
      hbands_397000
      hbands_398000
      hbands_399000
      hbands_400000
      hbands_401000
      hbands_402000
      hbands_403000
      hbands_404000
      hbands_405000
      hbands_406000
      hbands_407000
      hbands_408000
      hbands_409000
      hbands_410000
      hbands_411000
      hbands_412000
      hbands_413000
      hbands_414000
      hbands_415000
      hbands_416000
      hbands_417000
      hbands_418000
      hbands_419000
      hbands_420000
      hbands_421000
      hbands_422000
      hbands_423000
      hbands_424000
      hbands_425000
      hbands_426000
      hbands_427000
      hbands_428000
      hbands_429000
      hbands_430000
      hbands_431000
      hbands_432000
      hbands_433000
      hbands_434000
      hbands_435000
      hbands_436000
      hbands_437000
      hbands_438000
      hbands_439000
      hbands_440000
      hbands_441000
      hbands_442000
      hbands_443000
      hbands_444000
      hbands_445000
      hbands_446000
      hbands_447000
      hbands_448000
      hbands_449000
      hbands_450000
      hbands_451000
      hbands_452000
      hbands_453000
      hbands_454000
      hbands_455000
      hbands_456000
      hbands_457000
      hbands_458000
      hbands_459000
      hbands_460000
      hbands_461000
      hbands_462000
      hbands_463000
      hbands_464000
      hbands_465000
      hbands_466000
      hbands_467000
      hbands_468000
      hbands_469000
      hbands_470000
      hbands_471000
      hbands_472000
      hbands_473000
      hbands_474000
      hbands_475000
      hbands_476000
      hbands_477000
      hbands_478000
      hbands_479000
      hbands_480000
      hbands_481000
      hbands_482000
      hbands_483000
      hbands_484000
      hbands_485000
      hbands_486000
      hbands_487000
      hbands_488000
      hbands_489000
      hbands_490000
      hbands_491000
      hbands_492000
      hbands_493000
      hbands_494000
      hbands_495000
      hbands_496000
      hbands_497000
      hbands_498000
      hbands_499000
      hbands_500000
      hbands_501000
      hbands_502000
      hbands_503000
      hbands_504000
      hbands_505000
      hbands_506000
      hbands_507000
      hbands_508000
      hbands_509000
      hbands_510000
      hbands_511000
      hbands_512000
      hbands_513000
      hbands_514000
      hbands_515000
      hbands_516000
      hbands_517000
      hbands_518000
      hbands_519000
      hbands_520000
      hbands_521000
      hbands_522000
      hbands_523000
      hbands_524000
      hbands_525000
      hbands_526000
      hbands_527000
      hbands_528000
      hbands_529000
      hbands_530000
      hbands_531000
      hbands_532000
      hbands_533000
      hbands_534000
      hbands_535000
      hbands_536000
      hbands_537000
      hbands_538000
      hbands_539000
      hbands_540000
      hbands_541000
      hbands_542000
      hbands_543000
      hbands_544000
      hbands_545000
      hbands_546000
      hbands_547000
      hbands_548000
      hbands_549000
      hbands_550000
      hbands_551000
      hbands_552000
      hbands_553000
      hbands_554000
      hbands_555000
      hbands_556000
      hbands_557000
      hbands_558000
      hbands_559000
      hbands_560000
      hbands_561000
      hbands_562000
      hbands_563000
      hbands_564000
      hbands_565000
      hbands_566000
      hbands_567000
      hbands_568000
      hbands_569000
      hbands_570000
      hbands_571000
      hbands_572000
      hbands_573000
      hbands_574000
      hbands_575000
      hbands_576000
      hbands_577000
      hbands_578000
      hbands_579000
      hbands_580000
      hbands_581000
      hbands_582000
      hbands_583000
      hbands_584000
      hbands_585000
      hbands_586000
      hbands_587000
      hbands_588000
      hbands_589000
      hbands_590000
      hbands_591000
      hγ591000)
    (segment_591000_592000 hbands hγ)

end AllZeros_h592000
