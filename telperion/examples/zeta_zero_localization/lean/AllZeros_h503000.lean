/-  Height-chain step: all nontrivial zeta zeros up to height 503000 on Re = 1/2 --
    `AllZeros_h502000` + a `[502000, 503000]` SEGMENT certificate (44 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h502000
import RHInBoxT_1d4000000_3999999d4000000_502000_502023
import RHInBoxT_1d4000000_3999999d4000000_502023_502045
import RHInBoxT_1d4000000_3999999d4000000_502045_502068
import RHInBoxT_1d4000000_3999999d4000000_502068_502091
import RHInBoxT_1d4000000_3999999d4000000_502091_502114
import RHInBoxT_1d4000000_3999999d4000000_502114_502136
import RHInBoxT_1d4000000_3999999d4000000_502136_502159
import RHInBoxT_1d4000000_3999999d4000000_502159_502182
import RHInBoxT_1d4000000_3999999d4000000_502182_502205
import RHInBoxT_1d4000000_3999999d4000000_502205_502227
import RHInBoxT_1d4000000_3999999d4000000_502227_502250
import RHInBoxT_1d4000000_3999999d4000000_502250_502273
import RHInBoxT_1d4000000_3999999d4000000_502273_502295
import RHInBoxT_1d4000000_3999999d4000000_2009179d4_502318
import RHInBoxT_1d4000000_3999999d4000000_502318_502341
import RHInBoxT_1d4000000_3999999d4000000_2009363d4_502364
import RHInBoxT_1d4000000_3999999d4000000_502364_502386
import RHInBoxT_1d4000000_3999999d4000000_502386_502409
import RHInBoxT_1d4000000_3999999d4000000_502409_502432
import RHInBoxT_1d4000000_3999999d4000000_502432_502455
import RHInBoxT_1d4000000_3999999d4000000_502455_502477
import RHInBoxT_1d4000000_3999999d4000000_502477_502500
import RHInBoxT_1d4000000_3999999d4000000_502500_502523
import RHInBoxT_1d4000000_3999999d4000000_502523_502545
import RHInBoxT_1d4000000_3999999d4000000_502545_502568
import RHInBoxT_1d4000000_3999999d4000000_2010271d4_502591
import RHInBoxT_1d4000000_3999999d4000000_502591_502614
import RHInBoxT_1d4000000_3999999d4000000_502614_502636
import RHInBoxT_1d4000000_3999999d4000000_2010543d4_502659
import RHInBoxT_1d4000000_3999999d4000000_502659_2010729d4
import RHInBoxT_1d4000000_3999999d4000000_502682_502705
import RHInBoxT_1d4000000_3999999d4000000_502705_502727
import RHInBoxT_1d4000000_3999999d4000000_502727_502750
import RHInBoxT_1d4000000_3999999d4000000_502750_502773
import RHInBoxT_1d4000000_3999999d4000000_2011091d4_502795
import RHInBoxT_1d4000000_3999999d4000000_502795_502818
import RHInBoxT_1d4000000_3999999d4000000_502818_502841
import RHInBoxT_1d4000000_3999999d4000000_502841_1005729d2
import RHInBoxT_1d4000000_3999999d4000000_502864_2011545d4
import RHInBoxT_1d4000000_3999999d4000000_502886_2011637d4
import RHInBoxT_1d4000000_3999999d4000000_502909_2011729d4
import RHInBoxT_1d4000000_3999999d4000000_502932_502955
import RHInBoxT_1d4000000_3999999d4000000_502955_502977
import RHInBoxT_1d4000000_3999999d4000000_502977_503000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h503000

/-- The 44-band NOMINAL partition of `[502000, 503000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 502000
  | 1 => 502023
  | 2 => 502045
  | 3 => 502068
  | 4 => 502091
  | 5 => 502114
  | 6 => 502136
  | 7 => 502159
  | 8 => 502182
  | 9 => 502205
  | 10 => 502227
  | 11 => 502250
  | 12 => 502273
  | 13 => 502295
  | 14 => 502318
  | 15 => 502341
  | 16 => 502364
  | 17 => 502386
  | 18 => 502409
  | 19 => 502432
  | 20 => 502455
  | 21 => 502477
  | 22 => 502500
  | 23 => 502523
  | 24 => 502545
  | 25 => 502568
  | 26 => 502591
  | 27 => 502614
  | 28 => 502636
  | 29 => 502659
  | 30 => 502682
  | 31 => 502705
  | 32 => 502727
  | 33 => 502750
  | 34 => 502773
  | 35 => 502795
  | 36 => 502818
  | 37 => 502841
  | 38 => 502864
  | 39 => 502886
  | 40 => 502909
  | 41 => 502932
  | 42 => 502955
  | 43 => 502977
  | 44 => 503000
  | _ => 503000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((502000:ℝ)) ≤ (502023); norm_num
  · show ((502023:ℝ)) ≤ (502045); norm_num
  · show ((502045:ℝ)) ≤ (502068); norm_num
  · show ((502068:ℝ)) ≤ (502091); norm_num
  · show ((502091:ℝ)) ≤ (502114); norm_num
  · show ((502114:ℝ)) ≤ (502136); norm_num
  · show ((502136:ℝ)) ≤ (502159); norm_num
  · show ((502159:ℝ)) ≤ (502182); norm_num
  · show ((502182:ℝ)) ≤ (502205); norm_num
  · show ((502205:ℝ)) ≤ (502227); norm_num
  · show ((502227:ℝ)) ≤ (502250); norm_num
  · show ((502250:ℝ)) ≤ (502273); norm_num
  · show ((502273:ℝ)) ≤ (502295); norm_num
  · show ((502295:ℝ)) ≤ (502318); norm_num
  · show ((502318:ℝ)) ≤ (502341); norm_num
  · show ((502341:ℝ)) ≤ (502364); norm_num
  · show ((502364:ℝ)) ≤ (502386); norm_num
  · show ((502386:ℝ)) ≤ (502409); norm_num
  · show ((502409:ℝ)) ≤ (502432); norm_num
  · show ((502432:ℝ)) ≤ (502455); norm_num
  · show ((502455:ℝ)) ≤ (502477); norm_num
  · show ((502477:ℝ)) ≤ (502500); norm_num
  · show ((502500:ℝ)) ≤ (502523); norm_num
  · show ((502523:ℝ)) ≤ (502545); norm_num
  · show ((502545:ℝ)) ≤ (502568); norm_num
  · show ((502568:ℝ)) ≤ (502591); norm_num
  · show ((502591:ℝ)) ≤ (502614); norm_num
  · show ((502614:ℝ)) ≤ (502636); norm_num
  · show ((502636:ℝ)) ≤ (502659); norm_num
  · show ((502659:ℝ)) ≤ (502682); norm_num
  · show ((502682:ℝ)) ≤ (502705); norm_num
  · show ((502705:ℝ)) ≤ (502727); norm_num
  · show ((502727:ℝ)) ≤ (502750); norm_num
  · show ((502750:ℝ)) ≤ (502773); norm_num
  · show ((502773:ℝ)) ≤ (502795); norm_num
  · show ((502795:ℝ)) ≤ (502818); norm_num
  · show ((502818:ℝ)) ≤ (502841); norm_num
  · show ((502841:ℝ)) ≤ (502864); norm_num
  · show ((502864:ℝ)) ≤ (502886); norm_num
  · show ((502886:ℝ)) ≤ (502909); norm_num
  · show ((502909:ℝ)) ≤ (502932); norm_num
  · show ((502932:ℝ)) ≤ (502955); norm_num
  · show ((502955:ℝ)) ≤ (502977); norm_num
  · show ((502977:ℝ)) ≤ (503000); norm_num
  · show ((503000:ℝ)) ≤ (503000); norm_num
  · exact le_refl _

/-- The lower edges of the 44 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 502000
  | 1 => 502023
  | 2 => 502045
  | 3 => 502068
  | 4 => 502091
  | 5 => 502114
  | 6 => 502136
  | 7 => 502159
  | 8 => 502182
  | 9 => 502205
  | 10 => 502227
  | 11 => 502250
  | 12 => 502273
  | 13 => 2009179 / 4
  | 14 => 502318
  | 15 => 2009363 / 4
  | 16 => 502364
  | 17 => 502386
  | 18 => 502409
  | 19 => 502432
  | 20 => 502455
  | 21 => 502477
  | 22 => 502500
  | 23 => 502523
  | 24 => 502545
  | 25 => 2010271 / 4
  | 26 => 502591
  | 27 => 502614
  | 28 => 2010543 / 4
  | 29 => 502659
  | 30 => 502682
  | 31 => 502705
  | 32 => 502727
  | 33 => 502750
  | 34 => 2011091 / 4
  | 35 => 502795
  | 36 => 502818
  | 37 => 502841
  | 38 => 502864
  | 39 => 502886
  | 40 => 502909
  | 41 => 502932
  | 42 => 502955
  | 43 => 502977
  | _ => 502977

/-- The upper edges of the 44 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 502023
  | 1 => 502045
  | 2 => 502068
  | 3 => 502091
  | 4 => 502114
  | 5 => 502136
  | 6 => 502159
  | 7 => 502182
  | 8 => 502205
  | 9 => 502227
  | 10 => 502250
  | 11 => 502273
  | 12 => 502295
  | 13 => 502318
  | 14 => 502341
  | 15 => 502364
  | 16 => 502386
  | 17 => 502409
  | 18 => 502432
  | 19 => 502455
  | 20 => 502477
  | 21 => 502500
  | 22 => 502523
  | 23 => 502545
  | 24 => 502568
  | 25 => 502591
  | 26 => 502614
  | 27 => 502636
  | 28 => 502659
  | 29 => 2010729 / 4
  | 30 => 502705
  | 31 => 502727
  | 32 => 502750
  | 33 => 502773
  | 34 => 502795
  | 35 => 502818
  | 36 => 502841
  | 37 => 1005729 / 2
  | 38 => 2011545 / 4
  | 39 => 2011637 / 4
  | 40 => 2011729 / 4
  | 41 => 502955
  | 42 => 502977
  | 43 => 503000
  | _ => 503000

set_option maxHeartbeats 1600000 in
/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 44 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 503000` (`log 503000 ≤ 14`, `2.7^14 ≥ 503000`). -/
theorem haC_503000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 503000 := by
  have hlog : Real.log 503000 ≤ 14 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h14 : Real.exp 14 = (Real.exp 1) ^ 14 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 14 ≤ (Real.exp 1) ^ 14 := pow_le_pow_left₀ (by norm_num) he1 14
    rw [h14]; nlinarith [hpow]
  have hpos : 0 < Real.log 503000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 503000
      ≤ (1 / 4000000) * 14 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[502000, 503000]` segment's band hypothesis: every band `i < 44` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 44 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 44 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[502000, 503000]` SEGMENT: every zero with `502000 ≤ Im ≤ 503000` is on the line. -/
theorem segment_502000_503000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 503000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (502000:ℝ) ≤ ρ.im → ρ.im ≤ 503000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 502000 503000 bndSeg 44 (by norm_num) bndSeg_mono rfl rfl haC_503000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 503000 via the HEIGHT CHAIN**: `[0,502000]` ∘ `[502000,503000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_503000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 503000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 503000 → ρ.re = 1 / 2 := by
  have hγ502000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 502000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 502000 503000
    (AllZeros_h502000.all_nontrivial_zeros_up_to_height_502000_of_bands
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
      hγ502000)
    (segment_502000_503000 hbands hγ)

end AllZeros_h503000
