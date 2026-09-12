/-  Height-chain step: all nontrivial zeta zeros up to height 58000 on Re = 1/2 --
    `AllZeros_h57000` + a `[57000, 58000]` SEGMENT certificate (35 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h57000
import RHInBoxT_1d4000000_3999999d4000000_57000_57029
import RHInBoxT_1d4000000_3999999d4000000_57029_57057
import RHInBoxT_1d4000000_3999999d4000000_57057_57086
import RHInBoxT_1d4000000_3999999d4000000_57086_57114
import RHInBoxT_1d4000000_3999999d4000000_57114_57143
import RHInBoxT_1d4000000_3999999d4000000_57143_57171
import RHInBoxT_1d4000000_3999999d4000000_57171_57200
import RHInBoxT_1d4000000_3999999d4000000_57200_57229
import RHInBoxT_1d4000000_3999999d4000000_57229_57257
import RHInBoxT_1d4000000_3999999d4000000_229027d4_57286
import RHInBoxT_1d4000000_3999999d4000000_57286_57314
import RHInBoxT_1d4000000_3999999d4000000_57314_229373d4
import RHInBoxT_1d4000000_3999999d4000000_57343_57371
import RHInBoxT_1d4000000_3999999d4000000_57371_57400
import RHInBoxT_1d4000000_3999999d4000000_57400_57429
import RHInBoxT_1d4000000_3999999d4000000_229715d4_57457
import RHInBoxT_1d4000000_3999999d4000000_57457_57486
import RHInBoxT_1d4000000_3999999d4000000_57486_57514
import RHInBoxT_1d4000000_3999999d4000000_57514_57543
import RHInBoxT_1d4000000_3999999d4000000_57543_57571
import RHInBoxT_1d4000000_3999999d4000000_57571_57600
import RHInBoxT_1d4000000_3999999d4000000_57600_57629
import RHInBoxT_1d4000000_3999999d4000000_230515d4_57657
import RHInBoxT_1d4000000_3999999d4000000_230627d4_230745d4
import RHInBoxT_1d4000000_3999999d4000000_57686_57714
import RHInBoxT_1d4000000_3999999d4000000_57714_57743
import RHInBoxT_1d4000000_3999999d4000000_57743_57771
import RHInBoxT_1d4000000_3999999d4000000_57771_57800
import RHInBoxT_1d4000000_3999999d4000000_57800_57829
import RHInBoxT_1d4000000_3999999d4000000_57829_57857
import RHInBoxT_1d4000000_3999999d4000000_57857_231545d4
import RHInBoxT_1d4000000_3999999d4000000_57886_57914
import RHInBoxT_1d4000000_3999999d4000000_57914_57943
import RHInBoxT_1d4000000_3999999d4000000_57943_57971
import RHInBoxT_1d4000000_3999999d4000000_57971_58000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h58000

/-- The 35-band NOMINAL partition of `[57000, 58000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 57000
  | 1 => 57029
  | 2 => 57057
  | 3 => 57086
  | 4 => 57114
  | 5 => 57143
  | 6 => 57171
  | 7 => 57200
  | 8 => 57229
  | 9 => 57257
  | 10 => 57286
  | 11 => 57314
  | 12 => 57343
  | 13 => 57371
  | 14 => 57400
  | 15 => 57429
  | 16 => 57457
  | 17 => 57486
  | 18 => 57514
  | 19 => 57543
  | 20 => 57571
  | 21 => 57600
  | 22 => 57629
  | 23 => 57657
  | 24 => 57686
  | 25 => 57714
  | 26 => 57743
  | 27 => 57771
  | 28 => 57800
  | 29 => 57829
  | 30 => 57857
  | 31 => 57886
  | 32 => 57914
  | 33 => 57943
  | 34 => 57971
  | 35 => 58000
  | _ => 58000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((57000:ℝ)) ≤ (57029); norm_num
  · show ((57029:ℝ)) ≤ (57057); norm_num
  · show ((57057:ℝ)) ≤ (57086); norm_num
  · show ((57086:ℝ)) ≤ (57114); norm_num
  · show ((57114:ℝ)) ≤ (57143); norm_num
  · show ((57143:ℝ)) ≤ (57171); norm_num
  · show ((57171:ℝ)) ≤ (57200); norm_num
  · show ((57200:ℝ)) ≤ (57229); norm_num
  · show ((57229:ℝ)) ≤ (57257); norm_num
  · show ((57257:ℝ)) ≤ (57286); norm_num
  · show ((57286:ℝ)) ≤ (57314); norm_num
  · show ((57314:ℝ)) ≤ (57343); norm_num
  · show ((57343:ℝ)) ≤ (57371); norm_num
  · show ((57371:ℝ)) ≤ (57400); norm_num
  · show ((57400:ℝ)) ≤ (57429); norm_num
  · show ((57429:ℝ)) ≤ (57457); norm_num
  · show ((57457:ℝ)) ≤ (57486); norm_num
  · show ((57486:ℝ)) ≤ (57514); norm_num
  · show ((57514:ℝ)) ≤ (57543); norm_num
  · show ((57543:ℝ)) ≤ (57571); norm_num
  · show ((57571:ℝ)) ≤ (57600); norm_num
  · show ((57600:ℝ)) ≤ (57629); norm_num
  · show ((57629:ℝ)) ≤ (57657); norm_num
  · show ((57657:ℝ)) ≤ (57686); norm_num
  · show ((57686:ℝ)) ≤ (57714); norm_num
  · show ((57714:ℝ)) ≤ (57743); norm_num
  · show ((57743:ℝ)) ≤ (57771); norm_num
  · show ((57771:ℝ)) ≤ (57800); norm_num
  · show ((57800:ℝ)) ≤ (57829); norm_num
  · show ((57829:ℝ)) ≤ (57857); norm_num
  · show ((57857:ℝ)) ≤ (57886); norm_num
  · show ((57886:ℝ)) ≤ (57914); norm_num
  · show ((57914:ℝ)) ≤ (57943); norm_num
  · show ((57943:ℝ)) ≤ (57971); norm_num
  · show ((57971:ℝ)) ≤ (58000); norm_num
  · show ((58000:ℝ)) ≤ (58000); norm_num
  · exact le_refl _

/-- The lower edges of the 35 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 57000
  | 1 => 57029
  | 2 => 57057
  | 3 => 57086
  | 4 => 57114
  | 5 => 57143
  | 6 => 57171
  | 7 => 57200
  | 8 => 57229
  | 9 => 229027 / 4
  | 10 => 57286
  | 11 => 57314
  | 12 => 57343
  | 13 => 57371
  | 14 => 57400
  | 15 => 229715 / 4
  | 16 => 57457
  | 17 => 57486
  | 18 => 57514
  | 19 => 57543
  | 20 => 57571
  | 21 => 57600
  | 22 => 230515 / 4
  | 23 => 230627 / 4
  | 24 => 57686
  | 25 => 57714
  | 26 => 57743
  | 27 => 57771
  | 28 => 57800
  | 29 => 57829
  | 30 => 57857
  | 31 => 57886
  | 32 => 57914
  | 33 => 57943
  | 34 => 57971
  | _ => 57971

/-- The upper edges of the 35 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 57029
  | 1 => 57057
  | 2 => 57086
  | 3 => 57114
  | 4 => 57143
  | 5 => 57171
  | 6 => 57200
  | 7 => 57229
  | 8 => 57257
  | 9 => 57286
  | 10 => 57314
  | 11 => 229373 / 4
  | 12 => 57371
  | 13 => 57400
  | 14 => 57429
  | 15 => 57457
  | 16 => 57486
  | 17 => 57514
  | 18 => 57543
  | 19 => 57571
  | 20 => 57600
  | 21 => 57629
  | 22 => 57657
  | 23 => 230745 / 4
  | 24 => 57714
  | 25 => 57743
  | 26 => 57771
  | 27 => 57800
  | 28 => 57829
  | 29 => 57857
  | 30 => 231545 / 4
  | 31 => 57914
  | 32 => 57943
  | 33 => 57971
  | 34 => 58000
  | _ => 58000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 35 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 58000` (`log 58000 ≤ 12`, `2.7^12 ≥ 58000`). -/
theorem haC_58000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 58000 := by
  have hlog : Real.log 58000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 58000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 58000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[57000, 58000]` segment's band hypothesis: every band `i < 35` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 35 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 35 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[57000, 58000]` SEGMENT: every zero with `57000 ≤ Im ≤ 58000` is on the line. -/
theorem segment_57000_58000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 58000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (57000:ℝ) ≤ ρ.im → ρ.im ≤ 58000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 57000 58000 bndSeg 35 (by norm_num) bndSeg_mono rfl rfl haC_58000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 58000 via the HEIGHT CHAIN**: `[0,57000]` ∘ `[57000,58000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_58000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 58000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 58000 → ρ.re = 1 / 2 := by
  have hγ57000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 57000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 57000 58000
    (AllZeros_h57000.all_nontrivial_zeros_up_to_height_57000_of_bands
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
      hγ57000)
    (segment_57000_58000 hbands hγ)

end AllZeros_h58000
