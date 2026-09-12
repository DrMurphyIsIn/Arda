/-  Height-chain step: all nontrivial zeta zeros up to height 41000 on Re = 1/2 --
    `AllZeros_h40000` + a `[40000, 41000]` SEGMENT certificate (34 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h40000
import RHInBoxT_1d4000000_3999999d4000000_40000_40029
import RHInBoxT_1d4000000_3999999d4000000_40029_40059
import RHInBoxT_1d4000000_3999999d4000000_40059_40088
import RHInBoxT_1d4000000_3999999d4000000_40088_40118
import RHInBoxT_1d4000000_3999999d4000000_40118_40147
import RHInBoxT_1d4000000_3999999d4000000_40147_40176
import RHInBoxT_1d4000000_3999999d4000000_40176_40206
import RHInBoxT_1d4000000_3999999d4000000_40206_40235
import RHInBoxT_1d4000000_3999999d4000000_40235_40265
import RHInBoxT_1d4000000_3999999d4000000_40265_40294
import RHInBoxT_1d4000000_3999999d4000000_40294_40324
import RHInBoxT_1d4000000_3999999d4000000_161295d4_40353
import RHInBoxT_1d4000000_3999999d4000000_40353_40382
import RHInBoxT_1d4000000_3999999d4000000_40382_40412
import RHInBoxT_1d4000000_3999999d4000000_40412_40441
import RHInBoxT_1d4000000_3999999d4000000_40441_40471
import RHInBoxT_1d4000000_3999999d4000000_161883d4_40500
import RHInBoxT_1d4000000_3999999d4000000_40500_40529
import RHInBoxT_1d4000000_3999999d4000000_162115d4_40559
import RHInBoxT_1d4000000_3999999d4000000_40559_40588
import RHInBoxT_1d4000000_3999999d4000000_40588_40618
import RHInBoxT_1d4000000_3999999d4000000_162471d4_40647
import RHInBoxT_1d4000000_3999999d4000000_40647_162705d4
import RHInBoxT_1d4000000_3999999d4000000_40676_40706
import RHInBoxT_1d4000000_3999999d4000000_40706_40735
import RHInBoxT_1d4000000_3999999d4000000_162939d4_40765
import RHInBoxT_1d4000000_3999999d4000000_40765_40794
import RHInBoxT_1d4000000_3999999d4000000_40794_40824
import RHInBoxT_1d4000000_3999999d4000000_40824_40853
import RHInBoxT_1d4000000_3999999d4000000_40853_40882
import RHInBoxT_1d4000000_3999999d4000000_40882_40912
import RHInBoxT_1d4000000_3999999d4000000_40912_40941
import RHInBoxT_1d4000000_3999999d4000000_40941_40971
import RHInBoxT_1d4000000_3999999d4000000_40971_41000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h41000

/-- The 34-band NOMINAL partition of `[40000, 41000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 40000
  | 1 => 40029
  | 2 => 40059
  | 3 => 40088
  | 4 => 40118
  | 5 => 40147
  | 6 => 40176
  | 7 => 40206
  | 8 => 40235
  | 9 => 40265
  | 10 => 40294
  | 11 => 40324
  | 12 => 40353
  | 13 => 40382
  | 14 => 40412
  | 15 => 40441
  | 16 => 40471
  | 17 => 40500
  | 18 => 40529
  | 19 => 40559
  | 20 => 40588
  | 21 => 40618
  | 22 => 40647
  | 23 => 40676
  | 24 => 40706
  | 25 => 40735
  | 26 => 40765
  | 27 => 40794
  | 28 => 40824
  | 29 => 40853
  | 30 => 40882
  | 31 => 40912
  | 32 => 40941
  | 33 => 40971
  | 34 => 41000
  | _ => 41000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((40000:ℝ)) ≤ (40029); norm_num
  · show ((40029:ℝ)) ≤ (40059); norm_num
  · show ((40059:ℝ)) ≤ (40088); norm_num
  · show ((40088:ℝ)) ≤ (40118); norm_num
  · show ((40118:ℝ)) ≤ (40147); norm_num
  · show ((40147:ℝ)) ≤ (40176); norm_num
  · show ((40176:ℝ)) ≤ (40206); norm_num
  · show ((40206:ℝ)) ≤ (40235); norm_num
  · show ((40235:ℝ)) ≤ (40265); norm_num
  · show ((40265:ℝ)) ≤ (40294); norm_num
  · show ((40294:ℝ)) ≤ (40324); norm_num
  · show ((40324:ℝ)) ≤ (40353); norm_num
  · show ((40353:ℝ)) ≤ (40382); norm_num
  · show ((40382:ℝ)) ≤ (40412); norm_num
  · show ((40412:ℝ)) ≤ (40441); norm_num
  · show ((40441:ℝ)) ≤ (40471); norm_num
  · show ((40471:ℝ)) ≤ (40500); norm_num
  · show ((40500:ℝ)) ≤ (40529); norm_num
  · show ((40529:ℝ)) ≤ (40559); norm_num
  · show ((40559:ℝ)) ≤ (40588); norm_num
  · show ((40588:ℝ)) ≤ (40618); norm_num
  · show ((40618:ℝ)) ≤ (40647); norm_num
  · show ((40647:ℝ)) ≤ (40676); norm_num
  · show ((40676:ℝ)) ≤ (40706); norm_num
  · show ((40706:ℝ)) ≤ (40735); norm_num
  · show ((40735:ℝ)) ≤ (40765); norm_num
  · show ((40765:ℝ)) ≤ (40794); norm_num
  · show ((40794:ℝ)) ≤ (40824); norm_num
  · show ((40824:ℝ)) ≤ (40853); norm_num
  · show ((40853:ℝ)) ≤ (40882); norm_num
  · show ((40882:ℝ)) ≤ (40912); norm_num
  · show ((40912:ℝ)) ≤ (40941); norm_num
  · show ((40941:ℝ)) ≤ (40971); norm_num
  · show ((40971:ℝ)) ≤ (41000); norm_num
  · show ((41000:ℝ)) ≤ (41000); norm_num
  · exact le_refl _

/-- The lower edges of the 34 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 40000
  | 1 => 40029
  | 2 => 40059
  | 3 => 40088
  | 4 => 40118
  | 5 => 40147
  | 6 => 40176
  | 7 => 40206
  | 8 => 40235
  | 9 => 40265
  | 10 => 40294
  | 11 => 161295 / 4
  | 12 => 40353
  | 13 => 40382
  | 14 => 40412
  | 15 => 40441
  | 16 => 161883 / 4
  | 17 => 40500
  | 18 => 162115 / 4
  | 19 => 40559
  | 20 => 40588
  | 21 => 162471 / 4
  | 22 => 40647
  | 23 => 40676
  | 24 => 40706
  | 25 => 162939 / 4
  | 26 => 40765
  | 27 => 40794
  | 28 => 40824
  | 29 => 40853
  | 30 => 40882
  | 31 => 40912
  | 32 => 40941
  | 33 => 40971
  | _ => 40971

/-- The upper edges of the 34 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 40029
  | 1 => 40059
  | 2 => 40088
  | 3 => 40118
  | 4 => 40147
  | 5 => 40176
  | 6 => 40206
  | 7 => 40235
  | 8 => 40265
  | 9 => 40294
  | 10 => 40324
  | 11 => 40353
  | 12 => 40382
  | 13 => 40412
  | 14 => 40441
  | 15 => 40471
  | 16 => 40500
  | 17 => 40529
  | 18 => 40559
  | 19 => 40588
  | 20 => 40618
  | 21 => 40647
  | 22 => 162705 / 4
  | 23 => 40706
  | 24 => 40735
  | 25 => 40765
  | 26 => 40794
  | 27 => 40824
  | 28 => 40853
  | 29 => 40882
  | 30 => 40912
  | 31 => 40941
  | 32 => 40971
  | 33 => 41000
  | _ => 41000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 34 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 41000` (`log 41000 ≤ 11`, `2.7^11 ≥ 41000`). -/
theorem haC_41000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 41000 := by
  have hlog : Real.log 41000 ≤ 11 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h11 : Real.exp 11 = (Real.exp 1) ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 11 ≤ (Real.exp 1) ^ 11 := pow_le_pow_left₀ (by norm_num) he1 11
    rw [h11]; nlinarith [hpow]
  have hpos : 0 < Real.log 41000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 41000
      ≤ (1 / 4000000) * 11 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[40000, 41000]` segment's band hypothesis: every band `i < 34` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 34 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 34 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[40000, 41000]` SEGMENT: every zero with `40000 ≤ Im ≤ 41000` is on the line. -/
theorem segment_40000_41000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 41000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (40000:ℝ) ≤ ρ.im → ρ.im ≤ 41000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 40000 41000 bndSeg 34 (by norm_num) bndSeg_mono rfl rfl haC_41000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 41000 via the HEIGHT CHAIN**: `[0,40000]` ∘ `[40000,41000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_41000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 41000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 41000 → ρ.re = 1 / 2 := by
  have hγ40000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 40000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 40000 41000
    (AllZeros_h40000.all_nontrivial_zeros_up_to_height_40000_of_bands
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
      hγ40000)
    (segment_40000_41000 hbands hγ)

end AllZeros_h41000
