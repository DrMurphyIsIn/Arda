/-  Height-chain step: all nontrivial zeta zeros up to height 34000 on Re = 1/2 --
    `AllZeros_h33000` + a `[33000, 34000]` SEGMENT certificate (33 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h33000
import RHInBoxT_1d4000000_3999999d4000000_33000_33030
import RHInBoxT_1d4000000_3999999d4000000_33030_33061
import RHInBoxT_1d4000000_3999999d4000000_33061_33091
import RHInBoxT_1d4000000_3999999d4000000_33091_33121
import RHInBoxT_1d4000000_3999999d4000000_132483d4_33152
import RHInBoxT_1d4000000_3999999d4000000_33152_33182
import RHInBoxT_1d4000000_3999999d4000000_33182_33212
import RHInBoxT_1d4000000_3999999d4000000_33212_33242
import RHInBoxT_1d4000000_3999999d4000000_33242_33273
import RHInBoxT_1d4000000_3999999d4000000_33273_33303
import RHInBoxT_1d4000000_3999999d4000000_33303_33333
import RHInBoxT_1d4000000_3999999d4000000_33333_33364
import RHInBoxT_1d4000000_3999999d4000000_33364_33394
import RHInBoxT_1d4000000_3999999d4000000_33394_33424
import RHInBoxT_1d4000000_3999999d4000000_133695d4_33455
import RHInBoxT_1d4000000_3999999d4000000_33455_33485
import RHInBoxT_1d4000000_3999999d4000000_33485_33515
import RHInBoxT_1d4000000_3999999d4000000_33515_33545
import RHInBoxT_1d4000000_3999999d4000000_33545_33576
import RHInBoxT_1d4000000_3999999d4000000_33576_33606
import RHInBoxT_1d4000000_3999999d4000000_33606_33636
import RHInBoxT_1d4000000_3999999d4000000_33636_33667
import RHInBoxT_1d4000000_3999999d4000000_33667_33697
import RHInBoxT_1d4000000_3999999d4000000_33697_134909d4
import RHInBoxT_1d4000000_3999999d4000000_33727_33758
import RHInBoxT_1d4000000_3999999d4000000_33758_33788
import RHInBoxT_1d4000000_3999999d4000000_135151d4_33818
import RHInBoxT_1d4000000_3999999d4000000_33818_33848
import RHInBoxT_1d4000000_3999999d4000000_33848_135517d4
import RHInBoxT_1d4000000_3999999d4000000_33879_33909
import RHInBoxT_1d4000000_3999999d4000000_33909_33939
import RHInBoxT_1d4000000_3999999d4000000_135755d4_33970
import RHInBoxT_1d4000000_3999999d4000000_33970_34000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h34000

/-- The 33-band NOMINAL partition of `[33000, 34000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 33000
  | 1 => 33030
  | 2 => 33061
  | 3 => 33091
  | 4 => 33121
  | 5 => 33152
  | 6 => 33182
  | 7 => 33212
  | 8 => 33242
  | 9 => 33273
  | 10 => 33303
  | 11 => 33333
  | 12 => 33364
  | 13 => 33394
  | 14 => 33424
  | 15 => 33455
  | 16 => 33485
  | 17 => 33515
  | 18 => 33545
  | 19 => 33576
  | 20 => 33606
  | 21 => 33636
  | 22 => 33667
  | 23 => 33697
  | 24 => 33727
  | 25 => 33758
  | 26 => 33788
  | 27 => 33818
  | 28 => 33848
  | 29 => 33879
  | 30 => 33909
  | 31 => 33939
  | 32 => 33970
  | 33 => 34000
  | _ => 34000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((33000:ℝ)) ≤ (33030); norm_num
  · show ((33030:ℝ)) ≤ (33061); norm_num
  · show ((33061:ℝ)) ≤ (33091); norm_num
  · show ((33091:ℝ)) ≤ (33121); norm_num
  · show ((33121:ℝ)) ≤ (33152); norm_num
  · show ((33152:ℝ)) ≤ (33182); norm_num
  · show ((33182:ℝ)) ≤ (33212); norm_num
  · show ((33212:ℝ)) ≤ (33242); norm_num
  · show ((33242:ℝ)) ≤ (33273); norm_num
  · show ((33273:ℝ)) ≤ (33303); norm_num
  · show ((33303:ℝ)) ≤ (33333); norm_num
  · show ((33333:ℝ)) ≤ (33364); norm_num
  · show ((33364:ℝ)) ≤ (33394); norm_num
  · show ((33394:ℝ)) ≤ (33424); norm_num
  · show ((33424:ℝ)) ≤ (33455); norm_num
  · show ((33455:ℝ)) ≤ (33485); norm_num
  · show ((33485:ℝ)) ≤ (33515); norm_num
  · show ((33515:ℝ)) ≤ (33545); norm_num
  · show ((33545:ℝ)) ≤ (33576); norm_num
  · show ((33576:ℝ)) ≤ (33606); norm_num
  · show ((33606:ℝ)) ≤ (33636); norm_num
  · show ((33636:ℝ)) ≤ (33667); norm_num
  · show ((33667:ℝ)) ≤ (33697); norm_num
  · show ((33697:ℝ)) ≤ (33727); norm_num
  · show ((33727:ℝ)) ≤ (33758); norm_num
  · show ((33758:ℝ)) ≤ (33788); norm_num
  · show ((33788:ℝ)) ≤ (33818); norm_num
  · show ((33818:ℝ)) ≤ (33848); norm_num
  · show ((33848:ℝ)) ≤ (33879); norm_num
  · show ((33879:ℝ)) ≤ (33909); norm_num
  · show ((33909:ℝ)) ≤ (33939); norm_num
  · show ((33939:ℝ)) ≤ (33970); norm_num
  · show ((33970:ℝ)) ≤ (34000); norm_num
  · show ((34000:ℝ)) ≤ (34000); norm_num
  · exact le_refl _

/-- The lower edges of the 33 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 33000
  | 1 => 33030
  | 2 => 33061
  | 3 => 33091
  | 4 => 132483 / 4
  | 5 => 33152
  | 6 => 33182
  | 7 => 33212
  | 8 => 33242
  | 9 => 33273
  | 10 => 33303
  | 11 => 33333
  | 12 => 33364
  | 13 => 33394
  | 14 => 133695 / 4
  | 15 => 33455
  | 16 => 33485
  | 17 => 33515
  | 18 => 33545
  | 19 => 33576
  | 20 => 33606
  | 21 => 33636
  | 22 => 33667
  | 23 => 33697
  | 24 => 33727
  | 25 => 33758
  | 26 => 135151 / 4
  | 27 => 33818
  | 28 => 33848
  | 29 => 33879
  | 30 => 33909
  | 31 => 135755 / 4
  | 32 => 33970
  | _ => 33970

/-- The upper edges of the 33 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 33030
  | 1 => 33061
  | 2 => 33091
  | 3 => 33121
  | 4 => 33152
  | 5 => 33182
  | 6 => 33212
  | 7 => 33242
  | 8 => 33273
  | 9 => 33303
  | 10 => 33333
  | 11 => 33364
  | 12 => 33394
  | 13 => 33424
  | 14 => 33455
  | 15 => 33485
  | 16 => 33515
  | 17 => 33545
  | 18 => 33576
  | 19 => 33606
  | 20 => 33636
  | 21 => 33667
  | 22 => 33697
  | 23 => 134909 / 4
  | 24 => 33758
  | 25 => 33788
  | 26 => 33818
  | 27 => 33848
  | 28 => 135517 / 4
  | 29 => 33909
  | 30 => 33939
  | 31 => 33970
  | 32 => 34000
  | _ => 34000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 33 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 34000` (`log 34000 ≤ 11`, `2.7^11 ≥ 34000`). -/
theorem haC_34000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 34000 := by
  have hlog : Real.log 34000 ≤ 11 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h11 : Real.exp 11 = (Real.exp 1) ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 11 ≤ (Real.exp 1) ^ 11 := pow_le_pow_left₀ (by norm_num) he1 11
    rw [h11]; nlinarith [hpow]
  have hpos : 0 < Real.log 34000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 34000
      ≤ (1 / 4000000) * 11 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[33000, 34000]` segment's band hypothesis: every band `i < 33` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 33 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 33 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[33000, 34000]` SEGMENT: every zero with `33000 ≤ Im ≤ 34000` is on the line. -/
theorem segment_33000_34000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 34000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (33000:ℝ) ≤ ρ.im → ρ.im ≤ 34000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 33000 34000 bndSeg 33 (by norm_num) bndSeg_mono rfl rfl haC_34000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 34000 via the HEIGHT CHAIN**: `[0,33000]` ∘ `[33000,34000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_34000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 34000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 34000 → ρ.re = 1 / 2 := by
  have hγ33000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 33000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 33000 34000
    (AllZeros_h33000.all_nontrivial_zeros_up_to_height_33000_of_bands
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
      hγ33000)
    (segment_33000_34000 hbands hγ)

end AllZeros_h34000
