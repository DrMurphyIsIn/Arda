/-  Height-chain step: all nontrivial zeta zeros up to height 33000 on Re = 1/2 --
    `AllZeros_h32000` + a `[32000, 33000]` SEGMENT certificate (33 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h32000
import RHInBoxT_1d4000000_3999999d4000000_32000_128121d4
import RHInBoxT_1d4000000_3999999d4000000_32030_128245d4
import RHInBoxT_1d4000000_3999999d4000000_32061_128365d4
import RHInBoxT_1d4000000_3999999d4000000_32091_32121
import RHInBoxT_1d4000000_3999999d4000000_32121_128609d4
import RHInBoxT_1d4000000_3999999d4000000_32152_32182
import RHInBoxT_1d4000000_3999999d4000000_32182_32212
import RHInBoxT_1d4000000_3999999d4000000_32212_32242
import RHInBoxT_1d4000000_3999999d4000000_32242_32273
import RHInBoxT_1d4000000_3999999d4000000_32273_32303
import RHInBoxT_1d4000000_3999999d4000000_32303_32333
import RHInBoxT_1d4000000_3999999d4000000_32333_32364
import RHInBoxT_1d4000000_3999999d4000000_32364_32394
import RHInBoxT_1d4000000_3999999d4000000_32394_32424
import RHInBoxT_1d4000000_3999999d4000000_32424_32455
import RHInBoxT_1d4000000_3999999d4000000_32455_32485
import RHInBoxT_1d4000000_3999999d4000000_32485_32515
import RHInBoxT_1d4000000_3999999d4000000_32515_32545
import RHInBoxT_1d4000000_3999999d4000000_32545_32576
import RHInBoxT_1d4000000_3999999d4000000_32576_32606
import RHInBoxT_1d4000000_3999999d4000000_32606_32636
import RHInBoxT_1d4000000_3999999d4000000_32636_32667
import RHInBoxT_1d4000000_3999999d4000000_32667_32697
import RHInBoxT_1d4000000_3999999d4000000_32697_32727
import RHInBoxT_1d4000000_3999999d4000000_32727_32758
import RHInBoxT_1d4000000_3999999d4000000_32758_32788
import RHInBoxT_1d4000000_3999999d4000000_32788_32818
import RHInBoxT_1d4000000_3999999d4000000_32818_32848
import RHInBoxT_1d4000000_3999999d4000000_32848_32879
import RHInBoxT_1d4000000_3999999d4000000_32879_32909
import RHInBoxT_1d4000000_3999999d4000000_32909_32939
import RHInBoxT_1d4000000_3999999d4000000_65877d2_32970
import RHInBoxT_1d4000000_3999999d4000000_32970_33000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h33000

/-- The 33-band NOMINAL partition of `[32000, 33000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 32000
  | 1 => 32030
  | 2 => 32061
  | 3 => 32091
  | 4 => 32121
  | 5 => 32152
  | 6 => 32182
  | 7 => 32212
  | 8 => 32242
  | 9 => 32273
  | 10 => 32303
  | 11 => 32333
  | 12 => 32364
  | 13 => 32394
  | 14 => 32424
  | 15 => 32455
  | 16 => 32485
  | 17 => 32515
  | 18 => 32545
  | 19 => 32576
  | 20 => 32606
  | 21 => 32636
  | 22 => 32667
  | 23 => 32697
  | 24 => 32727
  | 25 => 32758
  | 26 => 32788
  | 27 => 32818
  | 28 => 32848
  | 29 => 32879
  | 30 => 32909
  | 31 => 32939
  | 32 => 32970
  | 33 => 33000
  | _ => 33000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((32000:ℝ)) ≤ (32030); norm_num
  · show ((32030:ℝ)) ≤ (32061); norm_num
  · show ((32061:ℝ)) ≤ (32091); norm_num
  · show ((32091:ℝ)) ≤ (32121); norm_num
  · show ((32121:ℝ)) ≤ (32152); norm_num
  · show ((32152:ℝ)) ≤ (32182); norm_num
  · show ((32182:ℝ)) ≤ (32212); norm_num
  · show ((32212:ℝ)) ≤ (32242); norm_num
  · show ((32242:ℝ)) ≤ (32273); norm_num
  · show ((32273:ℝ)) ≤ (32303); norm_num
  · show ((32303:ℝ)) ≤ (32333); norm_num
  · show ((32333:ℝ)) ≤ (32364); norm_num
  · show ((32364:ℝ)) ≤ (32394); norm_num
  · show ((32394:ℝ)) ≤ (32424); norm_num
  · show ((32424:ℝ)) ≤ (32455); norm_num
  · show ((32455:ℝ)) ≤ (32485); norm_num
  · show ((32485:ℝ)) ≤ (32515); norm_num
  · show ((32515:ℝ)) ≤ (32545); norm_num
  · show ((32545:ℝ)) ≤ (32576); norm_num
  · show ((32576:ℝ)) ≤ (32606); norm_num
  · show ((32606:ℝ)) ≤ (32636); norm_num
  · show ((32636:ℝ)) ≤ (32667); norm_num
  · show ((32667:ℝ)) ≤ (32697); norm_num
  · show ((32697:ℝ)) ≤ (32727); norm_num
  · show ((32727:ℝ)) ≤ (32758); norm_num
  · show ((32758:ℝ)) ≤ (32788); norm_num
  · show ((32788:ℝ)) ≤ (32818); norm_num
  · show ((32818:ℝ)) ≤ (32848); norm_num
  · show ((32848:ℝ)) ≤ (32879); norm_num
  · show ((32879:ℝ)) ≤ (32909); norm_num
  · show ((32909:ℝ)) ≤ (32939); norm_num
  · show ((32939:ℝ)) ≤ (32970); norm_num
  · show ((32970:ℝ)) ≤ (33000); norm_num
  · show ((33000:ℝ)) ≤ (33000); norm_num
  · exact le_refl _

/-- The lower edges of the 33 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 32000
  | 1 => 32030
  | 2 => 32061
  | 3 => 32091
  | 4 => 32121
  | 5 => 32152
  | 6 => 32182
  | 7 => 32212
  | 8 => 32242
  | 9 => 32273
  | 10 => 32303
  | 11 => 32333
  | 12 => 32364
  | 13 => 32394
  | 14 => 32424
  | 15 => 32455
  | 16 => 32485
  | 17 => 32515
  | 18 => 32545
  | 19 => 32576
  | 20 => 32606
  | 21 => 32636
  | 22 => 32667
  | 23 => 32697
  | 24 => 32727
  | 25 => 32758
  | 26 => 32788
  | 27 => 32818
  | 28 => 32848
  | 29 => 32879
  | 30 => 32909
  | 31 => 65877 / 2
  | 32 => 32970
  | _ => 32970

/-- The upper edges of the 33 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 128121 / 4
  | 1 => 128245 / 4
  | 2 => 128365 / 4
  | 3 => 32121
  | 4 => 128609 / 4
  | 5 => 32182
  | 6 => 32212
  | 7 => 32242
  | 8 => 32273
  | 9 => 32303
  | 10 => 32333
  | 11 => 32364
  | 12 => 32394
  | 13 => 32424
  | 14 => 32455
  | 15 => 32485
  | 16 => 32515
  | 17 => 32545
  | 18 => 32576
  | 19 => 32606
  | 20 => 32636
  | 21 => 32667
  | 22 => 32697
  | 23 => 32727
  | 24 => 32758
  | 25 => 32788
  | 26 => 32818
  | 27 => 32848
  | 28 => 32879
  | 29 => 32909
  | 30 => 32939
  | 31 => 32970
  | 32 => 33000
  | _ => 33000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 33 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 33000` (`log 33000 ≤ 11`, `2.7^11 ≥ 33000`). -/
theorem haC_33000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 33000 := by
  have hlog : Real.log 33000 ≤ 11 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h11 : Real.exp 11 = (Real.exp 1) ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 11 ≤ (Real.exp 1) ^ 11 := pow_le_pow_left₀ (by norm_num) he1 11
    rw [h11]; nlinarith [hpow]
  have hpos : 0 < Real.log 33000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 33000
      ≤ (1 / 4000000) * 11 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[32000, 33000]` segment's band hypothesis: every band `i < 33` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 33 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 33 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[32000, 33000]` SEGMENT: every zero with `32000 ≤ Im ≤ 33000` is on the line. -/
theorem segment_32000_33000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 33000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (32000:ℝ) ≤ ρ.im → ρ.im ≤ 33000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 32000 33000 bndSeg 33 (by norm_num) bndSeg_mono rfl rfl haC_33000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 33000 via the HEIGHT CHAIN**: `[0,32000]` ∘ `[32000,33000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_33000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 33000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 33000 → ρ.re = 1 / 2 := by
  have hγ32000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 32000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 32000 33000
    (AllZeros_h32000.all_nontrivial_zeros_up_to_height_32000_of_bands
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
      hγ32000)
    (segment_32000_33000 hbands hγ)

end AllZeros_h33000
