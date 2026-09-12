/-  Height-chain step: all nontrivial zeta zeros up to height 40000 on Re = 1/2 --
    `AllZeros_h39000` + a `[39000, 40000]` SEGMENT certificate (34 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h39000
import RHInBoxT_1d4000000_3999999d4000000_155999d4_39029
import RHInBoxT_1d4000000_3999999d4000000_39029_39059
import RHInBoxT_1d4000000_3999999d4000000_39059_39088
import RHInBoxT_1d4000000_3999999d4000000_39088_39118
import RHInBoxT_1d4000000_3999999d4000000_39118_156589d4
import RHInBoxT_1d4000000_3999999d4000000_39147_39176
import RHInBoxT_1d4000000_3999999d4000000_39176_39206
import RHInBoxT_1d4000000_3999999d4000000_39206_39235
import RHInBoxT_1d4000000_3999999d4000000_39235_157061d4
import RHInBoxT_1d4000000_3999999d4000000_39265_39294
import RHInBoxT_1d4000000_3999999d4000000_39294_157297d4
import RHInBoxT_1d4000000_3999999d4000000_39324_39353
import RHInBoxT_1d4000000_3999999d4000000_157411d4_39382
import RHInBoxT_1d4000000_3999999d4000000_157527d4_39412
import RHInBoxT_1d4000000_3999999d4000000_39412_39441
import RHInBoxT_1d4000000_3999999d4000000_39441_157885d4
import RHInBoxT_1d4000000_3999999d4000000_39471_158001d4
import RHInBoxT_1d4000000_3999999d4000000_39500_39529
import RHInBoxT_1d4000000_3999999d4000000_39529_39559
import RHInBoxT_1d4000000_3999999d4000000_39559_39588
import RHInBoxT_1d4000000_3999999d4000000_158351d4_158473d4
import RHInBoxT_1d4000000_3999999d4000000_39618_39647
import RHInBoxT_1d4000000_3999999d4000000_158587d4_39676
import RHInBoxT_1d4000000_3999999d4000000_39676_39706
import RHInBoxT_1d4000000_3999999d4000000_39706_158941d4
import RHInBoxT_1d4000000_3999999d4000000_39735_39765
import RHInBoxT_1d4000000_3999999d4000000_39765_39794
import RHInBoxT_1d4000000_3999999d4000000_159175d4_39824
import RHInBoxT_1d4000000_3999999d4000000_39824_39853
import RHInBoxT_1d4000000_3999999d4000000_159411d4_159529d4
import RHInBoxT_1d4000000_3999999d4000000_39882_39912
import RHInBoxT_1d4000000_3999999d4000000_39912_159765d4
import RHInBoxT_1d4000000_3999999d4000000_39941_39971
import RHInBoxT_1d4000000_3999999d4000000_39971_40000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h40000

/-- The 34-band NOMINAL partition of `[39000, 40000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 39000
  | 1 => 39029
  | 2 => 39059
  | 3 => 39088
  | 4 => 39118
  | 5 => 39147
  | 6 => 39176
  | 7 => 39206
  | 8 => 39235
  | 9 => 39265
  | 10 => 39294
  | 11 => 39324
  | 12 => 39353
  | 13 => 39382
  | 14 => 39412
  | 15 => 39441
  | 16 => 39471
  | 17 => 39500
  | 18 => 39529
  | 19 => 39559
  | 20 => 39588
  | 21 => 39618
  | 22 => 39647
  | 23 => 39676
  | 24 => 39706
  | 25 => 39735
  | 26 => 39765
  | 27 => 39794
  | 28 => 39824
  | 29 => 39853
  | 30 => 39882
  | 31 => 39912
  | 32 => 39941
  | 33 => 39971
  | 34 => 40000
  | _ => 40000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((39000:ℝ)) ≤ (39029); norm_num
  · show ((39029:ℝ)) ≤ (39059); norm_num
  · show ((39059:ℝ)) ≤ (39088); norm_num
  · show ((39088:ℝ)) ≤ (39118); norm_num
  · show ((39118:ℝ)) ≤ (39147); norm_num
  · show ((39147:ℝ)) ≤ (39176); norm_num
  · show ((39176:ℝ)) ≤ (39206); norm_num
  · show ((39206:ℝ)) ≤ (39235); norm_num
  · show ((39235:ℝ)) ≤ (39265); norm_num
  · show ((39265:ℝ)) ≤ (39294); norm_num
  · show ((39294:ℝ)) ≤ (39324); norm_num
  · show ((39324:ℝ)) ≤ (39353); norm_num
  · show ((39353:ℝ)) ≤ (39382); norm_num
  · show ((39382:ℝ)) ≤ (39412); norm_num
  · show ((39412:ℝ)) ≤ (39441); norm_num
  · show ((39441:ℝ)) ≤ (39471); norm_num
  · show ((39471:ℝ)) ≤ (39500); norm_num
  · show ((39500:ℝ)) ≤ (39529); norm_num
  · show ((39529:ℝ)) ≤ (39559); norm_num
  · show ((39559:ℝ)) ≤ (39588); norm_num
  · show ((39588:ℝ)) ≤ (39618); norm_num
  · show ((39618:ℝ)) ≤ (39647); norm_num
  · show ((39647:ℝ)) ≤ (39676); norm_num
  · show ((39676:ℝ)) ≤ (39706); norm_num
  · show ((39706:ℝ)) ≤ (39735); norm_num
  · show ((39735:ℝ)) ≤ (39765); norm_num
  · show ((39765:ℝ)) ≤ (39794); norm_num
  · show ((39794:ℝ)) ≤ (39824); norm_num
  · show ((39824:ℝ)) ≤ (39853); norm_num
  · show ((39853:ℝ)) ≤ (39882); norm_num
  · show ((39882:ℝ)) ≤ (39912); norm_num
  · show ((39912:ℝ)) ≤ (39941); norm_num
  · show ((39941:ℝ)) ≤ (39971); norm_num
  · show ((39971:ℝ)) ≤ (40000); norm_num
  · show ((40000:ℝ)) ≤ (40000); norm_num
  · exact le_refl _

/-- The lower edges of the 34 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 155999 / 4
  | 1 => 39029
  | 2 => 39059
  | 3 => 39088
  | 4 => 39118
  | 5 => 39147
  | 6 => 39176
  | 7 => 39206
  | 8 => 39235
  | 9 => 39265
  | 10 => 39294
  | 11 => 39324
  | 12 => 157411 / 4
  | 13 => 157527 / 4
  | 14 => 39412
  | 15 => 39441
  | 16 => 39471
  | 17 => 39500
  | 18 => 39529
  | 19 => 39559
  | 20 => 158351 / 4
  | 21 => 39618
  | 22 => 158587 / 4
  | 23 => 39676
  | 24 => 39706
  | 25 => 39735
  | 26 => 39765
  | 27 => 159175 / 4
  | 28 => 39824
  | 29 => 159411 / 4
  | 30 => 39882
  | 31 => 39912
  | 32 => 39941
  | 33 => 39971
  | _ => 39971

/-- The upper edges of the 34 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 39029
  | 1 => 39059
  | 2 => 39088
  | 3 => 39118
  | 4 => 156589 / 4
  | 5 => 39176
  | 6 => 39206
  | 7 => 39235
  | 8 => 157061 / 4
  | 9 => 39294
  | 10 => 157297 / 4
  | 11 => 39353
  | 12 => 39382
  | 13 => 39412
  | 14 => 39441
  | 15 => 157885 / 4
  | 16 => 158001 / 4
  | 17 => 39529
  | 18 => 39559
  | 19 => 39588
  | 20 => 158473 / 4
  | 21 => 39647
  | 22 => 39676
  | 23 => 39706
  | 24 => 158941 / 4
  | 25 => 39765
  | 26 => 39794
  | 27 => 39824
  | 28 => 39853
  | 29 => 159529 / 4
  | 30 => 39912
  | 31 => 159765 / 4
  | 32 => 39971
  | 33 => 40000
  | _ => 40000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 34 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 40000` (`log 40000 ≤ 11`, `2.7^11 ≥ 40000`). -/
theorem haC_40000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 40000 := by
  have hlog : Real.log 40000 ≤ 11 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h11 : Real.exp 11 = (Real.exp 1) ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 11 ≤ (Real.exp 1) ^ 11 := pow_le_pow_left₀ (by norm_num) he1 11
    rw [h11]; nlinarith [hpow]
  have hpos : 0 < Real.log 40000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 40000
      ≤ (1 / 4000000) * 11 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[39000, 40000]` segment's band hypothesis: every band `i < 34` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 34 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 34 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[39000, 40000]` SEGMENT: every zero with `39000 ≤ Im ≤ 40000` is on the line. -/
theorem segment_39000_40000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 40000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (39000:ℝ) ≤ ρ.im → ρ.im ≤ 40000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 39000 40000 bndSeg 34 (by norm_num) bndSeg_mono rfl rfl haC_40000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 40000 via the HEIGHT CHAIN**: `[0,39000]` ∘ `[39000,40000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_40000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 40000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 40000 → ρ.re = 1 / 2 := by
  have hγ39000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 39000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 39000 40000
    (AllZeros_h39000.all_nontrivial_zeros_up_to_height_39000_of_bands
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
      hγ39000)
    (segment_39000_40000 hbands hγ)

end AllZeros_h40000
