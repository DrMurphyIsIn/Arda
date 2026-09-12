/-  Height-chain step: all nontrivial zeta zeros up to height 38000 on Re = 1/2 --
    `AllZeros_h37000` + a `[37000, 38000]` SEGMENT certificate (33 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h37000
import RHInBoxT_1d4000000_3999999d4000000_37000_37030
import RHInBoxT_1d4000000_3999999d4000000_37030_37061
import RHInBoxT_1d4000000_3999999d4000000_37061_37091
import RHInBoxT_1d4000000_3999999d4000000_37091_37121
import RHInBoxT_1d4000000_3999999d4000000_37121_37152
import RHInBoxT_1d4000000_3999999d4000000_37152_37182
import RHInBoxT_1d4000000_3999999d4000000_37182_37212
import RHInBoxT_1d4000000_3999999d4000000_37212_37242
import RHInBoxT_1d4000000_3999999d4000000_37242_37273
import RHInBoxT_1d4000000_3999999d4000000_149091d4_37303
import RHInBoxT_1d4000000_3999999d4000000_37303_149333d4
import RHInBoxT_1d4000000_3999999d4000000_37333_37364
import RHInBoxT_1d4000000_3999999d4000000_37364_37394
import RHInBoxT_1d4000000_3999999d4000000_37394_37424
import RHInBoxT_1d4000000_3999999d4000000_37424_37455
import RHInBoxT_1d4000000_3999999d4000000_37455_37485
import RHInBoxT_1d4000000_3999999d4000000_37485_37515
import RHInBoxT_1d4000000_3999999d4000000_37515_37545
import RHInBoxT_1d4000000_3999999d4000000_37545_150305d4
import RHInBoxT_1d4000000_3999999d4000000_37576_150425d4
import RHInBoxT_1d4000000_3999999d4000000_37606_37636
import RHInBoxT_1d4000000_3999999d4000000_37636_37667
import RHInBoxT_1d4000000_3999999d4000000_37667_37697
import RHInBoxT_1d4000000_3999999d4000000_37697_37727
import RHInBoxT_1d4000000_3999999d4000000_37727_37758
import RHInBoxT_1d4000000_3999999d4000000_37758_37788
import RHInBoxT_1d4000000_3999999d4000000_151151d4_151273d4
import RHInBoxT_1d4000000_3999999d4000000_37818_37848
import RHInBoxT_1d4000000_3999999d4000000_37848_37879
import RHInBoxT_1d4000000_3999999d4000000_37879_151637d4
import RHInBoxT_1d4000000_3999999d4000000_37909_37939
import RHInBoxT_1d4000000_3999999d4000000_37939_37970
import RHInBoxT_1d4000000_3999999d4000000_37970_38000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h38000

/-- The 33-band NOMINAL partition of `[37000, 38000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 37000
  | 1 => 37030
  | 2 => 37061
  | 3 => 37091
  | 4 => 37121
  | 5 => 37152
  | 6 => 37182
  | 7 => 37212
  | 8 => 37242
  | 9 => 37273
  | 10 => 37303
  | 11 => 37333
  | 12 => 37364
  | 13 => 37394
  | 14 => 37424
  | 15 => 37455
  | 16 => 37485
  | 17 => 37515
  | 18 => 37545
  | 19 => 37576
  | 20 => 37606
  | 21 => 37636
  | 22 => 37667
  | 23 => 37697
  | 24 => 37727
  | 25 => 37758
  | 26 => 37788
  | 27 => 37818
  | 28 => 37848
  | 29 => 37879
  | 30 => 37909
  | 31 => 37939
  | 32 => 37970
  | 33 => 38000
  | _ => 38000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((37000:ℝ)) ≤ (37030); norm_num
  · show ((37030:ℝ)) ≤ (37061); norm_num
  · show ((37061:ℝ)) ≤ (37091); norm_num
  · show ((37091:ℝ)) ≤ (37121); norm_num
  · show ((37121:ℝ)) ≤ (37152); norm_num
  · show ((37152:ℝ)) ≤ (37182); norm_num
  · show ((37182:ℝ)) ≤ (37212); norm_num
  · show ((37212:ℝ)) ≤ (37242); norm_num
  · show ((37242:ℝ)) ≤ (37273); norm_num
  · show ((37273:ℝ)) ≤ (37303); norm_num
  · show ((37303:ℝ)) ≤ (37333); norm_num
  · show ((37333:ℝ)) ≤ (37364); norm_num
  · show ((37364:ℝ)) ≤ (37394); norm_num
  · show ((37394:ℝ)) ≤ (37424); norm_num
  · show ((37424:ℝ)) ≤ (37455); norm_num
  · show ((37455:ℝ)) ≤ (37485); norm_num
  · show ((37485:ℝ)) ≤ (37515); norm_num
  · show ((37515:ℝ)) ≤ (37545); norm_num
  · show ((37545:ℝ)) ≤ (37576); norm_num
  · show ((37576:ℝ)) ≤ (37606); norm_num
  · show ((37606:ℝ)) ≤ (37636); norm_num
  · show ((37636:ℝ)) ≤ (37667); norm_num
  · show ((37667:ℝ)) ≤ (37697); norm_num
  · show ((37697:ℝ)) ≤ (37727); norm_num
  · show ((37727:ℝ)) ≤ (37758); norm_num
  · show ((37758:ℝ)) ≤ (37788); norm_num
  · show ((37788:ℝ)) ≤ (37818); norm_num
  · show ((37818:ℝ)) ≤ (37848); norm_num
  · show ((37848:ℝ)) ≤ (37879); norm_num
  · show ((37879:ℝ)) ≤ (37909); norm_num
  · show ((37909:ℝ)) ≤ (37939); norm_num
  · show ((37939:ℝ)) ≤ (37970); norm_num
  · show ((37970:ℝ)) ≤ (38000); norm_num
  · show ((38000:ℝ)) ≤ (38000); norm_num
  · exact le_refl _

/-- The lower edges of the 33 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 37000
  | 1 => 37030
  | 2 => 37061
  | 3 => 37091
  | 4 => 37121
  | 5 => 37152
  | 6 => 37182
  | 7 => 37212
  | 8 => 37242
  | 9 => 149091 / 4
  | 10 => 37303
  | 11 => 37333
  | 12 => 37364
  | 13 => 37394
  | 14 => 37424
  | 15 => 37455
  | 16 => 37485
  | 17 => 37515
  | 18 => 37545
  | 19 => 37576
  | 20 => 37606
  | 21 => 37636
  | 22 => 37667
  | 23 => 37697
  | 24 => 37727
  | 25 => 37758
  | 26 => 151151 / 4
  | 27 => 37818
  | 28 => 37848
  | 29 => 37879
  | 30 => 37909
  | 31 => 37939
  | 32 => 37970
  | _ => 37970

/-- The upper edges of the 33 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 37030
  | 1 => 37061
  | 2 => 37091
  | 3 => 37121
  | 4 => 37152
  | 5 => 37182
  | 6 => 37212
  | 7 => 37242
  | 8 => 37273
  | 9 => 37303
  | 10 => 149333 / 4
  | 11 => 37364
  | 12 => 37394
  | 13 => 37424
  | 14 => 37455
  | 15 => 37485
  | 16 => 37515
  | 17 => 37545
  | 18 => 150305 / 4
  | 19 => 150425 / 4
  | 20 => 37636
  | 21 => 37667
  | 22 => 37697
  | 23 => 37727
  | 24 => 37758
  | 25 => 37788
  | 26 => 151273 / 4
  | 27 => 37848
  | 28 => 37879
  | 29 => 151637 / 4
  | 30 => 37939
  | 31 => 37970
  | 32 => 38000
  | _ => 38000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 33 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 38000` (`log 38000 ≤ 11`, `2.7^11 ≥ 38000`). -/
theorem haC_38000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 38000 := by
  have hlog : Real.log 38000 ≤ 11 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h11 : Real.exp 11 = (Real.exp 1) ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 11 ≤ (Real.exp 1) ^ 11 := pow_le_pow_left₀ (by norm_num) he1 11
    rw [h11]; nlinarith [hpow]
  have hpos : 0 < Real.log 38000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 38000
      ≤ (1 / 4000000) * 11 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[37000, 38000]` segment's band hypothesis: every band `i < 33` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 33 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 33 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[37000, 38000]` SEGMENT: every zero with `37000 ≤ Im ≤ 38000` is on the line. -/
theorem segment_37000_38000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 38000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (37000:ℝ) ≤ ρ.im → ρ.im ≤ 38000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 37000 38000 bndSeg 33 (by norm_num) bndSeg_mono rfl rfl haC_38000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 38000 via the HEIGHT CHAIN**: `[0,37000]` ∘ `[37000,38000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_38000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 38000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 38000 → ρ.re = 1 / 2 := by
  have hγ37000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 37000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 37000 38000
    (AllZeros_h37000.all_nontrivial_zeros_up_to_height_37000_of_bands
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
      hγ37000)
    (segment_37000_38000 hbands hγ)

end AllZeros_h38000
