/-  Height-chain step: all nontrivial zeta zeros up to height 36000 on Re = 1/2 --
    `AllZeros_h35000` + a `[35000, 36000]` SEGMENT certificate (33 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h35000
import RHInBoxT_1d4000000_3999999d4000000_35000_35030
import RHInBoxT_1d4000000_3999999d4000000_35030_35061
import RHInBoxT_1d4000000_3999999d4000000_140243d4_35091
import RHInBoxT_1d4000000_3999999d4000000_35091_35121
import RHInBoxT_1d4000000_3999999d4000000_35121_35152
import RHInBoxT_1d4000000_3999999d4000000_140607d4_35182
import RHInBoxT_1d4000000_3999999d4000000_140727d4_35212
import RHInBoxT_1d4000000_3999999d4000000_35212_35242
import RHInBoxT_1d4000000_3999999d4000000_35242_35273
import RHInBoxT_1d4000000_3999999d4000000_35273_35303
import RHInBoxT_1d4000000_3999999d4000000_35303_35333
import RHInBoxT_1d4000000_3999999d4000000_141331d4_35364
import RHInBoxT_1d4000000_3999999d4000000_35364_35394
import RHInBoxT_1d4000000_3999999d4000000_35394_35424
import RHInBoxT_1d4000000_3999999d4000000_35424_35455
import RHInBoxT_1d4000000_3999999d4000000_141819d4_35485
import RHInBoxT_1d4000000_3999999d4000000_35485_35515
import RHInBoxT_1d4000000_3999999d4000000_35515_35545
import RHInBoxT_1d4000000_3999999d4000000_35545_35576
import RHInBoxT_1d4000000_3999999d4000000_35576_35606
import RHInBoxT_1d4000000_3999999d4000000_35606_35636
import RHInBoxT_1d4000000_3999999d4000000_35636_35667
import RHInBoxT_1d4000000_3999999d4000000_35667_35697
import RHInBoxT_1d4000000_3999999d4000000_142787d4_35727
import RHInBoxT_1d4000000_3999999d4000000_35727_35758
import RHInBoxT_1d4000000_3999999d4000000_35758_143153d4
import RHInBoxT_1d4000000_3999999d4000000_35788_35818
import RHInBoxT_1d4000000_3999999d4000000_35818_35848
import RHInBoxT_1d4000000_3999999d4000000_35848_35879
import RHInBoxT_1d4000000_3999999d4000000_35879_35909
import RHInBoxT_1d4000000_3999999d4000000_35909_35939
import RHInBoxT_1d4000000_3999999d4000000_35939_35970
import RHInBoxT_1d4000000_3999999d4000000_35970_36000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h36000

/-- The 33-band NOMINAL partition of `[35000, 36000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 35000
  | 1 => 35030
  | 2 => 35061
  | 3 => 35091
  | 4 => 35121
  | 5 => 35152
  | 6 => 35182
  | 7 => 35212
  | 8 => 35242
  | 9 => 35273
  | 10 => 35303
  | 11 => 35333
  | 12 => 35364
  | 13 => 35394
  | 14 => 35424
  | 15 => 35455
  | 16 => 35485
  | 17 => 35515
  | 18 => 35545
  | 19 => 35576
  | 20 => 35606
  | 21 => 35636
  | 22 => 35667
  | 23 => 35697
  | 24 => 35727
  | 25 => 35758
  | 26 => 35788
  | 27 => 35818
  | 28 => 35848
  | 29 => 35879
  | 30 => 35909
  | 31 => 35939
  | 32 => 35970
  | 33 => 36000
  | _ => 36000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((35000:ℝ)) ≤ (35030); norm_num
  · show ((35030:ℝ)) ≤ (35061); norm_num
  · show ((35061:ℝ)) ≤ (35091); norm_num
  · show ((35091:ℝ)) ≤ (35121); norm_num
  · show ((35121:ℝ)) ≤ (35152); norm_num
  · show ((35152:ℝ)) ≤ (35182); norm_num
  · show ((35182:ℝ)) ≤ (35212); norm_num
  · show ((35212:ℝ)) ≤ (35242); norm_num
  · show ((35242:ℝ)) ≤ (35273); norm_num
  · show ((35273:ℝ)) ≤ (35303); norm_num
  · show ((35303:ℝ)) ≤ (35333); norm_num
  · show ((35333:ℝ)) ≤ (35364); norm_num
  · show ((35364:ℝ)) ≤ (35394); norm_num
  · show ((35394:ℝ)) ≤ (35424); norm_num
  · show ((35424:ℝ)) ≤ (35455); norm_num
  · show ((35455:ℝ)) ≤ (35485); norm_num
  · show ((35485:ℝ)) ≤ (35515); norm_num
  · show ((35515:ℝ)) ≤ (35545); norm_num
  · show ((35545:ℝ)) ≤ (35576); norm_num
  · show ((35576:ℝ)) ≤ (35606); norm_num
  · show ((35606:ℝ)) ≤ (35636); norm_num
  · show ((35636:ℝ)) ≤ (35667); norm_num
  · show ((35667:ℝ)) ≤ (35697); norm_num
  · show ((35697:ℝ)) ≤ (35727); norm_num
  · show ((35727:ℝ)) ≤ (35758); norm_num
  · show ((35758:ℝ)) ≤ (35788); norm_num
  · show ((35788:ℝ)) ≤ (35818); norm_num
  · show ((35818:ℝ)) ≤ (35848); norm_num
  · show ((35848:ℝ)) ≤ (35879); norm_num
  · show ((35879:ℝ)) ≤ (35909); norm_num
  · show ((35909:ℝ)) ≤ (35939); norm_num
  · show ((35939:ℝ)) ≤ (35970); norm_num
  · show ((35970:ℝ)) ≤ (36000); norm_num
  · show ((36000:ℝ)) ≤ (36000); norm_num
  · exact le_refl _

/-- The lower edges of the 33 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 35000
  | 1 => 35030
  | 2 => 140243 / 4
  | 3 => 35091
  | 4 => 35121
  | 5 => 140607 / 4
  | 6 => 140727 / 4
  | 7 => 35212
  | 8 => 35242
  | 9 => 35273
  | 10 => 35303
  | 11 => 141331 / 4
  | 12 => 35364
  | 13 => 35394
  | 14 => 35424
  | 15 => 141819 / 4
  | 16 => 35485
  | 17 => 35515
  | 18 => 35545
  | 19 => 35576
  | 20 => 35606
  | 21 => 35636
  | 22 => 35667
  | 23 => 142787 / 4
  | 24 => 35727
  | 25 => 35758
  | 26 => 35788
  | 27 => 35818
  | 28 => 35848
  | 29 => 35879
  | 30 => 35909
  | 31 => 35939
  | 32 => 35970
  | _ => 35970

/-- The upper edges of the 33 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 35030
  | 1 => 35061
  | 2 => 35091
  | 3 => 35121
  | 4 => 35152
  | 5 => 35182
  | 6 => 35212
  | 7 => 35242
  | 8 => 35273
  | 9 => 35303
  | 10 => 35333
  | 11 => 35364
  | 12 => 35394
  | 13 => 35424
  | 14 => 35455
  | 15 => 35485
  | 16 => 35515
  | 17 => 35545
  | 18 => 35576
  | 19 => 35606
  | 20 => 35636
  | 21 => 35667
  | 22 => 35697
  | 23 => 35727
  | 24 => 35758
  | 25 => 143153 / 4
  | 26 => 35818
  | 27 => 35848
  | 28 => 35879
  | 29 => 35909
  | 30 => 35939
  | 31 => 35970
  | 32 => 36000
  | _ => 36000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 33 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 36000` (`log 36000 ≤ 11`, `2.7^11 ≥ 36000`). -/
theorem haC_36000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 36000 := by
  have hlog : Real.log 36000 ≤ 11 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h11 : Real.exp 11 = (Real.exp 1) ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 11 ≤ (Real.exp 1) ^ 11 := pow_le_pow_left₀ (by norm_num) he1 11
    rw [h11]; nlinarith [hpow]
  have hpos : 0 < Real.log 36000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 36000
      ≤ (1 / 4000000) * 11 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[35000, 36000]` segment's band hypothesis: every band `i < 33` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 33 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 33 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[35000, 36000]` SEGMENT: every zero with `35000 ≤ Im ≤ 36000` is on the line. -/
theorem segment_35000_36000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 36000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (35000:ℝ) ≤ ρ.im → ρ.im ≤ 36000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 35000 36000 bndSeg 33 (by norm_num) bndSeg_mono rfl rfl haC_36000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 36000 via the HEIGHT CHAIN**: `[0,35000]` ∘ `[35000,36000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_36000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 36000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 36000 → ρ.re = 1 / 2 := by
  have hγ35000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 35000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 35000 36000
    (AllZeros_h35000.all_nontrivial_zeros_up_to_height_35000_of_bands
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
      hγ35000)
    (segment_35000_36000 hbands hγ)

end AllZeros_h36000
