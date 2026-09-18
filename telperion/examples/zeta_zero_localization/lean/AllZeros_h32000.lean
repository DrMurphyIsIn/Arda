/-  Height-chain step: all nontrivial zeta zeros up to height 32000 on Re = 1/2 --
    `AllZeros_h31000` + a `[31000, 32000]` SEGMENT certificate (33 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h31000
import RHInBoxT_1d4000000_3999999d4000000_31000_31030
import RHInBoxT_1d4000000_3999999d4000000_31030_31061
import RHInBoxT_1d4000000_3999999d4000000_31061_31091
import RHInBoxT_1d4000000_3999999d4000000_31091_31121
import RHInBoxT_1d4000000_3999999d4000000_31121_31152
import RHInBoxT_1d4000000_3999999d4000000_31152_31182
import RHInBoxT_1d4000000_3999999d4000000_31182_124849d4
import RHInBoxT_1d4000000_3999999d4000000_31212_31242
import RHInBoxT_1d4000000_3999999d4000000_31242_31273
import RHInBoxT_1d4000000_3999999d4000000_31273_31303
import RHInBoxT_1d4000000_3999999d4000000_31303_31333
import RHInBoxT_1d4000000_3999999d4000000_31333_31364
import RHInBoxT_1d4000000_3999999d4000000_31364_31394
import RHInBoxT_1d4000000_3999999d4000000_31394_31424
import RHInBoxT_1d4000000_3999999d4000000_31424_31455
import RHInBoxT_1d4000000_3999999d4000000_31455_31485
import RHInBoxT_1d4000000_3999999d4000000_31485_31515
import RHInBoxT_1d4000000_3999999d4000000_31515_31545
import RHInBoxT_1d4000000_3999999d4000000_31545_31576
import RHInBoxT_1d4000000_3999999d4000000_31576_31606
import RHInBoxT_1d4000000_3999999d4000000_31606_31636
import RHInBoxT_1d4000000_3999999d4000000_31636_31667
import RHInBoxT_1d4000000_3999999d4000000_31667_31697
import RHInBoxT_1d4000000_3999999d4000000_31697_31727
import RHInBoxT_1d4000000_3999999d4000000_31727_31758
import RHInBoxT_1d4000000_3999999d4000000_31758_31788
import RHInBoxT_1d4000000_3999999d4000000_31788_31818
import RHInBoxT_1d4000000_3999999d4000000_31818_31848
import RHInBoxT_1d4000000_3999999d4000000_31848_31879
import RHInBoxT_1d4000000_3999999d4000000_31879_31909
import RHInBoxT_1d4000000_3999999d4000000_31909_31939
import RHInBoxT_1d4000000_3999999d4000000_31939_31970
import RHInBoxT_1d4000000_3999999d4000000_31970_32000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h32000

/-- The 33-band NOMINAL partition of `[31000, 32000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 31000
  | 1 => 31030
  | 2 => 31061
  | 3 => 31091
  | 4 => 31121
  | 5 => 31152
  | 6 => 31182
  | 7 => 31212
  | 8 => 31242
  | 9 => 31273
  | 10 => 31303
  | 11 => 31333
  | 12 => 31364
  | 13 => 31394
  | 14 => 31424
  | 15 => 31455
  | 16 => 31485
  | 17 => 31515
  | 18 => 31545
  | 19 => 31576
  | 20 => 31606
  | 21 => 31636
  | 22 => 31667
  | 23 => 31697
  | 24 => 31727
  | 25 => 31758
  | 26 => 31788
  | 27 => 31818
  | 28 => 31848
  | 29 => 31879
  | 30 => 31909
  | 31 => 31939
  | 32 => 31970
  | 33 => 32000
  | _ => 32000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((31000:ℝ)) ≤ (31030); norm_num
  · show ((31030:ℝ)) ≤ (31061); norm_num
  · show ((31061:ℝ)) ≤ (31091); norm_num
  · show ((31091:ℝ)) ≤ (31121); norm_num
  · show ((31121:ℝ)) ≤ (31152); norm_num
  · show ((31152:ℝ)) ≤ (31182); norm_num
  · show ((31182:ℝ)) ≤ (31212); norm_num
  · show ((31212:ℝ)) ≤ (31242); norm_num
  · show ((31242:ℝ)) ≤ (31273); norm_num
  · show ((31273:ℝ)) ≤ (31303); norm_num
  · show ((31303:ℝ)) ≤ (31333); norm_num
  · show ((31333:ℝ)) ≤ (31364); norm_num
  · show ((31364:ℝ)) ≤ (31394); norm_num
  · show ((31394:ℝ)) ≤ (31424); norm_num
  · show ((31424:ℝ)) ≤ (31455); norm_num
  · show ((31455:ℝ)) ≤ (31485); norm_num
  · show ((31485:ℝ)) ≤ (31515); norm_num
  · show ((31515:ℝ)) ≤ (31545); norm_num
  · show ((31545:ℝ)) ≤ (31576); norm_num
  · show ((31576:ℝ)) ≤ (31606); norm_num
  · show ((31606:ℝ)) ≤ (31636); norm_num
  · show ((31636:ℝ)) ≤ (31667); norm_num
  · show ((31667:ℝ)) ≤ (31697); norm_num
  · show ((31697:ℝ)) ≤ (31727); norm_num
  · show ((31727:ℝ)) ≤ (31758); norm_num
  · show ((31758:ℝ)) ≤ (31788); norm_num
  · show ((31788:ℝ)) ≤ (31818); norm_num
  · show ((31818:ℝ)) ≤ (31848); norm_num
  · show ((31848:ℝ)) ≤ (31879); norm_num
  · show ((31879:ℝ)) ≤ (31909); norm_num
  · show ((31909:ℝ)) ≤ (31939); norm_num
  · show ((31939:ℝ)) ≤ (31970); norm_num
  · show ((31970:ℝ)) ≤ (32000); norm_num
  · show ((32000:ℝ)) ≤ (32000); norm_num
  · exact le_refl _

/-- The lower edges of the 33 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 31000
  | 1 => 31030
  | 2 => 31061
  | 3 => 31091
  | 4 => 31121
  | 5 => 31152
  | 6 => 31182
  | 7 => 31212
  | 8 => 31242
  | 9 => 31273
  | 10 => 31303
  | 11 => 31333
  | 12 => 31364
  | 13 => 31394
  | 14 => 31424
  | 15 => 31455
  | 16 => 31485
  | 17 => 31515
  | 18 => 31545
  | 19 => 31576
  | 20 => 31606
  | 21 => 31636
  | 22 => 31667
  | 23 => 31697
  | 24 => 31727
  | 25 => 31758
  | 26 => 31788
  | 27 => 31818
  | 28 => 31848
  | 29 => 31879
  | 30 => 31909
  | 31 => 31939
  | 32 => 31970
  | _ => 31970

/-- The upper edges of the 33 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 31030
  | 1 => 31061
  | 2 => 31091
  | 3 => 31121
  | 4 => 31152
  | 5 => 31182
  | 6 => 124849 / 4
  | 7 => 31242
  | 8 => 31273
  | 9 => 31303
  | 10 => 31333
  | 11 => 31364
  | 12 => 31394
  | 13 => 31424
  | 14 => 31455
  | 15 => 31485
  | 16 => 31515
  | 17 => 31545
  | 18 => 31576
  | 19 => 31606
  | 20 => 31636
  | 21 => 31667
  | 22 => 31697
  | 23 => 31727
  | 24 => 31758
  | 25 => 31788
  | 26 => 31818
  | 27 => 31848
  | 28 => 31879
  | 29 => 31909
  | 30 => 31939
  | 31 => 31970
  | 32 => 32000
  | _ => 32000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 33 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 32000` (`log 32000 ≤ 11`, `2.7^11 ≥ 32000`). -/
theorem haC_32000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 32000 := by
  have hlog : Real.log 32000 ≤ 11 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h11 : Real.exp 11 = (Real.exp 1) ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 11 ≤ (Real.exp 1) ^ 11 := pow_le_pow_left₀ (by norm_num) he1 11
    rw [h11]; nlinarith [hpow]
  have hpos : 0 < Real.log 32000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 32000
      ≤ (1 / 4000000) * 11 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[31000, 32000]` segment's band hypothesis: every band `i < 33` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 33 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 33 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[31000, 32000]` SEGMENT: every zero with `31000 ≤ Im ≤ 32000` is on the line. -/
theorem segment_31000_32000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 32000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (31000:ℝ) ≤ ρ.im → ρ.im ≤ 32000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 31000 32000 bndSeg 33 (by norm_num) bndSeg_mono rfl rfl haC_32000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 32000 via the HEIGHT CHAIN**: `[0,31000]` ∘ `[31000,32000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_32000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 32000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 32000 → ρ.re = 1 / 2 := by
  have hγ31000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 31000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 31000 32000
    (AllZeros_h31000.all_nontrivial_zeros_up_to_height_31000_of_bands
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
      hγ31000)
    (segment_31000_32000 hbands hγ)

end AllZeros_h32000
