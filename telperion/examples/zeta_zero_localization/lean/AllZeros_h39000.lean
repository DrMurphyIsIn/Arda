/-  Height-chain step: all nontrivial zeta zeros up to height 39000 on Re = 1/2 --
    `AllZeros_h38000` + a `[38000, 39000]` SEGMENT certificate (33 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h38000
import RHInBoxT_1d4000000_3999999d4000000_38000_38030
import RHInBoxT_1d4000000_3999999d4000000_152119d4_38061
import RHInBoxT_1d4000000_3999999d4000000_152243d4_38091
import RHInBoxT_1d4000000_3999999d4000000_38091_152485d4
import RHInBoxT_1d4000000_3999999d4000000_38121_38152
import RHInBoxT_1d4000000_3999999d4000000_38152_38182
import RHInBoxT_1d4000000_3999999d4000000_38182_38212
import RHInBoxT_1d4000000_3999999d4000000_38212_38242
import RHInBoxT_1d4000000_3999999d4000000_152967d4_38273
import RHInBoxT_1d4000000_3999999d4000000_38273_38303
import RHInBoxT_1d4000000_3999999d4000000_153211d4_38333
import RHInBoxT_1d4000000_3999999d4000000_153331d4_38364
import RHInBoxT_1d4000000_3999999d4000000_38364_38394
import RHInBoxT_1d4000000_3999999d4000000_38394_38424
import RHInBoxT_1d4000000_3999999d4000000_38424_38455
import RHInBoxT_1d4000000_3999999d4000000_38455_38485
import RHInBoxT_1d4000000_3999999d4000000_38485_38515
import RHInBoxT_1d4000000_3999999d4000000_38515_38545
import RHInBoxT_1d4000000_3999999d4000000_38545_38576
import RHInBoxT_1d4000000_3999999d4000000_38576_38606
import RHInBoxT_1d4000000_3999999d4000000_154423d4_38636
import RHInBoxT_1d4000000_3999999d4000000_38636_38667
import RHInBoxT_1d4000000_3999999d4000000_154667d4_38697
import RHInBoxT_1d4000000_3999999d4000000_38697_38727
import RHInBoxT_1d4000000_3999999d4000000_154907d4_38758
import RHInBoxT_1d4000000_3999999d4000000_38758_38788
import RHInBoxT_1d4000000_3999999d4000000_38788_38818
import RHInBoxT_1d4000000_3999999d4000000_38818_38848
import RHInBoxT_1d4000000_3999999d4000000_38848_38879
import RHInBoxT_1d4000000_3999999d4000000_38879_38909
import RHInBoxT_1d4000000_3999999d4000000_38909_38939
import RHInBoxT_1d4000000_3999999d4000000_38939_38970
import RHInBoxT_1d4000000_3999999d4000000_38970_39000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h39000

/-- The 33-band NOMINAL partition of `[38000, 39000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 38000
  | 1 => 38030
  | 2 => 38061
  | 3 => 38091
  | 4 => 38121
  | 5 => 38152
  | 6 => 38182
  | 7 => 38212
  | 8 => 38242
  | 9 => 38273
  | 10 => 38303
  | 11 => 38333
  | 12 => 38364
  | 13 => 38394
  | 14 => 38424
  | 15 => 38455
  | 16 => 38485
  | 17 => 38515
  | 18 => 38545
  | 19 => 38576
  | 20 => 38606
  | 21 => 38636
  | 22 => 38667
  | 23 => 38697
  | 24 => 38727
  | 25 => 38758
  | 26 => 38788
  | 27 => 38818
  | 28 => 38848
  | 29 => 38879
  | 30 => 38909
  | 31 => 38939
  | 32 => 38970
  | 33 => 39000
  | _ => 39000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((38000:ℝ)) ≤ (38030); norm_num
  · show ((38030:ℝ)) ≤ (38061); norm_num
  · show ((38061:ℝ)) ≤ (38091); norm_num
  · show ((38091:ℝ)) ≤ (38121); norm_num
  · show ((38121:ℝ)) ≤ (38152); norm_num
  · show ((38152:ℝ)) ≤ (38182); norm_num
  · show ((38182:ℝ)) ≤ (38212); norm_num
  · show ((38212:ℝ)) ≤ (38242); norm_num
  · show ((38242:ℝ)) ≤ (38273); norm_num
  · show ((38273:ℝ)) ≤ (38303); norm_num
  · show ((38303:ℝ)) ≤ (38333); norm_num
  · show ((38333:ℝ)) ≤ (38364); norm_num
  · show ((38364:ℝ)) ≤ (38394); norm_num
  · show ((38394:ℝ)) ≤ (38424); norm_num
  · show ((38424:ℝ)) ≤ (38455); norm_num
  · show ((38455:ℝ)) ≤ (38485); norm_num
  · show ((38485:ℝ)) ≤ (38515); norm_num
  · show ((38515:ℝ)) ≤ (38545); norm_num
  · show ((38545:ℝ)) ≤ (38576); norm_num
  · show ((38576:ℝ)) ≤ (38606); norm_num
  · show ((38606:ℝ)) ≤ (38636); norm_num
  · show ((38636:ℝ)) ≤ (38667); norm_num
  · show ((38667:ℝ)) ≤ (38697); norm_num
  · show ((38697:ℝ)) ≤ (38727); norm_num
  · show ((38727:ℝ)) ≤ (38758); norm_num
  · show ((38758:ℝ)) ≤ (38788); norm_num
  · show ((38788:ℝ)) ≤ (38818); norm_num
  · show ((38818:ℝ)) ≤ (38848); norm_num
  · show ((38848:ℝ)) ≤ (38879); norm_num
  · show ((38879:ℝ)) ≤ (38909); norm_num
  · show ((38909:ℝ)) ≤ (38939); norm_num
  · show ((38939:ℝ)) ≤ (38970); norm_num
  · show ((38970:ℝ)) ≤ (39000); norm_num
  · show ((39000:ℝ)) ≤ (39000); norm_num
  · exact le_refl _

/-- The lower edges of the 33 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 38000
  | 1 => 152119 / 4
  | 2 => 152243 / 4
  | 3 => 38091
  | 4 => 38121
  | 5 => 38152
  | 6 => 38182
  | 7 => 38212
  | 8 => 152967 / 4
  | 9 => 38273
  | 10 => 153211 / 4
  | 11 => 153331 / 4
  | 12 => 38364
  | 13 => 38394
  | 14 => 38424
  | 15 => 38455
  | 16 => 38485
  | 17 => 38515
  | 18 => 38545
  | 19 => 38576
  | 20 => 154423 / 4
  | 21 => 38636
  | 22 => 154667 / 4
  | 23 => 38697
  | 24 => 154907 / 4
  | 25 => 38758
  | 26 => 38788
  | 27 => 38818
  | 28 => 38848
  | 29 => 38879
  | 30 => 38909
  | 31 => 38939
  | 32 => 38970
  | _ => 38970

/-- The upper edges of the 33 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 38030
  | 1 => 38061
  | 2 => 38091
  | 3 => 152485 / 4
  | 4 => 38152
  | 5 => 38182
  | 6 => 38212
  | 7 => 38242
  | 8 => 38273
  | 9 => 38303
  | 10 => 38333
  | 11 => 38364
  | 12 => 38394
  | 13 => 38424
  | 14 => 38455
  | 15 => 38485
  | 16 => 38515
  | 17 => 38545
  | 18 => 38576
  | 19 => 38606
  | 20 => 38636
  | 21 => 38667
  | 22 => 38697
  | 23 => 38727
  | 24 => 38758
  | 25 => 38788
  | 26 => 38818
  | 27 => 38848
  | 28 => 38879
  | 29 => 38909
  | 30 => 38939
  | 31 => 38970
  | 32 => 39000
  | _ => 39000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 33 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 39000` (`log 39000 ≤ 11`, `2.7^11 ≥ 39000`). -/
theorem haC_39000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 39000 := by
  have hlog : Real.log 39000 ≤ 11 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h11 : Real.exp 11 = (Real.exp 1) ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 11 ≤ (Real.exp 1) ^ 11 := pow_le_pow_left₀ (by norm_num) he1 11
    rw [h11]; nlinarith [hpow]
  have hpos : 0 < Real.log 39000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 39000
      ≤ (1 / 4000000) * 11 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[38000, 39000]` segment's band hypothesis: every band `i < 33` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 33 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 33 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[38000, 39000]` SEGMENT: every zero with `38000 ≤ Im ≤ 39000` is on the line. -/
theorem segment_38000_39000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 39000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (38000:ℝ) ≤ ρ.im → ρ.im ≤ 39000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 38000 39000 bndSeg 33 (by norm_num) bndSeg_mono rfl rfl haC_39000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 39000 via the HEIGHT CHAIN**: `[0,38000]` ∘ `[38000,39000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_39000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 39000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 39000 → ρ.re = 1 / 2 := by
  have hγ38000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 38000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 38000 39000
    (AllZeros_h38000.all_nontrivial_zeros_up_to_height_38000_of_bands
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
      hγ38000)
    (segment_38000_39000 hbands hγ)

end AllZeros_h39000
