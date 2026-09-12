/-  Height-chain step: all nontrivial zeta zeros up to height 27000 on Re = 1/2 --
    `AllZeros_h26000` + a `[26000, 27000]` SEGMENT certificate (32 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h26000
import RHInBoxT_1d4000000_3999999d4000000_26000_26031
import RHInBoxT_1d4000000_3999999d4000000_26031_26062
import RHInBoxT_1d4000000_3999999d4000000_26062_26094
import RHInBoxT_1d4000000_3999999d4000000_26094_26125
import RHInBoxT_1d4000000_3999999d4000000_26125_26156
import RHInBoxT_1d4000000_3999999d4000000_26156_26188
import RHInBoxT_1d4000000_3999999d4000000_104751d4_26219
import RHInBoxT_1d4000000_3999999d4000000_26219_105001d4
import RHInBoxT_1d4000000_3999999d4000000_26250_26281
import RHInBoxT_1d4000000_3999999d4000000_26281_26312
import RHInBoxT_1d4000000_3999999d4000000_105247d4_26344
import RHInBoxT_1d4000000_3999999d4000000_26344_26375
import RHInBoxT_1d4000000_3999999d4000000_26375_26406
import RHInBoxT_1d4000000_3999999d4000000_26406_105753d4
import RHInBoxT_1d4000000_3999999d4000000_26438_26469
import RHInBoxT_1d4000000_3999999d4000000_26469_26500
import RHInBoxT_1d4000000_3999999d4000000_26500_26531
import RHInBoxT_1d4000000_3999999d4000000_26531_26562
import RHInBoxT_1d4000000_3999999d4000000_106247d4_26594
import RHInBoxT_1d4000000_3999999d4000000_26594_26625
import RHInBoxT_1d4000000_3999999d4000000_26625_26656
import RHInBoxT_1d4000000_3999999d4000000_26656_26688
import RHInBoxT_1d4000000_3999999d4000000_26688_26719
import RHInBoxT_1d4000000_3999999d4000000_26719_26750
import RHInBoxT_1d4000000_3999999d4000000_26750_107125d4
import RHInBoxT_1d4000000_3999999d4000000_26781_26812
import RHInBoxT_1d4000000_3999999d4000000_26812_26844
import RHInBoxT_1d4000000_3999999d4000000_26844_26875
import RHInBoxT_1d4000000_3999999d4000000_26875_26906
import RHInBoxT_1d4000000_3999999d4000000_26906_107753d4
import RHInBoxT_1d4000000_3999999d4000000_26938_26969
import RHInBoxT_1d4000000_3999999d4000000_26969_27000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h27000

/-- The 32-band NOMINAL partition of `[26000, 27000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 26000
  | 1 => 26031
  | 2 => 26062
  | 3 => 26094
  | 4 => 26125
  | 5 => 26156
  | 6 => 26188
  | 7 => 26219
  | 8 => 26250
  | 9 => 26281
  | 10 => 26312
  | 11 => 26344
  | 12 => 26375
  | 13 => 26406
  | 14 => 26438
  | 15 => 26469
  | 16 => 26500
  | 17 => 26531
  | 18 => 26562
  | 19 => 26594
  | 20 => 26625
  | 21 => 26656
  | 22 => 26688
  | 23 => 26719
  | 24 => 26750
  | 25 => 26781
  | 26 => 26812
  | 27 => 26844
  | 28 => 26875
  | 29 => 26906
  | 30 => 26938
  | 31 => 26969
  | 32 => 27000
  | _ => 27000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((26000:ℝ)) ≤ (26031); norm_num
  · show ((26031:ℝ)) ≤ (26062); norm_num
  · show ((26062:ℝ)) ≤ (26094); norm_num
  · show ((26094:ℝ)) ≤ (26125); norm_num
  · show ((26125:ℝ)) ≤ (26156); norm_num
  · show ((26156:ℝ)) ≤ (26188); norm_num
  · show ((26188:ℝ)) ≤ (26219); norm_num
  · show ((26219:ℝ)) ≤ (26250); norm_num
  · show ((26250:ℝ)) ≤ (26281); norm_num
  · show ((26281:ℝ)) ≤ (26312); norm_num
  · show ((26312:ℝ)) ≤ (26344); norm_num
  · show ((26344:ℝ)) ≤ (26375); norm_num
  · show ((26375:ℝ)) ≤ (26406); norm_num
  · show ((26406:ℝ)) ≤ (26438); norm_num
  · show ((26438:ℝ)) ≤ (26469); norm_num
  · show ((26469:ℝ)) ≤ (26500); norm_num
  · show ((26500:ℝ)) ≤ (26531); norm_num
  · show ((26531:ℝ)) ≤ (26562); norm_num
  · show ((26562:ℝ)) ≤ (26594); norm_num
  · show ((26594:ℝ)) ≤ (26625); norm_num
  · show ((26625:ℝ)) ≤ (26656); norm_num
  · show ((26656:ℝ)) ≤ (26688); norm_num
  · show ((26688:ℝ)) ≤ (26719); norm_num
  · show ((26719:ℝ)) ≤ (26750); norm_num
  · show ((26750:ℝ)) ≤ (26781); norm_num
  · show ((26781:ℝ)) ≤ (26812); norm_num
  · show ((26812:ℝ)) ≤ (26844); norm_num
  · show ((26844:ℝ)) ≤ (26875); norm_num
  · show ((26875:ℝ)) ≤ (26906); norm_num
  · show ((26906:ℝ)) ≤ (26938); norm_num
  · show ((26938:ℝ)) ≤ (26969); norm_num
  · show ((26969:ℝ)) ≤ (27000); norm_num
  · show ((27000:ℝ)) ≤ (27000); norm_num
  · exact le_refl _

/-- The lower edges of the 32 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 26000
  | 1 => 26031
  | 2 => 26062
  | 3 => 26094
  | 4 => 26125
  | 5 => 26156
  | 6 => 104751 / 4
  | 7 => 26219
  | 8 => 26250
  | 9 => 26281
  | 10 => 105247 / 4
  | 11 => 26344
  | 12 => 26375
  | 13 => 26406
  | 14 => 26438
  | 15 => 26469
  | 16 => 26500
  | 17 => 26531
  | 18 => 106247 / 4
  | 19 => 26594
  | 20 => 26625
  | 21 => 26656
  | 22 => 26688
  | 23 => 26719
  | 24 => 26750
  | 25 => 26781
  | 26 => 26812
  | 27 => 26844
  | 28 => 26875
  | 29 => 26906
  | 30 => 26938
  | 31 => 26969
  | _ => 26969

/-- The upper edges of the 32 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 26031
  | 1 => 26062
  | 2 => 26094
  | 3 => 26125
  | 4 => 26156
  | 5 => 26188
  | 6 => 26219
  | 7 => 105001 / 4
  | 8 => 26281
  | 9 => 26312
  | 10 => 26344
  | 11 => 26375
  | 12 => 26406
  | 13 => 105753 / 4
  | 14 => 26469
  | 15 => 26500
  | 16 => 26531
  | 17 => 26562
  | 18 => 26594
  | 19 => 26625
  | 20 => 26656
  | 21 => 26688
  | 22 => 26719
  | 23 => 26750
  | 24 => 107125 / 4
  | 25 => 26812
  | 26 => 26844
  | 27 => 26875
  | 28 => 26906
  | 29 => 107753 / 4
  | 30 => 26969
  | 31 => 27000
  | _ => 27000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 32 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 27000` (`log 27000 ≤ 11`, `2.7^11 ≥ 27000`). -/
theorem haC_27000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 27000 := by
  have hlog : Real.log 27000 ≤ 11 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h11 : Real.exp 11 = (Real.exp 1) ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 11 ≤ (Real.exp 1) ^ 11 := pow_le_pow_left₀ (by norm_num) he1 11
    rw [h11]; nlinarith [hpow]
  have hpos : 0 < Real.log 27000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 27000
      ≤ (1 / 4000000) * 11 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[26000, 27000]` segment's band hypothesis: every band `i < 32` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 32 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 32 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[26000, 27000]` SEGMENT: every zero with `26000 ≤ Im ≤ 27000` is on the line. -/
theorem segment_26000_27000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 27000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (26000:ℝ) ≤ ρ.im → ρ.im ≤ 27000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 26000 27000 bndSeg 32 (by norm_num) bndSeg_mono rfl rfl haC_27000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 27000 via the HEIGHT CHAIN**: `[0,26000]` ∘ `[26000,27000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_27000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 27000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 27000 → ρ.re = 1 / 2 := by
  have hγ26000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 26000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 26000 27000
    (AllZeros_h26000.all_nontrivial_zeros_up_to_height_26000_of_bands
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
      hγ26000)
    (segment_26000_27000 hbands hγ)

end AllZeros_h27000
