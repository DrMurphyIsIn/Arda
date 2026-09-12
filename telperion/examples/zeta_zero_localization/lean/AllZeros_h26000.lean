/-  Height-chain step: all nontrivial zeta zeros up to height 26000 on Re = 1/2 --
    `AllZeros_h25000` + a `[25000, 26000]` SEGMENT certificate (32 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h25000
import RHInBoxT_1d4000000_3999999d4000000_25000_25031
import RHInBoxT_1d4000000_3999999d4000000_25031_25062
import RHInBoxT_1d4000000_3999999d4000000_25062_100377d4
import RHInBoxT_1d4000000_3999999d4000000_25094_25125
import RHInBoxT_1d4000000_3999999d4000000_25125_25156
import RHInBoxT_1d4000000_3999999d4000000_25156_25188
import RHInBoxT_1d4000000_3999999d4000000_25188_25219
import RHInBoxT_1d4000000_3999999d4000000_25219_25250
import RHInBoxT_1d4000000_3999999d4000000_25250_25281
import RHInBoxT_1d4000000_3999999d4000000_25281_25312
import RHInBoxT_1d4000000_3999999d4000000_25312_25344
import RHInBoxT_1d4000000_3999999d4000000_25344_25375
import RHInBoxT_1d4000000_3999999d4000000_25375_25406
import RHInBoxT_1d4000000_3999999d4000000_25406_25438
import RHInBoxT_1d4000000_3999999d4000000_25438_25469
import RHInBoxT_1d4000000_3999999d4000000_25469_25500
import RHInBoxT_1d4000000_3999999d4000000_25500_25531
import RHInBoxT_1d4000000_3999999d4000000_102123d4_25562
import RHInBoxT_1d4000000_3999999d4000000_102247d4_25594
import RHInBoxT_1d4000000_3999999d4000000_25594_25625
import RHInBoxT_1d4000000_3999999d4000000_25625_25656
import RHInBoxT_1d4000000_3999999d4000000_25656_25688
import RHInBoxT_1d4000000_3999999d4000000_25688_25719
import RHInBoxT_1d4000000_3999999d4000000_25719_25750
import RHInBoxT_1d4000000_3999999d4000000_25750_25781
import RHInBoxT_1d4000000_3999999d4000000_25781_25812
import RHInBoxT_1d4000000_3999999d4000000_25812_25844
import RHInBoxT_1d4000000_3999999d4000000_25844_25875
import RHInBoxT_1d4000000_3999999d4000000_25875_25906
import RHInBoxT_1d4000000_3999999d4000000_25906_25938
import RHInBoxT_1d4000000_3999999d4000000_25938_25969
import RHInBoxT_1d4000000_3999999d4000000_25969_26000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h26000

/-- The 32-band NOMINAL partition of `[25000, 26000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 25000
  | 1 => 25031
  | 2 => 25062
  | 3 => 25094
  | 4 => 25125
  | 5 => 25156
  | 6 => 25188
  | 7 => 25219
  | 8 => 25250
  | 9 => 25281
  | 10 => 25312
  | 11 => 25344
  | 12 => 25375
  | 13 => 25406
  | 14 => 25438
  | 15 => 25469
  | 16 => 25500
  | 17 => 25531
  | 18 => 25562
  | 19 => 25594
  | 20 => 25625
  | 21 => 25656
  | 22 => 25688
  | 23 => 25719
  | 24 => 25750
  | 25 => 25781
  | 26 => 25812
  | 27 => 25844
  | 28 => 25875
  | 29 => 25906
  | 30 => 25938
  | 31 => 25969
  | 32 => 26000
  | _ => 26000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((25000:ℝ)) ≤ (25031); norm_num
  · show ((25031:ℝ)) ≤ (25062); norm_num
  · show ((25062:ℝ)) ≤ (25094); norm_num
  · show ((25094:ℝ)) ≤ (25125); norm_num
  · show ((25125:ℝ)) ≤ (25156); norm_num
  · show ((25156:ℝ)) ≤ (25188); norm_num
  · show ((25188:ℝ)) ≤ (25219); norm_num
  · show ((25219:ℝ)) ≤ (25250); norm_num
  · show ((25250:ℝ)) ≤ (25281); norm_num
  · show ((25281:ℝ)) ≤ (25312); norm_num
  · show ((25312:ℝ)) ≤ (25344); norm_num
  · show ((25344:ℝ)) ≤ (25375); norm_num
  · show ((25375:ℝ)) ≤ (25406); norm_num
  · show ((25406:ℝ)) ≤ (25438); norm_num
  · show ((25438:ℝ)) ≤ (25469); norm_num
  · show ((25469:ℝ)) ≤ (25500); norm_num
  · show ((25500:ℝ)) ≤ (25531); norm_num
  · show ((25531:ℝ)) ≤ (25562); norm_num
  · show ((25562:ℝ)) ≤ (25594); norm_num
  · show ((25594:ℝ)) ≤ (25625); norm_num
  · show ((25625:ℝ)) ≤ (25656); norm_num
  · show ((25656:ℝ)) ≤ (25688); norm_num
  · show ((25688:ℝ)) ≤ (25719); norm_num
  · show ((25719:ℝ)) ≤ (25750); norm_num
  · show ((25750:ℝ)) ≤ (25781); norm_num
  · show ((25781:ℝ)) ≤ (25812); norm_num
  · show ((25812:ℝ)) ≤ (25844); norm_num
  · show ((25844:ℝ)) ≤ (25875); norm_num
  · show ((25875:ℝ)) ≤ (25906); norm_num
  · show ((25906:ℝ)) ≤ (25938); norm_num
  · show ((25938:ℝ)) ≤ (25969); norm_num
  · show ((25969:ℝ)) ≤ (26000); norm_num
  · show ((26000:ℝ)) ≤ (26000); norm_num
  · exact le_refl _

/-- The lower edges of the 32 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 25000
  | 1 => 25031
  | 2 => 25062
  | 3 => 25094
  | 4 => 25125
  | 5 => 25156
  | 6 => 25188
  | 7 => 25219
  | 8 => 25250
  | 9 => 25281
  | 10 => 25312
  | 11 => 25344
  | 12 => 25375
  | 13 => 25406
  | 14 => 25438
  | 15 => 25469
  | 16 => 25500
  | 17 => 102123 / 4
  | 18 => 102247 / 4
  | 19 => 25594
  | 20 => 25625
  | 21 => 25656
  | 22 => 25688
  | 23 => 25719
  | 24 => 25750
  | 25 => 25781
  | 26 => 25812
  | 27 => 25844
  | 28 => 25875
  | 29 => 25906
  | 30 => 25938
  | 31 => 25969
  | _ => 25969

/-- The upper edges of the 32 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 25031
  | 1 => 25062
  | 2 => 100377 / 4
  | 3 => 25125
  | 4 => 25156
  | 5 => 25188
  | 6 => 25219
  | 7 => 25250
  | 8 => 25281
  | 9 => 25312
  | 10 => 25344
  | 11 => 25375
  | 12 => 25406
  | 13 => 25438
  | 14 => 25469
  | 15 => 25500
  | 16 => 25531
  | 17 => 25562
  | 18 => 25594
  | 19 => 25625
  | 20 => 25656
  | 21 => 25688
  | 22 => 25719
  | 23 => 25750
  | 24 => 25781
  | 25 => 25812
  | 26 => 25844
  | 27 => 25875
  | 28 => 25906
  | 29 => 25938
  | 30 => 25969
  | 31 => 26000
  | _ => 26000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 32 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 26000` (`log 26000 ≤ 11`, `2.7^11 ≥ 26000`). -/
theorem haC_26000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 26000 := by
  have hlog : Real.log 26000 ≤ 11 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h11 : Real.exp 11 = (Real.exp 1) ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 11 ≤ (Real.exp 1) ^ 11 := pow_le_pow_left₀ (by norm_num) he1 11
    rw [h11]; nlinarith [hpow]
  have hpos : 0 < Real.log 26000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 26000
      ≤ (1 / 4000000) * 11 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[25000, 26000]` segment's band hypothesis: every band `i < 32` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 32 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 32 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[25000, 26000]` SEGMENT: every zero with `25000 ≤ Im ≤ 26000` is on the line. -/
theorem segment_25000_26000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 26000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (25000:ℝ) ≤ ρ.im → ρ.im ≤ 26000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 25000 26000 bndSeg 32 (by norm_num) bndSeg_mono rfl rfl haC_26000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 26000 via the HEIGHT CHAIN**: `[0,25000]` ∘ `[25000,26000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_26000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 26000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 26000 → ρ.re = 1 / 2 := by
  have hγ25000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 25000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 25000 26000
    (AllZeros_h25000.all_nontrivial_zeros_up_to_height_25000_of_bands
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
      hγ25000)
    (segment_25000_26000 hbands hγ)

end AllZeros_h26000
