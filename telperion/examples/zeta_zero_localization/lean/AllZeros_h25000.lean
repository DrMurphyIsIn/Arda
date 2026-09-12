/-  Height-chain step: all nontrivial zeta zeros up to height 25000 on Re = 1/2 --
    `AllZeros_h24000` + a `[24000, 25000]` SEGMENT certificate (32 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h24000
import RHInBoxT_1d4000000_3999999d4000000_24000_24031
import RHInBoxT_1d4000000_3999999d4000000_96123d4_24062
import RHInBoxT_1d4000000_3999999d4000000_24062_24094
import RHInBoxT_1d4000000_3999999d4000000_24094_24125
import RHInBoxT_1d4000000_3999999d4000000_24125_24156
import RHInBoxT_1d4000000_3999999d4000000_24156_24188
import RHInBoxT_1d4000000_3999999d4000000_24188_96877d4
import RHInBoxT_1d4000000_3999999d4000000_24219_24250
import RHInBoxT_1d4000000_3999999d4000000_24250_97125d4
import RHInBoxT_1d4000000_3999999d4000000_24281_24312
import RHInBoxT_1d4000000_3999999d4000000_24312_24344
import RHInBoxT_1d4000000_3999999d4000000_24344_24375
import RHInBoxT_1d4000000_3999999d4000000_24375_24406
import RHInBoxT_1d4000000_3999999d4000000_24406_24438
import RHInBoxT_1d4000000_3999999d4000000_24438_24469
import RHInBoxT_1d4000000_3999999d4000000_24469_98001d4
import RHInBoxT_1d4000000_3999999d4000000_24500_24531
import RHInBoxT_1d4000000_3999999d4000000_24531_24562
import RHInBoxT_1d4000000_3999999d4000000_24562_24594
import RHInBoxT_1d4000000_3999999d4000000_24594_24625
import RHInBoxT_1d4000000_3999999d4000000_24625_98625d4
import RHInBoxT_1d4000000_3999999d4000000_24656_24688
import RHInBoxT_1d4000000_3999999d4000000_24688_24719
import RHInBoxT_1d4000000_3999999d4000000_24719_24750
import RHInBoxT_1d4000000_3999999d4000000_24750_24781
import RHInBoxT_1d4000000_3999999d4000000_99123d4_24812
import RHInBoxT_1d4000000_3999999d4000000_24812_24844
import RHInBoxT_1d4000000_3999999d4000000_24844_24875
import RHInBoxT_1d4000000_3999999d4000000_24875_24906
import RHInBoxT_1d4000000_3999999d4000000_24906_24938
import RHInBoxT_1d4000000_3999999d4000000_24938_24969
import RHInBoxT_1d4000000_3999999d4000000_24969_25000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h25000

/-- The 32-band NOMINAL partition of `[24000, 25000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 24000
  | 1 => 24031
  | 2 => 24062
  | 3 => 24094
  | 4 => 24125
  | 5 => 24156
  | 6 => 24188
  | 7 => 24219
  | 8 => 24250
  | 9 => 24281
  | 10 => 24312
  | 11 => 24344
  | 12 => 24375
  | 13 => 24406
  | 14 => 24438
  | 15 => 24469
  | 16 => 24500
  | 17 => 24531
  | 18 => 24562
  | 19 => 24594
  | 20 => 24625
  | 21 => 24656
  | 22 => 24688
  | 23 => 24719
  | 24 => 24750
  | 25 => 24781
  | 26 => 24812
  | 27 => 24844
  | 28 => 24875
  | 29 => 24906
  | 30 => 24938
  | 31 => 24969
  | 32 => 25000
  | _ => 25000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((24000:ℝ)) ≤ (24031); norm_num
  · show ((24031:ℝ)) ≤ (24062); norm_num
  · show ((24062:ℝ)) ≤ (24094); norm_num
  · show ((24094:ℝ)) ≤ (24125); norm_num
  · show ((24125:ℝ)) ≤ (24156); norm_num
  · show ((24156:ℝ)) ≤ (24188); norm_num
  · show ((24188:ℝ)) ≤ (24219); norm_num
  · show ((24219:ℝ)) ≤ (24250); norm_num
  · show ((24250:ℝ)) ≤ (24281); norm_num
  · show ((24281:ℝ)) ≤ (24312); norm_num
  · show ((24312:ℝ)) ≤ (24344); norm_num
  · show ((24344:ℝ)) ≤ (24375); norm_num
  · show ((24375:ℝ)) ≤ (24406); norm_num
  · show ((24406:ℝ)) ≤ (24438); norm_num
  · show ((24438:ℝ)) ≤ (24469); norm_num
  · show ((24469:ℝ)) ≤ (24500); norm_num
  · show ((24500:ℝ)) ≤ (24531); norm_num
  · show ((24531:ℝ)) ≤ (24562); norm_num
  · show ((24562:ℝ)) ≤ (24594); norm_num
  · show ((24594:ℝ)) ≤ (24625); norm_num
  · show ((24625:ℝ)) ≤ (24656); norm_num
  · show ((24656:ℝ)) ≤ (24688); norm_num
  · show ((24688:ℝ)) ≤ (24719); norm_num
  · show ((24719:ℝ)) ≤ (24750); norm_num
  · show ((24750:ℝ)) ≤ (24781); norm_num
  · show ((24781:ℝ)) ≤ (24812); norm_num
  · show ((24812:ℝ)) ≤ (24844); norm_num
  · show ((24844:ℝ)) ≤ (24875); norm_num
  · show ((24875:ℝ)) ≤ (24906); norm_num
  · show ((24906:ℝ)) ≤ (24938); norm_num
  · show ((24938:ℝ)) ≤ (24969); norm_num
  · show ((24969:ℝ)) ≤ (25000); norm_num
  · show ((25000:ℝ)) ≤ (25000); norm_num
  · exact le_refl _

/-- The lower edges of the 32 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 24000
  | 1 => 96123 / 4
  | 2 => 24062
  | 3 => 24094
  | 4 => 24125
  | 5 => 24156
  | 6 => 24188
  | 7 => 24219
  | 8 => 24250
  | 9 => 24281
  | 10 => 24312
  | 11 => 24344
  | 12 => 24375
  | 13 => 24406
  | 14 => 24438
  | 15 => 24469
  | 16 => 24500
  | 17 => 24531
  | 18 => 24562
  | 19 => 24594
  | 20 => 24625
  | 21 => 24656
  | 22 => 24688
  | 23 => 24719
  | 24 => 24750
  | 25 => 99123 / 4
  | 26 => 24812
  | 27 => 24844
  | 28 => 24875
  | 29 => 24906
  | 30 => 24938
  | 31 => 24969
  | _ => 24969

/-- The upper edges of the 32 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 24031
  | 1 => 24062
  | 2 => 24094
  | 3 => 24125
  | 4 => 24156
  | 5 => 24188
  | 6 => 96877 / 4
  | 7 => 24250
  | 8 => 97125 / 4
  | 9 => 24312
  | 10 => 24344
  | 11 => 24375
  | 12 => 24406
  | 13 => 24438
  | 14 => 24469
  | 15 => 98001 / 4
  | 16 => 24531
  | 17 => 24562
  | 18 => 24594
  | 19 => 24625
  | 20 => 98625 / 4
  | 21 => 24688
  | 22 => 24719
  | 23 => 24750
  | 24 => 24781
  | 25 => 24812
  | 26 => 24844
  | 27 => 24875
  | 28 => 24906
  | 29 => 24938
  | 30 => 24969
  | 31 => 25000
  | _ => 25000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 32 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 25000` (`log 25000 ≤ 11`, `2.7^11 ≥ 25000`). -/
theorem haC_25000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 25000 := by
  have hlog : Real.log 25000 ≤ 11 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h11 : Real.exp 11 = (Real.exp 1) ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 11 ≤ (Real.exp 1) ^ 11 := pow_le_pow_left₀ (by norm_num) he1 11
    rw [h11]; nlinarith [hpow]
  have hpos : 0 < Real.log 25000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 25000
      ≤ (1 / 4000000) * 11 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[24000, 25000]` segment's band hypothesis: every band `i < 32` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 32 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 32 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[24000, 25000]` SEGMENT: every zero with `24000 ≤ Im ≤ 25000` is on the line. -/
theorem segment_24000_25000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 25000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (24000:ℝ) ≤ ρ.im → ρ.im ≤ 25000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 24000 25000 bndSeg 32 (by norm_num) bndSeg_mono rfl rfl haC_25000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 25000 via the HEIGHT CHAIN**: `[0,24000]` ∘ `[24000,25000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_25000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 25000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 25000 → ρ.re = 1 / 2 := by
  have hγ24000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 24000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 24000 25000
    (AllZeros_h24000.all_nontrivial_zeros_up_to_height_24000_of_bands
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
      hγ24000)
    (segment_24000_25000 hbands hγ)

end AllZeros_h25000
