/-  Height-chain step: all nontrivial zeta zeros up to height 28000 on Re = 1/2 --
    `AllZeros_h27000` + a `[27000, 28000]` SEGMENT certificate (32 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h27000
import RHInBoxT_1d4000000_3999999d4000000_27000_27031
import RHInBoxT_1d4000000_3999999d4000000_27031_108249d4
import RHInBoxT_1d4000000_3999999d4000000_27062_27094
import RHInBoxT_1d4000000_3999999d4000000_27094_27125
import RHInBoxT_1d4000000_3999999d4000000_27125_27156
import RHInBoxT_1d4000000_3999999d4000000_108623d4_27188
import RHInBoxT_1d4000000_3999999d4000000_27188_108877d4
import RHInBoxT_1d4000000_3999999d4000000_27219_27250
import RHInBoxT_1d4000000_3999999d4000000_108999d4_27281
import RHInBoxT_1d4000000_3999999d4000000_27281_27312
import RHInBoxT_1d4000000_3999999d4000000_27312_27344
import RHInBoxT_1d4000000_3999999d4000000_109375d4_27375
import RHInBoxT_1d4000000_3999999d4000000_27375_27406
import RHInBoxT_1d4000000_3999999d4000000_27406_27438
import RHInBoxT_1d4000000_3999999d4000000_27438_27469
import RHInBoxT_1d4000000_3999999d4000000_27469_27500
import RHInBoxT_1d4000000_3999999d4000000_27500_27531
import RHInBoxT_1d4000000_3999999d4000000_27531_27562
import RHInBoxT_1d4000000_3999999d4000000_27562_110377d4
import RHInBoxT_1d4000000_3999999d4000000_27594_27625
import RHInBoxT_1d4000000_3999999d4000000_27625_27656
import RHInBoxT_1d4000000_3999999d4000000_110623d4_27688
import RHInBoxT_1d4000000_3999999d4000000_27688_27719
import RHInBoxT_1d4000000_3999999d4000000_27719_27750
import RHInBoxT_1d4000000_3999999d4000000_27750_27781
import RHInBoxT_1d4000000_3999999d4000000_111123d4_111249d4
import RHInBoxT_1d4000000_3999999d4000000_27812_111377d4
import RHInBoxT_1d4000000_3999999d4000000_27844_27875
import RHInBoxT_1d4000000_3999999d4000000_27875_27906
import RHInBoxT_1d4000000_3999999d4000000_27906_27938
import RHInBoxT_1d4000000_3999999d4000000_27938_27969
import RHInBoxT_1d4000000_3999999d4000000_111875d4_28000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h28000

/-- The 32-band NOMINAL partition of `[27000, 28000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 27000
  | 1 => 27031
  | 2 => 27062
  | 3 => 27094
  | 4 => 27125
  | 5 => 27156
  | 6 => 27188
  | 7 => 27219
  | 8 => 27250
  | 9 => 27281
  | 10 => 27312
  | 11 => 27344
  | 12 => 27375
  | 13 => 27406
  | 14 => 27438
  | 15 => 27469
  | 16 => 27500
  | 17 => 27531
  | 18 => 27562
  | 19 => 27594
  | 20 => 27625
  | 21 => 27656
  | 22 => 27688
  | 23 => 27719
  | 24 => 27750
  | 25 => 27781
  | 26 => 27812
  | 27 => 27844
  | 28 => 27875
  | 29 => 27906
  | 30 => 27938
  | 31 => 27969
  | 32 => 28000
  | _ => 28000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((27000:ℝ)) ≤ (27031); norm_num
  · show ((27031:ℝ)) ≤ (27062); norm_num
  · show ((27062:ℝ)) ≤ (27094); norm_num
  · show ((27094:ℝ)) ≤ (27125); norm_num
  · show ((27125:ℝ)) ≤ (27156); norm_num
  · show ((27156:ℝ)) ≤ (27188); norm_num
  · show ((27188:ℝ)) ≤ (27219); norm_num
  · show ((27219:ℝ)) ≤ (27250); norm_num
  · show ((27250:ℝ)) ≤ (27281); norm_num
  · show ((27281:ℝ)) ≤ (27312); norm_num
  · show ((27312:ℝ)) ≤ (27344); norm_num
  · show ((27344:ℝ)) ≤ (27375); norm_num
  · show ((27375:ℝ)) ≤ (27406); norm_num
  · show ((27406:ℝ)) ≤ (27438); norm_num
  · show ((27438:ℝ)) ≤ (27469); norm_num
  · show ((27469:ℝ)) ≤ (27500); norm_num
  · show ((27500:ℝ)) ≤ (27531); norm_num
  · show ((27531:ℝ)) ≤ (27562); norm_num
  · show ((27562:ℝ)) ≤ (27594); norm_num
  · show ((27594:ℝ)) ≤ (27625); norm_num
  · show ((27625:ℝ)) ≤ (27656); norm_num
  · show ((27656:ℝ)) ≤ (27688); norm_num
  · show ((27688:ℝ)) ≤ (27719); norm_num
  · show ((27719:ℝ)) ≤ (27750); norm_num
  · show ((27750:ℝ)) ≤ (27781); norm_num
  · show ((27781:ℝ)) ≤ (27812); norm_num
  · show ((27812:ℝ)) ≤ (27844); norm_num
  · show ((27844:ℝ)) ≤ (27875); norm_num
  · show ((27875:ℝ)) ≤ (27906); norm_num
  · show ((27906:ℝ)) ≤ (27938); norm_num
  · show ((27938:ℝ)) ≤ (27969); norm_num
  · show ((27969:ℝ)) ≤ (28000); norm_num
  · show ((28000:ℝ)) ≤ (28000); norm_num
  · exact le_refl _

/-- The lower edges of the 32 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 27000
  | 1 => 27031
  | 2 => 27062
  | 3 => 27094
  | 4 => 27125
  | 5 => 108623 / 4
  | 6 => 27188
  | 7 => 27219
  | 8 => 108999 / 4
  | 9 => 27281
  | 10 => 27312
  | 11 => 109375 / 4
  | 12 => 27375
  | 13 => 27406
  | 14 => 27438
  | 15 => 27469
  | 16 => 27500
  | 17 => 27531
  | 18 => 27562
  | 19 => 27594
  | 20 => 27625
  | 21 => 110623 / 4
  | 22 => 27688
  | 23 => 27719
  | 24 => 27750
  | 25 => 111123 / 4
  | 26 => 27812
  | 27 => 27844
  | 28 => 27875
  | 29 => 27906
  | 30 => 27938
  | 31 => 111875 / 4
  | _ => 111875 / 4

/-- The upper edges of the 32 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 27031
  | 1 => 108249 / 4
  | 2 => 27094
  | 3 => 27125
  | 4 => 27156
  | 5 => 27188
  | 6 => 108877 / 4
  | 7 => 27250
  | 8 => 27281
  | 9 => 27312
  | 10 => 27344
  | 11 => 27375
  | 12 => 27406
  | 13 => 27438
  | 14 => 27469
  | 15 => 27500
  | 16 => 27531
  | 17 => 27562
  | 18 => 110377 / 4
  | 19 => 27625
  | 20 => 27656
  | 21 => 27688
  | 22 => 27719
  | 23 => 27750
  | 24 => 27781
  | 25 => 111249 / 4
  | 26 => 111377 / 4
  | 27 => 27875
  | 28 => 27906
  | 29 => 27938
  | 30 => 27969
  | 31 => 28000
  | _ => 28000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 32 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 28000` (`log 28000 ≤ 11`, `2.7^11 ≥ 28000`). -/
theorem haC_28000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 28000 := by
  have hlog : Real.log 28000 ≤ 11 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h11 : Real.exp 11 = (Real.exp 1) ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 11 ≤ (Real.exp 1) ^ 11 := pow_le_pow_left₀ (by norm_num) he1 11
    rw [h11]; nlinarith [hpow]
  have hpos : 0 < Real.log 28000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 28000
      ≤ (1 / 4000000) * 11 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[27000, 28000]` segment's band hypothesis: every band `i < 32` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 32 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 32 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[27000, 28000]` SEGMENT: every zero with `27000 ≤ Im ≤ 28000` is on the line. -/
theorem segment_27000_28000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 28000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (27000:ℝ) ≤ ρ.im → ρ.im ≤ 28000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 27000 28000 bndSeg 32 (by norm_num) bndSeg_mono rfl rfl haC_28000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 28000 via the HEIGHT CHAIN**: `[0,27000]` ∘ `[27000,28000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_28000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 28000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 28000 → ρ.re = 1 / 2 := by
  have hγ27000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 27000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 27000 28000
    (AllZeros_h27000.all_nontrivial_zeros_up_to_height_27000_of_bands
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
      hγ27000)
    (segment_27000_28000 hbands hγ)

end AllZeros_h28000
