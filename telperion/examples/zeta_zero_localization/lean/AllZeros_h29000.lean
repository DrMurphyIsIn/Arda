/-  Height-chain step: all nontrivial zeta zeros up to height 29000 on Re = 1/2 --
    `AllZeros_h28000` + a `[28000, 29000]` SEGMENT certificate (32 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h28000
import RHInBoxT_1d4000000_3999999d4000000_28000_28031
import RHInBoxT_1d4000000_3999999d4000000_28031_28062
import RHInBoxT_1d4000000_3999999d4000000_28062_28094
import RHInBoxT_1d4000000_3999999d4000000_112375d4_28125
import RHInBoxT_1d4000000_3999999d4000000_28125_28156
import RHInBoxT_1d4000000_3999999d4000000_28156_28188
import RHInBoxT_1d4000000_3999999d4000000_28188_28219
import RHInBoxT_1d4000000_3999999d4000000_112875d4_113001d4
import RHInBoxT_1d4000000_3999999d4000000_28250_28281
import RHInBoxT_1d4000000_3999999d4000000_28281_28312
import RHInBoxT_1d4000000_3999999d4000000_56623d2_28344
import RHInBoxT_1d4000000_3999999d4000000_113375d4_28375
import RHInBoxT_1d4000000_3999999d4000000_28375_28406
import RHInBoxT_1d4000000_3999999d4000000_28406_28438
import RHInBoxT_1d4000000_3999999d4000000_28438_28469
import RHInBoxT_1d4000000_3999999d4000000_28469_28500
import RHInBoxT_1d4000000_3999999d4000000_28500_28531
import RHInBoxT_1d4000000_3999999d4000000_28531_28562
import RHInBoxT_1d4000000_3999999d4000000_114247d4_114377d4
import RHInBoxT_1d4000000_3999999d4000000_28594_114501d4
import RHInBoxT_1d4000000_3999999d4000000_28625_114625d4
import RHInBoxT_1d4000000_3999999d4000000_28656_114753d4
import RHInBoxT_1d4000000_3999999d4000000_28688_28719
import RHInBoxT_1d4000000_3999999d4000000_114875d4_28750
import RHInBoxT_1d4000000_3999999d4000000_28750_28781
import RHInBoxT_1d4000000_3999999d4000000_28781_28812
import RHInBoxT_1d4000000_3999999d4000000_28812_28844
import RHInBoxT_1d4000000_3999999d4000000_115375d4_28875
import RHInBoxT_1d4000000_3999999d4000000_28875_28906
import RHInBoxT_1d4000000_3999999d4000000_28906_28938
import RHInBoxT_1d4000000_3999999d4000000_28938_28969
import RHInBoxT_1d4000000_3999999d4000000_115875d4_29000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h29000

/-- The 32-band NOMINAL partition of `[28000, 29000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 28000
  | 1 => 28031
  | 2 => 28062
  | 3 => 28094
  | 4 => 28125
  | 5 => 28156
  | 6 => 28188
  | 7 => 28219
  | 8 => 28250
  | 9 => 28281
  | 10 => 28312
  | 11 => 28344
  | 12 => 28375
  | 13 => 28406
  | 14 => 28438
  | 15 => 28469
  | 16 => 28500
  | 17 => 28531
  | 18 => 28562
  | 19 => 28594
  | 20 => 28625
  | 21 => 28656
  | 22 => 28688
  | 23 => 28719
  | 24 => 28750
  | 25 => 28781
  | 26 => 28812
  | 27 => 28844
  | 28 => 28875
  | 29 => 28906
  | 30 => 28938
  | 31 => 28969
  | 32 => 29000
  | _ => 29000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((28000:ℝ)) ≤ (28031); norm_num
  · show ((28031:ℝ)) ≤ (28062); norm_num
  · show ((28062:ℝ)) ≤ (28094); norm_num
  · show ((28094:ℝ)) ≤ (28125); norm_num
  · show ((28125:ℝ)) ≤ (28156); norm_num
  · show ((28156:ℝ)) ≤ (28188); norm_num
  · show ((28188:ℝ)) ≤ (28219); norm_num
  · show ((28219:ℝ)) ≤ (28250); norm_num
  · show ((28250:ℝ)) ≤ (28281); norm_num
  · show ((28281:ℝ)) ≤ (28312); norm_num
  · show ((28312:ℝ)) ≤ (28344); norm_num
  · show ((28344:ℝ)) ≤ (28375); norm_num
  · show ((28375:ℝ)) ≤ (28406); norm_num
  · show ((28406:ℝ)) ≤ (28438); norm_num
  · show ((28438:ℝ)) ≤ (28469); norm_num
  · show ((28469:ℝ)) ≤ (28500); norm_num
  · show ((28500:ℝ)) ≤ (28531); norm_num
  · show ((28531:ℝ)) ≤ (28562); norm_num
  · show ((28562:ℝ)) ≤ (28594); norm_num
  · show ((28594:ℝ)) ≤ (28625); norm_num
  · show ((28625:ℝ)) ≤ (28656); norm_num
  · show ((28656:ℝ)) ≤ (28688); norm_num
  · show ((28688:ℝ)) ≤ (28719); norm_num
  · show ((28719:ℝ)) ≤ (28750); norm_num
  · show ((28750:ℝ)) ≤ (28781); norm_num
  · show ((28781:ℝ)) ≤ (28812); norm_num
  · show ((28812:ℝ)) ≤ (28844); norm_num
  · show ((28844:ℝ)) ≤ (28875); norm_num
  · show ((28875:ℝ)) ≤ (28906); norm_num
  · show ((28906:ℝ)) ≤ (28938); norm_num
  · show ((28938:ℝ)) ≤ (28969); norm_num
  · show ((28969:ℝ)) ≤ (29000); norm_num
  · show ((29000:ℝ)) ≤ (29000); norm_num
  · exact le_refl _

/-- The lower edges of the 32 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 28000
  | 1 => 28031
  | 2 => 28062
  | 3 => 112375 / 4
  | 4 => 28125
  | 5 => 28156
  | 6 => 28188
  | 7 => 112875 / 4
  | 8 => 28250
  | 9 => 28281
  | 10 => 56623 / 2
  | 11 => 113375 / 4
  | 12 => 28375
  | 13 => 28406
  | 14 => 28438
  | 15 => 28469
  | 16 => 28500
  | 17 => 28531
  | 18 => 114247 / 4
  | 19 => 28594
  | 20 => 28625
  | 21 => 28656
  | 22 => 28688
  | 23 => 114875 / 4
  | 24 => 28750
  | 25 => 28781
  | 26 => 28812
  | 27 => 115375 / 4
  | 28 => 28875
  | 29 => 28906
  | 30 => 28938
  | 31 => 115875 / 4
  | _ => 115875 / 4

/-- The upper edges of the 32 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 28031
  | 1 => 28062
  | 2 => 28094
  | 3 => 28125
  | 4 => 28156
  | 5 => 28188
  | 6 => 28219
  | 7 => 113001 / 4
  | 8 => 28281
  | 9 => 28312
  | 10 => 28344
  | 11 => 28375
  | 12 => 28406
  | 13 => 28438
  | 14 => 28469
  | 15 => 28500
  | 16 => 28531
  | 17 => 28562
  | 18 => 114377 / 4
  | 19 => 114501 / 4
  | 20 => 114625 / 4
  | 21 => 114753 / 4
  | 22 => 28719
  | 23 => 28750
  | 24 => 28781
  | 25 => 28812
  | 26 => 28844
  | 27 => 28875
  | 28 => 28906
  | 29 => 28938
  | 30 => 28969
  | 31 => 29000
  | _ => 29000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 32 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 29000` (`log 29000 ≤ 11`, `2.7^11 ≥ 29000`). -/
theorem haC_29000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 29000 := by
  have hlog : Real.log 29000 ≤ 11 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h11 : Real.exp 11 = (Real.exp 1) ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 11 ≤ (Real.exp 1) ^ 11 := pow_le_pow_left₀ (by norm_num) he1 11
    rw [h11]; nlinarith [hpow]
  have hpos : 0 < Real.log 29000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 29000
      ≤ (1 / 4000000) * 11 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[28000, 29000]` segment's band hypothesis: every band `i < 32` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 32 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 32 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[28000, 29000]` SEGMENT: every zero with `28000 ≤ Im ≤ 29000` is on the line. -/
theorem segment_28000_29000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 29000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (28000:ℝ) ≤ ρ.im → ρ.im ≤ 29000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 28000 29000 bndSeg 32 (by norm_num) bndSeg_mono rfl rfl haC_29000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 29000 via the HEIGHT CHAIN**: `[0,28000]` ∘ `[28000,29000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_29000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 29000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 29000 → ρ.re = 1 / 2 := by
  have hγ28000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 28000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 28000 29000
    (AllZeros_h28000.all_nontrivial_zeros_up_to_height_28000_of_bands
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
      hγ28000)
    (segment_28000_29000 hbands hγ)

end AllZeros_h29000
