/-  Height-chain step: all nontrivial zeta zeros up to height 24000 on Re = 1/2 --
    `AllZeros_h23000` + a `[23000, 24000]` SEGMENT certificate (32 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h23000
import RHInBoxT_1d4000000_3999999d4000000_23000_23031
import RHInBoxT_1d4000000_3999999d4000000_23031_23062
import RHInBoxT_1d4000000_3999999d4000000_23062_92377d4
import RHInBoxT_1d4000000_3999999d4000000_23094_23125
import RHInBoxT_1d4000000_3999999d4000000_92499d4_23156
import RHInBoxT_1d4000000_3999999d4000000_92623d4_23188
import RHInBoxT_1d4000000_3999999d4000000_23188_23219
import RHInBoxT_1d4000000_3999999d4000000_23219_23250
import RHInBoxT_1d4000000_3999999d4000000_23250_23281
import RHInBoxT_1d4000000_3999999d4000000_23281_23312
import RHInBoxT_1d4000000_3999999d4000000_23312_93377d4
import RHInBoxT_1d4000000_3999999d4000000_23344_93501d4
import RHInBoxT_1d4000000_3999999d4000000_23375_23406
import RHInBoxT_1d4000000_3999999d4000000_23406_23438
import RHInBoxT_1d4000000_3999999d4000000_23438_23469
import RHInBoxT_1d4000000_3999999d4000000_23469_23500
import RHInBoxT_1d4000000_3999999d4000000_23500_23531
import RHInBoxT_1d4000000_3999999d4000000_23531_23562
import RHInBoxT_1d4000000_3999999d4000000_94247d4_23594
import RHInBoxT_1d4000000_3999999d4000000_23594_23625
import RHInBoxT_1d4000000_3999999d4000000_23625_23656
import RHInBoxT_1d4000000_3999999d4000000_23656_94753d4
import RHInBoxT_1d4000000_3999999d4000000_23688_23719
import RHInBoxT_1d4000000_3999999d4000000_94875d4_23750
import RHInBoxT_1d4000000_3999999d4000000_23750_95125d4
import RHInBoxT_1d4000000_3999999d4000000_23781_23812
import RHInBoxT_1d4000000_3999999d4000000_95247d4_95377d4
import RHInBoxT_1d4000000_3999999d4000000_23844_23875
import RHInBoxT_1d4000000_3999999d4000000_23875_23906
import RHInBoxT_1d4000000_3999999d4000000_23906_23938
import RHInBoxT_1d4000000_3999999d4000000_23938_23969
import RHInBoxT_1d4000000_3999999d4000000_23969_24000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h24000

/-- The 32-band NOMINAL partition of `[23000, 24000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 23000
  | 1 => 23031
  | 2 => 23062
  | 3 => 23094
  | 4 => 23125
  | 5 => 23156
  | 6 => 23188
  | 7 => 23219
  | 8 => 23250
  | 9 => 23281
  | 10 => 23312
  | 11 => 23344
  | 12 => 23375
  | 13 => 23406
  | 14 => 23438
  | 15 => 23469
  | 16 => 23500
  | 17 => 23531
  | 18 => 23562
  | 19 => 23594
  | 20 => 23625
  | 21 => 23656
  | 22 => 23688
  | 23 => 23719
  | 24 => 23750
  | 25 => 23781
  | 26 => 23812
  | 27 => 23844
  | 28 => 23875
  | 29 => 23906
  | 30 => 23938
  | 31 => 23969
  | 32 => 24000
  | _ => 24000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((23000:ℝ)) ≤ (23031); norm_num
  · show ((23031:ℝ)) ≤ (23062); norm_num
  · show ((23062:ℝ)) ≤ (23094); norm_num
  · show ((23094:ℝ)) ≤ (23125); norm_num
  · show ((23125:ℝ)) ≤ (23156); norm_num
  · show ((23156:ℝ)) ≤ (23188); norm_num
  · show ((23188:ℝ)) ≤ (23219); norm_num
  · show ((23219:ℝ)) ≤ (23250); norm_num
  · show ((23250:ℝ)) ≤ (23281); norm_num
  · show ((23281:ℝ)) ≤ (23312); norm_num
  · show ((23312:ℝ)) ≤ (23344); norm_num
  · show ((23344:ℝ)) ≤ (23375); norm_num
  · show ((23375:ℝ)) ≤ (23406); norm_num
  · show ((23406:ℝ)) ≤ (23438); norm_num
  · show ((23438:ℝ)) ≤ (23469); norm_num
  · show ((23469:ℝ)) ≤ (23500); norm_num
  · show ((23500:ℝ)) ≤ (23531); norm_num
  · show ((23531:ℝ)) ≤ (23562); norm_num
  · show ((23562:ℝ)) ≤ (23594); norm_num
  · show ((23594:ℝ)) ≤ (23625); norm_num
  · show ((23625:ℝ)) ≤ (23656); norm_num
  · show ((23656:ℝ)) ≤ (23688); norm_num
  · show ((23688:ℝ)) ≤ (23719); norm_num
  · show ((23719:ℝ)) ≤ (23750); norm_num
  · show ((23750:ℝ)) ≤ (23781); norm_num
  · show ((23781:ℝ)) ≤ (23812); norm_num
  · show ((23812:ℝ)) ≤ (23844); norm_num
  · show ((23844:ℝ)) ≤ (23875); norm_num
  · show ((23875:ℝ)) ≤ (23906); norm_num
  · show ((23906:ℝ)) ≤ (23938); norm_num
  · show ((23938:ℝ)) ≤ (23969); norm_num
  · show ((23969:ℝ)) ≤ (24000); norm_num
  · show ((24000:ℝ)) ≤ (24000); norm_num
  · exact le_refl _

/-- The lower edges of the 32 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 23000
  | 1 => 23031
  | 2 => 23062
  | 3 => 23094
  | 4 => 92499 / 4
  | 5 => 92623 / 4
  | 6 => 23188
  | 7 => 23219
  | 8 => 23250
  | 9 => 23281
  | 10 => 23312
  | 11 => 23344
  | 12 => 23375
  | 13 => 23406
  | 14 => 23438
  | 15 => 23469
  | 16 => 23500
  | 17 => 23531
  | 18 => 94247 / 4
  | 19 => 23594
  | 20 => 23625
  | 21 => 23656
  | 22 => 23688
  | 23 => 94875 / 4
  | 24 => 23750
  | 25 => 23781
  | 26 => 95247 / 4
  | 27 => 23844
  | 28 => 23875
  | 29 => 23906
  | 30 => 23938
  | 31 => 23969
  | _ => 23969

/-- The upper edges of the 32 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 23031
  | 1 => 23062
  | 2 => 92377 / 4
  | 3 => 23125
  | 4 => 23156
  | 5 => 23188
  | 6 => 23219
  | 7 => 23250
  | 8 => 23281
  | 9 => 23312
  | 10 => 93377 / 4
  | 11 => 93501 / 4
  | 12 => 23406
  | 13 => 23438
  | 14 => 23469
  | 15 => 23500
  | 16 => 23531
  | 17 => 23562
  | 18 => 23594
  | 19 => 23625
  | 20 => 23656
  | 21 => 94753 / 4
  | 22 => 23719
  | 23 => 23750
  | 24 => 95125 / 4
  | 25 => 23812
  | 26 => 95377 / 4
  | 27 => 23875
  | 28 => 23906
  | 29 => 23938
  | 30 => 23969
  | 31 => 24000
  | _ => 24000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 32 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 24000` (`log 24000 ≤ 11`, `2.7^11 ≥ 24000`). -/
theorem haC_24000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 24000 := by
  have hlog : Real.log 24000 ≤ 11 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h11 : Real.exp 11 = (Real.exp 1) ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 11 ≤ (Real.exp 1) ^ 11 := pow_le_pow_left₀ (by norm_num) he1 11
    rw [h11]; nlinarith [hpow]
  have hpos : 0 < Real.log 24000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 24000
      ≤ (1 / 4000000) * 11 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[23000, 24000]` segment's band hypothesis: every band `i < 32` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 32 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 32 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[23000, 24000]` SEGMENT: every zero with `23000 ≤ Im ≤ 24000` is on the line. -/
theorem segment_23000_24000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 24000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (23000:ℝ) ≤ ρ.im → ρ.im ≤ 24000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 23000 24000 bndSeg 32 (by norm_num) bndSeg_mono rfl rfl haC_24000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 24000 via the HEIGHT CHAIN**: `[0,23000]` ∘ `[23000,24000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_24000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 24000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 24000 → ρ.re = 1 / 2 := by
  have hγ23000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 23000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 23000 24000
    (AllZeros_h23000.all_nontrivial_zeros_up_to_height_23000_of_bands
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
      hγ23000)
    (segment_23000_24000 hbands hγ)

end AllZeros_h24000
