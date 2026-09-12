/-  Height-chain step: all nontrivial zeta zeros up to height 11000 on Re = 1/2 --
    `AllZeros_h10000` + a `[10000, 11000]` SEGMENT certificate (28 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h10000
import RHInBoxT_1d4000000_3999999d4000000_10000_10036
import RHInBoxT_1d4000000_3999999d4000000_10036_10071
import RHInBoxT_1d4000000_3999999d4000000_10071_40429d4
import RHInBoxT_1d4000000_3999999d4000000_10107_10143
import RHInBoxT_1d4000000_3999999d4000000_10143_10179
import RHInBoxT_1d4000000_3999999d4000000_40715d4_10214
import RHInBoxT_1d4000000_3999999d4000000_10214_10250
import RHInBoxT_1d4000000_3999999d4000000_10250_10286
import RHInBoxT_1d4000000_3999999d4000000_10286_10321
import RHInBoxT_1d4000000_3999999d4000000_10321_10357
import RHInBoxT_1d4000000_3999999d4000000_10357_10393
import RHInBoxT_1d4000000_3999999d4000000_10393_10429
import RHInBoxT_1d4000000_3999999d4000000_10429_10464
import RHInBoxT_1d4000000_3999999d4000000_10464_10500
import RHInBoxT_1d4000000_3999999d4000000_10500_10536
import RHInBoxT_1d4000000_3999999d4000000_10536_10571
import RHInBoxT_1d4000000_3999999d4000000_10571_10607
import RHInBoxT_1d4000000_3999999d4000000_10607_10643
import RHInBoxT_1d4000000_3999999d4000000_10643_42717d4
import RHInBoxT_1d4000000_3999999d4000000_10679_10714
import RHInBoxT_1d4000000_3999999d4000000_10714_10750
import RHInBoxT_1d4000000_3999999d4000000_42999d4_10786
import RHInBoxT_1d4000000_3999999d4000000_43143d4_10821
import RHInBoxT_1d4000000_3999999d4000000_10821_43429d4
import RHInBoxT_1d4000000_3999999d4000000_10857_10893
import RHInBoxT_1d4000000_3999999d4000000_10893_10929
import RHInBoxT_1d4000000_3999999d4000000_10929_10964
import RHInBoxT_1d4000000_3999999d4000000_10964_11000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h11000

/-- The 28-band NOMINAL partition of `[10000, 11000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 10000
  | 1 => 10036
  | 2 => 10071
  | 3 => 10107
  | 4 => 10143
  | 5 => 10179
  | 6 => 10214
  | 7 => 10250
  | 8 => 10286
  | 9 => 10321
  | 10 => 10357
  | 11 => 10393
  | 12 => 10429
  | 13 => 10464
  | 14 => 10500
  | 15 => 10536
  | 16 => 10571
  | 17 => 10607
  | 18 => 10643
  | 19 => 10679
  | 20 => 10714
  | 21 => 10750
  | 22 => 10786
  | 23 => 10821
  | 24 => 10857
  | 25 => 10893
  | 26 => 10929
  | 27 => 10964
  | 28 => 11000
  | _ => 11000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((10000:ℝ)) ≤ (10036); norm_num
  · show ((10036:ℝ)) ≤ (10071); norm_num
  · show ((10071:ℝ)) ≤ (10107); norm_num
  · show ((10107:ℝ)) ≤ (10143); norm_num
  · show ((10143:ℝ)) ≤ (10179); norm_num
  · show ((10179:ℝ)) ≤ (10214); norm_num
  · show ((10214:ℝ)) ≤ (10250); norm_num
  · show ((10250:ℝ)) ≤ (10286); norm_num
  · show ((10286:ℝ)) ≤ (10321); norm_num
  · show ((10321:ℝ)) ≤ (10357); norm_num
  · show ((10357:ℝ)) ≤ (10393); norm_num
  · show ((10393:ℝ)) ≤ (10429); norm_num
  · show ((10429:ℝ)) ≤ (10464); norm_num
  · show ((10464:ℝ)) ≤ (10500); norm_num
  · show ((10500:ℝ)) ≤ (10536); norm_num
  · show ((10536:ℝ)) ≤ (10571); norm_num
  · show ((10571:ℝ)) ≤ (10607); norm_num
  · show ((10607:ℝ)) ≤ (10643); norm_num
  · show ((10643:ℝ)) ≤ (10679); norm_num
  · show ((10679:ℝ)) ≤ (10714); norm_num
  · show ((10714:ℝ)) ≤ (10750); norm_num
  · show ((10750:ℝ)) ≤ (10786); norm_num
  · show ((10786:ℝ)) ≤ (10821); norm_num
  · show ((10821:ℝ)) ≤ (10857); norm_num
  · show ((10857:ℝ)) ≤ (10893); norm_num
  · show ((10893:ℝ)) ≤ (10929); norm_num
  · show ((10929:ℝ)) ≤ (10964); norm_num
  · show ((10964:ℝ)) ≤ (11000); norm_num
  · show ((11000:ℝ)) ≤ (11000); norm_num
  · exact le_refl _

/-- The lower edges of the 28 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 10000
  | 1 => 10036
  | 2 => 10071
  | 3 => 10107
  | 4 => 10143
  | 5 => 40715 / 4
  | 6 => 10214
  | 7 => 10250
  | 8 => 10286
  | 9 => 10321
  | 10 => 10357
  | 11 => 10393
  | 12 => 10429
  | 13 => 10464
  | 14 => 10500
  | 15 => 10536
  | 16 => 10571
  | 17 => 10607
  | 18 => 10643
  | 19 => 10679
  | 20 => 10714
  | 21 => 42999 / 4
  | 22 => 43143 / 4
  | 23 => 10821
  | 24 => 10857
  | 25 => 10893
  | 26 => 10929
  | 27 => 10964
  | _ => 10964

/-- The upper edges of the 28 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 10036
  | 1 => 10071
  | 2 => 40429 / 4
  | 3 => 10143
  | 4 => 10179
  | 5 => 10214
  | 6 => 10250
  | 7 => 10286
  | 8 => 10321
  | 9 => 10357
  | 10 => 10393
  | 11 => 10429
  | 12 => 10464
  | 13 => 10500
  | 14 => 10536
  | 15 => 10571
  | 16 => 10607
  | 17 => 10643
  | 18 => 42717 / 4
  | 19 => 10714
  | 20 => 10750
  | 21 => 10786
  | 22 => 10821
  | 23 => 43429 / 4
  | 24 => 10893
  | 25 => 10929
  | 26 => 10964
  | 27 => 11000
  | _ => 11000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 28 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 11000` (`log 11000 ≤ 10`, `2.7^10 ≥ 11000`). -/
theorem haC_11000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 11000 := by
  have hlog : Real.log 11000 ≤ 10 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h10 : Real.exp 10 = (Real.exp 1) ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 10 ≤ (Real.exp 1) ^ 10 := pow_le_pow_left₀ (by norm_num) he1 10
    rw [h10]; nlinarith [hpow]
  have hpos : 0 < Real.log 11000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 11000
      ≤ (1 / 4000000) * 10 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[10000, 11000]` segment's band hypothesis: every band `i < 28` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 28 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 28 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[10000, 11000]` SEGMENT: every zero with `10000 ≤ Im ≤ 11000` is on the line. -/
theorem segment_10000_11000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 11000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (10000:ℝ) ≤ ρ.im → ρ.im ≤ 11000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 10000 11000 bndSeg 28 (by norm_num) bndSeg_mono rfl rfl haC_11000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 11000 via the HEIGHT CHAIN**: `[0,10000]` ∘ `[10000,11000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_11000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 11000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 11000 → ρ.re = 1 / 2 := by
  have hγ10000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 10000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 10000 11000
    (AllZeros_h10000.all_nontrivial_zeros_up_to_height_10000_of_bands
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
      hγ10000)
    (segment_10000_11000 hbands hγ)

end AllZeros_h11000
