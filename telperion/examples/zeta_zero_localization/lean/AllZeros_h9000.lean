/-  Height-chain step: all nontrivial zeta zeros up to height 9000 on Re = 1/2 --
    `AllZeros_h8000` + a `[8000, 9000]` SEGMENT certificate (28 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h8000
import RHInBoxT_1d4000000_3999999d4000000_8000_8036
import RHInBoxT_1d4000000_3999999d4000000_32143d4_8071
import RHInBoxT_1d4000000_3999999d4000000_8071_8107
import RHInBoxT_1d4000000_3999999d4000000_32427d4_8143
import RHInBoxT_1d4000000_3999999d4000000_8143_8179
import RHInBoxT_1d4000000_3999999d4000000_8179_8214
import RHInBoxT_1d4000000_3999999d4000000_8214_8250
import RHInBoxT_1d4000000_3999999d4000000_8250_8286
import RHInBoxT_1d4000000_3999999d4000000_8286_8321
import RHInBoxT_1d4000000_3999999d4000000_8321_8357
import RHInBoxT_1d4000000_3999999d4000000_8357_8393
import RHInBoxT_1d4000000_3999999d4000000_8393_8429
import RHInBoxT_1d4000000_3999999d4000000_8429_8464
import RHInBoxT_1d4000000_3999999d4000000_8464_8500
import RHInBoxT_1d4000000_3999999d4000000_8500_34145d4
import RHInBoxT_1d4000000_3999999d4000000_8536_8571
import RHInBoxT_1d4000000_3999999d4000000_34283d4_8607
import RHInBoxT_1d4000000_3999999d4000000_8607_8643
import RHInBoxT_1d4000000_3999999d4000000_8643_8679
import RHInBoxT_1d4000000_3999999d4000000_8679_34857d4
import RHInBoxT_1d4000000_3999999d4000000_8714_8750
import RHInBoxT_1d4000000_3999999d4000000_8750_35145d4
import RHInBoxT_1d4000000_3999999d4000000_8786_8821
import RHInBoxT_1d4000000_3999999d4000000_8821_8857
import RHInBoxT_1d4000000_3999999d4000000_8857_8893
import RHInBoxT_1d4000000_3999999d4000000_8893_8929
import RHInBoxT_1d4000000_3999999d4000000_8929_8964
import RHInBoxT_1d4000000_3999999d4000000_8964_9000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h9000

/-- The 28-band NOMINAL partition of `[8000, 9000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 8000
  | 1 => 8036
  | 2 => 8071
  | 3 => 8107
  | 4 => 8143
  | 5 => 8179
  | 6 => 8214
  | 7 => 8250
  | 8 => 8286
  | 9 => 8321
  | 10 => 8357
  | 11 => 8393
  | 12 => 8429
  | 13 => 8464
  | 14 => 8500
  | 15 => 8536
  | 16 => 8571
  | 17 => 8607
  | 18 => 8643
  | 19 => 8679
  | 20 => 8714
  | 21 => 8750
  | 22 => 8786
  | 23 => 8821
  | 24 => 8857
  | 25 => 8893
  | 26 => 8929
  | 27 => 8964
  | 28 => 9000
  | _ => 9000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((8000:ℝ)) ≤ (8036); norm_num
  · show ((8036:ℝ)) ≤ (8071); norm_num
  · show ((8071:ℝ)) ≤ (8107); norm_num
  · show ((8107:ℝ)) ≤ (8143); norm_num
  · show ((8143:ℝ)) ≤ (8179); norm_num
  · show ((8179:ℝ)) ≤ (8214); norm_num
  · show ((8214:ℝ)) ≤ (8250); norm_num
  · show ((8250:ℝ)) ≤ (8286); norm_num
  · show ((8286:ℝ)) ≤ (8321); norm_num
  · show ((8321:ℝ)) ≤ (8357); norm_num
  · show ((8357:ℝ)) ≤ (8393); norm_num
  · show ((8393:ℝ)) ≤ (8429); norm_num
  · show ((8429:ℝ)) ≤ (8464); norm_num
  · show ((8464:ℝ)) ≤ (8500); norm_num
  · show ((8500:ℝ)) ≤ (8536); norm_num
  · show ((8536:ℝ)) ≤ (8571); norm_num
  · show ((8571:ℝ)) ≤ (8607); norm_num
  · show ((8607:ℝ)) ≤ (8643); norm_num
  · show ((8643:ℝ)) ≤ (8679); norm_num
  · show ((8679:ℝ)) ≤ (8714); norm_num
  · show ((8714:ℝ)) ≤ (8750); norm_num
  · show ((8750:ℝ)) ≤ (8786); norm_num
  · show ((8786:ℝ)) ≤ (8821); norm_num
  · show ((8821:ℝ)) ≤ (8857); norm_num
  · show ((8857:ℝ)) ≤ (8893); norm_num
  · show ((8893:ℝ)) ≤ (8929); norm_num
  · show ((8929:ℝ)) ≤ (8964); norm_num
  · show ((8964:ℝ)) ≤ (9000); norm_num
  · show ((9000:ℝ)) ≤ (9000); norm_num
  · exact le_refl _

/-- The lower edges of the 28 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 8000
  | 1 => 32143 / 4
  | 2 => 8071
  | 3 => 32427 / 4
  | 4 => 8143
  | 5 => 8179
  | 6 => 8214
  | 7 => 8250
  | 8 => 8286
  | 9 => 8321
  | 10 => 8357
  | 11 => 8393
  | 12 => 8429
  | 13 => 8464
  | 14 => 8500
  | 15 => 8536
  | 16 => 34283 / 4
  | 17 => 8607
  | 18 => 8643
  | 19 => 8679
  | 20 => 8714
  | 21 => 8750
  | 22 => 8786
  | 23 => 8821
  | 24 => 8857
  | 25 => 8893
  | 26 => 8929
  | 27 => 8964
  | _ => 8964

/-- The upper edges of the 28 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 8036
  | 1 => 8071
  | 2 => 8107
  | 3 => 8143
  | 4 => 8179
  | 5 => 8214
  | 6 => 8250
  | 7 => 8286
  | 8 => 8321
  | 9 => 8357
  | 10 => 8393
  | 11 => 8429
  | 12 => 8464
  | 13 => 8500
  | 14 => 34145 / 4
  | 15 => 8571
  | 16 => 8607
  | 17 => 8643
  | 18 => 8679
  | 19 => 34857 / 4
  | 20 => 8750
  | 21 => 35145 / 4
  | 22 => 8821
  | 23 => 8857
  | 24 => 8893
  | 25 => 8929
  | 26 => 8964
  | 27 => 9000
  | _ => 9000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 28 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 9000` (`log 9000 ≤ 10`, `2.7^10 ≥ 9000`). -/
theorem haC_9000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 9000 := by
  have hlog : Real.log 9000 ≤ 10 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h10 : Real.exp 10 = (Real.exp 1) ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 10 ≤ (Real.exp 1) ^ 10 := pow_le_pow_left₀ (by norm_num) he1 10
    rw [h10]; nlinarith [hpow]
  have hpos : 0 < Real.log 9000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 9000
      ≤ (1 / 4000000) * 10 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[8000, 9000]` segment's band hypothesis: every band `i < 28` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 28 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 28 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[8000, 9000]` SEGMENT: every zero with `8000 ≤ Im ≤ 9000` is on the line. -/
theorem segment_8000_9000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 9000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (8000:ℝ) ≤ ρ.im → ρ.im ≤ 9000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 8000 9000 bndSeg 28 (by norm_num) bndSeg_mono rfl rfl haC_9000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 9000 via the HEIGHT CHAIN**: `[0,8000]` ∘ `[8000,9000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_9000_of_bands
    (hbands_1000 : AllZeros_h1000.BandHyp)
    (hbands_2000 : AllZeros_h2000.BandHyp)
    (hbands_3000 : AllZeros_h3000.BandHyp)
    (hbands_4000 : AllZeros_h4000.BandHyp)
    (hbands_5000 : AllZeros_h5000.BandHyp)
    (hbands_6000 : AllZeros_h6000.BandHyp)
    (hbands_7000 : AllZeros_h7000.BandHyp)
    (hbands_8000 : AllZeros_h8000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 9000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 9000 → ρ.re = 1 / 2 := by
  have hγ8000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 8000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 8000 9000
    (AllZeros_h8000.all_nontrivial_zeros_up_to_height_8000_of_bands
      hbands_1000
      hbands_2000
      hbands_3000
      hbands_4000
      hbands_5000
      hbands_6000
      hbands_7000
      hbands_8000
      hγ8000)
    (segment_8000_9000 hbands hγ)

end AllZeros_h9000
