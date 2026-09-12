/-  Height-chain step: all nontrivial zeta zeros up to height 20000 on Re = 1/2 --
    `AllZeros_h19000` + a `[19000, 20000]` SEGMENT certificate (31 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h19000
import RHInBoxT_1d4000000_3999999d4000000_19000_19032
import RHInBoxT_1d4000000_3999999d4000000_19032_19065
import RHInBoxT_1d4000000_3999999d4000000_19065_19097
import RHInBoxT_1d4000000_3999999d4000000_76387d4_76517d4
import RHInBoxT_1d4000000_3999999d4000000_19129_19161
import RHInBoxT_1d4000000_3999999d4000000_19161_19194
import RHInBoxT_1d4000000_3999999d4000000_19194_19226
import RHInBoxT_1d4000000_3999999d4000000_76903d4_19258
import RHInBoxT_1d4000000_3999999d4000000_19258_19290
import RHInBoxT_1d4000000_3999999d4000000_19290_77293d4
import RHInBoxT_1d4000000_3999999d4000000_19323_77421d4
import RHInBoxT_1d4000000_3999999d4000000_19355_19387
import RHInBoxT_1d4000000_3999999d4000000_19387_19419
import RHInBoxT_1d4000000_3999999d4000000_19419_77809d4
import RHInBoxT_1d4000000_3999999d4000000_19452_19484
import RHInBoxT_1d4000000_3999999d4000000_77935d4_19516
import RHInBoxT_1d4000000_3999999d4000000_19516_19548
import RHInBoxT_1d4000000_3999999d4000000_19548_19581
import RHInBoxT_1d4000000_3999999d4000000_19581_19613
import RHInBoxT_1d4000000_3999999d4000000_19613_19645
import RHInBoxT_1d4000000_3999999d4000000_19645_78709d4
import RHInBoxT_1d4000000_3999999d4000000_19677_19710
import RHInBoxT_1d4000000_3999999d4000000_19710_19742
import RHInBoxT_1d4000000_3999999d4000000_19742_19774
import RHInBoxT_1d4000000_3999999d4000000_19774_19806
import RHInBoxT_1d4000000_3999999d4000000_79223d4_19839
import RHInBoxT_1d4000000_3999999d4000000_19839_19871
import RHInBoxT_1d4000000_3999999d4000000_79483d4_19903
import RHInBoxT_1d4000000_3999999d4000000_19903_19935
import RHInBoxT_1d4000000_3999999d4000000_19935_19968
import RHInBoxT_1d4000000_3999999d4000000_79871d4_20000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h20000

/-- The 31-band NOMINAL partition of `[19000, 20000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 19000
  | 1 => 19032
  | 2 => 19065
  | 3 => 19097
  | 4 => 19129
  | 5 => 19161
  | 6 => 19194
  | 7 => 19226
  | 8 => 19258
  | 9 => 19290
  | 10 => 19323
  | 11 => 19355
  | 12 => 19387
  | 13 => 19419
  | 14 => 19452
  | 15 => 19484
  | 16 => 19516
  | 17 => 19548
  | 18 => 19581
  | 19 => 19613
  | 20 => 19645
  | 21 => 19677
  | 22 => 19710
  | 23 => 19742
  | 24 => 19774
  | 25 => 19806
  | 26 => 19839
  | 27 => 19871
  | 28 => 19903
  | 29 => 19935
  | 30 => 19968
  | 31 => 20000
  | _ => 20000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((19000:ℝ)) ≤ (19032); norm_num
  · show ((19032:ℝ)) ≤ (19065); norm_num
  · show ((19065:ℝ)) ≤ (19097); norm_num
  · show ((19097:ℝ)) ≤ (19129); norm_num
  · show ((19129:ℝ)) ≤ (19161); norm_num
  · show ((19161:ℝ)) ≤ (19194); norm_num
  · show ((19194:ℝ)) ≤ (19226); norm_num
  · show ((19226:ℝ)) ≤ (19258); norm_num
  · show ((19258:ℝ)) ≤ (19290); norm_num
  · show ((19290:ℝ)) ≤ (19323); norm_num
  · show ((19323:ℝ)) ≤ (19355); norm_num
  · show ((19355:ℝ)) ≤ (19387); norm_num
  · show ((19387:ℝ)) ≤ (19419); norm_num
  · show ((19419:ℝ)) ≤ (19452); norm_num
  · show ((19452:ℝ)) ≤ (19484); norm_num
  · show ((19484:ℝ)) ≤ (19516); norm_num
  · show ((19516:ℝ)) ≤ (19548); norm_num
  · show ((19548:ℝ)) ≤ (19581); norm_num
  · show ((19581:ℝ)) ≤ (19613); norm_num
  · show ((19613:ℝ)) ≤ (19645); norm_num
  · show ((19645:ℝ)) ≤ (19677); norm_num
  · show ((19677:ℝ)) ≤ (19710); norm_num
  · show ((19710:ℝ)) ≤ (19742); norm_num
  · show ((19742:ℝ)) ≤ (19774); norm_num
  · show ((19774:ℝ)) ≤ (19806); norm_num
  · show ((19806:ℝ)) ≤ (19839); norm_num
  · show ((19839:ℝ)) ≤ (19871); norm_num
  · show ((19871:ℝ)) ≤ (19903); norm_num
  · show ((19903:ℝ)) ≤ (19935); norm_num
  · show ((19935:ℝ)) ≤ (19968); norm_num
  · show ((19968:ℝ)) ≤ (20000); norm_num
  · show ((20000:ℝ)) ≤ (20000); norm_num
  · exact le_refl _

/-- The lower edges of the 31 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 19000
  | 1 => 19032
  | 2 => 19065
  | 3 => 76387 / 4
  | 4 => 19129
  | 5 => 19161
  | 6 => 19194
  | 7 => 76903 / 4
  | 8 => 19258
  | 9 => 19290
  | 10 => 19323
  | 11 => 19355
  | 12 => 19387
  | 13 => 19419
  | 14 => 19452
  | 15 => 77935 / 4
  | 16 => 19516
  | 17 => 19548
  | 18 => 19581
  | 19 => 19613
  | 20 => 19645
  | 21 => 19677
  | 22 => 19710
  | 23 => 19742
  | 24 => 19774
  | 25 => 79223 / 4
  | 26 => 19839
  | 27 => 79483 / 4
  | 28 => 19903
  | 29 => 19935
  | 30 => 79871 / 4
  | _ => 79871 / 4

/-- The upper edges of the 31 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 19032
  | 1 => 19065
  | 2 => 19097
  | 3 => 76517 / 4
  | 4 => 19161
  | 5 => 19194
  | 6 => 19226
  | 7 => 19258
  | 8 => 19290
  | 9 => 77293 / 4
  | 10 => 77421 / 4
  | 11 => 19387
  | 12 => 19419
  | 13 => 77809 / 4
  | 14 => 19484
  | 15 => 19516
  | 16 => 19548
  | 17 => 19581
  | 18 => 19613
  | 19 => 19645
  | 20 => 78709 / 4
  | 21 => 19710
  | 22 => 19742
  | 23 => 19774
  | 24 => 19806
  | 25 => 19839
  | 26 => 19871
  | 27 => 19903
  | 28 => 19935
  | 29 => 19968
  | 30 => 20000
  | _ => 20000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 31 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 20000` (`log 20000 ≤ 10`, `2.7^10 ≥ 20000`). -/
theorem haC_20000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 20000 := by
  have hlog : Real.log 20000 ≤ 10 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h10 : Real.exp 10 = (Real.exp 1) ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 10 ≤ (Real.exp 1) ^ 10 := pow_le_pow_left₀ (by norm_num) he1 10
    rw [h10]; nlinarith [hpow]
  have hpos : 0 < Real.log 20000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 20000
      ≤ (1 / 4000000) * 10 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[19000, 20000]` segment's band hypothesis: every band `i < 31` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 31 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 31 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[19000, 20000]` SEGMENT: every zero with `19000 ≤ Im ≤ 20000` is on the line. -/
theorem segment_19000_20000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 20000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (19000:ℝ) ≤ ρ.im → ρ.im ≤ 20000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 19000 20000 bndSeg 31 (by norm_num) bndSeg_mono rfl rfl haC_20000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 20000 via the HEIGHT CHAIN**: `[0,19000]` ∘ `[19000,20000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_20000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 20000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 20000 → ρ.re = 1 / 2 := by
  have hγ19000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 19000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 19000 20000
    (AllZeros_h19000.all_nontrivial_zeros_up_to_height_19000_of_bands
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
      hγ19000)
    (segment_19000_20000 hbands hγ)

end AllZeros_h20000
