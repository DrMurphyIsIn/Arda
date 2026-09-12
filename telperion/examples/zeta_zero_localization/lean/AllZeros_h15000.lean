/-  Height-chain step: all nontrivial zeta zeros up to height 15000 on Re = 1/2 --
    `AllZeros_h14000` + a `[14000, 15000]` SEGMENT certificate (29 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h14000
import RHInBoxT_1d4000000_3999999d4000000_14000_14034
import RHInBoxT_1d4000000_3999999d4000000_14034_14069
import RHInBoxT_1d4000000_3999999d4000000_14069_14103
import RHInBoxT_1d4000000_3999999d4000000_14103_14138
import RHInBoxT_1d4000000_3999999d4000000_14138_14172
import RHInBoxT_1d4000000_3999999d4000000_14172_14207
import RHInBoxT_1d4000000_3999999d4000000_56827d4_14241
import RHInBoxT_1d4000000_3999999d4000000_56963d4_14276
import RHInBoxT_1d4000000_3999999d4000000_14276_14310
import RHInBoxT_1d4000000_3999999d4000000_57239d4_57381d4
import RHInBoxT_1d4000000_3999999d4000000_14345_14379
import RHInBoxT_1d4000000_3999999d4000000_14379_14414
import RHInBoxT_1d4000000_3999999d4000000_14414_14448
import RHInBoxT_1d4000000_3999999d4000000_57791d4_14483
import RHInBoxT_1d4000000_3999999d4000000_14483_14517
import RHInBoxT_1d4000000_3999999d4000000_14517_58209d4
import RHInBoxT_1d4000000_3999999d4000000_14552_14586
import RHInBoxT_1d4000000_3999999d4000000_14586_14621
import RHInBoxT_1d4000000_3999999d4000000_14621_14655
import RHInBoxT_1d4000000_3999999d4000000_14655_14690
import RHInBoxT_1d4000000_3999999d4000000_14690_58897d4
import RHInBoxT_1d4000000_3999999d4000000_14724_14759
import RHInBoxT_1d4000000_3999999d4000000_14759_14793
import RHInBoxT_1d4000000_3999999d4000000_14793_14828
import RHInBoxT_1d4000000_3999999d4000000_14828_14862
import RHInBoxT_1d4000000_3999999d4000000_14862_14897
import RHInBoxT_1d4000000_3999999d4000000_59587d4_59725d4
import RHInBoxT_1d4000000_3999999d4000000_14931_14966
import RHInBoxT_1d4000000_3999999d4000000_14966_60001d4

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h15000

/-- The 29-band NOMINAL partition of `[14000, 15000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 14000
  | 1 => 14034
  | 2 => 14069
  | 3 => 14103
  | 4 => 14138
  | 5 => 14172
  | 6 => 14207
  | 7 => 14241
  | 8 => 14276
  | 9 => 14310
  | 10 => 14345
  | 11 => 14379
  | 12 => 14414
  | 13 => 14448
  | 14 => 14483
  | 15 => 14517
  | 16 => 14552
  | 17 => 14586
  | 18 => 14621
  | 19 => 14655
  | 20 => 14690
  | 21 => 14724
  | 22 => 14759
  | 23 => 14793
  | 24 => 14828
  | 25 => 14862
  | 26 => 14897
  | 27 => 14931
  | 28 => 14966
  | 29 => 15000
  | _ => 15000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((14000:ℝ)) ≤ (14034); norm_num
  · show ((14034:ℝ)) ≤ (14069); norm_num
  · show ((14069:ℝ)) ≤ (14103); norm_num
  · show ((14103:ℝ)) ≤ (14138); norm_num
  · show ((14138:ℝ)) ≤ (14172); norm_num
  · show ((14172:ℝ)) ≤ (14207); norm_num
  · show ((14207:ℝ)) ≤ (14241); norm_num
  · show ((14241:ℝ)) ≤ (14276); norm_num
  · show ((14276:ℝ)) ≤ (14310); norm_num
  · show ((14310:ℝ)) ≤ (14345); norm_num
  · show ((14345:ℝ)) ≤ (14379); norm_num
  · show ((14379:ℝ)) ≤ (14414); norm_num
  · show ((14414:ℝ)) ≤ (14448); norm_num
  · show ((14448:ℝ)) ≤ (14483); norm_num
  · show ((14483:ℝ)) ≤ (14517); norm_num
  · show ((14517:ℝ)) ≤ (14552); norm_num
  · show ((14552:ℝ)) ≤ (14586); norm_num
  · show ((14586:ℝ)) ≤ (14621); norm_num
  · show ((14621:ℝ)) ≤ (14655); norm_num
  · show ((14655:ℝ)) ≤ (14690); norm_num
  · show ((14690:ℝ)) ≤ (14724); norm_num
  · show ((14724:ℝ)) ≤ (14759); norm_num
  · show ((14759:ℝ)) ≤ (14793); norm_num
  · show ((14793:ℝ)) ≤ (14828); norm_num
  · show ((14828:ℝ)) ≤ (14862); norm_num
  · show ((14862:ℝ)) ≤ (14897); norm_num
  · show ((14897:ℝ)) ≤ (14931); norm_num
  · show ((14931:ℝ)) ≤ (14966); norm_num
  · show ((14966:ℝ)) ≤ (15000); norm_num
  · show ((15000:ℝ)) ≤ (15000); norm_num
  · exact le_refl _

/-- The lower edges of the 29 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 14000
  | 1 => 14034
  | 2 => 14069
  | 3 => 14103
  | 4 => 14138
  | 5 => 14172
  | 6 => 56827 / 4
  | 7 => 56963 / 4
  | 8 => 14276
  | 9 => 57239 / 4
  | 10 => 14345
  | 11 => 14379
  | 12 => 14414
  | 13 => 57791 / 4
  | 14 => 14483
  | 15 => 14517
  | 16 => 14552
  | 17 => 14586
  | 18 => 14621
  | 19 => 14655
  | 20 => 14690
  | 21 => 14724
  | 22 => 14759
  | 23 => 14793
  | 24 => 14828
  | 25 => 14862
  | 26 => 59587 / 4
  | 27 => 14931
  | 28 => 14966
  | _ => 14966

/-- The upper edges of the 29 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 14034
  | 1 => 14069
  | 2 => 14103
  | 3 => 14138
  | 4 => 14172
  | 5 => 14207
  | 6 => 14241
  | 7 => 14276
  | 8 => 14310
  | 9 => 57381 / 4
  | 10 => 14379
  | 11 => 14414
  | 12 => 14448
  | 13 => 14483
  | 14 => 14517
  | 15 => 58209 / 4
  | 16 => 14586
  | 17 => 14621
  | 18 => 14655
  | 19 => 14690
  | 20 => 58897 / 4
  | 21 => 14759
  | 22 => 14793
  | 23 => 14828
  | 24 => 14862
  | 25 => 14897
  | 26 => 59725 / 4
  | 27 => 14966
  | 28 => 60001 / 4
  | _ => 60001 / 4

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 29 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 15000` (`log 15000 ≤ 10`, `2.7^10 ≥ 15000`). -/
theorem haC_15000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 15000 := by
  have hlog : Real.log 15000 ≤ 10 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h10 : Real.exp 10 = (Real.exp 1) ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 10 ≤ (Real.exp 1) ^ 10 := pow_le_pow_left₀ (by norm_num) he1 10
    rw [h10]; nlinarith [hpow]
  have hpos : 0 < Real.log 15000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 15000
      ≤ (1 / 4000000) * 10 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[14000, 15000]` segment's band hypothesis: every band `i < 29` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 29 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 29 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[14000, 15000]` SEGMENT: every zero with `14000 ≤ Im ≤ 15000` is on the line. -/
theorem segment_14000_15000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 15000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (14000:ℝ) ≤ ρ.im → ρ.im ≤ 15000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 14000 15000 bndSeg 29 (by norm_num) bndSeg_mono rfl rfl haC_15000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 15000 via the HEIGHT CHAIN**: `[0,14000]` ∘ `[14000,15000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_15000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 15000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 15000 → ρ.re = 1 / 2 := by
  have hγ14000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 14000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 14000 15000
    (AllZeros_h14000.all_nontrivial_zeros_up_to_height_14000_of_bands
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
      hγ14000)
    (segment_14000_15000 hbands hγ)

end AllZeros_h15000
