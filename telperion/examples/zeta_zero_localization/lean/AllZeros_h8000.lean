/-  Height-chain step: all nontrivial zeta zeros up to height 8000 on Re = 1/2 --
    `AllZeros_h7000` + a `[7000, 8000]` SEGMENT certificate (27 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h7000
import RHInBoxT_1d4000000_3999999d4000000_7000_7037
import RHInBoxT_1d4000000_3999999d4000000_7037_7074
import RHInBoxT_1d4000000_3999999d4000000_7074_7111
import RHInBoxT_1d4000000_3999999d4000000_7111_7148
import RHInBoxT_1d4000000_3999999d4000000_7148_7185
import RHInBoxT_1d4000000_3999999d4000000_7185_7222
import RHInBoxT_1d4000000_3999999d4000000_7222_7259
import RHInBoxT_1d4000000_3999999d4000000_7259_7296
import RHInBoxT_1d4000000_3999999d4000000_7296_7333
import RHInBoxT_1d4000000_3999999d4000000_7333_7370
import RHInBoxT_1d4000000_3999999d4000000_7370_7407
import RHInBoxT_1d4000000_3999999d4000000_7407_7444
import RHInBoxT_1d4000000_3999999d4000000_7444_7481
import RHInBoxT_1d4000000_3999999d4000000_7481_7519
import RHInBoxT_1d4000000_3999999d4000000_30075d4_7556
import RHInBoxT_1d4000000_3999999d4000000_7556_7593
import RHInBoxT_1d4000000_3999999d4000000_7593_7630
import RHInBoxT_1d4000000_3999999d4000000_7630_7667
import RHInBoxT_1d4000000_3999999d4000000_7667_7704
import RHInBoxT_1d4000000_3999999d4000000_7704_7741
import RHInBoxT_1d4000000_3999999d4000000_30963d4_7778
import RHInBoxT_1d4000000_3999999d4000000_7778_7815
import RHInBoxT_1d4000000_3999999d4000000_7815_31409d4
import RHInBoxT_1d4000000_3999999d4000000_7852_7889
import RHInBoxT_1d4000000_3999999d4000000_7889_31705d4
import RHInBoxT_1d4000000_3999999d4000000_7926_7963
import RHInBoxT_1d4000000_3999999d4000000_31851d4_8000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h8000

/-- The 27-band NOMINAL partition of `[7000, 8000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 7000
  | 1 => 7037
  | 2 => 7074
  | 3 => 7111
  | 4 => 7148
  | 5 => 7185
  | 6 => 7222
  | 7 => 7259
  | 8 => 7296
  | 9 => 7333
  | 10 => 7370
  | 11 => 7407
  | 12 => 7444
  | 13 => 7481
  | 14 => 7519
  | 15 => 7556
  | 16 => 7593
  | 17 => 7630
  | 18 => 7667
  | 19 => 7704
  | 20 => 7741
  | 21 => 7778
  | 22 => 7815
  | 23 => 7852
  | 24 => 7889
  | 25 => 7926
  | 26 => 7963
  | 27 => 8000
  | _ => 8000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((7000:ℝ)) ≤ (7037); norm_num
  · show ((7037:ℝ)) ≤ (7074); norm_num
  · show ((7074:ℝ)) ≤ (7111); norm_num
  · show ((7111:ℝ)) ≤ (7148); norm_num
  · show ((7148:ℝ)) ≤ (7185); norm_num
  · show ((7185:ℝ)) ≤ (7222); norm_num
  · show ((7222:ℝ)) ≤ (7259); norm_num
  · show ((7259:ℝ)) ≤ (7296); norm_num
  · show ((7296:ℝ)) ≤ (7333); norm_num
  · show ((7333:ℝ)) ≤ (7370); norm_num
  · show ((7370:ℝ)) ≤ (7407); norm_num
  · show ((7407:ℝ)) ≤ (7444); norm_num
  · show ((7444:ℝ)) ≤ (7481); norm_num
  · show ((7481:ℝ)) ≤ (7519); norm_num
  · show ((7519:ℝ)) ≤ (7556); norm_num
  · show ((7556:ℝ)) ≤ (7593); norm_num
  · show ((7593:ℝ)) ≤ (7630); norm_num
  · show ((7630:ℝ)) ≤ (7667); norm_num
  · show ((7667:ℝ)) ≤ (7704); norm_num
  · show ((7704:ℝ)) ≤ (7741); norm_num
  · show ((7741:ℝ)) ≤ (7778); norm_num
  · show ((7778:ℝ)) ≤ (7815); norm_num
  · show ((7815:ℝ)) ≤ (7852); norm_num
  · show ((7852:ℝ)) ≤ (7889); norm_num
  · show ((7889:ℝ)) ≤ (7926); norm_num
  · show ((7926:ℝ)) ≤ (7963); norm_num
  · show ((7963:ℝ)) ≤ (8000); norm_num
  · show ((8000:ℝ)) ≤ (8000); norm_num
  · exact le_refl _

/-- The lower edges of the 27 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 7000
  | 1 => 7037
  | 2 => 7074
  | 3 => 7111
  | 4 => 7148
  | 5 => 7185
  | 6 => 7222
  | 7 => 7259
  | 8 => 7296
  | 9 => 7333
  | 10 => 7370
  | 11 => 7407
  | 12 => 7444
  | 13 => 7481
  | 14 => 30075 / 4
  | 15 => 7556
  | 16 => 7593
  | 17 => 7630
  | 18 => 7667
  | 19 => 7704
  | 20 => 30963 / 4
  | 21 => 7778
  | 22 => 7815
  | 23 => 7852
  | 24 => 7889
  | 25 => 7926
  | 26 => 31851 / 4
  | _ => 31851 / 4

/-- The upper edges of the 27 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 7037
  | 1 => 7074
  | 2 => 7111
  | 3 => 7148
  | 4 => 7185
  | 5 => 7222
  | 6 => 7259
  | 7 => 7296
  | 8 => 7333
  | 9 => 7370
  | 10 => 7407
  | 11 => 7444
  | 12 => 7481
  | 13 => 7519
  | 14 => 7556
  | 15 => 7593
  | 16 => 7630
  | 17 => 7667
  | 18 => 7704
  | 19 => 7741
  | 20 => 7778
  | 21 => 7815
  | 22 => 31409 / 4
  | 23 => 7889
  | 24 => 31705 / 4
  | 25 => 7963
  | 26 => 8000
  | _ => 8000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 27 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 8000` (`log 8000 ≤ 10`, `2.7^10 ≥ 8000`). -/
theorem haC_8000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 8000 := by
  have hlog : Real.log 8000 ≤ 10 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h10 : Real.exp 10 = (Real.exp 1) ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 10 ≤ (Real.exp 1) ^ 10 := pow_le_pow_left₀ (by norm_num) he1 10
    rw [h10]; nlinarith [hpow]
  have hpos : 0 < Real.log 8000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 8000
      ≤ (1 / 4000000) * 10 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[7000, 8000]` segment's band hypothesis: every band `i < 27` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 27 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 27 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[7000, 8000]` SEGMENT: every zero with `7000 ≤ Im ≤ 8000` is on the line. -/
theorem segment_7000_8000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 8000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (7000:ℝ) ≤ ρ.im → ρ.im ≤ 8000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 7000 8000 bndSeg 27 (by norm_num) bndSeg_mono rfl rfl haC_8000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 8000 via the HEIGHT CHAIN**: `[0,7000]` ∘ `[7000,8000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_8000_of_bands
    (hbands_1000 : AllZeros_h1000.BandHyp)
    (hbands_2000 : AllZeros_h2000.BandHyp)
    (hbands_3000 : AllZeros_h3000.BandHyp)
    (hbands_4000 : AllZeros_h4000.BandHyp)
    (hbands_5000 : AllZeros_h5000.BandHyp)
    (hbands_6000 : AllZeros_h6000.BandHyp)
    (hbands_7000 : AllZeros_h7000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 8000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 8000 → ρ.re = 1 / 2 := by
  have hγ7000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 7000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 7000 8000
    (AllZeros_h7000.all_nontrivial_zeros_up_to_height_7000_of_bands
      hbands_1000
      hbands_2000
      hbands_3000
      hbands_4000
      hbands_5000
      hbands_6000
      hbands_7000
      hγ7000)
    (segment_7000_8000 hbands hγ)

end AllZeros_h8000
