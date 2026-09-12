/-  Height-chain step: all nontrivial zeta zeros up to height 17000 on Re = 1/2 --
    `AllZeros_h16000` + a `[16000, 17000]` SEGMENT certificate (30 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h16000
import RHInBoxT_1d4000000_3999999d4000000_63999d4_16033
import RHInBoxT_1d4000000_3999999d4000000_64131d4_16067
import RHInBoxT_1d4000000_3999999d4000000_16067_64401d4
import RHInBoxT_1d4000000_3999999d4000000_16100_64533d4
import RHInBoxT_1d4000000_3999999d4000000_16133_16167
import RHInBoxT_1d4000000_3999999d4000000_16167_16200
import RHInBoxT_1d4000000_3999999d4000000_16200_16233
import RHInBoxT_1d4000000_3999999d4000000_16233_16267
import RHInBoxT_1d4000000_3999999d4000000_16267_65201d4
import RHInBoxT_1d4000000_3999999d4000000_16300_16333
import RHInBoxT_1d4000000_3999999d4000000_16333_16367
import RHInBoxT_1d4000000_3999999d4000000_16367_16400
import RHInBoxT_1d4000000_3999999d4000000_16400_65733d4
import RHInBoxT_1d4000000_3999999d4000000_16433_16467
import RHInBoxT_1d4000000_3999999d4000000_16467_16500
import RHInBoxT_1d4000000_3999999d4000000_16500_16533
import RHInBoxT_1d4000000_3999999d4000000_16533_16567
import RHInBoxT_1d4000000_3999999d4000000_16567_16600
import RHInBoxT_1d4000000_3999999d4000000_16600_16633
import RHInBoxT_1d4000000_3999999d4000000_16633_16667
import RHInBoxT_1d4000000_3999999d4000000_16667_16700
import RHInBoxT_1d4000000_3999999d4000000_16700_16733
import RHInBoxT_1d4000000_3999999d4000000_16733_16767
import RHInBoxT_1d4000000_3999999d4000000_16767_16800
import RHInBoxT_1d4000000_3999999d4000000_16800_16833
import RHInBoxT_1d4000000_3999999d4000000_16833_16867
import RHInBoxT_1d4000000_3999999d4000000_16867_16900
import RHInBoxT_1d4000000_3999999d4000000_67599d4_16933
import RHInBoxT_1d4000000_3999999d4000000_16933_16967
import RHInBoxT_1d4000000_3999999d4000000_16967_17000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h17000

/-- The 30-band NOMINAL partition of `[16000, 17000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 16000
  | 1 => 16033
  | 2 => 16067
  | 3 => 16100
  | 4 => 16133
  | 5 => 16167
  | 6 => 16200
  | 7 => 16233
  | 8 => 16267
  | 9 => 16300
  | 10 => 16333
  | 11 => 16367
  | 12 => 16400
  | 13 => 16433
  | 14 => 16467
  | 15 => 16500
  | 16 => 16533
  | 17 => 16567
  | 18 => 16600
  | 19 => 16633
  | 20 => 16667
  | 21 => 16700
  | 22 => 16733
  | 23 => 16767
  | 24 => 16800
  | 25 => 16833
  | 26 => 16867
  | 27 => 16900
  | 28 => 16933
  | 29 => 16967
  | 30 => 17000
  | _ => 17000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((16000:ℝ)) ≤ (16033); norm_num
  · show ((16033:ℝ)) ≤ (16067); norm_num
  · show ((16067:ℝ)) ≤ (16100); norm_num
  · show ((16100:ℝ)) ≤ (16133); norm_num
  · show ((16133:ℝ)) ≤ (16167); norm_num
  · show ((16167:ℝ)) ≤ (16200); norm_num
  · show ((16200:ℝ)) ≤ (16233); norm_num
  · show ((16233:ℝ)) ≤ (16267); norm_num
  · show ((16267:ℝ)) ≤ (16300); norm_num
  · show ((16300:ℝ)) ≤ (16333); norm_num
  · show ((16333:ℝ)) ≤ (16367); norm_num
  · show ((16367:ℝ)) ≤ (16400); norm_num
  · show ((16400:ℝ)) ≤ (16433); norm_num
  · show ((16433:ℝ)) ≤ (16467); norm_num
  · show ((16467:ℝ)) ≤ (16500); norm_num
  · show ((16500:ℝ)) ≤ (16533); norm_num
  · show ((16533:ℝ)) ≤ (16567); norm_num
  · show ((16567:ℝ)) ≤ (16600); norm_num
  · show ((16600:ℝ)) ≤ (16633); norm_num
  · show ((16633:ℝ)) ≤ (16667); norm_num
  · show ((16667:ℝ)) ≤ (16700); norm_num
  · show ((16700:ℝ)) ≤ (16733); norm_num
  · show ((16733:ℝ)) ≤ (16767); norm_num
  · show ((16767:ℝ)) ≤ (16800); norm_num
  · show ((16800:ℝ)) ≤ (16833); norm_num
  · show ((16833:ℝ)) ≤ (16867); norm_num
  · show ((16867:ℝ)) ≤ (16900); norm_num
  · show ((16900:ℝ)) ≤ (16933); norm_num
  · show ((16933:ℝ)) ≤ (16967); norm_num
  · show ((16967:ℝ)) ≤ (17000); norm_num
  · show ((17000:ℝ)) ≤ (17000); norm_num
  · exact le_refl _

/-- The lower edges of the 30 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 63999 / 4
  | 1 => 64131 / 4
  | 2 => 16067
  | 3 => 16100
  | 4 => 16133
  | 5 => 16167
  | 6 => 16200
  | 7 => 16233
  | 8 => 16267
  | 9 => 16300
  | 10 => 16333
  | 11 => 16367
  | 12 => 16400
  | 13 => 16433
  | 14 => 16467
  | 15 => 16500
  | 16 => 16533
  | 17 => 16567
  | 18 => 16600
  | 19 => 16633
  | 20 => 16667
  | 21 => 16700
  | 22 => 16733
  | 23 => 16767
  | 24 => 16800
  | 25 => 16833
  | 26 => 16867
  | 27 => 67599 / 4
  | 28 => 16933
  | 29 => 16967
  | _ => 16967

/-- The upper edges of the 30 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 16033
  | 1 => 16067
  | 2 => 64401 / 4
  | 3 => 64533 / 4
  | 4 => 16167
  | 5 => 16200
  | 6 => 16233
  | 7 => 16267
  | 8 => 65201 / 4
  | 9 => 16333
  | 10 => 16367
  | 11 => 16400
  | 12 => 65733 / 4
  | 13 => 16467
  | 14 => 16500
  | 15 => 16533
  | 16 => 16567
  | 17 => 16600
  | 18 => 16633
  | 19 => 16667
  | 20 => 16700
  | 21 => 16733
  | 22 => 16767
  | 23 => 16800
  | 24 => 16833
  | 25 => 16867
  | 26 => 16900
  | 27 => 16933
  | 28 => 16967
  | 29 => 17000
  | _ => 17000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 30 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 17000` (`log 17000 ≤ 10`, `2.7^10 ≥ 17000`). -/
theorem haC_17000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 17000 := by
  have hlog : Real.log 17000 ≤ 10 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h10 : Real.exp 10 = (Real.exp 1) ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 10 ≤ (Real.exp 1) ^ 10 := pow_le_pow_left₀ (by norm_num) he1 10
    rw [h10]; nlinarith [hpow]
  have hpos : 0 < Real.log 17000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 17000
      ≤ (1 / 4000000) * 10 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[16000, 17000]` segment's band hypothesis: every band `i < 30` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 30 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 30 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[16000, 17000]` SEGMENT: every zero with `16000 ≤ Im ≤ 17000` is on the line. -/
theorem segment_16000_17000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 17000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (16000:ℝ) ≤ ρ.im → ρ.im ≤ 17000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 16000 17000 bndSeg 30 (by norm_num) bndSeg_mono rfl rfl haC_17000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 17000 via the HEIGHT CHAIN**: `[0,16000]` ∘ `[16000,17000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_17000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 17000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 17000 → ρ.re = 1 / 2 := by
  have hγ16000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 16000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 16000 17000
    (AllZeros_h16000.all_nontrivial_zeros_up_to_height_16000_of_bands
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
      hγ16000)
    (segment_16000_17000 hbands hγ)

end AllZeros_h17000
