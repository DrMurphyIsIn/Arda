/-  Height-chain step: all nontrivial zeta zeros up to height 21000 on Re = 1/2 --
    `AllZeros_h20000` + a `[20000, 21000]` SEGMENT certificate (31 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h20000
import RHInBoxT_1d4000000_3999999d4000000_20000_20032
import RHInBoxT_1d4000000_3999999d4000000_20032_20065
import RHInBoxT_1d4000000_3999999d4000000_20065_20097
import RHInBoxT_1d4000000_3999999d4000000_20097_20129
import RHInBoxT_1d4000000_3999999d4000000_20129_20161
import RHInBoxT_1d4000000_3999999d4000000_20161_20194
import RHInBoxT_1d4000000_3999999d4000000_20194_20226
import RHInBoxT_1d4000000_3999999d4000000_80903d4_20258
import RHInBoxT_1d4000000_3999999d4000000_20258_20290
import RHInBoxT_1d4000000_3999999d4000000_20290_20323
import RHInBoxT_1d4000000_3999999d4000000_81291d4_20355
import RHInBoxT_1d4000000_3999999d4000000_20355_20387
import RHInBoxT_1d4000000_3999999d4000000_20387_20419
import RHInBoxT_1d4000000_3999999d4000000_20419_20452
import RHInBoxT_1d4000000_3999999d4000000_20452_20484
import RHInBoxT_1d4000000_3999999d4000000_20484_20516
import RHInBoxT_1d4000000_3999999d4000000_20516_20548
import RHInBoxT_1d4000000_3999999d4000000_20548_20581
import RHInBoxT_1d4000000_3999999d4000000_20581_20613
import RHInBoxT_1d4000000_3999999d4000000_20613_20645
import RHInBoxT_1d4000000_3999999d4000000_20645_20677
import RHInBoxT_1d4000000_3999999d4000000_20677_20710
import RHInBoxT_1d4000000_3999999d4000000_20710_20742
import RHInBoxT_1d4000000_3999999d4000000_20742_20774
import RHInBoxT_1d4000000_3999999d4000000_83095d4_83225d4
import RHInBoxT_1d4000000_3999999d4000000_20806_20839
import RHInBoxT_1d4000000_3999999d4000000_20839_20871
import RHInBoxT_1d4000000_3999999d4000000_20871_20903
import RHInBoxT_1d4000000_3999999d4000000_20903_20935
import RHInBoxT_1d4000000_3999999d4000000_20935_83873d4
import RHInBoxT_1d4000000_3999999d4000000_20968_21000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h21000

/-- The 31-band NOMINAL partition of `[20000, 21000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 20000
  | 1 => 20032
  | 2 => 20065
  | 3 => 20097
  | 4 => 20129
  | 5 => 20161
  | 6 => 20194
  | 7 => 20226
  | 8 => 20258
  | 9 => 20290
  | 10 => 20323
  | 11 => 20355
  | 12 => 20387
  | 13 => 20419
  | 14 => 20452
  | 15 => 20484
  | 16 => 20516
  | 17 => 20548
  | 18 => 20581
  | 19 => 20613
  | 20 => 20645
  | 21 => 20677
  | 22 => 20710
  | 23 => 20742
  | 24 => 20774
  | 25 => 20806
  | 26 => 20839
  | 27 => 20871
  | 28 => 20903
  | 29 => 20935
  | 30 => 20968
  | 31 => 21000
  | _ => 21000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((20000:ℝ)) ≤ (20032); norm_num
  · show ((20032:ℝ)) ≤ (20065); norm_num
  · show ((20065:ℝ)) ≤ (20097); norm_num
  · show ((20097:ℝ)) ≤ (20129); norm_num
  · show ((20129:ℝ)) ≤ (20161); norm_num
  · show ((20161:ℝ)) ≤ (20194); norm_num
  · show ((20194:ℝ)) ≤ (20226); norm_num
  · show ((20226:ℝ)) ≤ (20258); norm_num
  · show ((20258:ℝ)) ≤ (20290); norm_num
  · show ((20290:ℝ)) ≤ (20323); norm_num
  · show ((20323:ℝ)) ≤ (20355); norm_num
  · show ((20355:ℝ)) ≤ (20387); norm_num
  · show ((20387:ℝ)) ≤ (20419); norm_num
  · show ((20419:ℝ)) ≤ (20452); norm_num
  · show ((20452:ℝ)) ≤ (20484); norm_num
  · show ((20484:ℝ)) ≤ (20516); norm_num
  · show ((20516:ℝ)) ≤ (20548); norm_num
  · show ((20548:ℝ)) ≤ (20581); norm_num
  · show ((20581:ℝ)) ≤ (20613); norm_num
  · show ((20613:ℝ)) ≤ (20645); norm_num
  · show ((20645:ℝ)) ≤ (20677); norm_num
  · show ((20677:ℝ)) ≤ (20710); norm_num
  · show ((20710:ℝ)) ≤ (20742); norm_num
  · show ((20742:ℝ)) ≤ (20774); norm_num
  · show ((20774:ℝ)) ≤ (20806); norm_num
  · show ((20806:ℝ)) ≤ (20839); norm_num
  · show ((20839:ℝ)) ≤ (20871); norm_num
  · show ((20871:ℝ)) ≤ (20903); norm_num
  · show ((20903:ℝ)) ≤ (20935); norm_num
  · show ((20935:ℝ)) ≤ (20968); norm_num
  · show ((20968:ℝ)) ≤ (21000); norm_num
  · show ((21000:ℝ)) ≤ (21000); norm_num
  · exact le_refl _

/-- The lower edges of the 31 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 20000
  | 1 => 20032
  | 2 => 20065
  | 3 => 20097
  | 4 => 20129
  | 5 => 20161
  | 6 => 20194
  | 7 => 80903 / 4
  | 8 => 20258
  | 9 => 20290
  | 10 => 81291 / 4
  | 11 => 20355
  | 12 => 20387
  | 13 => 20419
  | 14 => 20452
  | 15 => 20484
  | 16 => 20516
  | 17 => 20548
  | 18 => 20581
  | 19 => 20613
  | 20 => 20645
  | 21 => 20677
  | 22 => 20710
  | 23 => 20742
  | 24 => 83095 / 4
  | 25 => 20806
  | 26 => 20839
  | 27 => 20871
  | 28 => 20903
  | 29 => 20935
  | 30 => 20968
  | _ => 20968

/-- The upper edges of the 31 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 20032
  | 1 => 20065
  | 2 => 20097
  | 3 => 20129
  | 4 => 20161
  | 5 => 20194
  | 6 => 20226
  | 7 => 20258
  | 8 => 20290
  | 9 => 20323
  | 10 => 20355
  | 11 => 20387
  | 12 => 20419
  | 13 => 20452
  | 14 => 20484
  | 15 => 20516
  | 16 => 20548
  | 17 => 20581
  | 18 => 20613
  | 19 => 20645
  | 20 => 20677
  | 21 => 20710
  | 22 => 20742
  | 23 => 20774
  | 24 => 83225 / 4
  | 25 => 20839
  | 26 => 20871
  | 27 => 20903
  | 28 => 20935
  | 29 => 83873 / 4
  | 30 => 21000
  | _ => 21000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 31 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 21000` (`log 21000 ≤ 11`, `2.7^11 ≥ 21000`). -/
theorem haC_21000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 21000 := by
  have hlog : Real.log 21000 ≤ 11 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h11 : Real.exp 11 = (Real.exp 1) ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 11 ≤ (Real.exp 1) ^ 11 := pow_le_pow_left₀ (by norm_num) he1 11
    rw [h11]; nlinarith [hpow]
  have hpos : 0 < Real.log 21000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 21000
      ≤ (1 / 4000000) * 11 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[20000, 21000]` segment's band hypothesis: every band `i < 31` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 31 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 31 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[20000, 21000]` SEGMENT: every zero with `20000 ≤ Im ≤ 21000` is on the line. -/
theorem segment_20000_21000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 21000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (20000:ℝ) ≤ ρ.im → ρ.im ≤ 21000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 20000 21000 bndSeg 31 (by norm_num) bndSeg_mono rfl rfl haC_21000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 21000 via the HEIGHT CHAIN**: `[0,20000]` ∘ `[20000,21000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_21000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 21000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 21000 → ρ.re = 1 / 2 := by
  have hγ20000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 20000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 20000 21000
    (AllZeros_h20000.all_nontrivial_zeros_up_to_height_20000_of_bands
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
      hγ20000)
    (segment_20000_21000 hbands hγ)

end AllZeros_h21000
