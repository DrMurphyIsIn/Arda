/-  Height-chain step: all nontrivial zeta zeros up to height 19000 on Re = 1/2 --
    `AllZeros_h18000` + a `[18000, 19000]` SEGMENT certificate (31 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h18000
import RHInBoxT_1d4000000_3999999d4000000_18000_18032
import RHInBoxT_1d4000000_3999999d4000000_18032_18065
import RHInBoxT_1d4000000_3999999d4000000_18065_18097
import RHInBoxT_1d4000000_3999999d4000000_18097_18129
import RHInBoxT_1d4000000_3999999d4000000_18129_18161
import RHInBoxT_1d4000000_3999999d4000000_18161_18194
import RHInBoxT_1d4000000_3999999d4000000_18194_72905d4
import RHInBoxT_1d4000000_3999999d4000000_18226_18258
import RHInBoxT_1d4000000_3999999d4000000_18258_18290
import RHInBoxT_1d4000000_3999999d4000000_18290_73293d4
import RHInBoxT_1d4000000_3999999d4000000_18323_73421d4
import RHInBoxT_1d4000000_3999999d4000000_18355_18387
import RHInBoxT_1d4000000_3999999d4000000_73547d4_18419
import RHInBoxT_1d4000000_3999999d4000000_18419_18452
import RHInBoxT_1d4000000_3999999d4000000_18452_18484
import RHInBoxT_1d4000000_3999999d4000000_18484_18516
import RHInBoxT_1d4000000_3999999d4000000_74063d4_18548
import RHInBoxT_1d4000000_3999999d4000000_18548_18581
import RHInBoxT_1d4000000_3999999d4000000_18581_18613
import RHInBoxT_1d4000000_3999999d4000000_18613_74581d4
import RHInBoxT_1d4000000_3999999d4000000_18645_18677
import RHInBoxT_1d4000000_3999999d4000000_74707d4_18710
import RHInBoxT_1d4000000_3999999d4000000_18710_18742
import RHInBoxT_1d4000000_3999999d4000000_18742_18774
import RHInBoxT_1d4000000_3999999d4000000_18774_18806
import RHInBoxT_1d4000000_3999999d4000000_18806_18839
import RHInBoxT_1d4000000_3999999d4000000_18839_75485d4
import RHInBoxT_1d4000000_3999999d4000000_18871_18903
import RHInBoxT_1d4000000_3999999d4000000_18903_18935
import RHInBoxT_1d4000000_3999999d4000000_18935_18968
import RHInBoxT_1d4000000_3999999d4000000_18968_76001d4

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h19000

/-- The 31-band NOMINAL partition of `[18000, 19000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 18000
  | 1 => 18032
  | 2 => 18065
  | 3 => 18097
  | 4 => 18129
  | 5 => 18161
  | 6 => 18194
  | 7 => 18226
  | 8 => 18258
  | 9 => 18290
  | 10 => 18323
  | 11 => 18355
  | 12 => 18387
  | 13 => 18419
  | 14 => 18452
  | 15 => 18484
  | 16 => 18516
  | 17 => 18548
  | 18 => 18581
  | 19 => 18613
  | 20 => 18645
  | 21 => 18677
  | 22 => 18710
  | 23 => 18742
  | 24 => 18774
  | 25 => 18806
  | 26 => 18839
  | 27 => 18871
  | 28 => 18903
  | 29 => 18935
  | 30 => 18968
  | 31 => 19000
  | _ => 19000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((18000:ℝ)) ≤ (18032); norm_num
  · show ((18032:ℝ)) ≤ (18065); norm_num
  · show ((18065:ℝ)) ≤ (18097); norm_num
  · show ((18097:ℝ)) ≤ (18129); norm_num
  · show ((18129:ℝ)) ≤ (18161); norm_num
  · show ((18161:ℝ)) ≤ (18194); norm_num
  · show ((18194:ℝ)) ≤ (18226); norm_num
  · show ((18226:ℝ)) ≤ (18258); norm_num
  · show ((18258:ℝ)) ≤ (18290); norm_num
  · show ((18290:ℝ)) ≤ (18323); norm_num
  · show ((18323:ℝ)) ≤ (18355); norm_num
  · show ((18355:ℝ)) ≤ (18387); norm_num
  · show ((18387:ℝ)) ≤ (18419); norm_num
  · show ((18419:ℝ)) ≤ (18452); norm_num
  · show ((18452:ℝ)) ≤ (18484); norm_num
  · show ((18484:ℝ)) ≤ (18516); norm_num
  · show ((18516:ℝ)) ≤ (18548); norm_num
  · show ((18548:ℝ)) ≤ (18581); norm_num
  · show ((18581:ℝ)) ≤ (18613); norm_num
  · show ((18613:ℝ)) ≤ (18645); norm_num
  · show ((18645:ℝ)) ≤ (18677); norm_num
  · show ((18677:ℝ)) ≤ (18710); norm_num
  · show ((18710:ℝ)) ≤ (18742); norm_num
  · show ((18742:ℝ)) ≤ (18774); norm_num
  · show ((18774:ℝ)) ≤ (18806); norm_num
  · show ((18806:ℝ)) ≤ (18839); norm_num
  · show ((18839:ℝ)) ≤ (18871); norm_num
  · show ((18871:ℝ)) ≤ (18903); norm_num
  · show ((18903:ℝ)) ≤ (18935); norm_num
  · show ((18935:ℝ)) ≤ (18968); norm_num
  · show ((18968:ℝ)) ≤ (19000); norm_num
  · show ((19000:ℝ)) ≤ (19000); norm_num
  · exact le_refl _

/-- The lower edges of the 31 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 18000
  | 1 => 18032
  | 2 => 18065
  | 3 => 18097
  | 4 => 18129
  | 5 => 18161
  | 6 => 18194
  | 7 => 18226
  | 8 => 18258
  | 9 => 18290
  | 10 => 18323
  | 11 => 18355
  | 12 => 73547 / 4
  | 13 => 18419
  | 14 => 18452
  | 15 => 18484
  | 16 => 74063 / 4
  | 17 => 18548
  | 18 => 18581
  | 19 => 18613
  | 20 => 18645
  | 21 => 74707 / 4
  | 22 => 18710
  | 23 => 18742
  | 24 => 18774
  | 25 => 18806
  | 26 => 18839
  | 27 => 18871
  | 28 => 18903
  | 29 => 18935
  | 30 => 18968
  | _ => 18968

/-- The upper edges of the 31 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 18032
  | 1 => 18065
  | 2 => 18097
  | 3 => 18129
  | 4 => 18161
  | 5 => 18194
  | 6 => 72905 / 4
  | 7 => 18258
  | 8 => 18290
  | 9 => 73293 / 4
  | 10 => 73421 / 4
  | 11 => 18387
  | 12 => 18419
  | 13 => 18452
  | 14 => 18484
  | 15 => 18516
  | 16 => 18548
  | 17 => 18581
  | 18 => 18613
  | 19 => 74581 / 4
  | 20 => 18677
  | 21 => 18710
  | 22 => 18742
  | 23 => 18774
  | 24 => 18806
  | 25 => 18839
  | 26 => 75485 / 4
  | 27 => 18903
  | 28 => 18935
  | 29 => 18968
  | 30 => 76001 / 4
  | _ => 76001 / 4

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 31 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 19000` (`log 19000 ≤ 10`, `2.7^10 ≥ 19000`). -/
theorem haC_19000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 19000 := by
  have hlog : Real.log 19000 ≤ 10 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h10 : Real.exp 10 = (Real.exp 1) ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 10 ≤ (Real.exp 1) ^ 10 := pow_le_pow_left₀ (by norm_num) he1 10
    rw [h10]; nlinarith [hpow]
  have hpos : 0 < Real.log 19000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 19000
      ≤ (1 / 4000000) * 10 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[18000, 19000]` segment's band hypothesis: every band `i < 31` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 31 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 31 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[18000, 19000]` SEGMENT: every zero with `18000 ≤ Im ≤ 19000` is on the line. -/
theorem segment_18000_19000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 19000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (18000:ℝ) ≤ ρ.im → ρ.im ≤ 19000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 18000 19000 bndSeg 31 (by norm_num) bndSeg_mono rfl rfl haC_19000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 19000 via the HEIGHT CHAIN**: `[0,18000]` ∘ `[18000,19000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_19000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 19000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 19000 → ρ.re = 1 / 2 := by
  have hγ18000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 18000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 18000 19000
    (AllZeros_h18000.all_nontrivial_zeros_up_to_height_18000_of_bands
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
      hγ18000)
    (segment_18000_19000 hbands hγ)

end AllZeros_h19000
