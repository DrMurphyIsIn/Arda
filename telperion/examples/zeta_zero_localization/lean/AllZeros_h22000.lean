/-  Height-chain step: all nontrivial zeta zeros up to height 22000 on Re = 1/2 --
    `AllZeros_h21000` + a `[21000, 22000]` SEGMENT certificate (31 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h21000
import RHInBoxT_1d4000000_3999999d4000000_21000_84129d4
import RHInBoxT_1d4000000_3999999d4000000_21032_21065
import RHInBoxT_1d4000000_3999999d4000000_21065_21097
import RHInBoxT_1d4000000_3999999d4000000_21097_21129
import RHInBoxT_1d4000000_3999999d4000000_21129_21161
import RHInBoxT_1d4000000_3999999d4000000_21161_21194
import RHInBoxT_1d4000000_3999999d4000000_21194_21226
import RHInBoxT_1d4000000_3999999d4000000_21226_21258
import RHInBoxT_1d4000000_3999999d4000000_21258_21290
import RHInBoxT_1d4000000_3999999d4000000_21290_21323
import RHInBoxT_1d4000000_3999999d4000000_21323_21355
import RHInBoxT_1d4000000_3999999d4000000_85419d4_85549d4
import RHInBoxT_1d4000000_3999999d4000000_21387_21419
import RHInBoxT_1d4000000_3999999d4000000_21419_21452
import RHInBoxT_1d4000000_3999999d4000000_21452_21484
import RHInBoxT_1d4000000_3999999d4000000_21484_21516
import RHInBoxT_1d4000000_3999999d4000000_21516_21548
import RHInBoxT_1d4000000_3999999d4000000_21548_21581
import RHInBoxT_1d4000000_3999999d4000000_21581_21613
import RHInBoxT_1d4000000_3999999d4000000_21613_21645
import RHInBoxT_1d4000000_3999999d4000000_86579d4_21677
import RHInBoxT_1d4000000_3999999d4000000_86707d4_21710
import RHInBoxT_1d4000000_3999999d4000000_21710_21742
import RHInBoxT_1d4000000_3999999d4000000_21742_21774
import RHInBoxT_1d4000000_3999999d4000000_21774_21806
import RHInBoxT_1d4000000_3999999d4000000_21806_21839
import RHInBoxT_1d4000000_3999999d4000000_21839_21871
import RHInBoxT_1d4000000_3999999d4000000_21871_21903
import RHInBoxT_1d4000000_3999999d4000000_21903_21935
import RHInBoxT_1d4000000_3999999d4000000_87739d4_21968
import RHInBoxT_1d4000000_3999999d4000000_21968_22000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h22000

/-- The 31-band NOMINAL partition of `[21000, 22000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 21000
  | 1 => 21032
  | 2 => 21065
  | 3 => 21097
  | 4 => 21129
  | 5 => 21161
  | 6 => 21194
  | 7 => 21226
  | 8 => 21258
  | 9 => 21290
  | 10 => 21323
  | 11 => 21355
  | 12 => 21387
  | 13 => 21419
  | 14 => 21452
  | 15 => 21484
  | 16 => 21516
  | 17 => 21548
  | 18 => 21581
  | 19 => 21613
  | 20 => 21645
  | 21 => 21677
  | 22 => 21710
  | 23 => 21742
  | 24 => 21774
  | 25 => 21806
  | 26 => 21839
  | 27 => 21871
  | 28 => 21903
  | 29 => 21935
  | 30 => 21968
  | 31 => 22000
  | _ => 22000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((21000:ℝ)) ≤ (21032); norm_num
  · show ((21032:ℝ)) ≤ (21065); norm_num
  · show ((21065:ℝ)) ≤ (21097); norm_num
  · show ((21097:ℝ)) ≤ (21129); norm_num
  · show ((21129:ℝ)) ≤ (21161); norm_num
  · show ((21161:ℝ)) ≤ (21194); norm_num
  · show ((21194:ℝ)) ≤ (21226); norm_num
  · show ((21226:ℝ)) ≤ (21258); norm_num
  · show ((21258:ℝ)) ≤ (21290); norm_num
  · show ((21290:ℝ)) ≤ (21323); norm_num
  · show ((21323:ℝ)) ≤ (21355); norm_num
  · show ((21355:ℝ)) ≤ (21387); norm_num
  · show ((21387:ℝ)) ≤ (21419); norm_num
  · show ((21419:ℝ)) ≤ (21452); norm_num
  · show ((21452:ℝ)) ≤ (21484); norm_num
  · show ((21484:ℝ)) ≤ (21516); norm_num
  · show ((21516:ℝ)) ≤ (21548); norm_num
  · show ((21548:ℝ)) ≤ (21581); norm_num
  · show ((21581:ℝ)) ≤ (21613); norm_num
  · show ((21613:ℝ)) ≤ (21645); norm_num
  · show ((21645:ℝ)) ≤ (21677); norm_num
  · show ((21677:ℝ)) ≤ (21710); norm_num
  · show ((21710:ℝ)) ≤ (21742); norm_num
  · show ((21742:ℝ)) ≤ (21774); norm_num
  · show ((21774:ℝ)) ≤ (21806); norm_num
  · show ((21806:ℝ)) ≤ (21839); norm_num
  · show ((21839:ℝ)) ≤ (21871); norm_num
  · show ((21871:ℝ)) ≤ (21903); norm_num
  · show ((21903:ℝ)) ≤ (21935); norm_num
  · show ((21935:ℝ)) ≤ (21968); norm_num
  · show ((21968:ℝ)) ≤ (22000); norm_num
  · show ((22000:ℝ)) ≤ (22000); norm_num
  · exact le_refl _

/-- The lower edges of the 31 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 21000
  | 1 => 21032
  | 2 => 21065
  | 3 => 21097
  | 4 => 21129
  | 5 => 21161
  | 6 => 21194
  | 7 => 21226
  | 8 => 21258
  | 9 => 21290
  | 10 => 21323
  | 11 => 85419 / 4
  | 12 => 21387
  | 13 => 21419
  | 14 => 21452
  | 15 => 21484
  | 16 => 21516
  | 17 => 21548
  | 18 => 21581
  | 19 => 21613
  | 20 => 86579 / 4
  | 21 => 86707 / 4
  | 22 => 21710
  | 23 => 21742
  | 24 => 21774
  | 25 => 21806
  | 26 => 21839
  | 27 => 21871
  | 28 => 21903
  | 29 => 87739 / 4
  | 30 => 21968
  | _ => 21968

/-- The upper edges of the 31 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 84129 / 4
  | 1 => 21065
  | 2 => 21097
  | 3 => 21129
  | 4 => 21161
  | 5 => 21194
  | 6 => 21226
  | 7 => 21258
  | 8 => 21290
  | 9 => 21323
  | 10 => 21355
  | 11 => 85549 / 4
  | 12 => 21419
  | 13 => 21452
  | 14 => 21484
  | 15 => 21516
  | 16 => 21548
  | 17 => 21581
  | 18 => 21613
  | 19 => 21645
  | 20 => 21677
  | 21 => 21710
  | 22 => 21742
  | 23 => 21774
  | 24 => 21806
  | 25 => 21839
  | 26 => 21871
  | 27 => 21903
  | 28 => 21935
  | 29 => 21968
  | 30 => 22000
  | _ => 22000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 31 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 22000` (`log 22000 ≤ 11`, `2.7^11 ≥ 22000`). -/
theorem haC_22000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 22000 := by
  have hlog : Real.log 22000 ≤ 11 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h11 : Real.exp 11 = (Real.exp 1) ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 11 ≤ (Real.exp 1) ^ 11 := pow_le_pow_left₀ (by norm_num) he1 11
    rw [h11]; nlinarith [hpow]
  have hpos : 0 < Real.log 22000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 22000
      ≤ (1 / 4000000) * 11 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[21000, 22000]` segment's band hypothesis: every band `i < 31` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 31 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 31 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[21000, 22000]` SEGMENT: every zero with `21000 ≤ Im ≤ 22000` is on the line. -/
theorem segment_21000_22000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 22000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (21000:ℝ) ≤ ρ.im → ρ.im ≤ 22000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 21000 22000 bndSeg 31 (by norm_num) bndSeg_mono rfl rfl haC_22000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 22000 via the HEIGHT CHAIN**: `[0,21000]` ∘ `[21000,22000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_22000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 22000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 22000 → ρ.re = 1 / 2 := by
  have hγ21000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 21000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 21000 22000
    (AllZeros_h21000.all_nontrivial_zeros_up_to_height_21000_of_bands
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
      hγ21000)
    (segment_21000_22000 hbands hγ)

end AllZeros_h22000
