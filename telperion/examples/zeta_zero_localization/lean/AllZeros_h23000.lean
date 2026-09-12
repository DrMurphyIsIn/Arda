/-  Height-chain step: all nontrivial zeta zeros up to height 23000 on Re = 1/2 --
    `AllZeros_h22000` + a `[22000, 23000]` SEGMENT certificate (31 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h22000
import RHInBoxT_1d4000000_3999999d4000000_22000_22032
import RHInBoxT_1d4000000_3999999d4000000_22032_22065
import RHInBoxT_1d4000000_3999999d4000000_22065_22097
import RHInBoxT_1d4000000_3999999d4000000_22097_22129
import RHInBoxT_1d4000000_3999999d4000000_22129_22161
import RHInBoxT_1d4000000_3999999d4000000_22161_22194
import RHInBoxT_1d4000000_3999999d4000000_22194_88905d4
import RHInBoxT_1d4000000_3999999d4000000_22226_22258
import RHInBoxT_1d4000000_3999999d4000000_22258_22290
import RHInBoxT_1d4000000_3999999d4000000_22290_22323
import RHInBoxT_1d4000000_3999999d4000000_22323_89421d4
import RHInBoxT_1d4000000_3999999d4000000_22355_89549d4
import RHInBoxT_1d4000000_3999999d4000000_22387_22419
import RHInBoxT_1d4000000_3999999d4000000_22419_22452
import RHInBoxT_1d4000000_3999999d4000000_22452_89937d4
import RHInBoxT_1d4000000_3999999d4000000_22484_22516
import RHInBoxT_1d4000000_3999999d4000000_22516_22548
import RHInBoxT_1d4000000_3999999d4000000_22548_90325d4
import RHInBoxT_1d4000000_3999999d4000000_22581_22613
import RHInBoxT_1d4000000_3999999d4000000_22613_22645
import RHInBoxT_1d4000000_3999999d4000000_22645_22677
import RHInBoxT_1d4000000_3999999d4000000_22677_22710
import RHInBoxT_1d4000000_3999999d4000000_22710_22742
import RHInBoxT_1d4000000_3999999d4000000_22742_22774
import RHInBoxT_1d4000000_3999999d4000000_22774_22806
import RHInBoxT_1d4000000_3999999d4000000_22806_91357d4
import RHInBoxT_1d4000000_3999999d4000000_22839_22871
import RHInBoxT_1d4000000_3999999d4000000_22871_22903
import RHInBoxT_1d4000000_3999999d4000000_22903_22935
import RHInBoxT_1d4000000_3999999d4000000_22935_22968
import RHInBoxT_1d4000000_3999999d4000000_22968_23000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h23000

/-- The 31-band NOMINAL partition of `[22000, 23000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 22000
  | 1 => 22032
  | 2 => 22065
  | 3 => 22097
  | 4 => 22129
  | 5 => 22161
  | 6 => 22194
  | 7 => 22226
  | 8 => 22258
  | 9 => 22290
  | 10 => 22323
  | 11 => 22355
  | 12 => 22387
  | 13 => 22419
  | 14 => 22452
  | 15 => 22484
  | 16 => 22516
  | 17 => 22548
  | 18 => 22581
  | 19 => 22613
  | 20 => 22645
  | 21 => 22677
  | 22 => 22710
  | 23 => 22742
  | 24 => 22774
  | 25 => 22806
  | 26 => 22839
  | 27 => 22871
  | 28 => 22903
  | 29 => 22935
  | 30 => 22968
  | 31 => 23000
  | _ => 23000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((22000:ℝ)) ≤ (22032); norm_num
  · show ((22032:ℝ)) ≤ (22065); norm_num
  · show ((22065:ℝ)) ≤ (22097); norm_num
  · show ((22097:ℝ)) ≤ (22129); norm_num
  · show ((22129:ℝ)) ≤ (22161); norm_num
  · show ((22161:ℝ)) ≤ (22194); norm_num
  · show ((22194:ℝ)) ≤ (22226); norm_num
  · show ((22226:ℝ)) ≤ (22258); norm_num
  · show ((22258:ℝ)) ≤ (22290); norm_num
  · show ((22290:ℝ)) ≤ (22323); norm_num
  · show ((22323:ℝ)) ≤ (22355); norm_num
  · show ((22355:ℝ)) ≤ (22387); norm_num
  · show ((22387:ℝ)) ≤ (22419); norm_num
  · show ((22419:ℝ)) ≤ (22452); norm_num
  · show ((22452:ℝ)) ≤ (22484); norm_num
  · show ((22484:ℝ)) ≤ (22516); norm_num
  · show ((22516:ℝ)) ≤ (22548); norm_num
  · show ((22548:ℝ)) ≤ (22581); norm_num
  · show ((22581:ℝ)) ≤ (22613); norm_num
  · show ((22613:ℝ)) ≤ (22645); norm_num
  · show ((22645:ℝ)) ≤ (22677); norm_num
  · show ((22677:ℝ)) ≤ (22710); norm_num
  · show ((22710:ℝ)) ≤ (22742); norm_num
  · show ((22742:ℝ)) ≤ (22774); norm_num
  · show ((22774:ℝ)) ≤ (22806); norm_num
  · show ((22806:ℝ)) ≤ (22839); norm_num
  · show ((22839:ℝ)) ≤ (22871); norm_num
  · show ((22871:ℝ)) ≤ (22903); norm_num
  · show ((22903:ℝ)) ≤ (22935); norm_num
  · show ((22935:ℝ)) ≤ (22968); norm_num
  · show ((22968:ℝ)) ≤ (23000); norm_num
  · show ((23000:ℝ)) ≤ (23000); norm_num
  · exact le_refl _

/-- The lower edges of the 31 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 22000
  | 1 => 22032
  | 2 => 22065
  | 3 => 22097
  | 4 => 22129
  | 5 => 22161
  | 6 => 22194
  | 7 => 22226
  | 8 => 22258
  | 9 => 22290
  | 10 => 22323
  | 11 => 22355
  | 12 => 22387
  | 13 => 22419
  | 14 => 22452
  | 15 => 22484
  | 16 => 22516
  | 17 => 22548
  | 18 => 22581
  | 19 => 22613
  | 20 => 22645
  | 21 => 22677
  | 22 => 22710
  | 23 => 22742
  | 24 => 22774
  | 25 => 22806
  | 26 => 22839
  | 27 => 22871
  | 28 => 22903
  | 29 => 22935
  | 30 => 22968
  | _ => 22968

/-- The upper edges of the 31 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 22032
  | 1 => 22065
  | 2 => 22097
  | 3 => 22129
  | 4 => 22161
  | 5 => 22194
  | 6 => 88905 / 4
  | 7 => 22258
  | 8 => 22290
  | 9 => 22323
  | 10 => 89421 / 4
  | 11 => 89549 / 4
  | 12 => 22419
  | 13 => 22452
  | 14 => 89937 / 4
  | 15 => 22516
  | 16 => 22548
  | 17 => 90325 / 4
  | 18 => 22613
  | 19 => 22645
  | 20 => 22677
  | 21 => 22710
  | 22 => 22742
  | 23 => 22774
  | 24 => 22806
  | 25 => 91357 / 4
  | 26 => 22871
  | 27 => 22903
  | 28 => 22935
  | 29 => 22968
  | 30 => 23000
  | _ => 23000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 31 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 23000` (`log 23000 ≤ 11`, `2.7^11 ≥ 23000`). -/
theorem haC_23000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 23000 := by
  have hlog : Real.log 23000 ≤ 11 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h11 : Real.exp 11 = (Real.exp 1) ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 11 ≤ (Real.exp 1) ^ 11 := pow_le_pow_left₀ (by norm_num) he1 11
    rw [h11]; nlinarith [hpow]
  have hpos : 0 < Real.log 23000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 23000
      ≤ (1 / 4000000) * 11 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[22000, 23000]` segment's band hypothesis: every band `i < 31` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 31 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 31 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[22000, 23000]` SEGMENT: every zero with `22000 ≤ Im ≤ 23000` is on the line. -/
theorem segment_22000_23000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 23000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (22000:ℝ) ≤ ρ.im → ρ.im ≤ 23000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 22000 23000 bndSeg 31 (by norm_num) bndSeg_mono rfl rfl haC_23000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 23000 via the HEIGHT CHAIN**: `[0,22000]` ∘ `[22000,23000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_23000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 23000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 23000 → ρ.re = 1 / 2 := by
  have hγ22000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 22000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 22000 23000
    (AllZeros_h22000.all_nontrivial_zeros_up_to_height_22000_of_bands
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
      hγ22000)
    (segment_22000_23000 hbands hγ)

end AllZeros_h23000
