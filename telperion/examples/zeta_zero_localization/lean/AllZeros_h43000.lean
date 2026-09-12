/-  Height-chain step: all nontrivial zeta zeros up to height 43000 on Re = 1/2 --
    `AllZeros_h42000` + a `[42000, 43000]` SEGMENT certificate (34 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h42000
import RHInBoxT_1d4000000_3999999d4000000_42000_168117d4
import RHInBoxT_1d4000000_3999999d4000000_42029_42059
import RHInBoxT_1d4000000_3999999d4000000_168235d4_42088
import RHInBoxT_1d4000000_3999999d4000000_42088_42118
import RHInBoxT_1d4000000_3999999d4000000_42118_42147
import RHInBoxT_1d4000000_3999999d4000000_42147_42176
import RHInBoxT_1d4000000_3999999d4000000_42176_42206
import RHInBoxT_1d4000000_3999999d4000000_42206_42235
import RHInBoxT_1d4000000_3999999d4000000_168939d4_42265
import RHInBoxT_1d4000000_3999999d4000000_42265_42294
import RHInBoxT_1d4000000_3999999d4000000_42294_42324
import RHInBoxT_1d4000000_3999999d4000000_42324_169413d4
import RHInBoxT_1d4000000_3999999d4000000_42353_42382
import RHInBoxT_1d4000000_3999999d4000000_42382_42412
import RHInBoxT_1d4000000_3999999d4000000_42412_42441
import RHInBoxT_1d4000000_3999999d4000000_42441_42471
import RHInBoxT_1d4000000_3999999d4000000_42471_170001d4
import RHInBoxT_1d4000000_3999999d4000000_42500_42529
import RHInBoxT_1d4000000_3999999d4000000_42529_42559
import RHInBoxT_1d4000000_3999999d4000000_170235d4_170353d4
import RHInBoxT_1d4000000_3999999d4000000_42588_42618
import RHInBoxT_1d4000000_3999999d4000000_42618_42647
import RHInBoxT_1d4000000_3999999d4000000_170587d4_42676
import RHInBoxT_1d4000000_3999999d4000000_170703d4_42706
import RHInBoxT_1d4000000_3999999d4000000_170823d4_42735
import RHInBoxT_1d4000000_3999999d4000000_170939d4_171061d4
import RHInBoxT_1d4000000_3999999d4000000_42765_42794
import RHInBoxT_1d4000000_3999999d4000000_42794_171297d4
import RHInBoxT_1d4000000_3999999d4000000_42824_42853
import RHInBoxT_1d4000000_3999999d4000000_42853_171529d4
import RHInBoxT_1d4000000_3999999d4000000_42882_42912
import RHInBoxT_1d4000000_3999999d4000000_42912_42941
import RHInBoxT_1d4000000_3999999d4000000_42941_42971
import RHInBoxT_1d4000000_3999999d4000000_42971_43000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h43000

/-- The 34-band NOMINAL partition of `[42000, 43000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 42000
  | 1 => 42029
  | 2 => 42059
  | 3 => 42088
  | 4 => 42118
  | 5 => 42147
  | 6 => 42176
  | 7 => 42206
  | 8 => 42235
  | 9 => 42265
  | 10 => 42294
  | 11 => 42324
  | 12 => 42353
  | 13 => 42382
  | 14 => 42412
  | 15 => 42441
  | 16 => 42471
  | 17 => 42500
  | 18 => 42529
  | 19 => 42559
  | 20 => 42588
  | 21 => 42618
  | 22 => 42647
  | 23 => 42676
  | 24 => 42706
  | 25 => 42735
  | 26 => 42765
  | 27 => 42794
  | 28 => 42824
  | 29 => 42853
  | 30 => 42882
  | 31 => 42912
  | 32 => 42941
  | 33 => 42971
  | 34 => 43000
  | _ => 43000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((42000:ℝ)) ≤ (42029); norm_num
  · show ((42029:ℝ)) ≤ (42059); norm_num
  · show ((42059:ℝ)) ≤ (42088); norm_num
  · show ((42088:ℝ)) ≤ (42118); norm_num
  · show ((42118:ℝ)) ≤ (42147); norm_num
  · show ((42147:ℝ)) ≤ (42176); norm_num
  · show ((42176:ℝ)) ≤ (42206); norm_num
  · show ((42206:ℝ)) ≤ (42235); norm_num
  · show ((42235:ℝ)) ≤ (42265); norm_num
  · show ((42265:ℝ)) ≤ (42294); norm_num
  · show ((42294:ℝ)) ≤ (42324); norm_num
  · show ((42324:ℝ)) ≤ (42353); norm_num
  · show ((42353:ℝ)) ≤ (42382); norm_num
  · show ((42382:ℝ)) ≤ (42412); norm_num
  · show ((42412:ℝ)) ≤ (42441); norm_num
  · show ((42441:ℝ)) ≤ (42471); norm_num
  · show ((42471:ℝ)) ≤ (42500); norm_num
  · show ((42500:ℝ)) ≤ (42529); norm_num
  · show ((42529:ℝ)) ≤ (42559); norm_num
  · show ((42559:ℝ)) ≤ (42588); norm_num
  · show ((42588:ℝ)) ≤ (42618); norm_num
  · show ((42618:ℝ)) ≤ (42647); norm_num
  · show ((42647:ℝ)) ≤ (42676); norm_num
  · show ((42676:ℝ)) ≤ (42706); norm_num
  · show ((42706:ℝ)) ≤ (42735); norm_num
  · show ((42735:ℝ)) ≤ (42765); norm_num
  · show ((42765:ℝ)) ≤ (42794); norm_num
  · show ((42794:ℝ)) ≤ (42824); norm_num
  · show ((42824:ℝ)) ≤ (42853); norm_num
  · show ((42853:ℝ)) ≤ (42882); norm_num
  · show ((42882:ℝ)) ≤ (42912); norm_num
  · show ((42912:ℝ)) ≤ (42941); norm_num
  · show ((42941:ℝ)) ≤ (42971); norm_num
  · show ((42971:ℝ)) ≤ (43000); norm_num
  · show ((43000:ℝ)) ≤ (43000); norm_num
  · exact le_refl _

/-- The lower edges of the 34 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 42000
  | 1 => 42029
  | 2 => 168235 / 4
  | 3 => 42088
  | 4 => 42118
  | 5 => 42147
  | 6 => 42176
  | 7 => 42206
  | 8 => 168939 / 4
  | 9 => 42265
  | 10 => 42294
  | 11 => 42324
  | 12 => 42353
  | 13 => 42382
  | 14 => 42412
  | 15 => 42441
  | 16 => 42471
  | 17 => 42500
  | 18 => 42529
  | 19 => 170235 / 4
  | 20 => 42588
  | 21 => 42618
  | 22 => 170587 / 4
  | 23 => 170703 / 4
  | 24 => 170823 / 4
  | 25 => 170939 / 4
  | 26 => 42765
  | 27 => 42794
  | 28 => 42824
  | 29 => 42853
  | 30 => 42882
  | 31 => 42912
  | 32 => 42941
  | 33 => 42971
  | _ => 42971

/-- The upper edges of the 34 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 168117 / 4
  | 1 => 42059
  | 2 => 42088
  | 3 => 42118
  | 4 => 42147
  | 5 => 42176
  | 6 => 42206
  | 7 => 42235
  | 8 => 42265
  | 9 => 42294
  | 10 => 42324
  | 11 => 169413 / 4
  | 12 => 42382
  | 13 => 42412
  | 14 => 42441
  | 15 => 42471
  | 16 => 170001 / 4
  | 17 => 42529
  | 18 => 42559
  | 19 => 170353 / 4
  | 20 => 42618
  | 21 => 42647
  | 22 => 42676
  | 23 => 42706
  | 24 => 42735
  | 25 => 171061 / 4
  | 26 => 42794
  | 27 => 171297 / 4
  | 28 => 42853
  | 29 => 171529 / 4
  | 30 => 42912
  | 31 => 42941
  | 32 => 42971
  | 33 => 43000
  | _ => 43000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 34 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 43000` (`log 43000 ≤ 11`, `2.7^11 ≥ 43000`). -/
theorem haC_43000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 43000 := by
  have hlog : Real.log 43000 ≤ 11 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h11 : Real.exp 11 = (Real.exp 1) ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 11 ≤ (Real.exp 1) ^ 11 := pow_le_pow_left₀ (by norm_num) he1 11
    rw [h11]; nlinarith [hpow]
  have hpos : 0 < Real.log 43000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 43000
      ≤ (1 / 4000000) * 11 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[42000, 43000]` segment's band hypothesis: every band `i < 34` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 34 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 34 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[42000, 43000]` SEGMENT: every zero with `42000 ≤ Im ≤ 43000` is on the line. -/
theorem segment_42000_43000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 43000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (42000:ℝ) ≤ ρ.im → ρ.im ≤ 43000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 42000 43000 bndSeg 34 (by norm_num) bndSeg_mono rfl rfl haC_43000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 43000 via the HEIGHT CHAIN**: `[0,42000]` ∘ `[42000,43000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_43000_of_bands
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
    (hbands_23000 : AllZeros_h23000.BandHyp)
    (hbands_24000 : AllZeros_h24000.BandHyp)
    (hbands_25000 : AllZeros_h25000.BandHyp)
    (hbands_26000 : AllZeros_h26000.BandHyp)
    (hbands_27000 : AllZeros_h27000.BandHyp)
    (hbands_28000 : AllZeros_h28000.BandHyp)
    (hbands_29000 : AllZeros_h29000.BandHyp)
    (hbands_30000 : AllZeros_h30000.BandHyp)
    (hbands_31000 : AllZeros_h31000.BandHyp)
    (hbands_32000 : AllZeros_h32000.BandHyp)
    (hbands_33000 : AllZeros_h33000.BandHyp)
    (hbands_34000 : AllZeros_h34000.BandHyp)
    (hbands_35000 : AllZeros_h35000.BandHyp)
    (hbands_36000 : AllZeros_h36000.BandHyp)
    (hbands_37000 : AllZeros_h37000.BandHyp)
    (hbands_38000 : AllZeros_h38000.BandHyp)
    (hbands_39000 : AllZeros_h39000.BandHyp)
    (hbands_40000 : AllZeros_h40000.BandHyp)
    (hbands_41000 : AllZeros_h41000.BandHyp)
    (hbands_42000 : AllZeros_h42000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 43000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 43000 → ρ.re = 1 / 2 := by
  have hγ42000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 42000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 42000 43000
    (AllZeros_h42000.all_nontrivial_zeros_up_to_height_42000_of_bands
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
      hbands_23000
      hbands_24000
      hbands_25000
      hbands_26000
      hbands_27000
      hbands_28000
      hbands_29000
      hbands_30000
      hbands_31000
      hbands_32000
      hbands_33000
      hbands_34000
      hbands_35000
      hbands_36000
      hbands_37000
      hbands_38000
      hbands_39000
      hbands_40000
      hbands_41000
      hbands_42000
      hγ42000)
    (segment_42000_43000 hbands hγ)

end AllZeros_h43000
