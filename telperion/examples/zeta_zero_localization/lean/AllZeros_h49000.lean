/-  Height-chain step: all nontrivial zeta zeros up to height 49000 on Re = 1/2 --
    `AllZeros_h48000` + a `[48000, 49000]` SEGMENT certificate (34 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h48000
import RHInBoxT_1d4000000_3999999d4000000_191999d4_48029
import RHInBoxT_1d4000000_3999999d4000000_48029_48059
import RHInBoxT_1d4000000_3999999d4000000_48059_48088
import RHInBoxT_1d4000000_3999999d4000000_192351d4_192473d4
import RHInBoxT_1d4000000_3999999d4000000_48118_48147
import RHInBoxT_1d4000000_3999999d4000000_48147_48176
import RHInBoxT_1d4000000_3999999d4000000_192703d4_48206
import RHInBoxT_1d4000000_3999999d4000000_48206_48235
import RHInBoxT_1d4000000_3999999d4000000_192939d4_48265
import RHInBoxT_1d4000000_3999999d4000000_48265_48294
import RHInBoxT_1d4000000_3999999d4000000_48294_48324
import RHInBoxT_1d4000000_3999999d4000000_48324_48353
import RHInBoxT_1d4000000_3999999d4000000_193411d4_48382
import RHInBoxT_1d4000000_3999999d4000000_48382_48412
import RHInBoxT_1d4000000_3999999d4000000_48412_193765d4
import RHInBoxT_1d4000000_3999999d4000000_48441_193885d4
import RHInBoxT_1d4000000_3999999d4000000_48471_48500
import RHInBoxT_1d4000000_3999999d4000000_48500_194117d4
import RHInBoxT_1d4000000_3999999d4000000_48529_48559
import RHInBoxT_1d4000000_3999999d4000000_48559_194353d4
import RHInBoxT_1d4000000_3999999d4000000_48588_194473d4
import RHInBoxT_1d4000000_3999999d4000000_48618_48647
import RHInBoxT_1d4000000_3999999d4000000_48647_48676
import RHInBoxT_1d4000000_3999999d4000000_48676_48706
import RHInBoxT_1d4000000_3999999d4000000_48706_48735
import RHInBoxT_1d4000000_3999999d4000000_48735_48765
import RHInBoxT_1d4000000_3999999d4000000_48765_48794
import RHInBoxT_1d4000000_3999999d4000000_48794_48824
import RHInBoxT_1d4000000_3999999d4000000_48824_195413d4
import RHInBoxT_1d4000000_3999999d4000000_48853_48882
import RHInBoxT_1d4000000_3999999d4000000_48882_195649d4
import RHInBoxT_1d4000000_3999999d4000000_48912_195765d4
import RHInBoxT_1d4000000_3999999d4000000_48941_48971
import RHInBoxT_1d4000000_3999999d4000000_48971_49000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h49000

/-- The 34-band NOMINAL partition of `[48000, 49000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 48000
  | 1 => 48029
  | 2 => 48059
  | 3 => 48088
  | 4 => 48118
  | 5 => 48147
  | 6 => 48176
  | 7 => 48206
  | 8 => 48235
  | 9 => 48265
  | 10 => 48294
  | 11 => 48324
  | 12 => 48353
  | 13 => 48382
  | 14 => 48412
  | 15 => 48441
  | 16 => 48471
  | 17 => 48500
  | 18 => 48529
  | 19 => 48559
  | 20 => 48588
  | 21 => 48618
  | 22 => 48647
  | 23 => 48676
  | 24 => 48706
  | 25 => 48735
  | 26 => 48765
  | 27 => 48794
  | 28 => 48824
  | 29 => 48853
  | 30 => 48882
  | 31 => 48912
  | 32 => 48941
  | 33 => 48971
  | 34 => 49000
  | _ => 49000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((48000:ℝ)) ≤ (48029); norm_num
  · show ((48029:ℝ)) ≤ (48059); norm_num
  · show ((48059:ℝ)) ≤ (48088); norm_num
  · show ((48088:ℝ)) ≤ (48118); norm_num
  · show ((48118:ℝ)) ≤ (48147); norm_num
  · show ((48147:ℝ)) ≤ (48176); norm_num
  · show ((48176:ℝ)) ≤ (48206); norm_num
  · show ((48206:ℝ)) ≤ (48235); norm_num
  · show ((48235:ℝ)) ≤ (48265); norm_num
  · show ((48265:ℝ)) ≤ (48294); norm_num
  · show ((48294:ℝ)) ≤ (48324); norm_num
  · show ((48324:ℝ)) ≤ (48353); norm_num
  · show ((48353:ℝ)) ≤ (48382); norm_num
  · show ((48382:ℝ)) ≤ (48412); norm_num
  · show ((48412:ℝ)) ≤ (48441); norm_num
  · show ((48441:ℝ)) ≤ (48471); norm_num
  · show ((48471:ℝ)) ≤ (48500); norm_num
  · show ((48500:ℝ)) ≤ (48529); norm_num
  · show ((48529:ℝ)) ≤ (48559); norm_num
  · show ((48559:ℝ)) ≤ (48588); norm_num
  · show ((48588:ℝ)) ≤ (48618); norm_num
  · show ((48618:ℝ)) ≤ (48647); norm_num
  · show ((48647:ℝ)) ≤ (48676); norm_num
  · show ((48676:ℝ)) ≤ (48706); norm_num
  · show ((48706:ℝ)) ≤ (48735); norm_num
  · show ((48735:ℝ)) ≤ (48765); norm_num
  · show ((48765:ℝ)) ≤ (48794); norm_num
  · show ((48794:ℝ)) ≤ (48824); norm_num
  · show ((48824:ℝ)) ≤ (48853); norm_num
  · show ((48853:ℝ)) ≤ (48882); norm_num
  · show ((48882:ℝ)) ≤ (48912); norm_num
  · show ((48912:ℝ)) ≤ (48941); norm_num
  · show ((48941:ℝ)) ≤ (48971); norm_num
  · show ((48971:ℝ)) ≤ (49000); norm_num
  · show ((49000:ℝ)) ≤ (49000); norm_num
  · exact le_refl _

/-- The lower edges of the 34 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 191999 / 4
  | 1 => 48029
  | 2 => 48059
  | 3 => 192351 / 4
  | 4 => 48118
  | 5 => 48147
  | 6 => 192703 / 4
  | 7 => 48206
  | 8 => 192939 / 4
  | 9 => 48265
  | 10 => 48294
  | 11 => 48324
  | 12 => 193411 / 4
  | 13 => 48382
  | 14 => 48412
  | 15 => 48441
  | 16 => 48471
  | 17 => 48500
  | 18 => 48529
  | 19 => 48559
  | 20 => 48588
  | 21 => 48618
  | 22 => 48647
  | 23 => 48676
  | 24 => 48706
  | 25 => 48735
  | 26 => 48765
  | 27 => 48794
  | 28 => 48824
  | 29 => 48853
  | 30 => 48882
  | 31 => 48912
  | 32 => 48941
  | 33 => 48971
  | _ => 48971

/-- The upper edges of the 34 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 48029
  | 1 => 48059
  | 2 => 48088
  | 3 => 192473 / 4
  | 4 => 48147
  | 5 => 48176
  | 6 => 48206
  | 7 => 48235
  | 8 => 48265
  | 9 => 48294
  | 10 => 48324
  | 11 => 48353
  | 12 => 48382
  | 13 => 48412
  | 14 => 193765 / 4
  | 15 => 193885 / 4
  | 16 => 48500
  | 17 => 194117 / 4
  | 18 => 48559
  | 19 => 194353 / 4
  | 20 => 194473 / 4
  | 21 => 48647
  | 22 => 48676
  | 23 => 48706
  | 24 => 48735
  | 25 => 48765
  | 26 => 48794
  | 27 => 48824
  | 28 => 195413 / 4
  | 29 => 48882
  | 30 => 195649 / 4
  | 31 => 195765 / 4
  | 32 => 48971
  | 33 => 49000
  | _ => 49000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 34 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 49000` (`log 49000 ≤ 11`, `2.7^11 ≥ 49000`). -/
theorem haC_49000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 49000 := by
  have hlog : Real.log 49000 ≤ 11 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h11 : Real.exp 11 = (Real.exp 1) ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 11 ≤ (Real.exp 1) ^ 11 := pow_le_pow_left₀ (by norm_num) he1 11
    rw [h11]; nlinarith [hpow]
  have hpos : 0 < Real.log 49000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 49000
      ≤ (1 / 4000000) * 11 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[48000, 49000]` segment's band hypothesis: every band `i < 34` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 34 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 34 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[48000, 49000]` SEGMENT: every zero with `48000 ≤ Im ≤ 49000` is on the line. -/
theorem segment_48000_49000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 49000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (48000:ℝ) ≤ ρ.im → ρ.im ≤ 49000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 48000 49000 bndSeg 34 (by norm_num) bndSeg_mono rfl rfl haC_49000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 49000 via the HEIGHT CHAIN**: `[0,48000]` ∘ `[48000,49000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_49000_of_bands
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
    (hbands_43000 : AllZeros_h43000.BandHyp)
    (hbands_44000 : AllZeros_h44000.BandHyp)
    (hbands_45000 : AllZeros_h45000.BandHyp)
    (hbands_46000 : AllZeros_h46000.BandHyp)
    (hbands_47000 : AllZeros_h47000.BandHyp)
    (hbands_48000 : AllZeros_h48000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 49000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 49000 → ρ.re = 1 / 2 := by
  have hγ48000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 48000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 48000 49000
    (AllZeros_h48000.all_nontrivial_zeros_up_to_height_48000_of_bands
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
      hbands_43000
      hbands_44000
      hbands_45000
      hbands_46000
      hbands_47000
      hbands_48000
      hγ48000)
    (segment_48000_49000 hbands hγ)

end AllZeros_h49000
