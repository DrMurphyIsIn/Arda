/-  Height-chain step: all nontrivial zeta zeros up to height 46000 on Re = 1/2 --
    `AllZeros_h45000` + a `[45000, 46000]` SEGMENT certificate (34 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h45000
import RHInBoxT_1d4000000_3999999d4000000_45000_45029
import RHInBoxT_1d4000000_3999999d4000000_45029_45059
import RHInBoxT_1d4000000_3999999d4000000_45059_45088
import RHInBoxT_1d4000000_3999999d4000000_45088_45118
import RHInBoxT_1d4000000_3999999d4000000_45118_45147
import RHInBoxT_1d4000000_3999999d4000000_45147_180705d4
import RHInBoxT_1d4000000_3999999d4000000_45176_45206
import RHInBoxT_1d4000000_3999999d4000000_45206_45235
import RHInBoxT_1d4000000_3999999d4000000_45235_45265
import RHInBoxT_1d4000000_3999999d4000000_45265_45294
import RHInBoxT_1d4000000_3999999d4000000_45294_181297d4
import RHInBoxT_1d4000000_3999999d4000000_45324_45353
import RHInBoxT_1d4000000_3999999d4000000_45353_45382
import RHInBoxT_1d4000000_3999999d4000000_45382_181649d4
import RHInBoxT_1d4000000_3999999d4000000_45412_45441
import RHInBoxT_1d4000000_3999999d4000000_45441_45471
import RHInBoxT_1d4000000_3999999d4000000_45471_182001d4
import RHInBoxT_1d4000000_3999999d4000000_45500_45529
import RHInBoxT_1d4000000_3999999d4000000_45529_45559
import RHInBoxT_1d4000000_3999999d4000000_45559_182353d4
import RHInBoxT_1d4000000_3999999d4000000_45588_45618
import RHInBoxT_1d4000000_3999999d4000000_45618_45647
import RHInBoxT_1d4000000_3999999d4000000_45647_45676
import RHInBoxT_1d4000000_3999999d4000000_45676_45706
import RHInBoxT_1d4000000_3999999d4000000_45706_45735
import RHInBoxT_1d4000000_3999999d4000000_45735_45765
import RHInBoxT_1d4000000_3999999d4000000_183059d4_45794
import RHInBoxT_1d4000000_3999999d4000000_45794_45824
import RHInBoxT_1d4000000_3999999d4000000_183295d4_45853
import RHInBoxT_1d4000000_3999999d4000000_183411d4_45882
import RHInBoxT_1d4000000_3999999d4000000_45882_45912
import RHInBoxT_1d4000000_3999999d4000000_183647d4_45941
import RHInBoxT_1d4000000_3999999d4000000_45941_45971
import RHInBoxT_1d4000000_3999999d4000000_45971_46000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h46000

/-- The 34-band NOMINAL partition of `[45000, 46000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 45000
  | 1 => 45029
  | 2 => 45059
  | 3 => 45088
  | 4 => 45118
  | 5 => 45147
  | 6 => 45176
  | 7 => 45206
  | 8 => 45235
  | 9 => 45265
  | 10 => 45294
  | 11 => 45324
  | 12 => 45353
  | 13 => 45382
  | 14 => 45412
  | 15 => 45441
  | 16 => 45471
  | 17 => 45500
  | 18 => 45529
  | 19 => 45559
  | 20 => 45588
  | 21 => 45618
  | 22 => 45647
  | 23 => 45676
  | 24 => 45706
  | 25 => 45735
  | 26 => 45765
  | 27 => 45794
  | 28 => 45824
  | 29 => 45853
  | 30 => 45882
  | 31 => 45912
  | 32 => 45941
  | 33 => 45971
  | 34 => 46000
  | _ => 46000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((45000:ℝ)) ≤ (45029); norm_num
  · show ((45029:ℝ)) ≤ (45059); norm_num
  · show ((45059:ℝ)) ≤ (45088); norm_num
  · show ((45088:ℝ)) ≤ (45118); norm_num
  · show ((45118:ℝ)) ≤ (45147); norm_num
  · show ((45147:ℝ)) ≤ (45176); norm_num
  · show ((45176:ℝ)) ≤ (45206); norm_num
  · show ((45206:ℝ)) ≤ (45235); norm_num
  · show ((45235:ℝ)) ≤ (45265); norm_num
  · show ((45265:ℝ)) ≤ (45294); norm_num
  · show ((45294:ℝ)) ≤ (45324); norm_num
  · show ((45324:ℝ)) ≤ (45353); norm_num
  · show ((45353:ℝ)) ≤ (45382); norm_num
  · show ((45382:ℝ)) ≤ (45412); norm_num
  · show ((45412:ℝ)) ≤ (45441); norm_num
  · show ((45441:ℝ)) ≤ (45471); norm_num
  · show ((45471:ℝ)) ≤ (45500); norm_num
  · show ((45500:ℝ)) ≤ (45529); norm_num
  · show ((45529:ℝ)) ≤ (45559); norm_num
  · show ((45559:ℝ)) ≤ (45588); norm_num
  · show ((45588:ℝ)) ≤ (45618); norm_num
  · show ((45618:ℝ)) ≤ (45647); norm_num
  · show ((45647:ℝ)) ≤ (45676); norm_num
  · show ((45676:ℝ)) ≤ (45706); norm_num
  · show ((45706:ℝ)) ≤ (45735); norm_num
  · show ((45735:ℝ)) ≤ (45765); norm_num
  · show ((45765:ℝ)) ≤ (45794); norm_num
  · show ((45794:ℝ)) ≤ (45824); norm_num
  · show ((45824:ℝ)) ≤ (45853); norm_num
  · show ((45853:ℝ)) ≤ (45882); norm_num
  · show ((45882:ℝ)) ≤ (45912); norm_num
  · show ((45912:ℝ)) ≤ (45941); norm_num
  · show ((45941:ℝ)) ≤ (45971); norm_num
  · show ((45971:ℝ)) ≤ (46000); norm_num
  · show ((46000:ℝ)) ≤ (46000); norm_num
  · exact le_refl _

/-- The lower edges of the 34 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 45000
  | 1 => 45029
  | 2 => 45059
  | 3 => 45088
  | 4 => 45118
  | 5 => 45147
  | 6 => 45176
  | 7 => 45206
  | 8 => 45235
  | 9 => 45265
  | 10 => 45294
  | 11 => 45324
  | 12 => 45353
  | 13 => 45382
  | 14 => 45412
  | 15 => 45441
  | 16 => 45471
  | 17 => 45500
  | 18 => 45529
  | 19 => 45559
  | 20 => 45588
  | 21 => 45618
  | 22 => 45647
  | 23 => 45676
  | 24 => 45706
  | 25 => 45735
  | 26 => 183059 / 4
  | 27 => 45794
  | 28 => 183295 / 4
  | 29 => 183411 / 4
  | 30 => 45882
  | 31 => 183647 / 4
  | 32 => 45941
  | 33 => 45971
  | _ => 45971

/-- The upper edges of the 34 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 45029
  | 1 => 45059
  | 2 => 45088
  | 3 => 45118
  | 4 => 45147
  | 5 => 180705 / 4
  | 6 => 45206
  | 7 => 45235
  | 8 => 45265
  | 9 => 45294
  | 10 => 181297 / 4
  | 11 => 45353
  | 12 => 45382
  | 13 => 181649 / 4
  | 14 => 45441
  | 15 => 45471
  | 16 => 182001 / 4
  | 17 => 45529
  | 18 => 45559
  | 19 => 182353 / 4
  | 20 => 45618
  | 21 => 45647
  | 22 => 45676
  | 23 => 45706
  | 24 => 45735
  | 25 => 45765
  | 26 => 45794
  | 27 => 45824
  | 28 => 45853
  | 29 => 45882
  | 30 => 45912
  | 31 => 45941
  | 32 => 45971
  | 33 => 46000
  | _ => 46000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 34 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 46000` (`log 46000 ≤ 11`, `2.7^11 ≥ 46000`). -/
theorem haC_46000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 46000 := by
  have hlog : Real.log 46000 ≤ 11 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h11 : Real.exp 11 = (Real.exp 1) ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 11 ≤ (Real.exp 1) ^ 11 := pow_le_pow_left₀ (by norm_num) he1 11
    rw [h11]; nlinarith [hpow]
  have hpos : 0 < Real.log 46000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 46000
      ≤ (1 / 4000000) * 11 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[45000, 46000]` segment's band hypothesis: every band `i < 34` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 34 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 34 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[45000, 46000]` SEGMENT: every zero with `45000 ≤ Im ≤ 46000` is on the line. -/
theorem segment_45000_46000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 46000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (45000:ℝ) ≤ ρ.im → ρ.im ≤ 46000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 45000 46000 bndSeg 34 (by norm_num) bndSeg_mono rfl rfl haC_46000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 46000 via the HEIGHT CHAIN**: `[0,45000]` ∘ `[45000,46000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_46000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 46000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 46000 → ρ.re = 1 / 2 := by
  have hγ45000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 45000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 45000 46000
    (AllZeros_h45000.all_nontrivial_zeros_up_to_height_45000_of_bands
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
      hγ45000)
    (segment_45000_46000 hbands hγ)

end AllZeros_h46000
