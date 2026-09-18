/-  Height-chain step: all nontrivial zeta zeros up to height 53000 on Re = 1/2 --
    `AllZeros_h52000` + a `[52000, 53000]` SEGMENT certificate (35 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h52000
import RHInBoxT_1d4000000_3999999d4000000_52000_52029
import RHInBoxT_1d4000000_3999999d4000000_52029_52057
import RHInBoxT_1d4000000_3999999d4000000_52057_52086
import RHInBoxT_1d4000000_3999999d4000000_52086_52114
import RHInBoxT_1d4000000_3999999d4000000_208455d4_52143
import RHInBoxT_1d4000000_3999999d4000000_52143_52171
import RHInBoxT_1d4000000_3999999d4000000_208683d4_52200
import RHInBoxT_1d4000000_3999999d4000000_52200_52229
import RHInBoxT_1d4000000_3999999d4000000_52229_52257
import RHInBoxT_1d4000000_3999999d4000000_52257_52286
import RHInBoxT_1d4000000_3999999d4000000_52286_52314
import RHInBoxT_1d4000000_3999999d4000000_209255d4_209373d4
import RHInBoxT_1d4000000_3999999d4000000_52343_52371
import RHInBoxT_1d4000000_3999999d4000000_52371_52400
import RHInBoxT_1d4000000_3999999d4000000_52400_52429
import RHInBoxT_1d4000000_3999999d4000000_209715d4_52457
import RHInBoxT_1d4000000_3999999d4000000_52457_52486
import RHInBoxT_1d4000000_3999999d4000000_52486_52514
import RHInBoxT_1d4000000_3999999d4000000_52514_52543
import RHInBoxT_1d4000000_3999999d4000000_52543_52571
import RHInBoxT_1d4000000_3999999d4000000_52571_52600
import RHInBoxT_1d4000000_3999999d4000000_52600_52629
import RHInBoxT_1d4000000_3999999d4000000_52629_52657
import RHInBoxT_1d4000000_3999999d4000000_52657_52686
import RHInBoxT_1d4000000_3999999d4000000_52686_52714
import RHInBoxT_1d4000000_3999999d4000000_52714_52743
import RHInBoxT_1d4000000_3999999d4000000_210971d4_52771
import RHInBoxT_1d4000000_3999999d4000000_211083d4_52800
import RHInBoxT_1d4000000_3999999d4000000_52800_52829
import RHInBoxT_1d4000000_3999999d4000000_52829_52857
import RHInBoxT_1d4000000_3999999d4000000_52857_52886
import RHInBoxT_1d4000000_3999999d4000000_52886_52914
import RHInBoxT_1d4000000_3999999d4000000_52914_52943
import RHInBoxT_1d4000000_3999999d4000000_52943_52971
import RHInBoxT_1d4000000_3999999d4000000_52971_53000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h53000

/-- The 35-band NOMINAL partition of `[52000, 53000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 52000
  | 1 => 52029
  | 2 => 52057
  | 3 => 52086
  | 4 => 52114
  | 5 => 52143
  | 6 => 52171
  | 7 => 52200
  | 8 => 52229
  | 9 => 52257
  | 10 => 52286
  | 11 => 52314
  | 12 => 52343
  | 13 => 52371
  | 14 => 52400
  | 15 => 52429
  | 16 => 52457
  | 17 => 52486
  | 18 => 52514
  | 19 => 52543
  | 20 => 52571
  | 21 => 52600
  | 22 => 52629
  | 23 => 52657
  | 24 => 52686
  | 25 => 52714
  | 26 => 52743
  | 27 => 52771
  | 28 => 52800
  | 29 => 52829
  | 30 => 52857
  | 31 => 52886
  | 32 => 52914
  | 33 => 52943
  | 34 => 52971
  | 35 => 53000
  | _ => 53000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((52000:ℝ)) ≤ (52029); norm_num
  · show ((52029:ℝ)) ≤ (52057); norm_num
  · show ((52057:ℝ)) ≤ (52086); norm_num
  · show ((52086:ℝ)) ≤ (52114); norm_num
  · show ((52114:ℝ)) ≤ (52143); norm_num
  · show ((52143:ℝ)) ≤ (52171); norm_num
  · show ((52171:ℝ)) ≤ (52200); norm_num
  · show ((52200:ℝ)) ≤ (52229); norm_num
  · show ((52229:ℝ)) ≤ (52257); norm_num
  · show ((52257:ℝ)) ≤ (52286); norm_num
  · show ((52286:ℝ)) ≤ (52314); norm_num
  · show ((52314:ℝ)) ≤ (52343); norm_num
  · show ((52343:ℝ)) ≤ (52371); norm_num
  · show ((52371:ℝ)) ≤ (52400); norm_num
  · show ((52400:ℝ)) ≤ (52429); norm_num
  · show ((52429:ℝ)) ≤ (52457); norm_num
  · show ((52457:ℝ)) ≤ (52486); norm_num
  · show ((52486:ℝ)) ≤ (52514); norm_num
  · show ((52514:ℝ)) ≤ (52543); norm_num
  · show ((52543:ℝ)) ≤ (52571); norm_num
  · show ((52571:ℝ)) ≤ (52600); norm_num
  · show ((52600:ℝ)) ≤ (52629); norm_num
  · show ((52629:ℝ)) ≤ (52657); norm_num
  · show ((52657:ℝ)) ≤ (52686); norm_num
  · show ((52686:ℝ)) ≤ (52714); norm_num
  · show ((52714:ℝ)) ≤ (52743); norm_num
  · show ((52743:ℝ)) ≤ (52771); norm_num
  · show ((52771:ℝ)) ≤ (52800); norm_num
  · show ((52800:ℝ)) ≤ (52829); norm_num
  · show ((52829:ℝ)) ≤ (52857); norm_num
  · show ((52857:ℝ)) ≤ (52886); norm_num
  · show ((52886:ℝ)) ≤ (52914); norm_num
  · show ((52914:ℝ)) ≤ (52943); norm_num
  · show ((52943:ℝ)) ≤ (52971); norm_num
  · show ((52971:ℝ)) ≤ (53000); norm_num
  · show ((53000:ℝ)) ≤ (53000); norm_num
  · exact le_refl _

/-- The lower edges of the 35 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 52000
  | 1 => 52029
  | 2 => 52057
  | 3 => 52086
  | 4 => 208455 / 4
  | 5 => 52143
  | 6 => 208683 / 4
  | 7 => 52200
  | 8 => 52229
  | 9 => 52257
  | 10 => 52286
  | 11 => 209255 / 4
  | 12 => 52343
  | 13 => 52371
  | 14 => 52400
  | 15 => 209715 / 4
  | 16 => 52457
  | 17 => 52486
  | 18 => 52514
  | 19 => 52543
  | 20 => 52571
  | 21 => 52600
  | 22 => 52629
  | 23 => 52657
  | 24 => 52686
  | 25 => 52714
  | 26 => 210971 / 4
  | 27 => 211083 / 4
  | 28 => 52800
  | 29 => 52829
  | 30 => 52857
  | 31 => 52886
  | 32 => 52914
  | 33 => 52943
  | 34 => 52971
  | _ => 52971

/-- The upper edges of the 35 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 52029
  | 1 => 52057
  | 2 => 52086
  | 3 => 52114
  | 4 => 52143
  | 5 => 52171
  | 6 => 52200
  | 7 => 52229
  | 8 => 52257
  | 9 => 52286
  | 10 => 52314
  | 11 => 209373 / 4
  | 12 => 52371
  | 13 => 52400
  | 14 => 52429
  | 15 => 52457
  | 16 => 52486
  | 17 => 52514
  | 18 => 52543
  | 19 => 52571
  | 20 => 52600
  | 21 => 52629
  | 22 => 52657
  | 23 => 52686
  | 24 => 52714
  | 25 => 52743
  | 26 => 52771
  | 27 => 52800
  | 28 => 52829
  | 29 => 52857
  | 30 => 52886
  | 31 => 52914
  | 32 => 52943
  | 33 => 52971
  | 34 => 53000
  | _ => 53000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 35 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 53000` (`log 53000 ≤ 11`, `2.7^11 ≥ 53000`). -/
theorem haC_53000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 53000 := by
  have hlog : Real.log 53000 ≤ 11 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h11 : Real.exp 11 = (Real.exp 1) ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 11 ≤ (Real.exp 1) ^ 11 := pow_le_pow_left₀ (by norm_num) he1 11
    rw [h11]; nlinarith [hpow]
  have hpos : 0 < Real.log 53000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 53000
      ≤ (1 / 4000000) * 11 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[52000, 53000]` segment's band hypothesis: every band `i < 35` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 35 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 35 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[52000, 53000]` SEGMENT: every zero with `52000 ≤ Im ≤ 53000` is on the line. -/
theorem segment_52000_53000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 53000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (52000:ℝ) ≤ ρ.im → ρ.im ≤ 53000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 52000 53000 bndSeg 35 (by norm_num) bndSeg_mono rfl rfl haC_53000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 53000 via the HEIGHT CHAIN**: `[0,52000]` ∘ `[52000,53000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_53000_of_bands
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
    (hbands_49000 : AllZeros_h49000.BandHyp)
    (hbands_50000 : AllZeros_h50000.BandHyp)
    (hbands_51000 : AllZeros_h51000.BandHyp)
    (hbands_52000 : AllZeros_h52000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 53000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 53000 → ρ.re = 1 / 2 := by
  have hγ52000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 52000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 52000 53000
    (AllZeros_h52000.all_nontrivial_zeros_up_to_height_52000_of_bands
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
      hbands_49000
      hbands_50000
      hbands_51000
      hbands_52000
      hγ52000)
    (segment_52000_53000 hbands hγ)

end AllZeros_h53000
