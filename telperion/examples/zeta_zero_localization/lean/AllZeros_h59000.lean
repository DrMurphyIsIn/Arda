/-  Height-chain step: all nontrivial zeta zeros up to height 59000 on Re = 1/2 --
    `AllZeros_h58000` + a `[58000, 59000]` SEGMENT certificate (35 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h58000
import RHInBoxT_1d4000000_3999999d4000000_58000_58029
import RHInBoxT_1d4000000_3999999d4000000_58029_232229d4
import RHInBoxT_1d4000000_3999999d4000000_58057_58086
import RHInBoxT_1d4000000_3999999d4000000_58086_232457d4
import RHInBoxT_1d4000000_3999999d4000000_58114_58143
import RHInBoxT_1d4000000_3999999d4000000_58143_58171
import RHInBoxT_1d4000000_3999999d4000000_58171_58200
import RHInBoxT_1d4000000_3999999d4000000_58200_232917d4
import RHInBoxT_1d4000000_3999999d4000000_58229_58257
import RHInBoxT_1d4000000_3999999d4000000_58257_58286
import RHInBoxT_1d4000000_3999999d4000000_58286_58314
import RHInBoxT_1d4000000_3999999d4000000_58314_58343
import RHInBoxT_1d4000000_3999999d4000000_58343_58371
import RHInBoxT_1d4000000_3999999d4000000_58371_58400
import RHInBoxT_1d4000000_3999999d4000000_58400_58429
import RHInBoxT_1d4000000_3999999d4000000_233715d4_58457
import RHInBoxT_1d4000000_3999999d4000000_58457_58486
import RHInBoxT_1d4000000_3999999d4000000_58486_58514
import RHInBoxT_1d4000000_3999999d4000000_58514_58543
import RHInBoxT_1d4000000_3999999d4000000_58543_58571
import RHInBoxT_1d4000000_3999999d4000000_58571_58600
import RHInBoxT_1d4000000_3999999d4000000_58600_58629
import RHInBoxT_1d4000000_3999999d4000000_58629_58657
import RHInBoxT_1d4000000_3999999d4000000_58657_58686
import RHInBoxT_1d4000000_3999999d4000000_58686_58714
import RHInBoxT_1d4000000_3999999d4000000_58714_58743
import RHInBoxT_1d4000000_3999999d4000000_58743_58771
import RHInBoxT_1d4000000_3999999d4000000_58771_58800
import RHInBoxT_1d4000000_3999999d4000000_58800_58829
import RHInBoxT_1d4000000_3999999d4000000_58829_58857
import RHInBoxT_1d4000000_3999999d4000000_58857_58886
import RHInBoxT_1d4000000_3999999d4000000_58886_58914
import RHInBoxT_1d4000000_3999999d4000000_58914_58943
import RHInBoxT_1d4000000_3999999d4000000_58943_58971
import RHInBoxT_1d4000000_3999999d4000000_58971_59000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h59000

/-- The 35-band NOMINAL partition of `[58000, 59000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 58000
  | 1 => 58029
  | 2 => 58057
  | 3 => 58086
  | 4 => 58114
  | 5 => 58143
  | 6 => 58171
  | 7 => 58200
  | 8 => 58229
  | 9 => 58257
  | 10 => 58286
  | 11 => 58314
  | 12 => 58343
  | 13 => 58371
  | 14 => 58400
  | 15 => 58429
  | 16 => 58457
  | 17 => 58486
  | 18 => 58514
  | 19 => 58543
  | 20 => 58571
  | 21 => 58600
  | 22 => 58629
  | 23 => 58657
  | 24 => 58686
  | 25 => 58714
  | 26 => 58743
  | 27 => 58771
  | 28 => 58800
  | 29 => 58829
  | 30 => 58857
  | 31 => 58886
  | 32 => 58914
  | 33 => 58943
  | 34 => 58971
  | 35 => 59000
  | _ => 59000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((58000:ℝ)) ≤ (58029); norm_num
  · show ((58029:ℝ)) ≤ (58057); norm_num
  · show ((58057:ℝ)) ≤ (58086); norm_num
  · show ((58086:ℝ)) ≤ (58114); norm_num
  · show ((58114:ℝ)) ≤ (58143); norm_num
  · show ((58143:ℝ)) ≤ (58171); norm_num
  · show ((58171:ℝ)) ≤ (58200); norm_num
  · show ((58200:ℝ)) ≤ (58229); norm_num
  · show ((58229:ℝ)) ≤ (58257); norm_num
  · show ((58257:ℝ)) ≤ (58286); norm_num
  · show ((58286:ℝ)) ≤ (58314); norm_num
  · show ((58314:ℝ)) ≤ (58343); norm_num
  · show ((58343:ℝ)) ≤ (58371); norm_num
  · show ((58371:ℝ)) ≤ (58400); norm_num
  · show ((58400:ℝ)) ≤ (58429); norm_num
  · show ((58429:ℝ)) ≤ (58457); norm_num
  · show ((58457:ℝ)) ≤ (58486); norm_num
  · show ((58486:ℝ)) ≤ (58514); norm_num
  · show ((58514:ℝ)) ≤ (58543); norm_num
  · show ((58543:ℝ)) ≤ (58571); norm_num
  · show ((58571:ℝ)) ≤ (58600); norm_num
  · show ((58600:ℝ)) ≤ (58629); norm_num
  · show ((58629:ℝ)) ≤ (58657); norm_num
  · show ((58657:ℝ)) ≤ (58686); norm_num
  · show ((58686:ℝ)) ≤ (58714); norm_num
  · show ((58714:ℝ)) ≤ (58743); norm_num
  · show ((58743:ℝ)) ≤ (58771); norm_num
  · show ((58771:ℝ)) ≤ (58800); norm_num
  · show ((58800:ℝ)) ≤ (58829); norm_num
  · show ((58829:ℝ)) ≤ (58857); norm_num
  · show ((58857:ℝ)) ≤ (58886); norm_num
  · show ((58886:ℝ)) ≤ (58914); norm_num
  · show ((58914:ℝ)) ≤ (58943); norm_num
  · show ((58943:ℝ)) ≤ (58971); norm_num
  · show ((58971:ℝ)) ≤ (59000); norm_num
  · show ((59000:ℝ)) ≤ (59000); norm_num
  · exact le_refl _

/-- The lower edges of the 35 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 58000
  | 1 => 58029
  | 2 => 58057
  | 3 => 58086
  | 4 => 58114
  | 5 => 58143
  | 6 => 58171
  | 7 => 58200
  | 8 => 58229
  | 9 => 58257
  | 10 => 58286
  | 11 => 58314
  | 12 => 58343
  | 13 => 58371
  | 14 => 58400
  | 15 => 233715 / 4
  | 16 => 58457
  | 17 => 58486
  | 18 => 58514
  | 19 => 58543
  | 20 => 58571
  | 21 => 58600
  | 22 => 58629
  | 23 => 58657
  | 24 => 58686
  | 25 => 58714
  | 26 => 58743
  | 27 => 58771
  | 28 => 58800
  | 29 => 58829
  | 30 => 58857
  | 31 => 58886
  | 32 => 58914
  | 33 => 58943
  | 34 => 58971
  | _ => 58971

/-- The upper edges of the 35 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 58029
  | 1 => 232229 / 4
  | 2 => 58086
  | 3 => 232457 / 4
  | 4 => 58143
  | 5 => 58171
  | 6 => 58200
  | 7 => 232917 / 4
  | 8 => 58257
  | 9 => 58286
  | 10 => 58314
  | 11 => 58343
  | 12 => 58371
  | 13 => 58400
  | 14 => 58429
  | 15 => 58457
  | 16 => 58486
  | 17 => 58514
  | 18 => 58543
  | 19 => 58571
  | 20 => 58600
  | 21 => 58629
  | 22 => 58657
  | 23 => 58686
  | 24 => 58714
  | 25 => 58743
  | 26 => 58771
  | 27 => 58800
  | 28 => 58829
  | 29 => 58857
  | 30 => 58886
  | 31 => 58914
  | 32 => 58943
  | 33 => 58971
  | 34 => 59000
  | _ => 59000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 35 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 59000` (`log 59000 ≤ 12`, `2.7^12 ≥ 59000`). -/
theorem haC_59000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 59000 := by
  have hlog : Real.log 59000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 59000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 59000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[58000, 59000]` segment's band hypothesis: every band `i < 35` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 35 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 35 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[58000, 59000]` SEGMENT: every zero with `58000 ≤ Im ≤ 59000` is on the line. -/
theorem segment_58000_59000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 59000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (58000:ℝ) ≤ ρ.im → ρ.im ≤ 59000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 58000 59000 bndSeg 35 (by norm_num) bndSeg_mono rfl rfl haC_59000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 59000 via the HEIGHT CHAIN**: `[0,58000]` ∘ `[58000,59000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_59000_of_bands
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
    (hbands_53000 : AllZeros_h53000.BandHyp)
    (hbands_54000 : AllZeros_h54000.BandHyp)
    (hbands_55000 : AllZeros_h55000.BandHyp)
    (hbands_56000 : AllZeros_h56000.BandHyp)
    (hbands_57000 : AllZeros_h57000.BandHyp)
    (hbands_58000 : AllZeros_h58000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 59000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 59000 → ρ.re = 1 / 2 := by
  have hγ58000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 58000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 58000 59000
    (AllZeros_h58000.all_nontrivial_zeros_up_to_height_58000_of_bands
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
      hbands_53000
      hbands_54000
      hbands_55000
      hbands_56000
      hbands_57000
      hbands_58000
      hγ58000)
    (segment_58000_59000 hbands hγ)

end AllZeros_h59000
