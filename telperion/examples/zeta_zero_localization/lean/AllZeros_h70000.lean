/-  Height-chain step: all nontrivial zeta zeros up to height 70000 on Re = 1/2 --
    `AllZeros_h69000` + a `[69000, 70000]` SEGMENT certificate (35 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h69000
import RHInBoxT_1d4000000_3999999d4000000_69000_276117d4
import RHInBoxT_1d4000000_3999999d4000000_69029_69057
import RHInBoxT_1d4000000_3999999d4000000_69057_69086
import RHInBoxT_1d4000000_3999999d4000000_69086_138229d2
import RHInBoxT_1d4000000_3999999d4000000_69114_69143
import RHInBoxT_1d4000000_3999999d4000000_69143_69171
import RHInBoxT_1d4000000_3999999d4000000_276683d4_69200
import RHInBoxT_1d4000000_3999999d4000000_69200_276917d4
import RHInBoxT_1d4000000_3999999d4000000_69229_69257
import RHInBoxT_1d4000000_3999999d4000000_69257_69286
import RHInBoxT_1d4000000_3999999d4000000_69286_69314
import RHInBoxT_1d4000000_3999999d4000000_69314_69343
import RHInBoxT_1d4000000_3999999d4000000_69343_69371
import RHInBoxT_1d4000000_3999999d4000000_69371_69400
import RHInBoxT_1d4000000_3999999d4000000_69400_69429
import RHInBoxT_1d4000000_3999999d4000000_69429_69457
import RHInBoxT_1d4000000_3999999d4000000_277827d4_69486
import RHInBoxT_1d4000000_3999999d4000000_69486_69514
import RHInBoxT_1d4000000_3999999d4000000_69514_69543
import RHInBoxT_1d4000000_3999999d4000000_69543_69571
import RHInBoxT_1d4000000_3999999d4000000_69571_69600
import RHInBoxT_1d4000000_3999999d4000000_69600_69629
import RHInBoxT_1d4000000_3999999d4000000_69629_69657
import RHInBoxT_1d4000000_3999999d4000000_69657_69686
import RHInBoxT_1d4000000_3999999d4000000_69686_69714
import RHInBoxT_1d4000000_3999999d4000000_278855d4_69743
import RHInBoxT_1d4000000_3999999d4000000_69743_69771
import RHInBoxT_1d4000000_3999999d4000000_69771_69800
import RHInBoxT_1d4000000_3999999d4000000_69800_69829
import RHInBoxT_1d4000000_3999999d4000000_69829_69857
import RHInBoxT_1d4000000_3999999d4000000_69857_69886
import RHInBoxT_1d4000000_3999999d4000000_69886_69914
import RHInBoxT_1d4000000_3999999d4000000_69914_279773d4
import RHInBoxT_1d4000000_3999999d4000000_69943_69971
import RHInBoxT_1d4000000_3999999d4000000_69971_280001d4

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h70000

/-- The 35-band NOMINAL partition of `[69000, 70000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 69000
  | 1 => 69029
  | 2 => 69057
  | 3 => 69086
  | 4 => 69114
  | 5 => 69143
  | 6 => 69171
  | 7 => 69200
  | 8 => 69229
  | 9 => 69257
  | 10 => 69286
  | 11 => 69314
  | 12 => 69343
  | 13 => 69371
  | 14 => 69400
  | 15 => 69429
  | 16 => 69457
  | 17 => 69486
  | 18 => 69514
  | 19 => 69543
  | 20 => 69571
  | 21 => 69600
  | 22 => 69629
  | 23 => 69657
  | 24 => 69686
  | 25 => 69714
  | 26 => 69743
  | 27 => 69771
  | 28 => 69800
  | 29 => 69829
  | 30 => 69857
  | 31 => 69886
  | 32 => 69914
  | 33 => 69943
  | 34 => 69971
  | 35 => 70000
  | _ => 70000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((69000:ℝ)) ≤ (69029); norm_num
  · show ((69029:ℝ)) ≤ (69057); norm_num
  · show ((69057:ℝ)) ≤ (69086); norm_num
  · show ((69086:ℝ)) ≤ (69114); norm_num
  · show ((69114:ℝ)) ≤ (69143); norm_num
  · show ((69143:ℝ)) ≤ (69171); norm_num
  · show ((69171:ℝ)) ≤ (69200); norm_num
  · show ((69200:ℝ)) ≤ (69229); norm_num
  · show ((69229:ℝ)) ≤ (69257); norm_num
  · show ((69257:ℝ)) ≤ (69286); norm_num
  · show ((69286:ℝ)) ≤ (69314); norm_num
  · show ((69314:ℝ)) ≤ (69343); norm_num
  · show ((69343:ℝ)) ≤ (69371); norm_num
  · show ((69371:ℝ)) ≤ (69400); norm_num
  · show ((69400:ℝ)) ≤ (69429); norm_num
  · show ((69429:ℝ)) ≤ (69457); norm_num
  · show ((69457:ℝ)) ≤ (69486); norm_num
  · show ((69486:ℝ)) ≤ (69514); norm_num
  · show ((69514:ℝ)) ≤ (69543); norm_num
  · show ((69543:ℝ)) ≤ (69571); norm_num
  · show ((69571:ℝ)) ≤ (69600); norm_num
  · show ((69600:ℝ)) ≤ (69629); norm_num
  · show ((69629:ℝ)) ≤ (69657); norm_num
  · show ((69657:ℝ)) ≤ (69686); norm_num
  · show ((69686:ℝ)) ≤ (69714); norm_num
  · show ((69714:ℝ)) ≤ (69743); norm_num
  · show ((69743:ℝ)) ≤ (69771); norm_num
  · show ((69771:ℝ)) ≤ (69800); norm_num
  · show ((69800:ℝ)) ≤ (69829); norm_num
  · show ((69829:ℝ)) ≤ (69857); norm_num
  · show ((69857:ℝ)) ≤ (69886); norm_num
  · show ((69886:ℝ)) ≤ (69914); norm_num
  · show ((69914:ℝ)) ≤ (69943); norm_num
  · show ((69943:ℝ)) ≤ (69971); norm_num
  · show ((69971:ℝ)) ≤ (70000); norm_num
  · show ((70000:ℝ)) ≤ (70000); norm_num
  · exact le_refl _

/-- The lower edges of the 35 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 69000
  | 1 => 69029
  | 2 => 69057
  | 3 => 69086
  | 4 => 69114
  | 5 => 69143
  | 6 => 276683 / 4
  | 7 => 69200
  | 8 => 69229
  | 9 => 69257
  | 10 => 69286
  | 11 => 69314
  | 12 => 69343
  | 13 => 69371
  | 14 => 69400
  | 15 => 69429
  | 16 => 277827 / 4
  | 17 => 69486
  | 18 => 69514
  | 19 => 69543
  | 20 => 69571
  | 21 => 69600
  | 22 => 69629
  | 23 => 69657
  | 24 => 69686
  | 25 => 278855 / 4
  | 26 => 69743
  | 27 => 69771
  | 28 => 69800
  | 29 => 69829
  | 30 => 69857
  | 31 => 69886
  | 32 => 69914
  | 33 => 69943
  | 34 => 69971
  | _ => 69971

/-- The upper edges of the 35 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 276117 / 4
  | 1 => 69057
  | 2 => 69086
  | 3 => 138229 / 2
  | 4 => 69143
  | 5 => 69171
  | 6 => 69200
  | 7 => 276917 / 4
  | 8 => 69257
  | 9 => 69286
  | 10 => 69314
  | 11 => 69343
  | 12 => 69371
  | 13 => 69400
  | 14 => 69429
  | 15 => 69457
  | 16 => 69486
  | 17 => 69514
  | 18 => 69543
  | 19 => 69571
  | 20 => 69600
  | 21 => 69629
  | 22 => 69657
  | 23 => 69686
  | 24 => 69714
  | 25 => 69743
  | 26 => 69771
  | 27 => 69800
  | 28 => 69829
  | 29 => 69857
  | 30 => 69886
  | 31 => 69914
  | 32 => 279773 / 4
  | 33 => 69971
  | 34 => 280001 / 4
  | _ => 280001 / 4

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 35 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 70000` (`log 70000 ≤ 12`, `2.7^12 ≥ 70000`). -/
theorem haC_70000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 70000 := by
  have hlog : Real.log 70000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 70000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 70000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[69000, 70000]` segment's band hypothesis: every band `i < 35` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 35 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 35 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[69000, 70000]` SEGMENT: every zero with `69000 ≤ Im ≤ 70000` is on the line. -/
theorem segment_69000_70000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 70000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (69000:ℝ) ≤ ρ.im → ρ.im ≤ 70000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 69000 70000 bndSeg 35 (by norm_num) bndSeg_mono rfl rfl haC_70000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 70000 via the HEIGHT CHAIN**: `[0,69000]` ∘ `[69000,70000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_70000_of_bands
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
    (hbands_59000 : AllZeros_h59000.BandHyp)
    (hbands_60000 : AllZeros_h60000.BandHyp)
    (hbands_61000 : AllZeros_h61000.BandHyp)
    (hbands_62000 : AllZeros_h62000.BandHyp)
    (hbands_63000 : AllZeros_h63000.BandHyp)
    (hbands_64000 : AllZeros_h64000.BandHyp)
    (hbands_65000 : AllZeros_h65000.BandHyp)
    (hbands_66000 : AllZeros_h66000.BandHyp)
    (hbands_67000 : AllZeros_h67000.BandHyp)
    (hbands_68000 : AllZeros_h68000.BandHyp)
    (hbands_69000 : AllZeros_h69000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 70000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 70000 → ρ.re = 1 / 2 := by
  have hγ69000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 69000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 69000 70000
    (AllZeros_h69000.all_nontrivial_zeros_up_to_height_69000_of_bands
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
      hbands_59000
      hbands_60000
      hbands_61000
      hbands_62000
      hbands_63000
      hbands_64000
      hbands_65000
      hbands_66000
      hbands_67000
      hbands_68000
      hbands_69000
      hγ69000)
    (segment_69000_70000 hbands hγ)

end AllZeros_h70000
