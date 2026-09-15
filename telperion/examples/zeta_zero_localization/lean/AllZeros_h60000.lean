/-  Height-chain step: all nontrivial zeta zeros up to height 60000 on Re = 1/2 --
    `AllZeros_h59000` + a `[59000, 60000]` SEGMENT certificate (35 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h59000
import RHInBoxT_1d4000000_3999999d4000000_235999d4_59029
import RHInBoxT_1d4000000_3999999d4000000_59029_59057
import RHInBoxT_1d4000000_3999999d4000000_59057_59086
import RHInBoxT_1d4000000_3999999d4000000_59086_59114
import RHInBoxT_1d4000000_3999999d4000000_59114_59143
import RHInBoxT_1d4000000_3999999d4000000_59143_59171
import RHInBoxT_1d4000000_3999999d4000000_59171_59200
import RHInBoxT_1d4000000_3999999d4000000_236799d4_236917d4
import RHInBoxT_1d4000000_3999999d4000000_59229_59257
import RHInBoxT_1d4000000_3999999d4000000_59257_59286
import RHInBoxT_1d4000000_3999999d4000000_59286_59314
import RHInBoxT_1d4000000_3999999d4000000_59314_59343
import RHInBoxT_1d4000000_3999999d4000000_59343_59371
import RHInBoxT_1d4000000_3999999d4000000_59371_118801d2
import RHInBoxT_1d4000000_3999999d4000000_59400_59429
import RHInBoxT_1d4000000_3999999d4000000_237715d4_59457
import RHInBoxT_1d4000000_3999999d4000000_59457_59486
import RHInBoxT_1d4000000_3999999d4000000_59486_59514
import RHInBoxT_1d4000000_3999999d4000000_59514_59543
import RHInBoxT_1d4000000_3999999d4000000_59543_59571
import RHInBoxT_1d4000000_3999999d4000000_59571_59600
import RHInBoxT_1d4000000_3999999d4000000_59600_59629
import RHInBoxT_1d4000000_3999999d4000000_59629_59657
import RHInBoxT_1d4000000_3999999d4000000_59657_59686
import RHInBoxT_1d4000000_3999999d4000000_238743d4_59714
import RHInBoxT_1d4000000_3999999d4000000_238855d4_59743
import RHInBoxT_1d4000000_3999999d4000000_59743_59771
import RHInBoxT_1d4000000_3999999d4000000_59771_59800
import RHInBoxT_1d4000000_3999999d4000000_59800_59829
import RHInBoxT_1d4000000_3999999d4000000_239315d4_59857
import RHInBoxT_1d4000000_3999999d4000000_59857_59886
import RHInBoxT_1d4000000_3999999d4000000_239543d4_59914
import RHInBoxT_1d4000000_3999999d4000000_59914_59943
import RHInBoxT_1d4000000_3999999d4000000_239771d4_239885d4
import RHInBoxT_1d4000000_3999999d4000000_59971_60000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h60000

/-- The 35-band NOMINAL partition of `[59000, 60000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 59000
  | 1 => 59029
  | 2 => 59057
  | 3 => 59086
  | 4 => 59114
  | 5 => 59143
  | 6 => 59171
  | 7 => 59200
  | 8 => 59229
  | 9 => 59257
  | 10 => 59286
  | 11 => 59314
  | 12 => 59343
  | 13 => 59371
  | 14 => 59400
  | 15 => 59429
  | 16 => 59457
  | 17 => 59486
  | 18 => 59514
  | 19 => 59543
  | 20 => 59571
  | 21 => 59600
  | 22 => 59629
  | 23 => 59657
  | 24 => 59686
  | 25 => 59714
  | 26 => 59743
  | 27 => 59771
  | 28 => 59800
  | 29 => 59829
  | 30 => 59857
  | 31 => 59886
  | 32 => 59914
  | 33 => 59943
  | 34 => 59971
  | 35 => 60000
  | _ => 60000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((59000:ℝ)) ≤ (59029); norm_num
  · show ((59029:ℝ)) ≤ (59057); norm_num
  · show ((59057:ℝ)) ≤ (59086); norm_num
  · show ((59086:ℝ)) ≤ (59114); norm_num
  · show ((59114:ℝ)) ≤ (59143); norm_num
  · show ((59143:ℝ)) ≤ (59171); norm_num
  · show ((59171:ℝ)) ≤ (59200); norm_num
  · show ((59200:ℝ)) ≤ (59229); norm_num
  · show ((59229:ℝ)) ≤ (59257); norm_num
  · show ((59257:ℝ)) ≤ (59286); norm_num
  · show ((59286:ℝ)) ≤ (59314); norm_num
  · show ((59314:ℝ)) ≤ (59343); norm_num
  · show ((59343:ℝ)) ≤ (59371); norm_num
  · show ((59371:ℝ)) ≤ (59400); norm_num
  · show ((59400:ℝ)) ≤ (59429); norm_num
  · show ((59429:ℝ)) ≤ (59457); norm_num
  · show ((59457:ℝ)) ≤ (59486); norm_num
  · show ((59486:ℝ)) ≤ (59514); norm_num
  · show ((59514:ℝ)) ≤ (59543); norm_num
  · show ((59543:ℝ)) ≤ (59571); norm_num
  · show ((59571:ℝ)) ≤ (59600); norm_num
  · show ((59600:ℝ)) ≤ (59629); norm_num
  · show ((59629:ℝ)) ≤ (59657); norm_num
  · show ((59657:ℝ)) ≤ (59686); norm_num
  · show ((59686:ℝ)) ≤ (59714); norm_num
  · show ((59714:ℝ)) ≤ (59743); norm_num
  · show ((59743:ℝ)) ≤ (59771); norm_num
  · show ((59771:ℝ)) ≤ (59800); norm_num
  · show ((59800:ℝ)) ≤ (59829); norm_num
  · show ((59829:ℝ)) ≤ (59857); norm_num
  · show ((59857:ℝ)) ≤ (59886); norm_num
  · show ((59886:ℝ)) ≤ (59914); norm_num
  · show ((59914:ℝ)) ≤ (59943); norm_num
  · show ((59943:ℝ)) ≤ (59971); norm_num
  · show ((59971:ℝ)) ≤ (60000); norm_num
  · show ((60000:ℝ)) ≤ (60000); norm_num
  · exact le_refl _

/-- The lower edges of the 35 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 235999 / 4
  | 1 => 59029
  | 2 => 59057
  | 3 => 59086
  | 4 => 59114
  | 5 => 59143
  | 6 => 59171
  | 7 => 236799 / 4
  | 8 => 59229
  | 9 => 59257
  | 10 => 59286
  | 11 => 59314
  | 12 => 59343
  | 13 => 59371
  | 14 => 59400
  | 15 => 237715 / 4
  | 16 => 59457
  | 17 => 59486
  | 18 => 59514
  | 19 => 59543
  | 20 => 59571
  | 21 => 59600
  | 22 => 59629
  | 23 => 59657
  | 24 => 238743 / 4
  | 25 => 238855 / 4
  | 26 => 59743
  | 27 => 59771
  | 28 => 59800
  | 29 => 239315 / 4
  | 30 => 59857
  | 31 => 239543 / 4
  | 32 => 59914
  | 33 => 239771 / 4
  | 34 => 59971
  | _ => 59971

/-- The upper edges of the 35 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 59029
  | 1 => 59057
  | 2 => 59086
  | 3 => 59114
  | 4 => 59143
  | 5 => 59171
  | 6 => 59200
  | 7 => 236917 / 4
  | 8 => 59257
  | 9 => 59286
  | 10 => 59314
  | 11 => 59343
  | 12 => 59371
  | 13 => 118801 / 2
  | 14 => 59429
  | 15 => 59457
  | 16 => 59486
  | 17 => 59514
  | 18 => 59543
  | 19 => 59571
  | 20 => 59600
  | 21 => 59629
  | 22 => 59657
  | 23 => 59686
  | 24 => 59714
  | 25 => 59743
  | 26 => 59771
  | 27 => 59800
  | 28 => 59829
  | 29 => 59857
  | 30 => 59886
  | 31 => 59914
  | 32 => 59943
  | 33 => 239885 / 4
  | 34 => 60000
  | _ => 60000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 35 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 60000` (`log 60000 ≤ 12`, `2.7^12 ≥ 60000`). -/
theorem haC_60000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 60000 := by
  have hlog : Real.log 60000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 60000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 60000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[59000, 60000]` segment's band hypothesis: every band `i < 35` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 35 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 35 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[59000, 60000]` SEGMENT: every zero with `59000 ≤ Im ≤ 60000` is on the line. -/
theorem segment_59000_60000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 60000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (59000:ℝ) ≤ ρ.im → ρ.im ≤ 60000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 59000 60000 bndSeg 35 (by norm_num) bndSeg_mono rfl rfl haC_60000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 60000 via the HEIGHT CHAIN**: `[0,59000]` ∘ `[59000,60000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_60000_of_bands
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
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 60000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 60000 → ρ.re = 1 / 2 := by
  have hγ59000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 59000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 59000 60000
    (AllZeros_h59000.all_nontrivial_zeros_up_to_height_59000_of_bands
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
      hγ59000)
    (segment_59000_60000 hbands hγ)

end AllZeros_h60000
