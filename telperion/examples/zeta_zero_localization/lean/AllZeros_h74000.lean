/-  Height-chain step: all nontrivial zeta zeros up to height 74000 on Re = 1/2 --
    `AllZeros_h73000` + a `[73000, 74000]` SEGMENT certificate (36 bands, width 1/4000000)
    composed by `AllZerosUpToHeight.height_chain`.  INDEXED-hypothesis form
    (B1): one `BandHyp` per segment instead of per-band binders.
    Emitted by campaign.py.  conjecture1_proved = False. -/
import Mathlib
import DlvpZetaZeroFree
import DlvpZetaRateEffective
import ZetaZeroConfinement
import AllZerosUpToHeight
import AllZeros_h73000
import RHInBoxT_1d4000000_3999999d4000000_73000_73028
import RHInBoxT_1d4000000_3999999d4000000_292111d4_73056
import RHInBoxT_1d4000000_3999999d4000000_73056_292333d4
import RHInBoxT_1d4000000_3999999d4000000_73083_292445d4
import RHInBoxT_1d4000000_3999999d4000000_73111_73139
import RHInBoxT_1d4000000_3999999d4000000_292555d4_73167
import RHInBoxT_1d4000000_3999999d4000000_73167_73194
import RHInBoxT_1d4000000_3999999d4000000_73194_73222
import RHInBoxT_1d4000000_3999999d4000000_73222_73250
import RHInBoxT_1d4000000_3999999d4000000_73250_73278
import RHInBoxT_1d4000000_3999999d4000000_293111d4_73306
import RHInBoxT_1d4000000_3999999d4000000_73306_73333
import RHInBoxT_1d4000000_3999999d4000000_293331d4_73361
import RHInBoxT_1d4000000_3999999d4000000_293443d4_293557d4
import RHInBoxT_1d4000000_3999999d4000000_73389_293669d4
import RHInBoxT_1d4000000_3999999d4000000_73417_73444
import RHInBoxT_1d4000000_3999999d4000000_73444_73472
import RHInBoxT_1d4000000_3999999d4000000_73472_73500
import RHInBoxT_1d4000000_3999999d4000000_293999d4_73528
import RHInBoxT_1d4000000_3999999d4000000_73528_73556
import RHInBoxT_1d4000000_3999999d4000000_73556_73583
import RHInBoxT_1d4000000_3999999d4000000_73583_73611
import RHInBoxT_1d4000000_3999999d4000000_73611_294557d4
import RHInBoxT_1d4000000_3999999d4000000_73639_73667
import RHInBoxT_1d4000000_3999999d4000000_73667_73694
import RHInBoxT_1d4000000_3999999d4000000_73694_73722
import RHInBoxT_1d4000000_3999999d4000000_73722_73750
import RHInBoxT_1d4000000_3999999d4000000_73750_73778
import RHInBoxT_1d4000000_3999999d4000000_73778_73806
import RHInBoxT_1d4000000_3999999d4000000_73806_73833
import RHInBoxT_1d4000000_3999999d4000000_295331d4_73861
import RHInBoxT_1d4000000_3999999d4000000_73861_73889
import RHInBoxT_1d4000000_3999999d4000000_73889_73917
import RHInBoxT_1d4000000_3999999d4000000_295667d4_73944
import RHInBoxT_1d4000000_3999999d4000000_73944_73972
import RHInBoxT_1d4000000_3999999d4000000_73972_74000

open Complex MeasureTheory Real
open scoped Topology

namespace AllZeros_h74000

/-- The 36-band NOMINAL partition of `[73000, 74000]`. -/
noncomputable def bndSeg : ℕ → ℝ := fun i => match i with
  | 0 => 73000
  | 1 => 73028
  | 2 => 73056
  | 3 => 73083
  | 4 => 73111
  | 5 => 73139
  | 6 => 73167
  | 7 => 73194
  | 8 => 73222
  | 9 => 73250
  | 10 => 73278
  | 11 => 73306
  | 12 => 73333
  | 13 => 73361
  | 14 => 73389
  | 15 => 73417
  | 16 => 73444
  | 17 => 73472
  | 18 => 73500
  | 19 => 73528
  | 20 => 73556
  | 21 => 73583
  | 22 => 73611
  | 23 => 73639
  | 24 => 73667
  | 25 => 73694
  | 26 => 73722
  | 27 => 73750
  | 28 => 73778
  | 29 => 73806
  | 30 => 73833
  | 31 => 73861
  | 32 => 73889
  | 33 => 73917
  | 34 => 73944
  | 35 => 73972
  | 36 => 74000
  | _ => 74000

theorem bndSeg_mono : Monotone bndSeg := by
  refine monotone_nat_of_le_succ ?_
  intro nn
  rcases nn with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | nn
  · show ((73000:ℝ)) ≤ (73028); norm_num
  · show ((73028:ℝ)) ≤ (73056); norm_num
  · show ((73056:ℝ)) ≤ (73083); norm_num
  · show ((73083:ℝ)) ≤ (73111); norm_num
  · show ((73111:ℝ)) ≤ (73139); norm_num
  · show ((73139:ℝ)) ≤ (73167); norm_num
  · show ((73167:ℝ)) ≤ (73194); norm_num
  · show ((73194:ℝ)) ≤ (73222); norm_num
  · show ((73222:ℝ)) ≤ (73250); norm_num
  · show ((73250:ℝ)) ≤ (73278); norm_num
  · show ((73278:ℝ)) ≤ (73306); norm_num
  · show ((73306:ℝ)) ≤ (73333); norm_num
  · show ((73333:ℝ)) ≤ (73361); norm_num
  · show ((73361:ℝ)) ≤ (73389); norm_num
  · show ((73389:ℝ)) ≤ (73417); norm_num
  · show ((73417:ℝ)) ≤ (73444); norm_num
  · show ((73444:ℝ)) ≤ (73472); norm_num
  · show ((73472:ℝ)) ≤ (73500); norm_num
  · show ((73500:ℝ)) ≤ (73528); norm_num
  · show ((73528:ℝ)) ≤ (73556); norm_num
  · show ((73556:ℝ)) ≤ (73583); norm_num
  · show ((73583:ℝ)) ≤ (73611); norm_num
  · show ((73611:ℝ)) ≤ (73639); norm_num
  · show ((73639:ℝ)) ≤ (73667); norm_num
  · show ((73667:ℝ)) ≤ (73694); norm_num
  · show ((73694:ℝ)) ≤ (73722); norm_num
  · show ((73722:ℝ)) ≤ (73750); norm_num
  · show ((73750:ℝ)) ≤ (73778); norm_num
  · show ((73778:ℝ)) ≤ (73806); norm_num
  · show ((73806:ℝ)) ≤ (73833); norm_num
  · show ((73833:ℝ)) ≤ (73861); norm_num
  · show ((73861:ℝ)) ≤ (73889); norm_num
  · show ((73889:ℝ)) ≤ (73917); norm_num
  · show ((73917:ℝ)) ≤ (73944); norm_num
  · show ((73944:ℝ)) ≤ (73972); norm_num
  · show ((73972:ℝ)) ≤ (74000); norm_num
  · show ((74000:ℝ)) ≤ (74000); norm_num
  · exact le_refl _

/-- The lower edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bLo : ℕ → ℝ := fun i => match i with
  | 0 => 73000
  | 1 => 292111 / 4
  | 2 => 73056
  | 3 => 73083
  | 4 => 73111
  | 5 => 292555 / 4
  | 6 => 73167
  | 7 => 73194
  | 8 => 73222
  | 9 => 73250
  | 10 => 293111 / 4
  | 11 => 73306
  | 12 => 293331 / 4
  | 13 => 293443 / 4
  | 14 => 73389
  | 15 => 73417
  | 16 => 73444
  | 17 => 73472
  | 18 => 293999 / 4
  | 19 => 73528
  | 20 => 73556
  | 21 => 73583
  | 22 => 73611
  | 23 => 73639
  | 24 => 73667
  | 25 => 73694
  | 26 => 73722
  | 27 => 73750
  | 28 => 73778
  | 29 => 73806
  | 30 => 295331 / 4
  | 31 => 73861
  | 32 => 73889
  | 33 => 295667 / 4
  | 34 => 73944
  | 35 => 73972
  | _ => 73972

/-- The upper edges of the 36 STRETCHED certificate boxes. -/
noncomputable def bHi : ℕ → ℝ := fun i => match i with
  | 0 => 73028
  | 1 => 73056
  | 2 => 292333 / 4
  | 3 => 292445 / 4
  | 4 => 73139
  | 5 => 73167
  | 6 => 73194
  | 7 => 73222
  | 8 => 73250
  | 9 => 73278
  | 10 => 73306
  | 11 => 73333
  | 12 => 73361
  | 13 => 293557 / 4
  | 14 => 293669 / 4
  | 15 => 73444
  | 16 => 73472
  | 17 => 73500
  | 18 => 73528
  | 19 => 73556
  | 20 => 73583
  | 21 => 73611
  | 22 => 294557 / 4
  | 23 => 73667
  | 24 => 73694
  | 25 => 73722
  | 26 => 73750
  | 27 => 73778
  | 28 => 73806
  | 29 => 73833
  | 30 => 73861
  | 31 => 73889
  | 32 => 73917
  | 33 => 73944
  | 34 => 73972
  | 35 => 74000
  | _ => 74000

/-- Each nominal band `[bndSeg i, bndSeg (i+1)]` sits inside the stretched
    certificate box `[bLo i, bHi i]`. -/
theorem hcover : ∀ i, i < 36 → bLo i ≤ bndSeg i ∧ bndSeg (i + 1) ≤ bHi i := by
  intro i hi
  interval_cases i <;>
    exact ⟨by norm_num [bLo, bndSeg], by norm_num [bndSeg, bHi]⟩

/-- `1/4000000 ≤ dlvpRateC / log 74000` (`log 74000 ≤ 12`, `2.7^12 ≥ 74000`). -/
theorem haC_74000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 74000 := by
  have hlog : Real.log 74000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 74000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 74000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

/-- The `[73000, 74000]` segment's band hypothesis: every band `i < 36` certifies
    its STRETCHED box `[bLo i, bHi i]`.  One binder replaces the 36 per-band
    hypotheses; the previous capstone consumes one such predicate per segment. -/
def BandHyp : Prop :=
  ∀ i, i < 36 → ∀ ρ : ℂ, (((1 / 4000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3999999 / 4000000)) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- The `[73000, 74000]` SEGMENT: every zero with `73000 ≤ Im ≤ 74000` is on the line. -/
theorem segment_73000_74000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 74000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (73000:ℝ) ≤ ρ.im → ρ.im ≤ 74000 → ρ.re = 1 / 2 := by
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  refine AllZerosUpToHeight.all_nontrivial_zeros_in_segment_on_line
    (1 / 4000000) 73000 74000 bndSeg 36 (by norm_num) bndSeg_mono rfl rfl haC_74000
    (by norm_num) (by norm_num) ?_ hγ
  intro i hi ρ hre him hz
  have hre' : (((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999 / 4000000 := by
    refine ⟨hre.1, ?_⟩
    have h2 := hre.2
    linarith [h2, hre_eq]
  obtain ⟨hcov1, hcov2⟩ := hcover i hi
  exact hbands i hi ρ hre'
    ⟨le_trans hcov1 him.1, le_trans him.2 hcov2⟩ hz

/-- **T = 74000 via the HEIGHT CHAIN**: `[0,73000]` ∘ `[73000,74000]` (segment).
    One `BandHyp` binder per segment (indexed form).  conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_74000_of_bands
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
    (hbands_70000 : AllZeros_h70000.BandHyp)
    (hbands_71000 : AllZeros_h71000.BandHyp)
    (hbands_72000 : AllZeros_h72000.BandHyp)
    (hbands_73000 : AllZeros_h73000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 74000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 74000 → ρ.re = 1 / 2 := by
  have hγ73000 : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 73000 → 55 / 16 ≤ |ρ.im| :=
    fun ρ hz h0 h2 => hγ ρ hz h0 (le_trans h2 (by norm_num))
  exact AllZerosUpToHeight.height_chain 73000 74000
    (AllZeros_h73000.all_nontrivial_zeros_up_to_height_73000_of_bands
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
      hbands_70000
      hbands_71000
      hbands_72000
      hbands_73000
      hγ73000)
    (segment_73000_74000 hbands hγ)

end AllZeros_h74000
