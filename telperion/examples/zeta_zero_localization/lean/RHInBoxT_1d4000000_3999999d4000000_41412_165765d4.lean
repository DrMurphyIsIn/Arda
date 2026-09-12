/-  T5 TURING-BAND certificate for `[(1 / 4000000),(3999999 / 4000000)] x [41412,(165765 / 4)]` with `N = 41`:
    the RvM edge decomposition (no boundary winding integral, no in-strip edges).
    Emitted by telperion `emit_turing_band_instantiation`.
    Arb non-kernel inputs: `hLine` (41 on-line zeros) + `hArbT` (edge non-vanishing,
    confinement, five edge argument-change enclosures).  conjecture1_proved = False. -/
import Mathlib
import RHInBox
import TuringBand
import BoxLocalization

open Complex MeasureTheory Real
open scoped Topology

set_option maxHeartbeats 400000

namespace RHInBoxT_1d4000000_3999999d4000000_41412_165765d4

/-- Ball center covering the RvM rectangle `[-1,2] x [41412,(165765 / 4)]`. -/
noncomputable def cPB : ℂ := ⟨((1 / 2)), ((331413 / 8))⟩

noncomputable def RPB : ℝ := Real.sqrt ((13837 / 64))

theorem RPB_pos : (0 : ℝ) < RPB := Real.sqrt_pos.mpr (by norm_num)

theorem hs1PB : (1 : ℂ) ∉ Metric.ball cPB RPB := by
  rw [Metric.mem_ball, Complex.dist_eq_re_im]
  unfold cPB RPB
  intro hlt
  simp only [Complex.one_re, Complex.one_im] at hlt
  have hle : Real.sqrt ((13837 / 64)) ≤
      Real.sqrt (((1 : ℝ) - ((1 / 2))) ^ 2 + ((0 : ℝ) - ((331413 / 8))) ^ 2) :=
    Real.sqrt_le_sqrt (by norm_num)
  linarith [hlt, hle]

/-- **T5 band `[(1 / 4000000),(3999999 / 4000000)] x [41412,(165765 / 4)]`, `N = 41`** via the RvM edge decomposition.
    conjecture1_proved = False. -/
theorem rh_in_box_1d4000000_3999999d4000000_41412_165765d4
    (hLine : ∃ xs : List ℝ, xs.length = 41 ∧ xs.IsChain (· < ·) ∧
      (∀ t ∈ xs, ((41412) : ℝ) ≤ t ∧ t ≤ ((165765 / 4))) ∧
      (∀ t ∈ xs, completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0))
    (hArbT :
      (∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta (↑x + (((41412) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta (↑x + ((((165765 / 4)) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((41412) : ℝ) ((165765 / 4)), riemannZeta (((-1 : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ ρ ∈ RHInBoxAnalytic.zeroFinset cPB RPB hs1PB,
        (-1 : ℝ) < ρ.re ∧ ρ.re < 2 ∧ ((41412) : ℝ) < ρ.im ∧ ρ.im < ((165765 / 4))) ∧
      DiffractionCore.argChangeVert riemannZeta 2 (41412) ((165765 / 4)) ∈ Set.Icc ((103263636063 / 1000000000000) : ℝ) (3226988627 / 31250000000) ∧
      DiffractionCore.argChangeHoriz riemannZeta ((165765 / 4)) 2 (-1) ∈ Set.Icc ((305490137391 / 500000000000) : ℝ) (610980274783 / 1000000000000) ∧
      DiffractionCore.argChangeHoriz riemannZeta (41412) 2 (-1) ∈ Set.Icc ((425617940517 / 1000000000000) : ℝ) (212808970259 / 500000000000) ∧
      DiffractionCore.argChangeVert Gammaℝ (-1) (41412) ((165765 / 4)) ∈ Set.Icc ((128609354000377 / 1000000000000) : ℝ) (64304677000189 / 500000000000) ∧
      DiffractionCore.argChangeVert Gammaℝ 2 (41412) ((165765 / 4)) ∈ Set.Icc ((64304676993797 / 500000000000) : ℝ) (25721870797519 / 200000000000)) :
    (∀ ρ, ((((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) → (((41412) : ℝ) ≤ ρ.im ∧ ρ.im ≤ ((165765 / 4))) →
      riemannZeta ρ = 0 → ρ.re = 1 / 2) := by
  have hRpos : (0 : ℝ) < RPB := RPB_pos
  have hT0 : (0 : ℝ) < (41412) := by norm_num
  have hTle : ((41412) : ℝ) ≤ ((165765 / 4)) := by norm_num
  have hs0 : (-1 : ℝ) ≤ ((1 / 4000000)) := by norm_num
  have hs2 : (((3999999 / 4000000)) : ℝ) ≤ 2 := by norm_num
  have hbox_ball : ∀ ρ : ℂ, ((-1 : ℝ) ≤ ρ.re ∧ ρ.re ≤ 2) →
      (((41412) : ℝ) ≤ ρ.im ∧ ρ.im ≤ ((165765 / 4))) → ρ ∈ Metric.ball cPB RPB := by
    intro ρ hre him
    rw [Metric.mem_ball, Complex.dist_eq_re_im]
    unfold cPB RPB
    apply Real.sqrt_lt_sqrt (by positivity)
    have h1 := hre.1; have h2 := hre.2; have h3 := him.1; have h4 := him.2
    nlinarith [h1, h2, h3, h4, sq_nonneg (ρ.re - ((1 / 2))), sq_nonneg (ρ.im - ((331413 / 8)))]
  obtain ⟨xsL, hlen, hchain, hbnd, hzeros⟩ := hLine
  have hre_line : ∀ (t : ℝ), (1 / 2 + (t : ℂ) * Complex.I).re = 1 / 2 := by
    intro t
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]; norm_num
  have him_line : ∀ (t : ℝ), (1 / 2 + (t : ℂ) * Complex.I).im = t := by
    intro t
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]; norm_num
  have hzeta : ∀ (t : ℝ), completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0 →
      riemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0 :=
    fun t h => BoxLocalization.line_zeta_zero_of_completed h
  set T : Finset ℂ :=
    (xsL.map fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * Complex.I).toFinset with hTdef
  have hTcard : T.card = 41 := by
    rw [hTdef, RHInBox.line_toFinset_card xsL hchain, hlen]
  have hre_lo : (((1 / 4000000)) : ℝ) ≤ 1 / 2 := by norm_num
  have hre_hi : (1 / 2 : ℝ) ≤ ((3999999 / 4000000)) := by norm_num
  have hTline : ∀ z ∈ T, z.re = 1 / 2 := by
    rw [hTdef]
    exact RHInBox.line_toFinset_forall xsL (fun t _ => hre_line t)
  have hTzero : ∀ z ∈ T, riemannZeta z = 0 := by
    rw [hTdef]
    exact RHInBox.line_toFinset_forall xsL (fun t ht => hzeta t (hzeros t ht))
  have hTbox : ∀ z ∈ T, ((((1 / 4000000)) : ℝ) ≤ z.re ∧ z.re ≤ ((3999999 / 4000000))) ∧ (((41412) : ℝ) ≤ z.im ∧ z.im ≤ ((165765 / 4))) := by
    rw [hTdef]
    refine RHInBox.line_toFinset_forall xsL (fun t ht => ?_)
    exact ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩,
      by rw [him_line]; exact (hbnd t ht).1, by rw [him_line]; exact (hbnd t ht).2⟩
  obtain ⟨hnzb, hnzt, hnzl, hins, hAV2, hAHt, hAHb, hAG1, hAG2⟩ := hArbT
  have hN1 : 1 ≤ 41 := by norm_num
  have hpinL : 2 * 3.1416 * ((41 : ℝ) - 1) <
      2 * ((103263636063 / 1000000000000) : ℝ) + (305490137391 / 500000000000) - (212808970259 / 500000000000) + (128609354000377 / 1000000000000) + (64304676993797 / 500000000000) := by norm_num
  have hpinH : 2 * ((3226988627 / 31250000000) : ℝ) + (610980274783 / 1000000000000) - (425617940517 / 1000000000000) + (64304677000189 / 500000000000) + (25721870797519 / 200000000000) <
      2 * 3.14 * ((41 : ℝ) + 1) := by norm_num
  have hcountN : ((41 : ℕ) : ℤ) = (T.card : ℤ) := by rw [hTcard]
  exact TuringBand.turing_band_on_line (((1 / 4000000)) : ℝ) ((3999999 / 4000000)) (41412) ((165765 / 4)) hT0 hTle hs0 hs2
    cPB RPB hRpos 41 hN1
    (103263636063 / 1000000000000) (3226988627 / 31250000000) (305490137391 / 500000000000) (610980274783 / 1000000000000) (425617940517 / 1000000000000) (212808970259 / 500000000000) (128609354000377 / 1000000000000) (64304677000189 / 500000000000) (64304676993797 / 500000000000) (25721870797519 / 200000000000)
    hbox_ball hs1PB hnzb hnzt hnzl hins hAV2 hAHt hAHb hAG1 hAG2 hpinL hpinH
    T hTline hTzero hTbox hcountN

/-- Kernel statement-match gate: `rh_in_box_1d4000000_3999999d4000000_41412_165765d4` states EXACTLY the canonical
    `TuringBand.BandStatement` at this band's parameters (defeq).  -/
theorem statement_match :
    TuringBand.BandStatement (((1 / 4000000)) : ℝ) ((3999999 / 4000000)) (41412) ((165765 / 4)) 41
      (103263636063 / 1000000000000) (3226988627 / 31250000000) (305490137391 / 500000000000) (610980274783 / 1000000000000) (425617940517 / 1000000000000) (212808970259 / 500000000000)
      (128609354000377 / 1000000000000) (64304677000189 / 500000000000) (64304676993797 / 500000000000) (25721870797519 / 200000000000) cPB RPB hs1PB :=
  rh_in_box_1d4000000_3999999d4000000_41412_165765d4

end RHInBoxT_1d4000000_3999999d4000000_41412_165765d4
