/-  T5 TURING-BAND certificate for `[(1 / 4000000),(3999999 / 4000000)] x [115079,115105]` with `N = 40`:
    the RvM edge decomposition (no boundary winding integral, no in-strip edges).
    Emitted by telperion `emit_turing_band_instantiation`.
    Arb non-kernel inputs: `hLine` (40 on-line zeros) + `hArbT` (edge non-vanishing,
    confinement, five edge argument-change enclosures).  conjecture1_proved = False. -/
import Mathlib
import RHInBox
import TuringBand
import BoxLocalization

open Complex MeasureTheory Real
open scoped Topology

set_option maxHeartbeats 400000

namespace RHInBoxT_1d4000000_3999999d4000000_115079_115105

/-- Ball center covering the RvM rectangle `[-1,2] x [115079,115105]`. -/
noncomputable def cPB : ℂ := ⟨((1 / 2)), (115092)⟩

noncomputable def RPB : ℝ := Real.sqrt ((2741 / 16))

theorem RPB_pos : (0 : ℝ) < RPB := Real.sqrt_pos.mpr (by norm_num)

theorem hs1PB : (1 : ℂ) ∉ Metric.ball cPB RPB := by
  rw [Metric.mem_ball, Complex.dist_eq_re_im]
  unfold cPB RPB
  intro hlt
  simp only [Complex.one_re, Complex.one_im] at hlt
  have hle : Real.sqrt ((2741 / 16)) ≤
      Real.sqrt (((1 : ℝ) - ((1 / 2))) ^ 2 + ((0 : ℝ) - (115092)) ^ 2) :=
    Real.sqrt_le_sqrt (by norm_num)
  linarith [hlt, hle]

/-- **T5 band `[(1 / 4000000),(3999999 / 4000000)] x [115079,115105]`, `N = 40`** via the RvM edge decomposition.
    conjecture1_proved = False. -/
theorem rh_in_box_1d4000000_3999999d4000000_115079_115105
    (hLine : ∃ xs : List ℝ, xs.length = 40 ∧ xs.IsChain (· < ·) ∧
      (∀ t ∈ xs, ((115079) : ℝ) ≤ t ∧ t ≤ (115105)) ∧
      (∀ t ∈ xs, completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0))
    (hArbT :
      (∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta (↑x + (((115079) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta (↑x + (((115105) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((115079) : ℝ) (115105), riemannZeta (((-1 : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ ρ ∈ RHInBoxAnalytic.zeroFinset cPB RPB hs1PB,
        (-1 : ℝ) < ρ.re ∧ ρ.re < 2 ∧ ((115079) : ℝ) < ρ.im ∧ ρ.im < (115105)) ∧
      DiffractionCore.argChangeVert riemannZeta 2 (115079) (115105) ∈ Set.Icc ((-62153324263 / 1000000000000) : ℝ) (-31076662131 / 500000000000) ∧
      DiffractionCore.argChangeHoriz riemannZeta (115105) 2 (-1) ∈ Set.Icc ((-84646137697 / 20000000000) : ℝ) (-4232306884849 / 1000000000000) ∧
      DiffractionCore.argChangeHoriz riemannZeta (115079) 2 (-1) ∈ Set.Icc ((-478165324947 / 1000000000000) : ℝ) (-239082662473 / 500000000000) ∧
      DiffractionCore.argChangeVert Gammaℝ (-1) (115079) (115105) ∈ Set.Icc ((127602930248541 / 1000000000000) : ℝ) (63801465124271 / 500000000000) ∧
      DiffractionCore.argChangeVert Gammaℝ 2 (115079) (115105) ∈ Set.Icc ((127602930247069 / 1000000000000) : ℝ) (12760293024707 / 100000000000)) :
    (∀ ρ, ((((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) → (((115079) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (115105)) →
      riemannZeta ρ = 0 → ρ.re = 1 / 2) := by
  have hRpos : (0 : ℝ) < RPB := RPB_pos
  have hT0 : (0 : ℝ) < (115079) := by norm_num
  have hTle : ((115079) : ℝ) ≤ (115105) := by norm_num
  have hs0 : (-1 : ℝ) ≤ ((1 / 4000000)) := by norm_num
  have hs2 : (((3999999 / 4000000)) : ℝ) ≤ 2 := by norm_num
  have hbox_ball : ∀ ρ : ℂ, ((-1 : ℝ) ≤ ρ.re ∧ ρ.re ≤ 2) →
      (((115079) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (115105)) → ρ ∈ Metric.ball cPB RPB := by
    intro ρ hre him
    rw [Metric.mem_ball, Complex.dist_eq_re_im]
    unfold cPB RPB
    apply Real.sqrt_lt_sqrt (by positivity)
    have h1 := hre.1; have h2 := hre.2; have h3 := him.1; have h4 := him.2
    nlinarith [h1, h2, h3, h4, sq_nonneg (ρ.re - ((1 / 2))), sq_nonneg (ρ.im - (115092))]
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
  have hTcard : T.card = 40 := by
    rw [hTdef, RHInBox.line_toFinset_card xsL hchain, hlen]
  have hre_lo : (((1 / 4000000)) : ℝ) ≤ 1 / 2 := by norm_num
  have hre_hi : (1 / 2 : ℝ) ≤ ((3999999 / 4000000)) := by norm_num
  have hTline : ∀ z ∈ T, z.re = 1 / 2 := by
    rw [hTdef]
    exact RHInBox.line_toFinset_forall xsL (fun t _ => hre_line t)
  have hTzero : ∀ z ∈ T, riemannZeta z = 0 := by
    rw [hTdef]
    exact RHInBox.line_toFinset_forall xsL (fun t ht => hzeta t (hzeros t ht))
  have hTbox : ∀ z ∈ T, ((((1 / 4000000)) : ℝ) ≤ z.re ∧ z.re ≤ ((3999999 / 4000000))) ∧ (((115079) : ℝ) ≤ z.im ∧ z.im ≤ (115105)) := by
    rw [hTdef]
    refine RHInBox.line_toFinset_forall xsL (fun t ht => ?_)
    exact ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩,
      by rw [him_line]; exact (hbnd t ht).1, by rw [him_line]; exact (hbnd t ht).2⟩
  obtain ⟨hnzb, hnzt, hnzl, hins, hAV2, hAHt, hAHb, hAG1, hAG2⟩ := hArbT
  have hN1 : 1 ≤ 40 := by norm_num
  have hpinL : 2 * 3.1416 * ((40 : ℝ) - 1) <
      2 * ((-62153324263 / 1000000000000) : ℝ) + (-84646137697 / 20000000000) - (-239082662473 / 500000000000) + (127602930248541 / 1000000000000) + (127602930247069 / 1000000000000) := by norm_num
  have hpinH : 2 * ((-31076662131 / 500000000000) : ℝ) + (-4232306884849 / 1000000000000) - (-478165324947 / 1000000000000) + (63801465124271 / 500000000000) + (12760293024707 / 100000000000) <
      2 * 3.14 * ((40 : ℝ) + 1) := by norm_num
  have hcountN : ((40 : ℕ) : ℤ) = (T.card : ℤ) := by rw [hTcard]
  exact TuringBand.turing_band_on_line (((1 / 4000000)) : ℝ) ((3999999 / 4000000)) (115079) (115105) hT0 hTle hs0 hs2
    cPB RPB hRpos 40 hN1
    (-62153324263 / 1000000000000) (-31076662131 / 500000000000) (-84646137697 / 20000000000) (-4232306884849 / 1000000000000) (-478165324947 / 1000000000000) (-239082662473 / 500000000000) (127602930248541 / 1000000000000) (63801465124271 / 500000000000) (127602930247069 / 1000000000000) (12760293024707 / 100000000000)
    hbox_ball hs1PB hnzb hnzt hnzl hins hAV2 hAHt hAHb hAG1 hAG2 hpinL hpinH
    T hTline hTzero hTbox hcountN

/-- Kernel statement-match gate: `rh_in_box_1d4000000_3999999d4000000_115079_115105` states EXACTLY the canonical
    `TuringBand.BandStatement` at this band's parameters (defeq).  -/
theorem statement_match :
    TuringBand.BandStatement (((1 / 4000000)) : ℝ) ((3999999 / 4000000)) (115079) (115105) 40
      (-62153324263 / 1000000000000) (-31076662131 / 500000000000) (-84646137697 / 20000000000) (-4232306884849 / 1000000000000) (-478165324947 / 1000000000000) (-239082662473 / 500000000000)
      (127602930248541 / 1000000000000) (63801465124271 / 500000000000) (127602930247069 / 1000000000000) (12760293024707 / 100000000000) cPB RPB hs1PB :=
  rh_in_box_1d4000000_3999999d4000000_115079_115105

end RHInBoxT_1d4000000_3999999d4000000_115079_115105
