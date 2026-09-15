/-  T5 TURING-BAND certificate for `[(1 / 4000000),(3999999 / 4000000)] x [435048,435071]` with `N = 41`:
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

namespace RHInBoxT_1d4000000_3999999d4000000_435048_435071

/-- Ball center covering the RvM rectangle `[-1,2] x [435048,435071]`. -/
noncomputable def cPB : ℂ := ⟨((1 / 2)), ((870119 / 2))⟩

noncomputable def RPB : ℝ := Real.sqrt ((2153 / 16))

theorem RPB_pos : (0 : ℝ) < RPB := Real.sqrt_pos.mpr (by norm_num)

theorem hs1PB : (1 : ℂ) ∉ Metric.ball cPB RPB := by
  rw [Metric.mem_ball, Complex.dist_eq_re_im]
  unfold cPB RPB
  intro hlt
  simp only [Complex.one_re, Complex.one_im] at hlt
  have hle : Real.sqrt ((2153 / 16)) ≤
      Real.sqrt (((1 : ℝ) - ((1 / 2))) ^ 2 + ((0 : ℝ) - ((870119 / 2))) ^ 2) :=
    Real.sqrt_le_sqrt (by norm_num)
  linarith [hlt, hle]

/-- **T5 band `[(1 / 4000000),(3999999 / 4000000)] x [435048,435071]`, `N = 41`** via the RvM edge decomposition.
    conjecture1_proved = False. -/
theorem rh_in_box_1d4000000_3999999d4000000_435048_435071
    (hLine : ∃ xs : List ℝ, xs.length = 41 ∧ xs.IsChain (· < ·) ∧
      (∀ t ∈ xs, ((435048) : ℝ) ≤ t ∧ t ≤ (435071)) ∧
      (∀ t ∈ xs, completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0))
    (hArbT :
      (∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta (↑x + (((435048) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta (↑x + (((435071) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((435048) : ℝ) (435071), riemannZeta (((-1 : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ ρ ∈ RHInBoxAnalytic.zeroFinset cPB RPB hs1PB,
        (-1 : ℝ) < ρ.re ∧ ρ.re < 2 ∧ ((435048) : ℝ) < ρ.im ∧ ρ.im < (435071)) ∧
      DiffractionCore.argChangeVert riemannZeta 2 (435048) (435071) ∈ Set.Icc ((-10006973191 / 40000000000) : ℝ) (-125087164887 / 500000000000) ∧
      DiffractionCore.argChangeHoriz riemannZeta (435071) 2 (-1) ∈ Set.Icc ((4193500911 / 100000000000) : ℝ) (41935009111 / 1000000000000) ∧
      DiffractionCore.argChangeHoriz riemannZeta (435048) 2 (-1) ∈ Set.Icc ((-1725707881259 / 1000000000000) : ℝ) (-862853940629 / 500000000000) ∧
      DiffractionCore.argChangeVert Gammaℝ (-1) (435048) (435071) ∈ Set.Icc ((16021456460227 / 125000000000) : ℝ) (128171651681817 / 1000000000000) ∧
      DiffractionCore.argChangeVert Gammaℝ 2 (435048) (435071) ∈ Set.Icc ((5126866067269 / 40000000000) : ℝ) (64085825840863 / 500000000000)) :
    (∀ ρ, ((((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) → (((435048) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (435071)) →
      riemannZeta ρ = 0 → ρ.re = 1 / 2) := by
  have hRpos : (0 : ℝ) < RPB := RPB_pos
  have hT0 : (0 : ℝ) < (435048) := by norm_num
  have hTle : ((435048) : ℝ) ≤ (435071) := by norm_num
  have hs0 : (-1 : ℝ) ≤ ((1 / 4000000)) := by norm_num
  have hs2 : (((3999999 / 4000000)) : ℝ) ≤ 2 := by norm_num
  have hbox_ball : ∀ ρ : ℂ, ((-1 : ℝ) ≤ ρ.re ∧ ρ.re ≤ 2) →
      (((435048) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (435071)) → ρ ∈ Metric.ball cPB RPB := by
    intro ρ hre him
    rw [Metric.mem_ball, Complex.dist_eq_re_im]
    unfold cPB RPB
    apply Real.sqrt_lt_sqrt (by positivity)
    have h1 := hre.1; have h2 := hre.2; have h3 := him.1; have h4 := him.2
    nlinarith [h1, h2, h3, h4, sq_nonneg (ρ.re - ((1 / 2))), sq_nonneg (ρ.im - ((870119 / 2)))]
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
  have hTbox : ∀ z ∈ T, ((((1 / 4000000)) : ℝ) ≤ z.re ∧ z.re ≤ ((3999999 / 4000000))) ∧ (((435048) : ℝ) ≤ z.im ∧ z.im ≤ (435071)) := by
    rw [hTdef]
    refine RHInBox.line_toFinset_forall xsL (fun t ht => ?_)
    exact ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩,
      by rw [him_line]; exact (hbnd t ht).1, by rw [him_line]; exact (hbnd t ht).2⟩
  obtain ⟨hnzb, hnzt, hnzl, hins, hAV2, hAHt, hAHb, hAG1, hAG2⟩ := hArbT
  have hN1 : 1 ≤ 41 := by norm_num
  have hpinL : 2 * 3.1416 * ((41 : ℝ) - 1) <
      2 * ((-10006973191 / 40000000000) : ℝ) + (4193500911 / 100000000000) - (-862853940629 / 500000000000) + (16021456460227 / 125000000000) + (5126866067269 / 40000000000) := by norm_num
  have hpinH : 2 * ((-125087164887 / 500000000000) : ℝ) + (41935009111 / 1000000000000) - (-1725707881259 / 1000000000000) + (128171651681817 / 1000000000000) + (64085825840863 / 500000000000) <
      2 * 3.14 * ((41 : ℝ) + 1) := by norm_num
  have hcountN : ((41 : ℕ) : ℤ) = (T.card : ℤ) := by rw [hTcard]
  exact TuringBand.turing_band_on_line (((1 / 4000000)) : ℝ) ((3999999 / 4000000)) (435048) (435071) hT0 hTle hs0 hs2
    cPB RPB hRpos 41 hN1
    (-10006973191 / 40000000000) (-125087164887 / 500000000000) (4193500911 / 100000000000) (41935009111 / 1000000000000) (-1725707881259 / 1000000000000) (-862853940629 / 500000000000) (16021456460227 / 125000000000) (128171651681817 / 1000000000000) (5126866067269 / 40000000000) (64085825840863 / 500000000000)
    hbox_ball hs1PB hnzb hnzt hnzl hins hAV2 hAHt hAHb hAG1 hAG2 hpinL hpinH
    T hTline hTzero hTbox hcountN

/-- Kernel statement-match gate: `rh_in_box_1d4000000_3999999d4000000_435048_435071` states EXACTLY the canonical
    `TuringBand.BandStatement` at this band's parameters (defeq).  -/
theorem statement_match :
    TuringBand.BandStatement (((1 / 4000000)) : ℝ) ((3999999 / 4000000)) (435048) (435071) 41
      (-10006973191 / 40000000000) (-125087164887 / 500000000000) (4193500911 / 100000000000) (41935009111 / 1000000000000) (-1725707881259 / 1000000000000) (-862853940629 / 500000000000)
      (16021456460227 / 125000000000) (128171651681817 / 1000000000000) (5126866067269 / 40000000000) (64085825840863 / 500000000000) cPB RPB hs1PB :=
  rh_in_box_1d4000000_3999999d4000000_435048_435071

end RHInBoxT_1d4000000_3999999d4000000_435048_435071
