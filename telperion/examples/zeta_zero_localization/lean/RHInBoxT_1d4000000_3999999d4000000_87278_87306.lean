/-  T5 TURING-BAND certificate for `[(1 / 4000000),(3999999 / 4000000)] x [87278,87306]` with `N = 43`:
    the RvM edge decomposition (no boundary winding integral, no in-strip edges).
    Emitted by telperion `emit_turing_band_instantiation`.
    Arb non-kernel inputs: `hLine` (43 on-line zeros) + `hArbT` (edge non-vanishing,
    confinement, five edge argument-change enclosures).  conjecture1_proved = False. -/
import Mathlib
import RHInBox
import TuringBand
import BoxLocalization

open Complex MeasureTheory Real
open scoped Topology

set_option maxHeartbeats 400000

namespace RHInBoxT_1d4000000_3999999d4000000_87278_87306

/-- Ball center covering the RvM rectangle `[-1,2] x [87278,87306]`. -/
noncomputable def cPB : ℂ := ⟨((1 / 2)), (87292)⟩

noncomputable def RPB : ℝ := Real.sqrt ((3173 / 16))

theorem RPB_pos : (0 : ℝ) < RPB := Real.sqrt_pos.mpr (by norm_num)

theorem hs1PB : (1 : ℂ) ∉ Metric.ball cPB RPB := by
  rw [Metric.mem_ball, Complex.dist_eq_re_im]
  unfold cPB RPB
  intro hlt
  simp only [Complex.one_re, Complex.one_im] at hlt
  have hle : Real.sqrt ((3173 / 16)) ≤
      Real.sqrt (((1 : ℝ) - ((1 / 2))) ^ 2 + ((0 : ℝ) - (87292)) ^ 2) :=
    Real.sqrt_le_sqrt (by norm_num)
  linarith [hlt, hle]

/-- **T5 band `[(1 / 4000000),(3999999 / 4000000)] x [87278,87306]`, `N = 43`** via the RvM edge decomposition.
    conjecture1_proved = False. -/
theorem rh_in_box_1d4000000_3999999d4000000_87278_87306
    (hLine : ∃ xs : List ℝ, xs.length = 43 ∧ xs.IsChain (· < ·) ∧
      (∀ t ∈ xs, ((87278) : ℝ) ≤ t ∧ t ≤ (87306)) ∧
      (∀ t ∈ xs, completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0))
    (hArbT :
      (∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta (↑x + (((87278) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta (↑x + (((87306) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((87278) : ℝ) (87306), riemannZeta (((-1 : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ ρ ∈ RHInBoxAnalytic.zeroFinset cPB RPB hs1PB,
        (-1 : ℝ) < ρ.re ∧ ρ.re < 2 ∧ ((87278) : ℝ) < ρ.im ∧ ρ.im < (87306)) ∧
      DiffractionCore.argChangeVert riemannZeta 2 (87278) (87306) ∈ Set.Icc ((38802512361 / 500000000000) : ℝ) (77605024723 / 1000000000000) ∧
      DiffractionCore.argChangeHoriz riemannZeta (87306) 2 (-1) ∈ Set.Icc ((73171468781 / 125000000000) : ℝ) (585371750249 / 1000000000000) ∧
      DiffractionCore.argChangeHoriz riemannZeta (87278) 2 (-1) ∈ Set.Icc ((-1170274797889 / 500000000000) : ℝ) (-2340549595777 / 1000000000000) ∧
      DiffractionCore.argChangeVert Gammaℝ (-1) (87278) (87306) ∈ Set.Icc ((133547918408003 / 1000000000000) : ℝ) (33386979602001 / 250000000000) ∧
      DiffractionCore.argChangeVert Gammaℝ 2 (87278) (87306) ∈ Set.Icc ((133547918405247 / 1000000000000) : ℝ) (1043343112541 / 7812500000)) :
    (∀ ρ, ((((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) → (((87278) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (87306)) →
      riemannZeta ρ = 0 → ρ.re = 1 / 2) := by
  have hRpos : (0 : ℝ) < RPB := RPB_pos
  have hT0 : (0 : ℝ) < (87278) := by norm_num
  have hTle : ((87278) : ℝ) ≤ (87306) := by norm_num
  have hs0 : (-1 : ℝ) ≤ ((1 / 4000000)) := by norm_num
  have hs2 : (((3999999 / 4000000)) : ℝ) ≤ 2 := by norm_num
  have hbox_ball : ∀ ρ : ℂ, ((-1 : ℝ) ≤ ρ.re ∧ ρ.re ≤ 2) →
      (((87278) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (87306)) → ρ ∈ Metric.ball cPB RPB := by
    intro ρ hre him
    rw [Metric.mem_ball, Complex.dist_eq_re_im]
    unfold cPB RPB
    apply Real.sqrt_lt_sqrt (by positivity)
    have h1 := hre.1; have h2 := hre.2; have h3 := him.1; have h4 := him.2
    nlinarith [h1, h2, h3, h4, sq_nonneg (ρ.re - ((1 / 2))), sq_nonneg (ρ.im - (87292))]
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
  have hTcard : T.card = 43 := by
    rw [hTdef, RHInBox.line_toFinset_card xsL hchain, hlen]
  have hre_lo : (((1 / 4000000)) : ℝ) ≤ 1 / 2 := by norm_num
  have hre_hi : (1 / 2 : ℝ) ≤ ((3999999 / 4000000)) := by norm_num
  have hTline : ∀ z ∈ T, z.re = 1 / 2 := by
    rw [hTdef]
    exact RHInBox.line_toFinset_forall xsL (fun t _ => hre_line t)
  have hTzero : ∀ z ∈ T, riemannZeta z = 0 := by
    rw [hTdef]
    exact RHInBox.line_toFinset_forall xsL (fun t ht => hzeta t (hzeros t ht))
  have hTbox : ∀ z ∈ T, ((((1 / 4000000)) : ℝ) ≤ z.re ∧ z.re ≤ ((3999999 / 4000000))) ∧ (((87278) : ℝ) ≤ z.im ∧ z.im ≤ (87306)) := by
    rw [hTdef]
    refine RHInBox.line_toFinset_forall xsL (fun t ht => ?_)
    exact ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩,
      by rw [him_line]; exact (hbnd t ht).1, by rw [him_line]; exact (hbnd t ht).2⟩
  obtain ⟨hnzb, hnzt, hnzl, hins, hAV2, hAHt, hAHb, hAG1, hAG2⟩ := hArbT
  have hN1 : 1 ≤ 43 := by norm_num
  have hpinL : 2 * 3.1416 * ((43 : ℝ) - 1) <
      2 * ((38802512361 / 500000000000) : ℝ) + (73171468781 / 125000000000) - (-2340549595777 / 1000000000000) + (133547918408003 / 1000000000000) + (133547918405247 / 1000000000000) := by norm_num
  have hpinH : 2 * ((77605024723 / 1000000000000) : ℝ) + (585371750249 / 1000000000000) - (-1170274797889 / 500000000000) + (33386979602001 / 250000000000) + (1043343112541 / 7812500000) <
      2 * 3.14 * ((43 : ℝ) + 1) := by norm_num
  have hcountN : ((43 : ℕ) : ℤ) = (T.card : ℤ) := by rw [hTcard]
  exact TuringBand.turing_band_on_line (((1 / 4000000)) : ℝ) ((3999999 / 4000000)) (87278) (87306) hT0 hTle hs0 hs2
    cPB RPB hRpos 43 hN1
    (38802512361 / 500000000000) (77605024723 / 1000000000000) (73171468781 / 125000000000) (585371750249 / 1000000000000) (-1170274797889 / 500000000000) (-2340549595777 / 1000000000000) (133547918408003 / 1000000000000) (33386979602001 / 250000000000) (133547918405247 / 1000000000000) (1043343112541 / 7812500000)
    hbox_ball hs1PB hnzb hnzt hnzl hins hAV2 hAHt hAHb hAG1 hAG2 hpinL hpinH
    T hTline hTzero hTbox hcountN

/-- Kernel statement-match gate: `rh_in_box_1d4000000_3999999d4000000_87278_87306` states EXACTLY the canonical
    `TuringBand.BandStatement` at this band's parameters (defeq).  -/
theorem statement_match :
    TuringBand.BandStatement (((1 / 4000000)) : ℝ) ((3999999 / 4000000)) (87278) (87306) 43
      (38802512361 / 500000000000) (77605024723 / 1000000000000) (73171468781 / 125000000000) (585371750249 / 1000000000000) (-1170274797889 / 500000000000) (-2340549595777 / 1000000000000)
      (133547918408003 / 1000000000000) (33386979602001 / 250000000000) (133547918405247 / 1000000000000) (1043343112541 / 7812500000) cPB RPB hs1PB :=
  rh_in_box_1d4000000_3999999d4000000_87278_87306

end RHInBoxT_1d4000000_3999999d4000000_87278_87306
