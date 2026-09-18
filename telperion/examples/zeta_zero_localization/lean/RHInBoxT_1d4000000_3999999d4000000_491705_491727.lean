/-  T5 TURING-BAND certificate for `[(1 / 4000000),(3999999 / 4000000)] x [491705,491727]` with `N = 38`:
    the RvM edge decomposition (no boundary winding integral, no in-strip edges).
    Emitted by telperion `emit_turing_band_instantiation`.
    Arb non-kernel inputs: `hLine` (38 on-line zeros) + `hArbT` (edge non-vanishing,
    confinement, five edge argument-change enclosures).  conjecture1_proved = False. -/
import Mathlib
import RHInBox
import TuringBand
import BoxLocalization

open Complex MeasureTheory Real
open scoped Topology

set_option maxHeartbeats 400000

namespace RHInBoxT_1d4000000_3999999d4000000_491705_491727

/-- Ball center covering the RvM rectangle `[-1,2] x [491705,491727]`. -/
noncomputable def cPB : ℂ := ⟨((1 / 2)), (491716)⟩

noncomputable def RPB : ℝ := Real.sqrt ((1973 / 16))

theorem RPB_pos : (0 : ℝ) < RPB := Real.sqrt_pos.mpr (by norm_num)

theorem hs1PB : (1 : ℂ) ∉ Metric.ball cPB RPB := by
  rw [Metric.mem_ball, Complex.dist_eq_re_im]
  unfold cPB RPB
  intro hlt
  simp only [Complex.one_re, Complex.one_im] at hlt
  have hle : Real.sqrt ((1973 / 16)) ≤
      Real.sqrt (((1 : ℝ) - ((1 / 2))) ^ 2 + ((0 : ℝ) - (491716)) ^ 2) :=
    Real.sqrt_le_sqrt (by norm_num)
  linarith [hlt, hle]

/-- **T5 band `[(1 / 4000000),(3999999 / 4000000)] x [491705,491727]`, `N = 38`** via the RvM edge decomposition.
    conjecture1_proved = False. -/
theorem rh_in_box_1d4000000_3999999d4000000_491705_491727
    (hLine : ∃ xs : List ℝ, xs.length = 38 ∧ xs.IsChain (· < ·) ∧
      (∀ t ∈ xs, ((491705) : ℝ) ≤ t ∧ t ≤ (491727)) ∧
      (∀ t ∈ xs, completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0))
    (hArbT :
      (∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta (↑x + (((491705) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta (↑x + (((491727) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((491705) : ℝ) (491727), riemannZeta (((-1 : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ ρ ∈ RHInBoxAnalytic.zeroFinset cPB RPB hs1PB,
        (-1 : ℝ) < ρ.re ∧ ρ.re < 2 ∧ ((491705) : ℝ) < ρ.im ∧ ρ.im < (491727)) ∧
      DiffractionCore.argChangeVert riemannZeta 2 (491705) (491727) ∈ Set.Icc ((-105529346159 / 200000000000) : ℝ) (-263823365397 / 500000000000) ∧
      DiffractionCore.argChangeHoriz riemannZeta (491727) 2 (-1) ∈ Set.Icc ((-6146331141307 / 1000000000000) : ℝ) (-3073165570653 / 500000000000) ∧
      DiffractionCore.argChangeHoriz riemannZeta (491705) 2 (-1) ∈ Set.Icc ((48212082709 / 25000000000) : ℝ) (1928483308361 / 1000000000000) ∧
      DiffractionCore.argChangeVert Gammaℝ (-1) (491705) (491727) ∈ Set.Icc ((61972787396037 / 500000000000) : ℝ) (4957822991683 / 40000000000) ∧
      DiffractionCore.argChangeVert Gammaℝ 2 (491705) (491727) ∈ Set.Icc ((61972787396003 / 500000000000) : ℝ) (123945574792007 / 1000000000000)) :
    (∀ ρ, ((((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) → (((491705) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (491727)) →
      riemannZeta ρ = 0 → ρ.re = 1 / 2) := by
  have hRpos : (0 : ℝ) < RPB := RPB_pos
  have hT0 : (0 : ℝ) < (491705) := by norm_num
  have hTle : ((491705) : ℝ) ≤ (491727) := by norm_num
  have hs0 : (-1 : ℝ) ≤ ((1 / 4000000)) := by norm_num
  have hs2 : (((3999999 / 4000000)) : ℝ) ≤ 2 := by norm_num
  have hbox_ball : ∀ ρ : ℂ, ((-1 : ℝ) ≤ ρ.re ∧ ρ.re ≤ 2) →
      (((491705) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (491727)) → ρ ∈ Metric.ball cPB RPB := by
    intro ρ hre him
    rw [Metric.mem_ball, Complex.dist_eq_re_im]
    unfold cPB RPB
    apply Real.sqrt_lt_sqrt (by positivity)
    have h1 := hre.1; have h2 := hre.2; have h3 := him.1; have h4 := him.2
    nlinarith [h1, h2, h3, h4, sq_nonneg (ρ.re - ((1 / 2))), sq_nonneg (ρ.im - (491716))]
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
  have hTcard : T.card = 38 := by
    rw [hTdef, RHInBox.line_toFinset_card xsL hchain, hlen]
  have hre_lo : (((1 / 4000000)) : ℝ) ≤ 1 / 2 := by norm_num
  have hre_hi : (1 / 2 : ℝ) ≤ ((3999999 / 4000000)) := by norm_num
  have hTline : ∀ z ∈ T, z.re = 1 / 2 := by
    rw [hTdef]
    exact RHInBox.line_toFinset_forall xsL (fun t _ => hre_line t)
  have hTzero : ∀ z ∈ T, riemannZeta z = 0 := by
    rw [hTdef]
    exact RHInBox.line_toFinset_forall xsL (fun t ht => hzeta t (hzeros t ht))
  have hTbox : ∀ z ∈ T, ((((1 / 4000000)) : ℝ) ≤ z.re ∧ z.re ≤ ((3999999 / 4000000))) ∧ (((491705) : ℝ) ≤ z.im ∧ z.im ≤ (491727)) := by
    rw [hTdef]
    refine RHInBox.line_toFinset_forall xsL (fun t ht => ?_)
    exact ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩,
      by rw [him_line]; exact (hbnd t ht).1, by rw [him_line]; exact (hbnd t ht).2⟩
  obtain ⟨hnzb, hnzt, hnzl, hins, hAV2, hAHt, hAHb, hAG1, hAG2⟩ := hArbT
  have hN1 : 1 ≤ 38 := by norm_num
  have hpinL : 2 * 3.1416 * ((38 : ℝ) - 1) <
      2 * ((-105529346159 / 200000000000) : ℝ) + (-6146331141307 / 1000000000000) - (1928483308361 / 1000000000000) + (61972787396037 / 500000000000) + (61972787396003 / 500000000000) := by norm_num
  have hpinH : 2 * ((-263823365397 / 500000000000) : ℝ) + (-3073165570653 / 500000000000) - (48212082709 / 25000000000) + (4957822991683 / 40000000000) + (123945574792007 / 1000000000000) <
      2 * 3.14 * ((38 : ℝ) + 1) := by norm_num
  have hcountN : ((38 : ℕ) : ℤ) = (T.card : ℤ) := by rw [hTcard]
  exact TuringBand.turing_band_on_line (((1 / 4000000)) : ℝ) ((3999999 / 4000000)) (491705) (491727) hT0 hTle hs0 hs2
    cPB RPB hRpos 38 hN1
    (-105529346159 / 200000000000) (-263823365397 / 500000000000) (-6146331141307 / 1000000000000) (-3073165570653 / 500000000000) (48212082709 / 25000000000) (1928483308361 / 1000000000000) (61972787396037 / 500000000000) (4957822991683 / 40000000000) (61972787396003 / 500000000000) (123945574792007 / 1000000000000)
    hbox_ball hs1PB hnzb hnzt hnzl hins hAV2 hAHt hAHb hAG1 hAG2 hpinL hpinH
    T hTline hTzero hTbox hcountN

/-- Kernel statement-match gate: `rh_in_box_1d4000000_3999999d4000000_491705_491727` states EXACTLY the canonical
    `TuringBand.BandStatement` at this band's parameters (defeq).  -/
theorem statement_match :
    TuringBand.BandStatement (((1 / 4000000)) : ℝ) ((3999999 / 4000000)) (491705) (491727) 38
      (-105529346159 / 200000000000) (-263823365397 / 500000000000) (-6146331141307 / 1000000000000) (-3073165570653 / 500000000000) (48212082709 / 25000000000) (1928483308361 / 1000000000000)
      (61972787396037 / 500000000000) (4957822991683 / 40000000000) (61972787396003 / 500000000000) (123945574792007 / 1000000000000) cPB RPB hs1PB :=
  rh_in_box_1d4000000_3999999d4000000_491705_491727

end RHInBoxT_1d4000000_3999999d4000000_491705_491727
