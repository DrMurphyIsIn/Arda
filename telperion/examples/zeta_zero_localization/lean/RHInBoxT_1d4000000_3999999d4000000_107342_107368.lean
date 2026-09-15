/-  T5 TURING-BAND certificate for `[(1 / 4000000),(3999999 / 4000000)] x [107342,107368]` with `N = 39`:
    the RvM edge decomposition (no boundary winding integral, no in-strip edges).
    Emitted by telperion `emit_turing_band_instantiation`.
    Arb non-kernel inputs: `hLine` (39 on-line zeros) + `hArbT` (edge non-vanishing,
    confinement, five edge argument-change enclosures).  conjecture1_proved = False. -/
import Mathlib
import RHInBox
import TuringBand
import BoxLocalization

open Complex MeasureTheory Real
open scoped Topology

set_option maxHeartbeats 400000

namespace RHInBoxT_1d4000000_3999999d4000000_107342_107368

/-- Ball center covering the RvM rectangle `[-1,2] x [107342,107368]`. -/
noncomputable def cPB : ℂ := ⟨((1 / 2)), (107355)⟩

noncomputable def RPB : ℝ := Real.sqrt ((2741 / 16))

theorem RPB_pos : (0 : ℝ) < RPB := Real.sqrt_pos.mpr (by norm_num)

theorem hs1PB : (1 : ℂ) ∉ Metric.ball cPB RPB := by
  rw [Metric.mem_ball, Complex.dist_eq_re_im]
  unfold cPB RPB
  intro hlt
  simp only [Complex.one_re, Complex.one_im] at hlt
  have hle : Real.sqrt ((2741 / 16)) ≤
      Real.sqrt (((1 : ℝ) - ((1 / 2))) ^ 2 + ((0 : ℝ) - (107355)) ^ 2) :=
    Real.sqrt_le_sqrt (by norm_num)
  linarith [hlt, hle]

/-- **T5 band `[(1 / 4000000),(3999999 / 4000000)] x [107342,107368]`, `N = 39`** via the RvM edge decomposition.
    conjecture1_proved = False. -/
theorem rh_in_box_1d4000000_3999999d4000000_107342_107368
    (hLine : ∃ xs : List ℝ, xs.length = 39 ∧ xs.IsChain (· < ·) ∧
      (∀ t ∈ xs, ((107342) : ℝ) ≤ t ∧ t ≤ (107368)) ∧
      (∀ t ∈ xs, completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0))
    (hArbT :
      (∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta (↑x + (((107342) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta (↑x + (((107368) : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((107342) : ℝ) (107368), riemannZeta (((-1 : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ ρ ∈ RHInBoxAnalytic.zeroFinset cPB RPB hs1PB,
        (-1 : ℝ) < ρ.re ∧ ρ.re < 2 ∧ ((107342) : ℝ) < ρ.im ∧ ρ.im < (107368)) ∧
      DiffractionCore.argChangeVert riemannZeta 2 (107342) (107368) ∈ Set.Icc ((-105667757709 / 250000000000) : ℝ) (-84534206167 / 200000000000) ∧
      DiffractionCore.argChangeHoriz riemannZeta (107368) 2 (-1) ∈ Set.Icc ((-653587230019 / 500000000000) : ℝ) (-1307174460037 / 1000000000000) ∧
      DiffractionCore.argChangeHoriz riemannZeta (107342) 2 (-1) ∈ Set.Icc ((3099879280203 / 500000000000) : ℝ) (6199758560407 / 1000000000000) ∧
      DiffractionCore.argChangeVert Gammaℝ (-1) (107342) (107368) ∈ Set.Icc ((25339650206381 / 200000000000) : ℝ) (63349125515953 / 500000000000) ∧
      DiffractionCore.argChangeVert Gammaℝ 2 (107342) (107368) ∈ Set.Icc ((126698251030213 / 1000000000000) : ℝ) (63349125515107 / 500000000000)) :
    (∀ ρ, ((((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) → (((107342) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (107368)) →
      riemannZeta ρ = 0 → ρ.re = 1 / 2) := by
  have hRpos : (0 : ℝ) < RPB := RPB_pos
  have hT0 : (0 : ℝ) < (107342) := by norm_num
  have hTle : ((107342) : ℝ) ≤ (107368) := by norm_num
  have hs0 : (-1 : ℝ) ≤ ((1 / 4000000)) := by norm_num
  have hs2 : (((3999999 / 4000000)) : ℝ) ≤ 2 := by norm_num
  have hbox_ball : ∀ ρ : ℂ, ((-1 : ℝ) ≤ ρ.re ∧ ρ.re ≤ 2) →
      (((107342) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (107368)) → ρ ∈ Metric.ball cPB RPB := by
    intro ρ hre him
    rw [Metric.mem_ball, Complex.dist_eq_re_im]
    unfold cPB RPB
    apply Real.sqrt_lt_sqrt (by positivity)
    have h1 := hre.1; have h2 := hre.2; have h3 := him.1; have h4 := him.2
    nlinarith [h1, h2, h3, h4, sq_nonneg (ρ.re - ((1 / 2))), sq_nonneg (ρ.im - (107355))]
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
  have hTcard : T.card = 39 := by
    rw [hTdef, RHInBox.line_toFinset_card xsL hchain, hlen]
  have hre_lo : (((1 / 4000000)) : ℝ) ≤ 1 / 2 := by norm_num
  have hre_hi : (1 / 2 : ℝ) ≤ ((3999999 / 4000000)) := by norm_num
  have hTline : ∀ z ∈ T, z.re = 1 / 2 := by
    rw [hTdef]
    exact RHInBox.line_toFinset_forall xsL (fun t _ => hre_line t)
  have hTzero : ∀ z ∈ T, riemannZeta z = 0 := by
    rw [hTdef]
    exact RHInBox.line_toFinset_forall xsL (fun t ht => hzeta t (hzeros t ht))
  have hTbox : ∀ z ∈ T, ((((1 / 4000000)) : ℝ) ≤ z.re ∧ z.re ≤ ((3999999 / 4000000))) ∧ (((107342) : ℝ) ≤ z.im ∧ z.im ≤ (107368)) := by
    rw [hTdef]
    refine RHInBox.line_toFinset_forall xsL (fun t ht => ?_)
    exact ⟨⟨by rw [hre_line]; exact hre_lo, by rw [hre_line]; exact hre_hi⟩,
      by rw [him_line]; exact (hbnd t ht).1, by rw [him_line]; exact (hbnd t ht).2⟩
  obtain ⟨hnzb, hnzt, hnzl, hins, hAV2, hAHt, hAHb, hAG1, hAG2⟩ := hArbT
  have hN1 : 1 ≤ 39 := by norm_num
  have hpinL : 2 * 3.1416 * ((39 : ℝ) - 1) <
      2 * ((-105667757709 / 250000000000) : ℝ) + (-653587230019 / 500000000000) - (6199758560407 / 1000000000000) + (25339650206381 / 200000000000) + (126698251030213 / 1000000000000) := by norm_num
  have hpinH : 2 * ((-84534206167 / 200000000000) : ℝ) + (-1307174460037 / 1000000000000) - (3099879280203 / 500000000000) + (63349125515953 / 500000000000) + (63349125515107 / 500000000000) <
      2 * 3.14 * ((39 : ℝ) + 1) := by norm_num
  have hcountN : ((39 : ℕ) : ℤ) = (T.card : ℤ) := by rw [hTcard]
  exact TuringBand.turing_band_on_line (((1 / 4000000)) : ℝ) ((3999999 / 4000000)) (107342) (107368) hT0 hTle hs0 hs2
    cPB RPB hRpos 39 hN1
    (-105667757709 / 250000000000) (-84534206167 / 200000000000) (-653587230019 / 500000000000) (-1307174460037 / 1000000000000) (3099879280203 / 500000000000) (6199758560407 / 1000000000000) (25339650206381 / 200000000000) (63349125515953 / 500000000000) (126698251030213 / 1000000000000) (63349125515107 / 500000000000)
    hbox_ball hs1PB hnzb hnzt hnzl hins hAV2 hAHt hAHb hAG1 hAG2 hpinL hpinH
    T hTline hTzero hTbox hcountN

/-- Kernel statement-match gate: `rh_in_box_1d4000000_3999999d4000000_107342_107368` states EXACTLY the canonical
    `TuringBand.BandStatement` at this band's parameters (defeq).  -/
theorem statement_match :
    TuringBand.BandStatement (((1 / 4000000)) : ℝ) ((3999999 / 4000000)) (107342) (107368) 39
      (-105667757709 / 250000000000) (-84534206167 / 200000000000) (-653587230019 / 500000000000) (-1307174460037 / 1000000000000) (3099879280203 / 500000000000) (6199758560407 / 1000000000000)
      (25339650206381 / 200000000000) (63349125515953 / 500000000000) (126698251030213 / 1000000000000) (63349125515107 / 500000000000) cPB RPB hs1PB :=
  rh_in_box_1d4000000_3999999d4000000_107342_107368

end RHInBoxT_1d4000000_3999999d4000000_107342_107368
