/-  HeightFloor.lean -- brick H3 = registry node AND_height_floor_kernel: the `55/16` HEIGHT FLOOR,
    hypothesis-free, at every height.

    THE THEOREMS (no hypotheses; axioms [propext, Classical.choice, Quot.sound], see
    AxiomGuardHeightFloor):

      * `strip_clear_low`   : no zero of `riemannZeta` with `0 < Re ρ < 1` and `0 < Im ρ ≤ 55/16`;
      * `height_floor H`    : `∀ ρ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ H → 55/16 ≤ |ρ.im|`,
                              for EVERY real `H` -- the `hγ` binder of the height ladder at any height;
      * `height_floor_280000` : that statement at `H = 280000`, VERBATIM the `hγ` binder of
                              `AllZeros_h280000_Indexed.all_nontrivial_zeros_up_to_height_280000`;
      * `im_gt_of_zero`     : the height-free form `ζ ρ = 0 → 0 < ρ.im → 55/16 < ρ.im`, and
        `abs_im_gt_of_zero` : `ζ ρ = 0 → ρ.im ≠ 0 → 55/16 < |ρ.im|` (conjugate symmetry).

    PROOF.
      1. `HeightFloorEM`: order-3 Euler-Maclaurin at `N = 2` gives, on `1/2 ≤ σ < 1`,
         `0 < t ≤ 55/16`, that a zero forces `‖G2 s‖ ≤ 23/100`, where
         `G2 s = (s - 1) + 2^(-s) (s² + 11 s + 36)/24`.
      2. `HeightFloorBoxes`: a 32-box cover certifies `‖G2 s‖ > 1/4` on `[1/2, 1] × [0, 55/16]`
         (kernel `decide` on an exact dyadic evaluator; cos/sin/`2^(-σ)` inputs from Taylor brackets).
      3. The reflection `ρ ↦ 1 - conj ρ` (`ZeroFreeBridge.riemannZeta_reflect_line_eq_zero`,
         Im-preserving) folds `0 < Re ρ < 1/2` onto the covered half.
      4. `ZetaZeroConfinement.no_low_zeros_of_strip_clear` turns the strip statement into the
         `hγ` form (it adds the off-real strip location `0 < Re ρ < 1`).

    Relation to the memo (ANDURIL_ARB_DISCHARGE_2026-09-23 §1.2, row H3): min |(s-1) ζ(s)| = 0.730 on
    `[1/2, 1] × [0, 55/16]`; the route here certifies the explicit main part `G2` instead of `ζ`
    itself, so no derivative/Lipschitz bound of `ζ` is needed -- the box enclosures are exact
    monotone brackets of the elementary functions `2^(-σ)`, `cos`, `sin`.

    conjecture1_proved = False.  A finite, low-height zero-free rectangle (the first zero is at
    height ≈ 14.13); nothing here bears on the Riemann Hypothesis.
-/
import HeightFloorBoxes
import ZetaZeroConfinement
import DlvpZetaSymmetry

open Complex

namespace HeightFloor

/-- **No zero on the right half of the low rectangle.** -/
theorem zeta_ne_zero_low_right {s : ℂ} (h1 : 1 / 2 ≤ s.re) (h2 : s.re < 1) (h3 : 0 < s.im)
    (h4 : s.im ≤ 55 / 16) : riemannZeta s ≠ 0 := by
  intro hz
  have hle := G2_norm_le_of_zero h1 h2 h3 h4 hz
  have hgt := Boxes.G2_norm_gt s.re s.im h1 h2.le h3.le h4
  rw [Complex.re_add_im s] at hgt
  linarith

/-- **The low strip is zero-free**: no zero with `0 < Re ρ < 1`, `0 < Im ρ ≤ 55/16`.  This is the
    `hclear_low` input of `ZetaZeroConfinement.no_low_zeros_of_strip_clear`. -/
theorem strip_clear_low : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
    0 < ρ.im → ρ.im ≤ 55 / 16 → False := by
  intro ρ hz h0 h1 him hT
  by_cases hh : 1 / 2 ≤ ρ.re
  · exact zeta_ne_zero_low_right hh h1 him hT hz
  · have hz' := ZeroFreeBridge.riemannZeta_reflect_line_eq_zero h0 h1 hz
    have hre : (1 - (starRingEnd ℂ) ρ).re = 1 - ρ.re := by simp
    have him' : (1 - (starRingEnd ℂ) ρ).im = ρ.im := by simp
    exact zeta_ne_zero_low_right (by rw [hre]; linarith) (by rw [hre]; linarith)
      (by rw [him']; exact him) (by rw [him']; exact hT) hz'

/-- **THE HEIGHT FLOOR, at every height `H`** (the capstone's `hγ`, hypothesis-free). -/
theorem height_floor (H : ℝ) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ H → 55 / 16 ≤ |ρ.im| :=
  ZetaZeroConfinement.no_low_zeros_of_strip_clear H strip_clear_low

/-- **The `hγ` binder of `AllZeros_h280000_Indexed.all_nontrivial_zeros_up_to_height_280000`,
    verbatim, discharged.** -/
theorem height_floor_280000 :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 280000 → 55 / 16 ≤ |ρ.im| :=
  height_floor 280000

/-- Height-free form: a zero with positive ordinate has ordinate `> 55/16`. -/
theorem im_gt_of_zero {ρ : ℂ} (hz : riemannZeta ρ = 0) (him : 0 < ρ.im) : 55 / 16 < ρ.im := by
  by_contra h
  obtain ⟨h0, h1⟩ := ZetaZeroConfinement.zeta_zero_re_mem_strip (ne_of_gt him) hz
  exact strip_clear_low ρ hz h0 h1 him (le_of_not_gt h)

/-- Both half-planes: every non-real zero has `|Im ρ| > 55/16`. -/
theorem abs_im_gt_of_zero {ρ : ℂ} (hz : riemannZeta ρ = 0) (him : ρ.im ≠ 0) :
    55 / 16 < |ρ.im| := by
  rcases lt_or_gt_of_ne him with hneg | hpos
  · have hc : riemannZeta ((starRingEnd ℂ) ρ) = 0 := by
      rw [riemannZeta_conj, hz, map_zero]
    have hcim : ((starRingEnd ℂ) ρ).im = -ρ.im := by simp
    have := im_gt_of_zero hc (by rw [hcim]; linarith)
    rw [hcim] at this
    rw [abs_of_neg hneg]; exact this
  · rw [abs_of_pos hpos]; exact im_gt_of_zero hz hpos

end HeightFloor
