/-
RvMBacklundS — Backlund S(T)=O(log T), PR 5 step 4: the full `riemannS` bound.

`π·S(T) = argChangeVert ζ 2 0 T + argChangeHoriz ζ T 2 (1/2)` (the corpus definition `riemannS`).  The
horizontal leg is `O(log T)` (PR 5 step 3).  The vertical leg at `Re = 2` is `O(1)`: `Re ζ(2+iy) > 0`
there (`re_zeta_two_ge`: `≥ 2 - π²/6 > 0`), so ζ stays in the right half-plane and its argument change is
`< π`.  Hence `|S(T)| = O(log T)`.

  * `argChangeVert_abs_lt_pi_of_rePos` — vertical confinement: `Re f > 0` up a vertical segment ⟹
    `|argChangeVert f σ T0 T1| < π` (mirror of PR 4a via the `i`-rotated FTC, `Complex.mul_I_im`).
  * `riemannS_abs_le_log` — `|S(T)| ≤ log((4T+19)/‖F_T 2‖)/log(7/6) + 2`, the explicit `O(log T)`.

Carries the same honest hypotheses as PR 5: `ζ ≠ 0` on the horizontal segment (`S(T)`-jump subtlety) and
`logDeriv ζ` continuity there.  conjecture1_proved = False.
-/
import Mathlib
import RvMBacklundCountJensen
import RvMBacklundCenter
import RvMDiffractionCore

open Complex MeasureTheory

namespace Backlund

/-- **Vertical half-plane confinement.**  If `Re f > 0` all along the vertical segment `Re = σ`,
    `Im ∈ [T0,T1]`, the net argument change of `f` up it is `< π` in absolute value. -/
theorem argChangeVert_abs_lt_pi_of_rePos (f : ℂ → ℂ) (σ T0 T1 : ℝ)
    (hdiff : ∀ y ∈ Set.uIcc T0 T1, DifferentiableAt ℂ f ((σ : ℂ) + (y : ℂ) * I))
    (hcont : ContinuousOn (fun y : ℝ => logDeriv f ((σ : ℂ) + (y : ℂ) * I)) (Set.uIcc T0 T1))
    (hpos : ∀ y ∈ Set.uIcc T0 T1, 0 < (f ((σ : ℂ) + (y : ℂ) * I)).re) :
    |DiffractionCore.argChangeVert f σ T0 T1| < Real.pi := by
  have hpath : ∀ y : ℝ, HasDerivAt (fun y : ℝ => (σ : ℂ) + (y : ℂ) * I) I y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := by simpa using (hasDerivAt_id y).ofReal_comp
    have h2 : HasDerivAt (fun y : ℝ => (y : ℂ) * I) I y := by simpa using h1.mul_const I
    exact h2.const_add (σ : ℂ)
  have hderiv : ∀ y ∈ Set.uIcc T0 T1,
      HasDerivAt (fun y : ℝ => Complex.log (f ((σ : ℂ) + (y : ℂ) * I)))
        (logDeriv f ((σ : ℂ) + (y : ℂ) * I) * I) y := by
    intro y hy
    have hfp : HasDerivAt (fun y : ℝ => f ((σ : ℂ) + (y : ℂ) * I))
        (I • deriv f ((σ : ℂ) + (y : ℂ) * I)) y := by
      simpa only [Function.comp_def] using ((hdiff y hy).hasDerivAt).scomp y (hpath y)
    have hslit : f ((σ : ℂ) + (y : ℂ) * I) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (hpos y hy))
    have hd := hfp.clog_real hslit
    rw [smul_eq_mul,
      show (I * deriv f ((σ : ℂ) + (y : ℂ) * I)) / f ((σ : ℂ) + (y : ℂ) * I)
        = logDeriv f ((σ : ℂ) + (y : ℂ) * I) * I by rw [logDeriv_apply]; ring] at hd
    exact hd
  have hFTC : (∫ y in T0..T1, logDeriv f ((σ : ℂ) + (y : ℂ) * I) * I)
      = Complex.log (f ((σ : ℂ) + (T1 : ℂ) * I)) - Complex.log (f ((σ : ℂ) + (T0 : ℂ) * I)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((hcont.mul continuousOn_const).intervalIntegrable)
  have hval : DiffractionCore.argChangeVert f σ T0 T1
      = Complex.arg (f ((σ : ℂ) + (T1 : ℂ) * I)) - Complex.arg (f ((σ : ℂ) + (T0 : ℂ) * I)) := by
    unfold DiffractionCore.argChangeVert
    have hWI : (∫ y in T0..T1, logDeriv f ((σ : ℂ) + (y : ℂ) * I)) * I
        = Complex.log (f ((σ : ℂ) + (T1 : ℂ) * I)) - Complex.log (f ((σ : ℂ) + (T0 : ℂ) * I)) := by
      rw [← intervalIntegral.integral_mul_const]; exact hFTC
    have himeq := congrArg Complex.im hWI
    rw [Complex.mul_I_im] at himeq
    rw [himeq, Complex.sub_im, Complex.log_im, Complex.log_im]
  have ha1 : |Complex.arg (f ((σ : ℂ) + (T1 : ℂ) * I))| < Real.pi / 2 := by
    rw [Complex.abs_arg_lt_pi_div_two_iff]; exact Or.inl (hpos T1 Set.right_mem_uIcc)
  have ha0 : |Complex.arg (f ((σ : ℂ) + (T0 : ℂ) * I))| < Real.pi / 2 := by
    rw [Complex.abs_arg_lt_pi_div_two_iff]; exact Or.inl (hpos T0 Set.left_mem_uIcc)
  rw [hval, abs_lt]
  rw [abs_lt] at ha1 ha0
  constructor <;> linarith [ha1.1, ha1.2, ha0.1, ha0.2]

/-- **`S(T) = O(log T)`.**  For `T ≥ 4`, with `ζ ≠ 0` and `logDeriv ζ` continuous along `[1/2,2]+iT`,
    `|riemannS T| ≤ log((4T+19)/‖F_T 2‖)/log(7/6) + 2`. -/
theorem riemannS_abs_le_log {T : ℝ} (hT : 4 ≤ T)
    (hζne : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2, riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0)
    (hlogcont : ContinuousOn (fun x : ℝ => logDeriv riemannZeta ((x : ℂ) + (T : ℂ) * I))
      (Set.Icc (1 / 2 : ℝ) 2)) :
    |DiffractionCore.riemannS T|
      ≤ Real.log ((4 * T + 19) / ‖backlundAux T ((2 : ℝ) : ℂ)‖) / Real.log (7 / 4 / (3 / 2)) + 2 := by
  set J : ℝ := Real.log ((4 * T + 19) / ‖backlundAux T ((2 : ℝ) : ℂ)‖) / Real.log (7 / 4 / (3 / 2))
    with hJ
  -- vertical leg (Re = 2): Re ζ > 0 ⟹ |argChangeVert| < π
  have hpos2 : (0 : ℝ) < 2 - Real.pi ^ 2 / 6 := by nlinarith [Real.pi_lt_d4, Real.pi_pos]
  have hne1 : ∀ y : ℝ, (((2 : ℝ) : ℂ) + (y : ℂ) * I) ≠ 1 := by
    intro y h; simp [Complex.ext_iff] at h
  have hvert : |DiffractionCore.argChangeVert riemannZeta 2 0 T| < Real.pi := by
    refine argChangeVert_abs_lt_pi_of_rePos riemannZeta 2 0 T
      (fun y _ => differentiableAt_riemannZeta (hne1 y)) ?_ ?_
    · simpa using DiffractionCore.continuous_logDeriv_zeta_line2.continuousOn
    · exact fun y _ => lt_of_lt_of_le hpos2 (re_zeta_two_ge y)
  -- horizontal leg (step 3), with the orientation flip 2 → 1/2
  have hhoriz := zeta_argChangeHoriz_abs_le_log hT hζne hlogcont
  have hflip : DiffractionCore.argChangeHoriz riemannZeta T 2 (1 / 2)
      = -DiffractionCore.argChangeHoriz riemannZeta T (1 / 2) 2 := by
    unfold DiffractionCore.argChangeHoriz
    rw [intervalIntegral.integral_symm (1 / 2) 2, Complex.neg_im]
  have hH : |DiffractionCore.argChangeHoriz riemannZeta T 2 (1 / 2)| ≤ (J + 1) * Real.pi := by
    rw [hflip, abs_neg]; exact hhoriz
  -- combine: |S| = |V + H|/π ≤ (π + (J+1)π)/π = J + 2
  rw [show DiffractionCore.riemannS T
      = (DiffractionCore.argChangeVert riemannZeta 2 0 T
          + DiffractionCore.argChangeHoriz riemannZeta T 2 (1 / 2)) / Real.pi from rfl,
    abs_div, abs_of_pos Real.pi_pos, div_le_iff₀ Real.pi_pos]
  calc |DiffractionCore.argChangeVert riemannZeta 2 0 T
          + DiffractionCore.argChangeHoriz riemannZeta T 2 (1 / 2)|
      ≤ |DiffractionCore.argChangeVert riemannZeta 2 0 T|
          + |DiffractionCore.argChangeHoriz riemannZeta T 2 (1 / 2)| := abs_add_le _ _
    _ ≤ Real.pi + (J + 1) * Real.pi := add_le_add hvert.le hH
    _ = (J + 2) * Real.pi := by ring

end Backlund
