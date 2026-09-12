/-
RvMBacklundConfine Nonstrict — Backlund S(T)=O(log T), PR 4c (nonstrict): confinement allowing zeros
at the endpoints.

The partition of `[1/2,2]` is cut AT the zeros of `Re ζ(·+iT)`, so each piece's endpoints have `Re = 0`.
The strict confinement (PR 4a/4c-sign) needs `Re f ≠ 0` on the CLOSED interval and cannot apply there.
This file provides the non-strict variant: `Re f ≥ 0` on the closed piece (zeros allowed) still confines
the argument change to `≤ π`, because `arg f ∈ [-π/2, π/2]` throughout.

  * `argChangeHoriz_abs_le_pi_of_re_nonneg` — `Re f ≥ 0` and `f ≠ 0` on the segment ⟹ `|argChangeHoriz| ≤ π`.
  * `argChangeHoriz_abs_le_pi_of_re_sign'` — either sign (`Re f ≥ 0` OR `Re f ≤ 0`), `f ≠ 0` ⟹ `≤ π`.

The FTC still runs: `Re f ≥ 0 ∧ f ≠ 0 ⟹ f ∈ slitPlane` (at a point with `Re = 0`, `f ≠ 0` forces
`Im ≠ 0`).  The `≤ π` bound comes from `Complex.abs_arg_le_pi_div_two_iff` (`|arg z| ≤ π/2 ↔ 0 ≤ re z`).
conjecture1_proved = False.
-/
import Mathlib
import RvMBacklundConfine

open Complex MeasureTheory intervalIntegral

namespace Backlund

/-- **Non-strict half-plane confinement.**  If `Re f ≥ 0` and `f ≠ 0` all along the horizontal segment,
    the net argument change of `f` there is `≤ π` in absolute value. -/
theorem argChangeHoriz_abs_le_pi_of_re_nonneg (f : ℂ → ℂ) (T x0 x1 : ℝ)
    (hdiff : ∀ x ∈ Set.uIcc x0 x1, DifferentiableAt ℂ f ((x : ℂ) + (T : ℂ) * I))
    (hcont : ContinuousOn (fun x : ℝ => logDeriv f ((x : ℂ) + (T : ℂ) * I)) (Set.uIcc x0 x1))
    (hne : ∀ x ∈ Set.uIcc x0 x1, f ((x : ℂ) + (T : ℂ) * I) ≠ 0)
    (hpos : ∀ x ∈ Set.uIcc x0 x1, 0 ≤ (f ((x : ℂ) + (T : ℂ) * I)).re) :
    |DiffractionCore.argChangeHoriz f T x0 x1| ≤ Real.pi := by
  have hpath : ∀ x : ℝ, HasDerivAt (fun t : ℝ => (t : ℂ) + (T : ℂ) * I) 1 x := by
    intro x
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := by simpa using (hasDerivAt_id x).ofReal_comp
    exact h1.add_const _
  -- f ∈ slitPlane along the segment (from Re ≥ 0 and f ≠ 0)
  have hslit : ∀ x ∈ Set.uIcc x0 x1, f ((x : ℂ) + (T : ℂ) * I) ∈ Complex.slitPlane := by
    intro x hx
    rcases lt_or_eq_of_le (hpos x hx) with h | h
    · exact Complex.mem_slitPlane_iff.mpr (Or.inl h)
    · refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
      intro him
      exact hne x hx (Complex.ext (by rw [Complex.zero_re]; exact h.symm)
        (by rw [Complex.zero_im]; exact him))
  have hderiv : ∀ x ∈ Set.uIcc x0 x1,
      HasDerivAt (fun t : ℝ => Complex.log (f ((t : ℂ) + (T : ℂ) * I)))
        (logDeriv f ((x : ℂ) + (T : ℂ) * I)) x := by
    intro x hx
    have hfp : HasDerivAt (fun t : ℝ => f ((t : ℂ) + (T : ℂ) * I))
        (deriv f ((x : ℂ) + (T : ℂ) * I)) x := by
      simpa only [Function.comp_def, one_smul] using ((hdiff x hx).hasDerivAt).scomp x (hpath x)
    have hd := hfp.clog_real (hslit x hx)
    rwa [← logDeriv_apply] at hd
  have hFTC : (∫ x in x0..x1, logDeriv f ((x : ℂ) + (T : ℂ) * I))
      = Complex.log (f ((x1 : ℂ) + (T : ℂ) * I)) - Complex.log (f ((x0 : ℂ) + (T : ℂ) * I)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)
  have hval : DiffractionCore.argChangeHoriz f T x0 x1
      = Complex.arg (f ((x1 : ℂ) + (T : ℂ) * I)) - Complex.arg (f ((x0 : ℂ) + (T : ℂ) * I)) := by
    unfold DiffractionCore.argChangeHoriz
    rw [hFTC, Complex.sub_im, Complex.log_im, Complex.log_im]
  have ha1 : |Complex.arg (f ((x1 : ℂ) + (T : ℂ) * I))| ≤ Real.pi / 2 :=
    Complex.abs_arg_le_pi_div_two_iff.mpr (hpos x1 Set.right_mem_uIcc)
  have ha0 : |Complex.arg (f ((x0 : ℂ) + (T : ℂ) * I))| ≤ Real.pi / 2 :=
    Complex.abs_arg_le_pi_div_two_iff.mpr (hpos x0 Set.left_mem_uIcc)
  rw [hval, abs_le]
  rw [abs_le] at ha1 ha0
  constructor <;> linarith [ha1.1, ha1.2, ha0.1, ha0.2]

/-- **Either-sign non-strict confinement.**  `Re f` one sign (`≥ 0` OR `≤ 0`) and `f ≠ 0` on the
    segment ⟹ `|argChangeHoriz| ≤ π`.  The `Re f ≤ 0` case applies the previous lemma to `-f`. -/
theorem argChangeHoriz_abs_le_pi_of_re_sign' (f : ℂ → ℂ) (T x0 x1 : ℝ)
    (hdiff : ∀ x ∈ Set.uIcc x0 x1, DifferentiableAt ℂ f ((x : ℂ) + (T : ℂ) * I))
    (hcont : ContinuousOn (fun x : ℝ => logDeriv f ((x : ℂ) + (T : ℂ) * I)) (Set.uIcc x0 x1))
    (hne : ∀ x ∈ Set.uIcc x0 x1, f ((x : ℂ) + (T : ℂ) * I) ≠ 0)
    (hsign : (∀ x ∈ Set.uIcc x0 x1, 0 ≤ (f ((x : ℂ) + (T : ℂ) * I)).re) ∨
             (∀ x ∈ Set.uIcc x0 x1, (f ((x : ℂ) + (T : ℂ) * I)).re ≤ 0)) :
    |DiffractionCore.argChangeHoriz f T x0 x1| ≤ Real.pi := by
  have hln : ∀ w : ℂ, logDeriv (fun z => -f z) w = logDeriv f w := by
    intro w
    simpa [neg_one_mul] using logDeriv_const_mul (f := f) w (-1 : ℂ) (by norm_num)
  rcases hsign with hpos | hneg
  · exact argChangeHoriz_abs_le_pi_of_re_nonneg f T x0 x1 hdiff hcont hne hpos
  · have hdiff' : ∀ x ∈ Set.uIcc x0 x1, DifferentiableAt ℂ (fun z => -f z) ((x : ℂ) + (T : ℂ) * I) :=
      fun x hx => (hdiff x hx).neg
    have hcont' : ContinuousOn (fun x : ℝ => logDeriv (fun z => -f z) ((x : ℂ) + (T : ℂ) * I))
        (Set.uIcc x0 x1) := hcont.congr (fun x _ => hln _)
    have hne' : ∀ x ∈ Set.uIcc x0 x1, (fun z => -f z) ((x : ℂ) + (T : ℂ) * I) ≠ 0 :=
      fun x hx => neg_ne_zero.mpr (hne x hx)
    have hpos' : ∀ x ∈ Set.uIcc x0 x1, 0 ≤ ((fun z => -f z) ((x : ℂ) + (T : ℂ) * I)).re := by
      intro x hx; simp only [Complex.neg_re]; linarith [hneg x hx]
    have h4 := argChangeHoriz_abs_le_pi_of_re_nonneg (fun z => -f z) T x0 x1 hdiff' hcont' hne' hpos'
    have harg : DiffractionCore.argChangeHoriz (fun z => -f z) T x0 x1
        = DiffractionCore.argChangeHoriz f T x0 x1 := by
      unfold DiffractionCore.argChangeHoriz
      exact congrArg Complex.im (intervalIntegral.integral_congr (fun x _ => hln _))
    rwa [harg] at h4

end Backlund
