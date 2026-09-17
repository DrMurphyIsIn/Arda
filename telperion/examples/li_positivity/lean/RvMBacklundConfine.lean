/-
RvMBacklundConfine — Backlund S(T)=O(log T), PR 4a: the half-plane argument-confinement lemma.

The foundational (and hardest) step of the Backlund `S(T)` bound.  On a horizontal subsegment where
`Re f > 0` throughout (equivalently: no sign change of `Re f`), the net argument change of `f` — which
is `argChangeHoriz f T x0 x1 = Im ∫ f'/f` — is `< π`, because the path stays in the right half-plane
`{Re > 0}` where `arg ∈ (−π/2, π/2)`.

  * `argChangeHoriz_abs_lt_pi_of_rePos` — if `f` is differentiable on the segment `[x0,x1]+iT`, its
    `logDeriv` is continuous there, and `Re f > 0` throughout, then `|argChangeHoriz f T x0 x1| < π`.

Proof: FTC turns `Im ∫ f'/f` into `arg f(x1+iT) − arg f(x0+iT)` (via `HasDerivAt.clog_real` +
`Complex.log_im = arg`), and `|arg z| < π/2` for `Re z > 0` (`Complex.abs_arg_lt_pi_div_two_iff`) gives
the `< π` bound.  Partitioning `[1/2,2]` at the sign changes and summing this over the `≤ count+1`
pieces is PR 4b.  conjecture1_proved = False.
-/
import Mathlib
import RvMDiffractionCore

open Complex MeasureTheory intervalIntegral

namespace Backlund

/-- **Half-plane argument confinement.**  If `Re f > 0` all along the horizontal segment, the net
    argument change of `f` there is `< π` in absolute value. -/
theorem argChangeHoriz_abs_lt_pi_of_rePos (f : ℂ → ℂ) (T x0 x1 : ℝ)
    (hdiff : ∀ x ∈ Set.uIcc x0 x1, DifferentiableAt ℂ f ((x : ℂ) + (T : ℂ) * I))
    (hcont : ContinuousOn (fun x : ℝ => logDeriv f ((x : ℂ) + (T : ℂ) * I)) (Set.uIcc x0 x1))
    (hpos : ∀ x ∈ Set.uIcc x0 x1, 0 < (f ((x : ℂ) + (T : ℂ) * I)).re) :
    |DiffractionCore.argChangeHoriz f T x0 x1| < Real.pi := by
  -- the horizontal path and its derivative
  have hpath : ∀ x : ℝ, HasDerivAt (fun t : ℝ => (t : ℂ) + (T : ℂ) * I) 1 x := by
    intro x
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := by simpa using (hasDerivAt_id x).ofReal_comp
    exact h1.add_const _
  -- log(f(path ·)) has derivative logDeriv f along the segment
  have hderiv : ∀ x ∈ Set.uIcc x0 x1,
      HasDerivAt (fun t : ℝ => Complex.log (f ((t : ℂ) + (T : ℂ) * I)))
        (logDeriv f ((x : ℂ) + (T : ℂ) * I)) x := by
    intro x hx
    have hfp : HasDerivAt (fun t : ℝ => f ((t : ℂ) + (T : ℂ) * I))
        (deriv f ((x : ℂ) + (T : ℂ) * I)) x := by
      simpa only [Function.comp_def, one_smul] using ((hdiff x hx).hasDerivAt).scomp x (hpath x)
    have hslit : f ((x : ℂ) + (T : ℂ) * I) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (hpos x hx))
    have hd := hfp.clog_real hslit
    rwa [← logDeriv_apply] at hd
  -- FTC: the integral is a difference of logs
  have hFTC : (∫ x in x0..x1, logDeriv f ((x : ℂ) + (T : ℂ) * I))
      = Complex.log (f ((x1 : ℂ) + (T : ℂ) * I)) - Complex.log (f ((x0 : ℂ) + (T : ℂ) * I)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)
  -- Im of that is the difference of args
  have hval : DiffractionCore.argChangeHoriz f T x0 x1
      = Complex.arg (f ((x1 : ℂ) + (T : ℂ) * I)) - Complex.arg (f ((x0 : ℂ) + (T : ℂ) * I)) := by
    unfold DiffractionCore.argChangeHoriz
    rw [hFTC, Complex.sub_im, Complex.log_im, Complex.log_im]
  -- both args are in (−π/2, π/2) since Re > 0
  have ha1 : |Complex.arg (f ((x1 : ℂ) + (T : ℂ) * I))| < Real.pi / 2 := by
    rw [Complex.abs_arg_lt_pi_div_two_iff]; exact Or.inl (hpos x1 (Set.right_mem_uIcc))
  have ha0 : |Complex.arg (f ((x0 : ℂ) + (T : ℂ) * I))| < Real.pi / 2 := by
    rw [Complex.abs_arg_lt_pi_div_two_iff]; exact Or.inl (hpos x0 (Set.left_mem_uIcc))
  rw [hval, abs_lt]
  rw [abs_lt] at ha1 ha0
  constructor <;> linarith [ha1.1, ha1.2, ha0.1, ha0.2]

end Backlund
