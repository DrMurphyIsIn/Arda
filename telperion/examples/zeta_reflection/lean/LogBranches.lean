/-  LogBranches.lean -- A2 Theorem 3: the FTC / branch bridge.

    Restates and PROVES the statement drafted in `LogBranchesStub.lean`:

        argChangeVert_eq_im_log_sub   (the load-bearing vertical bridge)
        argChangeHoriz_eq_im_log_sub  (the rotation-free horizontal variant)

    "For `f` with a holomorphic branch `L` on a neighborhood of the segment, with
     `deriv L = logDeriv f` pointwise there and `f` nonvanishing on the segment, the
     continuous argument change ALONG the segment equals the imaginary-part difference
     of `L` at the endpoints."

    This converts FOUR of the five box-edge argument quantities (per the ANDÚRIL plan)
    from interval integrals to POINT evaluations of an explicit log-branch `L` (the
    Stirling/Binet branch for the Γℝ edges, the prime-power Dirichlet branch for the
    Re=2 ζ edge).  No rigorous quadrature is needed downstream.

    Proof shape (vertical): the path `g y := L (σ + i y)` has, by the chain rule,
    `HasDerivAt g (I * logDeriv f (σ + i y)) y` on the segment (using `AnalyticOnNhd`
    for differentiability of `L` and the hypothesis `deriv L = logDeriv f` for the
    value).  FTC-2 (`intervalIntegral.integral_eq_sub_of_hasDerivAt`) gives
    `∫ y, I * logDeriv f (σ+iy) = g T1 - g T0 = L(top) - L(bottom)`.  Pulling out `I`
    and taking `.im`, the `i`-rotation identity `(I * w).im = w.re` (`Complex.mul_I_im`)
    turns `(∫ logDeriv f).re = argChangeVert` into `(L(top) - L(bottom)).im`.  The
    `.re ↔ .im` bookkeeping mirrors `DiffractionCore.argChangeL_sub_const`.

    The horizontal variant is rotation-free: the path derivative is `1`, so
    `argChangeHoriz = (∫ logDeriv f).im = (L(right) - L(left)).im` directly.

    conjecture1_proved = False.
-/
import DiffractionCore

open Complex intervalIntegral

namespace ZetaReflection

/-- **Vertical FTC bridge (A2 Theorem 3).**  For `f` with a holomorphic log-branch `L`
    on an open neighborhood `S` of the vertical segment `{σ + i y : y ∈ [T0,T1]}`
    (`deriv L = logDeriv f` on `S`), the argument change UP the segment equals the
    imaginary-part difference of `L` at the endpoints:
    `argChangeVert f σ T0 T1 = Im (L (σ + i T1)) − Im (L (σ + i T0))`. -/
theorem argChangeVert_eq_im_log_sub
    (f L : ℂ → ℂ) (σ T0 T1 : ℝ) (S : Set ℂ)
    (hT : T0 ≤ T1)
    (_hS : IsOpen S)
    (hseg : ∀ y : ℝ, y ∈ Set.Icc T0 T1 → ((σ : ℂ) + (y : ℂ) * I) ∈ S)
    (hana : AnalyticOnNhd ℂ L S)
    (hderiv : ∀ z ∈ S, deriv L z = logDeriv f z)
    (_hf : ∀ y : ℝ, y ∈ Set.Icc T0 T1 → f ((σ : ℂ) + (y : ℂ) * I) ≠ 0) :
    DiffractionCore.argChangeVert f σ T0 T1
      = (L ((σ : ℂ) + (T1 : ℂ) * I)).im - (L ((σ : ℂ) + (T0 : ℂ) * I)).im := by
  -- The path `g y = L (σ + i y)` and its derivative `I * logDeriv f (σ + i y)`.
  -- Segment membership on the FTC integration interval `uIcc T0 T1 = Icc T0 T1`.
  have huIcc : Set.uIcc T0 T1 = Set.Icc T0 T1 := Set.uIcc_of_le hT
  -- Chain-rule derivative of the composed path on the segment.
  have hpathderiv : ∀ y ∈ Set.uIcc T0 T1,
      HasDerivAt (fun y : ℝ => L ((σ : ℂ) + (y : ℂ) * I))
        (I * logDeriv f ((σ : ℂ) + (y : ℂ) * I)) y := by
    intro y hy
    rw [huIcc] at hy
    have hzS : ((σ : ℂ) + (y : ℂ) * I) ∈ S := hseg y hy
    -- inner path `y ↦ σ + i y` has derivative `I`
    have hpath : HasDerivAt (fun y : ℝ => (σ : ℂ) + (y : ℂ) * I) I y := by
      have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := by
        simpa using (hasDerivAt_id y).ofReal_comp
      have h2 : HasDerivAt (fun y : ℝ => (y : ℂ) * I) I y := by
        simpa using h1.mul_const I
      simpa using h2.const_add (σ : ℂ)
    -- `L` is differentiable at the segment point (open set + AnalyticOnNhd)
    have hLdiff : HasDerivAt L (deriv L ((σ : ℂ) + (y : ℂ) * I)) ((σ : ℂ) + (y : ℂ) * I) :=
      (hana ((σ : ℂ) + (y : ℂ) * I) hzS).differentiableAt.hasDerivAt
    -- rewrite `deriv L = logDeriv f` at that point
    rw [hderiv _ hzS] at hLdiff
    -- chain rule: derivative of `L ∘ path` is `logDeriv f · I = I · logDeriv f`
    have hcomp := HasDerivAt.scomp y hLdiff hpath
    rw [Function.comp_def] at hcomp
    simpa [smul_eq_mul, mul_comm] using hcomp
  -- continuity of the integrand `logDeriv f (σ+iy) = deriv L (σ+iy)` from analyticity of `deriv L`
  have hpathc : Continuous (fun y : ℝ => (σ : ℂ) + (y : ℂ) * I) := by fun_prop
  have hcontD : ContinuousOn (fun y : ℝ => deriv L ((σ : ℂ) + (y : ℂ) * I))
      (Set.uIcc T0 T1) := by
    intro y hy
    rw [huIcc] at hy
    have hzS : ((σ : ℂ) + (y : ℂ) * I) ∈ S := hseg y hy
    have hcomp : ContinuousAt (fun y : ℝ => deriv L ((σ : ℂ) + (y : ℂ) * I)) y :=
      ContinuousAt.comp (g := deriv L) (f := fun y : ℝ => (σ : ℂ) + (y : ℂ) * I)
        ((hana.deriv ((σ : ℂ) + (y : ℂ) * I) hzS).continuousAt) hpathc.continuousAt
    exact hcomp.continuousWithinAt
  have hcont0 : ContinuousOn (fun y : ℝ => logDeriv f ((σ : ℂ) + (y : ℂ) * I))
      (Set.uIcc T0 T1) := by
    refine hcontD.congr ?_
    intro y hy
    rw [huIcc] at hy
    exact (hderiv _ (hseg y hy)).symm
  have hcont : ContinuousOn (fun y : ℝ => I * logDeriv f ((σ : ℂ) + (y : ℂ) * I))
      (Set.uIcc T0 T1) := continuousOn_const.mul hcont0
  have hInt : IntervalIntegrable
      (fun y : ℝ => I * logDeriv f ((σ : ℂ) + (y : ℂ) * I))
      MeasureTheory.volume T0 T1 :=
    hcont.intervalIntegrable
  -- FTC-2 on the composed path
  have hFTC : (∫ y in T0..T1, I * logDeriv f ((σ : ℂ) + (y : ℂ) * I))
      = L ((σ : ℂ) + (T1 : ℂ) * I) - L ((σ : ℂ) + (T0 : ℂ) * I) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hpathderiv hInt
  -- pull `I` out of the integral
  have hpull : (∫ y in T0..T1, I * logDeriv f ((σ : ℂ) + (y : ℂ) * I))
      = I * ∫ y in T0..T1, logDeriv f ((σ : ℂ) + (y : ℂ) * I) := by
    rw [intervalIntegral.integral_const_mul]
  -- combine: I * (∫ logDeriv f) = L(top) - L(bottom); take `.im` and use `(I*w).im = w.re`
  rw [hpull] at hFTC
  unfold DiffractionCore.argChangeVert
  -- `(I * ∫ logDeriv f).im = (∫ logDeriv f).re = argChangeVert`
  have him := congrArg Complex.im hFTC
  rw [Complex.I_mul_im] at him
  rw [him, Complex.sub_im]

/-- **Horizontal FTC bridge (A2 Theorem 3, rotation-free variant).**  For `f` with a
    holomorphic log-branch `L` on an open neighborhood `S` of the horizontal segment
    `{x + i T : x ∈ [x0,x1]}` (`deriv L = logDeriv f` on `S`), the argument change ALONG
    the segment equals the imaginary-part difference of `L` at the endpoints:
    `argChangeHoriz f T x0 x1 = Im (L (x1 + i T)) − Im (L (x0 + i T))`.
    The path derivative is `1`, so there is no `i`-rotation: `argChangeHoriz` is `(∫).im`
    directly. -/
theorem argChangeHoriz_eq_im_log_sub
    (f L : ℂ → ℂ) (T x0 x1 : ℝ) (S : Set ℂ)
    (hx : x0 ≤ x1)
    (_hS : IsOpen S)
    (hseg : ∀ x : ℝ, x ∈ Set.Icc x0 x1 → ((x : ℂ) + (T : ℂ) * I) ∈ S)
    (hana : AnalyticOnNhd ℂ L S)
    (hderiv : ∀ z ∈ S, deriv L z = logDeriv f z)
    (_hf : ∀ x : ℝ, x ∈ Set.Icc x0 x1 → f ((x : ℂ) + (T : ℂ) * I) ≠ 0) :
    DiffractionCore.argChangeHoriz f T x0 x1
      = (L ((x1 : ℂ) + (T : ℂ) * I)).im - (L ((x0 : ℂ) + (T : ℂ) * I)).im := by
  have huIcc : Set.uIcc x0 x1 = Set.Icc x0 x1 := Set.uIcc_of_le hx
  -- chain-rule derivative of the composed path; inner path has derivative `1`
  have hpathderiv : ∀ x ∈ Set.uIcc x0 x1,
      HasDerivAt (fun x : ℝ => L ((x : ℂ) + (T : ℂ) * I))
        (logDeriv f ((x : ℂ) + (T : ℂ) * I)) x := by
    intro x hx'
    rw [huIcc] at hx'
    have hzS : ((x : ℂ) + (T : ℂ) * I) ∈ S := hseg x hx'
    have hpath : HasDerivAt (fun x : ℝ => (x : ℂ) + (T : ℂ) * I) 1 x := by
      have h1 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 x := by
        simpa using (hasDerivAt_id x).ofReal_comp
      simpa using h1.add_const ((T : ℂ) * I)
    have hLdiff : HasDerivAt L (deriv L ((x : ℂ) + (T : ℂ) * I)) ((x : ℂ) + (T : ℂ) * I) :=
      (hana ((x : ℂ) + (T : ℂ) * I) hzS).differentiableAt.hasDerivAt
    rw [hderiv _ hzS] at hLdiff
    have hcomp := HasDerivAt.scomp x hLdiff hpath
    rw [Function.comp_def] at hcomp
    simpa [smul_eq_mul] using hcomp
  have hpathc : Continuous (fun x : ℝ => (x : ℂ) + (T : ℂ) * I) := by fun_prop
  have hcontD : ContinuousOn (fun x : ℝ => deriv L ((x : ℂ) + (T : ℂ) * I))
      (Set.uIcc x0 x1) := by
    intro x hx'
    rw [huIcc] at hx'
    have hzS : ((x : ℂ) + (T : ℂ) * I) ∈ S := hseg x hx'
    have hcomp : ContinuousAt (fun x : ℝ => deriv L ((x : ℂ) + (T : ℂ) * I)) x :=
      ContinuousAt.comp (g := deriv L) (f := fun x : ℝ => (x : ℂ) + (T : ℂ) * I)
        ((hana.deriv ((x : ℂ) + (T : ℂ) * I) hzS).continuousAt) hpathc.continuousAt
    exact hcomp.continuousWithinAt
  have hcont : ContinuousOn (fun x : ℝ => logDeriv f ((x : ℂ) + (T : ℂ) * I))
      (Set.uIcc x0 x1) := by
    refine hcontD.congr ?_
    intro x hx'
    rw [huIcc] at hx'
    exact (hderiv _ (hseg x hx')).symm
  have hInt : IntervalIntegrable
      (fun x : ℝ => logDeriv f ((x : ℂ) + (T : ℂ) * I)) MeasureTheory.volume x0 x1 :=
    hcont.intervalIntegrable
  have hFTC : (∫ x in x0..x1, logDeriv f ((x : ℂ) + (T : ℂ) * I))
      = L ((x1 : ℂ) + (T : ℂ) * I) - L ((x0 : ℂ) + (T : ℂ) * I) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hpathderiv hInt
  unfold DiffractionCore.argChangeHoriz
  rw [hFTC, Complex.sub_im]
