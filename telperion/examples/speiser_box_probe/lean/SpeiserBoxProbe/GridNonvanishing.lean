/-
  # The grid-modulus non-vanishing instrument

  A general, unconditional, kernel-clean replacement for a winding/argument-principle
  certificate in the special case where the target is *zero-freeness on a convex region*
  rather than a zero *count*.

  If `f` is holomorphic on a convex region `R`, `‖f'‖ ≤ M` on `R`, a finite set `G ⊆ R`
  is a `δ`-net of `R`, and `‖f‖ ≥ L` at every net point with `M * δ < L`, then `f` has no
  zero on `R`.  The proof is the mean-value inequality on a convex set: moving at most `δ`
  from a net point changes `‖f‖` by at most `M * δ`, which is not enough to reach `0`.

  Why this shape rather than a winding integral: a winding certificate for `f` needs the
  integrand `f'/f` and hence, when `f = zeta'`, a *numerical evaluator for `zeta''`* along
  the contour.  The instrument below needs only a crude *uniform upper bound* on `zeta''`
  plus finitely many point lower bounds on `zeta'` -- strictly less numerical machinery.
  The price is that it certifies "no zeros" only, never a nonzero zero count.

  Nothing in this file mentions the Riemann Hypothesis and nothing here is a step toward
  it.  conjecture1_proved = False.
-/
import Mathlib

open Complex

namespace SpeiserBoxProbe

/-- Bound a complex modulus by bounding the sum of squared coordinate displacements. -/
theorem norm_sub_le_of_sq_le {z g : ℂ} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : (z.re - g.re) ^ 2 + (z.im - g.im) ^ 2 ≤ δ ^ 2) : ‖z - g‖ ≤ δ := by
  have hns : Complex.normSq (z - g) = (z.re - g.re) ^ 2 + (z.im - g.im) ^ 2 := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]; ring
  rw [Complex.norm_def, hns]
  calc Real.sqrt ((z.re - g.re) ^ 2 + (z.im - g.im) ^ 2)
      ≤ Real.sqrt (δ ^ 2) := Real.sqrt_le_sqrt h
    _ = δ := Real.sqrt_sq hδ

/-- **The grid-modulus non-vanishing instrument.**

    `R` convex, `f` holomorphic on `R` with `‖deriv f‖ ≤ M` there, `G` a `δ`-net of `R`
    contained in `R`, `‖f‖ ≥ L` on `G`, and the *gap condition* `M * δ < L`.  Then `f`
    is zero-free on `R`.

    The gap condition is the whole certificate: it is what an emitter must re-derive from
    the grid geometry and the claimed constants, and refuse if it fails. -/
theorem nonvanishing_of_grid
    {f : ℂ → ℂ} {R G : Set ℂ} {M δ L : ℝ}
    (hconv : Convex ℝ R)
    (hderiv : ∀ z ∈ R, HasDerivWithinAt f (deriv f z) R z)
    (hM : ∀ z ∈ R, ‖deriv f z‖ ≤ M)
    (hcover : ∀ z ∈ R, ∃ g ∈ G, ‖z - g‖ ≤ δ)
    (hGR : G ⊆ R)
    (hL : ∀ g ∈ G, L ≤ ‖f g‖)
    (hgap : M * δ < L) :
    ∀ z ∈ R, f z ≠ 0 := by
  intro z hz hfz
  obtain ⟨g, hgG, hzg⟩ := hcover z hz
  have hgR : g ∈ R := hGR hgG
  have hM0 : (0 : ℝ) ≤ M := le_trans (norm_nonneg _) (hM z hz)
  have key : ‖f z - f g‖ ≤ M * ‖z - g‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hM hconv hgR hz
  have hzero : ‖f z - f g‖ = ‖f g‖ := by rw [hfz, zero_sub, norm_neg]
  rw [hzero] at key
  have : M * ‖z - g‖ ≤ M * δ := mul_le_mul_of_nonneg_left hzg hM0
  have hfin : ‖f g‖ ≤ M * δ := le_trans key this
  have := hL g hgG
  linarith

end SpeiserBoxProbe
