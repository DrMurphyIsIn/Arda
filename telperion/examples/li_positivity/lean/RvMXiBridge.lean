/-
RvMXiBridge — the RvM box-argument foundation, ported to the UPSTREAM `riemannXi`.

THE SHARED OBJECT.  Our v4.32 Riemann–von Mangoldt development is built on
`xiTele s = ½·s·(s−1)·completedRiemannZeta₀ s + ½`.  The upstream `LiCriterion`
(v4.34) defines `riemannXi` by the SAME formula, and `li_criterion_rh_iff` is
stated about `taylorCoeff riemannXi`.  So the two developments are about ONE
function.

This file lands the RvM reflection foundation — the `s ↦ 1−s` / `s ↦ s̄` folds
that our box argument principle rests on — directly for the upstream `riemannXi`,
reusing `riemannXi_one_sub`, `riemannXi_conj`, `xi_entire`.  It compiles on the
unified v4.34 island, next to `li_criterion_rh_iff`: a concrete kernel-level
demonstration that the RvM apparatus attaches to the exact object Li's criterion
uses.

HONEST SCOPE.  What this establishes: the RvM foundation ports cleanly and is
about the SAME `riemannXi` as the Li ladder — the shared-object anchor is real.
What it does NOT do: (1) the full RvM count `N(T)=θ/π+1+S` is not re-derived here
(that is the remaining port of ~140 v4.32 theorems); (2) NOTHING here links the
zero COUNT `N(T)` to the Li COEFFICIENTS `λ_n` — that is the explicit-formula /
Guinand–Weil mathematics, which neither development contains.  Unification makes a
count↔coefficient bridge POSSIBLE; it does not make it free.  conjecture1_proved
= False.
-/
import LiPositivity
import Lc.LiCriterion.Fidelity

namespace LiPositivity

open LiCriterion Complex

/-- **The ξ reflection** for the upstream `riemannXi`:
    `_root_.logDeriv riemannXi (1−s) = −_root_.logDeriv riemannXi s`, by differentiating the
    functional equation `riemannXi_one_sub`. -/
theorem logDeriv_riemannXi_reflect (s : ℂ) :
    _root_.logDeriv riemannXi (1 - s) = - _root_.logDeriv riemannXi s := by
  have hsymm : (fun z : ℂ => riemannXi (1 - z)) = riemannXi := funext riemannXi_one_sub
  have hd : DifferentiableAt ℂ riemannXi (1 - s) := xi_entire _
  have hinner : HasDerivAt (fun z : ℂ => (1 : ℂ) - z) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub 1
  have hcomp : HasDerivAt (fun z : ℂ => riemannXi (1 - z))
      (deriv riemannXi (1 - s) * (-1)) s := hd.hasDerivAt.comp s hinner
  have h1 := hcomp.deriv
  rw [hsymm] at h1
  have hkey : deriv riemannXi (1 - s) = - deriv riemannXi s := by linear_combination h1
  rw [logDeriv_apply, logDeriv_apply, riemannXi_one_sub, hkey]; ring

/-- **The ξ conjugation** for the upstream `riemannXi`:
    `_root_.logDeriv riemannXi (s̄) = conj (_root_.logDeriv riemannXi s)`, from `riemannXi_conj`
    via the Schwarz-reflection derivative `HasDerivAt.star_conj`. -/
theorem logDeriv_riemannXi_conj (s : ℂ) :
    _root_.logDeriv riemannXi ((starRingEnd ℂ) s) = (starRingEnd ℂ) (_root_.logDeriv riemannXi s) := by
  have hdf : DifferentiableAt ℂ riemannXi s := xi_entire s
  have h1 := hdf.hasDerivAt.star_conj
  have hfun : (star ∘ riemannXi ∘ (starRingEnd ℂ)) = riemannXi := by
    funext z; simp only [Function.comp_apply]; rw [riemannXi_conj z]; simp
  rw [hfun] at h1
  have hderiv : deriv riemannXi ((starRingEnd ℂ) s) = (starRingEnd ℂ) (deriv riemannXi s) := by
    have h2 : (starRingEnd ℂ) (deriv riemannXi s) = star (deriv riemannXi s) := rfl
    rw [h2]; exact h1.deriv
  rw [logDeriv_apply, logDeriv_apply, hderiv, riemannXi_conj s, ← map_div₀]

/-- **THE ξ FOLD, pointwise**, for the upstream `riemannXi`:
    `Re(_root_.logDeriv riemannXi (σ+iy)) + Re(_root_.logDeriv riemannXi ((1−σ)+iy)) = 0`.

    This is the entire, pole-free reflection identity that collapses the left
    half of the RvM box onto its right — now on the same `riemannXi` whose Li
    coefficients determine RH.  The RvM box-argument foundation, on the Li
    object.  conjecture1_proved = False. -/
theorem fold_pointwise_riemannXi (sigma y : ℝ) :
    (_root_.logDeriv riemannXi ((sigma : ℂ) + y * I)).re
      + (_root_.logDeriv riemannXi (((1 - sigma : ℝ) : ℂ) + y * I)).re = 0 := by
  set s : ℂ := (sigma : ℂ) + y * I with hs
  set s' : ℂ := ((1 - sigma : ℝ) : ℂ) + y * I with hs'
  have hconj : (1 : ℂ) - s = (starRingEnd ℂ) s' := by
    rw [hs, hs']; apply Complex.ext <;> simp
  have hrefl := logDeriv_riemannXi_reflect s
  rw [hconj, logDeriv_riemannXi_conj s'] at hrefl
  have hre := congrArg Complex.re hrefl
  simp only [Complex.conj_re, Complex.neg_re] at hre
  linarith [hre]

end LiPositivity
