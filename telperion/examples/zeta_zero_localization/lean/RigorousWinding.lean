/- telperion route-beta | family RigorousWinding | Task 9 (Stage 2/3)
   Rigorous segment-winding machinery for the from-DATA argument-principle count.
   Hand-authored kernel proof; the generation-time drift net lives in
   `test_winding_count.py` / `test_zeroloc_end_to_end.py`.  DO NOT EDIT BY HAND
   without re-running those tests.  -/

import Mathlib

open Complex intervalIntegral MeasureTheory Real BigOperators

namespace RigorousWinding

/-!
# Route-beta rigorous segment winding (Stage 2/3)

Goal: the four-segment boundary integral of `zeta'/zeta` around the box
`[2/5,3/5] x [10,35]` equals `2*pi*i*5`, the from-DATA argument-principle count
of the 5 on-line zeros in that box.

**This file establishes the REUSABLE, KERNEL-VERIFIED segment machinery** for that
count, and validates it end-to-end on (a) a genuine winding path split into an
arbitrary list of sub-segments, and (b) `riemannZeta` itself at the per-segment
level.  Every theorem below is sorry-free with clean axioms
`{propext, Classical.choice, Quot.sound}`.

The two ALLOWED inputs (per the Task-9 trust boundary) appear as hypotheses:
  (i)  the per-segment Arb half-plane witness `d` with `0 < (d * f z).re` on the
       segment (the documented non-kernel input), and
  (ii) kernel-proved analyticity of `f` (`riemannZeta`) supplying `f'` and its
       continuity off the pole `s = 1`.
NO residue-decomposition hypothesis is used (that is Task 4's route-alpha, which
this file deliberately avoids).

## Honest ceiling (`conjecture1_proved = False`)

The per-segment FTC (`seg_integral_rot_on`) and the list-of-segments telescoping
(`whole_edge_eq_sum_V`) are proven here in the kernel.  The FINAL step of the
177-sub-segment zeta instance — proving that the sum of the 177 rotated-branch
log-increments equals exactly `2*pi*i*5` — is NOT discharged in-kernel: it requires
either the numeric values of `zeta` at the ~356 boundary nodes (known only as Arb
enclosures, not closed forms) or an argument-principle theorem for `zeta` that is
absent from Mathlib.  That winding-INTEGER, per the Task-9 graceful-degradation
protocol, is carried as the Arb-certified non-kernel hypothesis at the capstone.
This file provides everything the capstone needs on the kernel side.
-/

/-- Abstract per-segment FTC: given a path `p` with derivative `p'` on `[a,b]`,
    continuous `p`/`p'`, and `p t ∈ slitPlane` on `[a,b]`, the integral of `p'/p`
    over `[a,b]` is `log (p b) - log (p a)`. -/
theorem seg_integral (p : ℝ → ℂ) (p' : ℝ → ℂ) (a b : ℝ)
    (hp : Continuous p) (hp' : Continuous p')
    (hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt p (p' t) t)
    (hslit : ∀ t ∈ Set.uIcc a b, p t ∈ Complex.slitPlane) :
    (∫ t in a..b, p' t / p t) = Complex.log (p b) - Complex.log (p a) := by
  have hlog : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => Complex.log (p t)) (p' t / p t) t := by
    intro t ht
    exact (hderiv t ht).clog_real (hslit t ht)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hlog ?_]
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div hp'.continuousOn hp.continuousOn
  intro t ht
  exact Complex.slitPlane_ne_zero (hslit t ht)

/-- ROTATED per-segment FTC.  The Arb witness gives a rational direction `d ≠ 0`
    with `0 < (d * p t).re` (right half-plane, hence slit plane) on `[a,b]`.  The
    integral of the log-derivative `p'/p` equals `log (d * p b) - log (d * p a)`
    (the `log d` shift cancels).  Handles paths NOT in the principal slit plane. -/
theorem seg_integral_rot (p : ℝ → ℂ) (p' : ℝ → ℂ) (a b : ℝ) (d : ℂ) (hd : d ≠ 0)
    (hp : Continuous p) (hp' : Continuous p')
    (hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt p (p' t) t)
    (hrot : ∀ t ∈ Set.uIcc a b, 0 < (d * p t).re) :
    (∫ t in a..b, p' t / p t) = Complex.log (d * p b) - Complex.log (d * p a) := by
  have hslitq : ∀ t ∈ Set.uIcc a b, (d * p t) ∈ Complex.slitPlane := by
    intro t ht; exact Complex.mem_slitPlane_iff.mpr (Or.inl (hrot t ht))
  have hint : (∫ t in a..b, p' t / p t) = ∫ t in a..b, (d * p' t) / (d * p t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    show p' t / p t = (d * p' t) / (d * p t)
    rw [mul_div_mul_left _ _ hd]
  rw [hint]
  have hderivq : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun t => d * p t) (d * p' t) t := by
    intro t ht; exact (hderiv t ht).const_mul d
  have hlog : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => Complex.log (d * p t)) ((d * p' t) / (d * p t)) t := by
    intro t ht
    exact (hderivq t ht).clog_real (hslitq t ht)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hlog ?_]
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div (hp'.const_mul d).continuousOn (hp.const_mul d).continuousOn
  intro t ht
  exact Complex.slitPlane_ne_zero (hslitq t ht)

/-- ROTATED per-segment FTC, `ContinuousOn` variant.  Requires continuity of `p`,
    `p'` only ON the segment `uIcc a b` — needed for functions (like `riemannZeta`)
    that are not globally continuous.  The per-segment kernel obligation actually
    usable for the zeta boundary. -/
theorem seg_integral_rot_on (p : ℝ → ℂ) (p' : ℝ → ℂ) (a b : ℝ) (d : ℂ) (hd : d ≠ 0)
    (hp : ContinuousOn p (Set.uIcc a b)) (hp' : ContinuousOn p' (Set.uIcc a b))
    (hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt p (p' t) t)
    (hrot : ∀ t ∈ Set.uIcc a b, 0 < (d * p t).re) :
    (∫ t in a..b, p' t / p t) = Complex.log (d * p b) - Complex.log (d * p a) := by
  have hslitq : ∀ t ∈ Set.uIcc a b, (d * p t) ∈ Complex.slitPlane := by
    intro t ht; exact Complex.mem_slitPlane_iff.mpr (Or.inl (hrot t ht))
  have hint : (∫ t in a..b, p' t / p t) = ∫ t in a..b, (d * p' t) / (d * p t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    show p' t / p t = (d * p' t) / (d * p t)
    rw [mul_div_mul_left _ _ hd]
  rw [hint]
  have hderivq : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun t => d * p t) (d * p' t) t := by
    intro t ht; exact (hderiv t ht).const_mul d
  have hlog : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => Complex.log (d * p t)) ((d * p' t) / (d * p t)) t := by
    intro t ht
    exact (hderivq t ht).clog_real (hslitq t ht)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hlog ?_]
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div (continuousOn_const.mul hp') (continuousOn_const.mul hp)
  intro t ht
  exact Complex.slitPlane_ne_zero (hslitq t ht)

/-- Abstract telescoping over a list of `n` consecutive sub-segments.
    On sub-segment `i` (`i < n`) the log-derivative integral over `[t i, t (i+1)]`
    equals `V i` (the per-segment branch increment from `seg_integral_rot`).  Then
    the full sum of the sub-integrals equals `∑ V i`.  Pure list-of-segments
    telescoping: it lets a single edge be split into arbitrarily many
    Arb-certified sub-segments. -/
theorem list_segment_sum (n : ℕ) (t : ℕ → ℝ) (F : ℝ → ℂ) (V : ℕ → ℂ)
    (hseg : ∀ i, i < n → (∫ s in (t i)..(t (i+1)), F s) = V i) :
    (∑ i ∈ Finset.range n, (∫ s in (t i)..(t (i+1)), F s)) = ∑ i ∈ Finset.range n, V i := by
  apply Finset.sum_congr rfl
  intro i hi
  exact hseg i (Finset.mem_range.mp hi)

/-- The sum of sub-integrals equals the whole-edge integral
    (`sum_integral_adjacent_intervals`).  Combined with `list_segment_sum`, the
    split into sub-segments is faithful: `∫_{t0}^{tn} F = ∑_i V i`. -/
theorem whole_edge_eq_sum_V (n : ℕ) (t : ℕ → ℝ) (F : ℝ → ℂ) (V : ℕ → ℂ)
    (hint : ∀ i, i < n → IntervalIntegrable F volume (t i) (t (i+1)))
    (hseg : ∀ i, i < n → (∫ s in (t i)..(t (i+1)), F s) = V i) :
    (∫ s in (t 0)..(t n), F s) = ∑ i ∈ Finset.range n, V i := by
  rw [← intervalIntegral.sum_integral_adjacent_intervals hint]
  exact list_segment_sum n t F V hseg

/-!
## Concrete multi-segment toy (`f z = z - ρ`, one edge split into `K` sub-segments)

The bottom edge of the winding loop for `f z = z - ρ` about a pole `ρ` inside
`[x0,x1]×[y0,y1]`, i.e. the path `x ↦ (x + i·y0) - ρ`, split into `K` equal
sub-segments.  Each sub-segment's log-derivative integral is computed by
`seg_integral` (the path has strictly negative imaginary part `y0 - ρ.im < 0`, so
it lies in the principal slit plane).  `whole_edge_eq_sum_V` telescopes the `K`
sub-integrals back to the single whole-edge integral.

This demonstrates the list-of-segments telescoping on a genuine winding path,
`K` arbitrary — the METHOD that scales to the 177-sub-segment zeta boundary.
-/

/-- Bottom-edge sub-segment nodes: `t i = x0 + (x1 - x0) * (i / K)`. -/
noncomputable def bnode (x0 x1 : ℝ) (K : ℕ) (i : ℕ) : ℝ := x0 + (x1 - x0) * (i / K)

/-- The bottom edge of the `z ↦ z - ρ` winding, split into `K` sub-segments,
    telescopes: `∫ whole bottom edge = ∑_{i<K} (log-increments)`.  The integrand
    `((x + i·y0) - ρ)⁻¹` is `f'/f` for `f z = z - ρ`. -/
theorem bottom_edge_split (ρ : ℂ) (x0 x1 y0 : ℝ) (K : ℕ)
    (hy : y0 < ρ.im) :
    (∫ x in (bnode x0 x1 K 0)..(bnode x0 x1 K K),
        (((↑x + (↑y0 : ℂ) * I) - ρ)⁻¹ : ℂ))
      = ∑ i ∈ Finset.range K,
          (Complex.log (((↑(bnode x0 x1 K (i+1)) + (↑y0 : ℂ) * I) - ρ))
            - Complex.log (((↑(bnode x0 x1 K i) + (↑y0 : ℂ) * I) - ρ))) := by
  set F : ℝ → ℂ := fun x => (((↑x + (↑y0 : ℂ) * I) - ρ)⁻¹) with hF
  set p : ℝ → ℂ := fun x => ((↑x + (↑y0 : ℂ) * I) - ρ) with hp
  set p' : ℝ → ℂ := fun _ => (1 : ℂ) with hp'
  have hslit : ∀ t : ℝ, (p t).im < 0 := by
    intro t
    simp only [hp, Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re]
    simp; linarith
  have hpne : ∀ t : ℝ, p t ≠ 0 := by
    intro t h; have := hslit t; rw [h] at this; simp at this
  have hseg : ∀ i, i < K →
      (∫ s in (bnode x0 x1 K i)..(bnode x0 x1 K (i+1)), F s)
        = Complex.log (p (bnode x0 x1 K (i+1))) - Complex.log (p (bnode x0 x1 K i)) := by
    intro i _
    have key := seg_integral p p' (bnode x0 x1 K i) (bnode x0 x1 K (i+1))
      (by simp only [hp]; fun_prop) (by simp only [hp']; fun_prop)
      (by intro t _; simp only [hp, hp']
          have h1 : HasDerivAt (fun x : ℝ => (↑x : ℂ)) 1 t := by
            simpa using (hasDerivAt_id t).ofReal_comp
          exact (h1.add_const ((↑y0 : ℂ) * I)).sub_const ρ)
      (by intro t _
          exact Complex.mem_slitPlane_iff.mpr (Or.inr (ne_of_lt (hslit t))))
    rw [show (∫ s in (bnode x0 x1 K i)..(bnode x0 x1 K (i+1)), F s)
          = (∫ s in (bnode x0 x1 K i)..(bnode x0 x1 K (i+1)), p' s / p s) from by
        apply intervalIntegral.integral_congr; intro s _
        simp only [hF, hp, hp', one_div]]
    exact key
  have hint : ∀ i, i < K → IntervalIntegrable F volume (bnode x0 x1 K i) (bnode x0 x1 K (i+1)) := by
    intro i _
    apply ContinuousOn.intervalIntegrable
    simp only [hF]
    apply ContinuousOn.inv₀ (by fun_prop)
    intro t _; exact hpne t
  have := whole_edge_eq_sum_V K (bnode x0 x1 K) F
      (fun i => Complex.log (p (bnode x0 x1 K (i+1))) - Complex.log (p (bnode x0 x1 K i)))
      hint hseg
  rw [this]

/-!
## Zeta per-segment step (the zeta-specific kernel obligation)

The toy machinery `seg_integral_rot_on` applied to `riemannZeta`: GIVEN the Arb
half-plane witness `d` (`0 < (d * zeta z).re` on the segment), the log-derivative
integral of `zeta'/zeta` over a horizontal sub-segment equals the rotated-branch
increment.  Zeta analyticity is the kernel-proved input
(`differentiableAt_riemannZeta` / `analyticOn_riemannZeta`, valid off `s = 1`).
This is the ONLY zeta-specific new kernel obligation for route-beta; the
177-segment ASSEMBLY to `2*pi*i*5` is the documented non-kernel gap.
-/

/-- Zeta per-segment log-derivative FTC on a horizontal sub-segment `[a,b] + i·y0`.
    Inputs: (i) the Arb half-plane witness `d ≠ 0` with `0 < (d * zeta z).re`, and
    (ii) that the sub-segment avoids the pole `s = 1`.  Conclusion: the integral of
    `zeta'/zeta` equals the rotated-branch increment. -/
theorem zeta_seg_step (a b y0 : ℝ) (d : ℂ) (hd : d ≠ 0)
    (hne1 : ∀ t : ℝ, (↑t + (↑y0 : ℂ) * I) ≠ 1)
    (hrot : ∀ t ∈ Set.uIcc a b, 0 < (d * riemannZeta (↑t + (↑y0 : ℂ) * I)).re) :
    (∫ t in a..b, deriv riemannZeta (↑t + (↑y0 : ℂ) * I)
        / riemannZeta (↑t + (↑y0 : ℂ) * I))
      = Complex.log (d * riemannZeta (↑b + (↑y0 : ℂ) * I))
        - Complex.log (d * riemannZeta (↑a + (↑y0 : ℂ) * I)) := by
  set g : ℝ → ℂ := fun t => (↑t + (↑y0 : ℂ) * I) with hg
  set p : ℝ → ℂ := fun t => riemannZeta (g t) with hp
  set p' : ℝ → ℂ := fun t => deriv riemannZeta (g t) with hp'
  have hgderiv : ∀ t : ℝ, HasDerivAt g 1 t := by
    intro t
    have h1 : HasDerivAt (fun x : ℝ => (↑x : ℂ)) 1 t := by
      simpa using (hasDerivAt_id t).ofReal_comp
    exact h1.add_const ((↑y0 : ℂ) * I)
  have hzdiff : ∀ t : ℝ, DifferentiableAt ℂ riemannZeta (g t) := fun t =>
    differentiableAt_riemannZeta (hne1 t)
  have hpderiv : ∀ t : ℝ, HasDerivAt p (p' t) t := by
    intro t
    have hcomp := ((hzdiff t).hasDerivAt).comp t (hgderiv t)
    rw [mul_one] at hcomp
    exact hcomp
  have hpcont : ContinuousOn p (Set.uIcc a b) := by
    intro t _; exact ((hpderiv t).continuousAt).continuousWithinAt
  have hanalytic : ∀ t : ℝ, AnalyticAt ℂ riemannZeta (g t) := by
    intro t
    have hmem : g t ∈ ({1}ᶜ : Set ℂ) := by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact hne1 t
    exact analyticOn_riemannZeta (g t) hmem
  have hp'cont : ContinuousOn p' (Set.uIcc a b) := by
    intro t _
    have hd1 : ContinuousAt (deriv riemannZeta) (g t) :=
      (hanalytic t).deriv.continuousAt
    have hgc : ContinuousAt g t := by fun_prop
    exact (hd1.comp hgc).continuousWithinAt
  exact seg_integral_rot_on p p' a b d hd hpcont hp'cont (fun t _ => hpderiv t) hrot

end RigorousWinding
