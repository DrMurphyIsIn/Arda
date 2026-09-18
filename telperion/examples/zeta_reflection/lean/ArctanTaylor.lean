/-  ArctanTaylor.lean -- ANDÚRIL A4 θ-value instrument: the reusable arctan Taylor bracket.

    The θ-value route (`ThetaValue.lean`) needs, for the Euler/Weierstrass series
    `Im log Γ(x+iy) = y·log n − Σ_k arctan(y/(x+k))` (limit form), a KERNEL box for each
    `arctan(y/(x+k))`.  This file is the reusable arctan instrument that produces those boxes,
    with NO numeric hypotheses and NO special-function anchors (no ψ, no Γ).

    ## The instrument.

    For `u ≥ 0` and any truncation order `N`,

        |arctan u − atanPS u N| ≤ u^(2N+1)/(2N+1),        atanPS u N = Σ_{j<N} (−1)^j u^(2j+1)/(2j+1).

    This is the alternating Taylor bracket, proved RIGOROUSLY from the integral representation
    `arctan u = ∫₀ᵘ (1+t²)⁻¹` (Mathlib `integral_inv_one_add_sq`) via the finite geometric
    identity `(1+t²)⁻¹ = Σ_{j<N}(−t²)^j + (−t²)^N/(1+t²)` and the elementary remainder bound
    `|∫₀ᵘ (−t²)^N/(1+t²)| ≤ ∫₀ᵘ t^(2N) = u^(2N+1)/(2N+1)`.

    Two cheap corollaries used by the tail machinery (elementary, no integral):
      * `arctan_le_self`        : `arctan u ≤ u`               (0 ≤ u)
      * `self_sub_cube_le_arctan`: `u − u³/3 ≤ arctan u`       (0 ≤ u)

    All lemmas are GENERAL in `(u, N)` — the ThetaValue driver instantiates them per term.
    Guarded: `#print axioms arctan_bracket` = {propext, Classical.choice, Quot.sound}.

    conjecture1_proved = False.  A rigorous elementary arctan enclosure, a building block, NOT a
    proof of anything about ζ.
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open Real intervalIntegral MeasureTheory

namespace ArctanTaylor

/-- The `N`-term alternating arctan Taylor partial sum `Σ_{j<N} (−1)^j u^(2j+1)/(2j+1)`. -/
noncomputable def atanPS (u : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, (-1)^j * u^(2*j+1)/(2*j+1)

/-! ### The integral representation split. -/

/-- Integrating the finite geometric expansion term-by-term recovers `atanPS`. -/
theorem integral_polysum_eq_atanPS (u : ℝ) (N : ℕ) :
    (∫ t in (0:ℝ)..u, ∑ j ∈ Finset.range N, (-(t^2))^j) = atanPS u N := by
  rw [intervalIntegral.integral_finsetSum]
  · rw [atanPS]
    apply Finset.sum_congr rfl
    intro j _
    have heq : (fun t : ℝ => (-(t^2))^j) = (fun t : ℝ => (-1:ℝ)^j * t^(2*j)) := by
      funext t
      rw [show -(t^2) = (-1:ℝ) * t^2 from by ring, mul_pow, ← pow_mul]
    rw [heq, intervalIntegral.integral_const_mul, integral_pow, zero_pow (by omega), sub_zero]
    have hcast : ((2*j:ℕ):ℝ)+1 = 2*(j:ℝ)+1 := by push_cast; ring
    rw [show (2*j+1 : ℕ) = 2*j+1 from rfl, hcast]
    ring
  · intro j _
    exact (Continuous.intervalIntegrable (by fun_prop) _ _)

/-- `arctan u` decomposes as its Taylor partial sum plus the integral remainder. -/
theorem arctan_eq_ps_add_rem (u : ℝ) (N : ℕ) :
    arctan u = atanPS u N + ∫ t in (0:ℝ)..u, (-(t^2))^N / (1+t^2) := by
  have hint : arctan u = ∫ t in (0:ℝ)..u, (1+t^2)⁻¹ := by
    rw [integral_inv_one_add_sq, arctan_zero, sub_zero]
  have hsplit : ∀ t : ℝ, (1+t^2)⁻¹
      = (∑ j ∈ Finset.range N, (-(t^2))^j) + (-(t^2))^N /(1+t^2) := by
    intro t
    have hne : (-(t^2) : ℝ) ≠ 1 := by nlinarith [sq_nonneg t]
    rw [geom_sum_eq hne N]; field_simp; ring
  rw [hint,
    show (∫ t in (0:ℝ)..u, (1+t^2)⁻¹)
      = ∫ t in (0:ℝ)..u, ((∑ j ∈ Finset.range N, (-(t^2))^j) + (-(t^2))^N /(1+t^2)) from by
        apply intervalIntegral.integral_congr; intro t _; exact hsplit t]
  rw [intervalIntegral.integral_add]
  · rw [integral_polysum_eq_atanPS]
  · exact (Continuous.intervalIntegrable (by fun_prop) _ _)
  · apply Continuous.intervalIntegrable
    apply Continuous.div (by fun_prop) (by fun_prop) (fun t => by positivity)

/-! ### The remainder bound. -/

/-- The integral remainder is bounded by `u^(2N+1)/(2N+1)` for `0 ≤ u`. -/
theorem rem_abs_le (u : ℝ) (hu : 0 ≤ u) (N : ℕ) :
    |(∫ t in (0:ℝ)..u, (-(t^2))^N / (1+t^2))| ≤ u^(2*N+1)/(2*N+1) := by
  have hcont : Continuous (fun t : ℝ => (-(t^2))^N / (1+t^2)) :=
    Continuous.div (by fun_prop) (by fun_prop) (fun t => by positivity)
  have hintf : IntervalIntegrable (fun t => (-(t^2))^N / (1+t^2)) volume 0 u :=
    hcont.intervalIntegrable _ _
  have habs_int : IntervalIntegrable (fun t => |(-(t^2))^N / (1+t^2)|) volume 0 u := hintf.abs
  have hpow_int : IntervalIntegrable (fun t => t^(2*N)) volume 0 u :=
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  have h1 : |(∫ t in (0:ℝ)..u, (-(t^2))^N / (1+t^2))|
      ≤ ∫ t in (0:ℝ)..u, |(-(t^2))^N / (1+t^2)| := by
    have := intervalIntegral.abs_integral_le_integral_abs (f := fun t => (-(t^2))^N / (1+t^2))
      (a := 0) (b := u) (μ := volume) hu
    simpa using this
  have h2 : (∫ t in (0:ℝ)..u, |(-(t^2))^N / (1+t^2)|) ≤ ∫ t in (0:ℝ)..u, t^(2*N) := by
    apply intervalIntegral.integral_mono_on hu habs_int hpow_int
    intro t ht
    have hdenpos : (0:ℝ) < 1 + t^2 := by positivity
    rw [abs_div]
    have hnum : |(-(t^2))^N| = t^(2*N) := by
      rw [abs_pow, abs_neg, abs_of_nonneg (sq_nonneg t), ← pow_mul]
    rw [hnum, abs_of_pos hdenpos]
    have htp : (0:ℝ) ≤ t^(2*N) := by
      rw [pow_mul]; positivity
    apply div_le_self htp (by nlinarith [sq_nonneg t])
  have h3 : (∫ t in (0:ℝ)..u, t^(2*N)) = u^(2*N+1)/(2*N+1) := by
    rw [integral_pow, zero_pow (by omega), sub_zero]; push_cast; ring
  linarith [h1, h2, h3.le, h3.ge]

/-! ### THE INSTRUMENT: the two-sided arctan Taylor bracket. -/

/-- **Arctan Taylor bracket.**  For `0 ≤ u` and any `N`, `arctan u` is within
    `u^(2N+1)/(2N+1)` of its `N`-term Taylor partial sum. -/
theorem arctan_bracket (u : ℝ) (hu : 0 ≤ u) (N : ℕ) :
    |arctan u - atanPS u N| ≤ u^(2*N+1)/(2*N+1) := by
  rw [arctan_eq_ps_add_rem u N,
    show atanPS u N + (∫ t in (0:ℝ)..u, (-(t^2))^N / (1+t^2)) - atanPS u N
      = (∫ t in (0:ℝ)..u, (-(t^2))^N / (1+t^2)) from by ring]
  exact rem_abs_le u hu N

/-! ### Elementary corollaries (no integral) for the far-tail machinery. -/

/-- `arctan u ≤ u` for `0 ≤ u`. -/
theorem arctan_le_self {u : ℝ} (hu : 0 ≤ u) : arctan u ≤ u := by
  set g : ℝ → ℝ := fun y => y - arctan y with hg
  have hderiv : ∀ x, HasDerivAt g (1 - 1/(1+x^2)) x := fun x =>
    (hasDerivAt_id x).sub (Real.hasDerivAt_arctan x)
  have hmono : Monotone g := by
    apply monotone_of_deriv_nonneg
    · exact fun x => (hderiv x).differentiableAt
    · intro x
      rw [(hderiv x).deriv]
      have hpos : (0:ℝ) < 1 + x^2 := by positivity
      rw [sub_nonneg, div_le_one hpos]; nlinarith [sq_nonneg x]
  have := hmono hu
  simp only [hg, arctan_zero, sub_zero] at this
  linarith

/-- `u − u³/3 ≤ arctan u` for `0 ≤ u`. -/
theorem self_sub_cube_le_arctan {u : ℝ} (hu : 0 ≤ u) : u - u^3/3 ≤ arctan u := by
  set h : ℝ → ℝ := fun y => arctan y - (y - y^3/3) with hh
  have hderiv : ∀ x, HasDerivAt h (1/(1+x^2) - (1 - x^2)) x := by
    intro x
    have hp : HasDerivAt (fun y : ℝ => y^3/3) (x^2) x := by
      have : HasDerivAt (fun y : ℝ => y^3/3) ((3:ℕ) * x^(3-1)/3) x :=
        (hasDerivAt_pow 3 x).div_const 3
      simpa using this
    have hid : HasDerivAt (fun y : ℝ => y) (1:ℝ) x := hasDerivAt_id x
    have hc : HasDerivAt (fun y : ℝ => y - y^3/3) (1 - x^2) x := hid.sub hp
    exact (Real.hasDerivAt_arctan x).sub hc
  have hmono : Monotone h := by
    apply monotone_of_deriv_nonneg
    · exact fun x => (hderiv x).differentiableAt
    · intro x
      rw [(hderiv x).deriv]
      have hpos : (0:ℝ) < 1 + x^2 := by positivity
      have key : 1/(1+x^2) - (1 - x^2) = x^4/(1+x^2) := by field_simp; ring
      rw [key]; positivity
  have := hmono hu
  simp only [hh, arctan_zero, zero_sub] at this
  linarith

end ArctanTaylor
