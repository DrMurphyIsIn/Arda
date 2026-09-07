/-  COMBINATION (kernel): all nontrivial zeta zeros up to height T lie on Re = 1/2.

    This is the capstone composition of:
    * `ZetaZeroConfinement.zero_in_band` (Task 3, this branch): every nontrivial zero up
      to height T lies in the band `[a, 1-a]` (derived from the effective dVP zero-free
      region + the functional equation).
    * `RHInBox.rh_in_box_of_certificate` (PR #312, this branch): every zero IN a box
      `[sigma0,sigma1]x[T0,T1]` lies on the critical line (derived from the argument
      principle + winding count).

    The combination: set `sigma0 = a, sigma1 = 1-a, T0 = 0, T1 = T`.  Confinement puts
    every nontrivial zero up to T inside the box.  Box-localization then forces it onto
    Re = 1/2.  The conclusion `∀ ρ, ζ ρ = 0 → 0 < ρ.im → ρ.im ≤ T → ρ.re = 1/2` is
    DERIVED from the two atoms; it is NOT assumed.

    RESIDUALS (honest, documented):
    * `hγ_all`: `∀ ρ, ζ ρ = 0 → 0 < ρ.im → ρ.im ≤ T → 55/16 ≤ |ρ.im|` -- no Mathlib
      fact that all nontrivial zeros have imaginary part at least 14 > 55/16 ~ 3.44.
      Discharged at any concrete T by the on-line sweep (e.g. at T=100, all 29 zeros
      have height ≥ 14).
    * `ha_half`: `a ≤ 1/2` -- needed to supply `hsig : a ≤ 1-a` to the box theorem.
      Follows from `ha0 : 0 < a` + `haC : a ≤ dlvpRateC / log T` in practice (for
      T ≥ 100 and dlvpRateC ≤ 1/1792, the ratio is much smaller than 1/2), but we
      carry it as a hypothesis to avoid adding the concrete bound computation here.
    * The Arb bundle (`harb`), winding value (`hwind`), and on-line zero Finset (`Ton`)
      at box `[a,1-a]x[0,T]` are external inputs, exactly as for `rh_in_box_of_certificate`.

    `conjecture1_proved = False`.  This is a kernel-verified CONDITIONAL theorem (all
    zeros up to T on the line, given the documented Arb inputs + the height floor), NOT
    a proof of the Riemann Hypothesis.
-/
import Mathlib
import DlvpZetaZeroFree
import ZetaZeroConfinement
import RHInBox

open Complex MeasureTheory Real
open scoped Topology

namespace AllZerosUpToHeight

/-- **All nontrivial zeta zeros up to height T lie on Re = 1/2** (combination theorem).

    Composes `ZetaZeroConfinement.zero_in_band` (every zero up to T is in `[a,1-a]`)
    with `RHInBox.rh_in_box_of_certificate` (every zero in the box `[a,1-a]x[0,T]` is on
    the critical line) to conclude that every nontrivial zero `ρ` with `0 < ρ.im ≤ T`
    satisfies `ρ.re = 1/2`.

    **Parameters:**
    - `a T : ℝ` — the band/box half-width and height bound (free variables).
    - `haC : a ≤ dlvpRateC / log T` — ties `a` to the effective dVP rate.
    - `ha0 : 0 < a` — positivity of the band half-width.
    - `ha_half : a ≤ 1/2` — so that `a ≤ 1-a` (needed by the box theorem).
    - `hT : 100 ≤ T` — height floor (dVP region requires log T > 0, i.e. T > 1).
    - `c : ℂ`, `R : ℝ`, `N : ℤ` — Blaschke ball center/radius and winding count (free).
    - `hRpos : 0 < R` — ball radius positive.
    - `hbox_ball` — the box `[a,1-a]x[0,T]` is contained in `ball c R`.
    - `hs1 : (1:ℂ) ∉ ball c R` — the pole at 1 is outside the ball.
    - `Ton : Finset ℂ` — on-line zeros of `riemannZeta` in the box (supplied by Arb sweep).
    - `hTline`, `hTzero`, `hTbox` — membership properties of `Ton`.
    - `hwind` — winding number of the logDeriv integral around the box equals `2πiN`.
    - `harb` — the Arb regularity bundle (boundary nonvanishing + integrability).
    - `hcount : N = Ton.card` — the winding count equals the number of on-line zeros.
    - `hγ_all` — documented residual: all nontrivial zeros up to T have |Im| ≥ 55/16.

    **Conclusion:** `∀ ρ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ T → ρ.re = 1/2`.

    conjecture1_proved = False. -/
theorem all_nontrivial_zeros_up_to_height_on_line
    (a T : ℝ)
    (haC : a ≤ ZeroFreeBridge.dlvpRateC / Real.log T)
    (ha0 : 0 < a)
    (ha_half : a ≤ 1 / 2)
    (hT : 100 ≤ T)
    (c : ℂ) (R : ℝ) (N : ℤ)
    (hRpos : 0 < R)
    (hbox_ball : ∀ ρ : ℂ, (a ≤ ρ.re ∧ ρ.re ≤ 1 - a) → ((0 : ℝ) ≤ ρ.im ∧ ρ.im ≤ T) →
      ρ ∈ Metric.ball c R)
    (hs1 : (1 : ℂ) ∉ Metric.ball c R)
    (Ton : Finset ℂ)
    (hTline : ∀ z ∈ Ton, z.re = 1 / 2)
    (hTzero : ∀ z ∈ Ton, riemannZeta z = 0)
    (hTbox : ∀ z ∈ Ton, (a ≤ z.re ∧ z.re ≤ 1 - a) ∧ ((0 : ℝ) ≤ z.im ∧ z.im ≤ T))
    (hwind : (∫ x in a..(1 - a), logDeriv riemannZeta (↑x + ((0 : ℝ) : ℂ) * I))
        - (∫ x in a..(1 - a), logDeriv riemannZeta (↑x + (T : ℂ) * I))
        + I • (∫ y in (0 : ℝ)..T, logDeriv riemannZeta (((1 - a : ℝ) : ℂ) + ↑y * I))
        - I • (∫ y in (0 : ℝ)..T, logDeriv riemannZeta ((a : ℂ) + ↑y * I))
      = 2 * π * I * (N : ℂ))
    (harb : ∀ (E : ℂ → ℂ),
      let s := RHInBoxAnalytic.zeroFinset c R hs1
      let d := (MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ)
      DifferentiableOn ℂ E (Set.Icc a (1 - a) ×ℂ Set.Icc (0 : ℝ) T) →
      (∀ z ∈ Metric.ball c R, riemannZeta z ≠ 0 →
        logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z) →
      (∀ x ∈ Set.uIcc a (1 - a), riemannZeta (↑x + ((0 : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc a (1 - a), riemannZeta (↑x + (T : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc (0 : ℝ) T, riemannZeta (((1 - a : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc (0 : ℝ) T, riemannZeta ((a : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ ρ ∈ s, a < ρ.re ∧ ρ.re < 1 - a ∧ (0 : ℝ) < ρ.im ∧ ρ.im < T) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + ((0 : ℝ) : ℂ) * I) - ρ)⁻¹) volume a (1 - a)) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + (T : ℂ) * I) - ρ)⁻¹) volume a (1 - a)) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => ((((1 - a : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume (0 : ℝ) T) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => (((a : ℂ) + ↑y * I) - ρ)⁻¹) volume (0 : ℝ) T) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + ((0 : ℝ) : ℂ) * I) - ρ)⁻¹) volume a (1 - a)) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + (T : ℂ) * I) - ρ)⁻¹) volume a (1 - a)) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((((1 - a : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) volume (0 : ℝ) T) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * (((a : ℂ) + ↑y * I) - ρ)⁻¹) volume (0 : ℝ) T) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + ((0 : ℝ) : ℂ) * I)) volume a (1 - a)) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + (T : ℂ) * I)) volume a (1 - a)) ∧
      (IntervalIntegrable (fun y : ℝ => E (((1 - a : ℝ) : ℂ) + ↑y * I)) volume (0 : ℝ) T) ∧
      (IntervalIntegrable (fun y : ℝ => E ((a : ℂ) + ↑y * I)) volume (0 : ℝ) T))
    (hcount : (N : ℤ) = (Ton.card : ℤ))
    (hγ_all : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ T → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ T → ρ.re = 1 / 2 := by
  intro ρ hzero him0 himT
  -- Step 1: confinement — ρ is in the band [a, 1-a].
  obtain ⟨hlo, hhi⟩ := ZetaZeroConfinement.zero_in_band a T haC ha0 hT hzero him0 himT
    (hγ_all ρ hzero him0 himT)
  -- Step 2: box-localization — every zero in [a,1-a]x[0,T] is on Re=1/2.
  have hsig : a ≤ 1 - a := by linarith
  have hTle : (0 : ℝ) ≤ T := by linarith
  exact RHInBox.rh_in_box_of_certificate a (1 - a) 0 T c R N hRpos hsig hTle
    hbox_ball hs1 Ton hTline hTzero hTbox hwind harb hcount
    ρ ⟨hlo, hhi⟩ ⟨le_of_lt him0, himT⟩ hzero

end AllZerosUpToHeight
