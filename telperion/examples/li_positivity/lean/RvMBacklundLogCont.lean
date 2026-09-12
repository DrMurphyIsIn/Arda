/-
RvMBacklundLogCont — Backlund S(T)=O(log T), PR 6: discharging `hlogcont`.

The `S(T)=O(log T)` bound (PR 5 step 4) carried two hypotheses: `ζ ≠ 0` on the segment (`hζne`, the
genuine `S(T)`-jump caveat) and `logDeriv ζ` continuity there (`hlogcont`).  The second is derivable from
the first plus ζ-analyticity: `logDeriv ζ = deriv ζ / ζ`, and on `[1/2,2]+iT` (which avoids the pole
`s=1` for `T ≥ 4`) both `ζ` and `deriv ζ` are analytic — hence continuous — and `ζ ≠ 0`, so the quotient
is continuous.

  * `continuousOn_logDeriv_zeta_segment` — derives `hlogcont` from `T ≥ 4` and `hζne`.
  * `riemannS_abs_le_log_of_ne_zero` — the slimmed `S(T)=O(log T)`, carrying ONLY `hζne`.

conjecture1_proved = False.
-/
import Mathlib
import RvMBacklundS

open Complex MeasureTheory

namespace Backlund

/-- **`logDeriv ζ` is continuous along `[1/2,2]+iT`** (from ζ-analyticity and `ζ ≠ 0`). -/
theorem continuousOn_logDeriv_zeta_segment {T : ℝ} (hT : 4 ≤ T)
    (hζne : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2, riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0) :
    ContinuousOn (fun x : ℝ => logDeriv riemannZeta ((x : ℂ) + (T : ℂ) * I))
      (Set.Icc (1 / 2 : ℝ) 2) := by
  have hne1 : ∀ x : ℝ, ((x : ℂ) + (T : ℂ) * I) ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    have := congrArg Complex.im hx
    simp at this; linarith
  have hAO : AnalyticOnNhd ℂ riemannZeta ({(1 : ℂ)}ᶜ) :=
    DifferentiableOn.analyticOnNhd
      (fun w hw => (differentiableAt_riemannZeta hw).differentiableWithinAt) isOpen_compl_singleton
  have hpath : ContinuousOn (fun x : ℝ => (x : ℂ) + (T : ℂ) * I) (Set.Icc (1 / 2 : ℝ) 2) :=
    (Complex.continuous_ofReal.add continuous_const).continuousOn
  have hmaps : Set.MapsTo (fun x : ℝ => (x : ℂ) + (T : ℂ) * I) (Set.Icc (1 / 2 : ℝ) 2)
      ({(1 : ℂ)}ᶜ) := fun x _ => hne1 x
  have hζpath : ContinuousOn (fun x : ℝ => riemannZeta ((x : ℂ) + (T : ℂ) * I))
      (Set.Icc (1 / 2 : ℝ) 2) := hAO.continuousOn.comp hpath hmaps
  have hdζpath : ContinuousOn (fun x : ℝ => deriv riemannZeta ((x : ℂ) + (T : ℂ) * I))
      (Set.Icc (1 / 2 : ℝ) 2) := hAO.deriv.continuousOn.comp hpath hmaps
  have heq : (fun x : ℝ => logDeriv riemannZeta ((x : ℂ) + (T : ℂ) * I))
      = fun x : ℝ => deriv riemannZeta ((x : ℂ) + (T : ℂ) * I)
          / riemannZeta ((x : ℂ) + (T : ℂ) * I) := by
    funext x; rw [logDeriv_apply]
  rw [heq]
  exact hdζpath.div hζpath (fun x hx => hζne x hx)

/-- **`S(T)=O(log T)`, carrying only `ζ ≠ 0`.**  The `logDeriv ζ` continuity hypothesis of
    `riemannS_abs_le_log` is discharged from ζ-analyticity. -/
theorem riemannS_abs_le_log_of_ne_zero {T : ℝ} (hT : 4 ≤ T)
    (hζne : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2, riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0) :
    |DiffractionCore.riemannS T|
      ≤ Real.log ((4 * T + 19) / ‖backlundAux T ((2 : ℝ) : ℂ)‖) / Real.log (7 / 4 / (3 / 2)) + 2 :=
  riemannS_abs_le_log hT hζne (continuousOn_logDeriv_zeta_segment hT hζne)

end Backlund
