/-
RvMBacklundAux — Backlund's S(T)=O(log T), PR 1: the auxiliary function.

The Riemann–von Mangoldt term `S(T) = (1/π)·arg ζ(1/2+iT)` is bounded by the argument variation of `ζ`
along `[1/2,2]+iT`, which is `≤ π·(#sign changes of Re ζ + 1)`.  Backlund bounds those sign changes by
the zeros of an ANALYTIC auxiliary function whose real-axis restriction IS `Re ζ`:

    F_T(z) := ½·(ζ(z + iT) + ζ(z − iT)).

Then `F_T(σ) = Re ζ(σ+iT)` for real `σ` (via `ζ(conj s) = conj ζ(s)`), so `F_T` is analytic, real on the
axis, and its real zeros dominate the sign changes of `Re ζ`.  Its zero-count is then bounded by Jensen
+ `zeta_log_bound` (later PRs) → `O(log T)`.

This PR builds the auxiliary function, its real-axis identity, and its analyticity (off the two shifted
poles `z = 1 ∓ iT`).  conjecture1_proved = False.
-/
import Mathlib

open Complex

namespace Backlund

/-- Backlund's auxiliary function at height `T`: `F_T(z) = ½·(ζ(z+iT) + ζ(z−iT))`. -/
noncomputable def backlundAux (T : ℝ) (z : ℂ) : ℂ :=
  (riemannZeta (z + (T : ℂ) * I) + riemannZeta (z - (T : ℂ) * I)) / 2

/-- **On the real axis the auxiliary function IS `Re ζ`.**  `F_T(σ) = Re ζ(σ+iT)` for real `σ`
    (from `riemannZeta_conj` and `z + conj z = 2·Re z`). -/
theorem backlundAux_ofReal (T σ : ℝ) :
    backlundAux T (σ : ℂ) = ((riemannZeta ((σ : ℂ) + (T : ℂ) * I)).re : ℂ) := by
  have harg : ((σ : ℂ) - (T : ℂ) * I) = (starRingEnd ℂ) ((σ : ℂ) + (T : ℂ) * I) := by
    rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]; ring
  unfold backlundAux
  rw [harg, riemannZeta_conj, Complex.add_conj]
  push_cast; ring

/-- The auxiliary function is analytic off the two shifted poles `z = 1 ∓ iT`. -/
theorem backlundAux_analyticAt (T : ℝ) {z : ℂ}
    (h1 : z + (T : ℂ) * I ≠ 1) (h2 : z - (T : ℂ) * I ≠ 1) :
    AnalyticAt ℂ (backlundAux T) z := by
  have hAO : AnalyticOnNhd ℂ riemannZeta {(1 : ℂ)}ᶜ :=
    DifferentiableOn.analyticOnNhd
      (fun w hw => (differentiableAt_riemannZeta hw).differentiableWithinAt) isOpen_compl_singleton
  have hf1 : AnalyticAt ℂ (fun w : ℂ => w + (T : ℂ) * I) z := analyticAt_id.add analyticAt_const
  have hf2 : AnalyticAt ℂ (fun w : ℂ => w - (T : ℂ) * I) z := analyticAt_id.sub analyticAt_const
  have ha1 : AnalyticAt ℂ (fun w : ℂ => riemannZeta (w + (T : ℂ) * I)) z := by
    have h := AnalyticAt.comp (g := riemannZeta) (f := fun w : ℂ => w + (T : ℂ) * I) (x := z)
      (hAO (z + (T : ℂ) * I) h1) hf1
    simpa [Function.comp_def] using h
  have ha2 : AnalyticAt ℂ (fun w : ℂ => riemannZeta (w - (T : ℂ) * I)) z := by
    have h := AnalyticAt.comp (g := riemannZeta) (f := fun w : ℂ => w - (T : ℂ) * I) (x := z)
      (hAO (z - (T : ℂ) * I) h2) hf2
    simpa [Function.comp_def] using h
  unfold backlundAux
  exact (ha1.add ha2).div_const

end Backlund
