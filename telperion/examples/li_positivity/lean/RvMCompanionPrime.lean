/-
RvMCompanionPrime — Route P, Brick D1: the companion IS the log-prime spectrum plus the pole.

`rh_iff_companion_ge` makes `taylorCoeff zetaPoleCompanion n` RH's sole arithmetic carrier.  This
brick exposes that carrier as the von Mangoldt (log-prime / Bragg) spectrum: composing
`logDeriv_zeta_eq_companion_sub_pole` (`logDeriv ζ = logDeriv H − (·−1)⁻¹`) with the prime keystone
`logDeriv_zeta_eq_neg_LSeries_vonMangoldt` (`logDeriv ζ = −L(Λ)` on `Re s > 1`) gives, for `Re s > 1`,

    logDeriv zetaPoleCompanion s = − L(Λ) s + (s − 1)⁻¹        (Bragg peaks at k·log p, + pole).

This is the clean "companion = prime side + pole" identity anchoring the diffraction reading of
Route P (see ROUTEP_DIFFRACTION_SCOPE_2026-09-11.md).  It is a RE-COORDINATIZATION, not progress
toward RH: the von Mangoldt series converges only for `Re s > 1`, and the passage to the Li base
point is the explicit-formula analytic continuation whose uniform control IS RH.
conjecture1_proved = False.
-/
import Mathlib
import RvMDiffractionCore

open Complex

namespace RvMWeierstrass

/-- **Route P, Brick D1 — the companion is the log-prime spectrum plus the pole.**  For `Re s > 1`,
    the log-derivative of the pole-regularized companion `zetaPoleCompanion` equals the negative von
    Mangoldt L-series (the log-prime Bragg spectrum, peaks at `k·log p` with amplitude `Λ(pᵏ)`) plus
    the explicit simple pole `(s−1)⁻¹`.  Unconditional and kernel-clean; a re-coordinatization of
    Route P onto the prime side, NOT a step toward RH.  conjecture1_proved = False. -/
theorem logDeriv_zetaPoleCompanion_eq_vonMangoldt {s : ℂ} (hs : 1 < s.re) :
    logDeriv DiffractionCore.zetaPoleCompanion s
      = - LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s + (s - 1)⁻¹ := by
  have hz : s ≠ 1 := by rintro rfl; simp [Complex.one_re] at hs
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have h1 := DiffractionCore.logDeriv_zeta_eq_companion_sub_pole hz hζ
  have h2 := DiffractionCore.logDeriv_zeta_eq_neg_LSeries_vonMangoldt hs
  -- h1 : logDeriv ζ s = logDeriv zetaPoleCompanion s − (s−1)⁻¹
  -- h2 : logDeriv ζ s = − L(Λ) s
  linear_combination h2 - h1

end RvMWeierstrass
