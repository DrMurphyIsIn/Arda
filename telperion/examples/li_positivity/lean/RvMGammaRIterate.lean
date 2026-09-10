/-
RvMGammaRIterate — Phase 4b (iterate): the local iterated chain rule for the half-argument digamma.

`digamma` is only smooth off its poles, so Mathlib's global `iteratedDeriv_comp_const_mul` does not
apply.  On the right half-plane `{Re > 0}` — an open, ×(1/2)-invariant, pole-free set — `digamma` is
analytic (hence `ContDiffOn ⊤`), and the *local* chain rule `iteratedDerivWithin_comp_const_smul`
plus `iteratedDerivWithin_of_isOpen` give:

  * `digamma_contDiffOn_re_pos` — `digamma` is `ContDiffOn ℂ ⊤` on `{Re > 0}`.
  * `iteratedDeriv_digamma_half` — `iteratedDeriv m (fun s => ψ(s/2)) x = (1/2)^m · ψ^(m)(x/2)` for
    `Re x > 0`.

Together with `logDeriv_Gammaℝ_eq` (Phase 4b core) this reduces the archimedean factor's higher
derivatives to the Phase-4a polygamma values at `1/2`.  conjecture1_proved = False.
-/
import Mathlib
import RvMGammaR

open Complex

namespace RvMWeierstrass

/-- The open right half-plane `{z | 0 < Re z}`. -/
private def RHP : Set ℂ := {z : ℂ | 0 < z.re}

private theorem isOpen_RHP : IsOpen RHP := isOpen_lt continuous_const Complex.continuous_re

private theorem mul_half_re (z : ℂ) : ((1 / 2 : ℂ) * z).re = z.re / 2 := by
  simp [Complex.mul_re]; ring

/-- **`digamma` is smooth on the right half-plane.**  It is analytic there (no poles), hence
    `ContDiffOn ℂ ⊤`. -/
theorem digamma_contDiffOn_re_pos : ContDiffOn ℂ ⊤ Complex.digamma RHP := by
  have hne : ∀ z ∈ RHP, ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro z hz m h
    rw [h] at hz
    simp only [RHP, Set.mem_setOf_eq, Complex.neg_re, Complex.natCast_re] at hz
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hGdiff : DifferentiableOn ℂ Complex.Gamma RHP := fun z hz =>
    (Complex.differentiableAt_Gamma z (hne z hz)).differentiableWithinAt
  have hGana : AnalyticOnNhd ℂ Complex.Gamma RHP := hGdiff.analyticOnNhd isOpen_RHP
  have hGne : ∀ z ∈ RHP, Complex.Gamma z ≠ 0 := fun z hz => Complex.Gamma_ne_zero_of_re_pos hz
  have hdig : Complex.digamma = fun z => deriv Complex.Gamma z / Complex.Gamma z := by
    funext z; rw [Complex.digamma_def, logDeriv_apply]
  rw [hdig]
  exact ((hGana.deriv).div hGana hGne).contDiffOn isOpen_RHP.uniqueDiffOn

/-- **The half-argument chain rule.**  For `Re x > 0`,
    `iteratedDeriv m (fun s => digamma (s/2)) x = (1/2)^m · iteratedDeriv m digamma (x/2)`. -/
theorem iteratedDeriv_digamma_half (m : ℕ) {x : ℂ} (hx : 0 < x.re) :
    iteratedDeriv m (fun s => Complex.digamma (s / 2)) x
      = (1 / 2) ^ m * iteratedDeriv m Complex.digamma (x / 2) := by
  have hxU : x ∈ RHP := hx
  have hcxU : (1 / 2 : ℂ) * x ∈ RHP := by
    show 0 < ((1 / 2 : ℂ) * x).re
    rw [mul_half_re]; linarith
  have hmaps : Set.MapsTo (fun z => (1 / 2 : ℂ) * z) RHP RHP := by
    intro z hz
    show 0 < ((1 / 2 : ℂ) * z).re
    rw [mul_half_re]
    have : 0 < z.re := hz
    linarith
  have hCD : ContDiffOn ℂ (m : ℕ∞) Complex.digamma RHP :=
    digamma_contDiffOn_re_pos.of_le le_top
  have key := iteratedDerivWithin_comp_const_smul (𝕜 := ℂ) (n := m) (f := Complex.digamma)
    (s := RHP) (x := x) hxU isOpen_RHP.uniqueDiffOn hCD (1 / 2 : ℂ) hmaps
  rw [iteratedDerivWithin_of_isOpen isOpen_RHP hxU,
    iteratedDerivWithin_of_isOpen isOpen_RHP hcxU, smul_eq_mul] at key
  have hfun : (fun s : ℂ => Complex.digamma (s / 2)) = fun z : ℂ => Complex.digamma ((1 / 2 : ℂ) * z) := by
    funext s; rw [show (1 / 2 : ℂ) * s = s / 2 by ring]
  rw [hfun, key, show (1 / 2 : ℂ) * x = x / 2 by ring]

/-- **Higher derivatives of the archimedean factor at `1`.**  For `m ≥ 1`,
    `iteratedDeriv m (logDeriv Γℝ) 1 = (1/2)^(m+1) · iteratedDeriv m digamma (1/2)` — reducing the
    archimedean log-derivative's Taylor data to the Phase-4a polygamma values at `1/2`. -/
theorem iteratedDeriv_logDeriv_Gammaℝ_one (m : ℕ) (hm : 1 ≤ m) :
    iteratedDeriv m (logDeriv Complex.Gammaℝ) 1
      = (1 / 2) ^ (m + 1) * iteratedDeriv m Complex.digamma (1 / 2) := by
  have h1RHP : (1 : ℂ) ∈ RHP := by show (0 : ℝ) < (1 : ℂ).re; simp
  -- logDeriv Γℝ = -log π/2 + (1/2)·ψ(s/2)  on a neighbourhood of 1
  have hEq : logDeriv Complex.Gammaℝ =ᶠ[nhds (1 : ℂ)]
      fun s => -Complex.log (Real.pi : ℂ) / 2 + (1 / 2) * Complex.digamma (s / 2) := by
    filter_upwards [isOpen_RHP.mem_nhds h1RHP] with s hs
    refine logDeriv_Gammaℝ_eq (fun k hcon => ?_)
    have hsre : 0 < (s / 2).re := by
      rw [show s / 2 = (1 / 2 : ℂ) * s by ring, mul_half_re]; have : (0 : ℝ) < s.re := hs; linarith
    rw [hcon] at hsre
    simp only [Complex.neg_re, Complex.natCast_re] at hsre
    linarith [Nat.cast_nonneg (α := ℝ) k]
  rw [Filter.EventuallyEq.iteratedDeriv_eq m hEq]
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  -- the constant drops for order ≥ 1
  rw [iteratedDeriv_succ']
  have hderiv : deriv (fun s => -Complex.log (Real.pi : ℂ) / 2 + (1 / 2) * Complex.digamma (s / 2))
      = deriv (fun s => (1 / 2) * Complex.digamma (s / 2)) := by
    funext y; rw [deriv_const_add']
  rw [hderiv, ← iteratedDeriv_succ', iteratedDeriv_const_mul_field,
    iteratedDeriv_digamma_half (n + 1) (by norm_num)]
  ring

end RvMWeierstrass
