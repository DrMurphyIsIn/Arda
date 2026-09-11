/-
RvMLiCoeffId — the elementary summand of the coefficient split is identically 1.

The coefficient split `taylorCoeff_riemannXi_split` (#460) writes the n-th Li coefficient as
`taylorCoeff (fun s=>s) n + taylorCoeff zetaPoleCompanion n + taylorCoeff Γℝ n`.  The first summand
comes from the `1/s` pole of `logDeriv ξ` and is entirely elementary: under the Möbius pullback
`phi id z = (1−z)⁻¹ = M z`, one has `logDeriv(phi id) = M` (because `M'/M = (1−z)⁻¹ = M`), so its
n-th Taylor datum is `iteratedDeriv n M 0 / n! = n!/n! = 1`.

  * `taylorCoeff_id_eq_one` — `taylorCoeff (fun s => s) n = 1` for every `n`.
  * `taylorCoeff_riemannXi_split_explicit` — `taylorCoeff riemannXi n
        = 1 + taylorCoeff zetaPoleCompanion n + taylorCoeff Γℝ n`.

This makes the split explicit in every term that CAN be: the constant `1` (pole), the fully-computed
archimedean polygamma datum `taylorCoeff Γℝ n`, and the sole arithmetic-carrying term
`taylorCoeff zetaPoleCompanion n` (the ζ companion).  conjecture1_proved = False.
-/
import Mathlib
import RvMLiCoeffSplit
import RvMMobius

open Complex Filter Topology

namespace RvMWeierstrass

/-- **The pole summand is identically 1.**  `taylorCoeff (fun s => s) n = 1`.  The `1/s` piece of
    `logDeriv ξ` pulls back under Möbius to `logDeriv(phi id) = M = (1−·)⁻¹`, whose n-th derivative at
    `0` is `n!` (`iteratedDeriv_mobius`), giving `n!/n! = 1`. -/
theorem taylorCoeff_id_eq_one (n : ℕ) : LiCriterion.taylorCoeff (fun s : ℂ => s) n = 1 := by
  have hphi_eq : ∀ f : ℂ → ℂ, LiCriterion.phi f = fun z => f ((1 - z)⁻¹) := by
    intro f; rw [LiCriterion.phi_eq]; funext z; rw [one_div]
  -- `logDeriv(phi id)` agrees with the Möbius map `M = (1−·)⁻¹` on a neighbourhood of 0
  have hev : logDeriv (LiCriterion.phi (fun s : ℂ => s)) =ᶠ[𝓝 (0 : ℂ)] fun z => (1 - z)⁻¹ := by
    have h1z : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 1 := continuousAt_id.eventually_ne (by norm_num)
    filter_upwards [h1z] with z hz1'
    have hz0 : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (fun h => hz1' h.symm)
    have hidM : logDeriv (LiCriterion.phi (fun s : ℂ => s)) z
        = ((1 - z)⁻¹)⁻¹ * deriv (fun w : ℂ => (1 - w)⁻¹) z := by
      rw [hphi_eq, logDeriv_phi (f := fun s : ℂ => s) hz1' differentiableAt_id, logDeriv_id', one_div]
    have hderivM := iteratedDeriv_mobius 1 hz1'
    rw [iteratedDeriv_one] at hderivM
    rw [hidM, hderivM, inv_inv, Nat.factorial_one, Nat.cast_one]
    field_simp
  simp only [LiCriterion.taylorCoeff, LiCriterion.logDeriv_eq_rootLogDeriv,
    ← iteratedDeriv_eq_iterate]
  rw [Filter.EventuallyEq.iteratedDeriv_eq n hev,
    iteratedDeriv_mobius n (by norm_num : (0 : ℂ) ≠ 1)]
  have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [sub_zero, one_pow, div_one]
  exact div_self hfac

/-- **The coefficient split, with the elementary term resolved.**
    `taylorCoeff riemannXi n = 1 + taylorCoeff zetaPoleCompanion n + taylorCoeff Γℝ n`.  Every term
    that can be made explicit is: the constant `1` (the `1/s` pole), the archimedean polygamma datum
    `taylorCoeff Γℝ n` (Phase 4), and the lone arithmetic-carrying term (the ζ companion). -/
theorem taylorCoeff_riemannXi_split_explicit (n : ℕ) :
    LiCriterion.taylorCoeff LiCriterion.riemannXi n
      = 1 + LiCriterion.taylorCoeff DiffractionCore.zetaPoleCompanion n
        + LiCriterion.taylorCoeff Complex.Gammaℝ n := by
  rw [taylorCoeff_riemannXi_split, taylorCoeff_id_eq_one]

end RvMWeierstrass
