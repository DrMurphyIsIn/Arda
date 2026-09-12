/- PHASE 4 (dVP frontier, item 3 — concrete-instantiation ring/geometry facts): the mechanical
   hypotheses of `dlvp_zeta_region_of_canonical_decomp` for the concrete centre `c₀ = 2 + iγ` and
   evaluation point `σ + iγ`.

   With the analytic inputs all in place (CanonicalDecomp, `norm_logDeriv_g_le_strip`,
   `zeta_zero_count_strip`, `hAL_arith`, `g_sphere_log_osc_strip`), the region theorem's remaining
   hypotheses at `c₀ = 2 + iγ` are pure ring/geometry/arithmetic:

     * `hcz`   `c₀ + ((σ+iγ) - c₀) = σ+iγ`                         (c₀ cancels; `ring`);
     * `hz`    `(σ+iγ) - c₀ ∈ ball 0 R`                            (`‖σ-2‖ = 2-σ < R`);
     * `hzne`  eval point is not a shifted zero                    (ζ(σ+iγ) ≠ 0, `Re = σ > 1`);
     * `hβσ`   `β < σ`                                             (`σ > 1 > β`).

   These discharge the geometric/algebraic side of the concrete instantiation.
   conjecture1_proved = False (NOT a proof of RH).
-/
import DlvpZetaCountStrip

open Complex Metric MeromorphicOn

namespace ZeroFreeBridge

section Concrete
variable (σ γ R : ℝ)

/-- `hcz`: `c₀ + ((σ+iγ) - c₀) = σ+iγ` at `c₀ = 2+iγ` (the centre cancels). -/
theorem concrete_hcz :
    ((2 : ℂ) + (γ : ℂ) * I) + ((σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I))
      = (σ : ℂ) + (γ : ℂ) * I := by ring

/-- The recentred evaluation point is the REAL number `σ - 2`. -/
theorem concrete_eval_eq :
    (σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I) = ((σ - 2 : ℝ) : ℂ) := by
  push_cast; ring

/-- `hz`: `(σ+iγ) - c₀ ∈ ball 0 R`, given `2 - σ < R` and `σ ≤ 2` (`‖σ-2‖ = 2-σ < R`). -/
theorem concrete_hz_mem (hσ2 : σ ≤ 2) (hσR : 2 - σ < R) :
    (σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I) ∈ ball (0 : ℂ) R := by
  rw [mem_ball_zero_iff, concrete_eval_eq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (by linarith : σ - 2 ≤ 0)]
  linarith

/-- The recentred evaluation point recovers real part `σ` (via `c₀ + ·`). -/
theorem concrete_center_re :
    (((2 : ℂ) + (γ : ℂ) * I) + ((σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I))).re = σ := by
  rw [concrete_hcz]; simp

/-- `hzne`: the recentred eval point `(σ+iγ) - c₀` is not a divisor-support point (a shifted zero),
    because `ζ(σ+iγ) ≠ 0` (`Re = σ > 1`) while every support point `u` gives a zero `ζ(c₀+u) = 0`. -/
theorem concrete_hzne {c₀ : ℂ} {R : ℝ} (σ γ : ℝ)
    (hf_ana : AnalyticOnNhd ℂ (fun w => riemannZeta (c₀ + w)) (ball 0 R))
    (heval_ne : riemannZeta (c₀ + ((σ : ℂ) + (γ : ℂ) * I - c₀)) ≠ 0)
    {u : ℂ} (hu : divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u ≠ 0) :
    (σ : ℂ) + (γ : ℂ) * I - c₀ ≠ u := by
  have huball : u ∈ ball (0 : ℂ) R :=
    (divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R)).supportWithinDomain
      (Function.mem_support.mpr hu)
  have hord : analyticOrderAt (fun w => riemannZeta (c₀ + w)) u ≠ 0 := by
    intro h0; apply hu; rw [hf_ana.divisor_apply huball, h0]; rfl
  have hz0 := apply_eq_zero_of_analyticOrderAt_ne_zero
    (f := fun w => riemannZeta (c₀ + w)) (z₀ := u) hord
  intro h
  apply heval_ne
  rw [h]; exact hz0

/-- `hβσ`: `β < σ` from the σ-optimum `σ - 1 = 1/(2(3A+5AL)) > 0` (so `σ > 1`) and `β < 1`. -/
theorem concrete_hβσ {σ A L β : ℝ} (hA : 0 < A) (hL : 1 ≤ L) (hβ1 : β < 1)
    (hσ_opt : σ - 1 = 1 / (2 * (3 * A + 5 * (A * L)))) : β < σ := by
  have hden : 0 < 2 * (3 * A + 5 * (A * L)) := by nlinarith
  have hσ1 : 0 < σ - 1 := by rw [hσ_opt]; positivity
  linarith

end Concrete
end ZeroFreeBridge
