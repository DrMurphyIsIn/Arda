/- EMITTED-SHAPES DOGFOOD: kernel-checks that the new Telperion emitters produce compiling Lean.
   - `zeta_zero_free_poly_emitted`  <- emit_zero_free_region (region assembly, constant re-derived)
   - `integrableOn_bounded_div_cpow` <- emit_dominated_integrability (the reusable shape)
   Generated; if this compiles, the emitters' output is kernel-valid. conjecture1_proved = False. -/
import Mathlib

open Complex MeasureTheory

namespace EmittedShapes

/-- Zero-free-region assembly for `ζ` at `σ = 2 - β`: from the 3-4-1 positivity + pole (c1=2),
    growth (c2=5·γ^1), Cauchy (c4=24·γ^1) bounds, the region
    constant is 1/212336640 and the rate is `Re s > 1 - c/|t|^5`. Re-derived exactly before emission. -/
theorem zeta_zero_free_poly_emitted {β γ Zσ Zσt Zσ2t : ℝ}
    (hβ1 : β < 1) (hγ : 1 ≤ γ)
    (hZσ : 0 ≤ Zσ) (hZσt : 0 ≤ Zσt) (hZσ2t : 0 ≤ Zσ2t)
    (hprod : 1 ≤ Zσ ^ 3 * Zσt ^ 4 * Zσ2t)
    (hpole : Zσ ≤ 2 / (1 - β))
    (hstrip : Zσ2t ≤ 5 * γ)
    (hcauchy : Zσt ≤ 2 * (1 - β) * 24 * γ) :
    1 / (212336640 * γ ^ 5) ≤ 1 - β := by
  have hη : 0 < 1 - β := by linarith
  have hγ0 : 0 < γ := by linarith
  have hub : Zσ ^ 3 * Zσt ^ 4 * Zσ2t
      ≤ (2 / (1 - β)) ^ 3 * (2 * (1 - β) * 24 * γ) ^ 4 * (5 * γ) := by
    gcongr
  have hsimp : (2 / (1 - β)) ^ 3 * (2 * (1 - β) * 24 * γ) ^ 4 * (5 * γ)
      = 212336640 * (1 - β) * γ ^ 5 := by
    field_simp; ring
  rw [hsimp] at hub
  have h1 : (1 : ℝ) ≤ 212336640 * (1 - β) * γ ^ 5 := le_trans hprod hub
  rw [div_le_iff₀ (by positivity)]
  nlinarith [h1]

/-- Reusable shape: a bounded factor over a complex power is integrable on a ray, provided the power
    decays (`1 < Re p`). `‖b‖ ≤ B` supplied as `hb`. Mirrors R2's `hint_frac`. -/
theorem integrableOn_bounded_div_cpow {b : ℝ → ℂ} {p : ℂ} {c B : ℝ}
    (hc : 0 < c) (hp : 1 < p.re)
    (hbmeas : Measurable b) (hb : ∀ x, ‖b x‖ ≤ B) :
    MeasureTheory.IntegrableOn (fun x => b x / (x : ℂ) ^ p) (Set.Ioi c) := by
  have hbnd : MeasureTheory.IntegrableOn (fun x : ℝ => B * x ^ (-p.re)) (Set.Ioi c) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -p.re < -1) hc).const_mul B
  refine hbnd.mono' ?_ ?_
  · exact (hbmeas.div ((Complex.measurable_ofReal.pow_const p))).aestronglyMeasurable
  · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall (fun x hx => ?_))
    have hxpos : (0 : ℝ) < x := lt_trans hc hx
    rw [Real.norm_of_nonneg (by positivity), norm_div,
      Complex.norm_cpow_eq_rpow_re_of_pos hxpos, Real.rpow_neg hxpos.le, div_eq_mul_inv]
    exact mul_le_mul (hb x) le_rfl (by positivity) (le_trans (norm_nonneg _) (hb x))

end EmittedShapes
