/- PHASE 4 (dVP frontier, the EFFECTIVE pole bound): replace Mathlib's non-effective pole constant
   (`log_deriv_riemannZeta_add_inv_sub_bounded`, a bare `∃`) with an EXPLICIT one.

   The only non-effective input to `dlvp_zeta_region_rate`'s constant `c` is the pole bound
   `Re(-ζ'/ζ(σ)) ≤ Re(1/(σ-1)) + A₀` near `σ = 1`.  This file makes it explicit with
   `A₀ = 16`, `ε₀ = 1/48`, via a Cauchy estimate on `ζ₁ := (·-1)·ζ` (Mathlib `riemannZeta₁`,
   entire, `ζ₁ 1 = 1`, `ζ = (s-1)⁻¹·ζ₁`):

     * `zeta1_norm_le`   `‖ζ₁ z‖ ≤ 3` on `closedBall 1 (1/2)` — via the explicit `zeta_strip_bound`;
     * `zeta1_deriv_le`  `‖ζ₁' w‖ ≤ 12` on `closedBall 1 (1/4)` — Cauchy estimate (radius 1/4);
     * `zeta1_lower`     `‖ζ₁ σ‖ ≥ 3/4` for `σ-1 ≤ 1/48` — mean-value bound `‖ζ₁ σ - 1‖ ≤ 12(σ-1)`;
     * `zeta_logderiv_eq`  `ζ'/ζ = -(s-1)⁻¹ + ζ₁'/ζ₁` at an explicit point (`s≠1`, `ζ₁ s≠0`);
     * `hpole_effective`   `Re(-ζ'/ζ(σ)) ≤ Re(1/(σ-1)) + 16` for `1 < σ`, `σ-1 < 1/48`
       (`|ζ₁'/ζ₁| ≤ 12/(3/4) = 16`).

   Feeding this into the rate construction makes `c = 1/(112·(16 + 48 + E))` a CONCRETE positive
   real (`E` the explicit constant from `dlvp_zeta_region_rate`).  The dVP constant is now effective.
   conjecture1_proved = False (NOT a proof of RH).
-/
import StripBound
import StripRepr

open Complex Metric

namespace ZeroFreeBridge

/-- `‖ζ₁ z‖ ≤ 3` on the disk `closedBall 1 (1/2)`, from the explicit strip bound on `ζ`. -/
theorem zeta1_norm_le {z : ℂ} (hz : z ∈ closedBall (1 : ℂ) (1/2)) : ‖riemannZeta₁ z‖ ≤ 3 := by
  rw [mem_closedBall, Complex.dist_eq] at hz
  by_cases h1 : z = 1
  · subst h1; rw [riemannZeta₁_one]; simp
  · have hane : z - 1 ≠ 0 := sub_ne_zero.mpr h1
    have hz1 : (z - 1) * riemannZeta z = riemannZeta₁ z := by
      rw [riemannZeta_eq_inv_sub_mul h1, ← mul_assoc, mul_inv_cancel₀ hane, one_mul]
    have hre : (1:ℝ)/2 ≤ z.re := by
      have h := Complex.abs_re_le_norm (z - 1)
      rw [Complex.sub_re, Complex.one_re] at h
      have : |z.re - 1| ≤ 1/2 := le_trans h hz
      rw [abs_le] at this; linarith [this.1]
    have hstrip : z ∈ stripDomain := by
      refine ⟨?_, ?_⟩
      · show (0:ℝ) < z.re; linarith
      · intro hmem; exact h1 (Set.mem_singleton_iff.mp hmem)
    have hzb := zeta_strip_bound hstrip
    have hnz : ‖z‖ ≤ 3/2 := by
      have h := norm_sub_norm_le z 1; simp only [norm_one] at h; linarith
    have hapos : (0:ℝ) < ‖z - 1‖ := by rwa [norm_pos_iff]
    have hrpos : (0:ℝ) < z.re := by linarith
    have hzn : ‖riemannZeta₁ z‖ = ‖z - 1‖ * ‖riemannZeta z‖ := by rw [← hz1, norm_mul]
    rw [hzn]
    refine le_trans (mul_le_mul_of_nonneg_left hzb (le_of_lt hapos)) ?_
    have hexp : ‖z - 1‖ * (‖z‖ / ‖z - 1‖ + ‖z‖ / z.re) = ‖z‖ + ‖z - 1‖ * ‖z‖ / z.re := by field_simp
    rw [hexp]
    have hterm : ‖z - 1‖ * ‖z‖ / z.re ≤ 3/2 := by
      rw [div_le_iff₀ hrpos]; nlinarith [norm_nonneg z, hnz, hz, hre, hapos]
    linarith [hnz, hterm]

/-- `‖ζ₁' w‖ ≤ 12` on `closedBall 1 (1/4)` — Cauchy estimate (sphere of radius 1/4 stays in the
    `‖ζ₁‖ ≤ 3` disk). -/
theorem zeta1_deriv_le {w : ℂ} (hw : w ∈ closedBall (1 : ℂ) (1/4)) :
    ‖deriv riemannZeta₁ w‖ ≤ 12 := by
  have hd : DiffContOnCl ℂ riemannZeta₁ (ball w (1/4)) :=
    ⟨differentiable_riemannZeta₁.differentiableOn, differentiable_riemannZeta₁.continuous.continuousOn⟩
  have hb : ∀ z ∈ sphere w (1/4), ‖riemannZeta₁ z‖ ≤ 3 := by
    intro z hz
    rw [mem_sphere_iff_norm] at hz
    rw [mem_closedBall, Complex.dist_eq] at hw
    refine zeta1_norm_le ?_
    rw [mem_closedBall, Complex.dist_eq]
    calc ‖z - 1‖ = ‖(z - w) + (w - 1)‖ := by congr 1; ring
      _ ≤ ‖z - w‖ + ‖w - 1‖ := norm_add_le _ _
      _ ≤ 1/4 + 1/4 := by rw [hz]; linarith
      _ = 1/2 := by norm_num
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0:ℝ) < 1/4) hd hb
  linarith

/-- `‖ζ₁ σ‖ ≥ 3/4` for real `σ` with `σ - 1 ≤ 1/48` — mean-value bound off `ζ₁ 1 = 1`. -/
theorem zeta1_lower {σ : ℝ} (h1 : 1 ≤ σ) (h2 : σ - 1 ≤ 1/48) :
    3/4 ≤ ‖riemannZeta₁ (σ : ℂ)‖ := by
  have hmem : (σ : ℂ) ∈ closedBall (1 : ℂ) (1/4) := by
    rw [mem_closedBall, Complex.dist_eq,
      show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  have hmvt : ‖riemannZeta₁ (σ : ℂ) - riemannZeta₁ 1‖ ≤ 12 * ‖(σ : ℂ) - 1‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le (fun x _ => differentiable_riemannZeta₁ x)
      (fun x hx => zeta1_deriv_le hx) (convex_closedBall 1 (1/4)) (by simp) hmem
  rw [riemannZeta₁_one] at hmvt
  have hnorm : ‖(σ : ℂ) - 1‖ = σ - 1 := by
    rw [show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  rw [hnorm] at hmvt
  have hrev := norm_sub_norm_le (1 : ℂ) (riemannZeta₁ (σ : ℂ))
  rw [norm_one, norm_sub_rev] at hrev
  linarith [hrev, hmvt, h2]

/-- `ζ'/ζ = -(s-1)⁻¹ + ζ₁'/ζ₁` at an explicit point (`s ≠ 1`, `ζ₁ s ≠ 0`). -/
theorem zeta_logderiv_eq {s : ℂ} (hs : s ≠ 1) (hz1 : riemannZeta₁ s ≠ 0) :
    deriv riemannZeta s / riemannZeta s
      = -(s - 1)⁻¹ + deriv riemannZeta₁ s / riemannZeta₁ s := by
  have hsne : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hEq : riemannZeta =ᶠ[nhds s] (fun w => (w - 1)⁻¹ * riemannZeta₁ w) := by
    filter_upwards [isOpen_ne.mem_nhds hs] with w hw; exact riemannZeta_eq_inv_sub_mul hw
  have h1 : HasDerivAt (fun w : ℂ => (w - 1)⁻¹) (-1 / (s - 1) ^ 2) s := by
    have hb : HasDerivAt (fun w : ℂ => w - 1) 1 s := (hasDerivAt_id s).sub_const 1
    exact hb.inv hsne
  have h2 : HasDerivAt riemannZeta₁ (deriv riemannZeta₁ s) s :=
    (differentiable_riemannZeta₁ s).hasDerivAt
  have hprod := (h1.mul h2).congr_of_eventuallyEq hEq
  rw [hprod.deriv, riemannZeta_eq_inv_sub_mul hs]
  field_simp

/-- **The EFFECTIVE pole bound** — `Re(-ζ'/ζ(σ)) ≤ Re(1/(σ-1)) + 16` for real `σ` with
    `1 < σ` and `σ - 1 < 1/48`.  Explicit `A₀ = 16`, `ε₀ = 1/48`; makes the dVP constant effective. -/
theorem hpole_effective {σ : ℝ} (h1 : 1 < σ) (h2 : σ - 1 < 1/48) :
    (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤ (1 / ((σ : ℂ) - 1)).re + 16 := by
  have hσne : (σ : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hlow : 3/4 ≤ ‖riemannZeta₁ (σ : ℂ)‖ := zeta1_lower (le_of_lt h1) (le_of_lt h2)
  have hz1ne : riemannZeta₁ (σ : ℂ) ≠ 0 := by
    intro h; rw [h, norm_zero] at hlow; linarith
  have heq := zeta_logderiv_eq hσne hz1ne
  have hmem : (σ : ℂ) ∈ closedBall (1 : ℂ) (1/4) := by
    rw [mem_closedBall, Complex.dist_eq,
      show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  have hderivbd : ‖deriv riemannZeta₁ (σ : ℂ)‖ ≤ 12 := zeta1_deriv_le hmem
  have hratio : ‖deriv riemannZeta₁ (σ : ℂ) / riemannZeta₁ (σ : ℂ)‖ ≤ 16 := by
    rw [norm_div, div_le_iff₀ (by linarith : (0:ℝ) < ‖riemannZeta₁ (σ : ℂ)‖)]
    nlinarith [hderivbd, hlow, norm_nonneg (deriv riemannZeta₁ (σ : ℂ))]
  have hre_ge : -16 ≤ (deriv riemannZeta₁ (σ : ℂ) / riemannZeta₁ (σ : ℂ)).re := by
    have h := Complex.abs_re_le_norm (deriv riemannZeta₁ (σ : ℂ) / riemannZeta₁ (σ : ℂ))
    rw [abs_le] at h; linarith [h.1, hratio]
  have hval : (-deriv riemannZeta (σ : ℂ)) / riemannZeta (σ : ℂ)
      = ((σ : ℂ) - 1)⁻¹ - deriv riemannZeta₁ (σ : ℂ) / riemannZeta₁ (σ : ℂ) := by
    rw [neg_div, heq]; ring
  rw [hval, one_div, Complex.sub_re]
  linarith [hre_ge]

/-- **Pole-neighborhood notch: `ζ(s) ≠ 0` in the punctured disk `0 < ‖s - 1‖ ≤ 1/16`.**  The pole
    dominates: `‖ζ₁ s - 1‖ ≤ 12·‖s - 1‖ ≤ 3/4` (mean-value bound off `ζ₁ 1 = 1`, same MVT pattern
    as `zeta1_lower` but at a complex point), so `‖ζ₁ s‖ ≥ 1/4 > 0` and `ζ = (s-1)⁻¹·ζ₁ ≠ 0`.

    This is item (2) of the 55/16 low-strip closure (RH_IN_BOX_INTERFACE §6.2): it clears the
    corner `Re ∈ (999/1000, 1)`, `Im ∈ (0, ε₀)` that no argument-principle box can reach (an edge
    at `Re = 1` runs through the pole; an edge at `Re = 1 - δ` leaves a sliver). -/
theorem riemannZeta_ne_zero_near_one {s : ℂ} (hne : s ≠ 1) (hr : ‖s - 1‖ ≤ 1/16) :
    riemannZeta s ≠ 0 := by
  have hmem : s ∈ closedBall (1 : ℂ) (1/4) := by
    rw [mem_closedBall, Complex.dist_eq]; linarith
  have hmvt : ‖riemannZeta₁ s - riemannZeta₁ 1‖ ≤ 12 * ‖s - 1‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le (fun x _ => differentiable_riemannZeta₁ x)
      (fun x hx => zeta1_deriv_le hx) (convex_closedBall 1 (1/4)) (by simp) hmem
  rw [riemannZeta₁_one] at hmvt
  have h12 : 12 * ‖s - 1‖ ≤ 3/4 := by
    have := mul_le_mul_of_nonneg_left hr (by norm_num : (0:ℝ) ≤ 12)
    linarith
  have hlow : (1:ℝ)/4 ≤ ‖riemannZeta₁ s‖ := by
    have hrev := norm_sub_norm_le (1 : ℂ) (riemannZeta₁ s)
    rw [norm_one, norm_sub_rev] at hrev
    linarith
  have hz1ne : riemannZeta₁ s ≠ 0 := by
    intro h; rw [h, norm_zero] at hlow; linarith
  rw [riemannZeta_eq_inv_sub_mul hne]
  exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr hne)) hz1ne

end ZeroFreeBridge

