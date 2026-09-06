/- PHASE 4 (dVP frontier, obligation (i-b') → two ζ inputs): decompose the boundary growth of
   `log‖g‖` into ζ-growth and zero-factor control.

   The entire part is `g = ζ / P` where `P = ∏_ρ (·-ρ)^{m_ρ}` is the (polynomial) zero-factor of
   the ζ factorization `ζ = P • g`.  Wherever all three are nonzero, `‖ζ‖ = ‖P‖·‖g‖`, so

       log‖g‖ = log‖ζ‖ - log‖P‖ .

   Hence the boundary oscillation splits:
       log‖g z‖ - log‖g c‖ = (log‖ζ z‖ - log‖ζ c‖) + (log‖P c‖ - log‖P z‖),
   reducing the SOLE remaining ζ input to TWO named quantitative bounds on the sphere:
     * ζ-growth      `log‖ζ z‖ - log‖ζ c‖ ≤ Aζ`  (from `zeta_sphere_bound` + a lower bound on ‖ζ c‖);
     * zero-factor   `log‖P c‖ - log‖P z‖ ≤ AP`  (the factored zeros lie inside; with the two-scale
                     geometry `‖z-ρ‖` is bounded below on the sphere, and the zero count is O(L)).

   Composed with `DlvpMaxMod.norm_logDeriv_le_of_sphere_log_norm_le`, these give `‖E‖ ≤
   2(Aζ+AP)/(R-r) = O(L)`.  Function-agnostic in `ζ, P, g`.  conjecture1_proved = False (NOT RH).
-/
import DlvpMaxMod

open Complex Metric

namespace ZeroFreeBridge

/-- **Boundary-growth decomposition.**  For a factorization `ζ = P·g` (all factors nonzero at the
    centre `c` and on the sphere `sphere c R`), the boundary oscillation of `log‖g‖` is bounded by
    the sum of the ζ-growth bound `Aζ` and the zero-factor bound `AP`. -/
theorem log_norm_g_le_of_split {ζ P g : ℂ → ℂ} {c : ℂ} {R Aζ AP : ℝ}
    (hPc : P c ≠ 0) (hgc : g c ≠ 0)
    (hfac_c : ζ c = P c * g c)
    (hP : ∀ z ∈ sphere c R, P z ≠ 0) (hg : ∀ z ∈ sphere c R, g z ≠ 0)
    (hfac : ∀ z ∈ sphere c R, ζ z = P z * g z)
    (hζbound : ∀ z ∈ sphere c R, Real.log ‖ζ z‖ - Real.log ‖ζ c‖ ≤ Aζ)
    (hPbound : ∀ z ∈ sphere c R, Real.log ‖P c‖ - Real.log ‖P z‖ ≤ AP) :
    ∀ z ∈ sphere c R, Real.log ‖g z‖ - Real.log ‖g c‖ ≤ Aζ + AP := by
  -- `log‖g‖ = log‖ζ‖ - log‖P‖` wherever `ζ = P·g` with `P, g ≠ 0`.
  have hsplit : ∀ z ∈ sphere c R,
      Real.log ‖g z‖ = Real.log ‖ζ z‖ - Real.log ‖P z‖ := by
    intro z hz
    have hnorm : ‖ζ z‖ = ‖P z‖ * ‖g z‖ := by rw [hfac z hz, norm_mul]
    rw [hnorm, Real.log_mul (norm_ne_zero_iff.mpr (hP z hz)) (norm_ne_zero_iff.mpr (hg z hz))]
    ring
  have hsplit_c : Real.log ‖g c‖ = Real.log ‖ζ c‖ - Real.log ‖P c‖ := by
    have hnorm : ‖ζ c‖ = ‖P c‖ * ‖g c‖ := by rw [hfac_c, norm_mul]
    rw [hnorm, Real.log_mul (norm_ne_zero_iff.mpr hPc) (norm_ne_zero_iff.mpr hgc)]
    ring
  intro z hz
  rw [hsplit z hz, hsplit_c]
  have h1 := hζbound z hz
  have h2 := hPbound z hz
  linarith

/-- **(i-b') reduced to the two ζ inputs.**  For the factorization `ζ = P·g` with `g` holomorphic
    (up to the boundary) and zero-free on `ball c R`, the entire part at the centre is bounded by
    the ζ-growth and zero-factor sphere bounds: `‖logDeriv g c‖ ≤ 2 (Aζ + AP)/(R - r)`.  Feeding
    `Aζ, AP = O(L)` gives `‖E‖ = O(L)`, the last input to the dVP reduction skeleton. -/
theorem norm_logDeriv_le_of_boundary_split {ζ P g : ℂ → ℂ} {c : ℂ} {R r Aζ AP : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM : 0 < Aζ + AP)
    (hd : DiffContOnCl ℂ g (ball c R)) (hne : ∀ z ∈ ball c R, g z ≠ 0)
    (hPc : P c ≠ 0) (hgc : g c ≠ 0) (hfac_c : ζ c = P c * g c)
    (hP : ∀ z ∈ sphere c R, P z ≠ 0) (hg : ∀ z ∈ sphere c R, g z ≠ 0)
    (hfac : ∀ z ∈ sphere c R, ζ z = P z * g z)
    (hζbound : ∀ z ∈ sphere c R, Real.log ‖ζ z‖ - Real.log ‖ζ c‖ ≤ Aζ)
    (hPbound : ∀ z ∈ sphere c R, Real.log ‖P c‖ - Real.log ‖P z‖ ≤ AP) :
    ‖logDeriv g c‖ ≤ 2 * (Aζ + AP) / (R - r) :=
  norm_logDeriv_le_of_sphere_log_norm_le hr hrR hM hd hne
    (log_norm_g_le_of_split hPc hgc hfac_c hP hg hfac hζbound hPbound)

end ZeroFreeBridge
