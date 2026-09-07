/- PHASE 4 (dVP frontier, brick 3 — strip-capable ζ boundary oscillation): the version of
   `zeta_sphere_log_bound` / `g_sphere_log_osc` that survives the sphere DIPPING BELOW `Re = 1`.

   The original `zeta_sphere_log_bound` (`DlvpZetaSphereLog`) needs `R + 1 < c.re`, so the whole
   sphere stays in `Re > 1` — but then the disk cannot enclose a nontrivial zero `ρ₀` (which has
   `Re < 1`).  The KEY observation: `zeta_strip_bound` (`StripBound`) already holds on ALL of
   `stripDomain = {Re > 0} \ {1}` (NOT just `Re > 1`) — so the upper bound `‖ζ z‖ ≤ ‖z‖/‖z-1‖ +
   ‖z‖/Re z` is available on the sub-1 strip too.  We relax the hypothesis to `R < c.re - 1/2`
   (sphere stays in `Re > 1/2 > 0`) plus `R + 2 ≤ |c.im|` (sphere stays off `s = 1`, and `‖z-1‖`
   is large), and — since `ζ` MAY now vanish on the sphere — handle `Real.log ‖ζ z‖` at a zero by
   `Real.log 0 = 0 ≤ log U''` (the upper constant `U'' ≥ 1`).  The oscillation bound is unchanged
   in spirit: `log‖ζ z‖ - log‖ζ c‖ ≤ log U'' - log(2 - π²/6) = O(log|c|) = O(L)`.

   conjecture1_proved = False (NOT a proof of RH).
-/
import DlvpZetaLower
import DlvpZetaDisk
import StripBound
import DlvpCanonicalNorm

open Complex Metric

namespace ZeroFreeBridge

/-- **Strip-capable ζ boundary oscillation.**  On `sphere c R` about a centre with `Re c ≥ 2`,
    where the sphere is allowed to dip to `Re z > 1/2` (`R < c.re - 1/2`) as long as it stays off
    `s = 1` (`R + 2 ≤ |c.im|`), the log-oscillation of ζ is bounded by an explicit `O(log|c|)`:
    `log‖ζ z‖ - log‖ζ c‖ ≤ log U'' - log(2 - π²/6)`,
    `U'' = (‖c‖+R)/(|c.im|-R) + (‖c‖+R)/(c.re-R)`.  Uses `zeta_strip_bound` (valid on the FULL
    strip `Re > 0`, `s ≠ 1`) for the upper bound, so it survives the sphere reaching `Re < 1`. -/
theorem zeta_sphere_log_bound_strip (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hc2 : 2 ≤ c.re) (hRlt : R < c.re - 1/2) (himc : R + 2 ≤ |c.im|)
    {z : ℂ} (hz : z ∈ sphere c R) :
    Real.log ‖riemannZeta z‖ - Real.log ‖riemannZeta c‖
      ≤ Real.log ((‖c‖ + R) / (|c.im| - R) + (‖c‖ + R) / (c.re - R))
        - Real.log (2 - Real.pi ^ 2 / 6) := by
  have hnorm : ‖z - c‖ = R := by rw [← Complex.dist_eq]; exact Metric.mem_sphere.mp hz
  -- Re z ≥ c.re - R > 1/2
  have hzre : c.re - R ≤ z.re := by
    have h1 : |(z - c).re| ≤ ‖z - c‖ := Complex.abs_re_le_norm _
    rw [hnorm] at h1
    have h2 : (z - c).re = z.re - c.re := by simp
    rw [h2] at h1; have := (abs_le.mp h1).1; linarith
  have hd_re : (0 : ℝ) < c.re - R := by linarith
  have hzrepos : (0 : ℝ) < z.re := by linarith
  -- |z.im| ≥ |c.im| - R ≥ 2
  have himz : |c.im| - R ≤ |z.im| := by
    have h1 : |(z - c).im| ≤ ‖z - c‖ := Complex.abs_im_le_norm _
    rw [hnorm] at h1
    have h2 : (z - c).im = z.im - c.im := by simp
    rw [h2] at h1
    have h4 : |c.im| - |z.im| ≤ |c.im - z.im| := abs_sub_abs_le_abs_sub c.im z.im
    rw [abs_sub_comm c.im z.im] at h4
    linarith
  have hd_im : (0 : ℝ) < |c.im| - R := by linarith
  -- z ≠ 1
  have hzne1 : z ≠ 1 := by
    intro h; rw [h] at himz; simp only [Complex.one_im, abs_zero] at himz; linarith
  have hmem : z ∈ stripDomain := ⟨hzrepos, by simpa using hzne1⟩
  -- ‖z‖ ≤ ‖c‖ + R
  have hznorm : ‖z‖ ≤ ‖c‖ + R := by
    calc ‖z‖ ≤ ‖c‖ + ‖z - c‖ := by simpa using norm_le_norm_add_norm_sub' z c
      _ = ‖c‖ + R := by rw [hnorm]
  -- ‖z - 1‖ ≥ |z.im| ≥ |c.im| - R
  have hz1_lb : |c.im| - R ≤ ‖z - 1‖ := by
    calc |c.im| - R ≤ |z.im| := himz
      _ = |(z - 1).im| := by rw [Complex.sub_im]; simp
      _ ≤ ‖z - 1‖ := Complex.abs_im_le_norm _
  have hd1 : (0 : ℝ) < ‖z - 1‖ := by linarith
  -- upper bound from zeta_strip_bound (valid on the FULL strip Re > 0, s ≠ 1)
  have hsb := zeta_strip_bound hmem
  have hU1 : ‖z‖ / ‖z - 1‖ ≤ (‖c‖ + R) / (|c.im| - R) := by gcongr
  have hU2 : ‖z‖ / z.re ≤ (‖c‖ + R) / (c.re - R) := by gcongr
  have hupper : ‖riemannZeta z‖ ≤ (‖c‖ + R) / (|c.im| - R) + (‖c‖ + R) / (c.re - R) := by
    linarith [hsb, hU1, hU2]
  -- U'' ≥ 1
  have hcre_le : c.re ≤ ‖c‖ := le_trans (le_abs_self _) (Complex.abs_re_le_norm c)
  have hUge1 : (1 : ℝ) ≤ (‖c‖ + R) / (|c.im| - R) + (‖c‖ + R) / (c.re - R) := by
    have ht1 : (0 : ℝ) ≤ (‖c‖ + R) / (|c.im| - R) := by positivity
    have ht2 : (1 : ℝ) ≤ (‖c‖ + R) / (c.re - R) := by rw [le_div_iff₀ hd_re]; linarith
    linarith
  -- log‖ζ z‖ ≤ log U'' (handle a POSSIBLE zero of ζ on the sphere via log 0 = 0)
  have hlogU : Real.log ‖riemannZeta z‖
      ≤ Real.log ((‖c‖ + R) / (|c.im| - R) + (‖c‖ + R) / (c.re - R)) := by
    by_cases h0 : ‖riemannZeta z‖ = 0
    · rw [h0, Real.log_zero]; exact Real.log_nonneg hUge1
    · exact Real.log_le_log (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)) hupper
  -- lower bound at the centre
  have hlower : 2 - Real.pi ^ 2 / 6 ≤ ‖riemannZeta c‖ := zeta_norm_ge_two_sub hc2
  have hlogL : Real.log (2 - Real.pi ^ 2 / 6) ≤ Real.log ‖riemannZeta c‖ :=
    Real.log_le_log two_sub_pi_sq_div_six_pos hlower
  linarith

/-- **Strip-capable `g_sphere_log_osc`.**  The recentred-ζ Blaschke quotient boundary oscillation,
    now valid when the sphere dips below `Re = 1` — the swap that lets the disk enclose `ρ₀`.
    Mirrors `DlvpZetaEntire.g_sphere_log_osc` but feeds `zeta_sphere_log_bound_strip`. -/
theorem g_sphere_log_osc_strip {c₀ : ℂ} {R : ℝ} {g : ℂ → ℂ}
    (hR : 0 < R) (hc2 : 2 ≤ c₀.re) (hRlt : R < c₀.re - 1/2) (himc : R + 2 ≤ |c₀.im|)
    (D : CanonicalDecomp (fun w => riemannZeta (c₀ + w)) g R)
    (hf_cont : ContinuousOn (fun w => riemannZeta (c₀ + w)) (sphere 0 R))
    (hg_cont : ContinuousOn g (sphere 0 R))
    (hfg0 : ‖riemannZeta c₀‖ ≤ ‖g 0‖) :
    ∀ z ∈ sphere (0 : ℂ) R, Real.log ‖g z‖ - Real.log ‖g 0‖
      ≤ Real.log ((‖c₀‖ + R) / (|c₀.im| - R) + (‖c₀‖ + R) / (c₀.re - R))
          - Real.log (2 - Real.pi ^ 2 / 6) := by
  intro z hz
  have hgf : ‖g z‖ = ‖riemannZeta (c₀ + z)‖ :=
    (canonicalDecomp_norm_eq_on_sphere hR D hf_cont hg_cont hz).symm
  have hzc₀ : c₀ + z ∈ sphere c₀ R := by
    rw [mem_sphere_iff_norm, add_sub_cancel_left]
    rwa [mem_sphere_iff_norm, sub_zero] at hz
  have hζ := zeta_sphere_log_bound_strip c₀ R hR hc2 hRlt himc hzc₀
  have hζc₀pos : (0 : ℝ) < ‖riemannZeta c₀‖ := by
    have : 2 - Real.pi ^ 2 / 6 ≤ ‖riemannZeta c₀‖ := zeta_norm_ge_two_sub hc2
    linarith [two_sub_pi_sq_div_six_pos]
  have hlogc₀ : Real.log ‖riemannZeta c₀‖ ≤ Real.log ‖g 0‖ := Real.log_le_log hζc₀pos hfg0
  rw [hgf]
  linarith

end ZeroFreeBridge
