/- PHASE 4 (dVP frontier, item 3 input — strip-capable Jensen zero count): the version of
   `zeta_zero_count_unconditional` (`DlvpZetaDisk`) that survives the disk DIPPING BELOW `Re = 1`.

   The count `∑ divisor ≤ log(M/‖ζ c‖)/log(R/r)` (`zeta_zero_count_le`) takes the boundary bound `M`
   as a HYPOTHESIS and only needs `1 < c.re` at the CENTER plus `1 ∉ closedBall c |R|` — ζ is
   analytic on ANY disk avoiding `s = 1`, even one reaching `Re < 1`.  The original
   `zeta_zero_count_unconditional` supplies `M` via `zeta_sphere_bound` (`Re > 1`), forcing
   `|R| + 1 < c.re`.  Here we supply `M` via `zeta_strip_bound` (valid on the FULL strip
   `Re > 0`, `s ≠ 1`), so the disk may enclose a nontrivial zero `ρ₀` (`Re < 1`).

   This delivers the `O(L)` zero-count bound `∑ |divisor| ≤ Ccount·L` that `hAL_arith` (`DlvpHALArith`)
   consumes.  conjecture1_proved = False (NOT a proof of RH).
-/
import DlvpZetaDisk
import StripBound

open Complex Metric MeromorphicOn

namespace ZeroFreeBridge

/-- **Strip ζ sphere bound.**  `‖ζ z‖ ≤ (‖c‖+R)/(|c.im|-R) + (‖c‖+R)/(c.re-R)` on `sphere c R`,
    valid when the sphere dips to `Re > 1/2` (`R < c.re - 1/2`) as long as it stays off `s = 1`
    (`R + 2 ≤ |c.im|`).  Uses `zeta_strip_bound` (full strip), so survives `Re < 1`. -/
theorem zeta_sphere_bound_strip (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hRlt : R < c.re - 1/2) (himc : R + 2 ≤ |c.im|)
    {z : ℂ} (hz : z ∈ sphere c R) :
    ‖riemannZeta z‖ ≤ (‖c‖ + R) / (|c.im| - R) + (‖c‖ + R) / (c.re - R) := by
  have hnorm : ‖z - c‖ = R := by rw [← Complex.dist_eq]; exact Metric.mem_sphere.mp hz
  have hzre : c.re - R ≤ z.re := by
    have h1 : |(z - c).re| ≤ ‖z - c‖ := Complex.abs_re_le_norm _
    rw [hnorm] at h1
    have h2 : (z - c).re = z.re - c.re := by simp
    rw [h2] at h1; have := (abs_le.mp h1).1; linarith
  have hd_re : (0 : ℝ) < c.re - R := by linarith
  have hzrepos : (0 : ℝ) < z.re := by linarith
  have himz : |c.im| - R ≤ |z.im| := by
    have h1 : |(z - c).im| ≤ ‖z - c‖ := Complex.abs_im_le_norm _
    rw [hnorm] at h1
    have h2 : (z - c).im = z.im - c.im := by simp
    rw [h2] at h1
    have h4 : |c.im| - |z.im| ≤ |c.im - z.im| := abs_sub_abs_le_abs_sub c.im z.im
    rw [abs_sub_comm c.im z.im] at h4; linarith
  have hd_im : (0 : ℝ) < |c.im| - R := by linarith
  have hzne1 : z ≠ 1 := by
    intro h; rw [h] at himz; simp only [Complex.one_im, abs_zero] at himz; linarith
  have hmem : z ∈ stripDomain := ⟨hzrepos, by simpa using hzne1⟩
  have hznorm : ‖z‖ ≤ ‖c‖ + R := by
    calc ‖z‖ ≤ ‖c‖ + ‖z - c‖ := by simpa using norm_le_norm_add_norm_sub' z c
      _ = ‖c‖ + R := by rw [hnorm]
  have hz1_lb : |c.im| - R ≤ ‖z - 1‖ := by
    calc |c.im| - R ≤ |z.im| := himz
      _ = |(z - 1).im| := by rw [Complex.sub_im]; simp
      _ ≤ ‖z - 1‖ := Complex.abs_im_le_norm _
  have hd1 : (0 : ℝ) < ‖z - 1‖ := by linarith
  have hsb := zeta_strip_bound hmem
  have hU1 : ‖z‖ / ‖z - 1‖ ≤ (‖c‖ + R) / (|c.im| - R) := by gcongr
  have hU2 : ‖z‖ / z.re ≤ (‖c‖ + R) / (c.re - R) := by gcongr
  linarith [hsb, hU1, hU2]

/-- **Strip-capable UNCONDITIONAL Jensen zero-count for ζ.**  For a centre `c` with `1 < c.re`
    whose disk may reach `Re < 1` (`|R| < c.re - 1/2`) but stays off `s = 1` (`|R| + 2 ≤ |c.im|`),
    the ζ-zero count in the inner disk is bounded by an EXPLICIT `O(log|c.im|)` quantity — no
    boundary-bound hypothesis.  This is the `Re < 1`-capable companion to
    `zeta_zero_count_unconditional`, delivering `∑ divisor = O(L)` for a disk enclosing `ρ₀`. -/
theorem zeta_zero_count_strip (c : ℂ) (r R : ℝ)
    (hr : 0 < |r|) (hrR : |r| < |R|) (hc1 : 1 < c.re)
    (hRlt : |R| < c.re - 1/2) (himc : |R| + 2 ≤ |c.im|) :
    ∑ᶠ u, divisor riemannZeta (Metric.closedBall c |r|) u
      ≤ Real.log (((‖c‖ + |R|) / (|c.im| - |R|) + (‖c‖ + |R|) / (c.re - |R|)) / ‖riemannZeta c‖)
          / Real.log (R / r) := by
  have hRpos : 0 < |R| := lt_trans hr hrR
  have hcre_norm : c.re ≤ ‖c‖ := Complex.re_le_norm c
  have hd_re : 0 < c.re - |R| := by linarith
  have hd_im : 0 < |c.im| - |R| := by linarith
  have h1notin : (1 : ℂ) ∉ Metric.closedBall c |R| := by
    rw [Metric.mem_closedBall, Complex.dist_eq]
    intro hle
    have : |c.im| ≤ ‖c - 1‖ := by
      calc |c.im| = |(c - 1).im| := by rw [Complex.sub_im]; simp
        _ ≤ ‖c - 1‖ := Complex.abs_im_le_norm _
    rw [norm_sub_rev] at this
    linarith
  have hterm2 : 1 ≤ (‖c‖ + |R|) / (c.re - |R|) := by rw [le_div_iff₀ hd_re]; linarith
  have hM : 1 ≤ (‖c‖ + |R|) / (|c.im| - |R|) + (‖c‖ + |R|) / (c.re - |R|) := by
    have : 0 ≤ (‖c‖ + |R|) / (|c.im| - |R|) := by positivity
    linarith
  refine zeta_zero_count_le c r R _ hr hrR hM h1notin hc1 ?_
  intro z hz
  exact zeta_sphere_bound_strip c |R| hRpos hRlt himc hz

end ZeroFreeBridge
