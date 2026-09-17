/-
RvMBacklundJensen — Backlund S(T)=O(log T), PR 3b: the Jensen zero-count of F_T is O(log T).

Counts the real zeros of the auxiliary `F_T(z)=½(ζ(z+iT)+ζ(z−iT))` on the segment `[1/2,2]` via Jensen.
Geometry (for `T ≥ 4`): centre `c = 2`, inner `r = 3/2` (so `ball 2 (3/2) ⊇ [1/2,2]` on the axis),
outer `R = 7/4 < 2` (so the sphere stays `Re > 1/4 > 0`), poles `1∓iT` far.

  * `backlundAux_analyticOnNhd_ball` — `F_T` analytic on `closedBall 2 (7/4)` (`T ≥ 4`);
  * `zeta_shift_sphere_bound` / the assembled sphere bound `‖F_T‖ ≤ 4T+19` — via the FE-free full-strip
    bound `zeta_strip_bound` (`Re > 0`, so it survives the sphere dipping below `Re = 1/2`);
  * `backlundAux_zero_count_le` — with PR 3a's centre bound and `AnalyticOnNhd.sum_divisor_le`,
    `∑ᶠ divisor F_T (closedBall 2 (3/2)) ≤ log((4T+19)/‖F_T(2)‖)/log(7/6)` — an explicit `O(log T)`.

conjecture1_proved = False.
-/
import Mathlib
import RvMBacklundAux
import RvMBacklundCenter
import StripBound
import StripRepr
import DlvpZetaDisk

open Complex MeasureTheory ZeroFreeBridge

namespace Backlund

private theorem one_notMem (c : ℂ) (hc : (7 : ℝ) / 4 < |c.im|) :
    (1 : ℂ) ∉ Metric.closedBall c (7 / 4) := by
  rw [Metric.mem_closedBall, not_le, Complex.dist_eq]
  calc (7 : ℝ) / 4 < |c.im| := hc
    _ = |((1 : ℂ) - c).im| := by rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
    _ ≤ ‖(1 : ℂ) - c‖ := Complex.abs_im_le_norm _

/-- Analyticity of `F_T` on the Jensen ball, for `T ≥ 4`. -/
theorem backlundAux_analyticOnNhd_ball {T : ℝ} (hT : 4 ≤ T) :
    AnalyticOnNhd ℂ (backlundAux T) (Metric.closedBall (2 : ℂ) (7 / 4)) := by
  have him_p : ((2 : ℂ) + (T : ℂ) * I).im = T := by simp
  have him_m : ((2 : ℂ) - (T : ℂ) * I).im = -T := by simp
  have h1p : (1 : ℂ) ∉ Metric.closedBall ((2 : ℂ) + (T : ℂ) * I) (7 / 4) :=
    one_notMem _ (by rw [him_p, abs_of_pos (by linarith)]; linarith)
  have h1m : (1 : ℂ) ∉ Metric.closedBall ((2 : ℂ) - (T : ℂ) * I) (7 / 4) :=
    one_notMem _ (by rw [him_m, abs_of_neg (by linarith)]; linarith)
  have hmaps_p : Set.MapsTo (fun z : ℂ => z + (T : ℂ) * I) (Metric.closedBall (2 : ℂ) (7 / 4))
      (Metric.closedBall ((2 : ℂ) + (T : ℂ) * I) (7 / 4)) := by
    intro z hz; rw [Metric.mem_closedBall, Complex.dist_eq] at hz ⊢
    have : z + (T : ℂ) * I - ((2 : ℂ) + (T : ℂ) * I) = z - 2 := by ring
    rw [this]; exact hz
  have hmaps_m : Set.MapsTo (fun z : ℂ => z - (T : ℂ) * I) (Metric.closedBall (2 : ℂ) (7 / 4))
      (Metric.closedBall ((2 : ℂ) - (T : ℂ) * I) (7 / 4)) := by
    intro z hz; rw [Metric.mem_closedBall, Complex.dist_eq] at hz ⊢
    have : z - (T : ℂ) * I - ((2 : ℂ) - (T : ℂ) * I) = z - 2 := by ring
    rw [this]; exact hz
  have hp : AnalyticOnNhd ℂ (fun z : ℂ => riemannZeta (z + (T : ℂ) * I))
      (Metric.closedBall (2 : ℂ) (7 / 4)) :=
    (zeta_analyticOnNhd_disk _ _ h1p).comp (fun z _ => analyticAt_id.add analyticAt_const) hmaps_p
  have hm : AnalyticOnNhd ℂ (fun z : ℂ => riemannZeta (z - (T : ℂ) * I))
      (Metric.closedBall (2 : ℂ) (7 / 4)) :=
    (zeta_analyticOnNhd_disk _ _ h1m).comp (fun z _ => analyticAt_id.sub analyticAt_const) hmaps_m
  intro z hz
  exact ((hp z hz).add (hm z hz)).div_const

/-- `‖ζ(z ± iT)‖ ≤ 4T + 19` for `z ∈ sphere 2 (7/4)`, `T ≥ 4` — via `zeta_strip_bound` (`Re > 0`). -/
theorem zeta_shift_sphere_bound {T : ℝ} (hT : 4 ≤ T) {z : ℂ}
    (hz : z ∈ Metric.sphere (2 : ℂ) (7 / 4)) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    ‖riemannZeta (z + (ε : ℂ) * (T : ℂ) * I)‖ ≤ 4 * T + 19 := by
  rw [Metric.mem_sphere, Complex.dist_eq] at hz
  set w : ℂ := z + (ε : ℂ) * (T : ℂ) * I with hw
  have hzre_bd : |z.re - 2| ≤ 7 / 4 := by
    have := Complex.abs_re_le_norm (z - 2); rw [hz] at this; simpa using this
  have hzim_bd : |z.im| ≤ 7 / 4 := by
    have := Complex.abs_im_le_norm (z - 2); rw [hz] at this; simpa using this
  have hεabs : |ε| = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have hwre : w.re = z.re := by rw [hw]; simp
  have hwim : w.im = z.im + ε * T := by rw [hw]; simp
  rw [abs_le] at hzre_bd hzim_bd
  have hwre_lb : (1 : ℝ) / 4 ≤ w.re := by rw [hwre]; linarith [hzre_bd.1]
  have hwim_abs : T - 7 / 4 ≤ |w.im| := by
    rw [hwim]
    rcases hε with h | h
    · rw [h, one_mul, abs_of_pos (by linarith [hzim_bd.1])]; linarith [hzim_bd.1]
    · rw [h, abs_of_neg (by nlinarith [hzim_bd.2])]; nlinarith [hzim_bd.2]
  have hmem : w ∈ stripDomain := by
    refine ⟨by rw [Set.mem_setOf_eq]; linarith, ?_⟩
    rw [Set.mem_singleton_iff]; intro h1
    have : w.im = 0 := by rw [h1]; simp
    rw [this] at hwim_abs; simp at hwim_abs; linarith
  have hbound := zeta_strip_bound hmem
  have hwnorm : ‖w‖ ≤ 15 / 4 + T := by
    have hz15 : ‖z‖ ≤ 15 / 4 := by
      calc ‖z‖ ≤ ‖(2 : ℂ)‖ + ‖z - 2‖ := by simpa using norm_le_norm_add_norm_sub' z 2
        _ ≤ 15 / 4 := by rw [hz]; rw [Complex.norm_ofNat]; norm_num
    have hεT : ‖(ε : ℂ) * (T : ℂ) * I‖ ≤ T := by
      have heq : ‖(ε : ℂ) * (T : ℂ) * I‖ = T := by
        rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, hεabs, one_mul, abs_of_pos (by linarith : (0:ℝ) < T)]
      exact le_of_eq heq
    calc ‖w‖ = ‖z + (ε : ℂ) * (T : ℂ) * I‖ := by rw [hw]
      _ ≤ ‖z‖ + ‖(ε : ℂ) * (T : ℂ) * I‖ := norm_add_le _ _
      _ ≤ 15 / 4 + T := by linarith
  have hwm1 : T - 7 / 4 ≤ ‖w - 1‖ := by
    calc T - 7 / 4 ≤ |w.im| := hwim_abs
      _ = |(w - 1).im| := by rw [Complex.sub_im, Complex.one_im, sub_zero]
      _ ≤ ‖w - 1‖ := Complex.abs_im_le_norm _
  have hden1 : (0 : ℝ) < T - 7 / 4 := by linarith
  have hden2 : (0 : ℝ) < w.re := by linarith
  calc ‖riemannZeta w‖ ≤ ‖w‖ / ‖w - 1‖ + ‖w‖ / w.re := hbound
    _ ≤ (15 / 4 + T) / (T - 7 / 4) + (15 / 4 + T) / (1 / 4) := by
        gcongr <;> linarith [hwnorm, hwm1, hwre_lb, hden1]
    _ ≤ 4 * T + 19 := by
        have h1 : (15 / 4 + T) / (T - 7 / 4) ≤ 4 := by rw [div_le_iff₀ hden1]; nlinarith
        have h2 : (15 / 4 + T) / (1 / 4) = 15 + 4 * T := by ring
        rw [h2]; linarith

/-- **PR 3b: the Jensen zero-count of `F_T` is `O(log T)`.**  For `T ≥ 4`, the number of zeros of `F_T`
    in `closedBall 2 (3/2)` (which contains the real segment `[1/2,2]`) is at most
    `log((4T+19)/‖F_T(2)‖) / log(7/6)`. -/
theorem backlundAux_zero_count_le {T : ℝ} (hT : 4 ≤ T) :
    ∑ᶠ u, (MeromorphicOn.divisor (backlundAux T) (Metric.closedBall (2 : ℂ) (3 / 2))) u
      ≤ Real.log ((4 * T + 19) / ‖backlundAux T ((2 : ℝ) : ℂ)‖) / Real.log (7 / 4 / (3 / 2)) := by
  have hana := backlundAux_analyticOnNhd_ball hT
  have hpi : Real.pi ^ 2 / 6 < 2 := by nlinarith [Real.pi_lt_d4, Real.pi_pos]
  have hc2 : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num
  have hc0 : backlundAux T (2 : ℂ) ≠ 0 := by
    have hge := backlundAux_two_norm_ge T
    rw [hc2] at hge
    intro h; rw [h, norm_zero] at hge; linarith
  have hMge : (1 : ℝ) ≤ 4 * T + 19 := by linarith
  have hbound : ∀ z ∈ Metric.sphere (2 : ℂ) (7 / 4), ‖backlundAux T z‖ ≤ 4 * T + 19 := by
    intro z hz
    have hp := zeta_shift_sphere_bound hT hz 1 (Or.inl rfl)
    have hm := zeta_shift_sphere_bound hT hz (-1) (Or.inr rfl)
    have hval : backlundAux T z = (riemannZeta (z + ((1 : ℝ) : ℂ) * (T : ℂ) * I)
        + riemannZeta (z + ((-1 : ℝ) : ℂ) * (T : ℂ) * I)) / 2 := by
      unfold backlundAux; congr 2 <;> push_cast <;> ring
    rw [hval, norm_div, Complex.norm_ofNat]
    have hsum : ‖riemannZeta (z + ((1 : ℝ) : ℂ) * (T : ℂ) * I)
        + riemannZeta (z + ((-1 : ℝ) : ℂ) * (T : ℂ) * I)‖ ≤ (4 * T + 19) + (4 * T + 19) :=
      le_trans (norm_add_le _ _) (add_le_add hp hm)
    linarith
  have hkey := AnalyticOnNhd.sum_divisor_le (c := (2 : ℂ)) (r := 3 / 2) (R := 7 / 4)
    (M := 4 * T + 19) (f := backlundAux T) (by norm_num) (by norm_num) hMge
    (by rw [abs_of_pos (by norm_num : (0:ℝ) < 7/4)]; exact hana)
    (hc0) (by intro z hz; rw [abs_of_pos (by norm_num : (0:ℝ) < 7/4)] at hz; exact hbound z hz)
  rw [abs_of_pos (by norm_num : (0:ℝ) < 3/2)] at hkey
  rw [hc2]
  exact hkey

end Backlund
