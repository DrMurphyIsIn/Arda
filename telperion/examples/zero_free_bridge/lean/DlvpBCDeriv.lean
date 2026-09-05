/- PHASE 4 (dVP frontier, obligation (i-b') CORE): the Borel-Caratheodory + Cauchy derivative
   bound — an analytic function's derivative at the centre is controlled by the SUP OF ITS REAL
   PART on a disk.

   This is the analytic heart of (i-b').  With the log branch `h` (DlvpLogBranch) realising the
   entire part `E = logDeriv g = deriv h` and `Re h = log‖g‖`, bounding `‖E‖` reduces to bounding
   `‖deriv h c‖` by `sup Re h`.  That is exactly Borel-Caratheodory (which controls `‖f‖` by
   `sup Re f`) followed by a Cauchy estimate (which controls `‖f'‖` by `sup‖f‖`):

     * shift/centre: `f̃(w) = h(c+w) - h(c)` is analytic on `ball 0 R`, `f̃ 0 = 0`,
       `Re f̃ ≤ M'` where `M' = sup (Re h - Re h(c))`;
     * `Complex.borelCaratheodory_zero` ⟹ `‖f̃ z‖ ≤ 2 M' r/(R-r)` on the sphere `‖z‖ = r`;
     * `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` (Cauchy) ⟹
       `‖deriv f̃ 0‖ ≤ (2 M' r/(R-r))/r = 2 M'/(R-r)`;
     * `deriv f̃ 0 = deriv h c` (translation invariance).

   Result `norm_deriv_le_of_re_le`: `‖deriv h c‖ ≤ 2 M'/(R - r)` for any `0 < r < R`.
   Function-agnostic (any analytic `h`).  Feeding `M' = A·L` (from `Re h = log‖g‖ ≤ A·L`, the
   boundary growth) gives `‖E‖ ≤ A·L`.  conjecture1_proved = False (NOT a proof of RH).
-/
import Mathlib

open Complex Metric

namespace ZeroFreeBridge

/-- **Borel-Caratheodory + Cauchy derivative bound.**  If `h` is holomorphic on `ball c R` and
    its real part exceeds `(h c).re` by at most `M' > 0` throughout the disk, then for any
    `0 < r < R` the derivative at the centre satisfies `‖deriv h c‖ ≤ 2 M'/(R - r)`. -/
theorem norm_deriv_le_of_re_le {h : ℂ → ℂ} {c : ℂ} {R r M' : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hana : DifferentiableOn ℂ h (ball c R)) (hM' : 0 < M')
    (hbound : ∀ z ∈ ball c R, (h z).re - (h c).re ≤ M') :
    ‖deriv h c‖ ≤ 2 * M' / (R - r) := by
  have hR : 0 < R := hr.trans hrR
  have hRr : (0 : ℝ) < R - r := by linarith
  set f : ℂ → ℂ := fun w => h (c + w) - h c with hf_def
  have hcball : c ∈ ball c R := mem_ball_self hR
  have hhc : DifferentiableAt ℂ h c := (hana c hcball).differentiableAt (isOpen_ball.mem_nhds hcball)
  -- domain shift sends `ball 0 R` into `ball c R`.
  have hmaps : ∀ w ∈ ball (0 : ℂ) R, c + w ∈ ball c R := by
    intro w hw
    rw [mem_ball_zero_iff] at hw
    rw [mem_ball_iff_norm]
    simpa using hw
  -- `deriv f 0 = deriv h c`.
  have hf_deriv0 : HasDerivAt f (deriv h c) 0 := by
    have hbase : HasDerivAt h (deriv h c) (c + 0) := by simpa using hhc.hasDerivAt
    exact (hbase.comp_const_add c 0).sub_const (h c)
  -- `f` holomorphic on `ball 0 R`.
  have hf_diffR : DifferentiableOn ℂ f (ball 0 R) := by
    intro w hw
    have hcw : DifferentiableAt ℂ h (c + w) :=
      (hana _ (hmaps w hw)).differentiableAt (isOpen_ball.mem_nhds (hmaps w hw))
    have h1 : DifferentiableAt ℂ (fun w => h (c + w)) w := hcw.comp w (by fun_prop)
    exact (h1.sub_const (h c)).differentiableWithinAt
  have hf0 : f 0 = 0 := by simp [hf_def]
  have hmaps_re : Set.MapsTo f (ball 0 R) {z | z.re ≤ M'} := by
    intro w hw
    simp only [Set.mem_setOf_eq, hf_def, Complex.sub_re]
    exact hbound _ (hmaps w hw)
  -- Borel-Caratheodory value bound on the Cauchy sphere.
  have hsphere : ∀ z ∈ sphere (0 : ℂ) r, ‖f z‖ ≤ 2 * M' * r / (R - r) := by
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    have hzball : z ∈ ball (0 : ℂ) R := by rw [mem_ball_zero_iff, hz]; exact hrR
    have := Complex.borelCaratheodory_zero hM' hf_diffR hmaps_re hR hzball hf0
    rwa [hz] at this
  -- Cauchy estimate on the disk of radius `r`.
  have hdcc : DiffContOnCl ℂ f (ball 0 r) := by
    refine ⟨hf_diffR.mono (ball_subset_ball hrR.le), ?_⟩
    rw [closure_ball 0 hr.ne']
    exact hf_diffR.continuousOn.mono (closedBall_subset_ball hrR)
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hdcc hsphere
  rw [hf_deriv0.deriv] at hcauchy
  calc ‖deriv h c‖ ≤ 2 * M' * r / (R - r) / r := hcauchy
    _ = 2 * M' / (R - r) := by field_simp

end ZeroFreeBridge
