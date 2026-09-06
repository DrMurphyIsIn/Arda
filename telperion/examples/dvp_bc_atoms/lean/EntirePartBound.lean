/- telperion 0.1.6 | family EntirePartBound | input-hash aef4a7abfa6840cb
   4 theorems, 1 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace EntirePartBound

open Complex Metric

/-- Analytic log branch on a disk (helper): a zero-free holomorphic `g` on `ball c r`
    admits an analytic branch `h` of `log g`. -/
private theorem log_branch_of_analytic_nonvanishing {g : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (ball c r)) (hne : ∀ z ∈ ball c r, g z ≠ 0) :
    ∃ h : ℂ → ℂ, (∀ z ∈ ball c r, HasDerivAt h (logDeriv g z) z) ∧
      h c = Complex.log (g c) ∧
      (∀ z ∈ ball c r, Complex.exp (h z) = g z) ∧
      (∀ z ∈ ball c r, (h z).re = Real.log ‖g z‖) := by
  have hcball : c ∈ ball c r := mem_ball_self hr
  have hg_an : AnalyticOnNhd ℂ g (ball c r) := hg.analyticOnNhd isOpen_ball
  have hlog_diff : DifferentiableOn ℂ (logDeriv g) (ball c r) := by
    intro z hz
    have hderivg : DifferentiableAt ℂ (deriv g) z := (hg_an z hz).deriv.differentiableAt
    have hgz : DifferentiableAt ℂ g z := (hg_an z hz).differentiableAt
    exact (hderivg.div hgz (hne z hz)).differentiableWithinAt
  obtain ⟨h, hhc, hh⟩ := (hlog_diff.isExactOn_ball).with_val_at c (Complex.log (g c))
  have hφ : ∀ z ∈ ball c r, HasDerivAt (fun w => g w * Complex.exp (-h w)) 0 z := by
    intro z hz
    have hgz : HasDerivAt g (deriv g z) z := (hg_an z hz).differentiableAt.hasDerivAt
    have hexp : HasDerivAt (fun w => Complex.exp (-h w))
        (Complex.exp (-h z) * (-(logDeriv g z))) z := ((hh z hz).neg).cexp
    have hprod := hgz.mul hexp
    have hgz0 := hne z hz
    have hderiv0 : deriv g z * Complex.exp (-h z)
        + g z * (Complex.exp (-h z) * (-(logDeriv g z))) = 0 := by
      rw [logDeriv_apply]; field_simp; ring
    rw [hderiv0] at hprod
    exact hprod
  have hconst : ∀ z ∈ ball c r,
      (fun w => g w * Complex.exp (-h w)) z = (fun w => g w * Complex.exp (-h w)) c := by
    intro z hz
    refine (convex_ball c r).is_const_of_fderivWithin_eq_zero
      (fun x hx => (hφ x hx).differentiableAt.differentiableWithinAt) ?_ hz hcball
    intro x hx
    rw [fderivWithin_of_isOpen isOpen_ball hx]
    simpa using (hφ x hx).hasFDerivAt.fderiv
  have hφc : g c * Complex.exp (-h c) = 1 := by
    rw [hhc, Complex.exp_neg, Complex.exp_log (hne c hcball), mul_inv_cancel₀ (hne c hcball)]
  have hexp_eq : ∀ z ∈ ball c r, Complex.exp (h z) = g z := by
    intro z hz
    have key : g z * Complex.exp (-h z) = 1 := (hconst z hz).trans hφc
    rw [Complex.exp_neg] at key
    have hexpne : Complex.exp (h z) ≠ 0 := Complex.exp_ne_zero _
    field_simp [hexpne] at key
    exact key.symm
  refine ⟨h, hh, hhc, hexp_eq, ?_⟩
  intro z hz
  have hnorm : ‖g z‖ = Real.exp (h z).re := by rw [← hexp_eq z hz, Complex.norm_exp]
  rw [hnorm, Real.log_exp]

/-- Real-part → derivative bound (helper): Borel-Caratheodory + Cauchy. -/
private theorem norm_deriv_le_of_re_le {h : ℂ → ℂ} {c : ℂ} {R r M' : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hana : DifferentiableOn ℂ h (ball c R)) (hM' : 0 < M')
    (hbound : ∀ z ∈ ball c R, (h z).re - (h c).re ≤ M') :
    ‖deriv h c‖ ≤ 2 * M' / (R - r) := by
  have hR : 0 < R := hr.trans hrR
  have hRr : (0 : ℝ) < R - r := by linarith
  set f : ℂ → ℂ := fun w => h (c + w) - h c with hf_def
  have hcball : c ∈ ball c R := mem_ball_self hR
  have hhc : DifferentiableAt ℂ h c := (hana c hcball).differentiableAt (isOpen_ball.mem_nhds hcball)
  have hmaps : ∀ w ∈ ball (0 : ℂ) R, c + w ∈ ball c R := by
    intro w hw
    rw [mem_ball_zero_iff] at hw
    rw [mem_ball_iff_norm]
    simpa using hw
  have hf_deriv0 : HasDerivAt f (deriv h c) 0 := by
    have hbase : HasDerivAt h (deriv h c) (c + 0) := by simpa using hhc.hasDerivAt
    exact (hbase.comp_const_add c 0).sub_const (h c)
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
  have hsphere : ∀ z ∈ sphere (0 : ℂ) r, ‖f z‖ ≤ 2 * M' * r / (R - r) := by
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    have hzball : z ∈ ball (0 : ℂ) R := by rw [mem_ball_zero_iff, hz]; exact hrR
    have := Complex.borelCaratheodory_zero hM' hf_diffR hmaps_re hR hzball hf0
    rwa [hz] at this
  have hdcc : DiffContOnCl ℂ f (ball 0 r) := by
    refine ⟨hf_diffR.mono (ball_subset_ball hrR.le), ?_⟩
    rw [closure_ball 0 hr.ne']
    exact hf_diffR.continuousOn.mono (closedBall_subset_ball hrR)
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hdcc hsphere
  rw [hf_deriv0.deriv] at hcauchy
  calc ‖deriv h c‖ ≤ 2 * M' * r / (R - r) / r := hcauchy
    _ = 2 * M' / (R - r) := by field_simp

/-- Entire-part bound (helper): compose the two above via `Re h = log‖g‖`. -/
private theorem norm_logDeriv_le_of_log_norm_le {g : ℂ → ℂ} {c : ℂ} {R r M' : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM' : 0 < M')
    (hg : DifferentiableOn ℂ g (ball c R)) (hne : ∀ z ∈ ball c R, g z ≠ 0)
    (hbound : ∀ z ∈ ball c R, Real.log ‖g z‖ - Real.log ‖g c‖ ≤ M') :
    ‖logDeriv g c‖ ≤ 2 * M' / (R - r) := by
  have hR : 0 < R := hr.trans hrR
  have hcball : c ∈ ball c R := mem_ball_self hR
  obtain ⟨h, hh, _hhc, _hexp, hre⟩ := log_branch_of_analytic_nonvanishing hR hg hne
  have hh_diff : DifferentiableOn ℂ h (ball c R) :=
    fun z hz => (hh z hz).differentiableAt.differentiableWithinAt
  have hderiv_c : deriv h c = logDeriv g c := (hh c hcball).deriv
  have hre_bound : ∀ z ∈ ball c R, (h z).re - (h c).re ≤ M' := by
    intro z hz
    rw [hre z hz, hre c hcball]
    exact hbound z hz
  have := norm_deriv_le_of_re_le hr hrR hh_diff hM' hre_bound
  rwa [hderiv_c] at this

/-- Entire-part bound on `ball c (3 / 2)`: zero-free holomorphic `g` with
    `log‖g z‖ - log‖g c‖ ≤ 6` throughout implies `‖logDeriv g c‖ ≤ 2·6/((3 / 2) - (1 / 2))`.
    A concrete copy of `norm_logDeriv_le_of_log_norm_le`. -/
theorem entire_part_bound_a (g : ℂ → ℂ) (c : ℂ)
    (hg : DifferentiableOn ℂ g (ball c ((3 / 2) : ℝ)))
    (hne : ∀ z ∈ ball c ((3 / 2) : ℝ), g z ≠ 0)
    (hbound : ∀ z ∈ ball c ((3 / 2) : ℝ),
      Real.log ‖g z‖ - Real.log ‖g c‖ ≤ (6 : ℝ)) :
    ‖logDeriv g c‖ ≤ 2 * (6 : ℝ) / (((3 / 2) : ℝ) - (1 / 2)) :=
  norm_logDeriv_le_of_log_norm_le (by norm_num) (by norm_num) (by norm_num) hg hne hbound

end EntirePartBound
