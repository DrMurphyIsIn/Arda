import Mathlib

/-!
# Λ(1/2 + it) is real on the critical line (Stage-1 real-on-line prelude)

This is the one genuine analytic sub-lemma of Stage 1 of the zeta-zero-localization
project.  It establishes that the completed Riemann zeta function
`Λ = completedRiemannZeta` takes real values on the critical line `Re s = 1/2`,
so that sign-changes of `Λ(1/2 + it)` certify zeros on the critical line.

The proof derives the conjugation symmetry
`completedRiemannZeta (conj s) = conj (completedRiemannZeta s)` from the fact that
`Λ` has real Dirichlet/Mellin coefficients.  Concretely we conjugate the termwise
representation
`Λ s = π^(-s/2) · Γ(s/2) · Σ 1/n^s`  (valid for `1 < re s`)
and propagate the resulting identity to all of `ℂ` by the identity principle for the
entire function `Λ₀`.  Combined with the functional equation
`Λ(1 - s) = Λ(s)` and the observation that at `s = 1/2 + t·I` one has
`conj s = 1 - s`, this forces `Λ(1/2 + t·I)` to be fixed by conjugation, hence real.

Note: `conjecture1_proved = False`.  This lemma is a kernel prelude only; it does NOT
prove RH.  It records the real-on-line symmetry that downstream sign-change arguments
consume.
-/

open Complex Filter Topology ComplexConjugate

namespace ZetaZeroLocalization

/-- Conjugation symmetry for the *entire* completed zeta `Λ₀`:
`Λ₀ (conj s) = conj (Λ₀ s)`.  Proved by the identity principle: the two sides are
entire functions of `s` that agree on the half-plane `1 < re s`, where `Λ₀` has an
explicit real-coefficient Mellin representation. -/
theorem completedRiemannZeta₀_conj (s : ℂ) :
    completedRiemannZeta₀ (conj s) = conj (completedRiemannZeta₀ s) := by
  -- `g z := conj (Λ₀ (conj z))` is entire (composition of entire `Λ₀` with conjugation).
  have hg_an : AnalyticOnNhd ℂ (fun z ↦ conj (completedRiemannZeta₀ (conj z))) Set.univ :=
    DifferentiableOn.analyticOnNhd
      (fun z _ ↦
        (differentiableAt_conj_conj_iff.mpr
          differentiable_completedZeta₀.differentiableAt).differentiableWithinAt)
      isOpen_univ
  have hf_an : AnalyticOnNhd ℂ completedRiemannZeta₀ Set.univ :=
    analyticOnNhd_univ_iff_differentiable.mpr differentiable_completedZeta₀
  -- On `1 < re z`, conjugating the Mellin representation of `Λ` gives `conj (Λ (conj z)) = Λ z`.
  have hΛ (z : ℂ) (hz : 1 < z.re) :
      conj (completedRiemannZeta (conj z)) = completedRiemannZeta z := by
    rw [completedZeta_eq_tsum_of_one_lt_re (by rwa [conj_re]),
      completedZeta_eq_tsum_of_one_lt_re hz]
    have hπ : (Real.pi : ℂ).arg ≠ Real.pi := by
      rw [arg_ofReal_of_nonneg Real.pi_pos.le]; exact fun h => Real.pi_ne_zero h.symm
    rw [map_mul, map_mul, conj_tsum]
    congr 1
    · congr 1
      · -- `conj (π ^ (-(conj z) / 2)) = π ^ (-z / 2)`
        rw [show (-(conj z) / 2) = conj (-z / 2) by
              simp only [map_div₀, map_neg, map_ofNat],
          ← conj_cpow _ _ hπ, conj_ofReal]
      · -- `conj (Γ (conj z / 2)) = Γ (z / 2)`
        rw [show (conj z / 2) = conj (z / 2) by simp only [map_div₀, map_ofNat],
          Gamma_conj, conj_conj]
    · -- termwise: `conj (1 / (n : ℂ) ^ conj z) = 1 / (n : ℂ) ^ z`
      refine tsum_congr (fun n => ?_)
      have hn : (n : ℂ).arg ≠ Real.pi := by
        rw [natCast_arg]; exact fun h => Real.pi_ne_zero h.symm
      rw [map_div₀, map_one, ← conj_cpow _ _ hn, conj_natCast]
  -- Transfer to `Λ₀` on `1 < re z` using `Λ₀ z = Λ z + 1/z + 1/(1 - z)`.
  have hΛ₀ (z : ℂ) (hz : 1 < z.re) :
      conj (completedRiemannZeta₀ (conj z)) = completedRiemannZeta₀ z := by
    -- Expand both `Λ₀` via `Λ₀ w = Λ w + 1/w + 1/(1 - w)`, then conjugate the pieces.
    rw [show completedRiemannZeta₀ (conj z)
          = completedRiemannZeta (conj z) + 1 / (conj z) + 1 / (1 - conj z) by
            rw [completedRiemannZeta_eq]; ring,
      show completedRiemannZeta₀ z
          = completedRiemannZeta z + 1 / z + 1 / (1 - z) by
            rw [completedRiemannZeta_eq]; ring,
      map_add, map_add, hΛ z hz, map_div₀, map_one, map_div₀, map_one, map_sub, map_one,
      conj_conj]
  -- Identity principle: the two entire functions agree on the preconnected set `univ`.
  have heq : Set.EqOn (fun z ↦ conj (completedRiemannZeta₀ (conj z)))
      completedRiemannZeta₀ Set.univ := by
    apply hg_an.eqOn_of_preconnected_of_eventuallyEq hf_an isPreconnected_univ
      (Set.mem_univ 2)
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz using hΛ₀ z hz
  -- Evaluate at `s`, then conjugate both sides.
  have hval := heq (Set.mem_univ s)
  simp only at hval
  have := congrArg (starRingEnd ℂ) hval
  simpa [conj_conj] using this

/-- Conjugation symmetry for the completed Riemann zeta function `Λ`:
`Λ (conj s) = conj (Λ s)`.  Follows from the same symmetry of the entire `Λ₀` and the
explicit relation `Λ s = Λ₀ s - 1/s - 1/(1 - s)`, whose rational correction terms have
real coefficients. -/
theorem completedRiemannZeta_conj (s : ℂ) :
    completedRiemannZeta (conj s) = conj (completedRiemannZeta s) := by
  rw [completedRiemannZeta_eq (conj s), completedRiemannZeta_eq s,
    completedRiemannZeta₀_conj, map_sub, map_sub, map_div₀, map_one, map_div₀, map_one,
    map_sub, map_one]

/-- **Λ is real on the critical line.**  For every `t : ℝ`, the completed Riemann zeta
value `Λ(1/2 + t·I)` has zero imaginary part.  This is the Stage-1 real-on-line prelude:
it lets sign-changes of `Λ(1/2 + it)` certify zeros on the critical line. -/
theorem completedZeta_im_eq_zero (t : ℝ) :
    (completedRiemannZeta (1/2 + t * Complex.I)).im = 0 := by
  set s : ℂ := 1/2 + t * Complex.I with hs
  -- At `s = 1/2 + t·I` we have `conj s = 1 - s`.
  have hconj : conj s = 1 - s := by
    rw [hs]
    simp only [map_add, map_mul, map_div₀, map_one, map_ofNat, Complex.conj_I,
      Complex.conj_ofReal]
    ring
  -- `conj (Λ s) = Λ (conj s) = Λ (1 - s) = Λ s`.
  have key : conj (completedRiemannZeta s) = completedRiemannZeta s := by
    rw [← completedRiemannZeta_conj, hconj, completedRiemannZeta_one_sub]
  -- `conj z = z` forces `z.im = 0`.
  exact Complex.conj_eq_iff_im.mp key

end ZetaZeroLocalization
