/-
CompletedZetaConjugation — the Λ-conjugation brick, completing the reflection quadruple.

The wall map (RH_WALL_THREE_SWEEP_MAP_2026-09-16.md) records: "the same-ordinate refinement
— the partner 1 − conj(ρ) at the SAME ordinate — needs a Λ-conjugation lemma absent from
Mathlib; a clean next brick."  This is that brick.  Mathlib (v4.32 pin) has the two raw
symmetries ζ(conj s) = conj(ζ s) (Schwarz) and Λ(1−s) = Λ(s) (functional equation), but no
conjugation equivariance for Γℝ or Λ.  We derive both — Γℝ from `Gamma_conj` + `cpow_conj`
(π is a positive real, so its `arg` is 0, never π), Λ from the bridge ζ = Λ/Γℝ off the
Γℝ-degenerate set (0 < Re s suffices; Γℝ is nonvanishing there) — and then formalize what
OrdinateInsensitivity.riemannZeta_zero_conj could only say in prose: every completed-zeta
zero ρ with 0 < Re ρ has a partner 1 − conj ρ that is a zero AT THE SAME ORDINATE with the
MIRRORED real part 1 − Re ρ, and that partner coincides with ρ exactly when ρ is on the
critical line.  Off-line-ness is never solitary at a fixed height — the kernel now states
the same-ordinate mirrored pair itself, not just the opposite-ordinate conjugate.

conjecture1_proved = False.  A structural certificate about the zero set's symmetry,
NOT an RH route: it explains why reflection-invariant statistics cannot force Re = ½.
-/
import Mathlib

open Complex ComplexConjugate Real

namespace LambdaConjugation

/-- **Conjugation equivariance of the archimedean factor** `Γℝ(s) = π^(-s/2) Γ(s/2)`.
Both factors are conjugation-equivariant: the base `π` is a positive real (its argument
is `0`, never `π`, so `cpow_conj` applies), and `Γ` satisfies Schwarz reflection. -/
theorem Gammaℝ_conj (s : ℂ) : Gammaℝ (conj s) = conj (Gammaℝ s) := by
  rw [Gammaℝ_def, Gammaℝ_def, map_mul]
  congr 1
  · have harg : (↑π : ℂ).arg ≠ π := by
      rw [Complex.arg_ofReal_of_nonneg pi_pos.le]
      exact (Real.pi_ne_zero).symm
    have h : -conj s / 2 = conj (-s / 2) := by
      simp [map_div₀, map_ofNat]
    rw [h, Complex.cpow_conj _ _ harg, Complex.conj_ofReal]
  · have h : conj s / 2 = conj (s / 2) := by
      simp [map_div₀, map_ofNat]
    rw [h, Complex.Gamma_conj]

/-- **Conjugation equivariance of the completed zeta function** `Λ(conj s) = conj (Λ s)`
for `0 < Re s` (which covers the whole open strip and hence every nontrivial zero; the
hypothesis keeps us off the set `{0, −2, −4, …}` where `Γℝ` vanishes and the bridge
`ζ = Λ/Γℝ` degenerates). -/
theorem completedRiemannZeta_conj_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta (conj s) = conj (completedRiemannZeta s) := by
  have h0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
  have h0c : conj s ≠ 0 := by
    rw [starRingEnd_apply]
    exact star_ne_zero.mpr h0
  have hres : 0 < (conj s).re := by simpa using hs
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
  have hGc : Gammaℝ (conj s) ≠ 0 := Gammaℝ_ne_zero_of_re_pos hres
  have hb : completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
    rw [riemannZeta_def_of_ne_zero h0, mul_comm, div_mul_cancel₀ _ hG]
  have hbc : completedRiemannZeta (conj s) = Gammaℝ (conj s) * riemannZeta (conj s) := by
    rw [riemannZeta_def_of_ne_zero h0c, mul_comm, div_mul_cancel₀ _ hGc]
  rw [hbc, hb, map_mul, Gammaℝ_conj, riemannZeta_conj]

/-- **The same-ordinate mirror partner** — the theorem the reflection family existed for.
Every completed-zeta zero `ρ` with `0 < Re ρ` has a partner `1 − conj ρ` that is
(i) a zero, (ii) at the SAME ordinate `Im ρ`, (iii) at the MIRRORED real part `1 − Re ρ`,
and (iv) the partner equals `ρ` exactly when `Re ρ = ½`.  So an off-line zero always brings
a DISTINCT second zero at its own height, mirrored about the critical line — the precise
structure that makes every reflection-invariant functional unable to separate an on-line
zero from an off-line pair, and the kernel-checked reason the missing idea must break this
reflection unconditionally.  conjecture1_proved = False. -/
theorem same_ordinate_mirror_partner (ρ : ℂ) (hρ : completedRiemannZeta ρ = 0)
    (hre : 0 < ρ.re) :
    completedRiemannZeta (1 - conj ρ) = 0
      ∧ (1 - conj ρ).im = ρ.im
      ∧ (1 - conj ρ).re = 1 - ρ.re
      ∧ (1 - conj ρ = ρ ↔ ρ.re = 1 / 2) := by
  have hconj : completedRiemannZeta (conj ρ) = 0 := by
    rw [completedRiemannZeta_conj_of_re_pos hre, hρ, map_zero]
  refine ⟨?_, by simp, by simp, ?_⟩
  · rw [completedRiemannZeta_one_sub]
    exact hconj
  · constructor
    · intro h
      have h2 : (1 - conj ρ).re = ρ.re := by rw [h]
      simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at h2
      linarith
    · intro h
      apply Complex.ext
      · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re, h]
        norm_num
      · simp only [Complex.sub_im, Complex.one_im, Complex.conj_im]
        ring

end LambdaConjugation

#print axioms LambdaConjugation.Gammaℝ_conj
#print axioms LambdaConjugation.completedRiemannZeta_conj_of_re_pos
#print axioms LambdaConjugation.same_ordinate_mirror_partner
