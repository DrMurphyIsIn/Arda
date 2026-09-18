/-
RvMSpectralCookedControl — MIRRORMERE Route D, layer D4: the cooked-spectrum NEGATIVE CONTROL.

The Route-D (Hilbert–Pólya / spectral) terminal is NOT "find an operator whose spectrum is the
zeta zeros": bare operator existence is content-free.  This file certifies that triviality marker
in the kernel — for ANY finite list of reals `γ : Fin n → ℝ` there is a Hermitian complex matrix
whose characteristic polynomial has exactly those roots (the diagonal matrix).  So "a finite
self-adjoint operator with the (certified) zero ordinates as spectrum" is a statement about the
diagonal matrix, and carries no arithmetic content; the wall is the completion/positivity clause
(the merge with Route B's Weil/Li form), never operator existence.

Mathlib only (`Matrix.isHermitian_diagonal_iff` + `Matrix.charpoly_diagonal`).  Mirrors the
registry node `MM_spectral_cooked_control` (telperion/missions/mirrormere) VERBATIM.
No RH progress is claimed; conjecture1_proved = False.
-/
import Mathlib

/-- **Cooked-spectrum control.**  Any finite real spectrum is realized, with multiplicity, as the
    characteristic polynomial of a Hermitian complex matrix — the diagonal matrix.  Marks "finite
    operator with prescribed real spectrum" as content-free for Route D. -/
theorem spectral_cooked_control (n : ℕ) (γ : Fin n → ℝ) :
    ∃ A : Matrix (Fin n) (Fin n) ℂ, A.IsHermitian ∧
      A.charpoly = ∏ i, (Polynomial.X - Polynomial.C ((γ i : ℝ) : ℂ)) := by
  refine ⟨Matrix.diagonal (fun i => ((γ i : ℝ) : ℂ)), ?_, ?_⟩
  · rw [Matrix.isHermitian_diagonal_iff]
    intro i
    rw [isSelfAdjoint_iff, Complex.star_def, Complex.conj_ofReal]
  · exact Matrix.charpoly_diagonal _
