/-
  Proofs.MM_spectral_cooked_control_proof -- AUTHORED proof of node
  MM_spectral_cooked_control (Route-D negative control / triviality marker).

  Kernel-verified locally on rh/routes-node-proofs against the v4.32.0 toolchain
  (leanprover/lean4:v4.32.0). `#print axioms spectral_cooked_control` =
  [propext, Classical.choice, Quot.sound], 0 sorryAx. Pure Mathlib linear
  algebra; imports Mathlib only. conjecture1_proved = False.

  Content (the negative control): for ANY finite list of reals γ there is a
  Hermitian complex matrix whose characteristic polynomial has exactly those
  roots -- the diagonal matrix diag(γ). Marks "finite operator with prescribed
  real spectrum" as content-free; the Route-D wall is the completion/positivity
  clause, never operator existence. Sibling pattern: the Euler-factor rung
  control (MM_euler_factor_section_offline). Witness Hermitian by
  Matrix.diagonal_conjTranspose + Complex.conj_ofReal; charpoly by
  Matrix.charpoly_diagonal.
-/
import Mathlib

open Matrix Polynomial

theorem spectral_cooked_control (n : ℕ) (γ : Fin n → ℝ) :
    ∃ A : Matrix (Fin n) (Fin n) ℂ, A.IsHermitian ∧
      A.charpoly = ∏ i, (Polynomial.X - Polynomial.C ((γ i : ℝ) : ℂ)) := by
  refine ⟨Matrix.diagonal (fun i => ((γ i : ℝ) : ℂ)), ?_, ?_⟩
  · -- Hermitian: (diag d)ᴴ = diag d since each real entry is self-conjugate
    rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    simp [Complex.conj_ofReal]
  · -- characteristic polynomial of a diagonal matrix is ∏ (X - C dᵢ)
    exact Matrix.charpoly_diagonal _
