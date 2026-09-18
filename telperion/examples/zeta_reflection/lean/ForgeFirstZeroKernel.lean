/-  ForgeFirstZeroKernel.lean -- ANDÚRIL: THE argument-free first-zero theorem.

    Instantiates `ForgeFirstZero.first_zero_of_theta_boxes` with:
      * the two θ-limits Λ14, Λ15 supplied (with their `Tendsto`) by
        `ThetaConverge.convergence_obligation` at (x,y) = (1/4, 7) and (1/4, 15/2);
      * the FOUR cos/sin φ boxes proved kernel-clean in `ForgeThetaBox.cossin_{14,15}`.

    The result `first_zero_kernel` has NO hypotheses and NO arguments: a nontrivial zero of
    `completedRiemannZeta` exists in the open interval (14, 15), verified entirely by kernel
    computation over rational certificates.  conjecture1_proved = False -- this is a single
    verified zero, not a proof of RH.
-/
import ForgeFirstZero
import ForgeThetaBox
import ThetaConverge

open Complex Real Filter ThetaGap

namespace ForgeFirstZeroKernel

/-- `Γ(1/4 + (15/2)i) ≠ 0` (poles of Γ are at non-positive reals; here im = 15/2 ≠ 0). -/
private theorem gamma_15_ne_zero : Complex.Gamma (((1/4:ℝ):ℂ) + ((15/2:ℝ):ℂ)*I) ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro m hcontra
  have him := congrArg Complex.im hcontra
  simp at him

/-- **`first_zero_kernel` -- an argument-free, hypothesis-free zeta zero in (14, 15).**
    There is a real `r ∈ (14, 15)` with `completedRiemannZeta (1/2 + r·i) = 0`.  Proved by
    kernel evaluation only: the ζ boxes (`ForgeZeta14/15`), the θ boxes (`ForgeThetaBox`), and
    the magnitude-free sign bridge (`ZeroSignDecomp.first_zero_of_sign_quantities`). -/
theorem first_zero_kernel :
    ∃ r : ℝ, 14 < r ∧ r < 15 ∧ completedRiemannZeta (1 / 2 + (r : ℂ) * Complex.I) = 0 := by
  -- Λ14 from convergence_obligation at (1/4, 7); bridge 7 = 14/2 for the imLnVal function arg.
  obtain ⟨Λ14, hΛ14tend, _⟩ :=
    ThetaConverge.convergence_obligation (1/4) 7 (by norm_num) ThetaConverge.gamma_14_ne_zero
  obtain ⟨Λ15, hΛ15tend, _⟩ :=
    ThetaConverge.convergence_obligation (1/4) (15/2) (by norm_num) gamma_15_ne_zero
  -- Bridge the imLnVal function argument: `imLnVal (1/4) 7 = imLnVal (1/4) (14/2)`.
  have hf14 : imLnVal (1/4) (14/2) = imLnVal (1/4) 7 := by norm_num
  have hΛ14 : Filter.Tendsto (imLnVal (1/4) (14/2)) Filter.atTop (nhds Λ14) := by
    rw [hf14]; exact hΛ14tend
  -- cos/sin boxes.
  obtain ⟨hc14lo, hc14hi, hs14lo, hs14hi⟩ := ForgeThetaBox.cossin_14 Λ14 hΛ14
  obtain ⟨hc15lo, hc15hi, hs15lo, hs15hi⟩ := ForgeThetaBox.cossin_15 Λ15 hΛ15tend
  exact ForgeFirstZero.first_zero_of_theta_boxes Λ14 hΛ14 Λ15 hΛ15tend
    hc14lo hc14hi hs14lo hs14hi hc15lo hc15hi hs15lo hs15hi

end ForgeFirstZeroKernel
