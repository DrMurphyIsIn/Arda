/-
  General-case infrastructure, piece 1: convexity of the linear-fold potential
    Plin y := (11/50) * max 0 (y - T0)
  and the identity `Pval = Plin` off the two special points {1/3, 1}.

  Convexity is the basis for the Jensen reduction (arbitrary structural children -> equal children)
  in the general per-node super-solution `ValidPotentialPlain Pval`.

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.Potential
import R3Cert.Jensen

namespace R3Cert

open Real

/-- The convex "linear-fold" potential (`Pval` restricted to generic cavities). -/
noncomputable def Plin (y : ℝ) : ℝ := (11 / 50) * max 0 (y - T0)

/-- `y - T0` is (affine, hence) convex — proved directly from the `ConvexOn` definition. -/
theorem convexOn_sub_const_T0 : ConvexOn ℝ Set.univ (fun y : ℝ => y - T0) := by
  refine ⟨convex_univ, fun x _ y _ a b _ _ hab => ?_⟩
  dsimp only
  simp only [smul_eq_mul]
  have hb1 : b = 1 - a := by linarith
  subst hb1
  apply le_of_eq; ring

/-- `fun y => max 0 (y - T0)` is convex (sup of the constant `0` and the affine `y - T0`). -/
theorem convexOn_max_zero_sub : ConvexOn ℝ Set.univ (fun y : ℝ => max 0 (y - T0)) := by
  have h := (convexOn_const (0 : ℝ) convex_univ).sup convexOn_sub_const_T0
  have heq : ((fun _ : ℝ => (0 : ℝ)) ⊔ (fun y : ℝ => y - T0)) = (fun y : ℝ => max 0 (y - T0)) := by
    funext y; show (0 : ℝ) ⊔ (y - T0) = max 0 (y - T0); rfl
  rwa [heq] at h

/-- **`Plin` is convex** — directly from the convexity of the positive part (scaling by `11/50 ≥ 0`
    done by hand; the load-bearing route in `PotentialReduce` uses `posPart_add_le` instead). -/
theorem Plin_convexOn : ConvexOn ℝ Set.univ Plin := by
  obtain ⟨hconv, hineq⟩ := convexOn_max_zero_sub
  refine ⟨hconv, fun x hx y hy a b ha hb hab => ?_⟩
  have h := hineq hx hy ha hb hab
  simp only [smul_eq_mul] at h ⊢
  unfold Plin
  linarith [h]

/-- **`Pval = Plin` off the special points** `{1/3, 1}` (this is `Pval_struct`). -/
theorem Pval_eq_Plin {y : ℝ} (h3 : y ≠ 1 / 3) (h1 : y ≠ 1) : Pval y = Plin y :=
  Pval_struct y h3 h1

end R3Cert
