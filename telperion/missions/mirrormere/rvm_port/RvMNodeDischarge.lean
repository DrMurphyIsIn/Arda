import RvMDischarge
-- Reproduce the mirrormere node's Quasicrystal defs VERBATIM (identical to MMDefs).
namespace Quasicrystal
def RvMUnboundedMeanDensity (S : Set ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ∃ (F : Finset ℝ) (a L : ℝ),
    0 ≤ L ∧ (↑F ⊆ S) ∧ (∀ x ∈ F, x ∈ Set.Icc a (a + L)) ∧ r * L + 1 < F.card
def zetaOrdinates : Set ℝ :=
  {t : ℝ | ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ρ.im = t}
open Quasicrystal
-- The node theorem, discharged (was `by sorry`).  Defs are definitionally identical to
-- RvMGlue's, so the port discharge closes it directly.
theorem rvm_unbounded_mean_density : RvMUnboundedMeanDensity zetaOrdinates :=
  RvMGlue.rvm_unbounded_mean_density
end Quasicrystal
