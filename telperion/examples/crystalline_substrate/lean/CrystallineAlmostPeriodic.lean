/-
CrystallineSubstrate.AlmostPeriodic — brick 1 of the arithmetic-Fourier-quasicrystal
substrate tower (Route A / reverse-Dyson).  Bohr almost-periodicity of functions
ℝ → ℂ — genuinely ABSENT from Mathlib (checked 2026-09-16).  Foundational: the
diffraction of an arithmetic Fourier quasicrystal is a pure-point measure BECAUSE
its autocorrelation is a Bohr almost-periodic function; this file defines that
predicate and proves the base case.

conjecture1_proved = False.  This is substrate formalization; it neither proves nor
approaches RH.
-/
import Mathlib

namespace CrystallineSubstrate

/-- A set `S ⊆ ℝ` is **relatively dense**: some window length `L > 0` meets `S` in
every translate — every real `x` has a point of `S` in `[x, x+L]`. -/
def RelativelyDense (S : Set ℝ) : Prop :=
  ∃ L : ℝ, 0 < L ∧ ∀ x : ℝ, ∃ s ∈ S, s ∈ Set.Icc x (x + L)

/-- The **ε-almost-periods** of `f : ℝ → ℂ`: translations moving `f` uniformly by
at most `ε`. -/
def almostPeriods (f : ℝ → ℂ) (ε : ℝ) : Set ℝ :=
  {τ : ℝ | ∀ x : ℝ, ‖f (x + τ) - f x‖ ≤ ε}

/-- **Bohr almost-periodicity**: for every `ε > 0` the ε-almost-periods are
relatively dense.  (Bochner-equivalent to being a uniform limit of trigonometric
polynomials — a later brick.) -/
def IsAlmostPeriodic (f : ℝ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → RelativelyDense (almostPeriods f ε)

/-- `Set.univ` is relatively dense (window `L = 1`, witness `s = x`). -/
theorem relativelyDense_univ : RelativelyDense (Set.univ : Set ℝ) :=
  ⟨1, one_pos, fun x => ⟨x, Set.mem_univ x, le_refl x, by linarith⟩⟩

/-- **Brick-1 base case**: every constant function is Bohr almost-periodic.  Every
real is an ε-almost-period (the displacement is `0 ≤ ε`), and `ℝ` is relatively
dense. -/
theorem isAlmostPeriodic_const (c : ℂ) : IsAlmostPeriodic (fun _ => c) := by
  intro ε hε
  refine ⟨1, one_pos, fun x => ⟨x, ?_, le_refl x, by linarith⟩⟩
  intro y
  have h0 : (fun _ => c) (y + x) - (fun _ => c) x = 0 := by simp
  rw [h0, norm_zero]
  exact hε.le

end CrystallineSubstrate

#print axioms CrystallineSubstrate.isAlmostPeriodic_const
