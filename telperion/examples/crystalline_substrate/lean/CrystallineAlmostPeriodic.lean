/-
CrystallineSubstrate.AlmostPeriodic — bricks 1–2 of the arithmetic-Fourier-quasicrystal
substrate tower (Route A / reverse-Dyson).  Bohr almost-periodicity of ℝ → ℂ, absent
from Mathlib.  The diffraction of an arithmetic Fourier quasicrystal is a pure-point
measure BECAUSE its autocorrelation is Bohr almost-periodic; this file builds the
predicate and its first closure properties.

conjecture1_proved = False.  Substrate formalization; neither proves nor approaches RH.
-/
import Mathlib

namespace CrystallineSubstrate

/-- A set `S ⊆ ℝ` is **relatively dense**: some window `L > 0` meets `S` in every
translate — every `x` has a point of `S` in `[x, x+L]`. -/
def RelativelyDense (S : Set ℝ) : Prop :=
  ∃ L : ℝ, 0 < L ∧ ∀ x : ℝ, ∃ s ∈ S, s ∈ Set.Icc x (x + L)

/-- The **ε-almost-periods** of `f : ℝ → ℂ`: translations moving `f` uniformly by ≤ ε. -/
def almostPeriods (f : ℝ → ℂ) (ε : ℝ) : Set ℝ :=
  {τ : ℝ | ∀ x : ℝ, ‖f (x + τ) - f x‖ ≤ ε}

/-- **Bohr almost-periodicity**: for every `ε > 0` the ε-almost-periods are relatively
dense. -/
def IsAlmostPeriodic (f : ℝ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → RelativelyDense (almostPeriods f ε)

/-- Relative density is monotone under set inclusion. -/
theorem relativelyDense_mono {S T : Set ℝ} (hST : S ⊆ T) (hS : RelativelyDense S) :
    RelativelyDense T := by
  obtain ⟨L, hL, h⟩ := hS
  refine ⟨L, hL, fun x => ?_⟩
  obtain ⟨s, hs, hmem⟩ := h x
  exact ⟨s, hST hs, hmem⟩

/-- `Set.univ` is relatively dense (window `L = 1`, witness `s = x`). -/
theorem relativelyDense_univ : RelativelyDense (Set.univ : Set ℝ) :=
  ⟨1, one_pos, fun x => ⟨x, Set.mem_univ x, le_refl x, by linarith⟩⟩

/-- **Brick 1 — base case**: every constant function is Bohr almost-periodic. -/
theorem isAlmostPeriodic_const (c : ℂ) : IsAlmostPeriodic (fun _ => c) := by
  intro ε hε
  refine ⟨1, one_pos, fun x => ⟨x, ?_, le_refl x, by linarith⟩⟩
  intro y
  have h0 : (fun _ => c) (y + x) - (fun _ => c) x = 0 := by simp
  rw [h0, norm_zero]
  exact hε.le

/-- **Brick 2 — closed under scalar multiplication**: if `f` is Bohr almost-periodic
then so is `c · f`.  (Half of the vector-space structure of the almost-periodic
functions; the pure tones and trigonometric polynomials are assembled from here.) -/
theorem isAlmostPeriodic_smul (c : ℂ) {f : ℝ → ℂ} (hf : IsAlmostPeriodic f) :
    IsAlmostPeriodic (fun x => c * f x) := by
  rcases eq_or_ne c 0 with hc | hc
  · simpa [hc] using isAlmostPeriodic_const (0 : ℂ)
  · intro ε hε
    have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have hεc : 0 < ε / ‖c‖ := div_pos hε hcpos
    refine relativelyDense_mono (S := almostPeriods f (ε / ‖c‖)) ?_ (hf (ε / ‖c‖) hεc)
    intro τ hτ x
    have hstep : c * f (x + τ) - c * f x = c * (f (x + τ) - f x) := by ring
    rw [hstep, norm_mul]
    calc ‖c‖ * ‖f (x + τ) - f x‖
        ≤ ‖c‖ * (ε / ‖c‖) := by
          exact mul_le_mul_of_nonneg_left (hτ x) hcpos.le
      _ = ε := by field_simp

end CrystallineSubstrate

#print axioms CrystallineSubstrate.isAlmostPeriodic_smul
#print axioms CrystallineSubstrate.relativelyDense_mono
