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

/-- **Brick 3 — translation-invariance**: a translate of a Bohr almost-periodic
function is Bohr almost-periodic.  The ε-almost-period SET is itself unchanged by
translating the function (the almost-period condition is translation-invariant), so
relative density transfers directly. -/
theorem isAlmostPeriodic_comp_add_right {f : ℝ → ℂ} (hf : IsAlmostPeriodic f) (t : ℝ) :
    IsAlmostPeriodic (fun x => f (x + t)) := by
  intro ε hε
  have hset : almostPeriods (fun x => f (x + t)) ε = almostPeriods f ε := by
    ext τ
    simp only [almostPeriods, Set.mem_setOf_eq]
    constructor
    · intro h y
      have h' := h (y - t)
      rwa [show (y - t) + τ + t = y + τ by ring, show (y - t) + t = y by ring] at h'
    · intro h x
      have h' := h (x + t)
      rwa [show (x + t) + τ = x + τ + t by ring] at h'
  rw [hset]
  exact hf ε hε

/-- **Brick 4 — the integer lattice is relatively dense** (window `P`).  This is the
support skeleton of every periodic function and pure tone `e^{iλx}`: their exact
periods form the lattice `Pℤ`, which meets every window, hence (being a subset of the
ε-almost-periods) makes them Bohr almost-periodic.  A support-side tool — exactly the
side the multiplicative-rigidity search (wylptmzxv) identified as load-bearing. -/
theorem relativelyDense_intMul (P : ℝ) (hP : 0 < P) :
    RelativelyDense {y : ℝ | ∃ k : ℤ, y = (k : ℝ) * P} := by
  refine ⟨P, hP, fun x => ⟨(⌈x / P⌉ : ℝ) * P, ⟨⌈x / P⌉, rfl⟩, ?_, ?_⟩⟩
  · have h1 : x / P ≤ (⌈x / P⌉ : ℝ) := Int.le_ceil _
    have := mul_le_mul_of_nonneg_right h1 hP.le
    rwa [div_mul_cancel₀ x (ne_of_gt hP)] at this
  · have h2 : (⌈x / P⌉ : ℝ) < x / P + 1 := Int.ceil_lt_add_one _
    have := mul_lt_mul_of_pos_right h2 hP
    rw [add_mul, div_mul_cancel₀ x (ne_of_gt hP), one_mul] at this
    linarith

/-- Relative density of the lattice `Pℤ` for any nonzero `P` (via `{kP} = {k(-P)}`). -/
theorem relativelyDense_intMul_of_ne (P : ℝ) (hP : P ≠ 0) :
    RelativelyDense {y : ℝ | ∃ k : ℤ, y = (k : ℝ) * P} := by
  rcases lt_or_gt_of_ne hP with hneg | hpos
  · have hset : {y : ℝ | ∃ k : ℤ, y = (k : ℝ) * P}
             = {y : ℝ | ∃ k : ℤ, y = (k : ℝ) * (-P)} := by
      ext y
      constructor
      · rintro ⟨k, rfl⟩; exact ⟨-k, by push_cast; ring⟩
      · rintro ⟨k, rfl⟩; exact ⟨-k, by push_cast; ring⟩
    rw [hset]
    exact relativelyDense_intMul (-P) (by linarith)
  · exact relativelyDense_intMul P hpos

/-- **Brick 5 — the pure tone `e^{iλx}` is Bohr almost-periodic.**  The first genuine
diffraction object (a single Bragg peak) in the substrate: its exact periods form the
lattice `(2π/λ)ℤ`, relatively dense, on which the tone returns to its value
(`e^{2πik}=1`), so those are ε-almost-periods for every `ε`. -/
theorem isAlmostPeriodic_pureTone (lam : ℝ) :
    IsAlmostPeriodic (fun x : ℝ => Complex.exp (Complex.I * (lam : ℂ) * (x : ℂ))) := by
  rcases eq_or_ne lam 0 with h0 | h0
  · have hfun : (fun x : ℝ => Complex.exp (Complex.I * (lam : ℂ) * (x : ℂ)))
             = (fun _ : ℝ => (1 : ℂ)) := by
      funext x
      simp only [h0, Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero]
    rw [hfun]; exact isAlmostPeriodic_const 1
  · intro ε hε
    have hlam : (lam : ℂ) ≠ 0 := by exact_mod_cast h0
    set P : ℝ := 2 * Real.pi / lam with hPdef
    have hPne : P ≠ 0 := by
      rw [hPdef]; exact div_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) h0
    refine relativelyDense_mono (S := {y : ℝ | ∃ k : ℤ, y = (k : ℝ) * P}) ?_
      (relativelyDense_intMul_of_ne P hPne)
    rintro τ ⟨k, rfl⟩ x
    have harg : Complex.I * (lam : ℂ) * ((x + (k : ℝ) * P : ℝ) : ℂ)
             = Complex.I * (lam : ℂ) * (x : ℂ) + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [hPdef]; push_cast; field_simp
    show ‖Complex.exp (Complex.I * (lam : ℂ) * ((x + (k : ℝ) * P : ℝ) : ℂ))
        - Complex.exp (Complex.I * (lam : ℂ) * (x : ℂ))‖ ≤ ε
    rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, sub_self, norm_zero]
    exact hε.le

end CrystallineSubstrate

#print axioms CrystallineSubstrate.isAlmostPeriodic_smul
#print axioms CrystallineSubstrate.relativelyDense_mono
#print axioms CrystallineSubstrate.isAlmostPeriodic_comp_add_right
#print axioms CrystallineSubstrate.relativelyDense_intMul
#print axioms CrystallineSubstrate.relativelyDense_intMul_of_ne
#print axioms CrystallineSubstrate.isAlmostPeriodic_pureTone
