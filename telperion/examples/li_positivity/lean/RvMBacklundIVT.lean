/-
RvMBacklundIVT — Backlund S(T)=O(log T), PR 2: sign changes of Re ζ yield real zeros of F_T.

The auxiliary function `F_T(z) = ½(ζ(z+iT)+ζ(z−iT))` (PR 1) is REAL on the real axis (`F_T σ = Re ζ(σ+iT)`)
and, for `T ≠ 0`, CONTINUOUS there (its two poles `z = 1∓iT` are off the real axis).  So by the
intermediate value theorem, wherever `Re ζ` changes sign along the segment there is a real zero of `F_T`.
This is the "sign changes ≤ zeros of F_T" mechanism; the zeros are counted (Jensen) in PR 3.

  * `backlundAux_im` — `(F_T σ).im = 0` (real on the axis).
  * `continuous_backlundAux_line` — `σ ↦ F_T σ` is continuous (for `T ≠ 0`).
  * `backlundAux_root_of_sign_change` — opposite signs of `Re ζ` at the endpoints ⟹ a real zero of `F_T`.

conjecture1_proved = False.
-/
import Mathlib
import RvMBacklundAux

open Complex

namespace Backlund

/-- `F_T` is real on the real axis. -/
theorem backlundAux_im (T σ : ℝ) : (backlundAux T (σ : ℂ)).im = 0 := by
  rw [backlundAux_ofReal]; exact Complex.ofReal_im _

/-- For `T ≠ 0` the shifts `σ ± iT` avoid the pole at `1`, so `F_T` is continuous along the real axis. -/
theorem continuous_backlundAux_line (T : ℝ) (hT : T ≠ 0) :
    Continuous (fun σ : ℝ => backlundAux T (σ : ℂ)) := by
  rw [continuous_iff_continuousAt]
  intro σ
  have h1 : (σ : ℂ) + (T : ℂ) * I ≠ 1 := by
    intro h; have := congrArg Complex.im h; simp at this; exact hT this
  have h2 : (σ : ℂ) - (T : ℂ) * I ≠ 1 := by
    intro h; have := congrArg Complex.im h; simp at this; exact hT this
  exact ((backlundAux_analyticAt T h1 h2).continuousAt).comp
    Complex.continuous_ofReal.continuousAt

/-- **Sign change ⟹ real zero of `F_T`.**  If `Re ζ(σ+iT)` has opposite signs at `a` and `b`
    (`a ≤ b`, `T ≠ 0`), then `F_T` has a real zero in `[a,b]` — hence `Re ζ` vanishes there. -/
theorem backlundAux_root_of_sign_change (T : ℝ) (hT : T ≠ 0) {a b : ℝ} (hab : a ≤ b)
    (hsign : (backlundAux T (a : ℂ)).re * (backlundAux T (b : ℂ)).re < 0) :
    ∃ c ∈ Set.Icc a b, backlundAux T (c : ℂ) = 0 := by
  set g : ℝ → ℝ := fun σ => (backlundAux T (σ : ℂ)).re with hg
  have hgcon : ContinuousOn g (Set.Icc a b) :=
    (Complex.continuous_re.comp (continuous_backlundAux_line T hT)).continuousOn
  have hroot : ∃ c ∈ Set.Icc a b, g c = 0 := by
    rcases mul_neg_iff.mp hsign with ⟨hpa, hnb⟩ | ⟨hna, hpb⟩
    · have h0 : (0 : ℝ) ∈ Set.Icc (g b) (g a) := ⟨le_of_lt hnb, le_of_lt hpa⟩
      obtain ⟨c, hc, hgc0⟩ := intermediate_value_Icc' hab hgcon h0
      exact ⟨c, hc, hgc0⟩
    · have h0 : (0 : ℝ) ∈ Set.Icc (g a) (g b) := ⟨le_of_lt hna, le_of_lt hpb⟩
      obtain ⟨c, hc, hgc0⟩ := intermediate_value_Icc hab hgcon h0
      exact ⟨c, hc, hgc0⟩
  obtain ⟨c, hc, hgc0⟩ := hroot
  refine ⟨c, hc, ?_⟩
  have hre : (backlundAux T (c : ℂ)).re = 0 := hgc0
  have him : (backlundAux T (c : ℂ)).im = 0 := backlundAux_im T c
  simp only [Complex.ext_iff, Complex.zero_re, Complex.zero_im]
  exact ⟨hre, him⟩

end Backlund
