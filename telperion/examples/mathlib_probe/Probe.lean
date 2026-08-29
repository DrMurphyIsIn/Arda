/- Nail the combination via real HasSum; then the mini-assembly pattern for rung 4. -/
import Mathlib
open scoped Real

-- combination via real HasSum (avoids the complex SummationFilter L issue)
example (A B C : ℕ → ℝ) (hA : Summable A) (hB : Summable B) (hC : Summable C) :
    3 * (∑' n, A n) + 4 * (∑' n, B n) + (∑' n, C n) = ∑' n, (3 * A n + 4 * B n + C n) :=
  (((hA.hasSum.mul_left 3).add (hB.hasSum.mul_left 4)).add hC.hasSum).tsum_eq.symm

-- mini-assembly: 0 <= 3 Re(∑f) + 4 Re(∑g) + Re(∑h)  from per-term nonneg
example (f g h : ℕ → ℂ) (hf : Summable f) (hg : Summable g) (hh : Summable h)
    (hpt : ∀ n, 0 ≤ 3 * (f n).re + 4 * (g n).re + (h n).re) :
    0 ≤ 3 * (∑' n, f n).re + 4 * (∑' n, g n).re + (∑' n, h n).re := by
  have hA : Summable (fun n => (f n).re) := hf.map Complex.reCLM Complex.reCLM.cont
  have hB : Summable (fun n => (g n).re) := hg.map Complex.reCLM Complex.reCLM.cont
  have hC : Summable (fun n => (h n).re) := hh.map Complex.reCLM Complex.reCLM.cont
  rw [Complex.re_tsum hf, Complex.re_tsum hg, Complex.re_tsum hh,
      (((hA.hasSum.mul_left 3).add (hB.hasSum.mul_left 4)).add hC.hasSum).tsum_eq.symm]
  exact tsum_nonneg hpt
