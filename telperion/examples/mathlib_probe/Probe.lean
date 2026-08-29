/- Nail the tsum-combination joint: Re-tsum, Summable-of-re, and 3∑A+4∑B+∑C = ∑(3A+4B+C). -/
import Mathlib
open scoped Real

#check @Summable.tsum_add
#check @Summable.tsum_mul_left
#check @Summable.re

-- (A) does re_tsum apply cleanly?
example (f : ℕ → ℂ) (hf : Summable f) : (∑' n, f n).re = ∑' n, (f n).re :=
  Complex.re_tsum hf

-- (B) Summable of the re part from Summable f
example (f : ℕ → ℂ) (hf : Summable f) : Summable (fun n => (f n).re) :=
  hf.map Complex.reCLM Complex.reCLM.cont

-- (C) the linear combination
example (f g h : ℕ → ℝ) (hf : Summable f) (hg : Summable g) (hh : Summable h) :
    3 * (∑' n, f n) + 4 * (∑' n, g n) + (∑' n, h n)
      = ∑' n, (3 * f n + 4 * g n + h n) := by
  rw [Summable.tsum_add (by exact (hf.mul_left 3).add (hg.mul_left 4)) hh,
      Summable.tsum_add (hf.mul_left 3) (hg.mul_left 4),
      Summable.tsum_mul_left, Summable.tsum_mul_left]
