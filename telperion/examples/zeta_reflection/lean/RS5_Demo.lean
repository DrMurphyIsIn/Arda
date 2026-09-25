/-  RS5_Demo.lean -- lane B5: the IVT corollary applied to lane B4's two certified heights.

    `RS4.Demo.sign_B` : Re completedRiemannZeta(1/2 + 10000 i) < 0      (kernel-checked, lane B4)
    `RS4.Demo.sign_A` : Re completedRiemannZeta(1/2 + 10000.5 i) > 0    (kernel-checked, lane B4)
    `RS5.exists_zeta_zero_of_signs` (IVT on the continuous real function t -> Re Lambda(1/2+it), and
    Lambda = 0 -> riemannZeta = 0 on the line)  ==>  a zero of Mathlib's `riemannZeta` on the critical
    line with ordinate in (10000, 10000.5).  (mpmath: the zero is at 10000.0655...; untrusted.)

    Negative controls (each `... = false` is ALSO decided by the kernel), on the [510, 520] band data:
      * `bad_flip`   : one sample with its box sign-flipped;
      * `bad_margin` : one sample whose margin numerator E is halved (MarginOK fails: E / 2^64 < t^(-3/4));
      * `bad_order`  : two samples swapped (heights no longer strictly increasing);
      * `bad_floor`  : an honest RS4 certificate at t = 508 (exact box, emitted like the others) is
                       REJECTED by `RS5.sampleOK`, since 508 < 509 (the seam bound's range).

    conjecture1_proved = False.  One certified zero; nothing about RH.
-/
import RS4_Demo
import RS5_Band
import RS5_Band_T510_C0

open Complex

namespace RS5.Demo

/-- **A zero of `riemannZeta` on the critical line with ordinate in (10000, 10000.5).** -/
theorem zeta_zero_10000 :
    ∃ t ∈ Set.Ioo (10000 : ℝ) (20001 / 2), riemannZeta (1 / 2 + (t : ℂ) * I) = 0 :=
  RS5.exists_zeta_zero_of_signs (by norm_num) (Or.inr ⟨RS4.Demo.sign_B, RS4.Demo.sign_A⟩)

/-! ## negative controls -/

open RS5 RS5.BandT510.C0

/-- The first sample of the [510, 520] band with its box sign-flipped. -/
noncomputable def s0_flip : Sample :=
  { s0 with z := { s0.z with zlo := -s0.z.zhi, zhi := -s0.z.zlo } }

theorem bad_flip : bandOK (s0_flip :: rest) = false := by decide +kernel

/-- The first sample with its margin numerator halved. -/
noncomputable def s0_half : Sample := { s0 with E := s0.E / 2 }

theorem bad_margin : bandOK (s0_half :: rest) = false := by decide +kernel

/-- The first two samples swapped. -/
theorem bad_order : bandOK (rest.headD s0 :: s0 :: rest.tail) = false := by decide +kernel

/-- An honest RS4 certificate at t = 508 = 32512 / 2^6 (below the seam range). -/
noncomputable def s508 : Sample :=
  ⟨32512, 6, 172393917320239123, ⟨8, 165867631975556110254, 165867631975556110266,
    2286709923234962165, 2286709923234962168, 2155698214867571292, 2155698724904825410,
    15888675741772936086688, 15888748625848529536787, 6151751183996191129, 6151751183996191130,
    114942577531613394929, 114942577531613395021, 8197773122026406806, 8197773122026407033,
    16677632910744999831, 16677632910781893320, 1846635765474702147129467453165597880416,
    1856153990141107366751183536518027718857⟩⟩

theorem bad_floor : sampleOK s508 = false := by decide +kernel

end RS5.Demo
