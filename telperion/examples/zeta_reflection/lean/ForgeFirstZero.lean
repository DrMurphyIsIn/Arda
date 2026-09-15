/-  ForgeFirstZero.lean -- ANDÚRIL cert-forge: the final assembly, conditional on the two φ boxes.

    The ζ HALF is DONE and kernel-green (ForgeZeta14/15): hypothesis-free boxes for Re/Im ζ(1/2+it),
    t ∈ {14,15}.  This file consumes those boxes plus the two θ boxes (`cos φ`, `sin φ` at both heights
    — the sole remaining forge residue) and produces the first-zero theorem by:
      * interval-arithmetic evaluation of the sign quantity S(t) = cos φ·Re ζ − sin φ·Im ζ
        (`ForgeLogBracket.mul_encl` for each product, then subtraction), giving S(14) < 0, S(15) > 0;
      * `ZeroSignDecomp.first_zero_of_sign_quantities` (the PROVED magnitude-free bridge).

    `first_zero_of_theta_boxes` is therefore an argument-free first-zero theorem MODULO the two φ boxes
    — the exact interface the θ instrument must hit.  When the θ boxes land (imLnVal partial + rate →
    `phi_box`, then cos/sin over the ≈1.78 / 1.37 rad argument), instantiate here for `first_zero_kernel`.

    conjecture1_proved = False.
-/
import ZeroSignDecomp_t14
import ForgeZeta14
import ForgeZeta15
import ForgeLogBracket

open Complex Real ZeroSignDecomp ThetaGap

namespace ForgeFirstZero

/-- Bridge: the ForgeZeta ℂ-cast height form equals the target ℝ-cast form. -/
private theorem zbridge14 : ((1/2:ℂ) + (14:ℂ)*Complex.I) = ((1/2:ℂ)+(14:ℝ)*I) := by push_cast; ring
private theorem zbridge15 : ((1/2:ℂ) + (15:ℂ)*Complex.I) = ((1/2:ℂ)+(15:ℝ)*I) := by push_cast; ring

/-- **THE FINAL ASSEMBLY (conditional on the two φ boxes).**  Given the θ-limits `Λ14, Λ15` and
    kernel boxes for `cos φ` / `sin φ` at both heights (the forge's θ residue), there is a nontrivial
    zero of `completedRiemannZeta` in `(14, 15)`.  The ζ boxes are the PROVEN `ForgeZeta14/15`.  Only
    the four φ-box hypotheses remain; discharging them yields the argument-free `first_zero_kernel`. -/
theorem first_zero_of_theta_boxes
    (Λ14 : ℝ) (hΛ14 : Filter.Tendsto (imLnVal (1/4) (14/2)) Filter.atTop (nhds Λ14))
    (Λ15 : ℝ) (hΛ15 : Filter.Tendsto (imLnVal (1/4) (15/2)) Filter.atTop (nhds Λ15))
    -- θ boxes at a φ-box half-width of ≈0.15 rad (the loose target the θ instrument must hit):
    (hcos14lo : (-36/100 : ℝ) ≤ Real.cos (Λ14 - (14/2)*Real.log Real.pi))
    (hcos14hi : Real.cos (Λ14 - (14/2)*Real.log Real.pi) ≤ (-6/100 : ℝ))
    (hsin14lo : (-100/100 : ℝ) ≤ Real.sin (Λ14 - (14/2)*Real.log Real.pi))
    (hsin14hi : Real.sin (Λ14 - (14/2)*Real.log Real.pi) ≤ (-93/100 : ℝ))
    (hcos15lo : (5/100 : ℝ) ≤ Real.cos (Λ15 - (15/2)*Real.log Real.pi))
    (hcos15hi : Real.cos (Λ15 - (15/2)*Real.log Real.pi) ≤ (35/100 : ℝ))
    (hsin15lo : (-100/100 : ℝ) ≤ Real.sin (Λ15 - (15/2)*Real.log Real.pi))
    (hsin15hi : Real.sin (Λ15 - (15/2)*Real.log Real.pi) ≤ (-93/100 : ℝ)) :
    ∃ r : ℝ, 14 < r ∧ r < 15 ∧ completedRiemannZeta (1 / 2 + (r : ℂ) * Complex.I) = 0 := by
  -- ζ boxes (PROVEN), bridged to the (t:ℝ) form.
  obtain ⟨hRe14hi, hRe14lo⟩ := ForgeZeta14.zt14_zeta_re
  obtain ⟨hIm14hi, hIm14lo⟩ := ForgeZeta14.zt14_zeta_im
  obtain ⟨hRe15lo, hRe15hi⟩ := ForgeZeta15.zt15_zeta_re
  obtain ⟨hIm15lo, hIm15hi⟩ := ForgeZeta15.zt15_zeta_im
  rw [zbridge14] at hRe14hi hRe14lo hIm14hi hIm14lo
  rw [zbridge15] at hRe15lo hRe15hi hIm15lo hIm15hi
  -- S(14) < 0.  cos φ ∈ [-.23,-.19], Re ζ ∈ [.0141,.0304], sin φ ∈ [-.99,-.96], Im ζ ∈ [-.1114,-.0951].
  --   cos·Re ∈ [-.23·.0304, -.19·.0141] ⊂ [-.0070,-.0026] ; sin·Im ∈ [.96·.0951, .99·.1114] ⊂ [.0913,.1103]
  --   S = cos·Re − sin·Im ≤ -.0026 - .0913 < 0.
  set c14 := Real.cos (Λ14 - (14/2)*Real.log Real.pi)
  set s14 := Real.sin (Λ14 - (14/2)*Real.log Real.pi)
  set R14 := (riemannZeta ((1/2:ℂ)+(14:ℝ)*I)).re
  set I14 := (riemannZeta ((1/2:ℂ)+(14:ℝ)*I)).im
  -- cos·Re ≤ 0 (cos ≤ 0, Re ≥ 0); sin·Im ≥ (0.96)(0.0951) > 0.09 (both ≤ 0). Hence S < 0.
  have hcR14 : c14 * R14 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith [hcos14hi]) (by linarith [hRe14lo])
  have hsI14 : (88 : ℝ)/1000 ≤ s14 * I14 := by
    nlinarith [hsin14lo, hsin14hi, hIm14lo, hIm14hi]
  have hsign14 : c14 * R14 - s14 * I14 < 0 := by linarith [hcR14, hsI14]
  -- S(15) > 0.  cos φ ∈ [.18,.22], Re ζ ∈ [.138,.156]; sin φ ∈ [-.99,-.96], Im ζ ∈ [.696,.714].
  --   cos·Re ≥ .18·.138 = .0248 ; sin·Im ≤ -.96·.696 = -.668 ⇒ −sin·Im ≥ .668 ; S ≥ .0248+.668 > 0.
  set c15 := Real.cos (Λ15 - (15/2)*Real.log Real.pi)
  set s15 := Real.sin (Λ15 - (15/2)*Real.log Real.pi)
  set R15 := (riemannZeta ((1/2:ℂ)+(15:ℝ)*I)).re
  set I15 := (riemannZeta ((1/2:ℂ)+(15:ℝ)*I)).im
  have hcR15 : (6 : ℝ)/1000 ≤ c15 * R15 := by nlinarith [hcos15lo, hcos15hi, hRe15lo, hRe15hi]
  have hsI15 : s15 * I15 ≤ (-64 : ℝ)/100 := by nlinarith [hsin15lo, hsin15hi, hIm15lo, hIm15hi]
  have hsign15 : 0 < c15 * R15 - s15 * I15 := by linarith [hcR15, hsI15]
  -- Apply the proved magnitude-free bridge.
  exact first_zero_of_sign_quantities Λ14 hΛ14 Λ15 hΛ15 hsign14 hsign15

end ForgeFirstZero
