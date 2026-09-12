/-
RvMArchElemSeries — Arc B (archimedean Li growth), PR B1a: the ELEMENTARY series identity.

The archimedean Li data is `logDeriv (phi Γℝ) = logDeriv (Γℝ ∘ M)`, `M z = (1−z)⁻¹`.  Composing the
island's three stones — `logDeriv_phi` (chain rule through `M`), `logDeriv_Gammaℝ_eq` (reduction to
`ψ(s/2)`), and `digamma_series` (the Gauss–Weierstrass series) — and clearing every denominator
through the Möbius map turns the composition into an ELEMENTARY series of rational functions:

  `logDeriv (Γℝ∘M) z = −(γ + log π)/2 · M² − M + ∑'_j [ M²/(2(j+1)) − M/((2j+3) − (2j+2)z) ]`,

valid on `‖z‖ < 1/2`.  No polygamma values, no Faà di Bruno: every summand is rational in `z`, so
the `n`-th Taylor coefficient of each summand is explicit — `[z^n] M² = n+1`,
`[z^n] M·((2j+3)−(2j+2)z)⁻¹ = 1 − ((2j+2)/(2j+3))^{n+1}` (a telescoping geometric convolution) —
which is what makes the growth `taylorCoeff Γℝ n ~ (n/2)·log n` a harmonic-number statement
(PR B1b extracts the coefficients; PR B2/B3 prove the growth).  Identity numerically verified
exact to 40 digits with the truncation tail matching its analytic form (session gate).

conjecture1_proved = False: this is Γ-function calculus; nothing here approaches RH.
-/
import Mathlib
import RvMDigammaComplete
import RvMGammaR
import RvMPhiChain
import RvMMobius

open Complex

namespace RvMWeierstrass

/-- The `j`-th elementary archimedean summand: `M²/(2(j+1)) − M/((2j+3) − (2j+2)z)`,
    `M = (1−z)⁻¹`. -/
noncomputable def archSummand (j : ℕ) (z : ℂ) : ℂ :=
  1 / (2 * ((j : ℂ) + 1)) * ((1 - z)⁻¹) ^ 2
    - (1 - z)⁻¹ * ((2 * (j : ℂ) + 3) - (2 * (j : ℂ) + 2) * z)⁻¹

/-- **The elementary series identity for the archimedean log-derivative pullback**: on `‖z‖ < 1/2`,

  `logDeriv (Γℝ∘M) z = −(γ + log π)/2 · M² − M + ∑'_j archSummand j z`.

The whole polygamma content of the archimedean factor, as a single elementary series of rational
functions.  conjecture1_proved = False. -/
theorem logDeriv_phi_Gammaℝ_eq_elem {z : ℂ} (hz : ‖z‖ < 1 / 2) :
    logDeriv (fun w : ℂ => Complex.Gammaℝ ((1 - w)⁻¹)) z
      = -((Real.eulerMascheroniConstant : ℂ) + Complex.log (Real.pi : ℂ)) / 2
          * ((1 - z)⁻¹) ^ 2
        - (1 - z)⁻¹
        + ∑' j : ℕ, archSummand j z := by
  -- ball facts
  have hzre : z.re < 1 / 2 :=
    lt_of_le_of_lt ((le_abs_self _).trans (abs_re_le_norm z)) hz
  have hne : (1 : ℂ) - z ≠ 0 := by
    intro hc
    have h1 : z.re = 1 := by
      have h := sub_eq_zero.mp hc; rw [← h]; simp
    rw [h1] at hzre; norm_num at hzre
  have hz1 : z ≠ 1 := by
    intro h; exact hne (by rw [h]; ring)
  have hMre : 0 < ((1 - z)⁻¹).re := by
    rw [Complex.inv_re]
    apply div_pos
    · rw [Complex.sub_re, Complex.one_re]; linarith
    · exact Complex.normSq_pos.mpr hne
  -- pole avoidance for `ψ(s/2)` and the digamma series
  have hs2 : ∀ m : ℕ, ((1 - z)⁻¹) / 2 ≠ -(m : ℂ) := by
    intro m hm
    rw [div_eq_iff (two_ne_zero)] at hm
    have hre : ((1 - z)⁻¹).re = -(2 * (m : ℝ)) := by
      rw [hm]; simp [Complex.mul_re]; ring
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith [hMre]
  have hx : ∀ j : ℕ, ((1 - z)⁻¹) / 2 + (j : ℂ) ≠ 0 := by
    intro j hc
    have hm : ((1 - z)⁻¹) / 2 = -(j : ℂ) := by linear_combination hc
    exact hs2 j hm
  -- Γℝ differentiable at the Möbius image (pattern of RvMLiConnection)
  have hGdiff : DifferentiableAt ℂ Complex.Gammaℝ ((1 - z)⁻¹) := by
    rw [show Complex.Gammaℝ = fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) from by
      funext s; rw [Complex.Gammaℝ_def]]
    have hhalf : DifferentiableAt ℂ (fun s : ℂ => s / 2) ((1 - z)⁻¹) :=
      differentiableAt_id.div_const (2 : ℂ)
    have hcpow : DifferentiableAt ℂ (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) ((1 - z)⁻¹) :=
      (differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow
        (Or.inl (by exact_mod_cast Real.pi_ne_zero))
    have hgam : DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (s / 2)) ((1 - z)⁻¹) :=
      (Complex.differentiableAt_Gamma _ hs2).comp ((1 - z)⁻¹) hhalf
    exact hcpow.mul hgam
  -- the Möbius derivative
  have hderivM : deriv (fun w : ℂ => (1 - w)⁻¹) z = ((1 - z)⁻¹) ^ 2 := by
    have h1 := iteratedDeriv_mobius 1 hz1
    rw [iteratedDeriv_one] at h1
    rw [h1, Nat.factorial_one, inv_pow]
    norm_num
  -- expand through the three stones
  rw [logDeriv_phi hz1 hGdiff, hderivM, logDeriv_Gammaℝ_eq hs2, digamma_series hx]
  -- denominators of the per-term transform
  have hDne : ∀ j : ℕ, ((2 * (j : ℂ) + 3) - (2 * (j : ℂ) + 2) * z) ≠ 0 := by
    intro j hc
    have h1 : (2 * (j : ℂ) + 3) = (2 * (j : ℂ) + 2) * z := by linear_combination hc
    have h4 := congrArg norm h1
    rw [show (2 * (j : ℂ) + 3) = ((2 * j + 3 : ℕ) : ℂ) by push_cast; ring,
      Complex.norm_natCast, norm_mul,
      show (2 * (j : ℂ) + 2) = ((2 * j + 2 : ℕ) : ℂ) by push_cast; ring,
      Complex.norm_natCast] at h4
    have h6 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    push_cast at h4
    nlinarith [hz, norm_nonneg z]
  have hj1 : ∀ j : ℕ, ((j : ℂ) + 1) ≠ 0 := fun j => Nat.cast_add_one_ne_zero j
  have hxj1 : ∀ j : ℕ, ((1 - z)⁻¹) / 2 + ((j : ℂ) + 1) ≠ 0 := by
    intro j
    have h := hx (j + 1)
    push_cast at h
    exact h
  -- per-term identity: the digamma summand times `−M²/2` IS the elementary summand
  have hterm : ∀ j : ℕ,
      (1 / (((1 - z)⁻¹) / 2 + ((j : ℂ) + 1)) - 1 / ((j : ℂ) + 1))
          * (-(((1 - z)⁻¹) ^ 2) / 2)
        = archSummand j z := by
    intro j
    unfold archSummand
    have hD := hDne j
    have hxj := hxj1 j
    have hj := hj1 j
    field_simp
    ring
  -- fold the elementary tsum back into the digamma tsum
  rw [show (∑' j : ℕ, archSummand j z)
      = (∑' j : ℕ, (1 / (((1 - z)⁻¹) / 2 + ((j : ℂ) + 1)) - 1 / ((j : ℂ) + 1)))
          * (-(((1 - z)⁻¹) ^ 2) / 2) from by
    rw [← tsum_mul_right]
    exact tsum_congr fun j => (hterm j).symm]
  -- the pole term: `1/(M/2) = 2(1−z)`
  have hinv : 1 / (((1 - z)⁻¹) / 2) = 2 * (1 - z) := by
    field_simp
  rw [hinv]
  -- final algebra; `(1−z)·M² = M` is the one non-ring fact
  have hM2 : (1 - z) * ((1 - z)⁻¹) ^ 2 = (1 - z)⁻¹ := by
    field_simp
  linear_combination (-1 : ℂ) * hM2

end RvMWeierstrass
