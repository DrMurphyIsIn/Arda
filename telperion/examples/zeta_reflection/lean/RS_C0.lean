/-  RS_C0.lean -- lane RS, brick B3 (the Riemann-Siegel remainder), part 1: RIEMANN'S Psi.
    Mathlib-only (imports `RS_B2`).

    The main term of the Riemann-Siegel remainder is the Mordell integral with Gaussian e^{2 pi i w^2}
    (tau = 2):
        rsJ p = lineUp 0 (w |-> e^{2 pi i w^2} / (e^{i pi (p+w)} - e^{-i pi (p+w)})),   0 < p < 1.
    Its value is not elementary, but the combination that enters Z(t) is:

        2 Re(e^{-i pi/8} rsJ p) = cos(2 pi (p^2 - p - 1/16)) / cos(2 pi p) = Psi(p)   (Gabcke's C0).

    Proof (no residue theorem): write e^{i pi w^2} as a Gaussian Fourier integral along the (1-i)
    line, swap the two line integrals (Fubini), evaluate the inner one by the tau = 1 Mordell closed
    form (RS_Kernel), split the outer one into a tau = -1 Mordell integral (closed form by conjugation
    and one pole crossing) and a tau = -2 integral that is the conjugate of rsJ itself (symmetry
    rsJ(1-p) = rsJ(p)).  This gives rsJ + e^{i pi/4} conj(rsJ) = elementary, whose real part after the
    phase e^{-i pi/8} is Psi.

    conjecture1_proved = False.
-/
import RS_B2

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

namespace RSInt

/-! ## 1. Linearity for `lineDn`, translations -/

theorem lineDn_const_mul (k : ℂ) (F : ℂ → ℂ) (c : ℝ) :
    lineDn c (fun x => k * F x) = k * lineDn c F := by
  unfold lineDn; rw [← integral_const_mul]; congr 1; ext v; ring

theorem lineDn_sub {F G : ℂ → ℂ} {c : ℝ}
    (hF : Integrable (fun v : ℝ => F (c + v * (1 - I))))
    (hG : Integrable (fun v : ℝ => G (c + v * (1 - I)))) :
    lineDn c (fun x => F x - G x) = lineDn c F - lineDn c G := by
  unfold lineDn
  rw [← integral_sub (hF.mul_const _) (hG.mul_const _)]
  congr 1; ext v; ring

theorem lineUp_shift (p : ℝ) (H : ℂ → ℂ) : lineUp 0 (fun w => H (p + w)) = lineUp p H := by
  unfold lineUp; congr 1; ext v; congr 2; push_cast; ring

theorem lineDn_shift (p : ℝ) (H : ℂ → ℂ) : lineDn 0 (fun u => H (u + p)) = lineDn p H := by
  unfold lineDn; congr 1; ext v; congr 2; push_cast; ring

/-! ## 2. The Gaussian as a Fourier integral along the (1-i) line -/

theorem half_cpow_half_mul_sub : (1 / 2 : ℂ) ^ (1 / 2 : ℂ) * (1 - I) = cexp (-(↑π / 4 * I)) := by
  have h1 : (1 / 2 : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
    have : ((1 / 2 : ℝ) : ℂ) ^ ((1 / 2 : ℝ) : ℂ) = (((1 / 2 : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) :=
      (ofReal_cpow (by norm_num) _).symm
    push_cast at this
    rw [this]
    congr 1
    rw [← Real.sqrt_eq_rpow, Real.sqrt_div' 1 (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_one]
    field_simp
    rw [Real.sq_sqrt (by norm_num)]
  rw [h1, show -(↑π / 4 * I) = (-(↑π / 4 : ℂ)) * I by ring, Complex.exp_mul_I,
    ← ofReal_ofNat 4, ← ofReal_div, ← ofReal_neg, ← ofReal_cos, ← ofReal_sin, Real.cos_neg,
    Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four]
  push_cast; ring_nf

/-- `e^{i pi w^2} = e^{i pi/4} lineDn 0 (u |-> e^{-i pi u^2 + 2 pi i u w})` for every complex `w`. -/
theorem gauss_fourier_dn (w : ℂ) :
    cexp (↑π * I * w ^ 2) =
      cexp (↑π / 4 * I) * lineDn 0 (fun u => cexp (-(↑π * I * u ^ 2) + 2 * ↑π * I * u * w)) := by
  unfold lineDn
  have hpt : ∀ r : ℝ, cexp (-(↑π * I * (((0 : ℝ) : ℂ) + r * (1 - I)) ^ 2) +
      2 * ↑π * I * (((0 : ℝ) : ℂ) + r * (1 - I)) * w) * (1 - I) =
      cexp ((-2 * ↑π) * (r : ℂ) ^ 2 + (2 * ↑π * I * (1 - I) * w) * r + 0) * (1 - I) := by
    intro r
    congr 2
    push_cast
    linear_combination (2 * ↑π * (r : ℂ) ^ 2 - ↑π * I * (r : ℂ) ^ 2) * I_sq
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_mul_const,
    integral_cexp_quadratic (by simp [Real.pi_pos])]
  have hb : (↑π / -(-2 * ↑π) : ℂ) = 1 / 2 := by have := pi_ne_zero'; field_simp
  have hexp : (0 : ℂ) - (2 * ↑π * I * (1 - I) * w) ^ 2 / (4 * (-2 * ↑π)) = ↑π * I * w ^ 2 := by
    have hpi := pi_ne_zero'
    field_simp
    linear_combination (-4 * ↑π * I * w ^ 2 + 2 * ↑π * I ^ 2 * w ^ 2) * I_sq
  rw [hb, hexp]
  have h2 := half_cpow_half_mul_sub
  have h3 : cexp (↑π / 4 * I) * cexp (-(↑π / 4 * I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  linear_combination (-cexp (↑π * I * w ^ 2)) * h3 -
    (cexp (↑π / 4 * I) * cexp (↑π * I * w ^ 2)) * h2

/-! ## 3. The tau = 2 Mordell integral and its symmetry -/

/-- The tau = 2 Mordell integral: `rsJ p = lineUp 0 (w |-> e^{2 pi i w^2} / rsD (p + w))`. -/
def rsJ (p : ℝ) : ℂ := lineUp 0 (fun w => cexp (2 * ↑π * I * w ^ 2) / rsD (p + w))

theorem rsD_one_sub (z : ℂ) : rsD (1 - z) = rsD z := by
  unfold rsD
  rw [show ↑π * I * (1 - z) = ↑π * I + -(↑π * I * z) by ring,
    show -(↑π * I + -(↑π * I * z)) = -(↑π * I) + ↑π * I * z by ring, Complex.exp_add,
    Complex.exp_add, Complex.exp_pi_mul_I, exp_neg_piI]
  ring

theorem rsJ_symm (p : ℝ) : rsJ (1 - p) = rsJ p := by
  unfold rsJ lineUp
  rw [← integral_neg_eq_self]
  congr 1; ext v
  push_cast
  rw [show (1 : ℂ) - ↑p + (0 + -(v : ℂ) * (1 + I)) = 1 - (↑p + (0 + ↑v * (1 + I))) by ring,
    rsD_one_sub]
  ring_nf

/-- A point `p + v (1+i)` with `0 < p < 1` is never an integer. -/
theorem pt_ne_int {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (v : ℝ) (n : ℤ) :
    (p : ℂ) + ((0 : ℝ) + v * (1 + I)) ≠ n := by
  have := lineUp_pt_ne_int (c := p) (notInt_of_Ioo (n := 0) (by simpa using hp)
    (by simpa using hp1)) v n
  simpa using this

theorem continuous_J_integrand {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Continuous (fun v : ℝ => cexp (↑π * I * ((0 : ℝ) + v * (1 + I) : ℂ) ^ 2) /
      rsD (p + ((0 : ℝ) + v * (1 + I)))) := by
  rw [continuous_iff_continuousAt]
  intro v
  have hD : rsD (p + ((0 : ℝ) + v * (1 + I))) ≠ 0 := rsD_ne_zero_of_ne (pt_ne_int hp hp1 v)
  exact ((by fun_prop : Continuous (fun v : ℝ => cexp (↑π * I * ((0 : ℝ) + v * (1 + I) : ℂ) ^ 2))).continuousAt).div
    ((differentiable_rsD.continuous.comp (by fun_prop :
      Continuous (fun v : ℝ => (p : ℂ) + ((0 : ℝ) + v * (1 + I))))).continuousAt) hD

theorem norm_J_integrand_le {p : ℝ} (v : ℝ) (hv : 1 ≤ |v|) :
    ‖cexp (↑π * I * ((0 : ℝ) + v * (1 + I) : ℂ) ^ 2) / rsD (p + ((0 : ℝ) + v * (1 + I)))‖ ≤
      1 * Real.exp (-(2 * π) * v ^ 2 + 0 * |v|) := by
  have h1 : 1 ≤ |((p : ℂ) + ((0 : ℝ) + v * (1 + I))).im| := by simpa using hv
  rw [norm_div, norm_exp_piI_sq]
  have hD := one_le_norm_rsD h1
  have hre : -(2 * π * ((0 : ℝ) + v * (1 + I) : ℂ).re * ((0 : ℝ) + v * (1 + I) : ℂ).im) =
      -(2 * π) * v ^ 2 + 0 * |v| := by simp; ring
  rw [hre, one_mul]
  exact div_le_self (Real.exp_pos _).le hD

theorem integrable_J_integrand {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Integrable (fun v : ℝ => cexp (↑π * I * ((0 : ℝ) + v * (1 + I) : ℂ) ^ 2) /
      rsD (p + ((0 : ℝ) + v * (1 + I)))) :=
  integrable_of_continuous_of_tail (continuous_J_integrand hp hp1) (a := 2 * π) (b := 0) (C := 1)
    (R := 1) (by positivity) (fun v hv => norm_J_integrand_le v hv)

/-! ## 4. Fubini: rsJ as an iterated integral -/

theorem rsJ_fubini {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    rsJ p = cexp (↑π / 4 * I) * lineDn 0 (fun u => cexp (-(↑π * I * u ^ 2)) *
      lineUp 0 (fun w => cexp (↑π * I * w ^ 2) / rsD (p + w) * cexp (2 * ↑π * I * u * w))) := by
  set F : ℝ → ℝ → ℂ := fun v r =>
    cexp (↑π * I * ((0 : ℝ) + v * (1 + I) : ℂ) ^ 2) / rsD (p + ((0 : ℝ) + v * (1 + I))) * (1 + I) *
      (cexp (-(↑π * I * ((0 : ℝ) + r * (1 - I) : ℂ) ^ 2) +
        2 * ↑π * I * ((0 : ℝ) + r * (1 - I)) * ((0 : ℝ) + v * (1 + I))) * (1 - I)) with hF
  -- rsJ as the iterated integral ∫ v ∫ r
  have hL : rsJ p = cexp (↑π / 4 * I) * ∫ v : ℝ, ∫ r : ℝ, F v r := by
    unfold rsJ lineUp
    rw [← integral_const_mul]
    congr 1; ext v
    simp only [hF]
    rw [integral_const_mul, ← mul_assoc, ← mul_assoc]
    have hg := gauss_fourier_dn ((0 : ℝ) + v * (1 + I))
    unfold lineDn at hg
    rw [show cexp (2 * ↑π * I * ((0 : ℝ) + v * (1 + I) : ℂ) ^ 2) =
      cexp (↑π * I * ((0 : ℝ) + v * (1 + I) : ℂ) ^ 2) * cexp (↑π * I * ((0 : ℝ) + v * (1 + I) : ℂ) ^ 2)
        by rw [← Complex.exp_add]; ring_nf]
    conv_lhs => rw [show ∀ A B C : ℂ, A * B / C * (1 + I) = B / C * (1 + I) * A from
      fun A B C => by ring]
    rw [hg]; ring
  -- integrability of F on the product
  have hf₁ : Integrable (fun v : ℝ => ‖cexp (↑π * I * ((0 : ℝ) + v * (1 + I) : ℂ) ^ 2) /
      rsD (p + ((0 : ℝ) + v * (1 + I))) * (1 + I)‖) :=
    ((integrable_J_integrand hp hp1).mul_const _).norm
  have hf₂ : Integrable (fun r : ℝ => Real.exp (-(2 * π) * r ^ 2) * ‖(1 - I : ℂ)‖) :=
    (integrable_exp_neg_mul_sq (by positivity)).mul_const _
  have hprod := hf₁.mul_prod hf₂
  have hcont : Continuous (Function.uncurry F) := by
    show Continuous (fun q : ℝ × ℝ => F q.1 q.2)
    simp only [hF]
    have h1 : Continuous (fun q : ℝ × ℝ => cexp (↑π * I * ((0 : ℝ) + q.1 * (1 + I) : ℂ) ^ 2) /
        rsD (p + ((0 : ℝ) + q.1 * (1 + I)))) :=
      (continuous_J_integrand hp hp1).comp continuous_fst
    have h2 : Continuous (fun q : ℝ × ℝ => cexp (-(↑π * I * ((0 : ℝ) + q.2 * (1 - I) : ℂ) ^ 2) +
        2 * ↑π * I * ((0 : ℝ) + q.2 * (1 - I)) * ((0 : ℝ) + q.1 * (1 + I)))) := by fun_prop
    exact (h1.mul continuous_const).mul (h2.mul continuous_const)
  have hint : Integrable (Function.uncurry F) (volume.prod volume) := by
    refine hprod.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun q => le_of_eq ?_)
    simp only [Function.uncurry, hF]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp]
    congr 3
    simp [pow_two, mul_re, mul_im]
    ring
  rw [hL, integral_integral_swap hint]
  congr 1
  unfold lineDn lineUp
  congr 1; ext r
  simp only [hF]
  rw [← integral_const_mul, ← integral_mul_const]
  congr 1; ext v
  rw [show -(↑π * I * ((0 : ℝ) + r * (1 - I) : ℂ) ^ 2) +
      2 * ↑π * I * ((0 : ℝ) + r * (1 - I)) * ((0 : ℝ) + v * (1 + I)) =
      -(↑π * I * ((0 : ℝ) + r * (1 - I) : ℂ) ^ 2) +
      2 * ↑π * I * ((0 : ℝ) + r * (1 - I)) * ((0 : ℝ) + v * (1 + I)) from rfl, Complex.exp_add]
  ring

/-! ## 5. The inner integral: the tau = 1 Mordell closed form -/

theorem inner_mordell {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (u : ℂ) :
    lineUp 0 (fun w => cexp (↑π * I * w ^ 2) / rsD (p + w) * cexp (2 * ↑π * I * u * w)) *
      rsD (u - p) = cexp (↑π * I * p ^ 2 - 2 * ↑π * I * u * p) *
        (cexp (↑π * I * (u - p)) - cexp (-(↑π * I * (u - p) ^ 2))) := by
  set y : ℂ := 2 * ↑π * I * (p - u) with hy
  have h1 : (fun w => cexp (↑π * I * w ^ 2) / rsD (p + w) * cexp (2 * ↑π * I * u * w)) =
      fun w => (fun x => cexp (↑π * I * p ^ 2 - 2 * ↑π * I * u * p) *
        (rsG x * cexp (-(x * y)))) (p + w) := by
    ext w
    simp only [rsG, hy]
    rw [show ∀ A B C D : ℂ, A * (B / C * D) = A * B * D / C from fun A B C D => by ring,
      ← Complex.exp_add, ← Complex.exp_add, div_mul_eq_mul_div, ← Complex.exp_add]
    congr 2; ring
  rw [h1, lineUp_shift p (fun x => cexp (↑π * I * p ^ 2 - 2 * ↑π * I * u * p) *
    (rsG x * cexp (-(x * y)))), lineUp_const_mul]
  have hM := lineUp_mordell hp hp1 y
  have hE1 : cexp (-y / 2) = cexp (↑π * I * (u - p)) := by rw [hy]; congr 1; ring
  have hE2 : cexp (y / 2) = cexp (-(↑π * I * (u - p))) := by rw [hy]; congr 1; ring
  have hG : cexp (I * y ^ 2 / (4 * ↑π)) = cexp (-(↑π * I * (u - p) ^ 2)) := by
    rw [hy]; congr 1
    have hpi := pi_ne_zero'
    field_simp
    linear_combination (4 * ((p : ℂ) - u) ^ 2) * I_sq
  rw [hE1, hE2, hG] at hM
  unfold rsD
  rw [mul_assoc, hM]

/-! ## 6. The outer integral splits into T1 - T2 -/

theorem dnLine_neg_p_ne_int {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (r : ℝ) (n : ℤ) :
    ((0 : ℝ) : ℂ) + r * (1 - I) - p ≠ n := by
  have hcl : ∀ m : ℤ, (m : ℝ) ≠ -p := notInt_of_Ioo (n := -1) (by push_cast; linarith)
    (by push_cast; linarith)
  have := lineDn_pt_ne_int hcl r n
  intro h; apply this; rw [← h]; push_cast; ring

theorem integrable_T1 (p : ℝ) (c : ℝ) (hcl : ∀ m : ℤ, (m : ℝ) ≠ c) :
    Integrable (fun v : ℝ => rsH ((c : ℂ) + v * (1 - I)) *
      cexp (↑π * I * (1 - 4 * p) * ((c : ℂ) + v * (1 - I)))) := by
  have hcont : ContinuousOn (fun x => rsH x * cexp (↑π * I * (1 - 4 * p) * x))
      {x : ℂ | x.re + x.im ∈ Icc c c} := by
    intro x hx
    have hxc : x.re + x.im = c := le_antisymm hx.2 hx.1
    have hD : rsD x ≠ 0 := by
      refine rsD_ne_zero_of_ne fun n hn => hcl n ?_
      rw [hn] at hxc; simpa using hxc
    exact ((differentiableAt_rsH hD).continuousAt.mul (by fun_prop)).continuousWithinAt
  exact integrable_lineDn (c₁ := c) (c₂ := c) ⟨le_rfl, le_rfl⟩ hcont (a := 2 * π) (by positivity)
    (fun x hx h1 => norm_rsH_mul_le (ψ := fun x => cexp (↑π * I * (1 - 4 * p) * x)) hx h1
      (A := 1) (B := ‖(↑π * I * (1 - 4 * p) : ℂ)‖) (by
        rw [one_mul]
        refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
        rw [norm_mul]))

theorem integrable_T2 {p : ℝ} (c : ℝ) (hcl : ∀ m : ℤ, (m : ℝ) ≠ c) (hcp : c = -p) :
    Integrable (fun v : ℝ => cexp (-(2 * ↑π * I * ((c : ℂ) + v * (1 - I)) ^ 2) -
      4 * ↑π * I * p * ((c : ℂ) + v * (1 - I))) / rsD ((c : ℂ) + v * (1 - I))) := by
  have hcont : ContinuousOn (fun x => cexp (-(2 * ↑π * I * x ^ 2) - 4 * ↑π * I * p * x) / rsD x)
      {x : ℂ | x.re + x.im ∈ Icc c c} := by
    intro x hx
    have hxc : x.re + x.im = c := le_antisymm hx.2 hx.1
    have hD : rsD x ≠ 0 := by
      refine rsD_ne_zero_of_ne fun n hn => hcl n ?_
      rw [hn] at hxc; simpa using hxc
    exact ((by fun_prop : Continuous (fun x : ℂ => cexp (-(2 * ↑π * I * x ^ 2) -
      4 * ↑π * I * p * x))).continuousAt.div (differentiable_rsD x).continuousAt hD).continuousWithinAt
  refine integrable_lineDn (c₁ := c) (c₂ := c) ⟨le_rfl, le_rfl⟩ hcont (a := 4 * π) (b := 0) (C := 1)
    (by positivity) (fun x hx h1 => ?_)
  have hxc : x.re = -p - x.im := by have := le_antisymm hx.2 hx.1; rw [hcp] at this; linarith
  rw [norm_div, Complex.norm_exp]
  have hre : (-(2 * (π : ℂ) * I * x ^ 2) - 4 * (π : ℂ) * I * p * x).re =
      -(4 * π) * x.im ^ 2 + 0 * |x.im| := by
    simp [pow_two, mul_re, mul_im]; rw [hxc]; ring
  rw [hre, one_mul]
  exact div_le_self (Real.exp_pos _).le (one_le_norm_rsD h1)

/-- **The outer split.**  `rsJ p = e^{i pi/4} e^{-2 pi i p^2} (T1 - T2)`, with
    `T1 = lineDn (-p) (rsH e^{i pi (1-4p) y})` (tau = -1) and
    `T2 = lineDn (-p) (e^{-2 pi i y^2 - 4 pi i p y} / rsD y)` (tau = -2). -/
theorem rsJ_outer {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    rsJ p = cexp (↑π / 4 * I) * (cexp (-(2 * ↑π * I * p ^ 2)) *
      (lineDn (-p) (fun y => rsH y * cexp (↑π * I * (1 - 4 * p) * y)) -
        lineDn (-p) (fun y => cexp (-(2 * ↑π * I * y ^ 2) - 4 * ↑π * I * p * y) / rsD y))) := by
  have hcl : ∀ m : ℤ, (m : ℝ) ≠ -p := notInt_of_Ioo (n := -1) (by push_cast; linarith)
    (by push_cast; linarith)
  set Q : ℂ → ℂ := fun y => cexp (-(2 * ↑π * I * p ^ 2)) *
    (rsH y * cexp (↑π * I * (1 - 4 * p) * y) -
      cexp (-(2 * ↑π * I * y ^ 2) - 4 * ↑π * I * p * y) / rsD y) with hQ
  rw [rsJ_fubini hp hp1]
  congr 1
  have hstep : lineDn 0 (fun u => cexp (-(↑π * I * u ^ 2)) * lineUp 0 (fun w =>
      cexp (↑π * I * w ^ 2) / rsD (p + w) * cexp (2 * ↑π * I * u * w))) =
      lineDn 0 (fun u => Q (u + ((-p : ℝ) : ℂ))) := by
    refine lineDn_congr fun r => ?_
    set u : ℂ := ((0 : ℝ) : ℂ) + r * (1 - I) with hu
    have hD : rsD (u - p) ≠ 0 := rsD_ne_zero_of_ne (dnLine_neg_p_ne_int hp hp1 r)
    have hin := inner_mordell hp hp1 u
    have hinner : lineUp 0 (fun w => cexp (↑π * I * w ^ 2) / rsD (p + w) *
        cexp (2 * ↑π * I * u * w)) = cexp (↑π * I * p ^ 2 - 2 * ↑π * I * u * p) *
          (cexp (↑π * I * (u - p)) - cexp (-(↑π * I * (u - p) ^ 2))) / rsD (u - p) := by
      rw [eq_div_iff hD]; exact hin
    rw [hinner]
    simp only [hQ, rsH]
    rw [show u + ((-p : ℝ) : ℂ) = u - p by push_cast; ring]
    have e1 : cexp (-(↑π * I * u ^ 2)) * cexp (↑π * I * p ^ 2 - 2 * ↑π * I * u * p) *
        cexp (↑π * I * (u - p)) = cexp (-(2 * ↑π * I * p ^ 2)) * cexp (-(↑π * I * (u - p) ^ 2)) *
          cexp (↑π * I * (1 - 4 * p) * (u - p)) := by
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
      congr 1; ring
    have e2 : cexp (-(↑π * I * u ^ 2)) * cexp (↑π * I * p ^ 2 - 2 * ↑π * I * u * p) *
        cexp (-(↑π * I * (u - p) ^ 2)) = cexp (-(2 * ↑π * I * p ^ 2)) *
          cexp (-(2 * ↑π * I * (u - p) ^ 2) - 4 * ↑π * I * p * (u - p)) := by
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
      congr 1; ring
    calc cexp (-(↑π * I * u ^ 2)) * (cexp (↑π * I * p ^ 2 - 2 * ↑π * I * u * p) *
          (cexp (↑π * I * (u - p)) - cexp (-(↑π * I * (u - p) ^ 2))) / rsD (u - p))
        = (cexp (-(↑π * I * u ^ 2)) * cexp (↑π * I * p ^ 2 - 2 * ↑π * I * u * p) *
            cexp (↑π * I * (u - p)) - cexp (-(↑π * I * u ^ 2)) *
            cexp (↑π * I * p ^ 2 - 2 * ↑π * I * u * p) * cexp (-(↑π * I * (u - p) ^ 2))) /
              rsD (u - p) := by ring
      _ = (cexp (-(2 * ↑π * I * p ^ 2)) * cexp (-(↑π * I * (u - p) ^ 2)) *
            cexp (↑π * I * (1 - 4 * p) * (u - p)) - cexp (-(2 * ↑π * I * p ^ 2)) *
            cexp (-(2 * ↑π * I * (u - p) ^ 2) - 4 * ↑π * I * p * (u - p))) / rsD (u - p) := by
          rw [e1, e2]
      _ = _ := by ring
  rw [hstep, lineDn_shift, hQ, lineDn_const_mul, lineDn_sub (integrable_T1 p (-p) hcl)
    (integrable_T2 (-p) hcl rfl)]

/-! ## 7. T2 is the conjugate of rsJ; T1 by one pole crossing and the Mordell formula -/

theorem T2_eq {p : ℝ} :
    lineDn (-p) (fun y => cexp (-(2 * ↑π * I * y ^ 2) - 4 * ↑π * I * p * y) / rsD y) =
      cexp (2 * ↑π * I * p ^ 2) * conj (rsJ p) := by
  rw [← lineDn_shift (-p)]
  have h1 : (fun u => (fun y => cexp (-(2 * ↑π * I * y ^ 2) - 4 * ↑π * I * p * y) / rsD y)
      (u + ((-p : ℝ) : ℂ))) =
      fun u => cexp (2 * ↑π * I * p ^ 2) * (cexp (-(2 * ↑π * I * u ^ 2)) / rsD (u - p)) := by
    ext u
    simp only
    rw [show u + ((-p : ℝ) : ℂ) = u - p by push_cast; ring, mul_div_assoc', ← Complex.exp_add]
    congr 2; ring
  rw [h1, lineDn_const_mul, lineDn_eq_conj]
  congr 2
  rw [← rsJ_symm p]
  unfold rsJ
  congr 1; ext x
  have hc : conj x - (p : ℂ) = conj (x - p) := by simp [map_sub]
  rw [map_div₀, ← Complex.exp_conj, hc, conj_rsD_conj,
    show ((1 - p : ℝ) : ℂ) + x = (x - p) + 1 by push_cast; ring, rsD_add_one]
  congr 1
  simp only [map_neg, map_mul, map_pow, Complex.conj_ofReal, Complex.conj_I, Complex.conj_conj,
    map_ofNat]
  congr 1; ring

theorem norm_exp_lin_le (ζ x : ℂ) : ‖cexp (ζ * x)‖ ≤ 1 * Real.exp (‖ζ‖ * ‖x‖) := by
  rw [one_mul]
  exact (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr (by rw [norm_mul]))

theorem T1_eq {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    lineDn (-p) (fun y => rsH y * cexp (↑π * I * (1 - 4 * p) * y)) =
      1 - conj (rsK (1 - p) (↑π * I * (1 - 4 * p))) := by
  have hcross := lineDn_cross (ψ := fun y => cexp (↑π * I * (1 - 4 * p) * y)) (n := 0)
    (c₁ := -p) (c₂ := 1 - p) (by push_cast; linarith) (by push_cast; linarith)
    (by push_cast; linarith) (by push_cast; linarith) (fun x _ => by fun_prop)
    (A := 1) (B := ‖(↑π * I * (1 - 4 * (p : ℂ)))‖)
    (fun x _ => by
      show ‖cexp (↑π * I * (1 - 4 * (p : ℂ)) * x)‖ ≤
        1 * Real.exp (‖(↑π * I * (1 - 4 * (p : ℂ)))‖ * ‖x‖)
      exact norm_exp_lin_le _ x)
  have h2 : lineDn (1 - p) (fun y => rsH y * cexp (↑π * I * (1 - 4 * p) * y)) =
      -conj (rsK (1 - p) (↑π * I * (1 - 4 * p))) := by
    rw [lineDn_rsH_eq]
    congr 2
    unfold rsK
    congr 1; ext x
    congr 1
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_sub, map_one, map_ofNat, Complex.conj_ofReal, Complex.conj_I,
      Complex.conj_conj]
    ring
  rw [h2] at hcross
  simp only [Int.cast_zero, mul_zero, Complex.exp_zero] at hcross
  linear_combination -hcross

/-! ## 8. Riemann's Psi -/

/-- **The C0 identity (Riemann's Psi).**  For `0 < p < 1` with `cos(2 pi p) ≠ 0`:
        2 Re(e^{-i pi/8} rsJ p) = cos(2 pi (p^2 - p - 1/16)) / cos(2 pi p). -/
theorem rsJ_C0 {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (hcos : Real.cos (2 * π * p) ≠ 0) :
    2 * (cexp (-(↑π / 8 * I)) * rsJ p).re =
      Real.cos (2 * π * (p ^ 2 - p - 1 / 16)) / Real.cos (2 * π * p) := by
  -- the basic units
  set a : ℂ := cexp (↑π / 8 * I) with ha
  set b : ℂ := cexp (↑π * I * p) with hb
  set c : ℂ := cexp (↑π * I * p ^ 2) with hc
  have ha0 : a ≠ 0 := Complex.exp_ne_zero _
  have hb0 : b ≠ 0 := Complex.exp_ne_zero _
  have hc0 : c ≠ 0 := Complex.exp_ne_zero _
  have conj_exp_I : ∀ x : ℝ, conj (cexp (↑x * I)) = (cexp (↑x * I))⁻¹ := by
    intro x
    rw [← Complex.exp_conj, ← Complex.exp_neg]
    congr 1; simp [map_mul]
  have hca : conj a = a⁻¹ := by
    have := conj_exp_I (π / 8); push_cast at this; exact this
  have hcb : conj b = b⁻¹ := by
    have := conj_exp_I (π * p); push_cast at this
    rw [hb, show ↑π * I * (p : ℂ) = ↑π * ↑p * I by ring]; exact this
  have hcc : conj c = c⁻¹ := by
    have := conj_exp_I (π * p ^ 2); push_cast at this
    rw [hc, show ↑π * I * (p : ℂ) ^ 2 = ↑π * ↑p ^ 2 * I by ring]; exact this
  have ha8 : a ^ 8 = -1 := by
    rw [ha, ← Complex.exp_nat_mul, show ((8 : ℕ) : ℂ) * (↑π / 8 * I) = ↑π * I by push_cast; ring,
      Complex.exp_pi_mul_I]
  -- the Mordell data at c = 1 - p, zeta = pi i (1 - 4p)
  set ζ : ℂ := ↑π * I * (1 - 4 * p) with hζ
  set K := rsK (1 - p) ζ with hK
  have hM : K * (cexp (-ζ / 2) - cexp (ζ / 2)) = cexp (-ζ / 2) - cexp (I * ζ ^ 2 / (4 * ↑π)) :=
    lineUp_mordell (by linarith) (by linarith) ζ
  have hE1 : cexp (-ζ / 2) = a⁻¹ ^ 4 * b ^ 2 := by
    rw [ha, hb, ← Complex.exp_neg, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add,
      hζ]
    congr 1; push_cast; ring
  have hE2 : cexp (ζ / 2) = a ^ 4 * b⁻¹ ^ 2 := by
    rw [ha, hb, ← Complex.exp_neg, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add,
      hζ]
    congr 1; push_cast; ring
  have hG : cexp (I * ζ ^ 2 / (4 * ↑π)) = a⁻¹ ^ 2 * b ^ 2 * c⁻¹ ^ 4 := by
    rw [ha, hb, hc, ← Complex.exp_neg, ← Complex.exp_neg, ← Complex.exp_nat_mul,
      ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add, hζ]
    congr 1
    have hpi := pi_ne_zero'
    field_simp
    push_cast
    linear_combination (8 - 64 * (p : ℂ) + 128 * (p : ℂ) ^ 2) * I_sq
  rw [hE1, hE2, hG] at hM
  -- conjugate of the Mordell identity
  have hMc := congrArg conj hM
  simp only [map_mul, map_sub, map_pow, map_inv₀, hca, hcb, hcc, inv_inv] at hMc
  -- the outer relation
  have hout := rsJ_outer hp hp1
  rw [T1_eq hp hp1, T2_eq] at hout
  have hcinv2 : cexp (-(2 * ↑π * I * p ^ 2)) = c⁻¹ ^ 2 := by
    rw [hc, ← Complex.exp_neg, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hc2 : cexp (2 * ↑π * I * p ^ 2) = c ^ 2 := by
    rw [hc, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have ha2 : cexp (↑π / 4 * I) = a ^ 2 := by
    rw [ha, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [hcinv2, hc2, ha2, ← hK] at hout
  -- X + conj X
  set X := cexp (-(↑π / 8 * I)) * rsJ p with hX
  have hXa : cexp (-(↑π / 8 * I)) = a⁻¹ := by rw [ha, Complex.exp_neg]
  have haa : a⁻¹ * a = 1 := inv_mul_cancel₀ ha0
  have hcc2 : c⁻¹ ^ 2 * c ^ 2 = 1 := by rw [← mul_pow, inv_mul_cancel₀ hc0, one_pow]
  have hsum : X + conj X = a * c⁻¹ ^ 2 * (1 - conj K) := by
    have hconjX : conj X = a * conj (rsJ p) := by rw [hX, map_mul, hXa, map_inv₀, hca, inv_inv]
    rw [hconjX, hX, hXa]
    linear_combination a⁻¹ * hout + (a * c⁻¹ ^ 2 * (1 - conj K) -
      a * conj (rsJ p) * c⁻¹ ^ 2 * c ^ 2) * haa - (a * conj (rsJ p)) * hcc2
  -- the right-hand side as a function of a, b, c
  have hcosx : ((Real.cos (2 * π * (p ^ 2 - p - 1 / 16)) : ℝ) : ℂ) =
      (c ^ 2 * b⁻¹ ^ 2 * a⁻¹ + c⁻¹ ^ 2 * b ^ 2 * a) / 2 := by
    rw [Complex.ofReal_cos, show Complex.cos _ = (2 * Complex.cos _) / 2 by ring, Complex.two_cos,
      ha, hb, hc]
    rw [← Complex.exp_neg, ← Complex.exp_neg, ← Complex.exp_neg, ← Complex.exp_nat_mul,
      ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add,
      ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 2 <;> push_cast <;> ring
  have hcosy : ((Real.cos (2 * π * p) : ℝ) : ℂ) = (b ^ 2 + b⁻¹ ^ 2) / 2 := by
    rw [Complex.ofReal_cos, show Complex.cos _ = (2 * Complex.cos _) / 2 by ring, Complex.two_cos,
      hb, ← Complex.exp_neg, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    congr 2 <;> push_cast <;> ring
  have hden : b ^ 2 + b⁻¹ ^ 2 ≠ 0 := by
    intro h; apply hcos
    have : ((Real.cos (2 * π * p) : ℝ) : ℂ) = 0 := by rw [hcosy, h, zero_div]
    exact_mod_cast this
  have hD : a ^ 4 * b⁻¹ ^ 2 - a⁻¹ ^ 4 * b ^ 2 ≠ 0 := by
    intro h; apply hden
    have hab : (a ^ 4 * b⁻¹ ^ 2 - a⁻¹ ^ 4 * b ^ 2) * (a ^ 4 * b ^ 2) = a ^ 8 - b ^ 4 := by
      field_simp
    rw [h, zero_mul, ha8] at hab
    have hb2 : b ^ 2 + b⁻¹ ^ 2 = (b ^ 4 + 1) / b ^ 2 := by field_simp
    rw [hb2, show b ^ 4 + 1 = 0 by linear_combination hab, zero_div]
  -- solve for conj K
  have hKc : conj K = (a ^ 4 * b⁻¹ ^ 2 - a ^ 2 * b⁻¹ ^ 2 * c ^ 4) / (a ^ 4 * b⁻¹ ^ 2 - a⁻¹ ^ 4 * b ^ 2) := by
    rw [eq_div_iff hD]; linear_combination hMc
  -- conclude
  have h1b : 1 + b ^ 4 ≠ 0 := by
    intro h; apply hden
    have hb2 : b ^ 2 + b⁻¹ ^ 2 = (b ^ 4 + 1) / b ^ 2 := by field_simp
    rw [hb2, show b ^ 4 + 1 = 0 by linear_combination h, zero_div]
  have h8b : a ^ 8 - b ^ 4 ≠ 0 := by
    rw [ha8]; intro h; apply h1b; linear_combination -h
  have hfinal : X + conj X =
      ((Real.cos (2 * π * (p ^ 2 - p - 1 / 16)) / Real.cos (2 * π * p) : ℝ) : ℂ) := by
    rw [hsum, hKc, Complex.ofReal_div, hcosx, hcosy]
    have hu : (1 + b ^ 4)⁻¹ * (1 + b ^ 4) = 1 := inv_mul_cancel₀ h1b
    field_simp
    linear_combination (c ^ 4 - c ^ 4 * (1 + b ^ 4)⁻¹ - a ^ 2 * b ^ 4 * (1 + b ^ 4)⁻¹) * ha8 +
      (a ^ 2 * b ^ 4 + c ^ 4) * hu
  rw [Complex.add_conj] at hfinal
  exact_mod_cast hfinal

end RSInt
