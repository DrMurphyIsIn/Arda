/-
  ArchS8_ProlateData -- stage S8 of the archimedean conceptual blueprint (2026-10-11), part 2:
  the abstract prolate interface and CC's ε (84), Prop 5.3 (97)/(99), Lemma 5.4, Rem 5.6
  (arXiv:2006.13771, sections 4-5), in the additive variable t = log ρ.

  THE INTERFACE (`ProlateData`).  Only what sections 4-5 actually use:
    lam n            λ(n), with λ(n)² < 1                 (S6: eigenvalues of P₁ F P₁ on even L²)
    phi n            ξ_n^an, the analytic continuation of the normalised even prolate ξ_n
                     (= ξ_n on [0,1], = λ(n)⁻¹ F ξ_n on [1,∞)), required C¹ on ℝ
    T > 0            the additive range: everything below holds for |t| < T, i.e. ρ ∈ (e^{-T}, e^T)
    M n, N n         sup bounds for |ξ_n^an| and |(ξ_n^an)'| on [e^{-T}, 1] and on [1, e^T]
    summable_wMN     Σ λ(n)²/(1-λ(n)²) · M n · N n < ∞
  No orthonormality or eigen-relation is needed for the statements of section 5; they enter only
  through S7 (Thm 4.7), which must identify `eps` below with CC's ε.  See ARCH_S8_NOTES.md.

  DEFINITIONS (t = log ρ):
    w n      = λ(n)²/(1-λ(n)²)
    kn n t   = ρ^{1/2} ∫_{ρ⁻¹}^1 ξ_n^an(x) ξ_n^an(ρx) dx               (kM, ArchS8_Volterra)
    eps t    = Σ w n · kn n t       -- CC (84) via ζ_n = λ/√(1-λ²) ξ_n^an on [1,∞) (cc84_term)
    eps1, eps2 = the termwise first and second derivatives
    Qeps t   = -eps2 t + eps t / 4  -- CC's (Qε)(ρ)
    Cn n t   = CC (99), the explicit C_n(ρ)

  THEOREMS.
    hasDerivAt_eps, hasDerivAt_eps1 : eps' = eps1, eps1' = eps2 on (-T, T)  (termwise, uniform bounds)
    prop53       : Qeps t = Σ w n · Cn n t on (-T, T)                       (CC Prop 5.3, (97)+(99))
    lemma54      : eps'(0) = Σ λ²/(1-λ²) · ξ_n(1)²                           (CC Lemma 5.4)
    epsMul_hasDerivWithinAt : the same as a right derivative at ρ = 1 of ε(ρ) = eps |log ρ|
    Qeps_zero    : Qeps 0 = 0                                               (CC Rem 5.6: Tr K_I = 0)
    eps_zero     : eps 0 = 0
  No sorry, no axiom.  conjecture1_proved = False.  Nothing here is RH progress.
-/
import ArchS8_Volterra

open MeasureTheory Set Filter Topology
open scoped Interval

noncomputable section

namespace ArchS8

/-- The data CC sections 4-5 use about the even prolate functions (see the module header and
ARCH_S8_NOTES.md for what S6/S9 must supply). -/
structure ProlateData where
  /-- λ(n), the eigenvalues of `P₁ F P₁` on even functions (CC (68)-(69)). -/
  lam : ℕ → ℝ
  lam_sq_lt_one : ∀ n, lam n ^ 2 < 1
  /-- ξ_n^an: the normalised even prolate on [0,1], continued analytically past 1. -/
  phi : ℕ → ℝ → ℝ
  phi_contDiff : ∀ n, ContDiff ℝ 1 (phi n)
  /-- The additive range: statements hold for |log ρ| < T. -/
  T : ℝ
  T_pos : 0 < T
  M : ℕ → ℝ
  N : ℕ → ℝ
  bound_inner : ∀ n, ∀ x ∈ Icc (Real.exp (-T)) 1, |phi n x| ≤ M n ∧ |deriv (phi n) x| ≤ M n
  bound_outer : ∀ n, ∀ x ∈ Icc 1 (Real.exp T), |phi n x| ≤ N n ∧ |deriv (phi n) x| ≤ N n
  summable_wMN : Summable fun n => lam n ^ 2 / (1 - lam n ^ 2) * (M n * N n)

/-- Bounds `α` on `[0, T]` and `β` on `[-T, 0]`. -/
def Bdd (T α β : ℝ) (X : ℝ → ℝ) : Prop :=
  (∀ s ∈ Icc 0 T, |X s| ≤ α) ∧ (∀ s ∈ Icc (-T) 0, |X s| ≤ β)

/-- In `volt X (· ∘ neg)` one factor always sits at a nonnegative, the other at a nonpositive
argument, so the product is bounded by `α β`. -/
theorem prod_bound_gen {T α β : ℝ} {X Z : ℝ → ℝ} (hX : Bdd T α β X) (hZ : Bdd T α β Z)
    {t s : ℝ} (ht : t ∈ Ioo (-T) T) (hs : s ∈ uIcc 0 t) : |X s * Z (s - t)| ≤ α * β := by
  obtain ⟨ht1, ht2⟩ := ht
  rw [abs_mul]
  rcases mem_uIcc.1 hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hx := hX.1 s ⟨h1, by linarith⟩
    have hz := hZ.2 (s - t) ⟨by linarith, by linarith⟩
    exact mul_le_mul hx hz (abs_nonneg _) ((abs_nonneg _).trans hx)
  · have hx := hX.2 s ⟨by linarith, h2⟩
    have hz := hZ.1 (s - t) ⟨by linarith, by linarith⟩
    rw [mul_comm α β]
    exact mul_le_mul hx hz (abs_nonneg _) ((abs_nonneg _).trans hx)

/-- Generic bounds for the additive images, from bounds on ξ and ξ' at `e^{-s}`. -/
theorem aOf_bounds_gen {φ : ℝ → ℝ} {s c d K : ℝ}
    (hx : |φ (Real.exp (-s))| ≤ K ∧ |deriv φ (Real.exp (-s))| ≤ K)
    (hc : Real.exp (-s / 2) ≤ c) (hd : Real.exp (-s) ≤ d) :
    |aOf φ s| ≤ c * K ∧ |aOf' φ s| ≤ c * (K / 2 + d * K) := by
  have hc0 : 0 ≤ c := (Real.exp_pos _).le.trans hc
  constructor
  · unfold aOf
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul hc hx.1 (abs_nonneg _) hc0
  · unfold aOf'
    rw [abs_neg, abs_mul, abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul hc ?_ (abs_nonneg _) hc0
    calc |φ (Real.exp (-s)) / 2 + Real.exp (-s) * deriv φ (Real.exp (-s))|
        ≤ |φ (Real.exp (-s)) / 2| + |Real.exp (-s) * deriv φ (Real.exp (-s))| := abs_add_le _ _
      _ = |φ (Real.exp (-s))| / 2 + Real.exp (-s) * |deriv φ (Real.exp (-s))| := by
          rw [abs_div, abs_mul, abs_of_pos (Real.exp_pos _), abs_two]
      _ ≤ K / 2 + d * K := add_le_add (by linarith [hx.1])
          (mul_le_mul hd hx.2 (abs_nonneg _) ((Real.exp_pos _).le.trans hd))

theorem bOf_eq_aOf (φ : ℝ → ℝ) (u : ℝ) : bOf φ u = aOf φ (-u) := by
  unfold aOf bOf; simp only [neg_neg]

theorem bOf'_eq_aOf' (φ : ℝ → ℝ) (u : ℝ) : bOf' φ u = -aOf' φ (-u) := by
  unfold aOf' bOf'; simp only [neg_neg]

namespace ProlateData

variable (D : ProlateData)

/-- The weights λ(n)²/(1 - λ(n)²) of (97)-(99) and Lemma 5.4. -/
def w (n : ℕ) : ℝ := D.lam n ^ 2 / (1 - D.lam n ^ 2)

theorem w_nonneg (n : ℕ) : 0 ≤ D.w n :=
  div_nonneg (sq_nonneg _) (by linarith [D.lam_sq_lt_one n])

/-- The n-th matrix coefficient `ρ^{1/2} ∫_{ρ⁻¹}^1 ξ_n^an(x) ξ_n^an(ρx) dx` at `ρ = e^t`. -/
def kn (n : ℕ) (t : ℝ) : ℝ := kM (D.phi n) (D.phi n) t
/-- Its first derivative in `t` (`ρ∂_ρ`). -/
def kn1 (n : ℕ) (t : ℝ) : ℝ := kM1 (D.phi n) (D.phi n) t
/-- Its second derivative in `t` (`(ρ∂_ρ)²`). -/
def kn2 (n : ℕ) (t : ℝ) : ℝ := kM2 (D.phi n) (D.phi n) t

/-- **CC (99)**: `C_n(ρ)` at `ρ = e^t`, with `ξ_n^an = phi n`:
`ρ^{1/2}∫_{ρ⁻¹}^1 x ξ'(x) ρx ξ'(ρx) dx + ρ^{-3/2} ξ'(ρ⁻¹) ξ(1) - ρ^{3/2} ξ(1) ξ'(ρ)`. -/
def Cn (n : ℕ) (t : ℝ) : ℝ :=
  Real.exp (t / 2) * (∫ x in (Real.exp (-t))..1,
      (x * deriv (D.phi n) x) * (Real.exp t * x * deriv (D.phi n) (Real.exp t * x)))
    + Real.exp (-(3 / 2) * t) * deriv (D.phi n) (Real.exp (-t)) * D.phi n 1
    - Real.exp ((3 / 2) * t) * D.phi n 1 * deriv (D.phi n) (Real.exp t)

/-- CC's ε (84) at `ρ = e^t`: `Σ λ²/(1-λ²) ρ^{1/2} ∫_{ρ⁻¹}^1 ξ_n^an(x) ξ_n^an(ρx) dx`. -/
def eps (t : ℝ) : ℝ := ∑' n, D.w n * D.kn n t
/-- `ρ∂_ρ ε`. -/
def eps1 (t : ℝ) : ℝ := ∑' n, D.w n * D.kn1 n t
/-- `(ρ∂_ρ)² ε`. -/
def eps2 (t : ℝ) : ℝ := ∑' n, D.w n * D.kn2 n t
/-- CC's `(Qε)(ρ)`, `Q = -(ρ∂_ρ)² + 1/4`, at `ρ = e^t`. -/
def Qeps (t : ℝ) : ℝ := -(D.eps2 t) + D.eps t / 4

/-- CC's ε as a function of `ρ > 0`, extended by `ε(ρ⁻¹) = ε(ρ)`. -/
def epsMul (ρ : ℝ) : ℝ := D.eps |Real.log ρ|

/-! ### Termwise facts -/

theorem cont_phi (n : ℕ) : Continuous (D.phi n) := (D.phi_contDiff n).continuous
theorem cont_dphi (n : ℕ) : Continuous (deriv (D.phi n)) :=
  (D.phi_contDiff n).continuous_deriv le_rfl
theorem diff_phi (n : ℕ) : Differentiable ℝ (D.phi n) :=
  (D.phi_contDiff n).differentiable (by norm_num)

theorem hasDerivAt_kn (n : ℕ) (t : ℝ) : HasDerivAt (D.kn n) (D.kn1 n t) t :=
  (lemma52 (D.phi_contDiff n) (D.phi_contDiff n) t).1

theorem hasDerivAt_kn1 (n : ℕ) (t : ℝ) : HasDerivAt (D.kn1 n) (D.kn2 n t) t :=
  (lemma52 (D.phi_contDiff n) (D.phi_contDiff n) t).2.1

theorem continuous_kn2 (n : ℕ) : Continuous (D.kn2 n) := by
  have ha' := continuous_aOf' (D.cont_phi n) (D.cont_dphi n)
  have hb := continuous_bOf (D.cont_phi n)
  have hb' := continuous_bOf' (D.cont_phi n) (D.cont_dphi n)
  exact (continuous_const.mul hb').add ((ha'.mul continuous_const).add (continuous_volt ha' hb'))

@[simp] theorem kn_zero (n : ℕ) : D.kn n 0 = 0 := by simp [kn, kM]

@[simp] theorem kn1_zero (n : ℕ) : D.kn1 n 0 = D.phi n 1 ^ 2 := by simp [kn1, kM1, sq]

@[simp] theorem kn2_zero (n : ℕ) : D.kn2 n 0 = 0 := by
  simp [kn2, kM2, aOf', bOf']; ring

/-- **CC Prop 5.3, termwise**: `Q` applied to the n-th coefficient is CC's `C_n` (99). -/
theorem Qkn_eq_Cn (n : ℕ) (t : ℝ) : -(D.kn2 n t) + D.kn n t / 4 = D.Cn n t := by
  have h := (lemma52 (D.phi_contDiff n) (D.phi_contDiff n) t).2.2
  have e1 : Real.exp (-t / 2) * Real.exp (-t) = Real.exp (-(3 / 2) * t) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (t / 2) * Real.exp t = Real.exp ((3 / 2) * t) := by
    rw [← Real.exp_add]; ring_nf
  unfold kn kn2
  rw [h]
  unfold Cn kM Du
  linear_combination (deriv (D.phi n) (Real.exp (-t)) * D.phi n 1) * e1
    - (D.phi n 1 * deriv (D.phi n) (Real.exp t)) * e2

/-! ### Uniform bounds on (-T, T) -/

/-- `α n = 2 M n` bounds the a-side on `[0, T]`. -/
def alpha (n : ℕ) : ℝ := 2 * D.M n
/-- `β n = e^{T/2}(1 + e^T) N n` bounds the a-side on `[-T, 0]`. -/
def beta (n : ℕ) : ℝ := Real.exp (D.T / 2) * (1 + Real.exp D.T) * D.N n
/-- The uniform bound for `kn`, `kn1`, `kn2` on `(-T, T)`. -/
def B (n : ℕ) : ℝ := (2 + D.T) * (D.alpha n * D.beta n)

theorem M_nonneg (n : ℕ) : 0 ≤ D.M n :=
  (abs_nonneg _).trans (D.bound_inner n 1 ⟨Real.exp_le_one_iff.2 (by linarith [D.T_pos]),
    le_rfl⟩).1

theorem N_nonneg (n : ℕ) : 0 ≤ D.N n :=
  (abs_nonneg _).trans (D.bound_outer n 1 ⟨le_rfl,
    Real.one_le_exp_iff.2 D.T_pos.le⟩).1

theorem bdd_aOf (n : ℕ) :
    Bdd D.T (D.alpha n) (D.beta n) (aOf (D.phi n)) ∧
      Bdd D.T (D.alpha n) (D.beta n) (aOf' (D.phi n)) := by
  have hM := D.M_nonneg n
  have hN := D.N_nonneg n
  have hpos : ∀ s ∈ Icc 0 D.T, |aOf (D.phi n) s| ≤ D.alpha n ∧ |aOf' (D.phi n) s| ≤ D.alpha n := by
    intro s hs
    have hx : Real.exp (-s) ∈ Icc (Real.exp (-D.T)) 1 :=
      ⟨Real.exp_le_exp.2 (by linarith [hs.2]), Real.exp_le_one_iff.2 (by linarith [hs.1])⟩
    have h := aOf_bounds_gen (c := 1) (d := 1) (D.bound_inner n _ hx)
      (Real.exp_le_one_iff.2 (by linarith [hs.1])) (Real.exp_le_one_iff.2 (by linarith [hs.1]))
    unfold alpha
    exact ⟨h.1.trans (by linarith), h.2.trans (by linarith)⟩
  have hneg : ∀ s ∈ Icc (-D.T) 0, |aOf (D.phi n) s| ≤ D.beta n ∧ |aOf' (D.phi n) s| ≤ D.beta n := by
    intro s hs
    have hx : Real.exp (-s) ∈ Icc 1 (Real.exp D.T) :=
      ⟨Real.one_le_exp_iff.2 (by linarith [hs.2]), Real.exp_le_exp.2 (by linarith [hs.1])⟩
    have h := aOf_bounds_gen (c := Real.exp (D.T / 2)) (d := Real.exp D.T)
      (D.bound_outer n _ hx) (Real.exp_le_exp.2 (by linarith [hs.1]))
      (Real.exp_le_exp.2 (by linarith [hs.1]))
    have e0 : 0 ≤ Real.exp (D.T / 2) := (Real.exp_pos _).le
    have e1 : 0 ≤ Real.exp D.T := (Real.exp_pos _).le
    unfold beta
    refine ⟨h.1.trans ?_, h.2.trans ?_⟩
    · have : D.N n ≤ (1 + Real.exp D.T) * D.N n := by nlinarith
      calc Real.exp (D.T / 2) * D.N n ≤ Real.exp (D.T / 2) * ((1 + Real.exp D.T) * D.N n) :=
            mul_le_mul_of_nonneg_left this e0
        _ = _ := by ring
    · have : D.N n / 2 + Real.exp D.T * D.N n ≤ (1 + Real.exp D.T) * D.N n := by nlinarith
      calc Real.exp (D.T / 2) * (D.N n / 2 + Real.exp D.T * D.N n)
          ≤ Real.exp (D.T / 2) * ((1 + Real.exp D.T) * D.N n) := mul_le_mul_of_nonneg_left this e0
        _ = _ := by ring
  exact ⟨⟨fun s hs => (hpos s hs).1, fun s hs => (hneg s hs).1⟩,
    ⟨fun s hs => (hpos s hs).2, fun s hs => (hneg s hs).2⟩⟩

theorem alpha_beta_nonneg (n : ℕ) : 0 ≤ D.alpha n * D.beta n := by
  unfold alpha beta
  have := D.M_nonneg n
  have := D.N_nonneg n
  positivity

theorem summable_wB : Summable fun n => D.w n * D.B n := by
  refine (D.summable_wMN.mul_left ((2 + D.T) * (2 * (Real.exp (D.T / 2) * (1 + Real.exp D.T))))).congr
    fun n => ?_
  unfold w B alpha beta
  ring

theorem abs_kn_le (n : ℕ) {t : ℝ} (ht : t ∈ Ioo (-D.T) D.T) :
    |D.kn n t| ≤ D.B n ∧ |D.kn1 n t| ≤ D.B n ∧ |D.kn2 n t| ≤ D.B n := by
  obtain ⟨hA, hA'⟩ := D.bdd_aOf n
  have hab := D.alpha_beta_nonneg n
  have htT : |t| ≤ D.T := abs_le.2 ⟨ht.1.le, ht.2.le⟩
  set φ := D.phi n
  -- the three Volterra integrals
  have v1 : |volt (aOf φ) (bOf φ) t| ≤ D.alpha n * D.beta n * |t| :=
    abs_volt_le fun s hs => by
      rw [bOf_eq_aOf, show -(t - s) = s - t by ring]; exact prod_bound_gen hA hA ht hs
  have v2 : |volt (aOf' φ) (bOf φ) t| ≤ D.alpha n * D.beta n * |t| :=
    abs_volt_le fun s hs => by
      rw [bOf_eq_aOf, show -(t - s) = s - t by ring]; exact prod_bound_gen hA' hA ht hs
  have v3 : |volt (aOf' φ) (bOf' φ) t| ≤ D.alpha n * D.beta n * |t| :=
    abs_volt_le fun s hs => by
      rw [bOf'_eq_aOf', show -(t - s) = s - t by ring, mul_neg, abs_neg]
      exact prod_bound_gen hA' hA' ht hs
  have hz : (0 : ℝ) ∈ uIcc 0 t := left_mem_uIcc
  have htm : t ∈ uIcc 0 t := right_mem_uIcc
  have b1 : |aOf φ 0 * bOf φ t| ≤ D.alpha n * D.beta n := by
    rw [bOf_eq_aOf, show -t = 0 - t by ring]; exact prod_bound_gen hA hA ht hz
  have b2 : |aOf φ 0 * bOf' φ t| ≤ D.alpha n * D.beta n := by
    rw [bOf'_eq_aOf', show -t = 0 - t by ring, mul_neg, abs_neg]; exact prod_bound_gen hA hA' ht hz
  have b3 : |aOf' φ t * bOf φ 0| ≤ D.alpha n * D.beta n := by
    rw [bOf_eq_aOf, show -(0 : ℝ) = t - t by ring]; exact prod_bound_gen hA' hA ht htm
  have hT : D.alpha n * D.beta n * |t| ≤ D.alpha n * D.beta n * D.T :=
    mul_le_mul_of_nonneg_left htT hab
  have hTpos := D.T_pos
  have hcmp : ∀ x : ℝ, x ≤ 2 * (D.alpha n * D.beta n) + D.alpha n * D.beta n * D.T → x ≤ D.B n :=
    fun x hx => by unfold B; nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [kn, ← volt_aOf_bOf (D.cont_phi n) (D.cont_phi n)]
    exact hcmp _ (by nlinarith)
  · unfold kn1 kM1
    refine (abs_add_le _ _).trans (hcmp _ ?_)
    nlinarith
  · unfold kn2 kM2
    refine (abs_add_le _ _).trans (hcmp _ ?_)
    have := abs_add_le (aOf' φ t * bOf φ 0) (volt (aOf' φ) (bOf' φ) t)
    nlinarith

theorem norm_w_le (n : ℕ) {t : ℝ} (ht : t ∈ Ioo (-D.T) D.T) :
    ‖D.w n * D.kn n t‖ ≤ D.w n * D.B n ∧ ‖D.w n * D.kn1 n t‖ ≤ D.w n * D.B n ∧
      ‖D.w n * D.kn2 n t‖ ≤ D.w n * D.B n := by
  obtain ⟨h0, h1, h2⟩ := D.abs_kn_le n ht
  have hw := D.w_nonneg n
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
  exact ⟨mul_le_mul_of_nonneg_left h0 hw, mul_le_mul_of_nonneg_left h1 hw,
    mul_le_mul_of_nonneg_left h2 hw⟩

theorem zero_mem_Ioo : (0 : ℝ) ∈ Ioo (-D.T) D.T := ⟨by linarith [D.T_pos], D.T_pos⟩

/-! ### Termwise differentiation of ε -/

theorem hasDerivAt_eps {t : ℝ} (ht : t ∈ Ioo (-D.T) D.T) : HasDerivAt D.eps (D.eps1 t) t :=
  hasDerivAt_tsum_of_isPreconnected (u := fun n => D.w n * D.B n)
    (g := fun n t => D.w n * D.kn n t) (g' := fun n t => D.w n * D.kn1 n t)
    D.summable_wB isOpen_Ioo isPreconnected_Ioo
    (fun n y _ => (D.hasDerivAt_kn n y).const_mul (D.w n)) (fun n y hy => (D.norm_w_le n hy).2.1)
    D.zero_mem_Ioo (by simp) ht

theorem hasDerivAt_eps1 {t : ℝ} (ht : t ∈ Ioo (-D.T) D.T) : HasDerivAt D.eps1 (D.eps2 t) t :=
  hasDerivAt_tsum_of_isPreconnected (u := fun n => D.w n * D.B n)
    (g := fun n t => D.w n * D.kn1 n t) (g' := fun n t => D.w n * D.kn2 n t)
    D.summable_wB isOpen_Ioo isPreconnected_Ioo
    (fun n y _ => (D.hasDerivAt_kn1 n y).const_mul (D.w n)) (fun n y hy => (D.norm_w_le n hy).2.2)
    D.zero_mem_Ioo
    (Summable.of_norm_bounded D.summable_wB fun n => (D.norm_w_le n D.zero_mem_Ioo).2.1) ht

theorem continuousOn_eps : ContinuousOn D.eps (Ioo (-D.T) D.T) :=
  fun _ ht => (D.hasDerivAt_eps ht).continuousAt.continuousWithinAt

theorem continuousOn_eps1 : ContinuousOn D.eps1 (Ioo (-D.T) D.T) :=
  fun _ ht => (D.hasDerivAt_eps1 ht).continuousAt.continuousWithinAt

theorem continuousOn_eps2 : ContinuousOn D.eps2 (Ioo (-D.T) D.T) :=
  continuousOn_tsum (f := fun n t => D.w n * D.kn2 n t)
    (fun n => (continuous_const.mul (D.continuous_kn2 n)).continuousOn) D.summable_wB
    fun n _ hx => (D.norm_w_le n hx).2.2

theorem continuousOn_Qeps : ContinuousOn D.Qeps (Ioo (-D.T) D.T) :=
  (D.continuousOn_eps2.neg).add (D.continuousOn_eps.div_const 4)

/-! ### CC Prop 5.3, Lemma 5.4, Rem 5.6 -/

/-- **CC Proposition 5.3** ((97) with (99)): on `|log ρ| < T`, `ε` is twice differentiable in
`log ρ` and `(Qε)(ρ) = Σ λ(n)²/(1-λ(n)²) C_n(ρ)`. -/
theorem prop53 {t : ℝ} (ht : t ∈ Ioo (-D.T) D.T) :
    HasDerivAt D.eps (D.eps1 t) t ∧ HasDerivAt D.eps1 (D.eps2 t) t ∧
      D.Qeps t = ∑' n, D.w n * D.Cn n t := by
  refine ⟨D.hasDerivAt_eps ht, D.hasDerivAt_eps1 ht, ?_⟩
  have s2 : Summable fun n => D.w n * D.kn2 n t :=
    Summable.of_norm_bounded D.summable_wB fun n => (D.norm_w_le n ht).2.2
  have s0 : Summable fun n => D.w n * D.kn n t :=
    Summable.of_norm_bounded D.summable_wB fun n => (D.norm_w_le n ht).1
  unfold Qeps eps eps2
  rw [← tsum_neg, ← tsum_div_const, ← s2.neg.tsum_add (s0.div_const 4)]
  refine tsum_congr fun n => ?_
  rw [← D.Qkn_eq_Cn n t]
  ring

@[simp] theorem eps_zero : D.eps 0 = 0 := by simp [eps]

theorem eps1_zero : D.eps1 0 = ∑' n, D.w n * D.phi n 1 ^ 2 := by simp [eps1]

/-- **CC Lemma 5.4** (structural identity): `ε'(1⁺) = Σ λ(n)²/(1-λ(n)²) ξ_n(1)²`, as the
derivative of `ε` in `log ρ` at `ρ = 1` (see `epsMul_hasDerivWithinAt` for the `ρ`-derivative). -/
theorem lemma54 : HasDerivAt D.eps (∑' n, D.w n * D.phi n 1 ^ 2) 0 := by
  rw [← D.eps1_zero]; exact D.hasDerivAt_eps D.zero_mem_Ioo

/-- **CC Remark 5.6** (the kernel of `K_I` has zero diagonal, "Tr K_I = 0"): `(Qε)(1) = 0`. -/
@[simp] theorem Qeps_zero : D.Qeps 0 = 0 := by simp [Qeps, eps2]

theorem epsMul_inv (ρ : ℝ) : D.epsMul ρ⁻¹ = D.epsMul ρ := by
  simp [epsMul, Real.log_inv, abs_neg]

/-- CC's ε on `ρ ≥ 1`, as in the proof of Lemma 5.4:
`ε(ρ) = Σ λ²/(1-λ²) · ρ^{1/2} ∫_{ρ⁻¹}^1 ξ_n^an(x) ξ_n^an(ρx) dx`. -/
theorem epsMul_eq {ρ : ℝ} (hρ : 1 ≤ ρ) :
    D.epsMul ρ = ∑' n, D.w n * (Real.sqrt ρ * ∫ x in ρ⁻¹..1, D.phi n x * D.phi n (ρ * x)) := by
  have hρ0 : 0 < ρ := by linarith
  have hl : |Real.log ρ| = Real.log ρ := abs_of_nonneg (Real.log_nonneg hρ)
  have e1 : Real.exp (Real.log ρ / 2) = Real.sqrt ρ := by
    rw [← Real.log_sqrt hρ0.le, Real.exp_log (Real.sqrt_pos.2 hρ0)]
  have e2 : Real.exp (-Real.log ρ) = ρ⁻¹ := by rw [Real.exp_neg, Real.exp_log hρ0]
  simp only [epsMul, hl, eps, kn, kM, e1, e2, Real.exp_log hρ0]

/-- CC's `ε'(1⁺)` as an honest right derivative in `ρ`: it equals `eps1 0`. -/
theorem epsMul_hasDerivWithinAt : HasDerivWithinAt D.epsMul (D.eps1 0) (Ici 1) 1 := by
  have h0 : Real.log 1 ∈ Ioo (-D.T) D.T := by rw [Real.log_one]; exact D.zero_mem_Ioo
  have h := (D.hasDerivAt_eps h0).comp 1 (Real.hasDerivAt_log one_ne_zero)
  simp only [Real.log_one, inv_one, mul_one] at h
  refine h.hasDerivWithinAt.congr (fun ρ hρ => ?_) (by simp [epsMul])
  simp [epsMul, abs_of_nonneg (Real.log_nonneg (mem_Ici.1 hρ))]

/-- The link to CC (84): with `ζ_n = λ(n)/√(1-λ(n)²) · ξ_n^an` on `[1,∞)` (CC, after (98)),
the n-th term `λ(n)/√(1-λ(n)²) ⟨ξ_n | ϑ(ρ⁻¹) ζ_n⟩` of (84) is `w n · kn n`. -/
theorem cc84_term (n : ℕ) (t : ℝ) :
    D.lam n / Real.sqrt (1 - D.lam n ^ 2)
        * kM (D.phi n) (fun x => D.lam n / Real.sqrt (1 - D.lam n ^ 2) * D.phi n x) t
      = D.w n * D.kn n t := by
  have hs : 0 < 1 - D.lam n ^ 2 := by linarith [D.lam_sq_lt_one n]
  have hc : (D.lam n / Real.sqrt (1 - D.lam n ^ 2)) ^ 2 = D.w n := by
    rw [div_pow, Real.sq_sqrt hs.le]; rfl
  unfold kn kM
  have : ∫ x in (Real.exp (-t))..1,
        D.phi n x * (D.lam n / Real.sqrt (1 - D.lam n ^ 2) * D.phi n (Real.exp t * x))
      = D.lam n / Real.sqrt (1 - D.lam n ^ 2)
          * ∫ x in (Real.exp (-t))..1, D.phi n x * D.phi n (Real.exp t * x) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun x _ => by ring
  rw [this, ← hc]
  ring

end ProlateData

end ArchS8
