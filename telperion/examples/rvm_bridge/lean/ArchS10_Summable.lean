/-
  ArchS10_Summable -- stage S10, part 3: S8's `summable_wMN` FROM THE EIGEN-RELATION ALONE.

  S8's `ProlateData` carries a field `summable_wMN : Summable (λ²/(1-λ²) M_n N_n)` with sup bounds
  M_n, N_n of ξ_n^an and its derivative; S8's notes recorded it as S6's one hard obligation (a sup
  bound beating 1/|λ_n|).  This module shows it is automatic for any orthonormal family of
  continuous everywhere-eigenfunctions of S9's T with nonzero eigenvalues and sup λ² < 1:

  1. (`abs_T_le_s`, `abs_Td_le_s`)  Taylor-expanding the kernel 2cos(2πxω) in ω, for 0 ≤ ω ≤ X,
     X ≥ 1, and continuous f:
         |T f(ω)|, |Td f(ω)|  ≤  s_X(f) := Σ'_j γ_j |⟨x^{2j}, f⟩|,     γ_j = 4 (4πX)^{2j}/(2j)!.
     The right side does not depend on ω.
  2. (`sum_sq_s_le`)  Bessel for each monomial x^{2j}, and Cauchy-Schwarz in j:
         Σ_{n∈S} s_X(e_n)²  ≤  (Σ'_j γ_j)²       for every finite S, any orthonormal family e_n.
  3. (`EigenFamily.toProlateData`)  Hence with M_n = N_n = s_X(ξ_n)/|λ_n| (X = e^T), and λξ = Tξ,
     λξ' = Tdξ, the fields `bound_inner`, `bound_outer`, `summable_wMN` all hold, with
         Σ_n λ_n²/(1-λ_n²) M_n N_n ≤ (Σ'γ)²/(1 - c)       (`sum_wMN_le`).
  So S8's series for ε, ε', ε'' and Qε converge uniformly on |t| < T with NO separate analytic
  input: S8's own `abs_kn_le` turns `sum_wMN_le` into Σ_n w_n sup|kn|, sup|kn1|, sup|kn2| < ∞.
  No sorry, no axiom.  conjecture1_proved = False.
-/
import ArchS9_Bridge
import ArchS8_ProlateData

open MeasureTheory Set Finset Filter Topology

noncomputable section

namespace ArchS10

open ArchS9

/-- The majorant `γ_j = 4 (4πX)^{2j}/(2j)!`. -/
def gam (X : ℝ) (j : ℕ) : ℝ := 4 * (4 * Real.pi * X) ^ (2 * j) / ((2 * j).factorial : ℝ)

lemma gam_nonneg {X : ℝ} (hX : 0 ≤ X) (j : ℕ) : 0 ≤ gam X j := by
  unfold gam; positivity

lemma summable_pow_two_mul (y : ℝ) :
    Summable fun j : ℕ => y ^ (2 * j) / ((2 * j).factorial : ℝ) :=
  (Real.summable_pow_div_factorial y).comp_injective (mul_right_injective₀ two_ne_zero)

lemma summable_gam (X : ℝ) : Summable (gam X) := by
  have := (summable_pow_two_mul (4 * Real.pi * X)).mul_left 4
  refine this.congr fun j => ?_
  unfold gam; ring

lemma abs_aC (j : ℕ) : |aC j| = 2 * (2 * Real.pi) ^ (2 * j) / ((2 * j).factorial : ℝ) := by
  unfold aC
  rw [abs_div, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one,
    abs_of_pos (by positivity : (0 : ℝ) < 2), abs_of_pos (by positivity : (0 : ℝ) < (2 * Real.pi) ^ (2 * j)),
    abs_of_pos (by positivity : (0 : ℝ) < ((2 * j).factorial : ℝ))]

lemma aC_term_le {X ω : ℝ} (hX : 1 ≤ X) (hω : 0 ≤ ω) (hωX : ω ≤ X) (j : ℕ) :
    |aC j * ω ^ (2 * j)| ≤ gam X j := by
  rw [abs_mul, abs_aC, abs_pow, abs_of_nonneg hω]
  unfold gam
  have h1 : ω ^ (2 * j) ≤ X ^ (2 * j) := pow_le_pow_left₀ hω hωX _
  have h2 : (2 * Real.pi) ^ (2 * j) * X ^ (2 * j) ≤ (4 * Real.pi * X) ^ (2 * j) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by nlinarith [Real.pi_pos]) _
  have hf : (0 : ℝ) < ((2 * j).factorial : ℝ) := by positivity
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hf]
  have h3 : (2 * Real.pi) ^ (2 * j) * ω ^ (2 * j) ≤ (2 * Real.pi) ^ (2 * j) * X ^ (2 * j) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h4 : 0 ≤ (4 * Real.pi * X) ^ (2 * j) :=
    pow_nonneg (mul_nonneg (by positivity) (by linarith)) _
  nlinarith [h2, h3, h4]

lemma aCd_term_le {X ω : ℝ} (hX : 1 ≤ X) (hω : 0 ≤ ω) (hωX : ω ≤ X) (j : ℕ) :
    |aC j * (2 * j : ℝ) * ω ^ (2 * j - 1)| ≤ gam X j := by
  rw [abs_mul, abs_mul, abs_aC, abs_pow, abs_of_nonneg hω,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * j)]
  unfold gam
  have hf : (0 : ℝ) < ((2 * j).factorial : ℝ) := by positivity
  have h1 : ω ^ (2 * j - 1) ≤ X ^ (2 * j) :=
    (pow_le_pow_left₀ hω hωX _).trans (pow_le_pow_right₀ hX (by omega))
  have h2 : (2 * j : ℝ) ≤ 2 ^ (2 * j) := by
    have : (2 * j : ℕ) < 2 ^ (2 * j) := Nat.lt_two_pow_self
    exact_mod_cast this.le
  have h3 : (2 * Real.pi) ^ (2 * j) * 2 ^ (2 * j) * X ^ (2 * j) = (4 * Real.pi * X) ^ (2 * j) := by
    rw [← mul_pow, ← mul_pow]; ring_nf
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hf]
  have hp : (0 : ℝ) ≤ (2 * Real.pi) ^ (2 * j) := by positivity
  calc 2 * (2 * Real.pi) ^ (2 * j) * (2 * j : ℝ) * ω ^ (2 * j - 1)
      ≤ 2 * (2 * Real.pi) ^ (2 * j) * 2 ^ (2 * j) * X ^ (2 * j) := by
        have : (2 * j : ℝ) * ω ^ (2 * j - 1) ≤ 2 ^ (2 * j) * X ^ (2 * j) :=
          mul_le_mul h2 h1 (by positivity) (by positivity)
        nlinarith
    _ = 2 * (4 * Real.pi * X) ^ (2 * j) := by rw [← h3]; ring
    _ ≤ 4 * (4 * Real.pi * X) ^ (2 * j) := by nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ 4 * Real.pi * X) (2 * j)]

/-- `s_X(f) = Σ'_j γ_j |⟨x^{2j}, f⟩|`. -/
def sX (X : ℝ) (f : ℝ → ℝ) : ℝ := ∑' j, gam X j * |mom j f|

lemma summable_gam_mom {X : ℝ} (hX : 0 ≤ X) {f : ℝ → ℝ} (hf : Continuous f) :
    Summable fun j => gam X j * |mom j f| :=
  ((summable_gam X).mul_right (L1 f)).of_nonneg_of_le
    (fun j => mul_nonneg (gam_nonneg hX j) (abs_nonneg _))
    (fun j => mul_le_mul_of_nonneg_left (abs_mom_le j hf) (gam_nonneg hX j))

lemma sX_nonneg {X : ℝ} (hX : 0 ≤ X) (f : ℝ → ℝ) : 0 ≤ sX X f :=
  tsum_nonneg fun j => mul_nonneg (gam_nonneg hX j) (abs_nonneg _)

lemma partial_le_sX {X : ℝ} (hX : 0 ≤ X) {f : ℝ → ℝ} (hf : Continuous f) (J : ℕ) :
    ∑ j ∈ range J, gam X j * |mom j f| ≤ sX X f :=
  (summable_gam_mom hX hf).sum_le_tsum _ fun j _ => mul_nonneg (gam_nonneg hX j) (abs_nonneg _)

lemma tendsto_pow_div_fact_two (y : ℝ) :
    Tendsto (fun J : ℕ => y ^ (2 * J) / ((2 * J).factorial : ℝ)) atTop (𝓝 0) :=
  (summable_pow_two_mul y).tendsto_atTop_zero

lemma tendsto_pow_div_fact_odd (y : ℝ) :
    Tendsto (fun M : ℕ => y ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ)) atTop (𝓝 0) :=
  ((Real.summable_pow_div_factorial y).comp_injective
    (fun a b h => by simpa using h : Function.Injective fun M : ℕ => 2 * M + 1)).tendsto_atTop_zero

/-- **The ω-free bound for `T`.** -/
theorem abs_T_le_s {X : ℝ} (hX : 1 ≤ X) {f : ℝ → ℝ} (hf : Continuous f) {ω : ℝ} (hω : 0 ≤ ω)
    (hωX : ω ≤ X) : |T f ω| ≤ sX X f := by
  have hX0 : 0 ≤ X := by linarith
  have hlim : Tendsto (fun J : ℕ => sX X f + 4 * ((2 * Real.pi * X) ^ (2 * J)
      / ((2 * J).factorial : ℝ)) * L1 f) atTop (𝓝 (sX X f + 4 * 0 * L1 f)) :=
    tendsto_const_nhds.add (((tendsto_pow_div_fact_two _).const_mul 4).mul_const _)
  rw [mul_zero, zero_mul, add_zero] at hlim
  have hev : ∀ᶠ J : ℕ in atTop, |T f ω| ≤ sX X f + 4 * ((2 * Real.pi * X) ^ (2 * J)
      / ((2 * J).factorial : ℝ)) * L1 f := by
    obtain ⟨J0, hJ0⟩ := exists_nat_ge (2 * Real.pi * X)
    refine eventually_atTop.2 ⟨J0, fun J hJ => ?_⟩
    have hJ : 2 * Real.pi * X ≤ (2 * J + 1) / 2 := by
      have : (J0 : ℝ) ≤ J := by exact_mod_cast hJ
      nlinarith
    have h1 := T_sub_le J hf hω hωX hJ
    have h2 : |∑ j ∈ range J, aC j * ω ^ (2 * j) * mom j f| ≤ sX X f := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_trans (Finset.sum_le_sum fun j _ => ?_)
        (partial_le_sX hX0 hf J))
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (aC_term_le hX hω hωX j) (abs_nonneg _)
    have h3 := abs_sub_abs_le_abs_sub (T f ω) (∑ j ∈ range J, aC j * ω ^ (2 * j) * mom j f)
    have e : 4 * (2 * Real.pi * X) ^ (2 * J) / ((2 * J).factorial : ℝ) * L1 f
        = 4 * ((2 * Real.pi * X) ^ (2 * J) / ((2 * J).factorial : ℝ)) * L1 f := by ring
    rw [e] at h1
    linarith
  exact ge_of_tendsto hlim hev

/-- **The ω-free bound for `Td`.** -/
theorem abs_Td_le_s {X : ℝ} (hX : 1 ≤ X) {f : ℝ → ℝ} (hf : Continuous f) {ω : ℝ} (hω : 0 ≤ ω)
    (hωX : ω ≤ X) : |Td f ω| ≤ sX X f := by
  have hX0 : 0 ≤ X := by linarith
  have hlim : Tendsto (fun M : ℕ => sX X f + 8 * Real.pi * ((2 * Real.pi * X) ^ (2 * M + 1)
      / ((2 * M + 1).factorial : ℝ)) * L1 f) atTop (𝓝 (sX X f + 8 * Real.pi * 0 * L1 f)) :=
    tendsto_const_nhds.add (((tendsto_pow_div_fact_odd _).const_mul (8 * Real.pi)).mul_const _)
  rw [mul_zero, zero_mul, add_zero] at hlim
  have hev : ∀ᶠ M : ℕ in atTop, |Td f ω| ≤ sX X f + 8 * Real.pi * ((2 * Real.pi * X) ^ (2 * M + 1)
      / ((2 * M + 1).factorial : ℝ)) * L1 f := by
    obtain ⟨M0, hM0⟩ := exists_nat_ge (2 * Real.pi * X)
    refine eventually_atTop.2 ⟨M0, fun M hM => ?_⟩
    have hM : 2 * Real.pi * X ≤ (2 * M + 1 + 1) / 2 := by
      have : (M0 : ℝ) ≤ M := by exact_mod_cast hM
      nlinarith
    have h1 := Td_sub_le M hf hω hωX hM
    have h2 : |∑ j ∈ range (M + 1), aC j * (2 * j : ℝ) * ω ^ (2 * j - 1) * mom j f| ≤ sX X f := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_trans (Finset.sum_le_sum fun j _ => ?_)
        (partial_le_sX hX0 hf (M + 1)))
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (aCd_term_le hX hω hωX j) (abs_nonneg _)
    have h3 := abs_sub_abs_le_abs_sub (Td f ω)
      (∑ j ∈ range (M + 1), aC j * (2 * j : ℝ) * ω ^ (2 * j - 1) * mom j f)
    have e : 8 * Real.pi * (2 * Real.pi * X) ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ) * L1 f
        = 8 * Real.pi * ((2 * Real.pi * X) ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ)) * L1 f := by
      ring
    rw [e] at h1
    linarith
  exact ge_of_tendsto hlim hev

/-! ## Bessel in each moment. -/

/-- Cauchy-Schwarz for a nonnegative-weighted series. -/
lemma tsum_sq_le {g m : ℕ → ℝ} (hg : ∀ j, 0 ≤ g j) (hgs : Summable g) (hm : ∀ j, |m j| ≤ 1) :
    (∑' j, g j * |m j|) ^ 2 ≤ (∑' j, g j) * ∑' j, g j * m j ^ 2 := by
  have s1 : Summable fun j => g j * |m j| :=
    hgs.of_nonneg_of_le (fun j => mul_nonneg (hg j) (abs_nonneg _))
      (fun j => by have := hm j; nlinarith [hg j])
  have s2 : Summable fun j => g j * m j ^ 2 :=
    hgs.of_nonneg_of_le (fun j => mul_nonneg (hg j) (sq_nonneg _))
      (fun j => by
        have h := hm j
        have : m j ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg (m j)]
        nlinarith [hg j])
  have hfin : ∀ J, (∑ j ∈ range J, g j * |m j|) ^ 2 ≤ (∑' j, g j) * ∑' j, g j * m j ^ 2 := by
    intro J
    have cs := Finset.sum_mul_sq_le_sq_mul_sq (range J) (fun j => Real.sqrt (g j))
      (fun j => Real.sqrt (g j) * |m j|)
    have e1 : ∑ j ∈ range J, Real.sqrt (g j) * (Real.sqrt (g j) * |m j|) = ∑ j ∈ range J, g j * |m j| :=
      Finset.sum_congr rfl fun j _ => by rw [← mul_assoc, Real.mul_self_sqrt (hg j)]
    have e2 : ∑ j ∈ range J, Real.sqrt (g j) ^ 2 = ∑ j ∈ range J, g j :=
      Finset.sum_congr rfl fun j _ => Real.sq_sqrt (hg j)
    have e3 : ∑ j ∈ range J, (Real.sqrt (g j) * |m j|) ^ 2 = ∑ j ∈ range J, g j * m j ^ 2 :=
      Finset.sum_congr rfl fun j _ => by rw [mul_pow, Real.sq_sqrt (hg j), sq_abs]
    rw [e1, e2, e3] at cs
    refine cs.trans (mul_le_mul (hgs.sum_le_tsum _ fun j _ => hg j)
      (s2.sum_le_tsum _ fun j _ => mul_nonneg (hg j) (sq_nonneg _)) (Finset.sum_nonneg
        fun j _ => mul_nonneg (hg j) (sq_nonneg _)) (tsum_nonneg hg))
  have hlim : Tendsto (fun J => (∑ j ∈ range J, g j * |m j|) ^ 2) atTop (𝓝 ((∑' j, g j * |m j|) ^ 2)) :=
    (s1.hasSum.tendsto_sum_nat).pow 2
  exact le_of_tendsto' hlim hfin

lemma ip_mono_self_le (j : ℕ) : ip (fun x => x ^ (2 * j)) (fun x => x ^ (2 * j)) ≤ 1 := by
  have := ip_self_le_of_bound (f := fun x : ℝ => x ^ (2 * j)) (by fun_prop) (B := 1) fun x hx => by
    rw [abs_of_nonneg (by have := hx.1; positivity)]; exact pow_le_one₀ hx.1 hx.2
  simpa using this

/-- **Bessel in every moment**: for an orthonormal continuous family and every finite S,
`Σ_{n∈S} s_X(e_n)² ≤ (Σ'_j γ_j)²`. -/
theorem sum_sq_s_le {X : ℝ} (hX : 0 ≤ X) (e : ℕ → ℝ → ℝ) (he : ∀ k, Continuous (e k))
    (horth : ∀ k l, ip (e k) (e l) = if k = l then 1 else 0) (S : Finset ℕ) :
    ∑ n ∈ S, sX X (e n) ^ 2 ≤ (∑' j, gam X j) ^ 2 := by
  have hg := gam_nonneg hX
  have hgs := summable_gam X
  have hL : ∀ n, L1 (e n) ≤ 1 := fun n => by
    have := L1_le_sqrt (he n); rw [horth, if_pos rfl, Real.sqrt_one] at this; exact this
  have hm : ∀ n j, |mom j (e n)| ≤ 1 := fun n j => (abs_mom_le j (he n)).trans (hL n)
  have hsq : ∀ n j, mom j (e n) ^ 2 ≤ 1 := fun n j => by
    rw [← sq_abs]; nlinarith [hm n j, abs_nonneg (mom j (e n))]
  have s2 : ∀ n, Summable fun j => gam X j * mom j (e n) ^ 2 := fun n =>
    hgs.of_nonneg_of_le (fun j => mul_nonneg (hg j) (sq_nonneg _))
      (fun j => by nlinarith [hg j, hsq n j])
  have step1 : ∑ n ∈ S, sX X (e n) ^ 2 ≤ ∑ n ∈ S, (∑' j, gam X j) * ∑' j, gam X j * mom j (e n) ^ 2 :=
    Finset.sum_le_sum fun n _ => tsum_sq_le hg hgs (hm n)
  have hmom : ∀ n j, mom j (e n) = ip (fun x => x ^ (2 * j)) (e n) := fun _ _ => rfl
  have step2 : ∑ n ∈ S, ∑' j, gam X j * mom j (e n) ^ 2 ≤ ∑' j, gam X j := by
    rw [← Summable.tsum_finsetSum (fun n _ => s2 n)]
    refine Summable.tsum_le_tsum (fun j => ?_) (summable_sum fun n _ => s2 n) hgs
    rw [← Finset.mul_sum]
    have hb := bessel_finite e he horth (r := fun x => x ^ (2 * j)) (by fun_prop) S
    simp only [← hmom] at hb
    calc gam X j * ∑ n ∈ S, mom j (e n) ^ 2 ≤ gam X j * 1 :=
          mul_le_mul_of_nonneg_left (hb.trans (ip_mono_self_le j)) (hg j)
      _ = gam X j := mul_one _
  rw [← Finset.mul_sum] at step1
  calc ∑ n ∈ S, sX X (e n) ^ 2 ≤ (∑' j, gam X j) * ∑ n ∈ S, ∑' j, gam X j * mom j (e n) ^ 2 := step1
    _ ≤ (∑' j, gam X j) * ∑' j, gam X j := mul_le_mul_of_nonneg_left step2 (tsum_nonneg hg)
    _ = (∑' j, gam X j) ^ 2 := by ring

/-! ## The constructor. -/

/-- The data of an orthonormal family of continuous everywhere-eigenfunctions of `T` with nonzero
eigenvalues bounded away from ±1.  This is all S8's `ProlateData` needs. -/
structure EigenFamily where
  lam : ℕ → ℝ
  phi : ℕ → ℝ → ℝ
  cont : ∀ n, Continuous (phi n)
  eig : ∀ n ω, T (phi n) ω = lam n * phi n ω
  ne : ∀ n, lam n ≠ 0
  orth : ∀ n m, ip (phi n) (phi m) = if n = m then 1 else 0
  c : ℝ
  c_lt : c < 1
  lam_sq_le : ∀ n, lam n ^ 2 ≤ c

namespace EigenFamily

variable (F : EigenFamily)

lemma deriv_eq (n : ℕ) (x : ℝ) : deriv (F.phi n) x = Td (F.phi n) x / F.lam n :=
  (hasDerivAt_eig (F.cont n) (F.ne n) (F.eig n) x).deriv

lemma contDiff (n : ℕ) : ContDiff ℝ 1 (F.phi n) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (hasDerivAt_eig (F.cont n) (F.ne n) (F.eig n) x).differentiableAt, ?_⟩
  rw [show deriv (F.phi n) = fun x => Td (F.phi n) x / F.lam n from funext (F.deriv_eq n)]
  exact (continuous_Td (F.cont n)).div_const _

/-- `M_n = N_n = s_X(ξ_n)/|λ_n|`. -/
def Mb (X : ℝ) (n : ℕ) : ℝ := sX X (F.phi n) / |F.lam n|

lemma bound {X : ℝ} (hX : 1 ≤ X) (n : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hxX : x ≤ X) :
    |F.phi n x| ≤ F.Mb X n ∧ |deriv (F.phi n) x| ≤ F.Mb X n := by
  have hl : 0 < |F.lam n| := abs_pos.2 (F.ne n)
  unfold Mb
  constructor
  · rw [le_div_iff₀ hl, mul_comm, ← abs_mul, ← F.eig]
    exact abs_T_le_s hX (F.cont n) hx0 hxX
  · rw [F.deriv_eq, abs_div, div_le_div_iff_of_pos_right hl]
    exact abs_Td_le_s hX (F.cont n) hx0 hxX

lemma wMN_eq (X : ℝ) (n : ℕ) :
    F.lam n ^ 2 / (1 - F.lam n ^ 2) * (F.Mb X n * F.Mb X n)
      = sX X (F.phi n) ^ 2 / (1 - F.lam n ^ 2) := by
  unfold Mb
  have hl : |F.lam n| ≠ 0 := abs_ne_zero.2 (F.ne n)
  have h1 : 1 - F.lam n ^ 2 ≠ 0 := by have := F.lam_sq_le n; have := F.c_lt; intro h; linarith
  rw [← sq_abs (F.lam n)]
  field_simp

/-- **The bound behind `summable_wMN`**: every finite partial sum of `w_n M_n N_n` is at most
`(Σ'γ)²/(1 - c)`. -/
theorem sum_wMN_le {X : ℝ} (hX : 0 ≤ X) (S : Finset ℕ) :
    ∑ n ∈ S, F.lam n ^ 2 / (1 - F.lam n ^ 2) * (F.Mb X n * F.Mb X n)
      ≤ (∑' j, gam X j) ^ 2 / (1 - F.c) := by
  have hc : 0 < 1 - F.c := by linarith [F.c_lt]
  simp_rw [F.wMN_eq]
  calc ∑ n ∈ S, sX X (F.phi n) ^ 2 / (1 - F.lam n ^ 2)
      ≤ ∑ n ∈ S, sX X (F.phi n) ^ 2 / (1 - F.c) := Finset.sum_le_sum fun n _ =>
        div_le_div_of_nonneg_left (sq_nonneg _) hc (by linarith [F.lam_sq_le n])
    _ = (∑ n ∈ S, sX X (F.phi n) ^ 2) / (1 - F.c) := by rw [Finset.sum_div]
    _ ≤ _ := div_le_div_of_nonneg_right (sum_sq_s_le hX F.phi F.cont F.orth S) hc.le

/-- **S8's `ProlateData` from an eigenfamily**: no separate sup bound `M_n` is needed. -/
def toProlateData (T0 : ℝ) (hT : 0 < T0) : ArchS8.ProlateData where
  lam := F.lam
  lam_sq_lt_one n := lt_of_le_of_lt (F.lam_sq_le n) F.c_lt
  phi := F.phi
  phi_contDiff := F.contDiff
  T := T0
  T_pos := hT
  M := F.Mb (Real.exp T0)
  N := F.Mb (Real.exp T0)
  bound_inner n x hx := F.bound (Real.one_le_exp_iff.2 hT.le) n
    ((Real.exp_pos _).le.trans hx.1) (hx.2.trans (Real.one_le_exp_iff.2 hT.le))
  bound_outer n x hx := F.bound (Real.one_le_exp_iff.2 hT.le) n
    (zero_le_one.trans hx.1) hx.2
  summable_wMN := summable_of_sum_le
    (fun n => by
      have := F.wMN_eq (Real.exp T0) n
      simp only [Pi.zero_apply]
      rw [this]
      exact div_nonneg (sq_nonneg _) (by linarith [F.lam_sq_le n, F.c_lt]))
    (F.sum_wMN_le (Real.exp_pos T0).le)

@[simp] lemma toProlateData_lam (T0 : ℝ) (hT : 0 < T0) : (F.toProlateData T0 hT).lam = F.lam := rfl
@[simp] lemma toProlateData_phi (T0 : ℝ) (hT : 0 < T0) : (F.toProlateData T0 hT).phi = F.phi := rfl
@[simp] lemma toProlateData_T (T0 : ℝ) (hT : 0 < T0) : (F.toProlateData T0 hT).T = T0 := rfl

end EigenFamily

end ArchS10
