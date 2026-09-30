import Crux3_BandCert
import Crux3_BandDHData

/-!
# Crux3: Davenport-Heilbronn FAILS the band certificate (kernel-checked counterexample)

`Crux3_BandCert.band_floor` proves that zeta's Weil functional on the band
`span{cos(763u/9), cos(259u/3)}` on `[-9π/14, 9π/14]` (window `x = e^{9π/7} = 56.78`) is at least
`(1/2) ||v||^2`.  This file proves that Davenport-Heilbronn's functional is at most
`-(1/2) ||v||^2` on the test `v = -3 cos(763u/9) + 2 cos(259u/3)` of the same band.  So the certificate
separates `zeta` from `D`: `D` satisfies the same kind of functional equation but has zeros off the
line (the quadruple `0.8085 ± 85.699 i` sits inside this band).

D's functional is defined off-registry, as the arithmetic side of D's Guinand-Weil explicit formula.
The gamma factor is `Gamma_R(s + 1)`, the conductor is 5, and there is no pole:
* `archSideD g = g(0) log(5/π) + (1/2π) ∫ h_g(r) Re ψ(3/4 + ir/2) dr`, the `ζ` pattern with `1/4 -> 3/4`;
* `primeSideD w g = Σ_n w(n)/√n (g(log n) + g(-log n))`, where the weights `w` are the coefficients of
  `-D'/D`.

The weights are NOT assumed numerically.  The theorems take any `w` satisfying the defining identity
`a(n) log n = Σ_{d | n} w(d) a(n/d)` on `[1, 56]` (`Crux3_BandDHData`), and uniqueness pins `w`
down to the closed forms `cD`.

What is proved (all axiom-clean):
* `archD_band_le`: an upper bound on D's archimedean side for any band test.  It combines
  - the digamma majorant `psiD_le` (series with `N` terms, plus tails `(3/4)/N + (r/2)^2/(2N^2)`);
  - Lorentzian Parseval;
  - the `r^2` moment bound from the closed-form transform decay (`Fsq_mul_sq_le`, `R >= 2 k2`).
* `dh_band_arch_le`: `Re archSideD <= 4.33 ||v||^2` at `c* = (-3, 2)`, with `N = 300` and `R = 175`.
* `dh_band_comb_ge`: `Re primeSideD >= 4.86 ||v||^2` at `c*`.  The kappa ball comes from kernel-checked
  square-root brackets, and the prime logs from `exp(q/8)^8` enclosures; the table is `dtab_ok`
  (`decide +kernel`), and a tampered entry is rejected (`dtab_tamper`).
* `dh_band_negative`: `Re weilFormD w (v * v~) <= -(1/2) ||v||^2` (computed value: `-0.655 ||v||^2`).
* `band_separation`: on the same nonzero test, zeta's functional is `>= (1/2)||v||^2` and D's is
  `<= -(1/2)||v||^2`.

The link from `weilFormD` to D's zeros (`= Σ_ρ h(γ_ρ)`) is the classical explicit formula for `D`.
It is not formalized here.  It is cross-checked numerically in the research note: D's zero side gives
`-0.65464` against the arithmetic side's `-0.65462`.

No `sorry`.

`conjecture1_proved = False`.  This is a finite negative control.  Nothing here bears on RH.
-/

open MeasureTheory Complex Zeta23 Set Filter
open scoped ComplexConjugate

noncomputable section

namespace Crux3

/-! ## Telescoping tails. -/

lemma hasSum_telescope (f : ℕ → ℝ) (hf : Tendsto f atTop (nhds 0)) (hmono : ∀ n, f (n + 1) ≤ f n) :
    HasSum (fun n => f n - f (n + 1)) (f 0) := by
  have hnn : ∀ n, 0 ≤ f n - f (n + 1) := fun n => by linarith [hmono n]
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have e : ∀ M, ∑ i ∈ Finset.range M, (f i - f (i + 1)) = f 0 - f M := by
    intro M
    induction M with
    | zero => simp
    | succ M ih => rw [Finset.sum_range_succ, ih]; ring
  simp_rw [e]
  have := (tendsto_const_nhds (x := f 0)).sub hf
  simpa using this

/-- `sum_{n >= 0} 1/(n + N + 1)^2 <= 1/N`. -/
lemma tsum_inv_sq_tail {N : ℕ} (hN : 1 ≤ N) :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + N + 1) ^ 2) ∧ ∑' n : ℕ, 1 / ((n : ℝ) + N + 1) ^ 2 ≤ 1 / (N : ℝ) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set f : ℕ → ℝ := fun n => 1 / ((n : ℝ) + N) with hf
  have hlim : Tendsto f atTop (nhds 0) := by
    have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + N)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    exact (tendsto_inv_atTop_zero.comp h2).congr fun n => by simp [hf]
  have hmono : ∀ n, f (n + 1) ≤ f n := by
    intro n; simp only [hf]; push_cast
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hs := hasSum_telescope f hlim hmono
  have hle : ∀ n : ℕ, 1 / ((n : ℝ) + N + 1) ^ 2 ≤ f n - f (n + 1) := by
    intro n; simp only [hf]; push_cast
    have h1 : (0 : ℝ) < (n : ℝ) + N := by positivity
    rw [div_sub_div _ _ h1.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hnn : ∀ n : ℕ, 0 ≤ 1 / ((n : ℝ) + N + 1) ^ 2 := fun n => by positivity
  have hsum : Summable (fun n : ℕ => 1 / ((n : ℝ) + N + 1) ^ 2) :=
    Summable.of_nonneg_of_le hnn hle hs.summable
  refine ⟨hsum, ?_⟩
  have := hsum.tsum_le_tsum hle hs.summable
  rw [hs.tsum_eq] at this
  simp only [hf, Nat.cast_zero, zero_add] at this
  exact this

/-- `sum_{n >= 0} 1/(n + N + 1)^3 <= 1/(2 N^2)`. -/
lemma tsum_inv_cube_tail {N : ℕ} (hN : 1 ≤ N) :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + N + 1) ^ 3) ∧ ∑' n : ℕ, 1 / ((n : ℝ) + N + 1) ^ 3 ≤ 1 / (2 * (N : ℝ) ^ 2) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set f : ℕ → ℝ := fun n => 1 / (2 * ((n : ℝ) + N) ^ 2) with hf
  have hlim : Tendsto f atTop (nhds 0) := by
    have h3 : Tendsto (fun n : ℕ => ((n : ℝ) + N)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have g := tendsto_inv_atTop_zero.comp h3
    have := (g.pow 2).const_mul (1 / 2)
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at this
    refine this.congr fun n => ?_
    simp only [hf, Function.comp, one_div]
    rw [mul_inv, inv_pow]
  have hmono : ∀ n, f (n + 1) ≤ f n := by
    intro n; simp only [hf]; push_cast
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n), hN']
  have hs := hasSum_telescope f hlim hmono
  have hle : ∀ n : ℕ, 1 / ((n : ℝ) + N + 1) ^ 3 ≤ f n - f (n + 1) := by
    intro n; simp only [hf]; push_cast
    have h1 : (0 : ℝ) < (n : ℝ) + N := by positivity
    set m : ℝ := (n : ℝ) + N with hm
    have hm1 : (1 : ℝ) ≤ m := by rw [hm]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [show (n : ℝ) + 1 + N = m + 1 by rw [hm]; ring]
    rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg m, sq_nonneg (m + 1), mul_pos h1 h1]
  have hnn : ∀ n : ℕ, 0 ≤ 1 / ((n : ℝ) + N + 1) ^ 3 := fun n => by positivity
  have hsum : Summable (fun n : ℕ => 1 / ((n : ℝ) + N + 1) ^ 3) :=
    Summable.of_nonneg_of_le hnn hle hs.summable
  refine ⟨hsum, ?_⟩
  have := hsum.tsum_le_tsum hle hs.summable
  rw [hs.tsum_eq] at this
  simp only [hf, Nat.cast_zero, zero_add] at this
  exact this


/-! ## The digamma majorant on the line `Re s = 3/4`. -/

/-- `psiD r = Re psi(3/4 + i r/2)`, D's archimedean weight. -/
def psiD (r : ℝ) : ℝ := (Complex.digamma (3 / 4 + ((r : ℂ) / 2) * Complex.I)).re

lemma psiD_eq (r : ℝ) :
    psiD r = (Complex.digamma (((3 / 4 : ℝ) : ℂ) + Complex.I * ((r / 2 : ℝ) : ℂ))).re := by
  unfold psiD
  rw [show (3 / 4 : ℂ) + ((r : ℂ) / 2) * Complex.I = ((3 / 4 : ℝ) : ℂ) + Complex.I * ((r / 2 : ℝ) : ℂ) by
    push_cast; ring]

/-- One term of the vertical-line series, bounded by `a/u^2 + t^2/u^3`, `u = m + 1`. -/
lemma serTerm_le (a t : ℝ) (ha : 0 ≤ a) (m : ℕ) :
    1 / ((m : ℝ) + 1) - ((m : ℝ) + 1 + a) / (((m : ℝ) + 1 + a) ^ 2 + t ^ 2)
      ≤ a / ((m : ℝ) + 1) ^ 2 + t ^ 2 / ((m : ℝ) + 1) ^ 3 := by
  set u : ℝ := (m : ℝ) + 1 with hu
  have hu1 : 1 ≤ u := by rw [hu]; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hu0 : 0 < u := by linarith
  set p : ℝ := u + a with hp
  have hpu : u ≤ p := by rw [hp]; linarith
  have hp0 : 0 < p := by linarith
  have hD : 0 < p ^ 2 + t ^ 2 := by positivity
  have e : 1 / u - p / (p ^ 2 + t ^ 2) = (p * a + t ^ 2) / (u * (p ^ 2 + t ^ 2)) := by
    rw [hp]; field_simp; ring
  rw [e]
  have h1 : p * a / (u * (p ^ 2 + t ^ 2)) ≤ a / u ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : p * a * u ^ 2 ≤ a * (u * p ^ 2) := by
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg ha hu0.le) hp0.le) (sub_nonneg.mpr hpu)]
    nlinarith [mul_nonneg ha (sq_nonneg t), mul_nonneg (mul_nonneg ha hu0.le) (sq_nonneg t)]
  have h2 : t ^ 2 / (u * (p ^ 2 + t ^ 2)) ≤ t ^ 2 / u ^ 3 := by
    apply div_le_div_of_nonneg_left (sq_nonneg t) (by positivity)
    have : u ^ 2 ≤ p ^ 2 := by nlinarith
    nlinarith [sq_nonneg t]
  rw [add_div]
  linarith

/-- **The digamma majorant**: `psiD r <= -gamma + H_N - sum_{j<=N} lz(j + 3/4, r) + (3/4)/N + (r/2)^2/(2 N^2)`. -/
theorem psiD_le (r : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    psiD r ≤ -Real.eulerMascheroniConstant + ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + 1)
      - ∑ j ∈ Finset.range (N + 1), lz ((j : ℝ) + 3 / 4) r + (3 / 4) / N + (r / 2) ^ 2 / (2 * (N : ℝ) ^ 2) := by
  set t : ℝ := r / 2 with ht
  rw [psiD_eq, Zeta23.MuFields.re_digamma_vertical (by norm_num) (by norm_num)]
  have hs := Zeta23.MuFields.summable_re_terms (a := 3 / 4) (by norm_num) (by norm_num) t
  rw [← hs.sum_add_tsum_nat_add N]
  obtain ⟨hsq, hsq'⟩ := tsum_inv_sq_tail hN
  obtain ⟨hcu, hcu'⟩ := tsum_inv_cube_tail hN
  have hmaj : Summable (fun n : ℕ => (3 / 4 : ℝ) * (1 / ((n : ℝ) + N + 1) ^ 2) + t ^ 2 * (1 / ((n : ℝ) + N + 1) ^ 3)) :=
    (hsq.mul_left _).add (hcu.mul_left _)
  have hle : ∀ n : ℕ, (1 / (((n + N : ℕ) : ℝ) + 1) - (((n + N : ℕ) : ℝ) + 1 + 3 / 4)
        / ((((n + N : ℕ) : ℝ) + 1 + 3 / 4) ^ 2 + t ^ 2))
      ≤ (3 / 4 : ℝ) * (1 / ((n : ℝ) + N + 1) ^ 2) + t ^ 2 * (1 / ((n : ℝ) + N + 1) ^ 3) := by
    intro n
    have := serTerm_le (3 / 4) t (by norm_num) (n + N)
    push_cast at this ⊢
    calc _ ≤ 3 / 4 / ((n : ℝ) + N + 1) ^ 2 + t ^ 2 / ((n : ℝ) + N + 1) ^ 3 := this
      _ = _ := by ring
  have htail : ∑' n : ℕ, (1 / (((n + N : ℕ) : ℝ) + 1) - (((n + N : ℕ) : ℝ) + 1 + 3 / 4)
        / ((((n + N : ℕ) : ℝ) + 1 + 3 / 4) ^ 2 + t ^ 2))
      ≤ (3 / 4) / N + t ^ 2 / (2 * (N : ℝ) ^ 2) := by
    have h1 := (hs.comp_injective (add_left_injective N)).tsum_le_tsum hle hmaj
    rw [Summable.tsum_add (hsq.mul_left _) (hcu.mul_left _), tsum_mul_left, tsum_mul_left] at h1
    have h2 : (3 / 4 : ℝ) * ∑' n : ℕ, 1 / ((n : ℝ) + N + 1) ^ 2 ≤ (3 / 4) * (1 / N) :=
      mul_le_mul_of_nonneg_left hsq' (by norm_num)
    have h3 : t ^ 2 * ∑' n : ℕ, 1 / ((n : ℝ) + N + 1) ^ 3 ≤ t ^ 2 * (1 / (2 * (N : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hcu' (sq_nonneg t)
    have e1 : (3 / 4 : ℝ) * (1 / N) = (3 / 4) / N := by ring
    have e2 : t ^ 2 * (1 / (2 * (N : ℝ) ^ 2)) = t ^ 2 / (2 * (N : ℝ) ^ 2) := by ring
    try simp only [Function.comp] at h1
    linarith
  have hfin : ∑ n ∈ Finset.range N, (1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + 3 / 4) / (((n : ℝ) + 1 + 3 / 4) ^ 2 + t ^ 2))
      = ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + 1) - ∑ n ∈ Finset.range N, lz ((n : ℝ) + 1 + 3 / 4) r := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold lz; rw [ht]
  have hlz : ∑ j ∈ Finset.range (N + 1), lz ((j : ℝ) + 3 / 4) r
      = ∑ n ∈ Finset.range N, lz ((n : ℝ) + 1 + 3 / 4) r + lz (0 + 3 / 4) r := by
    rw [Finset.sum_range_succ']
    push_cast
    simp only [zero_add]
  have hlz0 : lz (0 + 3 / 4) r = (3 / 4) / ((3 / 4) ^ 2 + t ^ 2) := by unfold lz; rw [ht]; norm_num
  rw [hfin, hlz, hlz0]
  linarith


/-- The `b`-Lorentzian term `int g(y) e^{-2b|y|} dy`, any `b > 0`. -/
def lorTermB (v : ℝ → ℝ) (b : ℝ) : ℝ := ∫ y, acR v y * Real.exp (-2 * b * |y|)

section
variable {A k1 k2 s1 s2 : ℝ} (h : PairHyp A k1 k2 s1 s2) (c1 c2 : ℝ)
include h

/-- The `b`-Lorentzian term of the band test in closed form (any `b > 0`). -/
theorem lorTermB_bandV (b : ℝ) (hb0 : 0 < b) :
    lorTermB (bandV A k1 k2 c1 c2) b
      = c1 ^ 2 * Jd A k1 b + 2 * c1 * c2 * Jx A k1 k2 s1 s2 b + c2 ^ 2 * Jd A k2 b := by
  have hv := bandV_freqData h c1 c2
  have hA := h.A0
  unfold lorTermB
  -- step 1: evenness
  have e1 : (fun y => acR (bandV A k1 k2 c1 c2) y * Real.exp (-2 * b * |y|))
      = fun y => (fun t => acR (bandV A k1 k2 c1 c2) t * Real.exp (-(2 * b) * t)) |y| := by
    funext y
    simp only
    rcases abs_choice y with hy | hy
    · rw [hy]; ring_nf
    · rw [hy, hv.acR_neg]; ring_nf
  rw [e1, integral_comp_abs (f := fun t => acR (bandV A k1 k2 c1 c2) t * Real.exp (-(2 * b) * t))]
  -- step 2: restrict to (0, 2A]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Ioc_subset_Ioi_self : Ioc (0 : ℝ) (2 * A) ⊆ Ioi 0) (fun t ht => by
      simp only [Set.mem_sdiff, mem_Ioi, mem_Ioc, not_and_or, not_le] at ht
      rcases ht.2 with h1 | h1
      · exact absurd ht.1 (not_lt.mpr (le_of_lt (lt_of_le_of_lt (le_refl t) (by linarith))))
      · rw [hv.acR_eq_zero (by rw [abs_of_pos ht.1]; exact h1.le), zero_mul])]
  rw [← intervalIntegral.integral_of_le (by linarith)]
  -- step 3: the closed form on [0, 2A], as a linear combination of six basic integrands
  set E1 : ℝ → ℝ := fun t => Real.exp (-(2 * b) * t) * Real.cos (k1 * t) with hE1
  set Y1 : ℝ → ℝ := fun t => t * (Real.exp (-(2 * b) * t) * Real.cos (k1 * t)) with hY1
  set S1 : ℝ → ℝ := fun t => Real.exp (-(2 * b) * t) * Real.sin (k1 * t) with hS1
  set E2 : ℝ → ℝ := fun t => Real.exp (-(2 * b) * t) * Real.cos (k2 * t) with hE2
  set Y2 : ℝ → ℝ := fun t => t * (Real.exp (-(2 * b) * t) * Real.cos (k2 * t)) with hY2
  set S2 : ℝ → ℝ := fun t => Real.exp (-(2 * b) * t) * Real.sin (k2 * t) with hS2
  have hk1 : k1 ≠ 0 := h.k10.ne'
  have hk2 : k2 ≠ 0 := h.k20.ne'
  have h4 : k1 ^ 2 - k2 ^ 2 ≠ 0 := by
    rw [show k1 ^ 2 - k2 ^ 2 = (k1 - k2) * (k1 + k2) by ring]
    exact mul_ne_zero (by linarith [h.k12]) (by linarith [h.k10, h.k20])
  set a1 : ℝ := c1 ^ 2 * A with ha1
  set a2 : ℝ := -(c1 ^ 2 / 2) with ha2
  set a3 : ℝ := c1 ^ 2 / (2 * k1) - 2 * c1 * c2 * (s1 * s2 / (k1 ^ 2 - k2 ^ 2)) * k2 with ha3
  set a4 : ℝ := c2 ^ 2 * A with ha4
  set a5 : ℝ := -(c2 ^ 2 / 2) with ha5
  set a6 : ℝ := c2 ^ 2 / (2 * k2) + 2 * c1 * c2 * (s1 * s2 / (k1 ^ 2 - k2 ^ 2)) * k1 with ha6
  have hcongr : ∀ t ∈ uIcc (0 : ℝ) (2 * A),
      acR (bandV A k1 k2 c1 c2) t * Real.exp (-(2 * b) * t)
        = a1 * E1 t + a2 * Y1 t + a3 * S1 t + a4 * E2 t + a5 * Y2 t + a6 * S2 t := by
    intro t ht
    rw [uIcc_of_le (by linarith), mem_Icc] at ht
    rw [acR_bandV h c1 c2 ht.1 ht.2]
    simp only [hE1, hY1, hS1, hE2, hY2, hS2, ha1, ha2, ha3, ha4, ha5, ha6]
    unfold gD gX
    field_simp
    ring
  rw [intervalIntegral.integral_congr hcongr]
  have iE : ∀ f : ℝ → ℝ, Continuous f → IntervalIntegrable f volume 0 (2 * A) :=
    fun f hf => hf.intervalIntegrable _ _
  have cE1 : Continuous E1 := by rw [hE1]; fun_prop
  have cY1 : Continuous Y1 := by rw [hY1]; fun_prop
  have cS1 : Continuous S1 := by rw [hS1]; fun_prop
  have cE2 : Continuous E2 := by rw [hE2]; fun_prop
  have cY2 : Continuous Y2 := by rw [hY2]; fun_prop
  have cS2 : Continuous S2 := by rw [hS2]; fun_prop
  have hlin : ∫ t in (0 : ℝ)..(2 * A), (a1 * E1 t + a2 * Y1 t + a3 * S1 t + a4 * E2 t + a5 * Y2 t + a6 * S2 t)
      = a1 * (∫ t in (0 : ℝ)..(2 * A), E1 t) + a2 * (∫ t in (0 : ℝ)..(2 * A), Y1 t)
        + a3 * (∫ t in (0 : ℝ)..(2 * A), S1 t) + a4 * (∫ t in (0 : ℝ)..(2 * A), E2 t)
        + a5 * (∫ t in (0 : ℝ)..(2 * A), Y2 t) + a6 * (∫ t in (0 : ℝ)..(2 * A), S2 t) := by
    rw [intervalIntegral.integral_add (iE _ (by fun_prop)) (iE _ (by fun_prop)),
      intervalIntegral.integral_add (iE _ (by fun_prop)) (iE _ (by fun_prop)),
      intervalIntegral.integral_add (iE _ (by fun_prop)) (iE _ (by fun_prop)),
      intervalIntegral.integral_add (iE _ (by fun_prop)) (iE _ (by fun_prop)),
      intervalIntegral.integral_add (iE _ (by fun_prop)) (iE _ (by fun_prop)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [hlin]
  have hD1 : 0 < (2 * b) ^ 2 + k1 ^ 2 := by positivity
  have hD2 : 0 < (2 * b) ^ 2 + k2 ^ 2 := by positivity
  have ic1 : ∫ t in (0 : ℝ)..(2 * A), E1 t = _ := integral_exp_cos hD1 (cos_two_kA h.cos1) (sin_two_kA h.cos1)
  have ic2 : ∫ t in (0 : ℝ)..(2 * A), E2 t = _ := integral_exp_cos hD2 (cos_two_kA h.cos2) (sin_two_kA h.cos2)
  have is1 : ∫ t in (0 : ℝ)..(2 * A), S1 t = _ := integral_exp_sin hD1 (cos_two_kA h.cos1) (sin_two_kA h.cos1)
  have is2 : ∫ t in (0 : ℝ)..(2 * A), S2 t = _ := integral_exp_sin hD2 (cos_two_kA h.cos2) (sin_two_kA h.cos2)
  have iy1 : ∫ t in (0 : ℝ)..(2 * A), Y1 t = _ := integral_y_exp_cos hD1 (cos_two_kA h.cos1) (sin_two_kA h.cos1)
  have iy2 : ∫ t in (0 : ℝ)..(2 * A), Y2 t = _ := integral_y_exp_cos hD2 (cos_two_kA h.cos2) (sin_two_kA h.cos2)
  rw [ic1, ic2, is1, is2, iy1, iy2]
  simp only [ha1, ha2, ha3, ha4, ha5, ha6]
  unfold Jd Jx
  have e4 : ∀ k : ℝ, 4 * b ^ 2 + k ^ 2 = (2 * b) ^ 2 + k ^ 2 := fun k => by ring
  rw [e4 k1, e4 k2]
  generalize Real.exp (-(2 * b) * (2 * A)) = E
  field_simp
  ring
end

/-! ## Decay of the band transform beyond `2 k2`, and the `r^2` moment. -/

/-- One Dirichlet cosine: `|C_k(r)| <= (8k/3)/r^2` once `r^2 >= 4 k^2`. -/
lemma abs_integral_cos_cos_far {k A s r : ℝ} (hk : 0 < k) (hc : Real.cos (k * A) = 0)
    (hs : Real.sin (k * A) = s) (hs1 : |s| ≤ 1) (hr : 4 * k ^ 2 ≤ r ^ 2) :
    |∫ u in (-A)..A, Real.cos (k * u) * Real.cos (r * u)| ≤ (8 * k / 3) / r ^ 2 := by
  have hk2 : k ^ 2 < r ^ 2 := by nlinarith
  have hkr1 : k - r ≠ 0 := by
    intro h0; have : r = k := by linarith
    rw [this] at hk2; exact lt_irrefl _ hk2
  have hkr2 : k + r ≠ 0 := by
    intro h0; have : r = -k := by linarith
    rw [this, neg_sq] at hk2; exact lt_irrefl _ hk2
  rw [integral_cos_cos_dirichlet hc hs hkr1 hkr2]
  have hden : 0 < r ^ 2 - k ^ 2 := by linarith
  have hr0 : 0 < r ^ 2 := by nlinarith
  rw [abs_div, abs_of_neg (by linarith : k ^ 2 - r ^ 2 < 0), neg_sub]
  have hnum : |2 * s * k * Real.cos (r * A)| ≤ 2 * k := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hk]
    have hc1 := Real.abs_cos_le_one (r * A)
    calc 2 * |s| * k * |Real.cos (r * A)| = 2 * k * (|s| * |Real.cos (r * A)|) := by ring
      _ ≤ 2 * k * 1 := mul_le_mul_of_nonneg_left (mul_le_one₀ hs1 (abs_nonneg _) hc1) (by linarith)
      _ = 2 * k := by ring
  rw [div_le_div_iff₀ hden hr0]
  have : 2 * k * r ^ 2 ≤ (8 * k / 3) * (r ^ 2 - k ^ 2) := by nlinarith
  nlinarith [abs_nonneg (2 * s * k * Real.cos (r * A))]

section
variable {A k1 k2 s1 s2 : ℝ} (h : PairHyp A k1 k2 s1 s2) (c1 c2 : ℝ)
include h

/-- `Fsq(r) <= K'^2/r^4` for `r^2 >= 4 k2^2`, `K' = (8/3)(|c1| k1 + |c2| k2)`. -/
lemma Fsq_bandV_far {r : ℝ} (hr : 4 * k2 ^ 2 ≤ r ^ 2) :
    Fsq (bandV A k1 k2 c1 c2) r ≤ ((8 / 3) * (|c1| * k1 + |c2| * k2)) ^ 2 / r ^ 4 := by
  have hk1r : 4 * k1 ^ 2 ≤ r ^ 2 := by nlinarith [h.k12, h.k10]
  have d1 := abs_integral_cos_cos_far h.k10 h.cos1 h.sin1 h.abs_s1 hk1r
  have d2 := abs_integral_cos_cos_far h.k20 h.cos2 h.sin2 h.abs_s2 hr
  have hr0 : 0 < r ^ 2 := by nlinarith [h.k20]
  unfold Fsq
  rw [paperFT_bandV h c1 c2 r, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  set C1 := ∫ u in (-A)..A, Real.cos (k1 * u) * Real.cos (r * u)
  set C2 := ∫ u in (-A)..A, Real.cos (k2 * u) * Real.cos (r * u)
  have hb : |c1 * C1 + c2 * C2| ≤ (8 / 3) * (|c1| * k1 + |c2| * k2) / r ^ 2 := by
    calc |c1 * C1 + c2 * C2| ≤ |c1| * |C1| + |c2| * |C2| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ |c1| * ((8 * k1 / 3) / r ^ 2) + |c2| * ((8 * k2 / 3) / r ^ 2) := by gcongr
      _ = (8 / 3) * (|c1| * k1 + |c2| * k2) / r ^ 2 := by field_simp
  have h0 : 0 ≤ |c1 * C1 + c2 * C2| := abs_nonneg _
  have := pow_le_pow_left₀ h0 hb 2
  rw [sq_abs] at this
  calc (c1 * C1 + c2 * C2) ^ 2 ≤ ((8 / 3) * (|c1| * k1 + |c2| * k2) / r ^ 2) ^ 2 := this
    _ = ((8 / 3) * (|c1| * k1 + |c2| * k2)) ^ 2 / r ^ 4 := by rw [div_pow]; ring

/-- The pointwise moment bound `Fsq(r) r^2 <= R^2 Fsq(r) + 2 K'^2/(R^2 + r^2)`, `R >= 2 k2`. -/
lemma Fsq_mul_sq_le {R : ℝ} (hR : 2 * k2 ≤ R) (r : ℝ) :
    Fsq (bandV A k1 k2 c1 c2) r * r ^ 2
      ≤ R ^ 2 * Fsq (bandV A k1 k2 c1 c2) r
        + 2 * ((8 / 3) * (|c1| * k1 + |c2| * k2)) ^ 2 * (R ^ 2 + r ^ 2)⁻¹ := by
  have hF0 := Fsq_nonneg (bandV A k1 k2 c1 c2) r
  have hK : 0 ≤ 2 * ((8 / 3) * (|c1| * k1 + |c2| * k2)) ^ 2 * (R ^ 2 + r ^ 2)⁻¹ := by
    have : 0 < R := by linarith [h.k20]
    positivity
  by_cases hr : r ^ 2 ≤ R ^ 2
  · calc Fsq (bandV A k1 k2 c1 c2) r * r ^ 2 = r ^ 2 * Fsq (bandV A k1 k2 c1 c2) r := by ring
      _ ≤ R ^ 2 * Fsq (bandV A k1 k2 c1 c2) r := mul_le_mul_of_nonneg_right hr hF0
      _ ≤ _ := by linarith
  · rw [not_le] at hr
    have hk : 4 * k2 ^ 2 ≤ r ^ 2 := by nlinarith [h.k20]
    have hfar := Fsq_bandV_far h c1 c2 hk
    have hr0 : 0 < r ^ 2 := by nlinarith [h.k20]
    set K := ((8 / 3) * (|c1| * k1 + |c2| * k2)) ^ 2 with hKdef
    have hK0 : 0 ≤ K := by rw [hKdef]; positivity
    have e : Fsq (bandV A k1 k2 c1 c2) r * r ^ 2
        = R ^ 2 * Fsq (bandV A k1 k2 c1 c2) r + (r ^ 2 - R ^ 2) * Fsq (bandV A k1 k2 c1 c2) r := by ring
    rw [e]
    have h1 : (r ^ 2 - R ^ 2) * Fsq (bandV A k1 k2 c1 c2) r ≤ (r ^ 2 - R ^ 2) * (K / r ^ 4) :=
      mul_le_mul_of_nonneg_left hfar (by linarith)
    have h2 : (r ^ 2 - R ^ 2) * (K / r ^ 4) ≤ K / r ^ 2 := by
      have h4 : 0 ≤ K / r ^ 4 := by positivity
      have h5 : (r ^ 2 - R ^ 2) * (K / r ^ 4) ≤ r ^ 2 * (K / r ^ 4) :=
        mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg R]) h4
      have h6 : r ^ 2 * (K / r ^ 4) = K / r ^ 2 := by field_simp
      linarith
    have h3 : K / r ^ 2 ≤ 2 * K * (R ^ 2 + r ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, div_le_div_iff₀ hr0 (by positivity)]
      nlinarith
    linarith

end

/-- `int (R^2 + r^2)^{-1} dr = pi/R`. -/
lemma integral_inv_sq_add_sq {R : ℝ} (hR : 0 < R) : ∫ r : ℝ, (R ^ 2 + r ^ 2)⁻¹ = Real.pi / R := by
  have h := integral_univ_inv_one_add_sq
  have e : (fun r : ℝ => (R ^ 2 + r ^ 2)⁻¹) = fun r => (R ^ 2)⁻¹ * (1 + (R⁻¹ * r) ^ 2)⁻¹ := by
    funext r
    field_simp
  rw [e, integral_const_mul, Measure.integral_comp_mul_left (fun x => (1 + x ^ 2)⁻¹) R⁻¹, h]
  simp only [smul_eq_mul, inv_inv, abs_of_pos hR]
  field_simp

lemma integrable_inv_sq_add_sq {R : ℝ} (hR : 0 < R) : Integrable (fun r : ℝ => (R ^ 2 + r ^ 2)⁻¹) := by
  have h := (integrable_inv_one_add_sq).comp_mul_left' (inv_ne_zero hR.ne')
  have e : (fun r : ℝ => (R ^ 2 + r ^ 2)⁻¹) = fun r => (R ^ 2)⁻¹ * (1 + (R⁻¹ * r) ^ 2)⁻¹ := by
    funext r
    field_simp
  rw [e]
  exact h.const_mul _


/-! ## D's explicit-formula functional (Gamma_R(s+1), conductor 5, no pole). -/

/-- D's archimedean side: `g(0) log(5/pi) + (1/2pi) int h_g(r) Re psi(3/4 + ir/2) dr`. -/
def archSideD (g : ℝ → ℂ) : ℂ :=
  g 0 * (Real.log (5 / Real.pi) : ℂ)
    + (1 / (2 * (Real.pi : ℂ))) * ∫ r : ℝ, WeilExplicit.weilKernel g (1 / 2 + (r : ℂ) * Complex.I) * (psiD r : ℂ)

/-- D's prime side, weighted by the coefficients `w n` of `-D'/D`. -/
def primeSideD (w : ℕ → ℝ) (g : ℝ → ℂ) : ℂ :=
  ∑' n : ℕ, ((w n / Real.sqrt n : ℝ) : ℂ) * (g (Real.log n) + g (-Real.log n))

/-- D's Weil functional (the arithmetic side of D's explicit formula). -/
def weilFormD (w : ℕ → ℝ) (g : ℝ → ℂ) : ℂ := archSideD g - primeSideD w g

lemma psiD_growth : ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, |psiD r| ≤ C * (1 + |r| / 2) := by
  obtain ⟨C, hC0, hC⟩ := Zeta23.WeilEF.digamma_growth_strip
  refine ⟨C, hC0, fun r => ?_⟩
  have hre : (3 / 4 + ((r : ℂ) / 2) * Complex.I).re = 3 / 4 := by simp
  have him : (3 / 4 + ((r : ℂ) / 2) * Complex.I).im = r / 2 := by simp
  have hs := hC (3 / 4 + ((r : ℂ) / 2) * Complex.I) (by rw [hre]; norm_num) (by rw [hre]; norm_num)
  rw [him] at hs
  have hlog : Real.log (2 + |r / 2|) ≤ 1 + |r| / 2 := by
    rw [abs_div, abs_two]
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 + |r| / 2)
    linarith
  calc |psiD r| ≤ ‖Complex.digamma (3 / 4 + ((r : ℂ) / 2) * Complex.I)‖ := Complex.abs_re_le_norm _
    _ ≤ C * Real.log (2 + |r / 2|) := hs
    _ ≤ C * (1 + |r| / 2) := mul_le_mul_of_nonneg_left hlog hC0.le

lemma continuous_psiD : Continuous psiD := by
  unfold psiD
  apply Complex.continuous_re.comp
  refine continuous_iff_continuousAt.mpr fun r => ?_
  have hz : (3 / 4 + ((r : ℂ) / 2) * Complex.I) ∈ Complex.integerComplement := by
    rintro ⟨k, hk⟩
    have := congrArg Complex.re hk
    simp at this
    have h4 : (4 * k : ℤ) = 3 := by exact_mod_cast (by linarith : (4 * (k : ℝ)) = 3)
    omega
  have hf : Continuous (fun r : ℝ => (3 / 4 + ((r : ℂ) / 2) * Complex.I)) := by fun_prop
  exact ContinuousAt.comp (g := Complex.digamma) (f := fun r : ℝ => (3 / 4 + ((r : ℂ) / 2) * Complex.I))
    (Zeta23.Stirling.differentiableAt_digamma hz).continuousAt hf.continuousAt

section
variable {v : ℝ → ℝ} {L K : ℝ} (hv : FreqData v L K)
include hv

lemma FreqData.integrable_Fsq_psiD : Integrable (fun r => Fsq v r * psiD r) := by
  obtain ⟨C, hC0, hC⟩ := psiD_growth
  have hmaj : Integrable (fun r : ℝ => (K ^ 2 * C * (17 / 16)) * (1 + r ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  refine hmaj.mono' (hv.continuous_Fsq.mul continuous_psiD).aestronglyMeasurable (Eventually.of_forall fun r => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Fsq_nonneg v r)]
  have h1 := hv.Fsq_le_sq r
  have h2 := hC r
  have hpos : (0 : ℝ) < 1 + r ^ 2 := by positivity
  have h3 : 1 + |r| / 2 ≤ (17 / 16) * (1 + r ^ 2) := by
    have := sq_nonneg (|r| - 1 / 4)
    rw [sub_sq, sq_abs] at this
    nlinarith [abs_nonneg r]
  calc Fsq v r * |psiD r| ≤ (K ^ 2 / (1 + r ^ 2) ^ 2) * (C * ((17 / 16) * (1 + r ^ 2))) := by
        apply mul_le_mul h1 (h2.trans (mul_le_mul_of_nonneg_left h3 hC0.le)) (abs_nonneg _)
        positivity
    _ = (K ^ 2 * C * (17 / 16)) * (1 + r ^ 2)⁻¹ := by field_simp

/-- `Re archSideD(v * v~) = log(5/pi) g(0) + (1/2pi) int Fsq psiD`. -/
theorem FreqData.archD_re_eq :
    (archSideD (WeilForm.autocorr (fun u => (v u : ℂ)))).re
      = Real.log (5 / Real.pi) * acR v 0 + (1 / (2 * Real.pi)) * ∫ r, Fsq v r * psiD r := by
  set g : ℝ → ℂ := WeilExplicit.autocorr (fun u => (v u : ℂ)) with hgdef
  have hgA : g = fun y => (acR v y : ℂ) := FreqData.acR_eq
  have hint : ∫ r : ℝ, WeilExplicit.weilKernel g (1 / 2 + (r : ℂ) * Complex.I) * (psiD r : ℂ)
      = ((∫ r, Fsq v r * psiD r : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext r
    rw [RvMBridge4.weilKernel_line, hgdef, hv.line r]
    push_cast
    ring
  unfold archSideD
  rw [show WeilForm.autocorr (fun u => (v u : ℂ)) = g from rfl, hint]
  have hg0 : g 0 = (acR v 0 : ℂ) := by rw [hgA]
  rw [hg0]
  have e : (acR v 0 : ℂ) * (Real.log (5 / Real.pi) : ℂ) + (1 / (2 * (Real.pi : ℂ))) * ((∫ r, Fsq v r * psiD r : ℝ) : ℂ)
      = ((Real.log (5 / Real.pi) * acR v 0 + (1 / (2 * Real.pi)) * ∫ r, Fsq v r * psiD r : ℝ) : ℂ) := by
    push_cast; ring
  rw [e, Complex.ofReal_re]

/-- The prime side of D is the finite sum over `n < e^{2L}` (support), for any weights. -/
theorem FreqData.primeD_eq (w : ℕ → ℝ) :
    primeSideD w (WeilForm.autocorr (fun u => (v u : ℂ)))
      = ((∑ n ∈ Finset.range (⌈Real.exp (2 * L)⌉₊ + 1),
          (if Real.log n < 2 * L then 2 * w n / Real.sqrt n * acR v (Real.log n) else 0) : ℝ) : ℂ) := by
  set g : ℝ → ℂ := WeilExplicit.autocorr (fun u => (v u : ℂ)) with hgdef
  have hgA : g = fun y => (acR v y : ℂ) := FreqData.acR_eq
  set N0 : ℕ := ⌈Real.exp (2 * L)⌉₊ + 1 with hN0
  set term : ℕ → ℝ := fun n => if Real.log n < 2 * L then 2 * w n / Real.sqrt n * acR v (Real.log n) else 0
    with hterm
  have hbig : ∀ n : ℕ, n ∉ Finset.range N0 → ¬ Real.log n < 2 * L := by
    intro n hn hlt
    have hn' : N0 ≤ n := by simpa [Finset.mem_range] using hn
    have h1 : Real.exp (2 * L) < (n : ℝ) := by
      have := Nat.le_ceil (Real.exp (2 * L))
      have h2 : ((⌈Real.exp (2 * L)⌉₊ + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn'
      push_cast at h2
      linarith
    have h3 : 2 * L < Real.log n := by
      rw [← Real.log_exp (2 * L)]
      exact Real.log_lt_log (Real.exp_pos _) h1
    linarith
  have hpt : ∀ n : ℕ, ((w n / Real.sqrt n : ℝ) : ℂ) * (g (Real.log n) + g (-Real.log n)) = (term n : ℂ) := by
    intro n
    rw [hterm]
    simp only
    split_ifs with hn
    · rw [hgA]; simp only; rw [hv.acR_neg]; push_cast; ring
    · have h1 : acR v (Real.log n) = 0 := hv.acR_eq_zero ((not_lt.mp hn).trans (le_abs_self _))
      have h2 : acR v (-Real.log n) = 0 :=
        hv.acR_eq_zero (by rw [abs_neg]; exact (not_lt.mp hn).trans (le_abs_self _))
      rw [hgA]; simp only; rw [h1, h2]; simp
  unfold primeSideD
  have hvan : ∀ n ∉ Finset.range N0, term n = 0 := fun n hn => by
    rw [hterm]; simp only; rw [if_neg (hbig n hn)]
  rw [show WeilForm.autocorr (fun u => (v u : ℂ)) = g from rfl, tsum_congr hpt, ← Complex.ofReal_tsum,
    tsum_eq_sum (s := Finset.range N0) hvan]

end


/-! ## D's archimedean side on the band: the Lorentzian upper bound. -/

/-- **Upper bound of D's archimedean side** on the band test, `N` Lorentzians, cutoff `R >= 2 k2`:
`Re archSideD <= log(5/pi) g(0) + (-gamma + H_N + (3/4)/N) g(0) - sum_{j<=N} lorTermB(j + 3/4)
  + (R^2 g(0) + K'^2/R)/(8 N^2)`, `K' = (8/3)(|c1| k1 + |c2| k2)`. -/
theorem archD_band_le (c1 c2 : ℝ) (N : ℕ) (hN : 1 ≤ N) {R : ℝ} (hR : 2 * bk2 ≤ R) :
    (archSideD (WeilForm.autocorr (fun u => ((bandTest c1 c2 u : ℝ) : ℂ)))).re
      ≤ Real.log (5 / Real.pi) * acR (bandTest c1 c2) 0
        + (-Real.eulerMascheroniConstant + ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + 1) + (3 / 4) / N)
            * acR (bandTest c1 c2) 0
        - ∑ j ∈ Finset.range (N + 1), lorTermB (bandTest c1 c2) ((j : ℝ) + 3 / 4)
        + (R ^ 2 * acR (bandTest c1 c2) 0 + ((8 / 3) * (|c1| * bk1 + |c2| * bk2)) ^ 2 / R) / (8 * (N : ℝ) ^ 2) := by
  have h := pairHyp0
  have hv := bandV_freqData h c1 c2
  have hR0 : 0 < R := by linarith [h.k20]
  set v := bandTest c1 c2 with hvdef
  have hvv : v = bandV bandA bk1 bk2 c1 c2 := rfl
  rw [hvv] at *
  set K' : ℝ := (8 / 3) * (|c1| * bk1 + |c2| * bk2) with hK'
  set A0 : ℝ := acR (bandV bandA bk1 bk2 c1 c2) 0 with hA0
  rw [hv.archD_re_eq]
  set c : ℝ := -Real.eulerMascheroniConstant + ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + 1) + (3 / 4) / N with hc
  set F := Fsq (bandV bandA bk1 bk2 c1 c2) with hF
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  -- pointwise majorant
  have hmaj : ∀ r, F r * psiD r ≤ F r * c - ∑ j ∈ Finset.range (N + 1), F r * lz ((j : ℝ) + 3 / 4) r
      + (1 / (8 * (N : ℝ) ^ 2)) * (F r * r ^ 2) := by
    intro r
    have h1 := psiD_le r N hN
    have hF0 := Fsq_nonneg (bandV bandA bk1 bk2 c1 c2) r
    have h2 := mul_le_mul_of_nonneg_left h1 hF0
    rw [← Finset.mul_sum]
    have e : F r * (-Real.eulerMascheroniConstant + ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + 1)
        - ∑ j ∈ Finset.range (N + 1), lz ((j : ℝ) + 3 / 4) r + (3 / 4) / N + (r / 2) ^ 2 / (2 * (N : ℝ) ^ 2))
        = F r * c - F r * ∑ j ∈ Finset.range (N + 1), lz ((j : ℝ) + 3 / 4) r
          + (1 / (8 * (N : ℝ) ^ 2)) * (F r * r ^ 2) := by
      rw [hc]; field_simp; ring_nf
    linarith
  -- integrability
  have hbpos : ∀ j : ℕ, (0 : ℝ) < (j : ℝ) + 3 / 4 := fun j => by positivity
  have hIlz : ∀ j ∈ Finset.range (N + 1), Integrable (fun r => F r * lz ((j : ℝ) + 3 / 4) r) :=
    fun j _ => hv.integrable_Fsq_lz (hbpos j)
  have hIsq : Integrable (fun r => F r * r ^ 2) := by
    have hdom : Integrable (fun r : ℝ => R ^ 2 * F r + 2 * K' ^ 2 * (R ^ 2 + r ^ 2)⁻¹) :=
      (hv.integrable_Fsq.const_mul _).add ((integrable_inv_sq_add_sq hR0).const_mul _)
    refine hdom.mono' (hv.continuous_Fsq.mul (continuous_pow 2)).aestronglyMeasurable (Eventually.of_forall fun r => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Fsq_nonneg _ r) (sq_nonneg r))]
    exact Fsq_mul_sq_le h c1 c2 hR r
  have i3 : Integrable (fun r => F r * c) := hv.integrable_Fsq.mul_const c
  have i4 : Integrable (fun r => ∑ j ∈ Finset.range (N + 1), F r * lz ((j : ℝ) + 3 / 4) r) :=
    integrable_finsetSum _ hIlz
  have i1 : Integrable (fun r => F r * c - ∑ j ∈ Finset.range (N + 1), F r * lz ((j : ℝ) + 3 / 4) r) :=
    i3.sub i4
  have i2 : Integrable (fun r => (1 / (8 * (N : ℝ) ^ 2)) * (F r * r ^ 2)) := hIsq.const_mul _
  have hIR : Integrable (fun r => F r * c - ∑ j ∈ Finset.range (N + 1), F r * lz ((j : ℝ) + 3 / 4) r
      + (1 / (8 * (N : ℝ) ^ 2)) * (F r * r ^ 2)) := i1.add i2
  have hmono := integral_mono hv.integrable_Fsq_psiD hIR hmaj
  have eI : ∫ r, (F r * c - ∑ j ∈ Finset.range (N + 1), F r * lz ((j : ℝ) + 3 / 4) r
      + (1 / (8 * (N : ℝ) ^ 2)) * (F r * r ^ 2))
      = c * (2 * Real.pi * A0) - ∑ j ∈ Finset.range (N + 1), (∫ r, F r * lz ((j : ℝ) + 3 / 4) r)
        + (1 / (8 * (N : ℝ) ^ 2)) * ∫ r, F r * r ^ 2 := by
    rw [integral_add (f := fun r => F r * c - ∑ j ∈ Finset.range (N + 1), F r * lz ((j : ℝ) + 3 / 4) r)
      (g := fun r => (1 / (8 * (N : ℝ) ^ 2)) * (F r * r ^ 2)) i1 i2,
      integral_sub (f := fun r => F r * c) (g := fun r => ∑ j ∈ Finset.range (N + 1), F r * lz ((j : ℝ) + 3 / 4) r) i3 i4,
      integral_finsetSum _ hIlz, integral_mul_const, integral_const_mul, hv.integral_Fsq]
    generalize (∑ j ∈ Finset.range (N + 1), (∫ r, F r * lz ((j : ℝ) + 3 / 4) r)) = S
    generalize (∫ r, F r * r ^ 2) = T
    ring
  rw [eI] at hmono
  have hlz : ∀ j ∈ Finset.range (N + 1), ∫ r, F r * lz ((j : ℝ) + 3 / 4) r
      = 2 * Real.pi * lorTermB (bandV bandA bk1 bk2 c1 c2) ((j : ℝ) + 3 / 4) := by
    intro j _
    unfold lorTermB
    exact integral_mul_lz hv.continuous_acR hv.integrable_acR hv.integrable_Fsq hv.hFT (hbpos j)
  rw [Finset.sum_congr rfl hlz, ← Finset.mul_sum] at hmono
  -- the r^2 moment
  have hsq : ∫ r, F r * r ^ 2 ≤ R ^ 2 * (2 * Real.pi * A0) + 2 * K' ^ 2 * (Real.pi / R) := by
    have hdom : Integrable (fun r : ℝ => R ^ 2 * F r + 2 * K' ^ 2 * (R ^ 2 + r ^ 2)⁻¹) :=
      (hv.integrable_Fsq.const_mul _).add ((integrable_inv_sq_add_sq hR0).const_mul _)
    have := integral_mono hIsq hdom (fun r => Fsq_mul_sq_le h c1 c2 hR r)
    rw [integral_add (hv.integrable_Fsq.const_mul _) ((integrable_inv_sq_add_sq hR0).const_mul _),
      integral_const_mul, integral_const_mul, hv.integral_Fsq, integral_inv_sq_add_sq hR0] at this
    exact this
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hk : (1 / (2 * Real.pi)) * ((1 / (8 * (N : ℝ) ^ 2)) * (R ^ 2 * (2 * Real.pi * A0) + 2 * K' ^ 2 * (Real.pi / R)))
      = (R ^ 2 * A0 + K' ^ 2 / R) / (8 * (N : ℝ) ^ 2) := by
    field_simp
  have hsq' : (1 / (8 * (N : ℝ) ^ 2)) * ∫ r, F r * r ^ 2
      ≤ (1 / (8 * (N : ℝ) ^ 2)) * (R ^ 2 * (2 * Real.pi * A0) + 2 * K' ^ 2 * (Real.pi / R)) :=
    mul_le_mul_of_nonneg_left hsq (by positivity)
  have hfin : (1 / (2 * Real.pi)) * ∫ r, F r * psiD r
      ≤ c * A0 - ∑ j ∈ Finset.range (N + 1), lorTermB (bandV bandA bk1 bk2 c1 c2) ((j : ℝ) + 3 / 4)
        + (R ^ 2 * A0 + K' ^ 2 / R) / (8 * (N : ℝ) ^ 2) := by
    have h2 := mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))
    have h3 := mul_le_mul_of_nonneg_left hsq' (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))
    rw [hk] at h3
    have e : (1 / (2 * Real.pi)) * (c * (2 * Real.pi * A0)
        - 2 * Real.pi * ∑ j ∈ Finset.range (N + 1), lorTermB (bandV bandA bk1 bk2 c1 c2) ((j : ℝ) + 3 / 4)
        + (1 / (8 * (N : ℝ) ^ 2)) * ∫ r, F r * r ^ 2)
        = c * A0 - ∑ j ∈ Finset.range (N + 1), lorTermB (bandV bandA bk1 bk2 c1 c2) ((j : ℝ) + 3 / 4)
          + (1 / (2 * Real.pi)) * ((1 / (8 * (N : ℝ) ^ 2)) * ∫ r, F r * r ^ 2) := by
      generalize (∑ j ∈ Finset.range (N + 1), lorTermB (bandV bandA bk1 bk2 c1 c2) ((j : ℝ) + 3 / 4)) = S
      generalize (∫ r, F r * r ^ 2) = T
      field_simp
    rw [e] at h2
    linarith
  linarith


/-! ## D's prime side: the kappa ball, the prime-log table, and the checker. -/

/-- One D table entry (the weight comes from `dtab n` and the kappa / prime-log balls). -/
structure DEntry where
  lo : ℚ
  hi : ℚ
  q0 : ℚ
  q1 : ℚ
  m1 : ℤ
  m2 : ℤ

def DEntry.toT (E : DEntry) : TEntry := ⟨0, E.lo, E.hi, E.q0, E.q1, E.m1, E.m2⟩

/-- `sqrt 5` and `sqrt(10 - 2 sqrt 5)` between rationals (squares checked by the kernel). -/
def s5lo : ℚ := ((223606797749978969640917366873 : ℚ) / 100000000000000000000000000000)
def s5hi : ℚ := ((2236067977499789696409173668733 : ℚ) / 1000000000000000000000000000000)
def s10lo : ℚ := ((470228201833978503334964763711 : ℚ) / 200000000000000000000000000000)
def s10hi : ℚ := ((1175570504584946258337411909279 : ℚ) / 500000000000000000000000000000)

/-- The prime-log table `log p in [lo, hi]`, `p <= 53`. -/
def lpTab : ℕ → ℚ × ℚ
  | 2 => (((86643397569993 : ℚ) / 125000000000000), ((693147180559947 : ℚ) / 1000000000000000))
  | 3 => (((274653072167027 : ℚ) / 250000000000000), ((1098612288668111 : ℚ) / 1000000000000000))
  | 5 => (((1609437912434099 : ℚ) / 1000000000000000), ((804718956217051 : ℚ) / 500000000000000))
  | 7 => (((121619384315957 : ℚ) / 62500000000000), ((389182029811063 : ℚ) / 200000000000000))
  | 11 => (((2397895272798369 : ℚ) / 1000000000000000), ((599473818199593 : ℚ) / 250000000000000))
  | 13 => (((512989871492307 : ℚ) / 200000000000000), ((1282474678730769 : ℚ) / 500000000000000))
  | 17 => (((566642668811243 : ℚ) / 200000000000000), ((1416606672028109 : ℚ) / 500000000000000))
  | 19 => (((2944438979166439 : ℚ) / 1000000000000000), ((1472219489583221 : ℚ) / 500000000000000))
  | 23 => (((783873553982287 : ℚ) / 250000000000000), ((3135494215929151 : ℚ) / 1000000000000000))
  | 29 => (((3367295829986473 : ℚ) / 1000000000000000), ((841823957496619 : ℚ) / 250000000000000))
  | 31 => (((686797440897029 : ℚ) / 200000000000000), ((858496801121287 : ℚ) / 250000000000000))
  | 37 => (((3610917912644223 : ℚ) / 1000000000000000), ((1805458956322113 : ℚ) / 500000000000000))
  | 41 => (((1856786033352153 : ℚ) / 500000000000000), ((3713572066704309 : ℚ) / 1000000000000000))
  | 43 => (((3761200115693561 : ℚ) / 1000000000000000), ((940300028923391 : ℚ) / 250000000000000))
  | 47 => (((3850147601710057 : ℚ) / 1000000000000000), ((192507380085503 : ℚ) / 50000000000000))
  | 53 => (((99257297838803 : ℚ) / 25000000000000), ((3970291913552123 : ℚ) / 1000000000000000))
  | _ => (0, 0)

/-- The D table entry of `n` (`log n`, `1/sqrt n`, reduction multiples). -/
def dtabE : ℕ → DEntry
  | 2 => ⟨((86643397569993 : ℚ) / 125000000000000), ((693147180559947 : ℚ) / 1000000000000000), ((707106781186547523 : ℚ) / 1000000000000000000), ((353553390593273763 : ℚ) / 500000000000000000), 9, 10⟩
  | 3 => ⟨((274653072167027 : ℚ) / 250000000000000), ((1098612288668111 : ℚ) / 1000000000000000), ((577350269189625763 : ℚ) / 1000000000000000000), ((288675134594812883 : ℚ) / 500000000000000000), 15, 15⟩
  | 4 => ⟨((1386294361119889 : ℚ) / 1000000000000000), ((346573590279973 : ℚ) / 250000000000000), ((499999999999999999 : ℚ) / 1000000000000000000), ((250000000000000001 : ℚ) / 500000000000000000), 19, 19⟩
  | 6 => ⟨((895879734614027 : ℚ) / 500000000000000), ((1791759469228057 : ℚ) / 1000000000000000), ((81649658092772603 : ℚ) / 200000000000000000), ((204124145231931509 : ℚ) / 500000000000000000), 24, 25⟩
  | 7 => ⟨((121619384315957 : ℚ) / 62500000000000), ((389182029811063 : ℚ) / 200000000000000), ((188982236504613613 : ℚ) / 500000000000000000), ((377964473009227229 : ℚ) / 1000000000000000000), 26, 27⟩
  | 8 => ⟨((1039720770839917 : ℚ) / 500000000000000), ((2079441541679837 : ℚ) / 1000000000000000), ((353553390593273761 : ℚ) / 1000000000000000000), ((88388347648318441 : ℚ) / 250000000000000000), 28, 29⟩
  | 9 => ⟨((1098612288668109 : ℚ) / 500000000000000), ((2197224577336221 : ℚ) / 1000000000000000), ((83333333333333333 : ℚ) / 250000000000000000), ((66666666666666667 : ℚ) / 200000000000000000), 30, 30⟩
  | 11 => ⟨((2397895272798369 : ℚ) / 1000000000000000), ((599473818199593 : ℚ) / 250000000000000), ((301511344577763621 : ℚ) / 1000000000000000000), ((37688918072220453 : ℚ) / 125000000000000000), 32, 33⟩
  | 12 => ⟨((2484906649787999 : ℚ) / 1000000000000000), ((1242453324894001 : ℚ) / 500000000000000), ((288675134594812881 : ℚ) / 1000000000000000000), ((72168783648703221 : ℚ) / 250000000000000000), 34, 34⟩
  | 13 => ⟨((512989871492307 : ℚ) / 200000000000000), ((1282474678730769 : ℚ) / 500000000000000), ((1733438113203841 : ℚ) / 6250000000000000), ((277350098112614563 : ℚ) / 1000000000000000000), 35, 35⟩
  | 14 => ⟨((2639057329615257 : ℚ) / 1000000000000000), ((131952866480763 : ℚ) / 50000000000000), ((267261241912424383 : ℚ) / 1000000000000000000), ((133630620956212193 : ℚ) / 500000000000000000), 36, 36⟩
  | 16 => ⟨((138629436111989 : ℚ) / 50000000000000), ((2772588722239783 : ℚ) / 1000000000000000), ((249999999999999999 : ℚ) / 1000000000000000000), ((125000000000000001 : ℚ) / 500000000000000000), 37, 38⟩
  | 17 => ⟨((566642668811243 : ℚ) / 200000000000000), ((1416606672028109 : ℚ) / 500000000000000), ((60633906259083243 : ℚ) / 250000000000000000), ((9701425001453319 : ℚ) / 40000000000000000), 38, 39⟩
  | 18 => ⟨((2890371757896163 : ℚ) / 1000000000000000), ((1445185878948083 : ℚ) / 500000000000000), ((736569563735987 : ℚ) / 3125000000000000), ((235702260395515843 : ℚ) / 1000000000000000000), 39, 40⟩
  | 19 => ⟨((2944438979166439 : ℚ) / 1000000000000000), ((1472219489583221 : ℚ) / 500000000000000), ((57353933467640441 : ℚ) / 250000000000000000), ((229415733870561767 : ℚ) / 1000000000000000000), 40, 40⟩
  | 21 => ⟨((3044522437723421 : ℚ) / 1000000000000000), ((95141326178857 : ℚ) / 31250000000000), ((10910894511799619 : ℚ) / 50000000000000000), ((218217890235992383 : ℚ) / 1000000000000000000), 41, 42⟩
  | 23 => ⟨((783873553982287 : ℚ) / 250000000000000), ((3135494215929151 : ℚ) / 1000000000000000), ((208514414057074761 : ℚ) / 1000000000000000000), ((52128603514268691 : ℚ) / 250000000000000000), 42, 43⟩
  | 24 => ⟨((397256728793493 : ℚ) / 125000000000000), ((3178053830347947 : ℚ) / 1000000000000000), ((204124145231931507 : ℚ) / 1000000000000000000), ((20412414523193151 : ℚ) / 100000000000000000), 43, 44⟩
  | 26 => ⟨((3258096538021481 : ℚ) / 1000000000000000), ((814524134505371 : ℚ) / 250000000000000), ((19611613513818403 : ℚ) / 100000000000000000), ((196116135138184033 : ℚ) / 1000000000000000000), 44, 45⟩
  | 27 => ⟨((411979608250541 : ℚ) / 125000000000000), ((3295836866004331 : ℚ) / 1000000000000000), ((192450089729875253 : ℚ) / 1000000000000000000), ((24056261216234407 : ℚ) / 125000000000000000), 44, 45⟩
  | 28 => ⟨((1666102255087601 : ℚ) / 500000000000000), ((666440902035041 : ℚ) / 200000000000000), ((47245559126153403 : ℚ) / 250000000000000000), ((37796447300922723 : ℚ) / 200000000000000000), 45, 46⟩
  | 29 => ⟨((3367295829986473 : ℚ) / 1000000000000000), ((841823957496619 : ℚ) / 250000000000000), ((92847669088525931 : ℚ) / 500000000000000000), ((37139067635410373 : ℚ) / 200000000000000000), 45, 46⟩
  | 31 => ⟨((686797440897029 : ℚ) / 200000000000000), ((858496801121287 : ℚ) / 250000000000000), ((179605302026774899 : ℚ) / 1000000000000000000), ((89802651013387451 : ℚ) / 500000000000000000), 46, 47⟩
  | 32 => ⟨((138629436111989 : ℚ) / 40000000000000), ((216608493924983 : ℚ) / 62500000000000), ((2209708691207961 : ℚ) / 12500000000000000), ((176776695296636883 : ℚ) / 1000000000000000000), 47, 48⟩
  | 34 => ⟨((22039753278851 : ℚ) / 6250000000000), ((3526360524616163 : ℚ) / 1000000000000000), ((42874646285627209 : ℚ) / 250000000000000000), ((171498585142508839 : ℚ) / 1000000000000000000), 48, 48⟩
  | 36 => ⟨((3583518938456109 : ℚ) / 1000000000000000), ((223969933653507 : ℚ) / 62500000000000), ((33333333333333333 : ℚ) / 200000000000000000), ((41666666666666667 : ℚ) / 250000000000000000), 48, 49⟩
  | 37 => ⟨((3610917912644223 : ℚ) / 1000000000000000), ((1805458956322113 : ℚ) / 500000000000000), ((164398987305357287 : ℚ) / 1000000000000000000), ((16439898730535729 : ℚ) / 100000000000000000), 49, 50⟩
  | 39 => ⟨((732712329225929 : ℚ) / 200000000000000), ((228972602883103 : ℚ) / 62500000000000), ((40032038451271783 : ℚ) / 250000000000000000), ((32025630761017427 : ℚ) / 200000000000000000), 49, 50⟩
  | 41 => ⟨((1856786033352153 : ℚ) / 500000000000000), ((3713572066704309 : ℚ) / 1000000000000000), ((9760860118037879 : ℚ) / 62500000000000000), ((156173761888606067 : ℚ) / 1000000000000000000), 50, 51⟩
  | 42 => ⟨((3737669618283367 : ℚ) / 1000000000000000), ((373766961828337 : ℚ) / 100000000000000), ((154303349962091909 : ℚ) / 1000000000000000000), ((19287918745261489 : ℚ) / 125000000000000000), 50, 51⟩
  | 43 => ⟨((3761200115693561 : ℚ) / 1000000000000000), ((940300028923391 : ℚ) / 250000000000000), ((30499714066520933 : ℚ) / 200000000000000000), ((38124642583151167 : ℚ) / 250000000000000000), 51, 52⟩
  | 46 => ⟨((1914320698244547 : ℚ) / 500000000000000), ((3828641396489097 : ℚ) / 1000000000000000), ((36860489038724283 : ℚ) / 250000000000000000), ((29488391230979427 : ℚ) / 200000000000000000), 52, 53⟩
  | 47 => ⟨((3850147601710057 : ℚ) / 1000000000000000), ((192507380085503 : ℚ) / 50000000000000), ((72932495748947277 : ℚ) / 500000000000000000), ((145864991497894557 : ℚ) / 1000000000000000000), 52, 53⟩
  | 48 => ⟨((3871201010907889 : ℚ) / 1000000000000000), ((967800252726973 : ℚ) / 250000000000000), ((3608439182435161 : ℚ) / 25000000000000000), ((144337567297406443 : ℚ) / 1000000000000000000), 52, 53⟩
  | 49 => ⟨((6226912476977 : ℚ) / 1600000000000), ((972955074527657 : ℚ) / 250000000000000), ((17857142857142857 : ℚ) / 125000000000000000), ((142857142857142859 : ℚ) / 1000000000000000000), 53, 53⟩
  | 51 => ⟨((982956408181081 : ℚ) / 250000000000000), ((3931825632724327 : ℚ) / 1000000000000000), ((140028008402800979 : ℚ) / 1000000000000000000), ((70014004201400491 : ℚ) / 500000000000000000), 53, 54⟩
  | 52 => ⟨((1975621859290713 : ℚ) / 500000000000000), ((3951243718581429 : ℚ) / 1000000000000000), ((138675049056307279 : ℚ) / 1000000000000000000), ((69337524528153641 : ℚ) / 500000000000000000), 53, 54⟩
  | 53 => ⟨((99257297838803 : ℚ) / 25000000000000), ((3970291913552123 : ℚ) / 1000000000000000), ((68680281974344511 : ℚ) / 500000000000000000), ((5494422557947561 : ℚ) / 40000000000000000), 54, 55⟩
  | 54 => ⟨((3988984046564273 : ℚ) / 1000000000000000), ((997246011641069 : ℚ) / 250000000000000), ((136082763487954337 : ℚ) / 1000000000000000000), ((6804138174397717 : ℚ) / 50000000000000000), 54, 55⟩
  | 56 => ⟨((1006337922683787 : ℚ) / 250000000000000), ((4025351690735151 : ℚ) / 1000000000000000), ((133630620956212191 : ℚ) / 1000000000000000000), ((66815310478106097 : ℚ) / 500000000000000000), 54, 55⟩
  | _ => ⟨0, 0, 0, 0, 0, 0⟩

lemma sqrt5_bounds : ((s5lo : ℚ) : ℝ) ≤ Real.sqrt 5 ∧ Real.sqrt 5 ≤ ((s5hi : ℚ) : ℝ) := by
  have h1 : (s5lo : ℚ) ^ 2 ≤ 5 := by unfold s5lo; decide +kernel
  have h2 : (5 : ℚ) ≤ s5hi ^ 2 := by unfold s5hi; decide +kernel
  have h0 : (0 : ℚ) ≤ s5lo := by unfold s5lo; decide +kernel
  have h3 : (0 : ℚ) ≤ s5hi := by unfold s5hi; decide +kernel
  constructor
  · apply Real.le_sqrt_of_sq_le
    exact_mod_cast h1
  · rw [Real.sqrt_le_left (by exact_mod_cast h3)]
    exact_mod_cast h2

lemma sqrt10_bounds : ((s10lo : ℚ) : ℝ) ≤ Real.sqrt (10 - 2 * Real.sqrt 5)
    ∧ Real.sqrt (10 - 2 * Real.sqrt 5) ≤ ((s10hi : ℚ) : ℝ) := by
  obtain ⟨a, b⟩ := sqrt5_bounds
  have h1 : (s10lo : ℚ) ^ 2 ≤ 10 - 2 * s5hi := by unfold s10lo s5hi; decide +kernel
  have h2 : 10 - 2 * s5lo ≤ (s10hi : ℚ) ^ 2 := by unfold s10hi s5lo; decide +kernel
  have h3 : (0 : ℚ) ≤ s10hi := by unfold s10hi; decide +kernel
  have h1R : ((s10lo : ℚ) : ℝ) ^ 2 ≤ 10 - 2 * ((s5hi : ℚ) : ℝ) := by exact_mod_cast h1
  have h2R : 10 - 2 * ((s5lo : ℚ) : ℝ) ≤ ((s10hi : ℚ) : ℝ) ^ 2 := by exact_mod_cast h2
  constructor
  · apply Real.le_sqrt_of_sq_le
    linarith
  · rw [Real.sqrt_le_left (by exact_mod_cast h3)]
    linarith

/-- The kappa ball (rational endpoints; checked from the square-root brackets). -/
def kapLo : ℚ := (s10lo - 2) / (s5hi - 1)
def kapHi : ℚ := (s10hi - 2) / (s5lo - 1)
def kapB : ℚ × ℚ := ((kapLo + kapHi) / 2, (kapHi - kapLo) / 2)

lemma kap_InB : InB kapD kapB.1 kapB.2 := by
  obtain ⟨a5, b5⟩ := sqrt5_bounds
  obtain ⟨a10, b10⟩ := sqrt10_bounds
  have hs5 : (1 : ℚ) < s5lo := by unfold s5lo; decide +kernel
  have hs10 : (2 : ℚ) < s10lo := by unfold s10lo; decide +kernel
  have hs5R : (1 : ℝ) < ((s5lo : ℚ) : ℝ) := by exact_mod_cast hs5
  have hs10R : (2 : ℝ) < ((s10lo : ℚ) : ℝ) := by exact_mod_cast hs10
  apply InB.of_bounds
  · unfold kapLo kapD
    push_cast
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  · unfold kapHi kapD
    push_cast
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith

/-- The prime-log check. -/
def lpOK (p : ℕ) : Bool :=
  decide (0 < p) && decide (|(lpTab p).1 / 8| ≤ 1) && decide (|(lpTab p).2 / 8| ≤ 1) &&
  decide ((expSQ KX ((lpTab p).1 / 8) + expRQ KX ((lpTab p).1 / 8)) ^ 8 ≤ (p : ℚ)) &&
  decide (0 ≤ expSQ KX ((lpTab p).2 / 8) - expRQ KX ((lpTab p).2 / 8)) &&
  decide ((p : ℚ) ≤ (expSQ KX ((lpTab p).2 / 8) - expRQ KX ((lpTab p).2 / 8)) ^ 8)

def lpB (p : ℕ) : ℚ × ℚ := (((lpTab p).1 + (lpTab p).2) / 2, ((lpTab p).2 - (lpTab p).1) / 2)

lemma lp_InB {p : ℕ} (h : lpOK p = true) : InB (Real.log p) (lpB p).1 (lpB p).2 := by
  unfold lpOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hp, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact InB.of_bounds (le_log_of KX (by unfold KX; norm_num) p hp h1 h3)
    (log_le_of KX (by unfold KX; norm_num) p hp h2 h4 h5)

/-- Horner ball of a rational polynomial at a ball. -/
def polyBall : List ℚ → ℚ × ℚ → ℚ × ℚ
  | [], _ => (0, 0)
  | q :: qs, xB => bAdd (q, 0) (bMul xB (polyBall qs xB))

lemma polyBall_sound {x : ℝ} {xB : ℚ × ℚ} (hx : InB x xB.1 xB.2) :
    ∀ l : List ℚ, InB (polyEval l x) (polyBall l xB).1 (polyBall l xB).2
  | [] => by simp [polyEval, polyBall, InB]
  | q :: qs => by
    have h0 : InB (q : ℝ) ((q, (0 : ℚ)) : ℚ × ℚ).1 ((q, (0 : ℚ)) : ℚ × ℚ).2 := by simp [InB]
    have := InB.bAdd h0 (hx.bMul (polyBall_sound hx qs))
    exact this

/-- The ball of `cDexpr l = sum_p (poly_p kappa) log p`. -/
def cdBall : List (ℕ × List ℚ) → ℚ × ℚ
  | [] => (0, 0)
  | t :: ts => bAdd (bMul (polyBall t.2 kapB) (lpB t.1)) (cdBall ts)

lemma cdBall_sound : ∀ l : List (ℕ × List ℚ), (∀ t ∈ l, lpOK t.1 = true) →
    InB (cDexpr l) (cdBall l).1 (cdBall l).2
  | [], _ => by simp [cDexpr, cdBall, InB]
  | t :: ts, h => by
    have ht := h t (List.mem_cons_self)
    have hts : ∀ u ∈ ts, lpOK u.1 = true := fun u hu => h u (List.mem_cons_of_mem _ hu)
    have := ((polyBall_sound kap_InB t.2).bMul (lp_InB ht)).bAdd (cdBall_sound ts hts)
    simpa [cDexpr, cdBall] using this

/-- The D weight ball `2 cD(n)/sqrt n`. -/
def wDB (n : ℕ) (E : DEntry) : ℚ × ℚ := bMul (bC 2 (cdBall (dtab n))) (sB E.toT)

/-- The D entry check. -/
def dEntryOK (P : BandP) (n : ℕ) (E : DEntry) : Bool :=
  (dtab n).isEmpty ||
  (decide (0 < n) && decide (|E.lo / 8| ≤ 1) && decide (|E.hi / 8| ≤ 1) &&
   decide ((expSQ KX (E.lo / 8) + expRQ KX (E.lo / 8)) ^ 8 ≤ (n : ℚ)) &&
   decide (0 ≤ expSQ KX (E.hi / 8) - expRQ KX (E.hi / 8)) &&
   decide ((n : ℚ) ≤ (expSQ KX (E.hi / 8) - expRQ KX (E.hi / 8)) ^ 8) &&
   decide (0 ≤ E.q0) && decide (E.q0 ^ 2 * n ≤ 1) && decide (1 ≤ E.q1 ^ 2 * n) && decide (0 ≤ E.q1) &&
   decide (|(phiB P.k1 E.toT E.m1).1| ≤ ((2 * MT + 1 : ℕ) : ℚ) / 2) &&
   decide (|(phiB P.k2 E.toT E.m2).1| ≤ ((2 * MT + 1 : ℕ) : ℚ) / 2) &&
   decide (E.hi < 2 * P.Q * PLOq) && (dtab n).all (fun t => lpOK t.1))

/-- The three output balls of a D entry. -/
def dOutB (P : BandP) (n : ℕ) (E : DEntry) : (ℚ × ℚ) × (ℚ × ℚ) × (ℚ × ℚ) :=
  if (dtab n).isEmpty then ((0, 0), (0, 0), (0, 0))
  else (bRound (bMul (wDB n E) (gD1B P E.toT)) RT, bRound (bMul (wDB n E) (gD2B P E.toT)) RT,
    bRound (bMul (wDB n E) (gXB P E.toT)) RT)

/-- **Soundness of one D entry.** -/
theorem dEntry_sound (P : BandP) (hQ : 0 ≤ P.Q) (n : ℕ) (E : DEntry) (hok : dEntryOK P n E = true) :
    InB (2 * cD n / Real.sqrt n * gDr ((P.Q : ℝ) * Real.pi) P.k1 (Real.log n)) (dOutB P n E).1.1 (dOutB P n E).1.2
      ∧ InB (2 * cD n / Real.sqrt n * gDr ((P.Q : ℝ) * Real.pi) P.k2 (Real.log n))
        (dOutB P n E).2.1.1 (dOutB P n E).2.1.2
      ∧ InB (2 * cD n / Real.sqrt n * gXr P.k1 P.k2 P.s12 (Real.log n)) (dOutB P n E).2.2.1 (dOutB P n E).2.2.2
      ∧ (dtab n ≠ [] → Real.log n < 2 * ((P.Q : ℝ) * Real.pi)) := by
  by_cases he : (dtab n).isEmpty = true
  · have hnil : dtab n = [] := List.isEmpty_iff.mp he
    have hc : cD n = 0 := by simp [cD, cDexpr, hnil]
    simp only [dOutB, he, if_true, hc]
    refine ⟨?_, ?_, ?_, fun h => absurd hnil h⟩ <;> simp [InB]
  · have hok' := hok
    unfold dEntryOK at hok'
    simp only [he, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hok'
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hn, hlo8⟩, hhi8⟩, hexp1⟩, hexp2⟩, hexp3⟩, hq0⟩, hq01⟩, hq11⟩, hq1⟩, hph1⟩, hph2⟩, hA⟩,
      hlp⟩ := hok'
    have he' : (dtab n).isEmpty = false := by simpa using he
    simp only [dOutB, he']
    set E' := E.toT with hE'
    have hy : InB (Real.log n) (yB E').1 (yB E').2 := by
      apply InB.of_bounds
      · exact le_log_of KX (by unfold KX; norm_num) n hn hlo8 hexp1
      · exact log_le_of KX (by unfold KX; norm_num) n hn hhi8 hexp2 hexp3
    have hs : InB (1 / Real.sqrt n) (sB E').1 (sB E').2 := by
      obtain ⟨a, b⟩ := inv_sqrt_between hn hq0 hq01 hq11 hq1
      exact InB.of_bounds a b
    have hpi : InB Real.pi piB.1 piB.2 := pi_InB
    have hcd : InB (cD n) (cdBall (dtab n)).1 (cdBall (dtab n)).2 := by
      unfold cD
      exact cdBall_sound (dtab n) (fun t ht => by
        rw [List.all_eq_true] at hlp
        exact hlp t ht)
    have hw : InB (2 * cD n / Real.sqrt n) (wDB n E).1 (wDB n E).2 := by
      have := (hcd.bC 2).bMul hs
      refine this.of_eq ?_
      push_cast; ring
    have hphi : ∀ (k : ℚ) (m : ℤ), InB ((k : ℝ) * Real.log n - m * (2 * Real.pi)) (phiB k E' m).1 (phiB k E' m).2 := by
      intro k m
      have := ((hy.bC k).bSub (hpi.bC (2 * m))).bRound RD
      refine this.of_eq ?_
      push_cast; ring
    have hc : ∀ (k : ℚ) (m : ℤ), |(phiB k E' m).1| ≤ ((2 * MT + 1 : ℕ) : ℚ) / 2 →
        InB (Real.cos ((k : ℝ) * Real.log n)) (cosB (phiB k E' m)).1 (cosB (phiB k E' m)).2 := by
      intro k m hm
      have := InB.cos_of MT m (hphi k m) hm
      unfold cosB
      refine this.mono (le_of_eq ?_)
      ring
    have hsn : ∀ (k : ℚ) (m : ℤ), |(phiB k E' m).1| ≤ ((2 * MT + 1 : ℕ) : ℚ) / 2 →
        InB (Real.sin ((k : ℝ) * Real.log n)) (sinB (phiB k E' m)).1 (sinB (phiB k E' m)).2 := by
      intro k m hm
      have hm' : |(phiB k E' m).1| ≤ ((2 * MT + 1 + 1 : ℕ) : ℚ) / 2 := by
        refine hm.trans ?_
        push_cast
        linarith
      have := InB.sin_of MT m (hphi k m) hm'
      unfold sinB
      refine this.mono (le_of_eq ?_)
      ring
    have htA : InB (2 * ((P.Q : ℝ) * Real.pi) - Real.log n) (tAyB P E').1 (tAyB P E').2 := by
      have := ((hpi.bC P.Q).bC 2).bSub hy
      refine this.of_eq ?_
      push_cast; ring
    have hm1 : E'.m1 = E.m1 := rfl
    have hm2 : E'.m2 = E.m2 := rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hg : InB (gDr ((P.Q : ℝ) * Real.pi) P.k1 (Real.log n)) (gD1B P E').1 (gD1B P E').2 := by
        have := ((htA.bMul (hc P.k1 E'.m1 hph1)).bC (1 / 2)).bAdd ((hsn P.k1 E'.m1 hph1).bC (1 / (2 * P.k1)))
        refine this.of_eq ?_
        unfold gDr; push_cast; ring
      exact (hw.bMul hg).bRound RT
    · have hg : InB (gDr ((P.Q : ℝ) * Real.pi) P.k2 (Real.log n)) (gD2B P E').1 (gD2B P E').2 := by
        have := ((htA.bMul (hc P.k2 E'.m2 hph2)).bC (1 / 2)).bAdd ((hsn P.k2 E'.m2 hph2).bC (1 / (2 * P.k2)))
        refine this.of_eq ?_
        unfold gDr; push_cast; ring
      exact (hw.bMul hg).bRound RT
    · have hg : InB (gXr P.k1 P.k2 P.s12 (Real.log n)) (gXB P E').1 (gXB P E').2 := by
        have := (((hsn P.k2 E'.m2 hph2).bC P.k1).bSub ((hsn P.k1 E'.m1 hph1).bC P.k2)).bC
          (P.s12 / (P.k1 ^ 2 - P.k2 ^ 2))
        refine this.of_eq ?_
        unfold gXr; push_cast; ring
      exact (hw.bMul hg).bRound RT
    · intro _
      have h1 := hy.le
      have h2 : ((E'.lo + E'.hi) / 2 + (E'.hi - E'.lo) / 2 : ℚ) = E'.hi := by ring
      unfold yB at h1
      simp only at h1
      rw [h2] at h1
      have h3 : ((E.hi : ℚ) : ℝ) < ((2 * P.Q * PLOq : ℚ) : ℝ) := by exact_mod_cast hA
      have h4 := Real.pi_gt_d20
      push_cast at h3
      have hPL : (PLOq : ℝ) ≤ Real.pi := by unfold PLOq; push_cast; linarith
      have hQR : (0 : ℝ) ≤ P.Q := by exact_mod_cast hQ
      have h5 : 2 * (P.Q : ℝ) * PLOq ≤ 2 * ((P.Q : ℝ) * Real.pi) := by nlinarith
      have h6 : E'.hi = E.hi := rfl
      rw [h6] at h1
      linarith

set_option maxRecDepth 100000 in
theorem dtab_ok : (List.range 57).all (fun n => dEntryOK P0 n (dtabE n)) = true := by decide +kernel

/-- Negative control: shifting one log enclosure up by `10^-3` is rejected by the checker. -/
theorem dtab_tamper :
    dEntryOK P0 7 ⟨(dtabE 7).lo + 1 / 1000, (dtabE 7).hi + 1 / 1000, (dtabE 7).q0, (dtabE 7).q1,
      (dtabE 7).m1, (dtabE 7).m2⟩ = false := by
  decide +kernel


/-! ## The D certificate at `c* = (-3, 2)`: the prime side. -/

/-- The three D prime sums of the band. -/
def PD11 : ℝ := ∑ n ∈ Finset.range 57, 2 * cD n / Real.sqrt n * gD bandA bk1 (Real.log n)
def PD22 : ℝ := ∑ n ∈ Finset.range 57, 2 * cD n / Real.sqrt n * gD bandA bk2 (Real.log n)
def PD12 : ℝ := ∑ n ∈ Finset.range 57, 2 * cD n / Real.sqrt n * gXr bk1 bk2 (-1) (Real.log n)

lemma dEntry_ok (n : ℕ) (hn : n < 57) : dEntryOK P0 n (dtabE n) = true := by
  have h := dtab_ok
  rw [List.all_eq_true] at h
  exact h n (List.mem_range.mpr hn)

lemma dEntry_sound0 (n : ℕ) (hn : n < 57) :
    InB (2 * cD n / Real.sqrt n * gD bandA bk1 (Real.log n))
        (dOutB P0 n (dtabE n)).1.1 (dOutB P0 n (dtabE n)).1.2
      ∧ InB (2 * cD n / Real.sqrt n * gD bandA bk2 (Real.log n))
        (dOutB P0 n (dtabE n)).2.1.1 (dOutB P0 n (dtabE n)).2.1.2
      ∧ InB (2 * cD n / Real.sqrt n * gXr bk1 bk2 (-1) (Real.log n))
        (dOutB P0 n (dtabE n)).2.2.1 (dOutB P0 n (dtabE n)).2.2.2
      ∧ (dtab n ≠ [] → Real.log n < 2 * bandA) := by
  have h := dEntry_sound P0 (by unfold P0; norm_num) n (dtabE n) (dEntry_ok n hn)
  obtain ⟨hQ, hk1, hk2, hs⟩ := P0_cast
  rw [hQ, hk1, hk2, hs] at h
  have e : ∀ A k y : ℝ, gDr A k y = gD A k y := fun _ _ _ => rfl
  simp only [e] at h
  exact h

theorem PD_balls :
    InB PD11 (∑ n ∈ Finset.range 57, (dOutB P0 n (dtabE n)).1.1) (∑ n ∈ Finset.range 57, (dOutB P0 n (dtabE n)).1.2)
      ∧ InB PD22 (∑ n ∈ Finset.range 57, (dOutB P0 n (dtabE n)).2.1.1)
        (∑ n ∈ Finset.range 57, (dOutB P0 n (dtabE n)).2.1.2)
      ∧ InB PD12 (∑ n ∈ Finset.range 57, (dOutB P0 n (dtabE n)).2.2.1)
        (∑ n ∈ Finset.range 57, (dOutB P0 n (dtabE n)).2.2.2) := by
  refine ⟨?_, ?_, ?_⟩
  · exact InB.sum _ _ _ _ fun n hn => (dEntry_sound0 n (Finset.mem_range.mp hn)).1
  · exact InB.sum _ _ _ _ fun n hn => (dEntry_sound0 n (Finset.mem_range.mp hn)).2.1
  · exact InB.sum _ _ _ _ fun n hn => (dEntry_sound0 n (Finset.mem_range.mp hn)).2.2.1

theorem q_PD11 : 4937230859 / 10 ^ 9 ≤
    (∑ n ∈ Finset.range 57, (dOutB P0 n (dtabE n)).1.1) - (∑ n ∈ Finset.range 57, (dOutB P0 n (dtabE n)).1.2) := by
  decide +kernel
theorem q_PD22 : -1239492161 / 10 ^ 9 ≤
    (∑ n ∈ Finset.range 57, (dOutB P0 n (dtabE n)).2.1.1)
      - (∑ n ∈ Finset.range 57, (dOutB P0 n (dtabE n)).2.1.2) := by
  decide +kernel
theorem q_PD12 : (∑ n ∈ Finset.range 57, (dOutB P0 n (dtabE n)).2.2.1)
      + (∑ n ∈ Finset.range 57, (dOutB P0 n (dtabE n)).2.2.2) ≤ -7350119194 / 10 ^ 9 := by
  decide +kernel

lemma PD_bounds : 4937230859 / 10 ^ 9 ≤ PD11 ∧ -1239492161 / 10 ^ 9 ≤ PD22 ∧ PD12 ≤ -7350119194 / 10 ^ 9 := by
  obtain ⟨hP11, hP22, hP12⟩ := PD_balls
  have a1 := hP11.ge
  have a2 := hP22.ge
  have a3 := hP12.le
  have q1 := Rat.cast_le (K := ℝ) |>.mpr q_PD11
  have q2 := Rat.cast_le (K := ℝ) |>.mpr q_PD22
  have q3 := Rat.cast_le (K := ℝ) |>.mpr q_PD12
  push_cast at a1 a2 a3 q1 q2 q3
  refine ⟨by linarith, by linarith, by linarith⟩

/-- The defining identity at `n = 1` forces `w 1 = 0` (`a(1) = 1`, `log 1 = 0`). -/
lemma w_one_of_conv (w : ℕ → ℝ)
    (hw : ∀ n : ℕ, 1 ≤ n → n ≤ 56 → aD n * Real.log n = ∑ d ∈ n.divisors, w d * aD (n / d)) : w 1 = 0 := by
  have h := hw 1 le_rfl (by norm_num)
  rw [Nat.divisors_one, Finset.sum_singleton, Nat.div_self (by norm_num), aD_one, Nat.cast_one, Real.log_one,
    mul_zero, mul_one] at h
  exact h.symm

/-- D's prime sum on the band, for ANY weights `w` obeying the defining identity of `-D'/D` on `[1, 56]`. -/
lemma dh_prime_sum (w : ℕ → ℝ)
    (hw : ∀ n : ℕ, 1 ≤ n → n ≤ 56 → aD n * Real.log n = ∑ d ∈ n.divisors, w d * aD (n / d)) (c1 c2 : ℝ) :
    ∑ n ∈ Finset.range (⌈Real.exp (2 * bandA)⌉₊ + 1),
        (if Real.log n < 2 * bandA then
          2 * w n / Real.sqrt n * acR (bandV bandA bk1 bk2 c1 c2) (Real.log n) else 0)
      = c1 ^ 2 * PD11 + 2 * c1 * c2 * PD12 + c2 ^ 2 * PD22 := by
  have h := pairHyp0
  have hwc := eq_cD_of_conv w (w_one_of_conv w hw) hw
  set f : ℕ → ℝ := fun n => if Real.log n < 2 * bandA then
      2 * w n / Real.sqrt n * acR (bandV bandA bk1 bk2 c1 c2) (Real.log n) else 0
    with hf
  have hfN0 : ∀ n, ⌈Real.exp (2 * bandA)⌉₊ + 1 ≤ n → f n = 0 := by
    intro n hn
    rw [hf]; simp only
    rw [if_neg]
    intro hlt
    have h1 : Real.exp (2 * bandA) < (n : ℝ) := by
      have := Nat.le_ceil (Real.exp (2 * bandA))
      have h2 : ((⌈Real.exp (2 * bandA)⌉₊ + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      push_cast at h2
      linarith
    have h3 : 2 * bandA < Real.log n := by
      rw [← Real.log_exp (2 * bandA)]
      exact Real.log_lt_log (Real.exp_pos _) h1
    linarith
  have hf57 : ∀ n, 57 ≤ n → f n = 0 := by
    intro n hn
    rw [hf]; simp only
    rw [if_neg]
    intro hlt
    have h1 : Real.log 57 ≤ Real.log n :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    linarith [twoA_lt_log57]
  have hterm : ∀ n ∈ Finset.range 57, f n
      = c1 ^ 2 * (2 * cD n / Real.sqrt n * gD bandA bk1 (Real.log n))
        + 2 * c1 * c2 * (2 * cD n / Real.sqrt n * gXr bk1 bk2 (-1) (Real.log n))
        + c2 ^ 2 * (2 * cD n / Real.sqrt n * gD bandA bk2 (Real.log n)) := by
    intro n hn
    have hn' := Finset.mem_range.mp hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      rw [hf]; simp
    · have hwn : w n = cD n := hwc n hpos (by omega)
      by_cases hd : dtab n = []
      · have hc : cD n = 0 := by simp [cD, cDexpr, hd]
        rw [hf]; simp only; rw [hwn, hc]; simp
      · have hlt := (dEntry_sound0 n hn').2.2.2 hd
        rw [hf]; simp only; rw [if_pos hlt, hwn]
        rw [acR_bandV h c1 c2 (Real.log_natCast_nonneg n) hlt.le, gX_eq]
        ring
  rw [sum_range_eq_of_vanish f _ _ hfN0 hf57, Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  rfl

lemma bandTest_norm (c1 c2 : ℝ) :
    ∫ x, ‖((bandTest c1 c2 x : ℝ) : ℂ)‖ ^ 2 = bandA * (c1 ^ 2 + c2 ^ 2) := by
  rw [← acR_bandV_zero pairHyp0 c1 c2]
  unfold acR bandTest
  congr 1
  funext x
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, sub_zero, sq]

/-- **D's band comb at `c* = (-3, 2)`**: D's prime side on the band test is at least `4.86 ||v||^2`
(computed: 4.863), for any weights `w` given by the defining identity of `-D'/D` on `[1, 56]`. -/
theorem dh_band_comb_ge (w : ℕ → ℝ)
    (hw : ∀ n : ℕ, 1 ≤ n → n ≤ 56 → aD n * Real.log n = ∑ d ∈ n.divisors, w d * aD (n / d)) :
    (486 / 100 : ℝ) * (∫ x, ‖((bandTest (-3) 2 x : ℝ) : ℂ)‖ ^ 2)
      ≤ (primeSideD w (WeilForm.autocorr (fun u => ((bandTest (-3) 2 u : ℝ) : ℂ)))).re := by
  have hv := bandV_freqData pairHyp0 (-3) 2
  have hp := hv.primeD_eq w
  rw [bandTest_norm]
  unfold bandTest
  rw [hp, Complex.ofReal_re, dh_prime_sum w hw (-3) 2]
  obtain ⟨hA1, hA2⟩ := bandA_bounds
  obtain ⟨p1, p2, p3⟩ := PD_bounds
  nlinarith

/-! ## The D certificate at `c* = (-3, 2)`: the archimedean side. -/

theorem q_H300 : ∑ n ∈ Finset.range 300, (1 : ℚ) / ((n : ℚ) + 1) ≤ 3141331941 / 500000000 := by
  decide +kernel
theorem q_DS1a : (492715841 / 250000000 : ℚ)
    ≤ ∑ j ∈ Finset.range 301, 4 * ((j : ℚ) + 3 / 4) / (4 * ((j : ℚ) + 3 / 4) ^ 2 + (763 / 9) ^ 2) := by
  decide +kernel
theorem q_DS1b : (1953040213 / 10 ^ 9 : ℚ)
    ≤ ∑ j ∈ Finset.range 301, 4 * ((j : ℚ) + 3 / 4) / (4 * ((j : ℚ) + 3 / 4) ^ 2 + (259 / 3) ^ 2) := by
  decide +kernel
theorem q_DS2a : (4591963 / 500000000 : ℚ)
    ≤ ∑ j ∈ Finset.range 301, 2 * (763 / 9 : ℚ) ^ 2 / (4 * ((j : ℚ) + 3 / 4) ^ 2 + (763 / 9) ^ 2) ^ 2 := by
  decide +kernel
theorem q_DS2b : (9019101 / 10 ^ 9 : ℚ)
    ≤ ∑ j ∈ Finset.range 301, 2 * (259 / 3 : ℚ) ^ 2 / (4 * ((j : ℚ) + 3 / 4) ^ 2 + (259 / 3) ^ 2) ^ 2 := by
  decide +kernel
theorem q_DSx : (284399 / 31250000 : ℚ) ≤ ∑ j ∈ Finset.range 301, 2 * (763 / 9 : ℚ) * (259 / 3)
      / ((4 * ((j : ℚ) + 3 / 4) ^ 2 + (763 / 9) ^ 2) * (4 * ((j : ℚ) + 3 / 4) ^ 2 + (259 / 3) ^ 2)) := by
  decide +kernel

lemma Jd_ge {A k b : ℝ} :
    A * (4 * b / (4 * b ^ 2 + k ^ 2)) + 2 * k ^ 2 / (4 * b ^ 2 + k ^ 2) ^ 2 ≤ Jd A k b := by
  unfold Jd
  have hE : 0 ≤ Real.exp (-(2 * b) * (2 * A)) := (Real.exp_pos _).le
  have h1 : 2 * A * (2 * b) / (4 * b ^ 2 + k ^ 2) = A * (4 * b / (4 * b ^ 2 + k ^ 2)) := by ring
  have h2 : 2 * k ^ 2 / (4 * b ^ 2 + k ^ 2) ^ 2
      ≤ 2 * k ^ 2 * (1 + Real.exp (-(2 * b) * (2 * A))) / (4 * b ^ 2 + k ^ 2) ^ 2 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [sq_nonneg k]
  linarith

/-- The Lorentzian sums of D's majorant, `N = 300`, `b = j + 3/4`. -/
def DSJ1 : ℝ := ∑ j ∈ Finset.range (300 + 1), Jd bandA bk1 ((j : ℝ) + 3 / 4)
def DSJ2 : ℝ := ∑ j ∈ Finset.range (300 + 1), Jd bandA bk2 ((j : ℝ) + 3 / 4)
def DSJx : ℝ := ∑ j ∈ Finset.range (300 + 1), Jx bandA bk1 bk2 1 (-1) ((j : ℝ) + 3 / 4)

lemma DSJ1_ge : bandA * (492715841 / 250000000) + 4591963 / 500000000 ≤ DSJ1 := by
  have hA0 : 0 < bandA := pairHyp0.A0
  have hq1 := Rat.cast_le (K := ℝ) |>.mpr q_DS1a
  have hq2 := Rat.cast_le (K := ℝ) |>.mpr q_DS2a
  push_cast at hq1 hq2
  have hle : ∑ j ∈ Finset.range 301, (bandA * (4 * ((j : ℝ) + 3 / 4) / (4 * ((j : ℝ) + 3 / 4) ^ 2 + bk1 ^ 2))
      + 2 * bk1 ^ 2 / (4 * ((j : ℝ) + 3 / 4) ^ 2 + bk1 ^ 2) ^ 2) ≤ DSJ1 :=
    Finset.sum_le_sum fun j _ => Jd_ge
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hle
  unfold bk1 at hle
  have := mul_le_mul_of_nonneg_left hq1 hA0.le
  linarith

lemma DSJ2_ge : bandA * (1953040213 / 10 ^ 9) + 9019101 / 10 ^ 9 ≤ DSJ2 := by
  have hA0 : 0 < bandA := pairHyp0.A0
  have hq1 := Rat.cast_le (K := ℝ) |>.mpr q_DS1b
  have hq2 := Rat.cast_le (K := ℝ) |>.mpr q_DS2b
  push_cast at hq1 hq2
  have hle : ∑ j ∈ Finset.range 301, (bandA * (4 * ((j : ℝ) + 3 / 4) / (4 * ((j : ℝ) + 3 / 4) ^ 2 + bk2 ^ 2))
      + 2 * bk2 ^ 2 / (4 * ((j : ℝ) + 3 / 4) ^ 2 + bk2 ^ 2) ^ 2) ≤ DSJ2 :=
    Finset.sum_le_sum fun j _ => Jd_ge
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hle
  unfold bk2 at hle
  have := mul_le_mul_of_nonneg_left hq1 hA0.le
  linarith

lemma DSJx_le : DSJx ≤ -(284399 / 31250000) := by
  have hA0 : 0 < bandA := pairHyp0.A0
  have hk1 : (0 : ℝ) < bk1 := pairHyp0.k10
  have hk2 : (0 : ℝ) < bk2 := pairHyp0.k20
  have hx := Rat.cast_le (K := ℝ) |>.mpr q_DSx
  push_cast at hx
  have hhi : DSJx ≤ ∑ j ∈ Finset.range 301, -(2 * bk1 * bk2 / ((4 * ((j : ℝ) + 3 / 4) ^ 2 + bk1 ^ 2)
        * (4 * ((j : ℝ) + 3 / 4) ^ 2 + bk2 ^ 2))) :=
    Finset.sum_le_sum fun j _ => (Jx_bounds hA0.le (by positivity) hk1 hk2).2
  rw [Finset.sum_neg_distrib] at hhi
  unfold bk1 bk2 at hhi
  linarith

/-- `log pi >= 1.1447` (from `e^{1.1447} <= 3.14159... <= pi`). -/
lemma log_pi_ge' : (11447 / 10000 : ℝ) ≤ Real.log Real.pi := by
  have hq : |((11447 / 10000 : ℚ)) / 8| ≤ 1 := by norm_num
  have h := exp_near KX (by unfold KX; norm_num) hq
  have hc : (expSQ KX ((11447 / 10000 : ℚ) / 8) + expRQ KX ((11447 / 10000 : ℚ) / 8)) ^ 8 ≤ PLOq := by
    unfold KX PLOq; decide +kernel
  have hup : Real.exp (((11447 / 10000 : ℚ) / 8 : ℚ) : ℝ)
      ≤ ((expSQ KX ((11447 / 10000 : ℚ) / 8) + expRQ KX ((11447 / 10000 : ℚ) / 8) : ℚ) : ℝ) := by
    have := le_abs_self (Real.exp (((11447 / 10000 : ℚ) / 8 : ℚ) : ℝ) - (expSQ KX ((11447 / 10000 : ℚ) / 8) : ℝ))
    rw [Rat.cast_add]
    linarith
  have h8 : Real.exp ((11447 / 10000 : ℚ) : ℝ) = Real.exp ((((11447 / 10000 : ℚ) / 8 : ℚ)) : ℝ) ^ 8 := by
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have hpow := pow_le_pow_left₀ (Real.exp_pos _).le hup 8
  have hcR : ((expSQ KX ((11447 / 10000 : ℚ) / 8) + expRQ KX ((11447 / 10000 : ℚ) / 8) : ℚ) : ℝ) ^ 8
      ≤ ((PLOq : ℚ) : ℝ) := by
    exact_mod_cast hc
  have hpi : ((PLOq : ℚ) : ℝ) ≤ Real.pi := by have := Real.pi_gt_d20; unfold PLOq; push_cast; linarith
  have : Real.exp ((11447 / 10000 : ℚ) : ℝ) ≤ Real.pi := by rw [h8]; linarith
  rw [Real.le_log_iff_exp_le Real.pi_pos]
  have e : ((11447 / 10000 : ℚ) : ℝ) = 11447 / 10000 := by push_cast; ring
  rw [← e]
  exact this

lemma log5_le : Real.log 5 ≤ 804718956217051 / 500000000000000 := by
  have h := log_le_of KX (by unfold KX; norm_num) (q := 804718956217051 / 500000000000000) 5 (by norm_num)
    (by norm_num) (by unfold KX; decide +kernel) (by unfold KX; decide +kernel)
  push_cast at h
  exact h

lemma log5pi_le : Real.log (5 / Real.pi) ≤ 804718956217051 / 500000000000000 - 11447 / 10000 := by
  rw [Real.log_div (by norm_num) Real.pi_ne_zero]
  linarith [log5_le, log_pi_ge']

/-- **D's band archimedean side at `c* = (-3, 2)`**: at most `4.33 ||v||^2` (computed band value 4.21;
the certified majorant is 4.319). -/
theorem dh_band_arch_le :
    (archSideD (WeilForm.autocorr (fun u => ((bandTest (-3) 2 u : ℝ) : ℂ)))).re
      ≤ (433 / 100 : ℝ) * (∫ x, ‖((bandTest (-3) 2 x : ℝ) : ℂ)‖ ^ 2) := by
  have h := pairHyp0
  have hA := archD_band_le (-3) 2 300 (by norm_num) (R := 175) (by unfold bk2; norm_num)
  have hA0 : acR (bandTest (-3) 2) 0 = bandA * ((-3) ^ 2 + 2 ^ 2) := acR_bandV_zero h (-3) 2
  have e : ∀ j ∈ Finset.range (300 + 1), lorTermB (bandTest (-3) 2) ((j : ℝ) + 3 / 4)
      = (-3) ^ 2 * Jd bandA bk1 ((j : ℝ) + 3 / 4) + 2 * (-3) * 2 * Jx bandA bk1 bk2 1 (-1) ((j : ℝ) + 3 / 4)
        + 2 ^ 2 * Jd bandA bk2 ((j : ℝ) + 3 / 4) :=
    fun j _ => lorTermB_bandV h (-3) 2 ((j : ℝ) + 3 / 4) (by positivity)
  have hlor : ∑ j ∈ Finset.range (300 + 1), lorTermB (bandTest (-3) 2) ((j : ℝ) + 3 / 4)
      = (-3) ^ 2 * DSJ1 + 2 * (-3) * 2 * DSJx + 2 ^ 2 * DSJ2 := by
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum]
    rfl
  rw [hA0, hlor] at hA
  rw [bandTest_norm]
  have hK : ((8 / 3 : ℝ) * (|(-3 : ℝ)| * bk1 + |(2 : ℝ)| * bk2)) ^ 2 / 175 = (3416 / 3) ^ 2 / 175 := by
    unfold bk1 bk2; norm_num
  rw [hK] at hA
  have hN : ((300 : ℕ) : ℝ) = 300 := by norm_num
  rw [hN] at hA
  obtain ⟨hA1, hA2⟩ := bandA_bounds
  have hApos : 0 < bandA := h.A0
  have hL := log5pi_le
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have hH := Rat.cast_le (K := ℝ) |>.mpr q_H300
  push_cast at hH
  have h1 := DSJ1_ge
  have h2 := DSJ2_ge
  have hx := DSJx_le
  set L5 := Real.log (5 / Real.pi)
  set γ := Real.eulerMascheroniConstant
  set H := ∑ n ∈ Finset.range 300, (1 : ℝ) / ((n : ℝ) + 1)
  have m1 : L5 * bandA ≤ (804718956217051 / 500000000000000 - 11447 / 10000) * bandA :=
    mul_le_mul_of_nonneg_right hL hApos.le
  have m2 : (1 / 2) * bandA ≤ γ * bandA := mul_le_mul_of_nonneg_right hγ.le hApos.le
  have m3 : H * bandA ≤ (3141331941 / 500000000) * bandA := mul_le_mul_of_nonneg_right hH hApos.le
  nlinarith

/-- **THE DAVENPORT-HEILBRONN BAND COUNTEREXAMPLE (kernel-checked).**  On the band test
`v = -3 cos(763u/9) + 2 cos(259u/3)` on `[-9π/14, 9π/14]` (the same test space as `band_floor`),
D's explicit-formula functional (`archSideD - primeSideD`, `Gamma_R(s+1)`, conductor 5, no pole), with
prime weights `w` = the coefficients of `-D'/D` (given only by their defining identity on `[1, 56]`),
is at most `-(1/2) ||v||^2` (computed: `-0.655 ||v||^2`).  So the band certificate that zeta passes
(`band_floor`: `>= (1/2) ||v||^2`) is FAILED by D. -/
theorem dh_band_negative (w : ℕ → ℝ)
    (hw : ∀ n : ℕ, 1 ≤ n → n ≤ 56 → aD n * Real.log n = ∑ d ∈ n.divisors, w d * aD (n / d)) :
    (weilFormD w (WeilForm.autocorr (fun u => ((bandTest (-3) 2 u : ℝ) : ℂ)))).re
      ≤ -(1 / 2 : ℝ) * ∫ x, ‖((bandTest (-3) 2 x : ℝ) : ℂ)‖ ^ 2 := by
  have h1 := dh_band_arch_le
  have h2 := dh_band_comb_ge w hw
  unfold weilFormD
  rw [Complex.sub_re]
  have hpos : 0 ≤ ∫ x, ‖((bandTest (-3) 2 x : ℝ) : ℂ)‖ ^ 2 := integral_nonneg (fun x => by positivity)
  linarith

/-- **The separation**, in one statement: on the same nonzero band test, zeta's Weil functional is
`>= (1/2) ||v||^2` and D's is `<= -(1/2) ||v||^2`. -/
theorem band_separation (w : ℕ → ℝ)
    (hw : ∀ n : ℕ, 1 ≤ n → n ≤ 56 → aD n * Real.log n = ∑ d ∈ n.divisors, w d * aD (n / d)) :
    0 < ∫ x, ‖((bandTest (-3) 2 x : ℝ) : ℂ)‖ ^ 2
      ∧ (1 / 2 : ℝ) * (∫ x, ‖((bandTest (-3) 2 x : ℝ) : ℂ)‖ ^ 2)
          ≤ (WeilForm.weilForm (WeilForm.autocorr (fun u => ((bandTest (-3) 2 u : ℝ) : ℂ)))).re
      ∧ (weilFormD w (WeilForm.autocorr (fun u => ((bandTest (-3) 2 u : ℝ) : ℂ)))).re
          ≤ -(1 / 2 : ℝ) * ∫ x, ‖((bandTest (-3) 2 x : ℝ) : ℂ)‖ ^ 2 := by
  refine ⟨?_, band_floor (-3) 2, dh_band_negative w hw⟩
  rw [bandTest_norm]
  have := pairHyp0.A0
  positivity

/-- Non-vacuity: D's closed-form weights `cD` satisfy the hypothesis (`cD_conv`), so the separation
holds for them. -/
theorem band_separation_cD :
    0 < ∫ x, ‖((bandTest (-3) 2 x : ℝ) : ℂ)‖ ^ 2
      ∧ (1 / 2 : ℝ) * (∫ x, ‖((bandTest (-3) 2 x : ℝ) : ℂ)‖ ^ 2)
          ≤ (WeilForm.weilForm (WeilForm.autocorr (fun u => ((bandTest (-3) 2 u : ℝ) : ℂ)))).re
      ∧ (weilFormD cD (WeilForm.autocorr (fun u => ((bandTest (-3) 2 u : ℝ) : ℂ)))).re
          ≤ -(1 / 2 : ℝ) * ∫ x, ‖((bandTest (-3) 2 x : ℝ) : ℂ)‖ ^ 2 :=
  band_separation cD cD_conv

end Crux3
