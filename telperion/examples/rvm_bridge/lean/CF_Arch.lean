import CF_Test

/-!
# CF_Arch: the Gamma_C (conductor 20) Weil functional and its two-sided archimedean bounds

Counterfeit-ladder lane (CF), 2026-09-24, `rvm_bridge` island.

`conjecture1_proved = False`.  Nothing here bears on RH; this is the explicit-formula functional of a
degree-2 L-function with the gamma factor of an imaginary quadratic field, evaluated on test functions.

## The functional

`zeta_K`, `K = Q(sqrt -5)`, and the Epstein counterfeit `E = (zeta_K + L(chi_-4) L(chi_5))/2` share the
completed form `Lam(s) = 20^{s/2} Gamma_R(s) Gamma_R(s+1) F(s) = Lam(1 - s)`
(`Gamma_R(s) Gamma_R(s+1) = Gamma_C(s)`, Mathlib's `Complex.Gammaℝ_mul_Gammaℝ_add_one`), and a simple
pole at `s = 1`.  Their Guinand-Weil explicit formula has, for `g = v * v~`,
* the arch side  `archSideGC g = H_g(0) + H_g(1) + g(0) log(20/pi^2)
    + (1/2pi) int h_g(r) [Re psi(1/4 + ir/2) + Re psi(3/4 + ir/2)] dr`
  (the two pole terms, exactly as in the registry's `archSide`; `log 20 - 2 log pi` is
  `2 Re (d/ds) log(20^{s/2} pi^{-s})`; the two digamma terms are the `Gamma_R(s)` and `Gamma_R(s+1)`
  factors, i.e. the registry's zeta term plus Crux3's `psiD`);
* the prime side `primeSideD w g = sum_n w(n)/sqrt n (g(log n) + g(-log n))` (Crux3's generic comb),
  with `w` the coefficients of `-F'/F`.
`weilFormGC w g = archSideGC g - primeSideD w g`.  The identification with the zero sum is the classical
explicit formula for these two functions; it is NOT formalized (checked numerically, lane notes).

## Proved here
* `re_digamma_le` / `re_digamma_ge`: the vertical-line digamma series truncated at `N`, with the tail
  bounded above by `a/N + t^2/(2N^2)` and below by `0` (any `0 < a < 1`);
* `FreqData.archGC_re_eq`: `Re archSideGC(v * v~) = 2 P^2 + log(20/pi^2) g(0) + (1/2pi) int Fsq (psiR + psiD)`,
  `P = int v(u) e^{-u/2} du`;
* `FreqData.archGC_re_ge` and `FreqData.archGC_re_le`: two-sided bounds by Lorentzian terms
  (the upper one carries the `r^2` moment of `Fsq`);
* `bandM_moment`: the `r^2` moment of the M-mode test, `int Fsq r^2 <= 2 pi R^2 g(0) + 2 pi K'^2/R`.
No `sorry`.
-/

open MeasureTheory Complex Zeta23 Set Filter Crux3
open scoped ComplexConjugate
open WeilExplicit RvMBridge4 RvMBridge5 RvMBridgeZhu

noncomputable section

namespace CF

/-! ## The truncated vertical-line digamma series, both directions -/

/-- **Upper truncation**: `Re psi(a + it) <= -gamma + H_N - sum_{j<=N} (j+a)/((j+a)^2+t^2) + a/N + t^2/(2N^2)`. -/
theorem re_digamma_le (a t : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (N : ℕ) (hN : 1 ≤ N) :
    (Complex.digamma ((a : ℂ) + Complex.I * t)).re
      ≤ -Real.eulerMascheroniConstant + ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + 1)
        - ∑ j ∈ Finset.range (N + 1), ((j : ℝ) + a) / (((j : ℝ) + a) ^ 2 + t ^ 2)
        + a / N + t ^ 2 / (2 * (N : ℝ) ^ 2) := by
  rw [Zeta23.MuFields.re_digamma_vertical ha0 ha1]
  have hs := Zeta23.MuFields.summable_re_terms ha0 ha1 t
  rw [← hs.sum_add_tsum_nat_add N]
  obtain ⟨hsq, hsq'⟩ := tsum_inv_sq_tail hN
  obtain ⟨hcu, hcu'⟩ := tsum_inv_cube_tail hN
  have hmaj : Summable (fun n : ℕ => a * (1 / ((n : ℝ) + N + 1) ^ 2) + t ^ 2 * (1 / ((n : ℝ) + N + 1) ^ 3)) :=
    (hsq.mul_left _).add (hcu.mul_left _)
  have hle : ∀ n : ℕ, (1 / (((n + N : ℕ) : ℝ) + 1) - (((n + N : ℕ) : ℝ) + 1 + a)
        / ((((n + N : ℕ) : ℝ) + 1 + a) ^ 2 + t ^ 2))
      ≤ a * (1 / ((n : ℝ) + N + 1) ^ 2) + t ^ 2 * (1 / ((n : ℝ) + N + 1) ^ 3) := by
    intro n
    have := serTerm_le a t ha0.le (n + N)
    push_cast at this ⊢
    calc _ ≤ a / ((n : ℝ) + N + 1) ^ 2 + t ^ 2 / ((n : ℝ) + N + 1) ^ 3 := this
      _ = _ := by ring
  have htail : ∑' n : ℕ, (1 / (((n + N : ℕ) : ℝ) + 1) - (((n + N : ℕ) : ℝ) + 1 + a)
        / ((((n + N : ℕ) : ℝ) + 1 + a) ^ 2 + t ^ 2))
      ≤ a / N + t ^ 2 / (2 * (N : ℝ) ^ 2) := by
    have h1 := (hs.comp_injective (add_left_injective N)).tsum_le_tsum hle hmaj
    rw [Summable.tsum_add (hsq.mul_left _) (hcu.mul_left _), tsum_mul_left, tsum_mul_left] at h1
    have h2 : a * ∑' n : ℕ, 1 / ((n : ℝ) + N + 1) ^ 2 ≤ a * (1 / N) :=
      mul_le_mul_of_nonneg_left hsq' ha0.le
    have h3 : t ^ 2 * ∑' n : ℕ, 1 / ((n : ℝ) + N + 1) ^ 3 ≤ t ^ 2 * (1 / (2 * (N : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hcu' (sq_nonneg t)
    have e1 : a * (1 / (N : ℝ)) = a / N := by ring
    have e2 : t ^ 2 * (1 / (2 * (N : ℝ) ^ 2)) = t ^ 2 / (2 * (N : ℝ) ^ 2) := by ring
    try simp only [Function.comp] at h1
    linarith
  have hfin : ∑ n ∈ Finset.range N, (1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t ^ 2))
      = ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + 1)
        - ∑ n ∈ Finset.range N, (((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t ^ 2)) := by
    rw [← Finset.sum_sub_distrib]
  have hlz : ∑ j ∈ Finset.range (N + 1), ((j : ℝ) + a) / (((j : ℝ) + a) ^ 2 + t ^ 2)
      = ∑ n ∈ Finset.range N, (((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t ^ 2)) + a / (a ^ 2 + t ^ 2) := by
    rw [Finset.sum_range_succ']
    push_cast
    simp only [zero_add]
  rw [hfin, hlz]
  linarith

/-- **Lower truncation** (the tail is `>= 0`):
`-gamma + H_N - sum_{j<=N} (j+a)/((j+a)^2+t^2) <= Re psi(a + it)`. -/
theorem re_digamma_ge (a t : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (N : ℕ) :
    -Real.eulerMascheroniConstant + ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + 1)
        - ∑ j ∈ Finset.range (N + 1), ((j : ℝ) + a) / (((j : ℝ) + a) ^ 2 + t ^ 2)
      ≤ (Complex.digamma ((a : ℂ) + Complex.I * t)).re := by
  rw [Zeta23.MuFields.re_digamma_vertical ha0 ha1]
  have hs := Zeta23.MuFields.summable_re_terms ha0 ha1 t
  rw [← hs.sum_add_tsum_nat_add N]
  have hnn : ∀ n : ℕ, 0 ≤ (1 / (((n + N : ℕ) : ℝ) + 1) - (((n + N : ℕ) : ℝ) + 1 + a)
        / ((((n + N : ℕ) : ℝ) + 1 + a) ^ 2 + t ^ 2)) := by
    intro n
    set u : ℝ := ((n + N : ℕ) : ℝ) + 1 with hu
    have hu1 : 1 ≤ u := by rw [hu]; have := Nat.cast_nonneg (α := ℝ) (n + N); linarith
    have hp : 0 < u + a := by linarith
    rw [sub_nonneg, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg t, sq_nonneg (u + a)]
  have htail : 0 ≤ ∑' n : ℕ, (1 / (((n + N : ℕ) : ℝ) + 1) - (((n + N : ℕ) : ℝ) + 1 + a)
        / ((((n + N : ℕ) : ℝ) + 1 + a) ^ 2 + t ^ 2)) := tsum_nonneg hnn
  have hfin : ∑ n ∈ Finset.range N, (1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t ^ 2))
      = ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + 1)
        - ∑ n ∈ Finset.range N, (((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t ^ 2)) := by
    rw [← Finset.sum_sub_distrib]
  have hlz : ∑ j ∈ Finset.range (N + 1), ((j : ℝ) + a) / (((j : ℝ) + a) ^ 2 + t ^ 2)
      = ∑ n ∈ Finset.range N, (((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t ^ 2)) + a / (a ^ 2 + t ^ 2) := by
    rw [Finset.sum_range_succ']
    push_cast
    simp only [zero_add]
  rw [hfin, hlz]
  linarith

lemma psiR_eq' (r : ℝ) :
    RvMBridge11.psiR r = (Complex.digamma (((1 / 4 : ℝ) : ℂ) + Complex.I * ((r / 2 : ℝ) : ℂ))).re := by
  unfold RvMBridge11.psiR
  rw [show (1 / 4 : ℂ) + ((r : ℂ) / 2) * Complex.I = ((1 / 4 : ℝ) : ℂ) + Complex.I * ((r / 2 : ℝ) : ℂ) by
    push_cast; ring]

lemma lz_eq (b r : ℝ) : lz b r = b / (b ^ 2 + (r / 2) ^ 2) := rfl

/-- `psiR` (the `Gamma_R(s)` weight, `Re psi(1/4 + ir/2)`) from above. -/
theorem psiR_le (r : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    RvMBridge11.psiR r ≤ -Real.eulerMascheroniConstant + ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + 1)
      - ∑ j ∈ Finset.range (N + 1), lz ((j : ℝ) + 1 / 4) r + (1 / 4) / N + (r / 2) ^ 2 / (2 * (N : ℝ) ^ 2) := by
  rw [psiR_eq']
  have := re_digamma_le (1 / 4) (r / 2) (by norm_num) (by norm_num) N hN
  simpa only [lz_eq] using this

/-- `psiD` (the `Gamma_R(s+1)` weight, `Re psi(3/4 + ir/2)`) from below. -/
theorem psiD_ge (r : ℝ) (N : ℕ) :
    -Real.eulerMascheroniConstant + ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + 1)
      - ∑ j ∈ Finset.range (N + 1), lz ((j : ℝ) + 3 / 4) r ≤ psiD r := by
  rw [psiD_eq]
  have := re_digamma_ge (3 / 4) (r / 2) (by norm_num) (by norm_num) N
  simpa only [lz_eq] using this

/-! ## The functional -/

/-- The arch side of a degree-2 L-function with gamma factor `20^{s/2} Gamma_R(s) Gamma_R(s+1)` and a
simple pole at `s = 1`: the two pole terms, `g(0) log(20/pi^2)`, and the `Gamma_R(s)`, `Gamma_R(s+1)` digamma
terms. -/
def archSideGC (g : ℝ → ℂ) : ℂ :=
  weilKernel g 0 + weilKernel g 1 + g 0 * (Real.log (20 / Real.pi ^ 2) : ℂ)
    + (1 / (2 * (Real.pi : ℂ))) * ∫ r : ℝ, weilKernel g (1 / 2 + (r : ℂ) * Complex.I)
        * ((RvMBridge11.psiR r + psiD r : ℝ) : ℂ)

/-- The Weil functional of such an L-function with log-derivative coefficients `w`. -/
def weilFormGC (w : ℕ → ℝ) (g : ℝ → ℂ) : ℂ := archSideGC g - primeSideD w g

lemma weilKernel_real_zero (v : ℝ → ℝ) :
    weilKernel (fun u => (v u : ℂ)) 0 = ((∫ u, v u * Real.exp (-(1 / 2) * u) : ℝ) : ℂ) := by
  unfold weilKernel
  rw [← integral_complex_ofReal]
  congr 1
  funext u
  push_cast
  congr 1
  congr 1
  ring

section
variable {v : ℝ → ℝ} {L K : ℝ} (hv : FreqData v L K)
include hv

/-- The two pole terms of a real even test: each is `P^2`, `P = int v(u) e^{-u/2} du`. -/
theorem _root_.Crux3.FreqData.pole_eq :
    weilKernel (WeilForm.autocorr (fun u => (v u : ℂ))) 0
        = (((∫ u, v u * Real.exp (-(1 / 2) * u)) ^ 2 : ℝ) : ℂ)
      ∧ weilKernel (WeilForm.autocorr (fun u => (v u : ℂ))) 1
        = (((∫ u, v u * Real.exp (-(1 / 2) * u)) ^ 2 : ℝ) : ℂ) := by
  set fC : ℝ → ℂ := fun u => (v u : ℂ) with hfC
  set g : ℝ → ℂ := WeilExplicit.autocorr fC with hgdef
  have hcI : (starRingEnd ℂ) (Complex.I / 2) = -(Complex.I / 2) := by
    simp [Complex.conj_I, map_ofNat, neg_div]
  have hcI' : (starRingEnd ℂ) (-Complex.I / 2) = Complex.I / 2 := by
    simp [Complex.conj_I, map_ofNat, neg_div]
  have hev1 : ∀ u, v (-u) = 1 * v u := fun u => by rw [one_mul]; exact hv.even u
  have hpole0 : weilKernel g 0 = ((1 * ‖weilKernel fC 0‖ ^ 2 : ℝ) : ℂ) := by
    rw [weilKernel_zero, hgdef, autocorr_eq_weilTest, EF.paperFT_weilTest hv.hcont hv.hcont hv.hcs hv.hcs,
      hcI, hfC, paperFT_neg_of_parity (by norm_num : (1 : ℝ) * 1 = 1) hev1, map_mul, Complex.conj_ofReal,
      mul_left_comm, Complex.mul_conj', weilKernel_zero]
    push_cast
    ring
  have hpole1 : weilKernel g 1 = ((1 * ‖weilKernel fC 0‖ ^ 2 : ℝ) : ℂ) := by
    rw [weilKernel_one, hgdef, autocorr_eq_weilTest, EF.paperFT_weilTest hv.hcont hv.hcont hv.hcs hv.hcs,
      hcI', hfC, neg_div, paperFT_neg_of_parity (by norm_num : (1 : ℝ) * 1 = 1) hev1, mul_assoc,
      Complex.mul_conj', weilKernel_zero]
    push_cast
    ring
  have hn : ‖weilKernel fC 0‖ ^ 2 = (∫ u, v u * Real.exp (-(1 / 2) * u)) ^ 2 := by
    rw [hfC, weilKernel_real_zero, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [one_mul, hn] at hpole0 hpole1
  exact ⟨hpole0, hpole1⟩

/-- **The real part of the Gamma_C arch side** on a real even test. -/
theorem _root_.Crux3.FreqData.archGC_re_eq :
    (archSideGC (WeilForm.autocorr (fun u => (v u : ℂ)))).re
      = 2 * (∫ u, v u * Real.exp (-(1 / 2) * u)) ^ 2 + Real.log (20 / Real.pi ^ 2) * acR v 0
        + (1 / (2 * Real.pi)) * (∫ r, Fsq v r * RvMBridge11.psiR r)
        + (1 / (2 * Real.pi)) * (∫ r, Fsq v r * psiD r) := by
  set g : ℝ → ℂ := WeilExplicit.autocorr (fun u => (v u : ℂ)) with hgdef
  have hgA : g = fun y => (acR v y : ℂ) := FreqData.acR_eq
  obtain ⟨hp0, hp1⟩ := hv.pole_eq
  have hint : ∫ r : ℝ, weilKernel g (1 / 2 + (r : ℂ) * Complex.I) * ((RvMBridge11.psiR r + psiD r : ℝ) : ℂ)
      = ((∫ r, Fsq v r * RvMBridge11.psiR r + Fsq v r * psiD r : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext r
    rw [RvMBridge4.weilKernel_line, hgdef, hv.line r]
    push_cast
    ring
  have hsplit : ∫ r, Fsq v r * RvMBridge11.psiR r + Fsq v r * psiD r
      = (∫ r, Fsq v r * RvMBridge11.psiR r) + ∫ r, Fsq v r * psiD r :=
    integral_add hv.integrable_Fsq_psiR hv.integrable_Fsq_psiD
  unfold archSideGC
  rw [show WeilForm.autocorr (fun u => (v u : ℂ)) = g from rfl] at hp0 hp1 ⊢
  rw [hp0, hp1, hint, hsplit]
  have hg0 : g 0 = (acR v 0 : ℂ) := by rw [hgA]
  rw [hg0]
  set P := ∫ u, v u * Real.exp (-(1 / 2) * u)
  set I1 := ∫ r, Fsq v r * RvMBridge11.psiR r
  set I2 := ∫ r, Fsq v r * psiD r
  have e : ((P ^ 2 : ℝ) : ℂ) + ((P ^ 2 : ℝ) : ℂ) + (acR v 0 : ℂ) * (Real.log (20 / Real.pi ^ 2) : ℂ)
      + (1 / (2 * (Real.pi : ℂ))) * ((I1 + I2 : ℝ) : ℂ)
      = ((2 * P ^ 2 + Real.log (20 / Real.pi ^ 2) * acR v 0 + (1 / (2 * Real.pi)) * I1
          + (1 / (2 * Real.pi)) * I2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [e, Complex.ofReal_re]

/-- Lorentzian lower bound of one digamma integral: if `psi >= c - sum_{j<=N} lz(j + a)` pointwise then
`(1/2pi) int Fsq psi >= c g(0) - sum_{j<=N} lorTermB(j + a)`. -/
theorem _root_.Crux3.FreqData.psiInt_ge {psi : ℝ → ℝ} (hpsi : Integrable (fun r => Fsq v r * psi r)) (a c : ℝ) (ha : 0 < a)
    (N : ℕ) (hpt : ∀ r, c - ∑ j ∈ Finset.range (N + 1), lz ((j : ℝ) + a) r ≤ psi r) :
    c * acR v 0 - ∑ j ∈ Finset.range (N + 1), lorTermB v ((j : ℝ) + a)
      ≤ (1 / (2 * Real.pi)) * ∫ r, Fsq v r * psi r := by
  have hbpos : ∀ j : ℕ, (0 : ℝ) < (j : ℝ) + a := fun j => by positivity
  have hIlz : ∀ j ∈ Finset.range (N + 1), Integrable (fun r => Fsq v r * lz ((j : ℝ) + a) r) :=
    fun j _ => hv.integrable_Fsq_lz (hbpos j)
  have e : (fun r => Fsq v r * (c - ∑ j ∈ Finset.range (N + 1), lz ((j : ℝ) + a) r))
      = fun r => Fsq v r * c - ∑ j ∈ Finset.range (N + 1), Fsq v r * lz ((j : ℝ) + a) r := by
    funext r
    rw [mul_sub, Finset.mul_sum]
  have hImin : Integrable (fun r => Fsq v r * (c - ∑ j ∈ Finset.range (N + 1), lz ((j : ℝ) + a) r)) := by
    rw [e]
    exact (hv.integrable_Fsq.mul_const c).sub (integrable_finsetSum _ hIlz)
  have hmin : ∀ r, Fsq v r * (c - ∑ j ∈ Finset.range (N + 1), lz ((j : ℝ) + a) r) ≤ Fsq v r * psi r :=
    fun r => mul_le_mul_of_nonneg_left (hpt r) (Fsq_nonneg v r)
  have hmono := integral_mono hImin hpsi hmin
  have hsplit : ∫ r, Fsq v r * (c - ∑ j ∈ Finset.range (N + 1), lz ((j : ℝ) + a) r)
      = c * (2 * Real.pi * acR v 0) - ∑ j ∈ Finset.range (N + 1), 2 * Real.pi * lorTermB v ((j : ℝ) + a) := by
    rw [e, integral_sub (hv.integrable_Fsq.mul_const c) (integrable_finsetSum _ hIlz),
      integral_finsetSum _ hIlz, integral_mul_const, hv.integral_Fsq]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun j _ => ?_
      unfold lorTermB
      exact integral_mul_lz hv.continuous_acR hv.integrable_acR hv.integrable_Fsq hv.hFT (hbpos j)
  rw [hsplit] at hmono
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h2 := mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))
  have e2 : (1 / (2 * Real.pi)) * (c * (2 * Real.pi * acR v 0)
      - ∑ j ∈ Finset.range (N + 1), 2 * Real.pi * lorTermB v ((j : ℝ) + a))
      = c * acR v 0 - ∑ j ∈ Finset.range (N + 1), lorTermB v ((j : ℝ) + a) := by
    rw [← Finset.mul_sum]
    generalize (∑ j ∈ Finset.range (N + 1), lorTermB v ((j : ℝ) + a)) = S
    field_simp
  rw [e2] at h2
  exact h2

/-- Lorentzian upper bound of one digamma integral: if
`psi <= c - sum_{j<=N} lz(j + a) + (r/2)^2/(2N^2)` pointwise, and `Fsq r^2` is integrable, then
`(1/2pi) int Fsq psi <= c g(0) - sum_{j<=N} lorTermB(j + a) + (1/2pi)(1/(8N^2)) int Fsq r^2`. -/
theorem _root_.Crux3.FreqData.psiInt_le {psi : ℝ → ℝ} (hpsi : Integrable (fun r => Fsq v r * psi r)) (a c : ℝ) (ha : 0 < a)
    (N : ℕ) (hN : 1 ≤ N) (hIsq : Integrable (fun r => Fsq v r * r ^ 2))
    (hpt : ∀ r, psi r ≤ c - ∑ j ∈ Finset.range (N + 1), lz ((j : ℝ) + a) r + (r / 2) ^ 2 / (2 * (N : ℝ) ^ 2)) :
    (1 / (2 * Real.pi)) * ∫ r, Fsq v r * psi r
      ≤ c * acR v 0 - ∑ j ∈ Finset.range (N + 1), lorTermB v ((j : ℝ) + a)
        + (1 / (2 * Real.pi)) * ((1 / (8 * (N : ℝ) ^ 2)) * ∫ r, Fsq v r * r ^ 2) := by
  have hbpos : ∀ j : ℕ, (0 : ℝ) < (j : ℝ) + a := fun j => by positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hIlz : ∀ j ∈ Finset.range (N + 1), Integrable (fun r => Fsq v r * lz ((j : ℝ) + a) r) :=
    fun j _ => hv.integrable_Fsq_lz (hbpos j)
  have hmaj : ∀ r, Fsq v r * psi r ≤ Fsq v r * c - ∑ j ∈ Finset.range (N + 1), Fsq v r * lz ((j : ℝ) + a) r
      + (1 / (8 * (N : ℝ) ^ 2)) * (Fsq v r * r ^ 2) := by
    intro r
    have h2 := mul_le_mul_of_nonneg_left (hpt r) (Fsq_nonneg v r)
    rw [← Finset.mul_sum]
    have e : Fsq v r * (c - ∑ j ∈ Finset.range (N + 1), lz ((j : ℝ) + a) r + (r / 2) ^ 2 / (2 * (N : ℝ) ^ 2))
        = Fsq v r * c - Fsq v r * ∑ j ∈ Finset.range (N + 1), lz ((j : ℝ) + a) r
          + (1 / (8 * (N : ℝ) ^ 2)) * (Fsq v r * r ^ 2) := by
      field_simp; ring
    linarith
  have i3 : Integrable (fun r => Fsq v r * c) := hv.integrable_Fsq.mul_const c
  have i4 : Integrable (fun r => ∑ j ∈ Finset.range (N + 1), Fsq v r * lz ((j : ℝ) + a) r) :=
    integrable_finsetSum _ hIlz
  have i1 : Integrable (fun r => Fsq v r * c - ∑ j ∈ Finset.range (N + 1), Fsq v r * lz ((j : ℝ) + a) r) :=
    i3.sub i4
  have i2 : Integrable (fun r => (1 / (8 * (N : ℝ) ^ 2)) * (Fsq v r * r ^ 2)) := hIsq.const_mul _
  have i12 : Integrable (fun r => Fsq v r * c - ∑ j ∈ Finset.range (N + 1), Fsq v r * lz ((j : ℝ) + a) r
      + (1 / (8 * (N : ℝ) ^ 2)) * (Fsq v r * r ^ 2)) := i1.add i2
  have hmono := integral_mono hpsi i12 hmaj
  have eI : ∫ r, (Fsq v r * c - ∑ j ∈ Finset.range (N + 1), Fsq v r * lz ((j : ℝ) + a) r
      + (1 / (8 * (N : ℝ) ^ 2)) * (Fsq v r * r ^ 2))
      = c * (2 * Real.pi * acR v 0) - ∑ j ∈ Finset.range (N + 1), 2 * Real.pi * lorTermB v ((j : ℝ) + a)
        + (1 / (8 * (N : ℝ) ^ 2)) * ∫ r, Fsq v r * r ^ 2 := by
    rw [integral_add i1 i2, integral_sub i3 i4, integral_finsetSum _ hIlz, integral_mul_const,
      integral_const_mul, hv.integral_Fsq]
    congr 2
    · ring
    · refine Finset.sum_congr rfl fun j _ => ?_
      unfold lorTermB
      exact integral_mul_lz hv.continuous_acR hv.integrable_acR hv.integrable_Fsq hv.hFT (hbpos j)
  rw [eI] at hmono
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h2 := mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))
  have e2 : (1 / (2 * Real.pi)) * (c * (2 * Real.pi * acR v 0)
      - ∑ j ∈ Finset.range (N + 1), 2 * Real.pi * lorTermB v ((j : ℝ) + a)
      + (1 / (8 * (N : ℝ) ^ 2)) * ∫ r, Fsq v r * r ^ 2)
      = c * acR v 0 - ∑ j ∈ Finset.range (N + 1), lorTermB v ((j : ℝ) + a)
        + (1 / (2 * Real.pi)) * ((1 / (8 * (N : ℝ) ^ 2)) * ∫ r, Fsq v r * r ^ 2) := by
    rw [← Finset.mul_sum]
    generalize (∑ j ∈ Finset.range (N + 1), lorTermB v ((j : ℝ) + a)) = S
    generalize (∫ r, Fsq v r * r ^ 2) = T
    field_simp
  rw [e2] at h2
  exact h2

/-- **Lower bound of the Gamma_C arch side** (both digamma tails `>= 0` dropped; the pole terms kept). -/
theorem _root_.Crux3.FreqData.archGC_re_ge (N : ℕ) :
    2 * (∫ u, v u * Real.exp (-(1 / 2) * u)) ^ 2 + Real.log (20 / Real.pi ^ 2) * acR v 0
      + ((-Real.eulerMascheroniConstant + ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + 1)) * acR v 0
          - ∑ j ∈ Finset.range (N + 1), lorTermB v ((j : ℝ) + 1 / 4))
      + ((-Real.eulerMascheroniConstant + ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + 1)) * acR v 0
          - ∑ j ∈ Finset.range (N + 1), lorTermB v ((j : ℝ) + 3 / 4))
    ≤ (archSideGC (WeilForm.autocorr (fun u => (v u : ℂ)))).re := by
  rw [hv.archGC_re_eq]
  have h1 := hv.psiInt_ge hv.integrable_Fsq_psiR (1 / 4) _ (by norm_num) N (fun r => psiR_ge_lz r N)
  have h2 := hv.psiInt_ge hv.integrable_Fsq_psiD (3 / 4) _ (by norm_num) N (fun r => psiD_ge r N)
  linarith

/-- **Upper bound of the Gamma_C arch side** (pole terms exact; both digamma tails bounded; the `r^2`
moment of `Fsq` bounded by `T`). -/
theorem _root_.Crux3.FreqData.archGC_re_le (N : ℕ) (hN : 1 ≤ N) (hIsq : Integrable (fun r => Fsq v r * r ^ 2)) (T : ℝ)
    (hT : ∫ r, Fsq v r * r ^ 2 ≤ T) :
    (archSideGC (WeilForm.autocorr (fun u => (v u : ℂ)))).re
      ≤ 2 * (∫ u, v u * Real.exp (-(1 / 2) * u)) ^ 2 + Real.log (20 / Real.pi ^ 2) * acR v 0
        + ((-Real.eulerMascheroniConstant + ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + 1) + (1 / 4) / N) * acR v 0
            - ∑ j ∈ Finset.range (N + 1), lorTermB v ((j : ℝ) + 1 / 4))
        + ((-Real.eulerMascheroniConstant + ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + 1) + (3 / 4) / N) * acR v 0
            - ∑ j ∈ Finset.range (N + 1), lorTermB v ((j : ℝ) + 3 / 4))
        + 2 * ((1 / (2 * Real.pi)) * ((1 / (8 * (N : ℝ) ^ 2)) * T)) := by
  rw [hv.archGC_re_eq]
  have h1 := hv.psiInt_le hv.integrable_Fsq_psiR (1 / 4)
    (-Real.eulerMascheroniConstant + ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + 1) + (1 / 4) / N)
    (by norm_num) N hN hIsq (fun r => by have := psiR_le r N hN; linarith)
  have h2 := hv.psiInt_le hv.integrable_Fsq_psiD (3 / 4)
    (-Real.eulerMascheroniConstant + ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + 1) + (3 / 4) / N)
    (by norm_num) N hN hIsq (fun r => by have := psiD_le r N hN; linarith)
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h3 : (1 / (2 * Real.pi)) * ((1 / (8 * (N : ℝ) ^ 2)) * ∫ r, Fsq v r * r ^ 2)
      ≤ (1 / (2 * Real.pi)) * ((1 / (8 * (N : ℝ) ^ 2)) * T) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_left hT (by positivity)
  linarith

end

/-! ## The `r^2` moment of the M-mode test -/

section
variable {A : ℝ} {M : ℕ} {k s : ℕ → ℝ} (h : ModeHyp A M k s) (c : ℕ → ℝ)
include h

/-- `Fsq(r) <= K'^2/r^4` once `r^2 >= 4 k_i^2` for every mode, `K' = (8/3) sum |c_i| k_i`. -/
lemma Fsq_bandM_far {r : ℝ} (hr : ∀ i, i < M → 4 * k i ^ 2 ≤ r ^ 2) (_hr0 : 0 < r ^ 2) :
    Fsq (bandM A M k c) r ≤ ((8 / 3) * ∑ i ∈ Finset.range M, |c i| * k i) ^ 2 / r ^ 4 := by
  unfold Fsq
  rw [paperFT_bandM h c r, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hb : |∑ i ∈ Finset.range M, c i * (∫ u in (-A)..A, Real.cos (k i * u) * Real.cos (r * u))|
      ≤ (8 / 3) * (∑ i ∈ Finset.range M, |c i| * k i) / r ^ 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_le_sum fun i hi => ?_
    have hiM := Finset.mem_range.mp hi
    have d := abs_integral_cos_cos_far (h.kpos i hiM) (h.cosk i hiM) (h.sink i hiM) (h.abs_s i hiM) (hr i hiM)
    rw [abs_mul]
    calc |c i| * |∫ u in (-A)..A, Real.cos (k i * u) * Real.cos (r * u)|
        ≤ |c i| * ((8 * k i / 3) / r ^ 2) := mul_le_mul_of_nonneg_left d (abs_nonneg _)
      _ = (8 / 3) * (|c i| * k i) / r ^ 2 := by ring
  have h0 : 0 ≤ |∑ i ∈ Finset.range M, c i * (∫ u in (-A)..A, Real.cos (k i * u) * Real.cos (r * u))| :=
    abs_nonneg _
  have := pow_le_pow_left₀ h0 hb 2
  rw [sq_abs] at this
  calc _ ≤ ((8 / 3) * (∑ i ∈ Finset.range M, |c i| * k i) / r ^ 2) ^ 2 := this
    _ = ((8 / 3) * ∑ i ∈ Finset.range M, |c i| * k i) ^ 2 / r ^ 4 := by rw [div_pow]; ring

/-- **The `r^2` moment**: for `R > 0` with `2 k_i <= R` for every mode,
`Fsq r^2` is integrable and `int Fsq r^2 <= 2 pi R^2 g(0) + 2 pi K'^2/R`. -/
theorem bandM_moment {R : ℝ} (hR0 : 0 < R) (hR : ∀ i, i < M → 2 * k i ≤ R) :
    Integrable (fun r => Fsq (bandM A M k c) r * r ^ 2)
      ∧ ∫ r, Fsq (bandM A M k c) r * r ^ 2
          ≤ R ^ 2 * (2 * Real.pi * acR (bandM A M k c) 0)
            + 2 * ((8 / 3) * ∑ i ∈ Finset.range M, |c i| * k i) ^ 2 * (Real.pi / R) := by
  have hv := bandM_freqData h c
  set F := Fsq (bandM A M k c) with hF
  set K := ((8 / 3) * ∑ i ∈ Finset.range M, |c i| * k i) ^ 2 with hKdef
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  have hpt : ∀ r, F r * r ^ 2 ≤ R ^ 2 * F r + 2 * K * (R ^ 2 + r ^ 2)⁻¹ := by
    intro r
    have hF0 := Fsq_nonneg (bandM A M k c) r
    have hKp : 0 ≤ 2 * K * (R ^ 2 + r ^ 2)⁻¹ := by positivity
    by_cases hr : r ^ 2 ≤ R ^ 2
    · calc F r * r ^ 2 = r ^ 2 * F r := by ring
        _ ≤ R ^ 2 * F r := mul_le_mul_of_nonneg_right hr hF0
        _ ≤ _ := by linarith
    · rw [not_le] at hr
      have hr0 : 0 < r ^ 2 := lt_of_le_of_lt (sq_nonneg R) hr
      have hfar := Fsq_bandM_far h c (r := r) (fun i hi => by
        have := hR i hi
        have hk := h.kpos i hi
        nlinarith) hr0
      have e : F r * r ^ 2 = R ^ 2 * F r + (r ^ 2 - R ^ 2) * F r := by ring
      rw [e]
      have h1 : (r ^ 2 - R ^ 2) * F r ≤ (r ^ 2 - R ^ 2) * (K / r ^ 4) :=
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
  have hdom : Integrable (fun r : ℝ => R ^ 2 * F r + 2 * K * (R ^ 2 + r ^ 2)⁻¹) :=
    (hv.integrable_Fsq.const_mul _).add ((integrable_inv_sq_add_sq hR0).const_mul _)
  have hIsq : Integrable (fun r => F r * r ^ 2) := by
    refine hdom.mono' (hv.continuous_Fsq.mul (continuous_pow 2)).aestronglyMeasurable
      (Eventually.of_forall fun r => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Fsq_nonneg _ r) (sq_nonneg r))]
    exact hpt r
  refine ⟨hIsq, ?_⟩
  have := integral_mono hIsq hdom hpt
  rw [integral_add (hv.integrable_Fsq.const_mul _) ((integrable_inv_sq_add_sq hR0).const_mul _),
    integral_const_mul, integral_const_mul, hv.integral_Fsq, integral_inv_sq_add_sq hR0] at this
  exact this

end

end CF
