/-
Crux_axiso_construct.lean -- Class P, constructor seat: the kernel-checked core.

conjecture1_proved = False.

This file says nothing about where the zeros of `riemannZeta` itself lie. It checks the
parts of the constructor seat's report ("every counterexample route is blocked; class P
collapses to {zeta}; P2 and the pole normalization in P1 are the hypotheses doing the work")
that can be settled exactly, in the kernel, today.

Checked by: `cd telperion/examples/rvm_bridge/lean && lake env lean Crux/Crux_axiso_construct.lean`
(Lean v4.33.0-rc2, Mathlib 51e6992e, Zeta23 @ fbdc36bb). There is no `sorry`, no `admit`, no
`native_decide`, no `opaque`, and no new `axiom`. The `#print axioms` block at the end reports
only `propext`, `Classical.choice`, `Quot.sound`.

WHAT THIS FILE ESTABLISHES (every item is THEOREM-kernel-checked):

 A. Dirichlet-series toolkit. `IsLogDerivCoeff F g` says that `L g` has finite abscissa and
    equals `-F'/F` along a real ray to `+∞`. When `F = L a` with `a 1 = 1`:
    `logMul_eq_convolution` gives `a·log = g ⍟ a`, so `g` (the von Mangoldt function `Λ_F`) is
    UNIQUE whenever it exists. From that we get `logDerivCoeff_prime`,
    `logDerivCoeff_prime_sq` (`Λ_F(p²) = log p·(2a(p²) - a(p)²)`), the arithmetic half of the
    positivity lemma (`positivity_lemma`: P2 implies `a ≥ 0`), and a necessary condition,
    `P2_forces_sq_ineq` (P2 implies `a(p)² ≤ 2a(p²)`). Positive control: `zeta_P2`.
 B. NEAR-MISS 1, `F0 = ζ(s)(1+2^{-s})(1+2^{1-s})`. The factor `P0` is self-reciprocal with
    conductor 4 (`P0_reciprocal_four`). The completion `Xi0` is entire (`Xi0_entire`), satisfies
    `Xi0(1-s) = Xi0(s)` (`Xi0_one_sub`), and equals `s(s-1)2^sΓ_ℝ(s)F0(s)` (`Xi0_eq`).
    `F0 = L a0` with `a0(n) ∈ {1,4,6}` (`F0_eq_LSeries`, `a0_cases`), and `a0` is multiplicative
    (`a0_mul_coprime`). The zero set of `P0` is exactly `{i t_k} ∪ {1 + i t_k}` with
    `t_k = (2k+1)π/log 2` (`P0_eq_zero_iff`), so `Xi0` has zeros on `Re s = 1`
    (`Xi0_zero_offline`). The von Mangoldt series of `F0` EXISTS (`F0_logDeriv_exists`), has
    closed form `log 2·(1-(-1)^m-(-2)^m)` at `2^m` (`F0_vonMangoldt_two_pow`), and EVERY
    representation has `Λ_{F0}(4) = -4 log 2` (`F0_logDerivCoeff_four`). So P2 fails
    (`F0_not_P2`), while the functional equation, the entire completion, and the coefficient
    conditions checked above all hold (finite order is not checked).
 C. LEMMA C at prime conductor. If `1 + c p^{-s}` (real `c`, prime `p`) is self-reciprocal
    with conductor `p`, then `c² = p` (`Pc_selfRecip_sq`). This family is nonempty
    (`Pc_sqrt_selfRecip`), the von Mangoldt series exists (`Fc_logDeriv_exists`), and
    `Λ_F(p²) = (1-p) log p < 0`, so P2 fails for every member (`lemmaC_prime`). At conductor
    `p²`, every real self-reciprocal quadratic falls in one of two branches
    (`Pq_selfRecip_cases`), and both branches fail P2 for every prime `p`
    (`lemmaC_prime_sq`, through the polynomial fact `sq_family_core`).
 D. NEAR-MISS 2, `F1 = ζ(s/2+3/4)ζ(s/2-1/4)`. Its completion `Xi1` is entire, satisfies
    `Xi1(1-s) = Xi1(s)`, and equals a polynomial times ONE gamma factor `Γ_ℂ(s/2-1/4)` times
    `F1` (`Xi1_eq`). It has NO zero on `Re s = 1/2` (`Xi1_no_zero_on_line`). Every zero has real
    part in `(-3/2,1/2) ∪ (1/2,5/2)` (`Xi1_zero_re`). UNCONDITIONALLY it has zeros of
    arbitrarily large height with `1/2 < Re s < 5/2` (`Xi1_offline_zeros`, via Zeta23's
    hypothesis-free Riemann--von Mangoldt formula). P2 holds in Beurling form:
    `-F1'/F1 = Σ b1(n)(√n)^{-s}` with every `b1(n) ≥ 0` (`F1_logDeriv_hasSum`, `b1_nonneg`).
    The class-P pole normalization fails, because there is a genuine pole at `s = 1/2`
    (`F1_pole_half`).
 E. The E8-normalized twin `ζ(s/2+7/4)ζ(s/2-5/4)`. Its completion is entire and symmetric, it
    has no zero with real part in `[-3/2, 5/2]` (`XiE8_zero_re`), and it has unconditional zeros
    with `5/2 < Re s < 9/2` (`XiE8_offline_zeros`). Both D and E are cases of the family
    `XiPair a`, `a ≥ 3/4`.
 F. Theorem A, Step 3 (the Cohn--Elkies pairing), CONDITIONAL on the Step-2 pairing identity,
    which is taken as a hypothesis. The pointwise facts about `f = sinc(πx)²/(1-x²)` and
    `f̂ = (1-|t|+sin(2π|t|)/(2π))₊` are proved (`ceF_nonpos`, `ceF_eq_zero_iff`, `ceFhat_nonneg`,
    `ceFhat_eq_zero_of_one_le`), along with support forcing onto ℤ (`ce_support_forcing`,
    `thmA_step3_plus`) and the exclusion of `ε = -1` (`thmA_step3_minus`).
 G. Rescaling a degree-`d` object to center 1/2 moves its pole to `(d+1)/2`
    (`rescale_pole`, `rescale_reflect`).

WHAT THIS FILE DOES NOT ESTABLISH (these remain THEOREM-paper-proof or CONJECTURE; see
telperion/research/axiso_construct/README.md):
 - Theorem A as a whole. Step 2 (functional equation ⟹ distributional Poisson identity) and
   Step 4 (Hamburger's theorem) are not formalized. The Fourier-pair identity `𝓕 f = f̂` is
   certified symbolically in Python, not in Lean. The conductor bound rests on Theorem A.
 - Theorem B (it cites Kaczorowski--Perelli 1999 and Saias--Weingartner 2009). Lemma C for
   conductors other than `p` and `p²` (it needs Dirichlet approximation, Landau, and Hadamard). Prop D. The Landau
   half of the positivity lemma (the pole at 1, zero-freeness for `σ > 1`).
 - That the E8 Epstein zeta equals `240 ζ(u) ζ(u-3)`. This is classical and not in Mathlib.
   Here the twin is the product of zetas, by definition.
 - The twisted Beurling conjecture (CONJECTURE-with-evidence).
 - Anything about the Riemann hypothesis.
-/
import Mathlib
import Zeta23.RvM.Statement
import Zeta23.GammaFacts.Complete
import Zeta23.Assembly
import Zeta23.Statement.SeamClosed

open Complex LSeries Filter Topology MeasureTheory
open scoped LSeries.notation ComplexOrder Real

noncomputable section

namespace CruxAxisoConstruct

/-! ## A. Dirichlet-series toolkit (THEOREM-kernel-checked) -/

/-- Along real `x → +∞`, `(x : EReal)` eventually exceeds any `e < ⊤`. -/
lemma eventually_coe_gt {e : EReal} (he : e < ⊤) : ∀ᶠ x : ℝ in atTop, e < (x : EReal) := by
  obtain ⟨r, hr, -⟩ := EReal.exists_between_coe_real he
  filter_upwards [eventually_gt_atTop r] with x hx
  exact hr.trans (by exact_mod_cast hx)

/-- `IsLogDerivCoeff F g`: the Dirichlet series `L g` has finite abscissa of absolute
convergence and represents `-F'/F` along the real ray to `+∞`. Condition P2 for `F` is
`∃ g, IsLogDerivCoeff F g ∧ ∀ n, 0 ≤ g n` (with `ComplexOrder`: real and nonnegative). -/
def IsLogDerivCoeff (F : ℂ → ℂ) (g : ℕ → ℂ) : Prop :=
  abscissaOfAbsConv g < ⊤ ∧ ∀ᶠ x : ℝ in atTop, -deriv F x / F x = LSeries g x

/-- **Uniqueness of `Λ_F`.** If `F = L a`, `a 1 = 1`, and `L g = -F'/F` on a real ray, then
`log n · a n = (g ⍟ a) n` for all `n ≥ 1`. This recursion determines `g` from `a`. -/
theorem logMul_eq_convolution {a g : ℕ → ℂ} (ha : abscissaOfAbsConv a < ⊤) (ha1 : a 1 = 1)
    (hg : IsLogDerivCoeff (LSeries a) g) {n : ℕ} (hn : n ≠ 0) :
    logMul a n = (g ⍟ a) n := by
  obtain ⟨hgA, hgE⟩ := hg
  have hne : ∀ᶠ x : ℝ in atTop, LSeries a x ≠ 0 := by
    have h := LSeries.tendsto_atTop ha
    rw [ha1] at h
    exact h.eventually_ne one_ne_zero
  have key : ∀ᶠ x : ℝ in atTop, LSeries (logMul a) x = LSeries (g ⍟ a) x := by
    filter_upwards [hgE, hne, eventually_coe_gt ha, eventually_coe_gt hgA] with x hx hx0 hxa hxg
    have hxa' : abscissaOfAbsConv a < (x : ℂ).re := by simpa using hxa
    have hxg' : abscissaOfAbsConv g < (x : ℂ).re := by simpa using hxg
    have h1 : deriv (LSeries a) (x : ℂ) = -LSeries (logMul a) x := LSeries_deriv hxa'
    rw [h1, neg_neg] at hx
    rw [LSeries_convolution' (LSeriesSummable_of_abscissaOfAbsConv_lt_re hxg')
      (LSeriesSummable_of_abscissaOfAbsConv_lt_re hxa'), ← hx, div_mul_cancel₀ _ hx0]
  have hA1 : abscissaOfAbsConv (logMul a) < ⊤ := by rwa [LSeries.abscissaOfAbsConv_logMul]
  have hA2 : abscissaOfAbsConv (g ⍟ a) < ⊤ :=
    (LSeries.abscissaOfAbsConv_convolution_le g a).trans_lt (max_lt hgA ha)
  exact LSeries.eq_of_LSeries_eventually_eq hA1 hA2 key hn

lemma convolution_one_apply (g a : ℕ → ℂ) : (g ⍟ a) 1 = g 1 * a 1 := by
  simp [LSeries.convolution_def]

lemma convolution_prime_pow (g a : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (g ⍟ a) (p ^ k) = ∑ j ∈ Finset.range (k + 1), g (p ^ j) * a (p ^ (k - j)) := by
  rw [LSeries.convolution_def]
  simp only
  rw [Nat.sum_divisorsAntidiagonal (fun x y => g x * a y), Nat.divisors_prime_pow hp,
    Finset.sum_map]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Function.Embedding.coeFn_mk]
  rw [Nat.pow_div (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hp.pos]

lemma log_natCast_pow (p k : ℕ) : Complex.log ((p : ℂ) ^ k) = (k : ℂ) * (Real.log p : ℂ) := by
  rw [← Nat.cast_pow, ← Complex.natCast_log, Nat.cast_pow, Real.log_pow]
  push_cast
  ring

lemma logMul_prime_pow (a : ℕ → ℂ) (p k : ℕ) :
    logMul a (p ^ k) = ((k : ℂ) * (Real.log p : ℂ)) * a (p ^ k) := by
  simp only [LSeries.logMul]
  rw [Nat.cast_pow, log_natCast_pow]

theorem logDerivCoeff_one {a g : ℕ → ℂ} (ha : abscissaOfAbsConv a < ⊤) (ha1 : a 1 = 1)
    (hg : IsLogDerivCoeff (LSeries a) g) : g 1 = 0 := by
  have h := logMul_eq_convolution ha ha1 hg one_ne_zero
  rw [convolution_one_apply, ha1, mul_one] at h
  rw [← h]
  simp [LSeries.logMul]

theorem logDerivCoeff_prime {a g : ℕ → ℂ} (ha : abscissaOfAbsConv a < ⊤) (ha1 : a 1 = 1)
    (hg : IsLogDerivCoeff (LSeries a) g) {p : ℕ} (hp : p.Prime) :
    g p = (Real.log p : ℂ) * a p := by
  have h := logMul_eq_convolution ha ha1 hg (pow_ne_zero 1 hp.ne_zero)
  have h1 := logDerivCoeff_one ha ha1 hg
  rw [convolution_prime_pow g a hp 1, logMul_prime_pow] at h
  simp [Finset.sum_range_succ, h1, ha1] at h
  rw [Complex.natCast_log, ← h]

/-- `Λ_F(p²) = log p · (2 a(p²) - a(p)²)`. -/
theorem logDerivCoeff_prime_sq {a g : ℕ → ℂ} (ha : abscissaOfAbsConv a < ⊤) (ha1 : a 1 = 1)
    (hg : IsLogDerivCoeff (LSeries a) g) {p : ℕ} (hp : p.Prime) :
    g (p ^ 2) = (Real.log p : ℂ) * (2 * a (p ^ 2) - a p ^ 2) := by
  have h := logMul_eq_convolution ha ha1 hg (pow_ne_zero 2 hp.ne_zero)
  have h1 := logDerivCoeff_one ha ha1 hg
  have hp1 := logDerivCoeff_prime ha ha1 hg hp
  rw [convolution_prime_pow g a hp 2, logMul_prime_pow] at h
  simp [Finset.sum_range_succ, h1, ha1, hp1] at h
  rw [Complex.natCast_log]
  rw [Complex.natCast_log] at hp1
  linear_combination -h

/-- Positivity lemma, arithmetic core: nonnegative `Λ_F` forces nonnegative coefficients. -/
theorem coeff_nonneg_of_logDeriv_nonneg {a g : ℕ → ℂ} (ha1 : a 1 = 1)
    (hconv : ∀ n, n ≠ 0 → logMul a n = (g ⍟ a) n) (hg : ∀ n, 0 ≤ g n) :
    ∀ n, n ≠ 0 → 0 ≤ a n := by
  have hg1 : g 1 = 0 := by
    have h := hconv 1 one_ne_zero
    rw [convolution_one_apply, ha1, mul_one] at h
    rw [← h]
    simp [LSeries.logMul]
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn2
    · rw [ha1]; exact zero_le_one
    · have hrec := hconv n hn
      rw [LSeries.convolution_def] at hrec
      simp only at hrec
      have hsum : 0 ≤ ∑ x ∈ n.divisorsAntidiagonal, g x.1 * a x.2 := by
        refine Finset.sum_nonneg fun x hx => ?_
        obtain ⟨hmul, -⟩ := Nat.mem_divisorsAntidiagonal.mp hx
        by_cases hx1 : x.1 = 1
        · rw [hx1, hg1, zero_mul]
        · have hx10 : x.1 ≠ 0 := by rintro h; rw [h, zero_mul] at hmul; omega
          have hx20 : x.2 ≠ 0 := by rintro h; rw [h, mul_zero] at hmul; omega
          have hlt : x.2 < n := by
            rw [← hmul]
            have : 2 ≤ x.1 := by omega
            nlinarith [Nat.pos_of_ne_zero hx20]
          exact mul_nonneg (hg _) (ih _ hlt hx20)
      have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn2)
      have hlogC : (0 : ℂ) < (Real.log n : ℂ) := by exact_mod_cast hlog
      rw [← hrec] at hsum
      simp only [LSeries.logMul] at hsum
      rw [← Complex.natCast_log] at hsum
      have : a n = ((Real.log n)⁻¹ : ℝ) * ((Real.log n : ℂ) * a n) := by
        rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hlog.ne', Complex.ofReal_one,
          one_mul]
      rw [this]
      exact mul_nonneg (by exact_mod_cast (inv_pos.mpr hlog).le) hsum


/-- **Positivity lemma, analytic form.** If `F = L a` with `a 1 = 1` and finite abscissa, and
`-F'/F = L g` with every `g n ≥ 0` (P2), then every coefficient `a n` (`n ≥ 1`) is `≥ 0`. -/
theorem positivity_lemma {a g : ℕ → ℂ} (ha : abscissaOfAbsConv a < ⊤) (ha1 : a 1 = 1)
    (hg : IsLogDerivCoeff (LSeries a) g) (hpos : ∀ n, 0 ≤ g n) : ∀ n, n ≠ 0 → 0 ≤ a n :=
  coeff_nonneg_of_logDeriv_nonneg ha1 (fun _ hn => logMul_eq_convolution ha ha1 hg hn) hpos

/-- **P2 forces `a(p)² ≤ 2 a(p²)` at every prime `p`.** -/
theorem P2_forces_sq_ineq {a g : ℕ → ℂ} (ha : abscissaOfAbsConv a < ⊤) (ha1 : a 1 = 1)
    (hg : IsLogDerivCoeff (LSeries a) g) (hpos : ∀ n, 0 ≤ g n) {p : ℕ} (hp : p.Prime) :
    a p ^ 2 ≤ 2 * a (p ^ 2) := by
  have h := hpos (p ^ 2)
  rw [logDerivCoeff_prime_sq ha ha1 hg hp] at h
  have hl : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have h' : 0 ≤ ((Real.log p)⁻¹ : ℝ) * ((Real.log p : ℂ) * (2 * a (p ^ 2) - a p ^ 2)) :=
    mul_nonneg (by exact_mod_cast (inv_pos.mpr hl).le) h
  rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hl.ne', Complex.ofReal_one,
    one_mul] at h'
  exact sub_nonneg.mp h'

/-- Positive control: `ζ` itself satisfies P2 in the sense of `IsLogDerivCoeff`. -/
theorem zeta_P2 : IsLogDerivCoeff riemannZeta ↗ArithmeticFunction.vonMangoldt ∧
    ∀ n : ℕ, (0 : ℂ) ≤ ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) := by
  refine ⟨⟨?_, ?_⟩, fun n => ?_⟩
  · have h2 : (1 : ℝ) < ((2 : ℝ) : ℂ).re := by simp
    exact ((ArithmeticFunction.LSeriesSummable_vonMangoldt h2).abscissaOfAbsConv_le).trans_lt
      (by simp)
  · filter_upwards [eventually_gt_atTop 1] with x hx
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hx)]
  · exact Complex.zero_le_real.mpr ArithmeticFunction.vonMangoldt_nonneg

/-! ### Divisor-indicator L-series: `L [m ∣ ·] = m^{-s} ζ` -/

/-- The indicator of the multiples of `m`, as a coefficient sequence. -/
def dvdInd (m : ℕ) (n : ℕ) : ℂ := if m ∣ n then 1 else 0

lemma norm_dvdInd_le (m n : ℕ) : ‖dvdInd m n‖ ≤ 1 := by
  unfold dvdInd; split_ifs <;> simp

lemma one_lt_re_coe {s : ℂ} (hs : 1 < s.re) : (1 : EReal) < (s.re : EReal) := by
  exact_mod_cast hs

lemma LSeriesSummable_of_bounded {f : ℕ → ℂ} (C : ℝ) (hf : ∀ n, n ≠ 0 → ‖f n‖ ≤ C) {s : ℂ}
    (hs : 1 < s.re) : LSeriesSummable f s :=
  LSeriesSummable_of_abscissaOfAbsConv_lt_re
    ((LSeries.abscissaOfAbsConv_le_of_le_const ⟨C, hf⟩).trans_lt (one_lt_re_coe hs))

lemma LSeries_dvdInd {m : ℕ} (hm : m ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    LSeries (dvdInd m) s = (m : ℂ) ^ (-s) * riemannZeta s := by
  rw [← LSeries_one_eq_riemannZeta hs]
  unfold LSeries
  rw [← tsum_mul_left]
  have hinj : Function.Injective (fun k : ℕ => m * k) := fun a b h =>
    Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm) h
  have hsupp : Function.support (term (dvdInd m) s) ⊆ Set.range (fun k : ℕ => m * k) := by
    intro n hn
    rw [Function.mem_support] at hn
    by_cases hdvd : m ∣ n
    · obtain ⟨k, rfl⟩ := hdvd
      exact ⟨k, rfl⟩
    · exfalso; apply hn
      rcases eq_or_ne n 0 with rfl | hn0
      · simp
      · rw [term_of_ne_zero hn0]; simp [dvdInd, hdvd]
  rw [← hinj.tsum_eq hsupp]
  congr 1
  ext k
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · rw [term_of_ne_zero (mul_ne_zero hm hk), term_of_ne_zero hk]
    simp only [dvdInd, dvd_mul_right, if_true, Pi.one_apply, Nat.cast_mul]
    rw [Complex.natCast_mul_natCast_cpow, cpow_neg]
    have h1 : (m : ℂ) ^ s ≠ 0 := by
      rw [Ne, cpow_eq_zero_iff]; exact fun h => hm (by exact_mod_cast h.1)
    have h2 : (k : ℂ) ^ s ≠ 0 := by
      rw [Ne, cpow_eq_zero_iff]; exact fun h => hk (by exact_mod_cast h.1)
    field_simp

/-! ## B. NEAR-MISS 1: `F0 = ζ(s) (1 + 2^{-s}) (1 + 2^{1-s})` (THEOREM-kernel-checked)

It has the class-P functional equation (twisted, conductor 4), an Euler product, and
coefficients in `{1, 4, 6}`. It has zeros on `Re s = 0` and `Re s = 1`. The only class-P
condition it breaks is P2, at `n = 4`. -/

/-- The Dirichlet polynomial `P0(s) = 1 + 3·2^{-s} + 2·4^{-s}`. -/
def P0 (s : ℂ) : ℂ := 1 + 3 * (2 : ℂ) ^ (-s) + 2 * (4 : ℂ) ^ (-s)

/-- `F0 = ζ · P0`. -/
def F0 (s : ℂ) : ℂ := riemannZeta s * P0 s

/-- The coefficient sequence of `F0`: `a0(n) = 1 + 3·[2 ∣ n] + 2·[4 ∣ n]`. -/
def a0 : ℕ → ℂ := (1 : ℕ → ℂ) + (3 : ℂ) • dvdInd 2 + (2 : ℂ) • dvdInd 4

lemma a0_apply (n : ℕ) : a0 n = 1 + 3 * dvdInd 2 n + 2 * dvdInd 4 n := by
  simp [a0]

lemma four_cpow (x : ℂ) : (4 : ℂ) ^ x = (2 : ℂ) ^ x * (2 : ℂ) ^ x := by
  have h : (4 : ℂ) = ((2 : ℝ) : ℂ) * ((2 : ℝ) : ℂ) := by push_cast; norm_num
  rw [h, Complex.mul_cpow_ofReal_nonneg (by norm_num) (by norm_num)]
  norm_num

lemma P0_factor (s : ℂ) : P0 s = (1 + (2 : ℂ) ^ (-s)) * (1 + (2 : ℂ) ^ (1 - s)) := by
  have h : (2 : ℂ) ^ (1 - s) = 2 * (2 : ℂ) ^ (-s) := by
    rw [sub_eq_add_neg, cpow_add _ _ (by norm_num), cpow_one]
  rw [P0, h, four_cpow]
  ring

/-- `P0` is self-reciprocal with conductor `4`: `2^s P0(s) = 2^{1-s} P0(1-s)`. -/
theorem P0_reciprocal (s : ℂ) : (2 : ℂ) ^ s * P0 s = (2 : ℂ) ^ (1 - s) * P0 (1 - s) := by
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have hw : (2 : ℂ) ^ s ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; exact fun h => h2 h.1
  simp only [P0, four_cpow]
  rw [neg_sub, cpow_sub _ _ h2, cpow_sub _ _ h2, cpow_one, cpow_neg]
  field_simp
  ring

/-- The same self-reciprocity in conductor form: `P0(s) = 4^{1/2 - s} P0(1 - s)`. -/
theorem P0_reciprocal_four (s : ℂ) : P0 s = (4 : ℂ) ^ ((1 : ℂ) / 2 - s) * P0 (1 - s) := by
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have hw : (2 : ℂ) ^ s ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; exact fun h => h2 h.1
  have hsq : (2 : ℂ) ^ ((1 : ℂ) / 2 - s) * (2 : ℂ) ^ ((1 : ℂ) / 2 - s) = (2 : ℂ) ^ (1 - s) / 2 ^ s := by
    rw [← cpow_add _ _ h2, ← cpow_sub _ _ h2]
    ring_nf
  rw [four_cpow, hsq, div_mul_eq_mul_div, ← P0_reciprocal s]
  field_simp

/-- Transfer: if `F = L a` on a right half-plane, `F` and `L a` have the same log-derivative
coefficient sequences. -/
lemma isLogDerivCoeff_congr {F : ℂ → ℂ} {a : ℕ → ℂ} (σ : ℝ)
    (hF : ∀ s : ℂ, σ < s.re → F s = LSeries a s) {g : ℕ → ℂ} :
    IsLogDerivCoeff F g ↔ IsLogDerivCoeff (LSeries a) g := by
  have hev : ∀ x : ℝ, σ < x → F =ᶠ[𝓝 (x : ℂ)] LSeries a := by
    intro x hx
    have hx' : σ < (x : ℂ).re := by simpa using hx
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hx'] with y hy
    exact hF y hy
  unfold IsLogDerivCoeff
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    filter_upwards [h2, eventually_gt_atTop σ] with x hx hxσ
    rw [← (hev x hxσ).deriv_eq, ← (hev x hxσ).eq_of_nhds]
    exact hx
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    filter_upwards [h2, eventually_gt_atTop σ] with x hx hxσ
    rw [(hev x hxσ).deriv_eq, (hev x hxσ).eq_of_nhds]
    exact hx

lemma LSeriesSummable_one {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (1 : ℕ → ℂ) s :=
  LSeriesSummable_of_bounded 1 (fun n _ => by simp) hs

lemma LSeriesSummable_dvdInd (m : ℕ) {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (dvdInd m) s :=
  LSeriesSummable_of_bounded 1 (fun n _ => norm_dvdInd_le m n) hs

theorem F0_eq_LSeries {s : ℂ} (hs : 1 < s.re) : F0 s = LSeries a0 s := by
  have h1 := LSeriesSummable_one hs
  have h2 := LSeriesSummable_dvdInd 2 hs
  have h4 := LSeriesSummable_dvdInd 4 hs
  rw [a0, LSeries_add (h1.add (h2.smul 3)) (h4.smul 2), LSeries_add h1 (h2.smul 3),
    LSeries_smul, LSeries_smul, LSeries_one_eq_riemannZeta hs,
    LSeries_dvdInd two_ne_zero hs, LSeries_dvdInd four_ne_zero hs]
  simp only [F0, P0]
  push_cast
  ring

lemma a0_cases (n : ℕ) : a0 n = 1 ∨ a0 n = 4 ∨ a0 n = 6 := by
  rw [a0_apply]
  unfold dvdInd
  by_cases h4 : 4 ∣ n
  · have h2 : 2 ∣ n := dvd_trans (by norm_num) h4
    rw [if_pos h2, if_pos h4]; norm_num
  · by_cases h2 : 2 ∣ n
    · rw [if_pos h2, if_neg h4]; norm_num
    · rw [if_neg h2, if_neg h4]; norm_num

lemma a0_nonneg (n : ℕ) : 0 ≤ a0 n := by
  rcases a0_cases n with h | h | h <;> rw [h] <;> norm_num

lemma a0_one : a0 1 = 1 := by rw [a0_apply]; simp [dvdInd]
lemma a0_two : a0 2 = 4 := by rw [a0_apply]; simp [dvdInd]; norm_num
lemma a0_four : a0 4 = 6 := by
  rw [a0_apply]; simp only [dvdInd]
  rw [if_pos (by norm_num), if_pos (by norm_num)]; norm_num

lemma a0_abscissa : abscissaOfAbsConv a0 < ⊤ := by
  refine (LSeries.abscissaOfAbsConv_le_of_le_const ⟨6, fun n _ => ?_⟩).trans_lt
    (by exact_mod_cast EReal.coe_lt_top 1)
  rcases a0_cases n with h | h | h <;> rw [h] <;> norm_num

/-- **P2 FAILS for F0, exactly at n = 4.** Every Dirichlet series representing `-F0'/F0`
near `+∞` has coefficient `-4 log 2` at `n = 4`. -/
theorem F0_logDerivCoeff_four {g : ℕ → ℂ} (hg : IsLogDerivCoeff F0 g) :
    g 4 = ((-(4 * Real.log 2) : ℝ) : ℂ) := by
  rw [isLogDerivCoeff_congr 1 (fun s hs => F0_eq_LSeries hs)] at hg
  have h := logDerivCoeff_prime_sq a0_abscissa a0_one hg Nat.prime_two
  rw [show (2 : ℕ) ^ 2 = 4 by norm_num, a0_four, a0_two] at h
  rw [h]
  push_cast
  ring

theorem F0_not_P2 : ¬ ∃ g : ℕ → ℂ, IsLogDerivCoeff F0 g ∧ ∀ n, 0 ≤ g n := by
  rintro ⟨g, hg, hpos⟩
  have h4 := hpos 4
  rw [F0_logDerivCoeff_four hg, Complex.zero_le_real] at h4
  have : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

/-- The coefficients of `F0` are multiplicative, so `F0` has an Euler product. -/
theorem a0_mul_coprime {m n : ℕ} (h : Nat.Coprime m n) : a0 (m * n) = a0 m * a0 n := by
  have key : ∀ {m n : ℕ}, Nat.Coprime m n → ¬ 2 ∣ n → a0 (m * n) = a0 m * a0 n := by
    intro m n _ hn
    have hn4 : ¬ 4 ∣ n := fun h4 => hn (dvd_trans (by norm_num) h4)
    have hc4 : Nat.Coprime 4 n := by
      have h2n : Nat.Coprime 2 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hn
      simpa using Nat.Coprime.pow_left 2 h2n
    have h2 : 2 ∣ m * n ↔ 2 ∣ m := by
      constructor
      · intro h2; exact ((Nat.Prime.dvd_mul Nat.prime_two).mp h2).resolve_right hn
      · intro h2; exact dvd_mul_of_dvd_left h2 n
    have h4 : 4 ∣ m * n ↔ 4 ∣ m := by
      constructor
      · intro h4; exact hc4.dvd_of_dvd_mul_right h4
      · intro h4; exact dvd_mul_of_dvd_left h4 n
    simp only [a0_apply, dvdInd]
    rw [if_neg hn, if_neg hn4]
    by_cases hm2 : 2 ∣ m
    · rw [if_pos (h2.mpr hm2), if_pos hm2]
      by_cases hm4 : 4 ∣ m
      · rw [if_pos (h4.mpr hm4), if_pos hm4]; ring
      · rw [if_neg (fun h => hm4 (h4.mp h)), if_neg hm4]; ring
    · have hm4 : ¬ 4 ∣ m := fun h => hm2 (dvd_trans (by norm_num) h)
      rw [if_neg (fun h => hm2 (h2.mp h)), if_neg hm2, if_neg (fun h => hm4 (h4.mp h)),
        if_neg hm4]
      ring
  by_cases hn : 2 ∣ n
  · have hm : ¬ 2 ∣ m := fun hm => by
      have hg := Nat.dvd_gcd hm hn
      rw [h.gcd_eq_one] at hg
      exact absurd hg (by norm_num)
    rw [mul_comm m n, mul_comm (a0 m)]
    exact key h.symm hm
  · exact key h hn

/-! ### The entire completion `xiC u = u(u-1)Λ(u) = u(u-1)Λ₀(u) + 1` of zeta -/

/-- `xiC u = u (u-1) Λ₀(u) + 1`, the entire completion `u(u-1)Λ(u)` of zeta. -/
def xiC (u : ℂ) : ℂ := u * (u - 1) * completedRiemannZeta₀ u + 1

lemma differentiable_xiC : Differentiable ℂ xiC :=
  ((differentiable_id.mul (differentiable_id.sub_const 1)).mul
    differentiable_completedZeta₀).add_const 1

lemma xiC_one_sub (u : ℂ) : xiC (1 - u) = xiC u := by
  simp only [xiC, completedRiemannZeta₀_one_sub]
  ring

lemma xiC_eq_completed {u : ℂ} (h0 : u ≠ 0) (h1 : u ≠ 1) :
    xiC u = u * (u - 1) * completedRiemannZeta u := by
  have h1' : (1 - u) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have h1'' : (u - 1) ≠ 0 := sub_ne_zero.mpr h1
  rw [completedRiemannZeta_eq, xiC]
  field_simp
  ring

lemma completed_eq_Gammaℝ_mul {u : ℂ} (h0 : u ≠ 0) (hG : Gammaℝ u ≠ 0) :
    completedRiemannZeta u = Gammaℝ u * riemannZeta u := by
  rw [riemannZeta_def_of_ne_zero h0]
  field_simp

lemma xiC_eq_zeta {u : ℂ} (h0 : u ≠ 0) (h1 : u ≠ 1) (hG : Gammaℝ u ≠ 0) :
    xiC u = u * (u - 1) * Gammaℝ u * riemannZeta u := by
  rw [xiC_eq_completed h0 h1, completed_eq_Gammaℝ_mul h0 hG]
  ring

lemma xiC_one : xiC 1 = 1 := by simp [xiC]

lemma xiC_ne_zero_of_one_le_re {u : ℂ} (hu : 1 ≤ u.re) : xiC u ≠ 0 := by
  rcases eq_or_ne u 1 with rfl | h1
  · rw [xiC_one]; exact one_ne_zero
  have h0 : u ≠ 0 := by rintro rfl; simp at hu; linarith
  have hG : Gammaℝ u ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  rw [xiC_eq_zeta h0 h1 hG]
  have hz := riemannZeta_ne_zero_of_one_le_re hu
  have h1' : u - 1 ≠ 0 := sub_ne_zero.mpr h1
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero h0 h1') hG) hz

lemma xiC_ne_zero_of_re_nonpos {u : ℂ} (hu : u.re ≤ 0) : xiC u ≠ 0 := by
  rw [← xiC_one_sub]
  exact xiC_ne_zero_of_one_le_re (by simp; linarith)

/-- The zeros of `xiC` lie in the open critical strip. -/
lemma xiC_zero_strip {u : ℂ} (h : xiC u = 0) : 0 < u.re ∧ u.re < 1 := by
  refine ⟨?_, ?_⟩
  · by_contra hc; exact xiC_ne_zero_of_re_nonpos (not_lt.mp hc) h
  · by_contra hc; exact xiC_ne_zero_of_one_le_re (not_lt.mp hc) h

/-- A nontrivial zero of `ζ` (strip zero) is a zero of `xiC`. -/
lemma xiC_eq_zero_of_zeta {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    xiC ρ = 0 := by
  have hρ0 : ρ ≠ 0 := by rintro rfl; simp at h0
  have hρ1 : ρ ≠ 1 := by rintro rfl; simp at h1
  rw [xiC_eq_zeta hρ0 hρ1 (Complex.Gammaℝ_ne_zero_of_re_pos h0), hz, mul_zero]

/-- The completed `F0`: `Xi0(s) = 2^s P0(s) xiC(s)`. -/
def Xi0 (s : ℂ) : ℂ := (2 : ℂ) ^ s * P0 s * xiC s

lemma differentiable_P0 : Differentiable ℂ P0 := by
  unfold P0
  have h2 : Differentiable ℂ fun s : ℂ => (2 : ℂ) ^ (-s) :=
    differentiable_neg.const_cpow (Or.inl (by norm_num))
  have h4 : Differentiable ℂ fun s : ℂ => (4 : ℂ) ^ (-s) :=
    differentiable_neg.const_cpow (Or.inl (by norm_num))
  exact ((differentiable_const 1).add (h2.const_mul 3)).add (h4.const_mul 2)

theorem Xi0_entire : Differentiable ℂ Xi0 :=
  ((differentiable_id.const_cpow (Or.inl (by norm_num))).mul differentiable_P0).mul
    differentiable_xiC

theorem Xi0_one_sub (s : ℂ) : Xi0 (1 - s) = Xi0 s := by
  simp only [Xi0, xiC_one_sub, ← P0_reciprocal s]

theorem Xi0_eq {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) (hG : Gammaℝ s ≠ 0) :
    Xi0 s = s * (s - 1) * (2 : ℂ) ^ s * Gammaℝ s * F0 s := by
  rw [Xi0, xiC_eq_zeta h0 h1 hG, F0]
  ring

/-! ### The exact zero set of `P0` -/

/-- `t_k = (2k+1) π / log 2`. -/
def tk (k : ℤ) : ℝ := (2 * k + 1) * π / Real.log 2

lemma tk_neg (n : ℤ) : tk (-n - 1) = -tk n := by
  simp only [tk]; push_cast; ring

lemma log_two_ne_zero_C : (Real.log 2 : ℂ) ≠ 0 := by
  exact_mod_cast (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'

lemma clog_two : Complex.log 2 = (Real.log 2 : ℂ) := by
  rw [Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

lemma two_cpow_eq_neg_one_iff (w : ℂ) : (2 : ℂ) ^ w = -1 ↔ ∃ n : ℤ, w = (tk n : ℂ) * I := by
  have hl := log_two_ne_zero_C
  rw [cpow_def_of_ne_zero two_ne_zero, clog_two]
  constructor
  · intro h
    have h1 : Complex.exp ((Real.log 2 : ℂ) * w - π * I) = 1 := by
      rw [Complex.exp_sub, h, Complex.exp_pi_mul_I]; norm_num
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
    refine ⟨n, ?_⟩
    have hw : (Real.log 2 : ℂ) * w = (2 * n + 1) * π * I := by linear_combination hn
    have : w = ((2 * n + 1) * π * I) / (Real.log 2 : ℂ) := by rw [← hw]; field_simp
    rw [this]
    simp only [tk]
    push_cast
    ring
  · rintro ⟨n, rfl⟩
    have : (Real.log 2 : ℂ) * ((tk n : ℂ) * I) = (n : ℂ) * (2 * π * I) + π * I := by
      simp only [tk]; push_cast; field_simp
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, Complex.exp_pi_mul_I]
    ring

/-- **The zero set of `P0` is exactly `{i t_k} ∪ {1 + i t_k}`**: every zero of the Dirichlet
polynomial lies on `Re s = 0` or `Re s = 1`. -/
theorem P0_eq_zero_iff (s : ℂ) :
    P0 s = 0 ↔ ∃ k : ℤ, s = (tk k : ℂ) * I ∨ s = 1 + (tk k : ℂ) * I := by
  rw [P0_factor, mul_eq_zero]
  constructor
  · rintro (h | h)
    · obtain ⟨n, hn⟩ := (two_cpow_eq_neg_one_iff (-s)).mp (by linear_combination h)
      refine ⟨-n - 1, Or.inl ?_⟩
      rw [tk_neg]; push_cast; linear_combination -hn
    · obtain ⟨n, hn⟩ := (two_cpow_eq_neg_one_iff (1 - s)).mp (by linear_combination h)
      refine ⟨-n - 1, Or.inr ?_⟩
      rw [tk_neg]; push_cast; linear_combination -hn
  · rintro ⟨k, rfl | rfl⟩
    · left
      have : (2 : ℂ) ^ (-((tk k : ℂ) * I)) = -1 :=
        (two_cpow_eq_neg_one_iff _).mpr ⟨-k - 1, by rw [tk_neg]; push_cast; ring⟩
      rw [this]; ring
    · right
      have : (2 : ℂ) ^ (1 - (1 + (tk k : ℂ) * I)) = -1 :=
        (two_cpow_eq_neg_one_iff _).mpr ⟨-k - 1, by rw [tk_neg]; push_cast; ring⟩
      rw [this]; ring

theorem P0_zero_re {s : ℂ} (h : P0 s = 0) : s.re = 0 ∨ s.re = 1 := by
  obtain ⟨k, rfl | rfl⟩ := (P0_eq_zero_iff s).mp h
  · left; simp
  · right; simp

/-- `F0` and its entire, FE-symmetric completion `Xi0` vanish at `1 + i t_k`, a point with
real part `1`: zeros OFF the critical line `Re s = 1/2`. -/
theorem Xi0_zero_offline (k : ℤ) :
    F0 (1 + (tk k : ℂ) * I) = 0 ∧ Xi0 (1 + (tk k : ℂ) * I) = 0 ∧
      (1 + (tk k : ℂ) * I).re = 1 := by
  have hP : P0 (1 + (tk k : ℂ) * I) = 0 := (P0_eq_zero_iff _).mpr ⟨k, Or.inr rfl⟩
  refine ⟨by rw [F0, hP, mul_zero], by rw [Xi0, hP, mul_zero, zero_mul], by simp⟩

/-! ## C. LEMMA C at prime conductor (THEOREM-kernel-checked)

Every self-reciprocal `ζ · (1 + c p^{-s})` breaks P2. -/

/-- `Pc p c s = 1 + c p^{-s}`. -/
def Pc (p : ℕ) (c : ℝ) (s : ℂ) : ℂ := 1 + (c : ℂ) * (p : ℂ) ^ (-s)

/-- `Fc = ζ · Pc`. -/
def Fc (p : ℕ) (c : ℝ) (s : ℂ) : ℂ := riemannZeta s * Pc p c s

/-- coefficients of `Fc`: `1 + c [p ∣ n]`. -/
def ac (p : ℕ) (c : ℝ) : ℕ → ℂ := (1 : ℕ → ℂ) + (c : ℂ) • dvdInd p

lemma ac_apply (p : ℕ) (c : ℝ) (n : ℕ) : ac p c n = 1 + c * dvdInd p n := by simp [ac]

theorem Fc_eq_LSeries {p : ℕ} (hp : p ≠ 0) (c : ℝ) {s : ℂ} (hs : 1 < s.re) :
    Fc p c s = LSeries (ac p c) s := by
  rw [ac, LSeries_add (LSeriesSummable_one hs) ((LSeriesSummable_dvdInd p hs).smul _),
    LSeries_smul, LSeries_one_eq_riemannZeta hs, LSeries_dvdInd hp hs]
  simp only [Fc, Pc]
  ring

lemma ac_one {p : ℕ} (hp : 2 ≤ p) (c : ℝ) : ac p c 1 = 1 := by
  rw [ac_apply]
  simp [dvdInd, Nat.dvd_one, show p ≠ 1 by omega]

lemma ac_self (p : ℕ) (c : ℝ) : ac p c p = 1 + c := by
  rw [ac_apply]; simp [dvdInd]

lemma ac_sq (p : ℕ) (c : ℝ) : ac p c (p ^ 2) = 1 + c := by
  rw [ac_apply]; simp [dvdInd, dvd_pow_self p two_ne_zero]

lemma ac_abscissa (p : ℕ) (c : ℝ) : abscissaOfAbsConv (ac p c) < ⊤ := by
  refine (LSeries.abscissaOfAbsConv_le_of_le_const ⟨1 + |c|, fun n _ => ?_⟩).trans_lt
    (by exact_mod_cast EReal.coe_lt_top 1)
  rw [ac_apply]
  calc ‖1 + (c : ℂ) * dvdInd p n‖ ≤ ‖(1 : ℂ)‖ + ‖(c : ℂ)‖ * ‖dvdInd p n‖ := by
        rw [← norm_mul]; exact norm_add_le _ _
    _ ≤ 1 + |c| * 1 := by
        rw [norm_one, Complex.norm_real, Real.norm_eq_abs]
        gcongr
        exact norm_dvdInd_le p n
    _ = 1 + |c| := by ring

theorem Fc_logDerivCoeff_sq {p : ℕ} (hp : p.Prime) (c : ℝ) {g : ℕ → ℂ}
    (hg : IsLogDerivCoeff (Fc p c) g) : g (p ^ 2) = ((Real.log p * (1 - c ^ 2) : ℝ) : ℂ) := by
  rw [isLogDerivCoeff_congr 1 (fun s hs => Fc_eq_LSeries hp.ne_zero c hs)] at hg
  have h := logDerivCoeff_prime_sq (ac_abscissa p c) (ac_one hp.two_le c) hg hp
  rw [ac_sq, ac_self] at h
  rw [h]
  push_cast
  ring

/-- Self-reciprocity with conductor `p` forces `c² = p`. (Only the values at `s = 0, 2` are
used, and `E` is arbitrary.) -/
theorem Pc_selfRecip_sq {p : ℕ} (hp : 2 ≤ p) {c : ℝ} {E : ℂ}
    (h : ∀ s : ℂ, Pc p c s = E * (p : ℂ) ^ ((1 : ℂ) / 2 - s) * Pc p c (1 - s)) :
    c ^ 2 = p := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have h0 := h 0
  have h2 := h 2
  set T := E * (p : ℂ) ^ ((1 : ℂ) / 2) with hT
  have e0 : Pc p c 0 = 1 + c := by simp [Pc]
  have e1 : Pc p c (1 - 0) = 1 + c * (p : ℂ)⁻¹ := by
    simp only [Pc, sub_zero]; rw [cpow_neg_one]
  have e2 : Pc p c 2 = 1 + c * ((p : ℂ) ^ 2)⁻¹ := by
    simp only [Pc]; rw [cpow_neg, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, cpow_natCast]
  have e3 : Pc p c (1 - 2) = 1 + c * p := by
    simp only [Pc]; norm_num
  have q0 : (p : ℂ) ^ ((1 : ℂ) / 2 - 0) = (p : ℂ) ^ ((1 : ℂ) / 2) := by rw [sub_zero]
  have q2 : (p : ℂ) ^ ((1 : ℂ) / 2 - 2) = (p : ℂ) ^ ((1 : ℂ) / 2) * ((p : ℂ) ^ 2)⁻¹ := by
    rw [cpow_sub _ _ hp0, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, cpow_natCast, div_eq_mul_inv]
  rw [e0, e1, q0] at h0
  rw [e2, e3, q2] at h2
  have h0' : ((1 : ℂ) + c) * p = T * (p + c) := by
    rw [h0, hT]; field_simp
  have h2' : (p : ℂ) ^ 2 + c = T * (1 + c * p) := by
    have := congrArg (fun z => z * (p : ℂ) ^ 2) h2
    rw [hT]
    field_simp at this
    linear_combination this
  have key : ((p : ℂ) ^ 2 - 1) * (p - (c : ℂ) ^ 2) = 0 := by
    linear_combination (p + c) * h2' - (1 + c * p) * h0'
  have hp21 : (p : ℂ) ^ 2 - 1 ≠ 0 := by
    have : (1 : ℝ) < (p : ℝ) ^ 2 := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp
      nlinarith
    intro h'
    have : ((p : ℝ) ^ 2 - 1 : ℝ) = 0 := by exact_mod_cast h'
    linarith
  have := (mul_eq_zero.mp key).resolve_left hp21
  have : ((c ^ 2 : ℝ) : ℂ) = ((p : ℝ) : ℂ) := by push_cast; linear_combination -this
  exact_mod_cast this

/-- The self-reciprocal family is nonempty: `c = √p`, `E = 1`. -/
theorem Pc_sqrt_selfRecip {p : ℕ} (hp : 0 < p) (s : ℂ) :
    Pc p (Real.sqrt p) s = (p : ℂ) ^ ((1 : ℂ) / 2 - s) * Pc p (Real.sqrt p) (1 - s) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hsq : ((Real.sqrt p : ℝ) : ℂ) = (p : ℂ) ^ ((1 : ℂ) / 2) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    push_cast
    ring_nf
  have hr : (p : ℂ) ^ ((1 : ℂ) / 2) * (p : ℂ) ^ ((1 : ℂ) / 2) = p := by
    rw [← cpow_add _ _ hp0]; norm_num
  have hw : (p : ℂ) ^ s ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; exact fun h => hp0 h.1
  simp only [Pc]
  rw [hsq, cpow_sub _ _ hp0, neg_sub, cpow_sub _ _ hp0, cpow_one, cpow_neg]
  field_simp
  linear_combination (-(p : ℂ) ^ s) * hr

/-- **LEMMA C, prime conductor (kernel-checked).** If `P(s) = 1 + c p^{-s}` (real `c`, prime `p`)
is self-reciprocal with conductor `p`, then `F = ζ P` has `Λ_F(p²) = (1 - p) log p < 0`:
P2 fails. -/
theorem lemmaC_prime {p : ℕ} (hp : p.Prime) {c : ℝ} {E : ℂ}
    (h : ∀ s : ℂ, Pc p c s = E * (p : ℂ) ^ ((1 : ℂ) / 2 - s) * Pc p c (1 - s)) :
    (∀ g : ℕ → ℂ, IsLogDerivCoeff (Fc p c) g → g (p ^ 2) = ((Real.log p * (1 - p) : ℝ) : ℂ)) ∧
    ¬ ∃ g : ℕ → ℂ, IsLogDerivCoeff (Fc p c) g ∧ ∀ n, 0 ≤ g n := by
  have hc := Pc_selfRecip_sq hp.two_le h
  have hval : ∀ g : ℕ → ℂ, IsLogDerivCoeff (Fc p c) g →
      g (p ^ 2) = ((Real.log p * (1 - p) : ℝ) : ℂ) := by
    intro g hg
    rw [Fc_logDerivCoeff_sq hp c hg, hc]
  refine ⟨hval, ?_⟩
  rintro ⟨g, hg, hpos⟩
  have h4 := hpos (p ^ 2)
  rw [hval g hg, Complex.zero_le_real] at h4
  have hl : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  nlinarith

/-! ### Existence: the von Mangoldt series of `ζ · Π (1 + α q^{-s})`

This makes the P2 statements above non-vacuous: `Λ_F` exists, and by uniqueness its values
are forced. -/

/-- `geomCoeff q α` lives on the powers `q^k`, `k ≥ 1`, with value `log q · (-1)^{k+1} α^k`:
the Dirichlet coefficients of `-(d/ds) log (1 + α q^{-s})`. -/
def geomCoeff (q : ℕ) (α : ℂ) (n : ℕ) : ℂ :=
  if 2 ≤ n ∧ q ^ Nat.log q n = n then
    (Real.log q : ℂ) * (-1) ^ (Nat.log q n + 1) * α ^ Nat.log q n
  else 0

lemma geomCoeff_pow {q : ℕ} (hq : 2 ≤ q) (α : ℂ) (k : ℕ) :
    geomCoeff q α (q ^ (k + 1)) = (Real.log q : ℂ) * (-1) ^ (k + 2) * α ^ (k + 1) := by
  have hlog : Nat.log q (q ^ (k + 1)) = k + 1 := Nat.log_pow (by omega) _
  have h2 : 2 ≤ q ^ (k + 1) := le_trans hq (Nat.le_self_pow (by omega) q)
  simp [geomCoeff, hlog, h2]

lemma geomCoeff_eq_zero {q : ℕ} (α : ℂ) {n : ℕ}
    (hn : n ∉ Set.range (fun k : ℕ => q ^ (k + 1))) : geomCoeff q α n = 0 := by
  unfold geomCoeff
  rw [if_neg]
  rintro ⟨h2, hpow⟩
  apply hn
  have hne : Nat.log q n ≠ 0 := by
    intro h0; rw [h0, pow_zero] at hpow; omega
  refine ⟨Nat.log q n - 1, ?_⟩
  show q ^ (Nat.log q n - 1 + 1) = n
  rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hne)]
  exact hpow

lemma natCast_pow_cpow (q m : ℕ) (s : ℂ) : ((q ^ m : ℕ) : ℂ) ^ s = ((q : ℂ) ^ s) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih, pow_succ]

theorem geomCoeff_hasSum {q : ℕ} (hq : 2 ≤ q) (α : ℂ) {s : ℂ}
    (hα : ‖α * (q : ℂ) ^ (-s)‖ < 1) :
    LSeriesHasSum (geomCoeff q α) s
      ((Real.log q : ℂ) * (α * (q : ℂ) ^ (-s)) / (1 + α * (q : ℂ) ^ (-s))) := by
  set u := α * (q : ℂ) ^ (-s) with hu
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hqs : (q : ℂ) ^ s ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; exact fun h => hq0 h.1
  have hinj : Function.Injective (fun k : ℕ => q ^ (k + 1)) := by
    intro a b h
    have := Nat.pow_right_injective hq h
    omega
  unfold LSeriesHasSum
  rw [← hinj.hasSum_iff]
  · have hgeo : HasSum (fun k : ℕ => (-u) ^ k) (1 - (-u))⁻¹ :=
      hasSum_geometric_of_norm_lt_one (by rwa [norm_neg])
    have hgeo' := hgeo.mul_left ((Real.log q : ℂ) * u)
    have hval : (Real.log q : ℂ) * u * (1 - (-u))⁻¹ = (Real.log q : ℂ) * u / (1 + u) := by
      rw [sub_neg_eq_add, add_comm, div_eq_mul_inv]
    rw [hval] at hgeo'
    have hfun : (term (geomCoeff q α) s ∘ fun k : ℕ => q ^ (k + 1)) =
        fun i : ℕ => (Real.log q : ℂ) * u * (-u) ^ i := by
      funext k
      have hk : q ^ (k + 1) ≠ 0 := pow_ne_zero _ (by omega)
      simp only [Function.comp_apply]
      rw [term_of_ne_zero hk, geomCoeff_pow hq, natCast_pow_cpow, hu, cpow_neg,
        neg_pow (α * ((q : ℂ) ^ s)⁻¹) k, mul_pow, inv_pow]
      have hQk : ((q : ℂ) ^ s) ^ k ≠ 0 := pow_ne_zero _ hqs
      field_simp
      ring
    rw [hfun]
    exact hgeo'
  · intro n hn
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    · rw [term_of_ne_zero hn0, geomCoeff_eq_zero α hn, zero_div]

lemma hasDerivAt_one_add_mul_cpow {q : ℕ} (hq : 2 ≤ q) (α s : ℂ) :
    HasDerivAt (fun z : ℂ => 1 + α * (q : ℂ) ^ (-z))
      (-((Real.log q : ℂ) * (α * (q : ℂ) ^ (-s)))) s := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have h : HasDerivAt (fun z : ℂ => (q : ℂ) ^ (-z)) ((q : ℂ) ^ (-s) * Complex.log q * (-1)) s :=
    (hasDerivAt_neg s).const_cpow (Or.inl hq0)
  have h2 := (h.const_mul α).const_add 1
  exact h2.congr_deriv (by rw [← Complex.natCast_log]; ring)

lemma one_add_ne_zero_of_norm_lt {u : ℂ} (hu : ‖u‖ < 1) : 1 + u ≠ 0 := by
  intro h
  have : u = -1 := by linear_combination h
  rw [this, norm_neg, norm_one] at hu
  exact lt_irrefl _ hu

lemma norm_mul_cpow_neg {q : ℕ} (hq : 2 ≤ q) (α : ℂ) (s : ℂ) :
    ‖α * (q : ℂ) ^ (-s)‖ = ‖α‖ * (q : ℝ) ^ (-s.re) := by
  rw [norm_mul]
  congr 1
  have := Complex.norm_cpow_eq_rpow_re_of_pos (show (0 : ℝ) < q by exact_mod_cast (by omega : 0 < q)) (-s)
  simpa using this

/-- Abstract assembly: `-(ζ A B)'/(ζ A B) = L Λ + L c₁ + L c₂` from the three pieces. -/
lemma logDeriv_three {s : ℂ} (hs : 1 < s.re) {A B : ℂ → ℂ} {A' B' : ℂ}
    (hA : HasDerivAt A A' s) (hB : HasDerivAt B B' s) (hA0 : A s ≠ 0) (hB0 : B s ≠ 0) :
    -deriv (fun z => riemannZeta z * A z * B z) s / (riemannZeta s * A s * B s) =
      L ↗ArithmeticFunction.vonMangoldt s + (-A' / A s) + (-B' / B s) := by
  have hs1 : s ≠ 1 := by rintro rfl; simp at hs
  have hz : HasDerivAt riemannZeta (deriv riemannZeta s) s :=
    (differentiableAt_riemannZeta hs1).hasDerivAt
  have hz0 : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
  have hd : HasDerivAt (fun z => riemannZeta z * A z * B z)
      ((deriv riemannZeta s * A s + riemannZeta s * A') * B s +
        riemannZeta s * A s * B') s := (hz.mul hA).mul hB
  rw [hd.deriv, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  field_simp
  ring

/-- **Existence for F0**: `-F0'/F0` IS a Dirichlet series, with coefficients
`Λ(n) + geomCoeff 2 1 n + geomCoeff 2 2 n`. -/
theorem F0_logDeriv_exists :
    IsLogDerivCoeff F0 (↗ArithmeticFunction.vonMangoldt + geomCoeff 2 1 + geomCoeff 2 2) := by
  have hnorm : ∀ {s : ℂ}, 1 < s.re → ‖(1 : ℂ) * (2 : ℕ) ^ (-s)‖ < 1 ∧
      ‖(2 : ℂ) * (2 : ℕ) ^ (-s)‖ < 1 := by
    intro s hs
    rw [norm_mul_cpow_neg le_rfl, norm_mul_cpow_neg le_rfl]
    have h1 : (2 : ℝ) ^ (-s.re) < 2 ^ (-(1 : ℝ)) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    have h2 : (2 : ℝ) ^ (-(1 : ℝ)) = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
    rw [h2] at h1
    simp only [norm_one, one_mul, Complex.norm_ofNat]
    push_cast
    constructor <;> linarith
  have hsumm : ∀ {s : ℂ}, 1 < s.re → LSeriesSummable
      (↗ArithmeticFunction.vonMangoldt + geomCoeff 2 1 + geomCoeff 2 2) s := by
    intro s hs
    exact ((ArithmeticFunction.LSeriesSummable_vonMangoldt hs).add
      (geomCoeff_hasSum le_rfl 1 (hnorm hs).1).LSeriesSummable).add
      (geomCoeff_hasSum le_rfl 2 (hnorm hs).2).LSeriesSummable
  refine ⟨?_, ?_⟩
  · have h2 : (1 : ℝ) < ((2 : ℝ) : ℂ).re := by simp
    exact ((hsumm h2).abscissaOfAbsConv_le).trans_lt (by simp)
  · filter_upwards [eventually_gt_atTop 1] with x hx
    have hx' : 1 < (x : ℂ).re := by simpa using hx
    obtain ⟨hn1, hn2⟩ := hnorm hx'
    have hF0 : F0 = fun z => riemannZeta z * (1 + (1 : ℂ) * ((2 : ℕ) : ℂ) ^ (-z)) *
        (1 + (2 : ℂ) * ((2 : ℕ) : ℂ) ^ (-z)) := by
      funext z
      rw [F0, P0_factor, mul_assoc]
      congr 2
      · push_cast; ring
      · rw [sub_eq_add_neg, cpow_add _ _ (by norm_num), cpow_one]; push_cast; ring
    rw [hF0]
    have hA := hasDerivAt_one_add_mul_cpow le_rfl 1 (x : ℂ)
    have hB := hasDerivAt_one_add_mul_cpow le_rfl 2 (x : ℂ)
    rw [logDeriv_three hx' hA hB (one_add_ne_zero_of_norm_lt hn1) (one_add_ne_zero_of_norm_lt hn2)]
    have e1 := (geomCoeff_hasSum le_rfl 1 hn1).LSeries_eq
    have e2 := (geomCoeff_hasSum le_rfl 2 hn2).LSeries_eq
    rw [LSeries_add ((ArithmeticFunction.LSeriesSummable_vonMangoldt hx').add
        (geomCoeff_hasSum le_rfl 1 hn1).LSeriesSummable)
        (geomCoeff_hasSum le_rfl 2 hn2).LSeriesSummable,
      LSeries_add (ArithmeticFunction.LSeriesSummable_vonMangoldt hx')
        (geomCoeff_hasSum le_rfl 1 hn1).LSeriesSummable, e1, e2]
    field_simp

/-- The von Mangoldt function of `F0` exists and `Λ_{F0}(4) = -4 log 2 < 0`. -/
theorem F0_vonMangoldt_four :
    ∃ g : ℕ → ℂ, IsLogDerivCoeff F0 g ∧ g 4 = ((-(4 * Real.log 2) : ℝ) : ℂ) :=
  ⟨_, F0_logDeriv_exists, F0_logDerivCoeff_four F0_logDeriv_exists⟩

/-- Closed form on the powers of two: `Λ_{F0}(2^m) = log 2 · (1 - (-1)^m - (-2)^m)`, `m ≥ 1`. -/
theorem F0_vonMangoldt_two_pow (k : ℕ) :
    (↗ArithmeticFunction.vonMangoldt + geomCoeff 2 1 + geomCoeff 2 2) (2 ^ (k + 1)) =
      (Real.log 2 : ℂ) * (1 - (-1) ^ (k + 1) - (-2) ^ (k + 1)) := by
  simp only [Pi.add_apply]
  rw [geomCoeff_pow le_rfl, geomCoeff_pow le_rfl,
    ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero k),
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  push_cast
  rw [neg_pow (2 : ℂ) (k + 1)]
  ring

/-- **Existence for the prime-conductor family**: for `|c| < p`, `-Fc'/Fc` is the Dirichlet
series with coefficients `Λ + geomCoeff p c`. (Self-reciprocity gives `|c| = √p < p`.) -/
theorem Fc_logDeriv_exists {p : ℕ} (hp : 2 ≤ p) {c : ℝ} (hc : |c| < p) :
    IsLogDerivCoeff (Fc p c) (↗ArithmeticFunction.vonMangoldt + geomCoeff p c) := by
  have hnorm : ∀ {s : ℂ}, 1 < s.re → ‖(c : ℂ) * (p : ℂ) ^ (-s)‖ < 1 := by
    intro s hs
    rw [norm_mul_cpow_neg hp, Complex.norm_real, Real.norm_eq_abs]
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
    have h1 : (p : ℝ) ^ (-s.re) < (p : ℝ) ^ (-(1 : ℝ)) :=
      Real.rpow_lt_rpow_of_exponent_lt hp1 (by linarith)
    rw [Real.rpow_neg_one] at h1
    have hp0 : (0 : ℝ) < p := by linarith
    calc |c| * (p : ℝ) ^ (-s.re) ≤ |c| * (p : ℝ)⁻¹ := by gcongr
      _ < p * (p : ℝ)⁻¹ := by gcongr
      _ = 1 := by field_simp
  have hsumm : ∀ {s : ℂ}, 1 < s.re →
      LSeriesSummable (↗ArithmeticFunction.vonMangoldt + geomCoeff p c) s := by
    intro s hs
    exact (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).add
      (geomCoeff_hasSum hp c (hnorm hs)).LSeriesSummable
  refine ⟨?_, ?_⟩
  · have h2 : (1 : ℝ) < ((2 : ℝ) : ℂ).re := by simp
    exact ((hsumm h2).abscissaOfAbsConv_le).trans_lt (by simp)
  · filter_upwards [eventually_gt_atTop 1] with x hx
    have hx' : 1 < (x : ℂ).re := by simpa using hx
    have hn := hnorm hx'
    have hFc : Fc p c = fun z => riemannZeta z * (1 + (c : ℂ) * (p : ℂ) ^ (-z)) * 1 := by
      funext z; rw [Fc, Pc, mul_one]
    rw [hFc]
    have hA := hasDerivAt_one_add_mul_cpow hp (c : ℂ) (x : ℂ)
    rw [logDeriv_three hx' hA (hasDerivAt_const (x : ℂ) (1 : ℂ))
      (one_add_ne_zero_of_norm_lt hn) one_ne_zero]
    rw [LSeries_add (ArithmeticFunction.LSeriesSummable_vonMangoldt hx')
      (geomCoeff_hasSum hp c hn).LSeriesSummable, (geomCoeff_hasSum hp c hn).LSeries_eq]
    field_simp
    ring


/-! ## C'. LEMMA C at conductor `p²` (THEOREM-kernel-checked, every prime `p`)

A real self-reciprocal `P` of conductor `p²` is `1 + x p^{-s} + p·p^{-2s}` (`ε = +1`, any real
`x`) or `1 - p·p^{-2s}` (`ε = -1`) (`Pq_selfRecip_cases`). In the first branch
`Λ_F(p^k) = log p · (1 - s_k)`, `k ≤ 5`, with `s_k` the power sums of the inverse roots
(`Fq_plus_values`), and `sq_family_core` shows that some `1 - s_k < 0`. In the second branch,
`P2_forces_sq_ineq` is violated at `p`. Together with Section C, this covers every single-prime
conductor `q ∈ {p, p²}`. -/

/-- Power sums `s_k` of the inverse roots of `1 + x z + p z²` are `-x, x² - 2p, -x³ + 3px,
x⁴ - 4px² + 2p², -x⁵ + 5px³ - 5p²x`. For every real `x` and every `p ≥ 2`, one of the numbers
`1 - s_k` (`k ≤ 5`) is negative. -/
theorem sq_family_core (p x : ℝ) (hp : 2 ≤ p) :
    1 + x < 0 ∨ 1 + 2 * p - x ^ 2 < 0 ∨ 1 + x ^ 3 - 3 * p * x < 0 ∨
      1 - x ^ 4 + 4 * p * x ^ 2 - 2 * p ^ 2 < 0 ∨ 1 + x ^ 5 - 5 * p * x ^ 3 + 5 * p ^ 2 * x < 0 := by
  by_cases h1 : x < -1
  · left; linarith
  push Not at h1
  by_cases h2 : 2 * p + 1 < x ^ 2
  · right; left; linarith
  push Not at h2
  by_cases h3 : x ≤ 0
  · by_cases hx : x = -1
    · right; right; right; right
      subst hx
      nlinarith
    · have hxgt : -1 < x := lt_of_le_of_ne h1 (Ne.symm hx)
      have hu : x ^ 2 < 1 := by nlinarith
      right; right; right; left
      nlinarith [mul_pos (show (0 : ℝ) < 1 - x ^ 2 by linarith)
        (show (0 : ℝ) < 4 * p - 1 - x ^ 2 by nlinarith),
        mul_nonneg (show (0 : ℝ) ≤ p by linarith) (show (0 : ℝ) ≤ p - 2 by linarith),
        sq_nonneg x]
  · push Not at h3
    by_cases h4 : 2 * p ^ 2 + 1 < (x ^ 2 - 2 * p) ^ 2
    · right; right; right; left
      nlinarith
    · push Not at h4
      have hx1 : 1 ≤ x := by
        by_contra hc
        push Not at hc
        have hsq : x ^ 2 < 1 := by nlinarith
        have : (2 * p - 1) ^ 2 < (x ^ 2 - 2 * p) ^ 2 := by nlinarith
        nlinarith
      right; right; left
      by_cases h5 : x ^ 2 ≤ 2 * p
      · nlinarith [mul_le_mul_of_nonneg_left hx1 (show (0 : ℝ) ≤ 3 * p - x ^ 2 by linarith)]
      · push Not at h5
        have hx2 : 2 ≤ x := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hx2 (show (0 : ℝ) ≤ 3 * p - x ^ 2 by linarith)]


/-- The prime-power recursion `k log p · a(p^k) = Σ_{j ≤ k} Λ_F(p^j) a(p^{k-j})`. -/
theorem logDerivCoeff_prime_pow {a g : ℕ → ℂ} (ha : abscissaOfAbsConv a < ⊤) (ha1 : a 1 = 1)
    (hg : IsLogDerivCoeff (LSeries a) g) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ((k : ℂ) * (Real.log p : ℂ)) * a (p ^ k) =
      ∑ j ∈ Finset.range (k + 1), g (p ^ j) * a (p ^ (k - j)) := by
  rw [← logMul_prime_pow, logMul_eq_convolution ha ha1 hg (pow_ne_zero k hp.ne_zero),
    convolution_prime_pow g a hp k]

/-- `Pq p x y s = 1 + x p^{-s} + y p^{-2s}`. -/
def Pq (p : ℕ) (x y : ℝ) (s : ℂ) : ℂ :=
  1 + (x : ℂ) * (p : ℂ) ^ (-s) + (y : ℂ) * ((p : ℂ) ^ (-s)) ^ 2

/-- `Fq = ζ · Pq`. -/
def Fq (p : ℕ) (x y : ℝ) (s : ℂ) : ℂ := riemannZeta s * Pq p x y s

/-- coefficients of `Fq`: `1 + x [p ∣ n] + y [p² ∣ n]`. -/
def aq (p : ℕ) (x y : ℝ) : ℕ → ℂ := (1 : ℕ → ℂ) + (x : ℂ) • dvdInd p + (y : ℂ) • dvdInd (p ^ 2)

lemma aq_apply (p : ℕ) (x y : ℝ) (n : ℕ) :
    aq p x y n = 1 + x * dvdInd p n + y * dvdInd (p ^ 2) n := by simp [aq]

theorem Fq_eq_LSeries {p : ℕ} (hp : p ≠ 0) (x y : ℝ) {s : ℂ} (hs : 1 < s.re) :
    Fq p x y s = LSeries (aq p x y) s := by
  rw [aq, LSeries_add ((LSeriesSummable_one hs).add ((LSeriesSummable_dvdInd p hs).smul _))
      ((LSeriesSummable_dvdInd (p ^ 2) hs).smul _),
    LSeries_add (LSeriesSummable_one hs) ((LSeriesSummable_dvdInd p hs).smul _),
    LSeries_smul, LSeries_smul, LSeries_one_eq_riemannZeta hs, LSeries_dvdInd hp hs,
    LSeries_dvdInd (pow_ne_zero 2 hp) hs, natCast_pow_cpow]
  simp only [Fq, Pq]
  ring

lemma aq_one {p : ℕ} (hp : 2 ≤ p) (x y : ℝ) : aq p x y 1 = 1 := by
  have h1 : ¬ p ∣ 1 := by rw [Nat.dvd_one]; omega
  have h2 : ¬ p ^ 2 ∣ 1 := by
    rw [Nat.dvd_one]; intro h; have : p ≤ p ^ 2 := Nat.le_self_pow two_ne_zero p; omega
  rw [aq_apply]; simp [dvdInd, h1, h2]

lemma aq_self {p : ℕ} (hp : 2 ≤ p) (x y : ℝ) : aq p x y p = 1 + x := by
  have h2 : ¬ p ^ 2 ∣ p := by
    intro h
    have := Nat.le_of_dvd (by omega) h
    nlinarith
  rw [aq_apply]; simp [dvdInd, h2]

lemma aq_pow {p : ℕ} (x y : ℝ) {k : ℕ} (hk : 2 ≤ k) : aq p x y (p ^ k) = 1 + x + y := by
  have h1 : p ∣ p ^ k := dvd_pow_self p (by omega)
  have h2 : p ^ 2 ∣ p ^ k := pow_dvd_pow p hk
  rw [aq_apply]; simp [dvdInd, h1, h2]

lemma aq_abscissa (p : ℕ) (x y : ℝ) : abscissaOfAbsConv (aq p x y) < ⊤ := by
  refine (LSeries.abscissaOfAbsConv_le_of_le_const ⟨1 + |x| + |y|, fun n _ => ?_⟩).trans_lt
    (by exact_mod_cast EReal.coe_lt_top 1)
  rw [aq_apply]
  have hp := norm_dvdInd_le p n
  have hq := norm_dvdInd_le (p ^ 2) n
  calc ‖1 + (x : ℂ) * dvdInd p n + (y : ℂ) * dvdInd (p ^ 2) n‖
      ≤ ‖(1 : ℂ)‖ + ‖(x : ℂ) * dvdInd p n‖ + ‖(y : ℂ) * dvdInd (p ^ 2) n‖ := norm_add₃_le
    _ ≤ 1 + |x| * 1 + |y| * 1 := by
        rw [norm_one, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs]
        gcongr
    _ = 1 + |x| + |y| := by ring

/-- For the `ε = +1` branch `y = p`: the forced values `Λ_F(p^k) = log p · (1 - s_k)`,
`k = 1, …, 5`. -/
theorem Fq_plus_values {p : ℕ} (hp : p.Prime) (x : ℝ) {g : ℕ → ℂ}
    (hg : IsLogDerivCoeff (Fq p x p) g) :
    g p = ((Real.log p * (1 + x) : ℝ) : ℂ) ∧
    g (p ^ 2) = ((Real.log p * (1 + 2 * p - x ^ 2) : ℝ) : ℂ) ∧
    g (p ^ 3) = ((Real.log p * (1 + x ^ 3 - 3 * p * x) : ℝ) : ℂ) ∧
    g (p ^ 4) = ((Real.log p * (1 - x ^ 4 + 4 * p * x ^ 2 - 2 * p ^ 2) : ℝ) : ℂ) ∧
    g (p ^ 5) = ((Real.log p * (1 + x ^ 5 - 5 * p * x ^ 3 + 5 * p ^ 2 * x) : ℝ) : ℂ) := by
  have hp2 := hp.two_le
  rw [isLogDerivCoeff_congr 1 (fun s hs => Fq_eq_LSeries hp.ne_zero x p hs)] at hg
  have ha := aq_abscissa p x p
  have ha1 := aq_one hp2 x p
  have g1 := logDerivCoeff_one ha ha1 hg
  have e1 := aq_self hp2 x p
  have e2 := aq_pow (p := p) x p (le_refl 2)
  have e3 := aq_pow (p := p) x p (show 2 ≤ 3 by norm_num)
  have e4 := aq_pow (p := p) x p (show 2 ≤ 4 by norm_num)
  have e5 := aq_pow (p := p) x p (show 2 ≤ 5 by norm_num)
  have r1 := logDerivCoeff_prime_pow ha ha1 hg hp 1
  have r2 := logDerivCoeff_prime_pow ha ha1 hg hp 2
  have r3 := logDerivCoeff_prime_pow ha ha1 hg hp 3
  have r4 := logDerivCoeff_prime_pow ha ha1 hg hp 4
  have r5 := logDerivCoeff_prime_pow ha ha1 hg hp 5
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
    Nat.sub_zero, Nat.sub_self, g1, zero_mul, ha1, mul_one] at r1 r2 r3 r4 r5
  norm_num at r1 r2 r3 r4 r5
  rw [e1] at r1 r2 r3 r4 r5
  rw [e2] at r2 r3 r4 r5
  rw [e3] at r3 r4 r5
  rw [e4] at r4 r5
  rw [e5] at r5
  push_cast at r1 r2 r3 r4 r5
  have h1 : g p = Complex.log p * (1 + x) := by linear_combination -r1
  have h2 : g (p ^ 2) = Complex.log p * (1 + 2 * p - x ^ 2) := by
    linear_combination -r2 - (1 + (x : ℂ)) * h1
  have h3 : g (p ^ 3) = Complex.log p * (1 + x ^ 3 - 3 * p * x) := by
    linear_combination -r3 - (1 + (x : ℂ) + p) * h1 - (1 + (x : ℂ)) * h2
  have h4 : g (p ^ 4) = Complex.log p * (1 - x ^ 4 + 4 * p * x ^ 2 - 2 * p ^ 2) := by
    linear_combination -r4 - (1 + (x : ℂ) + p) * h1 - (1 + (x : ℂ) + p) * h2 -
      (1 + (x : ℂ)) * h3
  have h5 : g (p ^ 5) = Complex.log p * (1 + x ^ 5 - 5 * p * x ^ 3 + 5 * p ^ 2 * x) := by
    linear_combination -r5 - (1 + (x : ℂ) + p) * h1 - (1 + (x : ℂ) + p) * h2 -
      (1 + (x : ℂ) + p) * h3 - (1 + (x : ℂ)) * h4
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h1]; push_cast; ring
  · rw [h2]; push_cast; ring
  · rw [h3]; push_cast; ring
  · rw [h4]; push_cast; ring
  · rw [h5]; push_cast; ring

/-- **LEMMA C, conductor `p²`, branch `ε = +1` (every prime `p`, every real `x`).** -/
theorem lemmaC_prime_sq_plus {p : ℕ} (hp : p.Prime) (x : ℝ) :
    ¬ ∃ g : ℕ → ℂ, IsLogDerivCoeff (Fq p x p) g ∧ ∀ n, 0 ≤ g n := by
  rintro ⟨g, hg, hpos⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := Fq_plus_values hp x hg
  have hl : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have q1 := hpos p; have q2 := hpos (p ^ 2); have q3 := hpos (p ^ 3)
  have q4 := hpos (p ^ 4); have q5 := hpos (p ^ 5)
  rw [h1, Complex.zero_le_real] at q1
  rw [h2, Complex.zero_le_real] at q2
  rw [h3, Complex.zero_le_real] at q3
  rw [h4, Complex.zero_le_real] at q4
  rw [h5, Complex.zero_le_real] at q5
  rcases sq_family_core p x hp2 with c | c | c | c | c
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith

/-- **LEMMA C, conductor `p²`, branch `ε = -1`:** `ζ(s)(1 - p·p^{-2s})` violates
`a(p)² ≤ 2a(p²)`. -/
theorem lemmaC_prime_sq_minus {p : ℕ} (hp : p.Prime) :
    ¬ ∃ g : ℕ → ℂ, IsLogDerivCoeff (Fq p 0 (-p)) g ∧ ∀ n, 0 ≤ g n := by
  rintro ⟨g, hg, hpos⟩
  rw [isLogDerivCoeff_congr 1 (fun s hs => Fq_eq_LSeries hp.ne_zero 0 (-p) hs)] at hg
  have h := P2_forces_sq_ineq (aq_abscissa p 0 (-p)) (aq_one hp.two_le 0 (-p)) hg hpos hp
  rw [aq_self hp.two_le, aq_pow 0 (-p) (le_refl 2)] at h
  have hre := (Complex.le_def.mp h).1
  simp at hre
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  linarith

/-- Self-reciprocity with conductor `p²` leaves exactly two branches: `y = p` (`ε = +1`, any `x`)
or `x = 0, y = -p` (`ε = -1`). Only the values at `s = 0, 1, 2` are used, and `E` is arbitrary. -/
theorem Pq_selfRecip_cases {p : ℕ} (hp : 2 ≤ p) {x y : ℝ} {E : ℂ}
    (h : ∀ s : ℂ, Pq p x y s = E * (p : ℂ) ^ (1 - 2 * s) * Pq p x y (1 - s)) :
    y = p ∨ (x = 0 ∧ y = -p) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  set u : ℂ := (p : ℂ)⁻¹ with hu
  have hpu : (p : ℂ) * u = 1 := by rw [hu]; field_simp
  have pw : ∀ n : ℕ, (p : ℂ) ^ (-(n : ℂ)) = u ^ n := fun n => by
    rw [cpow_neg, cpow_natCast, hu, inv_pow]
  have e0 : Pq p x y 0 = 1 + x + y := by simp [Pq]
  have e1 : Pq p x y 1 = 1 + x * u + y * u ^ 2 := by
    simp only [Pq]; rw [show -(1 : ℂ) = -((1 : ℕ) : ℂ) by norm_num, pw]; ring
  have e2 : Pq p x y 2 = 1 + x * u ^ 2 + y * u ^ 4 := by
    simp only [Pq]; rw [show -(2 : ℂ) = -((2 : ℕ) : ℂ) by norm_num, pw]; ring
  have em : Pq p x y (-1) = 1 + x * p + y * p ^ 2 := by
    simp only [Pq]; rw [neg_neg, cpow_one]
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  rw [e0, show (1 : ℂ) - 2 * 0 = ((1 : ℕ) : ℂ) by norm_num, cpow_natCast, pow_one,
    show (1 : ℂ) - 0 = 1 by ring, e1] at h0
  rw [e1, show (1 : ℂ) - 2 * 1 = -((1 : ℕ) : ℂ) by norm_num, pw, pow_one,
    show (1 : ℂ) - 1 = 0 by ring, e0] at h1
  rw [e2, show (1 : ℂ) - 2 * 2 = -((3 : ℕ) : ℂ) by norm_num, pw,
    show (1 : ℂ) - 2 = -1 by ring, em] at h2
  have q0 : (1 - E * y * u) + (x - E * x) + (y - E * p) = 0 := by
    linear_combination h0 + (E * x + E * y * u) * hpu
  have q1 : (1 - E * y * u) + (x - E * x) * u + (y - E * p) * u ^ 2 = 0 := by
    linear_combination h1 - E * u * hpu
  have q2 : (1 - E * y * u) + (x - E * x) * u ^ 2 + (y - E * p) * u ^ 4 = 0 := by
    linear_combination h2 + (E * x * u ^ 2 + E * y * u * (p * u + 1) - E * u ^ 3) * hpu
  have hu0 : u ≠ 0 := by rw [hu]; exact inv_ne_zero hp0
  have hu1 : 1 - u ≠ 0 := by
    intro h'
    have : (p : ℂ) = 1 := by
      have hu' : u = 1 := by linear_combination -h'
      rw [hu'] at hpu; linear_combination hpu
    have : p = 1 := by exact_mod_cast this
    omega
  have hu2 : 1 + u ≠ 0 := by
    intro h'
    have hu' : u = -1 := by linear_combination h'
    rw [hu'] at hpu
    have : ((p : ℝ) : ℂ) = ((-1 : ℝ) : ℂ) := by push_cast; linear_combination -hpu
    have : (p : ℝ) = -1 := by exact_mod_cast this
    have : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    linarith
  have k1 : (1 - u) * ((x - E * x) + (y - E * p) * (1 + u)) = 0 := by
    linear_combination q0 - q1
  have k2 : u * (1 - u) * ((x - E * x) + (y - E * p) * u * (1 + u)) = 0 := by
    linear_combination q1 - q2
  have m1 := (mul_eq_zero.mp k1).resolve_left hu1
  have m2 := (mul_eq_zero.mp k2).resolve_left (mul_ne_zero hu0 hu1)
  have k3 : (y - E * p) * ((1 + u) * (1 - u)) = 0 := by linear_combination m1 - m2
  have c2 : (y : ℂ) - E * p = 0 := (mul_eq_zero.mp k3).resolve_right (mul_ne_zero hu2 hu1)
  have c1 : (x : ℂ) - E * x = 0 := by linear_combination m1 - (1 + u) * c2
  have c0 : 1 - E * y * u = 0 := by linear_combination q0 - c1 - c2
  have hE : (E - 1) * (E + 1) = 0 := by
    linear_combination -c0 - E * u * c2 - E ^ 2 * hpu
  rcases mul_eq_zero.mp hE with hE1 | hE1
  · left
    have hE' : E = 1 := by linear_combination hE1
    rw [hE'] at c2
    have : ((y : ℝ) : ℂ) = ((p : ℝ) : ℂ) := by push_cast; linear_combination c2
    exact_mod_cast this
  · right
    have hE' : E = -1 := by linear_combination hE1
    rw [hE'] at c1 c2
    constructor
    · have : ((x : ℝ) : ℂ) = ((0 : ℝ) : ℂ) := by push_cast; linear_combination c1 / 2
      exact_mod_cast this
    · have : ((y : ℝ) : ℂ) = ((-(p : ℝ) : ℝ) : ℂ) := by push_cast; linear_combination c2
      exact_mod_cast this

/-- Both branches really are self-reciprocal (the hypothesis of `lemmaC_prime_sq` is satisfiable
for every `x`). -/
theorem Pq_plus_selfRecip {p : ℕ} (hp : 0 < p) (x : ℝ) (s : ℂ) :
    Pq p x p s = (p : ℂ) ^ (1 - 2 * s) * Pq p x p (1 - s) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hw : (p : ℂ) ^ s ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; exact fun h => hp0 h.1
  simp only [Pq]
  rw [cpow_sub _ _ hp0, cpow_one, neg_sub, cpow_sub _ _ hp0, cpow_one, cpow_neg,
    show (2 : ℂ) * s = ((2 : ℕ) : ℂ) * s by norm_num, cpow_nat_mul]
  push_cast
  field_simp
  ring

theorem Pq_minus_selfRecip {p : ℕ} (hp : 0 < p) (s : ℂ) :
    Pq p 0 (-p) s = -1 * (p : ℂ) ^ (1 - 2 * s) * Pq p 0 (-p) (1 - s) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hw : (p : ℂ) ^ s ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; exact fun h => hp0 h.1
  simp only [Pq]
  rw [cpow_sub _ _ hp0, cpow_one, neg_sub, cpow_sub _ _ hp0, cpow_one, cpow_neg,
    show (2 : ℂ) * s = ((2 : ℕ) : ℂ) * s by norm_num, cpow_nat_mul]
  push_cast
  field_simp
  ring

/-- **LEMMA C at conductor `p²` (kernel-checked, every prime `p`).** If
`P(s) = 1 + x p^{-s} + y p^{-2s}` (real `x, y`) is self-reciprocal with conductor `p²`, then
`F = ζ P` fails P2. -/
theorem lemmaC_prime_sq {p : ℕ} (hp : p.Prime) {x y : ℝ} {E : ℂ}
    (h : ∀ s : ℂ, Pq p x y s = E * (p : ℂ) ^ (1 - 2 * s) * Pq p x y (1 - s)) :
    ¬ ∃ g : ℕ → ℂ, IsLogDerivCoeff (Fq p x y) g ∧ ∀ n, 0 ≤ g n := by
  rcases Pq_selfRecip_cases hp.two_le h with hy | ⟨hx, hy⟩
  · subst hy; exact lemmaC_prime_sq_plus hp x
  · subst hx; subst hy; exact lemmaC_prime_sq_minus hp

/-! ## D/E. The two-factor family and the near-miss F1 (THEOREM-kernel-checked)

### Unconditional nontrivial zeros of ζ (via Zeta23's Riemann--von Mangoldt formula)

Zeta23 enters the file only through the next theorem. That theorem consumes the hypothesis-free
`Zeta23.RvM.riemannVonMangoldt Zeta23.gammaFacts`, `Zeta23.Assembly.eventually_N_ge`, and
`Zeta23.Assembly.tendsto_Tl_atTop`, together with the definitions `Zeta23.zetaZeroConfig`,
`Zeta23.l`, and `Zeta23.IsNontrivialZero`. -/

/-- For every height `T` there is a zero `ρ` of `ζ` with `0 < Re ρ < 1` and `Im ρ > T`.
Re-derived here from Zeta23's hypothesis-free Riemann--von Mangoldt formula. -/
theorem exists_nontrivial_zero_above (T : ℝ) :
    ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ T < ρ.im := by
  have hRvM := Zeta23.RvM.riemannVonMangoldt Zeta23.gammaFacts
  have h1 := Zeta23.Assembly.eventually_N_ge Zeta23.zetaZeroConfig hRvM
  have h2 : ∀ᶠ T' : ℝ in atTop, 4 * Real.pi < T' * Zeta23.l T' :=
    Zeta23.Assembly.tendsto_Tl_atTop.eventually_gt_atTop _
  obtain ⟨T', ⟨hT1, hT2⟩, hT3⟩ := ((h1.and h2).and (eventually_ge_atTop T)).exists
  have hpos : (0 : ℝ) < (Zeta23.zetaZeroConfig.N T' (2 * T') : ℝ) := by
    refine lt_of_lt_of_le ?_ hT1
    rw [lt_div_iff₀ (by positivity), zero_mul]
    linarith [Real.pi_pos]
  have hne : (Zeta23.zetaZeroConfig.window T' (2 * T')).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    simp [Zeta23.ZeroConfig.N, h] at hpos
  obtain ⟨ρ, hρ, hρT, -⟩ := hne
  have hρ' : Zeta23.IsNontrivialZero ρ := hρ
  exact ⟨ρ, hρ'.1, hρ'.2.1, hρ'.2.2, lt_of_le_of_lt hT3 hρT⟩

/-! ### The two-factor family `XiPair a s = xiC (s/2 + a) xiC (s/2 + 1/2 - a)` -/

/-- `XiPair a s = xiC(s/2 + a) · xiC(s/2 + 1/2 - a)`: entire and symmetric under `s ↦ 1-s`. -/
def XiPair (a : ℝ) (s : ℂ) : ℂ := xiC (s / 2 + a) * xiC (s / 2 + (1 / 2 - a))

theorem XiPair_entire (a : ℝ) : Differentiable ℂ (XiPair a) :=
  (differentiable_xiC.comp ((differentiable_id.div_const 2).add_const _)).mul
    (differentiable_xiC.comp ((differentiable_id.div_const 2).add_const _))

theorem XiPair_one_sub (a : ℝ) (s : ℂ) : XiPair a (1 - s) = XiPair a s := by
  unfold XiPair
  have e1 : (1 - s) / 2 + (a : ℂ) = 1 - (s / 2 + (1 / 2 - a)) := by ring
  have e2 : (1 - s) / 2 + (1 / 2 - (a : ℂ)) = 1 - (s / 2 + a) := by ring
  rw [e1, e2, xiC_one_sub, xiC_one_sub, mul_comm]

theorem XiPair_zero_re {a : ℝ} {s : ℂ} (h : XiPair a s = 0) :
    (-2 * a < s.re ∧ s.re < 2 - 2 * a) ∨ (2 * a - 1 < s.re ∧ s.re < 2 * a + 1) := by
  unfold XiPair at h
  rcases mul_eq_zero.mp h with h | h
  · left
    have := xiC_zero_strip h
    simp at this
    constructor <;> linarith [this.1, this.2]
  · right
    have := xiC_zero_strip h
    simp at this
    constructor <;> linarith [this.1, this.2]

/-- For `a ≥ 3/4` the entire, FE-symmetric `XiPair a` has NO zero on `Re s = 1/2`. -/
theorem XiPair_no_zero_on_line {a : ℝ} (ha : 3 / 4 ≤ a) {s : ℂ} (hs : s.re = 1 / 2) :
    XiPair a s ≠ 0 := by
  intro h
  rcases XiPair_zero_re h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith

/-- Every nontrivial zero `ρ` of `ζ` produces the zero `s = 2ρ - 1 + 2a` of `XiPair a`. -/
theorem XiPair_zero_of_zeta_zero (a : ℝ) {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) : XiPair a (2 * ρ - 1 + 2 * a) = 0 := by
  unfold XiPair
  have : (2 * ρ - 1 + 2 * (a : ℂ)) / 2 + (1 / 2 - (a : ℂ)) = ρ := by ring
  rw [this, xiC_eq_zero_of_zeta hz h0 h1, mul_zero]

/-- **Unconditional**: for `a ≥ 3/4`, `XiPair a` has zeros of arbitrarily large height, all
off the critical line (real part in `(2a-1, 2a+1)`, so `> 1/2`). -/
theorem XiPair_offline_zeros (a : ℝ) (T : ℝ) :
    ∃ s : ℂ, XiPair a s = 0 ∧ 2 * a - 1 < s.re ∧ s.re < 2 * a + 1 ∧ 2 * T < s.im := by
  obtain ⟨ρ, hz, h0, h1, hT⟩ := exists_nontrivial_zero_above T
  refine ⟨2 * ρ - 1 + 2 * a, XiPair_zero_of_zeta_zero a hz h0 h1, ?_, ?_, ?_⟩ <;> simp <;> linarith

/-! ### NEAR-MISS 2: `F1(s) = ζ(s/2 + 3/4) ζ(s/2 - 1/4)`

It has P2 (Beurling form), an Euler product over the Beurling primes `√p`, one gamma factor, and
an exact FE about `1/2`, yet NO zero on the critical line and infinitely many off it. The only
thing it breaks is the class-P pole normalization. -/

/-- `F1(s) = ζ(s/2 + 3/4) ζ(s/2 - 1/4)`. -/
def F1 (s : ℂ) : ℂ := riemannZeta (s / 2 + 3 / 4) * riemannZeta (s / 2 - 1 / 4)

/-- The completion of `F1`. -/
def Xi1 : ℂ → ℂ := XiPair (3 / 4)

lemma Xi1_apply (s : ℂ) : Xi1 s = xiC (s / 2 + 3 / 4) * xiC (s / 2 - 1 / 4) := by
  simp only [Xi1, XiPair]
  congr 2 <;> push_cast <;> ring

/-- `Xi1` is `F1` times ONE gamma factor `Γ_ℂ(s/2 - 1/4) = 2 (2π)^{1/4 - s/2} Γ(s/2 - 1/4)` and a
polynomial with roots at `-3/2, 1/2, 1/2, 5/2` (in place of the class-P `s(s-1)`). -/
theorem Xi1_eq {s : ℂ} (hs : 1 / 2 < s.re) (hs' : s ≠ 5 / 2) :
    Xi1 s = (s / 2 + 3 / 4) * (s / 2 - 1 / 4) * (s / 2 - 1 / 4) * (s / 2 - 5 / 4) *
      Gammaℂ (s / 2 - 1 / 4) * F1 s := by
  set w := s / 2 + 3 / 4 with hw
  set v := s / 2 - 1 / 4 with hv
  have hwre : 1 < w.re := by rw [hw]; simp; linarith
  have hvre : 0 < v.re := by rw [hv]; simp; linarith
  have hw0 : w ≠ 0 := by rintro h; rw [h] at hwre; simp at hwre; linarith
  have hw1 : w ≠ 1 := by rintro h; rw [h] at hwre; simp at hwre
  have hv0 : v ≠ 0 := by rintro h; rw [h] at hvre; simp at hvre
  have hv1 : v ≠ 1 := by
    rintro h; apply hs'
    have : s = 2 * v + 1 / 2 := by rw [hv]; ring
    rw [this, h]; norm_num
  have hvw : v + 1 = w := by rw [hv, hw]; ring
  rw [Xi1_apply, xiC_eq_zeta hw0 hw1 (Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)),
    xiC_eq_zeta hv0 hv1 (Complex.Gammaℝ_ne_zero_of_re_pos hvre), F1,
    ← Complex.Gammaℝ_mul_Gammaℝ_add_one v, hvw]
  have : v - 1 = s / 2 - 5 / 4 := by rw [hv]; ring
  have h2 : w - 1 = v := by rw [← hvw]; ring
  rw [h2]
  rw [← this]
  ring

theorem Xi1_one_sub (s : ℂ) : Xi1 (1 - s) = Xi1 s := XiPair_one_sub _ s

theorem Xi1_entire : Differentiable ℂ Xi1 := XiPair_entire _

theorem Xi1_no_zero_on_line {s : ℂ} (hs : s.re = 1 / 2) : Xi1 s ≠ 0 :=
  XiPair_no_zero_on_line (le_refl _) hs

/-- Every zero of `Xi1` is off the line: real part in `(-3/2, 1/2)` or `(1/2, 5/2)`. -/
theorem Xi1_zero_re {s : ℂ} (h : Xi1 s = 0) :
    (-3 / 2 < s.re ∧ s.re < 1 / 2) ∨ (1 / 2 < s.re ∧ s.re < 5 / 2) := by
  rcases XiPair_zero_re h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; constructor <;> linarith
  · right; constructor <;> linarith

/-- **Unconditional**: `Xi1` (entire, `Xi1(1-s) = Xi1(s)`) has zeros of arbitrarily large
height, each with `1/2 < Re s < 5/2`; and `F1` vanishes there too. -/
theorem Xi1_offline_zeros (T : ℝ) :
    ∃ s : ℂ, Xi1 s = 0 ∧ F1 s = 0 ∧ 1 / 2 < s.re ∧ s.re < 5 / 2 ∧ T < s.im := by
  obtain ⟨ρ, hz, h0, h1, hT⟩ := exists_nontrivial_zero_above (T / 2)
  refine ⟨2 * ρ + 1 / 2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Xi1_apply]
    have : (2 * ρ + 1 / 2) / 2 - 1 / 4 = ρ := by ring
    rw [this, xiC_eq_zero_of_zeta hz h0 h1, mul_zero]
  · rw [F1]
    have : (2 * ρ + 1 / 2) / 2 - 1 / 4 = ρ := by ring
    rw [this, hz, mul_zero]
  all_goals simp; linarith

/-! ### The E8-normalized twin `ζ(s/2 + 7/4) ζ(s/2 - 5/4)` -/

/-- Completion of `ζ(s/2 + 7/4) ζ(s/2 - 5/4)`, the E8-normalized twin. -/
def XiE8 : ℂ → ℂ := XiPair (7 / 4)

theorem XiE8_one_sub (s : ℂ) : XiE8 (1 - s) = XiE8 s := XiPair_one_sub _ s

theorem XiE8_entire : Differentiable ℂ XiE8 := XiPair_entire _

/-- No zero of the E8 completion has real part in `[-3/2, 5/2]`. -/
theorem XiE8_zero_re {s : ℂ} (h : XiE8 s = 0) :
    (-7 / 2 < s.re ∧ s.re < -3 / 2) ∨ (5 / 2 < s.re ∧ s.re < 9 / 2) := by
  rcases XiPair_zero_re h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; constructor <;> linarith
  · right; constructor <;> linarith

theorem XiE8_offline_zeros (T : ℝ) :
    ∃ s : ℂ, XiE8 s = 0 ∧ 5 / 2 < s.re ∧ s.re < 9 / 2 ∧ 2 * T < s.im := by
  obtain ⟨s, h, h1, h2, h3⟩ := XiPair_offline_zeros (7 / 4) T
  exact ⟨s, h, by linarith, by linarith, h3⟩

/-! ### P2 for F1 (Beurling form) and the pole at `1/2` -/

/-- The Beurling log-coefficient of `F1` at the generalized integer `√n`. -/
def b1 (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / 2 * ((n : ℝ) ^ (-(3 / 4 : ℝ)) + (n : ℝ) ^ (1 / 4 : ℝ))

lemma b1_nonneg (n : ℕ) : 0 ≤ b1 n := by
  unfold b1
  have := ArithmeticFunction.vonMangoldt_nonneg (n := n)
  positivity

/-- **P2 holds for F1 (Beurling form).** For `Re s > 5/2`,
`-F1'(s)/F1(s) = Σ_n b1(n) (√n)^{-s}` with every `b1(n) ≥ 0`. -/
theorem F1_logDeriv_hasSum {s : ℂ} (hs : 5 / 2 < s.re) :
    HasSum (fun n : ℕ => ((b1 n : ℝ) : ℂ) * (n : ℂ) ^ (-(s / 2))) (-deriv F1 s / F1 s) := by
  set w := s / 2 + 3 / 4 with hw
  set v := s / 2 - 1 / 4 with hv
  have hwre : 1 < w.re := by rw [hw]; simp; linarith
  have hvre : 1 < v.re := by rw [hv]; simp; linarith
  have hw1 : w ≠ 1 := by rintro h; rw [h] at hwre; simp at hwre
  have hv1 : v ≠ 1 := by rintro h; rw [h] at hvre; simp at hvre
  have hdw : HasDerivAt (fun z : ℂ => riemannZeta (z / 2 + 3 / 4))
      (deriv riemannZeta w * (1 / 2)) s := by
    have h1 : HasDerivAt (fun z : ℂ => z / 2 + 3 / 4) (1 / 2) s := by
      simpa using ((hasDerivAt_id s).div_const (2 : ℂ)).add_const (3 / 4 : ℂ)
    exact (differentiableAt_riemannZeta hw1).hasDerivAt.comp s h1
  have hdv : HasDerivAt (fun z : ℂ => riemannZeta (z / 2 - 1 / 4))
      (deriv riemannZeta v * (1 / 2)) s := by
    have h1 : HasDerivAt (fun z : ℂ => z / 2 - 1 / 4) (1 / 2) s := by
      simpa using ((hasDerivAt_id s).div_const (2 : ℂ)).sub_const (1 / 4 : ℂ)
    exact (differentiableAt_riemannZeta hv1).hasDerivAt.comp s h1
  have hF : HasDerivAt F1 (deriv riemannZeta w * (1 / 2) * riemannZeta v +
      riemannZeta w * (deriv riemannZeta v * (1 / 2))) s := hdw.mul hdv
  rw [hF.deriv]
  have hzw : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hwre.le
  have hzv : riemannZeta v ≠ 0 := riemannZeta_ne_zero_of_one_le_re hvre.le
  have heq : -(deriv riemannZeta w * (1 / 2) * riemannZeta v +
      riemannZeta w * (deriv riemannZeta v * (1 / 2))) / F1 s =
      (1 / 2) * (-deriv riemannZeta w / riemannZeta w) +
        (1 / 2) * (-deriv riemannZeta v / riemannZeta v) := by
    simp only [F1]
    rw [← hw, ← hv]
    field_simp
    ring
  rw [heq, ← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hwre,
    ← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hvre]
  have hsw := (ArithmeticFunction.LSeriesSummable_vonMangoldt hwre).LSeriesHasSum
  have hsv := (ArithmeticFunction.LSeriesSummable_vonMangoldt hvre).LSeriesHasSum
  have hsum := (hsw.mul_left (1 / 2)).add (hsv.mul_left (1 / 2))
  have hfun : (fun n : ℕ => ((b1 n : ℝ) : ℂ) * (n : ℂ) ^ (-(s / 2))) = fun n =>
      1 / 2 * term (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) w n +
        1 / 2 * term (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) v n := by
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [b1]
    · rw [term_of_ne_zero hn, term_of_ne_zero hn]
      have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      have hA : (n : ℂ) ^ (s / 2) ≠ 0 := by
        rw [Ne, cpow_eq_zero_iff]; exact fun h => hn0 h.1
      have hB : (n : ℂ) ^ ((3 / 4 : ℝ) : ℂ) ≠ 0 := by
        rw [Ne, cpow_eq_zero_iff]; exact fun h => hn0 h.1
      have hC : (n : ℂ) ^ ((1 / 4 : ℝ) : ℂ) ≠ 0 := by
        rw [Ne, cpow_eq_zero_iff]; exact fun h => hn0 h.1
      have ew : (n : ℂ) ^ w = (n : ℂ) ^ (s / 2) * (n : ℂ) ^ ((3 / 4 : ℝ) : ℂ) := by
        rw [hw, ← cpow_add _ _ hn0]; push_cast; ring_nf
      have ev : (n : ℂ) ^ v = (n : ℂ) ^ (s / 2) / (n : ℂ) ^ ((1 / 4 : ℝ) : ℂ) := by
        rw [hv, ← cpow_sub _ _ hn0]; push_cast; ring_nf
      have e1 : (((n : ℝ) ^ (-(3 / 4 : ℝ)) : ℝ) : ℂ) = ((n : ℂ) ^ ((3 / 4 : ℝ) : ℂ))⁻¹ := by
        rw [Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_neg, cpow_neg]
        norm_cast
      have e2 : (((n : ℝ) ^ (1 / 4 : ℝ) : ℝ) : ℂ) = (n : ℂ) ^ ((1 / 4 : ℝ) : ℂ) := by
        rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
        norm_cast
      have e3 : (n : ℂ) ^ (-(s / 2)) = ((n : ℂ) ^ (s / 2))⁻¹ := cpow_neg _ _
      simp only [b1]
      push_cast
      rw [e1, e2, e3, ew, ev]
      field_simp
  rw [hfun]
  exact hsum

/-- `F1` has a genuine pole at `s = 1/2` (outside `{0, 1}`): `(s - 1/2) F1(s) → -1`. -/
theorem F1_pole_half :
    Tendsto (fun s : ℂ => (s - 1 / 2) * F1 s) (𝓝[≠] (1 / 2)) (𝓝 (-1)) := by
  have hmap : Tendsto (fun s : ℂ => s / 2 + 3 / 4) (𝓝[≠] (1 / 2)) (𝓝[≠] 1) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h : Tendsto (fun s : ℂ => s / 2 + 3 / 4) (𝓝 (1 / 2)) (𝓝 ((1 / 2) / 2 + 3 / 4)) :=
        ((continuous_id.div_const 2).add continuous_const).tendsto _
      rw [show ((1 : ℂ) / 2) / 2 + 3 / 4 = 1 by norm_num] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      intro h
      apply hs
      simp only [Set.mem_singleton_iff] at h ⊢
      linear_combination 2 * h
  have h1 := riemannZeta_residue_one.comp hmap
  have h2 : Tendsto (fun s : ℂ => riemannZeta (s / 2 - 1 / 4)) (𝓝[≠] (1 / 2))
      (𝓝 (riemannZeta 0)) := by
    have hc : ContinuousAt riemannZeta 0 :=
      (differentiableAt_riemannZeta zero_ne_one).continuousAt
    have h : Tendsto (fun s : ℂ => s / 2 - 1 / 4) (𝓝 (1 / 2)) (𝓝 ((1 / 2) / 2 - 1 / 4)) :=
      ((continuous_id.div_const 2).sub continuous_const).tendsto _
    rw [show ((1 : ℂ) / 2) / 2 - 1 / 4 = 0 by norm_num] at h
    exact (hc.tendsto.comp h).mono_left nhdsWithin_le_nhds
  have hlim := (h1.const_mul 2).mul h2
  rw [riemannZeta_zero] at hlim
  have hval : (2 : ℂ) * 1 * (-1 / 2) = -1 := by norm_num
  rw [hval] at hlim
  refine hlim.congr (fun s => ?_)
  simp only [F1, Function.comp_apply]
  ring

/-! ## F. Theorem A, Step 3: the Cohn--Elkies pairing

The pointwise facts and the measure-theoretic support forcing are THEOREM-kernel-checked. The
pairing identity itself (Step 2: FE ⟹ distributional Poisson identity) is a HYPOTHESIS of
`thmA_step3_plus` / `thmA_step3_minus`. It is not proved here. -/

/-- The one-dimensional Cohn--Elkies function `f(x) = sinc(πx)² / (1 - x²)`, i.e.
`sin²(πx) / (π² x² (1 - x²))` with its removable singularities filled (`f(0) = 1`, `f(±1) = 0`). -/
def ceF (x : ℝ) : ℝ := Real.sinc (π * x) ^ 2 / (1 - x ^ 2)

/-- Its Fourier transform `(1 - |t| + sin(2π|t|)/(2π))_+`, supported in `[-1, 1]`. -/
def ceFhat (t : ℝ) : ℝ := if |t| ≤ 1 then 1 - |t| + Real.sin (2 * π * |t|) / (2 * π) else 0

lemma ceF_zero : ceF 0 = 1 := by simp [ceF, Real.sinc_zero]

lemma ceF_nonpos {x : ℝ} (hx : 1 ≤ |x|) : ceF x ≤ 0 := by
  unfold ceF
  have h1 : 1 - x ^ 2 ≤ 0 := by nlinarith [sq_abs x, abs_nonneg x]
  exact div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) h1

lemma ceF_eq_zero_iff {x : ℝ} (hx : 1 ≤ |x|) : ceF x = 0 ↔ ∃ n : ℤ, x = n := by
  unfold ceF
  constructor
  · intro h
    rcases div_eq_zero_iff.mp h with h | h
    · have hs : Real.sinc (π * x) = 0 := pow_eq_zero_iff two_ne_zero |>.mp h
      have hx0 : x ≠ 0 := by rintro rfl; simp at hx; linarith
      have hpx : π * x ≠ 0 := mul_ne_zero Real.pi_ne_zero hx0
      rw [Real.sinc_of_ne_zero hpx, div_eq_zero_iff] at hs
      rcases hs with hs | hs
      · obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hs
        refine ⟨n, ?_⟩
        have hpi : π ≠ 0 := Real.pi_ne_zero
        have : (n : ℝ) * π = x * π := by rw [hn]; ring
        exact (mul_right_cancel₀ hpi this).symm
      · exact absurd hs hpx
    · have hq : (x - 1) * (x + 1) = 0 := by ring_nf; linarith
      rcases mul_eq_zero.mp hq with h' | h'
      · exact ⟨1, by push_cast; linarith⟩
      · exact ⟨-1, by push_cast; linarith⟩
  · rintro ⟨n, rfl⟩
    have hsin : Real.sin (π * n) = 0 := by rw [mul_comm]; exact Real.sin_int_mul_pi n
    rcases eq_or_ne (n : ℝ) 0 with h0 | h0
    · rw [h0] at hx; simp at hx; linarith
    · rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero h0), hsin]
      simp

lemma ceFhat_nonneg (t : ℝ) : 0 ≤ ceFhat t := by
  unfold ceFhat
  split_ifs with h
  · set v := 1 - |t| with hv
    have hv0 : 0 ≤ v := by rw [hv]; linarith
    have hsin : Real.sin (2 * π * |t|) = -Real.sin (2 * π * v) := by
      rw [hv, show 2 * π * (1 - |t|) = 2 * π - 2 * π * |t| by ring, Real.sin_two_pi_sub]
      ring
    rw [hsin]
    have hle : Real.sin (2 * π * v) ≤ 2 * π * v := Real.sin_le (by positivity)
    have hpi : 0 < 2 * π := by positivity
    have : Real.sin (2 * π * v) / (2 * π) ≤ v := by
      rw [div_le_iff₀ hpi]; linarith
    rw [neg_div]
    linarith
  · exact le_refl 0

lemma ceFhat_zero : ceFhat 0 = 1 := by simp [ceFhat]

lemma ceFhat_eq_zero_of_one_le {t : ℝ} (ht : 1 ≤ |t|) : ceFhat t = 0 := by
  unfold ceFhat
  split_ifs with h
  · have : |t| = 1 := le_antisymm h ht
    rw [this]
    simp
  · rfl

lemma ceFhat_one : ceFhat 1 = 0 := ceFhat_eq_zero_of_one_le (by simp)

/-- **Support forcing (Cohn--Elkies pairing, kernel-checked).** If a positive measure lives on
`|x| ≥ 1`, integrates `f`, and `∫ f dN = 0`, then `N` is concentrated on the integers. -/
theorem ce_support_forcing {N : Measure ℝ} (hsupp : ∀ᵐ x ∂N, 1 ≤ |x|) (hint : Integrable ceF N)
    (h0 : ∫ x, ceF x ∂N = 0) : ∀ᵐ x : ℝ ∂N, ∃ n : ℤ, x = (n : ℝ) := by
  have hnn : 0 ≤ᵐ[N] fun x => -ceF x :=
    hsupp.mono fun x hx => by simpa using ceF_nonpos hx
  have hz : (fun x => -ceF x) =ᵐ[N] 0 := by
    refine (integral_eq_zero_iff_of_nonneg_ae hnn hint.neg).mp ?_
    rw [integral_neg, h0, neg_zero]
  filter_upwards [hz, hsupp] with x hx hx1
  exact (ceF_eq_zero_iff hx1).mp (by simpa using hx)

lemma ceFhat_integral_zero {N : Measure ℝ} (hsupp : ∀ᵐ x ∂N, 1 ≤ x) :
    ∫ t, ceFhat t ∂N = 0 := by
  have : (fun t => ceFhat t) =ᵐ[N] fun _ => (0 : ℝ) :=
    hsupp.mono fun x hx => ceFhat_eq_zero_of_one_le (by rw [abs_of_pos (by linarith)]; exact hx)
  rw [integral_congr_ae this]
  simp

/-- **Theorem A, Step 3, `ε = +1` (conditional on the pairing identity of Step 2).**
For `ν = δ₀ + N + N(-·)` with `N ≥ 0` on `[1, ∞)`, the identity `⟨ν, f⟩ = ⟨ν, f̂⟩` (both sides
written out for even `f`, `f̂`) forces `N` onto the integers. -/
theorem thmA_step3_plus {N : Measure ℝ} (hsupp : ∀ᵐ x ∂N, 1 ≤ x) (hint : Integrable ceF N)
    (hpair : ceF 0 + 2 * ∫ x, ceF x ∂N = ceFhat 0 + 2 * ∫ t, ceFhat t ∂N) :
    ∀ᵐ x : ℝ ∂N, ∃ n : ℤ, x = (n : ℝ) := by
  rw [ceFhat_integral_zero hsupp, ceF_zero, ceFhat_zero] at hpair
  have h0 : ∫ x, ceF x ∂N = 0 := by linarith
  exact ce_support_forcing (hsupp.mono fun x hx => by rw [abs_of_pos (by linarith)]; exact hx)
    hint h0

/-- **Theorem A, Step 3, `ε = -1` (conditional on the paired identities of Step 2).**
With `N = δ₁ + N'` (`a₁ = 1`), the Gaussian pairing `β = ⟨ν, e^{-πx²}⟩` and the magic pairing
`1 = -⟨ν, f⟩ + 2β` are incompatible. -/
theorem thmA_step3_minus {N N' : Measure ℝ} (hN : N = Measure.dirac 1 + N')
    (hsupp : ∀ᵐ x ∂N, 1 ≤ x)
    (hintG : Integrable (fun x : ℝ => Real.exp (-π * x ^ 2)) N) (β : ℝ)
    (hgauss : β = 1 + 2 * ∫ x, Real.exp (-π * x ^ 2) ∂N)
    (hpair : ceFhat 0 + 2 * ∫ t, ceFhat t ∂N = -(ceF 0 + 2 * ∫ x, ceF x ∂N) + 2 * β) :
    False := by
  have hF : ∫ x, ceF x ∂N ≤ 0 :=
    integral_nonpos_of_ae (hsupp.mono fun x hx =>
      ceF_nonpos (by rw [abs_of_pos (by linarith)]; exact hx))
  have hG : Real.exp (-π) ≤ ∫ x, Real.exp (-π * x ^ 2) ∂N := by
    have hint1 : Integrable (fun x : ℝ => Real.exp (-π * x ^ 2)) (Measure.dirac 1) :=
      hintG.mono_measure (by rw [hN]; exact Measure.le_add_right le_rfl)
    have hint2 : Integrable (fun x : ℝ => Real.exp (-π * x ^ 2)) N' :=
      hintG.mono_measure (by rw [hN]; exact Measure.le_add_left le_rfl)
    rw [hN, integral_add_measure hint1 hint2, integral_dirac]
    have : 0 ≤ ∫ x, Real.exp (-π * x ^ 2) ∂N' := integral_nonneg fun x => (Real.exp_pos _).le
    simp only [one_pow, mul_one]
    linarith
  rw [ceFhat_integral_zero hsupp, ceFhat_zero, ceF_zero] at hpair
  have := Real.exp_pos (-π)
  linarith

/-! ## G. Lattice / number-field rescaling puts the pole at `(d+1)/2` (THEOREM-kernel-checked) -/

theorem rescale_pole {d : ℂ} (hd : d ≠ 0) (s : ℂ) :
    s / d + 1 / 2 - 1 / (2 * d) = 1 ↔ s = (d + 1) / 2 := by
  constructor
  · intro h
    field_simp at h
    linear_combination h / 2
  · rintro rfl
    field_simp
    ring

theorem rescale_reflect {d : ℂ} (hd : d ≠ 0) (s : ℂ) :
    (1 - s) / d + 1 / 2 - 1 / (2 * d) = 1 - (s / d + 1 / 2 - 1 / (2 * d)) := by
  field_simp
  ring

end CruxAxisoConstruct

end

#print axioms CruxAxisoConstruct.logMul_eq_convolution
#print axioms CruxAxisoConstruct.logDerivCoeff_prime
#print axioms CruxAxisoConstruct.logDerivCoeff_prime_sq
#print axioms CruxAxisoConstruct.coeff_nonneg_of_logDeriv_nonneg
#print axioms CruxAxisoConstruct.positivity_lemma
#print axioms CruxAxisoConstruct.P2_forces_sq_ineq
#print axioms CruxAxisoConstruct.zeta_P2
#print axioms CruxAxisoConstruct.LSeries_dvdInd
#print axioms CruxAxisoConstruct.P0_factor
#print axioms CruxAxisoConstruct.P0_reciprocal
#print axioms CruxAxisoConstruct.P0_reciprocal_four
#print axioms CruxAxisoConstruct.F0_eq_LSeries
#print axioms CruxAxisoConstruct.a0_cases
#print axioms CruxAxisoConstruct.a0_nonneg
#print axioms CruxAxisoConstruct.a0_mul_coprime
#print axioms CruxAxisoConstruct.F0_logDerivCoeff_four
#print axioms CruxAxisoConstruct.F0_not_P2
#print axioms CruxAxisoConstruct.Xi0_entire
#print axioms CruxAxisoConstruct.Xi0_one_sub
#print axioms CruxAxisoConstruct.Xi0_eq
#print axioms CruxAxisoConstruct.P0_eq_zero_iff
#print axioms CruxAxisoConstruct.P0_zero_re
#print axioms CruxAxisoConstruct.Xi0_zero_offline
#print axioms CruxAxisoConstruct.Fc_eq_LSeries
#print axioms CruxAxisoConstruct.Fc_logDerivCoeff_sq
#print axioms CruxAxisoConstruct.Pc_selfRecip_sq
#print axioms CruxAxisoConstruct.Pc_sqrt_selfRecip
#print axioms CruxAxisoConstruct.lemmaC_prime
#print axioms CruxAxisoConstruct.geomCoeff_hasSum
#print axioms CruxAxisoConstruct.F0_logDeriv_exists
#print axioms CruxAxisoConstruct.F0_vonMangoldt_four
#print axioms CruxAxisoConstruct.F0_vonMangoldt_two_pow
#print axioms CruxAxisoConstruct.Fc_logDeriv_exists
#print axioms CruxAxisoConstruct.sq_family_core
#print axioms CruxAxisoConstruct.logDerivCoeff_prime_pow
#print axioms CruxAxisoConstruct.Fq_eq_LSeries
#print axioms CruxAxisoConstruct.Fq_plus_values
#print axioms CruxAxisoConstruct.lemmaC_prime_sq_plus
#print axioms CruxAxisoConstruct.lemmaC_prime_sq_minus
#print axioms CruxAxisoConstruct.Pq_selfRecip_cases
#print axioms CruxAxisoConstruct.Pq_plus_selfRecip
#print axioms CruxAxisoConstruct.Pq_minus_selfRecip
#print axioms CruxAxisoConstruct.lemmaC_prime_sq
#print axioms CruxAxisoConstruct.exists_nontrivial_zero_above
#print axioms CruxAxisoConstruct.XiPair_entire
#print axioms CruxAxisoConstruct.XiPair_one_sub
#print axioms CruxAxisoConstruct.XiPair_zero_re
#print axioms CruxAxisoConstruct.XiPair_no_zero_on_line
#print axioms CruxAxisoConstruct.XiPair_offline_zeros
#print axioms CruxAxisoConstruct.Xi1_eq
#print axioms CruxAxisoConstruct.Xi1_one_sub
#print axioms CruxAxisoConstruct.Xi1_entire
#print axioms CruxAxisoConstruct.Xi1_no_zero_on_line
#print axioms CruxAxisoConstruct.Xi1_zero_re
#print axioms CruxAxisoConstruct.Xi1_offline_zeros
#print axioms CruxAxisoConstruct.XiE8_one_sub
#print axioms CruxAxisoConstruct.XiE8_entire
#print axioms CruxAxisoConstruct.XiE8_zero_re
#print axioms CruxAxisoConstruct.XiE8_offline_zeros
#print axioms CruxAxisoConstruct.b1_nonneg
#print axioms CruxAxisoConstruct.F1_logDeriv_hasSum
#print axioms CruxAxisoConstruct.F1_pole_half
#print axioms CruxAxisoConstruct.ceF_zero
#print axioms CruxAxisoConstruct.ceF_nonpos
#print axioms CruxAxisoConstruct.ceF_eq_zero_iff
#print axioms CruxAxisoConstruct.ceFhat_nonneg
#print axioms CruxAxisoConstruct.ceFhat_zero
#print axioms CruxAxisoConstruct.ceFhat_eq_zero_of_one_le
#print axioms CruxAxisoConstruct.ce_support_forcing
#print axioms CruxAxisoConstruct.thmA_step3_plus
#print axioms CruxAxisoConstruct.thmA_step3_minus
#print axioms CruxAxisoConstruct.rescale_pole
#print axioms CruxAxisoConstruct.rescale_reflect
