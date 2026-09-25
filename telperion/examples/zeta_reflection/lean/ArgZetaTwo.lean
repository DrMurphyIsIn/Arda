/-  ArgZetaTwo.lean -- brick K6a of the ANDURIL Arb discharge
    (telperion/docs/ANDURIL_ARB_DISCHARGE_2026-09-23.md, inventory row H2d, brick K6a).

    THE BINDER IT DISCHARGES.  Conjunct 5 of the `hArbT` binder of every emitted Turing band
    (`TuringBand.BandStatement`, `BandGlue.BandData.EnclHyp`) is

        hAV2 : DiffractionCore.argChangeVert riemannZeta 2 T0 T1 ∈ Set.Icc L1 H1,

    the argument change of ζ up the line `Re s = 2` between the band edges.  The emitted bands feed
    it a 1e-12-wide Arb enclosure.  This file proves a GENERIC enclosure, valid for every `T0`,
    `T1` and hence for all 10,379 bands of the h280000 ladder at once:

        argChangeVert riemannZeta 2 T0 T1 ∈ [-249/250, 249/250]         (`hAV2_generic`)

    because `|arg ζ(2 + i t)| ≤ log ζ(2) = log (π²/6) < 0.498` for every real `t`.

    HOW.
      * `argChangeVert_zeta_two_eq`: the argument change IS a difference of principal arguments,
            argChangeVert ζ 2 T0 T1 = arg ζ(2 + i T1) - arg ζ(2 + i T0),
        by the fundamental theorem of calculus for `y ↦ log ζ(2 + i y)` (principal `Complex.log`),
        legitimate because `ζ(2 + i y)` stays in the right half-plane.
      * `arg_zeta_eq_im_primeLog`, `abs_arg_zeta_two_le`: on `Re s = 2`, ζ(s) = exp L(s) with
        L(s) = Σ_p -log(1 - p^{-s}) (Mathlib's `riemannZeta_eulerProduct_exp_log`), and
        ‖L(s)‖ ≤ Σ_p -log(1 - p^{-2}) =: G termwise (Taylor series of `-log(1 - z)` dominated
        by that of `-log(1 - ‖z‖)`).  Since G < π, `Complex.log (exp L) = L`, so
        arg ζ(s) = Im L(s) ∈ [-G, G]; since G < π/2, Re ζ(s) > 0.
      * `exp_primeSum`: exp G = ζ(2) = π²/6 (the same Euler product at the real point 2), so
        G = log (π²/6); `log_pi_sq_div_six_lt`: log (π²/6) < 249/500 from π < 3.1416 and the
        degree-6 Taylor lower bound of `exp`.

    This is the "Λ(n) series at σ = 2" bound of the memo: mathematically G = Σ_n Λ(n)/(n² log n) =
    log ζ(2); the formal route here is the prime Euler product, not the Λ(n) series itself.
    (Not formalized, for orientation only: by Kronecker's theorem the supremum of |arg ζ(2+it)| is
    Σ_p arcsin(p⁻²) ≈ 0.455, so the constant is within 10 percent of optimal.)

    Trust: no hypotheses beyond those stated; axioms [propext, Classical.choice, Quot.sound]
    (see AxiomGuardArgChange.lean).  No `sorry`.

    conjecture1_proved = False.  A height-uniform bound on one edge of a finite zero count; nothing
    here bears on the Riemann Hypothesis. -/
import Mathlib
import DiffractionCore

open Complex

namespace ArgZetaTwo

/-! ## 1. The logarithm of the Euler product -/

/-- The prime logarithm series `L(s) = Σ_p -log(1 - p^{-s})` (principal logs). -/
noncomputable def primeLog (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, -Complex.log (1 - ((p : ℕ) : ℂ) ^ (-s))

/-- The Euler product in exponential form (Mathlib). -/
theorem exp_primeLog {s : ℂ} (hs : 1 < s.re) : Complex.exp (primeLog s) = riemannZeta s :=
  riemannZeta_eulerProduct_exp_log hs

/-- `‖-log(1 - z)‖ ≤ -log(1 - ‖z‖)` on the open unit disc: the Taylor series `Σ zⁿ/n` is
    dominated termwise by `Σ ‖z‖ⁿ/n`. -/
theorem norm_neg_log_one_sub_le {z : ℂ} (hz : ‖z‖ < 1) :
    ‖-Complex.log (1 - z)‖ ≤ -Real.log (1 - ‖z‖) := by
  have hc := Complex.hasSum_taylorSeries_neg_log hz
  have hr0 : ‖((‖z‖ : ℝ) : ℂ)‖ < 1 := by simpa using hz
  have hr := Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log hr0)
  have hre_term : ∀ n : ℕ, (((‖z‖ : ℝ) : ℂ) ^ n / (n : ℂ)).re = ‖z‖ ^ n / n := by
    intro n
    rw [show (((‖z‖ : ℝ) : ℂ) ^ n / (n : ℂ)) = (((‖z‖ ^ n / n : ℝ)) : ℂ) by push_cast; ring]
    exact Complex.ofReal_re _
  have hre_sum : (-Complex.log (1 - ((‖z‖ : ℝ) : ℂ))).re = -Real.log (1 - ‖z‖) := by
    rw [show (1 : ℂ) - ((‖z‖ : ℝ) : ℂ) = ((1 - ‖z‖ : ℝ) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_log (by linarith [norm_nonneg z])]
    simp
  simp only [hre_term, hre_sum] at hr
  refine hc.norm_le_of_bounded hr (fun n => ?_)
  rw [norm_div, norm_pow, Complex.norm_natCast]

/-- `-log(1 - x) ≤ 2 x` for `0 ≤ x ≤ 1/2`. -/
theorem neg_log_one_sub_le_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    -Real.log (1 - x) ≤ 2 * x := by
  have hpos : 0 < 1 - x := by linarith
  have h1 : -Real.log (1 - x) = Real.log (1 - x)⁻¹ := by rw [Real.log_inv]
  have h2 : Real.log (1 - x)⁻¹ ≤ (1 - x)⁻¹ - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h3 : (1 - x)⁻¹ - 1 ≤ 2 * x := by
    rw [inv_eq_one_div, div_sub_one hpos.ne', div_le_iff₀ hpos]
    nlinarith
  linarith

/-- `0 ≤ -log(1 - x)` for `0 ≤ x < 1`. -/
theorem neg_log_one_sub_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) : 0 ≤ -Real.log (1 - x) := by
  have : Real.log (1 - x) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  linarith

/-! ## 2. The real prime sum `G = Σ_p -log(1 - p^{-2})` -/

/-- The prime term `-log(1 - p^{-2})`. -/
noncomputable def primeTerm (p : Nat.Primes) : ℝ := -Real.log (1 - (((p : ℕ) : ℝ) ^ 2)⁻¹)

theorem prime_inv_sq_le (p : Nat.Primes) : (((p : ℕ) : ℝ) ^ 2)⁻¹ ≤ 1 / 4 := by
  have h2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.two_le
  have h4 : (4 : ℝ) ≤ ((p : ℕ) : ℝ) ^ 2 := by nlinarith
  rw [inv_eq_one_div]
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) h4

theorem prime_inv_sq_nonneg (p : Nat.Primes) : 0 ≤ (((p : ℕ) : ℝ) ^ 2)⁻¹ := by positivity

theorem primeTerm_nonneg (p : Nat.Primes) : 0 ≤ primeTerm p :=
  neg_log_one_sub_nonneg (prime_inv_sq_nonneg p) (by linarith [prime_inv_sq_le p])

theorem summable_prime_inv_sq : Summable (fun p : Nat.Primes => (((p : ℕ) : ℝ) ^ 2)⁻¹) := by
  have h := (Nat.Primes.summable_rpow (r := -2)).mpr (by norm_num)
  refine h.congr (fun p => ?_)
  have hp : (0 : ℝ) ≤ ((p : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [Real.rpow_neg hp, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem summable_primeTerm : Summable primeTerm := by
  refine Summable.of_nonneg_of_le primeTerm_nonneg (fun p => ?_) (summable_prime_inv_sq.mul_left 2)
  exact neg_log_one_sub_le_two_mul (prime_inv_sq_nonneg p) (by linarith [prime_inv_sq_le p])

/-- `G = Σ_p -log(1 - p^{-2})`. -/
noncomputable def primeSum : ℝ := ∑' p : Nat.Primes, primeTerm p

theorem hasSum_primeTerm : HasSum primeTerm primeSum := summable_primeTerm.hasSum

/-- On the real point `2` the complex prime log series is the real prime sum. -/
theorem primeLog_two : primeLog 2 = (primeSum : ℂ) := by
  unfold primeLog primeSum
  rw [Complex.ofReal_tsum]
  congr 1
  funext p
  unfold primeTerm
  have hp : (0 : ℝ) ≤ 1 - (((p : ℕ) : ℝ) ^ 2)⁻¹ := by linarith [prime_inv_sq_le p]
  have hcp : ((p : ℕ) : ℂ) ^ (-(2 : ℂ)) = ((((((p : ℕ) : ℝ) ^ 2)⁻¹ : ℝ)) : ℂ) := by
    rw [Complex.cpow_neg, Complex.cpow_two]
    push_cast
    ring
  rw [hcp, show (1 : ℂ) - ((((((p : ℕ) : ℝ) ^ 2)⁻¹ : ℝ)) : ℂ)
      = (((1 - (((p : ℕ) : ℝ) ^ 2)⁻¹ : ℝ)) : ℂ) by push_cast; ring,
    ← Complex.ofReal_log hp]
  push_cast
  ring

/-- `exp G = π²/6`: the Euler product at the real point `2`. -/
theorem exp_primeSum : Real.exp primeSum = Real.pi ^ 2 / 6 := by
  have h := exp_primeLog (s := 2) (by norm_num)
  rw [primeLog_two, riemannZeta_two, ← Complex.ofReal_exp] at h
  exact_mod_cast h

/-- `G = log (π²/6) = log ζ(2)`. -/
theorem primeSum_eq : primeSum = Real.log (Real.pi ^ 2 / 6) := by
  rw [← exp_primeSum, Real.log_exp]

/-- **`log ζ(2) = log (π²/6) < 0.498`** (π < 3.1416 and the degree-6 Taylor lower bound of exp). -/
theorem log_pi_sq_div_six_lt : Real.log (Real.pi ^ 2 / 6) < 249 / 500 := by
  have hpi := Real.pi_lt_d4
  have hpi0 := Real.pi_pos
  have hexp := Real.sum_le_exp_of_nonneg (x := (249 / 500 : ℝ)) (by norm_num) 7
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hexp
  norm_num at hexp
  have hsq : Real.pi ^ 2 / 6 < Real.exp (249 / 500) := by
    have : Real.pi ^ 2 < 3.1416 ^ 2 := by nlinarith
    norm_num at this ⊢
    linarith
  rw [Real.log_lt_iff_lt_exp (by positivity)]
  exact hsq

theorem primeSum_lt : primeSum < 249 / 500 := by
  rw [primeSum_eq]; exact log_pi_sq_div_six_lt

theorem primeSum_nonneg : 0 ≤ primeSum := tsum_nonneg primeTerm_nonneg

/-! ## 3. `|arg ζ(2 + i t)| ≤ G` -/

/-- The point `2 + i t`. -/
theorem re_two_add (t : ℝ) : ((2 : ℂ) + (t : ℂ) * I).re = 2 := by simp

/-- `‖L(2 + i t)‖ ≤ G`. -/
theorem norm_primeLog_le (t : ℝ) : ‖primeLog ((2 : ℂ) + (t : ℂ) * I)‖ ≤ primeSum := by
  unfold primeLog
  refine tsum_of_norm_bounded hasSum_primeTerm (fun p => ?_)
  have hnorm : ‖((p : ℕ) : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * I))‖ = (((p : ℕ) : ℝ) ^ 2)⁻¹ := by
    rw [Complex.norm_natCast_cpow_of_pos p.prop.pos]
    have hre : (-((2 : ℂ) + (t : ℂ) * I)).re = -2 := by simp
    rw [hre, Real.rpow_neg (Nat.cast_nonneg _), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  have hlt : ‖((p : ℕ) : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * I))‖ < 1 := by
    rw [hnorm]; linarith [prime_inv_sq_le p]
  have h := norm_neg_log_one_sub_le hlt
  rw [hnorm] at h
  exact h

/-- On `Re s = 2`, the principal logarithm of ζ is the prime log series. -/
theorem log_zeta_two_eq (t : ℝ) :
    Complex.log (riemannZeta ((2 : ℂ) + (t : ℂ) * I)) = primeLog ((2 : ℂ) + (t : ℂ) * I) := by
  set L := primeLog ((2 : ℂ) + (t : ℂ) * I) with hL
  have hexp : Complex.exp L = riemannZeta ((2 : ℂ) + (t : ℂ) * I) :=
    exp_primeLog (by rw [re_two_add]; norm_num)
  have hn := norm_primeLog_le t
  rw [← hL] at hn
  have him : |L.im| ≤ primeSum := le_trans (Complex.abs_im_le_norm L) hn
  have hG := primeSum_lt
  have hpi : (249 / 500 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
  rw [← hexp]
  apply Complex.log_exp
  · linarith [(abs_le.mp him).1]
  · linarith [(abs_le.mp him).2]

/-- `arg ζ(2 + i t) = Im L(2 + i t)`. -/
theorem arg_zeta_eq_im_primeLog (t : ℝ) :
    Complex.arg (riemannZeta ((2 : ℂ) + (t : ℂ) * I)) = (primeLog ((2 : ℂ) + (t : ℂ) * I)).im := by
  rw [← Complex.log_im, log_zeta_two_eq]

/-- **`|arg ζ(2 + i t)| ≤ log ζ(2)`** for every real `t`. -/
theorem abs_arg_zeta_two_le (t : ℝ) :
    |Complex.arg (riemannZeta ((2 : ℂ) + (t : ℂ) * I))| ≤ Real.log (Real.pi ^ 2 / 6) := by
  rw [arg_zeta_eq_im_primeLog, ← primeSum_eq]
  exact le_trans (Complex.abs_im_le_norm _) (norm_primeLog_le t)

/-- `ζ(2 + i t)` lies in the open right half-plane. -/
theorem re_zeta_two_pos (t : ℝ) : 0 < (riemannZeta ((2 : ℂ) + (t : ℂ) * I)).re := by
  set L := primeLog ((2 : ℂ) + (t : ℂ) * I) with hL
  have hexp : Complex.exp L = riemannZeta ((2 : ℂ) + (t : ℂ) * I) :=
    exp_primeLog (by rw [re_two_add]; norm_num)
  have hn := norm_primeLog_le t
  rw [← hL] at hn
  have him : |L.im| ≤ primeSum := le_trans (Complex.abs_im_le_norm L) hn
  have hG := primeSum_lt
  have hpi2 : (249 / 500 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
  rw [← hexp, Complex.exp_re]
  apply mul_pos (Real.exp_pos _)
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [(abs_le.mp him).1, (abs_le.mp him).2]

theorem zeta_two_mem_slitPlane (t : ℝ) : riemannZeta ((2 : ℂ) + (t : ℂ) * I) ∈ slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (re_zeta_two_pos t))

/-! ## 4. The argument change up `Re s = 2` -/

/-- **The σ = 2 argument change is a difference of principal arguments** (every `T0`, `T1`):
    `argChangeVert ζ 2 T0 T1 = arg ζ(2 + i T1) - arg ζ(2 + i T0)`. -/
theorem argChangeVert_zeta_two_eq (T0 T1 : ℝ) :
    DiffractionCore.argChangeVert riemannZeta 2 T0 T1
      = Complex.arg (riemannZeta ((2 : ℂ) + (T1 : ℂ) * I))
        - Complex.arg (riemannZeta ((2 : ℂ) + (T0 : ℂ) * I)) := by
  set γ : ℝ → ℂ := fun y => (2 : ℂ) + (y : ℂ) * I with hγdef
  have hγ : ∀ y : ℝ, HasDerivAt γ I y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := (hasDerivAt_id y).ofReal_comp
    have h2 := (h1.mul_const I).const_add (2 : ℂ)
    simpa [hγdef] using h2
  have hne1 : ∀ y : ℝ, γ y ≠ 1 := by
    intro y h
    have := congrArg Complex.re h
    simp [hγdef] at this
  have hζ : ∀ y : ℝ, HasDerivAt (fun y => riemannZeta (γ y)) (deriv riemannZeta (γ y) * I) y :=
    fun y => ((differentiableAt_riemannZeta (hne1 y)).hasDerivAt).comp y (hγ y)
  have hG : ∀ y : ℝ, HasDerivAt (fun y => Complex.log (riemannZeta (γ y)))
      (deriv riemannZeta (γ y) * I / riemannZeta (γ y)) y :=
    fun y => (hζ y).clog_real (zeta_two_mem_slitPlane y)
  have heq : (fun y => deriv riemannZeta (γ y) * I / riemannZeta (γ y))
      = fun y => I * logDeriv riemannZeta (γ y) := by
    funext y; rw [logDeriv_apply]; ring
  have hcont : Continuous (fun y : ℝ => I * logDeriv riemannZeta (γ y)) :=
    continuous_const.mul DiffractionCore.continuous_logDeriv_zeta_line2
  have hint : IntervalIntegrable (fun y => deriv riemannZeta (γ y) * I / riemannZeta (γ y))
      MeasureTheory.volume T0 T1 := by
    rw [heq]; exact hcont.intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hG y) hint
  rw [heq, intervalIntegral.integral_const_mul] at hFTC
  have him := congrArg Complex.im hFTC
  rw [Complex.sub_im, Complex.log_im, Complex.log_im] at him
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add] at him
  unfold DiffractionCore.argChangeVert
  rw [show (((2 : ℝ)) : ℂ) = (2 : ℂ) by norm_num]
  exact him

/-- `|argChangeVert ζ 2 T0 T1| ≤ 2 log ζ(2)` for every `T0`, `T1`. -/
theorem abs_argChangeVert_zeta_two_le (T0 T1 : ℝ) :
    |DiffractionCore.argChangeVert riemannZeta 2 T0 T1| ≤ 2 * Real.log (Real.pi ^ 2 / 6) := by
  rw [argChangeVert_zeta_two_eq]
  have h1 := abs_arg_zeta_two_le T1
  have h0 := abs_arg_zeta_two_le T0
  rw [abs_le] at h0 h1 ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2]

/-- **K6a in the exact `hAV2` binder form** (generic: every band, every height):
    `argChangeVert riemannZeta 2 T0 T1 ∈ Set.Icc (-(249/250)) (249/250)`. -/
theorem hAV2_generic (T0 T1 : ℝ) :
    DiffractionCore.argChangeVert riemannZeta 2 T0 T1 ∈ Set.Icc (-(249 / 250 : ℝ)) (249 / 250) := by
  have h := abs_argChangeVert_zeta_two_le T0 T1
  have hl := log_pi_sq_div_six_lt
  rw [abs_le] at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- `hAV2` for any enclosure `[L1, H1] ⊇ [-249/250, 249/250]`. -/
theorem hAV2_of_le {T0 T1 L1 H1 : ℝ} (hL : L1 ≤ -(249 / 250)) (hH : 249 / 250 ≤ H1) :
    DiffractionCore.argChangeVert riemannZeta 2 T0 T1 ∈ Set.Icc L1 H1 := by
  have h := hAV2_generic T0 T1
  exact ⟨le_trans hL h.1, le_trans h.2 hH⟩

end ArgZetaTwo
