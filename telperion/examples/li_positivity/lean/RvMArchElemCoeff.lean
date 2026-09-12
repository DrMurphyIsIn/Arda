/-
RvMArchElemCoeff — Arc B (archimedean Li growth), PR B1b part 2: the Taylor-coefficient extraction.

B1a gave the elementary series `logDeriv (Γℝ∘M) z = −(γ+log π)/2·M² − M + ∑'_j archSummand j z`
(`M = (1−z)⁻¹`), B1b part 1 gave its compact form, `O(1/j²)` bound, and uniform convergence on
`closedBall 0 (1/4)`.  This file extracts the `n`-th Taylor coefficient of the archimedean Li
generating function as an explicit elementary value:

  * `iteratedDeriv_invOneSub_sq` / `iteratedDeriv_scaledMobius` — closed forms for the two rational
    building blocks of a summand.
  * `archSummand_eq_linear` — the summand in linear (non-common-denominator) form.
  * `iteratedDeriv_archSummand_zero` — the `n`-th derivative of a single summand at `0`.
  * `iteratedDeriv_tsum_archSummand` — THE SWAP: differentiation commutes with the infinite sum,
    proven by iterating Mathlib's locally-uniform-limit derivative theorem on the open ball
    `ball 0 (1/4)` (no per-order summable bounds, only B1b-pt1's single 0-th-order uniform bound).
  * `taylorCoeff_Gammaℝ_elem` — the headline: `taylorCoeff Γℝ n` as `−(γ+log π)/2·(n+1) − 1 +
    ∑'_j ((n+1)/(2(j+1)) − 1 + ((2j+2)/(2j+3))^(n+1))`, a harmonic-number-shaped series.

conjecture1_proved = False: Γ-function calculus; nothing here approaches RH.
-/
import Mathlib
import RvMArchElemBound
import RvMMobius
import RvMLiConnection
import Lc.LiCriterion.Basic

open Complex

namespace RvMWeierstrass

/-- **Iterated derivative of `M² = ((1−z)⁻¹)²`.**  `d^n/dz^n ((1−z)⁻¹)² = (n+1)!/(1−z)^(n+2)`. -/
theorem iteratedDeriv_invOneSub_sq (n : ℕ) {z : ℂ} (hz : z ≠ 1) :
    iteratedDeriv n (fun w : ℂ => ((1 - w)⁻¹) ^ 2) z
      = ((n + 1).factorial : ℂ) / (1 - z) ^ (n + 2) := by
  -- `((1−w)⁻¹)² = deriv (fun w => (1−w)⁻¹) w` on the open set `{w | w ≠ 1}`
  have hsq : (fun w : ℂ => ((1 - w)⁻¹) ^ 2)
      =ᶠ[nhds z] deriv (fun w : ℂ => (1 - w)⁻¹) := by
    filter_upwards [isOpen_ne.mem_nhds hz] with w hw
    have h1 := iteratedDeriv_mobius 1 hw
    rw [iteratedDeriv_one] at h1
    have hne : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
    rw [h1, Nat.factorial_one]
    field_simp
    ring
  rw [Filter.EventuallyEq.iteratedDeriv_eq n hsq, ← iteratedDeriv_succ',
    iteratedDeriv_mobius (n + 1) hz]

/-- **Iterated derivative of a scaled Möbius `(a − b·z)⁻¹`.**  For `a − b·z ≠ 0`,
    `d^n/dz^n (a − b·w)⁻¹ = n!·bⁿ/(a − b·z)^(n+1)`. -/
theorem iteratedDeriv_scaledMobius (n : ℕ) (a b : ℂ) {z : ℂ} (hz : a - b * z ≠ 0) :
    iteratedDeriv n (fun w : ℂ => (a - b * w)⁻¹) z
      = (n.factorial : ℂ) * b ^ n / (a - b * z) ^ (n + 1) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have hnbhd : iteratedDeriv n (fun w : ℂ => (a - b * w)⁻¹)
        =ᶠ[nhds z] fun w => (n.factorial : ℂ) * b ^ n / (a - b * w) ^ (n + 1) := by
      have hopen : IsOpen {w : ℂ | a - b * w ≠ 0} :=
        isOpen_ne.preimage (by fun_prop)
      filter_upwards [hopen.mem_nhds hz] with w hw using ih hw
    rw [Filter.EventuallyEq.deriv_eq hnbhd]
    -- differentiate the closed form
    have hbase : HasDerivAt (fun w : ℂ => a - b * w) (-b) z := by
      have : HasDerivAt (fun w : ℂ => a - b * w) (0 - b * 1) z :=
        (hasDerivAt_const z a).sub ((hasDerivAt_id z).const_mul b)
      simpa using this
    have hd : HasDerivAt (fun w : ℂ => (n.factorial : ℂ) * b ^ n / (a - b * w) ^ (n + 1))
        ((n.factorial : ℂ) * b ^ n *
          (-(↑(n + 1) * (a - b * z) ^ n * -b) / ((a - b * z) ^ (n + 1)) ^ 2)) z := by
      have hfun : (fun w : ℂ => (n.factorial : ℂ) * b ^ n / (a - b * w) ^ (n + 1))
          = fun w : ℂ => (n.factorial : ℂ) * b ^ n * ((a - b * w) ^ (n + 1))⁻¹ := by
        funext w; rw [div_eq_mul_inv]
      rw [hfun]
      exact ((hbase.pow (n + 1)).inv (pow_ne_zero _ hz)).const_mul ((n.factorial : ℂ) * b ^ n)
    rw [hd.deriv]
    have hpow2 : ((a - b * z) ^ (n + 1)) ^ 2 = (a - b * z) ^ (n + 1 + 1) * (a - b * z) ^ n := by
      rw [← pow_add, ← pow_mul]; congr 1; omega
    rw [Nat.factorial_succ, hpow2]
    rw [show -(↑(n + 1) * (a - b * z) ^ n * -b) = (↑(n + 1) : ℂ) * b * (a - b * z) ^ n by ring]
    rw [show (n.factorial : ℂ) * b ^ n * ((↑(n + 1) * b * (a - b * z) ^ n)
        / ((a - b * z) ^ (n + 1 + 1) * (a - b * z) ^ n))
        = ((n.factorial : ℂ) * b ^ n * (↑(n + 1) * b)) * (a - b * z) ^ n
            / ((a - b * z) ^ (n + 1 + 1) * (a - b * z) ^ n) by ring]
    rw [mul_div_mul_right _ _ (pow_ne_zero n hz)]
    push_cast [Nat.factorial_succ]; ring

/-- **Linear form of the elementary summand.**  On `‖z‖ < 1/2`,
    `archSummand j z = 1/(2(j+1))·M² − M + (2j+2)·((2j+3)−(2j+2)z)⁻¹`, `M = (1−z)⁻¹`.  The split of
    `−M/D` into `−M + (2j+2)/D` (key identity `M·D = (2j+2) + M`) puts every summand into a form
    whose `n`-th Taylor coefficient is read off term-by-term from the two Möbius closed forms. -/
theorem archSummand_eq_linear (j : ℕ) {z : ℂ} (hz : ‖z‖ < 1 / 2) :
    archSummand j z
      = 1 / (2 * ((j : ℂ) + 1)) * ((1 - z)⁻¹) ^ 2
        - (1 - z)⁻¹
        + (2 * (j : ℂ) + 2) * ((2 * (j : ℂ) + 3) - (2 * (j : ℂ) + 2) * z)⁻¹ := by
  have hzre : z.re < 1 / 2 :=
    lt_of_le_of_lt ((le_abs_self _).trans (abs_re_le_norm z)) hz
  have hne : (1 : ℂ) - z ≠ 0 := by
    intro hc
    have h1 : z.re = 1 := by have h := sub_eq_zero.mp hc; rw [← h]; simp
    rw [h1] at hzre; norm_num at hzre
  have hDne : ((2 * (j : ℂ) + 3) - (2 * (j : ℂ) + 2) * z) ≠ 0 := by
    intro hc
    have h1 : (2 * (j : ℂ) + 3) = (2 * (j : ℂ) + 2) * z := by linear_combination hc
    have h4 := congrArg norm h1
    rw [show (2 * (j : ℂ) + 3) = ((2 * j + 3 : ℕ) : ℂ) by push_cast; ring,
      Complex.norm_natCast, norm_mul,
      show (2 * (j : ℂ) + 2) = ((2 * j + 2 : ℕ) : ℂ) by push_cast; ring,
      Complex.norm_natCast] at h4
    have h6 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    push_cast at h4
    nlinarith [hz, norm_nonneg z]
  unfold archSummand
  -- key cancellation: `M·D = (2j+2) + M`, hence `−M·D⁻¹ = −M + (2j+2)·D⁻¹`
  set D : ℂ := (2 * (j : ℂ) + 3) - (2 * (j : ℂ) + 2) * z with hDdef
  -- key cancellation: `M·D = (2j+2) + M` (from `M·(1−z)=1`, `D = (2j+2)(1−z)+1`)
  have hMD : (1 - z)⁻¹ * D = (2 * (j : ℂ) + 2) + (1 - z)⁻¹ := by
    have hM1 : (1 - z)⁻¹ * (1 - z) = 1 := inv_mul_cancel₀ hne
    rw [hDdef]
    linear_combination (2 * (j : ℂ) + 2) * hM1
  -- divide by `D`:  `M·D⁻¹ = M − (2j+2)·D⁻¹`
  have hMDinv : (1 - z)⁻¹ * D⁻¹ = (1 - z)⁻¹ - (2 * (j : ℂ) + 2) * D⁻¹ := by
    have hDinv : D * D⁻¹ = 1 := mul_inv_cancel₀ hDne
    have h := congrArg (fun x => x * D⁻¹) hMD
    simp only [mul_assoc] at h
    rw [hDinv, mul_one] at h
    linear_combination -h
  linear_combination -hMDinv

/-- **The `n`-th derivative of a single summand at `0`.**  Combining the linear form with the two
    Möbius closed forms evaluated at `0`:
    `iteratedDeriv n (archSummand j) 0 = (n+1)!/(2(j+1)) − n! + n!·(2j+2)^(n+1)/(2j+3)^(n+1)`. -/
theorem iteratedDeriv_archSummand_zero (n j : ℕ) :
    iteratedDeriv n (archSummand j) 0
      = ((n + 1).factorial : ℂ) / (2 * ((j : ℂ) + 1))
        - (n.factorial : ℂ)
        + (n.factorial : ℂ) * (2 * (j : ℂ) + 2) ^ (n + 1) / (2 * (j : ℂ) + 3) ^ (n + 1) := by
  -- the three pieces of the linear form are entire near 0 (inverses of nonvanishing polynomials)
  have hz1 : (0 : ℂ) ≠ 1 := by norm_num
  have hane : (2 * (j : ℂ) + 3) - (2 * (j : ℂ) + 2) * 0 ≠ 0 := by
    rw [mul_zero, sub_zero]
    have : (2 * (j : ℂ) + 3) = ((2 * j + 3 : ℕ) : ℂ) := by push_cast; ring
    rw [this]
    exact_mod_cast (Nat.succ_ne_zero (2 * j + 2))
  -- smoothness of each piece at 0
  have hM : ContDiffAt ℂ (n : ℕ∞) (fun w : ℂ => (1 - w)⁻¹) 0 :=
    (contDiffAt_const.sub contDiffAt_id).inv (by norm_num)
  have hP1' : ContDiffAt ℂ (n : ℕ∞) (fun w : ℂ => 1 / (2 * ((j : ℂ) + 1)) * ((1 - w)⁻¹) ^ 2) 0 :=
    contDiffAt_const.mul (hM.pow 2)
  have hP3 : ContDiffAt ℂ (n : ℕ∞)
      (fun w : ℂ => (2 * (j : ℂ) + 2) * ((2 * (j : ℂ) + 3) - (2 * (j : ℂ) + 2) * w)⁻¹) 0 :=
    contDiffAt_const.mul ((contDiffAt_const.sub (contDiffAt_const.mul contDiffAt_id)).inv hane)
  -- split the linear form through iterated-derivative linearity
  have hEq : archSummand j =ᶠ[nhds (0 : ℂ)]
      fun z => 1 / (2 * ((j : ℂ) + 1)) * ((1 - z)⁻¹) ^ 2
        - (1 - z)⁻¹
        + (2 * (j : ℂ) + 2) * ((2 * (j : ℂ) + 3) - (2 * (j : ℂ) + 2) * z)⁻¹ := by
    have hball : Metric.ball (0 : ℂ) (1 / 2) ∈ nhds (0 : ℂ) :=
      Metric.ball_mem_nhds 0 (by norm_num)
    filter_upwards [hball] with z hz
    have hzn : ‖z‖ < 1 / 2 := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hz; exact hz
    exact archSummand_eq_linear j hzn
  rw [Filter.EventuallyEq.iteratedDeriv_eq n hEq,
    iteratedDeriv_fun_add (hP1'.sub hM) hP3,
    iteratedDeriv_fun_sub hP1' hM,
    iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field,
    iteratedDeriv_invOneSub_sq n hz1, iteratedDeriv_mobius_zero n,
    iteratedDeriv_scaledMobius n (2 * (j : ℂ) + 3) (2 * (j : ℂ) + 2) hane]
  -- evaluate the closed forms at 0
  rw [show (1 : ℂ) - 0 = 1 by ring, one_pow, div_one, mul_zero, sub_zero]
  ring

/-- `archSummand j` is analytic on the open ball `ball 0 (1/4)` (inverse of a nonvanishing
    polynomial; the poles lie at `1` and `(2j+3)/(2j+2) ≥ 1`, both outside the ball). -/
theorem archSummand_analyticOnNhd (j : ℕ) :
    AnalyticOnNhd ℂ (archSummand j) (Metric.ball (0 : ℂ) (1 / 4)) := by
  refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) Metric.isOpen_ball
  have hzn : ‖z‖ < 1 / 2 := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hz
    linarith
  have hne : (1 : ℂ) - z ≠ 0 := by
    intro hc
    have h1 : (1 : ℝ) ≤ ‖z‖ := by
      have := congrArg norm hc
      simp only [norm_zero] at this
      have h2 : ‖(1 : ℂ)‖ - ‖z‖ ≤ ‖(1 : ℂ) - z‖ := norm_sub_norm_le _ _
      rw [this, norm_one] at h2; linarith
    linarith
  have hDne : ((2 * (j : ℂ) + 3) - (2 * (j : ℂ) + 2) * z) ≠ 0 := by
    intro hc
    have h1 : (2 * (j : ℂ) + 3) = (2 * (j : ℂ) + 2) * z := by linear_combination hc
    have h4 := congrArg norm h1
    rw [show (2 * (j : ℂ) + 3) = ((2 * j + 3 : ℕ) : ℂ) by push_cast; ring,
      Complex.norm_natCast, norm_mul,
      show (2 * (j : ℂ) + 2) = ((2 * j + 2 : ℕ) : ℂ) by push_cast; ring,
      Complex.norm_natCast] at h4
    have h6 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    push_cast at h4
    nlinarith [hzn, norm_nonneg z]
  unfold archSummand
  refine ((differentiableWithinAt_const _).mul ?_).sub (?_)
  · exact (((differentiableWithinAt_const 1).sub differentiableWithinAt_id).inv hne).pow 2
  · refine DifferentiableWithinAt.mul ?_ ?_
    · exact ((differentiableWithinAt_const 1).sub differentiableWithinAt_id).inv hne
    · exact ((differentiableWithinAt_const _).sub
        ((differentiableWithinAt_const _).mul differentiableWithinAt_id)).inv hDne

/-- **THE SWAP.**  On the open ball `ball 0 (1/4)`, differentiation commutes with the infinite sum:
    `iteratedDeriv n (fun z => ∑' j, archSummand j z) 0 = ∑' j, iteratedDeriv n (archSummand j) 0`.
    Proven by iterating Mathlib's locally-uniform-limit derivative theorem `n` times, carrying only
    differentiability of the finite partial sums' iterated derivatives (all analytic) — no per-order
    summable bounds, only B1b-pt1's single 0-th-order uniform bound. -/
theorem iteratedDeriv_tsum_archSummand (n : ℕ) :
    iteratedDeriv n (fun z => ∑' j : ℕ, archSummand j z) 0
      = ∑' j : ℕ, iteratedDeriv n (archSummand j) 0 := by
  set U : Set ℂ := Metric.ball (0 : ℂ) (1 / 4) with hUdef
  have hUopen : IsOpen U := Metric.isOpen_ball
  have h0U : (0 : ℂ) ∈ U := by rw [hUdef, Metric.mem_ball, dist_self]; norm_num
  -- each finite partial sum is differentiable on U (finite sum of analytic terms)
  have hFdiff : ∀ (k : ℕ) (t : Finset ℕ),
      DifferentiableOn ℂ (deriv^[k] (fun z => ∑ j ∈ t, archSummand j z)) U := by
    intro k t
    have hana : AnalyticOnNhd ℂ (fun z => ∑ j ∈ t, archSummand j z) U :=
      Finset.analyticOnNhd_fun_sum t (fun j _ => archSummand_analyticOnNhd j)
    exact (hana.iterated_deriv k).differentiableOn
  -- the deriv-composed finite sum converges locally uniformly to the deriv-composed tsum
  -- base case: the partial sums converge loc-unif to the tsum on U
  have hbase : TendstoLocallyUniformlyOn
      (fun (t : Finset ℕ) (z : ℂ) => ∑ j ∈ t, archSummand j z)
      (fun z => ∑' j : ℕ, archSummand j z) Filter.atTop U :=
    (tendstoUniformlyOn_archSummand.mono (by
      rw [hUdef]; exact Metric.ball_subset_closedBall)).tendstoLocallyUniformlyOn
  -- iterate the derivative theorem k times
  have hiter : ∀ k : ℕ, TendstoLocallyUniformlyOn
      (fun (t : Finset ℕ) (z : ℂ) => deriv^[k] (fun z => ∑ j ∈ t, archSummand j z) z)
      (deriv^[k] (fun z => ∑' j : ℕ, archSummand j z)) Filter.atTop U := by
    intro k
    induction k with
    | zero => simpa using hbase
    | succ k ih =>
      have hstep := ih.deriv (Filter.Eventually.of_forall (fun t => hFdiff k t)) hUopen
      -- `deriv ∘ (deriv^[k] ∘ F) = deriv^[k+1] ∘ F`; rewrite both functions into `deriv^[k+1]` form
      have hrwL : (deriv ∘ fun (t : Finset ℕ) (z : ℂ) =>
            deriv^[k] (fun z => ∑ j ∈ t, archSummand j z) z)
          = fun (t : Finset ℕ) (z : ℂ) =>
            deriv^[k + 1] (fun z => ∑ j ∈ t, archSummand j z) z := by
        funext t z
        rw [Function.comp_apply, Function.iterate_succ', Function.comp_apply]
      have hrwR : deriv (deriv^[k] fun z : ℂ => ∑' j : ℕ, archSummand j z)
          = deriv^[k + 1] (fun z : ℂ => ∑' j : ℕ, archSummand j z) := by
        rw [Function.iterate_succ', Function.comp_apply]
      rw [hrwL, hrwR] at hstep
      exact hstep
  -- evaluate the k=n limit at 0
  have hpt := (hiter n).tendsto_at h0U
  -- rewrite both sides via iteratedDeriv
  simp only [← iteratedDeriv_eq_iterate] at hpt
  -- the finite swap: iteratedDeriv of a finite sum is the finite sum of iteratedDerivs
  have hfin : ∀ t : Finset ℕ,
      iteratedDeriv n (fun z => ∑ j ∈ t, archSummand j z) 0
        = ∑ j ∈ t, iteratedDeriv n (archSummand j) 0 := by
    intro t
    refine iteratedDeriv_fun_sum (fun j _ => ?_)
    exact ((archSummand_analyticOnNhd j).contDiffOn hUopen.uniqueDiffOn).contDiffAt
      (hUopen.mem_nhds h0U) |>.of_le le_top
  simp only [hfin] at hpt
  -- convergence of Finset partial sums atTop IS HasSum
  have hHS : HasSum (fun j : ℕ => iteratedDeriv n (archSummand j) 0)
      (iteratedDeriv n (fun z => ∑' j : ℕ, archSummand j z) 0) := hpt
  exact hHS.tsum_eq.symm

set_option maxHeartbeats 1000000 in
/-- **The archimedean Li coefficient, as an elementary harmonic-number-shaped series.**
    `taylorCoeff Γℝ n = −(γ+log π)/2·(n+1) − 1 + ∑'_j ((n+1)/(2(j+1)) − 1 + ((2j+2)/(2j+3))^(n+1))`.
    The `n`-th Taylor coefficient of the archimedean factor of the Li generating function, reduced to
    an explicit elementary series (PR B1b part 2).  conjecture1_proved = False. -/
theorem taylorCoeff_Gammaℝ_elem (n : ℕ) :
    LiCriterion.taylorCoeff Complex.Gammaℝ n
      = -((Real.eulerMascheroniConstant : ℂ) + Complex.log (Real.pi : ℂ)) / 2 * ((n : ℂ) + 1)
        - 1
        + ∑' j : ℕ, (((n : ℂ) + 1) / (2 * ((j : ℂ) + 1)) - 1
            + (((2 * (j : ℂ) + 2) / (2 * (j : ℂ) + 3)) ^ (n + 1))) := by
  set U : Set ℂ := Metric.ball (0 : ℂ) (1 / 4) with hUdef
  have hUopen : IsOpen U := Metric.isOpen_ball
  have h0U : (0 : ℂ) ∈ U := by rw [hUdef, Metric.mem_ball, dist_self]; norm_num
  have hz1 : (0 : ℂ) ≠ 1 := by norm_num
  -- the three terms of the B1a identity, as functions
  set c : ℂ := -((Real.eulerMascheroniConstant : ℂ) + Complex.log (Real.pi : ℂ)) / 2 with hcdef
  -- smoothness at 0 of the two elementary heads and the tsum tail
  have hMsq : ContDiffAt ℂ (n : ℕ∞) (fun w : ℂ => c * ((1 - w)⁻¹) ^ 2) 0 :=
    contDiffAt_const.mul (((contDiffAt_const.sub contDiffAt_id).inv (by norm_num)).pow 2)
  have hM : ContDiffAt ℂ (n : ℕ∞) (fun w : ℂ => (1 - w)⁻¹) 0 :=
    (contDiffAt_const.sub contDiffAt_id).inv (by norm_num)
  have hTail : ContDiffAt ℂ (n : ℕ∞) (fun z => ∑' j : ℕ, archSummand j z) 0 := by
    have hana : AnalyticOnNhd ℂ (fun z => ∑' j : ℕ, archSummand j z) U := by
      refine (differentiableOn_tsum_of_summable_norm summable_archBound
        (fun j => (archSummand_analyticOnNhd j).differentiableOn) hUopen
        (fun j w hw => ?_)).analyticOnNhd hUopen
      have hwn : ‖w‖ ≤ 1 / 4 := by
        rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hw; linarith
      exact archSummand_norm_le j hwn
    exact (hana.contDiffOn hUopen.uniqueDiffOn).contDiffAt (hUopen.mem_nhds h0U) |>.of_le le_top
  -- unfold taylorCoeff and rewrite phi Γℝ to the Möbius pullback
  rw [LiCriterion.taylorCoeff, ← iteratedDeriv_eq_iterate, LiCriterion.logDeriv_eq_rootLogDeriv,
    show LiCriterion.phi Complex.Gammaℝ = fun w : ℂ => Complex.Gammaℝ ((1 - w)⁻¹) by
      funext w; rw [LiCriterion.phi, one_div]]
  -- replace the log-derivative by the B1a elementary series near 0
  have hEq : (fun z => logDeriv (fun w : ℂ => Complex.Gammaℝ ((1 - w)⁻¹)) z)
      =ᶠ[nhds (0 : ℂ)]
      fun z => c * ((1 - z)⁻¹) ^ 2 - (1 - z)⁻¹ + ∑' j : ℕ, archSummand j z := by
    have hball : Metric.ball (0 : ℂ) (1 / 2) ∈ nhds (0 : ℂ) :=
      Metric.ball_mem_nhds 0 (by norm_num)
    filter_upwards [hball] with z hz
    have hzn : ‖z‖ < 1 / 2 := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hz; exact hz
    rw [logDeriv_phi_Gammaℝ_eq_elem hzn, hcdef]
  rw [Filter.EventuallyEq.iteratedDeriv_eq n hEq,
    iteratedDeriv_fun_add (hMsq.sub hM) hTail,
    iteratedDeriv_fun_sub hMsq hM,
    iteratedDeriv_const_mul_field,
    iteratedDeriv_invOneSub_sq n hz1, iteratedDeriv_mobius_zero n,
    iteratedDeriv_tsum_archSummand n]
  -- evaluate the two heads at 0, substitute per-summand derivs, and divide by n!
  simp only [iteratedDeriv_archSummand_zero]
  rw [show (1 : ℂ) - 0 = 1 by ring, one_pow, div_one]
  have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hsucc : ((n + 1).factorial : ℂ) = ((n : ℂ) + 1) * (n.factorial : ℂ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  -- push the n!-division into the tsum, then split heads / tail
  rw [add_div]
  congr 1
  · -- the two elementary heads: `(c·(n+1)! − n!)/n! = c·(n+1) − 1`
    rw [hsucc]
    field_simp
  · -- the tail: divide term-by-term
    rw [← tsum_div_const]
    refine tsum_congr fun j => ?_
    have hj1 : (2 : ℂ) * ((j : ℂ) + 1) ≠ 0 :=
      mul_ne_zero two_ne_zero (Nat.cast_add_one_ne_zero j)
    have h2j3 : (2 * (j : ℂ) + 3) ^ (n + 1) ≠ 0 := by
      apply pow_ne_zero
      rw [show (2 * (j : ℂ) + 3) = ((2 * j + 3 : ℕ) : ℂ) by push_cast; ring]
      exact_mod_cast Nat.succ_ne_zero (2 * j + 2)
    rw [hsucc, div_pow]
    field_simp

end RvMWeierstrass
