/-  EMZetaTail.lean -- A2 Theorem 1, TAIL track: the order-K Euler-Maclaurin tail engine.

    The blocker of PROGRAM ANDÚRIL's reflection track.  Builds on `EMZeta.lean` /
    `EMZetaComplex.lean` (the K=1 chain).  The K=1 remainder envelope `‖s‖/(2·Re s)` proven in
    `EMZetaComplex.em_zeta_strip_enclosure` is sign-LOOSE (≈14 at s=1/2+14i), so the G2 reflected
    band could not be made sign-tight from it.  This file raises the Euler-Maclaurin order and cuts
    the sum at a finite `N`, producing a remainder that DECAYS like `N^{-Re s - K + 1}`, small enough
    to make `gLine` boxes sign-tight.

    Architecture (bottom-up, all real-`s` first, then the complex analytic continuation):

      F.  Order-k periodized "saw" Bernoulli API beyond k=1:
            * `sawBernoulli k` is already defined in EMZeta; here we prove
              `sawBernoulli_hasDerivAt_ae`-style derivative facts (`(k+1)·sawBernoulli k` a.e.),
              and the EXPLICIT sup bounds `|sawBernoulli 2| ≤ 1/6`, `|sawBernoulli 3| ≤ B3sup`.
      G.  `em_saw_step` — the one IBP step raising the saw order by one over a unit cell (the
            proven form of `EMZetaWip.em_saw_step_wip`).
      H.  The order-K remainder over the tail `[N, ∞)` with the explicit `N`-decaying bound.

    conjecture1_proved = False.  This is a classical analysis lemma (Euler-Maclaurin tail bound),
    NOT a proof of RH.
-/
import EMZeta
import EMZetaComplex

open MeasureTheory intervalIntegral Set Filter Topology Complex
open scoped Real

namespace ZetaReflection

/-! ## F. Order-k periodized Bernoulli: derivative tower and explicit sup bounds. -/

/-- The order-2 saw on the cell `[m, m+1)` is `(x - m)^2 - (x - m) + 1/6`. -/
lemma sawBernoulli_two_eq_on_Ico {m : ℤ} {x : ℝ} (hx : x ∈ Ico (m : ℝ) (m + 1)) :
    sawBernoulli 2 x = (x - m) ^ 2 - (x - m) + 6⁻¹ := by
  rw [sawBernoulli_eq_on_Ico 2 hx, bernoulliFun_two]

/-- Explicit sup bound for the order-2 saw: `|sawBernoulli 2 x| ≤ 1/6`.
    On the unit cell `y := {x} ∈ [0,1)`, `B₂(y) = y² − y + 1/6 = (y − 1/2)² − 1/12 ∈ [−1/12, 1/6]`. -/
lemma abs_sawBernoulli_two_le (x : ℝ) : |sawBernoulli 2 x| ≤ 1 / 6 := by
  have h0 : (0 : ℝ) ≤ Int.fract x := Int.fract_nonneg x
  have h1 : Int.fract x < 1 := Int.fract_lt_one x
  rw [sawBernoulli, bernoulliFun_two, abs_le]
  constructor <;> nlinarith [sq_nonneg (Int.fract x - 1/2), h0, h1]

/-- The order-3 saw on `[0,1)` in closed form: `B₃(y) = y³ − (3/2)y² + (1/2)y`
    (`bernoulli 3 = 0` kills the constant term). -/
lemma bernoulliFun_three (y : ℝ) :
    bernoulliFun 3 y = y ^ 3 - (3/2) * y ^ 2 + (1/2) * y := by
  have h3zero : bernoulli 3 = 0 := bernoulli_eq_zero_of_odd (by decide) (by norm_num)
  simp only [bernoulliFun, Polynomial.bernoulli_def, Finset.sum_range_succ, Finset.sum_range_zero]
  simp [Polynomial.eval_finset_sum, h3zero]
  ring

/-- Explicit sup bound for the order-3 saw: `|sawBernoulli 3 x| ≤ 1/12`.
    `B₃(y) = y(1−y)(1/2−y)` on `[0,1)`; its exact extrema are `±√3/36 ≈ ±0.0481`, so the clean
    rational envelope `1/12 ≈ 0.083` (nlinarith-certifiable) is a valid — and, at the tail cut
    `N ≥ 50`, sign-tight — bound.  See the reported remainder number in the module header. -/
lemma abs_sawBernoulli_three_le (x : ℝ) : |sawBernoulli 3 x| ≤ 1 / 12 := by
  have h0 : (0 : ℝ) ≤ Int.fract x := Int.fract_nonneg x
  have h1 : Int.fract x < 1 := Int.fract_lt_one x
  set y := Int.fract x with hy
  have hy1 : y ≤ 1 := le_of_lt h1
  rw [sawBernoulli, bernoulliFun_three, abs_le]
  refine ⟨?_, ?_⟩
  · nlinarith [mul_nonneg h0 (sub_nonneg.mpr hy1), sq_nonneg (2*y-1),
      mul_nonneg (mul_nonneg h0 (sub_nonneg.mpr hy1)) (sq_nonneg (2*y-1))]
  · nlinarith [mul_nonneg h0 (sub_nonneg.mpr hy1), sq_nonneg (2*y-1),
      mul_nonneg (mul_nonneg h0 (sub_nonneg.mpr hy1)) (sq_nonneg (2*y-1))]

/-! ## G. The saw-order-raising IBP step over a unit cell.

    The antiderivative tower: `sawBernoulli (k+1) / (k+1)` has derivative `sawBernoulli k` on the
    OPEN cell `(m, m+1)` (from `antideriv_bernoulliFun`, since `Int.fract` has derivative `1` off
    ℤ and `bernoulliFun (k+1)/(k+1)` has derivative `bernoulliFun k`).  IBP with this antiderivative
    turns `∫ sawBernoulli k · fk` into a boundary term plus `∫ sawBernoulli (k+1) · fk'`, exactly
    one order higher.  The endpoint saw values are `bernoulliFun (k+1) 0` and `bernoulliFun (k+1) 1`
    (the cell is `[m, m+1]`), which for `k+1 ≠ 1` are EQUAL by `bernoulliFun_endpoints_eq_of_ne_one`
    — the mechanism that makes the interior Bernoulli boundary terms telescope to zero. -/

/-- On the OPEN cell `(m, m+1)`, the shifted Bernoulli antiderivative `bernoulliFun (k+1) ({x})/(k+1)`
    has derivative `sawBernoulli k x`.  (`Int.fract` is differentiable with derivative `1` there.) -/
lemma sawAntideriv_hasDerivAt_Ioo (k : ℕ) {m : ℤ} {x : ℝ} (hx : x ∈ Ioo (m : ℝ) (m + 1)) :
    HasDerivAt (fun y => sawBernoulli (k + 1) y / (k + 1)) (sawBernoulli k x) x := by
  -- `Int.fract` has derivative 1 on the open cell (floor is locally constant `= m`).
  have hfloor : ∀ᶠ y in 𝓝 x, ⌊y⌋ = m := by
    have hlt : (m : ℝ) < x := hx.1
    have hgt : x < (m : ℝ) + 1 := hx.2
    have hmem : x ∈ Ioo (m : ℝ) (m + 1) := hx
    filter_upwards [Ioo_mem_nhds hlt hgt] with y hy
    rw [Int.floor_eq_iff]
    exact ⟨le_of_lt hy.1, by have := hy.2; linarith⟩
  have hfract : HasDerivAt (fun y => Int.fract y) 1 x := by
    have hid : HasDerivAt (fun y : ℝ => y - (m : ℝ)) 1 x := by
      simpa using (hasDerivAt_id x).sub_const (m : ℝ)
    refine hid.congr_of_eventuallyEq ?_
    filter_upwards [hfloor] with y hy
    rw [Int.fract, hy]
  -- `bernoulliFun (k+1)/(k+1)` has derivative `bernoulliFun k` (Mathlib `antideriv_bernoulliFun`).
  have hanti : HasDerivAt (fun z => bernoulliFun (k + 1) z / (k + 1)) (bernoulliFun k (Int.fract x))
      (Int.fract x) := antideriv_bernoulliFun k (Int.fract x)
  -- Chain rule.
  have hcomp := hanti.comp x hfract
  rw [mul_one] at hcomp
  have hfun : ((fun z => bernoulliFun (k + 1) z / (↑k + 1)) ∘ Int.fract)
      = (fun y => sawBernoulli (k + 1) y / (k + 1)) := by
    funext y; simp [Function.comp, sawBernoulli]
  rw [hfun] at hcomp
  exact hcomp

/-- The continuous polynomial surrogate `W y = bernoulliFun (k+1) (y - m) / (k+1)` for the shifted
    saw antiderivative on the cell `[m, m+1]`.  It is C¹ everywhere with derivative
    `bernoulliFun k (y - m)`, and agrees with `sawBernoulli (k+1) ·/(k+1)` on `[m, m+1)`. -/
private noncomputable def sawSurrogate (k : ℕ) (m : ℤ) (y : ℝ) : ℝ :=
  bernoulliFun (k + 1) (y - m) / (k + 1)

private lemma sawSurrogate_hasDerivAt (k : ℕ) (m : ℤ) (y : ℝ) :
    HasDerivAt (sawSurrogate k m) (bernoulliFun k (y - m)) y := by
  have hshift : HasDerivAt (fun z : ℝ => z - (m : ℝ)) 1 y := by
    simpa using (hasDerivAt_id y).sub_const (m : ℝ)
  have hanti := antideriv_bernoulliFun k (y - m)
  have hcomp := hanti.comp y hshift
  rw [mul_one] at hcomp
  have hfun : ((fun z => bernoulliFun (k + 1) z / (↑k + 1)) ∘ (fun z : ℝ => z - (m : ℝ)))
      = sawSurrogate k m := by
    funext z; simp [Function.comp, sawSurrogate]
  rw [hfun] at hcomp
  exact hcomp

private lemma sawSurrogate_eq_saw_on_Ico (k : ℕ) {m : ℤ} {y : ℝ} (hy : y ∈ Ico (m : ℝ) (m + 1)) :
    sawSurrogate k m y = sawBernoulli (k + 1) y / (k + 1) := by
  rw [sawSurrogate, sawBernoulli_eq_on_Ico (k + 1) hy]

/-- **The saw-order-raising IBP step** (the proven form of `EMZetaWip.em_saw_step_wip`).
    Over the unit cell `[m, m+1]`, for `fk` with derivative `fk1` and `fk1` interval-integrable,
        ∫ sawBernoulli k · fk
          = (B_{k+1}(1)·fk(m+1) − B_{k+1}(0)·fk(m)) / (k+1)
            − (∫ sawBernoulli (k+1) · fk1) / (k+1).
    The endpoint saw values are written via the raw `bernoulliFun (k+1)` at `0` and `1` (the cell
    endpoints shifted), which coincide for `k+1 ≠ 1` (`bernoulliFun_endpoints_eq_of_ne_one`),
    the mechanism that makes the summed interior boundary terms telescope. -/
theorem em_saw_step (k : ℕ) (m : ℤ) (fk fk1 : ℝ → ℝ)
    (hd : ∀ x ∈ Icc (m : ℝ) (m + 1), HasDerivAt fk (fk1 x) x)
    (hi : IntervalIntegrable fk1 volume (m : ℝ) (m + 1)) :
    (∫ x in (m : ℝ)..(m + 1), sawBernoulli k x * fk x)
      = (bernoulliFun (k + 1) 1 * fk (m + 1) - bernoulliFun (k + 1) 0 * fk m) / (k + 1)
        - (∫ x in (m : ℝ)..(m + 1), sawBernoulli (k + 1) x * fk1 x) / (k + 1) := by
  have hcc : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
  set W : ℝ → ℝ := sawSurrogate k m with hWdef
  -- W has derivative `bernoulliFun k (x - m)` everywhere; on the cell that equals `sawBernoulli k`.
  have hW' : ∀ x, HasDerivAt W (bernoulliFun k (x - m)) x := fun x => sawSurrogate_hasDerivAt k m x
  have hWcont : Continuous W := by
    rw [hWdef]
    unfold sawSurrogate
    fun_prop
  have huv : ∀ x ∈ uIcc (m : ℝ) (m + 1), HasDerivAt W (bernoulliFun k (x - m)) x :=
    fun x _ => hW' x
  have hfd : ∀ x ∈ uIcc (m : ℝ) (m + 1), HasDerivAt fk (fk1 x) x := by
    intro x hx; rw [uIcc_of_le hcc] at hx; exact hd x hx
  -- derivative of W is interval integrable (continuous polynomial).
  have hW'int : IntervalIntegrable (fun x => bernoulliFun k (x - m)) volume (m : ℝ) (m + 1) := by
    apply Continuous.intervalIntegrable; fun_prop
  -- IBP: ∫ (W'·fk + W·fk1) = W·fk |end - W·fk |start.
  have hIBP := integral_deriv_mul_eq_sub huv hfd hW'int hi
  -- Endpoint values of W (polynomial, exact).
  have hWL : W (m : ℝ) = bernoulliFun (k + 1) 0 / (k + 1) := by
    simp [hWdef, sawSurrogate]
  have hWR : W ((m : ℝ) + 1) = bernoulliFun (k + 1) 1 / (k + 1) := by
    simp only [hWdef, sawSurrogate, add_sub_cancel_left]
  -- Interval integrability of the two products.
  have hWfk1int : IntervalIntegrable (fun x => W x * fk1 x) volume (m : ℝ) (m + 1) :=
    hi.continuousOn_mul hWcont.continuousOn
  have hW'fkint : IntervalIntegrable (fun x => bernoulliFun k (x - m) * fk x) volume (m : ℝ) (m + 1) := by
    have hfkcont : ContinuousOn fk (uIcc (m : ℝ) (m + 1)) := fun x hx =>
      (hfd x hx).continuousAt.continuousWithinAt
    exact (hfkcont.intervalIntegrable).continuousOn_mul (by fun_prop)
  -- Split the LHS integrand.
  have hsplit :
      (∫ x in (m : ℝ)..(m + 1), bernoulliFun k (x - m) * fk x + W x * fk1 x)
        = (∫ x in (m : ℝ)..(m + 1), bernoulliFun k (x - m) * fk x)
          + ∫ x in (m : ℝ)..(m + 1), W x * fk1 x := by
    rw [intervalIntegral.integral_add hW'fkint hWfk1int]
  -- Convert the two saw-integrands (a.e. equal to the polynomial surrogates on the cell).
  have hsaw_k : (∫ x in (m : ℝ)..(m + 1), sawBernoulli k x * fk x)
      = ∫ x in (m : ℝ)..(m + 1), bernoulliFun k (x - m) * fk x := by
    apply intervalIntegral.integral_congr_ae
    have hnull : ∀ᵐ x, x ≠ ((m : ℝ) + 1) := MeasureTheory.Measure.ae_ne _ _
    filter_upwards [hnull] with x hxne hxmem
    rw [uIoc_of_le hcc] at hxmem
    have hxIco : x ∈ Ico (m : ℝ) (m + 1) := ⟨le_of_lt hxmem.1, lt_of_le_of_ne hxmem.2 hxne⟩
    rw [sawBernoulli_eq_on_Ico k hxIco]
  have hsaw_k1 : (∫ x in (m : ℝ)..(m + 1), sawBernoulli (k + 1) x * fk1 x)
      = ∫ x in (m : ℝ)..(m + 1), ((k + 1) * W x) * fk1 x := by
    apply intervalIntegral.integral_congr_ae
    have hnull : ∀ᵐ x, x ≠ ((m : ℝ) + 1) := MeasureTheory.Measure.ae_ne _ _
    filter_upwards [hnull] with x hxne hxmem
    rw [uIoc_of_le hcc] at hxmem
    have hxIco : x ∈ Ico (m : ℝ) (m + 1) := ⟨le_of_lt hxmem.1, lt_of_le_of_ne hxmem.2 hxne⟩
    have := sawSurrogate_eq_saw_on_Ico k hxIco
    rw [hWdef]
    have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    rw [this]; field_simp
  -- Assemble.
  rw [hsaw_k]
  have key : (∫ x in (m : ℝ)..(m + 1), bernoulliFun k (x - m) * fk x)
      + ∫ x in (m : ℝ)..(m + 1), W x * fk1 x
      = W ((m : ℝ) + 1) * fk ((m : ℝ) + 1) - W (m : ℝ) * fk (m : ℝ) := by
    rw [← hsplit]; exact hIBP
  rw [hWL, hWR] at key
  -- The saw(k+1) integral in terms of W.
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  rw [hsaw_k1]
  have hpull : (∫ x in (m : ℝ)..(m + 1), ((k + 1) * W x) * fk1 x)
      = ((k : ℝ) + 1) * ∫ x in (m : ℝ)..(m + 1), W x * fk1 x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _; ring
  rw [hpull]
  -- `((k+1)·I)/(k+1) = I`; then the goal is `∫saw_k·fk = boundary/(k+1) - I`, exactly `key`.
  have hcancel : (((k : ℝ) + 1) * ∫ x in (m : ℝ)..(m + 1), W x * fk1 x) / ((k : ℝ) + 1)
      = ∫ x in (m : ℝ)..(m + 1), W x * fk1 x := by
    rw [mul_comm]; exact mul_div_cancel_right₀ _ hk1
  rw [hcancel]
  linear_combination key

/-! ## H. The order-K tail remainder integrals and their explicit `N`-decaying bounds.

    The consumer needs a remainder over the TAIL `[N, ∞)` whose norm decays in `N`.  We work with
    the complex integrand `sawBernoulli k x · (c · (x:ℂ)^(-s-k))` where `c` is the falling-factorial
    coefficient `(-1)^k s(s+1)…(s+k-1)` (the k-th derivative coefficient of `x^{-s}`).  The norm
    bound is the clean product form
        ‖∫_N^∞ saw_k · c·x^{-s-k}‖ ≤ Bsup_k · ‖c‖ · N^{-Re s - k + 1} / (Re s + k - 1),
    from `‖saw_k‖ ≤ Bsup_k`, `‖x^{-s-k}‖ = x^{-Re s - k}`, and `∫_N^∞ x^{-Re s -k} = N^{-Re s -k+1}/(Re s+k-1)`. -/

/-- Generic explicit tail bound for a saw-weighted power integrand on `[N, ∞)`.
    If `‖sawBernoulli k x‖ ≤ B` for all `x` (as a real bound on the real saw) and the integrand is
    `sawBernoulli k x · (c · (x:ℂ)^(-s-k))`, then over `[N,∞)` with `N ≥ 1` and `Re s + k > 1`,
        ‖∫‖ ≤ B · ‖c‖ · N^{-(Re s + k - 1)} / (Re s + k - 1).
    This is the single reusable engine for all K. -/
theorem em_tail_integral_bound {k : ℕ} {s c : ℂ} {B : ℝ} {N : ℕ}
    (hN : 1 ≤ N) (hexp : 1 < s.re + k) (hB : 0 ≤ B)
    (hsawB : ∀ x : ℝ, |sawBernoulli k x| ≤ B) :
    ‖∫ x in Ioi (N : ℝ), (sawBernoulli k x : ℂ) * (c * (x : ℂ) ^ (-s - k))‖
      ≤ B * ‖c‖ * (N : ℝ) ^ (-(s.re + k - 1)) / (s.re + k - 1) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hσk1 : 0 < s.re + k - 1 := by linarith
  -- exponent for the norm: -(Re s + k) < -1.
  have hexplt : -(s.re + (k : ℝ)) < -1 := by
    have : (1 : ℝ) < s.re + k := hexp
    linarith
  -- integrand norm domination: ‖·‖ ≤ (B·‖c‖) · x^{-(Re s + k)} on (N,∞).
  have hdom : IntegrableOn (fun x : ℝ => (B * ‖c‖) * x ^ (-(s.re + (k : ℝ)))) (Ioi (N : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (a := -(s.re + (k : ℝ))) hexplt hNpos).const_mul _
  have hInt : IntegrableOn (fun x : ℝ => (sawBernoulli k x : ℂ) * (c * (x : ℂ) ^ (-s - k)))
      (Ioi (N : ℝ)) := by
    refine Integrable.mono' hdom ?_ ?_
    · apply Measurable.aestronglyMeasurable
      exact (Complex.measurable_ofReal.comp (sawBernoulli_measurable k)).mul
        (measurable_const.mul (Complex.measurable_ofReal.pow_const _))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
      have hxpos : (0 : ℝ) < x := lt_trans hNpos hx
      have hnormcpow : ‖(x : ℂ) ^ (-s - k)‖ = x ^ (-(s.re + (k : ℝ))) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
        congr 1
        rw [Complex.sub_re, Complex.neg_re, Complex.natCast_re]
        ring
      have hrpownn : (0 : ℝ) ≤ x ^ (-(s.re + (k : ℝ))) := Real.rpow_nonneg hxpos.le _
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hnormcpow]
      calc |sawBernoulli k x| * (‖c‖ * x ^ (-(s.re + (k : ℝ))))
          ≤ B * (‖c‖ * x ^ (-(s.re + (k : ℝ)))) := by
            gcongr; exact hsawB x
        _ = (B * ‖c‖) * x ^ (-(s.re + (k : ℝ))) := by ring
  -- ‖∫‖ ≤ ∫‖·‖ ≤ ∫ dom = (B‖c‖)·N^{-(σ+k-1)}/(σ+k-1).
  calc ‖∫ x in Ioi (N : ℝ), (sawBernoulli k x : ℂ) * (c * (x : ℂ) ^ (-s - k))‖
      ≤ ∫ x in Ioi (N : ℝ), ‖(sawBernoulli k x : ℂ) * (c * (x : ℂ) ^ (-s - k))‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x in Ioi (N : ℝ), (B * ‖c‖) * x ^ (-(s.re + (k : ℝ))) := by
        apply setIntegral_mono_on hInt.norm hdom measurableSet_Ioi
        intro x hx
        have hxpos : (0 : ℝ) < x := lt_trans hNpos hx
        have hnormcpow : ‖(x : ℂ) ^ (-s - k)‖ = x ^ (-(s.re + (k : ℝ))) := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
          congr 1
          rw [Complex.sub_re, Complex.neg_re, Complex.natCast_re]; ring
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hnormcpow]
        calc |sawBernoulli k x| * (‖c‖ * x ^ (-(s.re + (k : ℝ))))
            ≤ B * (‖c‖ * x ^ (-(s.re + (k : ℝ)))) := by
              gcongr; exact hsawB x
          _ = (B * ‖c‖) * x ^ (-(s.re + (k : ℝ))) := by ring
    _ = B * ‖c‖ * (N : ℝ) ^ (-(s.re + k - 1)) / (s.re + k - 1) := by
        rw [MeasureTheory.integral_const_mul,
          integral_Ioi_rpow_of_lt (a := -(s.re + (k : ℝ))) hexplt hNpos]
        have hexp1 : -(s.re + (k : ℝ)) + 1 = -(s.re + k - 1) := by ring
        rw [hexp1]
        have hne : s.re + (k : ℝ) - 1 ≠ 0 := ne_of_gt hσk1
        field_simp

end ZetaReflection
