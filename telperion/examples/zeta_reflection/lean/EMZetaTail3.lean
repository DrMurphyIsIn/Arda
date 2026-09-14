/-  EMZetaTail3.lean -- A2 Theorem 1, STAGE 1: the assembled order-3 Euler-Maclaurin ζ identity.

    The de-risked plumbing the em-tail agent handed off (see EMZetaTail.lean header, Part J and the
    "REMAINING for the full ζ-order-K identity" note).  Ties `em_saw_step_window` (the proven,
    analyticity-free IBP order-raiser) to `riemannZeta` by raising the K=1 remainder
    `∫_1^∞ saw₁·(−s·x^{−s−1})` of `EMZetaComplex.em_zeta_strip` to order 3 over the tail `[N,∞)`.

    THE ASSEMBLED IDENTITY (`em_zeta_strip_3`):  for `0 < Re s`, `s ≠ 1`, `N ≥ 1`,
        riemannZeta s
          = (∑_{n∈Ico 1 N} n^{-s})              -- the finite Dirichlet head
            + (N:ℂ)^(1-s)/(s-1)                 -- the ∫_1^N x^{-s} closed form (integral_cpow)
            + (N:ℂ)^(-s)/2                       -- the trapezoid endpoint
            + (1/12)·s·(N:ℂ)^(-s-1)              -- the B₂/2! · f'(N) correction (B₂ = 1/6)
            + emZetaR3 s N,                       -- the order-3 remainder = (1/6)·∫_N^∞ saw₃·c₃·x^{-s-3}
    with `‖emZetaR3 s N‖ ≤ (1/6)·(1/12)·‖s(s+1)(s+2)‖·N^{-(Re s+2)}/(Re s+2)` (from `em_tail3_bound`).

    Route (all real-saw IBP + one M→∞ limit; NO new analyticity — the analyticity was spent once in
    `em_zeta_strip`):
      1.  Split `∫_1^∞ saw₁·f₁ = ∫_1^N saw₁·f₁ + ∫_N^∞ saw₁·f₁`, with `f₁ x = −s·x^{−s−1}`.
      2.  `∫_1^N saw₁·f₁` → finite sum via `em_cpow_partial` (already proven) + `integral_cpow` head.
      3.  `∫_N^∞ saw₁·f₁`: raise order 1→2→3 over `[N,M]` by two `em_saw_step_window`, then `M→∞`.
          The order-2 boundary term carries `B₂(0)=1/6`; the order-3 boundary term carries
          `B₃(0)=bernoulli 3 = 0` and VANISHES.  Net: `∫_N^∞ saw₁·f₁ = (1/12)·s·N^{-s-1} + (1/6)·tail₃`.

    conjecture1_proved = False.  Classical Euler-Maclaurin; NOT a proof of RH.
-/
import EMZetaTail

open MeasureTheory intervalIntegral Set Filter Topology Complex
open scoped Real

namespace ZetaReflection

/-! ## Notation for the σ-direction derivative tower of `x^{-s}`.

    `f₁ x = −s·x^{−s−1}` (the 1st `x`-derivative of `x^{-s}`), `f₂ x = s(s+1)·x^{−s−2}` (2nd),
    `f₃ x = −s(s+1)(s+2)·x^{−s−3} = emTailCoeff3 s · x^{-s-3}` (3rd). -/

/-- The 1st derivative coefficient function `f₁ x = −s·x^{−s−1}`. -/
noncomputable def emF1 (s : ℂ) (x : ℝ) : ℂ := -s * (x : ℂ) ^ (-s - 1)

/-- The 2nd derivative coefficient function `f₂ x = s(s+1)·x^{−s−2}`. -/
noncomputable def emF2 (s : ℂ) (x : ℝ) : ℂ := s * (s + 1) * (x : ℂ) ^ (-s - 2)

/-- The 3rd derivative coefficient function `f₃ x = emTailCoeff3 s · x^{−s−3}`. -/
noncomputable def emF3 (s : ℂ) (x : ℝ) : ℂ := emTailCoeff3 s * (x : ℂ) ^ (-s - 3)

/-- `f₁` has derivative `f₂` on the positive reals (`s ≠ -1`). -/
theorem emF1_hasDerivAt {s : ℂ} (hs : s ≠ -1) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (emF1 s) (emF2 s x) x := by
  have h := hasDerivAt_cpow_neg2 hs hx
  unfold emF1 emF2
  exact h

/-- `f₂` has derivative `f₃` on the positive reals (`s ≠ -2`). -/
theorem emF2_hasDerivAt {s : ℂ} (hs : s ≠ -2) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (emF2 s) (emF3 s x) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hr : (-s - 2 : ℂ) ≠ 0 := by
    intro h; apply hs; linear_combination -h
  have hstep : HasDerivAt (fun x : ℝ => (x : ℂ) ^ (-s - 2))
      ((-s - 2) * (x : ℂ) ^ (-s - 2 - 1)) x := hasDerivAt_ofReal_cpow_const hx0 hr
  have hfull := hstep.const_mul (s * (s + 1))
  have hval : (s * (s + 1)) * ((-s - 2) * (x : ℂ) ^ (-s - 2 - 1))
      = emTailCoeff3 s * (x : ℂ) ^ (-s - 3) := by
    rw [emTailCoeff3, show (-s - 2 - 1 : ℂ) = -s - 3 by ring]; ring
  rw [hval] at hfull
  unfold emF2 emF3
  exact hfull

/-! ## Integrability of the saw-weighted power tails on `(N, ∞)`.

    For `Re s + k > 1` the integrand `saw_k x · (c · x^{−s−k})` is integrable on `(N,∞)`: its norm is
    `≤ B·‖c‖·x^{−(Re s+k)}` with `−(Re s+k) < −1`.  This is the domination used inside
    `em_tail_integral_bound`; we isolate it as a standalone integrability fact (the M→∞ limits need
    it, and the window lemma's per-cell integrability follows by restriction). -/

/-- The saw-weighted power integrand `saw_k · (c·x^{−s−k})` is integrable on `(a, ∞)` for `a ≥ 1`,
    `Re s + k > 1`, given a real sup bound `B` on `saw_k`. -/
theorem saw_pow_integrableOn_Ioi {k : ℕ} {s c : ℂ} {B : ℝ} {a : ℝ}
    (ha : 1 ≤ a) (hexp : 1 < s.re + k) (hsawB : ∀ x : ℝ, |sawBernoulli k x| ≤ B) :
    IntegrableOn (fun x : ℝ => (sawBernoulli k x : ℂ) * (c * (x : ℂ) ^ (-s - k))) (Ioi a) := by
  have hapos : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  have hexplt : -(s.re + (k : ℝ)) < -1 := by linarith
  have hdom : IntegrableOn (fun x : ℝ => (B * ‖c‖) * x ^ (-(s.re + (k : ℝ)))) (Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (a := -(s.re + (k : ℝ))) hexplt hapos).const_mul _
  refine Integrable.mono' hdom ?_ ?_
  · apply Measurable.aestronglyMeasurable
    exact (Complex.measurable_ofReal.comp (sawBernoulli_measurable k)).mul
      (measurable_const.mul (Complex.measurable_ofReal.pow_const _))
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    have hxpos : (0 : ℝ) < x := lt_trans hapos hx
    have hnormcpow : ‖(x : ℂ) ^ (-s - k)‖ = x ^ (-(s.re + (k : ℝ))) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
      congr 1
      rw [Complex.sub_re, Complex.neg_re, Complex.natCast_re]; ring
    have hrpownn : (0 : ℝ) ≤ x ^ (-(s.re + (k : ℝ))) := Real.rpow_nonneg hxpos.le _
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hnormcpow]
    calc |sawBernoulli k x| * (‖c‖ * x ^ (-(s.re + (k : ℝ))))
        ≤ B * (‖c‖ * x ^ (-(s.re + (k : ℝ)))) := by gcongr; exact hsawB x
      _ = (B * ‖c‖) * x ^ (-(s.re + (k : ℝ))) := by ring

/-- The `k = 2` tail integrand `saw₂ · f₂ = saw₂ · (s(s+1)·x^{−s−2})` is integrable on `(a,∞)`,
    `a ≥ 1`, `Re s > -1` (in particular `Re s > 0`). -/
theorem emF2_integrableOn_Ioi {s : ℂ} {a : ℝ} (ha : 1 ≤ a) (hs : -1 < s.re) :
    IntegrableOn (fun x : ℝ => (sawBernoulli 2 x : ℂ) * emF2 s x) (Ioi a) := by
  have hexp : (1 : ℝ) < s.re + ((2 : ℕ) : ℝ) := by push_cast; linarith
  have h := saw_pow_integrableOn_Ioi (k := 2) (s := s) (c := s * (s + 1)) (B := 1 / 6)
    (a := a) ha hexp (fun x => abs_sawBernoulli_two_le x)
  refine h.congr_fun ?_ measurableSet_Ioi
  intro x _; simp only [emF2]; norm_num

/-- The `k = 3` tail integrand `saw₃ · f₃ = saw₃ · (emTailCoeff3 s·x^{−s−3})` is integrable on
    `(a,∞)`, `a ≥ 1`, `Re s > -2` (in particular `Re s > 0`). -/
theorem emF3_integrableOn_Ioi {s : ℂ} {a : ℝ} (ha : 1 ≤ a) (hs : -2 < s.re) :
    IntegrableOn (fun x : ℝ => (sawBernoulli 3 x : ℂ) * emF3 s x) (Ioi a) := by
  have hexp : (1 : ℝ) < s.re + ((3 : ℕ) : ℝ) := by push_cast; linarith
  have h := saw_pow_integrableOn_Ioi (k := 3) (s := s) (c := emTailCoeff3 s) (B := 1 / 12)
    (a := a) ha hexp (fun x => abs_sawBernoulli_three_le x)
  refine h.congr_fun ?_ measurableSet_Ioi
  intro x _; simp only [emF3]; norm_num

/-- The `k = 1` tail integrand `saw₁ · f₁ = saw₁ · (−s·x^{−s−1})` is integrable on `(a,∞)`,
    `a ≥ 1`, `Re s > 0`. -/
theorem emF1_integrableOn_Ioi {s : ℂ} {a : ℝ} (ha : 1 ≤ a) (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (sawBernoulli 1 x : ℂ) * emF1 s x) (Ioi a) := by
  have hexp : (1 : ℝ) < s.re + ((1 : ℕ) : ℝ) := by push_cast; linarith
  have h := saw_pow_integrableOn_Ioi (k := 1) (s := s) (c := -s) (B := 1 / 2)
    (a := a) ha hexp (fun x => abs_sawBernoulli_one_le x)
  refine h.congr_fun ?_ measurableSet_Ioi
  intro x _; simp only [emF1]; norm_num

/-! ## Per-cell interval integrability of the coefficient functions (window lemma inputs). -/

/-- `emF2 s` is interval-integrable on any `[b, b+1]` with `b ≥ 1` (continuous there). -/
theorem emF2_intervalIntegrable {s : ℂ} {b : ℝ} (hb : 1 ≤ b) :
    IntervalIntegrable (emF2 s) volume b (b + 1) := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by linarith)]
  apply ContinuousOn.mul continuousOn_const
  apply ContinuousOn.cpow_const Complex.continuous_ofReal.continuousOn
  intro x hx
  exact Or.inl (by simp only [Complex.ofReal_re]; linarith [hx.1])

/-- `emF3 s` is interval-integrable on any `[b, b+1]` with `b ≥ 1` (continuous there). -/
theorem emF3_intervalIntegrable {s : ℂ} {b : ℝ} (hb : 1 ≤ b) :
    IntervalIntegrable (emF3 s) volume b (b + 1) := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by linarith)]
  apply ContinuousOn.mul continuousOn_const
  apply ContinuousOn.cpow_const Complex.continuous_ofReal.continuousOn
  intro x hx
  exact Or.inl (by simp only [Complex.ofReal_re]; linarith [hx.1])

/-! ## The ℂ-valued saw-order-raising IBP step and its windowed sum.

    `em_saw_step` / `em_saw_step_window` in `EMZetaTail.lean` are stated for real `fk : ℝ → ℝ`.  Our
    coefficient functions `emF1/2/3` are ℂ-valued, so we re-derive the two identities with ℂ codomain
    (the saw itself stays real, cast to ℂ where multiplied).  The proofs mirror the real ones exactly:
    `integral_deriv_mul_eq_sub` (IBP) is codomain-generic; only the real `sawSurrogate W` is cast. -/

/-- The real saw antiderivative surrogate `W y = bernoulliFun (k+1)(y−m)/(k+1)`, cast to ℂ, with
    derivative `(bernoulliFun k (y−m) : ℂ)`.  (ℂ-lift of `sawSurrogate_hasDerivAt`.) -/
private lemma sawSurrogateC_hasDerivAt (k : ℕ) (m : ℤ) (y : ℝ) :
    HasDerivAt (fun z : ℝ => ((bernoulliFun (k + 1) (z - m) / (k + 1) : ℝ) : ℂ))
      ((bernoulliFun k (y - m) : ℝ) : ℂ) y := by
  have hshift : HasDerivAt (fun z : ℝ => z - (m : ℝ)) 1 y := by
    simpa using (hasDerivAt_id y).sub_const (m : ℝ)
  have hanti := antideriv_bernoulliFun k (y - m)
  have hcomp := hanti.comp y hshift
  rw [mul_one] at hcomp
  -- real HasDerivAt, then push through ofReal
  have hreal : HasDerivAt (fun z : ℝ => bernoulliFun (k + 1) (z - m) / (k + 1))
      (bernoulliFun k (y - m)) y := by
    have hfun : ((fun z => bernoulliFun (k + 1) z / (↑k + 1)) ∘ (fun z : ℝ => z - (m : ℝ)))
        = (fun z : ℝ => bernoulliFun (k + 1) (z - m) / (k + 1)) := by
      funext z; simp [Function.comp]
    rw [hfun] at hcomp; exact hcomp
  exact hreal.ofReal_comp

/-- **The ℂ-valued saw-order-raising IBP step** over a unit cell `[m, m+1]`. -/
theorem em_saw_step_cpow (k : ℕ) (m : ℤ) (fk fk1 : ℝ → ℂ)
    (hd : ∀ x ∈ Icc (m : ℝ) (m + 1), HasDerivAt fk (fk1 x) x)
    (hi : IntervalIntegrable fk1 volume (m : ℝ) (m + 1)) :
    (∫ x in (m : ℝ)..(m + 1), (sawBernoulli k x : ℂ) * fk x)
      = ((bernoulliFun (k + 1) 1 : ℂ) * fk (m + 1) - (bernoulliFun (k + 1) 0 : ℂ) * fk m) / (k + 1)
        - (∫ x in (m : ℝ)..(m + 1), (sawBernoulli (k + 1) x : ℂ) * fk1 x) / (k + 1) := by
  have hcc : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
  set W : ℝ → ℂ := fun z => ((bernoulliFun (k + 1) (z - m) / (k + 1) : ℝ) : ℂ) with hWdef
  have hW' : ∀ x, HasDerivAt W ((bernoulliFun k (x - m) : ℝ) : ℂ) x :=
    fun x => sawSurrogateC_hasDerivAt k m x
  have hWcont : Continuous W := by
    rw [hWdef]; fun_prop
  have huv : ∀ x ∈ uIcc (m : ℝ) (m + 1), HasDerivAt W ((bernoulliFun k (x - m) : ℝ) : ℂ) x :=
    fun x _ => hW' x
  have hfd : ∀ x ∈ uIcc (m : ℝ) (m + 1), HasDerivAt fk (fk1 x) x := by
    intro x hx; rw [uIcc_of_le hcc] at hx; exact hd x hx
  have hW'int : IntervalIntegrable (fun x => ((bernoulliFun k (x - m) : ℝ) : ℂ)) volume
      (m : ℝ) (m + 1) := by apply Continuous.intervalIntegrable; fun_prop
  have hIBP := integral_deriv_mul_eq_sub huv hfd hW'int hi
  have hWL : W (m : ℝ) = ((bernoulliFun (k + 1) 0 : ℝ) : ℂ) / (k + 1) := by
    simp [hWdef]
  have hWR : W ((m : ℝ) + 1) = ((bernoulliFun (k + 1) 1 : ℝ) : ℂ) / (k + 1) := by
    simp only [hWdef, add_sub_cancel_left]; push_cast; ring
  have hWfk1int : IntervalIntegrable (fun x => W x * fk1 x) volume (m : ℝ) (m + 1) :=
    hi.continuousOn_mul hWcont.continuousOn
  have hW'fkint : IntervalIntegrable (fun x => ((bernoulliFun k (x - m) : ℝ) : ℂ) * fk x) volume
      (m : ℝ) (m + 1) := by
    have hfkcont : ContinuousOn fk (uIcc (m : ℝ) (m + 1)) := fun x hx =>
      (hfd x hx).continuousAt.continuousWithinAt
    exact (hfkcont.intervalIntegrable).continuousOn_mul (by fun_prop)
  have hsplit :
      (∫ x in (m : ℝ)..(m + 1), ((bernoulliFun k (x - m) : ℝ) : ℂ) * fk x + W x * fk1 x)
        = (∫ x in (m : ℝ)..(m + 1), ((bernoulliFun k (x - m) : ℝ) : ℂ) * fk x)
          + ∫ x in (m : ℝ)..(m + 1), W x * fk1 x := by
    rw [intervalIntegral.integral_add hW'fkint hWfk1int]
  have hsaw_k : (∫ x in (m : ℝ)..(m + 1), (sawBernoulli k x : ℂ) * fk x)
      = ∫ x in (m : ℝ)..(m + 1), ((bernoulliFun k (x - m) : ℝ) : ℂ) * fk x := by
    apply intervalIntegral.integral_congr_ae
    have hnull : ∀ᵐ x, x ≠ ((m : ℝ) + 1) := MeasureTheory.Measure.ae_ne _ _
    filter_upwards [hnull] with x hxne hxmem
    rw [uIoc_of_le hcc] at hxmem
    have hxIco : x ∈ Ico (m : ℝ) (m + 1) := ⟨le_of_lt hxmem.1, lt_of_le_of_ne hxmem.2 hxne⟩
    rw [sawBernoulli_eq_on_Ico k hxIco]
  have hsaw_k1 : (∫ x in (m : ℝ)..(m + 1), (sawBernoulli (k + 1) x : ℂ) * fk1 x)
      = ∫ x in (m : ℝ)..(m + 1), (((k : ℂ) + 1) * W x) * fk1 x := by
    apply intervalIntegral.integral_congr_ae
    have hnull : ∀ᵐ x, x ≠ ((m : ℝ) + 1) := MeasureTheory.Measure.ae_ne _ _
    filter_upwards [hnull] with x hxne hxmem
    rw [uIoc_of_le hcc] at hxmem
    have hxIco : x ∈ Ico (m : ℝ) (m + 1) := ⟨le_of_lt hxmem.1, lt_of_le_of_ne hxmem.2 hxne⟩
    have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    rw [sawBernoulli_eq_on_Ico (k + 1) hxIco, hWdef]
    push_cast
    field_simp
  rw [hsaw_k]
  have key : (∫ x in (m : ℝ)..(m + 1), ((bernoulliFun k (x - m) : ℝ) : ℂ) * fk x)
      + ∫ x in (m : ℝ)..(m + 1), W x * fk1 x
      = W ((m : ℝ) + 1) * fk ((m : ℝ) + 1) - W (m : ℝ) * fk (m : ℝ) := by
    rw [← hsplit]; exact hIBP
  rw [hWL, hWR] at key
  have hk1 : ((k : ℂ) + 1) ≠ 0 := by
    have : ((k : ℝ) + 1) ≠ 0 := by positivity
    exact_mod_cast this
  rw [hsaw_k1]
  have hpull : (∫ x in (m : ℝ)..(m + 1), (((k : ℂ) + 1) * W x) * fk1 x)
      = ((k : ℂ) + 1) * ∫ x in (m : ℝ)..(m + 1), W x * fk1 x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _; ring
  rw [hpull]
  have hcancel : (((k : ℂ) + 1) * ∫ x in (m : ℝ)..(m + 1), W x * fk1 x) / ((k : ℂ) + 1)
      = ∫ x in (m : ℝ)..(m + 1), W x * fk1 x := by
    rw [mul_comm]; exact mul_div_cancel_right₀ _ hk1
  rw [hcancel]
  -- Reconcile the boundary term division: key uses (B/(k+1))*fk, goal uses (B*fk)/(k+1).
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← sub_div] at key
  linear_combination key

/-- Telescoping sum of first differences of a ℂ-valued function evaluated at ℕ casts. -/
private lemma sum_telescope_diff_cpow (g : ℝ → ℂ) {M N : ℕ} (hMN : M ≤ N) :
    (∑ j ∈ Finset.Ico M N, (g ((j : ℝ) + 1) - g (j : ℝ))) = g (N : ℝ) - g (M : ℝ) := by
  induction N, hMN using Nat.le_induction with
  | base => simp
  | succ p hp ih => rw [Finset.sum_Ico_succ_top hp, ih]; push_cast; ring

/-- **The ℂ-valued summed saw-order-raising over `[M, N]`** (ℂ-lift of `em_saw_step_window`).
    For `k ≥ 1`, the interior boundary terms telescope (`B_{k+1}(0) = B_{k+1}(1)`), leaving
        ∫_M^N saw_k·fk = B_{k+1}(0)·(fk N − fk M)/(k+1) − (∫_M^N saw_{k+1}·fk1)/(k+1). -/
theorem em_saw_step_window_cpow {k : ℕ} (hk : 1 ≤ k) (M N : ℕ) (hMN : M ≤ N) (fk fk1 : ℝ → ℂ)
    (hd : ∀ x ∈ Icc (M : ℝ) N, HasDerivAt fk (fk1 x) x)
    (hi : ∀ j ∈ Finset.Ico M N, IntervalIntegrable fk1 volume (j : ℝ) (j + 1)) :
    (∫ x in (M : ℝ)..N, (sawBernoulli k x : ℂ) * fk x)
      = (bernoulliFun (k + 1) 0 : ℂ) * (fk N - fk M) / (k + 1)
        - (∫ x in (M : ℝ)..N, (sawBernoulli (k + 1) x : ℂ) * fk1 x) / (k + 1) := by
  have hk1ne : k + 1 ≠ 1 := by omega
  have hendeq : (bernoulliFun (k + 1) 1 : ℝ) = (bernoulliFun (k + 1) 0 : ℝ) :=
    bernoulliFun_endpoints_eq_of_ne_one hk1ne
  have hcell : ∀ j ∈ Finset.Ico M N, ∀ x ∈ Icc (j : ℝ) (j + 1), HasDerivAt fk (fk1 x) x := by
    intro j hj x hx
    rw [Finset.mem_Ico] at hj
    refine hd x ⟨le_trans (by exact_mod_cast hj.1) hx.1, ?_⟩
    have : (j : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hj.2
    linarith [hx.2]
  have hstep : ∀ j ∈ Finset.Ico M N,
      (∫ x in (j : ℝ)..(j + 1), (sawBernoulli k x : ℂ) * fk x)
        = ((bernoulliFun (k + 1) 1 : ℂ) * fk (j + 1) - (bernoulliFun (k + 1) 0 : ℂ) * fk j) / (k + 1)
          - (∫ x in (j : ℝ)..(j + 1), (sawBernoulli (k + 1) x : ℂ) * fk1 x) / (k + 1) := by
    intro j hj
    have hcast : (((j : ℤ)) : ℝ) = (j : ℝ) := by push_cast; ring
    have := em_saw_step_cpow k (j : ℤ) fk fk1
      (by intro x hx; rw [hcast] at hx; exact hcell j hj x hx)
      (by rw [hcast]; exact hi j hj)
    simpa [hcast] using this
  have hsum := Finset.sum_congr rfl hstep
  -- per-cell integrability of the two integrands.
  have hint_k : ∀ j ∈ Finset.Ico M N,
      IntervalIntegrable (fun x => (sawBernoulli k x : ℂ) * fk x) volume (j : ℝ) (j + 1) := by
    intro j hj
    have hcc : (j : ℝ) ≤ (j : ℝ) + 1 := by linarith
    have hfkcont : ContinuousOn fk (Icc (j : ℝ) (j + 1)) :=
      fun x hx => (hcell j hj x hx).continuousAt.continuousWithinAt
    have hcont : IntervalIntegrable (fun x => ((bernoulliFun k (x - j) : ℝ) : ℂ) * fk x) volume
        (j : ℝ) (j + 1) := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hcc]
      exact (Continuous.continuousOn (by fun_prop)).mul hfkcont
    refine (intervalIntegrable_congr_ae ?_).mpr hcont
    have hnull : ∀ᵐ x, x ≠ ((j : ℝ) + 1) := MeasureTheory.Measure.ae_ne _ _
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hnull] with x hxne hxmem
    rw [uIoc_of_le hcc] at hxmem
    have hxIco : x ∈ Ico ((j : ℤ) : ℝ) (((j : ℤ) : ℝ) + 1) := by
      refine ⟨?_, ?_⟩
      · have : (j : ℝ) < x := hxmem.1; push_cast; linarith
      · have hlt : x < (j : ℝ) + 1 := lt_of_le_of_ne hxmem.2 hxne; push_cast; linarith
    rw [sawBernoulli_eq_on_Ico k hxIco]; norm_num
  have htel_k : (∑ j ∈ Finset.Ico M N, ∫ x in (j : ℝ)..(j + 1), (sawBernoulli k x : ℂ) * fk x)
      = ∫ x in (M : ℝ)..N, (sawBernoulli k x : ℂ) * fk x := by
    have hint : ∀ j ∈ Set.Ico M N,
        IntervalIntegrable (fun x => (sawBernoulli k x : ℂ) * fk x) volume
          ((fun j : ℕ => (j : ℝ)) j) ((fun j : ℕ => (j : ℝ)) (j + 1)) := by
      intro j hj; simpa [Nat.cast_succ] using hint_k j (Finset.mem_Ico.mpr hj)
    have := intervalIntegral.sum_integral_adjacent_intervals_Ico
      (a := fun j : ℕ => (j : ℝ)) (f := fun x => (sawBernoulli k x : ℂ) * fk x) (μ := volume) hMN hint
    simpa using this
  have hint_k1 : ∀ j ∈ Finset.Ico M N,
      IntervalIntegrable (fun x => (sawBernoulli (k + 1) x : ℂ) * fk1 x) volume (j : ℝ) (j + 1) := by
    intro j hj
    have hcc : (j : ℝ) ≤ (j : ℝ) + 1 := by linarith
    have hcont : IntervalIntegrable (fun x => ((bernoulliFun (k + 1) (x - j) : ℝ) : ℂ) * fk1 x) volume
        (j : ℝ) (j + 1) := (hi j hj).continuousOn_mul (by fun_prop)
    refine (intervalIntegrable_congr_ae ?_).mpr hcont
    have hnull : ∀ᵐ x, x ≠ ((j : ℝ) + 1) := MeasureTheory.Measure.ae_ne _ _
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hnull] with x hxne hxmem
    rw [uIoc_of_le hcc] at hxmem
    have hxIco : x ∈ Ico ((j : ℤ) : ℝ) (((j : ℤ) : ℝ) + 1) := by
      refine ⟨?_, ?_⟩
      · have : (j : ℝ) < x := hxmem.1; push_cast; linarith
      · have hlt : x < (j : ℝ) + 1 := lt_of_le_of_ne hxmem.2 hxne; push_cast; linarith
    rw [sawBernoulli_eq_on_Ico (k + 1) hxIco]; norm_num
  have htel_k1 : (∑ j ∈ Finset.Ico M N, ∫ x in (j : ℝ)..(j + 1), (sawBernoulli (k + 1) x : ℂ) * fk1 x)
      = ∫ x in (M : ℝ)..N, (sawBernoulli (k + 1) x : ℂ) * fk1 x := by
    have hint : ∀ j ∈ Set.Ico M N,
        IntervalIntegrable (fun x => (sawBernoulli (k + 1) x : ℂ) * fk1 x) volume
          ((fun j : ℕ => (j : ℝ)) j) ((fun j : ℕ => (j : ℝ)) (j + 1)) := by
      intro j hj; simpa [Nat.cast_succ] using hint_k1 j (Finset.mem_Ico.mpr hj)
    have := intervalIntegral.sum_integral_adjacent_intervals_Ico
      (a := fun j : ℕ => (j : ℝ)) (f := fun x => (sawBernoulli (k + 1) x : ℂ) * fk1 x) (μ := volume) hMN hint
    simpa using this
  have hbdry : (∑ j ∈ Finset.Ico M N,
        ((bernoulliFun (k + 1) 1 : ℂ) * fk (j + 1) - (bernoulliFun (k + 1) 0 : ℂ) * fk j)) / (k + 1)
      = (bernoulliFun (k + 1) 0 : ℂ) * (fk N - fk M) / (k + 1) := by
    congr 1
    have hendeqC : ((bernoulliFun (k + 1) 1 : ℝ) : ℂ) = ((bernoulliFun (k + 1) 0 : ℝ) : ℂ) := by
      exact_mod_cast hendeq
    rw [hendeqC]
    have : (∑ j ∈ Finset.Ico M N,
        ((bernoulliFun (k + 1) 0 : ℂ) * fk (j + 1) - (bernoulliFun (k + 1) 0 : ℂ) * fk j))
        = (∑ j ∈ Finset.Ico M N,
            (bernoulliFun (k + 1) 0 : ℂ) * (fk ((j : ℝ) + 1) - fk (j : ℝ))) := by
      apply Finset.sum_congr rfl; intro j _; push_cast; ring
    rw [this, ← Finset.mul_sum, sum_telescope_diff_cpow fk hMN]
  rw [Finset.sum_sub_distrib] at hsum
  rw [← Finset.sum_div, ← Finset.sum_div, htel_k1, htel_k, hbdry] at hsum
  exact hsum

/-! ## The finite `[N, M]` order-1 → order-3 raise.

    Two `em_saw_step_window_cpow` applications.  `B₂(0) = 1/6`, `B₃(0) = 0` (so the order-3 boundary
    vanishes).  Net:  `∫_N^M saw₁·f₁ = (1/12)·(f₁ M − f₁ N) + (1/6)·∫_N^M saw₃·f₃`. -/

/-- `bernoulliFun 2 0 = 1/6` as a ℂ literal. -/
private lemma bernoulliFunC_two_zero : ((bernoulliFun 2 0 : ℝ) : ℂ) = 1 / 6 := by
  rw [bernoulliFun_two]; push_cast; norm_num

/-- `bernoulliFun 3 0 = 0` as a ℂ literal (`bernoulli 3 = 0`). -/
private lemma bernoulliFunC_three_zero : ((bernoulliFun 3 0 : ℝ) : ℂ) = 0 := by
  rw [bernoulliFun_eval_zero, bernoulli_eq_zero_of_odd (by decide) (by norm_num)]
  simp

/-- **The finite windowed order-3 raise** over `[N, M]` (`1 ≤ N ≤ M`, `Re s > 0`, `s ∉ {−1, −2}`).
        ∫_N^M saw₁·f₁ = (1/12)·(f₁ M − f₁ N) + (1/6)·∫_N^M saw₃·f₃. -/
theorem emTail_finite_raise3 {s : ℂ} (hs1 : s ≠ -1) (hs2 : s ≠ -2)
    {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    (∫ x in (N : ℝ)..M, (sawBernoulli 1 x : ℂ) * emF1 s x)
      = (1 / 12) * (emF1 s M - emF1 s N)
        + (1 / 6) * ∫ x in (N : ℝ)..M, (sawBernoulli 3 x : ℂ) * emF3 s x := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  -- derivative availability on [N, M]
  have hd1 : ∀ x ∈ Icc (N : ℝ) M, HasDerivAt (emF1 s) (emF2 s x) x := by
    intro x hx; exact emF1_hasDerivAt hs1 (lt_of_lt_of_le zero_lt_one (le_trans hNR hx.1))
  have hd2 : ∀ x ∈ Icc (N : ℝ) M, HasDerivAt (emF2 s) (emF3 s x) x := by
    intro x hx; exact emF2_hasDerivAt hs2 (lt_of_lt_of_le zero_lt_one (le_trans hNR hx.1))
  have hi1 : ∀ j ∈ Finset.Ico N M, IntervalIntegrable (emF2 s) volume (j : ℝ) (j + 1) := by
    intro j hj; rw [Finset.mem_Ico] at hj
    exact emF2_intervalIntegrable (le_trans hNR (by exact_mod_cast hj.1))
  have hi2 : ∀ j ∈ Finset.Ico N M, IntervalIntegrable (emF3 s) volume (j : ℝ) (j + 1) := by
    intro j hj; rw [Finset.mem_Ico] at hj
    exact emF3_intervalIntegrable (le_trans hNR (by exact_mod_cast hj.1))
  -- Step 1 (k = 1): raise saw₁·f₁ using derivative f₂.
  have hstep1 := em_saw_step_window_cpow (k := 1) le_rfl N M hNM (emF1 s) (emF2 s) hd1 hi1
  -- Step 2 (k = 2): raise saw₂·f₂ using derivative f₃.
  have hstep2 := em_saw_step_window_cpow (k := 2) (by norm_num) N M hNM (emF2 s) (emF3 s) hd2 hi2
  -- Simplify the Bernoulli constants.
  rw [show (1 : ℕ) + 1 = 2 from rfl, bernoulliFunC_two_zero] at hstep1
  rw [show (2 : ℕ) + 1 = 3 from rfl, bernoulliFunC_three_zero] at hstep2
  -- hstep2:  ∫saw₂·f₂ = 0·(…)/3 − (∫saw₃·f₃)/3  =  −(∫saw₃·f₃)/3.
  rw [zero_mul, zero_div, zero_sub] at hstep2
  -- Substitute into hstep1 and normalise the scalars.
  rw [hstep1, hstep2]
  push_cast
  ring

/-! ## The `M → ∞` limit: the tail order-3 identity on `[N, ∞)`.

    Take `M → ∞` in `emTail_finite_raise3`.  The finite integrals converge to their `Ioi`
    counterparts (`intervalIntegral_tendsto_integral_Ioi` + the integrability lemmas), and the
    boundary term `(1/12)·f₁ M → 0` (`‖f₁ M‖ = ‖s‖·M^{−Re s−1} → 0`).  Net:
        ∫_N^∞ saw₁·f₁ = (1/12)·s·N^{−s−1} + (1/6)·∫_N^∞ saw₃·f₃. -/

/-- `emF1 s M → 0` along `M : ℕ → ∞` (for `Re s > 0`): its norm is `‖s‖·M^{−Re s−1}`. -/
private lemma emF1_tendsto_zero {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun M : ℕ => emF1 s (M : ℝ)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hnorm : (fun M : ℕ => ‖emF1 s (M : ℝ)‖)
      =ᶠ[atTop] (fun M : ℕ => ‖s‖ * (M : ℝ) ^ (-(s.re + 1))) := by
    filter_upwards [eventually_gt_atTop 0] with M hM
    have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    rw [emF1, norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hMpos]
    congr 1
    rw [Complex.sub_re, Complex.neg_re, Complex.one_re]; ring
  refine Tendsto.congr' hnorm.symm ?_
  have hlim : Tendsto (fun M : ℕ => (M : ℝ) ^ (-(s.re + 1))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (y := s.re + 1) (by linarith)).comp tendsto_natCast_atTop_atTop
  simpa using hlim.const_mul ‖s‖

/-- **The tail order-3 identity on `[N, ∞)`** (`N ≥ 1`, `Re s > 0`, `s ∉ {−1,−2}`):
        ∫_N^∞ saw₁·f₁ = (1/12)·s·(N:ℂ)^{−s−1} + (1/6)·∫_N^∞ saw₃·f₃. -/
theorem emTail_raise3 {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ -1) (hs2 : s ≠ -2)
    {N : ℕ} (hN : 1 ≤ N) :
    (∫ x in Ioi (N : ℝ), (sawBernoulli 1 x : ℂ) * emF1 s x)
      = (1 / 12) * s * (N : ℂ) ^ (-s - 1)
        + (1 / 6) * ∫ x in Ioi (N : ℝ), (sawBernoulli 3 x : ℂ) * emF3 s x := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hint1 : IntegrableOn (fun x : ℝ => (sawBernoulli 1 x : ℂ) * emF1 s x) (Ioi (N : ℝ)) :=
    emF1_integrableOn_Ioi hNR hs
  have hint3 : IntegrableOn (fun x : ℝ => (sawBernoulli 3 x : ℂ) * emF3 s x) (Ioi (N : ℝ)) :=
    emF3_integrableOn_Ioi hNR (by linarith)
  -- LHS finite → improper.
  have hLHS : Tendsto (fun M : ℕ => ∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli 1 x : ℂ) * emF1 s x)
      atTop (𝓝 (∫ x in Ioi (N : ℝ), (sawBernoulli 1 x : ℂ) * emF1 s x)) :=
    intervalIntegral_tendsto_integral_Ioi (N : ℝ) hint1 tendsto_natCast_atTop_atTop
  -- RHS pieces.
  have hRHS3 : Tendsto (fun M : ℕ => ∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli 3 x : ℂ) * emF3 s x)
      atTop (𝓝 (∫ x in Ioi (N : ℝ), (sawBernoulli 3 x : ℂ) * emF3 s x)) :=
    intervalIntegral_tendsto_integral_Ioi (N : ℝ) hint3 tendsto_natCast_atTop_atTop
  have hBdry : Tendsto (fun M : ℕ => (1 / 12 : ℂ) * (emF1 s (M : ℝ) - emF1 s (N : ℝ)))
      atTop (𝓝 ((1 / 12 : ℂ) * (0 - emF1 s (N : ℝ)))) :=
    ((emF1_tendsto_zero hs).sub_const _).const_mul _
  -- Assemble the RHS limit.
  have hRHS : Tendsto (fun M : ℕ =>
      (1 / 12 : ℂ) * (emF1 s (M : ℝ) - emF1 s (N : ℝ))
        + (1 / 6) * ∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli 3 x : ℂ) * emF3 s x) atTop
      (𝓝 ((1 / 12 : ℂ) * (0 - emF1 s (N : ℝ))
          + (1 / 6) * ∫ x in Ioi (N : ℝ), (sawBernoulli 3 x : ℂ) * emF3 s x)) :=
    hBdry.add (hRHS3.const_mul _)
  -- The finite identity holds eventually (for M ≥ N).
  have hEq : ∀ᶠ M : ℕ in atTop, (∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli 1 x : ℂ) * emF1 s x)
      = (1 / 12 : ℂ) * (emF1 s (M : ℝ) - emF1 s (N : ℝ))
        + (1 / 6) * ∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli 3 x : ℂ) * emF3 s x := by
    filter_upwards [eventually_ge_atTop N] with M hM
    exact emTail_finite_raise3 hs1 hs2 hN hM
  have hLHS' := hLHS.congr' hEq
  have hlim := tendsto_nhds_unique hLHS' hRHS
  rw [hlim]
  -- (1/12)(0 − f₁ N) = (1/12)·s·N^{−s−1}.
  have hf1N : emF1 s (N : ℝ) = -s * (N : ℂ) ^ (-s - 1) := by
    rw [emF1]; push_cast; ring
  rw [hf1N]; ring

/-! ## Head integral closed form and the finite head identity. -/

/-- The head integral `∫_1^N x^{−s} = (N^{1−s} − 1)/(1−s)` (`integral_cpow`, `1 ≤ N`, `s ≠ 1`). -/
theorem integral_cpow_head {s : ℂ} (hs1 : s ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    (∫ x in (1 : ℝ)..(N : ℝ), (x : ℂ) ^ (-s)) = ((N : ℂ) ^ (1 - s) - 1) / (1 - s) := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h0notin : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (N : ℝ) := by
    rw [Set.uIcc_of_le hNR]; simp
  have hsne : (-s : ℂ) ≠ -1 := by
    intro h; apply hs1; linear_combination -h
  have hguard : (-1 : ℝ) < (-s : ℂ).re ∨ (-s : ℂ) ≠ -1 ∧ (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (N : ℝ) :=
    Or.inr ⟨hsne, h0notin⟩
  rw [integral_cpow hguard]
  have he : (-s + 1 : ℂ) = 1 - s := by ring
  rw [he]
  push_cast
  rw [Complex.one_cpow]

/-- **The finite head identity**: `∫_1^N saw₁·f₁ = Σ_{Ico 1 N} n^{-s} − (N^{1-s}−1)/(1-s)
    + (N^{-s}−1)/2` (from `em_cpow_partial` + `integral_cpow_head`, `1 ≤ N`, `s ≠ 1`). -/
theorem emHead_identity {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    (∫ x in (1 : ℝ)..(N : ℝ), (sawBernoulli 1 x : ℂ) * emF1 s x)
      = (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s))
        - ((N : ℂ) ^ (1 - s) - 1) / (1 - s)
        + (((N : ℝ) : ℂ) ^ (-s) - 1) / 2 := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  have hpart := em_cpow_partial (s := s) hs0 (N := N) hN
  have hhead := integral_cpow_head hs1 hN
  -- em_cpow_partial: Σ = ∫x^{-s} − (N^{-s}−1^{-s})/2 + ∫saw₁·(-s x^{-s-1})
  -- and the remainder integrand equals saw₁·emF1.
  have hcong : (∫ x in (1 : ℝ)..(N : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
      = ∫ x in (1 : ℝ)..(N : ℝ), (sawBernoulli 1 x : ℂ) * emF1 s x := by
    apply intervalIntegral.integral_congr; intro x _; simp only [emF1]
  rw [hcong] at hpart
  -- 1^{-s} = 1
  have h1s : ((1 : ℝ) : ℂ) ^ (-s) = 1 := by
    rw [Complex.ofReal_one, Complex.one_cpow]
  rw [h1s, hhead] at hpart
  -- solve for the saw integral.  Normalise casts (↑↑N vs ↑N) then linarith-style combine.
  have hden : (1 - s) ≠ 0 := by
    intro h; apply hs1; linear_combination -h
  push_cast at hpart ⊢
  linear_combination -hpart

/-! ## The improper-integral split `∫_{Ioi 1} = ∫_1^N + ∫_{Ioi N}`. -/

/-- `∫_{Ioi 1} saw₁·f₁ = ∫_1^N saw₁·f₁ + ∫_{Ioi N} saw₁·f₁` (disjoint union `Ioc 1 N ⊎ Ioi N`,
    `1 ≤ N`, `Re s > 0`). -/
theorem emTail_split {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    (∫ x in Ioi (1 : ℝ), (sawBernoulli 1 x : ℂ) * emF1 s x)
      = (∫ x in (1 : ℝ)..(N : ℝ), (sawBernoulli 1 x : ℂ) * emF1 s x)
        + ∫ x in Ioi (N : ℝ), (sawBernoulli 1 x : ℂ) * emF1 s x := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hint1 : IntegrableOn (fun x : ℝ => (sawBernoulli 1 x : ℂ) * emF1 s x) (Ioi (1 : ℝ)) :=
    emF1_integrableOn_Ioi le_rfl hs
  -- Ioi 1 = Ioc 1 N ∪ Ioi N (disjoint), so the set integral splits.
  have hsplit : (∫ x in Ioi (1 : ℝ), (sawBernoulli 1 x : ℂ) * emF1 s x)
      = (∫ x in Ioc (1 : ℝ) (N : ℝ), (sawBernoulli 1 x : ℂ) * emF1 s x)
        + ∫ x in Ioi (N : ℝ), (sawBernoulli 1 x : ℂ) * emF1 s x := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hNR]
    rw [setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hint1.mono_set (Set.Ioc_subset_Ioi_self))
      (hint1.mono_set (Set.Ioi_subset_Ioi hNR))]
  rw [hsplit]
  congr 1
  rw [intervalIntegral.integral_of_le hNR]

/-! ## STAGE 1 CAPSTONE: the assembled order-3 Euler-Maclaurin ζ identity. -/

/-- **The order-3 EM remainder** `R₃(s,N) = (1/6)·∫_N^∞ saw₃·(c₃(s)·x^{−s−3})`.  This is exactly
    `(1/6)` times the integral `em_tail3_bound` / `em_tail3_number` control. -/
noncomputable def emZetaR3 (s : ℂ) (N : ℕ) : ℂ :=
  (1 / 6) * ∫ x in Ioi (N : ℝ), (sawBernoulli 3 x : ℂ) * emF3 s x

/-- **THE ASSEMBLED IDENTITY (A2 Theorem 1, order 3).**  For every `s` with `0 < Re s`, `s ≠ 1`,
    `s ≠ -1`, `s ≠ -2` (the last two automatic on `Re s > 0`), and every `N ≥ 1`,
        riemannZeta s
          = (∑_{n∈Ico 1 N} n^{-s})
            + (N:ℂ)^(1−s)/(s−1)
            + (N:ℂ)^(−s)/2
            + (1/12)·s·(N:ℂ)^(−s−1)
            + emZetaR3 s N.
    The finite part is elementary (Dirichlet head + three explicit power terms) — directly boxable by
    the `DIntv` interval evaluator — and `emZetaR3 s N` is the kernel-bounded order-3 tail. -/
theorem em_zeta_strip_3 {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    riemannZeta s
      = (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s))
        + (N : ℂ) ^ (1 - s) / (s - 1)
        + ((N : ℝ) : ℂ) ^ (-s) / 2
        + (1 / 12) * s * (N : ℂ) ^ (-s - 1)
        + emZetaR3 s N := by
  have hsm1 : s ≠ -1 := by intro h; rw [h] at hs; simp at hs; linarith
  have hsm2 : s ≠ -2 := by intro h; rw [h] at hs; simp at hs; linarith
  have hden : (1 - s) ≠ 0 := by intro h; apply hs1; linear_combination -h
  have hden' : (s - 1) ≠ 0 := by intro h; apply hs1; linear_combination h
  -- Start from the K=1 strip identity; its remainder integrand matches saw₁·emF1.
  have hstrip := em_zeta_strip hs hs1
  have hcong : (∫ x in Ioi (1 : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
      = ∫ x in Ioi (1 : ℝ), (sawBernoulli 1 x : ℂ) * emF1 s x := by
    apply setIntegral_congr_fun measurableSet_Ioi; intro x _; simp only [emF1]
  rw [hcong] at hstrip
  -- Split the tail, expand the head, raise the far tail.
  rw [emTail_split hs hN, emHead_identity hs hs1 hN, emTail_raise3 hs hsm1 hsm2 hN] at hstrip
  rw [hstrip, emZetaR3]
  -- Algebra: collapse 1/(s-1) and 1/2 constants; (N^{1-s}−1)/(1-s) = N^{1-s}/(s-1) − 1/(s-1) etc.
  have hrw1 : ((N : ℂ) ^ (1 - s) - 1) / (1 - s) = -((N : ℂ) ^ (1 - s) / (s - 1)) + 1 / (s - 1) := by
    field_simp
    ring
  rw [hrw1]
  ring

/-- **The order-3 remainder envelope** (evaluator-facing): `‖emZetaR3 s N‖` decays like `N^{−Re s−2}`.
        ‖emZetaR3 s N‖ ≤ (1/6)·(1/12)·‖s(s+1)(s+2)‖·N^{−(Re s+2)}/(Re s+2).
    Immediate from `em_tail3_bound` (the `emF3` integrand is the `em_tail3_bound` integrand). -/
theorem emZetaR3_bound {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    ‖emZetaR3 s N‖
      ≤ (1 / 6) * ((1 / 12) * ‖s * (s + 1) * (s + 2)‖ * (N : ℝ) ^ (-(s.re + 3 - 1)) / (s.re + 3 - 1)) := by
  have hbnd := em_tail3_bound (s := s) (N := N) hN hs
  -- the emF3 integrand IS the em_tail3 integrand.
  have hcong : (∫ x in Ioi (N : ℝ), (sawBernoulli 3 x : ℂ) * emF3 s x)
      = ∫ x in Ioi (N : ℝ),
          (sawBernoulli 3 x : ℂ) * (emTailCoeff3 s * (x : ℂ) ^ (-s - 3)) := by
    apply setIntegral_congr_fun measurableSet_Ioi; intro x _; simp only [emF3]
  rw [emZetaR3, hcong, norm_mul]
  have h6 : ‖(1 / 6 : ℂ)‖ = 1 / 6 := by rw [Complex.norm_div]; simp
  rw [h6]
  gcongr

/-- **THE ORDER-3 NUMBER, lifted to `emZetaR3`** (the evaluator's sign-tight envelope at the pilot
    point).  At `s = 1/2 + 14i`, `N = 200`, `‖emZetaR3 s 200‖ ≤ (1/6)·(1/1000) < 2·10⁻⁴`. -/
theorem emZetaR3_number :
    ‖emZetaR3 ((1 / 2 : ℂ) + 14 * Complex.I) 200‖ ≤ (1 : ℝ) / 6000 := by
  have hnum := em_tail3_number
  have hcong : (∫ x in Ioi (200 : ℝ),
        (sawBernoulli 3 x : ℂ) * emF3 ((1 / 2 : ℂ) + 14 * Complex.I) x)
      = ∫ x in Ioi (200 : ℝ), (sawBernoulli 3 x : ℂ)
          * (emTailCoeff3 ((1 / 2 : ℂ) + 14 * Complex.I) * (x : ℂ) ^ (-((1 / 2 : ℂ) + 14 * Complex.I) - 3)) := by
    apply setIntegral_congr_fun measurableSet_Ioi; intro x _; simp only [emF3]
  rw [show (200 : ℕ) = 200 from rfl] at *
  rw [emZetaR3]
  norm_num only
  rw [hcong, norm_mul]
  have h6 : ‖(1 / 6 : ℂ)‖ = 1 / 6 := by rw [Complex.norm_div]; simp
  rw [h6]
  calc (1 / 6) * ‖_‖ ≤ (1 / 6) * (1 / 1000) := by gcongr
    _ = 1 / 6000 := by norm_num

end ZetaReflection
