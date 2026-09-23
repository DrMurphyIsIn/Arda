/-  EMZetaHigh.lean -- the GENERAL-ORDER Euler-Maclaurin representation of ζ with an explicit,
    PROVED remainder bound (lane emhigh, memo ANDURIL_ARB_DISCHARGE_2026-09-23 section 3 / step 2
    node `AND_em_zeta_orderK`).

    The island's order-3 chain (`EMZetaTail.em_zeta_strip3`) stops at the saw-3 remainder.  This
    file raises the order to ANY `m ≥ 1` by induction, so the finite part carries every Bernoulli
    correction `B_2, B_4, …, B_{2K}` and the remainder decays like `N^{-(Re s + 2K - 1)}`:

      M1.  `poch`, `emC`            -- rising factorial `s(s+1)…(s+k-1)` and the k-th x-derivative
                                       coefficient `(-1)^k (s)_k` of `x^{-s}`.
      M2.  `em_tail_step`           -- ONE saw-order-raising step on the tail `[N, ∞)`, any k ≥ 1
                                       (generalises `EMZetaTail.em_tail2_step` / `em_tail3_step`).
      M3.  `emTail_unroll`          -- the induction: the saw-1 tail equals the explicit Bernoulli
                                       sum plus `(-1)^(m-1) emTail m / m!`.
      M4.  `em_zeta_order`          -- the general-order identity for `riemannZeta` on `Re s > 0`.
      M5.  `emTail_norm_le`         -- remainder bound from any sup bound of the order-m saw.
      M6.  `abs_sawBernoulli_even_le` -- `|B̃_{2K}(x)| ≤ |B_{2K}|` for every K ≥ 1 (Mathlib's
                                       Fourier cosine series of the Bernoulli polynomials).
      M6'. `abs_sawBernoulli_odd_le`  -- `|B̃_{2K+1}(x)| ≤ 2(2K+1)!/(2π)^{2K+1} (1 + (π²/6−1)/2^{2K−1})`
                                       (Fourier sine series + `ζ(p) ≤ 1 + (π²/6−1)/2^{p−2}`).
      M7.  `em_zeta_orderK_enclosure` -- THE THEOREM (general K), even-saw remainder:
             ‖ζ(s) − emFinite K s N‖ ≤ |B_{2K}|/(2K)! · ‖(s)_{2K}‖ · N^{-(σ+2K-1)}/(σ+2K-1),
           and `em_zeta_orderK_enclosure_odd`, the same finite part with the saw-(2K+1) remainder
             ‖ζ(s) − emFinite K s N‖ ≤ 2(1+(π²/6−1)/2^{2K−1})/(2π)^{2K+1} · ‖(s)_{2K+1}‖ · N^{-(σ+2K)}/(σ+2K)
           (smaller by about `|s+2K|/(2πN)`), with the evaluator-facing Dirichlet form
           `emFinite = Σ_{n<N} n^{-s} + N^{-s}·emCorr`; `em_line_remainder_le` / `_odd_le` are the
           critical-line forms with a rational majorant `Q` of the Pochhammer norm and `r ≤ √N`.
      M8.  exact Bernoulli numbers `B_2 … B_12` (the K ≤ 6 constants).

    conjecture1_proved = False.  A classical analysis lemma (Euler-Maclaurin), not a proof of RH.
-/
import EMZetaTail
import Mathlib.Analysis.Real.Pi.Bounds

open MeasureTheory intervalIntegral Set Filter Topology Complex
open scoped Real Nat

namespace ZetaReflection

namespace EMHigh

/-! ## M1. Rising factorial and the derivative coefficients of `x^{-s}`. -/

/-- The rising factorial `(s)_k = s (s+1) ⋯ (s+k-1)`. -/
noncomputable def poch (s : ℂ) : ℕ → ℂ
  | 0 => 1
  | k + 1 => poch s k * (s + k)

@[simp] lemma poch_zero (s : ℂ) : poch s 0 = 1 := rfl

lemma poch_succ (s : ℂ) (k : ℕ) : poch s (k + 1) = poch s k * (s + k) := rfl

lemma norm_poch_succ (s : ℂ) (k : ℕ) : ‖poch s (k + 1)‖ = ‖poch s k‖ * ‖s + k‖ := by
  rw [poch_succ, norm_mul]

/-- `d^k/dx^k x^{-s} = emC s k · x^{-s-k}` with `emC s k = (-1)^k (s)_k`. -/
noncomputable def emC (s : ℂ) (k : ℕ) : ℂ := (-1) ^ k * poch s k

lemma emC_succ (s : ℂ) (k : ℕ) : emC s (k + 1) = emC s k * (-s - k) := by
  simp only [emC, poch_succ, pow_succ]; ring

lemma norm_emC (s : ℂ) (k : ℕ) : ‖emC s k‖ = ‖poch s k‖ := by
  simp [emC, norm_pow]

lemma emC_one (s : ℂ) : emC s 1 = -s := by
  simp [emC, poch_succ]

/-- The x-derivative of the k-th term: `d/dx (emC s k · x^{-s-k}) = emC s (k+1) · x^{-s-(k+1)}`
    for real `x > 0` (needs `-s-k ≠ 0`, automatic on `Re s > 0`). -/
theorem hasDerivAt_emTerm {s : ℂ} (hs : 0 < s.re) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => emC s k * (x : ℂ) ^ (-s - k))
      (emC s (k + 1) * (x : ℂ) ^ (-s - ((k + 1 : ℕ) : ℂ))) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hr : (-s - k : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.neg_re, Complex.natCast_re, Complex.zero_re] at this
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hstep := (hasDerivAt_ofReal_cpow_const hx0 hr).const_mul (emC s k)
  have hexp : (-s - (k : ℂ) - 1) = -s - ((k + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [hexp] at hstep
  have hval : emC s k * ((-s - k) * (x : ℂ) ^ (-s - ((k + 1 : ℕ) : ℂ)))
      = emC s (k + 1) * (x : ℂ) ^ (-s - ((k + 1 : ℕ) : ℂ)) := by
    rw [emC_succ]; ring
  rw [hval] at hstep
  exact hstep

/-! ## M2. The general saw-order-raising step on the tail `[N, ∞)`. -/

/-- Every periodized Bernoulli function is bounded (`bernoulliFun k` is continuous on `[0,1]`). -/
theorem sawBernoulli_bounded (k : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, |sawBernoulli k x| ≤ B := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    ((continuous_bernoulliFun (k := k)).continuousOn)
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  have hmem : Int.fract x ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  have := hC _ hmem
  rw [Real.norm_eq_abs] at this
  exact le_trans this (le_max_left _ _)

/-- Integrability of the k-th tail integrand on `(N, ∞)` whenever `Re s + k > 1`. -/
theorem emTail_integrableOn (k : ℕ) {s : ℂ} {N : ℕ} (hN : 1 ≤ N) (hk : 1 < s.re + k) :
    IntegrableOn (fun x : ℝ => (sawBernoulli k x : ℂ) * (emC s k * (x : ℂ) ^ (-s - k)))
      (Ioi (N : ℝ)) := by
  obtain ⟨B, hB0, hB⟩ := sawBernoulli_bounded k
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hexplt : -(s.re + (k : ℝ)) < -1 := by linarith
  have hdom : IntegrableOn (fun x : ℝ => (B * ‖emC s k‖) * x ^ (-(s.re + (k : ℝ)))) (Ioi (N : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (a := -(s.re + (k : ℝ))) hexplt hNpos).const_mul _
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
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hnormcpow]
    calc |sawBernoulli k x| * (‖emC s k‖ * x ^ (-(s.re + (k : ℝ))))
        ≤ B * (‖emC s k‖ * x ^ (-(s.re + (k : ℝ)))) := by
          gcongr; exact hB x
      _ = (B * ‖emC s k‖) * x ^ (-(s.re + (k : ℝ))) := by ring

/-- The order-k tail integral `∫_N^∞ B̃_k(x) · emC s k · x^{-s-k} dx`. -/
noncomputable def emTail (s : ℂ) (N k : ℕ) : ℂ :=
  ∫ x in Ioi (N : ℝ), (sawBernoulli k x : ℂ) * (emC s k * (x : ℂ) ^ (-s - k))

/-- **One saw-order-raising step on the tail**, any `k ≥ 1`, `Re s > 0`, `N ≥ 1`:
        emTail s N k = B_{k+1} · (−emC s k · N^{−s−k}) / (k+1) − emTail s N (k+1) / (k+1).
    Finite window `[N, M]` by `EMZetaTail.em_saw_step_window_cpow`, then `M → ∞`. -/
theorem em_tail_step (k : ℕ) (hk : 1 ≤ k) {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    emTail s N k
      = (bernoulli (k + 1) : ℂ) * (-(emC s k * ((N : ℝ) : ℂ) ^ (-s - k))) / (k + 1)
        - emTail s N (k + 1) / (k + 1) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set fk : ℝ → ℂ := fun x => emC s k * (x : ℂ) ^ (-s - k) with hfk
  set fk1 : ℝ → ℂ := fun x => emC s (k + 1) * (x : ℂ) ^ (-s - ((k + 1 : ℕ) : ℂ)) with hfk1
  have hIk : IntegrableOn (fun x : ℝ => (sawBernoulli k x : ℂ) * fk x) (Ioi (N : ℝ)) :=
    emTail_integrableOn k hN (by linarith)
  have hIk1 : IntegrableOn (fun x : ℝ => (sawBernoulli (k + 1) x : ℂ) * fk1 x) (Ioi (N : ℝ)) :=
    emTail_integrableOn (k + 1) hN (by push_cast; linarith)
  -- the finite-window identity for every M ≥ N
  have hwin : ∀ M : ℕ, N ≤ M →
      (∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli k x : ℂ) * fk x)
        = (bernoulliFun (k + 1) 0 : ℂ) * (fk M - fk N) / (k + 1)
          - (∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli (k + 1) x : ℂ) * fk1 x) / (k + 1) := by
    intro M hM
    have hd : ∀ x ∈ Icc (N : ℝ) M, HasDerivAt fk (fk1 x) x := by
      intro x hx
      have hx1 : (1 : ℝ) ≤ x := le_trans (by exact_mod_cast hN) hx.1
      exact hasDerivAt_emTerm hs k (lt_of_lt_of_le zero_lt_one hx1)
    have hi : ∀ j ∈ Finset.Ico N M, IntervalIntegrable fk1 volume (j : ℝ) (j + 1) := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast le_trans hN hj.1
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le (by linarith)]
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.cpow_const Complex.continuous_ofReal.continuousOn
      intro x hx
      have : (1 : ℝ) ≤ x := le_trans hj1 hx.1
      exact Or.inl (by simp only [Complex.ofReal_re]; linarith)
    exact em_saw_step_window_cpow (k := k) hk N M hM fk fk1 hd hi
  -- limits as M → ∞
  have hA : Tendsto (fun M : ℕ => ∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli k x : ℂ) * fk x) atTop
      (𝓝 (∫ x in Ioi (N : ℝ), (sawBernoulli k x : ℂ) * fk x)) :=
    intervalIntegral_tendsto_integral_Ioi N hIk tendsto_natCast_atTop_atTop
  have hB : Tendsto (fun M : ℕ => ∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli (k + 1) x : ℂ) * fk1 x)
      atTop (𝓝 (∫ x in Ioi (N : ℝ), (sawBernoulli (k + 1) x : ℂ) * fk1 x)) :=
    intervalIntegral_tendsto_integral_Ioi N hIk1 tendsto_natCast_atTop_atTop
  have hEnd0 : Tendsto (fun M : ℕ => fk (M : ℝ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hnorm : (fun M : ℕ => ‖fk (M : ℝ)‖)
        =ᶠ[atTop] (fun M : ℕ => ‖emC s k‖ * (M : ℝ) ^ (-(s.re + k))) := by
      filter_upwards [eventually_gt_atTop 0] with M hM
      have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
      rw [hfk, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hMpos]
      congr 2
      rw [Complex.sub_re, Complex.neg_re, Complex.natCast_re]; ring
    refine Tendsto.congr' hnorm.symm ?_
    have hz : Tendsto (fun M : ℕ => (M : ℝ) ^ (-(s.re + k))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (y := s.re + k) (by positivity)).comp tendsto_natCast_atTop_atTop
    simpa using hz.const_mul ‖emC s k‖
  have hRHS : Tendsto (fun M : ℕ =>
      (bernoulliFun (k + 1) 0 : ℂ) * (fk M - fk N) / (k + 1)
        - (∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli (k + 1) x : ℂ) * fk1 x) / (k + 1)) atTop
      (𝓝 ((bernoulliFun (k + 1) 0 : ℂ) * (0 - fk N) / (k + 1)
        - (∫ x in Ioi (N : ℝ), (sawBernoulli (k + 1) x : ℂ) * fk1 x) / (k + 1))) := by
    apply Tendsto.sub
    · apply Tendsto.div_const
      apply Tendsto.const_mul
      exact hEnd0.sub_const (fk N)
    · exact hB.div_const _
  have hEq : ∀ᶠ M : ℕ in atTop,
      (∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli k x : ℂ) * fk x)
        = (bernoulliFun (k + 1) 0 : ℂ) * (fk M - fk N) / (k + 1)
          - (∫ x in (N : ℝ)..(M : ℝ), (sawBernoulli (k + 1) x : ℂ) * fk1 x) / (k + 1) := by
    filter_upwards [eventually_ge_atTop N] with M hM using hwin M hM
  have hlim := tendsto_nhds_unique (hA.congr' hEq) hRHS
  have hb : (bernoulliFun (k + 1) 0 : ℂ) = (bernoulli (k + 1) : ℂ) := by
    rw [bernoulliFun_eval_zero]; push_cast; rfl
  simp only [emTail]
  rw [hlim, hb, hfk, hfk1]
  push_cast
  ring

/-! ## M3. The induction: unrolling the saw-1 tail to any order. -/

/-- **Unrolled tail.**  For every `j`, the saw-1 tail equals the explicit Bernoulli corrections
    `Σ_{i<j} B_{i+2} (s)_{i+1} N^{-s-(i+1)} / (i+2)!` plus the order-`(j+1)` remainder
    `(-1)^j emTail s N (j+1) / (j+1)!`. -/
theorem emTail_unroll_step {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) (j : ℕ) :
    (-1) ^ j * emTail s N (j + 1) / ((j + 1)! : ℂ)
      = (bernoulli (j + 2) : ℂ) * poch s (j + 1) / ((j + 2)! : ℂ)
            * ((N : ℝ) : ℂ) ^ (-s - ((j + 1 : ℕ) : ℂ))
        + (-1) ^ (j + 1) * emTail s N (j + 2) / ((j + 2)! : ℂ) := by
  rw [em_tail_step (j + 1) (by omega) hs hN]
  have hf : ((j + 2)! : ℂ) = ((j : ℂ) + 2) * ((j + 1)! : ℂ) := by
    rw [show j + 2 = (j + 1) + 1 from rfl, Nat.factorial_succ (j + 1)]; push_cast; ring
  rw [hf]
  have h1 : ((j + 1)! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h2 : ((j : ℂ) + 2) ≠ 0 := by
    have : ((j : ℝ) + 2) ≠ 0 := by positivity
    exact_mod_cast this
  simp only [emC]
  set u : ℂ := (-1) ^ j with hu
  have hu2 : u * u = 1 := by
    rw [hu, ← pow_add, ← two_mul, pow_mul]; norm_num
  have hpj : ((-1 : ℂ) ^ (j + 1)) = u * (-1) := by rw [hu, pow_succ]
  rw [hpj]
  set P := poch s (j + 1)
  set X := ((N : ℝ) : ℂ) ^ (-s - ((j + 1 : ℕ) : ℂ))
  set T := emTail s N (j + 1 + 1)
  set b := (bernoulli (j + 1 + 1) : ℂ)
  have hc : ((j + 1 : ℕ) : ℂ) + 1 = (j : ℂ) + 2 := by push_cast; ring
  rw [hc]
  field_simp
  linear_combination (b * P * X) * hu2

/-- **Unrolled tail.**  For every `j`, the saw-1 tail equals the explicit Bernoulli corrections
    `Σ_{i<j} B_{i+2} (s)_{i+1} N^{-s-(i+1)} / (i+2)!` plus the order-`(j+1)` remainder
    `(-1)^j emTail s N (j+1) / (j+1)!`. -/
theorem emTail_unroll {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) (j : ℕ) :
    emTail s N 1
      = (∑ i ∈ Finset.range j, (bernoulli (i + 2) : ℂ) * poch s (i + 1) / ((i + 2)! : ℂ)
            * ((N : ℝ) : ℂ) ^ (-s - ((i + 1 : ℕ) : ℂ)))
        + (-1) ^ j * emTail s N (j + 1) / ((j + 1)! : ℂ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [ih, Finset.sum_range_succ, emTail_unroll_step hs hN j]
    ring

/-! ## M4. The general-order identity for `riemannZeta`. -/

/-- The explicit order-`m` finite part, Dirichlet form:
    `Σ_{n=1}^{N-1} n^{-s} + N^{1-s}/(s-1) + N^{-s}/2 + Σ_{i<m-1} B_{i+2} (s)_{i+1} N^{-s-(i+1)}/(i+2)!`. -/
noncomputable def emFiniteM (m : ℕ) (s : ℂ) (N : ℕ) : ℂ :=
  (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s)) + (N : ℂ) ^ (1 - s) / (s - 1) + (N : ℂ) ^ (-s) / 2
    + ∑ i ∈ Finset.range (m - 1), (bernoulli (i + 2) : ℂ) * poch s (i + 1) / ((i + 2)! : ℂ)
        * (N : ℂ) ^ (-s - ((i + 1 : ℕ) : ℂ))

/-- **The general-order Euler-Maclaurin identity for ζ** (`Re s > 0`, `s ≠ 1`, `N ≥ 1`, `m ≥ 1`):
        ζ(s) = emFiniteM m s N + (-1)^(m-1) · emTail s N m / m!.
    From the K = 1 continuation `EMZetaComplex.em_zeta_strip`, the `[1,N] ∪ (N,∞)` split, the
    Dirichlet rewrite `em_cpow_partial` + `integral_cpow`, and `emTail_unroll`. -/
theorem em_zeta_order (m : ℕ) (hm : 1 ≤ m) {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {N : ℕ}
    (hN : 1 ≤ N) :
    riemannZeta s = emFiniteM m s N + (-1) ^ (m - 1) * emTail s N m / (m ! : ℂ) := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs
  have hK1 := em_zeta_strip hs hs1
  have h1N : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  -- split ∫_1^∞ = ∫_1^N + ∫_N^∞
  have hI1_Ioi : IntegrableOn (fun x : ℝ => (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
      (Ioi 1) := em_cpow_remainder_integrableOn_strip hs
  have hsplit : (∫ x in Ioi (1 : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
      = (∫ x in (1 : ℝ)..(N : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
        + ∫ x in Ioi (N : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)) := by
    have hIcc : IntegrableOn (fun x : ℝ => (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
        (Ioc 1 N) := hI1_Ioi.mono_set Ioc_subset_Ioi_self
    have hIoiN : IntegrableOn (fun x : ℝ => (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
        (Ioi N) := hI1_Ioi.mono_set (Ioi_subset_Ioi h1N)
    have hunion : (∫ x in Ioi (1 : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
        = (∫ x in Ioc (1 : ℝ) N, (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
          + ∫ x in Ioi (N : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)) := by
      rw [← setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hIcc hIoiN,
        Set.Ioc_union_Ioi_eq_Ioi h1N]
    rw [hunion, ← intervalIntegral.integral_of_le h1N]
  -- the tail is emTail s N 1
  have htail : (∫ x in Ioi (N : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
      = emTail s N 1 := by
    simp only [emTail, emC_one, Nat.cast_one]
  -- the Dirichlet rewrite of the [1,N] saw integral
  have hpart := em_cpow_partial hs0 (N := N) hN
  have hint : (∫ x in (1 : ℝ)..(N : ℝ), (x : ℂ) ^ (-s))
      = (((N : ℝ) : ℂ) ^ (-s + 1) - ((1 : ℝ) : ℂ) ^ (-s + 1)) / (-s + 1) := by
    apply integral_cpow
    right
    refine ⟨?_, ?_⟩
    · intro h; apply hs1; linear_combination -h
    · rw [Set.uIcc_of_le h1N]; intro h; have := h.1; linarith
  have hunroll := emTail_unroll hs hN (m - 1)
  rw [show m - 1 + 1 = m by omega] at hunroll
  rw [hK1, hsplit, htail, hunroll]
  -- normalize casts and powers
  have hNc : ((N : ℝ) : ℂ) = (N : ℂ) := Complex.ofReal_natCast N
  have hone : ((1 : ℝ) : ℂ) = 1 := Complex.ofReal_one
  rw [hint, hNc, hone] at hpart
  simp only [Complex.one_cpow] at hpart
  simp only [hNc, emFiniteM]
  have hsm1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hden : (-s + 1) ≠ 0 := by
    rw [show (-s + 1 : ℂ) = -(s - 1) by ring]; exact neg_ne_zero.mpr hsm1
  have hpow : (N : ℂ) ^ (-s + 1) = (N : ℂ) ^ (1 - s) := by rw [show (-s + 1 : ℂ) = 1 - s by ring]
  rw [hpow] at hpart
  set Isaw : ℂ := ∫ x in (1 : ℝ)..(N : ℝ), (sawBernoulli 1 x : ℂ) * (-s * (x : ℂ) ^ (-s - 1))
    with hIsaw
  set S : ℂ := ∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s) with hS
  have hIsaw_eq : Isaw = S - ((N : ℂ) ^ (1 - s) - 1) / (-s + 1) + ((N : ℂ) ^ (-s) - 1) / 2 := by
    linear_combination -hpart
  rw [hIsaw_eq]
  field_simp
  ring

/-! ## M5. The remainder bound from a sup bound of the order-m saw. -/

/-- `‖emTail s N m‖ ≤ B · ‖(s)_m‖ · N^{-(σ+m-1)} / (σ+m-1)` whenever `|B̃_m| ≤ B`. -/
theorem emTail_norm_le (m : ℕ) (hm : 1 ≤ m) {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N)
    {B : ℝ} (hB0 : 0 ≤ B) (hsaw : ∀ x : ℝ, |sawBernoulli m x| ≤ B) :
    ‖emTail s N m‖ ≤ B * ‖poch s m‖ * (N : ℝ) ^ (-(s.re + m - 1)) / (s.re + m - 1) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h := em_tail_integral_bound (k := m) (s := s) (c := emC s m) (B := B) (N := N) hN
    (by linarith) hB0 hsaw
  rw [norm_emC] at h
  exact h

/-! ## M6. The sup bound `|B̃_{2K}(x)| ≤ |B_{2K}|` (general K ≥ 1). -/

/-- `|B_{2K}(x)| ≤ |B_{2K}|` on `[0,1]`, from the Fourier cosine series of the Bernoulli
    polynomial (`hasSum_one_div_nat_pow_mul_cos`) compared termwise with its value at `x = 0`. -/
theorem abs_bernoulliFun_even_le (K : ℕ) (hK : K ≠ 0) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |bernoulliFun (2 * K) x| ≤ |(bernoulli (2 * K) : ℝ)| := by
  set C : ℝ := (-1 : ℝ) ^ (K + 1) * (2 * π) ^ (2 * K) / 2 / (2 * K)! with hCdef
  have hx' := hasSum_one_div_nat_pow_mul_cos hK hx
  have h0' := hasSum_one_div_nat_pow_mul_cos hK (left_mem_Icc.mpr (zero_le_one' ℝ))
  have hBx : (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * K))).eval x
      = bernoulliFun (2 * K) x := rfl
  have hB0 : (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * K))).eval 0
      = (bernoulli (2 * K) : ℝ) := by
    rw [← bernoulliFun_eval_zero]; rfl
  rw [hBx] at hx'
  rw [hB0] at h0'
  -- h0' : HasSum (fun n => 1/n^(2K) * cos(2π n 0)) (C * B_{2K})
  have hg : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ (2 * K)) (C * (bernoulli (2 * K) : ℝ)) := by
    have := h0'
    simp only [mul_zero, Real.cos_zero, mul_one] at this
    exact this
  have hle1 : C * bernoulliFun (2 * K) x ≤ C * (bernoulli (2 * K) : ℝ) := by
    refine hasSum_le (fun n => ?_) hx' hg
    have hnn : (0 : ℝ) ≤ 1 / (n : ℝ) ^ (2 * K) := by positivity
    calc 1 / (n : ℝ) ^ (2 * K) * Real.cos (2 * π * n * x)
        ≤ 1 / (n : ℝ) ^ (2 * K) * 1 := by
          apply mul_le_mul_of_nonneg_left (Real.cos_le_one _) hnn
      _ = 1 / (n : ℝ) ^ (2 * K) := by ring
  have hle2 : -(C * bernoulliFun (2 * K) x) ≤ C * (bernoulli (2 * K) : ℝ) := by
    refine hasSum_le (fun n => ?_) hx'.neg hg
    have hnn : (0 : ℝ) ≤ 1 / (n : ℝ) ^ (2 * K) := by positivity
    have := Real.neg_one_le_cos (2 * π * n * x)
    show -(1 / (n : ℝ) ^ (2 * K) * Real.cos (2 * π * n * x)) ≤ 1 / (n : ℝ) ^ (2 * K)
    nlinarith
  have habs : |C * bernoulliFun (2 * K) x| ≤ C * (bernoulli (2 * K) : ℝ) :=
    abs_le.mpr ⟨by linarith, hle1⟩
  have hCne : C ≠ 0 := by
    have e : C = (-1 : ℝ) ^ (K + 1) * ((2 * π) ^ (2 * K) / 2 / (2 * K)!) := by rw [hCdef]; ring
    rw [e]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (ne_of_gt (by positivity))
  have hCpos : 0 < |C| := abs_pos.mpr hCne
  rw [abs_mul] at habs
  have h3 : C * (bernoulli (2 * K) : ℝ) ≤ |C| * |(bernoulli (2 * K) : ℝ)| := by
    rw [← abs_mul]; exact le_abs_self _
  exact le_of_mul_le_mul_left (le_trans habs h3) hCpos

/-- **The even saw sup bound**: `|B̃_{2K}(x)| ≤ |B_{2K}|` for all real `x`, `K ≥ 1`. -/
theorem abs_sawBernoulli_even_le (K : ℕ) (hK : K ≠ 0) (x : ℝ) :
    |sawBernoulli (2 * K) x| ≤ |(bernoulli (2 * K) : ℝ)| :=
  abs_bernoulliFun_even_le K hK ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩

/-! ## M6'. The odd sup bound `|B̃_{2K+1}(x)| ≤ 2 (2K+1)! ζ(2K+1) / (2π)^{2K+1}` (general K ≥ 1),
    with the elementary majorant `ζ(p) ≤ 1 + (π²/6 − 1)/2^(p−2)`. -/

/-- `Σ_n 1/n^p ≤ 1 + (π²/6 − 1)/2^(p−2)` for `p ≥ 2` (compare with `Σ 1/n² = π²/6`: for `n ≥ 2`,
    `n^p ≥ 2^(p−2) n²`). -/
theorem hasSum_one_div_pow_le {p : ℕ} (hp : 2 ≤ p) {S : ℝ}
    (hS : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ p) S) :
    S ≤ 1 + (π ^ 2 / 6 - 1) / 2 ^ (p - 2) := by
  set c : ℝ := 1 / 2 ^ (p - 2) with hc
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 := by
    rw [hc, div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  have hg : HasSum (fun n : ℕ => (if n = 1 then (1 - c) else 0) + c * (1 / (n : ℝ) ^ 2))
      ((1 - c) + c * (π ^ 2 / 6)) :=
    (hasSum_ite_eq 1 (1 - c)).add (hasSum_zeta_two.mul_left c)
  have hle : ∀ n : ℕ, 1 / (n : ℝ) ^ p ≤ (if n = 1 then (1 - c) else 0) + c * (1 / (n : ℝ) ^ 2) := by
    intro n
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      · have hp0 : p ≠ 0 := by omega
        simp [hp0]
      · simp
    · have hn : (2 : ℝ) ≤ n := by exact_mod_cast h
      have hne : n ≠ 1 := by omega
      simp only [hne, if_false, zero_add]
      have hnpos : (0 : ℝ) < n := by linarith
      have hpow : (n : ℝ) ^ 2 * 2 ^ (p - 2) ≤ (n : ℝ) ^ p := by
        have : (n : ℝ) ^ p = (n : ℝ) ^ 2 * (n : ℝ) ^ (p - 2) := by
          rw [← pow_add]; congr 1; omega
        rw [this]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hn _) (by positivity)
      rw [hc, div_mul_div_comm, one_mul]
      apply one_div_le_one_div_of_le (by positivity)
      linarith [hpow, mul_comm ((n : ℝ) ^ 2) (2 ^ (p - 2))]
  have h := hasSum_le hle hS hg
  have e : (1 - c) + c * (π ^ 2 / 6) = 1 + (π ^ 2 / 6 - 1) / 2 ^ (p - 2) := by
    rw [hc]; field_simp; ring
  linarith [h, e]

/-- `|B_{2K+1}(x)| ≤ 2 (2K+1)!/(2π)^{2K+1} · (1 + (π²/6 − 1)/2^(2K−1))` on `[0,1]`, from the Fourier
    sine series (`hasSum_one_div_nat_pow_mul_sin`). -/
theorem abs_bernoulliFun_odd_le (K : ℕ) (hK : K ≠ 0) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |bernoulliFun (2 * K + 1) x|
      ≤ 2 * ((2 * K + 1)! : ℝ) / (2 * π) ^ (2 * K + 1) * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) := by
  have hx' := hasSum_one_div_nat_pow_mul_sin hK hx
  have hBx : (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * K + 1))).eval x
      = bernoulliFun (2 * K + 1) x := rfl
  rw [hBx] at hx'
  set C : ℝ := (-1 : ℝ) ^ (K + 1) * (2 * π) ^ (2 * K + 1) / 2 / (2 * K + 1)! with hCdef
  have hsum : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (2 * K + 1)) :=
    Real.summable_one_div_nat_pow.mpr (by omega)
  have hS := hsum.hasSum
  set S := ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * K + 1) with hSdef
  have hle1 : C * bernoulliFun (2 * K + 1) x ≤ S := by
    refine hasSum_le (fun n => ?_) hx' hS
    have hnn : (0 : ℝ) ≤ 1 / (n : ℝ) ^ (2 * K + 1) := by positivity
    calc 1 / (n : ℝ) ^ (2 * K + 1) * Real.sin (2 * π * n * x)
        ≤ 1 / (n : ℝ) ^ (2 * K + 1) * 1 := mul_le_mul_of_nonneg_left (Real.sin_le_one _) hnn
      _ = 1 / (n : ℝ) ^ (2 * K + 1) := by ring
  have hle2 : -(C * bernoulliFun (2 * K + 1) x) ≤ S := by
    refine hasSum_le (fun n => ?_) hx'.neg hS
    have hnn : (0 : ℝ) ≤ 1 / (n : ℝ) ^ (2 * K + 1) := by positivity
    have := Real.neg_one_le_sin (2 * π * n * x)
    show -(1 / (n : ℝ) ^ (2 * K + 1) * Real.sin (2 * π * n * x)) ≤ 1 / (n : ℝ) ^ (2 * K + 1)
    nlinarith
  have habs : |C * bernoulliFun (2 * K + 1) x| ≤ S := abs_le.mpr ⟨by linarith, hle1⟩
  have hSle := hasSum_one_div_pow_le (p := 2 * K + 1) (by omega) hS
  rw [show 2 * K + 1 - 2 = 2 * K - 1 by omega] at hSle
  have hCabs : |C| = (2 * π) ^ (2 * K + 1) / 2 / (2 * K + 1)! := by
    rw [hCdef, abs_div, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos (by positivity : (0 : ℝ) < (2 * π) ^ (2 * K + 1)), abs_two,
      abs_of_pos (by exact_mod_cast Nat.factorial_pos _ : (0 : ℝ) < ((2 * K + 1)! : ℝ))]
  have hCpos : 0 < |C| := by rw [hCabs]; positivity
  rw [abs_mul] at habs
  have hB : |bernoulliFun (2 * K + 1) x| ≤ S / |C| := by
    rw [le_div_iff₀ hCpos, mul_comm]; exact habs
  refine le_trans hB ?_
  rw [hCabs]
  have hF : (0 : ℝ) < ((2 * K + 1)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hpi : (0 : ℝ) < (2 * π) ^ (2 * K + 1) := by positivity
  rw [div_div, div_div_eq_mul_div]
  calc S * (2 * ((2 * K + 1)! : ℝ)) / (2 * π) ^ (2 * K + 1)
      ≤ (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) * (2 * ((2 * K + 1)! : ℝ)) / (2 * π) ^ (2 * K + 1) := by
        gcongr
    _ = 2 * ((2 * K + 1)! : ℝ) / (2 * π) ^ (2 * K + 1) * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) := by
        ring

/-- **The odd saw sup bound**, all real `x`, `K ≥ 1`. -/
theorem abs_sawBernoulli_odd_le (K : ℕ) (hK : K ≠ 0) (x : ℝ) :
    |sawBernoulli (2 * K + 1) x|
      ≤ 2 * ((2 * K + 1)! : ℝ) / (2 * π) ^ (2 * K + 1) * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) :=
  abs_bernoulliFun_odd_le K hK ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩

/-! ## M7. THE THEOREM: general-K enclosure, evaluator (Dirichlet) form. -/

/-- The evaluator-facing correction factor, so that `emFinite K s N = Σ_{n<N} n^{-s} + N^{-s}·emCorr`:
    `emCorr K s N = N/(s-1) + 1/2 + Σ_{i<2K-1} B_{i+2} (s)_{i+1} / ((i+2)! N^{i+1})`
    (the order-(2K+1) Euler-Maclaurin correction: `B_2, B_4, …, B_{2K}`; odd `B`'s vanish). -/
noncomputable def emCorr (K : ℕ) (s : ℂ) (N : ℕ) : ℂ :=
  (N : ℂ) / (s - 1) + 1 / 2
    + ∑ i ∈ Finset.range (2 * K - 1),
        (bernoulli (i + 2) : ℂ) * poch s (i + 1) / ((i + 2)! : ℂ) / (N : ℂ) ^ (i + 1)

/-- The order-(2K+1) Euler-Maclaurin finite part of ζ: the Dirichlet sum `Σ_{n=1}^{N-1} n^{-s}`
    plus `N^{-s}` times the correction factor. -/
noncomputable def emFinite (K : ℕ) (s : ℂ) (N : ℕ) : ℂ :=
  (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s)) + (N : ℂ) ^ (-s) * emCorr K s N

theorem emFinite_eq_emFiniteM (K : ℕ) (s : ℂ) {N : ℕ} (hN : 1 ≤ N) :
    emFinite K s N = emFiniteM (2 * K) s N := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have h1 : (N : ℂ) ^ (1 - s) = (N : ℂ) * (N : ℂ) ^ (-s) := by
    rw [show (1 : ℂ) - s = 1 + -s by ring, Complex.cpow_add _ _ hN0, Complex.cpow_one]
  have h2 : ∀ i : ℕ, (N : ℂ) ^ (-s - ((i + 1 : ℕ) : ℂ)) = (N : ℂ) ^ (-s) / (N : ℂ) ^ (i + 1) := by
    intro i
    rw [Complex.cpow_sub _ _ hN0, Complex.cpow_natCast]
  simp only [emFinite, emFiniteM, emCorr, h1, h2]
  have hsum : (∑ i ∈ Finset.range (2 * K - 1), (bernoulli (i + 2) : ℂ) * poch s (i + 1)
        / ((i + 2)! : ℂ) * ((N : ℂ) ^ (-s) / (N : ℂ) ^ (i + 1)))
      = (N : ℂ) ^ (-s) * ∑ i ∈ Finset.range (2 * K - 1),
          (bernoulli (i + 2) : ℂ) * poch s (i + 1) / ((i + 2)! : ℂ) / (N : ℂ) ^ (i + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _; ring
  rw [hsum]
  ring

/-- **THE GENERAL-ORDER EULER-MACLAURIN ENCLOSURE OF ζ (any K ≥ 1).**  For `0 < Re s`, `s ≠ 1`,
    `N ≥ 1`, with `σ = Re s`:
        ‖ζ(s) − emFinite K s N‖ ≤ |B_{2K}|/(2K)! · ‖(s)_{2K}‖ · N^{-(σ+2K-1)} / (σ+2K-1).
    The finite part carries the Bernoulli corrections through `B_{2K}` (order 2K+1); the remainder
    is the saw-`2K` tail with the exact rational sup constant `|B_{2K}|` (`abs_sawBernoulli_even_le`). -/
theorem em_zeta_orderK_enclosure (K : ℕ) (hK : 1 ≤ K) {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖riemannZeta s - emFinite K s N‖
      ≤ |(bernoulli (2 * K) : ℝ)| / ((2 * K)! : ℝ) * ‖poch s (2 * K)‖
          * (N : ℝ) ^ (-(s.re + ((2 * K : ℕ) : ℝ) - 1)) / (s.re + ((2 * K : ℕ) : ℝ) - 1) := by
  have hm : 1 ≤ 2 * K := by omega
  have hid := em_zeta_order (2 * K) hm hs hs1 hN
  rw [emFinite_eq_emFiniteM K s hN]
  have hdiff : riemannZeta s - emFiniteM (2 * K) s N
      = (-1) ^ (2 * K - 1) * emTail s N (2 * K) / ((2 * K)! : ℂ) := by
    rw [hid]; ring
  rw [hdiff]
  have hF : (0 : ℝ) < ((2 * K)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hnorm : ‖(-1) ^ (2 * K - 1) * emTail s N (2 * K) / ((2 * K)! : ℂ)‖
      = ‖emTail s N (2 * K)‖ / ((2 * K)! : ℝ) := by
    rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    congr 1
    exact_mod_cast Complex.norm_natCast _
  rw [hnorm]
  have hbd := emTail_norm_le (2 * K) hm hs hN (abs_nonneg _)
    (abs_sawBernoulli_even_le K (by omega))
  have hσ : 0 < s.re + ((2 * K : ℕ) : ℝ) - 1 := by
    have : (1 : ℝ) ≤ ((2 * K : ℕ) : ℝ) := by exact_mod_cast hm
    linarith
  calc ‖emTail s N (2 * K)‖ / ((2 * K)! : ℝ)
      ≤ (|(bernoulli (2 * K) : ℝ)| * ‖poch s (2 * K)‖
          * (N : ℝ) ^ (-(s.re + ((2 * K : ℕ) : ℝ) - 1)) / (s.re + ((2 * K : ℕ) : ℝ) - 1))
          / ((2 * K)! : ℝ) := by
        exact div_le_div_of_nonneg_right hbd hF.le
    _ = _ := by ring

/-- The order-(2K+1) finite part does not change when the saw-(2K+1) remainder form is used: the
    extra Bernoulli term carries `B_{2K+1} = 0`. -/
theorem emFiniteM_odd_eq (K : ℕ) (hK : 1 ≤ K) (s : ℂ) (N : ℕ) :
    emFiniteM (2 * K + 1) s N = emFiniteM (2 * K) s N := by
  simp only [emFiniteM]
  rw [show 2 * K + 1 - 1 = (2 * K - 1) + 1 by omega, Finset.sum_range_succ,
    show 2 * K - 1 + 2 = 2 * K + 1 by omega,
    bernoulli_eq_zero_of_odd (by exact ⟨K, rfl⟩ : Odd (2 * K + 1)) (by omega)]
  simp

/-- **THE ORDER-(2K+1) ENCLOSURE, odd-saw remainder form (any K ≥ 1).**  Same finite part as
    `em_zeta_orderK_enclosure`; the remainder is the saw-(2K+1) tail, bounded with the Fourier
    constant of `abs_sawBernoulli_odd_le`:
        ‖ζ(s) − emFinite K s N‖ ≤ 2(1 + (π²/6−1)/2^(2K−1))/(2π)^(2K+1) · ‖(s)_{2K+1}‖
                                    · N^{−(σ+2K)} / (σ+2K).
    It beats the even form by the factor `≈ |s+2K|/(2πN)`, i.e. whenever `N > t/(2π)`. -/
theorem em_zeta_orderK_enclosure_odd (K : ℕ) (hK : 1 ≤ K) {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖riemannZeta s - emFinite K s N‖
      ≤ 2 * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) / (2 * π) ^ (2 * K + 1) * ‖poch s (2 * K + 1)‖
          * (N : ℝ) ^ (-(s.re + ((2 * K + 1 : ℕ) : ℝ) - 1)) / (s.re + ((2 * K + 1 : ℕ) : ℝ) - 1) := by
  have hm : 1 ≤ 2 * K + 1 := by omega
  have hid := em_zeta_order (2 * K + 1) hm hs hs1 hN
  rw [emFinite_eq_emFiniteM K s hN, ← emFiniteM_odd_eq K hK s N]
  have hdiff : riemannZeta s - emFiniteM (2 * K + 1) s N
      = (-1) ^ (2 * K + 1 - 1) * emTail s N (2 * K + 1) / ((2 * K + 1)! : ℂ) := by
    rw [hid]; ring
  rw [hdiff]
  have hF : (0 : ℝ) < ((2 * K + 1)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hnorm : ‖(-1) ^ (2 * K + 1 - 1) * emTail s N (2 * K + 1) / ((2 * K + 1)! : ℂ)‖
      = ‖emTail s N (2 * K + 1)‖ / ((2 * K + 1)! : ℝ) := by
    rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    congr 1
    exact_mod_cast Complex.norm_natCast _
  rw [hnorm]
  have hB0 : 0 ≤ 2 * ((2 * K + 1)! : ℝ) / (2 * π) ^ (2 * K + 1)
      * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) := by
    have hpi6 : (0 : ℝ) ≤ π ^ 2 / 6 - 1 := by
      have := Real.pi_gt_three
      nlinarith
    positivity
  have hbd := emTail_norm_le (2 * K + 1) hm hs hN hB0 (abs_sawBernoulli_odd_le K (by omega))
  have hσ : 0 < s.re + ((2 * K + 1 : ℕ) : ℝ) - 1 := by
    have : (1 : ℝ) ≤ ((2 * K + 1 : ℕ) : ℝ) := by exact_mod_cast hm
    linarith
  calc ‖emTail s N (2 * K + 1)‖ / ((2 * K + 1)! : ℝ)
      ≤ (2 * ((2 * K + 1)! : ℝ) / (2 * π) ^ (2 * K + 1) * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1))
          * ‖poch s (2 * K + 1)‖ * (N : ℝ) ^ (-(s.re + ((2 * K + 1 : ℕ) : ℝ) - 1))
          / (s.re + ((2 * K + 1 : ℕ) : ℝ) - 1)) / ((2 * K + 1)! : ℝ) :=
        div_le_div_of_nonneg_right hbd hF.le
    _ = _ := by field_simp

/-! ## M7'. The critical line: rational remainder and real/imaginary parts of the correction. -/

/-- `Π_{j<k} ((σ+j)² + t²)`, which is `‖(σ + i t)_k‖²`. -/
noncomputable def pochNormSq (σ t : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => pochNormSq σ t k * ((σ + k) ^ 2 + t ^ 2)

theorem norm_poch_sq (σ t : ℝ) (k : ℕ) :
    ‖poch ((σ : ℂ) + (t : ℂ) * I) k‖ ^ 2 = pochNormSq σ t k := by
  induction k with
  | zero => simp [pochNormSq]
  | succ k ih =>
    rw [norm_poch_succ, mul_pow, ih, pochNormSq, Complex.sq_norm, Complex.normSq_apply]
    congr 1
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.natCast_re, Complex.add_im, Complex.mul_im, Complex.natCast_im]
    ring

theorem norm_poch_le (σ t : ℝ) (k : ℕ) (Q : ℝ) (hQ0 : 0 ≤ Q) (hQ : pochNormSq σ t k ≤ Q ^ 2) :
    ‖poch ((σ : ℂ) + (t : ℂ) * I) k‖ ≤ Q := by
  rw [← norm_poch_sq] at hQ
  have h0 := norm_nonneg (poch ((σ : ℂ) + (t : ℂ) * I) k)
  nlinarith [hQ]

/-- **Critical-line remainder in rational form** (the kernel-evaluator consumer).  With
    `s = 1/2 + i t`, `Q ≥ 0`, `Q² ≥ Π_{j<2K}((1/2+j)² + t²)`, `0 < r ≤ √N`:
        ‖ζ(s) − emFinite K s N‖ ≤ |B_{2K}|/(2K)! · Q / (N^{2K-1} r) / (2K − 1/2). -/
theorem em_line_remainder_le (K : ℕ) (hK : 1 ≤ K) (t : ℝ) {N : ℕ} (hN : 1 ≤ N) (Q : ℝ)
    (hQ0 : 0 ≤ Q) (hQ : pochNormSq (1 / 2) t (2 * K) ≤ Q ^ 2) (r : ℕ) (hr0 : 0 < r)
    (hr : r ^ 2 ≤ N) :
    ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I) - emFinite K ((1 / 2 : ℂ) + (t : ℂ) * I) N‖
      ≤ |(bernoulli (2 * K) : ℝ)| / ((2 * K)! : ℝ) * Q / ((N : ℝ) ^ (2 * K - 1) * r)
          / (((2 * K : ℕ) : ℝ) - 1 / 2) := by
  set s : ℂ := (1 / 2 : ℂ) + (t : ℂ) * I with hsdef
  have hre : s.re = 1 / 2 := by simp [hsdef]
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hre] at this; norm_num at this
  have h := em_zeta_orderK_enclosure K hK hs hs1 hN
  rw [hre] at h
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr0
  have hm1 : (2 : ℝ) ≤ ((2 * K : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ 2 * K by omega)
  have hpoch : ‖poch s (2 * K)‖ ≤ Q := by
    have := norm_poch_le (1 / 2) t (2 * K) Q hQ0 hQ
    simpa [hsdef] using this
  -- N^{-(1/2 + 2K - 1)} ≤ 1/(N^{2K-1} r)
  have hpow : (N : ℝ) ^ (-((1 / 2 : ℝ) + ((2 * K : ℕ) : ℝ) - 1))
      ≤ 1 / ((N : ℝ) ^ (2 * K - 1) * r) := by
    have hsq : (r : ℝ) ≤ Real.sqrt N := by
      rw [Real.le_sqrt (by positivity) (by positivity)]; exact_mod_cast hr
    have e : (N : ℝ) ^ (-((1 / 2 : ℝ) + ((2 * K : ℕ) : ℝ) - 1))
        = 1 / ((N : ℝ) ^ (2 * K - 1) * Real.sqrt N) := by
      have hk : ((1 / 2 : ℝ) + ((2 * K : ℕ) : ℝ) - 1) = ((2 * K - 1 : ℕ) : ℝ) + (1 / 2 : ℝ) := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [hk, Real.rpow_neg (le_of_lt hNR), Real.rpow_add hNR, Real.rpow_natCast,
        ← Real.sqrt_eq_rpow, one_div]
    rw [e]
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul_of_nonneg_left hsq (by positivity)
  have hden : ((1 / 2 : ℝ) + ((2 * K : ℕ) : ℝ) - 1) = ((2 * K : ℕ) : ℝ) - 1 / 2 := by ring
  have hdpos : (0 : ℝ) < ((2 * K : ℕ) : ℝ) - 1 / 2 := by linarith
  rw [hden] at h hpow
  refine le_trans h ?_
  have hF : (0 : ℝ) < ((2 * K)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hpn : 0 ≤ (N : ℝ) ^ (-(((2 * K : ℕ) : ℝ) - 1 / 2)) := by positivity
  calc |(bernoulli (2 * K) : ℝ)| / ((2 * K)! : ℝ) * ‖poch s (2 * K)‖
        * (N : ℝ) ^ (-(((2 * K : ℕ) : ℝ) - 1 / 2)) / (((2 * K : ℕ) : ℝ) - 1 / 2)
      ≤ |(bernoulli (2 * K) : ℝ)| / ((2 * K)! : ℝ) * Q * (1 / ((N : ℝ) ^ (2 * K - 1) * r))
          / (((2 * K : ℕ) : ℝ) - 1 / 2) := by
        gcongr
    _ = |(bernoulli (2 * K) : ℝ)| / ((2 * K)! : ℝ) * Q / ((N : ℝ) ^ (2 * K - 1) * r)
          / (((2 * K : ℕ) : ℝ) - 1 / 2) := by ring

/-- **Critical-line remainder, odd-saw form, rational shape.**  With `s = 1/2 + i t`, `Q ≥ 0`,
    `Q² ≥ Π_{j<2K+1}((1/2+j)² + t²)`, `0 < r ≤ √N`:
        ‖ζ(s) − emFinite K s N‖ ≤ 2(1 + (π²/6−1)/2^(2K−1))/(2π)^(2K+1) · Q / (N^{2K} r) / (2K + 1/2). -/
theorem em_line_remainder_odd_le (K : ℕ) (hK : 1 ≤ K) (t : ℝ) {N : ℕ} (hN : 1 ≤ N) (Q : ℝ)
    (hQ0 : 0 ≤ Q) (hQ : pochNormSq (1 / 2) t (2 * K + 1) ≤ Q ^ 2) (r : ℕ) (hr0 : 0 < r)
    (hr : r ^ 2 ≤ N) :
    ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I) - emFinite K ((1 / 2 : ℂ) + (t : ℂ) * I) N‖
      ≤ 2 * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) / (2 * π) ^ (2 * K + 1) * Q
          / ((N : ℝ) ^ (2 * K) * r) / (((2 * K + 1 : ℕ) : ℝ) - 1 / 2) := by
  set s : ℂ := (1 / 2 : ℂ) + (t : ℂ) * I with hsdef
  have hre : s.re = 1 / 2 := by simp [hsdef]
  have hs : 0 < s.re := by rw [hre]; norm_num
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hre] at this; norm_num at this
  have h := em_zeta_orderK_enclosure_odd K hK hs hs1 hN
  rw [hre] at h
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr0
  have hm1 : (3 : ℝ) ≤ ((2 * K + 1 : ℕ) : ℝ) := by exact_mod_cast (show 3 ≤ 2 * K + 1 by omega)
  have hpoch : ‖poch s (2 * K + 1)‖ ≤ Q := by
    have := norm_poch_le (1 / 2) t (2 * K + 1) Q hQ0 hQ
    simpa [hsdef] using this
  have hden : ((1 / 2 : ℝ) + ((2 * K + 1 : ℕ) : ℝ) - 1) = ((2 * K + 1 : ℕ) : ℝ) - 1 / 2 := by ring
  have hdpos : (0 : ℝ) < ((2 * K + 1 : ℕ) : ℝ) - 1 / 2 := by linarith
  have hpow : (N : ℝ) ^ (-(((2 * K + 1 : ℕ) : ℝ) - 1 / 2)) ≤ 1 / ((N : ℝ) ^ (2 * K) * r) := by
    have hsq : (r : ℝ) ≤ Real.sqrt N := by
      rw [Real.le_sqrt (by positivity) (by positivity)]; exact_mod_cast hr
    have e : (N : ℝ) ^ (-(((2 * K + 1 : ℕ) : ℝ) - 1 / 2))
        = 1 / ((N : ℝ) ^ (2 * K) * Real.sqrt N) := by
      have hk : ((2 * K + 1 : ℕ) : ℝ) - 1 / 2 = ((2 * K : ℕ) : ℝ) + (1 / 2 : ℝ) := by
        push_cast; ring
      rw [hk, Real.rpow_neg (le_of_lt hNR), Real.rpow_add hNR, Real.rpow_natCast,
        ← Real.sqrt_eq_rpow, one_div]
    rw [e]
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul_of_nonneg_left hsq (by positivity)
  rw [hden] at h
  refine le_trans h ?_
  have hpi6 : (0 : ℝ) ≤ π ^ 2 / 6 - 1 := by
    have := Real.pi_gt_three
    nlinarith
  have hC : 0 ≤ 2 * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) / (2 * π) ^ (2 * K + 1) := by positivity
  have hpn : 0 ≤ (N : ℝ) ^ (-(((2 * K + 1 : ℕ) : ℝ) - 1 / 2)) := by positivity
  calc 2 * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) / (2 * π) ^ (2 * K + 1) * ‖poch s (2 * K + 1)‖
        * (N : ℝ) ^ (-(((2 * K + 1 : ℕ) : ℝ) - 1 / 2)) / (((2 * K + 1 : ℕ) : ℝ) - 1 / 2)
      ≤ 2 * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) / (2 * π) ^ (2 * K + 1) * Q
          * (1 / ((N : ℝ) ^ (2 * K) * r)) / (((2 * K + 1 : ℕ) : ℝ) - 1 / 2) := by
        gcongr
    _ = 2 * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) / (2 * π) ^ (2 * K + 1) * Q
          / ((N : ℝ) ^ (2 * K) * r) / (((2 * K + 1 : ℕ) : ℝ) - 1 / 2) := by ring

/-! ## M7''. Real and imaginary parts of the correction factor on a vertical line. -/

/-- Real and imaginary parts of `(σ + i t)_k` by the complex product recursion. -/
noncomputable def pochRI (σ t : ℝ) : ℕ → ℝ × ℝ
  | 0 => (1, 0)
  | k + 1 => ((pochRI σ t k).1 * (σ + k) - (pochRI σ t k).2 * t,
              (pochRI σ t k).1 * t + (pochRI σ t k).2 * (σ + k))

theorem poch_re_im (σ t : ℝ) (k : ℕ) :
    (poch ((σ : ℂ) + (t : ℂ) * I) k).re = (pochRI σ t k).1 ∧
    (poch ((σ : ℂ) + (t : ℂ) * I) k).im = (pochRI σ t k).2 := by
  induction k with
  | zero => simp [pochRI]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [poch_succ, pochRI, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.natCast_re,
      Complex.natCast_im, h1, h2]
    constructor <;> ring

/-- `Re (emCorr K (σ + i t) N)` in closed real form. -/
noncomputable def emCorrRe (K : ℕ) (σ t : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) * (σ - 1) / ((σ - 1) ^ 2 + t ^ 2) + 1 / 2
    + ∑ i ∈ Finset.range (2 * K - 1),
        (bernoulli (i + 2) : ℝ) / ((i + 2)! : ℝ) / (N : ℝ) ^ (i + 1) * (pochRI σ t (i + 1)).1

/-- `Im (emCorr K (σ + i t) N)` in closed real form. -/
noncomputable def emCorrIm (K : ℕ) (σ t : ℝ) (N : ℕ) : ℝ :=
  -((N : ℝ) * t) / ((σ - 1) ^ 2 + t ^ 2)
    + ∑ i ∈ Finset.range (2 * K - 1),
        (bernoulli (i + 2) : ℝ) / ((i + 2)! : ℝ) / (N : ℝ) ^ (i + 1) * (pochRI σ t (i + 1)).2

/-- A complex number times a real scalar, real and imaginary parts. -/
private lemma re_im_ofReal_mul (a : ℝ) (z : ℂ) :
    ((a : ℂ) * z).re = a * z.re ∧ ((a : ℂ) * z).im = a * z.im := by
  constructor <;> simp [Complex.mul_re, Complex.mul_im]

theorem emCorr_re_im (K : ℕ) (σ t : ℝ) (N : ℕ) :
    (emCorr K ((σ : ℂ) + (t : ℂ) * I) N).re = emCorrRe K σ t N ∧
    (emCorr K ((σ : ℂ) + (t : ℂ) * I) N).im = emCorrIm K σ t N := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hsdef
  -- the N/(s-1) part
  have hq : (N : ℂ) / (s - 1)
      = (((N : ℝ) * (σ - 1) / ((σ - 1) ^ 2 + t ^ 2) : ℝ) : ℂ)
        + ((-((N : ℝ) * t) / ((σ - 1) ^ 2 + t ^ 2) : ℝ) : ℂ) * I := by
    by_cases h0 : (σ - 1) ^ 2 + t ^ 2 = 0
    · have hσ : σ - 1 = 0 := by nlinarith [sq_nonneg (σ - 1), sq_nonneg t]
      have ht : t = 0 := by nlinarith [sq_nonneg (σ - 1), sq_nonneg t]
      have hs1 : s - 1 = 0 := by
        rw [hsdef, ht]; push_cast
        have : (σ : ℂ) = 1 := by
          have : σ = 1 := by linarith
          rw [this]; simp
        rw [this]; ring
      rw [hs1, div_zero, h0]; simp
    · have hs1 : s - 1 ≠ 0 := by
        intro h
        apply h0
        have hre := congrArg Complex.re h
        have him := congrArg Complex.im h
        simp [hsdef] at hre him
        rw [him]; nlinarith [hre]
      rw [div_eq_iff hs1]
      apply Complex.ext <;>
        simp only [hsdef, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
          Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
          Complex.I_im, Complex.one_re, Complex.one_im, Complex.natCast_re, Complex.natCast_im] <;>
        field_simp <;> ring
  -- each correction term is a real scalar times poch
  have hterm : ∀ i : ℕ, (bernoulli (i + 2) : ℂ) * poch s (i + 1) / ((i + 2)! : ℂ) / (N : ℂ) ^ (i + 1)
      = (((bernoulli (i + 2) : ℝ) / ((i + 2)! : ℝ) / (N : ℝ) ^ (i + 1) : ℝ) : ℂ) * poch s (i + 1) := by
    intro i; push_cast; ring
  have hsum_re : (∑ i ∈ Finset.range (2 * K - 1), (bernoulli (i + 2) : ℂ) * poch s (i + 1)
        / ((i + 2)! : ℂ) / (N : ℂ) ^ (i + 1)).re
      = ∑ i ∈ Finset.range (2 * K - 1),
          (bernoulli (i + 2) : ℝ) / ((i + 2)! : ℝ) / (N : ℝ) ^ (i + 1) * (pochRI σ t (i + 1)).1 := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hterm i, (re_im_ofReal_mul _ _).1, (poch_re_im σ t (i + 1)).1]
  have hsum_im : (∑ i ∈ Finset.range (2 * K - 1), (bernoulli (i + 2) : ℂ) * poch s (i + 1)
        / ((i + 2)! : ℂ) / (N : ℂ) ^ (i + 1)).im
      = ∑ i ∈ Finset.range (2 * K - 1),
          (bernoulli (i + 2) : ℝ) / ((i + 2)! : ℝ) / (N : ℝ) ^ (i + 1) * (pochRI σ t (i + 1)).2 := by
    rw [Complex.im_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hterm i, (re_im_ofReal_mul _ _).2, (poch_re_im σ t (i + 1)).2]
  have hre1 : ((((N : ℝ) * (σ - 1) / ((σ - 1) ^ 2 + t ^ 2) : ℝ) : ℂ)
        + ((-((N : ℝ) * t) / ((σ - 1) ^ 2 + t ^ 2) : ℝ) : ℂ) * I).re
      = (N : ℝ) * (σ - 1) / ((σ - 1) ^ 2 + t ^ 2) := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]; ring
  have him1 : ((((N : ℝ) * (σ - 1) / ((σ - 1) ^ 2 + t ^ 2) : ℝ) : ℂ)
        + ((-((N : ℝ) * t) / ((σ - 1) ^ 2 + t ^ 2) : ℝ) : ℂ) * I).im
      = -((N : ℝ) * t) / ((σ - 1) ^ 2 + t ^ 2) := by
    simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]; ring
  have hhalf_re : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
  have hhalf_im : ((1 : ℂ) / 2).im = 0 := by norm_num
  constructor
  · rw [emCorr, Complex.add_re, Complex.add_re, hq, hsum_re, emCorrRe, hre1, hhalf_re]
  · rw [emCorr, Complex.add_im, Complex.add_im, hq, hsum_im, emCorrIm, him1, hhalf_im, add_zero]

/-! ## M8. The exact Bernoulli numbers `B_2 … B_12` (the constants of K ≤ 6). -/

theorem bernoulli'_five : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
theorem bernoulli'_seven : bernoulli' 7 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
theorem bernoulli'_nine : bernoulli' 9 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
theorem bernoulli'_eleven : bernoulli' 11 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose, bernoulli'_five]

theorem bernoulli'_eight : bernoulli' 8 = -1 / 30 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose, bernoulli'_five, bernoulli'_six, bernoulli'_seven]

theorem bernoulli'_ten : bernoulli' 10 = 5 / 66 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose, bernoulli'_five, bernoulli'_six, bernoulli'_seven,
    bernoulli'_eight, bernoulli'_nine]

theorem bernoulli'_twelve : bernoulli' 12 = -691 / 2730 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose, bernoulli'_five, bernoulli'_six, bernoulli'_seven,
    bernoulli'_eight, bernoulli'_nine, bernoulli'_ten, bernoulli'_eleven]

theorem bernoulli_four' : bernoulli 4 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_four]
theorem bernoulli_six' : bernoulli 6 = 1 / 42 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_six]
theorem bernoulli_eight' : bernoulli 8 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_eight]
theorem bernoulli_ten' : bernoulli 10 = 5 / 66 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_ten]
theorem bernoulli_twelve' : bernoulli 12 = -691 / 2730 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_twelve]

/-- The odd Bernoulli numbers `B_3, …, B_13` vanish. -/
theorem bernoulli_odd_vanish :
    bernoulli 3 = 0 ∧ bernoulli 5 = 0 ∧ bernoulli 7 = 0 ∧ bernoulli 9 = 0 ∧ bernoulli 11 = 0 ∧
      bernoulli 13 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact bernoulli_eq_zero_of_odd (by decide) (by norm_num)

end EMHigh

end ZetaReflection
