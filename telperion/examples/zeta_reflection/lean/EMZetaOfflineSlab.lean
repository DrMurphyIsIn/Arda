/-  EMZetaOfflineSlab.lean -- lane offline: zero-free cells OFF the critical line by a Taylor model
    of the Euler-Maclaurin finite part (the analysis behind a `SlabClear` certificate).

    For a center `c = σc + i tc` (`σc ≥ 0`) and a point `s = c + h`, `‖h‖ ≤ r`:

      T1.  `exp_taylor_le`        -- `‖e^w - Σ_{k≤p} w^k/k!‖ ≤ ‖w‖^(p+1) (p+2)/((p+1)!(p+1))`, `‖w‖ ≤ 1`;
      T2.  `natCpow_neg_add`      -- `n^(-(c+h)) = n^(-c) e^(-h log n)`;
      T3.  `norm_poch_sub_le`     -- `‖(c+h)_k - (c)_k‖ ≤ (U+r)^k - U^k` when every `‖c + j‖ ≤ U`;
      T4.  `emCorr_sub_le`        -- the correction factor moves by at most
                                     `δ = N r / a² + Σ_{i<2K-1} |B_{i+2}|/(i+2)! ((U+r)^(i+1) - U^(i+1)) / N^(i+1)`
                                     (`a ≤ Im c`, `a ≤ Im s`);
      T5.  `emFinite_taylor_le`   -- THE TAYLOR MODEL:
                                     `‖emFinite K (c+h) N - Σ_{k≤p} h^k (-1)^k/k! · W_k‖ ≤ Err`, where
                                     `W_k = Σ_{n<N} (log n)^k n^(-c) + (log N)^k N^(-c) emCorr(c)` and
                                     `Err = C_p (r L)^(p+1) ((N-1) + ‖emCorr(c)‖) + 3 δ`, `L ≥ log N`;
      T6.  `em_remainder_region`  -- the order-(2K+1) remainder uniformly on `1/2 ≤ Re s ≤ 1`,
                                     `0 ≤ Im s ≤ B`;
      T7.  `zeta_ne_zero_of_cell` -- a zero at `s` would force `‖Σ_k h^k …‖ ≤ Err + E`; so
                                     `‖W_0‖ > Σ_{k=1}^p ‖W_k‖ r^k / k! + Err + E` rules it out.

    conjecture1_proved = False.  A finite, local nonvanishing argument; nothing about RH.
-/
import EMZetaOfflineCheck
import Mathlib.Analysis.Complex.ExponentialBounds

open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

namespace ArbEcon

namespace Off

/-! ## T1. The complex exponential Taylor remainder. -/

/-- The Taylor constant `C_p = (p+2) / ((p+1)! (p+1))`. -/
noncomputable def Cp (p : ℕ) : ℝ := ((p + 2 : ℕ) : ℝ) / (((p + 1)! : ℕ) * ((p + 1 : ℕ) : ℝ))

theorem Cp_nonneg (p : ℕ) : 0 ≤ Cp p := by unfold Cp; positivity

theorem exp_taylor_le (w : ℂ) (hw : ‖w‖ ≤ 1) (p : ℕ) :
    ‖Complex.exp w - ∑ k ∈ Finset.range (p + 1), w ^ k / (k ! : ℂ)‖ ≤ ‖w‖ ^ (p + 1) * Cp p := by
  have h := Complex.exp_bound hw (n := p + 1) (by omega)
  refine le_trans h (le_of_eq ?_)
  unfold Cp
  push_cast
  field_simp
  ring

/-! ## T2. Shifting the exponent. -/

theorem natCpow_neg_add (n : ℕ) (hn : 1 ≤ n) (c h : ℂ) :
    (n : ℂ) ^ (-(c + h)) = (n : ℂ) ^ (-c) * Complex.exp (-(h * ((Real.log n : ℝ) : ℂ))) := by
  have hne : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log hnpos.le]
  rw [Complex.cpow_def_of_ne_zero hne, Complex.cpow_def_of_ne_zero hne, hlog, ← Complex.exp_add]
  congr 1
  ring

theorem norm_natCpow_neg_le_one (n : ℕ) (hn : 1 ≤ n) (c : ℂ) (hc : 0 ≤ c.re) :
    ‖(n : ℂ) ^ (-c)‖ ≤ 1 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_cpow_eq_rpow_re_of_pos hnpos, Complex.neg_re]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by linarith)

/-! ## T3. The Pochhammer symbol moves slowly. -/

theorem norm_poch_sub_le (c h : ℂ) (r U : ℝ) (hr : ‖h‖ ≤ r) (hU0 : 0 ≤ U) :
    ∀ k : ℕ, (∀ j, j < k → ‖c + j‖ ≤ U) → ‖poch (c + h) k - poch c k‖ ≤ (U + r) ^ k - U ^ k := by
  have hr0 : 0 ≤ r := le_trans (norm_nonneg _) hr
  intro k
  induction k with
  | zero => intro _; simp [poch]
  | succ k ih =>
    intro hj
    have hk := ih (fun j hjk => hj j (by omega))
    have hck : ‖c + k‖ ≤ U := hj k (by omega)
    have hpk : ‖poch c k‖ ≤ U ^ k := by
      clear ih hk
      induction k with
      | zero => simp [poch]
      | succ k ih2 =>
        rw [norm_poch_succ, pow_succ]
        exact mul_le_mul (ih2 (fun j hjk => hj j (by omega)) (hj k (by omega))) (hj k (by omega))
          (norm_nonneg _) (pow_nonneg hU0 _)
    have e : poch (c + h) (k + 1) - poch c (k + 1)
        = (poch (c + h) k - poch c k) * (c + k + h) + poch c k * h := by
      rw [poch_succ, poch_succ]; ring
    rw [e]
    have hsum : ‖c + k + h‖ ≤ U + r := le_trans (norm_add_le _ _) (add_le_add hck hr)
    calc ‖(poch (c + h) k - poch c k) * (c + k + h) + poch c k * h‖
        ≤ ‖poch (c + h) k - poch c k‖ * ‖c + k + h‖ + ‖poch c k‖ * ‖h‖ := by
          refine le_trans (norm_add_le _ _) ?_
          rw [norm_mul, norm_mul]
      _ ≤ ((U + r) ^ k - U ^ k) * (U + r) + U ^ k * r := by
          have hUk : 0 ≤ (U + r) ^ k - U ^ k := by
            have : U ^ k ≤ (U + r) ^ k := pow_le_pow_left₀ hU0 (by linarith) k
            linarith
          gcongr
      _ = (U + r) ^ (k + 1) - U ^ (k + 1) := by ring

/-! ## T4. The correction factor moves slowly. -/

/-- The variation budget `δ` of the correction factor. -/
noncomputable def corrVar (K N : ℕ) (r a U : ℝ) : ℝ :=
  (N : ℝ) * r / a ^ 2
    + ∑ i ∈ Finset.range (2 * K - 1),
        |(bernoulli (i + 2) : ℝ)| / ((i + 2)! : ℝ) * ((U + r) ^ (i + 1) - U ^ (i + 1)) / (N : ℝ) ^ (i + 1)

theorem emCorr_sub_le (K N : ℕ) (hN : 1 ≤ N) (c h : ℂ) (r a U : ℝ) (hr : ‖h‖ ≤ r) (ha : 0 < a)
    (hca : a ≤ c.im) (hsa : a ≤ (c + h).im) (hU0 : 0 ≤ U) (hU : ∀ j, j < 2 * K → ‖c + j‖ ≤ U) :
    ‖emCorr K (c + h) N - emCorr K c N‖ ≤ corrVar K N r a U := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hr0 : 0 ≤ r := le_trans (norm_nonneg _) hr
  have hc1 : c - 1 ≠ 0 := by
    intro h0; have := congrArg Complex.im h0; simp at this; linarith
  have hs1 : c + h - 1 ≠ 0 := by
    intro h0; have := congrArg Complex.im h0
    have hch : (c + h).im = c.im + h.im := Complex.add_im c h
    simp at this; linarith
  have hnc : a ≤ ‖c - 1‖ := by
    refine le_trans ?_ (Complex.abs_im_le_norm _)
    simp only [Complex.sub_im, Complex.one_im, sub_zero]
    rw [abs_of_pos (by linarith)]; exact hca
  have hns : a ≤ ‖c + h - 1‖ := by
    refine le_trans ?_ (Complex.abs_im_le_norm _)
    simp only [Complex.sub_im, Complex.one_im, sub_zero]
    rw [abs_of_pos (by linarith)]; exact hsa
  unfold emCorr corrVar
  have e : ((N : ℂ) / (c + h - 1) + 1 / 2
        + ∑ i ∈ Finset.range (2 * K - 1),
            (bernoulli (i + 2) : ℂ) * poch (c + h) (i + 1) / ((i + 2)! : ℂ) / (N : ℂ) ^ (i + 1))
      - ((N : ℂ) / (c - 1) + 1 / 2
        + ∑ i ∈ Finset.range (2 * K - 1),
            (bernoulli (i + 2) : ℂ) * poch c (i + 1) / ((i + 2)! : ℂ) / (N : ℂ) ^ (i + 1))
      = (N : ℂ) * (-h) / ((c + h - 1) * (c - 1))
        + ∑ i ∈ Finset.range (2 * K - 1),
            (bernoulli (i + 2) : ℂ) / ((i + 2)! : ℂ) * (poch (c + h) (i + 1) - poch c (i + 1))
              / (N : ℂ) ^ (i + 1) := by
    have hfr : (N : ℂ) / (c + h - 1) - (N : ℂ) / (c - 1) = (N : ℂ) * (-h) / ((c + h - 1) * (c - 1)) := by
      field_simp; ring
    have hsum : ∑ i ∈ Finset.range (2 * K - 1),
          ((bernoulli (i + 2) : ℂ) * poch (c + h) (i + 1) / ((i + 2)! : ℂ) / (N : ℂ) ^ (i + 1)
            - (bernoulli (i + 2) : ℂ) * poch c (i + 1) / ((i + 2)! : ℂ) / (N : ℂ) ^ (i + 1))
        = ∑ i ∈ Finset.range (2 * K - 1),
            (bernoulli (i + 2) : ℂ) / ((i + 2)! : ℂ) * (poch (c + h) (i + 1) - poch c (i + 1))
              / (N : ℂ) ^ (i + 1) := by
      apply Finset.sum_congr rfl; intro i _; ring
    rw [← hsum, Finset.sum_sub_distrib, ← hfr]; ring
  rw [e]
  refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
  · rw [norm_div, norm_mul, norm_neg, norm_mul, Complex.norm_natCast]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : a * a ≤ ‖c + h - 1‖ * ‖c - 1‖ := mul_le_mul hns hnc ha.le (norm_nonneg _)
    have h2 : (N : ℝ) * ‖h‖ ≤ (N : ℝ) * r := mul_le_mul_of_nonneg_left hr hNR.le
    calc (N : ℝ) * ‖h‖ * a ^ 2 ≤ (N : ℝ) * r * a ^ 2 := by gcongr
      _ = (N : ℝ) * r * (a * a) := by ring
      _ ≤ (N : ℝ) * r * (‖c + h - 1‖ * ‖c - 1‖) := by gcongr
  · refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum ?_)
    intro i hi
    have hi' : i + 1 ≤ 2 * K := by
      have := Finset.mem_range.mp hi; omega
    have hp := norm_poch_sub_le c h r U hr hU0 (i + 1) (fun j hj => hU j (by omega))
    have hb : ‖((bernoulli (i + 2) : ℚ) : ℂ)‖ = |((bernoulli (i + 2) : ℚ) : ℝ)| := by
      rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
    simp only [norm_div, norm_mul, norm_pow, Complex.norm_natCast, hb]
    have hF : (0 : ℝ) < ((i + 2)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hNp : (0 : ℝ) < (N : ℝ) ^ (i + 1) := by positivity
    gcongr

/-! ## T5. The Taylor model of the finite part. -/

/-- The `k`-th Taylor weight at the center `c`:
    `W_k = Σ_{n<N} (log n)^k n^(-c) + (log N)^k N^(-c) emCorr(c)`. -/
noncomputable def Wk (K N : ℕ) (c : ℂ) (k : ℕ) : ℂ :=
  (∑ n ∈ Finset.Ico 1 N, ((Real.log n : ℝ) : ℂ) ^ k * (n : ℂ) ^ (-c))
    + ((Real.log N : ℝ) : ℂ) ^ k * (N : ℂ) ^ (-c) * emCorr K c N

/-- The error budget of the Taylor model. -/
noncomputable def taylorErr (K N p : ℕ) (c : ℂ) (r L a U : ℝ) : ℝ :=
  Cp p * (r * L) ^ (p + 1) * (((N : ℝ) - 1) + ‖emCorr K c N‖) + 3 * corrVar K N r a U

theorem exp_one_le_three : Real.exp 1 ≤ 3 := by
  have := Real.exp_one_lt_d9
  linarith

theorem emFinite_taylor_le (K N p : ℕ) (hN : 1 ≤ N) (c h : ℂ) (r L a U : ℝ) (hc : 0 ≤ c.re)
    (hr : ‖h‖ ≤ r) (hL : Real.log N ≤ L) (hrL : r * L ≤ 1) (ha : 0 < a) (hca : a ≤ c.im)
    (hsa : a ≤ (c + h).im) (hU0 : 0 ≤ U) (hU : ∀ j, j < 2 * K → ‖c + j‖ ≤ U) :
    ‖emFinite K (c + h) N
        - ∑ k ∈ Finset.range (p + 1), h ^ k * ((-1) ^ k / (k ! : ℂ) * Wk K N c k)‖
      ≤ taylorErr K N p c r L a U := by
  have hr0 : 0 ≤ r := le_trans (norm_nonneg _) hr
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hNR
  have hL0 : 0 ≤ L := le_trans hlogN hL
  -- per-term exponential remainder
  have hterm : ∀ n : ℕ, 1 ≤ n → n ≤ N →
      ‖Complex.exp (-(h * ((Real.log n : ℝ) : ℂ)))
          - ∑ k ∈ Finset.range (p + 1), (-(h * ((Real.log n : ℝ) : ℂ))) ^ k / (k ! : ℂ)‖
        ≤ (r * L) ^ (p + 1) * Cp p := by
    intro n hn1 hnN
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
    have hlognL : Real.log n ≤ L :=
      le_trans (Real.log_le_log (by exact_mod_cast (show 0 < n by omega))
        (by exact_mod_cast hnN)) hL
    have hw : ‖-(h * ((Real.log n : ℝ) : ℂ))‖ ≤ r * L := by
      rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hlogn]
      exact mul_le_mul hr hlognL hlogn hr0
    have hw1 : ‖-(h * ((Real.log n : ℝ) : ℂ))‖ ≤ 1 := le_trans hw hrL
    refine le_trans (exp_taylor_le _ hw1 p) ?_
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hw _) (Cp_nonneg p)
  -- the polynomial part, rewritten termwise
  have hpow : ∀ (x : ℝ) (k : ℕ), (-(h * (x : ℂ))) ^ k / (k ! : ℂ)
      = h ^ k * ((-1) ^ k / (k ! : ℂ) * (x : ℂ) ^ k) := by
    intro x k; rw [neg_pow, mul_pow]; ring
  have hpoly : ∑ k ∈ Finset.range (p + 1), h ^ k * ((-1) ^ k / (k ! : ℂ) * Wk K N c k)
      = (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-c)
            * ∑ k ∈ Finset.range (p + 1), (-(h * ((Real.log n : ℝ) : ℂ))) ^ k / (k ! : ℂ))
        + (N : ℂ) ^ (-c) * emCorr K c N
            * ∑ k ∈ Finset.range (p + 1), (-(h * ((Real.log N : ℝ) : ℂ))) ^ k / (k ! : ℂ) := by
    simp only [Wk, mul_add, Finset.sum_add_distrib]
    congr 1
    · calc ∑ k ∈ Finset.range (p + 1), h ^ k * ((-1) ^ k / (k ! : ℂ)
              * ∑ n ∈ Finset.Ico 1 N, ((Real.log n : ℝ) : ℂ) ^ k * (n : ℂ) ^ (-c))
          = ∑ k ∈ Finset.range (p + 1), ∑ n ∈ Finset.Ico 1 N,
              h ^ k * ((-1) ^ k / (k ! : ℂ) * (((Real.log n : ℝ) : ℂ) ^ k * (n : ℂ) ^ (-c))) := by
            apply Finset.sum_congr rfl; intro k _; rw [Finset.mul_sum, Finset.mul_sum]
        _ = ∑ n ∈ Finset.Ico 1 N, ∑ k ∈ Finset.range (p + 1),
              h ^ k * ((-1) ^ k / (k ! : ℂ) * (((Real.log n : ℝ) : ℂ) ^ k * (n : ℂ) ^ (-c))) :=
            Finset.sum_comm
        _ = _ := by
            apply Finset.sum_congr rfl; intro n _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro k _
            rw [hpow]; ring
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _
      rw [hpow]; ring
  -- the finite part at c + h
  have hfin : emFinite K (c + h) N
      = (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-c) * Complex.exp (-(h * ((Real.log n : ℝ) : ℂ))))
        + (N : ℂ) ^ (-c) * Complex.exp (-(h * ((Real.log N : ℝ) : ℂ))) * emCorr K (c + h) N := by
    unfold emFinite
    congr 1
    · apply Finset.sum_congr rfl
      intro n hn
      exact natCpow_neg_add n (Finset.mem_Ico.mp hn).1 c h
    · rw [natCpow_neg_add N hN c h]
  rw [hpoly, hfin]
  set eN := Complex.exp (-(h * ((Real.log N : ℝ) : ℂ))) with heN
  set PN := ∑ k ∈ Finset.range (p + 1), (-(h * ((Real.log N : ℝ) : ℂ))) ^ k / (k ! : ℂ) with hPN
  have e : (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-c) * Complex.exp (-(h * ((Real.log n : ℝ) : ℂ))))
        + (N : ℂ) ^ (-c) * eN * emCorr K (c + h) N
        - ((∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-c)
            * ∑ k ∈ Finset.range (p + 1), (-(h * ((Real.log n : ℝ) : ℂ))) ^ k / (k ! : ℂ))
          + (N : ℂ) ^ (-c) * emCorr K c N * PN)
      = (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-c) * (Complex.exp (-(h * ((Real.log n : ℝ) : ℂ)))
            - ∑ k ∈ Finset.range (p + 1), (-(h * ((Real.log n : ℝ) : ℂ))) ^ k / (k ! : ℂ)))
        + ((N : ℂ) ^ (-c) * emCorr K c N * (eN - PN)
          + (N : ℂ) ^ (-c) * eN * (emCorr K (c + h) N - emCorr K c N)) := by
    have hsd : (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-c) * Complex.exp (-(h * ((Real.log n : ℝ) : ℂ))))
          - ∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-c)
              * ∑ k ∈ Finset.range (p + 1), (-(h * ((Real.log n : ℝ) : ℂ))) ^ k / (k ! : ℂ)
        = ∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-c) * (Complex.exp (-(h * ((Real.log n : ℝ) : ℂ)))
            - ∑ k ∈ Finset.range (p + 1), (-(h * ((Real.log n : ℝ) : ℂ))) ^ k / (k ! : ℂ)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro n _; ring
    rw [← hsd]
    ring
  rw [e]
  have hNc : ‖(N : ℂ) ^ (-c)‖ ≤ 1 := norm_natCpow_neg_le_one N hN c hc
  -- the three pieces
  have p1 : ‖∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-c) * (Complex.exp (-(h * ((Real.log n : ℝ) : ℂ)))
        - ∑ k ∈ Finset.range (p + 1), (-(h * ((Real.log n : ℝ) : ℂ))) ^ k / (k ! : ℂ))‖
      ≤ ((N : ℝ) - 1) * ((r * L) ^ (p + 1) * Cp p) := by
    refine le_trans (norm_sum_le _ _) ?_
    have hle : ∀ n ∈ Finset.Ico 1 N, ‖(n : ℂ) ^ (-c) * (Complex.exp (-(h * ((Real.log n : ℝ) : ℂ)))
        - ∑ k ∈ Finset.range (p + 1), (-(h * ((Real.log n : ℝ) : ℂ))) ^ k / (k ! : ℂ))‖
          ≤ (r * L) ^ (p + 1) * Cp p := by
      intro n hn
      obtain ⟨hn1, hnN⟩ := Finset.mem_Ico.mp hn
      rw [norm_mul]
      have := hterm n hn1 hnN.le
      have hn' := norm_natCpow_neg_le_one n hn1 c hc
      calc ‖(n : ℂ) ^ (-c)‖ * ‖Complex.exp (-(h * ((Real.log n : ℝ) : ℂ)))
            - ∑ k ∈ Finset.range (p + 1), (-(h * ((Real.log n : ℝ) : ℂ))) ^ k / (k ! : ℂ)‖
          ≤ 1 * ((r * L) ^ (p + 1) * Cp p) := by
            gcongr
        _ = (r * L) ^ (p + 1) * Cp p := one_mul _
    refine le_trans (Finset.sum_le_sum hle) (le_of_eq ?_)
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    push_cast [Nat.cast_sub hN]
    ring
  have p2 : ‖(N : ℂ) ^ (-c) * emCorr K c N * (eN - PN)‖
      ≤ ‖emCorr K c N‖ * ((r * L) ^ (p + 1) * Cp p) := by
    rw [norm_mul, norm_mul]
    have := hterm N hN le_rfl
    calc ‖(N : ℂ) ^ (-c)‖ * ‖emCorr K c N‖ * ‖eN - PN‖
        ≤ 1 * ‖emCorr K c N‖ * ((r * L) ^ (p + 1) * Cp p) := by gcongr
      _ = _ := by ring
  have p3 : ‖(N : ℂ) ^ (-c) * eN * (emCorr K (c + h) N - emCorr K c N)‖ ≤ 3 * corrVar K N r a U := by
    rw [norm_mul, norm_mul]
    have hv := emCorr_sub_le K N hN c h r a U hr ha hca hsa hU0 hU
    have heNle : ‖eN‖ ≤ 3 := by
      rw [heN, Complex.norm_exp]
      have hre : (-(h * ((Real.log N : ℝ) : ℂ))).re ≤ 1 := by
        have h1 : (-(h * ((Real.log N : ℝ) : ℂ))).re ≤ ‖-(h * ((Real.log N : ℝ) : ℂ))‖ :=
          Complex.re_le_norm _
        have h2 : ‖-(h * ((Real.log N : ℝ) : ℂ))‖ ≤ r * L := by
          rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hlogN]
          exact mul_le_mul hr hL hlogN hr0
        linarith
      exact le_trans (Real.exp_le_exp.mpr hre) exp_one_le_three
    calc ‖(N : ℂ) ^ (-c)‖ * ‖eN‖ * ‖emCorr K (c + h) N - emCorr K c N‖
        ≤ 1 * 3 * corrVar K N r a U := by gcongr
      _ = 3 * corrVar K N r a U := by ring
  unfold taylorErr
  calc _ ≤ ‖∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-c) * (Complex.exp (-(h * ((Real.log n : ℝ) : ℂ)))
            - ∑ k ∈ Finset.range (p + 1), (-(h * ((Real.log n : ℝ) : ℂ))) ^ k / (k ! : ℂ))‖
        + (‖(N : ℂ) ^ (-c) * emCorr K c N * (eN - PN)‖
          + ‖(N : ℂ) ^ (-c) * eN * (emCorr K (c + h) N - emCorr K c N)‖) :=
        le_trans (norm_add_le _ _) (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ ((N : ℝ) - 1) * ((r * L) ^ (p + 1) * Cp p)
        + (‖emCorr K c N‖ * ((r * L) ^ (p + 1) * Cp p) + 3 * corrVar K N r a U) := by
        gcongr
    _ = Cp p * (r * L) ^ (p + 1) * (((N : ℝ) - 1) + ‖emCorr K c N‖) + 3 * corrVar K N r a U := by
        ring

/-! ## T6. The order-(2K+1) remainder uniformly on a region. -/

/-- The odd-saw remainder constant `C_K = 2 (1 + (π²/6 - 1)/2^(2K-1)) / (2π)^(2K+1)`. -/
noncomputable def CK (K : ℕ) : ℝ := 2 * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) / (2 * π) ^ (2 * K + 1)

theorem CK_nonneg (K : ℕ) : 0 ≤ CK K := by
  unfold CK
  have : (0 : ℝ) ≤ π ^ 2 / 6 - 1 := by nlinarith [Real.pi_gt_three]
  positivity

/-- `C_K` below an explicit rational (`6.283184 < 2π`, `π < 3.141593`). -/
theorem CK_le (K : ℕ) :
    CK K ≤ 2 * (1 + ((3141593 : ℝ) ^ 2 / 1000000 ^ 2 / 6 - 1) / 2 ^ (2 * K - 1))
      / ((6283184 : ℝ) ^ (2 * K + 1) / 1000000 ^ (2 * K + 1)) := by
  have hlo : (6283184 : ℝ) / 1000000 ≤ 2 * π := by
    have := Real.pi_gt_d6; norm_num at this ⊢; linarith
  have hhi : π ≤ (3141593 : ℝ) / 1000000 := by
    have := Real.pi_lt_d6; norm_num at this ⊢; linarith
  have hpipos : (0 : ℝ) < π := Real.pi_pos
  have hpi2 : π ^ 2 ≤ ((3141593 : ℝ) / 1000000) ^ 2 := pow_le_pow_left₀ hpipos.le hhi 2
  have h2k : (0 : ℝ) < (2 : ℝ) ^ (2 * K - 1) := by positivity
  have hnum0 : 0 ≤ 1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1) := by
    have : (0 : ℝ) ≤ π ^ 2 / 6 - 1 := by nlinarith [Real.pi_gt_three]
    positivity
  unfold CK
  rw [← div_pow, ← div_pow]
  gcongr

theorem pochNormSq_mono (σ t σ' t' : ℝ) (hσ0 : 0 ≤ σ) (hσ : σ ≤ σ') (ht : |t| ≤ t') :
    ∀ k : ℕ, pochNormSq σ t k ≤ pochNormSq σ' t' k := by
  intro k
  induction k with
  | zero => simp [pochNormSq]
  | succ k ih =>
    simp only [pochNormSq]
    have h0 : 0 ≤ pochNormSq σ t k := by
      clear ih
      induction k with
      | zero => simp [pochNormSq]
      | succ k ih2 => simp only [pochNormSq]; exact mul_nonneg ih2 (by positivity)
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hsq : (σ + k) ^ 2 + t ^ 2 ≤ (σ' + k) ^ 2 + t' ^ 2 := by
      have h1 : (σ + k) ^ 2 ≤ (σ' + k) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
      have h2 : t ^ 2 ≤ t' ^ 2 := by
        rw [← sq_abs t]; exact pow_le_pow_left₀ (abs_nonneg t) ht 2
      linarith
    exact mul_le_mul ih hsq (by positivity) (le_trans h0 ih)

/-- **The EM remainder on a region**: for `1/2 ≤ Re s ≤ 1`, `0 < Im s ≤ B`,
        ‖ζ(s) − emFinite K s N‖ ≤ C_K · Qr / (N^(2K) r0) / (2K + 1/2)
    whenever `Qr² ≥ Π_{j ≤ 2K} ((1 + j)² + B²)` and `r0² ≤ N`. -/
theorem em_remainder_region (K N : ℕ) (hK : 1 ≤ K) (hN : 1 ≤ N) (s : ℂ) (hs0 : 1 / 2 ≤ s.re)
    (hs1 : s.re ≤ 1) (hsim : 0 < s.im) (B : ℝ) (hsB : s.im ≤ B) (Qr : ℝ) (hQr0 : 0 ≤ Qr)
    (hQ : pochNormSq 1 B (2 * K + 1) ≤ Qr ^ 2) (r0 : ℕ) (hr0 : 0 < r0) (hr0N : r0 ^ 2 ≤ N) :
    ‖riemannZeta s - emFinite K s N‖
      ≤ CK K * Qr / ((N : ℝ) ^ (2 * K) * r0) / (((2 * K : ℕ) : ℝ) + 1 / 2) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hr0R : (0 : ℝ) < r0 := by exact_mod_cast hr0
  have hs1' : s ≠ 1 := by
    intro h; rw [h] at hsim; simp at hsim
  have henc := EMOff.em_zeta_orderK_enclosure_odd_ext K hK (s := s)
    (by push_cast; linarith) hs1' hN
  refine le_trans henc ?_
  -- the Pochhammer factor
  have hseq : s = ((s.re : ℝ) : ℂ) + ((s.im : ℝ) : ℂ) * Complex.I := (Complex.re_add_im s).symm
  have hmono := pochNormSq_mono s.re s.im 1 B (by linarith) hs1
    (by rw [abs_of_pos hsim]; exact hsB) (2 * K + 1)
  have hpoch : ‖poch s (2 * K + 1)‖ ≤ Qr := by
    rw [hseq]; exact norm_poch_le s.re s.im (2 * K + 1) Qr hQr0 (le_trans hmono hQ)
  -- the power of N
  have hpow : (N : ℝ) ^ (-(s.re + ((2 * K + 1 : ℕ) : ℝ) - 1)) ≤ 1 / ((N : ℝ) ^ (2 * K) * r0) := by
    have hsq : (r0 : ℝ) ≤ Real.sqrt N := by
      rw [Real.le_sqrt (by positivity) (by positivity)]; exact_mod_cast hr0N
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have e : (N : ℝ) ^ (-((1 / 2 : ℝ) + ((2 * K : ℕ) : ℝ))) = 1 / ((N : ℝ) ^ (2 * K) * Real.sqrt N) := by
      rw [Real.rpow_neg hNR.le, Real.rpow_add hNR, Real.rpow_natCast, ← Real.sqrt_eq_rpow, one_div]
      ring
    calc (N : ℝ) ^ (-(s.re + ((2 * K + 1 : ℕ) : ℝ) - 1))
        ≤ (N : ℝ) ^ (-((1 / 2 : ℝ) + ((2 * K : ℕ) : ℝ))) := by
          apply Real.rpow_le_rpow_of_exponent_le hN1
          push_cast; linarith
      _ = 1 / ((N : ℝ) ^ (2 * K) * Real.sqrt N) := e
      _ ≤ 1 / ((N : ℝ) ^ (2 * K) * r0) := by
          apply one_div_le_one_div_of_le (by positivity)
          exact mul_le_mul_of_nonneg_left hsq (by positivity)
  have hden : ((2 * K : ℕ) : ℝ) + 1 / 2 ≤ s.re + ((2 * K + 1 : ℕ) : ℝ) - 1 := by push_cast; linarith
  have hden0 : (0 : ℝ) < ((2 * K : ℕ) : ℝ) + 1 / 2 := by positivity
  have hpn0 : 0 ≤ (N : ℝ) ^ (-(s.re + ((2 * K + 1 : ℕ) : ℝ) - 1)) := by positivity
  have hCK := CK_nonneg K
  change CK K * ‖poch s (2 * K + 1)‖ * (N : ℝ) ^ (-(s.re + ((2 * K + 1 : ℕ) : ℝ) - 1))
      / (s.re + ((2 * K + 1 : ℕ) : ℝ) - 1) ≤ _
  calc CK K * ‖poch s (2 * K + 1)‖ * (N : ℝ) ^ (-(s.re + ((2 * K + 1 : ℕ) : ℝ) - 1))
        / (s.re + ((2 * K + 1 : ℕ) : ℝ) - 1)
      ≤ CK K * Qr * (1 / ((N : ℝ) ^ (2 * K) * r0)) / (((2 * K : ℕ) : ℝ) + 1 / 2) := by
        gcongr
    _ = CK K * Qr / ((N : ℝ) ^ (2 * K) * r0) / (((2 * K : ℕ) : ℝ) + 1 / 2) := by ring

/-! ## T7. A zero-free cell. -/

/-- A uniform bound on the correction factor. -/
theorem norm_emCorr_le (K N : ℕ) (hN : 1 ≤ N) (c : ℂ) (a U : ℝ) (ha : 0 < a) (hca : a ≤ c.im)
    (hU0 : 0 ≤ U) (hU : ∀ j, j < 2 * K → ‖c + j‖ ≤ U) :
    ‖emCorr K c N‖ ≤ (N : ℝ) / a + 1 / 2
      + ∑ i ∈ Finset.range (2 * K - 1), |(bernoulli (i + 2) : ℝ)| / ((i + 2)! : ℝ) * U ^ (i + 1)
          / (N : ℝ) ^ (i + 1) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hnc : a ≤ ‖c - 1‖ := by
    refine le_trans ?_ (Complex.abs_im_le_norm _)
    simp only [Complex.sub_im, Complex.one_im, sub_zero]
    rw [abs_of_pos (by linarith)]; exact hca
  have hpk : ∀ k, k ≤ 2 * K → ‖poch c k‖ ≤ U ^ k := by
    intro k
    induction k with
    | zero => intro _; simp [poch]
    | succ k ih =>
      intro hk
      rw [norm_poch_succ, pow_succ]
      exact mul_le_mul (ih (by omega)) (hU k (by omega)) (norm_nonneg _) (pow_nonneg hU0 _)
  unfold emCorr
  refine le_trans (norm_add_le _ _) (add_le_add (le_trans (norm_add_le _ _) (add_le_add ?_ ?_)) ?_)
  · rw [norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_left hNR.le ha hnc
  · norm_num
  · refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum ?_)
    intro i hi
    have hi' : i + 1 ≤ 2 * K := by have := Finset.mem_range.mp hi; omega
    have hb : ‖((bernoulli (i + 2) : ℚ) : ℂ)‖ = |((bernoulli (i + 2) : ℚ) : ℝ)| := by
      rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
    simp only [norm_div, norm_mul, norm_pow, Complex.norm_natCast, hb]
    have hF : (0 : ℝ) < ((i + 2)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hNp : (0 : ℝ) < (N : ℝ) ^ (i + 1) := by positivity
    have := hpk (i + 1) hi'
    have hbn : 0 ≤ |((bernoulli (i + 2) : ℚ) : ℝ)| := abs_nonneg _
    calc |((bernoulli (i + 2) : ℚ) : ℝ)| * ‖poch c (i + 1)‖ / ((i + 2)! : ℝ) / (N : ℝ) ^ (i + 1)
        ≤ |((bernoulli (i + 2) : ℚ) : ℝ)| * U ^ (i + 1) / ((i + 2)! : ℝ) / (N : ℝ) ^ (i + 1) := by
          gcongr
      _ = _ := by ring

/-- **A zero-free cell.**  If `s = c + h` lies within `r` of the center `c = σc + i tc`, in the
    region of the remainder bound `E`, and the Taylor weights satisfy
    `‖W_0‖ > Σ_{k=1}^p ‖W_k‖ r^k / k! + F` with `F ≥ Err + E`, then `ζ(s) ≠ 0`. -/
theorem zeta_ne_zero_of_cell (K N p : ℕ) (hN : 1 ≤ N) (c s : ℂ) (r L a U E F : ℝ)
    (hc : 0 ≤ c.re) (hsc : ‖s - c‖ ≤ r) (hL : Real.log N ≤ L) (hrL : r * L ≤ 1) (ha : 0 < a)
    (hca : a ≤ c.im) (hsa : a ≤ s.im) (hU0 : 0 ≤ U) (hU : ∀ j, j < 2 * K → ‖c + j‖ ≤ U)
    (hE : ‖riemannZeta s - emFinite K s N‖ ≤ E) (hF : taylorErr K N p c r L a U + E ≤ F)
    (hmain : ∑ k ∈ Finset.Ico 1 (p + 1), ‖Wk K N c k‖ * r ^ k / (k ! : ℝ) + F < ‖Wk K N c 0‖) :
    riemannZeta s ≠ 0 := by
  intro hz
  set h := s - c with hh
  have hs : s = c + h := by rw [hh]; ring
  have hr0 : 0 ≤ r := le_trans (norm_nonneg _) hsc
  have hT := emFinite_taylor_le K N p hN c h r L a U hc hsc hL hrL ha hca (by rw [← hs]; exact hsa)
    hU0 hU
  rw [← hs] at hT
  rw [hz, zero_sub, norm_neg] at hE
  -- the polynomial is small
  have hP : ‖∑ k ∈ Finset.range (p + 1), h ^ k * ((-1) ^ k / (k ! : ℂ) * Wk K N c k)‖
      ≤ taylorErr K N p c r L a U + E := by
    have := norm_sub_le (∑ k ∈ Finset.range (p + 1), h ^ k * ((-1) ^ k / (k ! : ℂ) * Wk K N c k))
      (emFinite K s N)
    have e : ‖∑ k ∈ Finset.range (p + 1), h ^ k * ((-1) ^ k / (k ! : ℂ) * Wk K N c k) - emFinite K s N‖
        = ‖emFinite K s N - ∑ k ∈ Finset.range (p + 1), h ^ k * ((-1) ^ k / (k ! : ℂ) * Wk K N c k)‖ :=
      norm_sub_rev _ _
    have := norm_le_insert' (∑ k ∈ Finset.range (p + 1), h ^ k * ((-1) ^ k / (k ! : ℂ) * Wk K N c k))
      (emFinite K s N)
    linarith
  -- ... but large
  have hbig : ‖Wk K N c 0‖ - ∑ k ∈ Finset.Ico 1 (p + 1), ‖Wk K N c k‖ * r ^ k / (k ! : ℝ)
      ≤ ‖∑ k ∈ Finset.range (p + 1), h ^ k * ((-1) ^ k / (k ! : ℂ) * Wk K N c k)‖ := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < p + 1)]
    simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, div_one]
    have hrest : ‖∑ k ∈ Finset.Ico 1 (p + 1), h ^ k * ((-1) ^ k / (k ! : ℂ) * Wk K N c k)‖
        ≤ ∑ k ∈ Finset.Ico 1 (p + 1), ‖Wk K N c k‖ * r ^ k / (k ! : ℝ) := by
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum ?_)
      intro k _
      simp only [norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast]
      have hF : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos _
      have hhk : ‖h‖ ^ k ≤ r ^ k := pow_le_pow_left₀ (norm_nonneg _) hsc k
      calc ‖h‖ ^ k * (1 / (k ! : ℝ) * ‖Wk K N c k‖) ≤ r ^ k * (1 / (k ! : ℝ) * ‖Wk K N c k‖) := by
            gcongr
        _ = ‖Wk K N c k‖ * r ^ k / (k ! : ℝ) := by ring
    have := norm_sub_norm_le (Wk K N c 0 + ∑ k ∈ Finset.Ico 1 (p + 1),
      h ^ k * ((-1) ^ k / (k ! : ℂ) * Wk K N c k)) (Wk K N c 0)
    have e2 : ‖Wk K N c 0 + ∑ k ∈ Finset.Ico 1 (p + 1), h ^ k * ((-1) ^ k / (k ! : ℂ) * Wk K N c k)
        - Wk K N c 0‖ = ‖∑ k ∈ Finset.Ico 1 (p + 1), h ^ k * ((-1) ^ k / (k ! : ℂ) * Wk K N c k)‖ := by
      congr 1; ring
    have := norm_sub_norm_le (Wk K N c 0)
      (-(∑ k ∈ Finset.Ico 1 (p + 1), h ^ k * ((-1) ^ k / (k ! : ℂ) * Wk K N c k)))
    rw [sub_neg_eq_add, norm_neg] at this
    linarith
  linarith

end Off

end ArbEcon
