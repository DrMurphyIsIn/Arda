/-  H1000Octant.lean -- lane h1000-integrate: the kernel-checked OCTANT PIECE, the evaluator side of
    brick K6c (`ArgHoriz`) for the horizontal edges `[2, -1] + i T` of the RvM rectangles.

    `ArgHoriz.hAH_of_octCert_boxes` reduces `argChangeHoriz ζ T 2 (-1) ∈ [L, H]` to an octant
    certificate: breakpoints `2 = p 0 > p 1 > … > p m = -1`, one octant label `k j` per piece, and
    the no-crossing facts `0 < octX (k j) ζ(x + i T)` for every `x` of piece `j`, plus two point
    enclosures at `x = 2` and `x = -1`.  This file proves the no-crossing fact of ONE piece from ONE
    run of the off-line evaluator (`EMZetaOfflineEval`, `p + 1` accumulators) at the piece center
    `c = σc + i tc` and ONE Boolean check run by `decide +kernel`:

      A1. `emCorr_sub_le_norm`, `norm_emCorr_le_norm` -- the correction-factor bounds of
          `EMZetaOfflineSlab` with `a ≤ ‖c - 1‖` in place of `a ≤ Im c` (so they hold near `s = 1`
          at small heights);
      A2. `emFinite_taylor_le_G` -- the Taylor model of the EM finite part for ANY real part of the
          center: `‖n^(-c)‖ ≤ G` for `n ≤ N` (`G = 1` for `σc ≥ 0`, `N^(-σc)` for `σc < 0`);
      B.  `pochNormSq_mono_abs`, `em_remainder_horiz` -- the order-(2K+1) remainder uniformly on a
          horizontal segment `xlo ≤ x ≤ xhi` (negative `x` allowed, `x > -2K`);
          `natCpow_norm_le_of_pow` -- the `G` certificate `Gd^q N^b ≤ Gn^q N^a`;
      C.  `octLo`, `octUp`, `sumOct`, `checkOct`, `checkOct_sound` -- the kernel check
          `Σ_{k=1}^p |octX (W_k)| r^k/k! + (|α| + |β|) F < octX (W_0)` on the evaluator balls;
      D.  `piece_octX_pos` -- THE PIECE: for every real `x` with `|x - σc| ≤ r`,
          `0 < ArgHoriz.octX kk (ζ(x + i tc))`.  Along a horizontal piece `h = x - σc` is REAL, so
          the octant projection of the Taylor polynomial is a real polynomial in `h` and only the
          projections `octX (W_k)` enter;
      E.  `abs_sub_le_of_mem_uIcc`, `budget_mono` -- small helpers for the generated certificates.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (AxiomGuardAllZerosKernel_h1000).  No `sorry`.
    conjecture1_proved = False.  Finite interval arithmetic along finitely many segments; nothing
    here bears on the Riemann Hypothesis.
-/
import EMZetaOfflineSlabClear
import ArgHoriz

open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

namespace H1000Oct

open ArbEcon ArbEcon.Off

/-! ## A1. The correction factor, with `a ≤ ‖c - 1‖`. -/

theorem emCorr_sub_le_norm (K N : ℕ) (hN : 1 ≤ N) (c h : ℂ) (r a U : ℝ) (hr : ‖h‖ ≤ r) (ha : 0 < a)
    (hnc : a ≤ ‖c - 1‖) (hns : a ≤ ‖c + h - 1‖) (hU0 : 0 ≤ U) (hU : ∀ j, j < 2 * K → ‖c + j‖ ≤ U) :
    ‖emCorr K (c + h) N - emCorr K c N‖ ≤ corrVar K N r a U := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc1 : c - 1 ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hnc; linarith
  have hs1 : c + h - 1 ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hns; linarith
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
    calc (N : ℝ) * ‖h‖ * a ^ 2 ≤ (N : ℝ) * r * a ^ 2 := by gcongr
      _ = (N : ℝ) * r * (a * a) := by ring
      _ ≤ (N : ℝ) * r * (‖c + h - 1‖ * ‖c - 1‖) := by
          have hr0 : 0 ≤ r := le_trans (norm_nonneg _) hr
          gcongr
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

/-- A uniform bound on the correction factor from `a ≤ ‖c - 1‖`. -/
theorem norm_emCorr_le_norm (K N : ℕ) (hN : 1 ≤ N) (c : ℂ) (a U : ℝ) (ha : 0 < a) (hnc : a ≤ ‖c - 1‖)
    (hU0 : 0 ≤ U) (hU : ∀ j, j < 2 * K → ‖c + j‖ ≤ U) :
    ‖emCorr K c N‖ ≤ emcB K N a U := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpk : ∀ k, k ≤ 2 * K → ‖poch c k‖ ≤ U ^ k := by
    intro k
    induction k with
    | zero => intro _; simp [poch]
    | succ k ih =>
      intro hk
      rw [norm_poch_succ, pow_succ]
      exact mul_le_mul (ih (by omega)) (hU k (by omega)) (norm_nonneg _) (pow_nonneg hU0 _)
  unfold emCorr emcB
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

/-! ## A2. The Taylor model for any real part of the center. -/

/-- **The Taylor model of the EM finite part, general center.**  As
    `ArbEcon.Off.emFinite_taylor_le`, with `‖n^(-c)‖ ≤ G` for `1 ≤ n ≤ N` in place of `0 ≤ Re c`
    and `a ≤ ‖c - 1‖`, `a ≤ ‖c + h - 1‖` in place of `a ≤ Im c`, `a ≤ Im (c + h)`:
        `‖emFinite K (c+h) N - Σ_{k≤p} h^k (-1)^k/k! W_k‖ ≤ G · taylorErr`. -/
theorem emFinite_taylor_le_G (K N p : ℕ) (hN : 1 ≤ N) (c h : ℂ) (r L a U G : ℝ)
    (hG : ∀ n : ℕ, 1 ≤ n → n ≤ N → ‖(n : ℂ) ^ (-c)‖ ≤ G)
    (hr : ‖h‖ ≤ r) (hL : Real.log N ≤ L) (hrL : r * L ≤ 1) (ha : 0 < a) (hnc : a ≤ ‖c - 1‖)
    (hns : a ≤ ‖c + h - 1‖) (hU0 : 0 ≤ U) (hU : ∀ j, j < 2 * K → ‖c + j‖ ≤ U) :
    ‖emFinite K (c + h) N
        - ∑ k ∈ Finset.range (p + 1), h ^ k * ((-1) ^ k / (k ! : ℂ) * Wk K N c k)‖
      ≤ G * taylorErr K N p c r L a U := by
  have hr0 : 0 ≤ r := le_trans (norm_nonneg _) hr
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hNR
  have hG0 : 0 ≤ G := le_trans (norm_nonneg _) (hG 1 le_rfl hN)
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
  have hNc : ‖(N : ℂ) ^ (-c)‖ ≤ G := hG N hN le_rfl
  have p1 : ‖∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-c) * (Complex.exp (-(h * ((Real.log n : ℝ) : ℂ)))
        - ∑ k ∈ Finset.range (p + 1), (-(h * ((Real.log n : ℝ) : ℂ))) ^ k / (k ! : ℂ))‖
      ≤ ((N : ℝ) - 1) * (G * ((r * L) ^ (p + 1) * Cp p)) := by
    refine le_trans (norm_sum_le _ _) ?_
    have hle : ∀ n ∈ Finset.Ico 1 N, ‖(n : ℂ) ^ (-c) * (Complex.exp (-(h * ((Real.log n : ℝ) : ℂ)))
        - ∑ k ∈ Finset.range (p + 1), (-(h * ((Real.log n : ℝ) : ℂ))) ^ k / (k ! : ℂ))‖
          ≤ G * ((r * L) ^ (p + 1) * Cp p) := by
      intro n hn
      obtain ⟨hn1, hnN⟩ := Finset.mem_Ico.mp hn
      rw [norm_mul]
      exact mul_le_mul (hG n hn1 hnN.le) (hterm n hn1 hnN.le) (norm_nonneg _) hG0
    refine le_trans (Finset.sum_le_sum hle) (le_of_eq ?_)
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    push_cast [Nat.cast_sub hN]
    ring
  have p2 : ‖(N : ℂ) ^ (-c) * emCorr K c N * (eN - PN)‖
      ≤ G * ‖emCorr K c N‖ * ((r * L) ^ (p + 1) * Cp p) := by
    rw [norm_mul, norm_mul]
    have := hterm N hN le_rfl
    gcongr
  have p3 : ‖(N : ℂ) ^ (-c) * eN * (emCorr K (c + h) N - emCorr K c N)‖ ≤ G * 3 * corrVar K N r a U := by
    rw [norm_mul, norm_mul]
    have hv := emCorr_sub_le_norm K N hN c h r a U hr ha hnc hns hU0 hU
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
    gcongr
  unfold taylorErr
  calc _ ≤ ‖∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-c) * (Complex.exp (-(h * ((Real.log n : ℝ) : ℂ)))
            - ∑ k ∈ Finset.range (p + 1), (-(h * ((Real.log n : ℝ) : ℂ))) ^ k / (k ! : ℂ))‖
        + (‖(N : ℂ) ^ (-c) * emCorr K c N * (eN - PN)‖
          + ‖(N : ℂ) ^ (-c) * eN * (emCorr K (c + h) N - emCorr K c N)‖) :=
        le_trans (norm_add_le _ _) (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ ((N : ℝ) - 1) * (G * ((r * L) ^ (p + 1) * Cp p))
        + (G * ‖emCorr K c N‖ * ((r * L) ^ (p + 1) * Cp p) + G * 3 * corrVar K N r a U) := by
        gcongr
    _ = G * (Cp p * (r * L) ^ (p + 1) * (((N : ℝ) - 1) + ‖emCorr K c N‖) + 3 * corrVar K N r a U) := by
        ring

/-! ## B. The remainder along a horizontal segment, and the `G` certificate. -/

/-- `pochNormSq` is monotone under `|σ| ≤ σs`, `|t| ≤ ts` (negative `σ` allowed). -/
theorem pochNormSq_mono_abs (σ t σs ts : ℝ) (hσ : |σ| ≤ σs) (ht : |t| ≤ ts) :
    ∀ k : ℕ, pochNormSq σ t k ≤ pochNormSq σs ts k := by
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
    have hsq : (σ + k) ^ 2 + t ^ 2 ≤ (σs + k) ^ 2 + ts ^ 2 := by
      have habs : |σ + k| ≤ σs + k := by
        refine le_trans (abs_add_le _ _) ?_
        rw [abs_of_nonneg hk]; linarith
      have h1 : (σ + k) ^ 2 ≤ (σs + k) ^ 2 := by
        rw [← sq_abs (σ + k)]
        exact pow_le_pow_left₀ (abs_nonneg _) habs 2
      have h2 : t ^ 2 ≤ ts ^ 2 := by
        rw [← sq_abs t]; exact pow_le_pow_left₀ (abs_nonneg t) ht 2
      linarith
    exact mul_le_mul ih hsq (by positivity) (le_trans h0 ih)

/-- **The EM remainder along a horizontal segment** `x + i t`, `xlo ≤ x ≤ xhi`, `t ≠ 0`,
    `xlo > -2K` (negative real parts allowed): with `|x| ≤ σs` on the segment,
    `Qr² ≥ Π_{j ≤ 2K} ((σs + j)² + t²)` and `N^(-xlo) ≤ R`,
        ‖ζ(x + i t) − emFinite K (x + i t) N‖ ≤ C_K · Qr · R / N^(2K) / (xlo + 2K). -/
theorem em_remainder_horiz (K N : ℕ) (hK : 1 ≤ K) (hN : 1 ≤ N) (t : ℝ) (ht : t ≠ 0)
    (xlo xhi σs : ℝ) (hpos : 0 < xlo + 2 * K) (hs1 : xhi ≤ σs) (hs2 : -xlo ≤ σs)
    (Qr : ℝ) (hQr0 : 0 ≤ Qr) (hQ : pochNormSq σs t (2 * K + 1) ≤ Qr ^ 2)
    (R : ℝ) (hR : (N : ℝ) ^ (-xlo) ≤ R) :
    ∀ x : ℝ, xlo ≤ x → x ≤ xhi →
      ‖riemannZeta (sOfG x t) - emFinite K (sOfG x t) N‖
        ≤ CK K * Qr * R / (N : ℝ) ^ (2 * K) / (xlo + 2 * K) := by
  intro x hx0 hx1
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs1' : sOfG x t ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp [sOfG] at this
    exact ht this
  have hsre : (sOfG x t).re = x := by simp [sOfG]
  have henc := EMOff.em_zeta_orderK_enclosure_odd_ext K hK (s := sOfG x t)
    (by rw [hsre]; push_cast; linarith) hs1' hN
  rw [hsre] at henc
  refine le_trans henc ?_
  -- the Pochhammer factor
  have hmono := pochNormSq_mono_abs x t σs |t|
    (by rw [abs_le]; constructor <;> linarith) le_rfl (2 * K + 1)
  have hpq : pochNormSq σs |t| (2 * K + 1) = pochNormSq σs t (2 * K + 1) := by
    have : ∀ k, pochNormSq σs |t| k = pochNormSq σs t k := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => simp only [pochNormSq, ih, sq_abs]
    exact this _
  rw [hpq] at hmono
  have hpoch : ‖poch (sOfG x t) (2 * K + 1)‖ ≤ Qr := norm_poch_le x t (2 * K + 1) Qr hQr0 (le_trans hmono hQ)
  -- the power of N
  have hpow : (N : ℝ) ^ (-(x + ((2 * K + 1 : ℕ) : ℝ) - 1)) ≤ R / (N : ℝ) ^ (2 * K) := by
    have e : -(x + ((2 * K + 1 : ℕ) : ℝ) - 1) = -x + (-(((2 * K : ℕ) : ℝ))) := by push_cast; ring
    have hk : (N : ℝ) ^ (-(((2 * K : ℕ) : ℝ))) = ((N : ℝ) ^ (2 * K))⁻¹ := by
      rw [Real.rpow_neg hNR.le, Real.rpow_natCast]
    rw [e, Real.rpow_add hNR, hk, div_eq_mul_inv R]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    refine le_trans ?_ hR
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hden : xlo + 2 * K ≤ x + ((2 * K + 1 : ℕ) : ℝ) - 1 := by push_cast; linarith
  have hCK := CK_nonneg K
  have hpn0 : 0 ≤ (N : ℝ) ^ (-(x + ((2 * K + 1 : ℕ) : ℝ) - 1)) := by positivity
  change CK K * ‖poch (sOfG x t) (2 * K + 1)‖ * (N : ℝ) ^ (-(x + ((2 * K + 1 : ℕ) : ℝ) - 1))
      / (x + ((2 * K + 1 : ℕ) : ℝ) - 1) ≤ _
  have hR0 : 0 ≤ R := le_trans (by positivity) hR
  calc CK K * ‖poch (sOfG x t) (2 * K + 1)‖ * (N : ℝ) ^ (-(x + ((2 * K + 1 : ℕ) : ℝ) - 1))
        / (x + ((2 * K + 1 : ℕ) : ℝ) - 1)
      ≤ CK K * Qr * (R / (N : ℝ) ^ (2 * K)) / (xlo + 2 * K) := by
        gcongr
    _ = CK K * Qr * R / (N : ℝ) ^ (2 * K) / (xlo + 2 * K) := by ring

/-- **The `G` certificate**: for `σ ≥ xm = (a - b)/q` with `a ≤ b` (so `xm ≤ 0`) and
    `Gd^q N^b ≤ Gn^q N^a`, every `‖n^(-(σ + i t))‖`, `1 ≤ n ≤ N`, is at most `Gn/Gd`. -/
theorem natCpow_norm_le_of_pow (N : ℕ) (hN : 1 ≤ N) (a b q : ℕ) (hq : 1 ≤ q) (Gn Gd : ℕ)
    (hGd : 0 < Gd) (h : Gd ^ q * N ^ b ≤ Gn ^ q * N ^ a) (hab : a ≤ b) (σ t : ℝ)
    (hσ : ((a : ℝ) - b) / q ≤ σ) :
    ∀ n : ℕ, 1 ≤ n → n ≤ N → ‖(n : ℂ) ^ (-sOfG σ t)‖ ≤ (Gn : ℝ) / Gd := by
  intro n hn1 hnN
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hxm : ((a : ℝ) - b) / q ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ hqR.le
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl, Complex.norm_cpow_eq_rpow_re_of_pos hnpos,
    Complex.neg_re]
  have hre : (sOfG σ t).re = σ := by simp [sOfG]
  rw [hre]
  calc (n : ℝ) ^ (-σ) ≤ (n : ℝ) ^ (-(((a : ℝ) - b) / q)) :=
        Real.rpow_le_rpow_of_exponent_le hn1R (by linarith)
    _ ≤ (N : ℝ) ^ (-(((a : ℝ) - b) / q)) :=
        Real.rpow_le_rpow hnpos.le (by exact_mod_cast hnN) (by linarith)
    _ ≤ (Gn : ℝ) / Gd := rpow_neg_le_of_pow N hN a b q hq Gn Gd hGd h

/-- For `σ ≥ 0` the `G` factor is `1`. -/
theorem natCpow_norm_le_one (N : ℕ) (σ t : ℝ) (hσ : 0 ≤ σ) :
    ∀ n : ℕ, 1 ≤ n → n ≤ N → ‖(n : ℂ) ^ (-sOfG σ t)‖ ≤ 1 := by
  intro n hn1 _
  exact norm_natCpow_neg_le_one n hn1 (sOfG σ t) (by simp [sOfG, hσ])

/-! ## C. The kernel check of a piece. -/

/-- The octant projection `α Re w + β Im w`. -/
noncomputable def octXv (α β : ℤ) (w : ℂ) : ℝ := (α : ℝ) * w.re + (β : ℝ) * w.im

theorem octX_eq_octXv (kk : ℤ) (w : ℂ) :
    ArgHoriz.octX kk w = octXv (ArgHoriz.octA kk) (ArgHoriz.octB kk) w := rfl

/-- `|α Re w + β Im w| ≤ (|α| + |β|) ‖w‖`. -/
theorem abs_octXv_le (α β : ℤ) (w : ℂ) : |octXv α β w| ≤ (|(α : ℝ)| + |(β : ℝ)|) * ‖w‖ := by
  unfold octXv
  have h1 := Complex.abs_re_le_norm w
  have h2 := Complex.abs_im_le_norm w
  calc |(α : ℝ) * w.re + (β : ℝ) * w.im| ≤ |(α : ℝ) * w.re| + |(β : ℝ) * w.im| := abs_add_le _ _
    _ = |(α : ℝ)| * |w.re| + |(β : ℝ)| * |w.im| := by rw [abs_mul, abs_mul]
    _ ≤ |(α : ℝ)| * ‖w‖ + |(β : ℝ)| * ‖w‖ := by gcongr
    _ = (|(α : ℝ)| + |(β : ℝ)|) * ‖w‖ := by ring

/-- The projection is additive. -/
theorem octXv_add (α β : ℤ) (v w : ℂ) : octXv α β (v + w) = octXv α β v + octXv α β w := by
  unfold octXv; simp only [Complex.add_re, Complex.add_im]; ring

/-- The projection is `ℝ`-linear. -/
theorem octXv_ofReal_mul (α β : ℤ) (a : ℝ) (w : ℂ) : octXv α β ((a : ℂ) * w) = a * octXv α β w := by
  unfold octXv; simp only [Complex.re_ofReal_mul, Complex.im_ofReal_mul]; ring

theorem octXv_sum (α β : ℤ) (s : Finset ℕ) (f : ℕ → ℝ) (W : ℕ → ℂ) :
    octXv α β (∑ k ∈ s, (f k : ℂ) * W k) = ∑ k ∈ s, f k * octXv α β (W k) := by
  unfold octXv
  rw [Complex.re_sum, Complex.im_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Complex.re_ofReal_mul, Complex.im_ofReal_mul]; ring

/-- Lower bound, scaled, of the projection over a ball `d = (C_re, C_im, R_re, R_im)`. -/
def octLo (α β : ℤ) (d : ℤ × ℤ × ℤ × ℤ) : ℤ :=
  α * d.1 + β * d.2.1 - ((α.natAbs : ℤ) * d.2.2.1 + (β.natAbs : ℤ) * d.2.2.2)

/-- Upper bound, scaled, of the absolute projection over a ball. -/
def octUp (α β : ℤ) (d : ℤ × ℤ × ℤ × ℤ) : ℤ :=
  ((α * d.1 + β * d.2.1).natAbs : ℤ) + (α.natAbs : ℤ) * d.2.2.1 + (β.natAbs : ℤ) * d.2.2.2

theorem natAbs_cast (α : ℤ) : (((α.natAbs : ℤ)) : ℝ) = |(α : ℝ)| := by
  rw [Int.natCast_natAbs, Int.cast_abs]

/-- A ball of `W` (scaled by `S > 0`) gives the two bounds of its projection. -/
theorem oct_ball (α β : ℤ) (W : ℂ) (S : ℝ) (hS : 0 < S) (d : ℤ × ℤ × ℤ × ℤ)
    (hre : |W.re * S - (d.1 : ℝ)| ≤ (d.2.2.1 : ℝ)) (him : |W.im * S - (d.2.1 : ℝ)| ≤ (d.2.2.2 : ℝ)) :
    (octLo α β d : ℝ) ≤ octXv α β W * S ∧ |octXv α β W| * S ≤ (octUp α β d : ℝ) := by
  set u := W.re * S - (d.1 : ℝ) with hu
  set v := W.im * S - (d.2.1 : ℝ) with hv
  have e : octXv α β W * S = ((α : ℝ) * d.1 + (β : ℝ) * d.2.1) + ((α : ℝ) * u + (β : ℝ) * v) := by
    rw [hu, hv]; unfold octXv; ring
  have herr : |(α : ℝ) * u + (β : ℝ) * v| ≤ |(α : ℝ)| * d.2.2.1 + |(β : ℝ)| * d.2.2.2 := by
    calc |(α : ℝ) * u + (β : ℝ) * v| ≤ |(α : ℝ) * u| + |(β : ℝ) * v| := abs_add_le _ _
      _ = |(α : ℝ)| * |u| + |(β : ℝ)| * |v| := by rw [abs_mul, abs_mul]
      _ ≤ |(α : ℝ)| * d.2.2.1 + |(β : ℝ)| * d.2.2.2 := by gcongr
  have hlo : (octLo α β d : ℝ) = ((α : ℝ) * d.1 + (β : ℝ) * d.2.1) - (|(α : ℝ)| * d.2.2.1 + |(β : ℝ)| * d.2.2.2) := by
    simp only [octLo]; push_cast [natAbs_cast]; ring
  have hup : (octUp α β d : ℝ) = |(α : ℝ) * d.1 + (β : ℝ) * d.2.1| + |(α : ℝ)| * d.2.2.1 + |(β : ℝ)| * d.2.2.2 := by
    simp only [octUp]
    have h1 : (((((α * d.1 + β * d.2.1).natAbs : ℕ) : ℤ)) : ℝ) = |(α : ℝ) * d.1 + (β : ℝ) * d.2.1| := by
      rw [natAbs_cast]; push_cast; ring_nf
    push_cast [natAbs_cast] at h1 ⊢
    rw [h1]
  constructor
  · rw [hlo, e]
    have := neg_abs_le ((α : ℝ) * u + (β : ℝ) * v)
    linarith
  · have hm : |octXv α β W| * S = |octXv α β W * S| := by rw [abs_mul, abs_of_pos hS]
    rw [hup, hm, e]
    have := abs_add_le ((α : ℝ) * d.1 + (β : ℝ) * d.2.1) ((α : ℝ) * u + (β : ℝ) * v)
    linarith

/-- `Σ_{j ≥ k} octUp(W_j) rn^j rd^(p-j) (p!/j!)` over the paired accumulator lists. -/
def sumOct (α β BreN BimN BD : ℤ) (rn rd p : ℕ) : ℕ → List Acc → List Acc → ℤ
  | k, x1 :: xs1, x2 :: xs2 =>
    octUp α β (wData BreN BimN BD x1 x2) * (rn : ℤ) ^ k * (rd : ℤ) ^ (p - k) * ((p ! / k ! : ℕ) : ℤ)
      + sumOct α β BreN BimN BD rn rd p (k + 1) xs1 xs2
  | _, _, _ => 0

theorem sumOct_sound (P : ℕ) (f1 f2 : ℕ → ℂ) (B : ℂ) (α β BreN BimN BD : ℤ) (hBD : (0 : ℝ) < BD)
    (hBre : B.re = (BreN : ℝ) / BD) (hBim : B.im = (BimN : ℝ) / BD) (rn rd p : ℕ) :
    ∀ (m k : ℕ) (xs1 xs2 : List Acc), xs1.length = m → xs2.length = m →
      AccsOK P f1 k xs1 → AccsOK P f2 k xs2 →
      ∑ j ∈ Finset.Ico k (k + m), |octXv α β (f1 j + (f2 j - f1 j) * B)| * (2 ^ P * BD)
          * ((rn : ℝ) ^ j * (rd : ℝ) ^ (p - j) * ((p ! / j ! : ℕ) : ℝ))
        ≤ (sumOct α β BreN BimN BD rn rd p k xs1 xs2 : ℝ) := by
  have hS : (0 : ℝ) < 2 ^ P * BD := by positivity
  intro m
  induction m with
  | zero =>
    intro k xs1 xs2 hl1 hl2 _ _
    rw [List.length_eq_zero_iff] at hl1 hl2
    subst hl1; subst hl2
    simp [sumOct]
  | succ m ih =>
    intro k xs1 xs2 hl1 hl2 hA1 hA2
    match xs1, xs2, hl1, hl2, hA1, hA2 with
    | x1 :: ys1, x2 :: ys2, hl1, hl2, hA1, hA2 =>
      obtain ⟨hx1, hy1⟩ := hA1
      obtain ⟨hx2, hy2⟩ := hA2
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl1 hl2
      have hrec := ih (k + 1) ys1 ys2 hl1 hl2 hy1 hy2
      have hb := wball_sound P (f1 k) (f2 k) x1 x2 hx1 hx2 BreN BimN BD hBD B hBre hBim
      have hre : |(f1 k + (f2 k - f1 k) * B).re * (2 ^ P * BD) - ((wData BreN BimN BD x1 x2).1 : ℝ)|
          ≤ ((wData BreN BimN BD x1 x2).2.2.1 : ℝ) := by rw [← mul_assoc]; exact hb.1
      have him : |(f1 k + (f2 k - f1 k) * B).im * (2 ^ P * BD) - ((wData BreN BimN BD x1 x2).2.1 : ℝ)|
          ≤ ((wData BreN BimN BD x1 x2).2.2.2 : ℝ) := by rw [← mul_assoc]; exact hb.2
      have hu := (oct_ball α β (f1 k + (f2 k - f1 k) * B) (2 ^ P * BD) hS _ hre him).2
      have hfac : (0 : ℝ) ≤ (rn : ℝ) ^ k * (rd : ℝ) ^ (p - k) * ((p ! / k ! : ℕ) : ℝ) := by positivity
      rw [show k + (m + 1) = (k + 1) + m by ring, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
      have hs : (sumOct α β BreN BimN BD rn rd p k (x1 :: ys1) (x2 :: ys2) : ℝ)
          = (octUp α β (wData BreN BimN BD x1 x2) : ℝ) * ((rn : ℝ) ^ k * (rd : ℝ) ^ (p - k)
              * ((p ! / k ! : ℕ) : ℝ)) + (sumOct α β BreN BimN BD rn rd p (k + 1) ys1 ys2 : ℝ) := by
        simp only [sumOct, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast]; ring
      rw [hs]
      have := mul_le_mul_of_nonneg_right hu hfac
      linarith

/-- The right side of the piece check (scaled by `2^P BD rd^p p! FD`). -/
def octRHS (c : Cfg) (o : OCfg) (K N p : ℕ) (kk : ℤ) (ys1 ys2 : List Acc) (rn rd FN FD : ℕ) : ℤ :=
  sumOct (ArgHoriz.octA kk) (ArgHoriz.octB kk)
      (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).1
      (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).2.1
      (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).2.2 rn rd p 1 ys1 ys2 * FD
    + (((ArgHoriz.octA kk).natAbs : ℤ) + ((ArgHoriz.octB kk).natAbs : ℤ)) * FN * 2 ^ c.P
      * (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).2.2 * (rd : ℤ) ^ p * ((p ! : ℕ) : ℤ)

/-- The left side of the piece check. -/
def octLHS (c : Cfg) (o : OCfg) (K N p : ℕ) (kk : ℤ) (x1 x2 : Acc) (rd FD : ℕ) : ℤ :=
  octLo (ArgHoriz.octA kk) (ArgHoriz.octB kk)
      (wData (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).1
        (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).2.1
        (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).2.2 x1 x2)
    * ((rd : ℤ) ^ p * ((p ! : ℕ) : ℤ) * FD)

/-- **The kernel piece check.**  `xs1`, `xs2`: the `p + 1` accumulators after `N - 1` and `N` terms
    at `c = σ + i t`; octant `kk` (integer vector `(α, β) = (octA kk, octB kk)`); `r = rn/rd`;
    `F = FN/FD`.  Checks `Σ_{k=1}^p |octX (W_k)| r^k/k! + (|α| + |β|) F < octX (W_0)`, everything
    multiplied through by `2^P BD rd^p p! FD`. -/
def checkOct (c : Cfg) (o : OCfg) (K N p : ℕ) (xs1 xs2 : List Acc) (rn rd FN FD : ℕ) (kk : ℤ) : Bool :=
  match xs1, xs2 with
  | x1 :: ys1, x2 :: ys2 =>
    Nat.ble 1 K && Nat.ble K 6 && Nat.ble 2 N && Nat.ble 1 rd && Nat.ble 1 FD && Nat.ble 1 o.q &&
      Nat.ble 1 c.tn && Nat.beq ys1.length p && Nat.beq ys2.length p &&
      decide (octRHS c o K N p kk ys1 ys2 rn rd FN FD < octLHS c o K N p kk x1 x2 rd FD)
  | _, _ => false

set_option maxHeartbeats 2000000 in
theorem checkOct_sound (c : Cfg) (o : OCfg) (σ t : ℝ) (hσ : σ = ((o.a : ℝ) - o.b) / o.q)
    (ht : t = (c.tn : ℝ) / 2 ^ c.tq) (K N p : ℕ) (xs1 xs2 : List Acc) (rn rd FN FD : ℕ) (kk : ℤ)
    (h1 : AccsOK c.P (fun k => psumK σ t k (N - 1)) 0 xs1)
    (h2 : AccsOK c.P (fun k => psumK σ t k N) 0 xs2)
    (hc : checkOct c o K N p xs1 xs2 rn rd FN FD kk = true) :
    ∑ k ∈ Finset.Ico 1 (p + 1), |ArgHoriz.octX kk (Wk K N (sOfG σ t) k)| * ((rn : ℝ) / rd) ^ k
        / (k ! : ℝ)
      + (|((ArgHoriz.octA kk : ℤ) : ℝ)| + |((ArgHoriz.octB kk : ℤ) : ℝ)|) * ((FN : ℝ) / FD)
      < ArgHoriz.octX kk (Wk K N (sOfG σ t) 0) := by
  match xs1, xs2, h1, h2, hc with
  | x1 :: ys1, x2 :: ys2, h1, h2, hc =>
    simp only [checkOct, Bool.and_eq_true, Nat.ble_eq, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hK1, hK6⟩, hN2⟩, hrd⟩, hFD⟩, hq1⟩, htn1⟩, hl1⟩, hl2⟩, hmainZ⟩ := hc
    have hl1' : ys1.length = p := Nat.eq_of_beq_eq_true hl1
    have hl2' : ys2.length = p := Nat.eq_of_beq_eq_true hl2
    obtain ⟨hx1, hy1⟩ := h1
    obtain ⟨hx2, hy2⟩ := h2
    set u : ℕ := 2 ^ c.tq with hudef
    have hu : 0 < u := Nat.two_pow_pos _
    have huR : (0 : ℝ) < u := by exact_mod_cast hu
    have ht' : t = (c.tn : ℝ) / u := by rw [ht, hudef]; push_cast; ring
    have hσ' : σ = (((o.a : ℤ) - o.b : ℤ) : ℝ) / o.q := by rw [hσ]; push_cast; ring
    obtain ⟨hcre, hcim⟩ := corr_eqG K ((o.a : ℤ) - o.b) o.q u c.tn N hK1 hK6 (by omega) hu
      (by omega) (by omega) σ t hσ' ht'
    set cd := corrDataG K ((o.a : ℤ) - o.b) o.q u c.tn N with hcd
    have hqR : (0 : ℝ) < o.q := by exact_mod_cast (show 0 < o.q by omega)
    have htnR : (0 : ℝ) < c.tn := by exact_mod_cast (show 0 < c.tn by omega)
    have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hBDpos : (0 : ℝ) < (cd.2.2 : ℝ) := by
      have e : (cd.2.2 : ℝ) = 2 * (((((o.a : ℤ) - o.b : ℤ) : ℝ) - o.q) ^ 2 * (u : ℝ) ^ 2
          + (c.tn : ℝ) ^ 2 * (o.q : ℝ) ^ 2) * ((ArbEcon.OrderK.Lbeta : ℝ) * ((o.q : ℝ) * u * N) ^ (2 * K - 1)) := by
        simp only [hcd, corrDataG]; push_cast; ring
      rw [e]
      have hL : (0 : ℝ) < (ArbEcon.OrderK.Lbeta : ℝ) := by norm_num [ArbEcon.OrderK.Lbeta]
      positivity
    set B := emCorr K (sOfG σ t) N with hB
    have hBre : B.re = (cd.1 : ℝ) / cd.2.2 := by rw [← hcre]; exact (emCorr_re_im K σ t N).1
    have hBim : B.im = (cd.2.1 : ℝ) / cd.2.2 := by rw [← hcim]; exact (emCorr_re_im K σ t N).2
    have hW : ∀ k, Wk K N (sOfG σ t) k = psumK σ t k (N - 1) + (psumK σ t k N - psumK σ t k (N - 1)) * B :=
      fun k => Wk_eq_psumK K N (by omega) σ t k
    simp only [hW, octX_eq_octXv]
    set α := ArgHoriz.octA kk with hα
    set β := ArgHoriz.octB kk with hβ
    set S : ℝ := 2 ^ c.P * cd.2.2 with hS
    have hP : (0 : ℝ) < 2 ^ c.P := by positivity
    have hSpos : 0 < S := by positivity
    -- the k = 0 ball
    have hb0 := wball_sound c.P (psumK σ t 0 (N - 1)) (psumK σ t 0 N) x1 x2 hx1 hx2 cd.1 cd.2.1 cd.2.2
      hBDpos B hBre hBim
    set d0 := wData cd.1 cd.2.1 cd.2.2 x1 x2 with hd0
    set W0 := psumK σ t 0 (N - 1) + (psumK σ t 0 N - psumK σ t 0 (N - 1)) * B with hW0
    have hre0 : |W0.re * S - (d0.1 : ℝ)| ≤ (d0.2.2.1 : ℝ) := by rw [hS, ← mul_assoc]; exact hb0.1
    have him0 : |W0.im * S - (d0.2.1 : ℝ)| ≤ (d0.2.2.2 : ℝ) := by rw [hS, ← mul_assoc]; exact hb0.2
    have hlo0 := (oct_ball α β W0 S hSpos d0 hre0 him0).1
    -- the k ≥ 1 sum
    have hsum := sumOct_sound c.P (fun k => psumK σ t k (N - 1)) (fun k => psumK σ t k N) B α β cd.1
      cd.2.1 cd.2.2 hBDpos hBre hBim rn rd p p 1 ys1 ys2 hl1' hl2' hy1 hy2
    rw [show 1 + p = p + 1 by ring] at hsum
    set Msum : ℝ := (sumOct α β cd.1 cd.2.1 cd.2.2 rn rd p 1 ys1 ys2 : ℝ) with hMsum
    set T : ℝ := (rd : ℝ) ^ p * ((p ! : ℕ) : ℝ) * FD with hT
    have hrdR : (0 : ℝ) < rd := by exact_mod_cast (show 0 < rd by omega)
    have hFDR : (0 : ℝ) < FD := by exact_mod_cast (show 0 < FD by omega)
    have hpf : (0 : ℝ) < ((p ! : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos p
    have hTpos : 0 < T := by positivity
    set AB : ℝ := |(α : ℝ)| + |(β : ℝ)| with hAB
    have hRHScast : ((octRHS c o K N p kk ys1 ys2 rn rd FN FD : ℤ) : ℝ)
        = Msum * FD + AB * (FN : ℝ) * S * (rd : ℝ) ^ p * ((p ! : ℕ) : ℝ) := by
      simp only [octRHS, hMsum, hS, hAB, hcd, hudef, hα, hβ]
      push_cast [natAbs_cast]
      ring
    have hLHScast : ((octLHS c o K N p kk x1 x2 rd FD : ℤ) : ℝ) = (octLo α β d0 : ℝ) * T := by
      simp only [octLHS, hT, hd0, hcd, hudef, hα, hβ]
      push_cast
      ring
    have hmainR : Msum * FD + AB * (FN : ℝ) * S * (rd : ℝ) ^ p * ((p ! : ℕ) : ℝ)
        < (octLo α β d0 : ℝ) * T := by
      rw [← hRHScast, ← hLHScast]; exact_mod_cast hmainZ
    have h2' := mul_le_mul_of_nonneg_right hlo0 hTpos.le
    have h1' := mul_le_mul_of_nonneg_right hsum hFDR.le
    have hkey : (∑ j ∈ Finset.Ico 1 (p + 1),
          |octXv α β (psumK σ t j (N - 1) + (psumK σ t j N - psumK σ t j (N - 1)) * B)| * S
            * ((rn : ℝ) ^ j * (rd : ℝ) ^ (p - j) * ((p ! / j ! : ℕ) : ℝ))) * FD
        + AB * (FN : ℝ) * S * (rd : ℝ) ^ p * ((p ! : ℕ) : ℝ) < octXv α β W0 * S * T := by
      have : (∑ j ∈ Finset.Ico 1 (p + 1),
          |octXv α β (psumK σ t j (N - 1) + (psumK σ t j N - psumK σ t j (N - 1)) * B)| * (2 ^ c.P * cd.2.2)
            * ((rn : ℝ) ^ j * (rd : ℝ) ^ (p - j) * ((p ! / j ! : ℕ) : ℝ))) * FD ≤ Msum * FD := h1'
      rw [← hS] at this
      linarith
    have hterm : ∀ j ∈ Finset.Ico 1 (p + 1),
        |octXv α β (psumK σ t j (N - 1) + (psumK σ t j N - psumK σ t j (N - 1)) * B)| * S
          * ((rn : ℝ) ^ j * (rd : ℝ) ^ (p - j) * ((p ! / j ! : ℕ) : ℝ)) * FD
        = (|octXv α β (psumK σ t j (N - 1) + (psumK σ t j N - psumK σ t j (N - 1)) * B)|
            * ((rn : ℝ) / rd) ^ j / (j ! : ℝ)) * (S * T) := by
      intro j hj
      have hjp : j ≤ p := by have := Finset.mem_Ico.mp hj; omega
      have hdvd : j ! ∣ p ! := Nat.factorial_dvd_factorial hjp
      have hjf : (0 : ℝ) < (j ! : ℝ) := by exact_mod_cast Nat.factorial_pos j
      have hcast : ((p ! / j ! : ℕ) : ℝ) = ((p ! : ℕ) : ℝ) / (j ! : ℝ) := Nat.cast_div hdvd (ne_of_gt hjf)
      have hpow : (rd : ℝ) ^ p = (rd : ℝ) ^ (p - j) * (rd : ℝ) ^ j := by
        rw [← pow_add]; congr 1; omega
      rw [hcast, hT, hpow, div_pow]
      field_simp
    rw [Finset.sum_mul] at hkey
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul] at hkey
    have hST : 0 < S * T := by positivity
    have e3 : AB * (FN : ℝ) * S * (rd : ℝ) ^ p * ((p ! : ℕ) : ℝ) = AB * ((FN : ℝ) / FD) * (S * T) := by
      rw [hT]; field_simp
    rw [e3, ← add_mul, show octXv α β W0 * S * T = octXv α β W0 * (S * T) by ring] at hkey
    exact lt_of_mul_lt_mul_right hkey hST.le

/-! ## D. The piece. -/

/-- `‖c + j‖ ≤ U` for all `j < 2K` from the single corner inequality (any sign of `σc`). -/
theorem norm_add_nat_le_abs (K : ℕ) (σc tc U : ℝ) (hU0 : 0 ≤ U)
    (hU : (|σc| + (2 * K - 1 : ℝ)) ^ 2 + tc ^ 2 ≤ U ^ 2) :
    ∀ j, j < 2 * K → ‖sOfG σc tc + j‖ ≤ U := by
  intro j hj
  have hjR : (j : ℝ) ≤ 2 * K - 1 := by
    have : j + 1 ≤ 2 * K := hj
    have : ((j + 1 : ℕ) : ℝ) ≤ ((2 * K : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this; linarith
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hre : (sOfG σc tc + j).re = σc + j := by simp [sOfG]
  have him : (sOfG σc tc + j).im = tc := by simp [sOfG]
  have hsq : ‖sOfG σc tc + j‖ ^ 2 ≤ U ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    have habs : |σc + j| ≤ |σc| + (2 * K - 1 : ℝ) := by
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_of_nonneg hj0]; linarith
    have h1 : (σc + j) * (σc + j) ≤ (|σc| + (2 * K - 1 : ℝ)) ^ 2 := by
      rw [← sq, ← sq_abs (σc + j)]
      exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    nlinarith
  exact le_of_pow_le_pow_left₀ (by norm_num) hU0 hsq

/-- **THE PIECE.**  One evaluator run at the center `c = σc + i tc` (invariants after `N - 1` and
    `N` terms), one kernel check `checkOct … = true` at radius `r = rn/rd` and octant `kk`, and scalar
    side conditions: the Taylor radius `R ≥ r` with `R L ≤ 1` (`L ≥ log N`), `a + R ≤ ‖c - 1‖`,
    `‖c + j‖ ≤ U`, the `G` bound on `‖n^(-c)‖`, a remainder bound `E` on the piece, and the budget
    `G · (Taylor error at R) + E ≤ FN/FD`.  Then for EVERY real `x` with `|x - σc| ≤ r`,
    `0 < ArgHoriz.octX kk (ζ(x + i tc))`. -/
theorem piece_octX_pos (c : Cfg) (o : OCfg) (σc tc : ℝ) (hσ : σc = ((o.a : ℝ) - o.b) / o.q)
    (ht : tc = (c.tn : ℝ) / 2 ^ c.tq) (K N p : ℕ) (hN : 2 ≤ N) (s1 s2 : StO)
    (h1 : InvO c σc tc (N - 1) s1) (h2 : InvO c σc tc N s2) (rn rd FN FD : ℕ) (kk : ℤ)
    (hchk : checkOct c o K N p s1.acc s2.acc rn rd FN FD kk = true)
    (R L a U G E : ℝ) (hrR : (rn : ℝ) / rd ≤ R) (hL : (s2.lhi : ℝ) ≤ L * 2 ^ c.P) (hRL : R * L ≤ 1)
    (ha : 0 < a) (hA : (a + R) ^ 2 ≤ (σc - 1) ^ 2 + tc ^ 2)
    (hU0 : 0 ≤ U) (hU : (|σc| + (2 * K - 1 : ℝ)) ^ 2 + tc ^ 2 ≤ U ^ 2)
    (hG : ∀ n : ℕ, 1 ≤ n → n ≤ N → ‖(n : ℂ) ^ (-sOfG σc tc)‖ ≤ G)
    (hE : ∀ x : ℝ, |x - σc| ≤ (rn : ℝ) / rd →
      ‖riemannZeta (sOfG x tc) - emFinite K (sOfG x tc) N‖ ≤ E)
    (hbudget : G * (Cp p * (R * L) ^ (p + 1) * (((N : ℝ) - 1) + emcB K N a U)
        + 3 * corrVar K N R a U) + E ≤ (FN : ℝ) / FD) :
    ∀ x : ℝ, |x - σc| ≤ (rn : ℝ) / rd →
      0 < ArgHoriz.octX kk (riemannZeta ((x : ℂ) + (tc : ℂ) * I)) := by
  intro x hx
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have hmain := checkOct_sound c o σc tc hσ ht K N p s1.acc s2.acc rn rd FN FD kk h1.2.2.2.2
    h2.2.2.2.2 hchk
  -- log N ≤ L
  have hlogN : Real.log N ≤ L := by
    have h2l := h2.2.2.2.1
    have : Real.log N * 2 ^ c.P ≤ L * 2 ^ c.P := le_trans h2l hL
    exact le_of_mul_le_mul_right this hP
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL0 : 0 ≤ L := le_trans (Real.log_nonneg hN1) hlogN
  set cc : ℂ := sOfG σc tc with hcc
  set h : ℂ := ((x - σc : ℝ) : ℂ) with hh
  have hs : cc + h = (x : ℂ) + (tc : ℂ) * I := by
    rw [hcc, hh]; simp only [sOfG]; push_cast; ring
  have hr0 : (0 : ℝ) ≤ (rn : ℝ) / rd := le_trans (abs_nonneg _) hx
  have hR0 : 0 ≤ R := le_trans hr0 hrR
  have hr : ‖h‖ ≤ R := by
    rw [hh, Complex.norm_real, Real.norm_eq_abs]; exact le_trans hx hrR
  -- a + R ≤ ‖c - 1‖
  have hc1sq : ‖cc - 1‖ ^ 2 = (σc - 1) ^ 2 + tc ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hcc]
    simp only [sOfG, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.one_re, Complex.one_im]
    ring
  have hc1 : a + R ≤ ‖cc - 1‖ :=
    le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (norm_nonneg _) (by rw [hc1sq]; exact hA)
  have hnc : a ≤ ‖cc - 1‖ := by linarith
  have hns : a ≤ ‖cc + h - 1‖ := by
    have : ‖cc - 1‖ ≤ ‖cc + h - 1‖ + ‖h‖ := by
      calc ‖cc - 1‖ = ‖(cc + h - 1) + (-h)‖ := by congr 1; ring
        _ ≤ ‖cc + h - 1‖ + ‖-h‖ := norm_add_le _ _
        _ = ‖cc + h - 1‖ + ‖h‖ := by rw [norm_neg]
    linarith
  have hUj := norm_add_nat_le_abs K σc tc U hU0 hU
  have hG0 : 0 ≤ G := le_trans (norm_nonneg _) (hG 1 le_rfl (by omega))
  -- the Taylor model at radius R
  have hT := emFinite_taylor_le_G K N p (by omega) cc h R L a U G hG hr hlogN hRL ha hnc hns hU0 hUj
  rw [hs] at hT
  have hemc := norm_emCorr_le_norm K N (by omega) cc a U ha hnc hU0 hUj
  have hTe : G * taylorErr K N p cc R L a U
      ≤ G * (Cp p * (R * L) ^ (p + 1) * (((N : ℝ) - 1) + emcB K N a U) + 3 * corrVar K N R a U) := by
    apply mul_le_mul_of_nonneg_left _ hG0
    unfold taylorErr
    have hcp := Cp_nonneg p
    have hRL0 : 0 ≤ R * L := mul_nonneg hR0 hL0
    have : Cp p * (R * L) ^ (p + 1) * (((N : ℝ) - 1) + ‖emCorr K cc N‖)
        ≤ Cp p * (R * L) ^ (p + 1) * (((N : ℝ) - 1) + emcB K N a U) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    linarith
  have hEx := hE x hx
  have hsx : sOfG x tc = (x : ℂ) + (tc : ℂ) * I := rfl
  rw [hsx] at hEx
  set Pp := ∑ k ∈ Finset.range (p + 1), h ^ k * ((-1) ^ k / (k ! : ℂ) * Wk K N cc k) with hPp
  have herr : ‖riemannZeta ((x : ℂ) + (tc : ℂ) * I) - Pp‖ ≤ (FN : ℝ) / FD := by
    have := norm_sub_le_norm_sub_add_norm_sub (riemannZeta ((x : ℂ) + (tc : ℂ) * I))
      (emFinite K ((x : ℂ) + (tc : ℂ) * I) N) Pp
    linarith
  -- the octant projection of the Taylor polynomial (h is real)
  set α := ArgHoriz.octA kk with hα
  set β := ArgHoriz.octB kk with hβ
  have hPpv : Pp = ∑ k ∈ Finset.range (p + 1),
      ((((x - σc) ^ k * ((-1) ^ k / (k ! : ℝ)) : ℝ)) : ℂ) * Wk K N cc k := by
    rw [hPp]
    apply Finset.sum_congr rfl
    intro k _
    rw [hh]; push_cast; ring
  have hoctP : octXv α β Pp = ∑ k ∈ Finset.range (p + 1),
      ((x - σc) ^ k * ((-1) ^ k / (k ! : ℝ))) * octXv α β (Wk K N cc k) := by
    rw [hPpv, octXv_sum]
  have hlow : octXv α β (Wk K N cc 0)
      - ∑ k ∈ Finset.Ico 1 (p + 1), |octXv α β (Wk K N cc k)| * ((rn : ℝ) / rd) ^ k / (k ! : ℝ)
      ≤ octXv α β Pp := by
    rw [hoctP, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < p + 1)]
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul]
    have hrest : -(∑ k ∈ Finset.Ico 1 (p + 1), |octXv α β (Wk K N cc k)| * ((rn : ℝ) / rd) ^ k
          / (k ! : ℝ))
        ≤ ∑ k ∈ Finset.Ico 1 (p + 1), (x - σc) ^ k * ((-1) ^ k / (k ! : ℝ)) * octXv α β (Wk K N cc k) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_le_sum
      intro k _
      have hF : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos _
      have habs : |(x - σc) ^ k * ((-1) ^ k / (k ! : ℝ)) * octXv α β (Wk K N cc k)|
          ≤ |octXv α β (Wk K N cc k)| * ((rn : ℝ) / rd) ^ k / (k ! : ℝ) := by
        rw [abs_mul, abs_mul, abs_div, abs_pow, abs_pow, abs_neg, abs_one, one_pow,
          abs_of_pos hF]
        have hpk : |x - σc| ^ k ≤ ((rn : ℝ) / rd) ^ k := pow_le_pow_left₀ (abs_nonneg _) hx k
        calc |x - σc| ^ k * (1 / (k ! : ℝ)) * |octXv α β (Wk K N cc k)|
            ≤ ((rn : ℝ) / rd) ^ k * (1 / (k ! : ℝ)) * |octXv α β (Wk K N cc k)| := by gcongr
          _ = |octXv α β (Wk K N cc k)| * ((rn : ℝ) / rd) ^ k / (k ! : ℝ) := by ring
      have := neg_abs_le ((x - σc) ^ k * ((-1) ^ k / (k ! : ℝ)) * octXv α β (Wk K N cc k))
      linarith
    linarith
  -- combine
  have hsplit : octXv α β (riemannZeta ((x : ℂ) + (tc : ℂ) * I))
      = octXv α β Pp + octXv α β (riemannZeta ((x : ℂ) + (tc : ℂ) * I) - Pp) := by
    rw [← octXv_add]; congr 1; ring
  have hproj := abs_octXv_le α β (riemannZeta ((x : ℂ) + (tc : ℂ) * I) - Pp)
  have hAB0 : 0 ≤ |(α : ℝ)| + |(β : ℝ)| := by positivity
  have hprojF : |octXv α β (riemannZeta ((x : ℂ) + (tc : ℂ) * I) - Pp)|
      ≤ (|(α : ℝ)| + |(β : ℝ)|) * ((FN : ℝ) / FD) :=
    le_trans hproj (mul_le_mul_of_nonneg_left herr hAB0)
  have hmain' : ∑ k ∈ Finset.Ico 1 (p + 1), |octXv α β (Wk K N cc k)| * ((rn : ℝ) / rd) ^ k
        / (k ! : ℝ) + (|(α : ℝ)| + |(β : ℝ)|) * ((FN : ℝ) / FD) < octXv α β (Wk K N cc 0) := by
    simpa only [octX_eq_octXv] using hmain
  rw [octX_eq_octXv, hsplit]
  have := neg_abs_le (octXv α β (riemannZeta ((x : ℂ) + (tc : ℂ) * I) - Pp))
  linarith

/-! ## E. Helpers for the generated certificates. -/

/-- A point of `[a, b]` (either order) is within `r` of `σ` when both ends are. -/
theorem abs_sub_le_of_mem_uIcc {x a b σ r : ℝ} (hx : x ∈ Set.uIcc a b) (ha : |a - σ| ≤ r)
    (hb : |b - σ| ≤ r) : |x - σ| ≤ r := by
  rw [abs_le] at ha hb ⊢
  rcases Set.mem_uIcc.mp hx with h | h <;> constructor <;> linarith [h.1, h.2]

/-- `corrVar` is monotone in the radius. -/
theorem corrVar_mono (K N : ℕ) (r R a U : ℝ) (hr0 : 0 ≤ r) (hrR : r ≤ R) (hU0 : 0 ≤ U) :
    corrVar K N r a U ≤ corrVar K N R a U := by
  unfold corrVar
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  apply add_le_add
  · have ha2 : 0 ≤ a ^ 2 := sq_nonneg a
    gcongr
  · apply Finset.sum_le_sum
    intro i _
    have hF : (0 : ℝ) < ((i + 2)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hb : 0 ≤ |(bernoulli (i + 2) : ℝ)| := abs_nonneg _
    have hpow : (U + r) ^ (i + 1) ≤ (U + R) ^ (i + 1) := pow_le_pow_left₀ (by linarith) (by linarith) _
    have hNp : 0 ≤ (N : ℝ) ^ (i + 1) := by positivity
    have hsub : (U + r) ^ (i + 1) - U ^ (i + 1) ≤ (U + R) ^ (i + 1) - U ^ (i + 1) := by linarith
    have hsub0 : 0 ≤ (U + r) ^ (i + 1) - U ^ (i + 1) := by
      have : U ^ (i + 1) ≤ (U + r) ^ (i + 1) := pow_le_pow_left₀ hU0 (by linarith) _
      linarith
    rcases eq_or_lt_of_le hNp with hN | hN
    · rw [← hN]; simp
    · gcongr

/-- **Budget monotonicity** (slab cells): the error budget of `ArbEcon.Off.cell_zeta_ne_zero` at
    radius `r` is at most the budget at any `R ≥ r`. -/
theorem budget_mono (K N p : ℕ) (r R L a U X E : ℝ) (hr0 : 0 ≤ r) (hrR : r ≤ R) (hL0 : 0 ≤ L)
    (hU0 : 0 ≤ U) (hX : 0 ≤ X) :
    Cp p * (r * L) ^ (p + 1) * X + 3 * corrVar K N r a U + E
      ≤ Cp p * (R * L) ^ (p + 1) * X + 3 * corrVar K N R a U + E := by
  have hcp := Cp_nonneg p
  have h1 : (r * L) ^ (p + 1) ≤ (R * L) ^ (p + 1) :=
    pow_le_pow_left₀ (mul_nonneg hr0 hL0) (mul_le_mul_of_nonneg_right hrR hL0) _
  have h2 := corrVar_mono K N r R a U hr0 hrR hU0
  have h3 : Cp p * (r * L) ^ (p + 1) * X ≤ Cp p * (R * L) ^ (p + 1) * X := by gcongr
  linarith

/-! ## F. Closed forms for the generated budgets (K ≤ 6), and the slab-cell wrapper. -/

theorem abs_bern_div (i : ℕ) (hi : i ≤ 10) :
    |(bernoulli (i + 2) : ℝ)| / ((i + 2)! : ℝ)
      = |(ArbEcon.OrderK.betaN i : ℝ)| / (ArbEcon.OrderK.Lbeta : ℝ) := by
  have hF : (0 : ℝ) < ((i + 2)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hL : (0 : ℝ) < (ArbEcon.OrderK.Lbeta : ℝ) := by norm_num [ArbEcon.OrderK.Lbeta]
  rw [← abs_of_pos hF, ← abs_div, ArbEcon.OrderK.betaN_spec i hi, abs_div, abs_of_pos hL]

/-- `emcB` with the Bernoulli numbers replaced by `betaN / Lbeta` (`K ≤ 6`). -/
theorem emcB_betaN (K N : ℕ) (hK : K ≤ 6) (a U : ℝ) :
    emcB K N a U = (N : ℝ) / a + 1 / 2
      + ∑ i ∈ Finset.range (2 * K - 1), |(ArbEcon.OrderK.betaN i : ℝ)| / (ArbEcon.OrderK.Lbeta : ℝ)
          * (U ^ (i + 1) / (N : ℝ) ^ (i + 1)) := by
  unfold emcB
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ 10 := by have := Finset.mem_range.mp hi; omega
  rw [← abs_bern_div i hi']
  ring

/-- `corrVar` with the Bernoulli numbers replaced by `betaN / Lbeta` (`K ≤ 6`). -/
theorem corrVar_betaN (K N : ℕ) (hK : K ≤ 6) (r a U : ℝ) :
    corrVar K N r a U = (N : ℝ) * r / a ^ 2
      + ∑ i ∈ Finset.range (2 * K - 1), |(ArbEcon.OrderK.betaN i : ℝ)| / (ArbEcon.OrderK.Lbeta : ℝ)
          * (((U + r) ^ (i + 1) - U ^ (i + 1)) / (N : ℝ) ^ (i + 1)) := by
  unfold corrVar
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ 10 := by have := Finset.mem_range.mp hi; omega
  rw [← abs_bern_div i hi']
  ring

/-- A rational upper bound of the odd-saw remainder constant at `K = 6`. -/
theorem CK_six_le : CK 6 ≤ 84107 / 1000000000000000 := by
  refine le_trans (CK_le 6) ?_
  norm_num

/-- **One zero-free slab cell, budget at a larger radius.**  `ArbEcon.Off.cell_zeta_ne_zero` with the
    error budget stated at any radius `R ≥ r` (so one budget serves every cell of a slab). -/
theorem cell_zeta_ne_zero_R (c : Cfg) (o : OCfg) (σc tc : ℝ) (hσ : σc = ((o.a : ℝ) - o.b) / o.q)
    (ht : tc = (c.tn : ℝ) / 2 ^ c.tq) (K N p : ℕ) (hK : 1 ≤ K) (hN : 2 ≤ N) (s1 s2 : StO)
    (h1 : InvO c σc tc (N - 1) s1) (h2 : InvO c σc tc N s2) (rn rd FN FD : ℕ)
    (hchk : checkCell c o K N p s1.acc s2.acc rn rd FN FD = true)
    (R L a U B Qr : ℝ) (r0 : ℕ) (hrR : (rn : ℝ) / rd ≤ R) (hL : (s2.lhi : ℝ) ≤ L * 2 ^ c.P)
    (hRL : R * L ≤ 1) (ha : 0 < a) (hta : a ≤ tc) (hσc : 0 ≤ σc) (hU0 : 0 ≤ U)
    (hU : (σc + (2 * K - 1 : ℝ)) ^ 2 + tc ^ 2 ≤ U ^ 2) (hQr0 : 0 ≤ Qr)
    (hQ : pochNormSq 1 B (2 * K + 1) ≤ Qr ^ 2) (hr0 : 0 < r0) (hr0N : r0 ^ 2 ≤ N)
    (hbudget : Cp p * (R * L) ^ (p + 1) * (((N : ℝ) - 1) + emcB K N a U)
        + 3 * corrVar K N R a U
        + CK K * Qr / ((N : ℝ) ^ (2 * K) * r0) / (((2 * K : ℕ) : ℝ) + 1 / 2) ≤ (FN : ℝ) / FD) :
    ∀ s : ℂ, ‖s - sOfG σc tc‖ ≤ (rn : ℝ) / rd → a ≤ s.im → s.im ≤ B → 1 / 2 ≤ s.re → s.re ≤ 1 →
      riemannZeta s ≠ 0 := by
  have hP : (0 : ℝ) < 2 ^ c.P := by positivity
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlogN : Real.log N ≤ L := by
    have h2l := h2.2.2.2.1
    have : Real.log N * 2 ^ c.P ≤ L * 2 ^ c.P := le_trans h2l hL
    exact le_of_mul_le_mul_right this hP
  have hL0 : 0 ≤ L := le_trans (Real.log_nonneg hN1) hlogN
  have hr0' : (0 : ℝ) ≤ (rn : ℝ) / rd := by positivity
  have hrL : (rn : ℝ) / rd * L ≤ 1 := le_trans (mul_le_mul_of_nonneg_right hrR hL0) hRL
  have hX : 0 ≤ ((N : ℝ) - 1) + emcB K N a U := by
    unfold emcB
    have hsum : 0 ≤ ∑ i ∈ Finset.range (2 * K - 1), |(bernoulli (i + 2) : ℝ)| / ((i + 2)! : ℝ)
        * U ^ (i + 1) / (N : ℝ) ^ (i + 1) := by
      apply Finset.sum_nonneg; intro i _; positivity
    have : (0 : ℝ) ≤ (N : ℝ) / a := by positivity
    linarith
  have hb := budget_mono K N p ((rn : ℝ) / rd) R L a U (((N : ℝ) - 1) + emcB K N a U)
    (CK K * Qr / ((N : ℝ) ^ (2 * K) * r0) / (((2 * K : ℕ) : ℝ) + 1 / 2)) hr0' hrR hL0 hU0 hX
  exact cell_zeta_ne_zero c o σc tc hσ ht K N p hK hN s1 s2 h1 h2 rn rd FN FD hchk L a U B Qr r0 hL hrL
    ha hta hσc hU0 hU hQr0 hQ hr0 hr0N (le_trans hb hbudget)

/-! ## G. Generated-certificate adapters. -/

/-- `N^(-x) ≤ Rn/Rd` for `x = (a - b)/q` from the integer certificate `Rd^q N^b ≤ Rn^q N^a`. -/
theorem rpow_cert (N : ℕ) (hN : 1 ≤ N) (a b q : ℕ) (hq : 1 ≤ q) (Rn Rd : ℕ) (hRd : 0 < Rd)
    (h : Rd ^ q * N ^ b ≤ Rn ^ q * N ^ a) (x : ℝ) (hx : x = ((a : ℝ) - b) / q) :
    (N : ℝ) ^ (-x) ≤ (Rn : ℝ) / Rd := by
  rw [hx]; exact rpow_neg_le_of_pow N hN a b q hq Rn Rd hRd h

/-- The remainder along a horizontal segment at `K = 6` with the rational constant `CK_six_le`. -/
theorem em_remainder_horiz6 (N : ℕ) (hN : 1 ≤ N) (t : ℝ) (ht : t ≠ 0) (xlo xhi σs : ℝ)
    (hpos : 0 < xlo + 12) (hs1 : xhi ≤ σs) (hs2 : -xlo ≤ σs) (Qr : ℝ) (hQr0 : 0 ≤ Qr)
    (hQ : pochNormSq σs t 13 ≤ Qr ^ 2) (R : ℝ) (hR : (N : ℝ) ^ (-xlo) ≤ R) (E : ℝ)
    (hE : 84107 / 1000000000000000 * Qr * R / (N : ℝ) ^ 12 / (xlo + 12) ≤ E) :
    ∀ x : ℝ, xlo ≤ x → x ≤ xhi →
      ‖riemannZeta (sOfG x t) - emFinite 6 (sOfG x t) N‖ ≤ E := by
  intro x hx0 hx1
  have h := em_remainder_horiz 6 N (by norm_num) hN t ht xlo xhi σs (by push_cast; linarith) hs1 hs2
    Qr hQr0 hQ R hR x hx0 hx1
  refine le_trans h (le_trans ?_ hE)
  have hC := CK_six_le
  have hR0 : 0 ≤ R := le_trans (by positivity) hR
  have hNp : (0 : ℝ) < (N : ℝ) ^ 12 := by
    have : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    positivity
  push_cast
  have e : (2 : ℝ) * 6 = 12 := by norm_num
  rw [e]
  apply div_le_div_of_nonneg_right _ (by linarith)
  apply div_le_div_of_nonneg_right _ hNp.le
  apply mul_le_mul_of_nonneg_right _ hR0
  exact mul_le_mul_of_nonneg_right hC hQr0

/-- From a remainder bound on `[xlo, xhi]` to the piece form `|x - σ| ≤ r`. -/
theorem hE_of_range (K N : ℕ) (t σ r xlo xhi E : ℝ) (h1 : xlo ≤ σ - r) (h2 : σ + r ≤ xhi)
    (h : ∀ x : ℝ, xlo ≤ x → x ≤ xhi → ‖riemannZeta (sOfG x t) - emFinite K (sOfG x t) N‖ ≤ E) :
    ∀ x : ℝ, |x - σ| ≤ r → ‖riemannZeta (sOfG x t) - emFinite K (sOfG x t) N‖ ≤ E := by
  intro x hx
  rw [abs_le] at hx
  exact h x (by linarith [hx.1]) (by linarith [hx.2])

/-- The endpoint point enclosure of an octant certificate from the `k = 0` accumulators of the piece
    centred at the endpoint and ONE `ArbEcon.Off.checkG`. -/
theorem inBox_of_checkG (c : Cfg) (o : OCfg) (σ t : ℝ) (hσ : σ = ((o.a : ℝ) - o.b) / o.q)
    (ht : t = (c.tn : ℝ) / 2 ^ c.tq) (K N : ℕ) (s1 s2 : StO) (h1 : InvO c σ t (N - 1) s1)
    (h2 : InvO c σ t N s2) (hne1 : s1.acc ≠ []) (hne2 : s2.acc ≠ []) (D : ℕ)
    (reLo reHi imLo imHi : ℤ) (Qp Rn Rd : ℕ)
    (hc : checkG c o K N (s1.acc.headD Acc.zero) (s2.acc.headD Acc.zero) D reLo reHi imLo imHi Qp Rn Rd
      = true) :
    ArgHoriz.InBox (riemannZeta ((σ : ℂ) + (t : ℂ) * I)) ((reLo : ℝ) / D) ((reHi : ℝ) / D)
      ((imLo : ℝ) / D) ((imHi : ℝ) / D) := by
  obtain ⟨x1, xs1, hs1⟩ := List.exists_cons_of_ne_nil hne1
  obtain ⟨x2, xs2, hs2⟩ := List.exists_cons_of_ne_nil hne2
  have ha1 := accOK_head c σ t (N - 1) s1 x1 xs1 h1 hs1
  have ha2 := accOK_head c σ t N s2 x2 xs2 h2 hs2
  rw [hs1, hs2] at hc
  have := checkG_sound c o σ t hσ ht K N x1 x2 ha1 ha2 D reLo reHi imLo imHi Qp Rn Rd hc
  exact ⟨this.1.1, this.1.2, this.2.1, this.2.2⟩

end H1000Oct
