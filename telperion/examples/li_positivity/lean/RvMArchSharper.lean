/-
RvMArchSharper — Arc B (sharper archimedean Li constant), step S3 + capstone.

Assembles the sharper archimedean growth: the linear term's constant is exactly `(γ−1−log 2π)/2`.
Writing `trend n = (n/2)·(log n + γ − 1 − log 2π)` and `a n = arch_n − trend n`, we show:

  * `dtrend_sub_half_log_tendsto` — `trend(n+1) − trend n − (1/2)·log(n+1) → (γ − log 2π)/2`
    (from `(n/2)·log(1+1/n) → 1/2`, i.e. `n·log(1+1/n) → 1` via `tendsto_one_add_div_pow_exp`).
  * `archDiff_sub_dtrend_tendsto_zero` — **`a_{n+1} − a_n → 0`** (`Δa_n → 0`), combining the S1a
    difference identity, `AH = 1 − log 2` (S1b), the S2b crux limit `DseriesAsymptotic`, and the
    trend asymptotic.  The four constants cancel to `0` exactly.
  * `cesaro_of_diff_tendsto_zero` — a self-contained Cesàro lemma: `Δa_n → 0 ⟹ a_n/n → 0`
    (from Mathlib's `Filter.Tendsto.cesaro`, `a_n = a_0 + ∑_{k<n} Δa_k`).
  * `taylorCoeff_Gammaℝ_re_asymptotic_of_DseriesAsymptotic` — the headline
      `(arch_n − trend_n)/n → 0`,
    proved from `DseriesAsymptotic` (the single remaining analytic obligation, packaged in S2b).

conjecture1_proved = False: a Γ-function fact (the sharper archimedean Li asymptotic); nothing here
approaches RH.  The headline sharpens the merged `taylorCoeff_Gammaℝ_re_growth` (|·−(n/2)log n| ≤ 8n).
-/
import Mathlib
import RvMArchSharperS1
import RvMArchSharperS2a
import RvMArchSharperS2b

open Filter Topology Real

namespace RvMWeierstrass

/-- The trend `trend n = (n/2)·(log n + γ − 1 − log 2π)`. -/
noncomputable def trend (n : ℕ) : ℝ :=
  ((n : ℝ) / 2) * (Real.log n + Real.eulerMascheroniConstant - 1 - Real.log (2 * Real.pi))

/-! ### The Cesàro lemma -/

/-- **Cesàro.**  If the first differences `u(n+1) − u n → 0`, then `u n / n → 0`.
    (`u n = u 0 + ∑_{k<n} Δu_k`; Cesàro on `Δu`.) -/
theorem cesaro_of_diff_tendsto_zero (u : ℕ → ℝ)
    (h : Tendsto (fun n => u (n + 1) - u n) atTop (nhds 0)) :
    Tendsto (fun n => u n / n) atTop (nhds 0) := by
  -- Cesàro average of the differences → 0
  have hces : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹) * ∑ k ∈ Finset.range n, (u (k + 1) - u k)) atTop
      (nhds 0) := h.cesaro
  -- ∑_{k<n} Δu_k = u n − u 0  (telescoping)
  have htel : ∀ n : ℕ, ∑ k ∈ Finset.range n, (u (k + 1) - u k) = u n - u 0 := by
    intro n
    rw [Finset.sum_range_sub (fun k => u k)]
  -- so (u n − u 0)/n → 0; add u 0 / n → 0
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹) * (u n - u 0)) atTop (nhds 0) := by
    refine hces.congr (fun n => ?_); rw [htel n]
  have h2 : Tendsto (fun n : ℕ => u 0 * ((n : ℝ)⁻¹)) atTop (nhds 0) := by
    have hinv : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have := (tendsto_const_nhds (x := u 0)).mul hinv
    simpa using this
  have hsum := h1.add h2
  rw [add_zero] at hsum
  refine hsum.congr (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · simp [h0]
  · have hn : (n : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    field_simp
    ring

/-! ### The trend difference asymptotic -/

/-- `n·log(1 + 1/n) → 1` (from `(1 + 1/n)^n → e` and `log` continuity). -/
theorem nat_mul_log_one_add_inv_tendsto :
    Tendsto (fun n : ℕ => (n : ℝ) * Real.log (1 + 1 / (n : ℝ))) atTop (nhds 1) := by
  have he := Real.tendsto_one_add_div_pow_exp (1 : ℝ)
  have hlog : Tendsto (fun n : ℕ => Real.log ((1 + 1 / (n : ℝ)) ^ n)) atTop
      (nhds (Real.log (Real.exp 1))) := by
    apply (Real.continuousAt_log (by positivity)).tendsto.comp
    simpa using he
  rw [Real.log_exp] at hlog
  refine hlog.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hpos : (0 : ℝ) < 1 + 1 / (n : ℝ) := by
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    positivity
  rw [Real.log_pow]

/-- **The trend difference asymptotic.**
    `trend(n+1) − trend n − (1/2)·log(n+1) → (γ − log 2π)/2`.

    Exact algebra: `trend(n+1) − trend n − (1/2)log(n+1) = (n/2)·log(1+1/n) + (γ−1−log 2π)/2`, and
    `(n/2)·log(1+1/n) → 1/2`. -/
theorem dtrend_sub_half_log_tendsto :
    Tendsto (fun n : ℕ => trend (n + 1) - trend n - (1 / 2) * Real.log ((n : ℝ) + 1)) atTop
      (nhds ((Real.eulerMascheroniConstant - Real.log (2 * Real.pi)) / 2)) := by
  set K : ℝ := Real.eulerMascheroniConstant - 1 - Real.log (2 * Real.pi) with hK
  -- rewrite the difference to `(n/2)·log(1+1/n) + K/2`, eventually (n ≥ 1)
  have hrw : ∀ᶠ n : ℕ in atTop,
      trend (n + 1) - trend n - (1 / 2) * Real.log ((n : ℝ) + 1)
        = ((n : ℝ) / 2) * Real.log (1 + 1 / (n : ℝ)) + K / 2 := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    -- log(1+1/n) = log(n+1) − log n
    have hlogsplit : Real.log (1 + 1 / (n : ℝ)) = Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) := by
      rw [show (1 : ℝ) + 1 / (n : ℝ) = ((n : ℝ) + 1) / (n : ℝ) from by field_simp,
        Real.log_div (by linarith) (ne_of_gt hnpos)]
    unfold trend
    push_cast
    rw [hlogsplit, hK]
    ring
  -- limit of the RHS: (1/2)·(n·log(1+1/n)) → 1/2, plus K/2
  have hhalf : Tendsto (fun n : ℕ => ((n : ℝ) / 2) * Real.log (1 + 1 / (n : ℝ))) atTop
      (nhds (1 / 2)) := by
    have hbase := nat_mul_log_one_add_inv_tendsto.const_mul (1 / 2)
    rw [mul_one] at hbase
    refine hbase.congr (fun n => ?_); ring
  have hlim : Tendsto (fun n : ℕ => ((n : ℝ) / 2) * Real.log (1 + 1 / (n : ℝ)) + K / 2) atTop
      (nhds (1 / 2 + K / 2)) := hhalf.add_const _
  have hcst : (1 : ℝ) / 2 + K / 2 = (Real.eulerMascheroniConstant - Real.log (2 * Real.pi)) / 2 := by
    rw [hK]; ring
  rw [hcst] at hlim
  exact hlim.congr' (hrw.mono (fun n h => h.symm))

/-! ### `Δa_n → 0` -/

/-- The shifted crux limit: `Dseries(n+1) − (1/2)·log(n+1) → γ − 1 + (log 2)/2`, from
    `DseriesAsymptotic` composed with `n ↦ n+1`. -/
theorem Dseries_succ_sub_half_log_tendsto (hD : DseriesAsymptotic) :
    Tendsto (fun n : ℕ => Dseries (n + 1) - (1 / 2) * Real.log ((n : ℝ) + 1)) atTop
      (nhds (Real.eulerMascheroniConstant - 1 + Real.log 2 / 2)) := by
  have hcomp : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
    Filter.tendsto_atTop_mono (f := fun n : ℕ => n) (g := fun n : ℕ => n + 1)
      (fun n => by omega) Filter.tendsto_id
  have hshift := hD.comp hcomp
  refine hshift.congr (fun n => ?_)
  simp only [Function.comp_apply]
  push_cast
  ring_nf

/-- **`Δa_n → 0`** (`a n = arch_n − trend n`).  The S1a difference identity, `AH = 1 − log 2`, the
    crux limit `DseriesAsymptotic`, and the trend asymptotic combine; the four limit constants cancel
    to `0` exactly. -/
theorem archDiff_sub_dtrend_tendsto_zero (hD : DseriesAsymptotic) :
    Tendsto (fun n : ℕ =>
      ((LiCriterion.taylorCoeff Complex.Gammaℝ (n + 1)).re - trend (n + 1))
        - ((LiCriterion.taylorCoeff Complex.Gammaℝ n).re - trend n)) atTop (nhds 0) := by
  -- Δa_n = (arch_{n+1} − arch_n) − (trend_{n+1} − trend_n)
  --      = [−(γ+log π)/2 + (1−log2) + Dseries(n+1)] − dtrend_n
  --      = −(γ+log π)/2 + 1 − log2
  --        + [Dseries(n+1) − (1/2)log(n+1)] − [dtrend_n − (1/2)log(n+1)]
  set c1 : ℝ := -((Real.eulerMascheroniConstant + Real.log Real.pi) / 2) + (1 - Real.log 2) with hc1
  have hDlim := Dseries_succ_sub_half_log_tendsto hD
  have hTlim := dtrend_sub_half_log_tendsto
  -- combined limit: c1 + (γ−1+log2/2) − (γ−log2π)/2 = 0
  have hcomb : Tendsto (fun n : ℕ =>
      c1 + (Dseries (n + 1) - (1 / 2) * Real.log ((n : ℝ) + 1))
        - (trend (n + 1) - trend n - (1 / 2) * Real.log ((n : ℝ) + 1))) atTop
      (nhds (c1 + (Real.eulerMascheroniConstant - 1 + Real.log 2 / 2)
        - (Real.eulerMascheroniConstant - Real.log (2 * Real.pi)) / 2)) :=
    (tendsto_const_nhds.add hDlim).sub hTlim
  -- the limit constant is 0
  have hzero : c1 + (Real.eulerMascheroniConstant - 1 + Real.log 2 / 2)
      - (Real.eulerMascheroniConstant - Real.log (2 * Real.pi)) / 2 = 0 := by
    rw [hc1]
    have hlog2pi : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi :=
      Real.log_mul (by norm_num) (ne_of_gt Real.pi_pos)
    rw [hlog2pi]; ring
  rw [hzero] at hcomb
  -- Δa_n equals that combined expression (via the S1a difference identity + AH_eq)
  refine hcomb.congr (fun n => ?_)
  have hdiff := arch_succ_sub_eq n
  rw [AH_eq] at hdiff
  -- arch_{n+1} − arch_n = −(γ+logπ)/2 + (1−log2) + Dseries(n+1) = c1 + Dseries(n+1)
  rw [hc1]
  linarith [hdiff]

/-! ### The capstone -/

/-- **THE SHARPER ARCHIMEDEAN ASYMPTOTIC (conditional on the S2b crux limit).**
    `(arch_n − (n/2)·(log n + γ − 1 − log 2π)) / n → 0`.

    Sharpens the merged `taylorCoeff_Gammaℝ_re_growth` (`|arch_n − (n/2)·log n| ≤ 8n`): the linear
    term's constant is exactly `(γ − 1 − log 2π)/2`.  Proved from `DseriesAsymptotic` (S2b crux limit)
    via `Δa_n → 0` and Cesàro.

    conjecture1_proved = False: Γ-function calculus; nothing about RH. -/
theorem taylorCoeff_Gammaℝ_re_asymptotic_of_DseriesAsymptotic (hD : DseriesAsymptotic) :
    Tendsto (fun n : ℕ =>
      ((LiCriterion.taylorCoeff Complex.Gammaℝ n).re
        - ((n : ℝ) / 2) * (Real.log n + Real.eulerMascheroniConstant - 1
          - Real.log (2 * Real.pi)))
      / n) atTop (nhds 0) := by
  have hces := cesaro_of_diff_tendsto_zero
    (fun n => (LiCriterion.taylorCoeff Complex.Gammaℝ n).re - trend n)
    (archDiff_sub_dtrend_tendsto_zero hD)
  refine hces.congr (fun n => ?_)
  unfold trend
  ring_nf

end RvMWeierstrass
