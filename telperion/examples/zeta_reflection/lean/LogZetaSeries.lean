/-  LogZetaSeries.lean -- A2 Theorem 4: the prime-power log-zeta branch.

    Builds the explicit holomorphic branch `L₂` of `log ζ` on `Re s > 1` as a Dirichlet
    series over prime powers, and proves it is an antiderivative of `logDeriv ζ`:

        logZetaBranch s := ∑' n, Λ(n)/(log n) · n^{-s}          (`= LSeries vMlog s`)

    with

        hasDerivAt_logZetaBranch : HasDerivAt logZetaBranch (logDeriv ζ s) s  on Re s > 3/2
        deriv_logZetaBranch      : deriv logZetaBranch = logDeriv ζ           on Re s > 3/2
        analyticOnNhd_logZetaBranch : AnalyticOnNhd ℂ logZetaBranch branchRegion
        logZetaBranch_tail_bound : ‖L₂(s) − Σ_{n<N} termⁿ‖ ≤ Σ'_{n≥N} 1/n^{Re s}   (evaluator hook)

    This is the branch `L` that `LogBranches.argChangeVert_eq_im_log_sub` consumes for the
    Re = 2 vertical ζ edge (H4 edge 1): the argument change reduces to the imaginary-part
    difference of `logZetaBranch` at the two endpoints, each a convergent prime-power sum.

    Region: the open convex half-plane `Re s > 3/2` (contains the Re = 2 edge).  There the
    derivative terms admit the single summable majorant `‖term Λ (3/2) n‖`, as required by
    `hasDerivAt_tsum_of_isPreconnected`.

    conjecture1_proved = False.
-/
import DiffractionCore

open Complex ArithmeticFunction LSeries

namespace ZetaReflection

/-- The coefficient sequence of the log-ζ branch: `Λ(n)/log n` (as a complex number).
    For `n = 0, 1` the vonMangoldt value is `0`, so the coefficient is `0` (`0/0 = 0`). -/
noncomputable def vMlog (n : ℕ) : ℂ :=
  (vonMangoldt n : ℂ) / (Real.log n : ℂ)

/-- **The prime-power `log ζ` branch** `L₂(s) = ∑' n, Λ(n)/(log n) · n^{-s}`
    (`= LSeries vMlog s`). -/
noncomputable def logZetaBranch (s : ℂ) : ℂ := LSeries vMlog s

/-- The half-plane region on which the branch is differentiable with a uniform derivative
    majorant.  Open, convex (hence preconnected), and contains the `Re = 2` edge. -/
def branchRegion : Set ℂ := {s : ℂ | (3 / 2 : ℝ) < s.re}

lemma branchRegion_isOpen : IsOpen branchRegion :=
  isOpen_lt continuous_const Complex.continuous_re

lemma branchRegion_convex : Convex ℝ branchRegion :=
  convex_halfSpace_re_gt (r := (3 / 2 : ℝ))

lemma branchRegion_preconnected : IsPreconnected branchRegion :=
  branchRegion_convex.isPreconnected

lemma mem_branchRegion_iff {s : ℂ} : s ∈ branchRegion ↔ (3 / 2 : ℝ) < s.re := Iff.rfl

lemma two_mem_branchRegion : (2 : ℂ) ∈ branchRegion := by
  rw [mem_branchRegion_iff]; simp; norm_num

lemma one_lt_re_of_mem {s : ℂ} (hs : s ∈ branchRegion) : (1 : ℝ) < s.re :=
  lt_trans (by norm_num) hs

/-- `‖Λ(n)/log n‖ ≤ 1` for every `n` (the log-ζ coefficients are bounded by `1`:
    for a prime power `p^k` the coefficient is `1/k`; otherwise `0`). -/
lemma norm_vMlog_le_one (n : ℕ) : ‖vMlog n‖ ≤ 1 := by
  rcases le_or_gt n 1 with hn | hn
  · interval_cases n
    · simp [vMlog]
    · simp [vMlog, ArithmeticFunction.vonMangoldt_apply]
  · -- n ≥ 2 : 0 ≤ Λ n ≤ log n and log n > 0
    have hn2 : (2 : ℕ) ≤ n := hn
    have hnr : (1 : ℝ) < n := by exact_mod_cast hn
    have hlogpos : 0 < Real.log n := Real.log_pos hnr
    have hΛnn : 0 ≤ (vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
    have hΛle : (vonMangoldt n : ℝ) ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
    rw [vMlog, norm_div]
    rw [show ‖(vonMangoldt n : ℂ)‖ = (vonMangoldt n : ℝ) by
          rw [Complex.norm_real, Real.norm_of_nonneg hΛnn],
        show ‖(Real.log n : ℂ)‖ = Real.log n by
          rw [Complex.norm_real, Real.norm_of_nonneg (le_of_lt hlogpos)]]
    rw [div_le_one hlogpos]; exact hΛle

/-- Convergence of the branch at every point with `Re s > 1` (in particular on
    `branchRegion`): dominated by the constant-`1` L-series (the ζ series). -/
lemma summable_branch {s : ℂ} (hs : (1 : ℝ) < s.re) :
    Summable (fun n => LSeries.term vMlog s n) := by
  refine LSeriesSummable_of_le_const_mul_rpow (x := 1) (by simpa using hs) ?_
  exact ⟨1, fun n _ => by simpa using norm_vMlog_le_one n⟩

/-- Pointwise derivative of a single branch term: `d/ds [Λ(n)/log n · n^{-s}] = −Λ(n)·n^{-s}
    = −term Λ s n`.  Holds for every `n` (the `n ≤ 1` terms are `0` on both sides). -/
lemma hasDerivAt_term_vMlog (n : ℕ) (s : ℂ) :
    HasDerivAt (fun s => LSeries.term vMlog s n)
      (-(LSeries.term (fun n => (vonMangoldt n : ℂ)) s n)) s := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp only [LSeries.term_zero, neg_zero]; exact hasDerivAt_const _ _
  · rcases eq_or_ne n 1 with rfl | hn1
    · -- Λ 1 = 0 ⇒ both sides are 0
      have hΛ1 : (vonMangoldt 1 : ℂ) = 0 := by simp [ArithmeticFunction.vonMangoldt_apply]
      have hz1 : (fun s => LSeries.term vMlog s 1) = fun _ => (0 : ℂ) := by
        funext s; rw [LSeries.term_of_ne_zero hn0, vMlog, hΛ1, zero_div, zero_div]
      rw [hz1, LSeries.term_of_ne_zero hn0, hΛ1, zero_div, neg_zero]
      exact hasDerivAt_const _ _
    · -- generic n ≥ 2
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      have hncne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
      -- derivative of s ↦ n^{-s} is −(n^{-s}·log n)
      have hcpow : HasDerivAt (fun s => (n : ℂ) ^ (-s))
          (-((n : ℂ) ^ (-s) * Complex.log (n : ℂ))) s := by
        have hbase : HasDerivAt (fun u : ℂ => (n : ℂ) ^ u)
            ((n : ℂ) ^ (-s) * Complex.log (n : ℂ)) (-s) :=
          (Complex.hasStrictDerivAt_const_cpow (Or.inl hncne)).hasDerivAt
        have hneg : HasDerivAt (fun s : ℂ => -s) (-1 : ℂ) s :=
          (hasDerivAt_neg s)
        have hcomp := HasDerivAt.scomp s hbase hneg
        rw [Function.comp_def] at hcomp
        simpa [smul_eq_mul, mul_comm, mul_neg, mul_one] using hcomp
      -- term = (Λn/log n) · n^{-s}
      have hterm_eq : (fun s => LSeries.term vMlog s n)
          = fun s => vMlog n * (n : ℂ) ^ (-s) := by
        funext s
        rw [LSeries.term_of_ne_zero hn0, Complex.cpow_neg, div_eq_mul_inv]
      rw [hterm_eq]
      have hd : HasDerivAt (fun s => vMlog n * (n : ℂ) ^ (-s))
          (vMlog n * (-((n : ℂ) ^ (-s) * Complex.log (n : ℂ)))) s :=
        hcpow.const_mul (vMlog n)
      -- simplify value to −term Λ s n, using log n ≠ 0 (n ≥ 2) to cancel
      have hlogcast : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
        rw [← Complex.ofReal_natCast, Complex.ofReal_log (le_of_lt (by exact_mod_cast hnpos))]
      have hlogne : (Real.log n : ℂ) ≠ 0 := by
        have hnr : (1 : ℝ) < n := by
          have : (2 : ℕ) ≤ n := Nat.lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr hn0)
            (fun h => hn1 h.symm)
          exact_mod_cast this
        exact_mod_cast (ne_of_gt (Real.log_pos hnr))
      have hval : vMlog n * (-((n : ℂ) ^ (-s) * Complex.log (n : ℂ)))
          = -(LSeries.term (fun n => (vonMangoldt n : ℂ)) s n) := by
        rw [LSeries.term_of_ne_zero hn0, vMlog, hlogcast, Complex.cpow_neg]
        rw [div_eq_mul_inv (vonMangoldt n : ℂ), div_eq_mul_inv (vonMangoldt n : ℂ)]
        have hnsne : ((n : ℂ) ^ s) ≠ 0 := by
          rw [Complex.cpow_def_of_ne_zero hncne]; exact Complex.exp_ne_zero _
        field_simp [hlogne, hnsne]
      rw [hval] at hd
      exact hd

/-- Norm bound on the derivative terms over `branchRegion`: `‖term Λ s n‖ ≤ ‖term Λ (3/2) n‖`
    for `Re s > 3/2`.  The RHS is summable (vonMangoldt L-series convergence at `3/2 > 1`). -/
lemma norm_deriv_term_le (n : ℕ) {s : ℂ} (hs : s ∈ branchRegion) :
    ‖-(LSeries.term (fun n => (vonMangoldt n : ℂ)) s n)‖
      ≤ ‖LSeries.term (fun n => (vonMangoldt n : ℂ)) ((3 / 2 : ℝ) : ℂ) n‖ := by
  rw [norm_neg, LSeries.norm_term_eq, LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  · simp only [if_neg hn0, Complex.ofReal_re]
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hbase_pos : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
    have hle : (3 / 2 : ℝ) ≤ s.re := le_of_lt hs
    apply div_le_div_of_nonneg_left (norm_nonneg _)
      (Real.rpow_pos_of_pos hbase_pos _)
    exact Real.rpow_le_rpow_of_exponent_le hn1 hle

/-- Summability of the derivative-term majorant at `3/2 > 1`. -/
lemma summable_deriv_majorant :
    Summable (fun n => ‖LSeries.term (fun n => (vonMangoldt n : ℂ)) ((3 / 2 : ℝ) : ℂ) n‖) := by
  refine summable_norm_iff.mpr ?_
  refine ArithmeticFunction.LSeriesSummable_vonMangoldt ?_
  simp only [Complex.ofReal_re]; norm_num

/-- **A2 Theorem 4, core:** the branch is an antiderivative of `logDeriv ζ` on `branchRegion`:
    `HasDerivAt logZetaBranch (logDeriv ζ s) s` for `Re s > 3/2`.  Its derivative is the
    (negated) vonMangoldt L-series, which the prime keystone identifies with `logDeriv ζ`. -/
theorem hasDerivAt_logZetaBranch {s : ℂ} (hs : s ∈ branchRegion) :
    HasDerivAt logZetaBranch (logDeriv riemannZeta s) s := by
  -- pick a base point in the region for termwise differentiation
  have hs2 : (2 : ℂ) ∈ branchRegion := two_mem_branchRegion
  -- termwise differentiation of the tsum
  have hderiv :=
    hasDerivAt_tsum_of_isPreconnected
      (u := fun n => ‖LSeries.term (fun n => (vonMangoldt n : ℂ)) ((3 / 2 : ℝ) : ℂ) n‖)
      (g := fun n s => LSeries.term vMlog s n)
      (g' := fun n s => -(LSeries.term (fun n => (vonMangoldt n : ℂ)) s n))
      summable_deriv_majorant branchRegion_isOpen branchRegion_preconnected
      (fun n s _ => hasDerivAt_term_vMlog n s)
      (fun n s hsr => norm_deriv_term_le n hsr)
      hs2 (summable_branch (one_lt_re_of_mem hs2)) hs
  -- the derivative sum is −L(Λ)(s) = logDeriv ζ(s)
  have hsum_eq : (∑' n : ℕ, -(LSeries.term (fun n => (vonMangoldt n : ℂ)) s n))
      = logDeriv riemannZeta s := by
    rw [tsum_neg]
    rw [DiffractionCore.logDeriv_zeta_eq_neg_LSeries_vonMangoldt (one_lt_re_of_mem hs)]
    rfl
  rw [hsum_eq] at hderiv
  exact hderiv

/-- `deriv logZetaBranch = logDeriv ζ` on `branchRegion`. -/
theorem deriv_logZetaBranch {s : ℂ} (hs : s ∈ branchRegion) :
    deriv logZetaBranch s = logDeriv riemannZeta s :=
  (hasDerivAt_logZetaBranch hs).deriv

/-- Holomorphy: the branch is analytic on the open region `branchRegion` (`Re s > 3/2`). -/
theorem analyticOnNhd_logZetaBranch : AnalyticOnNhd ℂ logZetaBranch branchRegion := by
  refine DifferentiableOn.analyticOnNhd ?_ branchRegion_isOpen
  intro s hs
  exact (hasDerivAt_logZetaBranch hs).differentiableAt.differentiableWithinAt

/-- **Explicit tail bound (the computable-evaluator hook).**  The branch minus its first `N`
    terms is bounded in norm by the tail of the `Re s`-real ζ series: for `Re s > 1`,
        ‖L₂(s) − Σ_{n ∈ range N} term vMlog s n‖ ≤ Σ'_{n ≥ N} 1/n^{Re s}.
    Because `1/n^{Re s}` decays geometrically in `log n`, truncating at `N` gives an
    a-priori error the kernel evaluator can bound with a rational envelope. -/
theorem logZetaBranch_tail_bound {s : ℂ} (hs : (1 : ℝ) < s.re) (N : ℕ) :
    ‖logZetaBranch s - ∑ n ∈ Finset.range N, LSeries.term vMlog s n‖
      ≤ ∑' n : {n : ℕ // n ∉ Finset.range N},
          ‖LSeries.term (fun _ => (1 : ℂ)) s (n : ℕ)‖ := by
  have hsumm : Summable (fun n => LSeries.term vMlog s n) := summable_branch hs
  -- L₂(s) − partial sum = tsum over the complement of range N
  have hsplit : logZetaBranch s - ∑ n ∈ Finset.range N, LSeries.term vMlog s n
      = ∑' n : {n : ℕ // n ∉ Finset.range N}, LSeries.term vMlog s (n : ℕ) := by
    rw [logZetaBranch, LSeries]
    rw [← hsumm.sum_add_tsum_subtype_compl (Finset.range N)]
    ring
  rw [hsplit]
  -- termwise: ‖term vMlog s n‖ ≤ ‖term 1 s n‖  (from ‖vMlog n‖ ≤ 1)
  have hbound : ∀ n : {n : ℕ // n ∉ Finset.range N},
      ‖LSeries.term vMlog s (n : ℕ)‖ ≤ ‖LSeries.term (fun _ => (1 : ℂ)) s (n : ℕ)‖ := by
    rintro ⟨n, _⟩
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    · simp only [if_neg hn0, norm_one]
      have hbpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
      exact div_le_div_of_nonneg_right (norm_vMlog_le_one n)
        (le_of_lt (Real.rpow_pos_of_pos hbpos _))
  -- the RHS series is summable (comparison with the ζ series at Re s > 1)
  have hsumm1 : Summable (fun n : ℕ => LSeries.term (fun _ => (1 : ℂ)) s n) :=
    (LSeriesSummable_one_iff).mpr hs
  have hsummN : Summable (fun n : {n : ℕ // n ∉ Finset.range N} =>
      ‖LSeries.term (fun _ => (1 : ℂ)) s (n : ℕ)‖) :=
    (summable_norm_iff.mpr hsumm1).subtype _
  calc ‖∑' n : {n : ℕ // n ∉ Finset.range N}, LSeries.term vMlog s (n : ℕ)‖
      ≤ ∑' n : {n : ℕ // n ∉ Finset.range N}, ‖LSeries.term vMlog s (n : ℕ)‖ :=
        norm_tsum_le_tsum_norm ((summable_norm_iff.mpr hsumm).subtype _)
    _ ≤ ∑' n : {n : ℕ // n ∉ Finset.range N},
          ‖LSeries.term (fun _ => (1 : ℂ)) s (n : ℕ)‖ :=
        Summable.tsum_le_tsum hbound ((summable_norm_iff.mpr hsumm).subtype _) hsummN

end ZetaReflection
