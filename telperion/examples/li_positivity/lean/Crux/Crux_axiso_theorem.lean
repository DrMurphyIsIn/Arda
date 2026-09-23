/-
  Crux_axiso_theorem.lean -- buildable core of "Class P is the one-element set {zeta}".

  conjecture1_proved = False.  Nothing in this file bears on RH.  C4 of the write-up says the
  class-P question is a relabeling of RH for zeta, which remains open.

  SETTING (coefficient level).  `F(s) = Σ a(n) n^{-s}` and `G = log F = Σ b(n) n^{-s}` are encoded
  as real arithmetic functions `a, b`.  `IsDirExp a b` says `a(1) = 1` and `a · log = (b · log) ⋆ a`,
  i.e. `-F'/F = Σ Λ_F(n) n^{-s}` with `Λ_F = b · log`.  This determines `a` from `b` and conversely.
  The remaining hypotheses are:
  * P2 (log-positivity): `∀ n, 0 ≤ b n`.
  * KP99 periodicity with `θ = 0`: `∀ n > 0, a n = A (n mod q)`.
  * the FE in coefficient form: `|P(q)| = √q`, where `P := a ⋆ μ`, i.e. `F = ζ · P`.

  MAIN RESULT (kernel-checked): `classP_eq_zeta`.
    `IsDirExp a b`, `b ≥ 0`, `a` periodic mod `q`, and `|P(q)| = √q` together imply `q = 1` and
    `a ≡ 1`, i.e. `F = ζ`.
  This is C3 of the write-up at the coefficient level, with its two external inputs as
  hypotheses (see DOES NOT ESTABLISH).  Multiplicativity is not assumed.

  ESTABLISHES (kernel-checked, no `sorry`, axioms = propext, Classical.choice, Quot.sound):
  * `finite_difference_rigidity`, the lemma inside C3 Step 2: a periodic `u` with `Δ^k u(0) ≥ 0`
    for all `k ≥ 1` is constant.  Proof: Newton's forward formula makes `u` monotone.  No
    Pringsheim argument is needed.
  * `cumulant_rigidity`, the lemma inside C3 Step 1: if `m_{n+1} = Σ_j C(n,j) κ_{j+1} m_{n-j}`,
    `m_0 = 1`, `κ_k ≥ 0` and `m` is periodic, then `κ_1 = 1`, `κ_{≥2} = 0` and `m ≡ 1`.  Proof:
    `m_{kt} ≥ t! κ_k^t`.  No Pringsheim / Hadamard / exponential-independence argument is needed.
  * `IsDirExp.nonneg` (C1(i)): `b ≥ 0` gives `a ≥ 0`.  `IsDirExp.pmul_additive`: every additive
    weight `w` gives the derivation identity `a · w = (b · w) ⋆ a`.  This covers `v_p`
    (`vp_recursion`) and `Ω` (`diag_R`).
  * `IsDirExp.sqfree_cumulant`: on products of distinct primes, `(a, b)` is a moment-cumulant
    pair.
  * Step 1, `step1_units`: `a(n) = 1` for every `n` coprime to `q`.  This uses Dirichlet's
    theorem from Mathlib.
  * Step 2, `step2`: `a(n r) = a(n)` when `gcd(r, q) = 1`, so `F = D(s) · L(s, χ₀)`.  Proof: the
    `D_ℓ`-recursion gives `u_{k+1} = u_k + Σ(b ≥ 0)`.  No characters are needed.
  * Step 3, `step3`: `P = a ⋆ μ` vanishes off the divisors of `q`.
  * Step 4, `step4_top_coeff`: `|P(q)| ≤ 1`, with no FE assumed.  Proof: on the diagonal
    `p^{-s} ↦ t` (`p ∣ q`), `F_q-smooth = f(t)/V(t)`, and `f` has no zero in `|t| < 1`.  This is a
    formal identity in `ℂ⟦X⟧` plus evaluation at a single point, and `B_k ≤ k A_k` gives
    convergence.  It replaces Landau's theorem and Hadamard factorization.
  * Non-vacuity, `classP_hypotheses_satisfiable`: `ζ` meets every hypothesis with `q = 1`.
    Sharpness, `a2_topcoeff` and `a2_logcoeff_four`: `ζ(s)(1 + 2^{1/2-s})` meets periodicity
    and `|P(2)| = √2` with `q = 2`, and `b(4) = -1/2`.  So P2 cannot be dropped.
  * C9(i): `nc_F_vanishes`, `ncLambda_one_sub`, `ncLambda_eq`, and `a9_logcoeff_four`.
    `F = ζ(s)(1 + 4·2^{-s} + 2·4^{-s})` has nonnegative multiplicative coefficients and an exact
    FE `Λ_F(1-s) = Λ_F(s)` with `Λ_F = (4/π)^{s/2} Γ(s/2) F`.  It vanishes at
    `s₀ = log₂(2+√2) + iπ/log 2`, where `Re s₀ > 1`, and `b(4) = -11/2`.
  * C9(ii), `a5_logcoeff`: the KP conductor-5 element `ζ(s; ±1 mod 5) + φ 5^{-s} ζ(s)` has
    `b(2·7·17·37) = κ₄(log cosh) = -2`.
  * C6 algebra: `dlvp_step`, `dlvp_opt`, `dlvp_opt_attained`, `dlvp_region`, and `trig_341`.
    Once `4/(σ-β) ≤ 3/(σ-1) + L` holds at `σ = 1 + (2√3-3)/L`, it forces `1 - β ≥ (7-4√3)/L`.

  DOES NOT ESTABLISH:
  * The Kaczorowski-Perelli structure theorem for S#_1 (Acta Math. 182, 1999): conductor
    `q = πQ² ∈ ℕ` and `a(n) n^{iθ}` periodic mod `q`.  Nor `θ = 0`.  This enters as hypothesis `hA`.
  * FE ⟹ `|P(q)| = √q`.  Dividing F's FE by ζ's gives `q^{s/2} P(s) = ε q^{(1-s)/2} P(1-s)`, and
    comparing coefficients gives `P(q) = ε√q`.  This is paper-level and enters as `hFE`.
  * C1(ii)-(iv) (Landau, `μ = 0`, `ε = ±1`, simple pole), C2 (Hamburger), C5 (Beurling / Fejér /
    Hermite LP bounds), C7, C8 (RvM analogue), and C10 (conjecture).
  * The analytic inputs of C6 (Hadamard product, digamma bound, constant 2.4302).  Only the final
    algebra is checked.
  * That the C9(ii) element lies in S#_1 (the KP99 FE).  Only its log-coefficient is computed.
  * Anything about the zeros of `ζ`.
-/
import Mathlib

namespace Crux.AxisoTheorem

open Finset


open Finset

/-! ## K1 -/

open fwdDiff in
theorem monotone_of_fwdDiff_iter_nonneg (u : ℕ → ℝ)
    (h : ∀ k : ℕ, 0 ≤ (Δ_[1])^[k + 1] u 0) : Monotone u := by
  refine monotone_nat_of_le_succ fun n => ?_
  have key := shift_eq_sum_fwdDiff_iter (1 : ℕ) (Δ_[1] u) n 0
  simp only [zero_add, smul_eq_mul, mul_one] at key
  have hdiff : Δ_[1] u n = u (n + 1) - u n := rfl
  have hnn : 0 ≤ Δ_[1] u n := by
    rw [key]
    refine Finset.sum_nonneg fun k _ => ?_
    rw [nsmul_eq_mul, ← Function.iterate_succ_apply]
    exact mul_nonneg (Nat.cast_nonneg _) (h k)
  linarith [hdiff ▸ hnn]

theorem eq_of_monotone_periodic {u : ℕ → ℝ} (hmono : Monotone u) {r : ℕ} (hr : 0 < r)
    (hper : Function.Periodic u r) (n : ℕ) : u n = u 0 := by
  have h1 : u 0 ≤ u n := hmono (Nat.zero_le n)
  have h2 : u n ≤ u (n * r) := hmono (Nat.le_mul_of_pos_right n hr)
  have h3 : u (n * r) = u 0 := by simpa using hper.nat_mul_eq n
  linarith

open fwdDiff in
theorem finite_difference_rigidity (u : ℕ → ℝ) {r : ℕ} (hr : 0 < r)
    (hper : Function.Periodic u r) (h : ∀ k : ℕ, 0 ≤ (Δ_[1])^[k + 1] u 0) (n : ℕ) :
    u n = u 0 :=
  eq_of_monotone_periodic (monotone_of_fwdDiff_iter_nonneg u h) hr hper n

/-! ## K2 -/

def MomCum (m κ : ℕ → ℝ) : Prop :=
  m 0 = 1 ∧ ∀ n, m (n + 1) = ∑ j ∈ range (n + 1), (n.choose j : ℝ) * κ (j + 1) * m (n - j)

theorem MomCum.nonneg {m κ : ℕ → ℝ} (h : MomCum m κ) (hκ : ∀ k, 0 ≤ κ (k + 1)) (n : ℕ) :
    0 ≤ m n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · rw [h.1]; exact zero_le_one
    · rw [h.2 n]
      refine sum_nonneg fun j _ => ?_
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hκ j)) (ih _ (by omega))

theorem MomCum.term_le {m κ : ℕ → ℝ} (h : MomCum m κ) (hκ : ∀ k, 0 ≤ κ (k + 1)) (n j : ℕ)
    (hj : j ≤ n) : (n.choose j : ℝ) * κ (j + 1) * m (n - j) ≤ m (n + 1) := by
  rw [h.2 n]
  refine single_le_sum (f := fun j => (n.choose j : ℝ) * κ (j + 1) * m (n - j))
    (fun i _ => ?_) (mem_range.2 (by omega))
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hκ i)) (h.nonneg hκ _)

theorem choose_lower (k t : ℕ) : t + 1 ≤ ((k + 2) * t + (k + 1)).choose (k + 1) := by
  have h1 : (t + (k + 1)).choose (k + 1) ≤ ((k + 2) * t + (k + 1)).choose (k + 1) :=
    Nat.choose_le_choose (k + 1) (by nlinarith)
  have h2 : (t + (k + 1)).choose (k + 1) = (t + (k + 1)).choose t := by
    rw [Nat.choose_symm_add]
  have h3 : (t + 1).choose t ≤ (t + (k + 1)).choose t :=
    Nat.choose_le_choose t (by omega)
  have h4 : (t + 1).choose t = t + 1 := Nat.choose_succ_self_right t
  omega

theorem MomCum.factorial_lower {m κ : ℕ → ℝ} (h : MomCum m κ) (hκ : ∀ k, 0 ≤ κ (k + 1))
    (k t : ℕ) : (t.factorial : ℝ) * κ (k + 2) ^ t ≤ m ((k + 2) * t) := by
  induction t with
  | zero => simp [h.1]
  | succ t ih =>
    have hterm := h.term_le hκ ((k + 2) * t + (k + 1)) (k + 1) (by omega)
    have hidx1 : (k + 2) * t + (k + 1) + 1 = (k + 2) * (t + 1) := by ring
    have hidx2 : (k + 2) * t + (k + 1) - (k + 1) = (k + 2) * t := by omega
    rw [hidx1, hidx2] at hterm
    have hch : ((t + 1 : ℕ) : ℝ) ≤ (((k + 2) * t + (k + 1)).choose (k + 1) : ℝ) := by
      exact_mod_cast choose_lower k t
    have hκ2 : 0 ≤ κ (k + 2) := hκ (k + 1)
    have hm0 : 0 ≤ m ((k + 2) * t) := h.nonneg hκ _
    calc ((t + 1).factorial : ℝ) * κ (k + 2) ^ (t + 1)
        = ((t + 1 : ℕ) : ℝ) * κ (k + 2) * ((t.factorial : ℝ) * κ (k + 2) ^ t) := by
          rw [Nat.factorial_succ]; push_cast; ring
      _ ≤ (((k + 2) * t + (k + 1)).choose (k + 1) : ℝ) * κ (k + 2) * m ((k + 2) * t) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hch hκ2) ih (by positivity)
            (by positivity)
      _ ≤ m ((k + 2) * (t + 1)) := hterm

theorem MomCum.cumulant_eq_zero_of_bdd {m κ : ℕ → ℝ} (h : MomCum m κ)
    (hκ : ∀ k, 0 ≤ κ (k + 1)) {C : ℝ} (hC : ∀ n, m n ≤ C) (k : ℕ) : κ (k + 2) = 0 := by
  by_contra hne
  have hpos : 0 < κ (k + 2) := lt_of_le_of_ne (hκ (k + 1)) (Ne.symm hne)
  have ht := FloorSemiring.tendsto_pow_div_factorial_atTop (κ (k + 2))⁻¹
  have hB : (0 : ℝ) < 1 / (|C| + 1) := by positivity
  obtain ⟨t, ht'⟩ := (ht.eventually (gt_mem_nhds hB)).exists
  have hlow := h.factorial_lower hκ k t
  have hfpos : (0 : ℝ) < (t.factorial : ℝ) * κ (k + 2) ^ t := by
    have := Nat.factorial_pos t
    positivity
  have heq : (κ (k + 2))⁻¹ ^ t / (t.factorial : ℝ) = 1 / ((t.factorial : ℝ) * κ (k + 2) ^ t) := by
    rw [inv_pow]; field_simp
  rw [heq, one_div_lt_one_div hfpos (by positivity)] at ht'
  have := hC ((k + 2) * t)
  have : C ≤ |C| := le_abs_self C
  linarith

theorem MomCum.eq_pow_of_bdd {m κ : ℕ → ℝ} (h : MomCum m κ) (hκ : ∀ k, 0 ≤ κ (k + 1))
    {C : ℝ} (hC : ∀ n, m n ≤ C) (n : ℕ) : m n = κ 1 ^ n := by
  induction n with
  | zero => simp [h.1]
  | succ n ih =>
    rw [h.2 n, Finset.sum_eq_single 0]
    · simp [ih, pow_succ]; ring
    · intro j _ hj0
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      rw [show i + 1 + 1 = i + 2 by ring, h.cumulant_eq_zero_of_bdd hκ hC i]
      ring
    · intro h0; simp at h0

theorem cumulant_rigidity {m κ : ℕ → ℝ} (h : MomCum m κ) (hκ : ∀ k, 0 ≤ κ (k + 1))
    {r : ℕ} (hr : 0 < r) (hper : Function.Periodic m r) :
    κ 1 = 1 ∧ (∀ k, κ (k + 2) = 0) ∧ ∀ n, m n = 1 := by
  set C : ℝ := ∑ i ∈ range r, |m i| with hCdef
  have hC : ∀ n, m n ≤ C := by
    intro n
    rw [← hper.map_mod_nat n]
    calc m (n % r) ≤ |m (n % r)| := le_abs_self _
      _ ≤ C := single_le_sum (f := fun i => |m i|) (fun i _ => abs_nonneg _)
          (mem_range.2 (Nat.mod_lt n hr))
  have hpow := h.eq_pow_of_bdd hκ hC
  have hr1 : κ 1 ^ r = 1 := by
    rw [← hpow r, ← h.1]
    simpa using hper 0
  have hk1 : κ 1 = 1 := (pow_eq_one_iff_of_nonneg (hκ 0) hr.ne').mp hr1
  refine ⟨hk1, h.cumulant_eq_zero_of_bdd hκ hC, fun n => ?_⟩
  rw [hpow n, hk1, one_pow]




open ArithmeticFunction

def IsDirExp (a b : ArithmeticFunction ℝ) : Prop :=
  a 1 = 1 ∧ a.pmul log = (b.pmul log) * a

theorem af_sub_apply (f g : ArithmeticFunction ℝ) (n : ℕ) : (f - g) n = f n - g n := by
  rw [sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply, ← sub_eq_add_neg]

def IsAdditiveWeight (w : ArithmeticFunction ℝ) : Prop :=
  ∀ m n : ℕ, m ≠ 0 → n ≠ 0 → w (m * n) = w m + w n

theorem pmul_mul_of_additive {w : ArithmeticFunction ℝ} (hw : IsAdditiveWeight w)
    (f g : ArithmeticFunction ℝ) : (f * g).pmul w = f.pmul w * g + f * g.pmul w := by
  ext n
  simp only [pmul_apply, mul_apply, ArithmeticFunction.add_apply, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' := Nat.mem_divisorsAntidiagonal.mp hx
  have h1 : x.1 ≠ 0 := Nat.left_ne_zero_of_mem_divisorsAntidiagonal hx
  have h2 : x.2 ≠ 0 := Nat.right_ne_zero_of_mem_divisorsAntidiagonal hx
  rw [← hx'.1, hw _ _ h1 h2]; ring

theorem pmul_pmul_comm (f w w' : ArithmeticFunction ℝ) :
    (f.pmul w).pmul w' = (f.pmul w').pmul w := by
  ext n; simp only [pmul_apply]; ring

theorem pmul_sub' (f g w : ArithmeticFunction ℝ) : (f - g).pmul w = f.pmul w - g.pmul w := by
  ext n; simp only [pmul_apply, af_sub_apply]; ring

theorem isAdditiveWeight_log : IsAdditiveWeight log := by
  intro m n hm hn
  simp only [log_apply, Nat.cast_mul]
  exact Real.log_mul (by exact_mod_cast hm) (by exact_mod_cast hn)

noncomputable def vp (p : ℕ) : ArithmeticFunction ℝ := ⟨fun n => (padicValNat p n : ℝ), by simp⟩

theorem vp_apply (p n : ℕ) : vp p n = (padicValNat p n : ℝ) := rfl

theorem isAdditiveWeight_vp (p : ℕ) [Fact p.Prime] : IsAdditiveWeight (vp p) := by
  intro m n hm hn
  simp only [vp_apply, padicValNat.mul hm hn, Nat.cast_add]

theorem eq_zero_of_pmul_log {b E : ArithmeticFunction ℝ} (hE1 : E 1 = 0)
    (hE : E.pmul log = (b.pmul log) * E) : E = 0 := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · simp
      · simpa using hE1
    · have h := congrArg (fun f => f n) hE
      simp only [pmul_apply, mul_apply, log_apply] at h
      have hsum : ∑ x ∈ n.divisorsAntidiagonal, b x.1 * Real.log x.1 * E x.2 = 0 := by
        refine Finset.sum_eq_zero fun x hx => ?_
        have hx' := Nat.mem_divisorsAntidiagonal.mp hx
        have h1 : x.1 ≠ 0 := Nat.left_ne_zero_of_mem_divisorsAntidiagonal hx
        have h2 : x.2 ≠ 0 := Nat.right_ne_zero_of_mem_divisorsAntidiagonal hx
        by_cases hx1 : x.1 = 1
        · simp [hx1]
        · have hlt : x.2 < n := by
            have : 2 ≤ x.1 := by omega
            rw [← hx'.1]
            nlinarith [Nat.pos_of_ne_zero h2]
          simp [ih x.2 hlt]
      rw [hsum] at h
      have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
      simp only [ArithmeticFunction.zero_apply]
      rcases mul_eq_zero.mp h with h' | h'
      · exact h'
      · exact absurd h' hlog.ne'

theorem IsDirExp.pmul_additive {a b : ArithmeticFunction ℝ} (hab : IsDirExp a b)
    {w : ArithmeticFunction ℝ} (hw : IsAdditiveWeight w) : a.pmul w = (b.pmul w) * a := by
  have hw1 : w 1 = 0 := by
    have := hw 1 1 one_ne_zero one_ne_zero
    simp only [mul_one] at this
    linarith
  set E := (b.pmul w) * a - a.pmul w with hEdef
  have hE1 : E 1 = 0 := by
    simp only [E, af_sub_apply, mul_apply_one, pmul_apply, hw1]; ring
  have hcomm : (b.pmul w).pmul log = (b.pmul log).pmul w := pmul_pmul_comm b w log
  have hE : E.pmul log = (b.pmul log) * E := by
    calc E.pmul log = ((b.pmul w) * a).pmul log - (a.pmul w).pmul log := pmul_sub' _ _ _
      _ = ((b.pmul w).pmul log * a + (b.pmul w) * a.pmul log) - (a.pmul log).pmul w := by
          rw [pmul_mul_of_additive isAdditiveWeight_log, pmul_pmul_comm a w log]
      _ = ((b.pmul w).pmul log * a + (b.pmul w) * ((b.pmul log) * a))
            - ((b.pmul log) * a).pmul w := by rw [hab.2]
      _ = ((b.pmul w).pmul log * a + (b.pmul w) * ((b.pmul log) * a))
            - (((b.pmul log).pmul w) * a + (b.pmul log) * a.pmul w) := by
          rw [pmul_mul_of_additive hw]
      _ = (b.pmul log) * E := by rw [hcomm]; simp only [E]; ring
  have := eq_zero_of_pmul_log hE1 hE
  exact (sub_eq_zero.mp this).symm

/-- C1(i): nonnegative log-coefficients give nonnegative coefficients. -/
theorem IsDirExp.nonneg {a b : ArithmeticFunction ℝ} (hab : IsDirExp a b)
    (hb : ∀ n, 0 ≤ b n) (n : ℕ) : 0 ≤ a n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · simp
      · rw [hab.1]; exact zero_le_one
    · have h := congrArg (fun f => f n) hab.2
      simp only [pmul_apply, mul_apply, log_apply] at h
      have hsum : 0 ≤ ∑ x ∈ n.divisorsAntidiagonal, b x.1 * Real.log x.1 * a x.2 := by
        refine Finset.sum_nonneg fun x hx => ?_
        have hx' := Nat.mem_divisorsAntidiagonal.mp hx
        have h1 : x.1 ≠ 0 := Nat.left_ne_zero_of_mem_divisorsAntidiagonal hx
        have h2 : x.2 ≠ 0 := Nat.right_ne_zero_of_mem_divisorsAntidiagonal hx
        by_cases hx1 : x.1 = 1
        · simp [hx1]
        · have hlt : x.2 < n := by
            have : 2 ≤ x.1 := by omega
            rw [← hx'.1]
            nlinarith [Nat.pos_of_ne_zero h2]
          exact mul_nonneg (mul_nonneg (hb _) (Real.log_natCast_nonneg _)) (ih _ hlt)
      rw [← h] at hsum
      have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
      exact nonneg_of_mul_nonneg_left hsum hlog

/-- The `v_p`-recursion (derivation `D_p`): `v_p(n) a(n) = Σ_{d ∣ n} v_p(d) b(d) a(n/d)`. -/
theorem IsDirExp.vp_recursion {a b : ArithmeticFunction ℝ} (hab : IsDirExp a b)
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (padicValNat p n : ℝ) * a n
      = ∑ d ∈ n.divisors, (padicValNat p d : ℝ) * b d * a (n / d) := by
  have h := congrArg (fun f => f n) (hab.pmul_additive (isAdditiveWeight_vp p))
  simp only [pmul_apply, mul_apply, vp_apply] at h
  rw [mul_comm, h]
  rw [Nat.sum_divisorsAntidiagonal (f := fun x y => b x * (padicValNat p x : ℝ) * a y)]
  refine Finset.sum_congr rfl fun d _ => ?_
  ring



/-! ## Squarefree divisor structure -/

theorem sum_divisors_mul_coprime {M : Type*} [AddCommMonoid M] (f : ℕ → M) {m n : ℕ}
    (h : m.Coprime n) :
    ∑ d ∈ (m * n).divisors, f d = ∑ x ∈ m.divisors, ∑ y ∈ n.divisors, f (x * y) := by
  rw [h.divisors_mul, Finset.sum_map, ← Finset.sum_product' (f := fun x y => f (x * y))]
  exact Finset.sum_attach (m.divisors ×ˢ n.divisors) (fun p => f (p.1 * p.2))

theorem sum_divisors_mul_prod {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hm : ∀ p ∈ S, ¬ p ∣ m) :
    ∑ d ∈ (m * ∏ p ∈ S, p).divisors, f d
      = ∑ x ∈ m.divisors, ∑ U ∈ S.powerset, f (x * ∏ p ∈ U, p) := by
  classical
  induction S using Finset.induction_on generalizing f with
  | empty => simp
  | insert p S hpS ih =>
    have hp : p.Prime := hS p (Finset.mem_insert_self p S)
    have hS' : ∀ q ∈ S, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have hm' : ∀ q ∈ S, ¬ q ∣ m := fun q hq => hm q (Finset.mem_insert_of_mem hq)
    have hprod : m * ∏ q ∈ insert p S, q = (m * ∏ q ∈ S, q) * p := by
      rw [Finset.prod_insert hpS]; ring
    have hcop : Nat.Coprime (m * ∏ q ∈ S, q) p := by
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      intro hdvd
      rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
      · exact hm p (Finset.mem_insert_self p S) h
      · obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp h
        have := (Nat.prime_dvd_prime_iff_eq hp (hS' q hq)).mp hpq
        exact hpS (this ▸ hq)
    rw [hprod, sum_divisors_mul_coprime f hcop, hp.divisors]
    have ih' := ih (fun d => ∑ y ∈ ({1, p} : Finset ℕ), f (d * y)) hS' hm'
    rw [ih']
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_powerset_insert hpS, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun U hU => ?_
    have hpU : p ∉ U := fun h => hpS (Finset.mem_powerset.mp hU h)
    rw [Finset.sum_pair (hp.one_lt.ne), Finset.prod_insert hpU, mul_one]
    rw [show x * (∏ q ∈ U, q) * p = x * (p * ∏ q ∈ U, q) by ring]

theorem padicValNat_mul_prod {l : ℕ} [hl : Fact l.Prime] {x : ℕ} (hx0 : x ≠ 0)
    (hlx : ¬ l ∣ x) (U : Finset ℕ) (hU : ∀ p ∈ U, p.Prime) :
    padicValNat l (x * ∏ p ∈ U, p) = if l ∈ U then 1 else 0 := by
  classical
  have hU0 : ∏ p ∈ U, p ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp => (hU p hp).ne_zero
  rw [padicValNat.mul hx0 hU0, padicValNat.eq_zero_of_not_dvd hlx, zero_add,
    ← Nat.factorization_def _ hl.out,
    Nat.factorization_prod (fun p hp => (hU p hp).ne_zero)]
  rw [Finsupp.finsetSum_apply]
  rw [Finset.sum_congr rfl (fun p hp => by rw [(hU p hp).factorization])]
  simp [Finsupp.single_apply]

theorem mul_prod_div {m x : ℕ} (hx : x ∣ m) (hx0 : x ≠ 0) {S U : Finset ℕ} (hUS : U ⊆ S)
    (hS : ∀ p ∈ S, p ≠ 0) :
    (m * ∏ p ∈ S, p) / (x * ∏ p ∈ U, p) = (m / x) * ∏ p ∈ S \ U, p := by
  have hU0 : ∏ p ∈ U, p ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp => hS p (hUS hp)
  have hsplit : ∏ p ∈ S, p = (∏ p ∈ S \ U, p) * ∏ p ∈ U, p := (Finset.prod_sdiff hUS).symm
  obtain ⟨k, rfl⟩ := hx
  rw [Nat.mul_div_cancel_left k (Nat.pos_of_ne_zero hx0), hsplit]
  rw [show x * k * ((∏ p ∈ S \ U, p) * ∏ p ∈ U, p)
      = (x * ∏ p ∈ U, p) * (k * ∏ p ∈ S \ U, p) by ring]
  rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (mul_ne_zero hx0 hU0))]

/-- The `D_l` recursion at `m * l * ∏ S`, reindexed over the subsets `W ⊆ S`. -/
theorem IsDirExp.recursion_insert {a b : ArithmeticFunction ℝ} (hab : IsDirExp a b)
    {l : ℕ} (hl : l.Prime) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hlS : l ∉ S)
    {m : ℕ} (hm0 : m ≠ 0) (hm : ∀ p ∈ insert l S, ¬ p ∣ m) :
    a (m * ∏ p ∈ insert l S, p)
      = ∑ x ∈ m.divisors, ∑ W ∈ S.powerset,
          b (x * ∏ p ∈ insert l W, p) * a ((m / x) * ∏ p ∈ S \ W, p) := by
  classical
  have := Fact.mk hl
  have hS' : ∀ p ∈ insert l S, p.Prime := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hl
    · exact hS p hp
  have hrec := hab.vp_recursion l (m * ∏ p ∈ insert l S, p)
  have hlm : ¬ l ∣ m := hm l (Finset.mem_insert_self l S)
  rw [padicValNat_mul_prod hm0 hlm _ hS', ite_eq_left (Finset.mem_insert_self l S), Nat.cast_one,
    one_mul] at hrec
  rw [hrec, sum_divisors_mul_prod _ m _ hS' hm]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hxm : x ∣ m := Nat.dvd_of_mem_divisors hx
  have hx0 : x ≠ 0 := (Nat.pos_of_mem_divisors hx).ne'
  have hlx : ¬ l ∣ x := fun h => hlm (h.trans hxm)
  rw [Finset.sum_powerset_insert hlS]
  have h1 : ∑ U ∈ S.powerset, (padicValNat l (x * ∏ p ∈ U, p) : ℝ) * b (x * ∏ p ∈ U, p)
      * a ((m * ∏ p ∈ insert l S, p) / (x * ∏ p ∈ U, p)) = 0 := by
    refine Finset.sum_eq_zero fun U hU => ?_
    have hUS := Finset.mem_powerset.mp hU
    have hlU : l ∉ U := fun h => hlS (hUS h)
    rw [padicValNat_mul_prod hx0 hlx U (fun p hp => hS p (hUS hp)), ite_eq_right hlU]
    simp
  rw [h1, zero_add]
  refine Finset.sum_congr rfl fun W hW => ?_
  have hWS := Finset.mem_powerset.mp hW
  have hW' : ∀ p ∈ insert l W, p.Prime := fun p hp => hS' p (Finset.insert_subset_insert l hWS hp)
  rw [padicValNat_mul_prod hx0 hlx (insert l W) hW', ite_eq_left (Finset.mem_insert_self l W),
    Nat.cast_one, one_mul]
  congr 2
  rw [mul_prod_div hxm hx0 (Finset.insert_subset_insert l hWS) (fun p hp => (hS' p hp).ne_zero)]
  rw [Finset.insert_sdiff_insert, Finset.sdiff_insert_of_notMem hlS]

/-- The squarefree moment-cumulant bridge: if `a` at every sub-product of `S` depends only on
the number of factors (`a(∏U) = mm #U`) and `(mm, κ)` satisfy the moment-cumulant recursion,
then `b(∏U) = κ #U` for every nonempty `U ⊆ S`. -/
theorem IsDirExp.sqfree_cumulant {a b : ArithmeticFunction ℝ} (hab : IsDirExp a b)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {mm κ : ℕ → ℝ} (hmk : MomCum mm κ)
    (ha : ∀ U ⊆ S, a (∏ p ∈ U, p) = mm U.card) :
    ∀ n, ∀ U ⊆ S, U.card = n + 1 → b (∏ p ∈ U, p) = κ (n + 1) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro U hUS hcard
    obtain ⟨l, hlU⟩ : U.Nonempty := Finset.card_pos.mp (by omega)
    set U' := U.erase l with hU'
    have hlU' : l ∉ U' := Finset.notMem_erase l U
    have hUeq : U = insert l U' := (Finset.insert_erase hlU).symm
    have hcard' : U'.card = n := by rw [Finset.card_erase_of_mem hlU, hcard]; rfl
    have hU'S : U' ⊆ S := (Finset.erase_subset l U).trans hUS
    have hl : l.Prime := hS l (hUS hlU)
    have hrec := hab.recursion_insert hl (fun p hp => hS p (hU'S hp)) hlU' one_ne_zero (by
      intro p hp h
      have hp' : p ∈ U := hUeq ▸ hp
      exact (hS p (hUS hp')).one_lt.ne' (Nat.dvd_one.mp h))
    simp only [one_mul, Nat.divisors_one, Finset.sum_singleton, Nat.div_one] at hrec
    rw [← hUeq, ha U hUS, hcard] at hrec
    have hrec2 : mm (n + 1)
        = ∑ W ∈ U'.powerset, b (∏ p ∈ insert l W, p) * mm (n - W.card) := by
      rw [hrec]
      refine Finset.sum_congr rfl fun W hW => ?_
      have hWU := Finset.mem_powerset.mp hW
      rw [ha (U' \ W) (Finset.sdiff_subset.trans hU'S), Finset.card_sdiff_of_subset hWU, hcard']
    rw [← Finset.add_sum_erase _ _ (Finset.mem_powerset_self U')] at hrec2
    have hrest : ∑ W ∈ U'.powerset.erase U', b (∏ p ∈ insert l W, p) * mm (n - W.card)
        = ∑ W ∈ U'.powerset.erase U', κ (W.card + 1) * mm (n - W.card) := by
      refine Finset.sum_congr rfl fun W hW => ?_
      have hWne := Finset.ne_of_mem_erase hW
      have hWU := Finset.mem_powerset.mp (Finset.mem_of_mem_erase hW)
      have hlt : W.card < n := hcard' ▸ Finset.card_lt_card (lt_of_le_of_ne hWU hWne)
      have hlW : l ∉ W := fun h => hlU' (hWU h)
      rw [ih W.card hlt (insert l W) (Finset.insert_subset (hUS hlU) (hWU.trans hU'S))
        (Finset.card_insert_of_notMem hlW)]
    have hfull : ∑ W ∈ U'.powerset, κ (W.card + 1) * mm (n - W.card) = mm (n + 1) := by
      rw [Finset.sum_powerset_apply_card (fun j => κ (j + 1) * mm (n - j)), hcard', hmk.2 n]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [nsmul_eq_mul]; ring
    rw [← Finset.add_sum_erase _ _ (Finset.mem_powerset_self U'), hcard'] at hfull
    rw [hrest, ← hUeq, hcard', Nat.sub_self, hmk.1] at hrec2
    rw [Nat.sub_self, hmk.1] at hfull
    linarith

/-- The cumulant sequence of a moment sequence, defined by the recursion. -/
noncomputable def cum (mm : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => mm (n + 1) - ∑ j : Fin n, (n.choose j : ℝ) * cum mm (j + 1) * mm (n - j)

theorem momCum_cum {mm : ℕ → ℝ} (h0 : mm 0 = 1) : MomCum mm (cum mm) := by
  refine ⟨h0, fun n => ?_⟩
  rw [Finset.sum_range_succ, Nat.choose_self, Nat.sub_self, h0, cum,
    ← Fin.sum_univ_eq_sum_range (fun j => (n.choose j : ℝ) * cum mm (j + 1) * mm (n - j))]
  push_cast
  ring

/-! ## Step 1 (C3): the unit part of `F` is the unit part of `ζ` -/

theorem step1_units {q : ℕ} [NeZero q] {a b : ArithmeticFunction ℝ} (hab : IsDirExp a b)
    (hb : ∀ n, 0 ≤ b n) (A : ZMod q → ℝ) (hA : ∀ n, 0 < n → n.Coprime q → a n = A n) :
    ∀ n, 0 < n → n.Coprime q → a n = 1 := by
  classical
  intro n hn hcop
  set g : ZMod q := (n : ZMod q) with hgdef
  have hg : IsUnit g := (ZMod.isUnit_iff_coprime n q).mpr hcop
  set mm : ℕ → ℝ := fun j => A (g ^ j) with hmmdef
  have hA1 : A 1 = 1 := by
    have := hA 1 one_pos (Nat.coprime_one_left q)
    rw [hab.1] at this
    simpa using this.symm
  have hmm0 : mm 0 = 1 := by simp [mm, hA1]
  have hMC : MomCum mm (cum mm) := momCum_cum hmm0
  have hinf := Nat.infinite_setOfPred_prime_and_eq_mod hg
  have hstruct : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ (p : ZMod q) = g) →
      ∀ U ⊆ S, a (∏ p ∈ U, p) = mm U.card := by
    intro S hS U hU
    have hprime : ∀ p ∈ U, p.Prime ∧ (p : ZMod q) = g := fun p hp => hS p (hU hp)
    have hpos : 0 < ∏ p ∈ U, p := Finset.prod_pos (fun p hp => (hprime p hp).1.pos)
    have hcopU : (∏ p ∈ U, p).Coprime q := by
      apply Nat.Coprime.prod_left
      intro p hp
      exact (ZMod.isUnit_iff_coprime p q).mp ((hprime p hp).2 ▸ hg)
    rw [hA _ hpos hcopU]
    simp only [mm]
    congr 1
    push_cast
    rw [Finset.prod_congr rfl (fun p hp => (hprime p hp).2), Finset.prod_const]
  have hκ : ∀ k, 0 ≤ cum mm (k + 1) := by
    intro k
    obtain ⟨S, hS, hcard⟩ := hinf.exists_subset_card_eq (k + 1)
    have hS' : ∀ p ∈ S, p.Prime ∧ (p : ZMod q) = g := fun p hp => hS hp
    have := hab.sqfree_cumulant (fun p hp => (hS' p hp).1) hMC (hstruct S hS') k S
      subset_rfl hcard
    rw [← this]
    exact hb _
  set u : (ZMod q)ˣ := hg.unit with hudef
  have hper : Function.Periodic mm (orderOf u) := by
    intro j
    simp only [mm]
    rw [pow_add]
    have : g ^ orderOf u = 1 := by
      have h1 : (u : ZMod q) = g := hg.unit_spec
      rw [← h1, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
    rw [this, mul_one]
  have hr : 0 < orderOf u := orderOf_pos u
  obtain ⟨_, _, hall⟩ := cumulant_rigidity hMC hκ hr hper
  rw [hA n hn hcop]
  have := hall 1
  simpa [mm] using this


/-! ## Step 2 (C3): unit invariance on the `q`-smooth part -/

/-- `m` is `q`-smooth: every prime factor of `m` divides `q`. -/
def IsQSmooth (q m : ℕ) : Prop := ∀ p, p.Prime → p ∣ m → p ∣ q

theorem IsQSmooth.dvd {q m x : ℕ} (hm : IsQSmooth q m) (hx : x ∣ m) : IsQSmooth q x :=
  fun p hp hpx => hm p hp (hpx.trans hx)

/-- After Step 1, `b` at a product of distinct primes coprime to `q` is `1` on single primes and
`0` otherwise (the log-coefficients of `ζ`). -/
theorem sqfree_b_of_units {q : ℕ} {a b : ArithmeticFunction ℝ} (hab : IsDirExp a b)
    (hunit : ∀ n, 0 < n → n.Coprime q → a n = 1)
    {U : Finset ℕ} (hU : ∀ p ∈ U, p.Prime ∧ ¬ p ∣ q) :
    ∀ n, ∀ V ⊆ U, V.card = n + 1 → b (∏ p ∈ V, p) = if n = 0 then 1 else 0 := by
  classical
  set κ0 : ℕ → ℝ := fun j => if j = 1 then 1 else 0 with hκ0
  have hMC : MomCum (fun _ => 1) κ0 := by
    refine ⟨rfl, fun n => ?_⟩
    rw [Finset.sum_eq_single 0]
    · simp [κ0]
    · intro j _ hj
      simp [κ0, hj]
    · intro h; simp at h
  have ha : ∀ V ⊆ U, a (∏ p ∈ V, p) = (fun _ => (1 : ℝ)) V.card := by
    intro V hV
    apply hunit
    · exact Finset.prod_pos fun p hp => (hU p (hV hp)).1.pos
    · exact Nat.Coprime.prod_left fun p hp =>
        ((hU p (hV hp)).1.coprime_iff_not_dvd).mpr (hU p (hV hp)).2
  intro n V hV hcard
  rw [hab.sqfree_cumulant (fun p hp => (hU p hp).1) hMC ha n V hV hcard]
  simp [κ0]

/-- The divisor split behind Step 2: at `m * l * ∏ S` (with `m` `q`-smooth, `1 < m`), the only
surviving divisor classes are `x = 1` (giving `a(m ∏ S)`) and `x = m`. -/
theorem IsDirExp.split_smooth {q : ℕ} {a b : ArithmeticFunction ℝ} (hab : IsDirExp a b)
    (hunit : ∀ n, 0 < n → n.Coprime q → a n = 1)
    {m : ℕ} (hm1 : 1 < m) (hsm : IsQSmooth q m)
    (hQ : ∀ x, x ∣ m → 1 < x → x < m → ∀ W : Finset ℕ, W.Nonempty →
      (∀ p ∈ W, p.Prime ∧ ¬ p ∣ q) → b (x * ∏ p ∈ W, p) = 0)
    {l : ℕ} (hl : l.Prime) (hlq : ¬ l ∣ q) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime ∧ ¬ p ∣ q)
    (hlS : l ∉ S) :
    a (m * ∏ p ∈ insert l S, p)
      = a (m * ∏ p ∈ S, p) + ∑ W ∈ S.powerset, b (m * ∏ p ∈ insert l W, p) := by
  classical
  have hm0 : m ≠ 0 := by omega
  have hS' : ∀ p ∈ insert l S, p.Prime ∧ ¬ p ∣ q := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact ⟨hl, hlq⟩
    · exact hS p hp
  rw [hab.recursion_insert hl (fun p hp => (hS p hp).1) hlS hm0
    (fun p hp hpm => (hS' p hp).2 (hsm p (hS' p hp).1 hpm))]
  have hsub : ({1, m} : Finset ℕ) ⊆ m.divisors := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Nat.one_mem_divisors.mpr hm0
    · rw [Finset.mem_singleton.mp hx]; exact Nat.mem_divisors_self m hm0
  rw [← Finset.sum_subset hsub]
  · rw [Finset.sum_pair (by omega : (1 : ℕ) ≠ m)]
    congr 1
    · -- x = 1
      simp only [one_mul, Nat.div_one]
      rw [Finset.sum_eq_single ∅]
      · have h1 := sqfree_b_of_units hab hunit hS' 0 {l} (by simp) (by simp)
        simp only [Finset.prod_singleton] at h1
        simp [h1]
      · intro W hW hWne
        have hWS := Finset.mem_powerset.mp hW
        have hlW : l ∉ W := fun h => hlS (hWS h)
        have hcardW : (insert l W).card = W.card + 1 := Finset.card_insert_of_notMem hlW
        have hWc : W.card ≠ 0 := fun h => hWne (Finset.card_eq_zero.mp h)
        rw [sqfree_b_of_units hab hunit hS' W.card (insert l W)
          (Finset.insert_subset_insert l hWS) hcardW, ite_eq_right hWc, zero_mul]
      · intro h; exact absurd (Finset.empty_mem_powerset S) h
    · -- x = m
      refine Finset.sum_congr rfl fun W hW => ?_
      have hWS := Finset.mem_powerset.mp hW
      rw [Nat.div_self (by omega), one_mul]
      rw [hunit _ (Finset.prod_pos fun p hp => (hS p (Finset.sdiff_subset hp)).1.pos)
        (Nat.Coprime.prod_left fun p hp =>
          ((hS p (Finset.sdiff_subset hp)).1.coprime_iff_not_dvd).mpr
            (hS p (Finset.sdiff_subset hp)).2), mul_one]
  · intro x hx hxn
    have hxm : x ∣ m := Nat.dvd_of_mem_divisors hx
    have hx0 : 0 < x := Nat.pos_of_mem_divisors hx
    have hx1 : x ≠ 1 := fun h => hxn (by simp [h])
    have hxm' : x ≠ m := fun h => hxn (by simp [h])
    have hxle : x ≤ m := Nat.le_of_dvd (by omega) hxm
    refine Finset.sum_eq_zero fun W hW => ?_
    have hWS := Finset.mem_powerset.mp hW
    rw [hQ x hxm (by omega) (lt_of_le_of_ne hxle hxm') (insert l W) (Finset.insert_nonempty l W)
      (fun p hp => hS' p (Finset.insert_subset_insert l hWS hp)), zero_mul]

theorem natCast_mul_prod_eq {q : ℕ} {g : ZMod q} (m : ℕ) {S : Finset ℕ}
    (hS : ∀ p ∈ S, (p : ZMod q) = g) :
    ((m * ∏ p ∈ S, p : ℕ) : ZMod q) = (m : ZMod q) * g ^ S.card := by
  push_cast
  rw [Finset.prod_congr rfl hS, Finset.prod_const]

theorem step2_smooth {q : ℕ} [NeZero q] {a b : ArithmeticFunction ℝ} (hab : IsDirExp a b)
    (hb : ∀ n, 0 ≤ b n) (A : ZMod q → ℝ) (hA : ∀ n, 0 < n → a n = A n) :
    ∀ m, 0 < m → IsQSmooth q m →
      (∀ g : (ZMod q)ˣ, A ((m : ZMod q) * g) = A m) ∧
      (1 < m → ∀ W : Finset ℕ, W.Nonempty → (∀ p ∈ W, p.Prime ∧ ¬ p ∣ q) →
        b (m * ∏ p ∈ W, p) = 0) := by
  classical
  have hunit := step1_units hab hb A (fun n hn _ => hA n hn)
  have hA1 : A 1 = 1 := by
    have := hA 1 one_pos
    rw [hab.1] at this
    simpa using this.symm
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm0 hsm
    rcases Nat.lt_or_ge m 2 with hm | hm
    · -- m = 1
      have hm1 : m = 1 := by omega
      subst hm1
      refine ⟨fun g => ?_, fun h => absurd h (lt_irrefl 1)⟩
      obtain ⟨p, _, hp, hpg⟩ := Nat.forall_exists_prime_gt_and_eq_mod g.isUnit 0
      have hpcop : p.Coprime q := (ZMod.isUnit_iff_coprime p q).mp (hpg ▸ g.isUnit)
      have h1 := hunit p hp.pos hpcop
      rw [hA p hp.pos, hpg] at h1
      simp [h1, hA1]
    · have hm1 : 1 < m := by omega
      have hQ : ∀ x, x ∣ m → 1 < x → x < m → ∀ W : Finset ℕ, W.Nonempty →
          (∀ p ∈ W, p.Prime ∧ ¬ p ∣ q) → b (x * ∏ p ∈ W, p) = 0 :=
        fun x hx h1 hlt => (ih x hlt (by omega) (hsm.dvd hx)).2 h1
      -- (P): unit invariance at `m`
      have hP : ∀ g : (ZMod q)ˣ, A ((m : ZMod q) * g) = A m := by
        intro g
        set u : ℕ → ℝ := fun j => A ((m : ZMod q) * (g : ZMod q) ^ j) with hudef
        have hinf := Nat.infinite_setOfPred_prime_and_eq_mod g.isUnit
        have hmono : Monotone u := by
          refine monotone_nat_of_le_succ fun j => ?_
          obtain ⟨S, hS, hcard⟩ := hinf.exists_subset_card_eq (j + 1)
          have hS' : ∀ p ∈ S, p.Prime ∧ (p : ZMod q) = g := fun p hp => hS hp
          have hSq : ∀ p ∈ S, p.Prime ∧ ¬ p ∣ q := by
            intro p hp
            refine ⟨(hS' p hp).1, fun hpq => ?_⟩
            have hcop := (ZMod.isUnit_iff_coprime p q).mp ((hS' p hp).2 ▸ g.isUnit)
            exact (hS' p hp).1.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop hpq)
          obtain ⟨l, hlS⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
          have hSeq : S = insert l (S.erase l) := (Finset.insert_erase hlS).symm
          have hsplit := hab.split_smooth hunit hm1 hsm hQ (hSq l hlS).1 (hSq l hlS).2
            (S := S.erase l) (fun p hp => hSq p (Finset.mem_of_mem_erase hp))
            (Finset.notMem_erase l S)
          rw [← hSeq] at hsplit
          have hpos : ∀ T : Finset ℕ, T ⊆ S → 0 < m * ∏ p ∈ T, p := fun T hT =>
            Nat.mul_pos hm0 (Finset.prod_pos fun p hp => (hS' p (hT hp)).1.pos)
          have hS1 : a (m * ∏ p ∈ S, p) = u (j + 1) := by
            rw [hA _ (hpos S subset_rfl), natCast_mul_prod_eq m (fun p hp => (hS' p hp).2), hcard]
          have hS2 : a (m * ∏ p ∈ S.erase l, p) = u j := by
            rw [hA _ (hpos _ (Finset.erase_subset l S)),
              natCast_mul_prod_eq m (fun p hp => (hS' p (Finset.mem_of_mem_erase hp)).2),
              Finset.card_erase_of_mem hlS, hcard]
            rfl
          have hnn : 0 ≤ ∑ W ∈ (S.erase l).powerset, b (m * ∏ p ∈ insert l W, p) :=
            Finset.sum_nonneg fun W _ => hb _
          rw [hS1, hS2] at hsplit
          linarith
        have hper : Function.Periodic u (orderOf g) := by
          intro j
          simp only [u]
          rw [pow_add, ← Units.val_pow_eq_pow_val g (orderOf g), pow_orderOf_eq_one,
            Units.val_one, mul_one]
        have := eq_of_monotone_periodic hmono (orderOf_pos g) hper 1
        simpa [u] using this
      refine ⟨hP, fun _ W hWne hW => ?_⟩
      -- (Q): vanishing of `b(m ∏ W)`
      obtain ⟨l, hlW⟩ := hWne
      have hWeq : W = insert l (W.erase l) := (Finset.insert_erase hlW).symm
      have hsplit := hab.split_smooth hunit hm1 hsm hQ (hW l hlW).1 (hW l hlW).2
        (S := W.erase l) (fun p hp => hW p (Finset.mem_of_mem_erase hp))
        (Finset.notMem_erase l W)
      rw [← hWeq] at hsplit
      have hAm : ∀ T : Finset ℕ, T ⊆ W → a (m * ∏ p ∈ T, p) = A m := by
        intro T hT
        have hcop : (∏ p ∈ T, p).Coprime q := Nat.Coprime.prod_left fun p hp =>
          ((hW p (hT hp)).1.coprime_iff_not_dvd).mpr (hW p (hT hp)).2
        rw [hA _ (Nat.mul_pos hm0 (Finset.prod_pos fun p hp => (hW p (hT hp)).1.pos))]
        have := hP (ZMod.unitOfCoprime _ hcop)
        rw [ZMod.coe_unitOfCoprime] at this
        rw [← this]
        push_cast
        rfl
      rw [hAm W subset_rfl, hAm _ (Finset.erase_subset l W)] at hsplit
      have hsum0 : ∑ V ∈ (W.erase l).powerset, b (m * ∏ p ∈ insert l V, p) = 0 := by linarith
      have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun V _ => hb _)).mp hsum0
      have := hall (W.erase l) (Finset.mem_powerset_self _)
      rwa [← hWeq] at this

/-- Unit invariance of the residue function `A` at every positive integer. -/
theorem step2_unit_invariant {q : ℕ} [NeZero q] {a b : ArithmeticFunction ℝ}
    (hab : IsDirExp a b) (hb : ∀ n, 0 ≤ b n) (A : ZMod q → ℝ) (hA : ∀ n, 0 < n → a n = A n) :
    ∀ n : ℕ, 0 < n → ∀ g : (ZMod q)ˣ, A ((n : ZMod q) * g) = A n := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn g
    by_cases hsm : IsQSmooth q n
    · exact (step2_smooth hab hb A hA n hn hsm).1 g
    · simp only [IsQSmooth, not_forall] at hsm
      obtain ⟨p, hp, hpn, hpq⟩ := hsm
      obtain ⟨n', rfl⟩ := hpn
      have hn' : 0 < n' := Nat.pos_of_mul_pos_left hn
      have hlt : n' < p * n' := by
        have := hp.one_lt
        nlinarith
      have hcop : p.Coprime q := (hp.coprime_iff_not_dvd).mpr hpq
      set v : (ZMod q)ˣ := ZMod.unitOfCoprime p hcop with hv
      have hv' : (v : ZMod q) = p := ZMod.coe_unitOfCoprime p hcop
      have e1 : A (((p * n' : ℕ) : ZMod q) * g) = A n' := by
        have := ih n' hlt hn' (v * g)
        rw [← this]
        push_cast
        rw [hv']
        ring_nf
      have e2 : A ((p * n' : ℕ) : ZMod q) = A n' := by
        have := ih n' hlt hn' v
        rw [← this]
        push_cast
        rw [hv']
        ring_nf
      rw [e1, e2]

/-- **Steps 1+2 of C3 at the coefficient level.**  If `a = exp⋆(b)` with `b ≥ 0` and `a` is
periodic mod `q` (`a n = A (n mod q)`), then `a(n r) = a(n)` whenever `r` is coprime to `q`;
i.e. `F = D · L(s, χ₀)` with `D` supported on `q`-smooth integers. -/
theorem step2 {q : ℕ} [NeZero q] {a b : ArithmeticFunction ℝ} (hab : IsDirExp a b)
    (hb : ∀ n, 0 ≤ b n) (A : ZMod q → ℝ) (hA : ∀ n, 0 < n → a n = A n) :
    ∀ n r, 0 < n → 0 < r → r.Coprime q → a (n * r) = a n := by
  intro n r hn hr hcop
  rw [hA _ (Nat.mul_pos hn hr), hA n hn]
  have := step2_unit_invariant hab hb A hA n hn (ZMod.unitOfCoprime r hcop)
  rw [ZMod.coe_unitOfCoprime] at this
  push_cast
  exact this


/-! ## Step 3 (C3): `F = ζ · P` with `P` supported on the divisors of `q` -/

/-- `a(p y) = a(y)` whenever `v_p(y) ≥ v_p(q)` (for `p ∣ q` this is the unit `p + q/p^e`). -/
theorem step3_shift {q : ℕ} [NeZero q] {a b : ArithmeticFunction ℝ} (hab : IsDirExp a b)
    (hb : ∀ n, 0 ≤ b n) (A : ZMod q → ℝ) (hA : ∀ n, 0 < n → a n = A n)
    {p : ℕ} (hp : p.Prime) {y : ℕ} (hy : 0 < y)
    (hv : q.factorization p ≤ y.factorization p) : a (p * y) = a y := by
  by_cases hpq : p ∣ q
  · have hq0 : q ≠ 0 := NeZero.ne q
    set e := q.factorization p with he
    set q' := q / p ^ e with hq'
    have hq : p ^ e * q' = q := Nat.ordProj_mul_ordCompl_eq_self q p
    have hpq' : ¬ p ∣ q' := Nat.not_dvd_ordCompl hp hq0
    have hcop : (p + q').Coprime q := by
      rw [← hq]
      refine Nat.Coprime.mul_right (Nat.Coprime.pow_right _ ?_) ?_
      · rw [add_comm, Nat.coprime_add_self_left]
        exact ((hp.coprime_iff_not_dvd).mpr hpq').symm
      · rw [Nat.coprime_add_self_left]
        exact (hp.coprime_iff_not_dvd).mpr hpq'
    have hpe : p ^ e ∣ y := (hp.pow_dvd_iff_le_factorization hy.ne').mpr hv
    have hdiv : q ∣ q' * y := by
      rw [← hq, mul_comm q' y]
      exact Nat.mul_dvd_mul hpe dvd_rfl
    have hzero : ((q' * y : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
    have key : ((p * y : ℕ) : ZMod q)
        = (y : ZMod q) * ((ZMod.unitOfCoprime (p + q') hcop : (ZMod q)ˣ) : ZMod q) := by
      rw [ZMod.coe_unitOfCoprime]
      push_cast at hzero ⊢
      linear_combination -hzero
    rw [hA _ (Nat.mul_pos hp.pos hy), hA _ hy, key, step2_unit_invariant hab hb A hA y hy]
  · have hcop : p.Coprime q := (hp.coprime_iff_not_dvd).mpr hpq
    rw [mul_comm]
    exact step2 hab hb A hA y p hy hp.pos hcop

/-- **Step 3 of C3 at the coefficient level.**  `P := a ⋆ μ` (so `F = ζ · P`) vanishes at every
`n` that does not divide `q`: `P` is a Dirichlet polynomial supported on the divisors of `q`. -/
theorem step3 {q : ℕ} [NeZero q] {a b : ArithmeticFunction ℝ} (hab : IsDirExp a b)
    (hb : ∀ n, 0 ≤ b n) (A : ZMod q → ℝ) (hA : ∀ n, 0 < n → a n = A n) :
    ∀ n, 0 < n → ¬ n ∣ q → (a * (moebius : ArithmeticFunction ℝ)) n = 0 := by
  classical
  intro n hn hnq
  have hq0 : q ≠ 0 := NeZero.ne q
  -- a prime `p` with `v_p(q) < v_p(n)`
  obtain ⟨p, hpv⟩ : ∃ p, q.factorization p < n.factorization p := by
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    exact hnq ((Nat.factorization_le_iff_dvd hn.ne' hq0).mp (fun p => hcon p))
  have hp : p.Prime := by
    by_contra hnp
    rw [Nat.factorization_eq_zero_of_not_prime n hnp] at hpv
    omega
  set k := n.factorization p with hk
  set n' := n / p ^ k with hn'
  have hn_eq : p ^ k * n' = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hk1 : 1 ≤ k := by omega
  have hpn' : ¬ p ∣ n' := Nat.not_dvd_ordCompl hp hn.ne'
  have hn'0 : 0 < n' := by
    rcases Nat.eq_zero_or_pos n' with h | h
    · rw [h, mul_zero] at hn_eq; omega
    · exact h
  have hcop : (p ^ k).Coprime n' := Nat.Coprime.pow_left k ((hp.coprime_iff_not_dvd).mpr hpn')
  rw [mul_comm, mul_apply]
  rw [Nat.sum_divisorsAntidiagonal (f := fun x y => (moebius : ArithmeticFunction ℝ) x * a y)]
  rw [← hn_eq, sum_divisors_mul_coprime _ hcop, Nat.sum_divisors_prime_pow hp]
  -- only `i = 0, 1` survive
  have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range (k + 1) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rw [Finset.mem_range]; omega
  rw [← Finset.sum_subset hsub]
  · rw [Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1), ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun z hz => ?_
    have hzn' : z ∣ n' := Nat.dvd_of_mem_divisors hz
    have hz0 : 0 < z := Nat.pos_of_mem_divisors hz
    have hpz : ¬ p ∣ z := fun h => hpn' (h.trans hzn')
    obtain ⟨w, hw⟩ := hzn'
    have hw0 : 0 < w := by
      rcases Nat.eq_zero_or_pos w with h | h
      · rw [h, mul_zero] at hw; omega
      · exact h
    have hmu : (moebius : ArithmeticFunction ℝ) (p * z)
        = - (moebius : ArithmeticFunction ℝ) z := by
      rw [intCoe_apply, intCoe_apply,
        isMultiplicative_moebius.map_mul_of_coprime ((hp.coprime_iff_not_dvd).mpr hpz),
        moebius_apply_prime hp]
      push_cast; ring
    have e1 : p ^ k * n' / (p ^ 0 * z) = p * (p ^ (k - 1) * w) := by
      apply Nat.div_eq_of_eq_mul_left (Nat.mul_pos (pow_pos hp.pos _) hz0)
      rw [hw, pow_zero, one_mul]
      have : p ^ k = p * p ^ (k - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [this]; ring
    have e2 : p ^ k * n' / (p ^ 1 * z) = p ^ (k - 1) * w := by
      apply Nat.div_eq_of_eq_mul_left (Nat.mul_pos (pow_pos hp.pos _) hz0)
      rw [hw, pow_one]
      have : p ^ k = p * p ^ (k - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [this]; ring
    have hy : 0 < p ^ (k - 1) * w := Nat.mul_pos (pow_pos hp.pos _) hw0
    have hvy : q.factorization p ≤ (p ^ (k - 1) * w).factorization p := by
      rw [Nat.factorization_mul (pow_pos hp.pos _).ne' hw0.ne', Finsupp.add_apply,
        hp.factorization_pow, Finsupp.single_eq_same]
      omega
    have hshift := step3_shift hab hb A hA hp hy hvy
    rw [e1, e2, pow_zero, one_mul, pow_one, hmu, hshift]
    ring
  · intro i hi hi01
    rw [Finset.mem_range] at hi
    have hi2 : 2 ≤ i := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi01
      omega
    refine Finset.sum_eq_zero fun z hz => ?_
    have hns : ¬ Squarefree (p ^ i * z) := by
      intro hsq
      have : p * p ∣ p ^ i * z := by
        have : p * p ∣ p ^ i := by
          rw [← pow_two]; exact pow_dvd_pow p hi2
        exact this.mul_right z
      exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hsq p this))
    rw [intCoe_apply, moebius_eq_zero_of_not_squarefree hns]
    simp



/-! ## Step 4, part A: the `Ω`-graded `q`-smooth sets -/

/-- `Mk q k`: the `q`-smooth integers with exactly `k` prime factors (with multiplicity).  These are
exactly the divisors of `q^k` with `Ω = k`. -/
def Mk (q k : ℕ) : Finset ℕ := (q ^ k).divisors.filter (fun m => cardFactors m = k)

theorem mem_Mk {q k m : ℕ} (hq : q ≠ 0) : m ∈ Mk q k ↔ m ∣ q ^ k ∧ cardFactors m = k := by
  rw [Mk, Finset.mem_filter, Nat.mem_divisors]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, pow_ne_zero k hq⟩, h.2⟩⟩

theorem factorization_le_cardFactors (d p : ℕ) : d.factorization p ≤ cardFactors d := by
  by_cases hd : d = 0
  · simp [hd]
  by_cases hp : p.Prime
  · have h := Nat.ordProj_mul_ordCompl_eq_self d p
    have hc : cardFactors d = d.factorization p + cardFactors (d / p ^ d.factorization p) := by
      conv_lhs => rw [← h]
      rw [cardFactors_mul (pow_ne_zero _ hp.ne_zero) (Nat.ordCompl_pos p hd).ne',
        cardFactors_apply_prime_pow hp]
    omega
  · simp [Nat.factorization_eq_zero_of_not_prime d hp]

theorem dvd_pow_cardFactors {q K d : ℕ} (hq : q ≠ 0) (hd : d ∣ q ^ K) :
    d ∣ q ^ (cardFactors d) := by
  have hqK : q ^ K ≠ 0 := pow_ne_zero K hq
  have hd0 : d ≠ 0 := fun h => by rw [h, zero_dvd_iff] at hd; exact hqK hd
  rw [← Nat.factorization_le_iff_dvd hd0 (pow_ne_zero _ hq), Finsupp.le_def]
  intro p
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  by_cases hpq : q.factorization p = 0
  · have := (Finsupp.le_def.mp ((Nat.factorization_le_iff_dvd hd0 hqK).mpr hd)) p
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hpq, mul_zero] at this
    omega
  · have := factorization_le_cardFactors d p
    have h1 : 1 ≤ q.factorization p := Nat.one_le_iff_ne_zero.mpr hpq
    nlinarith

theorem one_mem_Mk_zero {q : ℕ} (hq : q ≠ 0) : Mk q 0 = {1} := by
  ext m
  rw [mem_Mk hq, pow_zero, Nat.dvd_one, Finset.mem_singleton]
  constructor
  · exact fun h => h.1
  · intro h; subst h; exact ⟨rfl, by simp⟩

/-- **Diagonal convolution identity.** Summing a Dirichlet convolution over `Mk q k` gives the
Cauchy product of the diagonal sums. -/
theorem diag_conv {R : Type*} [CommSemiring R] {q : ℕ} (hq : q ≠ 0) (f g : ℕ → R) (k : ℕ) :
    ∑ m ∈ Mk q k, ∑ x ∈ m.divisorsAntidiagonal, f x.1 * g x.2
      = ∑ j ∈ range (k + 1), (∑ d ∈ Mk q j, f d) * (∑ e ∈ Mk q (k - j), g e) := by
  have hR : ∀ j, (∑ d ∈ Mk q j, f d) * (∑ e ∈ Mk q (k - j), g e)
      = ∑ x ∈ Mk q j ×ˢ Mk q (k - j), f x.1 * g x.2 := by
    intro j; rw [Finset.sum_mul_sum, Finset.sum_product]
  simp_rw [hR]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun x => ⟨cardFactors x.2.1, x.2⟩) (fun y => ⟨y.2.1 * y.2.2, y.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨m, d, e⟩ hx
    simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal] at hx
    obtain ⟨hm, hde, hm0⟩ := hx
    rw [mem_Mk hq] at hm
    have hd0 : d ≠ 0 := fun h => by simp [h] at hde; exact hm0 hde.symm
    have he0 : e ≠ 0 := fun h => by simp [h] at hde; exact hm0 hde.symm
    have hcard : cardFactors d + cardFactors e = k := by
      rw [← cardFactors_mul hd0 he0, hde, hm.2]
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_product, mem_Mk hq]
    refine ⟨by omega, ⟨dvd_pow_cardFactors hq ((Dvd.intro e hde).trans hm.1), trivial⟩, ?_, by omega⟩
    have : k - cardFactors d = cardFactors e := by omega
    rw [this]
    exact dvd_pow_cardFactors hq ((Dvd.intro_left d hde).trans hm.1)
  · rintro ⟨j, d, e⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_product,
      mem_Mk hq] at hy
    obtain ⟨hj, ⟨hd, hdj⟩, ⟨he, hej⟩⟩ := hy
    have hd0 : d ≠ 0 := fun h => by rw [h, zero_dvd_iff] at hd; exact pow_ne_zero _ hq hd
    have he0 : e ≠ 0 := fun h => by rw [h, zero_dvd_iff] at he; exact pow_ne_zero _ hq he
    simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal, mem_Mk hq]
    refine ⟨⟨?_, ?_⟩, trivial, mul_ne_zero hd0 he0⟩
    · have := Nat.mul_dvd_mul hd he
      rwa [← pow_add, show j + (k - j) = k by omega] at this
    · rw [cardFactors_mul hd0 he0]; omega
  · rintro ⟨m, d, e⟩ hx
    simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal] at hx
    simp only [hx.2.1]
  · rintro ⟨j, d, e⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_product, mem_Mk hq] at hy
    simp only [hy.2.1.2]
  · rintro ⟨m, d, e⟩ _
    rfl

/-! Polynomial growth of `#Mk q k`. -/

theorem card_Mk_le {q : ℕ} (hq : q ≠ 0) (k : ℕ) : (Mk q k).card ≤ (k * q + 1) ^ q := by
  have h1 : (Mk q k).card ≤ (q ^ k).divisors.card := Finset.card_filter_le _ _
  refine h1.trans ?_
  rw [Nat.card_divisors (pow_ne_zero k hq)]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  have hbound : ∀ p ∈ (q ^ k).primeFactors, (q ^ k).factorization p + 1 ≤ k * q + 1 := by
    intro p _
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    have := Nat.factorization_lt p hq
    nlinarith
  refine (Finset.prod_le_pow_card _ _ _ hbound).trans ?_
  apply Nat.pow_le_pow_right (by omega)
  rw [Nat.primeFactors_pow q hk.ne']
  exact (Finset.card_le_card (fun _ hp => Nat.mem_divisors.mpr
    ⟨Nat.dvd_of_mem_primeFactors hp, hq⟩)).trans (Nat.card_divisors_le_self q)


section PowerSeriesEval

open Polynomial

/-! ## Step 4, part C: evaluating a formal power series against a polynomial -/

/-- Absolute summability of the power series `F` at the point `z`. -/
def AbsSum (F : PowerSeries ℂ) (z : ℂ) : Prop :=
  Summable fun k => ‖PowerSeries.coeff k F * z ^ k‖

/-- The value `Σ' k, F_k z^k`. -/
noncomputable def pev (F : PowerSeries ℂ) (z : ℂ) : ℂ := ∑' k, PowerSeries.coeff k F * z ^ k

theorem AbsSum.summable {F : PowerSeries ℂ} {z : ℂ} (h : AbsSum F z) :
    Summable fun k => PowerSeries.coeff k F * z ^ k := h.of_norm

theorem AbsSum.add {F G : PowerSeries ℂ} {z : ℂ} (hF : AbsSum F z) (hG : AbsSum G z) :
    AbsSum (F + G) z := by
  unfold AbsSum at *
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) (Summable.add hF hG)
  rw [map_add, add_mul]
  exact norm_add_le _ _

theorem pev_add {F G : PowerSeries ℂ} {z : ℂ} (hF : AbsSum F z) (hG : AbsSum G z) :
    pev (F + G) z = pev F z + pev G z := by
  simp only [pev, map_add, add_mul]
  exact Summable.tsum_add hF.summable hG.summable

theorem AbsSum.mul_C {F : PowerSeries ℂ} {z : ℂ} (hF : AbsSum F z) (c : ℂ) :
    AbsSum (F * PowerSeries.C c) z ∧ pev (F * PowerSeries.C c) z = pev F z * c := by
  have hco : ∀ k, PowerSeries.coeff k (F * PowerSeries.C c) * z ^ k
      = c * (PowerSeries.coeff k F * z ^ k) := by
    intro k; rw [PowerSeries.coeff_mul_C]; ring
  refine ⟨?_, ?_⟩
  · have hn : ∀ k, ‖c * (PowerSeries.coeff k F * z ^ k)‖ = ‖c‖ * ‖PowerSeries.coeff k F * z ^ k‖ :=
      fun k => norm_mul _ _
    simp only [AbsSum, hco, hn]
    exact Summable.mul_left ‖c‖ hF
  · simp only [pev, hco]
    rw [tsum_mul_left]; ring

theorem AbsSum.mul_X {F : PowerSeries ℂ} {z : ℂ} (hF : AbsSum F z) :
    AbsSum (F * PowerSeries.X) z ∧ pev (F * PowerSeries.X) z = pev F z * z := by
  have hsh : ∀ k, PowerSeries.coeff (k + 1) (F * PowerSeries.X) * z ^ (k + 1)
      = z * (PowerSeries.coeff k F * z ^ k) := by
    intro k; rw [PowerSeries.coeff_succ_mul_X]; ring
  have hs : AbsSum (F * PowerSeries.X) z := by
    unfold AbsSum
    rw [← summable_nat_add_iff 1]
    have hn : ∀ k, ‖z * (PowerSeries.coeff k F * z ^ k)‖ = ‖z‖ * ‖PowerSeries.coeff k F * z ^ k‖ :=
      fun k => norm_mul _ _
    simp only [hsh, hn]
    exact Summable.mul_left ‖z‖ hF
  refine ⟨hs, ?_⟩
  unfold pev
  rw [hs.summable.tsum_eq_zero_add]
  simp only [PowerSeries.coeff_zero_mul_X, zero_mul, zero_add, hsh]
  rw [tsum_mul_left]; ring

/-- `pev (F * p) z = pev F z * p(z)` for every polynomial `p`. -/
theorem AbsSum.mul_poly {z : ℂ} (p : ℂ[X]) :
    ∀ F : PowerSeries ℂ, AbsSum F z →
      AbsSum (F * (p : PowerSeries ℂ)) z ∧ pev (F * (p : PowerSeries ℂ)) z = pev F z * p.eval z := by
  induction p using Polynomial.induction_on with
  | C a =>
    intro F hF
    rw [Polynomial.coe_C, eval_C]
    exact hF.mul_C a
  | add p q hp hq =>
    intro F hF
    obtain ⟨hp1, hp2⟩ := hp F hF
    obtain ⟨hq1, hq2⟩ := hq F hF
    rw [Polynomial.coe_add, mul_add]
    refine ⟨hp1.add hq1, ?_⟩
    rw [pev_add hp1 hq1, hp2, hq2, eval_add]; ring
  | monomial n a ih =>
    intro F hF
    obtain ⟨h1, h2⟩ := ih F hF
    have hc : ((C a * X ^ (n + 1) : ℂ[X]) : PowerSeries ℂ)
        = ((C a * X ^ n : ℂ[X]) : PowerSeries ℂ) * PowerSeries.X := by
      rw [pow_succ, ← mul_assoc, Polynomial.coe_mul, Polynomial.coe_X]
    obtain ⟨h3, h4⟩ := h1.mul_X
    rw [hc, ← mul_assoc]
    refine ⟨h3, ?_⟩
    rw [h4, h2]
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    ring

theorem absSum_one (z : ℂ) : AbsSum 1 z := by
  unfold AbsSum
  apply summable_of_ne_finset_zero (s := {0})
  intro k hk
  rw [Finset.mem_singleton] at hk
  simp [PowerSeries.coeff_one, hk]

theorem pev_one (z : ℂ) : pev 1 z = 1 := by
  unfold pev
  simp only [PowerSeries.coeff_one]
  rw [tsum_eq_single 0]
  · simp
  · intro k hk; simp [hk]

theorem pev_coe (p : ℂ[X]) (z : ℂ) : AbsSum (p : PowerSeries ℂ) z ∧ pev (p : PowerSeries ℂ) z = p.eval z := by
  have := AbsSum.mul_poly (z := z) p 1 (absSum_one z)
  rw [one_mul, pev_one, one_mul] at this
  exact this

/-! ## Step 4, part E: no zero of `f` in the open unit disk -/

/-- The algebraic core of Step 4.  Suppose `V f B = X (V f' - V' f)` and `V N = 1` hold as
formal power series, and `B`, `N` converge absolutely at `z₀ ≠ 0`.  Then `z₀` is not a root of
`f ≠ 0`.  Proof: cancel the factor `(X - z₀)^{μ-1}` in `ℂ⟦X⟧` and evaluate at `z₀`. -/
theorem no_root_of_identity {f V : ℂ[X]} {B N : PowerSeries ℂ} {z0 : ℂ}
    (hK : ((V * f : ℂ[X]) : PowerSeries ℂ) * B
      = ((X * (V * derivative f - derivative V * f) : ℂ[X]) : PowerSeries ℂ))
    (hT : (V : PowerSeries ℂ) * N = 1) (hf : f ≠ 0) (hroot : f.eval z0 = 0) (hz0 : z0 ≠ 0)
    (hB : AbsSum B z0) (hN : AbsSum N z0) : False := by
  -- `V(z₀) ≠ 0`
  have hV : V.eval z0 ≠ 0 := by
    have h := (AbsSum.mul_poly (z := z0) V N hN).2
    rw [mul_comm N, hT, pev_one] at h
    intro h0; rw [h0, mul_zero] at h; exact one_ne_zero h
  -- factor out the root
  set μ := rootMultiplicity z0 f with hμdef
  have hμ : 0 < μ := (rootMultiplicity_pos hf).mpr hroot
  set g := f /ₘ (X - C z0) ^ μ with hgdef
  have hfg : (X - C z0) ^ μ * g = f := pow_mul_divByMonic_rootMultiplicity_eq f z0
  have hg : g.eval z0 ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero z0 hf
  obtain ⟨m, hm⟩ : ∃ m, μ = m + 1 := ⟨μ - 1, by omega⟩
  rw [hm] at hfg
  have hf' : derivative f = C ((m + 1 : ℕ) : ℂ) * (X - C z0) ^ m * g
      + (X - C z0) ^ (m + 1) * derivative g := by
    rw [← hfg, derivative_mul, derivative_X_sub_C_pow, Nat.add_sub_cancel]
  set W1 : ℂ[X] := C ((m + 1 : ℕ) : ℂ) * V * g
    + (X - C z0) * (V * derivative g - derivative V * g) with hW1
  have hW : X * (V * derivative f - derivative V * f) = (X - C z0) ^ m * (X * W1) := by
    rw [hf', ← hfg, hW1]; ring
  have hVf : V * f = (X - C z0) ^ m * (V * (X - C z0) * g) := by
    rw [← hfg]; ring
  have hK2 : (((X - C z0) ^ m : ℂ[X]) : PowerSeries ℂ)
      * (((V * (X - C z0) * g : ℂ[X]) : PowerSeries ℂ) * B)
      = (((X - C z0) ^ m : ℂ[X]) : PowerSeries ℂ) * ((X * W1 : ℂ[X]) : PowerSeries ℂ) := by
    rw [← mul_assoc, ← Polynomial.coe_mul, ← Polynomial.coe_mul, ← hVf, ← hW]
    exact hK
  have hne : (((X - C z0) ^ m : ℂ[X]) : PowerSeries ℂ) ≠ 0 := by
    intro h
    apply pow_ne_zero m (X_sub_C_ne_zero z0)
    apply Polynomial.coe_injective ℂ
    rw [h, Polynomial.coe_zero]
  have hK' := mul_left_cancel₀ hne hK2
  -- evaluate both sides at `z₀`
  have hL := (AbsSum.mul_poly (z := z0) (V * (X - C z0) * g) B hB).2
  rw [mul_comm B, hK'] at hL
  rw [(pev_coe _ z0).2] at hL
  simp only [eval_mul, eval_sub, eval_X, eval_C, sub_self, mul_zero, zero_mul, hW1,
    eval_add, add_zero] at hL
  -- `hL : z0 * (↑(m+1) * V(z0) * g(z0)) = 0`
  have : z0 * ((((m + 1 : ℕ) : ℂ)) * eval z0 V * eval z0 g) ≠ 0 := by
    refine mul_ne_zero hz0 (mul_ne_zero (mul_ne_zero ?_ hV) hg)
    exact_mod_cast Nat.succ_ne_zero m
  exact this (by simpa using hL)

/-! ## Step 4, part F: no root in the open disk bounds the top coefficient -/

theorem one_le_norm_multiset_prod (s : Multiset ℂ) (h : ∀ x ∈ s, 1 ≤ ‖x‖) : 1 ≤ ‖s.prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons, norm_mul]
    have ha := h a (Multiset.mem_cons_self a s)
    have hs := ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))
    nlinarith

theorem norm_leadingCoeff_le_one {f : ℂ[X]} (h0 : f.eval 0 = 1)
    (hroots : ∀ z, f.eval z = 0 → 1 ≤ ‖z‖) : ‖f.leadingCoeff‖ ≤ 1 := by
  have hsplit := C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (p := f))
  have he := congrArg (eval 0) hsplit
  rw [eval_mul, eval_C, eval_multiset_prod, h0, Multiset.map_map] at he
  have hprod : 1 ≤ ‖(Multiset.map (eval 0 ∘ fun a => X - C a) f.roots).prod‖ := by
    apply one_le_norm_multiset_prod
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    have hf0 : f ≠ 0 := by rintro rfl; simp at h0
    have hroot : f.eval r = 0 := (mem_roots hf0).mp hr
    simpa using hroots r hroot
  have hn := congrArg (fun x : ℂ => ‖x‖) he
  simp only [norm_mul, norm_one] at hn
  nlinarith [norm_nonneg f.leadingCoeff]


end PowerSeriesEval

/-! ## Step 4, part D: the diagonal generating functions of `(a, b)` -/

/-- `Ω` as a real additive weight. -/
noncomputable def omegaW : ArithmeticFunction ℝ := ⟨fun n => (cardFactors n : ℝ), by simp⟩

theorem omegaW_apply (n : ℕ) : omegaW n = (cardFactors n : ℝ) := rfl

theorem isAdditiveWeight_omegaW : IsAdditiveWeight omegaW := by
  intro m n hm hn
  simp only [omegaW_apply, cardFactors_mul hm hn, Nat.cast_add]

theorem cardDistinctFactors_eq_card (n : ℕ) : cardDistinctFactors n = n.primeFactors.card := by
  rw [cardDistinctFactors_apply, ← List.card_toFinset]; rfl

theorem card_primeFactors_le (q : ℕ) (hq : q ≠ 0) : q.primeFactors.card ≤ q :=
  (Finset.card_le_card (fun _ hp => Nat.mem_divisors.mpr
    ⟨Nat.dvd_of_mem_primeFactors hp, hq⟩)).trans (Nat.card_divisors_le_self q)

theorem cardFactors_le_of_dvd {m n : ℕ} (h : m ∣ n) (hn : n ≠ 0) : cardFactors m ≤ cardFactors n := by
  obtain ⟨k, rfl⟩ := h
  have hm : m ≠ 0 := left_ne_zero_of_mul hn
  have hk : k ≠ 0 := right_ne_zero_of_mul hn
  rw [cardFactors_mul hm hk]; omega

/-- Real identity (R): `k A_k = Σ_j B_j A_{k-j}`, from the `D_Ω` recursion. -/
theorem diag_R {q : ℕ} (hq : q ≠ 0) {a b : ArithmeticFunction ℝ} (hab : IsDirExp a b) (k : ℕ) :
    (k : ℝ) * ∑ m ∈ Mk q k, a m
      = ∑ j ∈ range (k + 1), (∑ d ∈ Mk q j, (cardFactors d : ℝ) * b d)
          * (∑ e ∈ Mk q (k - j), a e) := by
  rw [← diag_conv hq (fun d => (cardFactors d : ℝ) * b d) (fun e => a e) k, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmk := ((mem_Mk hq).mp hm).2
  have h := congrArg (fun f => f m) (hab.pmul_additive isAdditiveWeight_omegaW)
  simp only [pmul_apply, mul_apply, omegaW_apply] at h
  rw [← hmk, mul_comm, h]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-- Real identity (S): `A_k = Σ_j P_j N_{k-j}` where `P = a ⋆ μ` (i.e. `F = ζ · P`). -/
theorem diag_S {q : ℕ} (hq : q ≠ 0) (a : ArithmeticFunction ℝ) (k : ℕ) :
    ∑ m ∈ Mk q k, a m
      = ∑ j ∈ range (k + 1), (∑ d ∈ Mk q j, (a * (moebius : ArithmeticFunction ℝ)) d)
          * (∑ _e ∈ Mk q (k - j), (1 : ℝ)) := by
  rw [← diag_conv hq (fun d => (a * (moebius : ArithmeticFunction ℝ)) d) (fun _ => (1 : ℝ)) k]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm0 : m ≠ 0 := by
    intro h; rw [h, mem_Mk hq, zero_dvd_iff] at hm; exact pow_ne_zero k hq hm.1
  have hfac : a = (a * (moebius : ArithmeticFunction ℝ)) * (zeta : ArithmeticFunction ℝ) := by
    rw [mul_assoc, coe_moebius_mul_coe_zeta, mul_one]
  conv_lhs => rw [hfac]
  rw [mul_apply]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx2 : x.2 ≠ 0 := Nat.right_ne_zero_of_mem_divisorsAntidiagonal hx
  simp [natCoe_apply, zeta_apply, hx2]

/-- Real identity (T): `Σ_j ν_j N_{k-j} = [k = 0]` where `ν_j = Σ_{M_j} μ`. -/
theorem diag_T {q : ℕ} (hq : q ≠ 0) (k : ℕ) :
    ∑ j ∈ range (k + 1), (∑ d ∈ Mk q j, ((moebius d : ℤ) : ℝ)) * (∑ _e ∈ Mk q (k - j), (1 : ℝ))
      = if k = 0 then 1 else 0 := by
  rw [← diag_conv hq (fun d => ((moebius d : ℤ) : ℝ)) (fun _ => (1 : ℝ)) k]
  have hone : ∀ m ∈ Mk q k, ∑ x ∈ m.divisorsAntidiagonal, ((moebius x.1 : ℤ) : ℝ) * 1
      = if m = 1 then 1 else 0 := by
    intro m _
    have h := congrArg (fun f => f m)
      (coe_moebius_mul_coe_zeta (R := ℝ))
    simp only [mul_apply, intCoe_apply, natCoe_apply, zeta_apply, ArithmeticFunction.one_apply] at h
    rw [← h]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx2 : x.2 ≠ 0 := Nat.right_ne_zero_of_mem_divisorsAntidiagonal hx
    simp [hx2]
  rw [Finset.sum_congr rfl hone]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; rw [one_mem_Mk_zero hq]; simp
  · rw [ite_eq_right hk.ne']
    refine Finset.sum_eq_zero fun m hm => ?_
    have hmk := ((mem_Mk hq).mp hm).2
    have : m ≠ 1 := by rintro rfl; simp at hmk; omega
    simp [this]

/-! ## Step 4, part G: assembly -/

section Step4

open Polynomial

/-- `|P(q)| ≤ 1` where `P = a ⋆ μ` and `F = ζ · P`: **log-positivity plus periodicity bound the
top coefficient of `P`.**  Proof: along the diagonal `p^{-s} ↦ t` (for `p ∣ q`) the `q`-smooth
part of `F` becomes `f(t)/V(t)` with `f(t) = Σ_{d ∣ q} P(d) t^{Ω(d)}`.  The log-derivative
coefficients `B_k ≥ 0` satisfy `B_k ≤ k A_k = O(k^{q+1})`, so `Σ B_k t^k` converges on
`|t| < 1`.  Hence `f` has no zero in the open unit disk, so `|lc f| ≤ |f(0)| = 1`, and
`lc f = P(q)`. -/
theorem step4_top_coeff {q : ℕ} [NeZero q] {a b : ArithmeticFunction ℝ} (hab : IsDirExp a b)
    (hb : ∀ n, 0 ≤ b n) (A : ZMod q → ℝ) (hA : ∀ n, 0 < n → a n = A n) :
    |(a * (moebius : ArithmeticFunction ℝ)) q| ≤ 1 := by
  classical
  have hq : q ≠ 0 := NeZero.ne q
  set P : ArithmeticFunction ℝ := a * (moebius : ArithmeticFunction ℝ) with hPdef
  -- the diagonal sequences
  set dA : ℕ → ℝ := fun k => ∑ m ∈ Mk q k, a m with hdA
  set dB : ℕ → ℝ := fun k => ∑ m ∈ Mk q k, (cardFactors m : ℝ) * b m with hdB
  set dN : ℕ → ℝ := fun k => ∑ m ∈ Mk q k, (1 : ℝ) with hdN
  set dP : ℕ → ℝ := fun k => ∑ m ∈ Mk q k, P m with hdP
  set dM : ℕ → ℝ := fun k => ∑ m ∈ Mk q k, ((moebius m : ℤ) : ℝ) with hdM
  -- basic facts
  have ha_nonneg : ∀ n, 0 ≤ a n := hab.nonneg hb
  have hdA_nonneg : ∀ k, 0 ≤ dA k := fun k => Finset.sum_nonneg fun m _ => ha_nonneg m
  have hdB_nonneg : ∀ k, 0 ≤ dB k := fun k =>
    Finset.sum_nonneg fun m _ => mul_nonneg (Nat.cast_nonneg _) (hb m)
  have hdA0 : dA 0 = 1 := by simp only [dA, one_mem_Mk_zero hq, Finset.sum_singleton, hab.1]
  have hR := diag_R hq hab
  have hS := diag_S hq a
  have hT := diag_T hq
  -- `B_k ≤ k A_k`
  have hBle : ∀ k, dB k ≤ (k : ℝ) * dA k := by
    intro k
    rw [hR k]
    have := Finset.single_le_sum (f := fun j => dB j * dA (k - j))
      (fun j _ => mul_nonneg (hdB_nonneg j) (hdA_nonneg _)) (Finset.self_mem_range_succ k)
    simp only [Nat.sub_self, hdA0, mul_one] at this
    exact this
  -- bound on `a`
  set Amax : ℝ := ∑ x : ZMod q, |A x| with hAmax
  have hAmax_nonneg : 0 ≤ Amax := Finset.sum_nonneg fun x _ => abs_nonneg _
  have ha_le : ∀ n, 0 < n → a n ≤ Amax := by
    intro n hn
    rw [hA n hn]
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun x => |A x|)
      (fun x _ => abs_nonneg _) (Finset.mem_univ _))
  have hdN_le : ∀ k, dN k ≤ ((k : ℝ) * q + 1) ^ q := by
    intro k
    simp only [dN, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast card_Mk_le hq k
  have hdA_le : ∀ k, dA k ≤ Amax * dN k := by
    intro k
    simp only [dA, dN, Finset.mul_sum, mul_one]
    refine Finset.sum_le_sum fun m hm => ha_le m ?_
    have := ((mem_Mk hq).mp hm).1
    exact Nat.pos_of_ne_zero fun h => by
      rw [h, zero_dvd_iff] at this; exact pow_ne_zero k hq this
  -- summability on the open unit disk
  have hpoly : ∀ k : ℕ, ((k : ℝ) * q + 1) ^ q ≤ ((q : ℝ) + 1) ^ q * 2 ^ q * ((k : ℝ) ^ q + 1) := by
    intro k
    have h1 : (k : ℝ) * q + 1 ≤ ((q : ℝ) + 1) * ((k : ℝ) + 1) := by
      nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), (Nat.cast_nonneg q : (0 : ℝ) ≤ q)]
    have h2 : ((k : ℝ) + 1) ^ q ≤ 2 ^ q * ((k : ℝ) ^ q + 1) := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        simp only [Nat.cast_zero, zero_add, one_pow]
        have h2q : (1 : ℝ) ≤ 2 ^ q := one_le_pow₀ (by norm_num)
        have h0q : (0 : ℝ) ≤ 0 ^ q := by positivity
        nlinarith
      · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
        calc ((k : ℝ) + 1) ^ q ≤ (2 * k) ^ q :=
              pow_le_pow_left₀ (by positivity) (by linarith) q
          _ = 2 ^ q * (k : ℝ) ^ q := by rw [mul_pow]
          _ ≤ 2 ^ q * ((k : ℝ) ^ q + 1) := by nlinarith [pow_pos (show (0:ℝ) < 2 by norm_num) q]
    calc ((k : ℝ) * q + 1) ^ q ≤ (((q : ℝ) + 1) * ((k : ℝ) + 1)) ^ q :=
          pow_le_pow_left₀ (by positivity) h1 q
      _ = ((q : ℝ) + 1) ^ q * ((k : ℝ) + 1) ^ q := by rw [mul_pow]
      _ ≤ ((q : ℝ) + 1) ^ q * (2 ^ q * ((k : ℝ) ^ q + 1)) := by gcongr
      _ = ((q : ℝ) + 1) ^ q * 2 ^ q * ((k : ℝ) ^ q + 1) := by ring
  set Cq : ℝ := ((q : ℝ) + 1) ^ q * 2 ^ q with hCq
  have hCq_nonneg : 0 ≤ Cq := by positivity
  have hsumN : ∀ z : ℂ, ‖z‖ < 1 → AbsSum (PowerSeries.mk fun k => ((dN k : ℝ) : ℂ)) z := by
    intro z hz
    unfold AbsSum
    have hs1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) q
      (show ‖‖z‖‖ < 1 by rwa [norm_norm])
    have hs2 := summable_geometric_of_lt_one (norm_nonneg z) hz
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
      ((hs1.add hs2).mul_left Cq)
    rw [PowerSeries.coeff_mk, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg fun _ _ => zero_le_one)]
    have hk := (hdN_le k).trans (hpoly k)
    have hzk : 0 ≤ ‖z‖ ^ k := by positivity
    calc dN k * ‖z‖ ^ k ≤ Cq * ((k : ℝ) ^ q + 1) * ‖z‖ ^ k := by gcongr
      _ = Cq * ((k : ℝ) ^ q * ‖z‖ ^ k + ‖z‖ ^ k) := by ring
  have hsumB : ∀ z : ℂ, ‖z‖ < 1 → AbsSum (PowerSeries.mk fun k => ((dB k : ℝ) : ℂ)) z := by
    intro z hz
    unfold AbsSum
    have hs1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) (q + 1)
      (show ‖‖z‖‖ < 1 by rwa [norm_norm])
    have hs2 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
      (show ‖‖z‖‖ < 1 by rwa [norm_norm])
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
      ((hs1.add hs2).mul_left (Amax * Cq))
    rw [PowerSeries.coeff_mk, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hdB_nonneg k)]
    have hk : dB k ≤ Amax * Cq * ((k : ℝ) ^ (q + 1) + (k : ℝ) ^ 1) := by
      calc dB k ≤ (k : ℝ) * dA k := hBle k
        _ ≤ (k : ℝ) * (Amax * dN k) := by gcongr; exact hdA_le k
        _ ≤ (k : ℝ) * (Amax * (Cq * ((k : ℝ) ^ q + 1))) := by
            gcongr; exact (hdN_le k).trans (hpoly k)
        _ = Amax * Cq * ((k : ℝ) ^ (q + 1) + (k : ℝ) ^ 1) := by ring
    have hzk : 0 ≤ ‖z‖ ^ k := by positivity
    calc dB k * ‖z‖ ^ k ≤ Amax * Cq * ((k : ℝ) ^ (q + 1) + (k : ℝ) ^ 1) * ‖z‖ ^ k := by gcongr
      _ = Amax * Cq * ((k : ℝ) ^ (q + 1) * ‖z‖ ^ k + (k : ℝ) ^ 1 * ‖z‖ ^ k) := by ring
  -- the polynomials `f` and `V`
  have hdP_zero : ∀ j, cardFactors q < j → dP j = 0 := by
    intro j hj
    refine Finset.sum_eq_zero fun m hm => ?_
    obtain ⟨hmq, hmj⟩ := (mem_Mk hq).mp hm
    have hm0 : 0 < m := Nat.pos_of_ne_zero fun h => by
      rw [h, zero_dvd_iff] at hmq; exact pow_ne_zero j hq hmq
    by_contra hne
    have hdvd : m ∣ q := by
      by_contra hnd; exact hne (step3 hab hb A hA m hm0 hnd)
    have := cardFactors_le_of_dvd hdvd hq
    omega
  have hdM_zero : ∀ j, q < j → dM j = 0 := by
    intro j hj
    refine Finset.sum_eq_zero fun m hm => ?_
    obtain ⟨hmq, hmj⟩ := (mem_Mk hq).mp hm
    have hm0 : m ≠ 0 := fun h => by
      rw [h, zero_dvd_iff] at hmq; exact pow_ne_zero j hq hmq
    by_contra hne
    have hsq : Squarefree m := moebius_ne_zero_iff_squarefree.mp (by exact_mod_cast hne)
    have h1 : cardDistinctFactors m = cardFactors m :=
      (cardDistinctFactors_eq_cardFactors_iff_squarefree hm0).mpr hsq
    have h2 : m.primeFactors ⊆ q.primeFactors := by
      have := Nat.primeFactors_mono hmq (pow_ne_zero j hq)
      rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · omega
      · rwa [Nat.primeFactors_pow q hj0.ne'] at this
    have h3 := Finset.card_le_card h2
    rw [← cardDistinctFactors_eq_card] at h3
    have h4 := card_primeFactors_le q hq
    omega
  set f : ℂ[X] := ∑ j ∈ range (cardFactors q + 1), C ((dP j : ℝ) : ℂ) * X ^ j with hfdef
  set V : ℂ[X] := ∑ j ∈ range (q + 1), C ((dM j : ℝ) : ℂ) * X ^ j with hVdef
  have hfcoeff : ∀ j, f.coeff j = ((dP j : ℝ) : ℂ) := by
    intro j
    rw [hfdef, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · rw [Finset.mem_range, not_lt] at h
      rw [hdP_zero j (by omega)]; simp
  have hVcoeff : ∀ j, V.coeff j = ((dM j : ℝ) : ℂ) := by
    intro j
    rw [hVdef, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · rw [Finset.mem_range, not_lt] at h
      rw [hdM_zero j (by omega)]; simp
  -- the formal identities in `ℂ⟦X⟧`
  set psA : PowerSeries ℂ := PowerSeries.mk fun k => ((dA k : ℝ) : ℂ) with hpsA
  set psB : PowerSeries ℂ := PowerSeries.mk fun k => ((dB k : ℝ) : ℂ) with hpsB
  set psN : PowerSeries ℂ := PowerSeries.mk fun k => ((dN k : ℝ) : ℂ) with hpsN
  have eS : psA = (f : PowerSeries ℂ) * psN := by
    ext k
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i (f : PowerSeries ℂ) * PowerSeries.coeff j psN)]
    simp only [hpsA, hpsN, PowerSeries.coeff_mk, Polynomial.coeff_coe, hfcoeff]
    have hS' : dA k = ∑ j ∈ range (k + 1), dP j * dN (k - j) := hS k
    rw [hS']
    push_cast
    rfl
  have eT : (V : PowerSeries ℂ) * psN = 1 := by
    ext k
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i (V : PowerSeries ℂ) * PowerSeries.coeff j psN)]
    simp only [hpsN, PowerSeries.coeff_mk, Polynomial.coeff_coe, hVcoeff, PowerSeries.coeff_one]
    have := hT k
    have hc : ((∑ j ∈ range (k + 1), dM j * dN (k - j) : ℝ) : ℂ) = if k = 0 then 1 else 0 := by
      rw [show (∑ j ∈ range (k + 1), dM j * dN (k - j)) = if k = 0 then 1 else 0 from this]
      split_ifs <;> simp
    rw [← hc]
    push_cast
    rfl
  have eR : psB * psA = PowerSeries.X * PowerSeries.derivative ℂ psA := by
    ext k
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i psB * PowerSeries.coeff j psA)]
    simp only [hpsA, hpsB, PowerSeries.coeff_mk]
    rcases k with _ | k
    · simp only [PowerSeries.coeff_zero_X_mul, Finset.sum_range_one, Nat.sub_zero]
      have h0 : ((0 : ℕ) : ℝ) * dA 0 = ∑ j ∈ range (0 + 1), dB j * dA (0 - j) := hR 0
      simp only [Nat.cast_zero, zero_mul, zero_add, Finset.sum_range_one, Nat.sub_zero] at h0
      rw [← Complex.ofReal_mul, ← h0, Complex.ofReal_zero]
    · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, PowerSeries.coeff_mk]
      have hR' : ((k + 1 : ℕ) : ℝ) * dA (k + 1)
          = ∑ j ∈ range (k + 1 + 1), dB j * dA (k + 1 - j) := hR (k + 1)
      have hc : ∑ x ∈ range (k + 1).succ, ((dB x : ℝ) : ℂ) * ((dA (k + 1 - x) : ℝ) : ℂ)
          = (((∑ j ∈ range (k + 1 + 1), dB j * dA (k + 1 - j)) : ℝ) : ℂ) := by
        push_cast; rfl
      rw [hc, ← hR']
      push_cast
      ring
  -- derived identity (K)
  have eVA : (V : PowerSeries ℂ) * psA = f := by
    rw [eS, mul_left_comm, eT, mul_one]
  have eD : (V : PowerSeries ℂ) * PowerSeries.derivative ℂ psA
      + psA * PowerSeries.derivative ℂ (V : PowerSeries ℂ)
      = PowerSeries.derivative ℂ (f : PowerSeries ℂ) := by
    rw [← eVA, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  have eK : ((V * f : ℂ[X]) : PowerSeries ℂ) * psB
      = ((X * (V * derivative f - derivative V * f) : ℂ[X]) : PowerSeries ℂ) := by
    rw [Polynomial.coe_mul, Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_mul,
      Polynomial.coe_mul, Polynomial.coe_X, ← PowerSeries.derivative_coe,
      ← PowerSeries.derivative_coe, ← eVA]
    have : (V : PowerSeries ℂ) * PowerSeries.derivative ℂ psA
        = PowerSeries.derivative ℂ ((V : PowerSeries ℂ) * psA)
          - psA * PowerSeries.derivative ℂ (V : PowerSeries ℂ) := by
      rw [eVA, ← eD]; ring
    calc (V : PowerSeries ℂ) * ((V : PowerSeries ℂ) * psA) * psB
        = (V : PowerSeries ℂ) * (V : PowerSeries ℂ) * (psB * psA) := by ring
      _ = (V : PowerSeries ℂ) * (V : PowerSeries ℂ)
            * (PowerSeries.X * PowerSeries.derivative ℂ psA) := by rw [eR]
      _ = PowerSeries.X * ((V : PowerSeries ℂ)
            * ((V : PowerSeries ℂ) * PowerSeries.derivative ℂ psA)) := by ring
      _ = _ := by rw [this]; ring
  -- `f(0) = 1`
  have hf0 : f.eval 0 = 1 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, hfcoeff]
    simp only [dP, one_mem_Mk_zero hq, Finset.sum_singleton, hPdef, mul_apply_one, intCoe_apply,
      moebius_apply_one, hab.1]
    norm_num
  have hfne : f ≠ 0 := by rintro h; rw [h, eval_zero] at hf0; exact zero_ne_one hf0
  -- no root of `f` in the open unit disk
  have hroots : ∀ z, f.eval z = 0 → 1 ≤ ‖z‖ := by
    intro z hz
    by_contra hlt
    rw [not_le] at hlt
    have hz0 : z ≠ 0 := by rintro rfl; rw [hf0] at hz; exact one_ne_zero hz
    exact no_root_of_identity eK eT hfne hz hz0 (hsumB z hlt) (hsumN z hlt)
  have hlc := norm_leadingCoeff_le_one hf0 hroots
  -- `lc f = P(q)` (or `P(q) = 0`)
  have hdPq : dP (cardFactors q) = P q := by
    simp only [dP]
    rw [Finset.sum_eq_single q]
    · intro m hm hmq
      obtain ⟨hmdvd, hmk⟩ := (mem_Mk hq).mp hm
      have hm0 : 0 < m := Nat.pos_of_ne_zero fun h => by
        rw [h, zero_dvd_iff] at hmdvd; exact pow_ne_zero _ hq hmdvd
      by_contra hne
      have hdvd : m ∣ q := by
        by_contra hnd; exact hne (step3 hab hb A hA m hm0 hnd)
      obtain ⟨c, hc⟩ := hdvd
      have hc0 : c ≠ 0 := by rintro rfl; rw [mul_zero] at hc; exact hq hc
      have := cardFactors_mul hm0.ne' hc0
      rw [← hc, hmk] at this
      have hc1 : cardFactors c = 0 := by omega
      rcases (cardFactors_eq_zero_iff_eq_zero_or_one.mp hc1) with h | h
      · exact hc0 h
      · rw [h, mul_one] at hc; exact hmq hc.symm
    · intro hqm
      exact absurd ((mem_Mk hq).mpr
        ⟨dvd_pow_cardFactors hq (dvd_pow_self q one_ne_zero : q ∣ q ^ 1), rfl⟩) hqm
  by_cases hPq : P q = 0
  · rw [hPq, abs_zero]; exact zero_le_one
  · have hdeg : f.natDegree = cardFactors q := by
      apply le_antisymm
      · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro N hN
        rw [hfcoeff, hdP_zero N hN]; simp
      · apply Polynomial.le_natDegree_of_ne_zero
        rw [hfcoeff, hdPq]
        exact_mod_cast hPq
    have hlc' : f.leadingCoeff = ((P q : ℝ) : ℂ) := by
      rw [Polynomial.leadingCoeff, hdeg, hfcoeff, hdPq]
    rw [hlc', Complex.norm_real, Real.norm_eq_abs] at hlc
    exact hlc

/-- **C3 at the coefficient level (Steps 1-4).**  If `a = exp⋆(b)` with `b ≥ 0` (P2), `a` is
periodic mod `q` (the KP99 input), and the top coefficient of `P = F/ζ` satisfies
`|P(q)| = √q` (the coefficient form of the degree-1 FE `q^{s/2} P(s) = ε q^{(1-s)/2} P(1-s)`),
then `q = 1` and `a ≡ 1`, i.e. `F = ζ`. -/
theorem classP_eq_zeta {q : ℕ} [NeZero q] {a b : ArithmeticFunction ℝ} (hab : IsDirExp a b)
    (hb : ∀ n, 0 ≤ b n) (A : ZMod q → ℝ) (hA : ∀ n, 0 < n → a n = A n)
    (hFE : |(a * (moebius : ArithmeticFunction ℝ)) q| = √q) :
    q = 1 ∧ ∀ n, 0 < n → a n = 1 := by
  have hq : q ≠ 0 := NeZero.ne q
  have h1 := step4_top_coeff hab hb A hA
  rw [hFE] at h1
  have hq1 : (q : ℝ) ≤ 1 := by
    have hs := Real.sq_sqrt (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
    have hs0 := Real.sqrt_nonneg (q : ℝ)
    nlinarith
  have hq' : q = 1 := by
    have : q ≤ 1 := by exact_mod_cast hq1
    omega
  refine ⟨hq', fun n hn => ?_⟩
  have hunit := step1_units hab hb A (fun m hm _ => hA m hm)
  exact hunit n hn (by rw [hq']; exact Nat.coprime_one_right n)

end Step4

/-! ## Non-vacuity and sharpness of `classP_eq_zeta` -/

/-- The log-coefficients of `ζ`: `b(n) = Λ(n)/log n`. -/
noncomputable def zetaLogCoeff : ArithmeticFunction ℝ :=
  ⟨fun n => vonMangoldt n / Real.log n, by simp⟩

theorem zetaLogCoeff_apply (n : ℕ) : zetaLogCoeff n = vonMangoldt n / Real.log n := rfl

theorem zetaLogCoeff_nonneg (n : ℕ) : 0 ≤ zetaLogCoeff n := by
  rw [zetaLogCoeff_apply]
  exact div_nonneg vonMangoldt_nonneg (Real.log_natCast_nonneg n)

/-- `ζ = exp⋆(Λ/log)`: the relation `IsDirExp` is satisfiable. -/
theorem zeta_isDirExp : IsDirExp (zeta : ArithmeticFunction ℝ) zetaLogCoeff := by
  refine ⟨by simp [natCoe_apply], ?_⟩
  have hb : zetaLogCoeff.pmul log = (vonMangoldt : ArithmeticFunction ℝ) := by
    ext n
    rw [pmul_apply, zetaLogCoeff_apply, log_apply]
    by_cases hn : Real.log n = 0
    · have h01 : n = 0 ∨ n = 1 := by
        rcases Real.log_eq_zero.mp hn with h | h | h
        · left; exact_mod_cast h
        · right; exact_mod_cast h
        · have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          linarith
      rcases h01 with rfl | rfl <;> simp
    · field_simp
  rw [hb, vonMangoldt_mul_zeta]
  ext n
  rw [pmul_apply, log_apply, natCoe_apply, zeta_apply]
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn]

/-- **Non-vacuity.** `ζ` satisfies every hypothesis of `classP_eq_zeta` with `q = 1`. -/
theorem classP_hypotheses_satisfiable :
    IsDirExp (zeta : ArithmeticFunction ℝ) zetaLogCoeff ∧ (∀ n, 0 ≤ zetaLogCoeff n) ∧
      (∀ n, 0 < n → (zeta : ArithmeticFunction ℝ) n = (fun _ : ZMod 1 => (1 : ℝ)) (n : ZMod 1)) ∧
      |((zeta : ArithmeticFunction ℝ) * (moebius : ArithmeticFunction ℝ)) 1| = √((1 : ℕ) : ℝ) := by
  refine ⟨zeta_isDirExp, zetaLogCoeff_nonneg, fun n hn => ?_, ?_⟩
  · simp [natCoe_apply, zeta_apply, hn.ne']
  · rw [coe_zeta_mul_coe_moebius]; simp

/-- Coefficients of `ζ(s)(1 + 2^{1/2-s})` (conductor `2`, root number `+1`). -/
noncomputable def a2 : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else 1 + (if 2 ∣ n then √2 else 0), by simp⟩

theorem a2_apply (n : ℕ) : a2 n = if n = 0 then 0 else 1 + (if 2 ∣ n then √2 else 0) := rfl

theorem a2_periodic (n : ℕ) (hn : 0 < n) :
    a2 n = (fun x : ZMod 2 => if x = 0 then 1 + √2 else 1) (n : ZMod 2) := by
  rw [a2_apply, ite_eq_right hn.ne']
  simp only [ZMod.natCast_eq_zero_iff]
  split_ifs <;> simp

/-- `P = F/ζ = 1 + √2·2^{-s}` has top coefficient `P(2) = √2 = √q`: the FE input of
`classP_eq_zeta` holds with `q = 2`. -/
theorem a2_topcoeff : |(a2 * (moebius : ArithmeticFunction ℝ)) 2| = √((2 : ℕ) : ℝ) := by
  rw [mul_apply]
  have d2 : Nat.divisorsAntidiagonal 2 = {(1, 2), (2, 1)} := by decide
  rw [d2, Finset.sum_pair (by decide)]
  simp only [a2_apply, intCoe_apply, moebius_apply_prime Nat.prime_two, moebius_apply_one]
  norm_num

/-- **Sharpness.**  `ζ(s)(1 + 2^{1/2-s})` satisfies periodicity mod `2` and `|P(2)| = √2`, but
`q = 2 ≠ 1`.  This is consistent with `classP_eq_zeta` only because P2 fails:
`b(4) = -1/2 < 0`. -/
theorem a2_logcoeff_four {b : ArithmeticFunction ℝ} (h : IsDirExp a2 b) : b 4 = -1 / 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hs2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2 := congrArg (fun f => f 2) h.2
  have h4 := congrArg (fun f => f 4) h.2
  simp only [pmul_apply, mul_apply, log_apply] at h2 h4
  have d2 : Nat.divisorsAntidiagonal 2 = {(1, 2), (2, 1)} := by decide
  have d4 : Nat.divisorsAntidiagonal 4 = {(1, 4), (2, 2), (4, 1)} := by decide
  rw [d2] at h2
  rw [d4] at h4
  simp [a2_apply] at h2 h4
  norm_num at h2 h4
  rw [hlog4] at h4
  have hb2 : b 2 = 1 + √2 := by linarith
  rw [hb2] at h4
  have : (1 + 2 * b 4) * Real.log 2 = 0 := by nlinarith
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · exact absurd h hlog2.ne'

/-! ## C9(i) negative control: `F = ζ(s)(1 + 4·2^{-s} + 2·4^{-s})` -/

/-- The Dirichlet polynomial `P(s) = 1 + 4·2^{-s} + 2·4^{-s}`. -/
noncomputable def ncP (s : ℂ) : ℂ := 1 + 4 * (2 : ℂ) ^ (-s) + 2 * (4 : ℂ) ^ (-s)

theorem four_cpow (z : ℂ) : (4 : ℂ) ^ z = ((2 : ℂ) ^ z) ^ 2 := by
  rw [Complex.cpow_def_of_ne_zero (by norm_num), Complex.cpow_def_of_ne_zero (by norm_num),
    ← Complex.exp_nat_mul]
  congr 1
  have h4 : Complex.log 4 = 2 * Complex.log 2 := by
    have e4 : (4 : ℂ) = ((4 : ℝ) : ℂ) := by norm_num
    have e2 : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
    rw [e4, e2, ← Complex.ofReal_log (by norm_num), ← Complex.ofReal_log (by norm_num)]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  rw [h4]; push_cast; ring

/-- `2^s · P(s) = 2^s + 4 + 2^{1-s}`, which is invariant under `s ↦ 1 - s`. -/
theorem nc_twoPow_mul (s : ℂ) : (2 : ℂ) ^ s * ncP s = (2 : ℂ) ^ s + 4 + (2 : ℂ) ^ (1 - s) := by
  have h1 : (2 : ℂ) ^ s * (2 : ℂ) ^ (-s) = 1 := by
    rw [← Complex.cpow_add _ _ (by norm_num)]; simp
  have h2 : (2 : ℂ) ^ (1 - s) = 2 * (2 : ℂ) ^ (-s) := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ (by norm_num), Complex.cpow_one]
  rw [ncP, four_cpow, h2]
  linear_combination (4 + 2 * (2 : ℂ) ^ (-s)) * h1

/-- The completed function `Λ_F(s) = Λ_ζ(s)·(2^s + 4 + 2^{1-s})` (conductor `q = 4`). -/
noncomputable def ncLambda (s : ℂ) : ℂ :=
  completedRiemannZeta s * ((2 : ℂ) ^ s + 4 + (2 : ℂ) ^ (1 - s))

/-- The functional equation `Λ_F(1 - s) = Λ_F(s)` (root number `+1`). -/
theorem ncLambda_one_sub (s : ℂ) : ncLambda (1 - s) = ncLambda s := by
  simp only [ncLambda, completedRiemannZeta_one_sub, sub_sub_cancel]
  ring

/-- `Λ_F(s) = Γ_ℝ(s) · 2^s · ζ(s) P(s)` for `Re s > 0`, i.e. `Λ_F = (4/π)^{s/2} Γ(s/2) F(s)`. -/
theorem ncLambda_eq (s : ℂ) (hs : 0 < s.re) :
    ncLambda s = Complex.Gammaℝ s * (2 : ℂ) ^ s * (riemannZeta s * ncP s) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hG : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hs
  rw [ncLambda, ← nc_twoPow_mul, riemannZeta_def_of_ne_zero hs0]
  field_simp

/-- The zero `s₀ = log₂(2 + √2) + iπ/log 2`. -/
noncomputable def ncZero : ℂ :=
  ((Real.log (2 + √2) / Real.log 2 : ℝ) : ℂ) + ((Real.pi / Real.log 2 : ℝ) : ℂ) * Complex.I

theorem ncZero_re : 1 < ncZero.re := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hre : ncZero.re = Real.log (2 + √2) / Real.log 2 := by
    rw [ncZero, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re,
      mul_zero, add_zero]
  rw [hre, one_lt_div hlog2]
  apply Real.log_lt_log (by norm_num)
  have : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
  linarith

theorem two_cpow_neg_ncZero : (2 : ℂ) ^ (-ncZero) = ((√2 / 2 - 1 : ℝ) : ℂ) := by
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hs2 : 0 < 2 + √2 := by positivity
  have e2 : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  rw [Complex.cpow_def_of_ne_zero (by norm_num), e2, ← Complex.ofReal_log (by norm_num)]
  have hlog2c : ((Real.log 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlog2
  have harg : (Real.log 2 : ℂ) * -ncZero
      = ((-Real.log (2 + √2) : ℝ) : ℂ) + (-(Real.pi : ℂ)) * Complex.I := by
    simp only [ncZero]
    push_cast
    field_simp
    ring
  rw [harg, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hs2]
  have hpi : Complex.exp (-(Real.pi : ℂ) * Complex.I) = -1 := by
    rw [neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
  rw [hpi]
  have hval : (2 + √2)⁻¹ = 1 - √2 / 2 := by
    have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    field_simp
    nlinarith
  rw [hval]
  push_cast
  ring

/-- `P(s₀) = 0`: `2^{-s₀} = √2/2 - 1` is a root of `2x² + 4x + 1`. -/
theorem ncP_ncZero : ncP ncZero = 0 := by
  rw [ncP, four_cpow, two_cpow_neg_ncZero]
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have : (1 + 4 * (√2 / 2 - 1) + 2 * (√2 / 2 - 1) ^ 2 : ℝ) = 0 := by nlinarith
  exact_mod_cast this

/-- `F(s₀) = ζ(s₀) P(s₀) = 0` with `Re s₀ > 1`: an `F` with nonnegative multiplicative coefficients
and an exact conductor-4 FE can vanish in `σ > 1`. -/
theorem nc_F_vanishes : 1 < ncZero.re ∧ riemannZeta ncZero * ncP ncZero = 0 :=
  ⟨ncZero_re, by rw [ncP_ncZero, mul_zero]⟩

/-- Coefficients of `ζ(s)(1 + 4·2^{-s} + 2·4^{-s})`: `a(n) = 1 + 4[2 ∣ n] + 2[4 ∣ n]`. -/
noncomputable def a9 : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else 1 + (if 2 ∣ n then 4 else 0) + (if 4 ∣ n then 2 else 0),
    by simp⟩

theorem a9_apply (n : ℕ) : a9 n
    = if n = 0 then 0 else 1 + (if 2 ∣ n then 4 else 0) + (if 4 ∣ n then 2 else 0) := rfl

theorem a9_nonneg (n : ℕ) : 0 ≤ a9 n := by
  rw [a9_apply]; split_ifs <;> norm_num

/-- The log-coefficient of `F` at `4` is `-11/2 < 0`: P2 fails. -/
theorem a9_logcoeff_four {b : ArithmeticFunction ℝ} (h : IsDirExp a9 b) : b 4 = -11 / 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have h2 := congrArg (fun f => f 2) h.2
  have h4 := congrArg (fun f => f 4) h.2
  simp only [pmul_apply, mul_apply, log_apply] at h2 h4
  have d2 : Nat.divisorsAntidiagonal 2 = {(1, 2), (2, 1)} := by decide
  have d4 : Nat.divisorsAntidiagonal 4 = {(1, 4), (2, 2), (4, 1)} := by decide
  rw [d2] at h2
  rw [d4] at h4
  simp [a9_apply] at h2 h4
  norm_num at h2 h4
  rw [hlog4] at h4
  have hb2 : b 2 = 5 := by linarith
  rw [hb2] at h4
  have : (11 + 2 * b 4) * Real.log 2 = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · exact absurd h hlog2.ne'

/-! ## C9(ii) negative control: the KP element of conductor 5 fails P2 -/

/-- Residue function of `ζ(s; ±1 mod 5) + φ 5^{-s} ζ(s)`. -/
noncomputable def A5 : ZMod 5 → ℝ :=
  fun x => if x = 0 then (1 + √5) / 2 else if x = 1 ∨ x = 4 then 1 else 0

noncomputable def a5 : ArithmeticFunction ℝ := ⟨fun n => if n = 0 then 0 else A5 n, by simp⟩

theorem a5_apply (n : ℕ) : a5 n = if n = 0 then 0 else A5 n := rfl

theorem A5_one : A5 1 = 1 := by
  have h0 : (1 : ZMod 5) ≠ 0 := by decide
  simp [A5, h0]

theorem A5_two : A5 2 = 0 := by
  have h0 : (2 : ZMod 5) ≠ 0 := by decide
  have h1 : (2 : ZMod 5) ≠ 1 := by decide
  have h4 : (2 : ZMod 5) ≠ 4 := by decide
  simp [A5, h0, h1, h4]

theorem A5_three : A5 3 = 0 := by
  have h0 : (3 : ZMod 5) ≠ 0 := by decide
  have h1 : (3 : ZMod 5) ≠ 1 := by decide
  have h4 : (3 : ZMod 5) ≠ 4 := by decide
  simp [A5, h0, h1, h4]

theorem A5_four : A5 4 = 1 := by
  have h0 : (4 : ZMod 5) ≠ 0 := by decide
  simp [A5, h0]

theorem a5_nonneg (n : ℕ) : 0 ≤ a5 n := by
  rw [a5_apply, A5]
  have : 0 ≤ (1 + √5) / 2 := by positivity
  split_ifs <;> linarith

theorem a5_periodic (n : ℕ) (hn : 0 < n) : a5 n = A5 n := by
  rw [a5_apply, ite_eq_right hn.ne']

/-- The log-coefficient at `2·7·17·37 = 8806` (four primes `≡ 2 mod 5`) is the fourth cumulant
of the moment sequence `(1,0,1,0,…)`, namely `κ₄(log cosh) = -2 < 0`: P2 fails. -/
theorem a5_logcoeff {b : ArithmeticFunction ℝ} (h : IsDirExp a5 b) :
    b (2 * 7 * 17 * 37) = -2 := by
  classical
  set S : Finset ℕ := {2, 7, 17, 37} with hSdef
  have hSp : ∀ p ∈ S, p.Prime := by
    intro p hp
    simp only [hSdef, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> norm_num
  have hS2 : ∀ p ∈ S, (p : ZMod 5) = 2 := by
    intro p hp
    simp only [hSdef, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  set mm : ℕ → ℝ := fun j => A5 ((2 : ZMod 5) ^ j) with hmm
  have hmm0 : mm 0 = 1 := by simp only [mm, pow_zero, A5_one]
  have ha : ∀ U ⊆ S, a5 (∏ p ∈ U, p) = mm U.card := by
    intro U hU
    have hpos : 0 < ∏ p ∈ U, p := Finset.prod_pos fun p hp => (hSp p (hU hp)).pos
    rw [a5_periodic _ hpos]
    simp only [mm]
    congr 1
    have := natCast_mul_prod_eq (q := 5) 1 (S := U) (fun p hp => hS2 p (hU hp))
    simpa using this
  have hcard : S.card = 3 + 1 := by decide
  have hb := h.sqfree_cumulant hSp (momCum_cum hmm0) ha 3 S subset_rfl hcard
  have hprod : ∏ p ∈ S, p = 2 * 7 * 17 * 37 := by decide
  rw [hprod] at hb
  rw [hb]
  -- the cumulants of `(1,0,1,0,1,…)`
  have m1 : mm 1 = 0 := by simp only [mm, pow_one, A5_two]
  have m2 : mm 2 = 1 := by
    have : (2 : ZMod 5) ^ 2 = 4 := by decide
    simp only [mm, this, A5_four]
  have m3 : mm 3 = 0 := by
    have : (2 : ZMod 5) ^ 3 = 3 := by decide
    simp only [mm, this, A5_three]
  have m4 : mm 4 = 1 := by
    have : (2 : ZMod 5) ^ 4 = 1 := by decide
    simp only [mm, this, A5_one]
  have c1 : cum mm 1 = 0 := by
    rw [cum]; simp [m1]
  have c2 : cum mm 2 = 1 := by
    rw [cum]; simp [c1, m2, m1]
  have c3 : cum mm 3 = 0 := by
    rw [cum]; simp [Fin.sum_univ_succ, c1, c2, m3, m2, m1]
  rw [cum]
  norm_num [Fin.sum_univ_succ, c1, c2, c3, m4, m3, m2, m1]

/-! ## C6: the de la Vallée Poussin algebra -/

/-- From `4/(σ-β) ≤ 3/(σ-1) + L` at `σ = 1 + δ/L`: `1 - β ≥ δ(1-δ)/((3+δ)L)`. -/
theorem dlvp_step {L σ β δ : ℝ} (hL : 0 < L) (hδ0 : 0 < δ) (hσ : σ = 1 + δ / L)
    (hβσ : β < σ) (h : 4 / (σ - β) ≤ 3 / (σ - 1) + L) :
    δ * (1 - δ) / ((3 + δ) * L) ≤ 1 - β := by
  have hx : 0 < σ - β := by linarith
  have hσ1 : σ - 1 = δ / L := by rw [hσ]; ring
  rw [hσ1] at h
  have h3 : 3 / (δ / L) + L = L * (3 + δ) / δ := by field_simp
  rw [h3, div_le_div_iff₀ hx hδ0] at h
  rw [div_le_iff₀ (by positivity)]
  have hb : 1 - β = (σ - β) - δ / L := by rw [hσ]; ring
  rw [hb]
  have hLd : (σ - β - δ / L) * ((3 + δ) * L) = (σ - β) * ((3 + δ) * L) - δ * (3 + δ) := by
    field_simp
  rw [hLd]
  nlinarith

/-- `max_{δ > -3} δ(1-δ)/(3+δ) = 7 - 4√3 = (2 - √3)²`. -/
theorem dlvp_opt (δ : ℝ) (hδ : -3 < δ) : δ * (1 - δ) / (3 + δ) ≤ 7 - 4 * √3 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [div_le_iff₀ (by linarith)]
  nlinarith [sq_nonneg (δ - (2 * √3 - 3))]

theorem dlvp_opt_attained :
    0 < 2 * √3 - 3 ∧ 2 * √3 - 3 < 1 ∧
      (2 * √3 - 3) * (1 - (2 * √3 - 3)) / (3 + (2 * √3 - 3)) = 7 - 4 * √3 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hlo : 3 / 2 < √3 := by nlinarith [Real.sqrt_nonneg 3]
  have hhi : √3 < 2 := by nlinarith [Real.sqrt_nonneg 3]
  refine ⟨by linarith, by linarith, ?_⟩
  rw [div_eq_iff (by linarith)]
  nlinarith

/-- The explicit region of C6 (algebraic part): with `δ* = 2√3 - 3` and `σ = 1 + δ*/L`, the
3-4-1 inequality `4/(σ-β) ≤ 3/(σ-1) + L` forces `1 - β ≥ (7 - 4√3)/L`. -/
theorem dlvp_region {L β : ℝ} (hL : 0 < L) (hβ : β < 1 + (2 * √3 - 3) / L)
    (h : 4 / (1 + (2 * √3 - 3) / L - β) ≤ 3 / (1 + (2 * √3 - 3) / L - 1) + L) :
    (7 - 4 * √3) / L ≤ 1 - β := by
  obtain ⟨hd0, hd1, hval⟩ := dlvp_opt_attained
  have := dlvp_step hL hd0 rfl hβ h
  rw [← hval, div_div]
  exact this

/-- The trigonometric positivity behind 3-4-1: `3 + 4 cos θ + cos 2θ = 2(1 + cos θ)² ≥ 0`. -/
theorem trig_341 (θ : ℝ) : 0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  rw [Real.cos_two_mul]; nlinarith [sq_nonneg (1 + Real.cos θ)]


end Crux.AxisoTheorem

/-! ## Axiom audit -/

#print axioms Crux.AxisoTheorem.monotone_of_fwdDiff_iter_nonneg
#print axioms Crux.AxisoTheorem.eq_of_monotone_periodic
#print axioms Crux.AxisoTheorem.finite_difference_rigidity
#print axioms Crux.AxisoTheorem.MomCum.nonneg
#print axioms Crux.AxisoTheorem.MomCum.term_le
#print axioms Crux.AxisoTheorem.choose_lower
#print axioms Crux.AxisoTheorem.MomCum.factorial_lower
#print axioms Crux.AxisoTheorem.MomCum.cumulant_eq_zero_of_bdd
#print axioms Crux.AxisoTheorem.MomCum.eq_pow_of_bdd
#print axioms Crux.AxisoTheorem.cumulant_rigidity
#print axioms Crux.AxisoTheorem.af_sub_apply
#print axioms Crux.AxisoTheorem.pmul_mul_of_additive
#print axioms Crux.AxisoTheorem.pmul_pmul_comm
#print axioms Crux.AxisoTheorem.pmul_sub'
#print axioms Crux.AxisoTheorem.isAdditiveWeight_log
#print axioms Crux.AxisoTheorem.vp_apply
#print axioms Crux.AxisoTheorem.isAdditiveWeight_vp
#print axioms Crux.AxisoTheorem.eq_zero_of_pmul_log
#print axioms Crux.AxisoTheorem.IsDirExp.pmul_additive
#print axioms Crux.AxisoTheorem.IsDirExp.nonneg
#print axioms Crux.AxisoTheorem.IsDirExp.vp_recursion
#print axioms Crux.AxisoTheorem.sum_divisors_mul_coprime
#print axioms Crux.AxisoTheorem.sum_divisors_mul_prod
#print axioms Crux.AxisoTheorem.padicValNat_mul_prod
#print axioms Crux.AxisoTheorem.mul_prod_div
#print axioms Crux.AxisoTheorem.IsDirExp.recursion_insert
#print axioms Crux.AxisoTheorem.IsDirExp.sqfree_cumulant
#print axioms Crux.AxisoTheorem.momCum_cum
#print axioms Crux.AxisoTheorem.step1_units
#print axioms Crux.AxisoTheorem.IsQSmooth.dvd
#print axioms Crux.AxisoTheorem.sqfree_b_of_units
#print axioms Crux.AxisoTheorem.IsDirExp.split_smooth
#print axioms Crux.AxisoTheorem.natCast_mul_prod_eq
#print axioms Crux.AxisoTheorem.step2_smooth
#print axioms Crux.AxisoTheorem.step2_unit_invariant
#print axioms Crux.AxisoTheorem.step2
#print axioms Crux.AxisoTheorem.step3_shift
#print axioms Crux.AxisoTheorem.step3
#print axioms Crux.AxisoTheorem.mem_Mk
#print axioms Crux.AxisoTheorem.factorization_le_cardFactors
#print axioms Crux.AxisoTheorem.dvd_pow_cardFactors
#print axioms Crux.AxisoTheorem.one_mem_Mk_zero
#print axioms Crux.AxisoTheorem.diag_conv
#print axioms Crux.AxisoTheorem.card_Mk_le
#print axioms Crux.AxisoTheorem.AbsSum.summable
#print axioms Crux.AxisoTheorem.AbsSum.add
#print axioms Crux.AxisoTheorem.pev_add
#print axioms Crux.AxisoTheorem.AbsSum.mul_C
#print axioms Crux.AxisoTheorem.AbsSum.mul_X
#print axioms Crux.AxisoTheorem.AbsSum.mul_poly
#print axioms Crux.AxisoTheorem.absSum_one
#print axioms Crux.AxisoTheorem.pev_one
#print axioms Crux.AxisoTheorem.pev_coe
#print axioms Crux.AxisoTheorem.no_root_of_identity
#print axioms Crux.AxisoTheorem.one_le_norm_multiset_prod
#print axioms Crux.AxisoTheorem.norm_leadingCoeff_le_one
#print axioms Crux.AxisoTheorem.omegaW_apply
#print axioms Crux.AxisoTheorem.isAdditiveWeight_omegaW
#print axioms Crux.AxisoTheorem.cardDistinctFactors_eq_card
#print axioms Crux.AxisoTheorem.card_primeFactors_le
#print axioms Crux.AxisoTheorem.cardFactors_le_of_dvd
#print axioms Crux.AxisoTheorem.diag_R
#print axioms Crux.AxisoTheorem.diag_S
#print axioms Crux.AxisoTheorem.diag_T
#print axioms Crux.AxisoTheorem.step4_top_coeff
#print axioms Crux.AxisoTheorem.classP_eq_zeta
#print axioms Crux.AxisoTheorem.zetaLogCoeff_apply
#print axioms Crux.AxisoTheorem.zetaLogCoeff_nonneg
#print axioms Crux.AxisoTheorem.zeta_isDirExp
#print axioms Crux.AxisoTheorem.classP_hypotheses_satisfiable
#print axioms Crux.AxisoTheorem.a2_apply
#print axioms Crux.AxisoTheorem.a2_periodic
#print axioms Crux.AxisoTheorem.a2_topcoeff
#print axioms Crux.AxisoTheorem.a2_logcoeff_four
#print axioms Crux.AxisoTheorem.four_cpow
#print axioms Crux.AxisoTheorem.nc_twoPow_mul
#print axioms Crux.AxisoTheorem.ncLambda_one_sub
#print axioms Crux.AxisoTheorem.ncLambda_eq
#print axioms Crux.AxisoTheorem.ncZero_re
#print axioms Crux.AxisoTheorem.two_cpow_neg_ncZero
#print axioms Crux.AxisoTheorem.ncP_ncZero
#print axioms Crux.AxisoTheorem.nc_F_vanishes
#print axioms Crux.AxisoTheorem.a9_apply
#print axioms Crux.AxisoTheorem.a9_nonneg
#print axioms Crux.AxisoTheorem.a9_logcoeff_four
#print axioms Crux.AxisoTheorem.a5_apply
#print axioms Crux.AxisoTheorem.A5_one
#print axioms Crux.AxisoTheorem.A5_two
#print axioms Crux.AxisoTheorem.A5_three
#print axioms Crux.AxisoTheorem.A5_four
#print axioms Crux.AxisoTheorem.a5_nonneg
#print axioms Crux.AxisoTheorem.a5_periodic
#print axioms Crux.AxisoTheorem.a5_logcoeff
#print axioms Crux.AxisoTheorem.dlvp_step
#print axioms Crux.AxisoTheorem.dlvp_opt
#print axioms Crux.AxisoTheorem.dlvp_opt_attained
#print axioms Crux.AxisoTheorem.dlvp_region
#print axioms Crux.AxisoTheorem.trig_341
