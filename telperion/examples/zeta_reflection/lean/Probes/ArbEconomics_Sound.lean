/-  Probes/ArbEconomics_Sound.lean -- soundness of the Nat-only zeta evaluator (ArbEconomics_Eval).

    Every function of `ArbEconomics_Eval` is shown to produce a TRUE enclosure:
      * `logInc`   : `S <= (log m - log (m-1)) 2^P <= S + K + T`
                     (Mathlib `Real.hasSum_pow_div_log_of_abs_lt_one`, `abs_log_sub_add_sum_range_le`);
      * `termOf`   : `Rlo <= 2^P / sqrt m <= Rhi` for ANY Newton iterate (two-sided validation);
      * `trig`     : cos/sin balls of `theta` from the (pi/2)-reduction, the Horner scheme
                     (Mathlib `Complex.exp_bound`) and the quadrant rotation;
      * `step`/`run` : the loop invariant `Inv` (log bracket + Re/Im balls of the partial zeta sum).

    The main theorem `run_sound` turns a kernel-checked chunk equation
    `St.beq (run cfg L s) s' = true` into `Inv n s -> Inv (n + L) s'`.

    conjecture1_proved = False.  Finite interval arithmetic; nothing here is about RH.
-/
import Probes.ArbEconomics_Eval
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.IntervalCases

open Real Finset

namespace ArbEcon

/-! ## A. floor division / shifts, cast to ℝ -/

theorem natdiv_le (a b : ℕ) : ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / b := Nat.cast_div_le

theorem lt_natdiv_add_one (a b : ℕ) (hb : 0 < b) : (a : ℝ) / b < ((a / b : ℕ) : ℝ) + 1 := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_lt_iff₀ hbR]
  have h1 : a < (a / b + 1) * b := by
    have := Nat.lt_div_mul_add (a := a) hb
    nlinarith [this]
  have h2 : ((a : ℕ) : ℝ) < (((a / b + 1) * b : ℕ) : ℝ) := by exact_mod_cast h1
  push_cast at h2
  linarith

theorem shr_eq (a d : ℕ) : Nat.shiftRight a d = a / 2 ^ d := Nat.shiftRight_eq_div_pow a d

theorem shl_eq (a d : ℕ) : Nat.shiftLeft a d = a * 2 ^ d := Nat.shiftLeft_eq a d

theorem two_pow_pos' (P : ℕ) : (0 : ℝ) < (2 : ℝ) ^ P := by positivity

/-! The evaluator calls the kernel primitives directly; these `rfl` lemmas translate them back to
    notation for the proofs. -/
@[simp] theorem p_add (a b : ℕ) : Nat.add a b = a + b := rfl
@[simp] theorem p_mul (a b : ℕ) : Nat.mul a b = a * b := rfl
@[simp] theorem p_sub (a b : ℕ) : Nat.sub a b = a - b := rfl
@[simp] theorem p_div (a b : ℕ) : Nat.div a b = a / b := rfl
@[simp] theorem p_mod (a b : ℕ) : Nat.mod a b = a % b := rfl
@[simp] theorem p_shr (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl
@[simp] theorem p_shl (a b : ℕ) : Nat.shiftLeft a b = a <<< b := rfl

/-- `⌊a / 2^d⌋ ≤ a / 2^d < ⌊a / 2^d⌋ + 1` over ℝ. -/
theorem shr_bounds (a d : ℕ) :
    ((Nat.shiftRight a d : ℕ) : ℝ) ≤ (a : ℝ) / 2 ^ d ∧ (a : ℝ) / 2 ^ d < (Nat.shiftRight a d : ℝ) + 1 := by
  rw [shr_eq]
  have hpos : 0 < 2 ^ d := Nat.two_pow_pos d
  have e : ((2 ^ d : ℕ) : ℝ) = (2 : ℝ) ^ d := by push_cast; ring
  constructor
  · have := natdiv_le a (2 ^ d); rw [e] at this; exact this
  · have := lt_natdiv_add_one a (2 ^ d) hpos; rw [e] at this; exact this

/-! ## B. the log increment -/

/-- The (S, K, pw) triple is the floor-truncated log(1-x) series with `pw = m^(K+1)`. -/
def LogSpec (one m : ℕ) (r : ℕ × ℕ × ℕ) : Prop :=
  r.1 = ∑ i ∈ range r.2.1, one / (m ^ (i + 1) * (i + 1)) ∧ r.2.2 = m ^ (r.2.1 + 1)

theorem logLoop_spec (one m : ℕ) :
    ∀ (fuel i pw S : ℕ), pw = m ^ (i + 1) → S = ∑ j ∈ range i, one / (m ^ (j + 1) * (j + 1)) →
      LogSpec one m (logLoop one m fuel i pw S) := by
  intro fuel
  induction fuel with
  | zero =>
    intro i pw S hpw hS
    exact ⟨hS, hpw⟩
  | succ fuel ih =>
    intro i pw S hpw hS
    show LogSpec one m (Bool.rec (logLoop one m fuel (Nat.succ i) (Nat.mul pw m)
      (Nat.add S (Nat.div one (Nat.mul pw (Nat.succ i))))) (S, i, pw)
      (Nat.beq (Nat.div one (Nat.mul pw (Nat.succ i))) 0))
    cases Nat.beq (Nat.div one (Nat.mul pw (Nat.succ i))) 0 with
    | true => exact ⟨hS, hpw⟩
    | false =>
      apply ih
      · show pw * m = m ^ (i + 1 + 1)
        rw [hpw]; ring
      · show S + one / (pw * (i + 1)) = ∑ j ∈ range (i + 1), one / (m ^ (j + 1) * (j + 1))
        rw [sum_range_succ, ← hS, hpw]

theorem logFix_spec (one m : ℕ) :
    ∀ (K i pw S : ℕ), pw = m ^ (i + 1) → S = ∑ j ∈ range i, one / (m ^ (j + 1) * (j + 1)) →
      LogSpec one m (logFix one m K i pw S) := by
  intro K
  induction K with
  | zero =>
    intro i pw S hpw hS
    exact ⟨hS, hpw⟩
  | succ K ih =>
    intro i pw S hpw hS
    show LogSpec one m (logFix one m K (Nat.succ i) (Nat.mul pw m)
      (Nat.add S (Nat.div one (Nat.mul pw (Nat.succ i)))))
    apply ih
    · show pw * m = m ^ (i + 1 + 1)
      rw [hpw]; ring
    · show S + one / (pw * (i + 1)) = ∑ j ∈ range (i + 1), one / (m ^ (j + 1) * (j + 1))
      rw [sum_range_succ, ← hS, hpw]

/-- The real series value: `-log (1 - 1/m) = log m - log (m-1)`. -/
theorem log_sub_log_pred (m : ℕ) (hm : 2 ≤ m) :
    Real.log m - Real.log ((m : ℝ) - 1) = -Real.log (1 - 1 / (m : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have : (1 : ℝ) - 1 / m = ((m : ℝ) - 1) / m := by field_simp
  rw [this, Real.log_div (ne_of_gt hm1) (ne_of_gt hm0)]
  ring

/-- **The log-increment enclosure.**  For `m ≥ 2` and a `LogSpec` triple `(S, K, pw)` at
    `one = 2^P`:  `S ≤ (log m - log (m-1)) 2^P ≤ S + K + (2^(P+1) / pw + 1)`. -/
theorem logInc_bound (P m : ℕ) (hm : 2 ≤ m) (r : ℕ × ℕ × ℕ) (hr : LogSpec (2 ^ P) m r) :
    (r.1 : ℝ) ≤ (Real.log m - Real.log ((m : ℝ) - 1)) * 2 ^ P ∧
    (Real.log m - Real.log ((m : ℝ) - 1)) * 2 ^ P
      ≤ (r.1 : ℝ) + r.2.1 + ((2 ^ (P + 1) / r.2.2 : ℕ) + 1) := by
  obtain ⟨hS, hpw⟩ := hr
  set K := r.2.1 with hK
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  set x : ℝ := 1 / (m : ℝ) with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 / 2 := by rw [hx]; rw [div_le_div_iff₀ hm0 (by norm_num)]; linarith
  have habs : |x| < 1 := by rw [abs_of_pos hx0]; linarith
  have hP : (0 : ℝ) < 2 ^ P := two_pow_pos' P
  rw [log_sub_log_pred m hm]
  -- the real partial sum and its relation to the floors
  set sr : ℝ := ∑ i ∈ range K, x ^ (i + 1) / (i + 1) with hsr
  have hterm : ∀ i : ℕ, (2 : ℝ) ^ P * (x ^ (i + 1) / (i + 1))
      = ((2 ^ P : ℕ) : ℝ) / ((m ^ (i + 1) * (i + 1) : ℕ) : ℝ) := by
    intro i
    rw [hx, div_pow, one_pow]; push_cast; field_simp
  have hden : ∀ i : ℕ, 0 < m ^ (i + 1) * (i + 1) := fun i => by positivity
  have hlo_sum : (r.1 : ℝ) ≤ 2 ^ P * sr := by
    rw [hS, hsr, mul_sum]; push_cast
    apply sum_le_sum; intro i _
    rw [hterm i]
    have := natdiv_le (2 ^ P) (m ^ (i + 1) * (i + 1))
    push_cast at this ⊢; exact this
  have hhi_sum : 2 ^ P * sr ≤ (r.1 : ℝ) + K := by
    rw [hS, hsr, mul_sum]; push_cast
    have : ∑ i ∈ range K, (2 : ℝ) ^ P * (x ^ (i + 1) / (i + 1))
        ≤ ∑ i ∈ range K, (((2 ^ P / (m ^ (i + 1) * (i + 1)) : ℕ) : ℝ) + 1) := by
      apply sum_le_sum; intro i _
      rw [hterm i]
      exact le_of_lt (lt_natdiv_add_one _ _ (hden i))
    rw [sum_add_distrib] at this
    simpa using this
  -- lower bound: nonneg series dominates its partial sums
  have hsum := Real.hasSum_pow_div_log_of_abs_lt_one habs
  have hlow : sr ≤ -Real.log (1 - x) := by
    rw [hsr]
    apply sum_le_hasSum (range K) _ hsum
    intro i _; positivity
  -- upper bound: the Mathlib tail estimate
  have htail := Real.abs_log_sub_add_sum_range_le habs K
  rw [abs_of_pos hx0] at htail
  have hup : -Real.log (1 - x) ≤ sr + x ^ (K + 1) / (1 - x) := by
    have := (abs_le.mp htail).1; rw [← hsr] at this; linarith
  have htailU : (2 : ℝ) ^ P * (x ^ (K + 1) / (1 - x))
      ≤ (((2 ^ (P + 1) / r.2.2 : ℕ) : ℝ) + 1) := by
    have hpwpos : 0 < r.2.2 := by rw [hpw]; positivity
    have h1 : (2 : ℝ) ^ P * (x ^ (K + 1) / (1 - x)) ≤ ((2 ^ (P + 1) : ℕ) : ℝ) / (r.2.2 : ℝ) := by
      have hmK : (0 : ℝ) < (m : ℝ) ^ K := by positivity
      have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
      have hmne : (m : ℝ) ≠ 0 := ne_of_gt hm0
      have hm1ne : (m : ℝ) - 1 ≠ 0 := ne_of_gt hm1
      have e1 : x ^ (K + 1) / (1 - x) = 1 / ((m : ℝ) ^ K * ((m : ℝ) - 1)) := by
        rw [hx, show (1 : ℝ) - 1 / m = ((m : ℝ) - 1) / m by field_simp, div_pow, one_pow,
          div_div_eq_mul_div, pow_succ]
        field_simp
      have e2 : ((2 ^ (P + 1) : ℕ) : ℝ) / (r.2.2 : ℝ) = 2 * 2 ^ P / ((m : ℝ) ^ K * m) := by
        rw [hpw]; push_cast; ring
      rw [e1, e2, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have hmm : (m : ℝ) ≤ 2 * ((m : ℝ) - 1) := by linarith
      have := mul_le_mul_of_nonneg_left hmm (le_of_lt (mul_pos hP hmK))
      nlinarith [this]
    exact le_trans h1 (le_of_lt (lt_natdiv_add_one _ _ hpwpos))
  constructor
  · nlinarith [hlo_sum, hlow, hP]
  · have := mul_le_mul_of_nonneg_left hup (le_of_lt hP)
    nlinarith [hhi_sum, htailU, this]

/-! ## C. the square-root bracket -/

/-- For ANY `g`, the evaluator's `(Rlo, Rhi)` bracket `2^P / sqrt m`. -/
theorem sqrt_bracket (P m g : ℕ) (hm : 1 ≤ m) :
    ((Bool.rec 0 (Bool.rec (Nat.div (2 ^ (2 * P)) (Nat.mul m g)) g
        (Nat.ble (Nat.mul (Nat.mul g g) m) (2 ^ (2 * P)))) (Nat.ble 1 g) : ℕ) : ℝ)
        ≤ (2 : ℝ) ^ P / Real.sqrt m ∧
    (2 : ℝ) ^ P / Real.sqrt m ≤ ((Bool.rec (2 ^ P) (Bool.rec g
        (Nat.add (Nat.div (2 ^ (2 * P)) (Nat.mul m g)) 1)
        (Nat.ble (Nat.mul (Nat.mul g g) m) (2 ^ (2 * P)))) (Nat.ble 1 g) : ℕ) : ℝ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hsq : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
  have hP : (0 : ℝ) < 2 ^ P := two_pow_pos' P
  have hsqm : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt (le_of_lt hm0)
  have h1m : (1 : ℝ) ≤ Real.sqrt m := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by exact_mod_cast hm)
  set X := (2 : ℝ) ^ P / Real.sqrt m with hX
  have hX0 : 0 < X := by positivity
  have hXs : X * Real.sqrt m = 2 ^ P := by rw [hX]; field_simp
  have hXX : X * X * m = ((2 : ℝ) ^ P) ^ 2 := by
    have : (X * Real.sqrt m) * (X * Real.sqrt m) = X * X * (Real.sqrt m * Real.sqrt m) := by ring
    rw [hsqm, hXs] at this; rw [← this]; ring
  have hoS : (((2 ^ (2 * P) : ℕ)) : ℝ) = ((2 : ℝ) ^ P) ^ 2 := by push_cast; ring
  cases hpos : Nat.ble 1 g with
  | false =>
    constructor
    · exact le_of_lt (by simpa using hX0)
    · push_cast
      rw [hX, div_le_iff₀ hsq]; nlinarith
  | true =>
    have hg1 : 1 ≤ g := Nat.le_of_ble_eq_true hpos
    have hg0 : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
    have hmg : 0 < m * g := Nat.mul_pos (by omega) (by omega)
    have hq_le : ((Nat.div (2 ^ (2 * P)) (Nat.mul m g) : ℕ) : ℝ) ≤ ((2 : ℝ) ^ P) ^ 2 / ((m : ℝ) * g) := by
      have := natdiv_le (2 ^ (2 * P)) (m * g); rw [hoS] at this; push_cast at this; exact this
    have hq_lt : ((2 : ℝ) ^ P) ^ 2 / ((m : ℝ) * g) < ((Nat.div (2 ^ (2 * P)) (Nat.mul m g) : ℕ) : ℝ) + 1 := by
      have := lt_natdiv_add_one (2 ^ (2 * P)) (m * g) hmg; rw [hoS] at this; push_cast at this
      exact this
    have hkey : ((2 : ℝ) ^ P) ^ 2 / ((m : ℝ) * g) = X * X / g := by
      rw [← hXX]; field_simp
    cases hb : Nat.ble (Nat.mul (Nat.mul g g) m) (2 ^ (2 * P)) with
    | true =>
      have hle : g * g * m ≤ 2 ^ (2 * P) := Nat.le_of_ble_eq_true hb
      have hleR : (g : ℝ) * g * m ≤ ((2 : ℝ) ^ P) ^ 2 := by
        have : ((g * g * m : ℕ) : ℝ) ≤ ((2 ^ (2 * P) : ℕ) : ℝ) := by exact_mod_cast hle
        rw [hoS] at this; push_cast at this; exact this
      have hgX : (g : ℝ) ≤ X := by
        by_contra hcon; have hcon := lt_of_not_ge hcon
        have : X * X * m < (g : ℝ) * g * m := by
          have := mul_lt_mul'' hcon hcon (le_of_lt hX0) (le_of_lt hX0); nlinarith
        linarith
      constructor
      · exact hgX
      · push_cast
        have : X ≤ X * X / g := by rw [le_div_iff₀ hg0]; nlinarith
        linarith [hkey ▸ hq_lt]
    | false =>
      have hgt : ¬ (g * g * m ≤ 2 ^ (2 * P)) := by
        intro h; have h2 := Nat.ble_eq_true_of_le h
        have h3 : Nat.ble (Nat.mul (Nat.mul g g) m) (2 ^ (2 * P)) = true := h2
        rw [h3] at hb; exact Bool.noConfusion hb
      have hgtR : ((2 : ℝ) ^ P) ^ 2 < (g : ℝ) * g * m := by
        have : ((2 ^ (2 * P) : ℕ) : ℝ) < ((g * g * m : ℕ) : ℝ) := by exact_mod_cast (Nat.lt_of_not_le hgt)
        rw [hoS] at this; push_cast at this; exact this
      have hXg : X < (g : ℝ) := by
        by_contra hcon; have hcon := le_of_not_gt hcon
        have : (g : ℝ) * g * m ≤ X * X * m := by
          have := mul_le_mul hcon hcon (le_of_lt hg0) (le_of_lt hX0); nlinarith
        linarith
      constructor
      · have : X * X / g ≤ X := by rw [div_le_iff₀ hg0]; nlinarith
        linarith [hkey ▸ hq_le]
      · exact le_of_lt hXg

/-! ## D. the theta interval -/

theorem theta_bracket (P tn tq : ℕ) (L : ℝ) (lloN lhiN : ℕ)
    (hlo : (lloN : ℝ) ≤ L * 2 ^ P) (hhi : L * 2 ^ P ≤ lhiN) :
    ((Nat.shiftRight (Nat.mul tn lloN) tq : ℕ) : ℝ) ≤ ((tn : ℝ) / 2 ^ tq * L) * 2 ^ P ∧
    ((tn : ℝ) / 2 ^ tq * L) * 2 ^ P ≤ ((Nat.add (Nat.shiftRight (Nat.mul tn lhiN) tq) 1 : ℕ) : ℝ) := by
  have hq : (0 : ℝ) < 2 ^ tq := two_pow_pos' tq
  have htn : (0 : ℝ) ≤ tn := by positivity
  obtain ⟨b1, _⟩ := shr_bounds (tn * lloN) tq
  obtain ⟨_, b2⟩ := shr_bounds (tn * lhiN) tq
  simp only [p_mul, p_add, p_shr] at b1 b2 ⊢
  have e : ((tn : ℝ) / 2 ^ tq * L) * 2 ^ P = (tn : ℝ) * (L * 2 ^ P) / 2 ^ tq := by ring
  rw [e]
  constructor
  · refine le_trans b1 ?_
    push_cast
    apply div_le_div_of_nonneg_right _ (le_of_lt hq)
    exact mul_le_mul_of_nonneg_left hlo htn
  · push_cast
    refine le_trans ?_ (le_of_lt b2)
    push_cast
    apply div_le_div_of_nonneg_right _ (le_of_lt hq)
    exact mul_le_mul_of_nonneg_left hhi htn

/-! ## E. Horner: real recursion, closed form, fixed-point error -/

/-- Real Horner over real divisors, same shape as `horner` (head processed first). -/
noncomputable def hornerR (w : ℝ) : List ℝ → ℝ → ℝ
  | [], h => h
  | d :: ds, h => hornerR w ds (1 - w * h / d)

/-- cos divisors `(2k-1)(2k)` and sin divisors `(2k)(2k+1)`. -/
def fcos (k : ℕ) : ℕ := (2 * k - 1) * (2 * k)
def fsin (k : ℕ) : ℕ := (2 * k) * (2 * k + 1)

theorem hornerR_cos (w : ℝ) : ∀ (K : ℕ) (h : ℝ),
    hornerR w ((divList fcos K).map (fun d : ℕ => (d : ℝ))) h
      = (∑ j ∈ range K, (-1) ^ j * w ^ j / ((2 * j).factorial : ℝ))
        + (-1) ^ K * w ^ K / ((2 * K).factorial : ℝ) * h := by
  intro K
  induction K with
  | zero => intro h; simp [divList, hornerR]
  | succ K ih =>
    intro h
    simp only [divList, List.map_cons]
    show hornerR w (((fcos (K + 1) : ℕ) : ℝ) :: (divList fcos K).map (fun d : ℕ => (d : ℝ))) h = _
    simp only [hornerR]
    rw [ih, sum_range_succ]
    have hf : ((fcos (K + 1) : ℕ) : ℝ) = (2 * K + 1) * (2 * K + 2) := by
      simp only [fcos]; push_cast
      rw [show 2 * (K + 1) - 1 = 2 * K + 1 by omega]; push_cast; ring
    rw [hf]
    have hfac : ((2 * (K + 1)).factorial : ℝ) = ((2 * K).factorial : ℝ) * ((2 * K + 1) * (2 * K + 2)) := by
      rw [show 2 * (K + 1) = (2 * K + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
      push_cast; ring
    rw [hfac]
    have h1 : ((2 * K).factorial : ℝ) ≠ 0 := by positivity
    have h2 : ((2 : ℝ) * K + 1) * (2 * K + 2) ≠ 0 := by positivity
    field_simp
    ring

theorem hornerR_sin (w : ℝ) : ∀ (K : ℕ) (h : ℝ),
    hornerR w ((divList fsin K).map (fun d : ℕ => (d : ℝ))) h
      = (∑ j ∈ range K, (-1) ^ j * w ^ j / ((2 * j + 1).factorial : ℝ))
        + (-1) ^ K * w ^ K / ((2 * K + 1).factorial : ℝ) * h := by
  intro K
  induction K with
  | zero => intro h; simp [divList, hornerR]
  | succ K ih =>
    intro h
    simp only [divList, List.map_cons]
    show hornerR w (((fsin (K + 1) : ℕ) : ℝ) :: (divList fsin K).map (fun d : ℕ => (d : ℝ))) h = _
    simp only [hornerR]
    rw [ih, sum_range_succ]
    have hf : ((fsin (K + 1) : ℕ) : ℝ) = (2 * K + 2) * (2 * K + 3) := by
      simp only [fsin]; push_cast; ring
    rw [hf]
    have hfac : ((2 * (K + 1) + 1).factorial : ℝ)
        = ((2 * K + 1).factorial : ℝ) * ((2 * K + 2) * (2 * K + 3)) := by
      rw [show 2 * (K + 1) + 1 = (2 * K + 1 + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
      push_cast; ring
    rw [hfac]
    have h1 : ((2 * K + 1).factorial : ℝ) ≠ 0 := by positivity
    have h2 : ((2 : ℝ) * K + 2) * (2 * K + 3) ≠ 0 := by positivity
    field_simp
    ring

theorem fcos_ge (k : ℕ) (hk : 1 ≤ k) : 2 ≤ fcos k := by
  simp only [fcos]
  have : 1 ≤ 2 * k - 1 := by omega
  have : 2 ≤ 2 * k := by omega
  nlinarith

theorem fsin_ge (k : ℕ) (hk : 1 ≤ k) : 2 ≤ fsin k := by
  simp only [fsin]; nlinarith

theorem divList_mem {f : ℕ → ℕ} (hf : ∀ k, 1 ≤ k → 2 ≤ f k) : ∀ K, ∀ d ∈ divList f K, 2 ≤ d := by
  intro K
  induction K with
  | zero => intro d hd; simp [divList] at hd
  | succ K ih =>
    intro d hd
    simp only [divList, List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact hf _ (by omega)
    · exact ih d hd

/-- Fixed-point Horner error: with `wN = floor(one * w)` and every divisor `≥ 2`, the Nat Horner
    stays within 3 ulps of `one * hornerR`, never truncates, and stays `≤ one`. -/
theorem horner_err (one wN : ℕ) (w : ℝ) (hone : 0 < one) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hwlo : (wN : ℝ) ≤ one * w) (hwhi : (one : ℝ) * w < wN + 1) (hwN : wN ≤ one) :
    ∀ (L : List ℕ) (hN : ℕ) (hR : ℝ), (∀ d ∈ L, 2 ≤ d) → hN ≤ one → 0 ≤ hR → hR ≤ 1 →
      |(hN : ℝ) - one * hR| ≤ 3 →
      horner one wN (L.map (fun d : ℕ => one * d)) hN ≤ one ∧
      0 ≤ hornerR w (L.map (fun d : ℕ => (d : ℝ))) hR ∧ hornerR w (L.map (fun d : ℕ => (d : ℝ))) hR ≤ 1 ∧
      |(horner one wN (L.map (fun d : ℕ => one * d)) hN : ℝ)
        - one * hornerR w (L.map (fun d : ℕ => (d : ℝ))) hR| ≤ 3 := by
  intro L
  induction L with
  | nil =>
    intro hN hR _ hN1 hR0 hR1 herr
    exact ⟨hN1, hR0, hR1, herr⟩
  | cons d L ih =>
    intro hN hR hL hN1 hR0 hR1 herr
    have hd : 2 ≤ d := hL d (by simp)
    have hL' : ∀ d' ∈ L, 2 ≤ d' := fun d' hd' => hL d' (by simp [hd'])
    have honeR : (0 : ℝ) < one := by exact_mod_cast hone
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have hd0 : (0 : ℝ) < d := by linarith
    -- the next Nat and real accumulators
    set Q := wN * hN / (one * d) with hQ
    have hQle : Q ≤ one := by
      rw [hQ]
      apply Nat.div_le_of_le_mul
      have : wN * hN ≤ one * one := Nat.mul_le_mul hwN hN1
      calc wN * hN ≤ one * one := this
        _ ≤ one * d * one := by nlinarith
    have hstepN : horner one wN ((d :: L).map (fun d : ℕ => one * d)) hN
        = horner one wN (L.map (fun d : ℕ => one * d)) (one - Q) := rfl
    have hstepR : hornerR w ((d :: L).map (fun d : ℕ => (d : ℝ))) hR
        = hornerR w (L.map (fun d : ℕ => (d : ℝ))) (1 - w * hR / d) := rfl
    rw [hstepN, hstepR]
    apply ih (one - Q) (1 - w * hR / d) hL' (Nat.sub_le _ _)
    · -- 0 ≤ 1 - w hR / d
      have : w * hR / d ≤ 1 / 2 := by
        rw [div_le_iff₀ hd0]; nlinarith
      linarith
    · have : 0 ≤ w * hR / d := by positivity
      linarith
    · -- the error recursion
      have hcast : ((one - Q : ℕ) : ℝ) = (one : ℝ) - Q := by
        rw [Nat.cast_sub hQle]
      rw [hcast]
      have hQlo : (Q : ℝ) ≤ (wN : ℝ) * hN / (one * d) := by
        have := natdiv_le (wN * hN) (one * d); push_cast at this; exact this
      have hQhi : (wN : ℝ) * hN / (one * d) < Q + 1 := by
        have := lt_natdiv_add_one (wN * hN) (one * d) (Nat.mul_pos hone (by omega))
        push_cast at this; exact this
      have hmain : |(one : ℝ) * w * hR / d - (wN : ℝ) * hN / (one * d)| ≤ 2 := by
        have e : (one : ℝ) * w * hR / d - (wN : ℝ) * hN / (one * d)
            = (((one : ℝ) * w - wN) * hR + (wN / one) * (one * hR - hN)) / d := by
          field_simp; ring
        rw [e, abs_div, abs_of_pos hd0, div_le_iff₀ hd0]
        have h1 : |((one : ℝ) * w - wN) * hR| ≤ 1 := by
          rw [abs_mul, abs_of_nonneg hR0]
          have : |(one : ℝ) * w - wN| ≤ 1 := by rw [abs_le]; constructor <;> linarith
          nlinarith [abs_nonneg ((one : ℝ) * w - wN)]
        have h2 : |((wN : ℝ) / one) * (one * hR - hN)| ≤ 3 := by
          rw [abs_mul]
          have hw' : |(wN : ℝ) / one| ≤ 1 := by
            rw [abs_of_nonneg (by positivity), div_le_one honeR]; exact_mod_cast hwN
          have : |(one : ℝ) * hR - hN| ≤ 3 := by rw [abs_sub_comm]; exact herr
          nlinarith [abs_nonneg ((wN : ℝ) / one), abs_nonneg ((one : ℝ) * hR - hN)]
        calc |((one : ℝ) * w - wN) * hR + (wN / one) * (one * hR - hN)|
            ≤ |((one : ℝ) * w - wN) * hR| + |(wN / one) * (one * hR - hN)| := abs_add_le _ _
          _ ≤ 4 := by linarith
          _ ≤ 2 * d := by linarith
      rw [abs_le] at hmain ⊢
      constructor
      · have : (one : ℝ) - Q - one * (1 - w * hR / d) = one * w * hR / d - Q := by ring
        rw [this]; linarith [hmain.1, hQlo]
      · have : (one : ℝ) - Q - one * (1 - w * hR / d) = one * w * hR / d - Q := by ring
        rw [this]; linarith [hmain.2, hQhi]

/-! ## F. Taylor remainders for cos / sin through `Complex.exp_bound` -/

/-- `Σ_{m<2K} (uI)^m/m! = A_K + B_K I` with the real even / odd partial sums. -/
theorem expI_partial (u : ℝ) : ∀ K : ℕ,
    ∑ m ∈ range (2 * K), ((u : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)
      = ((∑ j ∈ range K, (-1) ^ j * (u ^ 2) ^ j / ((2 * j).factorial : ℝ) : ℝ) : ℂ)
        + ((u * ∑ j ∈ range K, (-1) ^ j * (u ^ 2) ^ j / ((2 * j + 1).factorial : ℝ) : ℝ) : ℂ)
          * Complex.I := by
  intro K
  induction K with
  | zero => simp
  | succ K ih =>
    rw [show 2 * (K + 1) = 2 * K + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, sum_range_succ, mul_add]
    have hI2 : ((u : ℂ) * Complex.I) ^ (2 * K) = ((-1) ^ K * (u ^ 2) ^ K : ℝ) := by
      rw [pow_mul, mul_pow, Complex.I_sq]; push_cast; ring
    have hI3 : ((u : ℂ) * Complex.I) ^ (2 * K + 1) = ((-1) ^ K * (u ^ 2) ^ K * u : ℝ) * Complex.I := by
      rw [pow_succ, hI2]; push_cast; ring
    rw [hI2, hI3]
    push_cast
    ring

/-- **cos / sin Taylor enclosure** for `0 ≤ u ≤ 1` with `K+1` even / odd terms. -/
theorem cos_sin_taylor (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (K : ℕ) :
    |Real.cos u - hornerR (u ^ 2) ((divList fcos K).map (fun d : ℕ => (d : ℝ))) 1|
      ≤ u ^ (2 * K + 2) * (((2 * K + 2).succ : ℝ) * (((2 * K + 2).factorial : ℝ) * (2 * K + 2 : ℕ))⁻¹) ∧
    |Real.sin u - u * hornerR (u ^ 2) ((divList fsin K).map (fun d : ℕ => (d : ℝ))) 1|
      ≤ u ^ (2 * K + 2) * (((2 * K + 2).succ : ℝ) * (((2 * K + 2).factorial : ℝ) * (2 * K + 2 : ℕ))⁻¹) := by
  have hn : 0 < 2 * K + 2 := by omega
  have hx : ‖(u : ℂ) * Complex.I‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
    exact hu1
  have hb := Complex.exp_bound hx hn
  have hnorm : ‖(u : ℂ) * Complex.I‖ = u := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
  rw [hnorm, show 2 * K + 2 = 2 * (K + 1) by ring, expI_partial u (K + 1)] at hb
  rw [show 2 * (K + 1) = 2 * K + 2 by ring] at hb
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin] at hb
  -- closed forms of the two Horner values
  have hc : hornerR (u ^ 2) ((divList fcos K).map (fun d : ℕ => (d : ℝ))) 1
      = ∑ j ∈ range (K + 1), (-1) ^ j * (u ^ 2) ^ j / ((2 * j).factorial : ℝ) := by
    rw [hornerR_cos, sum_range_succ, mul_one]
  have hs : hornerR (u ^ 2) ((divList fsin K).map (fun d : ℕ => (d : ℝ))) 1
      = ∑ j ∈ range (K + 1), (-1) ^ j * (u ^ 2) ^ j / ((2 * j + 1).factorial : ℝ) := by
    rw [hornerR_sin, sum_range_succ, mul_one]
  rw [hc, hs]
  set A := ∑ j ∈ range (K + 1), (-1) ^ j * (u ^ 2) ^ j / ((2 * j).factorial : ℝ)
  set B := u * ∑ j ∈ range (K + 1), (-1) ^ j * (u ^ 2) ^ j / ((2 * j + 1).factorial : ℝ)
  have e : (Real.cos u : ℂ) + (Real.sin u : ℂ) * Complex.I - ((A : ℂ) + (B : ℂ) * Complex.I)
      = ((Real.cos u - A : ℝ) : ℂ) + ((Real.sin u - B : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [e] at hb
  constructor
  · have := Complex.abs_re_le_norm (((Real.cos u - A : ℝ) : ℂ) + ((Real.sin u - B : ℝ) : ℂ) * Complex.I)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero] at this
    exact le_trans this hb
  · have := Complex.abs_im_le_norm (((Real.cos u - A : ℝ) : ℂ) + ((Real.sin u - B : ℝ) : ℂ) * Complex.I)
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, mul_one, mul_zero, zero_add, add_zero] at this
    exact le_trans this hb

/-! ## G. cos / sin of theta: reduction, Taylor core, rotation -/

/-- sign of a Bool (`true` = `+1`). -/
def sgn (b : Bool) : ℝ := Bool.rec (-1) 1 b

@[simp] theorem sgn_true : sgn true = 1 := rfl
@[simp] theorem sgn_false : sgn false = -1 := rfl
theorem sgn_not (b : Bool) : sgn (!b) = -sgn b := by cases b <;> simp [sgn]
theorem abs_sgn (b : Bool) : |sgn b| = 1 := by cases b <;> simp [sgn]

/-- signed ball: `|x 2^P - sgn s * m| ≤ r`. -/
def SBall (P : ℕ) (x : ℝ) (m : ℕ) (s : Bool) (r : ℕ) : Prop :=
  |x * 2 ^ P - sgn s * m| ≤ r

/-- The (pi/2)-reduction: `phi = theta - k pi/2` is within `rphi` ulps of `sgn pos * mag`. -/
theorem phi_ball (P hp rp k thlo thhi : ℕ) (θ : ℝ)
    (hlo : (thlo : ℝ) ≤ θ * 2 ^ P) (hhi : θ * 2 ^ P ≤ thhi)
    (hpi : |Real.pi / 2 * 2 ^ P - hp| ≤ rp) :
    |(θ - k * (Real.pi / 2)) * 2 ^ P
        - sgn (Nat.ble (Nat.shiftLeft (Nat.mul k hp) 1) (Nat.add thlo thhi))
          * ((Nat.shiftRight (Bool.rec (Nat.sub (Nat.shiftLeft (Nat.mul k hp) 1) (Nat.add thlo thhi))
              (Nat.sub (Nat.add thlo thhi) (Nat.shiftLeft (Nat.mul k hp) 1))
              (Nat.ble (Nat.shiftLeft (Nat.mul k hp) 1) (Nat.add thlo thhi))) 1 : ℕ) : ℝ)|
      ≤ ((Nat.add (Nat.add (Nat.shiftRight (Nat.sub thhi thlo) 1) (Nat.mul k rp)) 2 : ℕ) : ℝ) := by
  have hle : thlo ≤ thhi := by exact_mod_cast le_trans hlo hhi
  have hk : |(k : ℝ) * (Real.pi / 2) * 2 ^ P - k * hp| ≤ k * rp := by
    have : (k : ℝ) * (Real.pi / 2) * 2 ^ P - k * hp = k * (Real.pi / 2 * 2 ^ P - hp) := by ring
    rw [this, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ k)]
    exact mul_le_mul_of_nonneg_left hpi (by positivity)
  obtain ⟨hw1, hw2⟩ := shr_bounds (thhi - thlo) 1
  have hsubc : (((thhi - thlo : ℕ)) : ℝ) = (thhi : ℝ) - thlo := by rw [Nat.cast_sub hle]
  rw [hsubc, pow_one] at hw1 hw2
  simp only [p_add, p_mul, p_sub, p_shr, p_shl, Nat.shiftLeft_eq, pow_one] at *
  set M1 := thlo + thhi with hM1
  set M2 := k * hp * 2 with hM2
  have hcenter : |θ * 2 ^ P - ((thlo : ℝ) + thhi) / 2| ≤ ((thhi : ℝ) - thlo) / 2 := by
    rw [abs_le]; constructor <;> linarith
  cases hb : Nat.ble M2 M1 with
  | true =>
    have hM : M2 ≤ M1 := Nat.le_of_ble_eq_true hb
    obtain ⟨m1, m2⟩ := shr_bounds (M1 - M2) 1
    have hc : (((M1 - M2 : ℕ)) : ℝ) = (M1 : ℝ) - M2 := by rw [Nat.cast_sub hM]
    rw [hc, pow_one] at m1 m2
    simp only [p_shr] at m1 m2
    simp only [sgn_true, one_mul]
    push_cast [hM1, hM2] at m1 m2 ⊢
    rw [abs_le] at hk ⊢
    constructor <;> nlinarith [hk.1, hk.2, hcenter, abs_le.mp hcenter, hw1, hw2, m1, m2]
  | false =>
    have hM : M1 < M2 := Nat.lt_of_not_le (fun h => by
      have := Nat.ble_eq_true_of_le h; rw [this] at hb; exact Bool.noConfusion hb)
    obtain ⟨m1, m2⟩ := shr_bounds (M2 - M1) 1
    have hc : (((M2 - M1 : ℕ)) : ℝ) = (M2 : ℝ) - M1 := by rw [Nat.cast_sub (le_of_lt hM)]
    rw [hc, pow_one] at m1 m2
    simp only [p_shr] at m1 m2
    simp only [sgn_false, neg_one_mul, sub_neg_eq_add]
    push_cast [hM1, hM2] at m1 m2 ⊢
    rw [abs_le] at hk ⊢
    constructor <;> nlinarith [hk.1, hk.2, hcenter, abs_le.mp hcenter, hw1, hw2, m1, m2]

/-- The Taylor-core bound constant for `u ≤ 13/16` with `K+1` terms. -/
noncomputable def taylorBnd (K : ℕ) : ℝ :=
  (13 / 16 : ℝ) ^ (2 * K + 2) * (((2 * K + 2).succ : ℝ) * (((2 * K + 2).factorial : ℝ) * (2 * K + 2 : ℕ))⁻¹)

/-- **Fixed-point Taylor core.**  For `mag ≤ (13/16) 2^P`, `u = mag / 2^P`:
    `C = horner(dcos)` and `S0 = mag * horner(dsin) / 2^P` are within `3 + tau` / `4 + tau`
    ulps of `2^P cos u`, `2^P sin u`, and both are `≤ 2^P`. -/
theorem taylor_fixed (P K mag tau : ℕ) (hmag : mag * 16 ≤ 13 * 2 ^ P)
    (htau : (2 : ℝ) ^ P * taylorBnd K ≤ tau) :
    let one := 2 ^ P
    let w := Nat.shiftRight (Nat.mul mag mag) P
    let C := horner one w ((divList fcos K).map (fun d : ℕ => one * d)) one
    let S0 := Nat.shiftRight (Nat.mul mag (horner one w ((divList fsin K).map (fun d : ℕ => one * d)) one)) P
    |(C : ℝ) - 2 ^ P * Real.cos ((mag : ℝ) / 2 ^ P)| ≤ 3 + tau ∧
    |(S0 : ℝ) - 2 ^ P * Real.sin ((mag : ℝ) / 2 ^ P)| ≤ 4 + tau ∧ C ≤ one ∧ S0 ≤ one := by
  intro one w C S0
  have hP : (0 : ℝ) < 2 ^ P := two_pow_pos' P
  have hone : 0 < one := Nat.two_pow_pos P
  have honeR : ((one : ℕ) : ℝ) = (2 : ℝ) ^ P := by show ((2 ^ P : ℕ) : ℝ) = _; push_cast; ring
  set u : ℝ := (mag : ℝ) / 2 ^ P with hu
  have hu0 : 0 ≤ u := by positivity
  have hmagR : (mag : ℝ) * 16 ≤ 13 * 2 ^ P := by exact_mod_cast hmag
  have hu1 : u ≤ 13 / 16 := by rw [hu, div_le_iff₀ hP]; linarith
  have humag : (mag : ℝ) = u * 2 ^ P := by rw [hu]; field_simp
  -- w = floor(one * u^2)
  obtain ⟨w1, w2⟩ := shr_bounds (mag * mag) P
  have hwlo : (w : ℝ) ≤ (one : ℝ) * u ^ 2 := by
    rw [honeR]; have : ((mag * mag : ℕ) : ℝ) / 2 ^ P = 2 ^ P * u ^ 2 := by
      push_cast; rw [humag]; field_simp
    rw [← this]; exact w1
  have hwhi : (one : ℝ) * u ^ 2 < w + 1 := by
    rw [honeR]; have : ((mag * mag : ℕ) : ℝ) / 2 ^ P = 2 ^ P * u ^ 2 := by
      push_cast; rw [humag]; field_simp
    rw [← this]; exact w2
  have hwN : w ≤ one := by
    have : (w : ℝ) ≤ one := by
      calc (w : ℝ) ≤ one * u ^ 2 := hwlo
        _ ≤ one * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith
        _ = one := by ring
    exact_mod_cast this
  have hu21 : u ^ 2 ≤ 1 := by nlinarith
  have hbnd : u ^ (2 * K + 2) * (((2 * K + 2).succ : ℝ) * (((2 * K + 2).factorial : ℝ) * (2 * K + 2 : ℕ))⁻¹)
      ≤ taylorBnd K := by
    unfold taylorBnd
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact pow_le_pow_left₀ hu0 hu1 _
  obtain ⟨tc, ts⟩ := cos_sin_taylor u hu0 (by linarith) K
  -- cos
  have hc := horner_err one w (u ^ 2) hone (by positivity) hu21 hwlo hwhi hwN
    (divList fcos K) one 1 (divList_mem fcos_ge K) le_rfl (by norm_num) le_rfl (by simp)
  -- sin
  have hs := horner_err one w (u ^ 2) hone (by positivity) hu21 hwlo hwhi hwN
    (divList fsin K) one 1 (divList_mem fsin_ge K) le_rfl (by norm_num) le_rfl (by simp)
  obtain ⟨hcle, _, _, hcerr⟩ := hc
  obtain ⟨hsle, hs0, hs1, hserr⟩ := hs
  set Hc := hornerR (u ^ 2) ((divList fcos K).map (fun d : ℕ => (d : ℝ))) 1
  set Hs := hornerR (u ^ 2) ((divList fsin K).map (fun d : ℕ => (d : ℝ))) 1
  set G := horner one w ((divList fsin K).map (fun d : ℕ => one * d)) one
  rw [honeR] at hcerr hserr
  refine ⟨?_, ?_, hcle, ?_⟩
  · -- |C - one cos u| ≤ |C - one Hc| + one |Hc - cos u|
    have h1 : |(2 : ℝ) ^ P * Hc - 2 ^ P * Real.cos u| ≤ tau := by
      rw [← mul_sub, abs_mul, abs_of_pos hP, abs_sub_comm]
      calc 2 ^ P * |Real.cos u - Hc| ≤ 2 ^ P * taylorBnd K :=
            mul_le_mul_of_nonneg_left (le_trans tc hbnd) (le_of_lt hP)
        _ ≤ tau := htau
    calc |(C : ℝ) - 2 ^ P * Real.cos u|
        ≤ |(C : ℝ) - 2 ^ P * Hc| + |(2 : ℝ) ^ P * Hc - 2 ^ P * Real.cos u| := abs_sub_le _ _ _
      _ ≤ 3 + tau := by linarith
  · -- S0 = floor(mag G / one)
    obtain ⟨s1, s2⟩ := shr_bounds (mag * G) P
    have hGR : (G : ℝ) ≤ 2 ^ P := by rw [← honeR]; exact_mod_cast hsle
    have e1 : ((mag * G : ℕ) : ℝ) / 2 ^ P = u * G := by push_cast; rw [humag]; field_simp
    rw [e1] at s1 s2
    have h1 : |(S0 : ℝ) - u * G| ≤ 1 := by
      show |((Nat.shiftRight (Nat.mul mag G) P : ℕ) : ℝ) - u * G| ≤ 1
      simp only [p_mul] at s1 s2 ⊢
      rw [abs_le]; constructor <;> linarith
    have h2 : |u * G - 2 ^ P * (u * Hs)| ≤ 3 := by
      have : u * G - 2 ^ P * (u * Hs) = u * ((G : ℝ) - 2 ^ P * Hs) := by ring
      rw [this, abs_mul, abs_of_nonneg hu0]
      nlinarith [abs_nonneg ((G : ℝ) - 2 ^ P * Hs)]
    have h3 : |(2 : ℝ) ^ P * (u * Hs) - 2 ^ P * Real.sin u| ≤ tau := by
      rw [← mul_sub, abs_mul, abs_of_pos hP, abs_sub_comm]
      calc 2 ^ P * |Real.sin u - u * Hs| ≤ 2 ^ P * taylorBnd K :=
            mul_le_mul_of_nonneg_left (le_trans ts hbnd) (le_of_lt hP)
        _ ≤ tau := htau
    calc |(S0 : ℝ) - 2 ^ P * Real.sin u|
        ≤ |(S0 : ℝ) - u * G| + |u * G - 2 ^ P * (u * Hs)| + |(2 : ℝ) ^ P * (u * Hs) - 2 ^ P * Real.sin u| := by
          have := abs_sub_le (S0 : ℝ) (u * G) (2 ^ P * Real.sin u)
          have := abs_sub_le (u * G) (2 ^ P * (u * Hs)) (2 ^ P * Real.sin u)
          linarith
      _ ≤ 4 + tau := by linarith
  · -- S0 ≤ one
    show Nat.shiftRight (Nat.mul mag G) P ≤ one
    simp only [p_mul, p_shr, Nat.shiftRight_eq_div_pow]
    apply Nat.div_le_of_le_mul
    have hmo : mag ≤ one := by
      have : mag * 16 ≤ one * 16 := by simp only [one]; omega
      omega
    calc mag * G ≤ one * one := Nat.mul_le_mul hmo hsle
      _ = 2 ^ P * one := rfl

/-- Quadrant rotation: `theta = phi + k pi/2`. -/
theorem rot_cos_sin (φ : ℝ) (k : ℕ) :
    (k % 4 = 0 → Real.cos (φ + k * (π / 2)) = Real.cos φ ∧ Real.sin (φ + k * (π / 2)) = Real.sin φ) ∧
    (k % 4 = 1 → Real.cos (φ + k * (π / 2)) = -Real.sin φ ∧ Real.sin (φ + k * (π / 2)) = Real.cos φ) ∧
    (k % 4 = 2 → Real.cos (φ + k * (π / 2)) = -Real.cos φ ∧ Real.sin (φ + k * (π / 2)) = -Real.sin φ) ∧
    (k % 4 = 3 → Real.cos (φ + k * (π / 2)) = Real.sin φ ∧ Real.sin (φ + k * (π / 2)) = -Real.cos φ) := by
  have hk : (k : ℝ) * (π / 2) = ((k % 4 : ℕ) : ℝ) * (π / 2) + ((k / 4 : ℕ) : ℝ) * (2 * π) := by
    have := Nat.mod_add_div k 4
    have hR : (k : ℝ) = ((k % 4 : ℕ) : ℝ) + 4 * ((k / 4 : ℕ) : ℝ) := by exact_mod_cast this.symm
    rw [hR]; ring
  have base : ∀ j : ℕ, Real.cos (φ + k * (π / 2)) = Real.cos (φ + (k % 4 : ℕ) * (π / 2)) ∧
      Real.sin (φ + k * (π / 2)) = Real.sin (φ + (k % 4 : ℕ) * (π / 2)) := by
    intro _
    rw [hk, ← add_assoc]
    exact ⟨Real.cos_add_nat_mul_two_pi _ _, Real.sin_add_nat_mul_two_pi _ _⟩
  obtain ⟨hc, hs⟩ := base 0
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> rw [hc, hs, h]
  · simp
  · push_cast; rw [one_mul, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]; simp
  · push_cast
    rw [show (2 : ℝ) * (π / 2) = π by ring, Real.cos_add_pi, Real.sin_add_pi]; simp
  · push_cast
    rw [show φ + (3 : ℝ) * (π / 2) = (φ + π) + π / 2 by ring, Real.cos_add_pi_div_two,
      Real.sin_add_pi_div_two, Real.sin_add_pi, Real.cos_add_pi]; simp

theorem rotate_sound (P : ℕ) (φ : ℝ) (k : ℕ) (C rc S0 rs : ℕ) (sy : Bool)
    (hc : |Real.cos φ * 2 ^ P - C| ≤ rc) (hs : |Real.sin φ * 2 ^ P - sgn sy * S0| ≤ rs) :
    SBall P (Real.cos (φ + k * (π / 2)))
      (rotate (Nat.beq (Nat.mod (Nat.mod k 4) 2) 1) (Nat.ble 2 (Nat.mod k 4)) C rc S0 sy rs).cm
      (rotate (Nat.beq (Nat.mod (Nat.mod k 4) 2) 1) (Nat.ble 2 (Nat.mod k 4)) C rc S0 sy rs).cs
      (rotate (Nat.beq (Nat.mod (Nat.mod k 4) 2) 1) (Nat.ble 2 (Nat.mod k 4)) C rc S0 sy rs).cr ∧
    SBall P (Real.sin (φ + k * (π / 2)))
      (rotate (Nat.beq (Nat.mod (Nat.mod k 4) 2) 1) (Nat.ble 2 (Nat.mod k 4)) C rc S0 sy rs).sm
      (rotate (Nat.beq (Nat.mod (Nat.mod k 4) 2) 1) (Nat.ble 2 (Nat.mod k 4)) C rc S0 sy rs).ss
      (rotate (Nat.beq (Nat.mod (Nat.mod k 4) 2) 1) (Nat.ble 2 (Nat.mod k 4)) C rc S0 sy rs).sr ∧
    (rotate (Nat.beq (Nat.mod (Nat.mod k 4) 2) 1) (Nat.ble 2 (Nat.mod k 4)) C rc S0 sy rs).cm ≤ max C S0 ∧
    (rotate (Nat.beq (Nat.mod (Nat.mod k 4) 2) 1) (Nat.ble 2 (Nat.mod k 4)) C rc S0 sy rs).sm ≤ max C S0 := by
  obtain ⟨r0, r1, r2, r3⟩ := rot_cos_sin φ k
  have hj : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
  simp only [p_mod]
  unfold SBall
  generalize hjj : k % 4 = j at *
  interval_cases j
  · obtain ⟨e1, e2⟩ := r0 rfl
    refine ⟨?_, ?_, le_max_left _ _, le_max_right _ _⟩
    · show |Real.cos (φ + k * (π / 2)) * 2 ^ P - sgn true * C| ≤ rc
      rw [e1, sgn_true, one_mul]; exact hc
    · show |Real.sin (φ + k * (π / 2)) * 2 ^ P - sgn sy * S0| ≤ rs
      rw [e2]; exact hs
  · obtain ⟨e1, e2⟩ := r1 rfl
    refine ⟨?_, ?_, le_max_right _ _, le_max_left _ _⟩
    · show |Real.cos (φ + k * (π / 2)) * 2 ^ P - sgn (!sy) * S0| ≤ rs
      rw [e1, sgn_not, show -Real.sin φ * 2 ^ P - -sgn sy * S0 = -(Real.sin φ * 2 ^ P - sgn sy * S0) by ring,
        abs_neg]; exact hs
    · show |Real.sin (φ + k * (π / 2)) * 2 ^ P - sgn true * C| ≤ rc
      rw [e2, sgn_true, one_mul]; exact hc
  · obtain ⟨e1, e2⟩ := r2 rfl
    refine ⟨?_, ?_, le_max_left _ _, le_max_right _ _⟩
    · show |Real.cos (φ + k * (π / 2)) * 2 ^ P - sgn false * C| ≤ rc
      rw [e1, sgn_false, show -Real.cos φ * 2 ^ P - -1 * (C : ℝ) = -(Real.cos φ * 2 ^ P - C) by ring,
        abs_neg]; exact hc
    · show |Real.sin (φ + k * (π / 2)) * 2 ^ P - sgn (!sy) * S0| ≤ rs
      rw [e2, sgn_not, show -Real.sin φ * 2 ^ P - -sgn sy * S0 = -(Real.sin φ * 2 ^ P - sgn sy * S0) by ring,
        abs_neg]; exact hs
  · obtain ⟨e1, e2⟩ := r3 rfl
    refine ⟨?_, ?_, le_max_right _ _, le_max_left _ _⟩
    · show |Real.cos (φ + k * (π / 2)) * 2 ^ P - sgn sy * S0| ≤ rs
      rw [e1]; exact hs
    · show |Real.sin (φ + k * (π / 2)) * 2 ^ P - sgn false * C| ≤ rc
      rw [e2, sgn_false, show -Real.cos φ * 2 ^ P - -1 * (C : ℝ) = -(Real.cos φ * 2 ^ P - C) by ring,
        abs_neg]; exact hc

/-- Validity of an evaluator configuration for the height `t` (Horner length `K`).  Every field
    is a closed numeric fact, discharged per instance by `decide`/`rfl`/`norm_num`. -/
structure Valid (c : Cfg) (t : ℝ) (K : ℕ) : Prop where
  one_eq : c.one = 2 ^ c.P
  two1_eq : c.two1 = 2 ^ (c.P + 1)
  oneSq_eq : c.oneSq = 2 ^ (2 * c.P)
  t_eq : t = (c.tn : ℝ) / 2 ^ c.tq
  pi_ball : |Real.pi / 2 * 2 ^ c.P - c.hp| ≤ c.rp
  umax_le : c.umax * 16 ≤ 13 * 2 ^ c.P
  dcos_eq : c.dcos = (divList fcos K).map (fun d : ℕ => c.one * d)
  dsin_eq : c.dsin = (divList fsin K).map (fun d : ℕ => c.one * d)
  tau_ok : (2 : ℝ) ^ c.P * taylorBnd K ≤ c.tau
  hc_eq : ∀ w, c.hc w = horner c.one w c.dcos c.one
  hs_eq : ∀ w, c.hs w = horner c.one w c.dsin c.one
  lnf_eq : ∀ m, c.lnf m = logFix c.one m c.lnK 0 m 0

/-- cos/sin balls of `theta` (plus magnitude caps) -- what `trig` guarantees. -/
def TrigOK (P : ℕ) (θ : ℝ) (tr : Trig) : Prop :=
  SBall P (Real.cos θ) tr.cm tr.cs tr.cr ∧ SBall P (Real.sin θ) tr.sm tr.ss tr.sr ∧
  tr.cm ≤ 2 ^ P ∧ tr.sm ≤ 2 ^ P

theorem trig_sound (c : Cfg) (t : ℝ) (K : ℕ) (hv : Valid c t K) (θ : ℝ) (thlo thhi : ℕ)
    (hlo : (thlo : ℝ) ≤ θ * 2 ^ c.P) (hhi : θ * 2 ^ c.P ≤ thhi) :
    TrigOK c.P θ (trig c thlo thhi) := by
  have hP : (0 : ℝ) < 2 ^ c.P := two_pow_pos' c.P
  set k := Nat.div (Nat.add thlo c.hph) c.hp with hk
  set φ := θ - k * (Real.pi / 2) with hφ
  have hθ : θ = φ + k * (Real.pi / 2) := by rw [hφ]; ring
  have hball := phi_ball c.P c.hp c.rp k thlo thhi θ hlo hhi hv.pi_ball
  rw [← hφ] at hball
  set pos := Nat.ble (Nat.shiftLeft (Nat.mul k c.hp) 1) (Nat.add thlo thhi) with hpos
  set mag := Nat.shiftRight (Bool.rec (Nat.sub (Nat.shiftLeft (Nat.mul k c.hp) 1) (Nat.add thlo thhi))
              (Nat.sub (Nat.add thlo thhi) (Nat.shiftLeft (Nat.mul k c.hp) 1)) pos) 1 with hmag
  set rphi := Nat.add (Nat.add (Nat.shiftRight (Nat.sub thhi thlo) 1) (Nat.mul k c.rp)) 2 with hrphi
  have htrig : trig c thlo thhi = Bool.rec
      (rotate (Nat.beq (Nat.mod (Nat.mod k 4) 2) 1) (Nat.ble 2 (Nat.mod k 4)) 0 c.one 0 pos c.one)
      (rotate (Nat.beq (Nat.mod (Nat.mod k 4) 2) 1) (Nat.ble 2 (Nat.mod k 4))
        (c.hc (Nat.shiftRight (Nat.mul mag mag) c.P)) (Nat.add (Nat.add 3 c.tau) rphi)
        (Nat.shiftRight (Nat.mul mag (c.hs (Nat.shiftRight (Nat.mul mag mag) c.P))) c.P) pos
        (Nat.add (Nat.add 4 c.tau) rphi))
      (Nat.ble mag c.umax) := rfl
  rw [htrig]
  -- Lipschitz transfer from the center `sgn pos * u` to `phi`
  set u : ℝ := (mag : ℝ) / 2 ^ c.P with hu
  have hdist : |φ - sgn pos * u| * 2 ^ c.P ≤ rphi := by
    have : (φ - sgn pos * u) * 2 ^ c.P = φ * 2 ^ c.P - sgn pos * mag := by
      rw [hu]; field_simp
    rw [show |φ - sgn pos * u| * 2 ^ c.P = |(φ - sgn pos * u) * 2 ^ c.P| by
      rw [abs_mul, abs_of_pos hP], this]; exact hball
  have hcosφ : |Real.cos φ - Real.cos u| * 2 ^ c.P ≤ rphi := by
    have hcu : Real.cos (sgn pos * u) = Real.cos u := by
      cases pos <;> simp [sgn]
    rw [← hcu]
    exact le_trans (mul_le_mul_of_nonneg_right (Real.abs_cos_sub_cos_le _ _) (le_of_lt hP)) hdist
  have hsinφ : |Real.sin φ - sgn pos * Real.sin u| * 2 ^ c.P ≤ rphi := by
    have hsu : Real.sin (sgn pos * u) = sgn pos * Real.sin u := by
      cases pos <;> simp [sgn]
    rw [← hsu]
    exact le_trans (mul_le_mul_of_nonneg_right (Real.abs_sin_sub_sin_le _ _) (le_of_lt hP)) hdist
  cases hbr : Nat.ble mag c.umax with
  | false =>
    -- fallback: magnitudes 0, radii 2^P
    have hc0 : |Real.cos φ * 2 ^ c.P - ((0 : ℕ) : ℝ)| ≤ (c.one : ℝ) := by
      rw [hv.one_eq]; push_cast
      rw [sub_zero, abs_mul, abs_of_pos hP]
      exact mul_le_of_le_one_left (le_of_lt hP) (Real.abs_cos_le_one _)
    have hs0 : |Real.sin φ * 2 ^ c.P - sgn pos * ((0 : ℕ) : ℝ)| ≤ (c.one : ℝ) := by
      rw [hv.one_eq]; push_cast
      rw [mul_zero, sub_zero, abs_mul, abs_of_pos hP]
      exact mul_le_of_le_one_left (le_of_lt hP) (Real.abs_sin_le_one _)
    obtain ⟨h1, h2, h3, h4⟩ := rotate_sound c.P φ k 0 c.one 0 c.one pos hc0 hs0
    rw [← hθ] at h1 h2
    refine ⟨h1, h2, ?_, ?_⟩
    · exact le_trans h3 (by simp)
    · exact le_trans h4 (by simp)
  | true =>
    have hmu : mag * 16 ≤ 13 * 2 ^ c.P :=
      le_trans (Nat.mul_le_mul_right 16 (Nat.le_of_ble_eq_true hbr)) hv.umax_le
    have hT := taylor_fixed c.P K mag c.tau hmu hv.tau_ok
    simp only at hT
    rw [hv.hc_eq, hv.hs_eq, hv.dcos_eq, hv.dsin_eq, hv.one_eq]
    obtain ⟨tC, tS, tCle, tSle⟩ := hT
    rw [← hu] at tC tS
    set C := horner (2 ^ c.P) (Nat.shiftRight (Nat.mul mag mag) c.P)
      ((divList fcos K).map (fun d : ℕ => 2 ^ c.P * d)) (2 ^ c.P)
    set S0 := Nat.shiftRight (Nat.mul mag (horner (2 ^ c.P) (Nat.shiftRight (Nat.mul mag mag) c.P)
      ((divList fsin K).map (fun d : ℕ => 2 ^ c.P * d)) (2 ^ c.P))) c.P
    have hc1 : |Real.cos φ * 2 ^ c.P - C| ≤ ((Nat.add (Nat.add 3 c.tau) rphi : ℕ) : ℝ) := by
      have e : Real.cos φ * 2 ^ c.P - C = (Real.cos φ - Real.cos u) * 2 ^ c.P + (2 ^ c.P * Real.cos u - C) := by ring
      rw [e]
      calc |(Real.cos φ - Real.cos u) * 2 ^ c.P + (2 ^ c.P * Real.cos u - C)|
          ≤ |(Real.cos φ - Real.cos u) * 2 ^ c.P| + |2 ^ c.P * Real.cos u - (C : ℝ)| := abs_add_le _ _
        _ ≤ rphi + (3 + c.tau) := by
          have a1 : |(Real.cos φ - Real.cos u) * 2 ^ c.P| ≤ rphi := by
            rw [abs_mul, abs_of_pos hP]; exact hcosφ
          have a2 : |2 ^ c.P * Real.cos u - (C : ℝ)| ≤ 3 + c.tau := by
            rw [abs_sub_comm]; exact tC
          exact add_le_add a1 a2
        _ = _ := by simp only [p_add]; push_cast; ring
    have hs1 : |Real.sin φ * 2 ^ c.P - sgn pos * S0| ≤ ((Nat.add (Nat.add 4 c.tau) rphi : ℕ) : ℝ) := by
      have e : Real.sin φ * 2 ^ c.P - sgn pos * S0
          = (Real.sin φ - sgn pos * Real.sin u) * 2 ^ c.P + sgn pos * (2 ^ c.P * Real.sin u - S0) := by ring
      rw [e]
      calc |(Real.sin φ - sgn pos * Real.sin u) * 2 ^ c.P + sgn pos * (2 ^ c.P * Real.sin u - S0)|
          ≤ |(Real.sin φ - sgn pos * Real.sin u) * 2 ^ c.P| + |sgn pos * (2 ^ c.P * Real.sin u - (S0 : ℝ))| :=
            abs_add_le _ _
        _ ≤ rphi + (4 + c.tau) := by
          have a1 : |(Real.sin φ - sgn pos * Real.sin u) * 2 ^ c.P| ≤ rphi := by
            rw [abs_mul, abs_of_pos hP]; exact hsinφ
          have a2 : |sgn pos * (2 ^ c.P * Real.sin u - (S0 : ℝ))| ≤ 4 + c.tau := by
            rw [abs_mul, abs_sgn, one_mul, abs_sub_comm]; exact tS
          exact add_le_add a1 a2
        _ = _ := by simp only [p_add]; push_cast; ring
    obtain ⟨h1, h2, h3, h4⟩ := rotate_sound c.P φ k C _ S0 _ pos hc1 hs1
    rw [← hθ] at h1 h2
    refine ⟨h1, h2, le_trans h3 (max_le tCle tSle), le_trans h4 (max_le tCle tSle)⟩

/-! ## H. the zeta term, the term product, one step, the run -/

theorem inv_sqrt_eq (m : ℕ) (hm : 0 < m) :
    Real.exp (-(1 / 2) * Real.log m) = 1 / Real.sqrt m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  calc Real.exp (-(1 / 2) * Real.log m) = (Real.exp ((1 / 2) * Real.log m))⁻¹ := by
        rw [← Real.exp_neg]; ring_nf
    _ = (Real.sqrt m)⁻¹ := by rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hm0]; ring_nf
    _ = 1 / Real.sqrt m := (one_div _).symm

/-- `Re (m^(-(1/2 + i t))) = m^(-1/2) cos(t log m)`, `Im = -m^(-1/2) sin(t log m)`. -/
theorem cpow_term (m : ℕ) (hm : 0 < m) (t : ℝ) :
    ((m : ℂ) ^ (-((1 : ℂ) / 2 + (t : ℂ) * Complex.I))).re = 1 / Real.sqrt m * Real.cos (t * Real.log m) ∧
    ((m : ℂ) ^ (-((1 : ℂ) / 2 + (t : ℂ) * Complex.I))).im = -(1 / Real.sqrt m * Real.sin (t * Real.log m)) := by
  have hnpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hne : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hhalf : (1 : ℂ) / 2 = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
  have hlog : Complex.log (m : ℂ) = (Real.log m : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log hnpos.le]
  have hre : (((Real.log m : ℝ) : ℂ) * -(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
      = -(1 / 2) * Real.log m := by
    simp only [Complex.mul_re, Complex.neg_re, Complex.add_re, Complex.neg_im, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im]; ring
  have him : (((Real.log m : ℝ) : ℂ) * -(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).im
      = -(t * Real.log m) := by
    simp only [Complex.mul_im, Complex.neg_re, Complex.add_re, Complex.neg_im, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.I_re, Complex.I_im]; ring
  rw [Complex.cpow_def_of_ne_zero hne, hlog, hhalf]
  constructor
  · rw [Complex.exp_re, hre, him, Real.cos_neg, inv_sqrt_eq m hm]
  · rw [Complex.exp_im, hre, him, Real.sin_neg, inv_sqrt_eq m hm]; ring

/-- The term product: `x v` from `x ∈ [Rlo, Rhi] / 2^P` (`0 ≤ x ≤ 1`) and a signed ball of `v`. -/
theorem tmul_sound (P Rlo Rhi vm vr : ℕ) (vs : Bool) (x v : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hRlo : (Rlo : ℝ) ≤ x * 2 ^ P) (hRhi : x * 2 ^ P ≤ Rhi)
    (hv : |v * 2 ^ P - sgn vs * vm| ≤ vr) (hvm : vm ≤ 2 ^ P) :
    |x * v * 2 ^ P - sgn vs * ((Nat.shiftRight (Nat.mul Rhi vm) P : ℕ) : ℝ)|
      ≤ ((Nat.add (Nat.add (Nat.shiftRight (Nat.mul Rhi vr) P) (Nat.sub Rhi Rlo)) 2 : ℕ) : ℝ) := by
  have hP : (0 : ℝ) < 2 ^ P := two_pow_pos' P
  have hle : Rlo ≤ Rhi := by exact_mod_cast le_trans hRlo hRhi
  obtain ⟨a1, a2⟩ := shr_bounds (Rhi * vm) P
  obtain ⟨b1, b2⟩ := shr_bounds (Rhi * vr) P
  simp only [p_add, p_mul, p_sub, p_shr] at a1 a2 b1 b2 ⊢
  push_cast [Nat.cast_sub hle]
  have hvmR : (vm : ℝ) ≤ 2 ^ P := by exact_mod_cast hvm
  set T := (((Rhi * vm) >>> P : ℕ) : ℝ)
  set U := (((Rhi * vr) >>> P : ℕ) : ℝ)
  -- decomposition
  have e : x * v * 2 ^ P - sgn vs * T
      = x * (v * 2 ^ P - sgn vs * vm) + sgn vs * (vm * (x * 2 ^ P - Rhi) / 2 ^ P)
        + sgn vs * ((Rhi : ℝ) * vm / 2 ^ P - T) := by
    field_simp; ring
  rw [e]
  have t1 : |x * (v * 2 ^ P - sgn vs * vm)| ≤ U + 1 := by
    rw [abs_mul, abs_of_nonneg hx0]
    have : x * |v * 2 ^ P - sgn vs * vm| ≤ x * vr := mul_le_mul_of_nonneg_left hv hx0
    have hxr : x * (vr : ℝ) ≤ (Rhi : ℝ) * vr / 2 ^ P := by
      rw [le_div_iff₀ hP]; nlinarith [(by positivity : (0 : ℝ) ≤ vr)]
    push_cast at b2
    linarith
  have t2 : |sgn vs * (vm * (x * 2 ^ P - Rhi) / 2 ^ P)| ≤ (Rhi : ℝ) - Rlo := by
    rw [abs_mul, abs_sgn, one_mul, abs_div, abs_of_pos hP, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ vm),
      div_le_iff₀ hP]
    have : |x * 2 ^ P - Rhi| ≤ (Rhi : ℝ) - Rlo := by rw [abs_le]; constructor <;> linarith
    have hRR : (0 : ℝ) ≤ (Rhi : ℝ) - Rlo := by linarith
    nlinarith [abs_nonneg (x * 2 ^ P - Rhi)]
  have t3 : |sgn vs * ((Rhi : ℝ) * vm / 2 ^ P - T)| ≤ 1 := by
    rw [abs_mul, abs_sgn, one_mul, abs_le]
    push_cast at a1 a2
    constructor <;> linarith
  calc |x * (v * 2 ^ P - sgn vs * vm) + sgn vs * (vm * (x * 2 ^ P - Rhi) / 2 ^ P)
          + sgn vs * ((Rhi : ℝ) * vm / 2 ^ P - T)|
      ≤ |x * (v * 2 ^ P - sgn vs * vm)| + |sgn vs * (vm * (x * 2 ^ P - Rhi) / 2 ^ P)|
          + |sgn vs * ((Rhi : ℝ) * vm / 2 ^ P - T)| := by
        have := abs_add_le (x * (v * 2 ^ P - sgn vs * vm) + sgn vs * (vm * (x * 2 ^ P - Rhi) / 2 ^ P))
          (sgn vs * ((Rhi : ℝ) * vm / 2 ^ P - T))
        have := abs_add_le (x * (v * 2 ^ P - sgn vs * vm)) (sgn vs * (vm * (x * 2 ^ P - Rhi) / 2 ^ P))
        linarith
    _ ≤ (U + 1) + ((Rhi : ℝ) - Rlo) + 1 := by linarith
    _ = U + ((Rhi : ℝ) - Rlo) + 2 := by ring

/-- The partial zeta sum `Sum_{k=1}^{n} k^(-(1/2 + i t))`. -/
noncomputable def psum (t : ℝ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.Ico 1 (n + 1), (k : ℂ) ^ (-((1 : ℂ) / 2 + (t : ℂ) * Complex.I))

/-- The loop invariant after `n` terms. -/
def Inv (c : Cfg) (t : ℝ) (n : ℕ) (s : St) : Prop :=
  s.n = n ∧ 1 ≤ n ∧ (s.llo : ℝ) ≤ Real.log n * 2 ^ c.P ∧ Real.log n * 2 ^ c.P ≤ s.lhi ∧
  |(psum t n).re * 2 ^ c.P - ((s.reP : ℝ) - s.reN)| ≤ s.reR ∧
  |(psum t n).im * 2 ^ c.P - ((s.imP : ℝ) - s.imN)| ≤ s.imR

theorem inv_init (c : Cfg) (t : ℝ) (hone : c.one = 2 ^ c.P) : Inv c t 1 (St.init c) := by
  have hps : psum t 1 = 1 := by simp [psum]
  refine ⟨rfl, le_rfl, ?_, ?_, ?_, ?_⟩ <;> simp [St.init, hps, hone]

theorem logInc_spec (c : Cfg) (t : ℝ) (K : ℕ) (hv : Valid c t K) (m : ℕ) :
    LogSpec (2 ^ c.P) m (logInc c m) := by
  rw [← hv.one_eq]
  show LogSpec c.one m (Bool.rec (logLoop c.one m c.lnfuel 0 m 0) (c.lnf m) (Nat.ble c.lnbig m))
  cases Nat.ble c.lnbig m with
  | false => exact logLoop_spec c.one m c.lnfuel 0 m 0 (by ring) (by simp)
  | true =>
    show LogSpec c.one m (c.lnf m)
    rw [hv.lnf_eq]; exact logFix_spec c.one m c.lnK 0 m 0 (by ring) (by simp)

theorem step_sound (c : Cfg) (t : ℝ) (K : ℕ) (hv : Valid c t K) (n : ℕ) (s : St)
    (hI : Inv c t n s) : Inv c t (n + 1) (step c s) := by
  obtain ⟨hn, h1, hllo, hlhi, hre, him⟩ := hI
  have hP : (0 : ℝ) < 2 ^ c.P := two_pow_pos' c.P
  set m := n + 1 with hm
  have hm2 : 2 ≤ m := by omega
  have hmpos : 0 < m := by omega
  -- log
  have hls := logInc_spec c t K hv m
  obtain ⟨lb1, lb2⟩ := logInc_bound c.P m hm2 (logInc c m) hls
  have hmn : (m : ℝ) - 1 = (n : ℝ) := by rw [hm]; push_cast; ring
  rw [hmn] at lb1 lb2
  set lg := logInc c m with hlg
  have hstep_n : (step c s).n = m := by show Nat.succ s.n = m; rw [hn]
  have hllo' : ((step c s).llo : ℝ) = s.llo + lg.1 := by
    show ((Nat.add s.llo (logInc c (Nat.succ s.n)).1 : ℕ) : ℝ) = _
    rw [hn]; simp only [p_add]; push_cast; rfl
  have hlhi' : ((step c s).lhi : ℝ) = s.lhi + lg.1 + lg.2.1 + ((2 ^ (c.P + 1) / lg.2.2 : ℕ) + 1) := by
    show ((Nat.add (Nat.add (Nat.add s.lhi (logInc c (Nat.succ s.n)).1) (logInc c (Nat.succ s.n)).2.1)
      (Nat.add (Nat.div c.two1 (logInc c (Nat.succ s.n)).2.2) 1) : ℕ) : ℝ) = _
    rw [hn, hv.two1_eq]; simp only [p_add, p_div]; push_cast; rfl
  have hLlo : ((step c s).llo : ℝ) ≤ Real.log m * 2 ^ c.P := by
    rw [hllo']; nlinarith [lb1, hllo]
  have hLhi : Real.log m * 2 ^ c.P ≤ (step c s).lhi := by
    rw [hlhi']; nlinarith [lb2, hlhi]
  -- the term data
  set o := termOf c s with ho
  have hoLlo : o.llo = (step c s).llo := rfl
  have hoLhi : o.lhi = (step c s).lhi := rfl
  -- sqrt
  have hsq : (o.Rlo : ℝ) ≤ 2 ^ c.P / Real.sqrt m ∧ 2 ^ c.P / Real.sqrt m ≤ o.Rhi := by
    have := sqrt_bracket c.P m (isqrt c m (Nat.div c.oneSq m) s.g) (by omega)
    rw [← hv.oneSq_eq, ← hv.one_eq] at this
    have e1 : o.Rlo = Bool.rec 0 (Bool.rec (Nat.div c.oneSq (Nat.mul m (isqrt c m (Nat.div c.oneSq m) s.g)))
        (isqrt c m (Nat.div c.oneSq m) s.g)
        (Nat.ble (Nat.mul (Nat.mul (isqrt c m (Nat.div c.oneSq m) s.g) (isqrt c m (Nat.div c.oneSq m) s.g)) m)
          c.oneSq)) (Nat.ble 1 (isqrt c m (Nat.div c.oneSq m) s.g)) := by
      show (termOf c s).Rlo = _; simp only [termOf, hn]; rfl
    have e2 : o.Rhi = Bool.rec c.one (Bool.rec (isqrt c m (Nat.div c.oneSq m) s.g)
        (Nat.add (Nat.div c.oneSq (Nat.mul m (isqrt c m (Nat.div c.oneSq m) s.g))) 1)
        (Nat.ble (Nat.mul (Nat.mul (isqrt c m (Nat.div c.oneSq m) s.g) (isqrt c m (Nat.div c.oneSq m) s.g)) m)
          c.oneSq)) (Nat.ble 1 (isqrt c m (Nat.div c.oneSq m) s.g)) := by
      show (termOf c s).Rhi = _; simp only [termOf, hn]; rfl
    rw [e1, e2]; exact this
  set x := 1 / Real.sqrt m with hx
  have hsqrt1 : 1 ≤ Real.sqrt m := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 1 ≤ m))
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by rw [hx, div_le_one (by linarith)]; exact hsqrt1
  have hxlo : (o.Rlo : ℝ) ≤ x * 2 ^ c.P := by rw [hx, one_div_mul_eq_div]; exact hsq.1
  have hxhi : x * 2 ^ c.P ≤ o.Rhi := by rw [hx, one_div_mul_eq_div]; exact hsq.2
  -- theta and trig
  have htb := theta_bracket c.P c.tn c.tq (Real.log m) o.llo o.lhi
    (by rw [hoLlo]; exact hLlo) (by rw [hoLhi]; exact hLhi)
  rw [← hv.t_eq] at htb
  have htr : o.tr = trig c (Nat.shiftRight (Nat.mul c.tn o.llo) c.tq)
      (Nat.add (Nat.shiftRight (Nat.mul c.tn o.lhi) c.tq) 1) := by
    show (termOf c s).tr = _; simp only [termOf]; rfl
  have hT := trig_sound c t K hv (t * Real.log m) _ _ htb.1 htb.2
  rw [← htr] at hT
  obtain ⟨hcos, hsin, hcm, hsm⟩ := hT
  -- the two term balls
  have hRe := tmul_sound c.P o.Rlo o.Rhi o.tr.cm o.tr.cr o.tr.cs x (Real.cos (t * Real.log m))
    hx0 hx1 hxlo hxhi hcos hcm
  have hIm := tmul_sound c.P o.Rlo o.Rhi o.tr.sm o.tr.sr o.tr.ss x (Real.sin (t * Real.log m))
    hx0 hx1 hxlo hxhi hsin hsm
  obtain ⟨ere, eim⟩ := cpow_term m hmpos t
  have hps : psum t m = psum t n + (m : ℂ) ^ (-((1 : ℂ) / 2 + (t : ℂ) * Complex.I)) := by
    simp only [psum, hm]
    rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1)]
  refine ⟨hstep_n, by omega, hLlo, hLhi, ?_, ?_⟩
  · -- real part
    rw [hps, Complex.add_re, ere]
    set T := ((Nat.shiftRight (Nat.mul o.Rhi o.tr.cm) c.P : ℕ) : ℝ)
    set R := ((Nat.add (Nat.add (Nat.shiftRight (Nat.mul o.Rhi o.tr.cr) c.P) (Nat.sub o.Rhi o.Rlo)) 2 : ℕ) : ℝ) with hR
    have hcenter : ((step c s).reP : ℝ) - (step c s).reN = ((s.reP : ℝ) - s.reN) + sgn o.tr.cs * T := by
      show ((Bool.rec s.reP (Nat.add s.reP (Nat.shiftRight (Nat.mul o.Rhi o.tr.cm) c.P)) o.tr.cs : ℕ) : ℝ)
        - ((Bool.rec (Nat.add s.reN (Nat.shiftRight (Nat.mul o.Rhi o.tr.cm) c.P)) s.reN o.tr.cs : ℕ) : ℝ) = _
      cases o.tr.cs <;> simp [sgn, T] <;> ring
    have hrad : ((step c s).reR : ℝ) = s.reR + R := by
      show ((Nat.add s.reR (Nat.add (Nat.add (Nat.shiftRight (Nat.mul o.Rhi o.tr.cr) c.P) (Nat.sub o.Rhi o.Rlo)) 2) : ℕ) : ℝ) = _
      rw [hR]; simp only [p_add]; push_cast; ring
    rw [hcenter, hrad]
    have e : ((psum t n).re + x * Real.cos (t * Real.log m)) * 2 ^ c.P
        - (((s.reP : ℝ) - s.reN) + sgn o.tr.cs * T)
        = ((psum t n).re * 2 ^ c.P - ((s.reP : ℝ) - s.reN))
          + (x * Real.cos (t * Real.log m) * 2 ^ c.P - sgn o.tr.cs * T) := by ring
    rw [e]
    exact le_trans (abs_add_le _ _) (add_le_add hre hRe)
  · -- imaginary part:  Im term = -(x sin)
    rw [hps, Complex.add_im, eim]
    set T := ((Nat.shiftRight (Nat.mul o.Rhi o.tr.sm) c.P : ℕ) : ℝ)
    set R := ((Nat.add (Nat.add (Nat.shiftRight (Nat.mul o.Rhi o.tr.sr) c.P) (Nat.sub o.Rhi o.Rlo)) 2 : ℕ) : ℝ) with hR
    have hcenter : ((step c s).imP : ℝ) - (step c s).imN = ((s.imP : ℝ) - s.imN) - sgn o.tr.ss * T := by
      show ((Bool.rec (Nat.add s.imP (Nat.shiftRight (Nat.mul o.Rhi o.tr.sm) c.P)) s.imP o.tr.ss : ℕ) : ℝ)
        - ((Bool.rec s.imN (Nat.add s.imN (Nat.shiftRight (Nat.mul o.Rhi o.tr.sm) c.P)) o.tr.ss : ℕ) : ℝ) = _
      cases o.tr.ss <;> simp [sgn, T] <;> ring
    have hrad : ((step c s).imR : ℝ) = s.imR + R := by
      show ((Nat.add s.imR (Nat.add (Nat.add (Nat.shiftRight (Nat.mul o.Rhi o.tr.sr) c.P) (Nat.sub o.Rhi o.Rlo)) 2) : ℕ) : ℝ) = _
      rw [hR]; simp only [p_add]; push_cast; ring
    rw [hcenter, hrad]
    have e : ((psum t n).im + -(x * Real.sin (t * Real.log m))) * 2 ^ c.P
        - (((s.imP : ℝ) - s.imN) - sgn o.tr.ss * T)
        = ((psum t n).im * 2 ^ c.P - ((s.imP : ℝ) - s.imN))
          - (x * Real.sin (t * Real.log m) * 2 ^ c.P - sgn o.tr.ss * T) := by ring
    rw [e]
    exact le_trans (abs_sub _ _) (add_le_add him hIm)

theorem run_sound (c : Cfg) (t : ℝ) (K : ℕ) (hv : Valid c t K) :
    ∀ (L n : ℕ) (s : St), Inv c t n s → Inv c t (n + L) (run c L s) := by
  intro L
  induction L with
  | zero => intro n s h; exact h
  | succ L ih =>
    intro n s h
    have := ih (n + 1) (step c s) (step_sound c t K hv n s h)
    rw [show n + (L + 1) = n + 1 + L by ring]
    exact this

theorem St.beq_eq (a b : St) (h : St.beq a b = true) : a = b := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := a
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := b
  simp only [St.beq, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
    Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5, Nat.eq_of_beq_eq_true h6,
    Nat.eq_of_beq_eq_true h7, Nat.eq_of_beq_eq_true h8, Nat.eq_of_beq_eq_true h9,
    Nat.eq_of_beq_eq_true h10]

/-- **Chunk composition.**  A kernel-checked chunk `St.beq (run c L s) s' = true` transports the
    invariant from `s` (after `n` terms) to `s'` (after `n + L` terms). -/
theorem chunk_sound (c : Cfg) (t : ℝ) (K : ℕ) (hv : Valid c t K) (L n : ℕ) (s s' : St)
    (hI : Inv c t n s) (hchk : St.beq (run c L s) s' = true) : Inv c t (n + L) s' := by
  rw [← St.beq_eq _ _ hchk]; exact run_sound c t K hv L n s hI

end ArbEcon
