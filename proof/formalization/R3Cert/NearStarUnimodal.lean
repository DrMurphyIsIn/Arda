/-
  **Strict unimodality of the near-star ladder NS(k), with unique maximum exactly at k = 5.**

  The near-star family `N(c,k)` (root with `c` cherries + `k` cherry-arm children) has, via the exact cavity
  telescoping (`cavity_potential.py`, `near_star_arithmetic_proof.py`), a log-amplitude depending only on
  `s = c + k`, namely `gVal s` (Sweep.lean), and its 11th-power-cleared exact rational avatar `Rval s`
  (`Rval s = exp(11 * gVal s)`).  This file proves the SHARP shape statement that `gVal_nonpos` (JTail.lean)
  only weakly implies:

      **`Rval` is strictly increasing on `{0,...,5}` and strictly decreasing on `{5,6,...}`, so it has a
      UNIQUE maximum at `s = 5`, where `Rval 5 = 1` exactly (the tie).**

  Equivalently `gVal` (hence `log Phi(NS)`) is strictly unimodal with unique maximizer `s = 5` and maximum
  value `0` -- i.e. `Phi(NS(k))` is maximised at exactly `k = 5` with maximum `1`.

  This is strictly stronger than `gVal_nonpos` (which gives only `gVal s <= 0`, via a finite `s < 11` check
  plus a linear tail); here BOTH the increasing half AND the infinite decreasing tail are exact, closing the
  uniqueness of the maximizer with NO finite cutoff and NO interval arithmetic.

  MECHANISM (the `529/486` single crossing).  The exact step ratio is
      `Rval (n+1) / Rval n = t n := Romval * (((4n+7)*(n+1)) / ((4n+3)*(n+2)))^11`,   `Romval = 486/529`.
  Since `D n := 4n^2+11n+6` is strictly increasing, the bracket `(1 + 1/D n)` is strictly decreasing, so `t`
  is strictly decreasing.  `t 4 > 1` and `t 5 < 1` (exact rationals), and for the infinite tail `n >= 5` the
  UNIFORM bound `t n <= Romval * (162/161)^11 < 1` (as `D n >= D 5 = 161`) closes the decreasing half for all
  `n` at once.  The `23^2/(2*3^5) = 529/486` constant is the 23-adic content of `621 = 3^3 * 23`.

  Cross-checked in exact `fractions.Fraction` arithmetic: `near_star_arithmetic_proof.verify_proof`.

  NOTE (honest scope): this is the near-star / tie-harmonic family only -- the marginal near-tie envelope --
  NOT the general-children `Phi <= 1` crux (still OPEN, `Reach.phi_le_one_of_potential` conditional on a valid
  potential).  It upgrades the near-star INSTANCE from `<= 0` to `strictly unimodal, unique max at the tie`.
-/
import Mathlib
import R3Cert.Sweep
import R3Cert.TieHarmonic

namespace R3Cert

open Real

/-! ## The exact step ratio and its factorisation. -/

/-- `Rval n > 0` for every `n` (it is a ratio of positive reals). -/
theorem Rval_pos (n : ℕ) : 0 < Rval n := by unfold Rval; positivity

/-- **The exact step recurrence** `Rval (n+1) = Rval n * Romval * (((4n+7)*(n+1)) / ((4n+3)*(n+2)))^11`.
    Pure algebra (`field_simp`/`ring`); `Romval = (3/2)^11 / (621/64)^2 = 486/529`. -/
theorem Rval_succ (n : ℕ) :
    Rval (n + 1) = Rval n * Romval
      * (((4 * (n : ℝ) + 7) * ((n : ℝ) + 1)) / (((4 * (n : ℝ) + 3)) * ((n : ℝ) + 2))) ^ 11 := by
  unfold Rval Romval
  have h1 : (11 * (n + 1) : ℕ) = 11 * n + 11 := by ring
  have h2 : (1 + 2 * (n + 1) : ℕ) = (1 + 2 * n) + 2 := by ring
  rw [h1, h2]
  push_cast
  rw [pow_add, pow_add, mul_pow, mul_pow, ← mul_pow, ← mul_pow]
  have hd1 : (4 * (n : ℝ) + 3) ≠ 0 := by positivity
  have hd2 : ((n : ℝ) + 2) ≠ 0 := by positivity
  have hd3 : (621 / 64 : ℝ) ≠ 0 := by norm_num
  have hd4 : (3 * ((n : ℝ) + 1)) ≠ 0 := by positivity
  have hn7 : (4 * (n : ℝ) + 7) = 4 * ((n : ℝ) + 1) + 3 := by ring
  field_simp
  ring

/-- `Romval = 486 / 529` (the `23`-adic content constant), as an exact rational. -/
theorem Romval_eq_rat : Romval = 486 / 529 := by
  unfold Romval; norm_num

/-- The step-ratio bracket `b n := ((4n+7)*(n+1)) / ((4n+3)*(n+2))`, written as `1 + 1 / D n`,
    `D n = 4n^2+11n+6`. -/
theorem bracket_eq (n : ℕ) :
    ((4 * (n : ℝ) + 7) * ((n : ℝ) + 1)) / (((4 * (n : ℝ) + 3)) * ((n : ℝ) + 2))
      = 1 + 1 / (4 * (n : ℝ) ^ 2 + 11 * (n : ℝ) + 6) := by
  have hD : (4 * (n : ℝ) ^ 2 + 11 * (n : ℝ) + 6) = (4 * (n : ℝ) + 3) * ((n : ℝ) + 2) := by ring
  rw [hD]
  have hne : ((4 * (n : ℝ) + 3) * ((n : ℝ) + 2)) ≠ 0 := by positivity
  field_simp
  ring

/-! ## The increasing half `Rval 0 < ... < Rval 5` (finite, exact rationals). -/

/-- Each of the five ascending steps `Rval n < Rval (n+1)`, `n = 0..4`, holds: `t n > 1` as an exact rational.
    (Established by evaluating `Rval` at the two consecutive `n` and comparing rationals via `norm_num`.) -/
theorem Rval_step_up (n : ℕ) (hn : n ≤ 4) : Rval n < Rval (n + 1) := by
  interval_cases n <;> (unfold Rval; norm_num)

/-! ## The decreasing tail `Rval (n+1) < Rval n` for ALL `n >= 5` (uniform, exact). -/

/-- **The uniform tail step:** for every `n >= 5`, `Rval (n+1) < Rval n`.  The step ratio
    `t n = Romval * (b n)^11` satisfies `b n <= 162/161` (since `D n >= 161`), so
    `t n <= (486/529) * (162/161)^11 < 1` (exact rational), hence `Rval (n+1) = Rval n * t n < Rval n`. -/
theorem Rval_step_down (n : ℕ) (hn : 5 ≤ n) : Rval (n + 1) < Rval n := by
  have hnr : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set b : ℝ := ((4 * (n : ℝ) + 7) * ((n : ℝ) + 1)) / (((4 * (n : ℝ) + 3)) * ((n : ℝ) + 2)) with hbdef
  -- b = 1 + 1/D, D = 4n^2+11n+6 >= 161, so 1 <= b <= 162/161
  have hbval : b = 1 + 1 / (4 * (n : ℝ) ^ 2 + 11 * (n : ℝ) + 6) := by rw [hbdef]; exact bracket_eq n
  have hDpos : (0 : ℝ) < 4 * (n : ℝ) ^ 2 + 11 * (n : ℝ) + 6 := by positivity
  have hDge : (161 : ℝ) ≤ 4 * (n : ℝ) ^ 2 + 11 * (n : ℝ) + 6 := by nlinarith [hnr]
  have hb_ge1 : (1 : ℝ) ≤ b := by
    rw [hbval]; have : 0 < 1 / (4 * (n : ℝ) ^ 2 + 11 * (n : ℝ) + 6) := by positivity
    linarith
  have hb_le : b ≤ 162 / 161 := by
    rw [hbval]
    have hfrac : 1 / (4 * (n : ℝ) ^ 2 + 11 * (n : ℝ) + 6) ≤ 1 / 161 := by
      apply one_div_le_one_div_of_le (by norm_num) hDge
    linarith
  -- (b)^11 <= (162/161)^11
  have hb11 : b ^ 11 ≤ (162 / 161 : ℝ) ^ 11 :=
    pow_le_pow_left₀ (by linarith [hb_ge1]) hb_le 11
  -- t n = Romval * b^11 <= (486/529)*(162/161)^11 < 1
  have hRom : Romval = 486 / 529 := Romval_eq_rat
  have hRompos : (0 : ℝ) < Romval := by rw [hRom]; norm_num
  have htlt : Romval * b ^ 11 < 1 := by
    have hup : Romval * b ^ 11 ≤ (486 / 529 : ℝ) * (162 / 161) ^ 11 := by
      rw [hRom]
      exact mul_le_mul_of_nonneg_left hb11 (by norm_num)
    have hnum : (486 / 529 : ℝ) * (162 / 161) ^ 11 < 1 := by norm_num
    linarith
  -- Rval(n+1) = Rval n * (Romval * b^11) < Rval n * 1 = Rval n
  have hstep : Rval (n + 1) = Rval n * (Romval * b ^ 11) := by
    rw [Rval_succ n, ← hbdef]; ring
  have hRvalpos := Rval_pos n
  rw [hstep]
  calc Rval n * (Romval * b ^ 11) < Rval n * 1 :=
        mul_lt_mul_of_pos_left htlt hRvalpos
    _ = Rval n := by ring

/-! ## Assembly: strict unimodality with the unique maximum at `s = 5`. -/

/-- `Rval 5 = 1` -- the exact tie value (`64*243*23 = 621*576`), the maximum. -/
theorem Rval_five_eq_one : Rval 5 = 1 := by unfold Rval; norm_num

/-- **`Rval` is strictly increasing on `{0,...,5}`:** `m < n <= 5 -> Rval m < Rval n`.  Induction on `n` with
    the moving hypotheses `m < n`, `n <= 5` reverted into the goal (so `ih` has the general form). -/
theorem Rval_strictMono_up {m : ℕ} : ∀ {n : ℕ}, m < n → n ≤ 5 → Rval m < Rval n := by
  intro n
  induction n with
  | zero => intro h _; omega
  | succ k ih =>
    intro hmn hn
    have hk4 : k ≤ 4 := by omega
    have hstep : Rval k < Rval (k + 1) := Rval_step_up k hk4
    rcases Nat.lt_succ_iff_lt_or_eq.mp hmn with hlt | heq
    · exact lt_trans (ih hlt (by omega)) hstep
    · rw [heq]; exact hstep

/-- **`Rval` is strictly decreasing on `{5,6,...}`:** `5 <= m < n -> Rval n < Rval m`.  Induction on `n` with
    the moving hypothesis `m < n` reverted into the goal (so `ih` has the general form). -/
theorem Rval_strictAnti_down {m : ℕ} (hm : 5 ≤ m) : ∀ {n : ℕ}, m < n → Rval n < Rval m := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ k ih =>
    intro hmn
    have hk5 : 5 ≤ k := by omega
    have hstep : Rval (k + 1) < Rval k := Rval_step_down k hk5
    rcases Nat.lt_succ_iff_lt_or_eq.mp hmn with hlt | heq
    · exact lt_trans hstep (ih hlt)
    · rw [heq] at hstep ⊢; exact hstep

/-- **NS(k) is strictly unimodal with unique maximum exactly at `k = 5`:** for every `n != 5`,
    `Rval n < Rval 5 = 1`.  (`Rval s = exp(11*gVal s)`, so `Phi(NS(s)) = exp(gVal s)` is maximised at exactly
    `s = 5`, with maximum `1` -- the tie.) -/
theorem Rval_unique_max (n : ℕ) (hn : n ≠ 5) : Rval n < Rval 5 := by
  rcases lt_or_gt_of_ne hn with h | h
  · exact Rval_strictMono_up h (by omega)
  · exact Rval_strictAnti_down (le_refl 5) h

/-- **The near-star amplitude `gVal` is strictly unimodal with unique maximizer `s = 5` and maximum `0`.**
    For `n != 5`, `gVal n < 0 = gVal 5`.  (Since `11 * gVal n = log (Rval n)` and `Rval` is `< Rval 5 = 1`
    off the tie, `gVal n < 0`; and `gVal 5 = 0` is the exact tie.)  Strictly stronger than `gVal_nonpos`. -/
theorem gVal_unique_max (n : ℕ) (hn : n ≠ 5) : gVal n < 0 := by
  have hlt : Rval n < 1 := by rw [← Rval_five_eq_one]; exact Rval_unique_max n hn
  have hpos : 0 < Rval n := Rval_pos n
  have hlog : Real.log (Rval n) < 0 := Real.log_neg hpos hlt
  have h11 : 11 * gVal n = Real.log (Rval n) := Rval_eq n
  linarith [h11, hlog]

/-- **Packaged unimodality of the near-star ladder:** `gVal 5 = 0` (reusing the proven `gVal_five_zero`,
    TieHarmonic.lean) and `gVal n < 0` for every `n != 5`.  Equivalently `Phi(NS(k)) <= 1` with equality iff
    `k = 5`, the STRICT (unique-maximizer) form -- strictly stronger than `gVal_nonpos`. -/
theorem near_star_unimodal : gVal 5 = 0 ∧ ∀ n : ℕ, n ≠ 5 → gVal n < 0 :=
  ⟨gVal_five_zero, gVal_unique_max⟩

end R3Cert
