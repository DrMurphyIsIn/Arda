/-  Arb4_Q.lean -- lane Arb4 (h1000 compaction): exact rational arithmetic for Boolean kernel
    checkers.

    A certificate side condition such as the error budget of an octant piece is a polynomial
    inequality between explicit rationals.  Closing it by `norm_num` stores the whole normalisation
    trace in the olean (about 300 KB per budget at height 1000).  Here the same inequality is
    computed by `decide +kernel` over plain `Int`/`Nat` arithmetic (GMP-accelerated literals) and
    transported to `ℝ` by ONE soundness theorem per operation, proved once:

      * `Q`             -- an UNNORMALISED rational `n / (dm + 1)` (`n : ℤ`, `dm : ℕ`): the
                           denominator is positive by construction, so no positivity bookkeeping;
                           `val` is its real value, `frac n d` the rational `n / d` (`d ≥ 1`);
      * `add sub mul neg qabs npow div sumQ` -- the operations, `val_*` their homomorphism laws;
      * `le lt`         -- the Boolean comparisons, `le_sound`, `lt_sound`.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (Arb4_AxiomGuard).  No `sorry`.  conjecture1_proved = False.
-/
import Mathlib

namespace Arb4

/-- A rational `n / (dm + 1)`, NOT normalised (numerator in `ℤ`, denominator minus one in `ℕ`). -/
structure Q where
  n : ℤ
  dm : ℕ

namespace Q

/-- The real value `n / (dm + 1)`. -/
noncomputable def val (a : Q) : ℝ := (a.n : ℝ) / ((a.dm : ℝ) + 1)

/-- The rational `n / d` (for `d ≥ 1`). -/
def frac (n : ℤ) (d : ℕ) : Q := ⟨n, d - 1⟩

/-- `m / 1`. -/
def ofNat (m : ℕ) : Q := ⟨(m : ℤ), 0⟩

/-- `m / 1`. -/
def ofInt (m : ℤ) : Q := ⟨m, 0⟩

def add (a b : Q) : Q := ⟨a.n * ((b.dm : ℤ) + 1) + b.n * ((a.dm : ℤ) + 1), a.dm * b.dm + a.dm + b.dm⟩

def sub (a b : Q) : Q := ⟨a.n * ((b.dm : ℤ) + 1) - b.n * ((a.dm : ℤ) + 1), a.dm * b.dm + a.dm + b.dm⟩

def mul (a b : Q) : Q := ⟨a.n * b.n, a.dm * b.dm + a.dm + b.dm⟩

def neg (a : Q) : Q := ⟨-a.n, a.dm⟩

/-- `|a|`. -/
def qabs (a : Q) : Q := ⟨(a.n.natAbs : ℤ), a.dm⟩

/-- `a ^ k`. -/
def npow (a : Q) : ℕ → Q
  | 0 => ⟨1, 0⟩
  | k + 1 => mul (npow a k) a

/-- `a / b` for a POSITIVE numerator of `b` (read through `Int.toNat`). -/
def div (a b : Q) : Q := ⟨a.n * ((b.dm : ℤ) + 1), (a.dm + 1) * b.n.toNat - 1⟩

/-- `Σ_{i < k} f i`. -/
def sumQ (f : ℕ → Q) : ℕ → Q
  | 0 => ⟨0, 0⟩
  | k + 1 => add (sumQ f k) (f k)

/-- `a ≤ b`, cross-multiplied. -/
def le (a b : Q) : Bool := decide (a.n * ((b.dm : ℤ) + 1) ≤ b.n * ((a.dm : ℤ) + 1))

/-- `a < b`, cross-multiplied. -/
def lt (a b : Q) : Bool := decide (a.n * ((b.dm : ℤ) + 1) < b.n * ((a.dm : ℤ) + 1))

/-! ## The value homomorphism -/

theorem den_pos (a : Q) : (0 : ℝ) < (a.dm : ℝ) + 1 := by positivity

theorem den_ne (a : Q) : (a.dm : ℝ) + 1 ≠ 0 := ne_of_gt (den_pos a)

theorem val_frac (n : ℤ) {d : ℕ} (hd : 1 ≤ d) : (frac n d).val = (n : ℝ) / (d : ℝ) := by
  simp only [val, frac]
  rw [Nat.cast_sub hd]
  push_cast
  ring_nf

@[simp] theorem val_ofNat (m : ℕ) : (ofNat m).val = (m : ℝ) := by
  simp [val, ofNat]

@[simp] theorem val_ofInt (m : ℤ) : (ofInt m).val = (m : ℝ) := by
  simp [val, ofInt]

theorem cast_den_mul (a b : Q) :
    (((a.dm * b.dm + a.dm + b.dm : ℕ) : ℝ) + 1) = ((a.dm : ℝ) + 1) * ((b.dm : ℝ) + 1) := by
  push_cast; ring

theorem val_add (a b : Q) : (add a b).val = a.val + b.val := by
  have h1 := den_ne a
  have h2 := den_ne b
  simp only [val, add]
  rw [cast_den_mul]
  push_cast
  field_simp

theorem val_sub (a b : Q) : (sub a b).val = a.val - b.val := by
  have h1 := den_ne a
  have h2 := den_ne b
  simp only [val, sub]
  rw [cast_den_mul]
  push_cast
  field_simp

theorem val_mul (a b : Q) : (mul a b).val = a.val * b.val := by
  simp only [val, mul]
  rw [cast_den_mul]
  push_cast
  rw [mul_div_mul_comm]

theorem val_neg (a : Q) : (neg a).val = -a.val := by
  simp only [val, neg]
  push_cast
  ring

theorem val_qabs (a : Q) : (qabs a).val = |a.val| := by
  simp only [val, qabs]
  rw [abs_div, abs_of_pos (den_pos a), Int.natCast_natAbs, Int.cast_abs]

theorem val_npow (a : Q) : ∀ k, (npow a k).val = a.val ^ k
  | 0 => by simp [npow, val]
  | k + 1 => by rw [npow, val_mul, val_npow a k, pow_succ]

theorem val_div (a : Q) {b : Q} (hb : 0 < b.n) : (div a b).val = a.val / b.val := by
  have hb1 : 1 ≤ b.n.toNat := by omega
  have hb' : ((b.n.toNat : ℕ) : ℝ) = (b.n : ℝ) := by
    have : ((b.n.toNat : ℕ) : ℤ) = b.n := Int.toNat_of_nonneg hb.le
    exact_mod_cast this
  have hbpos : (0 : ℝ) < (b.n : ℝ) := by exact_mod_cast hb
  have hge : 1 ≤ (a.dm + 1) * b.n.toNat := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have e : ((((a.dm + 1) * b.n.toNat - 1 : ℕ)) : ℝ) + 1 = ((a.dm : ℝ) + 1) * (b.n : ℝ) := by
    rw [Nat.cast_sub hge]
    push_cast
    rw [hb']
    ring
  have h1 := den_ne a
  have h2 := den_ne b
  simp only [val, div]
  rw [e]
  push_cast
  field_simp

theorem val_sumQ (f : ℕ → Q) : ∀ k, (sumQ f k).val = ∑ i ∈ Finset.range k, (f i).val
  | 0 => by simp [sumQ, val]
  | k + 1 => by rw [sumQ, val_add, val_sumQ f k, Finset.sum_range_succ]

/-! ## The comparisons -/

theorem le_sound {a b : Q} (h : le a b = true) : a.val ≤ b.val := by
  have hz : a.n * ((b.dm : ℤ) + 1) ≤ b.n * ((a.dm : ℤ) + 1) := of_decide_eq_true h
  have hr : (a.n : ℝ) * ((b.dm : ℝ) + 1) ≤ (b.n : ℝ) * ((a.dm : ℝ) + 1) := by exact_mod_cast hz
  simp only [val]
  rw [div_le_div_iff₀ (den_pos a) (den_pos b)]
  exact hr

theorem lt_sound {a b : Q} (h : lt a b = true) : a.val < b.val := by
  have hz : a.n * ((b.dm : ℤ) + 1) < b.n * ((a.dm : ℤ) + 1) := of_decide_eq_true h
  have hr : (a.n : ℝ) * ((b.dm : ℝ) + 1) < (b.n : ℝ) * ((a.dm : ℝ) + 1) := by exact_mod_cast hz
  simp only [val]
  rw [div_lt_div_iff₀ (den_pos a) (den_pos b)]
  exact hr

/-- `0 < n` makes the value positive. -/
theorem val_pos {a : Q} (hn : 0 < a.n) : 0 < a.val := by
  have hn' : (0 : ℝ) < a.n := by exact_mod_cast hn
  exact div_pos hn' (den_pos a)

/-- `0 ≤ n` makes the value nonnegative. -/
theorem val_nonneg {a : Q} (hn : 0 ≤ a.n) : 0 ≤ a.val := by
  have hn' : (0 : ℝ) ≤ a.n := by exact_mod_cast hn
  exact div_nonneg hn' (den_pos a).le

/-- `a ≠ 0` from a nonzero numerator. -/
theorem val_ne_zero {a : Q} (hn : a.n ≠ 0) : a.val ≠ 0 := by
  have hn' : (a.n : ℝ) ≠ 0 := by exact_mod_cast hn
  exact div_ne_zero hn' (den_ne a)

/-! ## Literal conversions (small proof terms for the generated certificates) -/

theorem cv_nat (m : ℕ) [m.AtLeastTwo] : (ofNat (OfNat.ofNat m)).val = (OfNat.ofNat m : ℝ) := by
  rw [val_ofNat]; exact Nat.cast_ofNat

theorem cv_one : (ofNat 1).val = (1 : ℝ) := by rw [val_ofNat, Nat.cast_one]

theorem cv_frac (a b : ℕ) [a.AtLeastTwo] [b.AtLeastTwo] :
    (frac (OfNat.ofNat a) (OfNat.ofNat b)).val = (OfNat.ofNat a : ℝ) / (OfNat.ofNat b : ℝ) := by
  rw [val_frac _ (by exact Nat.AtLeastTwo.one_lt.le), Int.cast_ofNat, Nat.cast_ofNat]

theorem cv_sub (a b : Q) (x y : ℝ) (ha : a.val = x) (hb : b.val = y) : (sub a b).val = x - y := by
  rw [val_sub, ha, hb]

theorem cv_add (a b : Q) (x y : ℝ) (ha : a.val = x) (hb : b.val = y) : (add a b).val = x + y := by
  rw [val_add, ha, hb]

end Q

end Arb4
