/-
NatRootBracket -- the once-proved transport lemmas behind Telperion's
`nat_root_bracket_table` emitter.

Ported from the hand-built CN-1 formalization (tenth-discriminant, CN1/Numerics/RpowBounds.lean
and the rational-base lemma of CN1/Numerics/GammaRatio.lean; Lean v4.34.1 / Mathlib d13f23b) to
Lean v4.32.0 / Mathlib v4.32.0.  Mathlib only.  The statements are unchanged; the three
rational-base variants that CN-1 did not need (`rpow_rat_neg_div_upper`, `rpow_rat_div_lower`,
`rpow_rat_div_upper`) are added by the same proof.

The kernel decides integer inequalities on literals (`decide +kernel`, GMP-accelerated `Nat`);
these lemmas transport them to real `rpow` brackets:

* `rpow_div_lower/upper`:          `L^q ≤ m^p S^q`      gives `L/S ≤ m^(p/q)`;
                                    `m^p S^q ≤ U^q`      gives `m^(p/q) ≤ U/S`;
* `rpow_neg_div_lower/upper`:      `L^q m^p ≤ S^q`      gives `L/S ≤ m^(-p/q)`;
                                    `S^q ≤ U^q m^p`      gives `m^(-p/q) ≤ U/S`;
* `rpow_rat_div_lower/upper`:      `L^q b^p ≤ a^p S^q`  gives `L/S ≤ (a/b)^(p/q)`;
                                    `a^p S^q ≤ U^q b^p`  gives `(a/b)^(p/q) ≤ U/S`;
* `rpow_rat_neg_div_lower/upper`:  `L^q a^p ≤ b^p S^q`  gives `L/S ≤ (a/b)^(-p/q)`;
                                    `b^p S^q ≤ U^q a^p`  gives `(a/b)^(-p/q) ≤ U/S`;
* `sum_block_lo_neg/hi_neg`: a block of `K` such brackets, read from a `List ℕ` by `getD`,
  bounds a block of the range sum `∑ (i+1)^(-p/q)`;
* `sum_range_chunk`: a range sum over `C * K` terms as `C` blocks of `K`.

conjecture1_proved = False.
-/
import Mathlib

set_option autoImplicit false

namespace NatRootBracket

/-- `L^q ≤ m^p S^q` gives `L/S ≤ m^(p/q)`. -/
lemma rpow_div_lower (m p q L S : ℕ) (hq : 0 < q) (hS : 0 < S)
    (hL : L ^ q ≤ m ^ p * S ^ q) : (L : ℝ) / S ≤ (m : ℝ) ^ ((p : ℝ) / q) := by
  have hm : (0 : ℝ) ≤ m := by positivity
  have hy : (0 : ℝ) ≤ (m : ℝ) ^ ((p : ℝ) / q) := Real.rpow_nonneg hm _
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have hyq : ((m : ℝ) ^ ((p : ℝ) / q)) ^ q = (m : ℝ) ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm, div_mul_cancel₀ _ hq', Real.rpow_natCast]
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  rw [← pow_le_pow_iff_left₀ (by positivity) hy hq.ne', hyq, div_pow, div_le_iff₀ (by positivity)]
  exact_mod_cast hL

/-- `m^p S^q ≤ U^q` gives `m^(p/q) ≤ U/S`. -/
lemma rpow_div_upper (m p q U S : ℕ) (hq : 0 < q) (hS : 0 < S)
    (hU : m ^ p * S ^ q ≤ U ^ q) : (m : ℝ) ^ ((p : ℝ) / q) ≤ (U : ℝ) / S := by
  have hm : (0 : ℝ) ≤ m := by positivity
  have hy : (0 : ℝ) ≤ (m : ℝ) ^ ((p : ℝ) / q) := Real.rpow_nonneg hm _
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have hyq : ((m : ℝ) ^ ((p : ℝ) / q)) ^ q = (m : ℝ) ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm, div_mul_cancel₀ _ hq', Real.rpow_natCast]
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  rw [← pow_le_pow_iff_left₀ hy (by positivity) hq.ne', hyq, div_pow, le_div_iff₀ (by positivity)]
  exact_mod_cast hU

/-- `L^q m^p ≤ S^q` gives `L/S ≤ m^(-p/q)` (for `0 < m`). -/
lemma rpow_neg_div_lower (m p q L S : ℕ) (hm : 0 < m) (hq : 0 < q) (hS : 0 < S)
    (hL : L ^ q * m ^ p ≤ S ^ q) : (L : ℝ) / S ≤ (m : ℝ) ^ (-((p : ℝ) / q)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hy : (0 : ℝ) ≤ (m : ℝ) ^ (-((p : ℝ) / q)) := Real.rpow_nonneg hm'.le _
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have hyq : ((m : ℝ) ^ (-((p : ℝ) / q))) ^ q = 1 / (m : ℝ) ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm'.le, neg_mul, div_mul_cancel₀ _ hq',
      Real.rpow_neg hm'.le, Real.rpow_natCast, one_div]
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  rw [← pow_le_pow_iff_left₀ (by positivity) hy hq.ne', hyq, div_pow,
    div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  exact_mod_cast hL

/-- `S^q ≤ U^q m^p` gives `m^(-p/q) ≤ U/S` (for `0 < m`). -/
lemma rpow_neg_div_upper (m p q U S : ℕ) (hm : 0 < m) (hq : 0 < q) (hS : 0 < S)
    (hU : S ^ q ≤ U ^ q * m ^ p) : (m : ℝ) ^ (-((p : ℝ) / q)) ≤ (U : ℝ) / S := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hy : (0 : ℝ) ≤ (m : ℝ) ^ (-((p : ℝ) / q)) := Real.rpow_nonneg hm'.le _
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have hyq : ((m : ℝ) ^ (-((p : ℝ) / q))) ^ q = 1 / (m : ℝ) ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm'.le, neg_mul, div_mul_cancel₀ _ hq',
      Real.rpow_neg hm'.le, Real.rpow_natCast, one_div]
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  rw [← pow_le_pow_iff_left₀ hy (by positivity) hq.ne', hyq, div_pow,
    div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  exact_mod_cast hU

/-- `L^q b^p ≤ a^p S^q` gives `L/S ≤ (a/b)^(p/q)` (for `0 < a`, `0 < b`). -/
lemma rpow_rat_div_lower (a b p q L S : ℕ) (ha : 0 < a) (hb : 0 < b) (hq : 0 < q) (hS : 0 < S)
    (hL : L ^ q * b ^ p ≤ a ^ p * S ^ q) : (L : ℝ) / S ≤ ((a : ℝ) / b) ^ ((p : ℝ) / q) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hab : (0 : ℝ) < (a : ℝ) / b := by positivity
  have hy : (0 : ℝ) ≤ ((a : ℝ) / b) ^ ((p : ℝ) / q) := Real.rpow_nonneg hab.le _
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have hyq : (((a : ℝ) / b) ^ ((p : ℝ) / q)) ^ q = (a : ℝ) ^ p / (b : ℝ) ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hab.le, div_mul_cancel₀ _ hq', Real.rpow_natCast,
      div_pow]
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  rw [← pow_le_pow_iff_left₀ (by positivity) hy hq.ne', hyq, div_pow,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast hL

/-- `a^p S^q ≤ U^q b^p` gives `(a/b)^(p/q) ≤ U/S` (for `0 < a`, `0 < b`). -/
lemma rpow_rat_div_upper (a b p q U S : ℕ) (ha : 0 < a) (hb : 0 < b) (hq : 0 < q) (hS : 0 < S)
    (hU : a ^ p * S ^ q ≤ U ^ q * b ^ p) : ((a : ℝ) / b) ^ ((p : ℝ) / q) ≤ (U : ℝ) / S := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hab : (0 : ℝ) < (a : ℝ) / b := by positivity
  have hy : (0 : ℝ) ≤ ((a : ℝ) / b) ^ ((p : ℝ) / q) := Real.rpow_nonneg hab.le _
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have hyq : (((a : ℝ) / b) ^ ((p : ℝ) / q)) ^ q = (a : ℝ) ^ p / (b : ℝ) ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hab.le, div_mul_cancel₀ _ hq', Real.rpow_natCast,
      div_pow]
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  rw [← pow_le_pow_iff_left₀ hy (by positivity) hq.ne', hyq, div_pow,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast hU

/-- `L^q a^p ≤ b^p S^q` gives `L/S ≤ (a/b)^(-p/q)` (for `0 < a`, `0 < b`). -/
lemma rpow_rat_neg_div_lower (a b p q L S : ℕ) (ha : 0 < a) (hb : 0 < b) (hq : 0 < q) (hS : 0 < S)
    (hL : L ^ q * a ^ p ≤ b ^ p * S ^ q) : (L : ℝ) / S ≤ ((a : ℝ) / b) ^ (-((p : ℝ) / q)) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hab : (0 : ℝ) < (a : ℝ) / b := by positivity
  have hy : (0 : ℝ) ≤ ((a : ℝ) / b) ^ (-((p : ℝ) / q)) := Real.rpow_nonneg hab.le _
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have hyq : (((a : ℝ) / b) ^ (-((p : ℝ) / q))) ^ q = (b : ℝ) ^ p / (a : ℝ) ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hab.le, neg_mul, div_mul_cancel₀ _ hq',
      Real.rpow_neg hab.le, Real.rpow_natCast, div_pow, inv_div]
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  rw [← pow_le_pow_iff_left₀ (by positivity) hy hq.ne', hyq, div_pow,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast hL

/-- `b^p S^q ≤ U^q a^p` gives `(a/b)^(-p/q) ≤ U/S` (for `0 < a`, `0 < b`). -/
lemma rpow_rat_neg_div_upper (a b p q U S : ℕ) (ha : 0 < a) (hb : 0 < b) (hq : 0 < q) (hS : 0 < S)
    (hU : b ^ p * S ^ q ≤ U ^ q * a ^ p) : ((a : ℝ) / b) ^ (-((p : ℝ) / q)) ≤ (U : ℝ) / S := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hab : (0 : ℝ) < (a : ℝ) / b := by positivity
  have hy : (0 : ℝ) ≤ ((a : ℝ) / b) ^ (-((p : ℝ) / q)) := Real.rpow_nonneg hab.le _
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have hyq : (((a : ℝ) / b) ^ (-((p : ℝ) / q))) ^ q = (b : ℝ) ^ p / (a : ℝ) ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hab.le, neg_mul, div_mul_cancel₀ _ hq',
      Real.rpow_neg hab.le, Real.rpow_natCast, div_pow, inv_div]
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  rw [← pow_le_pow_iff_left₀ hy (by positivity) hq.ne', hyq, div_pow,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast hU

/-- A range sum over `C * K` terms as `C` blocks of `K`. -/
lemma sum_range_chunk {M : Type*} [AddCommMonoid M] (f : ℕ → M) (C K : ℕ) :
    ∑ i ∈ Finset.range (C * K), f i
      = ∑ c ∈ Finset.range C, ∑ n ∈ Finset.range K, f (K * c + n) := by
  induction C with
  | zero => simp
  | succ C ih =>
    rw [Finset.sum_range_succ, ← ih, show (C + 1) * K = C * K + K by ring, Finset.sum_range_add,
      mul_comm K C]

/-- Transport of a block of lower brackets to a block of a real range sum (negative exponent
`e = -p/q`).  `f` is the summand, `base` the block offset. -/
lemma sum_block_lo_neg (f : ℕ → ℝ) (e : ℝ) (p q S K base : ℕ) (hq : 0 < q) (hS : 0 < S)
    (he : e = -((p : ℝ) / q)) (hf : ∀ i, f i = ((i : ℝ) + 1) ^ e) (lo : List ℕ)
    (h : ∀ n < K, (lo.getD n 0) ^ q * (base + n + 1) ^ p ≤ S ^ q) :
    ((∑ n ∈ Finset.range K, lo.getD n 0 : ℕ) : ℝ) / S ≤ ∑ n ∈ Finset.range K, f (base + n) := by
  rw [Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_le_sum fun n hn => ?_
  have hn' : n < K := Finset.mem_range.mp hn
  have := rpow_neg_div_lower (base + n + 1) p q (lo.getD n 0) S (by omega) hq hS (h n hn')
  have hcast : ((base + n : ℕ) : ℝ) + 1 = ((base + n + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hf, he, hcast]
  exact this

/-- Transport of a block of upper brackets to a block of a real range sum (negative exponent
`e = -p/q`). -/
lemma sum_block_hi_neg (f : ℕ → ℝ) (e : ℝ) (p q S K base : ℕ) (hq : 0 < q) (hS : 0 < S)
    (he : e = -((p : ℝ) / q)) (hf : ∀ i, f i = ((i : ℝ) + 1) ^ e) (hi : List ℕ)
    (h : ∀ n < K, S ^ q ≤ (hi.getD n 0) ^ q * (base + n + 1) ^ p) :
    ∑ n ∈ Finset.range K, f (base + n) ≤ ((∑ n ∈ Finset.range K, hi.getD n 0 : ℕ) : ℝ) / S := by
  rw [Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_le_sum fun n hn => ?_
  have hn' : n < K := Finset.mem_range.mp hn
  have := rpow_neg_div_upper (base + n + 1) p q (hi.getD n 0) S (by omega) hq hS (h n hn')
  have hcast : ((base + n : ℕ) : ℝ) + 1 = ((base + n + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hf, he, hcast]
  exact this

end NatRootBracket
