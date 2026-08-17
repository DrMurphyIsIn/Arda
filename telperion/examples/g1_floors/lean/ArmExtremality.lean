/- HAND-AUTHORED (not telperion-generated): R1 single-hub arm-extremality -- the two scalar inequalities.

   Validated in exact Fraction arithmetic by  telperion/src/telperion/arm_lean_certificates.py
   (`ArmLeanCertificate.check()`); the Lean kernel re-proves each statement from scratch here.

   INEQUALITY 1  B(L,j') <= (3/2)^11 : base equality (L=0) + the integer descent tail
                 64(m+1)^11 <= 621 m^11 (m>=6), kernel-tight by an all-nonneg-coefficient Polya identity.
   INEQUALITY 2  the j=2 closure's final rational certificate  W*gamma^2 < 486/529  (W^3(50/27)^11 < 1).

   The g-lemma's multi-variable inductive step (max < gamma) is NOT formalized here -- it is a genuine
   optimization (grid-verified, not a Polya scalar), named as the residual in arm_lean_certificates.py.
   conjecture1_proved = False. -/
import Mathlib

namespace G1
namespace ArmExtremality

/-! ### Inequality 1 : `B(L,j') = W^L * ((3j'+L+3)/(2j'+2))^11 <= (3/2)^11` -/

/-- BASE (equality at `L = 0`): `B(0,j') = (3(j'+1)/(2(j'+1)))^11 = (3/2)^11` for every `j'`. -/
theorem B_base (j : ℕ) : (3 * ((j : ℚ) + 1)) / (2 * ((j : ℚ) + 1)) = 3 / 2 := by
  have h : ((j : ℚ) + 1) ≠ 0 := by positivity
  field_simp

/-- The all-nonnegative-coefficient Polya identity underlying the descent tail
    (`m = 6 + k`): `621*(6+k)^11 = 64*(7+k)^11 + P(k)` with `P` a nonneg-coefficient polynomial. -/
theorem tail_identity (k : ℕ) :
    621 * (6 + k) ^ 11 = 64 * (7 + k) ^ 11 +
      (557 * k ^ 11 + 36058 * k ^ 10 + 1057100 * k ^ 9 + 18510360 * k ^ 8
        + 214880160 * k ^ 7 + 1734000576 * k ^ 6 + 9907054080 * k ^ 5 + 39974056320 * k ^ 4
        + 111225554880 * k ^ 3 + 202159010240 * k ^ 2 + 214181872960 * k + 98748060224) := by
  ring

/-- The descent tail in `k`-form: `64*(7+k)^11 <= 621*(6+k)^11` for every `k : ℕ`
    (the remainder `P(k)` is a sum of naturals, hence nonneg). -/
theorem per_step_tail (k : ℕ) : 64 * (7 + k) ^ 11 ≤ 621 * (6 + k) ^ 11 := by
  rw [tail_identity]; exact Nat.le_add_right _ _

/-- The descent per-step inequality at every integer `m >= 6`:  `64*(m+1)^11 <= 621*m^11`.
    (Tightest at `m = 6`; already true at `m = 5`; FALSE at `m = 4` -- so `m >= 6` is not slack.) -/
theorem per_step (m : ℕ) (hm : 6 ≤ m) : 64 * (m + 1) ^ 11 ≤ 621 * m ^ 11 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have h : 6 + k + 1 = 7 + k := by omega
  rw [h]; exact per_step_tail k

/-! ### Inequality 2 : the j=2 closure's final rational certificate -/

/-- The exact rational certificate `W^3 * (50/27)^11 < 1`  (`W = 64/621`).  Equivalent to
    `W * gamma^2 = W^5 (5/3)^22 < 486/529` with `gamma = W^2 (5/3)^11`, i.e. the j=2 bound
    `Phi^11(B) <= W*gamma^2 < 486/529 = F_arm`. -/
theorem gstep_final_certificate : ((64 : ℚ) / 621) ^ 3 * (50 / 27) ^ 11 < 1 := by norm_num

/-- The j=2 closure spelled out: `W * (W^2 (5/3)^11)^2 < 486/529`. -/
theorem j2_closure :
    ((64 : ℚ) / 621) * (((64 : ℚ) / 621) ^ 2 * (5 / 3) ^ 11) ^ 2 < 486 / 529 := by
  norm_num

/-- Cross-multiplied integer form of the certificate: `64^3 * 50^11 < 621^3 * 27^11`. -/
theorem gstep_final_integer : (64 : ℕ) ^ 3 * 50 ^ 11 < 621 ^ 3 * 27 ^ 11 := by
  norm_num

/-! ### The branching (j' >= 2) g-step, reduced to two rational leaves

  The g-lemma's inductive step, in the all-non-leaf branching case, is a multi-variable optimization
  `max < gamma` (gamma = W^2 (5/3)^11).  Reduced (symmetric-argmax -> per-j' max at the crossover mu* ->
  boost < 4/3) to the two exact rational facts below; together they give `f_{j'>=2}(mu*) = W*boost^11 <
  W*(4/3)^11 < gamma`.  The majorization/monotonicity reduction itself is not yet formalized (see
  telperion/src/telperion/gstep_reduction.py). -/

/-- (I) `mu* < 1/3`, i.e. `gamma = W^2 (5/3)^11 < (10/9)^11`  -- so `3*mu* < 1` and the symmetric-max
    boost `1 + (3 j' mu* + 1)/(3j'+3) < 1 + (j'+1)/(3j'+3) = 4/3`. -/
theorem gamma_lt_ten_ninths_11 : ((64 : ℚ) / 621) ^ 2 * (5 / 3) ^ 11 < (10 / 9) ^ 11 := by
  norm_num

/-- (II) `W*(4/3)^11 < gamma`  -- so `f_{j'>=2}(mu*) = W*boost^11 < W*(4/3)^11 < gamma`. -/
theorem W_four_thirds_11_lt_gamma :
    ((64 : ℚ) / 621) * (4 / 3) ^ 11 < ((64 : ℚ) / 621) ^ 2 * (5 / 3) ^ 11 := by
  norm_num

/-- Cross-multiplied integer forms of the two leaves. -/
theorem gstep_leaf_I_integer : (64 : ℕ) ^ 2 * 5 ^ 11 * 9 ^ 11 < 621 ^ 2 * 3 ^ 11 * 10 ^ 11 := by
  norm_num

theorem gstep_leaf_II_integer : (621 : ℕ) * 4 ^ 11 < 64 * 5 ^ 11 := by
  norm_num

/-! ### Coordinate-wise unimodality (replaces majorization -- g_bound is Schur-CONVEX, so Schur fails).

  The global max of the branching g-step is at the symmetric crossover mu* by coordinate-wise unimodality:
  increasing below mu* (T1), and the descent condition below (T2) above mu*.  These two rational lemmas are
  the arithmetic engine; the over-the-reals T1/T2 at the irrational mu* and the Branch wiring remain. -/

/-- **T2 descent engine.**  For `j ≥ 2` and `μ ≤ S`, the coordinate-descent condition holds:
    `3 + μ ≤ (j+1) · boost`, where `boost = 1 + (3S+1)/(3j+3)`.  (Exactly `(j+1)·boost = (j+1) + (3S+1)/3
    ≥ j + 4/3 + μ ≥ 3 + μ` since `j ≥ 2`.)  This forces `g_bound` to decrease toward `μ*` above it. -/
theorem descent_engine (j : ℕ) (hj : 2 ≤ j) (S mu : ℚ) (hmu : mu ≤ S) :
    3 + mu ≤ ((j : ℚ) + 1) * (1 + (3 * S + 1) / (3 * (j : ℚ) + 3)) := by
  have hjq : (2 : ℚ) ≤ (j : ℚ) := by exact_mod_cast hj
  have hden : (0 : ℚ) < 3 * (j : ℚ) + 3 := by positivity
  have key : ((j : ℚ) + 1) * (1 + (3 * S + 1) / (3 * (j : ℚ) + 3))
      = ((j : ℚ) + 1) + (3 * S + 1) / 3 := by
    field_simp
  rw [key]
  have hfrac : (3 * mu + 1) / 3 ≤ (3 * S + 1) / 3 := by gcongr
  have hexp : ((j : ℚ) + 1) + (3 * mu + 1) / 3 = (j : ℚ) + mu + 4 / 3 := by ring
  linarith [hfrac, hexp, hjq]

/-- **Boost bound.**  If `3S ≤ j` (all child messages `≤ 1/3`), then `boost = 1 + (3S+1)/(3j+3) ≤ 4/3`.
    At the crossover this gives `boost(μ*) < 4/3` (via `3μ* < 1`, leaf I), hence `W·boost(μ*)^11 < W·(4/3)^11
    < γ`. -/
theorem boost_le_four_thirds (j : ℕ) (S : ℚ) (hS : 3 * S ≤ (j : ℚ)) :
    1 + (3 * S + 1) / (3 * (j : ℚ) + 3) ≤ 4 / 3 := by
  have hden : (0 : ℚ) < 3 * (j : ℚ) + 3 := by positivity
  have h : (3 * S + 1) / (3 * (j : ℚ) + 3) ≤ 1 / 3 := by
    rw [div_le_iff₀ hden]; linarith
  linarith

end ArmExtremality
end G1
