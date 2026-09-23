/-
  Crux_meta_barriers (li_positivity island) -- THE GOLDEN-FAKE BARRIER: BUILT, CORRECTED, BOUNDED.

  conjecture1_proved = False.  Nothing in this file says anything about where the zeros of the
  Riemann zeta function lie.  It is a meta-result: it bounds what one class of arguments can do.

  WHAT IT PROVES.  Every theorem below prints `[propext, Classical.choice, Quot.sound]` under
  `#print axioms` (the list is at the end of the file).  There is no `sorry`, no `admit`, no
  `native_decide`, no new axiom declaration and no opaque constant.

  1. Genus-one formal data (sections 1-3).  For every q >= 2 the formal Euler-product clauses
     (positive residue, a nonnegative number of degree-two places, nonnegative von Mangoldt weights
     at every degree) hold EXACTLY for |m| <= q (`admissible_iff`; the positivity half for every q
     is `N_pos_of_abs_le`, via the Lucas identity), while RH for the datum is m^2 <= 4q
     (`rh_int_iff_zeros`, `rh_iff`).  The square-root gap opens exactly at q = 5
     (`exists_admissible_not_rh_iff`).  Hasse/Rosati positivity of the degree form is equivalent to
     RH (`hasse_iff`; at this level that is a relabeling), and N_n = det(A^n - 1) (`N_eq_det`).
  2. The anti-golden fake (section 4).  XiA s = 2 cosh((s - 1/2) log 5) + sqrt 5 has EXACTLY the
     zeros 1/2 +- x0 + i (2k+1) pi / log 5 with x0 = log phi / log 5 (`XiA_eq_zero_iff`).  All of
     them are simple (`XiA_zero_simple`), inside the strip, and off the line.
  3. The golden hybrid XiH = xi * XiA (sections 5-7).  It is entire, symmetric, and real on the real
     axis, and its zero set is the nontrivial zeros of zeta together with the fake zeros
     (`XiH_eq_zero_iff`).  It satisfies the corpus's POINTWISE layer exactly as zeta does: Box 1 and
     Box 2 (LowHeightBox), the strip, no real zeros, the effective de la Vallee Poussin region
     (DlvpZetaZeroFree), and the Li disk condition (`hybrid_pointwiseLayer`,
     `zeta_pointwiseLayer`).  Hence `pointwise_layer_does_not_imply_rh`.  Its Li rungs 0..4 are
     nonnegative (`hybrid_li_rungs`): the fake paired sums converge and are termwise nonnegative,
     by LiBoxRungs's disk polynomials.
  4. The Euler side (sections 8 and 10).  CORRECTION: the proposal's literal hybrid
     zeta(s) Z_{5,-5}(5^{-s}) has a DOUBLE pole at s = 1 (`Hlit_double_pole`,
     `Hlit_not_simple_pole`), so it is not in the proposed class.  The repair
     H4 = zeta(s) (1 + 5*5^{-s} + 5*5^{-2s}) / (1 - 4*5^{-s}) does better on several counts:
       - it has the same completion (`XiH_eq_completion_H4`);
       - it has positive von Mangoldt weights at 5 for every n (`w4_pos`);
       - it has a SIMPLE pole at 1 with residue 11 (`H4_simple_pole`).
     It pays with a pole at the real point log 4 / log 5, which lies in (1/2, 1)
     (`H4_pole_in_strip`).  A completion factor that vanishes there absorbs it
     (`gammaH4_zero_in_strip`).  Ramanujan fails at 5 (`w4_even_ge`).
  5. LIMITS (section 9).
     - POLE SHADOW (`pole_shadow`: genus one, any finite denominator).  If every pole of a local
       factor lies strictly to the left of its off-line zero, some von Mangoldt weight is negative.
       So positivity, together with "no pole of the local factor in Re s > 1/2", forces local RH
       (`local_rh_of_positivity`).
     - LATTICE.  Every zero of a polynomial local factor at p recurs with period 2 pi i / log p
       (`local_factor_periodic`), so it has a copy below height pi / log 2 < 4.54
       (`local_zero_low_copy`).  Every RH-violating genus-one datum has an off-line zero in the
       strip at height <= pi / log q (`genus_one_low_offline_zero`).  The golden hybrid has one
       inside the corpus's certified zero-free box [0.001, 0.999] x [0, 55/16]
       (`hybrid_zero_in_certified_box`).
  The single statement `golden_fake_barrier` (section 11) packages items 3-5.

  WHAT IT DOES NOT PROVE.
  * Anything about zeta.  `pointwise_layer_does_not_imply_rh` is a relativization.  It refutes the
    universal statement "every zero set with these properties lies on the line".
    wall_adversary/BarrierScopeXR.lean proved, for the FE-only bundle, that such a refutation is
    silent about each single member, and the same holds here.  What this file adds is the list of
    properties that separate zeta from the hybrid, with every separation proved as a theorem.
  * That `hybridLi n` is the Li coefficient of XiH.  That identification rests on additivity of
    log-derivatives and on the fake's symmetric Hadamard product, and it is paper-level.  The
    numerics (telperion/research/crux_meta-barriers, checks N5-N6) confirm it.  The Gaussian layer
    lives on the rvm_bridge island, in its own Crux/Crux_meta_barriers.lean.
  * That the barrier survives richer axioms.  The proposal's class allows an arbitrary completion
    factor, and that freedom is what admits the hybrid: the repaired model's factor vanishes inside
    the strip.  With the exact Gamma_R completion, the sibling build Crux_axiso_theorem.lean shows
    the positive class collapses to {zeta} (modulo KP99).
  * That finite certificates are compatible with an off-line zero.  The barrier survives neither
    finite certification (every lattice fake has an off-line zero below height 4.54) nor the pole
    axiom (by the pole shadow), so it is NOT evidence for that claim.  For lattice models the
    opposite is a theorem here.  A barrier that survived both would need a non-lattice (global)
    Euler product, and whether one exists is open.
-/

import Mathlib
import LowHeightBox
import LiBoxRungs
import DlvpZetaZeroFree
import Lc.XiZeros
import Lc.LiCriterion.Fidelity

open Complex

namespace CruxMetaBarriers

/-! ## 1. Genus-one formal zeta data and the exact square-root gap

A genus-one formal datum over "a field with `q` elements" is
`Z(T) = (1 - m T + q T^2) / ((1 - T)(1 - q T))`.  Its Lefschetz numbers (point counts over the
degree-`n` extension, equivalently the von Mangoldt weights at `q^n` in units of `log q`) are
`N n = q^n + 1 - t n`, where `t n` is the `n`-th power sum of the roots of `x^2 - m x + q`.
The Riemann hypothesis for the datum is `m^2 <= 4 q`. -/

/-- Power sums `t n = alpha^n + beta^n` of the roots of `x^2 - m x + q`, by recurrence. -/
def tr (q m : ℤ) : ℕ → ℤ
  | 0 => 2
  | 1 => m
  | (n + 2) => m * tr q m (n + 1) - q * tr q m n

/-- Lefschetz numbers `N n = q^n + 1 - t n`. -/
def N (q m : ℤ) (n : ℕ) : ℤ := q ^ n + 1 - tr q m n

@[simp] lemma tr_zero (q m : ℤ) : tr q m 0 = 2 := rfl
@[simp] lemma tr_one (q m : ℤ) : tr q m 1 = m := rfl
lemma tr_succ_succ (q m : ℤ) (n : ℕ) :
    tr q m (n + 2) = m * tr q m (n + 1) - q * tr q m n := rfl

/-- Negating the trace negates the roots: `t_(-m) n = (-1)^n t_m n`. -/
lemma tr_neg (q m : ℤ) : ∀ n : ℕ, tr q (-m) n = (-1) ^ n * tr q m n
  | 0 => by simp
  | 1 => by simp
  | (n + 2) => by
      rw [tr_succ_succ, tr_succ_succ, tr_neg q m (n + 1), tr_neg q m n]
      ring

/-- Lucas `U`-sequence of `x^2 - m x + q`. -/
def lu (q m : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (n + 2) => m * lu q m (n + 1) - q * lu q m n

lemma lu_succ_succ (q m : ℤ) (n : ℕ) :
    lu q m (n + 2) = m * lu q m (n + 1) - q * lu q m n := rfl

/-- Cassini-type norm identity `U(n+1)^2 - m U(n+1) U(n) + q U(n)^2 = q^n`. -/
lemma lu_norm (q m : ℤ) : ∀ n : ℕ,
    lu q m (n + 1) ^ 2 - m * lu q m (n + 1) * lu q m n + q * lu q m n ^ 2 = q ^ n
  | 0 => by simp [lu]
  | (n + 1) => by
      have ih := lu_norm q m n
      rw [lu_succ_succ, pow_succ]
      linear_combination q * ih

lemma tr_eq_lu (q m : ℤ) : ∀ n : ℕ, tr q m n = 2 * lu q m (n + 1) - m * lu q m n
  | 0 => by simp [tr, lu]
  | 1 => by simp [tr, lu]; ring
  | (n + 2) => by
      rw [tr_succ_succ, tr_eq_lu q m (n + 1), tr_eq_lu q m n]
      have e1 : lu q m (n + 2 + 1) = m * lu q m (n + 2) - q * lu q m (n + 1) := rfl
      have e2 : lu q m (n + 2) = m * lu q m (n + 1) - q * lu q m n := rfl
      rw [e1, e2]
      ring

/-- **The Lucas identity** `t_n^2 - (m^2 - 4q) U_n^2 = 4 q^n`. -/
theorem lucas_identity (q m : ℤ) (n : ℕ) :
    tr q m n ^ 2 - (m ^ 2 - 4 * q) * lu q m n ^ 2 = 4 * q ^ n := by
  rw [tr_eq_lu, ← lu_norm q m n]
  ring

/-- Complex-root case: `m^2 <= 4 q` gives `N (n+1) >= 1`. -/
lemma N_pos_of_disc_nonpos (q m : ℤ) (hq : 2 ≤ q) (hD : m ^ 2 ≤ 4 * q) (n : ℕ) :
    1 ≤ N q m (n + 1) := by
  have hL := lucas_identity q m (n + 1)
  have hU : 0 ≤ (4 * q - m ^ 2) * lu q m (n + 1) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have hV : tr q m (n + 1) ^ 2 ≤ 4 * q ^ (n + 1) := by nlinarith
  have hqn : 2 ≤ q ^ (n + 1) := by
    calc (2 : ℤ) ≤ q := hq
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ (n + 1) := pow_le_pow_right₀ (by linarith) (by omega)
  unfold N
  by_contra hcon
  have h1 : q ^ (n + 1) + 1 ≤ tr q m (n + 1) := by linarith [not_le.mp hcon]
  have h2 : (q ^ (n + 1) + 1) ^ 2 ≤ tr q m (n + 1) ^ 2 := by
    have h0 : 0 ≤ q ^ (n + 1) + 1 := by linarith
    nlinarith
  nlinarith

/-- Real representation of the power sums through two real numbers with the right sum and
product. -/
lemma tr_real_rep (q m : ℤ) (α β : ℝ) (hs : α + β = m) (hp : α * β = q) :
    ∀ n : ℕ, (tr q m n : ℝ) = α ^ n + β ^ n ∧ (tr q m (n + 1) : ℝ) = α ^ (n + 1) + β ^ (n + 1)
  | 0 => by
      refine ⟨by simp [tr]; norm_num, ?_⟩
      simp [tr, hs]
  | (n + 1) => by
      obtain ⟨h0, h1⟩ := tr_real_rep q m α β hs hp n
      refine ⟨h1, ?_⟩
      rw [show n + 1 + 1 = n + 2 from rfl, tr_succ_succ]
      push_cast
      rw [h0, h1, ← hs, ← hp]
      ring

/-- The two real roots `(m +- sqrt(m^2 - 4q))/2` in the real-root case. -/
lemma real_roots (q m : ℤ) (hD : 4 * q < m ^ 2) :
    ∃ α β : ℝ, α + β = m ∧ α * β = q ∧
      α = ((m : ℝ) + Real.sqrt ((m : ℝ) ^ 2 - 4 * q)) / 2 ∧
      β = ((m : ℝ) - Real.sqrt ((m : ℝ) ^ 2 - 4 * q)) / 2 := by
  have hDR : 4 * (q : ℝ) < (m : ℝ) ^ 2 := by exact_mod_cast hD
  have hr2 : Real.sqrt ((m : ℝ) ^ 2 - 4 * q) ^ 2 = (m : ℝ) ^ 2 - 4 * q :=
    Real.sq_sqrt (by linarith)
  refine ⟨_, _, ?_, ?_, rfl, rfl⟩
  · ring
  · have : ((m : ℝ) + Real.sqrt ((m : ℝ) ^ 2 - 4 * q)) / 2
        * (((m : ℝ) - Real.sqrt ((m : ℝ) ^ 2 - 4 * q)) / 2)
        = ((m : ℝ) ^ 2 - Real.sqrt ((m : ℝ) ^ 2 - 4 * q) ^ 2) / 4 := by ring
    rw [this, hr2]; ring

/-- Real-root case with positive trace: both roots exceed `1` when `m <= q`. -/
lemma N_pos_real_pos (q m : ℤ) (hq : 2 ≤ q) (hm : m ≤ q) (hD : 4 * q < m ^ 2) (hm0 : 0 < m)
    (n : ℕ) : 1 ≤ N q m (n + 1) ∧ 0 < tr q m (n + 1) := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hmR : (m : ℝ) ≤ q := by exact_mod_cast hm
  have hDR : 4 * (q : ℝ) < (m : ℝ) ^ 2 := by exact_mod_cast hD
  have hm0R : (0 : ℝ) < m := by exact_mod_cast hm0
  have hm2 : (2 : ℝ) < m := by nlinarith
  obtain ⟨α, β, hs, hp, hα, hβ⟩ := real_roots q m hD
  set r : ℝ := Real.sqrt ((m : ℝ) ^ 2 - 4 * q) with hrdef
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrlt : r < m - 2 := by
    rw [hrdef, Real.sqrt_lt' (by linarith)]
    nlinarith
  have hβ1 : 1 < β := by rw [hβ]; linarith
  have hαβ : β ≤ α := by rw [hα, hβ]; linarith
  have hα1 : 1 < α := lt_of_lt_of_le hβ1 hαβ
  obtain ⟨_, htr⟩ := tr_real_rep q m α β hs hp n
  have hN : (N q m (n + 1) : ℝ) = (α ^ (n + 1) - 1) * (β ^ (n + 1) - 1) := by
    unfold N
    push_cast
    rw [htr, ← hp, mul_pow]
    ring
  have hαn : 1 < α ^ (n + 1) := one_lt_pow₀ hα1 (by omega)
  have hβn : 1 < β ^ (n + 1) := one_lt_pow₀ hβ1 (by omega)
  have hpos : (0 : ℝ) < N q m (n + 1) := by
    rw [hN]; exact mul_pos (by linarith) (by linarith)
  have htrpos : (0 : ℝ) < tr q m (n + 1) := by rw [htr]; linarith
  constructor
  · have : (0 : ℤ) < N q m (n + 1) := by exact_mod_cast hpos
    omega
  · exact_mod_cast htrpos

/-- **Euler positivity on the whole trivial range, every `q`.**  For `2 <= q` and `|m| <= q`,
every Lefschetz number is `>= 1`: the von Mangoldt weights of `Z_{q,m}` are positive.
(Complex roots: the Lucas identity.  Real roots: both roots have modulus `> 1`.) -/
theorem N_pos_of_abs_le (q m : ℤ) (hq : 2 ≤ q) (hm1 : -q ≤ m) (hm2 : m ≤ q) (n : ℕ) :
    1 ≤ N q m (n + 1) := by
  rcases le_or_gt (m ^ 2) (4 * q) with hD | hD
  · exact N_pos_of_disc_nonpos q m hq hD n
  · rcases le_or_gt m 0 with hm0 | hm0
    · have hmneg : 0 < -m := by
        rcases lt_or_eq_of_le hm0 with h | h
        · linarith
        · rw [h] at hD; linarith
      have hD' : 4 * q < (-m) ^ 2 := by rw [neg_sq]; exact hD
      obtain ⟨hN', htr'⟩ := N_pos_real_pos q (-m) hq (by linarith) hD' hmneg n
      have hrel : tr q m (n + 1) = (-1) ^ (n + 1) * tr q (-m) (n + 1) := by
        have := tr_neg q (-m) (n + 1)
        rw [neg_neg] at this
        exact this
      unfold N at hN' ⊢
      rw [hrel]
      rcases neg_one_pow_eq_or ℤ (n + 1) with h | h <;> rw [h] <;> nlinarith
    · exact (N_pos_real_pos q m hq hm2 hD hm0 n).1

@[simp] lemma N_one (q m : ℤ) : N q m 1 = q + 1 - m := by simp [N]
@[simp] lemma N_two (q m : ℤ) : N q m 2 = q ^ 2 + 1 - (m ^ 2 - 2 * q) := by
  simp [N, tr_succ_succ]; ring

/-- Twice the number of degree-two places: `2 a_2 = N_2 - N_1`. -/
def twoA2 (q m : ℤ) : ℤ := N q m 2 - N q m 1

/-- **Trivial bound.**  A pole with positive residue (`N_1 > 0`) and a nonnegative number of
degree-two places force `-q <= m <= q`. -/
theorem trivial_bound (q m : ℤ) (hq : 0 ≤ q) (hpole : 0 < N q m 1) (ha2 : 0 ≤ twoA2 q m) :
    -q ≤ m ∧ m ≤ q := by
  simp only [twoA2, N_one, N_two] at hpole ha2
  constructor
  · by_contra h
    rw [not_le] at h
    have h' : m ≤ -q - 1 := by omega
    nlinarith
  · omega

/-- The formal Euler-product axioms for a genus-one datum: positive residue, a nonnegative number
of degree-two places, and nonnegative von Mangoldt weights at every degree. -/
def Admissible (q m : ℤ) : Prop :=
  0 < N q m 1 ∧ 0 ≤ twoA2 q m ∧ ∀ n : ℕ, 0 ≤ N q m (n + 1)

/-- **The exact admissible range is the trivial range.**  For `q >= 2`, the formal axioms hold
iff `|m| <= q`, while RH for the datum is `m^2 <= 4q`. -/
theorem admissible_iff (q m : ℤ) (hq : 2 ≤ q) : Admissible q m ↔ -q ≤ m ∧ m ≤ q := by
  constructor
  · rintro ⟨h1, h2, _⟩
    exact trivial_bound q m (by linarith) h1 h2
  · rintro ⟨hm1, hm2⟩
    refine ⟨by simp; linarith, ?_, fun n => le_trans (by norm_num) (N_pos_of_abs_le q m hq hm1 hm2 n)⟩
    simp only [twoA2, N_one, N_two]
    nlinarith

/-- **The square-root gap opens exactly at `q = 5`.**  For `q >= 2` there is an admissible datum
violating RH iff `q >= 5`. -/
theorem exists_admissible_not_rh_iff (q : ℤ) (hq : 2 ≤ q) :
    (∃ m : ℤ, Admissible q m ∧ 4 * q < m ^ 2) ↔ 5 ≤ q := by
  constructor
  · rintro ⟨m, hadm, hlt⟩
    obtain ⟨h1, h2⟩ := (admissible_iff q m hq).1 hadm
    by_contra h5
    have hq4 : q ≤ 4 := by omega
    nlinarith
  · intro h5
    refine ⟨q, (admissible_iff q q hq).2 ⟨by linarith, le_rfl⟩, by nlinarith⟩

/-- For `q <= 4` the trivial bound already is the square-root bound. -/
theorem rh_of_trivial_small_q (q m : ℤ) (hq0 : 0 ≤ q) (hq : q ≤ 4) (h1 : -q ≤ m) (h2 : m ≤ q) :
    m ^ 2 ≤ 4 * q := by
  nlinarith

/-- The golden fake `(5, 5)`: every Lefschetz number is `>= 1`. -/
theorem N_golden_pos (n : ℕ) : 1 ≤ N 5 5 (n + 1) :=
  N_pos_of_abs_le 5 5 (by norm_num) (by norm_num) (by norm_num) n

/-- The anti-golden fake `(5, -5)`: every Lefschetz number is `>= 1`. -/
theorem N_anti_pos (n : ℕ) : 1 ≤ N 5 (-5) (n + 1) :=
  N_pos_of_abs_le 5 (-5) (by norm_num) (by norm_num) (by norm_num) n

/-- Both golden data violate RH: `25 > 20`. -/
theorem golden_violates_rh : ¬ ((5 : ℤ) ^ 2 ≤ 4 * 5) ∧ ¬ ((-5 : ℤ) ^ 2 ≤ 4 * 5) := by
  constructor <;> norm_num

/-! Place counts `a_d` (periodic orbits of exact period `d`) of the two golden data, degrees
`1..10`: `N_n = sum_{d | n} d a_d` with every `a_d` a nonnegative integer. -/

lemma euler_golden_1 : N 5 5 1 = 1 * 1 := by decide
lemma euler_golden_2 : N 5 5 2 = 1 * 1 + 2 * 5 := by decide
lemma euler_golden_3 : N 5 5 3 = 1 * 1 + 3 * 25 := by decide
lemma euler_golden_4 : N 5 5 4 = 1 * 1 + 2 * 5 + 4 * 110 := by decide
lemma euler_golden_5 : N 5 5 5 = 1 * 1 + 5 * 500 := by decide
lemma euler_golden_6 : N 5 5 6 = 1 * 1 + 2 * 5 + 3 * 25 + 6 * 2215 := by decide
lemma euler_golden_7 : N 5 5 7 = 1 * 1 + 7 * 10000 := by decide
lemma euler_golden_8 : N 5 5 8 = 1 * 1 + 2 * 5 + 4 * 110 + 8 * 45100 := by decide
lemma euler_golden_9 : N 5 5 9 = 1 * 1 + 3 * 25 + 9 * 205200 := by decide
lemma euler_golden_10 : N 5 5 10 = 1 * 1 + 2 * 5 + 5 * 500 + 10 * 937874 := by decide
lemma euler_anti_1 : N 5 (-5) 1 = 1 * 11 := by decide
lemma euler_anti_2 : N 5 (-5) 2 = 1 * 11 + 2 * 0 := by decide
lemma euler_anti_3 : N 5 (-5) 3 = 1 * 11 + 3 * 55 := by decide
lemma euler_anti_4 : N 5 (-5) 4 = 1 * 11 + 2 * 0 + 4 * 110 := by decide
lemma euler_anti_5 : N 5 (-5) 5 = 1 * 11 + 5 * 748 := by decide
lemma euler_anti_6 : N 5 (-5) 6 = 1 * 11 + 2 * 0 + 3 * 55 + 6 * 2200 := by decide
lemma euler_anti_7 : N 5 (-5) 7 = 1 * 11 + 7 * 12320 := by decide
lemma euler_anti_8 : N 5 (-5) 8 = 1 * 11 + 2 * 0 + 4 * 110 + 8 * 45100 := by decide
lemma euler_anti_9 : N 5 (-5) 9 = 1 * 11 + 3 * 55 + 9 * 228800 := by decide
lemma euler_anti_10 : N 5 (-5) 10 = 1 * 11 + 2 * 0 + 5 * 748 + 10 * 937750 := by decide

/-! ## 2. The completed genus-one function; RH for a datum is the Hasse bound -/

/-- The completed function of a genus-one datum, `Xi s = 2 cosh((s - 1/2) L) - c`
(`L = log q`, `c = m / sqrt q`). -/
noncomputable def Xi (L c : ℝ) (s : ℂ) : ℂ := 2 * Complex.cosh ((s - 1 / 2) * L) - c

/-- Functional equation `Xi (1 - s) = Xi s`. -/
theorem Xi_symm (L c : ℝ) (s : ℂ) : Xi L c (1 - s) = Xi L c s := by
  unfold Xi
  have : ((1 - s) - 1 / 2) * (L : ℂ) = -((s - 1 / 2) * L) := by ring
  rw [this, Complex.cosh_neg]

/-- `Xi` is `q^(s-1/2) P(q^(-s))`, `P T = 1 - m T + q T^2`, written with `q = exp L`. -/
theorem Xi_eq_P (L m : ℝ) (s : ℂ) :
    Complex.exp ((s - 1 / 2) * L) *
        (1 - m * Complex.exp (-s * L) + Complex.exp L * Complex.exp (-s * L) ^ 2)
      = Xi L (m * Real.exp (-L / 2)) s := by
  unfold Xi
  rw [Complex.cosh]
  have e1 : Complex.exp ((s - 1 / 2) * L) * Complex.exp (-s * L)
      = Complex.exp (-(L : ℂ) / 2) := by rw [← Complex.exp_add]; congr 1; ring
  have e2 : Complex.exp ((s - 1 / 2) * L) * (Complex.exp L * Complex.exp (-s * L) ^ 2)
      = Complex.exp (-((s - 1 / 2) * L)) := by
    rw [sq, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  push_cast
  linear_combination (-(m : ℂ)) * e1 + e2

lemma cosh_decomp (x y : ℝ) :
    Complex.cosh ((x : ℂ) + y * I) =
      (Real.cosh x * Real.cos y : ℝ) + (Real.sinh x * Real.sin y : ℝ) * I := by
  rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sinh, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast; ring

/-- **Hasse bound implies RH.**  If `|c| <= 2` every zero of `Xi` is on `Re s = 1/2`. -/
theorem rh_of_le_two (L c : ℝ) (hL : L ≠ 0) (hc : |c| ≤ 2) :
    ∀ s : ℂ, Xi L c s = 0 → s.re = 1 / 2 := by
  intro s hs
  set x : ℝ := (s.re - 1 / 2) * L with hx
  set y : ℝ := s.im * L with hy
  have hw : (s - 1 / 2) * (L : ℂ) = (x : ℂ) + y * I := by
    apply Complex.ext <;> simp [hx, hy]
  unfold Xi at hs
  rw [hw, cosh_decomp] at hs
  generalize hA : Real.cosh x * Real.cos y = A at hs
  generalize hB : Real.sinh x * Real.sin y = B at hs
  have hre : 2 * A - c = 0 := by
    have := congrArg Complex.re hs
    simpa using this
  have him : 2 * B = 0 := by
    have := congrArg Complex.im hs
    simpa using this
  by_contra hne
  have hx0 : x ≠ 0 := by
    intro h0
    apply hne
    have : (s.re - 1 / 2) * L = 0 := by rw [← hx]; exact h0
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hL
  have hsinh : Real.sinh x ≠ 0 := by
    rw [Ne, Real.sinh_eq_zero]; exact hx0
  have hsin : Real.sin y = 0 := by
    have : Real.sinh x * Real.sin y = 0 := by rw [hB]; linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hsinh
    · exact h
  have hcos : Real.cos y ^ 2 = 1 := by
    have := Real.sin_sq_add_cos_sq y
    rw [hsin] at this; linarith
  have hcosh : 1 < Real.cosh x := Real.one_lt_cosh.mpr hx0
  have habs : |2 * (Real.cosh x * Real.cos y)| = 2 * Real.cosh x := by
    have hc1 : |Real.cos y| = 1 := by
      have := sq_abs (Real.cos y)
      nlinarith [abs_nonneg (Real.cos y)]
    rw [abs_mul, abs_mul, hc1, abs_of_pos (by norm_num : (0:ℝ) < 2),
      abs_of_pos (by linarith : (0:ℝ) < Real.cosh x)]
    ring
  have hceq : 2 * (Real.cosh x * Real.cos y) = c := by rw [hA]; linarith
  rw [hceq] at habs
  linarith

lemma re_half_add (t : ℝ) : ((1 : ℂ) / 2 + (t : ℂ)).re = 1 / 2 + t := by simp

/-- For `|c| > 2`, some `x > 0` has `cosh x = |c|/2`. -/
lemma cosh_log_root (c : ℝ) (hc : 2 < |c|) :
    ∃ x : ℝ, 0 < x ∧ Real.cosh x = |c| / 2 := by
  set d : ℝ := Real.sqrt (c ^ 2 / 4 - 1) with hd
  have hc2 : c ^ 2 = |c| ^ 2 := (sq_abs c).symm
  have hpos : 0 ≤ c ^ 2 / 4 - 1 := by nlinarith [abs_nonneg c]
  have hdd : d * d = c ^ 2 / 4 - 1 := Real.mul_self_sqrt hpos
  have hd0 : 0 ≤ d := Real.sqrt_nonneg _
  set a : ℝ := |c| / 2 + d with ha
  have ha1 : 1 < a := by linarith
  have ha0 : 0 < a := by linarith
  have hinv : a⁻¹ = |c| / 2 - d := by
    have hne : a ≠ 0 := ne_of_gt ha0
    field_simp
    nlinarith [hdd, hc2]
  refine ⟨Real.log a, Real.log_pos ha1, ?_⟩
  rw [Real.cosh_log ha0, hinv, ha]
  ring

/-- **Beyond the Hasse bound there is an explicit off-line zero**: real if `c > 2`, on the
horizontal line `Im s = pi / L` if `c < -2`.  The displacement `x` satisfies `cosh x = |c|/2`. -/
theorem offline_zero_explicit (L c : ℝ) (hL : 0 < L) (hc : 2 < |c|) :
    ∃ x : ℝ, 0 < x ∧ Real.cosh x = |c| / 2 ∧
      ∃ s : ℂ, Xi L c s = 0 ∧ s.re = 1 / 2 + x / L ∧ (s.im = 0 ∨ s.im = Real.pi / L) := by
  obtain ⟨x, hx0, hcx⟩ := cosh_log_root c hc
  refine ⟨x, hx0, hcx, ?_⟩
  have hLne : (L : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hL)
  rcases le_or_gt 0 c with hcpos | hcneg
  · refine ⟨1 / 2 + (x / L : ℝ), ?_, ?_, Or.inl (by simp)⟩
    · unfold Xi
      have hw : ((1 / 2 + ((x / L : ℝ) : ℂ)) - 1 / 2) * (L : ℂ) = (x : ℂ) := by
        push_cast; field_simp; ring
      rw [hw, ← Complex.ofReal_cosh, hcx, abs_of_nonneg hcpos]
      push_cast; ring
    · exact re_half_add _
  · refine ⟨1 / 2 + (x / L : ℝ) + (Real.pi / L : ℝ) * I, ?_, ?_, Or.inr ?_⟩
    · unfold Xi
      have hw : ((1 / 2 + ((x / L : ℝ) : ℂ) + ((Real.pi / L : ℝ) : ℂ) * I) - 1 / 2) * (L : ℂ)
          = (x : ℂ) + (Real.pi : ℝ) * I := by
        push_cast; field_simp; ring
      rw [hw, cosh_decomp, Real.cos_pi, Real.sin_pi, hcx, abs_of_neg hcneg]
      push_cast; ring
    · simp
    · simp

/-- **Beyond the Hasse bound there is an off-line zero.** -/
theorem offline_zero (L c : ℝ) (hL : 0 < L) (hc : 2 < |c|) :
    ∃ s : ℂ, Xi L c s = 0 ∧ s.re ≠ 1 / 2 := by
  obtain ⟨x, hx0, _, s, hs, hre, _⟩ := offline_zero_explicit L c hL hc
  refine ⟨s, hs, ?_⟩
  rw [hre]
  have : 0 < x / L := div_pos hx0 hL
  intro h; linarith

/-- **RH for a genus-one datum is exactly the Hasse bound** `|c| <= 2`. -/
theorem rh_iff (L c : ℝ) (hL : 0 < L) :
    (∀ s : ℂ, Xi L c s = 0 → s.re = 1 / 2) ↔ |c| ≤ 2 := by
  constructor
  · intro h
    by_contra hc
    rw [not_le] at hc
    obtain ⟨s, hs, hre⟩ := offline_zero L c hL hc
    exact hre (h s hs)
  · intro hc
    exact rh_of_le_two L c (ne_of_gt hL) hc

/-- The integer RH predicate `m^2 <= 4q` is RH for the completed function. -/
theorem rh_int_iff_zeros (q m : ℤ) (hq : 2 ≤ q) :
    m ^ 2 ≤ 4 * q ↔ ∀ s : ℂ, Xi (Real.log q) ((m : ℝ) / Real.sqrt q) s = 0 → s.re = 1 / 2 := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hL : 0 < Real.log q := Real.log_pos (by linarith)
  rw [rh_iff _ _ hL]
  set t : ℝ := Real.sqrt q with ht
  have ht0 : 0 < t := Real.sqrt_pos.mpr hq0
  have ht2 : t ^ 2 = q := Real.sq_sqrt hq0.le
  rw [abs_div, abs_of_pos ht0, div_le_iff₀ ht0]
  have hm : ((m : ℝ)) ^ 2 = |(m : ℝ)| ^ 2 := (sq_abs _).symm
  constructor
  · intro h
    have h' : ((m : ℝ)) ^ 2 ≤ 4 * q := by exact_mod_cast h
    by_contra hc
    rw [not_le] at hc
    nlinarith [abs_nonneg (m : ℝ)]
  · intro h
    have : ((m : ℝ)) ^ 2 ≤ 4 * q := by nlinarith [abs_nonneg (m : ℝ)]
    exact_mod_cast this

/-! ## 3. The missing axiom (Hasse / Rosati positivity) and the toral-dynamics model

For an elliptic curve `deg (r - s Frob) = r^2 - m r s + q s^2 >= 0` because degrees are
cardinalities.  For a formal datum this positivity is an extra axiom, and it is exactly RH (at the
abstract level this equivalence is a relabeling of RH; its content is the geometric source).  The
Euler product only sees the orbit values `deg (Frob^n - 1) = N_n`. -/

/-- Hasse positivity is equivalent to RH, with universal witness `(r, s) = (m, 2)`. -/
theorem hasse_iff (q m : ℤ) :
    (∀ r s : ℤ, 0 ≤ r ^ 2 - m * r * s + q * s ^ 2) ↔ m ^ 2 ≤ 4 * q := by
  constructor
  · intro h
    have := h m 2
    nlinarith
  · intro hq r s
    nlinarith [sq_nonneg (2 * r - m * s), sq_nonneg s]

/-- The companion matrix of `x^2 - m x + q` (Frobenius on `H^1` of a 2-torus). -/
def A (q m : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![0, -q; 1, m]

/-- `det (A - r) = r^2 - m r + q`. -/
theorem det_A_sub (q m r : ℤ) :
    (A q m - Matrix.diagonal (fun _ => r)).det = r ^ 2 - m * r + q := by
  rw [Matrix.det_fin_two]
  simp [A]
  ring

/-- The golden Frobenius reverses orientation at `Frob - 2`: `det (A - 2) = -1 < 0`. -/
theorem golden_negative_degree : (A 5 5 - Matrix.diagonal (fun _ => (2 : ℤ))).det = -1 := by
  rw [det_A_sub]; norm_num

lemma A_sq (q m : ℤ) : A q m * A q m = m • A q m - q • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  rw [Matrix.smul_one_eq_diagonal]
  ext i j; fin_cases i <;> fin_cases j <;> simp [A, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma trace_A_pow (q m : ℤ) : ∀ n : ℕ, (A q m ^ n).trace = tr q m n
  | 0 => by simp
  | 1 => by simp [A, Matrix.trace_fin_two]
  | (n + 2) => by
      have h : A q m ^ (n + 2) = m • A q m ^ (n + 1) - q • A q m ^ n := by
        rw [show n + 2 = n + 1 + 1 from rfl, pow_succ (A q m) (n + 1), pow_succ (A q m) n,
          mul_assoc, A_sq, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one]
      rw [h, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, trace_A_pow q m (n + 1),
        trace_A_pow q m n, tr_succ_succ]
      simp

lemma det_A (q m : ℤ) : (A q m).det = q := by simp [A, Matrix.det_fin_two]

/-- **Lefschetz / Artin-Mazur form**: `N_n = det (A^n - 1)`, the Lefschetz number of the toral
endomorphism `A^n` of `R^2/Z^2`. -/
theorem N_eq_det (q m : ℤ) (n : ℕ) : N q m n = (A q m ^ n - 1).det := by
  have h2 : ∀ B : Matrix (Fin 2) (Fin 2) ℤ, (B - 1).det = B.det - B.trace + 1 := by
    intro B; simp [Matrix.det_fin_two, Matrix.trace_fin_two]; ring
  rw [h2, Matrix.det_pow, det_A, trace_A_pow]
  simp [N]; ring

/-- The formal axioms a genus-one Euler product, pole and functional equation supply. -/
structure FormalGenusOne where
  q : ℤ
  m : ℤ
  two_le_q : 2 ≤ q
  euler : ∀ n : ℕ, 0 ≤ N q m (n + 1)
  places_two : 0 ≤ twoA2 q m
  pole : 0 < N q m 1

/-- The Riemann hypothesis for the datum (the Hasse bound). -/
def FormalGenusOne.RH (D : FormalGenusOne) : Prop := D.m ^ 2 ≤ 4 * D.q

/-- The golden fake `(5, 5)`. -/
def golden : FormalGenusOne where
  q := 5
  m := 5
  two_le_q := by norm_num
  euler := fun n => le_trans (by norm_num) (N_golden_pos n)
  places_two := by simp [twoA2]
  pole := by simp

/-- The anti-golden fake `(5, -5)`. -/
def antiGolden : FormalGenusOne where
  q := 5
  m := -5
  two_le_q := by norm_num
  euler := fun n => le_trans (by norm_num) (N_anti_pos n)
  places_two := by simp [twoA2]
  pole := by simp

/-- The formal genus-one axioms do not imply RH. -/
theorem formal_axioms_do_not_imply_rh : ¬ (∀ D : FormalGenusOne, D.RH) := by
  intro h
  have := h golden
  simp [FormalGenusOne.RH, golden] at this

/-- The anti-golden datum violates RH as well. -/
theorem antiGolden_not_rh : ¬ antiGolden.RH := by
  simp [FormalGenusOne.RH, antiGolden]

/-! ## 4. The anti-golden fake: its complete zero set

`XiA s = 2 cosh((s - 1/2) log 5) + sqrt 5` is the completed function of `(q, m) = (5, -5)`.  Its
zeros are EXACTLY `1/2 +- x0 + i (2k+1) pi / log 5`, `x0 = log phi / log 5 = 0.2990...`,
all simple, all off the line, none real, none below height `pi / log 5 = 1.95...`. -/

/-- The golden ratio. -/
noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

lemma sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

lemma sqrt5_bounds : 2.236 < Real.sqrt 5 ∧ Real.sqrt 5 < 2.2361 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

lemma phi_pos : 0 < phi := by unfold phi; positivity

lemma one_lt_phi : 1 < phi := by
  have := sqrt5_bounds.1; unfold phi; linarith

lemma phi_lt : phi < 1.61805 := by
  have := sqrt5_bounds.2; unfold phi; linarith

lemma phi_sq : phi ^ 2 = phi + 1 := by
  unfold phi; have h := sqrt5_sq; nlinarith [h]

lemma cosh_log_phi : Real.cosh (Real.log phi) = Real.sqrt 5 / 2 := by
  have h5 : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  rw [Real.cosh_log phi_pos]
  unfold phi
  have hne : (1 + Real.sqrt 5) ≠ 0 := by positivity
  field_simp
  nlinarith [h5]

lemma log5_pos : 0 < Real.log 5 := Real.log_pos (by norm_num)

lemma log5_bounds : 1.58 < Real.log 5 ∧ Real.log 5 < 1.64 := by
  have h5 : Real.log 5 = 2 * Real.log 2 + Real.log (5 / 4) := by
    have e : (5 : ℝ) = 2 ^ 2 * (5 / 4) := by norm_num
    calc Real.log 5 = Real.log (2 ^ 2 * (5 / 4)) := by rw [← e]
      _ = 2 * Real.log 2 + Real.log (5 / 4) := by
          rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
  have hu := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 / 4 by norm_num)
  have hl := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 5 / 4 by norm_num)
  have h2l := Real.log_two_gt_d9
  have h2u := Real.log_two_lt_d9
  norm_num at hu hl
  constructor <;> linarith

lemma log_phi_pos : 0 < Real.log phi := Real.log_pos one_lt_phi

lemma log_phi_lt : Real.log phi < 0.61805 := by
  have := Real.log_le_sub_one_of_pos phi_pos
  have := phi_lt
  linarith

/-- `2 log phi < log 5` (i.e. `phi^2 < 5`): the fake zeros lie strictly inside the strip. -/
lemma two_log_phi_lt_log5 : 2 * Real.log phi < Real.log 5 := by
  rw [← Real.log_rpow phi_pos, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  apply Real.log_lt_log (by have := phi_pos; positivity)
  rw [phi_sq]; have := phi_lt; linarith

/-- Displacement of the fake zeros from the critical line, `log phi / log 5`. -/
noncomputable def x0 : ℝ := Real.log phi / Real.log 5

lemma x0_pos : 0 < x0 := div_pos log_phi_pos log5_pos

lemma x0_lt_half : x0 < 1 / 2 := by
  unfold x0; rw [div_lt_iff₀ log5_pos]; linarith [two_log_phi_lt_log5]

lemma x0_lt : x0 < 0.4 := by
  unfold x0; rw [div_lt_iff₀ log5_pos]
  have := log5_bounds.1; have := log_phi_lt; linarith

/-- The first fake height `pi / log 5` lies in `(1.9, 2)`. -/
lemma pi_div_log5_bounds : 1.9 < Real.pi / Real.log 5 ∧ Real.pi / Real.log 5 < 2 := by
  have h1 := log5_bounds.1
  have h2 := log5_bounds.2
  have hp1 := Real.pi_gt_d2
  have hp2 := Real.pi_lt_d2
  constructor
  · rw [lt_div_iff₀ log5_pos]; nlinarith
  · rw [div_lt_iff₀ log5_pos]; nlinarith

/-- The anti-golden completed function `2 cosh((s - 1/2) log 5) + sqrt 5`. -/
noncomputable def XiA (s : ℂ) : ℂ := Xi (Real.log 5) (-Real.sqrt 5) s

/-- The explicit fake zeros `1/2 + eps x0 + i (2k+1) pi / log 5`. -/
noncomputable def fakeZero (k : ℤ) (ε : ℝ) : ℂ :=
  ((1 / 2 + ε * x0 : ℝ) : ℂ) + (((2 * k + 1) * Real.pi / Real.log 5 : ℝ) : ℂ) * I

@[simp] lemma fakeZero_re (k : ℤ) (ε : ℝ) : (fakeZero k ε).re = 1 / 2 + ε * x0 := by
  simp only [fakeZero, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

@[simp] lemma fakeZero_im (k : ℤ) (ε : ℝ) :
    (fakeZero k ε).im = (2 * k + 1) * Real.pi / Real.log 5 := by
  simp only [fakeZero, Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

lemma cosh_w0 :
    Complex.cosh ((Real.log phi : ℂ) + Real.pi * I) = ((-(Real.sqrt 5 / 2) : ℝ) : ℂ) := by
  rw [Complex.cosh_add_pi_mul_I, ← Complex.ofReal_cosh, cosh_log_phi]; push_cast; ring

lemma XiA_eq (s : ℂ) :
    XiA s = 2 * Complex.cosh ((s - 1 / 2) * (Real.log 5 : ℝ)) + (Real.sqrt 5 : ℂ) := by
  unfold XiA Xi; push_cast; ring

lemma w_of_fakeZero (k : ℤ) (ε : ℝ) :
    (fakeZero k ε - 1 / 2) * ((Real.log 5 : ℝ) : ℂ)
      = ((ε * Real.log phi : ℝ) : ℂ) + (((2 * k + 1) * Real.pi : ℝ) : ℂ) * I := by
  have hLc : ((Real.log 5 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt log5_pos)
  unfold fakeZero x0
  push_cast
  field_simp
  ring

/-- Every listed point is a zero. -/
theorem XiA_fakeZero (k : ℤ) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) : XiA (fakeZero k ε) = 0 := by
  rw [XiA_eq, w_of_fakeZero, cosh_decomp]
  have hcos : Real.cos ((2 * k + 1) * Real.pi) = -1 := by
    have := Real.cos_int_mul_two_pi_add_pi k
    rw [← this]; congr 1; ring
  have hsin : Real.sin ((2 * k + 1) * Real.pi) = 0 := by
    have := Real.sin_int_mul_pi (2 * k + 1)
    rw [← this]; push_cast; ring_nf
  have hch : Real.cosh (ε * Real.log phi) = Real.sqrt 5 / 2 := by
    rcases hε with h | h
    · rw [h, one_mul, cosh_log_phi]
    · rw [h, neg_one_mul, Real.cosh_neg, cosh_log_phi]
  rw [hcos, hsin, hch]
  push_cast
  ring

/-- **The complete zero set of the anti-golden completed function.** -/
theorem XiA_eq_zero_iff (s : ℂ) :
    XiA s = 0 ↔ ∃ k : ℤ, ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ s = fakeZero k ε := by
  constructor
  · intro hz
    have hL := log5_pos
    have hLc : ((Real.log 5 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hL)
    set w : ℂ := (s - 1 / 2) * (Real.log 5 : ℝ) with hw
    have hs : s = 1 / 2 + w / (Real.log 5 : ℝ) := by rw [hw]; field_simp; ring
    have hcosh : Complex.cosh w = Complex.cosh ((Real.log phi : ℂ) + Real.pi * I) := by
      rw [XiA_eq, ← hw] at hz
      rw [cosh_w0]; push_cast; linear_combination hz / 2
    rw [← Complex.cos_mul_I, ← Complex.cos_mul_I, Complex.cos_eq_cos_iff] at hcosh
    obtain ⟨k, hk | hk⟩ := hcosh
    · refine ⟨k, 1, Or.inl rfl, ?_⟩
      have hw' : w = (Real.log phi : ℂ) + (2 * k + 1) * Real.pi * I := by
        linear_combination I * hk + (w - (Real.log phi : ℂ) - Real.pi * I) * I_sq
      rw [hs, hw']
      unfold fakeZero x0
      push_cast
      field_simp
      ring
    · refine ⟨-k - 1, -1, Or.inr rfl, ?_⟩
      have hw' : w = -(Real.log phi : ℂ) - (2 * k + 1) * Real.pi * I := by
        linear_combination (-I) * hk + (w + (Real.log phi : ℂ) + Real.pi * I) * I_sq
      rw [hs, hw']
      unfold fakeZero x0
      push_cast
      field_simp
      ring
  · rintro ⟨k, ε, hε, rfl⟩
    exact XiA_fakeZero k ε hε

/-- Every zero of `XiA` is simple: `XiA' = 2 log 5 sinh((s - 1/2) log 5)` and `sinh^2 = 1/4` at a
zero (from `cosh = -sqrt 5 / 2`). -/
theorem XiA_zero_simple (s : ℂ) (hs : XiA s = 0) :
    HasDerivAt XiA (2 * Complex.sinh ((s - 1 / 2) * (Real.log 5 : ℝ)) * (Real.log 5 : ℝ)) s ∧
      2 * Complex.sinh ((s - 1 / 2) * (Real.log 5 : ℝ)) * (Real.log 5 : ℝ) ≠ 0 := by
  constructor
  · have h1 : HasDerivAt (fun z : ℂ => (z - 1 / 2) * (Real.log 5 : ℝ)) (Real.log 5 : ℝ) s := by
      simpa using ((hasDerivAt_id s).sub_const (1 / 2 : ℂ)).mul_const ((Real.log 5 : ℝ) : ℂ)
    have h2 := ((h1.ccosh).const_mul (2 : ℂ)).add_const ((Real.sqrt 5 : ℝ) : ℂ)
    have hfun : XiA = fun z => 2 * Complex.cosh ((z - 1 / 2) * (Real.log 5 : ℝ))
        + ((Real.sqrt 5 : ℝ) : ℂ) := by
      funext z; rw [XiA_eq]
    rw [hfun]
    exact h2.congr_deriv (by ring)
  · have hc : Complex.cosh ((s - 1 / 2) * (Real.log 5 : ℝ)) = -(Real.sqrt 5 : ℂ) / 2 := by
      rw [XiA_eq] at hs; linear_combination hs / 2
    have hsq := Complex.cosh_sq_sub_sinh_sq ((s - 1 / 2) * (Real.log 5 : ℝ))
    rw [hc] at hsq
    have h5 : (Real.sqrt 5 : ℂ) ^ 2 = 5 := by
      rw [← Complex.ofReal_pow, sqrt5_sq]; push_cast; ring
    have hsh : Complex.sinh ((s - 1 / 2) * (Real.log 5 : ℝ)) ^ 2 = 1 / 4 := by
      linear_combination -hsq + h5 / 4
    have hLc : ((Real.log 5 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt log5_pos)
    intro h0
    have : Complex.sinh ((s - 1 / 2) * (Real.log 5 : ℝ)) = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · norm_num at h'
        · exact h'
      · exact absurd h hLc
    rw [this] at hsh
    norm_num at hsh

/-- The zero set is periodic with period `2 pi i / log 5` (a lattice in the imaginary direction). -/
theorem XiA_periodic (s : ℂ) :
    XiA (s + ((2 * Real.pi / Real.log 5 : ℝ) : ℂ) * I) = XiA s := by
  have hLc : ((Real.log 5 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt log5_pos)
  rw [XiA_eq, XiA_eq]
  have : (s + ((2 * Real.pi / Real.log 5 : ℝ) : ℂ) * I - 1 / 2) * ((Real.log 5 : ℝ) : ℂ)
      = (s - 1 / 2) * ((Real.log 5 : ℝ) : ℂ) + (2 * (Real.pi : ℂ)) * I := by
    push_cast; field_simp; ring
  rw [this, Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, Complex.cos_two_pi,
    Complex.sin_two_pi]
  ring

/-- The fake zeros lie strictly inside the critical strip. -/
lemma fakeZero_re_mem (k : ℤ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    0 < (fakeZero k ε).re ∧ (fakeZero k ε).re < 1 := by
  rw [fakeZero_re]
  have h1 := x0_pos; have h2 := x0_lt_half
  rcases hε with h | h <;> rw [h] <;> constructor <;> linarith

/-- The fake zeros are all OFF the critical line. -/
lemma fakeZero_re_ne_half (k : ℤ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) : (fakeZero k ε).re ≠ 1 / 2 := by
  rw [fakeZero_re]
  have h1 := x0_pos
  rcases hε with h | h <;> rw [h] <;> intro hc <;> linarith

lemma fakeZero_abs_re_sub_half (k : ℤ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ((fakeZero k ε).re - 1 / 2) ^ 2 = x0 ^ 2 := by
  rw [fakeZero_re]; rcases hε with h | h <;> rw [h] <;> ring

lemma one_le_abs_two_mul_add_one (k : ℤ) : (1 : ℝ) ≤ |2 * (k : ℝ) + 1| := by
  have : (1 : ℤ) ≤ |2 * k + 1| := by
    rcases le_or_gt 0 k with hk | hk
    · rw [abs_of_nonneg (by omega)]; omega
    · rw [abs_of_neg (by omega)]; omega
  have h' : ((1 : ℤ) : ℝ) ≤ ((|2 * k + 1| : ℤ) : ℝ) := by exact_mod_cast this
  push_cast at h'
  exact h'

/-- No fake zero lies below height `pi / log 5`. -/
lemma fakeZero_abs_im_ge (k : ℤ) (ε : ℝ) : Real.pi / Real.log 5 ≤ |(fakeZero k ε).im| := by
  rw [fakeZero_im, show (2 * (k : ℝ) + 1) * Real.pi / Real.log 5
      = (2 * (k : ℝ) + 1) * (Real.pi / Real.log 5) by ring, abs_mul,
    abs_of_pos (div_pos Real.pi_pos log5_pos)]
  have := one_le_abs_two_mul_add_one k
  have hp : 0 < Real.pi / Real.log 5 := div_pos Real.pi_pos log5_pos
  nlinarith

lemma fakeZero_im_sq_ge (k : ℤ) (ε : ℝ) : 3.61 ≤ (fakeZero k ε).im ^ 2 := by
  have h := fakeZero_abs_im_ge k ε
  have hb := pi_div_log5_bounds.1
  have h' : (1.9 : ℝ) ≤ |(fakeZero k ε).im| := by linarith
  have := sq_abs (fakeZero k ε).im
  nlinarith [abs_nonneg (fakeZero k ε).im]

/-- The golden-anti fake has an explicit zero in the rectangle `[0.001, 0.999] x [0, 55/16]`. -/
lemma fakeZero_in_box :
    1 / 1000 ≤ (fakeZero 0 1).re ∧ (fakeZero 0 1).re ≤ 999 / 1000 ∧
      0 ≤ (fakeZero 0 1).im ∧ (fakeZero 0 1).im ≤ 55 / 16 := by
  have him : (fakeZero 0 1).im = Real.pi / Real.log 5 := by
    rw [fakeZero_im]; push_cast; ring
  rw [fakeZero_re, him]
  have h1 := x0_pos; have h2 := x0_lt
  have hb := pi_div_log5_bounds
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-! ## 5. The golden hybrid: `XiH = xi * XiA`

`XiH` completes both the proposal's Euler product `zeta(s) Z_{5,-5}(5^(-s))` and the repaired
`H4` (section 10; section 8 checks the Euler side).  It is entire, symmetric under `s -> 1 - s`,
real on the real axis, and its zero set is exactly (nontrivial zeros of zeta) union (the explicit
fake zeros). -/

lemma XiA_differentiable : Differentiable ℂ XiA := by
  have : XiA = fun z => 2 * Complex.cosh ((z - 1 / 2) * (Real.log 5 : ℝ)) + ((Real.sqrt 5 : ℝ) : ℂ) := by
    funext z; rw [XiA_eq]
  rw [this]
  fun_prop

lemma XiA_one_sub (s : ℂ) : XiA (1 - s) = XiA s := Xi_symm _ _ s

lemma XiA_conj (s : ℂ) : XiA (starRingEnd ℂ s) = starRingEnd ℂ (XiA s) := by
  have h : starRingEnd ℂ ((s - 1 / 2) * ((Real.log 5 : ℝ) : ℂ))
      = (starRingEnd ℂ s - 1 / 2) * ((Real.log 5 : ℝ) : ℂ) := by
    rw [map_mul, map_sub, Complex.conj_ofReal, map_div₀, map_one, map_ofNat]
  rw [XiA_eq, XiA_eq, map_add, map_mul, ← Complex.cosh_conj, h, Complex.conj_ofReal, map_ofNat]

/-- The completed function of the golden hybrid. -/
noncomputable def XiH (s : ℂ) : ℂ := LiCriterion.riemannXi s * XiA s

theorem XiH_entire : Differentiable ℂ XiH :=
  LiCriterion.xi_entire.mul XiA_differentiable

theorem XiH_one_sub (s : ℂ) : XiH (1 - s) = XiH s := by
  unfold XiH; rw [LiCriterion.riemannXi_one_sub, XiA_one_sub]

theorem XiH_conj (s : ℂ) : XiH (starRingEnd ℂ s) = starRingEnd ℂ (XiH s) := by
  unfold XiH; rw [LiCriterion.riemannXi_conj, XiA_conj, map_mul]

/-- The zeros of the upstream `riemannXi` are exactly the nontrivial zeros of zeta. -/
lemma riemannXi_eq_zero_iff (s : ℂ) :
    LiCriterion.riemannXi s = 0 ↔ riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 := by
  have heq : LiCriterion.riemannXi s = XiZeros.riemannXi s := rfl
  rw [heq, XiZeros.xi_zeros_are_nontrivial_zeros]
  constructor
  · rintro ⟨ρ, rfl⟩; exact ρ.property
  · intro h; exact ⟨⟨s, h⟩, rfl⟩

/-- **The zero set of the hybrid.** -/
theorem XiH_eq_zero_iff (s : ℂ) :
    XiH s = 0 ↔ (riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1) ∨
      ∃ k : ℤ, ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ s = fakeZero k ε := by
  unfold XiH
  rw [mul_eq_zero, riemannXi_eq_zero_iff, XiA_eq_zero_iff]

/-- **The hybrid violates RH**: `1/2 + log phi / log 5 + i pi / log 5` is a zero off the line. -/
theorem XiH_offline_zero : XiH (fakeZero 0 1) = 0 ∧ (fakeZero 0 1).re ≠ 1 / 2 :=
  ⟨(XiH_eq_zero_iff _).2 (Or.inr ⟨0, 1, Or.inl rfl, rfl⟩), fakeZero_re_ne_half 0 (Or.inl rfl)⟩

/-! ## 6. The pointwise layer of the corpus, and the barrier

These are the conclusions of the corpus's hypothesis-free zero-location theorems, each a statement
about every zero separately: strip, reflection and conjugation symmetry, Box 1 and Box 2
(`LowHeightBox`), no real zeros, the de la Vallee Poussin region with the explicit constant
(`ZeroFreeBridge.riemannZeta_ne_zero_region`), and the disk condition `Re (rho (1 - rho)) >= 1`
from which `LiBoxRungs` derives the Li rungs `0..4`. -/

/-- `dlvpRateC <= 1/1792` (the constant is `1/(1792 K)` with `K >= 1`). -/
lemma dlvpRateC_le : ZeroFreeBridge.dlvpRateC ≤ 1 / 1792 := by
  have hpi : (0 : ℝ) < 2 - Real.pi ^ 2 / 6 := ZeroFreeBridge.two_sub_pi_sq_div_six_pos
  have hdK1 : 1 ≤ ZeroFreeBridge.dlvpRateK := by
    rw [ZeroFreeBridge.dlvpRateK]
    have hLrpos : 0 < Real.log ((23/16) / (11/8)) := Real.log_pos (by norm_num)
    have hlog15 : 0 ≤ Real.log (15 / (2 - Real.pi ^ 2 / 6)) :=
      Real.log_nonneg (by rw [le_div_iff₀ hpi]; nlinarith [hpi])
    have : 0 ≤ 2 * ((8 / (3 * Real.log ((23/16) / (11/8))) + 608/9) / 16)
        * (Real.log (15 / (2 - Real.pi ^ 2 / 6)) + 1) := by positivity
    linarith
  rw [ZeroFreeBridge.dlvpRateC,
    show (112:ℝ) * 16 * ZeroFreeBridge.dlvpRateK = 1792 * ZeroFreeBridge.dlvpRateK by ring]
  exact one_div_le_one_div_of_le (by norm_num) (by nlinarith [hdK1])

/-- The pointwise layer, as a predicate on a zero set `Z`. -/
structure PointwiseLayer (Z : ℂ → Prop) : Prop where
  strip : ∀ ρ, Z ρ → 0 < ρ.re ∧ ρ.re < 1
  reflect : ∀ ρ, Z ρ → Z (1 - ρ)
  conj : ∀ ρ, Z ρ → Z (starRingEnd ℂ ρ)
  box1 : ∀ ρ, Z ρ → Real.sqrt 3 / 2 ≤ |ρ.im|
  box2 : ∀ ρ, Z ρ → (ρ.re - 1 / 2) ^ 2 ≤ ρ.im ^ 2 / 3 - 1 / 4
  noReal : ∀ ρ, Z ρ → ρ.im ≠ 0
  dvp : ∀ ρ, Z ρ → 55 / 16 ≤ |ρ.im| → ρ.re ≤ 1 - ZeroFreeBridge.dlvpRateC / Real.log |ρ.im|
  liDisk : ∀ ρ, Z ρ → 1 ≤ (ρ * (1 - ρ)).re

/-- The nontrivial zeros of zeta. -/
def ZetaStripZero (ρ : ℂ) : Prop := riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

lemma sqrt3_half_pos : 0 < Real.sqrt 3 / 2 := by positivity

lemma sqrt3_half_lt : Real.sqrt 3 / 2 < 0.87 := by
  have : Real.sqrt 3 < 1.74 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

/-- The dVP conclusion in "every zero" form, from the corpus's zero-free region. -/
lemma zeta_dvp (ρ : ℂ) (h0 : riemannZeta ρ = 0) (hγ : 55 / 16 ≤ |ρ.im|) :
    ρ.re ≤ 1 - ZeroFreeBridge.dlvpRateC / Real.log |ρ.im| := by
  by_contra hc
  have hne := ZeroFreeBridge.riemannZeta_ne_zero_region ρ.re ρ.im hγ (lt_of_not_ge hc)
  apply hne
  rw [Complex.re_add_im]
  exact h0

/-- **Non-vacuity: zeta satisfies the pointwise layer** (every clause is a corpus theorem). -/
theorem zeta_pointwiseLayer : PointwiseLayer ZetaStripZero where
  strip := fun ρ h => h.2
  reflect := fun ρ h => by
    refine ⟨LowHeightBox.zeta_one_sub_zero h.1 h.2.1 h.2.2, ?_, ?_⟩ <;>
      simp only [Complex.sub_re, Complex.one_re] <;> linarith [h.2.1, h.2.2]
  conj := fun ρ h => by
    refine ⟨?_, ?_, ?_⟩
    · rw [riemannZeta_conj, h.1, map_zero]
    · simpa using h.2.1
    · simpa using h.2.2
  box1 := fun ρ h => LowHeightBox.zeta_zero_im_ge ρ h.1 h.2
  box2 := fun ρ h => LowHeightBox.zeta_zero_confined ρ h.1 h.2
  noReal := fun ρ h => by
    have := LowHeightBox.zeta_zero_im_ge ρ h.1 h.2
    have hp := sqrt3_half_pos
    intro h0; rw [h0, abs_zero] at this; linarith
  dvp := fun ρ h hγ => zeta_dvp ρ h.1 hγ
  liDisk := fun ρ h => LowHeightBox.re_mul_one_sub_ge_one ⟨ρ, h⟩

/-- The fake zeros satisfy every clause of the pointwise layer. -/
lemma fake_box2 (k : ℤ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ((fakeZero k ε).re - 1 / 2) ^ 2 ≤ (fakeZero k ε).im ^ 2 / 3 - 1 / 4 := by
  rw [fakeZero_abs_re_sub_half k hε]
  have h1 := fakeZero_im_sq_ge k ε
  have h2 := x0_lt; have h3 := x0_pos
  nlinarith

lemma fake_liDisk (k : ℤ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    1 ≤ (fakeZero k ε * (1 - fakeZero k ε)).re := by
  have hre : (fakeZero k ε * (1 - fakeZero k ε)).re
      = 1 / 4 - ((fakeZero k ε).re - 1 / 2) ^ 2 + (fakeZero k ε).im ^ 2 := by
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
    ring
  rw [hre, fakeZero_abs_re_sub_half k hε]
  have h1 := fakeZero_im_sq_ge k ε
  have h2 := x0_lt; have h3 := x0_pos
  nlinarith

lemma fake_dvp (k : ℤ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (hγ : 55 / 16 ≤ |(fakeZero k ε).im|) :
    (fakeZero k ε).re ≤ 1 - ZeroFreeBridge.dlvpRateC / Real.log |(fakeZero k ε).im| := by
  have hre : (fakeZero k ε).re ≤ 0.9 := by
    rw [fakeZero_re]
    have h2 := x0_lt; have h3 := x0_pos
    rcases hε with h | h <;> rw [h] <;> linarith
  have hlog1 : 1 ≤ Real.log |(fakeZero k ε).im| := by
    have hle : Real.exp 1 ≤ |(fakeZero k ε).im| := by nlinarith [Real.exp_one_lt_d9]
    calc (1 : ℝ) = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ ≤ Real.log |(fakeZero k ε).im| := Real.log_le_log (by positivity) hle
  have hc0 := ZeroFreeBridge.dlvpRateC_pos
  have hc1 := dlvpRateC_le
  have hdiv : ZeroFreeBridge.dlvpRateC / Real.log |(fakeZero k ε).im| ≤ 1 / 1792 := by
    have := div_le_self (le_of_lt hc0) hlog1
    linarith
  linarith

/-- The one-sub map sends fake zeros to fake zeros. -/
lemma one_sub_fakeZero (k : ℤ) (ε : ℝ) : 1 - fakeZero k ε = fakeZero (-k - 1) (-ε) := by
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.one_re, fakeZero_re]; ring
  · simp only [Complex.sub_im, Complex.one_im, fakeZero_im]; push_cast; ring

lemma conj_fakeZero (k : ℤ) (ε : ℝ) : starRingEnd ℂ (fakeZero k ε) = fakeZero (-k - 1) ε := by
  apply Complex.ext
  · simp only [Complex.conj_re, fakeZero_re]
  · simp only [Complex.conj_im, fakeZero_im]; push_cast; ring

/-- **The hybrid satisfies the pointwise layer.** -/
theorem hybrid_pointwiseLayer : PointwiseLayer (fun ρ => XiH ρ = 0) where
  strip := fun ρ h => by
    rcases (XiH_eq_zero_iff ρ).1 h with hz | ⟨k, ε, hε, rfl⟩
    · exact hz.2
    · exact fakeZero_re_mem k hε
  reflect := fun ρ h => by rw [XiH_one_sub]; exact h
  conj := fun ρ h => by rw [XiH_conj, h, map_zero]
  box1 := fun ρ h => by
    rcases (XiH_eq_zero_iff ρ).1 h with hz | ⟨k, ε, hε, rfl⟩
    · exact LowHeightBox.zeta_zero_im_ge ρ hz.1 hz.2
    · have := fakeZero_abs_im_ge k ε
      have := pi_div_log5_bounds.1
      have := sqrt3_half_lt
      linarith
  box2 := fun ρ h => by
    rcases (XiH_eq_zero_iff ρ).1 h with hz | ⟨k, ε, hε, rfl⟩
    · exact LowHeightBox.zeta_zero_confined ρ hz.1 hz.2
    · exact fake_box2 k hε
  noReal := fun ρ h => by
    rcases (XiH_eq_zero_iff ρ).1 h with hz | ⟨k, ε, hε, rfl⟩
    · exact zeta_pointwiseLayer.noReal ρ hz
    · have h1 := fakeZero_abs_im_ge k ε
      have h2 := pi_div_log5_bounds.1
      intro h0; rw [h0, abs_zero] at h1; linarith
  dvp := fun ρ h hγ => by
    rcases (XiH_eq_zero_iff ρ).1 h with hz | ⟨k, ε, hε, rfl⟩
    · exact zeta_dvp ρ hz.1 hγ
    · exact fake_dvp k hε hγ
  liDisk := fun ρ h => by
    rcases (XiH_eq_zero_iff ρ).1 h with hz | ⟨k, ε, hε, rfl⟩
    · exact zeta_pointwiseLayer.liDisk ρ hz
    · exact fake_liDisk k hε

/-- **THE POINTWISE BARRIER.**  No argument that uses only the pointwise layer (as a property of a
zero set) can prove that all zeros lie on the line: the hybrid satisfies the layer and has an
off-line zero.  (Sound but, like every relativization, silent about zeta itself: see the module
header and section 9 for exactly which extra inputs separate zeta from the hybrid.) -/
theorem pointwise_layer_does_not_imply_rh :
    ¬ ∀ Z : ℂ → Prop, PointwiseLayer Z → ∀ ρ, Z ρ → ρ.re = 1 / 2 := by
  intro h
  exact XiH_offline_zero.2 (h _ hybrid_pointwiseLayer _ XiH_offline_zero.1)

/-! ## 7. The Li rungs `0..4` of the hybrid

`LiBoxRungs` proves `0 <= Re lambda_n(zeta)` for `n <= 4` from the disk condition alone: each paired
summand is `Q_(n+1)(z)`, `z = 1/(rho (1 - rho))`, and `Re Q_N >= 0` on the disk `|z - 1/2| <= 1/2`.
The fake zeros satisfy the disk condition, so the fake paired sum is termwise nonnegative too.  The
hybrid's Li coefficient is the zeta coefficient plus the fake paired zero sum (additivity of Li
coefficients over a product; for the fake factor the symmetric paired-sum formula is the genus-one
Hadamard argument -- PAPER, not kernel; the kernel content is the nonnegativity and summability
of the fake sum). -/

/-- The paired Li summand at an arbitrary point (`LiFacePrelude.liPairedSummand_eq_pow`). -/
noncomputable def pairTerm (n : ℕ) (ρ : ℂ) : ℂ :=
  2 - (ρ / (ρ - 1)) ^ (n + 1) - ((ρ - 1) / ρ) ^ (n + 1)

lemma ne_zero_one_of_liDisk {ρ : ℂ} (h : 1 ≤ (ρ * (1 - ρ)).re) : ρ ≠ 0 ∧ ρ ≠ 1 := by
  constructor
  · rintro rfl; simp at h; linarith
  · rintro rfl; simp at h; linarith

lemma zOf_eq' {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    LowHeightBox.zOf ρ = 2 - ρ / (ρ - 1) - (ρ - 1) / ρ := by
  have h1' : ρ - 1 ≠ 0 := sub_ne_zero.mpr h1
  have h1'' : 1 - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  unfold LowHeightBox.zOf
  field_simp
  ring

lemma pairTerm_eq_Q {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    pairTerm 0 ρ = LowHeightBox.Q1 (LowHeightBox.zOf ρ) ∧
    pairTerm 1 ρ = LowHeightBox.Q2 (LowHeightBox.zOf ρ) ∧
    pairTerm 2 ρ = LowHeightBox.Q3 (LowHeightBox.zOf ρ) ∧
    pairTerm 3 ρ = LowHeightBox.Q4 (LowHeightBox.zOf ρ) ∧
    pairTerm 4 ρ = LowHeightBox.Q5 (LowHeightBox.zOf ρ) := by
  have h1' : ρ - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hv : ρ / (ρ - 1) * ((ρ - 1) / ρ) = 1 := by field_simp
  rw [zOf_eq' h0 h1]
  set w := ρ / (ρ - 1)
  set v := (ρ - 1) / ρ
  unfold pairTerm
  simp only [LowHeightBox.Q1, LowHeightBox.Q2, LowHeightBox.Q3, LowHeightBox.Q4, LowHeightBox.Q5]
  refine ⟨by ring, ?_, ?_, ?_, ?_⟩
  · linear_combination (2 : ℂ) * hv
  · linear_combination (3 * v + 3 * w) * hv
  · linear_combination (4 * v ^ 2 + 6 * v * w + 4 * w ^ 2 - 2) * hv
  · linear_combination (5 * v ^ 3 + 10 * v ^ 2 * w + 10 * v * w ^ 2 - 5 * v + 5 * w ^ 3 - 5 * w) * hv

lemma zOf_mem_disk' {ρ : ℂ} (hq : 1 ≤ (ρ * (1 - ρ)).re) :
    (LowHeightBox.zOf ρ).re ^ 2 + (LowHeightBox.zOf ρ).im ^ 2 ≤ (LowHeightBox.zOf ρ).re := by
  set q := ρ * (1 - ρ) with hqdef
  have hqne : q ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hq; norm_num at hq
  have hm : 0 < Complex.normSq q := Complex.normSq_pos.mpr hqne
  have hz : LowHeightBox.zOf ρ = q⁻¹ := by rw [LowHeightBox.zOf, one_div]
  rw [hz, Complex.inv_re, Complex.inv_im, Complex.normSq_apply] at *
  have hsum : (q.re / (q.re * q.re + q.im * q.im)) ^ 2 + (-q.im / (q.re * q.re + q.im * q.im)) ^ 2
      = 1 / (q.re * q.re + q.im * q.im) := by
    field_simp
  rw [hsum]
  exact (div_le_div_iff_of_pos_right hm).mpr hq

/-- **Termwise nonnegativity at any point of the disk**, `n <= 4`. -/
theorem pairTerm_re_nonneg {n : ℕ} (hn : n ≤ 4) {ρ : ℂ} (hq : 1 ≤ (ρ * (1 - ρ)).re) :
    0 ≤ (pairTerm n ρ).re := by
  obtain ⟨h0, h1⟩ := ne_zero_one_of_liDisk hq
  have hz := zOf_mem_disk' hq
  obtain ⟨e0, e1, e2, e3, e4⟩ := pairTerm_eq_Q h0 h1
  interval_cases n
  · rw [e0]; exact LowHeightBox.re_Q1_nonneg hz
  · rw [e1]; exact LowHeightBox.re_Q2_nonneg hz
  · rw [e2]; exact LowHeightBox.re_Q3_nonneg hz
  · rw [e3]; exact LowHeightBox.re_Q4_nonneg hz
  · rw [e4]; exact LowHeightBox.re_Q5_nonneg hz

/-- The fake Li coefficient: the paired zero sum over the fake zeros (one representative
`1/2 + x0 + i y_k` of each pair `{rho, 1 - rho}`). -/
noncomputable def fakeLi (n : ℕ) : ℂ := ∑' k : ℤ, pairTerm n (fakeZero k 1)

/-- The hybrid Li coefficient (zeta part: the upstream `taylorCoeff riemannXi n`). -/
noncomputable def hybridLi (n : ℕ) : ℂ := LiCriterion.taylorCoeff LiCriterion.riemannXi n + fakeLi n

lemma norm_Q_le {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖LowHeightBox.Q1 z‖ ≤ 121 * ‖z‖ ∧ ‖LowHeightBox.Q2 z‖ ≤ 121 * ‖z‖ ∧
    ‖LowHeightBox.Q3 z‖ ≤ 121 * ‖z‖ ∧ ‖LowHeightBox.Q4 z‖ ≤ 121 * ‖z‖ ∧
    ‖LowHeightBox.Q5 z‖ ≤ 121 * ‖z‖ := by
  have h0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hp : ∀ k : ℕ, k ≠ 0 → ‖z‖ ^ k ≤ ‖z‖ := fun k hk => pow_le_of_le_one h0 hz hk
  have n2 := hp 2 (by norm_num); have n3 := hp 3 (by norm_num)
  have n4 := hp 4 (by norm_num); have n5 := hp 5 (by norm_num)
  have c : ∀ (a : ℂ) (w : ℂ), ‖a * w‖ = ‖a‖ * ‖w‖ := fun a w => norm_mul a w
  simp only [LowHeightBox.Q1, LowHeightBox.Q2, LowHeightBox.Q3, LowHeightBox.Q4, LowHeightBox.Q5]
  refine ⟨by linarith, ?_, ?_, ?_, ?_⟩
  · calc ‖4 * z - z ^ 2‖ ≤ ‖4 * z‖ + ‖z ^ 2‖ := norm_sub_le _ _
      _ ≤ 4 * ‖z‖ + ‖z‖ := by rw [c]; norm_num; linarith
      _ ≤ 121 * ‖z‖ := by linarith
  · calc ‖9 * z - 6 * z ^ 2 + z ^ 3‖ ≤ ‖9 * z‖ + ‖6 * z ^ 2‖ + ‖z ^ 3‖ :=
          (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
      _ ≤ 9 * ‖z‖ + 6 * ‖z‖ + ‖z‖ := by rw [c, c]; norm_num; nlinarith
      _ ≤ 121 * ‖z‖ := by linarith
  · calc ‖16 * z - 20 * z ^ 2 + 8 * z ^ 3 - z ^ 4‖
          ≤ ‖16 * z‖ + ‖20 * z ^ 2‖ + ‖8 * z ^ 3‖ + ‖z ^ 4‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          refine (norm_add_le _ _).trans ?_
          gcongr
          exact norm_sub_le _ _
      _ ≤ 16 * ‖z‖ + 20 * ‖z‖ + 8 * ‖z‖ + ‖z‖ := by rw [c, c, c]; norm_num; nlinarith
      _ ≤ 121 * ‖z‖ := by linarith
  · calc ‖25 * z - 50 * z ^ 2 + 35 * z ^ 3 - 10 * z ^ 4 + z ^ 5‖
          ≤ ‖25 * z‖ + ‖50 * z ^ 2‖ + ‖35 * z ^ 3‖ + ‖10 * z ^ 4‖ + ‖z ^ 5‖ := by
          refine (norm_add_le _ _).trans ?_
          gcongr
          refine (norm_sub_le _ _).trans ?_
          gcongr
          refine (norm_add_le _ _).trans ?_
          gcongr
          exact norm_sub_le _ _
      _ ≤ 25 * ‖z‖ + 50 * ‖z‖ + 35 * ‖z‖ + 10 * ‖z‖ + ‖z‖ := by
          rw [c, c, c, c]; norm_num; nlinarith
      _ ≤ 121 * ‖z‖ := by linarith

/-- `‖zOf rho‖ <= 1 / Re (rho (1 - rho))` on the disk. -/
lemma norm_zOf_le {ρ : ℂ} (hq : 1 ≤ (ρ * (1 - ρ)).re) :
    ‖LowHeightBox.zOf ρ‖ ≤ 1 / (ρ * (1 - ρ)).re := by
  have hpos : 0 < (ρ * (1 - ρ)).re := by linarith
  rw [LowHeightBox.zOf, norm_div, norm_one]
  apply one_div_le_one_div_of_le hpos
  exact (Complex.re_le_norm _)

lemma fake_re_mul_ge (k : ℤ) :
    (fakeZero k 1).im ^ 2 ≤ (fakeZero k 1 * (1 - fakeZero k 1)).re := by
  have hre : (fakeZero k 1 * (1 - fakeZero k 1)).re
      = 1 / 4 - ((fakeZero k 1).re - 1 / 2) ^ 2 + (fakeZero k 1).im ^ 2 := by
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
    ring
  rw [hre, fakeZero_abs_re_sub_half k (Or.inl rfl)]
  have := x0_lt; have := x0_pos
  nlinarith

/-- The majorant `1/(2k+1)^2 <= 1/k^2 + [k = 0]` over `Z`, summable. -/
lemma summable_inv_odd_sq : Summable (fun k : ℤ => 1 / ((2 * (k : ℝ) + 1) ^ 2)) := by
  have hs : Summable (fun k : ℤ => 1 / (k : ℝ) ^ 2 + (if k = 0 then 1 else 0)) := by
    refine (Real.summable_one_div_int_pow.mpr (by norm_num)).add ?_
    exact summable_of_ne_finset_zero (s := {0}) (fun b hb => by
      simp only [Finset.mem_singleton] at hb; simp [hb])
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hs
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · have hk' : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by
      have : (1 : ℤ) ≤ k ^ 2 := by nlinarith [sq_nonneg k, Int.one_le_abs hk, sq_abs k]
      exact_mod_cast this
    have hle : (k : ℝ) ^ 2 ≤ (2 * (k : ℝ) + 1) ^ 2 := by
      have : (k : ℤ) ^ 2 ≤ (2 * k + 1) ^ 2 := by
        rcases le_or_gt 0 k with h | h
        · nlinarith
        · nlinarith
      exact_mod_cast this
    simp only [hk, ite_false, add_zero]
    exact one_div_le_one_div_of_le (by linarith) hle

/-- **The fake paired Li sums converge**, `n <= 4`. -/
theorem summable_fake_pairTerm {n : ℕ} (hn : n ≤ 4) :
    Summable (fun k : ℤ => pairTerm n (fakeZero k 1)) := by
  set c : ℝ := 121 * (Real.log 5 / Real.pi) ^ 2 with hc
  refine Summable.of_norm_bounded (summable_inv_odd_sq.mul_left c) (fun k => ?_)
  have hq := fake_liDisk k (Or.inl rfl)
  obtain ⟨h0, h1⟩ := ne_zero_one_of_liDisk hq
  have hz1 : ‖LowHeightBox.zOf (fakeZero k 1)‖ ≤ 1 := by
    have := norm_zOf_le hq
    have h1q : 1 / (fakeZero k 1 * (1 - fakeZero k 1)).re ≤ 1 := by
      rw [div_le_one (by linarith)]; exact hq
    linarith
  obtain ⟨e0, e1, e2, e3, e4⟩ := pairTerm_eq_Q h0 h1
  obtain ⟨b1, b2, b3, b4, b5⟩ := norm_Q_le hz1
  have hQ : ‖pairTerm n (fakeZero k 1)‖ ≤ 121 * ‖LowHeightBox.zOf (fakeZero k 1)‖ := by
    interval_cases n
    · rw [e0]; exact b1
    · rw [e1]; exact b2
    · rw [e2]; exact b3
    · rw [e3]; exact b4
    · rw [e4]; exact b5
  have hzb : ‖LowHeightBox.zOf (fakeZero k 1)‖ ≤ 1 / (fakeZero k 1).im ^ 2 := by
    have := norm_zOf_le hq
    have him2 : 0 < (fakeZero k 1).im ^ 2 := by have := fakeZero_im_sq_ge k 1; linarith
    have := one_div_le_one_div_of_le him2 (fake_re_mul_ge k)
    linarith
  have him : (fakeZero k 1).im ^ 2 = (2 * (k : ℝ) + 1) ^ 2 * (Real.pi / Real.log 5) ^ 2 := by
    rw [fakeZero_im]; ring
  have hodd : 0 < (2 * (k : ℝ) + 1) ^ 2 := by
    have := one_le_abs_two_mul_add_one k
    have := sq_abs (2 * (k : ℝ) + 1)
    nlinarith
  have hpl : 0 < Real.pi / Real.log 5 := div_pos Real.pi_pos log5_pos
  calc ‖pairTerm n (fakeZero k 1)‖ ≤ 121 * ‖LowHeightBox.zOf (fakeZero k 1)‖ := hQ
    _ ≤ 121 * (1 / (fakeZero k 1).im ^ 2) := by gcongr
    _ = c * (1 / (2 * (k : ℝ) + 1) ^ 2) := by
        rw [him, hc]; field_simp
    _ = c * (1 / ((2 * (k : ℝ) + 1) ^ 2)) := rfl

/-- **The hybrid's Li rungs `0..4` are nonnegative** -- exactly as for zeta. -/
theorem hybrid_li_rungs : ∀ n : ℕ, n < 5 → 0 ≤ (hybridLi n).re := by
  intro n hn
  unfold hybridLi fakeLi
  rw [Complex.add_re]
  have hz := LowHeightBox.li_rungs_lt_five n hn
  have hf : 0 ≤ (∑' k : ℤ, pairTerm n (fakeZero k 1)).re := by
    rw [Complex.re_tsum (summable_fake_pairTerm (by omega))]
    exact tsum_nonneg (fun k => pairTerm_re_nonneg (by omega) (fake_liDisk k (Or.inl rfl)))
  linarith

/-! ## 8. The Euler side: the literal hybrid has a DOUBLE pole; a repaired model

The proposal's hybrid is `H(s) = zeta(s) Z_{5,-5}(5^(-s))`, local factor at 5
`(1 + 5T + 5T^2)/((1-T)^2 (1-5T))`, `T = 5^(-s)`.  Its weights are positive (below), but the factor
`1/(1-5T)` has a pole at `s = 1`, so `H` has a DOUBLE pole there (`Hlit_double_pole`): the class
clause "a simple pole at `s = 1` with positive residue" FAILS for it.  The repair
`H4(s) = zeta(s) (1 + 5 * 5^(-s) + 5 * 5^(-2s))/(1 - 4 * 5^(-s))` has the same completed zero set
(the completion absorbs the denominator), positive weights `1 + 4^n - t_n(5,-5)`, and a SIMPLE
pole at `s = 1` with residue `11` -- but it pays with a pole at the real point
`log 4 / log 5 = 0.861...` inside the strip (`H4_pole_in_strip`).  Section 9 proves this trade is
forced. -/

/-- Ratio invariant of `t_n(5,5)` (the golden power sums). -/
lemma tr_five_ratio : ∀ n : ℕ, 2 * tr 5 5 (n + 1) ≤ tr 5 5 (n + 2) ∧
    tr 5 5 (n + 2) ≤ 4 * tr 5 5 (n + 1) ∧ 0 < tr 5 5 (n + 1)
  | 0 => by decide
  | (n + 1) => by
      obtain ⟨h1, h2, h3⟩ := tr_five_ratio n
      have e : tr 5 5 (n + 3) = 5 * tr 5 5 (n + 2) - 5 * tr 5 5 (n + 1) := tr_succ_succ 5 5 (n + 1)
      have hA : tr 5 5 (n + 1 + 1) = tr 5 5 (n + 2) := rfl
      have hB : tr 5 5 (n + 1 + 2) = tr 5 5 (n + 3) := rfl
      rw [hA, hB]
      refine ⟨?_, ?_, ?_⟩ <;> omega

lemma tr_five_le : ∀ n : ℕ, tr 5 5 (n + 2) ≤ 15 * 4 ^ n
  | 0 => by decide
  | (n + 1) => by
      have h := (tr_five_ratio (n + 1)).2.1
      have ih := tr_five_le n
      calc tr 5 5 (n + 1 + 2) ≤ 4 * tr 5 5 (n + 1 + 1) := h
        _ = 4 * tr 5 5 (n + 2) := rfl
        _ ≤ 4 * (15 * 4 ^ n) := by linarith
        _ = 15 * 4 ^ (n + 1) := by ring

/-- Local weights at `5^n` (units of `log 5`) of the literal hybrid: `1 + N_n(5,-5)`. -/
def wLit (n : ℕ) : ℤ := 1 + N 5 (-5) n

/-- The literal hybrid has positive weights at 5 (and zeta's weights elsewhere). -/
theorem wLit_pos (n : ℕ) : 2 ≤ wLit (n + 1) := by
  unfold wLit; linarith [N_anti_pos n]

/-- Local weights at `5^n` of the repaired hybrid `H4`: `1 + 4^n - t_n(5,-5)`. -/
def w4 (n : ℕ) : ℤ := 1 + 4 ^ n - tr 5 (-5) n

/-- **The repaired hybrid has positive von Mangoldt weights at 5, every `n`.** -/
theorem w4_pos (n : ℕ) : 1 ≤ w4 (n + 1) := by
  unfold w4
  rw [tr_neg]
  cases n with
  | zero => decide
  | succ n =>
      have h1 := tr_five_le n
      have h2 := (tr_five_ratio (n + 1)).2.2
      have h4 : (0 : ℤ) ≤ 4 ^ n := by positivity
      have e : (4 : ℤ) ^ (n + 1 + 1) = 16 * 4 ^ n := by ring
      have e2 : tr 5 5 (n + 1 + 1) = tr 5 5 (n + 2) := rfl
      rw [e, e2]
      rcases neg_one_pow_eq_or ℤ (n + 1 + 1) with h | h <;> rw [h] <;> nlinarith

/-- **Ramanujan fails at 5 for `H4`**: `Lambda(5^(2j+2)) >= (1 + 4^(2j)) log 5`, i.e. the weights
grow like `5^(0.86 k)`, beyond any bound `O(p^(k theta))`, `theta < 1/2`. -/
theorem w4_even_ge (j : ℕ) : 1 + 4 ^ (2 * j) ≤ w4 (2 * j + 2) := by
  unfold w4
  have hsign : ((-1 : ℤ)) ^ (2 * j + 2) = 1 := by
    rw [show 2 * j + 2 = 2 * (j + 1) by ring, pow_mul]; norm_num
  rw [tr_neg, hsign, one_mul]
  have h1 := tr_five_le (2 * j)
  have e : (4 : ℤ) ^ (2 * j + 2) = 16 * 4 ^ (2 * j) := by ring
  rw [e]
  linarith

/-- `T(s) = 5^(-s)`. -/
noncomputable def T5 (s : ℂ) : ℂ := (5 : ℂ) ^ (-s)

lemma T5_continuous : Continuous T5 := by
  unfold T5; exact continuous_neg.const_cpow (Or.inl (by norm_num))

lemma T5_one : T5 1 = 1 / 5 := by
  unfold T5; rw [Complex.cpow_neg_one]; norm_num

lemma T5_hasDerivAt (s : ℂ) : HasDerivAt T5 (-(T5 s * Complex.log 5)) s := by
  have h := (hasDerivAt_neg s).const_cpow (c := (5 : ℂ)) (Or.inl (by norm_num))
  unfold T5
  exact h.congr_deriv (by ring)

lemma log5C_ne : Complex.log 5 ≠ 0 := by
  rw [show (5 : ℂ) = ((5 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_log (by norm_num)]
  exact_mod_cast (ne_of_gt log5_pos)

/-- `(s - s0)/(1 - c T(s)) -> 1 / log 5` at a zero `s0` of `1 - c T`. -/
lemma tendsto_div_one_sub (c s0 : ℂ) (h : c * T5 s0 = 1) :
    Filter.Tendsto (fun s => (s - s0) / (1 - c * T5 s)) (nhdsWithin s0 {s0}ᶜ)
      (nhds (Complex.log 5)⁻¹) := by
  set f : ℂ → ℂ := fun s => 1 - c * T5 s with hf
  have hd : HasDerivAt f (Complex.log 5) s0 := by
    have := ((T5_hasDerivAt s0).const_mul c).const_sub 1
    refine this.congr_deriv ?_
    linear_combination (Complex.log 5) * h
  have hs := (hasDerivAt_iff_tendsto_slope.mp hd).inv₀ log5C_ne
  refine hs.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs0
  have hf0 : f s0 = 0 := by simp only [hf]; rw [h]; ring
  rw [slope_def_field, hf0, sub_zero, inv_div]

/-- The literal hybrid of the proposal, `zeta(s) Z_{5,-5}(5^(-s))`. -/
noncomputable def Hlit (s : ℂ) : ℂ :=
  riemannZeta s * ((1 + 5 * T5 s + 5 * T5 s ^ 2) / ((1 - T5 s) * (1 - 5 * T5 s)))

/-- **CORRECTION: the literal hybrid has a DOUBLE pole at `s = 1`**, with leading coefficient
`11 / (4 log 5)`. -/
theorem Hlit_double_pole :
    Filter.Tendsto (fun s => (s - 1) ^ 2 * Hlit s) (nhdsWithin 1 {1}ᶜ)
      (nhds (11 / 4 * (Complex.log 5)⁻¹)) := by
  have hG : ContinuousAt (fun s => (1 + 5 * T5 s + 5 * T5 s ^ 2) / (1 - T5 s)) 1 := by
    have := T5_continuous
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · rw [T5_one]; norm_num
  have hG1 : (1 + 5 * T5 1 + 5 * T5 1 ^ 2) / (1 - T5 1) = 11 / 4 := by
    rw [T5_one]; norm_num
  have h5 : 5 * T5 1 = 1 := by rw [T5_one]; norm_num
  have hlim := (riemannZeta_residue_one.mul
    ((hG.tendsto.mono_left nhdsWithin_le_nhds))).mul (tendsto_div_one_sub 5 1 h5)
  rw [hG1, one_mul] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  unfold Hlit
  rcases eq_or_ne (1 - T5 s) 0 with h0 | h0
  · rw [h0]; simp
  · rcases eq_or_ne (1 - 5 * T5 s) 0 with h0' | h0'
    · rw [h0']; simp
    · field_simp

/-- Consequently the literal hybrid has NO simple pole at `s = 1`: `(s - 1) H(s)` has no limit. -/
theorem Hlit_not_simple_pole :
    ¬ ∃ L : ℂ, Filter.Tendsto (fun s => (s - 1) * Hlit s) (nhdsWithin 1 {1}ᶜ) (nhds L) := by
  rintro ⟨L, hL⟩
  have h0 : Filter.Tendsto (fun s : ℂ => s - 1) (nhdsWithin 1 {1}ᶜ) (nhds 0) := by
    have : Filter.Tendsto (fun s : ℂ => s - 1) (nhds 1) (nhds (1 - 1)) :=
      (continuous_id.sub continuous_const).tendsto 1
    rw [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h2 := h0.mul hL
  rw [zero_mul] at h2
  have h3 : Filter.Tendsto (fun s => (s - 1) ^ 2 * Hlit s) (nhdsWithin 1 {1}ᶜ) (nhds 0) := by
    refine h2.congr' (Filter.Eventually.of_forall fun s => ?_)
    ring
  have := tendsto_nhds_unique h3 Hlit_double_pole
  have hne : (11 / 4 : ℂ) * (Complex.log 5)⁻¹ ≠ 0 :=
    mul_ne_zero (by norm_num) (inv_ne_zero log5C_ne)
  exact hne this.symm

/-- The repaired hybrid `H4(s) = zeta(s) (1 + 5 * 5^(-s) + 5 * 5^(-2s)) / (1 - 4 * 5^(-s))`. -/
noncomputable def H4 (s : ℂ) : ℂ :=
  riemannZeta s * ((1 + 5 * T5 s + 5 * T5 s ^ 2) / (1 - 4 * T5 s))

/-- **The repaired hybrid has a SIMPLE pole at `s = 1` with residue `11`.** -/
theorem H4_simple_pole :
    Filter.Tendsto (fun s => (s - 1) * H4 s) (nhdsWithin 1 {1}ᶜ) (nhds 11) := by
  have hG : ContinuousAt (fun s => (1 + 5 * T5 s + 5 * T5 s ^ 2) / (1 - 4 * T5 s)) 1 := by
    have := T5_continuous
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · rw [T5_one]; norm_num
  have hG1 : (1 + 5 * T5 1 + 5 * T5 1 ^ 2) / (1 - 4 * T5 1) = 11 := by
    rw [T5_one]; norm_num
  have hlim := riemannZeta_residue_one.mul (hG.tendsto.mono_left nhdsWithin_le_nhds)
  rw [hG1, one_mul] at hlim
  refine hlim.congr' (Filter.Eventually.of_forall fun s => ?_)
  unfold H4
  ring

/-- The real point `s0 = log 4 / log 5`. -/
noncomputable def s4 : ℝ := Real.log 4 / Real.log 5

lemma s4_mem : 1 / 2 < s4 ∧ s4 < 1 := by
  have h5 := log5_pos
  unfold s4
  constructor
  · rw [lt_div_iff₀ h5]
    have : Real.log 5 < Real.log 4 * 2 := by
      rw [show Real.log 4 * 2 = Real.log (4 ^ 2) by rw [Real.log_pow]; push_cast; ring]
      exact Real.log_lt_log (by norm_num) (by norm_num)
    linarith
  · rw [div_lt_one h5]; exact Real.log_lt_log (by norm_num) (by norm_num)

lemma T5_s4 : T5 (s4 : ℂ) = 1 / 4 := by
  unfold T5
  rw [show (5 : ℂ) = ((5 : ℝ) : ℂ) by norm_num, show -((s4 : ℝ) : ℂ) = ((-s4 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (by norm_num)]
  rw [Real.rpow_def_of_pos (by norm_num), s4]
  have h5 : Real.log 5 ≠ 0 := ne_of_gt log5_pos
  rw [show Real.log 5 * -(Real.log 4 / Real.log 5) = -Real.log 4 by field_simp, Real.exp_neg,
    Real.exp_log (by norm_num)]
  push_cast; ring

/-- **The repaired hybrid pays with a pole inside the strip**: a simple pole at the real point
`log 4 / log 5 in (1/2, 1)`, residue `zeta(s0) (41/16) / log 5 != 0`. -/
theorem H4_pole_in_strip :
    Filter.Tendsto (fun s => (s - s4) * H4 s) (nhdsWithin (s4 : ℂ) {(s4 : ℂ)}ᶜ)
      (nhds (riemannZeta s4 * (41 / 16) * (Complex.log 5)⁻¹)) ∧
      riemannZeta s4 * (41 / 16) * (Complex.log 5)⁻¹ ≠ 0 := by
  have hs := s4_mem
  have hz : riemannZeta (s4 : ℂ) ≠ 0 :=
    LowHeightBox.riemannZeta_ne_zero_of_unit_interval s4 (by linarith) hs.2
  constructor
  · have hc : (4 : ℂ) * T5 s4 = 1 := by rw [T5_s4]; norm_num
    have hZ : ContinuousAt riemannZeta (s4 : ℂ) := by
      apply (differentiableAt_riemannZeta ?_).continuousAt
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hP : ContinuousAt (fun s => 1 + 5 * T5 s + 5 * T5 s ^ 2) (s4 : ℂ) := by
      have := T5_continuous; fun_prop
    have hP1 : 1 + 5 * T5 (s4 : ℂ) + 5 * T5 (s4 : ℂ) ^ 2 = 41 / 16 := by
      rw [T5_s4]; norm_num
    have hlim := ((hZ.tendsto.mul hP.tendsto).mono_left nhdsWithin_le_nhds).mul
      (tendsto_div_one_sub 4 s4 hc)
    rw [hP1] at hlim
    refine hlim.congr' (Filter.Eventually.of_forall fun s => ?_)
    unfold H4
    ring
  · exact mul_ne_zero (mul_ne_zero hz (by norm_num)) (inv_ne_zero log5C_ne)

/-! ## 9. Limitations: what separates zeta from every lattice fake

(a) POLE SHADOW.  In an Euler product, a local factor `P_{q,m}(T)/prod_j (1 - delta_j T)` at a
prime power `q` (`T = q^(-s)`) contributes the weight `C + sum_j delta_j^n - t_n` at `q^n` (`C`: the
other factors' weight there, e.g. `C = 1` for zeta).  Its poles lie on `Re s = log|delta_j|/log q`,
its off-line zero on `Re s = log alpha / log q` (`alpha` the larger root).  If every pole is strictly
left of the zero, some weight is negative.  So `Lambda >= 0` forces a pole at least as far right as
the zero, and with no poles of the local factor in `Re s > 1/2` it forces local RH.

(b) LATTICE.  Every zero of a polynomial local factor at `p` recurs with period `2 pi i / log p`, so
some copy lies at height `<= pi / log p <= pi / log 2 < 4.54`; every RH-violating genus-one datum
has an off-line zero in the open strip at height `<= pi / log q`; the golden hybrid has one in the
corpus's certified box `[0.001, 0.999] x [0, 55/16]`. -/

/-- The larger root of `x^2 - |m| x + q`. -/
noncomputable def bigRoot (q m : ℤ) : ℝ := (|(m : ℝ)| + Real.sqrt ((m : ℝ) ^ 2 - 4 * q)) / 2

lemma tr_even_ge (q m : ℤ) (hD : 4 * q < m ^ 2) (j : ℕ) :
    bigRoot q m ^ (2 * j) ≤ (tr q m (2 * j) : ℝ) := by
  have hDa : 4 * q < |m| ^ 2 := by rw [sq_abs]; exact hD
  obtain ⟨α, β, hs, hp, hα, hβ⟩ := real_roots q |m| hDa
  have hrep := (tr_real_rep q |m| α β hs hp (2 * j)).1
  have htr : tr q m (2 * j) = tr q |m| (2 * j) := by
    rcases abs_choice m with h | h
    · rw [h]
    · rw [h, tr_neg, pow_mul]; norm_num
  have hαeq : α = bigRoot q m := by
    rw [hα, bigRoot]; push_cast; rw [sq_abs]
  rw [htr, hrep, ← hαeq]
  have : 0 ≤ β ^ (2 * j) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg β) j
  linarith

lemma bigRoot_gt (q m : ℤ) (hq : 2 ≤ q) (hD : 4 * q < m ^ 2) :
    Real.sqrt q < bigRoot q m ∧ 1 < bigRoot q m := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hDR : 4 * (q : ℝ) < (m : ℝ) ^ 2 := by exact_mod_cast hD
  have hsq : Real.sqrt q ^ 2 = q := Real.sq_sqrt (by linarith)
  have hs0 : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
  have hm : 2 * Real.sqrt q < |(m : ℝ)| := by
    have h1 : (2 * Real.sqrt q) ^ 2 < |(m : ℝ)| ^ 2 := by rw [sq_abs]; nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (abs_nonneg _) h1
  have hr : 0 ≤ Real.sqrt ((m : ℝ) ^ 2 - 4 * q) := Real.sqrt_nonneg _
  have hs1 : 1 < Real.sqrt q := by
    rw [Real.lt_sqrt (by norm_num)]; linarith
  unfold bigRoot
  constructor <;> linarith

/-- An auxiliary growth fact: if `0 <= b < a` and `1 < a`, then `C + k b^j < a^j` for some `j >= 1`. -/
lemma exists_pow_dominates (a b C : ℝ) (k : ℕ) (hb0 : 0 ≤ b) (hba : b < a) (ha : 1 < a) :
    ∃ j : ℕ, 1 ≤ j ∧ C + k * b ^ j < a ^ j := by
  have ha0 : 0 < a := by linarith
  have hr0 : 0 ≤ b / a := div_nonneg hb0 ha0.le
  have hr1 : b / a < 1 := by rw [div_lt_one ha0]; exact hba
  have hε : (0 : ℝ) < 1 / (2 * (k + 1)) := by positivity
  have e1 := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).eventually (gt_mem_nhds hε)
  have e2 := (tendsto_pow_atTop_atTop_of_one_lt ha).eventually_gt_atTop (2 * (|C| + 1))
  obtain ⟨j, hj2, hj3, hj1⟩ := (e1.and (e2.and (Filter.eventually_ge_atTop 1))).exists
  refine ⟨j, hj1, ?_⟩
  have hapos : 0 < a ^ j := pow_pos ha0 j
  have hbj : b ^ j = (b / a) ^ j * a ^ j := by
    rw [div_pow]; field_simp
  have hk : (k : ℝ) * (b / a) ^ j ≤ 1 / 2 := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have : (k : ℝ) * (b / a) ^ j ≤ k * (1 / (2 * (k + 1))) :=
      mul_le_mul_of_nonneg_left hj2.le hk0
    have h2 : (k : ℝ) * (1 / (2 * (k + 1))) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  have hC : C < a ^ j / 2 := by have := le_abs_self C; linarith
  calc C + k * b ^ j = C + (k * (b / a) ^ j) * a ^ j := by rw [hbj]; ring
    _ ≤ C + (1 / 2) * a ^ j := by gcongr
    _ < a ^ j := by linarith

/-- **POLE SHADOW (genus one).**  Let `2 <= q`, `4q < m^2` (an off-line local zero).  If every inverse
pole `delta_j` of the local denominator satisfies `|delta_j| <= R < alpha` (every pole strictly left
of the zero), then for every constant `C` some local weight `C + Re(sum_j delta_j^n) - t_n` with
`n >= 1` is NEGATIVE. -/
theorem pole_shadow (q m : ℤ) (hq : 2 ≤ q) (hD : 4 * q < m ^ 2) {k : ℕ} (δ : Fin k → ℂ) (R : ℝ)
    (hR0 : 0 ≤ R) (hR : ∀ j, ‖δ j‖ ≤ R) (hRα : R < bigRoot q m) (C : ℝ) :
    ∃ n : ℕ, 1 ≤ n ∧ C + (∑ j, δ j ^ n).re - tr q m n < 0 := by
  have hα1 := (bigRoot_gt q m hq hD).2
  set α := bigRoot q m
  have hb0 : 0 ≤ R ^ 2 := sq_nonneg R
  have hba : R ^ 2 < α ^ 2 := by nlinarith
  have ha1 : 1 < α ^ 2 := by nlinarith
  obtain ⟨j, hj1, hj⟩ := exists_pow_dominates (α ^ 2) (R ^ 2) C k hb0 hba ha1
  refine ⟨2 * j, by omega, ?_⟩
  have hsum : (∑ i, δ i ^ (2 * j)).re ≤ k * R ^ (2 * j) := by
    calc (∑ i, δ i ^ (2 * j)).re ≤ ‖∑ i, δ i ^ (2 * j)‖ := Complex.re_le_norm _
      _ ≤ ∑ i, ‖δ i ^ (2 * j)‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin k, R ^ (2 * j) := by
          apply Finset.sum_le_sum
          intro i _
          rw [norm_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) (hR i) _
      _ = k * R ^ (2 * j) := by simp
  have htr := tr_even_ge q m hD j
  have e1 : R ^ (2 * j) = (R ^ 2) ^ j := by rw [pow_mul]
  have e2 : α ^ (2 * j) = (α ^ 2) ^ j := by rw [pow_mul]
  rw [e1] at hsum
  rw [e2] at htr
  linarith

/-- **Local RH from positivity and the pole axiom.**  If the local weights at `q^n` are nonnegative
for every `n >= 1` and the local factor has no pole in `Re s > 1/2` (`|delta_j| <= sqrt q`), then the
local factor satisfies RH: `m^2 <= 4q`.  So every golden-type fake needs a pole of the local factor
in `Re s > 1/2` -- which `zeta` (holomorphic there except `s = 1`) does not have. -/
theorem local_rh_of_positivity (q m : ℤ) (hq : 2 ≤ q) {k : ℕ} (δ : Fin k → ℂ)
    (hpole : ∀ j, ‖δ j‖ ≤ Real.sqrt q) (C : ℝ)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 ≤ C + (∑ j, δ j ^ n).re - tr q m n) : m ^ 2 ≤ 4 * q := by
  by_contra hD
  rw [not_le] at hD
  obtain ⟨n, hn, hneg⟩ := pole_shadow q m hq hD δ (Real.sqrt q) (Real.sqrt_nonneg _) hpole
    (bigRoot_gt q m hq hD).1 C
  linarith [hpos n hn]

/-- The golden hybrid through the pole shadow: the larger inverse root of `1 + 5T + 5T^2` is
`(5 + sqrt 5)/2 in (3, 4)`, so positivity forces a local pole of modulus `>= 3.618...`, i.e. at
`Re s >= log((5 + sqrt 5)/2)/log 5 = 0.799...` (the real part of the off-line zero).  The literal
hybrid's pole has modulus `5` (`Re s = 1`, the double pole), the repaired one's modulus `4`
(`Re s = 0.861`, `H4_pole_in_strip`); numerically the least admissible modulus is `sqrt 14`
(research/crux_meta-barriers N8). -/
theorem golden_pole_modulus_forced : bigRoot 5 (-5) < 4 ∧ 3 < bigRoot 5 (-5) := by
  unfold bigRoot
  have h := sqrt5_bounds
  have e : Real.sqrt ((((-5 : ℤ) : ℝ)) ^ 2 - 4 * ((5 : ℤ) : ℝ)) = Real.sqrt 5 := by norm_num
  rw [e]
  norm_num
  constructor <;> linarith

/-- Every zero of a polynomial local factor at `p` recurs with period `2 pi i / log p`. -/
theorem local_factor_periodic (P : Polynomial ℂ) (p : ℝ) (hp : 1 < p) (s : ℂ) (k : ℤ) :
    P.eval ((p : ℂ) ^ (-(s + ((2 * Real.pi * k / Real.log p : ℝ) : ℂ) * I)))
      = P.eval ((p : ℂ) ^ (-s)) := by
  congr 1
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (by linarith : (0 : ℝ) < p))
  have hlog : Complex.log (p : ℂ) = (Real.log p : ℂ) := (Complex.ofReal_log (by linarith)).symm
  have hL : (Real.log p : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Real.log_pos hp))
  rw [Complex.cpow_def_of_ne_zero hp0, Complex.cpow_def_of_ne_zero hp0, hlog]
  have : (Real.log p : ℂ) * -(s + ((2 * Real.pi * k / Real.log p : ℝ) : ℂ) * I)
      = (Real.log p : ℂ) * -s + ((-k : ℤ) : ℂ) * (2 * Real.pi * I) := by
    push_cast; field_simp; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Every point has a vertical translate by the lattice `2 pi i Z / L` of height `<= pi / L`. -/
theorem exists_low_translate (s : ℂ) (L : ℝ) (hL : 0 < L) :
    ∃ k : ℤ, |(s + ((2 * Real.pi * k / L : ℝ) : ℂ) * I).im| ≤ Real.pi / L ∧
      (s + ((2 * Real.pi * k / L : ℝ) : ℂ) * I).re = s.re := by
  set x : ℝ := -(s.im * L / (2 * Real.pi)) with hx
  refine ⟨round x, ?_, by simp⟩
  have hpi := Real.pi_pos
  have him : (s + ((2 * Real.pi * (round x : ℤ) / L : ℝ) : ℂ) * I).im
      = (2 * Real.pi / L) * ((round x : ℝ) - x) := by
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one]
    rw [hx]; field_simp; ring
  rw [him, abs_mul, abs_of_pos (by positivity), abs_sub_comm]
  have := abs_sub_round x
  calc 2 * Real.pi / L * |x - (round x : ℝ)| ≤ 2 * Real.pi / L * (1 / 2) := by gcongr
    _ = Real.pi / L := by ring

/-- **Every zero of a polynomial local factor at a prime `p >= 2` has a copy with the same real part
at height `<= pi / log 2 < 4.54`.**  So an RH-violating local factor always shows an off-line zero
below height `4.54`.  A certificate "every zero with `|Im| <= T` is on the line", `T >= 4.54`
(the corpus has such certificates for zeta, Arb-conditional, up to height 4000; the first zeta
zero is at `14.13`), therefore FAILS for every lattice fake whose local zeros survive in the
completion: finite certification separates zeta from the whole lattice family. -/
theorem local_zero_low_copy (P : Polynomial ℂ) (p : ℝ) (hp : 2 ≤ p) (s : ℂ)
    (hs : P.eval ((p : ℂ) ^ (-s)) = 0) :
    ∃ s' : ℂ, P.eval ((p : ℂ) ^ (-s')) = 0 ∧ s'.re = s.re ∧ |s'.im| ≤ Real.pi / Real.log 2 := by
  have hL : 0 < Real.log p := Real.log_pos (by linarith)
  obtain ⟨k, hk1, hk2⟩ := exists_low_translate s (Real.log p) hL
  refine ⟨_, by rw [local_factor_periodic P p (by linarith) s k]; exact hs, hk2, ?_⟩
  refine hk1.trans ?_
  apply div_le_div_of_nonneg_left Real.pi_pos.le (Real.log_pos (by norm_num))
  exact Real.log_le_log (by norm_num) hp

lemma pi_div_log2_lt : Real.pi / Real.log 2 < 4.54 := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.pi_lt_d4
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

/-- **Every RH-violating admissible genus-one datum has an off-line zero in the open strip at height
`<= pi / log q`.** -/
theorem genus_one_low_offline_zero (q m : ℤ) (hq : 2 ≤ q) (hm1 : -q ≤ m) (hm2 : m ≤ q)
    (hD : 4 * q < m ^ 2) :
    ∃ s : ℂ, Xi (Real.log q) ((m : ℝ) / Real.sqrt q) s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧
      s.re ≠ 1 / 2 ∧ 0 ≤ s.im ∧ s.im ≤ Real.pi / Real.log q := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hL : 0 < Real.log q := Real.log_pos (by linarith)
  have ht0 : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have ht2 : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq0.le
  have hDR : 4 * (q : ℝ) < (m : ℝ) ^ 2 := by exact_mod_cast hD
  have habs : |(m : ℝ)| ≤ q := by
    have h1 : (-(q : ℝ)) ≤ m := by exact_mod_cast hm1
    have h2 : (m : ℝ) ≤ q := by exact_mod_cast hm2
    exact abs_le.mpr ⟨h1, h2⟩
  have hc : 2 < |(m : ℝ) / Real.sqrt q| := by
    rw [abs_div, abs_of_pos ht0, lt_div_iff₀ ht0]
    have h1 : (2 * Real.sqrt q) ^ 2 < |(m : ℝ)| ^ 2 := by rw [sq_abs]; nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (abs_nonneg _) h1
  obtain ⟨x, hx0, hcx, s, hs, hre, him⟩ := offline_zero_explicit (Real.log q) _ hL hc
  -- x < log q / 2 because cosh x = |m|/(2 sqrt q) <= sqrt q / 2 < cosh (log sqrt q)
  have hxL : x < Real.log q / 2 := by
    have hlogs : Real.log (Real.sqrt q) = Real.log q / 2 := by
      rw [Real.log_sqrt hq0.le]
    have hcs : Real.cosh (Real.log (Real.sqrt q)) = (Real.sqrt q + (Real.sqrt q)⁻¹) / 2 :=
      Real.cosh_log ht0
    have hlt : Real.cosh x < Real.cosh (Real.log q / 2) := by
      rw [hcx, ← hlogs, hcs, abs_div, abs_of_pos ht0]
      have h1 : |(m : ℝ)| / Real.sqrt q ≤ Real.sqrt q := by
        rw [div_le_iff₀ ht0]; nlinarith
      have h2 : 0 < (Real.sqrt q)⁻¹ := inv_pos.mpr ht0
      linarith
    rw [Real.cosh_lt_cosh, abs_of_pos hx0, abs_of_pos (by positivity)] at hlt
    exact hlt
  refine ⟨s, hs, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hre]; have : 0 < x / Real.log q := div_pos hx0 hL; linarith
  · rw [hre]
    have : x / Real.log q < 1 / 2 := by rw [div_lt_iff₀ hL]; linarith
    linarith
  · rw [hre]; have : 0 < x / Real.log q := div_pos hx0 hL; intro h; linarith
  · rcases him with h | h
    · linarith
    · have := div_pos Real.pi_pos hL; linarith
  · rcases him with h | h
    · have := div_pos Real.pi_pos hL; linarith
    · linarith

/-- **The golden hybrid violates the corpus's certified zero-free box**
`[0.001, 0.999] x [0, 55/16]` (for zeta that box is the Arb-conditional
`NoZerosInBox_1d1000_999d1000_0_55d16.no_zeros_in_box_1d1000_999d1000_0_55d16`): finite
certification separates zeta from the hybrid. -/
theorem hybrid_zero_in_certified_box :
    ∃ ρ : ℂ, XiH ρ = 0 ∧ ρ.re ≠ 1 / 2 ∧ 1 / 1000 ≤ ρ.re ∧ ρ.re ≤ 999 / 1000 ∧
      0 ≤ ρ.im ∧ ρ.im ≤ 55 / 16 :=
  ⟨fakeZero 0 1, XiH_offline_zero.1, XiH_offline_zero.2, fakeZero_in_box⟩

/-! ## 10. `XiH` is the completion of BOTH Dirichlet series

`XiH = gamma * H` with an explicit (non-`Gamma_R`) factor `gamma`: this is the class clause
"entire order-one completion, `gamma` NOT required to be `Gamma_R`".  For `H4` the factor
`gamma` has zeros INSIDE the strip (at `1 - 4 * 5^(-s) = 0`, i.e. `Re s = log 4 / log 5`): that is
how the completion absorbs the in-strip pole of `H4`. -/

lemma cpow5 (z : ℂ) : (5 : ℂ) ^ z = Complex.exp (z * (Real.log 5 : ℝ)) := by
  rw [Complex.cpow_def_of_ne_zero (by norm_num), show (5 : ℂ) = ((5 : ℝ) : ℂ) by norm_num,
    ← Complex.ofReal_log (by norm_num), mul_comm]

lemma exp_neg_half_log5 : Real.exp (-Real.log 5 / 2) = (Real.sqrt 5)⁻¹ := by
  rw [neg_div, Real.exp_neg, Real.exp_half, Real.exp_log (by norm_num)]

/-- `XiA s = 5^(s - 1/2) (1 + 5 T + 5 T^2)`, `T = 5^(-s)`. -/
theorem XiA_eq_P5 (s : ℂ) :
    XiA s = (5 : ℂ) ^ (s - 1 / 2) * (1 + 5 * T5 s + 5 * T5 s ^ 2) := by
  have h := Xi_eq_P (Real.log 5) (-5) s
  have hc : (-5 : ℝ) * Real.exp (-Real.log 5 / 2) = -Real.sqrt 5 := by
    rw [exp_neg_half_log5]
    have h5 : Real.sqrt 5 ≠ 0 := by positivity
    field_simp
    linarith [sqrt5_sq]
  rw [hc] at h
  unfold XiA
  rw [← h, cpow5, T5, cpow5]
  have he : Complex.exp ((Real.log 5 : ℝ) : ℂ) = 5 := by
    rw [← Complex.ofReal_exp, Real.exp_log (by norm_num)]; push_cast; ring
  rw [he]
  push_cast
  ring_nf

/-- The explicit completion factor of the repaired hybrid (zeros inside the strip). -/
noncomputable def gammaH4 (s : ℂ) : ℂ :=
  (1 / 2) * s * (s - 1) * Complex.Gammaℝ s * (5 : ℂ) ^ (s - 1 / 2) * (1 - 4 * T5 s)

/-- The explicit completion factor of the literal hybrid. -/
noncomputable def gammaLit (s : ℂ) : ℂ :=
  (1 / 2) * s * (s - 1) * Complex.Gammaℝ s * (5 : ℂ) ^ (s - 1 / 2) * ((1 - T5 s) * (1 - 5 * T5 s))

lemma xi_eq_gamma_zeta (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) :
    LiCriterion.riemannXi s = (1 / 2) * s * (s - 1) * (Complex.Gammaℝ s * riemannZeta s) := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  have hG : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hs
  have h1 : LiCriterion.riemannXi s = (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s :=
    XiZeros.xi_eq_half_s_sm1_Lambda hs0 hs1
  have h2 : riemannZeta s = completedRiemannZeta s / Complex.Gammaℝ s :=
    riemannZeta_def_of_ne_zero hs0
  rw [h1, h2]
  field_simp

/-- **`XiH` completes the repaired Dirichlet series**: `XiH = gammaH4 * H4` (where `H4` is finite). -/
theorem XiH_eq_completion_H4 (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) (hT : 1 - 4 * T5 s ≠ 0) :
    XiH s = gammaH4 s * H4 s := by
  unfold XiH gammaH4 H4
  rw [xi_eq_gamma_zeta s hs hs1, XiA_eq_P5]
  have key : (1 - 4 * T5 s) * ((1 + 5 * T5 s + 5 * T5 s ^ 2) / (1 - 4 * T5 s))
      = 1 + 5 * T5 s + 5 * T5 s ^ 2 := mul_div_cancel₀ _ hT
  linear_combination (-((1 / 2) * s * (s - 1) * Complex.Gammaℝ s * riemannZeta s
    * (5 : ℂ) ^ (s - 1 / 2))) * key

/-- **`XiH` completes the literal Dirichlet series as well**: `XiH = gammaLit * Hlit`. -/
theorem XiH_eq_completion_Hlit (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1)
    (hT : (1 - T5 s) * (1 - 5 * T5 s) ≠ 0) :
    XiH s = gammaLit s * Hlit s := by
  unfold XiH gammaLit Hlit
  rw [xi_eq_gamma_zeta s hs hs1, XiA_eq_P5]
  have key : ((1 - T5 s) * (1 - 5 * T5 s)) * ((1 + 5 * T5 s + 5 * T5 s ^ 2) / ((1 - T5 s) * (1 - 5 * T5 s)))
      = 1 + 5 * T5 s + 5 * T5 s ^ 2 := mul_div_cancel₀ _ hT
  linear_combination (-((1 / 2) * s * (s - 1) * Complex.Gammaℝ s * riemannZeta s
    * (5 : ℂ) ^ (s - 1 / 2))) * key

/-- `gammaH4` vanishes at the real point `log 4 / log 5` inside the strip. -/
theorem gammaH4_zero_in_strip : gammaH4 (s4 : ℂ) = 0 := by
  unfold gammaH4; rw [T5_s4]; ring

/-! ## 11. The certificate, in one statement -/

/-- **THE GOLDEN-FAKE BARRIER, with its corrections and its limits (kernel form).**

(i)   the hybrid completion `XiH` is entire, symmetric, conjugation-real, has an off-line zero;
(ii)  it satisfies the whole pointwise layer and the Li rungs `0..4` -- as zeta does;
(iii) the repaired Euler product `H4` has positive weights at 5, a simple pole at `1` with
      residue `11`, and `XiH` as its completion;
(iv)  CORRECTION: the proposal's literal Euler product has a double pole at `1`;
(v)   LIMITS: the positivity is paid for by a pole of `H4` inside the strip (forced, by
      `local_rh_of_positivity`), and the hybrid has an off-line zero inside the corpus's certified
      zero-free box. -/
theorem golden_fake_barrier :
    Differentiable ℂ XiH ∧ (∀ s, XiH (1 - s) = XiH s) ∧
    (∀ s, XiH (starRingEnd ℂ s) = starRingEnd ℂ (XiH s)) ∧
    (∃ ρ, XiH ρ = 0 ∧ ρ.re ≠ 1 / 2) ∧
    PointwiseLayer ZetaStripZero ∧ PointwiseLayer (fun ρ => XiH ρ = 0) ∧
    (∀ n : ℕ, n < 5 → 0 ≤ (hybridLi n).re) ∧
    (∀ n : ℕ, 1 ≤ w4 (n + 1)) ∧
    Filter.Tendsto (fun s => (s - 1) * H4 s) (nhdsWithin 1 {1}ᶜ) (nhds 11) ∧
    (¬ ∃ L : ℂ, Filter.Tendsto (fun s => (s - 1) * Hlit s) (nhdsWithin 1 {1}ᶜ) (nhds L)) ∧
    (1 / 2 < s4 ∧ s4 < 1 ∧ riemannZeta s4 * (41 / 16) * (Complex.log 5)⁻¹ ≠ 0 ∧
      Filter.Tendsto (fun s => (s - s4) * H4 s) (nhdsWithin (s4 : ℂ) {(s4 : ℂ)}ᶜ)
        (nhds (riemannZeta s4 * (41 / 16) * (Complex.log 5)⁻¹))) ∧
    (∃ ρ : ℂ, XiH ρ = 0 ∧ ρ.re ≠ 1 / 2 ∧ 1 / 1000 ≤ ρ.re ∧ ρ.re ≤ 999 / 1000 ∧
      0 ≤ ρ.im ∧ ρ.im ≤ 55 / 16) :=
  ⟨XiH_entire, XiH_one_sub, XiH_conj, ⟨_, XiH_offline_zero⟩, zeta_pointwiseLayer,
    hybrid_pointwiseLayer, hybrid_li_rungs, w4_pos, H4_simple_pole, Hlit_not_simple_pole,
    ⟨s4_mem.1, s4_mem.2, H4_pole_in_strip.2, H4_pole_in_strip.1⟩, hybrid_zero_in_certified_box⟩


end CruxMetaBarriers

#print axioms CruxMetaBarriers.tr_zero
#print axioms CruxMetaBarriers.tr_one
#print axioms CruxMetaBarriers.tr_succ_succ
#print axioms CruxMetaBarriers.tr_neg
#print axioms CruxMetaBarriers.lu_succ_succ
#print axioms CruxMetaBarriers.lu_norm
#print axioms CruxMetaBarriers.tr_eq_lu
#print axioms CruxMetaBarriers.lucas_identity
#print axioms CruxMetaBarriers.N_pos_of_disc_nonpos
#print axioms CruxMetaBarriers.tr_real_rep
#print axioms CruxMetaBarriers.real_roots
#print axioms CruxMetaBarriers.N_pos_real_pos
#print axioms CruxMetaBarriers.N_pos_of_abs_le
#print axioms CruxMetaBarriers.N_one
#print axioms CruxMetaBarriers.N_two
#print axioms CruxMetaBarriers.trivial_bound
#print axioms CruxMetaBarriers.admissible_iff
#print axioms CruxMetaBarriers.exists_admissible_not_rh_iff
#print axioms CruxMetaBarriers.rh_of_trivial_small_q
#print axioms CruxMetaBarriers.N_golden_pos
#print axioms CruxMetaBarriers.N_anti_pos
#print axioms CruxMetaBarriers.golden_violates_rh
#print axioms CruxMetaBarriers.euler_golden_1
#print axioms CruxMetaBarriers.euler_golden_2
#print axioms CruxMetaBarriers.euler_golden_3
#print axioms CruxMetaBarriers.euler_golden_4
#print axioms CruxMetaBarriers.euler_golden_5
#print axioms CruxMetaBarriers.euler_golden_6
#print axioms CruxMetaBarriers.euler_golden_7
#print axioms CruxMetaBarriers.euler_golden_8
#print axioms CruxMetaBarriers.euler_golden_9
#print axioms CruxMetaBarriers.euler_golden_10
#print axioms CruxMetaBarriers.euler_anti_1
#print axioms CruxMetaBarriers.euler_anti_2
#print axioms CruxMetaBarriers.euler_anti_3
#print axioms CruxMetaBarriers.euler_anti_4
#print axioms CruxMetaBarriers.euler_anti_5
#print axioms CruxMetaBarriers.euler_anti_6
#print axioms CruxMetaBarriers.euler_anti_7
#print axioms CruxMetaBarriers.euler_anti_8
#print axioms CruxMetaBarriers.euler_anti_9
#print axioms CruxMetaBarriers.euler_anti_10
#print axioms CruxMetaBarriers.Xi_symm
#print axioms CruxMetaBarriers.Xi_eq_P
#print axioms CruxMetaBarriers.cosh_decomp
#print axioms CruxMetaBarriers.rh_of_le_two
#print axioms CruxMetaBarriers.re_half_add
#print axioms CruxMetaBarriers.cosh_log_root
#print axioms CruxMetaBarriers.offline_zero_explicit
#print axioms CruxMetaBarriers.offline_zero
#print axioms CruxMetaBarriers.rh_iff
#print axioms CruxMetaBarriers.rh_int_iff_zeros
#print axioms CruxMetaBarriers.hasse_iff
#print axioms CruxMetaBarriers.det_A_sub
#print axioms CruxMetaBarriers.golden_negative_degree
#print axioms CruxMetaBarriers.A_sq
#print axioms CruxMetaBarriers.trace_A_pow
#print axioms CruxMetaBarriers.det_A
#print axioms CruxMetaBarriers.N_eq_det
#print axioms CruxMetaBarriers.formal_axioms_do_not_imply_rh
#print axioms CruxMetaBarriers.antiGolden_not_rh
#print axioms CruxMetaBarriers.sqrt5_sq
#print axioms CruxMetaBarriers.sqrt5_bounds
#print axioms CruxMetaBarriers.phi_pos
#print axioms CruxMetaBarriers.one_lt_phi
#print axioms CruxMetaBarriers.phi_lt
#print axioms CruxMetaBarriers.phi_sq
#print axioms CruxMetaBarriers.cosh_log_phi
#print axioms CruxMetaBarriers.log5_pos
#print axioms CruxMetaBarriers.log5_bounds
#print axioms CruxMetaBarriers.log_phi_pos
#print axioms CruxMetaBarriers.log_phi_lt
#print axioms CruxMetaBarriers.two_log_phi_lt_log5
#print axioms CruxMetaBarriers.x0_pos
#print axioms CruxMetaBarriers.x0_lt_half
#print axioms CruxMetaBarriers.x0_lt
#print axioms CruxMetaBarriers.pi_div_log5_bounds
#print axioms CruxMetaBarriers.fakeZero_re
#print axioms CruxMetaBarriers.fakeZero_im
#print axioms CruxMetaBarriers.cosh_w0
#print axioms CruxMetaBarriers.XiA_eq
#print axioms CruxMetaBarriers.w_of_fakeZero
#print axioms CruxMetaBarriers.XiA_fakeZero
#print axioms CruxMetaBarriers.XiA_eq_zero_iff
#print axioms CruxMetaBarriers.XiA_zero_simple
#print axioms CruxMetaBarriers.XiA_periodic
#print axioms CruxMetaBarriers.fakeZero_re_mem
#print axioms CruxMetaBarriers.fakeZero_re_ne_half
#print axioms CruxMetaBarriers.fakeZero_abs_re_sub_half
#print axioms CruxMetaBarriers.one_le_abs_two_mul_add_one
#print axioms CruxMetaBarriers.fakeZero_abs_im_ge
#print axioms CruxMetaBarriers.fakeZero_im_sq_ge
#print axioms CruxMetaBarriers.fakeZero_in_box
#print axioms CruxMetaBarriers.XiA_differentiable
#print axioms CruxMetaBarriers.XiA_one_sub
#print axioms CruxMetaBarriers.XiA_conj
#print axioms CruxMetaBarriers.XiH_entire
#print axioms CruxMetaBarriers.XiH_one_sub
#print axioms CruxMetaBarriers.XiH_conj
#print axioms CruxMetaBarriers.riemannXi_eq_zero_iff
#print axioms CruxMetaBarriers.XiH_eq_zero_iff
#print axioms CruxMetaBarriers.XiH_offline_zero
#print axioms CruxMetaBarriers.dlvpRateC_le
#print axioms CruxMetaBarriers.sqrt3_half_pos
#print axioms CruxMetaBarriers.sqrt3_half_lt
#print axioms CruxMetaBarriers.zeta_dvp
#print axioms CruxMetaBarriers.zeta_pointwiseLayer
#print axioms CruxMetaBarriers.fake_box2
#print axioms CruxMetaBarriers.fake_liDisk
#print axioms CruxMetaBarriers.fake_dvp
#print axioms CruxMetaBarriers.one_sub_fakeZero
#print axioms CruxMetaBarriers.conj_fakeZero
#print axioms CruxMetaBarriers.hybrid_pointwiseLayer
#print axioms CruxMetaBarriers.pointwise_layer_does_not_imply_rh
#print axioms CruxMetaBarriers.ne_zero_one_of_liDisk
#print axioms CruxMetaBarriers.zOf_eq'
#print axioms CruxMetaBarriers.pairTerm_eq_Q
#print axioms CruxMetaBarriers.zOf_mem_disk'
#print axioms CruxMetaBarriers.pairTerm_re_nonneg
#print axioms CruxMetaBarriers.norm_Q_le
#print axioms CruxMetaBarriers.norm_zOf_le
#print axioms CruxMetaBarriers.fake_re_mul_ge
#print axioms CruxMetaBarriers.summable_inv_odd_sq
#print axioms CruxMetaBarriers.summable_fake_pairTerm
#print axioms CruxMetaBarriers.hybrid_li_rungs
#print axioms CruxMetaBarriers.tr_five_ratio
#print axioms CruxMetaBarriers.tr_five_le
#print axioms CruxMetaBarriers.wLit_pos
#print axioms CruxMetaBarriers.w4_pos
#print axioms CruxMetaBarriers.w4_even_ge
#print axioms CruxMetaBarriers.T5_continuous
#print axioms CruxMetaBarriers.T5_one
#print axioms CruxMetaBarriers.T5_hasDerivAt
#print axioms CruxMetaBarriers.log5C_ne
#print axioms CruxMetaBarriers.tendsto_div_one_sub
#print axioms CruxMetaBarriers.Hlit_double_pole
#print axioms CruxMetaBarriers.Hlit_not_simple_pole
#print axioms CruxMetaBarriers.H4_simple_pole
#print axioms CruxMetaBarriers.s4_mem
#print axioms CruxMetaBarriers.T5_s4
#print axioms CruxMetaBarriers.H4_pole_in_strip
#print axioms CruxMetaBarriers.tr_even_ge
#print axioms CruxMetaBarriers.bigRoot_gt
#print axioms CruxMetaBarriers.exists_pow_dominates
#print axioms CruxMetaBarriers.pole_shadow
#print axioms CruxMetaBarriers.local_rh_of_positivity
#print axioms CruxMetaBarriers.golden_pole_modulus_forced
#print axioms CruxMetaBarriers.local_factor_periodic
#print axioms CruxMetaBarriers.exists_low_translate
#print axioms CruxMetaBarriers.local_zero_low_copy
#print axioms CruxMetaBarriers.pi_div_log2_lt
#print axioms CruxMetaBarriers.genus_one_low_offline_zero
#print axioms CruxMetaBarriers.hybrid_zero_in_certified_box
#print axioms CruxMetaBarriers.cpow5
#print axioms CruxMetaBarriers.exp_neg_half_log5
#print axioms CruxMetaBarriers.XiA_eq_P5
#print axioms CruxMetaBarriers.xi_eq_gamma_zeta
#print axioms CruxMetaBarriers.XiH_eq_completion_H4
#print axioms CruxMetaBarriers.XiH_eq_completion_Hlit
#print axioms CruxMetaBarriers.gammaH4_zero_in_strip
#print axioms CruxMetaBarriers.golden_fake_barrier
