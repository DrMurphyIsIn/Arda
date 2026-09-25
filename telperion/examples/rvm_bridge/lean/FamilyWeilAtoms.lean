/-
  FamilyWeilAtoms -- the constants layer of the atoms n = 2, 3, 4, 5 and the per-cell coefficient
  tables (Stage 1a of the quadratic-family programme, 2026-09-25).

  CONSTANTS (kernel-checkable: norm_num on the finite partial sums, decide on Nat/Int; no Rat
  kernel reduction):
    * log2_series_bound / log3_series_bound / log5_series_bound: the Taylor series of
      -log(1 - x) at x = 1/2, 1/3, 1/5 (Mathlib's Real.abs_log_sub_add_sum_range_le), so
      log 3 = log 2 + Σ 3^{-n}/n and log 5 = 2 log 2 + Σ 5^{-n}/n with explicit tails
      (2^-60, 3^-42/2, 5^-30/4);
    * log43_series_bound: the pilot's form log 3 = 2 log 2 - Σ_{n<=40} 4^{-n}/n, tail 4^{-40}/3;
    * log2_bounds (19 digits, width 1.8e-18) / log3_bounds (19 digits, width 1.9e-18) /
      log5_bounds (17 digits): rational enclosures;
    * sqrt2_bounds / sqrt3_bounds / sqrt5_bounds: 20-digit rationals squeezed by their squares
      (norm_num), and the inverses invSqrt2_bounds / invSqrt5_bounds (16 digits) /
      invSqrt3_bounds (20 digits) -- the prime side carries c(n)/sqrt n;
    * c3_bounds: the pilot's atom coefficient c(3) = 2 log 3 / sqrt 3 enclosed at 1e-16
      (1.2685682011951278 .. 1.2685682011951280, the pilot's c0 -+ dc);
    * logPi_le / logPi_le' (log pi <= 1.1447298859, the pilot's logPiUpQ; and <= 1.14472988584940018)
      from Real.pi_lt_d20 and the degree-19 Taylor polynomial of exp; two_logPi_le, two_gamma_le:
      the DOUBLED bounds (two digammas), gamma through E6Bridge30's eulerMascheroni_le
      (0.58112; the sharper KWin2 gamUp32 lives on an unmerged branch -- Stage 1b);
    * condLo_dm3: the conductor lower bound of the pilot member d = -3 is log3_lo.
  The shape mirrors KWin2_Consts.lean (origin/cl/kwin2, read only, NOT imported), which encloses
  log 2 and sqrt 2 the same way (partial sum + tail; squared rationals) but through `decide +kernel`
  on Q; here every numeric step is norm_num.

  ENVELOPE (twin of ZhuSplit `weilSymbol_ge_betaStar`): combMassF D L = Σ_{log n < 2L} 2|c(n)|/sqrt n,
  comb_le_combMassF, and symbolQ_ge_betaStar: for 15/4 <= T# <= t,
      symbolQ d L t >= betaStarQ d L T# = 2 log(T#/2pi) - 2/T# + log|d| - combMassF (quadData d) L,
  from ZhuEnvelope's psiR envelope and FamilyWeilDigamma's psiD envelope (Zhu Lemma 3.1 per
  digamma); combMassF_dm3_window4 evaluates the pilot's comb mass to 2 log 3/sqrt 3.

  ATOM WEIGHTS.  weightQ_two / _three / _four / _five: c_d(2) = log 2 (1 + chi_d(2)),
  c_d(3) = log 3 (1 + chi_d(3)), c_d(4) = log 2 (1 + chi_d(2)^2), c_d(5) = log 5 (1 + chi_d(5)),
  and c_d(0) = c_d(1) = c_d(6) = 0.  THE COEFFICIENT of cos(t log n) in the symbol is
  -2 c_d(n) n^{-1/2} (symbolQ_window4, symbolQ_window7: the explicit finite symbols on the
  windows log 3 < 2L <= log 4 and log 5 < 2L <= log 7, the latter containing x = 6.5).

  THE TABLES.  cellAtomTable4: the 18 cells cut at N = 4 as (d_min, 1 + eps_2, 1 + eps_3,
  1 + eps_2^2), kernel-checked against kron2 / kron3 (cellAtomTable4_check, decide) and against
  dmins4 (cellAtomTable4_dmins); weightQ_of_table4 turns each row into the three real weights;
  symbolQ_window4_of_table4 is the explicit symbol of each cell's d_min on the x = 4 window.
  cellAtomTable7: the same for the 54 cells cut at N = 7 with the fifth entry 1 + eps_5.

  Nothing about positivity is proved; no certificate is cut.  conjecture1_proved = False.
-/
import FamilyWeilSymbol
import FamilyWeilTable

open Zeta23 Complex MeasureTheory

noncomputable section

namespace FamilyWeil
open WeilExplicit RvMBridge11

/-! ## A. The logarithms. -/

/-- `|Σ_{i<60} 2^{-(i+1)}/(i+1) - log 2| <= 2^{-60}`. -/
theorem log2_series_bound :
    |(∑ i ∈ Finset.range 60, (1 / 2 : ℝ) ^ (i + 1) / ((i : ℝ) + 1)) - Real.log 2|
      ≤ (1 / 2) ^ 60 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (1 / 2 : ℝ)) (by norm_num) 60
  have e : Real.log (1 - 1 / 2) = -Real.log 2 := by
    rw [show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, Real.log_inv]
  rw [e] at h
  have hr : |(1 / 2 : ℝ)| ^ (60 + 1) / (1 - |(1 / 2 : ℝ)|) = (1 / 2) ^ 60 := by norm_num
  rw [hr] at h
  simpa [sub_eq_add_neg] using h

/-- `|Σ_{i<42} 3^{-(i+1)}/(i+1) + log 2 - log 3| <= 3^{-42}/2` (`log(1 - 1/3) = log 2 - log 3`). -/
theorem log3_series_bound :
    |(∑ i ∈ Finset.range 42, (1 / 3 : ℝ) ^ (i + 1) / ((i : ℝ) + 1)) + Real.log 2 - Real.log 3|
      ≤ (1 / 3) ^ 42 / 2 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (1 / 3 : ℝ)) (by norm_num) 42
  have e : Real.log (1 - 1 / 3) = Real.log 2 - Real.log 3 := by
    rw [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  rw [e] at h
  have hr : |(1 / 3 : ℝ)| ^ (42 + 1) / (1 - |(1 / 3 : ℝ)|) = (1 / 3) ^ 42 / 2 := by norm_num
  rw [hr] at h
  have e2 : (∑ i ∈ Finset.range 42, (1 / 3 : ℝ) ^ (i + 1) / ((i : ℝ) + 1))
      + (Real.log 2 - Real.log 3)
      = (∑ i ∈ Finset.range 42, (1 / 3 : ℝ) ^ (i + 1) / ((i : ℝ) + 1)) + Real.log 2 - Real.log 3 := by
    ring
  rw [e2] at h
  exact h

/-- The pilot's form: `|Σ_{i<40} 4^{-(i+1)}/(i+1) + log 3 - 2 log 2| <= 4^{-40}/3`
(`log(1 - 1/4) = log 3 - 2 log 2`; tail `(1/4)^41 · 4/3`). -/
theorem log43_series_bound :
    |(∑ i ∈ Finset.range 40, (1 / 4 : ℝ) ^ (i + 1) / ((i : ℝ) + 1)) + Real.log 3 - 2 * Real.log 2|
      ≤ (1 / 4) ^ 40 / 3 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (1 / 4 : ℝ)) (by norm_num) 40
  have e : Real.log (1 - 1 / 4) = Real.log 3 - 2 * Real.log 2 := by
    rw [show (1 : ℝ) - 1 / 4 = 3 / 2 ^ 2 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow]
    push_cast
    ring
  rw [e] at h
  have hr : |(1 / 4 : ℝ)| ^ (40 + 1) / (1 - |(1 / 4 : ℝ)|) = (1 / 4) ^ 40 / 3 := by norm_num
  rw [hr] at h
  have e2 : (∑ i ∈ Finset.range 40, (1 / 4 : ℝ) ^ (i + 1) / ((i : ℝ) + 1))
      + (Real.log 3 - 2 * Real.log 2)
      = (∑ i ∈ Finset.range 40, (1 / 4 : ℝ) ^ (i + 1) / ((i : ℝ) + 1))
        + Real.log 3 - 2 * Real.log 2 := by
    ring
  rw [e2] at h
  exact h

/-- `|Σ_{i<30} 5^{-(i+1)}/(i+1) + 2 log 2 - log 5| <= 5^{-30}/4` (`log(1 - 1/5) = 2 log 2 - log 5`). -/
theorem log5_series_bound :
    |(∑ i ∈ Finset.range 30, (1 / 5 : ℝ) ^ (i + 1) / ((i : ℝ) + 1)) + 2 * Real.log 2 - Real.log 5|
      ≤ (1 / 5) ^ 30 / 4 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (1 / 5 : ℝ)) (by norm_num) 30
  have e : Real.log (1 - 1 / 5) = 2 * Real.log 2 - Real.log 5 := by
    rw [show (1 : ℝ) - 1 / 5 = 2 ^ 2 / 5 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow]
    push_cast
    ring
  rw [e] at h
  have hr : |(1 / 5 : ℝ)| ^ (30 + 1) / (1 - |(1 / 5 : ℝ)|) = (1 / 5) ^ 30 / 4 := by norm_num
  rw [hr] at h
  have e2 : (∑ i ∈ Finset.range 30, (1 / 5 : ℝ) ^ (i + 1) / ((i : ℝ) + 1))
      + (2 * Real.log 2 - Real.log 5)
      = (∑ i ∈ Finset.range 30, (1 / 5 : ℝ) ^ (i + 1) / ((i : ℝ) + 1))
        + 2 * Real.log 2 - Real.log 5 := by
    ring
  rw [e2] at h
  exact h

/-- The 60-term partial sum of `log 2`, enclosed (`S = 0.69314718055994530940...`). -/
lemma log2_partial_bounds :
    (6931471805599453085 / 10 ^ 19 : ℝ) + (1 / 2) ^ 60
        ≤ ∑ i ∈ Finset.range 60, (1 / 2 : ℝ) ^ (i + 1) / ((i : ℝ) + 1)
      ∧ ∑ i ∈ Finset.range 60, (1 / 2 : ℝ) ^ (i + 1) / ((i : ℝ) + 1)
        ≤ (6931471805599453103 / 10 ^ 19 : ℝ) - (1 / 2) ^ 60 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  constructor <;> norm_num

/-- **`log 2` enclosed**: `0.6931471805599453085 <= log 2 <= 0.6931471805599453103`
(true value `0.69314718055994530942`). -/
theorem log2_bounds :
    (6931471805599453085 / 10 ^ 19 : ℝ) ≤ Real.log 2
      ∧ Real.log 2 ≤ (6931471805599453103 / 10 ^ 19 : ℝ) := by
  have h := abs_le.mp log2_series_bound
  have hS := log2_partial_bounds
  constructor <;> linarith [h.1, h.2, hS.1, hS.2]

/-- The 42-term partial sum of `log(3/2)`, enclosed (`S = 0.40546510810816438198...`). -/
lemma log32_partial_bounds :
    (40546510810816438197 / 10 ^ 20 : ℝ) + (1 / 3) ^ 42 / 2
        ≤ ∑ i ∈ Finset.range 42, (1 / 3 : ℝ) ^ (i + 1) / ((i : ℝ) + 1)
      ∧ ∑ i ∈ Finset.range 42, (1 / 3 : ℝ) ^ (i + 1) / ((i : ℝ) + 1)
        ≤ (40546510810816438199 / 10 ^ 20 : ℝ) - (1 / 3) ^ 42 / 2 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  constructor <;> norm_num

/-- **`log 3` enclosed**: `1.0986122886681096904 <= log 3 <= 1.0986122886681096923`
(true value `1.09861228866810969140`). -/
theorem log3_bounds :
    (10986122886681096904 / 10 ^ 19 : ℝ) ≤ Real.log 3
      ∧ Real.log 3 ≤ (10986122886681096923 / 10 ^ 19 : ℝ) := by
  have h2 := log2_bounds
  have h := abs_le.mp log3_series_bound
  have hS := log32_partial_bounds
  constructor <;> linarith [h.1, h.2, hS.1, hS.2, h2.1, h2.2]

/-- The 30-term partial sum of `log(5/4)`, enclosed. -/
lemma log54_partial_bounds :
    (22314355131420975 / 10 ^ 17 : ℝ) + (1 / 5) ^ 30 / 4
        ≤ ∑ i ∈ Finset.range 30, (1 / 5 : ℝ) ^ (i + 1) / ((i : ℝ) + 1)
      ∧ ∑ i ∈ Finset.range 30, (1 / 5 : ℝ) ^ (i + 1) / ((i : ℝ) + 1)
        ≤ (22314355131420976 / 10 ^ 17 : ℝ) - (1 / 5) ^ 30 / 4 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  constructor <;> norm_num

/-- **`log 5` enclosed**: `1.60943791243410036 <= log 5 <= 1.60943791243410039`. -/
theorem log5_bounds :
    (160943791243410036 / 10 ^ 17 : ℝ) ≤ Real.log 5
      ∧ Real.log 5 ≤ (160943791243410039 / 10 ^ 17 : ℝ) := by
  have h2 := log2_bounds
  have h := abs_le.mp log5_series_bound
  have hS := log54_partial_bounds
  constructor <;> linarith [h.1, h.2, hS.1, hS.2, h2.1, h2.2]

/-- `log 4 = 2 log 2`. -/
lemma log4_eq : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast
  ring

/-! ## B. The square roots and their inverses (20-digit rationals squeezed by their squares). -/

theorem sqrt2_bounds :
    (14142135623730950488 / 10 ^ 19 : ℝ) ≤ Real.sqrt 2
      ∧ Real.sqrt 2 ≤ (14142135623730950489 / 10 ^ 19 : ℝ) := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · rw [Real.sqrt_le_left (by norm_num)]
    norm_num

theorem sqrt3_bounds :
    (17320508075688772935 / 10 ^ 19 : ℝ) ≤ Real.sqrt 3
      ∧ Real.sqrt 3 ≤ (17320508075688772936 / 10 ^ 19 : ℝ) := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · rw [Real.sqrt_le_left (by norm_num)]
    norm_num

theorem sqrt5_bounds :
    (22360679774997896964 / 10 ^ 19 : ℝ) ≤ Real.sqrt 5
      ∧ Real.sqrt 5 ≤ (22360679774997896965 / 10 ^ 19 : ℝ) := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · rw [Real.sqrt_le_left (by norm_num)]
    norm_num

/-- From an enclosure `lo <= s <= hi`, `0 < lo`, the enclosure `1/hi <= 1/s <= 1/lo`. -/
lemma inv_bounds_of_bounds {s lo hi : ℝ} (hlo : 0 < lo) (h1 : lo ≤ s) (h2 : s ≤ hi) :
    1 / hi ≤ 1 / s ∧ 1 / s ≤ 1 / lo :=
  ⟨one_div_le_one_div_of_le (by linarith) h2, one_div_le_one_div_of_le hlo h1⟩

theorem invSqrt2_bounds :
    (7071067811865474 / 10 ^ 16 : ℝ) ≤ 1 / Real.sqrt 2
      ∧ 1 / Real.sqrt 2 ≤ (7071067811865476 / 10 ^ 16 : ℝ) := by
  have h := inv_bounds_of_bounds (by norm_num) sqrt2_bounds.1 sqrt2_bounds.2
  constructor
  · refine le_trans ?_ h.1
    norm_num
  · refine le_trans h.2 ?_
    norm_num

/-- `1/sqrt 3` at 20 digits: `0.57735026918962576448 .. 0.57735026918962576452`. -/
theorem invSqrt3_bounds :
    (57735026918962576448 / 10 ^ 20 : ℝ) ≤ 1 / Real.sqrt 3
      ∧ 1 / Real.sqrt 3 ≤ (57735026918962576452 / 10 ^ 20 : ℝ) := by
  have h := inv_bounds_of_bounds (by norm_num) sqrt3_bounds.1 sqrt3_bounds.2
  constructor
  · refine le_trans ?_ h.1
    norm_num
  · refine le_trans h.2 ?_
    norm_num

theorem invSqrt5_bounds :
    (4472135954999579 / 10 ^ 16 : ℝ) ≤ 1 / Real.sqrt 5
      ∧ 1 / Real.sqrt 5 ≤ (4472135954999580 / 10 ^ 16 : ℝ) := by
  have h := inv_bounds_of_bounds (by norm_num) sqrt5_bounds.1 sqrt5_bounds.2
  constructor
  · refine le_trans ?_ h.1
    norm_num
  · refine le_trans h.2 ?_
    norm_num

/-- `sqrt 4 = 2`. -/
lemma sqrt4_eq : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- **The pilot's atom coefficient `c(3) = 2 log 3 / sqrt 3`** enclosed at `1e-16`:
`1.2685682011951278 <= c(3) <= 1.2685682011951280` (the pilot's `c0 -+ dc`). -/
theorem c3_bounds :
    (12685682011951278 / 10 ^ 16 : ℝ) ≤ 2 * Real.log 3 / Real.sqrt 3
      ∧ 2 * Real.log 3 / Real.sqrt 3 ≤ (12685682011951280 / 10 ^ 16 : ℝ) := by
  have h3 := log3_bounds
  have hi := invSqrt3_bounds
  have hpos : (0 : ℝ) ≤ 2 * Real.log 3 := by
    have := h3.1
    linarith
  have e : 2 * Real.log 3 / Real.sqrt 3 = 2 * Real.log 3 * (1 / Real.sqrt 3) := by ring
  rw [e]
  constructor
  · have := mul_le_mul (by linarith [h3.1] : (2 * (10986122886681096904 / 10 ^ 19) : ℝ) ≤ 2 * Real.log 3)
      hi.1 (by norm_num) hpos
    refine le_trans ?_ this
    norm_num
  · have := mul_le_mul (by linarith [h3.2] : 2 * Real.log 3 ≤ (2 * (10986122886681096923 / 10 ^ 19) : ℝ))
      hi.2 (by linarith [hi.1]) (by norm_num)
    refine le_trans this ?_
    norm_num

/-! ## B'. `log pi` and `gamma`, and the doubled bounds (two digammas). -/

/-- `log pi <= q` once `pi <= Σ_{i<20} q^i/i!` (`q >= 0`): `Real.pi_lt_d20` against the degree-19
Taylor polynomial of `exp` (`Real.sum_le_exp_of_nonneg`). -/
lemma logPi_le_of_taylor {q : ℝ} (hq : 0 ≤ q)
    (h : (314159265358979323847 / 10 ^ 20 : ℝ) ≤ ∑ i ∈ Finset.range 20, q ^ i / (Nat.factorial i : ℝ)) :
    Real.log Real.pi ≤ q := by
  rw [Real.log_le_iff_le_exp Real.pi_pos]
  have hpi := Real.pi_lt_d20
  have hexp := Real.sum_le_exp_of_nonneg hq 20
  have e : (3.14159265358979323847 : ℝ) = 314159265358979323847 / 10 ^ 20 := by norm_num
  rw [e] at hpi
  linarith

/-- **`log pi <= 1.1447298859`** (the pilot's `logPiUpQ`; true value `1.14472988584940017414`). -/
theorem logPi_le : Real.log Real.pi ≤ (11447298859 / 10 ^ 10 : ℝ) := by
  refine logPi_le_of_taylor (by norm_num) ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

/-- **`log pi <= 1.14472988584940018`** (17 digits, `+6e-18`). -/
theorem logPi_le' : Real.log Real.pi ≤ (114472988584940018 / 10 ^ 17 : ℝ) := by
  refine logPi_le_of_taylor (by norm_num) ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

/-- The doubled `log pi` bound (the two `Gamma_R` factors each carry `-log pi`). -/
theorem two_logPi_le : 2 * Real.log Real.pi ≤ (22894597718 / 10 ^ 10 : ℝ) := by
  have := logPi_le
  linarith

/-- The doubled `gamma` bound through E6Bridge30's `eulerMascheroni_le` (`gamma <= 0.58112`; the
sharper `gamUp32` of KWin2_Consts lives on an unmerged branch). -/
theorem two_gamma_le : 2 * Real.eulerMascheroniConstant ≤ (116224 / 10 ^ 5 : ℝ) := by
  have := RvMBridge30.eulerMascheroni_le
  norm_num at this ⊢
  linarith

/-- The conductor term of the pilot member `d = -3` is `log 3`, hence `>= log3_lo`. -/
theorem condLo_dm3 :
    (10986122886681096904 / 10 ^ 19 : ℝ) ≤ Real.log (((-3 : ℤ).natAbs : ℕ) : ℝ) := by
  have h : ((-3 : ℤ).natAbs : ℕ) = 3 := by decide
  rw [h]
  push_cast
  exact log3_bounds.1

/-! ## C. The atom weights of a quadratic member. -/

lemma weightQ_zero (d : ℤ) : weightQ d 0 = 0 := by
  unfold weightQ
  simp

lemma weightQ_one (d : ℤ) : weightQ d 1 = 0 := by
  unfold weightQ
  simp

theorem weightQ_two (d : ℤ) : weightQ d 2 = Real.log 2 * (1 + (kron2 d : ℝ)) := by
  have h := weightQ_prime_pow Nat.prime_two one_ne_zero d
  simp only [pow_one, kronSym, if_true, Nat.cast_ofNat] at h
  exact h

theorem weightQ_three (d : ℤ) : weightQ d 3 = Real.log 3 * (1 + (kron3 d : ℝ)) := by
  have h := weightQ_prime_pow Nat.prime_three one_ne_zero d
  simp only [pow_one, kronSym_three, Nat.cast_ofNat] at h
  exact h

theorem weightQ_four (d : ℤ) : weightQ d 4 = Real.log 2 * (1 + (kron2 d : ℝ) ^ 2) := by
  have h := weightQ_prime_pow Nat.prime_two (k := 2) two_ne_zero d
  simp only [kronSym, if_true, Nat.cast_ofNat] at h
  norm_num at h
  exact h

theorem weightQ_five (d : ℤ) : weightQ d 5 = Real.log 5 * (1 + (kron5 d : ℝ)) := by
  have h := weightQ_prime_pow Nat.prime_five one_ne_zero d
  simp only [pow_one, kronSym_five, Nat.cast_ofNat] at h
  exact h

lemma weightQ_six (d : ℤ) : weightQ d 6 = 0 := by
  unfold weightQ
  rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr (by decide)]
  simp

/-! ## D. The explicit symbols on the two windows. -/

/-- The quadratic symbol on the `x = 4` window `log 3 < 2L <= log 4`: atoms `2` and `3`, with the
coefficients `-2 c_d(n) / sqrt n` on `cos(t log n)`. -/
theorem symbolQ_window4 (d : ℤ) {L : ℝ} (hL3 : Real.log 3 < 2 * L) (hL4 : 2 * L ≤ Real.log 4)
    (t : ℝ) :
    symbolQ d L t = psiR t + psiShift (muOf (decide (d < 0))) t - 2 * Real.log Real.pi
      + Real.log (d.natAbs : ℝ)
      - 2 * weightQ d 2 / Real.sqrt 2 * Real.cos (t * Real.log 2)
      - 2 * weightQ d 3 / Real.sqrt 3 * Real.cos (t * Real.log 3) := by
  have h23 : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  have h0 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  rw [symbolQ_eq_fin d (N := 4) (by norm_num) (by simpa using hL4)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat, Real.log_zero, Real.log_one, weightQ_zero, weightQ_one]
  rw [if_pos (by linarith), if_pos (by linarith), if_pos (by linarith), if_pos hL3]
  simp only [Real.sqrt_zero, Real.sqrt_one, mul_zero, zero_div, zero_mul, add_zero, zero_add]
  ring

/-- The quadratic symbol on the `x = 7` window `log 5 < 2L <= log 7` (which contains `x = 6.5`):
atoms `2, 3, 4, 5` (`6` carries weight `0`). -/
theorem symbolQ_window7 (d : ℤ) {L : ℝ} (hL5 : Real.log 5 < 2 * L) (hL7 : 2 * L ≤ Real.log 7)
    (t : ℝ) :
    symbolQ d L t = psiR t + psiShift (muOf (decide (d < 0))) t - 2 * Real.log Real.pi
      + Real.log (d.natAbs : ℝ)
      - 2 * weightQ d 2 / Real.sqrt 2 * Real.cos (t * Real.log 2)
      - 2 * weightQ d 3 / Real.sqrt 3 * Real.cos (t * Real.log 3)
      - 2 * weightQ d 4 / Real.sqrt 4 * Real.cos (t * Real.log 4)
      - 2 * weightQ d 5 / Real.sqrt 5 * Real.cos (t * Real.log 5) := by
  have h25 : Real.log 2 < Real.log 5 := Real.log_lt_log (by norm_num) (by norm_num)
  have h35 : Real.log 3 < Real.log 5 := Real.log_lt_log (by norm_num) (by norm_num)
  have h45 : Real.log 4 < Real.log 5 := Real.log_lt_log (by norm_num) (by norm_num)
  have h0 : (0 : ℝ) < Real.log 5 := Real.log_pos (by norm_num)
  rw [symbolQ_eq_fin d (N := 7) (by norm_num) (by simpa using hL7)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat, Real.log_zero, Real.log_one, weightQ_zero, weightQ_one, weightQ_six]
  rw [if_pos (by linarith), if_pos (by linarith), if_pos (by linarith), if_pos (by linarith),
    if_pos (by linarith), if_pos hL5]
  simp only [Real.sqrt_zero, Real.sqrt_one, mul_zero, zero_div, zero_mul, add_zero, zero_add,
    ite_self]
  ring

/-- `x = 6.5` lies in the `N = 7` window: `log 5 < log 6.5 <= log 7`. -/
lemma window65 : Real.log 5 < Real.log (13 / 2) ∧ Real.log (13 / 2) ≤ Real.log 7 :=
  ⟨Real.log_lt_log (by norm_num) (by norm_num), Real.log_le_log (by norm_num) (by norm_num)⟩

/-! ## E. The per-cell coefficient tables. -/

/-- The 18 cells cut at `N = 4`, in the order of `dmins4`: `(d_min, 1 + eps_2, 1 + eps_3, 1 + eps_2^2)`,
i.e. `c(2)/log 2`, `c(3)/log 3`, `c(4)/log 2`. -/
def cellAtomTable4 : List (ℤ × ℤ × ℤ × ℤ) :=
  [(5, 0, 0, 2), (-19, 0, 0, 2), (21, 0, 1, 2), (-3, 0, 1, 2), (13, 0, 2, 2), (-11, 0, 2, 2),
   (8, 1, 0, 1), (-4, 1, 0, 1), (12, 1, 1, 1), (-24, 1, 1, 1), (28, 1, 2, 1), (-8, 1, 2, 1),
   (17, 2, 0, 2), (-7, 2, 0, 2), (33, 2, 1, 2), (-15, 2, 1, 2), (73, 2, 2, 2), (-23, 2, 2, 2)]

/-- KERNEL CHECK: every row's integers are `1 + kron2 d`, `1 + kron3 d`, `1 + (kron2 d)^2`. -/
theorem cellAtomTable4_check : ∀ e ∈ cellAtomTable4,
    1 + kron2 e.1 = e.2.1 ∧ 1 + kron3 e.1 = e.2.2.1 ∧ 1 + kron2 e.1 ^ 2 = e.2.2.2 := by
  decide +kernel

/-- The rows are the `d_min` of `dmins4`, in order. -/
theorem cellAtomTable4_dmins : cellAtomTable4.map (·.1) = dmins4 := by decide

theorem cellAtomTable4_length : cellAtomTable4.length = 18 := by decide

/-- Each row gives the three real weights of its `d_min`. -/
theorem weightQ_of_table4 : ∀ e ∈ cellAtomTable4,
    weightQ e.1 2 = Real.log 2 * (e.2.1 : ℝ)
    ∧ weightQ e.1 3 = Real.log 3 * (e.2.2.1 : ℝ)
    ∧ weightQ e.1 4 = Real.log 2 * (e.2.2.2 : ℝ) := by
  intro e he
  obtain ⟨h2, h3, h4⟩ := cellAtomTable4_check e he
  rw [weightQ_two, weightQ_three, weightQ_four, ← h2, ← h3, ← h4]
  push_cast
  exact ⟨rfl, rfl, rfl⟩

/-- The explicit symbol of each cell's `d_min` on the `x = 4` window: the coefficient of
`cos(t log 2)` is `-2 (1 + eps_2) log 2 / sqrt 2`, of `cos(t log 3)` is `-2 (1 + eps_3) log 3 / sqrt 3`. -/
theorem symbolQ_window4_of_table4 {L : ℝ} (hL3 : Real.log 3 < 2 * L) (hL4 : 2 * L ≤ Real.log 4)
    (t : ℝ) : ∀ e ∈ cellAtomTable4,
    symbolQ e.1 L t = psiR t + psiShift (muOf (decide (e.1 < 0))) t - 2 * Real.log Real.pi
      + Real.log (e.1.natAbs : ℝ)
      - 2 * (Real.log 2 * (e.2.1 : ℝ)) / Real.sqrt 2 * Real.cos (t * Real.log 2)
      - 2 * (Real.log 3 * (e.2.2.1 : ℝ)) / Real.sqrt 3 * Real.cos (t * Real.log 3) := by
  intro e he
  obtain ⟨h2, h3, _⟩ := weightQ_of_table4 e he
  rw [symbolQ_window4 e.1 hL3 hL4 t, h2, h3]

/-- The 54 cells cut at `N = 7`, in the order of `dmins7`:
`(d_min, 1 + eps_2, 1 + eps_3, 1 + eps_2^2, 1 + eps_5)`. -/
def cellAtomTable7 : List (ℤ × ℤ × ℤ × ℤ × ℤ) :=
  [(53, 0, 0, 2, 0), (-43, 0, 0, 2, 0), (5, 0, 0, 2, 1), (-115, 0, 0, 2, 1), (29, 0, 0, 2, 2),
   (-19, 0, 0, 2, 2), (93, 0, 1, 2, 0), (-3, 0, 1, 2, 0), (165, 0, 1, 2, 1), (-195, 0, 1, 2, 1),
   (21, 0, 1, 2, 2), (-51, 0, 1, 2, 2), (13, 0, 2, 2, 0), (-83, 0, 2, 2, 0), (85, 0, 2, 2, 1),
   (-35, 0, 2, 2, 1), (61, 0, 2, 2, 2), (-11, 0, 2, 2, 2), (8, 1, 0, 1, 0), (-52, 1, 0, 1, 0),
   (140, 1, 0, 1, 1), (-40, 1, 0, 1, 1), (44, 1, 0, 1, 2), (-4, 1, 0, 1, 2), (12, 1, 1, 1, 0),
   (-132, 1, 1, 1, 0), (60, 1, 1, 1, 1), (-120, 1, 1, 1, 1), (24, 1, 1, 1, 2), (-24, 1, 1, 1, 2),
   (28, 1, 2, 1, 0), (-8, 1, 2, 1, 0), (40, 1, 2, 1, 1), (-20, 1, 2, 1, 1), (76, 1, 2, 1, 2),
   (-56, 1, 2, 1, 2), (17, 2, 0, 2, 0), (-7, 2, 0, 2, 0), (65, 2, 0, 2, 1), (-55, 2, 0, 2, 1),
   (41, 2, 0, 2, 2), (-31, 2, 0, 2, 2), (33, 2, 1, 2, 0), (-87, 2, 1, 2, 0), (105, 2, 1, 2, 1),
   (-15, 2, 1, 2, 1), (129, 2, 1, 2, 2), (-39, 2, 1, 2, 2), (73, 2, 2, 2, 0), (-23, 2, 2, 2, 0),
   (145, 2, 2, 2, 1), (-95, 2, 2, 2, 1), (241, 2, 2, 2, 2), (-71, 2, 2, 2, 2)]

theorem cellAtomTable7_check : ∀ e ∈ cellAtomTable7,
    1 + kron2 e.1 = e.2.1 ∧ 1 + kron3 e.1 = e.2.2.1 ∧ 1 + kron2 e.1 ^ 2 = e.2.2.2.1
      ∧ 1 + kron5 e.1 = e.2.2.2.2 := by
  decide +kernel

theorem cellAtomTable7_dmins : cellAtomTable7.map (·.1) = dmins7 := by decide

theorem cellAtomTable7_length : cellAtomTable7.length = 54 := by decide

theorem weightQ_of_table7 : ∀ e ∈ cellAtomTable7,
    weightQ e.1 2 = Real.log 2 * (e.2.1 : ℝ)
    ∧ weightQ e.1 3 = Real.log 3 * (e.2.2.1 : ℝ)
    ∧ weightQ e.1 4 = Real.log 2 * (e.2.2.2.1 : ℝ)
    ∧ weightQ e.1 5 = Real.log 5 * (e.2.2.2.2 : ℝ) := by
  intro e he
  obtain ⟨h2, h3, h4, h5⟩ := cellAtomTable7_check e he
  rw [weightQ_two, weightQ_three, weightQ_four, weightQ_five, ← h2, ← h3, ← h4, ← h5]
  push_cast
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The explicit symbol of each `N = 7` cell's `d_min` on the window `log 5 < 2L <= log 7`. -/
theorem symbolQ_window7_of_table7 {L : ℝ} (hL5 : Real.log 5 < 2 * L) (hL7 : 2 * L ≤ Real.log 7)
    (t : ℝ) : ∀ e ∈ cellAtomTable7,
    symbolQ e.1 L t = psiR t + psiShift (muOf (decide (e.1 < 0))) t - 2 * Real.log Real.pi
      + Real.log (e.1.natAbs : ℝ)
      - 2 * (Real.log 2 * (e.2.1 : ℝ)) / Real.sqrt 2 * Real.cos (t * Real.log 2)
      - 2 * (Real.log 3 * (e.2.2.1 : ℝ)) / Real.sqrt 3 * Real.cos (t * Real.log 3)
      - 2 * (Real.log 2 * (e.2.2.2.1 : ℝ)) / Real.sqrt 4 * Real.cos (t * Real.log 4)
      - 2 * (Real.log 5 * (e.2.2.2.2 : ℝ)) / Real.sqrt 5 * Real.cos (t * Real.log 5) := by
  intro e he
  obtain ⟨h2, h3, h4, h5⟩ := weightQ_of_table7 e he
  rw [symbolQ_window7 e.1 hL5 hL7 t, h2, h3, h4, h5]

/-! ## F. The two-digamma envelope (twin of ZhuSplit `weilSymbol_ge_betaStar`). -/

/-- The comb mass of a data on the window: `A_{D,L} = Σ_{log n < 2L} 2|c(n)|/sqrt n`
(Zhu's `combMass` is the zeta case, where `c = Λ >= 0`). -/
def combMassF (D : FormData) (L : ℝ) : ℝ :=
  ∑' n : ℕ, if Real.log n < 2 * L then 2 * |D.c n| / Real.sqrt n else 0

/-- On a window `2L <= log N` the comb mass is the finite sum over `n < N`. -/
theorem combMassF_eq_fin (D : FormData) {L : ℝ} {N : ℕ} (hN : 1 ≤ N) (hL : 2 * L ≤ Real.log N) :
    combMassF D L = ∑ n ∈ Finset.range N,
      (if Real.log n < 2 * L then 2 * |D.c n| / Real.sqrt n else 0) := by
  unfold combMassF
  apply tsum_eq_sum
  intro n hn
  rw [Finset.mem_range, not_lt] at hn
  have hlog : Real.log N ≤ Real.log n :=
    Real.log_le_log (Nat.cast_pos.mpr hN) (by exact_mod_cast hn)
  rw [if_neg (by linarith)]

/-- The comb is bounded by its mass (twin of ZhuSplit `comb_le_combMass`, with `|c|`). -/
theorem comb_le_combMassF (D : FormData) (L t : ℝ) :
    (∑' n : ℕ, if Real.log n < 2 * L then
        2 * D.c n / Real.sqrt n * Real.cos (t * Real.log n) else 0)
      ≤ combMassF D L := by
  set N0 : ℕ := ⌈Real.exp (2 * L)⌉₊ + 1 with hN0
  have hbig : ∀ n : ℕ, n ∉ Finset.range N0 → ¬ Real.log n < 2 * L := by
    intro n hn hlt
    have hn' : N0 ≤ n := by simpa [Finset.mem_range] using hn
    have h1 : Real.exp (2 * L) < (n : ℝ) := by
      have := Nat.le_ceil (Real.exp (2 * L))
      have h2 : ((⌈Real.exp (2 * L)⌉₊ + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn'
      push_cast at h2
      linarith
    have h3 : 2 * L < Real.log n := by
      rw [← Real.log_exp (2 * L)]
      exact Real.log_lt_log (Real.exp_pos _) h1
    linarith
  unfold combMassF
  rw [tsum_eq_sum (s := Finset.range N0) (fun n hn => by rw [if_neg (hbig n hn)]),
    tsum_eq_sum (s := Finset.range N0) (fun n hn => by rw [if_neg (hbig n hn)])]
  refine Finset.sum_le_sum fun n _ => ?_
  split_ifs with h
  · have hs : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
    have hcos : D.c n * Real.cos (t * Real.log n) ≤ |D.c n| := by
      calc D.c n * Real.cos (t * Real.log n) ≤ |D.c n * Real.cos (t * Real.log n)| := le_abs_self _
        _ = |D.c n| * |Real.cos (t * Real.log n)| := abs_mul _ _
        _ ≤ |D.c n| * 1 := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
        _ = |D.c n| := mul_one _
    have e : 2 * D.c n / Real.sqrt n * Real.cos (t * Real.log n)
        = 2 * (D.c n * Real.cos (t * Real.log n)) / Real.sqrt n := by ring
    rw [e]
    apply div_le_div_of_nonneg_right _ hs
    linarith
  · exact le_rfl

/-- The quadratic threshold `beta*_d(L, T#) = 2 log(T#/2pi) - 2/T# + log|d| - A_{d,L}`. -/
def betaStarQ (d : ℤ) (L Tsharp : ℝ) : ℝ :=
  2 * Real.log (Tsharp / (2 * Real.pi)) - 2 / Tsharp + Real.log (d.natAbs : ℝ)
    - combMassF (quadData d) L

/-- **The envelope step for the quadratic symbol** (twin of ZhuSplit `weilSymbol_ge_betaStar`,
Zhu eq. (4)): for `15/4 <= T# <= t`, `symbolQ d L t >= betaStarQ d L T#` -- Zhu's Lemma 3.1
envelope `log(t/2) - 1/t` PER digamma (ZhuEnvelope for `psiR`, FamilyWeilDigamma for `psiShift 1`),
`-2 log pi`, the exact conductor term, and the trivial comb bound. -/
theorem symbolQ_ge_betaStar (d : ℤ) {L Tsharp t : ℝ} (hT : 15 / 4 ≤ Tsharp) (ht : Tsharp ≤ t) :
    betaStarQ d L Tsharp ≤ symbolQ d L t := by
  rw [symbolQ_eq]
  have henv := symbolArch_quad_ge_envelope (decide (d < 0)) (hT.trans ht)
  have hcomb := comb_le_combMassF (quadData d) L t
  have hT0 : 0 < Tsharp := by linarith
  have ht0 : 0 < t := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hlog : Real.log (Tsharp / (2 * Real.pi)) ≤ Real.log (t / (2 * Real.pi)) :=
    Real.log_le_log (by positivity) (by gcongr)
  have hlog2 : Real.log (t / (2 * Real.pi)) = Real.log (t / 2) - Real.log Real.pi := by
    rw [show t / (2 * Real.pi) = (t / 2) / Real.pi by ring,
      Real.log_div (by positivity) hpi.ne']
  have hinv : 1 / t ≤ 1 / Tsharp := one_div_le_one_div_of_le hT0 ht
  have hc : (quadData d).c = weightQ d := rfl
  rw [hc] at hcomb
  unfold betaStarQ
  have e2 : (2 : ℝ) / Tsharp = 2 * (1 / Tsharp) := by ring
  rw [e2]
  linarith

/-- The pilot's comb mass: `d = -3` on the `x = 4` window has the single atom `3` with weight
`log 3`, so `A = 2 log 3 / sqrt 3` (`c(2) = 0` since `chi_{-3}(2) = -1`). -/
theorem combMassF_dm3_window4 {L : ℝ} (hL3 : Real.log 3 < 2 * L) (hL4 : 2 * L ≤ Real.log 4) :
    combMassF (quadData (-3)) L = 2 * Real.log 3 / Real.sqrt 3 := by
  have h23 : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  have h0 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  rw [combMassF_eq_fin _ (N := 4) (by norm_num) (by simpa using hL4)]
  have hc : (quadData (-3)).c = weightQ (-3) := rfl
  simp only [hc, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat, Real.log_zero, Real.log_one, weightQ_zero, weightQ_one, weightQ_two,
    weightQ_three]
  rw [if_pos (by linarith), if_pos (by linarith), if_pos (by linarith), if_pos hL3]
  have hk2 : kron2 (-3) = -1 := by decide
  have hk3 : kron3 (-3) = 0 := by decide
  rw [hk2, hk3]
  push_cast
  norm_num [abs_of_pos h0]

end FamilyWeil

end
