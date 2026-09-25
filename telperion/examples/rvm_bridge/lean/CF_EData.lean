import Crux3_BandTable

/-!
# CF_EData: the Epstein counterfeit E and zeta_K for K = Q(sqrt -5) -- coefficients and log-derivative weights

Counterfeit-ladder lane (CF), 2026-09-24, `rvm_bridge` island.

`conjecture1_proved = False`.  Bookkeeping for the counterfeit ladder; nothing here bears on RH.

## The two functions (normalized so that `a(1) = 1`)
* `E(s) = (1/2) sum_{(x,y) != (0,0)} (x^2 + 5 y^2)^{-s} = sum_n aE(n) n^{-s}`,
  `aE(n) = (1/2) #{(x, y) in Z^2 : x^2 + 5 y^2 = n}` (`aE`, defined by the lattice count itself).
  Classically `E = (zeta_K + L(s, chi_-4) L(s, chi_5))/2` (`aE_eq_half_sum` checks the coefficients on
  `[1, 27]`); `E` has NO Euler product.
* `zeta_K(s) = zeta(s) L(s, chi_-20) = sum_n aK(n) n^{-s}`, `aK = 1 * chi_-20` (`aKint`), with
  `-zeta_K'/zeta_K = sum_n Lambda(n) (1 + chi_-20(n)) n^{-s}` (`cK`).

## The weights
`-F'/F = sum_n c(n) n^{-s}` is equivalent to the Dirichlet-convolution identity
`a(n) log n = sum_{d | n} c(d) a(n/d)` (with `a(1) = 1`, so `c(1) = 0` and the identity is triangular).
* `cE n = rhoE n * log n` on `[1, 27]` (generated from the recursion; every `c_E(n)`, `n <= 27`, happens to
  be a rational multiple of `log n`), and `cE_conv` proves the identity for `n <= 27`; `eq_cE_of_conv`: any
  `w` satisfying it on `[1, 27]` equals `cE` there.
* `cK n = Lambda(n) (1 + chi_-20(n))`; `cK_conv` proves the identity with `aK` for `n <= 27`.
* Lemma-O witnesses: `cE 6 = 2 log 6 != 0` while `Lambda(6) = 0` (`cE_six`, `cE_six_ne_zero`).
No `sorry`.
-/

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

open Finset

noncomputable section

namespace CF

/-! ## A. The Epstein counterfeit's coefficients (lattice count) -/

/-- `#{(x, y) in Z^2 : x^2 + 5 y^2 = n}`, enumerated as `x = a - n`, `y = b - n` with `a, b in [0, 2n]`
(every representation has `|x|, |y| <= n`). -/
def aEcount (n : ℕ) : ℕ :=
  ((Finset.range (2 * n + 1) ×ˢ Finset.range (2 * n + 1)).filter
    (fun p : ℕ × ℕ => ((p.1 : ℤ) - n) ^ 2 + 5 * ((p.2 : ℤ) - n) ^ 2 = n)).card

/-- `aE(n) = (1/2) #{(x, y) : x^2 + 5 y^2 = n}`: the coefficients of `E = (1/2) sum' (x^2 + 5y^2)^{-s}`. -/
def aE (n : ℕ) : ℝ := (aEcount n : ℝ) / 2

/-- The lattice counts for `n <= 27` (table). -/
def aEcnt : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 4 => 2
  | 5 => 2
  | 6 => 4
  | 9 => 6
  | 14 => 4
  | 16 => 2
  | 20 => 2
  | 21 => 8
  | 24 => 4
  | 25 => 2
  | _ => 0

set_option maxRecDepth 100000 in
theorem aEcount_tab : ∀ n ∈ List.range 28, aEcount n = aEcnt n := by decide +kernel

lemma aE_of_tab {n : ℕ} (hn : n < 28) : aE n = (aEcnt n : ℝ) / 2 := by
  unfold aE
  rw [aEcount_tab n (List.mem_range.mpr hn)]

lemma aE_1 : aE 1 = 1 := by rw [aE_of_tab (by norm_num)]; norm_num [aEcnt]
lemma aE_2 : aE 2 = 0 := by rw [aE_of_tab (by norm_num)]; norm_num [aEcnt]
lemma aE_3 : aE 3 = 0 := by rw [aE_of_tab (by norm_num)]; norm_num [aEcnt]
lemma aE_4 : aE 4 = 1 := by rw [aE_of_tab (by norm_num)]; norm_num [aEcnt]
lemma aE_5 : aE 5 = 1 := by rw [aE_of_tab (by norm_num)]; norm_num [aEcnt]
lemma aE_6 : aE 6 = 2 := by rw [aE_of_tab (by norm_num)]; norm_num [aEcnt]
lemma aE_7 : aE 7 = 0 := by rw [aE_of_tab (by norm_num)]; norm_num [aEcnt]
lemma aE_8 : aE 8 = 0 := by rw [aE_of_tab (by norm_num)]; norm_num [aEcnt]
lemma aE_9 : aE 9 = 3 := by rw [aE_of_tab (by norm_num)]; norm_num [aEcnt]
lemma aE_10 : aE 10 = 0 := by rw [aE_of_tab (by norm_num)]; norm_num [aEcnt]
lemma aE_11 : aE 11 = 0 := by rw [aE_of_tab (by norm_num)]; norm_num [aEcnt]
lemma aE_12 : aE 12 = 0 := by rw [aE_of_tab (by norm_num)]; norm_num [aEcnt]
lemma aE_13 : aE 13 = 0 := by rw [aE_of_tab (by norm_num)]; norm_num [aEcnt]
lemma aE_14 : aE 14 = 2 := by rw [aE_of_tab (by norm_num)]; norm_num [aEcnt]
lemma aE_15 : aE 15 = 0 := by rw [aE_of_tab (by norm_num)]; norm_num [aEcnt]
lemma aE_16 : aE 16 = 1 := by rw [aE_of_tab (by norm_num)]; norm_num [aEcnt]
lemma aE_17 : aE 17 = 0 := by rw [aE_of_tab (by norm_num)]; norm_num [aEcnt]
lemma aE_18 : aE 18 = 0 := by rw [aE_of_tab (by norm_num)]; norm_num [aEcnt]
lemma aE_19 : aE 19 = 0 := by rw [aE_of_tab (by norm_num)]; norm_num [aEcnt]
lemma aE_20 : aE 20 = 1 := by rw [aE_of_tab (by norm_num)]; norm_num [aEcnt]
lemma aE_21 : aE 21 = 4 := by rw [aE_of_tab (by norm_num)]; norm_num [aEcnt]
lemma aE_22 : aE 22 = 0 := by rw [aE_of_tab (by norm_num)]; norm_num [aEcnt]
lemma aE_23 : aE 23 = 0 := by rw [aE_of_tab (by norm_num)]; norm_num [aEcnt]
lemma aE_24 : aE 24 = 2 := by rw [aE_of_tab (by norm_num)]; norm_num [aEcnt]
lemma aE_25 : aE 25 = 1 := by rw [aE_of_tab (by norm_num)]; norm_num [aEcnt]
lemma aE_26 : aE 26 = 0 := by rw [aE_of_tab (by norm_num)]; norm_num [aEcnt]
lemma aE_27 : aE 27 = 0 := by rw [aE_of_tab (by norm_num)]; norm_num [aEcnt]

/-- `c_E(n)/log n` on `[1, 27]` (from the recursion `aE(n) log n = sum_{d|n} c(d) aE(n/d)`). -/
def rhoE : ℕ → ℚ
  | 4 => (1 : ℚ)
  | 5 => (1 : ℚ)
  | 6 => (2 : ℚ)
  | 9 => (3 : ℚ)
  | 14 => (2 : ℚ)
  | 16 => ((1 : ℚ) / 2)
  | 21 => (4 : ℚ)
  | 25 => ((1 : ℚ) / 2)
  | _ => 0

/-- The coefficients `c_E(n)` of `-E'/E` for `n <= 27`. -/
def cE (n : ℕ) : ℝ := (rhoE n : ℝ) * Real.log n

lemma rhoE_1 : rhoE 1 = (0 : ℚ) := rfl
lemma rhoE_2 : rhoE 2 = (0 : ℚ) := rfl
lemma rhoE_3 : rhoE 3 = (0 : ℚ) := rfl
lemma rhoE_4 : rhoE 4 = (1 : ℚ) := rfl
lemma rhoE_5 : rhoE 5 = (1 : ℚ) := rfl
lemma rhoE_6 : rhoE 6 = (2 : ℚ) := rfl
lemma rhoE_7 : rhoE 7 = (0 : ℚ) := rfl
lemma rhoE_8 : rhoE 8 = (0 : ℚ) := rfl
lemma rhoE_9 : rhoE 9 = (3 : ℚ) := rfl
lemma rhoE_10 : rhoE 10 = (0 : ℚ) := rfl
lemma rhoE_11 : rhoE 11 = (0 : ℚ) := rfl
lemma rhoE_12 : rhoE 12 = (0 : ℚ) := rfl
lemma rhoE_13 : rhoE 13 = (0 : ℚ) := rfl
lemma rhoE_14 : rhoE 14 = (2 : ℚ) := rfl
lemma rhoE_15 : rhoE 15 = (0 : ℚ) := rfl
lemma rhoE_16 : rhoE 16 = ((1 : ℚ) / 2) := rfl
lemma rhoE_17 : rhoE 17 = (0 : ℚ) := rfl
lemma rhoE_18 : rhoE 18 = (0 : ℚ) := rfl
lemma rhoE_19 : rhoE 19 = (0 : ℚ) := rfl
lemma rhoE_20 : rhoE 20 = (0 : ℚ) := rfl
lemma rhoE_21 : rhoE 21 = (4 : ℚ) := rfl
lemma rhoE_22 : rhoE 22 = (0 : ℚ) := rfl
lemma rhoE_23 : rhoE 23 = (0 : ℚ) := rfl
lemma rhoE_24 : rhoE 24 = (0 : ℚ) := rfl
lemma rhoE_25 : rhoE 25 = ((1 : ℚ) / 2) := rfl
lemma rhoE_26 : rhoE 26 = (0 : ℚ) := rfl
lemma rhoE_27 : rhoE 27 = (0 : ℚ) := rfl

lemma lg_4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = ((2 : ℝ) ^ 2) by norm_num]
  repeat rw [Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_pow]
  push_cast
  ring
lemma lg_6 : Real.log (6 : ℝ) = 1 * Real.log 2 + 1 * Real.log 3 := by
  rw [show (6 : ℝ) = ((2 : ℝ) ^ 1) * ((3 : ℝ) ^ 1) by norm_num]
  repeat rw [Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_pow]
  push_cast
  ring
lemma lg_8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
  rw [show (8 : ℝ) = ((2 : ℝ) ^ 3) by norm_num]
  repeat rw [Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_pow]
  push_cast
  ring
lemma lg_9 : Real.log (9 : ℝ) = 2 * Real.log 3 := by
  rw [show (9 : ℝ) = ((3 : ℝ) ^ 2) by norm_num]
  repeat rw [Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_pow]
  push_cast
  ring
lemma lg_10 : Real.log (10 : ℝ) = 1 * Real.log 2 + 1 * Real.log 5 := by
  rw [show (10 : ℝ) = ((2 : ℝ) ^ 1) * ((5 : ℝ) ^ 1) by norm_num]
  repeat rw [Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_pow]
  push_cast
  ring
lemma lg_12 : Real.log (12 : ℝ) = 2 * Real.log 2 + 1 * Real.log 3 := by
  rw [show (12 : ℝ) = ((2 : ℝ) ^ 2) * ((3 : ℝ) ^ 1) by norm_num]
  repeat rw [Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_pow]
  push_cast
  ring
lemma lg_14 : Real.log (14 : ℝ) = 1 * Real.log 2 + 1 * Real.log 7 := by
  rw [show (14 : ℝ) = ((2 : ℝ) ^ 1) * ((7 : ℝ) ^ 1) by norm_num]
  repeat rw [Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_pow]
  push_cast
  ring
lemma lg_15 : Real.log (15 : ℝ) = 1 * Real.log 3 + 1 * Real.log 5 := by
  rw [show (15 : ℝ) = ((3 : ℝ) ^ 1) * ((5 : ℝ) ^ 1) by norm_num]
  repeat rw [Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_pow]
  push_cast
  ring
lemma lg_16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
  rw [show (16 : ℝ) = ((2 : ℝ) ^ 4) by norm_num]
  repeat rw [Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_pow]
  push_cast
  ring
lemma lg_18 : Real.log (18 : ℝ) = 1 * Real.log 2 + 2 * Real.log 3 := by
  rw [show (18 : ℝ) = ((2 : ℝ) ^ 1) * ((3 : ℝ) ^ 2) by norm_num]
  repeat rw [Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_pow]
  push_cast
  ring
lemma lg_20 : Real.log (20 : ℝ) = 2 * Real.log 2 + 1 * Real.log 5 := by
  rw [show (20 : ℝ) = ((2 : ℝ) ^ 2) * ((5 : ℝ) ^ 1) by norm_num]
  repeat rw [Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_pow]
  push_cast
  ring
lemma lg_21 : Real.log (21 : ℝ) = 1 * Real.log 3 + 1 * Real.log 7 := by
  rw [show (21 : ℝ) = ((3 : ℝ) ^ 1) * ((7 : ℝ) ^ 1) by norm_num]
  repeat rw [Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_pow]
  push_cast
  ring
lemma lg_22 : Real.log (22 : ℝ) = 1 * Real.log 2 + 1 * Real.log 11 := by
  rw [show (22 : ℝ) = ((2 : ℝ) ^ 1) * ((11 : ℝ) ^ 1) by norm_num]
  repeat rw [Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_pow]
  push_cast
  ring
lemma lg_24 : Real.log (24 : ℝ) = 3 * Real.log 2 + 1 * Real.log 3 := by
  rw [show (24 : ℝ) = ((2 : ℝ) ^ 3) * ((3 : ℝ) ^ 1) by norm_num]
  repeat rw [Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_pow]
  push_cast
  ring
lemma lg_25 : Real.log (25 : ℝ) = 2 * Real.log 5 := by
  rw [show (25 : ℝ) = ((5 : ℝ) ^ 2) by norm_num]
  repeat rw [Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_pow]
  push_cast
  ring
lemma lg_26 : Real.log (26 : ℝ) = 1 * Real.log 2 + 1 * Real.log 13 := by
  rw [show (26 : ℝ) = ((2 : ℝ) ^ 1) * ((13 : ℝ) ^ 1) by norm_num]
  repeat rw [Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_pow]
  push_cast
  ring
lemma lg_27 : Real.log (27 : ℝ) = 3 * Real.log 3 := by
  rw [show (27 : ℝ) = ((3 : ℝ) ^ 3) by norm_num]
  repeat rw [Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_pow]
  push_cast
  ring

lemma cE_conv_1 : aE 1 * Real.log (1 : ℕ) = ∑ d ∈ Nat.divisors 1, cE d * aE (1 / d) := by
  rw [show Nat.divisors 1 = {1} by decide]
  simp only [Finset.sum_singleton]
  norm_num [cE, rhoE_1, rhoE_2, rhoE_3, rhoE_4, rhoE_5, rhoE_6, rhoE_7, rhoE_8, rhoE_9, rhoE_10, rhoE_11, rhoE_12, rhoE_13, rhoE_14, rhoE_15, rhoE_16, rhoE_17, rhoE_18, rhoE_19, rhoE_20, rhoE_21, rhoE_22, rhoE_23, rhoE_24, rhoE_25, rhoE_26, rhoE_27, aE_1, aE_2, aE_3, aE_4, aE_5, aE_6, aE_7, aE_8, aE_9, aE_10, aE_11, aE_12, aE_13, aE_14, aE_15, aE_16, aE_17, aE_18, aE_19, aE_20, aE_21, aE_22, aE_23, aE_24, aE_25, aE_26, aE_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cE_conv_2 : aE 2 * Real.log (2 : ℕ) = ∑ d ∈ Nat.divisors 2, cE d * aE (2 / d) := by
  rw [show Nat.divisors 2 = {1, 2} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({2} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cE, rhoE_1, rhoE_2, rhoE_3, rhoE_4, rhoE_5, rhoE_6, rhoE_7, rhoE_8, rhoE_9, rhoE_10, rhoE_11, rhoE_12, rhoE_13, rhoE_14, rhoE_15, rhoE_16, rhoE_17, rhoE_18, rhoE_19, rhoE_20, rhoE_21, rhoE_22, rhoE_23, rhoE_24, rhoE_25, rhoE_26, rhoE_27, aE_1, aE_2, aE_3, aE_4, aE_5, aE_6, aE_7, aE_8, aE_9, aE_10, aE_11, aE_12, aE_13, aE_14, aE_15, aE_16, aE_17, aE_18, aE_19, aE_20, aE_21, aE_22, aE_23, aE_24, aE_25, aE_26, aE_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cE_conv_3 : aE 3 * Real.log (3 : ℕ) = ∑ d ∈ Nat.divisors 3, cE d * aE (3 / d) := by
  rw [show Nat.divisors 3 = {1, 3} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({3} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cE, rhoE_1, rhoE_2, rhoE_3, rhoE_4, rhoE_5, rhoE_6, rhoE_7, rhoE_8, rhoE_9, rhoE_10, rhoE_11, rhoE_12, rhoE_13, rhoE_14, rhoE_15, rhoE_16, rhoE_17, rhoE_18, rhoE_19, rhoE_20, rhoE_21, rhoE_22, rhoE_23, rhoE_24, rhoE_25, rhoE_26, rhoE_27, aE_1, aE_2, aE_3, aE_4, aE_5, aE_6, aE_7, aE_8, aE_9, aE_10, aE_11, aE_12, aE_13, aE_14, aE_15, aE_16, aE_17, aE_18, aE_19, aE_20, aE_21, aE_22, aE_23, aE_24, aE_25, aE_26, aE_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cE_conv_4 : aE 4 * Real.log (4 : ℕ) = ∑ d ∈ Nat.divisors 4, cE d * aE (4 / d) := by
  rw [show Nat.divisors 4 = {1, 2, 4} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({2, 4} : Finset ℕ) by decide), Finset.sum_insert (show (2 : ℕ) ∉ ({4} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cE, rhoE_1, rhoE_2, rhoE_3, rhoE_4, rhoE_5, rhoE_6, rhoE_7, rhoE_8, rhoE_9, rhoE_10, rhoE_11, rhoE_12, rhoE_13, rhoE_14, rhoE_15, rhoE_16, rhoE_17, rhoE_18, rhoE_19, rhoE_20, rhoE_21, rhoE_22, rhoE_23, rhoE_24, rhoE_25, rhoE_26, rhoE_27, aE_1, aE_2, aE_3, aE_4, aE_5, aE_6, aE_7, aE_8, aE_9, aE_10, aE_11, aE_12, aE_13, aE_14, aE_15, aE_16, aE_17, aE_18, aE_19, aE_20, aE_21, aE_22, aE_23, aE_24, aE_25, aE_26, aE_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cE_conv_5 : aE 5 * Real.log (5 : ℕ) = ∑ d ∈ Nat.divisors 5, cE d * aE (5 / d) := by
  rw [show Nat.divisors 5 = {1, 5} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({5} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cE, rhoE_1, rhoE_2, rhoE_3, rhoE_4, rhoE_5, rhoE_6, rhoE_7, rhoE_8, rhoE_9, rhoE_10, rhoE_11, rhoE_12, rhoE_13, rhoE_14, rhoE_15, rhoE_16, rhoE_17, rhoE_18, rhoE_19, rhoE_20, rhoE_21, rhoE_22, rhoE_23, rhoE_24, rhoE_25, rhoE_26, rhoE_27, aE_1, aE_2, aE_3, aE_4, aE_5, aE_6, aE_7, aE_8, aE_9, aE_10, aE_11, aE_12, aE_13, aE_14, aE_15, aE_16, aE_17, aE_18, aE_19, aE_20, aE_21, aE_22, aE_23, aE_24, aE_25, aE_26, aE_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cE_conv_6 : aE 6 * Real.log (6 : ℕ) = ∑ d ∈ Nat.divisors 6, cE d * aE (6 / d) := by
  rw [show Nat.divisors 6 = {1, 2, 3, 6} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({2, 3, 6} : Finset ℕ) by decide), Finset.sum_insert (show (2 : ℕ) ∉ ({3, 6} : Finset ℕ) by decide), Finset.sum_insert (show (3 : ℕ) ∉ ({6} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cE, rhoE_1, rhoE_2, rhoE_3, rhoE_4, rhoE_5, rhoE_6, rhoE_7, rhoE_8, rhoE_9, rhoE_10, rhoE_11, rhoE_12, rhoE_13, rhoE_14, rhoE_15, rhoE_16, rhoE_17, rhoE_18, rhoE_19, rhoE_20, rhoE_21, rhoE_22, rhoE_23, rhoE_24, rhoE_25, rhoE_26, rhoE_27, aE_1, aE_2, aE_3, aE_4, aE_5, aE_6, aE_7, aE_8, aE_9, aE_10, aE_11, aE_12, aE_13, aE_14, aE_15, aE_16, aE_17, aE_18, aE_19, aE_20, aE_21, aE_22, aE_23, aE_24, aE_25, aE_26, aE_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cE_conv_7 : aE 7 * Real.log (7 : ℕ) = ∑ d ∈ Nat.divisors 7, cE d * aE (7 / d) := by
  rw [show Nat.divisors 7 = {1, 7} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({7} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cE, rhoE_1, rhoE_2, rhoE_3, rhoE_4, rhoE_5, rhoE_6, rhoE_7, rhoE_8, rhoE_9, rhoE_10, rhoE_11, rhoE_12, rhoE_13, rhoE_14, rhoE_15, rhoE_16, rhoE_17, rhoE_18, rhoE_19, rhoE_20, rhoE_21, rhoE_22, rhoE_23, rhoE_24, rhoE_25, rhoE_26, rhoE_27, aE_1, aE_2, aE_3, aE_4, aE_5, aE_6, aE_7, aE_8, aE_9, aE_10, aE_11, aE_12, aE_13, aE_14, aE_15, aE_16, aE_17, aE_18, aE_19, aE_20, aE_21, aE_22, aE_23, aE_24, aE_25, aE_26, aE_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cE_conv_8 : aE 8 * Real.log (8 : ℕ) = ∑ d ∈ Nat.divisors 8, cE d * aE (8 / d) := by
  rw [show Nat.divisors 8 = {1, 2, 4, 8} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({2, 4, 8} : Finset ℕ) by decide), Finset.sum_insert (show (2 : ℕ) ∉ ({4, 8} : Finset ℕ) by decide), Finset.sum_insert (show (4 : ℕ) ∉ ({8} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cE, rhoE_1, rhoE_2, rhoE_3, rhoE_4, rhoE_5, rhoE_6, rhoE_7, rhoE_8, rhoE_9, rhoE_10, rhoE_11, rhoE_12, rhoE_13, rhoE_14, rhoE_15, rhoE_16, rhoE_17, rhoE_18, rhoE_19, rhoE_20, rhoE_21, rhoE_22, rhoE_23, rhoE_24, rhoE_25, rhoE_26, rhoE_27, aE_1, aE_2, aE_3, aE_4, aE_5, aE_6, aE_7, aE_8, aE_9, aE_10, aE_11, aE_12, aE_13, aE_14, aE_15, aE_16, aE_17, aE_18, aE_19, aE_20, aE_21, aE_22, aE_23, aE_24, aE_25, aE_26, aE_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cE_conv_9 : aE 9 * Real.log (9 : ℕ) = ∑ d ∈ Nat.divisors 9, cE d * aE (9 / d) := by
  rw [show Nat.divisors 9 = {1, 3, 9} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({3, 9} : Finset ℕ) by decide), Finset.sum_insert (show (3 : ℕ) ∉ ({9} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cE, rhoE_1, rhoE_2, rhoE_3, rhoE_4, rhoE_5, rhoE_6, rhoE_7, rhoE_8, rhoE_9, rhoE_10, rhoE_11, rhoE_12, rhoE_13, rhoE_14, rhoE_15, rhoE_16, rhoE_17, rhoE_18, rhoE_19, rhoE_20, rhoE_21, rhoE_22, rhoE_23, rhoE_24, rhoE_25, rhoE_26, rhoE_27, aE_1, aE_2, aE_3, aE_4, aE_5, aE_6, aE_7, aE_8, aE_9, aE_10, aE_11, aE_12, aE_13, aE_14, aE_15, aE_16, aE_17, aE_18, aE_19, aE_20, aE_21, aE_22, aE_23, aE_24, aE_25, aE_26, aE_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cE_conv_10 : aE 10 * Real.log (10 : ℕ) = ∑ d ∈ Nat.divisors 10, cE d * aE (10 / d) := by
  rw [show Nat.divisors 10 = {1, 2, 5, 10} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({2, 5, 10} : Finset ℕ) by decide), Finset.sum_insert (show (2 : ℕ) ∉ ({5, 10} : Finset ℕ) by decide), Finset.sum_insert (show (5 : ℕ) ∉ ({10} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cE, rhoE_1, rhoE_2, rhoE_3, rhoE_4, rhoE_5, rhoE_6, rhoE_7, rhoE_8, rhoE_9, rhoE_10, rhoE_11, rhoE_12, rhoE_13, rhoE_14, rhoE_15, rhoE_16, rhoE_17, rhoE_18, rhoE_19, rhoE_20, rhoE_21, rhoE_22, rhoE_23, rhoE_24, rhoE_25, rhoE_26, rhoE_27, aE_1, aE_2, aE_3, aE_4, aE_5, aE_6, aE_7, aE_8, aE_9, aE_10, aE_11, aE_12, aE_13, aE_14, aE_15, aE_16, aE_17, aE_18, aE_19, aE_20, aE_21, aE_22, aE_23, aE_24, aE_25, aE_26, aE_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cE_conv_11 : aE 11 * Real.log (11 : ℕ) = ∑ d ∈ Nat.divisors 11, cE d * aE (11 / d) := by
  rw [show Nat.divisors 11 = {1, 11} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({11} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cE, rhoE_1, rhoE_2, rhoE_3, rhoE_4, rhoE_5, rhoE_6, rhoE_7, rhoE_8, rhoE_9, rhoE_10, rhoE_11, rhoE_12, rhoE_13, rhoE_14, rhoE_15, rhoE_16, rhoE_17, rhoE_18, rhoE_19, rhoE_20, rhoE_21, rhoE_22, rhoE_23, rhoE_24, rhoE_25, rhoE_26, rhoE_27, aE_1, aE_2, aE_3, aE_4, aE_5, aE_6, aE_7, aE_8, aE_9, aE_10, aE_11, aE_12, aE_13, aE_14, aE_15, aE_16, aE_17, aE_18, aE_19, aE_20, aE_21, aE_22, aE_23, aE_24, aE_25, aE_26, aE_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cE_conv_12 : aE 12 * Real.log (12 : ℕ) = ∑ d ∈ Nat.divisors 12, cE d * aE (12 / d) := by
  rw [show Nat.divisors 12 = {1, 2, 3, 4, 6, 12} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({2, 3, 4, 6, 12} : Finset ℕ) by decide), Finset.sum_insert (show (2 : ℕ) ∉ ({3, 4, 6, 12} : Finset ℕ) by decide), Finset.sum_insert (show (3 : ℕ) ∉ ({4, 6, 12} : Finset ℕ) by decide), Finset.sum_insert (show (4 : ℕ) ∉ ({6, 12} : Finset ℕ) by decide), Finset.sum_insert (show (6 : ℕ) ∉ ({12} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cE, rhoE_1, rhoE_2, rhoE_3, rhoE_4, rhoE_5, rhoE_6, rhoE_7, rhoE_8, rhoE_9, rhoE_10, rhoE_11, rhoE_12, rhoE_13, rhoE_14, rhoE_15, rhoE_16, rhoE_17, rhoE_18, rhoE_19, rhoE_20, rhoE_21, rhoE_22, rhoE_23, rhoE_24, rhoE_25, rhoE_26, rhoE_27, aE_1, aE_2, aE_3, aE_4, aE_5, aE_6, aE_7, aE_8, aE_9, aE_10, aE_11, aE_12, aE_13, aE_14, aE_15, aE_16, aE_17, aE_18, aE_19, aE_20, aE_21, aE_22, aE_23, aE_24, aE_25, aE_26, aE_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cE_conv_13 : aE 13 * Real.log (13 : ℕ) = ∑ d ∈ Nat.divisors 13, cE d * aE (13 / d) := by
  rw [show Nat.divisors 13 = {1, 13} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({13} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cE, rhoE_1, rhoE_2, rhoE_3, rhoE_4, rhoE_5, rhoE_6, rhoE_7, rhoE_8, rhoE_9, rhoE_10, rhoE_11, rhoE_12, rhoE_13, rhoE_14, rhoE_15, rhoE_16, rhoE_17, rhoE_18, rhoE_19, rhoE_20, rhoE_21, rhoE_22, rhoE_23, rhoE_24, rhoE_25, rhoE_26, rhoE_27, aE_1, aE_2, aE_3, aE_4, aE_5, aE_6, aE_7, aE_8, aE_9, aE_10, aE_11, aE_12, aE_13, aE_14, aE_15, aE_16, aE_17, aE_18, aE_19, aE_20, aE_21, aE_22, aE_23, aE_24, aE_25, aE_26, aE_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cE_conv_14 : aE 14 * Real.log (14 : ℕ) = ∑ d ∈ Nat.divisors 14, cE d * aE (14 / d) := by
  rw [show Nat.divisors 14 = {1, 2, 7, 14} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({2, 7, 14} : Finset ℕ) by decide), Finset.sum_insert (show (2 : ℕ) ∉ ({7, 14} : Finset ℕ) by decide), Finset.sum_insert (show (7 : ℕ) ∉ ({14} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cE, rhoE_1, rhoE_2, rhoE_3, rhoE_4, rhoE_5, rhoE_6, rhoE_7, rhoE_8, rhoE_9, rhoE_10, rhoE_11, rhoE_12, rhoE_13, rhoE_14, rhoE_15, rhoE_16, rhoE_17, rhoE_18, rhoE_19, rhoE_20, rhoE_21, rhoE_22, rhoE_23, rhoE_24, rhoE_25, rhoE_26, rhoE_27, aE_1, aE_2, aE_3, aE_4, aE_5, aE_6, aE_7, aE_8, aE_9, aE_10, aE_11, aE_12, aE_13, aE_14, aE_15, aE_16, aE_17, aE_18, aE_19, aE_20, aE_21, aE_22, aE_23, aE_24, aE_25, aE_26, aE_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cE_conv_15 : aE 15 * Real.log (15 : ℕ) = ∑ d ∈ Nat.divisors 15, cE d * aE (15 / d) := by
  rw [show Nat.divisors 15 = {1, 3, 5, 15} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({3, 5, 15} : Finset ℕ) by decide), Finset.sum_insert (show (3 : ℕ) ∉ ({5, 15} : Finset ℕ) by decide), Finset.sum_insert (show (5 : ℕ) ∉ ({15} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cE, rhoE_1, rhoE_2, rhoE_3, rhoE_4, rhoE_5, rhoE_6, rhoE_7, rhoE_8, rhoE_9, rhoE_10, rhoE_11, rhoE_12, rhoE_13, rhoE_14, rhoE_15, rhoE_16, rhoE_17, rhoE_18, rhoE_19, rhoE_20, rhoE_21, rhoE_22, rhoE_23, rhoE_24, rhoE_25, rhoE_26, rhoE_27, aE_1, aE_2, aE_3, aE_4, aE_5, aE_6, aE_7, aE_8, aE_9, aE_10, aE_11, aE_12, aE_13, aE_14, aE_15, aE_16, aE_17, aE_18, aE_19, aE_20, aE_21, aE_22, aE_23, aE_24, aE_25, aE_26, aE_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cE_conv_16 : aE 16 * Real.log (16 : ℕ) = ∑ d ∈ Nat.divisors 16, cE d * aE (16 / d) := by
  rw [show Nat.divisors 16 = {1, 2, 4, 8, 16} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({2, 4, 8, 16} : Finset ℕ) by decide), Finset.sum_insert (show (2 : ℕ) ∉ ({4, 8, 16} : Finset ℕ) by decide), Finset.sum_insert (show (4 : ℕ) ∉ ({8, 16} : Finset ℕ) by decide), Finset.sum_insert (show (8 : ℕ) ∉ ({16} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cE, rhoE_1, rhoE_2, rhoE_3, rhoE_4, rhoE_5, rhoE_6, rhoE_7, rhoE_8, rhoE_9, rhoE_10, rhoE_11, rhoE_12, rhoE_13, rhoE_14, rhoE_15, rhoE_16, rhoE_17, rhoE_18, rhoE_19, rhoE_20, rhoE_21, rhoE_22, rhoE_23, rhoE_24, rhoE_25, rhoE_26, rhoE_27, aE_1, aE_2, aE_3, aE_4, aE_5, aE_6, aE_7, aE_8, aE_9, aE_10, aE_11, aE_12, aE_13, aE_14, aE_15, aE_16, aE_17, aE_18, aE_19, aE_20, aE_21, aE_22, aE_23, aE_24, aE_25, aE_26, aE_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cE_conv_17 : aE 17 * Real.log (17 : ℕ) = ∑ d ∈ Nat.divisors 17, cE d * aE (17 / d) := by
  rw [show Nat.divisors 17 = {1, 17} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({17} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cE, rhoE_1, rhoE_2, rhoE_3, rhoE_4, rhoE_5, rhoE_6, rhoE_7, rhoE_8, rhoE_9, rhoE_10, rhoE_11, rhoE_12, rhoE_13, rhoE_14, rhoE_15, rhoE_16, rhoE_17, rhoE_18, rhoE_19, rhoE_20, rhoE_21, rhoE_22, rhoE_23, rhoE_24, rhoE_25, rhoE_26, rhoE_27, aE_1, aE_2, aE_3, aE_4, aE_5, aE_6, aE_7, aE_8, aE_9, aE_10, aE_11, aE_12, aE_13, aE_14, aE_15, aE_16, aE_17, aE_18, aE_19, aE_20, aE_21, aE_22, aE_23, aE_24, aE_25, aE_26, aE_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cE_conv_18 : aE 18 * Real.log (18 : ℕ) = ∑ d ∈ Nat.divisors 18, cE d * aE (18 / d) := by
  rw [show Nat.divisors 18 = {1, 2, 3, 6, 9, 18} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({2, 3, 6, 9, 18} : Finset ℕ) by decide), Finset.sum_insert (show (2 : ℕ) ∉ ({3, 6, 9, 18} : Finset ℕ) by decide), Finset.sum_insert (show (3 : ℕ) ∉ ({6, 9, 18} : Finset ℕ) by decide), Finset.sum_insert (show (6 : ℕ) ∉ ({9, 18} : Finset ℕ) by decide), Finset.sum_insert (show (9 : ℕ) ∉ ({18} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cE, rhoE_1, rhoE_2, rhoE_3, rhoE_4, rhoE_5, rhoE_6, rhoE_7, rhoE_8, rhoE_9, rhoE_10, rhoE_11, rhoE_12, rhoE_13, rhoE_14, rhoE_15, rhoE_16, rhoE_17, rhoE_18, rhoE_19, rhoE_20, rhoE_21, rhoE_22, rhoE_23, rhoE_24, rhoE_25, rhoE_26, rhoE_27, aE_1, aE_2, aE_3, aE_4, aE_5, aE_6, aE_7, aE_8, aE_9, aE_10, aE_11, aE_12, aE_13, aE_14, aE_15, aE_16, aE_17, aE_18, aE_19, aE_20, aE_21, aE_22, aE_23, aE_24, aE_25, aE_26, aE_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cE_conv_19 : aE 19 * Real.log (19 : ℕ) = ∑ d ∈ Nat.divisors 19, cE d * aE (19 / d) := by
  rw [show Nat.divisors 19 = {1, 19} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({19} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cE, rhoE_1, rhoE_2, rhoE_3, rhoE_4, rhoE_5, rhoE_6, rhoE_7, rhoE_8, rhoE_9, rhoE_10, rhoE_11, rhoE_12, rhoE_13, rhoE_14, rhoE_15, rhoE_16, rhoE_17, rhoE_18, rhoE_19, rhoE_20, rhoE_21, rhoE_22, rhoE_23, rhoE_24, rhoE_25, rhoE_26, rhoE_27, aE_1, aE_2, aE_3, aE_4, aE_5, aE_6, aE_7, aE_8, aE_9, aE_10, aE_11, aE_12, aE_13, aE_14, aE_15, aE_16, aE_17, aE_18, aE_19, aE_20, aE_21, aE_22, aE_23, aE_24, aE_25, aE_26, aE_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cE_conv_20 : aE 20 * Real.log (20 : ℕ) = ∑ d ∈ Nat.divisors 20, cE d * aE (20 / d) := by
  rw [show Nat.divisors 20 = {1, 2, 4, 5, 10, 20} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({2, 4, 5, 10, 20} : Finset ℕ) by decide), Finset.sum_insert (show (2 : ℕ) ∉ ({4, 5, 10, 20} : Finset ℕ) by decide), Finset.sum_insert (show (4 : ℕ) ∉ ({5, 10, 20} : Finset ℕ) by decide), Finset.sum_insert (show (5 : ℕ) ∉ ({10, 20} : Finset ℕ) by decide), Finset.sum_insert (show (10 : ℕ) ∉ ({20} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cE, rhoE_1, rhoE_2, rhoE_3, rhoE_4, rhoE_5, rhoE_6, rhoE_7, rhoE_8, rhoE_9, rhoE_10, rhoE_11, rhoE_12, rhoE_13, rhoE_14, rhoE_15, rhoE_16, rhoE_17, rhoE_18, rhoE_19, rhoE_20, rhoE_21, rhoE_22, rhoE_23, rhoE_24, rhoE_25, rhoE_26, rhoE_27, aE_1, aE_2, aE_3, aE_4, aE_5, aE_6, aE_7, aE_8, aE_9, aE_10, aE_11, aE_12, aE_13, aE_14, aE_15, aE_16, aE_17, aE_18, aE_19, aE_20, aE_21, aE_22, aE_23, aE_24, aE_25, aE_26, aE_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cE_conv_21 : aE 21 * Real.log (21 : ℕ) = ∑ d ∈ Nat.divisors 21, cE d * aE (21 / d) := by
  rw [show Nat.divisors 21 = {1, 3, 7, 21} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({3, 7, 21} : Finset ℕ) by decide), Finset.sum_insert (show (3 : ℕ) ∉ ({7, 21} : Finset ℕ) by decide), Finset.sum_insert (show (7 : ℕ) ∉ ({21} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cE, rhoE_1, rhoE_2, rhoE_3, rhoE_4, rhoE_5, rhoE_6, rhoE_7, rhoE_8, rhoE_9, rhoE_10, rhoE_11, rhoE_12, rhoE_13, rhoE_14, rhoE_15, rhoE_16, rhoE_17, rhoE_18, rhoE_19, rhoE_20, rhoE_21, rhoE_22, rhoE_23, rhoE_24, rhoE_25, rhoE_26, rhoE_27, aE_1, aE_2, aE_3, aE_4, aE_5, aE_6, aE_7, aE_8, aE_9, aE_10, aE_11, aE_12, aE_13, aE_14, aE_15, aE_16, aE_17, aE_18, aE_19, aE_20, aE_21, aE_22, aE_23, aE_24, aE_25, aE_26, aE_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cE_conv_22 : aE 22 * Real.log (22 : ℕ) = ∑ d ∈ Nat.divisors 22, cE d * aE (22 / d) := by
  rw [show Nat.divisors 22 = {1, 2, 11, 22} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({2, 11, 22} : Finset ℕ) by decide), Finset.sum_insert (show (2 : ℕ) ∉ ({11, 22} : Finset ℕ) by decide), Finset.sum_insert (show (11 : ℕ) ∉ ({22} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cE, rhoE_1, rhoE_2, rhoE_3, rhoE_4, rhoE_5, rhoE_6, rhoE_7, rhoE_8, rhoE_9, rhoE_10, rhoE_11, rhoE_12, rhoE_13, rhoE_14, rhoE_15, rhoE_16, rhoE_17, rhoE_18, rhoE_19, rhoE_20, rhoE_21, rhoE_22, rhoE_23, rhoE_24, rhoE_25, rhoE_26, rhoE_27, aE_1, aE_2, aE_3, aE_4, aE_5, aE_6, aE_7, aE_8, aE_9, aE_10, aE_11, aE_12, aE_13, aE_14, aE_15, aE_16, aE_17, aE_18, aE_19, aE_20, aE_21, aE_22, aE_23, aE_24, aE_25, aE_26, aE_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cE_conv_23 : aE 23 * Real.log (23 : ℕ) = ∑ d ∈ Nat.divisors 23, cE d * aE (23 / d) := by
  rw [show Nat.divisors 23 = {1, 23} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({23} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cE, rhoE_1, rhoE_2, rhoE_3, rhoE_4, rhoE_5, rhoE_6, rhoE_7, rhoE_8, rhoE_9, rhoE_10, rhoE_11, rhoE_12, rhoE_13, rhoE_14, rhoE_15, rhoE_16, rhoE_17, rhoE_18, rhoE_19, rhoE_20, rhoE_21, rhoE_22, rhoE_23, rhoE_24, rhoE_25, rhoE_26, rhoE_27, aE_1, aE_2, aE_3, aE_4, aE_5, aE_6, aE_7, aE_8, aE_9, aE_10, aE_11, aE_12, aE_13, aE_14, aE_15, aE_16, aE_17, aE_18, aE_19, aE_20, aE_21, aE_22, aE_23, aE_24, aE_25, aE_26, aE_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cE_conv_24 : aE 24 * Real.log (24 : ℕ) = ∑ d ∈ Nat.divisors 24, cE d * aE (24 / d) := by
  rw [show Nat.divisors 24 = {1, 2, 3, 4, 6, 8, 12, 24} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({2, 3, 4, 6, 8, 12, 24} : Finset ℕ) by decide), Finset.sum_insert (show (2 : ℕ) ∉ ({3, 4, 6, 8, 12, 24} : Finset ℕ) by decide), Finset.sum_insert (show (3 : ℕ) ∉ ({4, 6, 8, 12, 24} : Finset ℕ) by decide), Finset.sum_insert (show (4 : ℕ) ∉ ({6, 8, 12, 24} : Finset ℕ) by decide), Finset.sum_insert (show (6 : ℕ) ∉ ({8, 12, 24} : Finset ℕ) by decide), Finset.sum_insert (show (8 : ℕ) ∉ ({12, 24} : Finset ℕ) by decide), Finset.sum_insert (show (12 : ℕ) ∉ ({24} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cE, rhoE_1, rhoE_2, rhoE_3, rhoE_4, rhoE_5, rhoE_6, rhoE_7, rhoE_8, rhoE_9, rhoE_10, rhoE_11, rhoE_12, rhoE_13, rhoE_14, rhoE_15, rhoE_16, rhoE_17, rhoE_18, rhoE_19, rhoE_20, rhoE_21, rhoE_22, rhoE_23, rhoE_24, rhoE_25, rhoE_26, rhoE_27, aE_1, aE_2, aE_3, aE_4, aE_5, aE_6, aE_7, aE_8, aE_9, aE_10, aE_11, aE_12, aE_13, aE_14, aE_15, aE_16, aE_17, aE_18, aE_19, aE_20, aE_21, aE_22, aE_23, aE_24, aE_25, aE_26, aE_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cE_conv_25 : aE 25 * Real.log (25 : ℕ) = ∑ d ∈ Nat.divisors 25, cE d * aE (25 / d) := by
  rw [show Nat.divisors 25 = {1, 5, 25} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({5, 25} : Finset ℕ) by decide), Finset.sum_insert (show (5 : ℕ) ∉ ({25} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cE, rhoE_1, rhoE_2, rhoE_3, rhoE_4, rhoE_5, rhoE_6, rhoE_7, rhoE_8, rhoE_9, rhoE_10, rhoE_11, rhoE_12, rhoE_13, rhoE_14, rhoE_15, rhoE_16, rhoE_17, rhoE_18, rhoE_19, rhoE_20, rhoE_21, rhoE_22, rhoE_23, rhoE_24, rhoE_25, rhoE_26, rhoE_27, aE_1, aE_2, aE_3, aE_4, aE_5, aE_6, aE_7, aE_8, aE_9, aE_10, aE_11, aE_12, aE_13, aE_14, aE_15, aE_16, aE_17, aE_18, aE_19, aE_20, aE_21, aE_22, aE_23, aE_24, aE_25, aE_26, aE_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cE_conv_26 : aE 26 * Real.log (26 : ℕ) = ∑ d ∈ Nat.divisors 26, cE d * aE (26 / d) := by
  rw [show Nat.divisors 26 = {1, 2, 13, 26} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({2, 13, 26} : Finset ℕ) by decide), Finset.sum_insert (show (2 : ℕ) ∉ ({13, 26} : Finset ℕ) by decide), Finset.sum_insert (show (13 : ℕ) ∉ ({26} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cE, rhoE_1, rhoE_2, rhoE_3, rhoE_4, rhoE_5, rhoE_6, rhoE_7, rhoE_8, rhoE_9, rhoE_10, rhoE_11, rhoE_12, rhoE_13, rhoE_14, rhoE_15, rhoE_16, rhoE_17, rhoE_18, rhoE_19, rhoE_20, rhoE_21, rhoE_22, rhoE_23, rhoE_24, rhoE_25, rhoE_26, rhoE_27, aE_1, aE_2, aE_3, aE_4, aE_5, aE_6, aE_7, aE_8, aE_9, aE_10, aE_11, aE_12, aE_13, aE_14, aE_15, aE_16, aE_17, aE_18, aE_19, aE_20, aE_21, aE_22, aE_23, aE_24, aE_25, aE_26, aE_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cE_conv_27 : aE 27 * Real.log (27 : ℕ) = ∑ d ∈ Nat.divisors 27, cE d * aE (27 / d) := by
  rw [show Nat.divisors 27 = {1, 3, 9, 27} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({3, 9, 27} : Finset ℕ) by decide), Finset.sum_insert (show (3 : ℕ) ∉ ({9, 27} : Finset ℕ) by decide), Finset.sum_insert (show (9 : ℕ) ∉ ({27} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cE, rhoE_1, rhoE_2, rhoE_3, rhoE_4, rhoE_5, rhoE_6, rhoE_7, rhoE_8, rhoE_9, rhoE_10, rhoE_11, rhoE_12, rhoE_13, rhoE_14, rhoE_15, rhoE_16, rhoE_17, rhoE_18, rhoE_19, rhoE_20, rhoE_21, rhoE_22, rhoE_23, rhoE_24, rhoE_25, rhoE_26, rhoE_27, aE_1, aE_2, aE_3, aE_4, aE_5, aE_6, aE_7, aE_8, aE_9, aE_10, aE_11, aE_12, aE_13, aE_14, aE_15, aE_16, aE_17, aE_18, aE_19, aE_20, aE_21, aE_22, aE_23, aE_24, aE_25, aE_26, aE_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

/-- **The defining identity of `-E'/E`** (`-E' = E (-E'/E)` read coefficientwise), `n <= 27`. -/
theorem cE_conv : ∀ n : ℕ, 1 ≤ n → n ≤ 27 → aE n * Real.log n = ∑ d ∈ n.divisors, cE d * aE (n / d) := by
  intro n h1 h2
  interval_cases n
  · exact cE_conv_1
  · exact cE_conv_2
  · exact cE_conv_3
  · exact cE_conv_4
  · exact cE_conv_5
  · exact cE_conv_6
  · exact cE_conv_7
  · exact cE_conv_8
  · exact cE_conv_9
  · exact cE_conv_10
  · exact cE_conv_11
  · exact cE_conv_12
  · exact cE_conv_13
  · exact cE_conv_14
  · exact cE_conv_15
  · exact cE_conv_16
  · exact cE_conv_17
  · exact cE_conv_18
  · exact cE_conv_19
  · exact cE_conv_20
  · exact cE_conv_21
  · exact cE_conv_22
  · exact cE_conv_23
  · exact cE_conv_24
  · exact cE_conv_25
  · exact cE_conv_26
  · exact cE_conv_27

lemma aE_one : aE 1 = 1 := by rw [aE_1]; try norm_num
lemma cE_one : cE 1 = 0 := by simp [cE]

/-- **Uniqueness**: any `w` with the defining identity on `[1, 27]` equals `cE` there. -/
theorem eq_cE_of_conv (w : ℕ → ℝ)
    (hw : ∀ n : ℕ, 1 ≤ n → n ≤ 27 → aE n * Real.log n = ∑ d ∈ n.divisors, w d * aE (n / d)) :
    ∀ n : ℕ, 1 ≤ n → n ≤ 27 → w n = cE n := by
  have hw1 : w 1 = 0 := by
    have h := hw 1 le_rfl (by norm_num)
    rw [Nat.divisors_one, Finset.sum_singleton, Nat.div_self (by norm_num), aE_one, Nat.cast_one, Real.log_one,
      mul_zero, mul_one] at h
    exact h.symm
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h1 h2
    rcases Nat.eq_or_lt_of_le h1 with h | h
    · subst h; rw [hw1, cE_one]
    · have hn0 : n ≠ 0 := by omega
      have e1 := hw n h1 h2
      have e2 := cE_conv n h1 h2
      rw [← Nat.insert_self_properDivisors hn0, Finset.sum_insert Nat.self_notMem_properDivisors] at e1 e2
      rw [Nat.div_self (by omega), aE_one, mul_one] at e1 e2
      have hsum : ∑ d ∈ n.properDivisors, w d * aE (n / d) = ∑ d ∈ n.properDivisors, cE d * aE (n / d) := by
        refine Finset.sum_congr rfl fun d hd => ?_
        have hd' := Nat.mem_properDivisors.mp hd
        have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hd'.1 (by omega)
        rw [ih d hd'.2 hd1 (by omega)]
      linarith

/-! ## B. zeta_K, K = Q(sqrt -5): chi_-20, its coefficients and its weights -/

/-- The Kronecker symbol `(-20/n)` (the character of `Q(sqrt -5)`): `1` on `{1, 3, 7, 9} mod 20`,
`-1` on `{11, 13, 17, 19} mod 20`, `0` otherwise. -/
def chi20 (n : ℕ) : ℤ :=
  if n % 20 = 1 ∨ n % 20 = 3 ∨ n % 20 = 7 ∨ n % 20 = 9 then 1
  else if n % 20 = 11 ∨ n % 20 = 13 ∨ n % 20 = 17 ∨ n % 20 = 19 then -1 else 0

/-- `chi_-4`. -/
def chi4 (n : ℕ) : ℤ := if n % 4 = 1 then 1 else if n % 4 = 3 then -1 else 0

/-- `chi_5 = (./5)`. -/
def chi5 (n : ℕ) : ℤ := if n % 5 = 1 ∨ n % 5 = 4 then 1 else if n % 5 = 2 ∨ n % 5 = 3 then -1 else 0

/-- The coefficients of `zeta_K = zeta * L(chi_-20)`: `aK = 1 * chi_-20` (ideals of norm `n`). -/
def aKint (n : ℕ) : ℤ := ∑ d ∈ n.divisors, chi20 d

/-- The coefficients of the genus product `L(chi_-4) L(chi_5)`. -/
def aGint (n : ℕ) : ℤ := ∑ d ∈ n.divisors, chi4 d * chi5 (n / d)

/-- `chi_-20 = chi_-4 chi_5` on `[0, 40)` (hence everywhere, both sides having period 20). -/
theorem chi20_eq_mul : ∀ n ∈ List.range 40, chi20 n = chi4 n * chi5 n := by decide

/-- **`E = (zeta_K + L(chi_-4) L(chi_5))/2`** at the level of coefficients, `n <= 27`:
`2 aE(n) = aK(n) + aG(n)` (i.e. the lattice count equals `aK + aG`). -/
theorem aE_eq_half_sum : ∀ n ∈ List.range 28, 1 ≤ n → (aEcount n : ℤ) = aKint n + aGint n := by
  decide +kernel

def aK (n : ℕ) : ℝ := (aKint n : ℝ)

/-- The weights of `-zeta_K'/zeta_K`: `Lambda(n) (1 + chi_-20(n))`, supported on prime powers. -/
def cK (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n * (1 + (chi20 n : ℝ))

/-- `c_K(n)/log n` on `[1, 27]`. -/
def rhoK : ℕ → ℚ
  | 2 => (1 : ℚ)
  | 3 => (2 : ℚ)
  | 4 => ((1 : ℚ) / 2)
  | 5 => (1 : ℚ)
  | 7 => (2 : ℚ)
  | 8 => ((1 : ℚ) / 3)
  | 9 => (1 : ℚ)
  | 16 => ((1 : ℚ) / 4)
  | 23 => (2 : ℚ)
  | 25 => ((1 : ℚ) / 2)
  | 27 => ((2 : ℚ) / 3)
  | _ => 0

lemma rhoK_1 : rhoK 1 = (0 : ℚ) := rfl
lemma rhoK_2 : rhoK 2 = (1 : ℚ) := rfl
lemma rhoK_3 : rhoK 3 = (2 : ℚ) := rfl
lemma rhoK_4 : rhoK 4 = ((1 : ℚ) / 2) := rfl
lemma rhoK_5 : rhoK 5 = (1 : ℚ) := rfl
lemma rhoK_6 : rhoK 6 = (0 : ℚ) := rfl
lemma rhoK_7 : rhoK 7 = (2 : ℚ) := rfl
lemma rhoK_8 : rhoK 8 = ((1 : ℚ) / 3) := rfl
lemma rhoK_9 : rhoK 9 = (1 : ℚ) := rfl
lemma rhoK_10 : rhoK 10 = (0 : ℚ) := rfl
lemma rhoK_11 : rhoK 11 = (0 : ℚ) := rfl
lemma rhoK_12 : rhoK 12 = (0 : ℚ) := rfl
lemma rhoK_13 : rhoK 13 = (0 : ℚ) := rfl
lemma rhoK_14 : rhoK 14 = (0 : ℚ) := rfl
lemma rhoK_15 : rhoK 15 = (0 : ℚ) := rfl
lemma rhoK_16 : rhoK 16 = ((1 : ℚ) / 4) := rfl
lemma rhoK_17 : rhoK 17 = (0 : ℚ) := rfl
lemma rhoK_18 : rhoK 18 = (0 : ℚ) := rfl
lemma rhoK_19 : rhoK 19 = (0 : ℚ) := rfl
lemma rhoK_20 : rhoK 20 = (0 : ℚ) := rfl
lemma rhoK_21 : rhoK 21 = (0 : ℚ) := rfl
lemma rhoK_22 : rhoK 22 = (0 : ℚ) := rfl
lemma rhoK_23 : rhoK 23 = (2 : ℚ) := rfl
lemma rhoK_24 : rhoK 24 = (0 : ℚ) := rfl
lemma rhoK_25 : rhoK 25 = ((1 : ℚ) / 2) := rfl
lemma rhoK_26 : rhoK 26 = (0 : ℚ) := rfl
lemma rhoK_27 : rhoK 27 = ((2 : ℚ) / 3) := rfl
/-- `aK` table. -/
def aKtab : ℕ → ℤ
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | 4 => 1
  | 5 => 1
  | 6 => 2
  | 7 => 2
  | 8 => 1
  | 9 => 3
  | 10 => 1
  | 12 => 2
  | 14 => 2
  | 15 => 2
  | 16 => 1
  | 18 => 3
  | 20 => 1
  | 21 => 4
  | 23 => 2
  | 24 => 2
  | 25 => 1
  | 27 => 4
  | _ => 0


lemma aK_of_tab : ∀ n ∈ List.range 28, aKint n = aKtab n := by decide

lemma aK_1 : aK 1 = 1 := by unfold aK; rw [aK_of_tab 1 (by decide)]; norm_num [aKtab]
lemma aK_2 : aK 2 = 1 := by unfold aK; rw [aK_of_tab 2 (by decide)]; norm_num [aKtab]
lemma aK_3 : aK 3 = 2 := by unfold aK; rw [aK_of_tab 3 (by decide)]; norm_num [aKtab]
lemma aK_4 : aK 4 = 1 := by unfold aK; rw [aK_of_tab 4 (by decide)]; norm_num [aKtab]
lemma aK_5 : aK 5 = 1 := by unfold aK; rw [aK_of_tab 5 (by decide)]; norm_num [aKtab]
lemma aK_6 : aK 6 = 2 := by unfold aK; rw [aK_of_tab 6 (by decide)]; norm_num [aKtab]
lemma aK_7 : aK 7 = 2 := by unfold aK; rw [aK_of_tab 7 (by decide)]; norm_num [aKtab]
lemma aK_8 : aK 8 = 1 := by unfold aK; rw [aK_of_tab 8 (by decide)]; norm_num [aKtab]
lemma aK_9 : aK 9 = 3 := by unfold aK; rw [aK_of_tab 9 (by decide)]; norm_num [aKtab]
lemma aK_10 : aK 10 = 1 := by unfold aK; rw [aK_of_tab 10 (by decide)]; norm_num [aKtab]
lemma aK_11 : aK 11 = 0 := by unfold aK; rw [aK_of_tab 11 (by decide)]; norm_num [aKtab]
lemma aK_12 : aK 12 = 2 := by unfold aK; rw [aK_of_tab 12 (by decide)]; norm_num [aKtab]
lemma aK_13 : aK 13 = 0 := by unfold aK; rw [aK_of_tab 13 (by decide)]; norm_num [aKtab]
lemma aK_14 : aK 14 = 2 := by unfold aK; rw [aK_of_tab 14 (by decide)]; norm_num [aKtab]
lemma aK_15 : aK 15 = 2 := by unfold aK; rw [aK_of_tab 15 (by decide)]; norm_num [aKtab]
lemma aK_16 : aK 16 = 1 := by unfold aK; rw [aK_of_tab 16 (by decide)]; norm_num [aKtab]
lemma aK_17 : aK 17 = 0 := by unfold aK; rw [aK_of_tab 17 (by decide)]; norm_num [aKtab]
lemma aK_18 : aK 18 = 3 := by unfold aK; rw [aK_of_tab 18 (by decide)]; norm_num [aKtab]
lemma aK_19 : aK 19 = 0 := by unfold aK; rw [aK_of_tab 19 (by decide)]; norm_num [aKtab]
lemma aK_20 : aK 20 = 1 := by unfold aK; rw [aK_of_tab 20 (by decide)]; norm_num [aKtab]
lemma aK_21 : aK 21 = 4 := by unfold aK; rw [aK_of_tab 21 (by decide)]; norm_num [aKtab]
lemma aK_22 : aK 22 = 0 := by unfold aK; rw [aK_of_tab 22 (by decide)]; norm_num [aKtab]
lemma aK_23 : aK 23 = 2 := by unfold aK; rw [aK_of_tab 23 (by decide)]; norm_num [aKtab]
lemma aK_24 : aK 24 = 2 := by unfold aK; rw [aK_of_tab 24 (by decide)]; norm_num [aKtab]
lemma aK_25 : aK 25 = 1 := by unfold aK; rw [aK_of_tab 25 (by decide)]; norm_num [aKtab]
lemma aK_26 : aK 26 = 0 := by unfold aK; rw [aK_of_tab 26 (by decide)]; norm_num [aKtab]
lemma aK_27 : aK 27 = 4 := by unfold aK; rw [aK_of_tab 27 (by decide)]; norm_num [aKtab]

/-- `cK n = rhoK n * log n` on `[1, 27]` (from `Lambda(n) = mu_n log n`, Crux3's `lam_tab`). -/
theorem cK_eq : ∀ n : ℕ, n ≤ 27 → cK n = (rhoK n : ℝ) * Real.log n := by
  intro n hn
  unfold cK
  rw [Crux3.lam_tab n (by omega)]
  interval_cases n <;> norm_num [Crux3.tab, chi20, rhoK] <;> ring

/-- `cK` in `rho log` form (for the per-`n` identities). -/
def cK' (n : ℕ) : ℝ := (rhoK n : ℝ) * Real.log n

lemma cK_conv'_1 : aK 1 * Real.log (1 : ℕ) = ∑ d ∈ Nat.divisors 1, cK' d * aK (1 / d) := by
  rw [show Nat.divisors 1 = {1} by decide]
  simp only [Finset.sum_singleton]
  norm_num [cK', rhoK_1, rhoK_2, rhoK_3, rhoK_4, rhoK_5, rhoK_6, rhoK_7, rhoK_8, rhoK_9, rhoK_10, rhoK_11, rhoK_12, rhoK_13, rhoK_14, rhoK_15, rhoK_16, rhoK_17, rhoK_18, rhoK_19, rhoK_20, rhoK_21, rhoK_22, rhoK_23, rhoK_24, rhoK_25, rhoK_26, rhoK_27, aK_1, aK_2, aK_3, aK_4, aK_5, aK_6, aK_7, aK_8, aK_9, aK_10, aK_11, aK_12, aK_13, aK_14, aK_15, aK_16, aK_17, aK_18, aK_19, aK_20, aK_21, aK_22, aK_23, aK_24, aK_25, aK_26, aK_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cK_conv'_2 : aK 2 * Real.log (2 : ℕ) = ∑ d ∈ Nat.divisors 2, cK' d * aK (2 / d) := by
  rw [show Nat.divisors 2 = {1, 2} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({2} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cK', rhoK_1, rhoK_2, rhoK_3, rhoK_4, rhoK_5, rhoK_6, rhoK_7, rhoK_8, rhoK_9, rhoK_10, rhoK_11, rhoK_12, rhoK_13, rhoK_14, rhoK_15, rhoK_16, rhoK_17, rhoK_18, rhoK_19, rhoK_20, rhoK_21, rhoK_22, rhoK_23, rhoK_24, rhoK_25, rhoK_26, rhoK_27, aK_1, aK_2, aK_3, aK_4, aK_5, aK_6, aK_7, aK_8, aK_9, aK_10, aK_11, aK_12, aK_13, aK_14, aK_15, aK_16, aK_17, aK_18, aK_19, aK_20, aK_21, aK_22, aK_23, aK_24, aK_25, aK_26, aK_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cK_conv'_3 : aK 3 * Real.log (3 : ℕ) = ∑ d ∈ Nat.divisors 3, cK' d * aK (3 / d) := by
  rw [show Nat.divisors 3 = {1, 3} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({3} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cK', rhoK_1, rhoK_2, rhoK_3, rhoK_4, rhoK_5, rhoK_6, rhoK_7, rhoK_8, rhoK_9, rhoK_10, rhoK_11, rhoK_12, rhoK_13, rhoK_14, rhoK_15, rhoK_16, rhoK_17, rhoK_18, rhoK_19, rhoK_20, rhoK_21, rhoK_22, rhoK_23, rhoK_24, rhoK_25, rhoK_26, rhoK_27, aK_1, aK_2, aK_3, aK_4, aK_5, aK_6, aK_7, aK_8, aK_9, aK_10, aK_11, aK_12, aK_13, aK_14, aK_15, aK_16, aK_17, aK_18, aK_19, aK_20, aK_21, aK_22, aK_23, aK_24, aK_25, aK_26, aK_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cK_conv'_4 : aK 4 * Real.log (4 : ℕ) = ∑ d ∈ Nat.divisors 4, cK' d * aK (4 / d) := by
  rw [show Nat.divisors 4 = {1, 2, 4} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({2, 4} : Finset ℕ) by decide), Finset.sum_insert (show (2 : ℕ) ∉ ({4} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cK', rhoK_1, rhoK_2, rhoK_3, rhoK_4, rhoK_5, rhoK_6, rhoK_7, rhoK_8, rhoK_9, rhoK_10, rhoK_11, rhoK_12, rhoK_13, rhoK_14, rhoK_15, rhoK_16, rhoK_17, rhoK_18, rhoK_19, rhoK_20, rhoK_21, rhoK_22, rhoK_23, rhoK_24, rhoK_25, rhoK_26, rhoK_27, aK_1, aK_2, aK_3, aK_4, aK_5, aK_6, aK_7, aK_8, aK_9, aK_10, aK_11, aK_12, aK_13, aK_14, aK_15, aK_16, aK_17, aK_18, aK_19, aK_20, aK_21, aK_22, aK_23, aK_24, aK_25, aK_26, aK_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cK_conv'_5 : aK 5 * Real.log (5 : ℕ) = ∑ d ∈ Nat.divisors 5, cK' d * aK (5 / d) := by
  rw [show Nat.divisors 5 = {1, 5} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({5} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cK', rhoK_1, rhoK_2, rhoK_3, rhoK_4, rhoK_5, rhoK_6, rhoK_7, rhoK_8, rhoK_9, rhoK_10, rhoK_11, rhoK_12, rhoK_13, rhoK_14, rhoK_15, rhoK_16, rhoK_17, rhoK_18, rhoK_19, rhoK_20, rhoK_21, rhoK_22, rhoK_23, rhoK_24, rhoK_25, rhoK_26, rhoK_27, aK_1, aK_2, aK_3, aK_4, aK_5, aK_6, aK_7, aK_8, aK_9, aK_10, aK_11, aK_12, aK_13, aK_14, aK_15, aK_16, aK_17, aK_18, aK_19, aK_20, aK_21, aK_22, aK_23, aK_24, aK_25, aK_26, aK_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cK_conv'_6 : aK 6 * Real.log (6 : ℕ) = ∑ d ∈ Nat.divisors 6, cK' d * aK (6 / d) := by
  rw [show Nat.divisors 6 = {1, 2, 3, 6} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({2, 3, 6} : Finset ℕ) by decide), Finset.sum_insert (show (2 : ℕ) ∉ ({3, 6} : Finset ℕ) by decide), Finset.sum_insert (show (3 : ℕ) ∉ ({6} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cK', rhoK_1, rhoK_2, rhoK_3, rhoK_4, rhoK_5, rhoK_6, rhoK_7, rhoK_8, rhoK_9, rhoK_10, rhoK_11, rhoK_12, rhoK_13, rhoK_14, rhoK_15, rhoK_16, rhoK_17, rhoK_18, rhoK_19, rhoK_20, rhoK_21, rhoK_22, rhoK_23, rhoK_24, rhoK_25, rhoK_26, rhoK_27, aK_1, aK_2, aK_3, aK_4, aK_5, aK_6, aK_7, aK_8, aK_9, aK_10, aK_11, aK_12, aK_13, aK_14, aK_15, aK_16, aK_17, aK_18, aK_19, aK_20, aK_21, aK_22, aK_23, aK_24, aK_25, aK_26, aK_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cK_conv'_7 : aK 7 * Real.log (7 : ℕ) = ∑ d ∈ Nat.divisors 7, cK' d * aK (7 / d) := by
  rw [show Nat.divisors 7 = {1, 7} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({7} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cK', rhoK_1, rhoK_2, rhoK_3, rhoK_4, rhoK_5, rhoK_6, rhoK_7, rhoK_8, rhoK_9, rhoK_10, rhoK_11, rhoK_12, rhoK_13, rhoK_14, rhoK_15, rhoK_16, rhoK_17, rhoK_18, rhoK_19, rhoK_20, rhoK_21, rhoK_22, rhoK_23, rhoK_24, rhoK_25, rhoK_26, rhoK_27, aK_1, aK_2, aK_3, aK_4, aK_5, aK_6, aK_7, aK_8, aK_9, aK_10, aK_11, aK_12, aK_13, aK_14, aK_15, aK_16, aK_17, aK_18, aK_19, aK_20, aK_21, aK_22, aK_23, aK_24, aK_25, aK_26, aK_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cK_conv'_8 : aK 8 * Real.log (8 : ℕ) = ∑ d ∈ Nat.divisors 8, cK' d * aK (8 / d) := by
  rw [show Nat.divisors 8 = {1, 2, 4, 8} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({2, 4, 8} : Finset ℕ) by decide), Finset.sum_insert (show (2 : ℕ) ∉ ({4, 8} : Finset ℕ) by decide), Finset.sum_insert (show (4 : ℕ) ∉ ({8} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cK', rhoK_1, rhoK_2, rhoK_3, rhoK_4, rhoK_5, rhoK_6, rhoK_7, rhoK_8, rhoK_9, rhoK_10, rhoK_11, rhoK_12, rhoK_13, rhoK_14, rhoK_15, rhoK_16, rhoK_17, rhoK_18, rhoK_19, rhoK_20, rhoK_21, rhoK_22, rhoK_23, rhoK_24, rhoK_25, rhoK_26, rhoK_27, aK_1, aK_2, aK_3, aK_4, aK_5, aK_6, aK_7, aK_8, aK_9, aK_10, aK_11, aK_12, aK_13, aK_14, aK_15, aK_16, aK_17, aK_18, aK_19, aK_20, aK_21, aK_22, aK_23, aK_24, aK_25, aK_26, aK_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cK_conv'_9 : aK 9 * Real.log (9 : ℕ) = ∑ d ∈ Nat.divisors 9, cK' d * aK (9 / d) := by
  rw [show Nat.divisors 9 = {1, 3, 9} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({3, 9} : Finset ℕ) by decide), Finset.sum_insert (show (3 : ℕ) ∉ ({9} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cK', rhoK_1, rhoK_2, rhoK_3, rhoK_4, rhoK_5, rhoK_6, rhoK_7, rhoK_8, rhoK_9, rhoK_10, rhoK_11, rhoK_12, rhoK_13, rhoK_14, rhoK_15, rhoK_16, rhoK_17, rhoK_18, rhoK_19, rhoK_20, rhoK_21, rhoK_22, rhoK_23, rhoK_24, rhoK_25, rhoK_26, rhoK_27, aK_1, aK_2, aK_3, aK_4, aK_5, aK_6, aK_7, aK_8, aK_9, aK_10, aK_11, aK_12, aK_13, aK_14, aK_15, aK_16, aK_17, aK_18, aK_19, aK_20, aK_21, aK_22, aK_23, aK_24, aK_25, aK_26, aK_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cK_conv'_10 : aK 10 * Real.log (10 : ℕ) = ∑ d ∈ Nat.divisors 10, cK' d * aK (10 / d) := by
  rw [show Nat.divisors 10 = {1, 2, 5, 10} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({2, 5, 10} : Finset ℕ) by decide), Finset.sum_insert (show (2 : ℕ) ∉ ({5, 10} : Finset ℕ) by decide), Finset.sum_insert (show (5 : ℕ) ∉ ({10} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cK', rhoK_1, rhoK_2, rhoK_3, rhoK_4, rhoK_5, rhoK_6, rhoK_7, rhoK_8, rhoK_9, rhoK_10, rhoK_11, rhoK_12, rhoK_13, rhoK_14, rhoK_15, rhoK_16, rhoK_17, rhoK_18, rhoK_19, rhoK_20, rhoK_21, rhoK_22, rhoK_23, rhoK_24, rhoK_25, rhoK_26, rhoK_27, aK_1, aK_2, aK_3, aK_4, aK_5, aK_6, aK_7, aK_8, aK_9, aK_10, aK_11, aK_12, aK_13, aK_14, aK_15, aK_16, aK_17, aK_18, aK_19, aK_20, aK_21, aK_22, aK_23, aK_24, aK_25, aK_26, aK_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cK_conv'_11 : aK 11 * Real.log (11 : ℕ) = ∑ d ∈ Nat.divisors 11, cK' d * aK (11 / d) := by
  rw [show Nat.divisors 11 = {1, 11} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({11} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cK', rhoK_1, rhoK_2, rhoK_3, rhoK_4, rhoK_5, rhoK_6, rhoK_7, rhoK_8, rhoK_9, rhoK_10, rhoK_11, rhoK_12, rhoK_13, rhoK_14, rhoK_15, rhoK_16, rhoK_17, rhoK_18, rhoK_19, rhoK_20, rhoK_21, rhoK_22, rhoK_23, rhoK_24, rhoK_25, rhoK_26, rhoK_27, aK_1, aK_2, aK_3, aK_4, aK_5, aK_6, aK_7, aK_8, aK_9, aK_10, aK_11, aK_12, aK_13, aK_14, aK_15, aK_16, aK_17, aK_18, aK_19, aK_20, aK_21, aK_22, aK_23, aK_24, aK_25, aK_26, aK_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cK_conv'_12 : aK 12 * Real.log (12 : ℕ) = ∑ d ∈ Nat.divisors 12, cK' d * aK (12 / d) := by
  rw [show Nat.divisors 12 = {1, 2, 3, 4, 6, 12} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({2, 3, 4, 6, 12} : Finset ℕ) by decide), Finset.sum_insert (show (2 : ℕ) ∉ ({3, 4, 6, 12} : Finset ℕ) by decide), Finset.sum_insert (show (3 : ℕ) ∉ ({4, 6, 12} : Finset ℕ) by decide), Finset.sum_insert (show (4 : ℕ) ∉ ({6, 12} : Finset ℕ) by decide), Finset.sum_insert (show (6 : ℕ) ∉ ({12} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cK', rhoK_1, rhoK_2, rhoK_3, rhoK_4, rhoK_5, rhoK_6, rhoK_7, rhoK_8, rhoK_9, rhoK_10, rhoK_11, rhoK_12, rhoK_13, rhoK_14, rhoK_15, rhoK_16, rhoK_17, rhoK_18, rhoK_19, rhoK_20, rhoK_21, rhoK_22, rhoK_23, rhoK_24, rhoK_25, rhoK_26, rhoK_27, aK_1, aK_2, aK_3, aK_4, aK_5, aK_6, aK_7, aK_8, aK_9, aK_10, aK_11, aK_12, aK_13, aK_14, aK_15, aK_16, aK_17, aK_18, aK_19, aK_20, aK_21, aK_22, aK_23, aK_24, aK_25, aK_26, aK_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cK_conv'_13 : aK 13 * Real.log (13 : ℕ) = ∑ d ∈ Nat.divisors 13, cK' d * aK (13 / d) := by
  rw [show Nat.divisors 13 = {1, 13} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({13} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cK', rhoK_1, rhoK_2, rhoK_3, rhoK_4, rhoK_5, rhoK_6, rhoK_7, rhoK_8, rhoK_9, rhoK_10, rhoK_11, rhoK_12, rhoK_13, rhoK_14, rhoK_15, rhoK_16, rhoK_17, rhoK_18, rhoK_19, rhoK_20, rhoK_21, rhoK_22, rhoK_23, rhoK_24, rhoK_25, rhoK_26, rhoK_27, aK_1, aK_2, aK_3, aK_4, aK_5, aK_6, aK_7, aK_8, aK_9, aK_10, aK_11, aK_12, aK_13, aK_14, aK_15, aK_16, aK_17, aK_18, aK_19, aK_20, aK_21, aK_22, aK_23, aK_24, aK_25, aK_26, aK_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cK_conv'_14 : aK 14 * Real.log (14 : ℕ) = ∑ d ∈ Nat.divisors 14, cK' d * aK (14 / d) := by
  rw [show Nat.divisors 14 = {1, 2, 7, 14} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({2, 7, 14} : Finset ℕ) by decide), Finset.sum_insert (show (2 : ℕ) ∉ ({7, 14} : Finset ℕ) by decide), Finset.sum_insert (show (7 : ℕ) ∉ ({14} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cK', rhoK_1, rhoK_2, rhoK_3, rhoK_4, rhoK_5, rhoK_6, rhoK_7, rhoK_8, rhoK_9, rhoK_10, rhoK_11, rhoK_12, rhoK_13, rhoK_14, rhoK_15, rhoK_16, rhoK_17, rhoK_18, rhoK_19, rhoK_20, rhoK_21, rhoK_22, rhoK_23, rhoK_24, rhoK_25, rhoK_26, rhoK_27, aK_1, aK_2, aK_3, aK_4, aK_5, aK_6, aK_7, aK_8, aK_9, aK_10, aK_11, aK_12, aK_13, aK_14, aK_15, aK_16, aK_17, aK_18, aK_19, aK_20, aK_21, aK_22, aK_23, aK_24, aK_25, aK_26, aK_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cK_conv'_15 : aK 15 * Real.log (15 : ℕ) = ∑ d ∈ Nat.divisors 15, cK' d * aK (15 / d) := by
  rw [show Nat.divisors 15 = {1, 3, 5, 15} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({3, 5, 15} : Finset ℕ) by decide), Finset.sum_insert (show (3 : ℕ) ∉ ({5, 15} : Finset ℕ) by decide), Finset.sum_insert (show (5 : ℕ) ∉ ({15} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cK', rhoK_1, rhoK_2, rhoK_3, rhoK_4, rhoK_5, rhoK_6, rhoK_7, rhoK_8, rhoK_9, rhoK_10, rhoK_11, rhoK_12, rhoK_13, rhoK_14, rhoK_15, rhoK_16, rhoK_17, rhoK_18, rhoK_19, rhoK_20, rhoK_21, rhoK_22, rhoK_23, rhoK_24, rhoK_25, rhoK_26, rhoK_27, aK_1, aK_2, aK_3, aK_4, aK_5, aK_6, aK_7, aK_8, aK_9, aK_10, aK_11, aK_12, aK_13, aK_14, aK_15, aK_16, aK_17, aK_18, aK_19, aK_20, aK_21, aK_22, aK_23, aK_24, aK_25, aK_26, aK_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cK_conv'_16 : aK 16 * Real.log (16 : ℕ) = ∑ d ∈ Nat.divisors 16, cK' d * aK (16 / d) := by
  rw [show Nat.divisors 16 = {1, 2, 4, 8, 16} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({2, 4, 8, 16} : Finset ℕ) by decide), Finset.sum_insert (show (2 : ℕ) ∉ ({4, 8, 16} : Finset ℕ) by decide), Finset.sum_insert (show (4 : ℕ) ∉ ({8, 16} : Finset ℕ) by decide), Finset.sum_insert (show (8 : ℕ) ∉ ({16} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cK', rhoK_1, rhoK_2, rhoK_3, rhoK_4, rhoK_5, rhoK_6, rhoK_7, rhoK_8, rhoK_9, rhoK_10, rhoK_11, rhoK_12, rhoK_13, rhoK_14, rhoK_15, rhoK_16, rhoK_17, rhoK_18, rhoK_19, rhoK_20, rhoK_21, rhoK_22, rhoK_23, rhoK_24, rhoK_25, rhoK_26, rhoK_27, aK_1, aK_2, aK_3, aK_4, aK_5, aK_6, aK_7, aK_8, aK_9, aK_10, aK_11, aK_12, aK_13, aK_14, aK_15, aK_16, aK_17, aK_18, aK_19, aK_20, aK_21, aK_22, aK_23, aK_24, aK_25, aK_26, aK_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cK_conv'_17 : aK 17 * Real.log (17 : ℕ) = ∑ d ∈ Nat.divisors 17, cK' d * aK (17 / d) := by
  rw [show Nat.divisors 17 = {1, 17} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({17} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cK', rhoK_1, rhoK_2, rhoK_3, rhoK_4, rhoK_5, rhoK_6, rhoK_7, rhoK_8, rhoK_9, rhoK_10, rhoK_11, rhoK_12, rhoK_13, rhoK_14, rhoK_15, rhoK_16, rhoK_17, rhoK_18, rhoK_19, rhoK_20, rhoK_21, rhoK_22, rhoK_23, rhoK_24, rhoK_25, rhoK_26, rhoK_27, aK_1, aK_2, aK_3, aK_4, aK_5, aK_6, aK_7, aK_8, aK_9, aK_10, aK_11, aK_12, aK_13, aK_14, aK_15, aK_16, aK_17, aK_18, aK_19, aK_20, aK_21, aK_22, aK_23, aK_24, aK_25, aK_26, aK_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cK_conv'_18 : aK 18 * Real.log (18 : ℕ) = ∑ d ∈ Nat.divisors 18, cK' d * aK (18 / d) := by
  rw [show Nat.divisors 18 = {1, 2, 3, 6, 9, 18} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({2, 3, 6, 9, 18} : Finset ℕ) by decide), Finset.sum_insert (show (2 : ℕ) ∉ ({3, 6, 9, 18} : Finset ℕ) by decide), Finset.sum_insert (show (3 : ℕ) ∉ ({6, 9, 18} : Finset ℕ) by decide), Finset.sum_insert (show (6 : ℕ) ∉ ({9, 18} : Finset ℕ) by decide), Finset.sum_insert (show (9 : ℕ) ∉ ({18} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cK', rhoK_1, rhoK_2, rhoK_3, rhoK_4, rhoK_5, rhoK_6, rhoK_7, rhoK_8, rhoK_9, rhoK_10, rhoK_11, rhoK_12, rhoK_13, rhoK_14, rhoK_15, rhoK_16, rhoK_17, rhoK_18, rhoK_19, rhoK_20, rhoK_21, rhoK_22, rhoK_23, rhoK_24, rhoK_25, rhoK_26, rhoK_27, aK_1, aK_2, aK_3, aK_4, aK_5, aK_6, aK_7, aK_8, aK_9, aK_10, aK_11, aK_12, aK_13, aK_14, aK_15, aK_16, aK_17, aK_18, aK_19, aK_20, aK_21, aK_22, aK_23, aK_24, aK_25, aK_26, aK_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cK_conv'_19 : aK 19 * Real.log (19 : ℕ) = ∑ d ∈ Nat.divisors 19, cK' d * aK (19 / d) := by
  rw [show Nat.divisors 19 = {1, 19} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({19} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cK', rhoK_1, rhoK_2, rhoK_3, rhoK_4, rhoK_5, rhoK_6, rhoK_7, rhoK_8, rhoK_9, rhoK_10, rhoK_11, rhoK_12, rhoK_13, rhoK_14, rhoK_15, rhoK_16, rhoK_17, rhoK_18, rhoK_19, rhoK_20, rhoK_21, rhoK_22, rhoK_23, rhoK_24, rhoK_25, rhoK_26, rhoK_27, aK_1, aK_2, aK_3, aK_4, aK_5, aK_6, aK_7, aK_8, aK_9, aK_10, aK_11, aK_12, aK_13, aK_14, aK_15, aK_16, aK_17, aK_18, aK_19, aK_20, aK_21, aK_22, aK_23, aK_24, aK_25, aK_26, aK_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cK_conv'_20 : aK 20 * Real.log (20 : ℕ) = ∑ d ∈ Nat.divisors 20, cK' d * aK (20 / d) := by
  rw [show Nat.divisors 20 = {1, 2, 4, 5, 10, 20} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({2, 4, 5, 10, 20} : Finset ℕ) by decide), Finset.sum_insert (show (2 : ℕ) ∉ ({4, 5, 10, 20} : Finset ℕ) by decide), Finset.sum_insert (show (4 : ℕ) ∉ ({5, 10, 20} : Finset ℕ) by decide), Finset.sum_insert (show (5 : ℕ) ∉ ({10, 20} : Finset ℕ) by decide), Finset.sum_insert (show (10 : ℕ) ∉ ({20} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cK', rhoK_1, rhoK_2, rhoK_3, rhoK_4, rhoK_5, rhoK_6, rhoK_7, rhoK_8, rhoK_9, rhoK_10, rhoK_11, rhoK_12, rhoK_13, rhoK_14, rhoK_15, rhoK_16, rhoK_17, rhoK_18, rhoK_19, rhoK_20, rhoK_21, rhoK_22, rhoK_23, rhoK_24, rhoK_25, rhoK_26, rhoK_27, aK_1, aK_2, aK_3, aK_4, aK_5, aK_6, aK_7, aK_8, aK_9, aK_10, aK_11, aK_12, aK_13, aK_14, aK_15, aK_16, aK_17, aK_18, aK_19, aK_20, aK_21, aK_22, aK_23, aK_24, aK_25, aK_26, aK_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cK_conv'_21 : aK 21 * Real.log (21 : ℕ) = ∑ d ∈ Nat.divisors 21, cK' d * aK (21 / d) := by
  rw [show Nat.divisors 21 = {1, 3, 7, 21} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({3, 7, 21} : Finset ℕ) by decide), Finset.sum_insert (show (3 : ℕ) ∉ ({7, 21} : Finset ℕ) by decide), Finset.sum_insert (show (7 : ℕ) ∉ ({21} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cK', rhoK_1, rhoK_2, rhoK_3, rhoK_4, rhoK_5, rhoK_6, rhoK_7, rhoK_8, rhoK_9, rhoK_10, rhoK_11, rhoK_12, rhoK_13, rhoK_14, rhoK_15, rhoK_16, rhoK_17, rhoK_18, rhoK_19, rhoK_20, rhoK_21, rhoK_22, rhoK_23, rhoK_24, rhoK_25, rhoK_26, rhoK_27, aK_1, aK_2, aK_3, aK_4, aK_5, aK_6, aK_7, aK_8, aK_9, aK_10, aK_11, aK_12, aK_13, aK_14, aK_15, aK_16, aK_17, aK_18, aK_19, aK_20, aK_21, aK_22, aK_23, aK_24, aK_25, aK_26, aK_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cK_conv'_22 : aK 22 * Real.log (22 : ℕ) = ∑ d ∈ Nat.divisors 22, cK' d * aK (22 / d) := by
  rw [show Nat.divisors 22 = {1, 2, 11, 22} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({2, 11, 22} : Finset ℕ) by decide), Finset.sum_insert (show (2 : ℕ) ∉ ({11, 22} : Finset ℕ) by decide), Finset.sum_insert (show (11 : ℕ) ∉ ({22} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cK', rhoK_1, rhoK_2, rhoK_3, rhoK_4, rhoK_5, rhoK_6, rhoK_7, rhoK_8, rhoK_9, rhoK_10, rhoK_11, rhoK_12, rhoK_13, rhoK_14, rhoK_15, rhoK_16, rhoK_17, rhoK_18, rhoK_19, rhoK_20, rhoK_21, rhoK_22, rhoK_23, rhoK_24, rhoK_25, rhoK_26, rhoK_27, aK_1, aK_2, aK_3, aK_4, aK_5, aK_6, aK_7, aK_8, aK_9, aK_10, aK_11, aK_12, aK_13, aK_14, aK_15, aK_16, aK_17, aK_18, aK_19, aK_20, aK_21, aK_22, aK_23, aK_24, aK_25, aK_26, aK_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cK_conv'_23 : aK 23 * Real.log (23 : ℕ) = ∑ d ∈ Nat.divisors 23, cK' d * aK (23 / d) := by
  rw [show Nat.divisors 23 = {1, 23} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({23} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cK', rhoK_1, rhoK_2, rhoK_3, rhoK_4, rhoK_5, rhoK_6, rhoK_7, rhoK_8, rhoK_9, rhoK_10, rhoK_11, rhoK_12, rhoK_13, rhoK_14, rhoK_15, rhoK_16, rhoK_17, rhoK_18, rhoK_19, rhoK_20, rhoK_21, rhoK_22, rhoK_23, rhoK_24, rhoK_25, rhoK_26, rhoK_27, aK_1, aK_2, aK_3, aK_4, aK_5, aK_6, aK_7, aK_8, aK_9, aK_10, aK_11, aK_12, aK_13, aK_14, aK_15, aK_16, aK_17, aK_18, aK_19, aK_20, aK_21, aK_22, aK_23, aK_24, aK_25, aK_26, aK_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cK_conv'_24 : aK 24 * Real.log (24 : ℕ) = ∑ d ∈ Nat.divisors 24, cK' d * aK (24 / d) := by
  rw [show Nat.divisors 24 = {1, 2, 3, 4, 6, 8, 12, 24} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({2, 3, 4, 6, 8, 12, 24} : Finset ℕ) by decide), Finset.sum_insert (show (2 : ℕ) ∉ ({3, 4, 6, 8, 12, 24} : Finset ℕ) by decide), Finset.sum_insert (show (3 : ℕ) ∉ ({4, 6, 8, 12, 24} : Finset ℕ) by decide), Finset.sum_insert (show (4 : ℕ) ∉ ({6, 8, 12, 24} : Finset ℕ) by decide), Finset.sum_insert (show (6 : ℕ) ∉ ({8, 12, 24} : Finset ℕ) by decide), Finset.sum_insert (show (8 : ℕ) ∉ ({12, 24} : Finset ℕ) by decide), Finset.sum_insert (show (12 : ℕ) ∉ ({24} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cK', rhoK_1, rhoK_2, rhoK_3, rhoK_4, rhoK_5, rhoK_6, rhoK_7, rhoK_8, rhoK_9, rhoK_10, rhoK_11, rhoK_12, rhoK_13, rhoK_14, rhoK_15, rhoK_16, rhoK_17, rhoK_18, rhoK_19, rhoK_20, rhoK_21, rhoK_22, rhoK_23, rhoK_24, rhoK_25, rhoK_26, rhoK_27, aK_1, aK_2, aK_3, aK_4, aK_5, aK_6, aK_7, aK_8, aK_9, aK_10, aK_11, aK_12, aK_13, aK_14, aK_15, aK_16, aK_17, aK_18, aK_19, aK_20, aK_21, aK_22, aK_23, aK_24, aK_25, aK_26, aK_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cK_conv'_25 : aK 25 * Real.log (25 : ℕ) = ∑ d ∈ Nat.divisors 25, cK' d * aK (25 / d) := by
  rw [show Nat.divisors 25 = {1, 5, 25} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({5, 25} : Finset ℕ) by decide), Finset.sum_insert (show (5 : ℕ) ∉ ({25} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cK', rhoK_1, rhoK_2, rhoK_3, rhoK_4, rhoK_5, rhoK_6, rhoK_7, rhoK_8, rhoK_9, rhoK_10, rhoK_11, rhoK_12, rhoK_13, rhoK_14, rhoK_15, rhoK_16, rhoK_17, rhoK_18, rhoK_19, rhoK_20, rhoK_21, rhoK_22, rhoK_23, rhoK_24, rhoK_25, rhoK_26, rhoK_27, aK_1, aK_2, aK_3, aK_4, aK_5, aK_6, aK_7, aK_8, aK_9, aK_10, aK_11, aK_12, aK_13, aK_14, aK_15, aK_16, aK_17, aK_18, aK_19, aK_20, aK_21, aK_22, aK_23, aK_24, aK_25, aK_26, aK_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cK_conv'_26 : aK 26 * Real.log (26 : ℕ) = ∑ d ∈ Nat.divisors 26, cK' d * aK (26 / d) := by
  rw [show Nat.divisors 26 = {1, 2, 13, 26} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({2, 13, 26} : Finset ℕ) by decide), Finset.sum_insert (show (2 : ℕ) ∉ ({13, 26} : Finset ℕ) by decide), Finset.sum_insert (show (13 : ℕ) ∉ ({26} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cK', rhoK_1, rhoK_2, rhoK_3, rhoK_4, rhoK_5, rhoK_6, rhoK_7, rhoK_8, rhoK_9, rhoK_10, rhoK_11, rhoK_12, rhoK_13, rhoK_14, rhoK_15, rhoK_16, rhoK_17, rhoK_18, rhoK_19, rhoK_20, rhoK_21, rhoK_22, rhoK_23, rhoK_24, rhoK_25, rhoK_26, rhoK_27, aK_1, aK_2, aK_3, aK_4, aK_5, aK_6, aK_7, aK_8, aK_9, aK_10, aK_11, aK_12, aK_13, aK_14, aK_15, aK_16, aK_17, aK_18, aK_19, aK_20, aK_21, aK_22, aK_23, aK_24, aK_25, aK_26, aK_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

lemma cK_conv'_27 : aK 27 * Real.log (27 : ℕ) = ∑ d ∈ Nat.divisors 27, cK' d * aK (27 / d) := by
  rw [show Nat.divisors 27 = {1, 3, 9, 27} by decide]
  simp only [Finset.sum_insert (show (1 : ℕ) ∉ ({3, 9, 27} : Finset ℕ) by decide), Finset.sum_insert (show (3 : ℕ) ∉ ({9, 27} : Finset ℕ) by decide), Finset.sum_insert (show (9 : ℕ) ∉ ({27} : Finset ℕ) by decide), Finset.sum_singleton]
  norm_num [cK', rhoK_1, rhoK_2, rhoK_3, rhoK_4, rhoK_5, rhoK_6, rhoK_7, rhoK_8, rhoK_9, rhoK_10, rhoK_11, rhoK_12, rhoK_13, rhoK_14, rhoK_15, rhoK_16, rhoK_17, rhoK_18, rhoK_19, rhoK_20, rhoK_21, rhoK_22, rhoK_23, rhoK_24, rhoK_25, rhoK_26, rhoK_27, aK_1, aK_2, aK_3, aK_4, aK_5, aK_6, aK_7, aK_8, aK_9, aK_10, aK_11, aK_12, aK_13, aK_14, aK_15, aK_16, aK_17, aK_18, aK_19, aK_20, aK_21, aK_22, aK_23, aK_24, aK_25, aK_26, aK_27]
  try simp only [lg_4, lg_6, lg_8, lg_9, lg_10, lg_12, lg_14, lg_15, lg_16, lg_18, lg_20, lg_21, lg_22, lg_24, lg_25, lg_26, lg_27]
  try ring

/-- **The defining identity of `-zeta_K'/zeta_K`** with the weights `Lambda(n)(1 + chi_-20(n))`,
`n <= 27`: `aK(n) log n = sum_{d | n} cK(d) aK(n/d)`. -/
theorem cK_conv : ∀ n : ℕ, 1 ≤ n → n ≤ 27 → aK n * Real.log n = ∑ d ∈ n.divisors, cK d * aK (n / d) := by
  intro n h1 h2
  have hc : ∀ d ∈ n.divisors, cK d * aK (n / d) = cK' d * aK (n / d) := by
    intro d hd
    have hdn : d ≤ n := Nat.divisor_le hd
    rw [cK_eq d (by omega)]
    rfl
  rw [Finset.sum_congr rfl hc]
  interval_cases n
  · exact cK_conv'_1
  · exact cK_conv'_2
  · exact cK_conv'_3
  · exact cK_conv'_4
  · exact cK_conv'_5
  · exact cK_conv'_6
  · exact cK_conv'_7
  · exact cK_conv'_8
  · exact cK_conv'_9
  · exact cK_conv'_10
  · exact cK_conv'_11
  · exact cK_conv'_12
  · exact cK_conv'_13
  · exact cK_conv'_14
  · exact cK_conv'_15
  · exact cK_conv'_16
  · exact cK_conv'_17
  · exact cK_conv'_18
  · exact cK_conv'_19
  · exact cK_conv'_20
  · exact cK_conv'_21
  · exact cK_conv'_22
  · exact cK_conv'_23
  · exact cK_conv'_24
  · exact cK_conv'_25
  · exact cK_conv'_26
  · exact cK_conv'_27

/-! ## C. Lemma-O witnesses at `n = 6` -/

/-- `c_E(6) = 2 log 6`: the Epstein counterfeit has a periodic orbit of length `log 6`. -/
theorem cE_six : cE 6 = 2 * Real.log 6 := by norm_num [cE, rhoE]

theorem cE_six_ne_zero : cE 6 ≠ 0 := by
  rw [cE_six]
  have : 0 < Real.log 6 := Real.log_pos (by norm_num)
  positivity

/-- `Lambda(6) = 0` and `c_K(6) = 0`: zeta and zeta_K have no orbit of length `log 6`. -/
theorem vonMangoldt_six : ArithmeticFunction.vonMangoldt 6 = 0 := by
  rw [Crux3.lam_tab 6 (by norm_num)]
  norm_num [Crux3.tab]

theorem cK_six : cK 6 = 0 := by rw [cK, vonMangoldt_six, zero_mul]

/-- For ANY weights with E's defining identity on `[1, 27]`, `w 6 = 2 log 6 != 0 = Lambda(6)`. -/
theorem epstein_orbit_six (w : ℕ → ℝ)
    (hw : ∀ n : ℕ, 1 ≤ n → n ≤ 27 → aE n * Real.log n = ∑ d ∈ n.divisors, w d * aE (n / d)) :
    w 6 = 2 * Real.log 6 ∧ w 6 ≠ 0 ∧ ArithmeticFunction.vonMangoldt 6 = 0 := by
  have h := eq_cE_of_conv w hw 6 (by norm_num) (by norm_num)
  refine ⟨by rw [h, cE_six], by rw [h]; exact cE_six_ne_zero, vonMangoldt_six⟩

end CF
