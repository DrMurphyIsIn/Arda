/-
RvMArchGrowth — Arc B (archimedean Li growth), PR B3: harmonic bridge + the growth assembly.

B2 (`RvMArchGrowthBounds`) gave the honest REAL form
  `(taylorCoeff Γℝ n).re = −((γ+log π)/2)·(n+1) − 1 + ∑'_j archRe n j`,
with per-term Bernoulli/Bonferroni/crude bounds, summability, and the `O(1/n)` `1/j²` tail.  This
file splits the tsum at `K = n`, identifies the finite head `∑_{j<n} (n+1)/(2(j+1))` as the harmonic
number `(n+1)/2·H_n`, bounds `H_n` two-sidedly by `Real.log` (Mathlib `log_add_one_le_harmonic` /
`harmonic_le_one_add_log`), and assembles the unconditional growth:

  `taylorCoeff_Gammaℝ_re_growth : ∀ n ≥ 2, |(taylorCoeff Γℝ n).re − (n/2)·log n| ≤ 8·n`.

The constant `8` is explicit and verified against the 40-digit numerics
(arch(8)=−0.5397, arch(16)=4.6142, arch(32)=20.1402, arch(63)=60.4924).

conjecture1_proved = False: Γ-function calculus; nothing here approaches RH.
-/
import Mathlib
import RvMArchGrowthBounds

open Complex Finset

namespace RvMWeierstrass

/-- The real harmonic number `H_n = ∑_{j<n} 1/(j+1)`, as a real-valued `Finset` sum. -/
noncomputable def Hsum (n : ℕ) : ℝ := ∑ j ∈ Finset.range n, 1 / ((j : ℝ) + 1)

/-- `Hsum n` is the real cast of Mathlib's `harmonic n`. -/
theorem Hsum_eq_harmonic (n : ℕ) : Hsum n = ((harmonic n : ℚ) : ℝ) := by
  unfold Hsum
  rw [show ((harmonic n : ℚ) : ℝ) = ∑ j ∈ Finset.range n, ((j : ℝ) + 1)⁻¹ from by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]; push_cast; rfl]
  apply Finset.sum_congr rfl
  intro j _
  rw [one_div]

/-- Lower bound `log(n+1) ≤ H_n` (Mathlib). -/
theorem log_add_one_le_Hsum (n : ℕ) : Real.log ((n : ℝ) + 1) ≤ Hsum n := by
  rw [Hsum_eq_harmonic]
  have := log_add_one_le_harmonic n
  push_cast at this
  convert this using 2

/-- Upper bound `H_n ≤ 1 + log n` (Mathlib). -/
theorem Hsum_le_one_add_log (n : ℕ) : Hsum n ≤ 1 + Real.log (n : ℝ) := by
  rw [Hsum_eq_harmonic]
  exact harmonic_le_one_add_log n

/-! ### The split at `K = n` -/

/-- The finite head `∑_{j<n} (n+1)/(2(j+1))` equals `(n+1)/2·H_n`. -/
theorem sum_head_eq (n : ℕ) :
    ∑ j ∈ Finset.range n, ((n : ℝ) + 1) / (2 * ((j : ℝ) + 1)) = ((n : ℝ) + 1) / 2 * Hsum n := by
  unfold Hsum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  field_simp

/-- **Lower bound on the series.**  Dropping the positive tail (`j ≥ n`) and `r^(n+1) ≥ 0` on the
    finite head gives `∑'_j archRe n j ≥ (n+1)/2·H_n − n`. -/
theorem tsum_archRe_lower (n : ℕ) :
    ((n : ℝ) + 1) / 2 * Hsum n - (n : ℝ) ≤ ∑' j : ℕ, archRe n j := by
  -- the finite head of the tsum is a lower bound (positive tail)
  have hsplit : ∑ j ∈ Finset.range n, archRe n j ≤ ∑' j : ℕ, archRe n j :=
    sum_le_hasSum _ (fun j _ => archRe_nonneg n j) (summable_archRe n).hasSum
  refine le_trans ?_ hsplit
  -- `∑_{j<n} archRe n j ≥ ∑_{j<n}[(n+1)/(2(j+1)) - 1] = (n+1)/2·H_n - n`
  have hterm : ∀ j ∈ Finset.range n,
      ((n : ℝ) + 1) / (2 * ((j : ℝ) + 1)) - 1 ≤ archRe n j := by
    intro j _
    unfold archRe
    have : (0 : ℝ) ≤ ((2 * (j : ℝ) + 2) / (2 * (j : ℝ) + 3)) ^ (n + 1) := by positivity
    linarith
  have hge : ∑ j ∈ Finset.range n, (((n : ℝ) + 1) / (2 * ((j : ℝ) + 1)) - 1)
      ≤ ∑ j ∈ Finset.range n, archRe n j :=
    Finset.sum_le_sum hterm
  refine le_trans (le_of_eq ?_) hge
  rw [Finset.sum_sub_distrib, sum_head_eq, Finset.sum_const, Finset.card_range]
  simp

/-- **Tail tsum bound** (`n ≥ 1`).  `∑'_k archRe n (n+k) ≤ (n+1)/(4n) + (n(n+1)/2)·(1/(4n))`,
    from the Bonferroni per-term bound and the `1/j²` tail. -/
theorem tsum_tail_archRe_le (n : ℕ) (hn : 1 ≤ n) :
    ∑' k : ℕ, archRe n (n + k)
      ≤ ((n : ℝ) + 1) / 4 * (1 / (n : ℝ))
        + ((n : ℝ) * ((n : ℝ) + 1) / 2) * (1 / 4 * (1 / (n : ℝ))) := by
  -- the tail is summable (shift of a summable sequence)
  have hsummable_tail : Summable (fun k : ℕ => archRe n (n + k)) := by
    have := (summable_nat_add_iff n).mpr (summable_archRe n)
    simpa [Nat.add_comm] using this
  -- per-term: archRe n (n+k) ≤ (n+1)/4·(1/(n+k+1)²) + (n(n+1)/2)·(1/4·(1/(n+k+1)²))
  have hterm : ∀ k : ℕ, archRe n (n + k)
      ≤ ((n : ℝ) + 1) / 4 * (1 / ((n : ℝ) + (k : ℝ) + 1) ^ 2)
        + ((n : ℝ) * ((n : ℝ) + 1) / 2) * (1 / 4 * (1 / ((n : ℝ) + (k : ℝ) + 1) ^ 2)) := by
    intro k
    refine (archRe_upper_bonferroni n (n + k)).trans ?_
    have hnk1 : (0 : ℝ) < (n : ℝ) + (k : ℝ) + 1 := by positivity
    have hA : ((n : ℝ) + 1) / ((2 * ((n : ℝ) + (k : ℝ)) + 2) * (2 * ((n : ℝ) + (k : ℝ)) + 3))
        ≤ ((n : ℝ) + 1) / 4 * (1 / ((n : ℝ) + (k : ℝ) + 1) ^ 2) := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have hn1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
      nlinarith [Nat.cast_nonneg n (α := ℝ), Nat.cast_nonneg k (α := ℝ), hn1]
    have hB : (1 / (2 * ((n : ℝ) + (k : ℝ)) + 3)) ^ 2 ≤ 1 / 4 * (1 / ((n : ℝ) + (k : ℝ) + 1) ^ 2) := by
      rw [div_pow, one_pow, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
      nlinarith [Nat.cast_nonneg n (α := ℝ), Nat.cast_nonneg k (α := ℝ)]
    have hnnq : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1) / 2 := by positivity
    have hBscaled := mul_le_mul_of_nonneg_left hB hnnq
    push_cast at hA hB hBscaled ⊢
    linarith [hA, hBscaled]
  calc ∑' k : ℕ, archRe n (n + k)
      ≤ ∑' k : ℕ, (((n : ℝ) + 1) / 4 * (1 / ((n : ℝ) + (k : ℝ) + 1) ^ 2)
          + ((n : ℝ) * ((n : ℝ) + 1) / 2) * (1 / 4 * (1 / ((n : ℝ) + (k : ℝ) + 1) ^ 2))) := by
        refine Summable.tsum_le_tsum hterm hsummable_tail ?_
        -- RHS summability
        apply Summable.add
        · exact (tsum_tail_summable n).mul_left _
        · exact ((tsum_tail_summable n).mul_left _).mul_left _
    _ = ((n : ℝ) + 1) / 4 * (∑' k : ℕ, 1 / ((n : ℝ) + (k : ℝ) + 1) ^ 2)
          + ((n : ℝ) * ((n : ℝ) + 1) / 2) * (1 / 4 * (∑' k : ℕ, 1 / ((n : ℝ) + (k : ℝ) + 1) ^ 2)) := by
        rw [Summable.tsum_add ((tsum_tail_summable n).mul_left _)
          (((tsum_tail_summable n).mul_left _).mul_left _), tsum_mul_left, tsum_mul_left,
          tsum_mul_left]
    _ ≤ ((n : ℝ) + 1) / 4 * (1 / (n : ℝ))
          + ((n : ℝ) * ((n : ℝ) + 1) / 2) * (1 / 4 * (1 / (n : ℝ))) := by
        have htail := tsum_tail_inv_sq_le n hn
        gcongr

/-- **Upper bound on the series** (`n ≥ 1`).  Split at `K = n`: crude on the finite head, Bonferroni
    on the tail.  `∑'_j archRe n j ≤ (n+1)/2·H_n + (n+1)/(4n) + (n+1)/8`. -/
theorem tsum_archRe_upper (n : ℕ) (hn : 1 ≤ n) :
    ∑' j : ℕ, archRe n j
      ≤ ((n : ℝ) + 1) / 2 * Hsum n + ((n : ℝ) + 1) / (4 * (n : ℝ)) + ((n : ℝ) + 1) / 8 := by
  -- split the tsum at K = n
  have hsplit : ∑ j ∈ Finset.range n, archRe n j + ∑' k : ℕ, archRe n (n + k)
      = ∑' j : ℕ, archRe n j := by
    have h := (summable_archRe n).sum_add_tsum_nat_add n
    rw [← h]
    congr 1
    exact tsum_congr (fun k => by rw [Nat.add_comm])
  rw [← hsplit]
  -- head ≤ (n+1)/2·H_n
  have hhead : ∑ j ∈ Finset.range n, archRe n j ≤ ((n : ℝ) + 1) / 2 * Hsum n := by
    refine le_trans (Finset.sum_le_sum (fun j _ => archRe_upper_crude n j)) ?_
    rw [sum_head_eq]
  -- tail ≤ (n+1)/(4n) + (n(n+1)/2)·(1/(4n))
  have htail := tsum_tail_archRe_le n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  -- the two tail constants sum to (n+1)/(4n) + (n+1)/8
  have htail' : ((n : ℝ) + 1) / 4 * (1 / (n : ℝ))
        + ((n : ℝ) * ((n : ℝ) + 1) / 2) * (1 / 4 * (1 / (n : ℝ)))
      = ((n : ℝ) + 1) / (4 * (n : ℝ)) + ((n : ℝ) + 1) / 8 := by
    field_simp
    ring
  rw [htail'] at htail
  linarith [hhead, htail]

/-! ### The growth headline -/

/-- `0 < γ + log π < 3`: `γ ∈ (1/2, 2/3)` (Mathlib) and `log π ≤ log 4 ≤ 2`
    (`Real.pi_le_four`, `Real.log_le_log`). -/
theorem euler_log_pi_bounds :
    0 < Real.eulerMascheroniConstant + Real.log Real.pi
      ∧ Real.eulerMascheroniConstant + Real.log Real.pi < 3 := by
  have hγ0 : (1 : ℝ) / 2 < Real.eulerMascheroniConstant := Real.one_half_lt_eulerMascheroniConstant
  have hγ1 : Real.eulerMascheroniConstant < 2 / 3 := Real.eulerMascheroniConstant_lt_two_thirds
  have hπpos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hlogπ0 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hlogπ : Real.log Real.pi ≤ Real.log 4 := Real.log_le_log hπpos Real.pi_le_four
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  refine ⟨by linarith, by nlinarith [hlogπ, hlog4, hlog2]⟩

/-- **THE ARCHIMEDEAN GROWTH BOUND (unconditional).**  For every `n ≥ 2`,
    `|(taylorCoeff Γℝ n).re − (n/2)·log n| ≤ 8·n`.

    The `(n/2)·log n` main term is a harmonic-number statement: the finite head `∑_{j<n}
    (n+1)/(2(j+1))` of the elementary series equals `(n+1)/2·H_n`, and `H_n = log n + O(1)`.  The
    constant `8` is explicit and verified against the 40-digit numerics
    (arch(8)=−0.5397, arch(16)=4.6142, arch(32)=20.1402, arch(63)=60.4924).

    conjecture1_proved = False. -/
theorem taylorCoeff_Gammaℝ_re_growth :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      |(LiCriterion.taylorCoeff Complex.Gammaℝ n).re - ((n : ℝ) / 2) * Real.log n| ≤ C * (n : ℝ) := by
  refine ⟨8, by norm_num, fun n hn2 => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two hn2
  set A : ℝ := (Real.eulerMascheroniConstant + Real.log Real.pi) / 2 with hA
  obtain ⟨hApos, hAlt⟩ := euler_log_pi_bounds
  have hA0 : 0 < A := by rw [hA]; linarith
  have hA1 : A < 3 / 2 := by rw [hA]; linarith
  -- log n ≤ n − 1 < n  (and log n ≥ 0 for n ≥ 1)
  have hlogn_le : Real.log (n : ℝ) ≤ (n : ℝ) := by
    have := Real.log_le_sub_one_of_pos hn0; linarith
  have hlogn0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  -- the real form
  have hre := taylorCoeff_Gammaℝ_re_eq n
  rw [show -((Real.eulerMascheroniConstant + Real.log Real.pi) / 2) = -A from by rw [hA]] at hre
  -- H_n two-sided
  have hHlo : Real.log ((n : ℝ) + 1) ≤ Hsum n := log_add_one_le_Hsum n
  have hHhi : Hsum n ≤ 1 + Real.log (n : ℝ) := Hsum_le_one_add_log n
  have hHpos : 0 ≤ Hsum n := le_trans (Real.log_nonneg (by linarith)) hHlo
  -- log n ≤ log (n+1)
  have hlog_mono : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_le_log hn0 (by linarith)
  -- LOWER bound on arch:  arch ≥ -A(n+1) - 1 + (n+1)/2·H_n - n
  have hlow : -A * ((n : ℝ) + 1) - 1 + (((n : ℝ) + 1) / 2 * Hsum n - (n : ℝ))
      ≤ (LiCriterion.taylorCoeff Complex.Gammaℝ n).re := by
    rw [hre]; linarith [tsum_archRe_lower n]
  -- UPPER bound on arch:  arch ≤ -A(n+1) - 1 + (n+1)/2·H_n + (n+1)/(4n) + (n+1)/8
  have hup : (LiCriterion.taylorCoeff Complex.Gammaℝ n).re
      ≤ -A * ((n : ℝ) + 1) - 1
        + (((n : ℝ) + 1) / 2 * Hsum n + ((n : ℝ) + 1) / (4 * (n : ℝ)) + ((n : ℝ) + 1) / 8) := by
    rw [hre]; linarith [tsum_archRe_upper n hn1]
  -- convert `(n+1)/2·H_n` to `(n/2)·log n` + linear errors, both directions
  set ref : ℝ := ((n : ℝ) / 2) * Real.log (n : ℝ) with href
  rw [abs_le]
  constructor
  · -- lower: arch − ref ≥ −8n
    -- (n+1)/2·H_n ≥ (n+1)/2·log n ≥ (n/2)·log n = ref  (H_n ≥ log(n+1) ≥ log n, n+1 ≥ n)
    have hkeylo : ref ≤ ((n : ℝ) + 1) / 2 * Hsum n := by
      rw [href]
      have h1 : ((n : ℝ) / 2) * Real.log (n : ℝ) ≤ ((n : ℝ) + 1) / 2 * Real.log (n : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hlogn0; linarith
      have h2 : ((n : ℝ) + 1) / 2 * Real.log (n : ℝ) ≤ ((n : ℝ) + 1) / 2 * Hsum n := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith [hlog_mono, hHlo]
      linarith
    -- `-A(n+1) - 1 - n ≥ -8n`  using A < 3/2, n ≥ 2
    have hn2r : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    have hAprod : A * ((n : ℝ) + 1) ≤ (3 / 2) * ((n : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right hA1.le (by linarith)
    nlinarith [hlow, hkeylo, hAprod, hn2r]
  · -- upper: arch − ref ≤ 8n
    -- (n+1)/2·H_n ≤ (n+1)/2·(1+log n) = (n+1)/2 + (n+1)/2·log n; and (n+1)/2·log n − ref = (1/2)log n
    have hkeyhi : ((n : ℝ) + 1) / 2 * Hsum n
        ≤ ((n : ℝ) + 1) / 2 + (1 / 2) * Real.log (n : ℝ) + ref := by
      rw [href]
      have h1 : ((n : ℝ) + 1) / 2 * Hsum n ≤ ((n : ℝ) + 1) / 2 * (1 + Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hHhi (by positivity)
      -- `(n+1)/2·(1+logn) = (n+1)/2 + (1/2)logn + (n/2)logn` exactly
      have hexp : ((n : ℝ) + 1) / 2 * (1 + Real.log (n : ℝ))
          = ((n : ℝ) + 1) / 2 + (1 / 2) * Real.log (n : ℝ) + (n : ℝ) / 2 * Real.log (n : ℝ) := by
        ring
      linarith [h1, hexp.le, hexp.ge]
    -- `-A(n+1) - 1 + (n+1)/2 + (1/2)log n + (n+1)/(4n) + (n+1)/8 ≤ 8n`
    have hn2r : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    have hsmall : ((n : ℝ) + 1) / (4 * (n : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [hn2r, hn0]
    -- arch − ref ≤ -A(n+1) - 1 + (n+1)/2 + (1/2)logn + (n+1)/(4n) + (n+1)/8 ≤ 8n
    have hAprod : 0 ≤ A * ((n : ℝ) + 1) := mul_nonneg hA0.le (by linarith)
    linarith [hup, hkeyhi, hAprod, hn2r, hlogn_le, hsmall, hlogn0]

end RvMWeierstrass
