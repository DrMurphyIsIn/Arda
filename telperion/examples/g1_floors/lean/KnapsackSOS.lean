/- HAND-AUTHORED (not telperion-generated): Grigoriev knapsack SOS lower bound,
   symbolic-n scalar layer -- P-vs-NP certificate ladder, rung 2.

   Validated in exact Fraction arithmetic by
   telperion/examples/knapsack_sos/knapsack_pseudoexpectation.py (all-green:
   brute-force formula match + negative control, 130x130 spectral
   reconstruction, integer-r sanity, r=3/2 teeth at exactly d=3, kernel
   identities, rank-1 factorization, closed-form scalars on the full grid).

   WHAT IS PROVEN HERE (kernel-checked, symbolic in n):
     * `constraint_identity` / `pseudoexpectation_ideal`: the pseudo-moment
       f(k) = prod_{j<k} (n/2-j)/(n-j) satisfies the knapsack ideal identity
       exactly (telescoping) -- E[(sum x - n/2) x_S] = 0 in scalar form;
     * `kernel_identity`: the constraint collapses each harmonic block to
       rank <= 1 -- the exact bidiagonal kernel recurrence for v;
     * `g1_closed` .. `g4_closed`: the alternating-sum block scalars equal
       the product form  g_k = prod_{j<k} (n-2j)/(2(n-2j-1));
     * `g0_pos` .. `g4_pos`: each scalar is positive for n > 2k-1 (in
       particular every odd n >= 2k+1);
     * `rank_one_quadform_nonneg` + `block0_psd` .. `block4_psd`: the rank-1
       blocks g_k v v^T have nonnegative quadratic form -- PSD;
     * `bridge_offdiag` / `bridge_corner`: two entries of the k=1 Gram block
       computed from the COMBINATORIAL formula equal the rank-1 prediction
       (demonstrating the Gram bridge is Lean-closable entry by entry);
     * `knapsack_unsat`: for odd N the boolean system really is unsatisfiable
       (nonvacuity: the refuted system has no solution, yet degree-8 SOS
       cannot see it for any odd n >= 9).

   WHAT IS PYTHON-PINNED (not yet kernel-checked): the general (k,i,j)
   combinatorial Gram-formula bridge G_k = g_k v v^T (exact on the grid, two
   entries proven here), and the standard duality "moment matrix PSD implies
   no SOS refutation of degree <= 2d" (literature; not formalized).

   CEILING (honesty): this certifies a lower bound AGAINST the SOS proof
   system only. SOS-hardness is not hardness. P_vs_NP_separated = False. -/
import Mathlib

namespace KnapsackSOS

/-! ### The pseudo-moment sequence -/

/-- Pseudo-moment of a k-subset monomial under the fractional hypergeometric
pseudoexpectation at r = n/2:  f(k) = prod_{j<k} (n/2 - j)/(n - j). -/
def f (n : ℚ) : ℕ → ℚ
  | 0 => 1
  | k + 1 => f n k * (n / 2 - k) / (n - k)

/-- Telescoping constraint identity: (n-k) f(k+1) = (n/2-k) f(k). -/
theorem constraint_identity (n : ℚ) (k : ℕ) (hk : (k : ℚ) ≠ n) :
    (n - k) * f n (k + 1) = (n / 2 - k) * f n k := by
  have h : n - (k : ℚ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hk)
  show (n - k) * (f n k * (n / 2 - k) / (n - k)) = (n / 2 - k) * f n k
  field_simp

/-- Scalar form of E[(sum_i x_i - n/2) x_S] = 0 for |S| = k:
the pseudoexpectation satisfies the knapsack constraint exactly. -/
theorem pseudoexpectation_ideal (n : ℚ) (k : ℕ) (hk : (k : ℚ) ≠ n) :
    (k : ℚ) * f n k + (n - k) * f n (k + 1) - (n / 2) * f n k = 0 := by
  rw [constraint_identity n k hk]; ring

/-! ### Block scalars: alternating sums and closed product forms -/

/-- g_k = 2^k sum_{s<=k} (-1)^(k-s) C(k,s) f(2k-s), written literally. -/
def g0 (_ : ℚ) : ℚ := 1
def g1 (n : ℚ) : ℚ := 2 * (f n 1 - f n 2)
def g2 (n : ℚ) : ℚ := 4 * (f n 2 - 2 * f n 3 + f n 4)
def g3 (n : ℚ) : ℚ := 8 * (f n 3 - 3 * f n 4 + 3 * f n 5 - f n 6)
def g4 (n : ℚ) : ℚ := 16 * (f n 4 - 4 * f n 5 + 6 * f n 6 - 4 * f n 7 + f n 8)

theorem g1_closed (n : ℚ) (hn : (1 : ℚ) < n) :
    g1 n = n / (2 * (n - 1)) := by
  have h0 : n ≠ 0 := ne_of_gt (by linarith)
  have h1 : n - 1 ≠ 0 := ne_of_gt (by linarith)
  simp only [g1, f]
  push_cast
  field_simp
  ring

theorem g2_closed (n : ℚ) (hn : (3 : ℚ) < n) :
    g2 n = n * (n - 2) / (4 * (n - 1) * (n - 3)) := by
  have h0 : n ≠ 0 := ne_of_gt (by linarith)
  have h1 : n - 1 ≠ 0 := ne_of_gt (by linarith)
  have h2 : n - 2 ≠ 0 := ne_of_gt (by linarith)
  have h3 : n - 3 ≠ 0 := ne_of_gt (by linarith)
  simp only [g2, f]
  push_cast
  field_simp
  ring

theorem g3_closed (n : ℚ) (hn : (5 : ℚ) < n) :
    g3 n = n * (n - 2) * (n - 4) / (8 * (n - 1) * (n - 3) * (n - 5)) := by
  have h0 : n ≠ 0 := ne_of_gt (by linarith)
  have h1 : n - 1 ≠ 0 := ne_of_gt (by linarith)
  have h2 : n - 2 ≠ 0 := ne_of_gt (by linarith)
  have h3 : n - 3 ≠ 0 := ne_of_gt (by linarith)
  have h4 : n - 4 ≠ 0 := ne_of_gt (by linarith)
  have h5 : n - 5 ≠ 0 := ne_of_gt (by linarith)
  simp only [g3, f]
  push_cast
  field_simp
  ring

theorem g4_closed (n : ℚ) (hn : (7 : ℚ) < n) :
    g4 n = n * (n - 2) * (n - 4) * (n - 6) /
      (16 * (n - 1) * (n - 3) * (n - 5) * (n - 7)) := by
  have h0 : n ≠ 0 := ne_of_gt (by linarith)
  have h1 : n - 1 ≠ 0 := ne_of_gt (by linarith)
  have h2 : n - 2 ≠ 0 := ne_of_gt (by linarith)
  have h3 : n - 3 ≠ 0 := ne_of_gt (by linarith)
  have h4 : n - 4 ≠ 0 := ne_of_gt (by linarith)
  have h5 : n - 5 ≠ 0 := ne_of_gt (by linarith)
  have h6 : n - 6 ≠ 0 := ne_of_gt (by linarith)
  have h7 : n - 7 ≠ 0 := ne_of_gt (by linarith)
  simp only [g4, f]
  push_cast
  field_simp
  ring

/-! ### Positivity of the block scalars -/

theorem g0_pos (n : ℚ) : 0 < g0 n := by norm_num [g0]

theorem g1_pos (n : ℚ) (hn : (1 : ℚ) < n) : 0 < g1 n := by
  rw [g1_closed n hn]
  have p0 : (0 : ℚ) < n := by linarith
  have p1 : (0 : ℚ) < n - 1 := by linarith
  positivity

theorem g2_pos (n : ℚ) (hn : (3 : ℚ) < n) : 0 < g2 n := by
  rw [g2_closed n hn]
  have p0 : (0 : ℚ) < n := by linarith
  have p1 : (0 : ℚ) < n - 1 := by linarith
  have p2 : (0 : ℚ) < n - 2 := by linarith
  have p3 : (0 : ℚ) < n - 3 := by linarith
  exact div_pos (mul_pos p0 p2) (mul_pos (mul_pos (by norm_num) p1) p3)

theorem g3_pos (n : ℚ) (hn : (5 : ℚ) < n) : 0 < g3 n := by
  rw [g3_closed n hn]
  have p0 : (0 : ℚ) < n := by linarith
  have p1 : (0 : ℚ) < n - 1 := by linarith
  have p2 : (0 : ℚ) < n - 2 := by linarith
  have p3 : (0 : ℚ) < n - 3 := by linarith
  have p4 : (0 : ℚ) < n - 4 := by linarith
  have p5 : (0 : ℚ) < n - 5 := by linarith
  exact div_pos (mul_pos (mul_pos p0 p2) p4)
    (mul_pos (mul_pos (mul_pos (by norm_num) p1) p3) p5)

theorem g4_pos (n : ℚ) (hn : (7 : ℚ) < n) : 0 < g4 n := by
  rw [g4_closed n hn]
  have p0 : (0 : ℚ) < n := by linarith
  have p1 : (0 : ℚ) < n - 1 := by linarith
  have p2 : (0 : ℚ) < n - 2 := by linarith
  have p3 : (0 : ℚ) < n - 3 := by linarith
  have p4 : (0 : ℚ) < n - 4 := by linarith
  have p5 : (0 : ℚ) < n - 5 := by linarith
  have p6 : (0 : ℚ) < n - 6 := by linarith
  have p7 : (0 : ℚ) < n - 7 := by linarith
  exact div_pos (mul_pos (mul_pos (mul_pos p0 p2) p4) p6)
    (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) p1) p3) p5) p7)

/-! ### The rank-1 direction and the kernel identity -/

/-- Surviving direction of the level-k block: v(0) = 1,
v(i+1) = v(i) * (n/2 - (k+i)) / (i+1). -/
def v (n : ℚ) (k : ℕ) : ℕ → ℚ
  | 0 => 1
  | i + 1 => v n k i * (n / 2 - (k + i)) / (i + 1)

/-- The exact bidiagonal kernel recurrence: symmetrized constraint vectors
kill every direction transverse to v, collapsing each block to rank <= 1. -/
theorem kernel_identity (n : ℚ) (k i : ℕ) :
    ((k : ℚ) + i - n / 2) * v n k i + ((i : ℚ) + 1) * v n k (i + 1) = 0 := by
  have h : (i : ℚ) + 1 ≠ 0 := ne_of_gt (by positivity)
  rw [v]
  field_simp
  ring

/-! ### Rank-1 PSD: nonnegative quadratic form -/

/-- A rank-1 matrix g w w^T with g >= 0 has nonnegative quadratic form. -/
theorem rank_one_quadform_nonneg {m : ℕ} (g : ℚ) (hg : 0 ≤ g) (w x : Fin m → ℚ) :
    0 ≤ ∑ i, ∑ j, x i * (g * w i * w j) * x j := by
  have key : ∑ i, ∑ j, x i * (g * w i * w j) * x j
      = g * (∑ i, w i * x i) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [key]
  exact mul_nonneg hg (sq_nonneg _)

/-- PSD of the five explicit rank-1 harmonic blocks, all n > 7 (in
particular every odd n >= 9), any block dimension m. -/
theorem block0_psd (n : ℚ) {m : ℕ} (x : Fin m → ℚ) :
    0 ≤ ∑ i : Fin m, ∑ j : Fin m, x i * (g0 n * v n 0 (i : ℕ) * v n 0 (j : ℕ)) * x j :=
  rank_one_quadform_nonneg _ (le_of_lt (g0_pos n)) _ x

theorem block1_psd (n : ℚ) (hn : (7 : ℚ) < n) {m : ℕ} (x : Fin m → ℚ) :
    0 ≤ ∑ i : Fin m, ∑ j : Fin m, x i * (g1 n * v n 1 (i : ℕ) * v n 1 (j : ℕ)) * x j :=
  rank_one_quadform_nonneg _ (le_of_lt (g1_pos n (by linarith))) _ x

theorem block2_psd (n : ℚ) (hn : (7 : ℚ) < n) {m : ℕ} (x : Fin m → ℚ) :
    0 ≤ ∑ i : Fin m, ∑ j : Fin m, x i * (g2 n * v n 2 (i : ℕ) * v n 2 (j : ℕ)) * x j :=
  rank_one_quadform_nonneg _ (le_of_lt (g2_pos n (by linarith))) _ x

theorem block3_psd (n : ℚ) (hn : (7 : ℚ) < n) {m : ℕ} (x : Fin m → ℚ) :
    0 ≤ ∑ i : Fin m, ∑ j : Fin m, x i * (g3 n * v n 3 (i : ℕ) * v n 3 (j : ℕ)) * x j :=
  rank_one_quadform_nonneg _ (le_of_lt (g3_pos n (by linarith))) _ x

theorem block4_psd (n : ℚ) (hn : (7 : ℚ) < n) {m : ℕ} (x : Fin m → ℚ) :
    0 ≤ ∑ i : Fin m, ∑ j : Fin m, x i * (g4 n * v n 4 (i : ℕ) * v n 4 (j : ℕ)) * x j :=
  rank_one_quadform_nonneg _ (le_of_lt (g4_pos n hn)) _ x

/-! ### Gram bridge demonstration (k = 1 block, entries (1,2) and (2,2)) -/

/-- Off-diagonal entry of the k=1 Gram block from the COMBINATORIAL formula
(2m(f2 - f3), m = n-2) equals the rank-1 prediction g1 * v(1). -/
theorem bridge_offdiag (n : ℚ) (hn : (3 : ℚ) < n) :
    2 * (n - 2) * (f n 2 - f n 3) = g1 n * (n / 2 - 1) := by
  have h0 : n ≠ 0 := ne_of_gt (by linarith)
  have h1 : n - 1 ≠ 0 := ne_of_gt (by linarith)
  have h2 : n - 2 ≠ 0 := ne_of_gt (by linarith)
  simp only [g1, f]
  push_cast
  field_simp
  ring

/-- Corner entry of the k=1 Gram block from the COMBINATORIAL formula
(2m((m-1)(f3-f4) + (f2-f3))) equals the rank-1 prediction g1 * v(1)^2. -/
theorem bridge_corner (n : ℚ) (hn : (3 : ℚ) < n) :
    2 * (n - 2) * ((n - 3) * (f n 3 - f n 4) + (f n 2 - f n 3))
      = g1 n * (n / 2 - 1) ^ 2 := by
  have h0 : n ≠ 0 := ne_of_gt (by linarith)
  have h1 : n - 1 ≠ 0 := ne_of_gt (by linarith)
  have h2 : n - 2 ≠ 0 := ne_of_gt (by linarith)
  have h3 : n - 3 ≠ 0 := ne_of_gt (by linarith)
  simp only [g1, f]
  push_cast
  field_simp
  ring

/-! ### Nonvacuity: the refuted system is genuinely unsatisfiable -/

/-- For odd N the knapsack system {x_i in {0,1}, sum x_i = N/2} has NO
solution -- the statement SOS cannot certify below degree n+1. -/
theorem knapsack_unsat (N : ℕ) (hN : Odd N) (x : Fin N → ℚ)
    (hx : ∀ i, x i = 0 ∨ x i = 1) : ∑ i, x i ≠ (N : ℚ) / 2 := by
  intro hsum
  classical
  set c : ℕ := (Finset.univ.filter fun i => x i = 1).card with hc
  have hxs : ∑ i, x i = (c : ℚ) := by
    rw [hc, Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases hx i with h | h <;> simp [h]
  rcases hN with ⟨p, hp⟩
  have h2 : (2 * c : ℚ) = (N : ℚ) := by
    rw [hxs] at hsum
    field_simp at hsum
    linarith
  have h3 : 2 * c = N := by exact_mod_cast h2
  omega

/-! ### Master statement -/

/-- Degree-8 knapsack SOS lower-bound certificate, scalar layer: for every
rational n > 7 (hence every odd integer n >= 9) all five harmonic block
scalars of the degree-8 pseudoexpectation moment matrix are positive. With
`kernel_identity` (rank-1 collapse) and `blockK_psd` (nonneg quadratic
forms) this is the complete PSD certificate for the moment matrix in
rank-1 factored form; with `knapsack_unsat` the refuted system is genuinely
infeasible. Grigoriev's degree lower bound, symbolic in n. -/
theorem knapsack_certificate (n : ℚ) (hn : (7 : ℚ) < n) :
    0 < g0 n ∧ 0 < g1 n ∧ 0 < g2 n ∧ 0 < g3 n ∧ 0 < g4 n :=
  ⟨g0_pos n, g1_pos n (by linarith), g2_pos n (by linarith),
    g3_pos n (by linarith), g4_pos n hn⟩

end KnapsackSOS

#print axioms KnapsackSOS.constraint_identity
#print axioms KnapsackSOS.pseudoexpectation_ideal
#print axioms KnapsackSOS.kernel_identity
#print axioms KnapsackSOS.g4_closed
#print axioms KnapsackSOS.rank_one_quadform_nonneg
#print axioms KnapsackSOS.bridge_corner
#print axioms KnapsackSOS.knapsack_unsat
#print axioms KnapsackSOS.knapsack_certificate
