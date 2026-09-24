/-
  Crux2_kappa_certify.lean -- buildable core of "kappa_zeta(x) = 0 certified up to x = 11.006 via a
  window-aware reduction" (lens: kappa-certify, crux round 2).

  conjecture1_proved = False.  RH is open and nothing here moves it.  kappa_zeta(x) is the number of negative
  squares of the Weil form Q on test functions supported in [-a, a], a = (1/2) log x; by Weil's criterion RH holds
  iff kappa_zeta(x) = 0 for EVERY x.  This file concerns finitely many windows x <= 11.006, which exclude no zero
  of zeta.  The same certificate pipeline certifies kappa = 0 for the Davenport-Heilbronn function D (off-line
  zero at 0.8085 + 85.699i) at x = 6.996 and 11.006 with margins 1e23 and 1e40 times larger than zeta's
  (negative control, see telperion/research/crux2_kappa-certify/README.md): window certificates at these scales
  are blind to the Euler product.  Nothing below uses or implies RH.

  Checked by: cd telperion/examples/li_positivity/lean && lake env lean Crux/Crux2_kappa_certify.lean
  (Lean v4.34.0-rc1, the island's Mathlib).  No `sorry`, `admit`, `native_decide`, `opaque` or new `axiom`.  The
  #print axioms block at the end reports only propext, Classical.choice, Quot.sound for every theorem.

  WHAT THIS FILE ESTABLISHES (THEOREM-kernel-checked):
  A. `LemmaA.shift_bound`, `LemmaA.shift_bound_signed`, `LemmaA.comb_bound`, `LemmaA.prime_comb_bound` -- the
     idea's Lemma A in CONTINUOUS form.  For every real measurable g with g^2 integrable and g = 0 outside [-A, A], shifts tau_i > 0, and real
     weights c_i:
        sum_i c_i * int g(u + tau_i) g(u) du  <=  (sum_i |c_i| cos(pi/(floor(2A/tau_i) + 2))) * int g(u)^2 du.
     With tau_n = log n, c_n = 2 Lambda(n)/sqrt n (prime_comb_bound, Mathlib's vonMangoldt), the left side is
     <P_A g, g> for the compressed prime comb and the bracket is the constant A'(A) of the window-aware reduction (A' ~ A_L/2 instead of Zhu's Kronecker sup
     A_L).  Previously only the finite path-graph core was kernel-checked and the orbit decomposition was on
     paper; the proof here avoids the decomposition: weighted AM-GM with a Perron weight that is constant on the
     translation cells floor((u + A)/tau), integrated using translation invariance of Lebesgue measure.
  B. `PathGraph.path_quad_le` (path-graph Perron bound) and `SchurTest.schur_test` (weighted Schur test): the
     finite cores of Lemma A and of the Fejer-mass heuristic (Lemma A').
  C. `schur_link`: generic Schur-complement step.  If C is positive definite and the Schur complement
     A - B C^{-1} B^T lies entrywise within w of a matrix S with S >= delta I and k w < delta, then the block
     matrix [[A, B], [B^T, C]] is positive semidefinite (C of any finite size).  `block_assembly`: the two-block
     inequality lam_min >= min(l, d) - e used to add the Legendre tail.
  D. Four certificate cores, each an EXACT rational congruence Sq - delta I = L D L^T (closed by `ring`) with
     `core_posdef` (every 8 x 8 matrix in the Arb box around Sq is positive definite) and `core_schur`
     (instantiation of C: every symmetric block matrix with C > 0 and Schur complement in the box is PSD):
       Core_x6996_even  x = e^{249/128} = 6.9958, lam0 = 4.39e-28  (Zhu-type reduction, T# = 560, N = 450)
       Core_x6996_odd   x = 6.9958,               lam0 = 1.25e-24  (T# = 800, N = 620)
       Core_x11006_even x = e^{307/128} = 11.006, lam0 = 6.6018e-49 (window-aware reduction, N = 2300)
       Core_x11006_odd  x = 11.006,               lam0 = 4.4579e-45 (window-aware reduction, N = 2300)
     Instantiated with the block matrix M - lam0 I (M = leading Legendre block of the reduced form), core_schur
     gives lam_min(M) >= lam0.  Negative controls (a pivot numerator +1, one Schur entry changed in its last digits, delta
     tripled; applied to Core_x11006_odd) make the kernel reject the core (unsolved goals, sorryAx) --
     see the research README.

  TRUST BOUNDARY (NOT kernel-checked):
  - Arb (python-flint 0.6.0) facts entering as the hypotheses of core_schur: C - lam0 I > 0 (verified Cholesky /
    LDL^T with rigorous residual) and the Schur-complement box `hbox`; and the matrices M themselves (composite
    Gauss-Legendre with Bernstein-ellipse remainders, spherical Bessel backward recurrences, digamma), the
    quadrature error bounds, the Legendre-tail bounds eps_B, eps_D, and the scalar constants b', eta, deficit, xi.
  - Paper lemmas: (P1) Weil's explicit formula, arithmetic side, for smooth compactly supported tests (only this
    is needed to read Q >= lam ||f||^2 as kappa = 0; a version is kernel-proved on the rvm_bridge island,
    RvMBridge4.limit_explicit_formula, and the normalisation used here agrees with the zero side over 2000
    zeros to 5e-25); (P2) the Binet envelope Re psi(1/4 + it/2) - log pi >= log(t/2pi) - 1/t for
    t >= 3/4; (P3) the reductions Q >= R (Zhu) and Q >= R'' (window-aware: Lemma A + Lemma B), whose comb step
    is A above and whose remaining analytic step (Lemma B, erf localisation) is on paper.

  DOES NOT ESTABLISH: anything about the zeros of zeta, or kappa_zeta(x) for any x > 11.006 (RH); the analytic
  reduction Q >= R'' as a Lean theorem; the Fejer-mass conjecture ||P_A|| ~ sum c_n (1 - log n/(2A)).
-/

import Mathlib

open Finset Matrix MeasureTheory Real

namespace Crux2KappaCertify

/-! ## 1. Generic finite-dimensional lemmas (box lemma, Schur-complement link, assembly) -/


def qf {n : ℕ} (G : Fin n → Fin n → ℝ) (v : Fin n → ℝ) : ℝ := ∑ i, ∑ j, v i * G i j * v j

lemma qf_sub {n : ℕ} (G S : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    qf G v - qf S v = qf (fun i j => G i j - S i j) v := by
  unfold qf
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

lemma abs_qf_le {n : ℕ} (E : Fin n → Fin n → ℝ) (w : ℝ) (h : ∀ i j, |E i j| ≤ w)
    (v : Fin n → ℝ) : |qf E v| ≤ w * (∑ i, |v i|) ^ 2 := by
  unfold qf
  calc |∑ i, ∑ j, v i * E i j * v j|
      ≤ ∑ i, |∑ j, v i * E i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |v i * E i j * v j| :=
        Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, w * (|v i| * |v j|) := by
        refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
        rw [abs_mul, abs_mul]
        have h1 := h i j
        have h2 : 0 ≤ |v i| * |v j| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
        calc |v i| * |E i j| * |v j| = |E i j| * (|v i| * |v j|) := by ring
          _ ≤ w * (|v i| * |v j|) := mul_le_mul_of_nonneg_right h1 h2
    _ = w * (∑ i, |v i|) ^ 2 := by
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]

lemma sum_abs_sq_le {n : ℕ} (v : Fin n → ℝ) : (∑ i, |v i|) ^ 2 ≤ (n : ℝ) * ∑ i, v i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun i => |v i|)
  simpa [sq_abs] using h

theorem posdef_of_box {n : ℕ} (G S : Fin n → Fin n → ℝ) (w δ : ℝ)
    (hbox : ∀ i j, |G i j - S i j| ≤ w) (hS : ∀ v : Fin n → ℝ, δ * ∑ i, v i ^ 2 ≤ qf S v)
    (hδ : (n : ℝ) * w < δ) (v : Fin n → ℝ) (hv : v ≠ 0) : 0 < qf G v := by
  obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hv
  have hw : 0 ≤ w := le_trans (abs_nonneg _) (hbox i0 i0)
  have hpos : 0 < ∑ i, v i ^ 2 :=
    lt_of_lt_of_le (by simpa using pow_pos (abs_pos.mpr hi0) 2)
      (Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i0))
  have h1 := abs_qf_le (fun i j => G i j - S i j) w hbox v
  have h2 := sum_abs_sq_le v
  have h3 := hS v
  have hsub := qf_sub G S v
  have h4 : -(w * (∑ i, |v i|) ^ 2) ≤ qf (fun i j => G i j - S i j) v := by
    have := neg_abs_le (qf (fun i j => G i j - S i j) v)
    linarith
  have h5 : w * (∑ i, |v i|) ^ 2 ≤ w * ((n : ℝ) * ∑ i, v i ^ 2) := mul_le_mul_of_nonneg_left h2 hw
  nlinarith

lemma dot_eq_qf {k : ℕ} (G : Matrix (Fin k) (Fin k) ℝ) (x : Fin k → ℝ) :
    star x ⬝ᵥ (G *ᵥ x) = qf (fun i j => G i j) x := by
  simp only [star_trivial, dotProduct, Matrix.mulVec, qf, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

/-- **Schur-complement link (generic).**  Let `M = [[A, B], [Bᵀ, C]]` be a real symmetric block matrix
(`A` of size `k`, `C` of any finite size), `C` positive definite, and suppose the Schur complement
`A - B C⁻¹ Bᵀ` lies entrywise within `w` of a matrix `S` whose form is `≥ δ |v|²` with `k w < δ`.
Then `M` is positive semidefinite.  (Applied with `M` = the leading Galerkin block minus `λ₀ I`.) -/
theorem schur_link {k : ℕ} {m : Type*} [Fintype m] [DecidableEq m]
    (S : Fin k → Fin k → ℝ) (w δ : ℝ) (hS : ∀ v : Fin k → ℝ, δ * ∑ i, v i ^ 2 ≤ qf S v)
    (hδ : (k : ℝ) * w < δ)
    (A : Matrix (Fin k) (Fin k) ℝ) (hA : A.IsHermitian) (B : Matrix (Fin k) m ℝ)
    (C : Matrix m m ℝ) (hC : C.PosDef)
    (hbox : ∀ i j, |(A - B * C⁻¹ * Bᴴ) i j - S i j| ≤ w) :
    (Matrix.fromBlocks A B Bᴴ C).PosSemidef := by
  have : Invertible C := hC.isUnit.invertible
  rw [Matrix.PosDef.fromBlocks₂₂ A B hC]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · exact hA.sub (Matrix.isHermitian_mul_mul_conjTranspose B hC.1.inv)
  · intro x
    rw [dot_eq_qf]
    by_cases hx : x = 0
    · subst hx; simp [qf]
    · exact le_of_lt (posdef_of_box _ S w δ hbox hS hδ x hx)

/-- **Two-block assembly** (step [C6] of every certificate).  With `X = |x_L|`, `Y = |x_T|` (leading and
tail Legendre coordinates), a leading-block lower bound `l`, a tail-block lower bound `d` and a coupling
bound `e ≥ 0`:  `l X² - 2 e X Y + d Y² ≥ (min l d - e)(X² + Y²)`. -/
theorem block_assembly (l d e X Y : ℝ) (he : 0 ≤ e) :
    (min l d - e) * (X ^ 2 + Y ^ 2) ≤ l * X ^ 2 - 2 * e * X * Y + d * Y ^ 2 := by
  have h1 : min l d * X ^ 2 ≤ l * X ^ 2 := mul_le_mul_of_nonneg_right (min_le_left l d) (sq_nonneg X)
  have h2 : min l d * Y ^ 2 ≤ d * Y ^ 2 := mul_le_mul_of_nonneg_right (min_le_right l d) (sq_nonneg Y)
  have h3 : 2 * e * X * Y ≤ e * (X ^ 2 + Y ^ 2) := by nlinarith [sq_nonneg (X - Y), he]
  nlinarith


/-! ## 2. Discrete cores of Lemma A (path graph) and Lemma A' (weighted Schur test) -/

namespace PathGraph


/-- Perron weight. -/
noncomputable def w (M : ℕ) (j : ℕ) : ℝ := Real.sin (π * ((j : ℝ) + 1) / ((M : ℝ) + 1))

lemma w_pos (M j : ℕ) (hj : j < M) : 0 < w M j := by
  unfold w
  apply Real.sin_pos_of_pos_of_lt_pi
  · have : (0:ℝ) < (j:ℝ) + 1 := by positivity
    positivity
  · have hM : (0:ℝ) < (M:ℝ) + 1 := by positivity
    rw [div_lt_iff₀ hM]
    have : ((j:ℝ) + 1) < (M:ℝ) + 1 := by
      have : (j:ℝ) < (M:ℝ) := by exact_mod_cast hj
      linarith
    nlinarith [Real.pi_pos]

lemma w_rec (M j : ℕ) :
    w M (j + 1) + (if j = 0 then 0 else w M (j - 1)) = 2 * Real.cos (π / ((M:ℝ) + 1)) * w M j := by
  unfold w
  have hM : ((M:ℝ) + 1) ≠ 0 := by positivity
  set θ := π / ((M:ℝ) + 1) with hθ
  have e1 : π * (((j + 1 : ℕ) : ℝ) + 1) / ((M:ℝ) + 1) = θ * ((j:ℝ) + 1) + θ := by
    rw [hθ]; push_cast; field_simp
  have e0 : π * ((j:ℝ) + 1) / ((M:ℝ) + 1) = θ * ((j:ℝ) + 1) := by
    rw [hθ]; field_simp
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h
    simp only [ite_true]
    rw [e1, e0]
    simp only [Nat.cast_zero, zero_add, mul_one]
    rw [show θ + θ = 2 * θ by ring, Real.sin_two_mul]
    ring
  · have hj : j ≠ 0 := Nat.pos_iff_ne_zero.mp h
    simp only [hj, ite_false]
    have e2 : π * (((j - 1 : ℕ) : ℝ) + 1) / ((M:ℝ) + 1) = θ * ((j:ℝ) + 1) - θ := by
      rw [hθ, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hj)]; push_cast; field_simp; ring
    rw [e1, e0, e2, Real.sin_add, Real.sin_sub]
    ring



lemma w_last (m : ℕ) : w (m + 1) (m + 1) = 0 := by
  unfold w
  have h : π * (((m + 1 : ℕ) : ℝ) + 1) / (((m + 1 : ℕ) : ℝ) + 1) = π := by
    have : (((m + 1 : ℕ) : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  rw [h, Real.sin_pi]

lemma amgm (a b p q : ℝ) (hp : 0 < p) (hq : 0 < q) : 2 * (a * b) ≤ q / p * a ^ 2 + p / q * b ^ 2 := by
  have h1 : 0 ≤ (q * a - p * b) ^ 2 := sq_nonneg _
  have h2 : q / p * a ^ 2 + p / q * b ^ 2 - 2 * (a * b) = (q * a - p * b) ^ 2 / (p * q) := by
    field_simp; ring
  have h3 : 0 ≤ (q * a - p * b) ^ 2 / (p * q) := div_nonneg h1 (le_of_lt (mul_pos hp hq))
  linarith

/-- **Path-graph Perron bound.**  `2 sum_{j<M-1} x_j x_{j+1} <= 2 cos(pi/(M+1)) sum_{j<M} x_j^2`. -/
theorem path_quad_le (M : ℕ) (x : ℕ → ℝ) :
    2 * ∑ j ∈ Finset.range (M - 1), x j * x (j + 1)
      ≤ 2 * Real.cos (π / ((M:ℝ) + 1)) * ∑ j ∈ Finset.range M, x j ^ 2 := by
  rcases M with _ | m
  · simp
  · simp only [Nat.add_sub_cancel]
    set c := 2 * Real.cos (π / (((m + 1 : ℕ) : ℝ) + 1)) with hc
    -- rewrite c * x_k^2 via the Perron recursion
    have key : ∀ k ∈ Finset.range (m + 1),
        c * x k ^ 2 = w (m + 1) (k + 1) / w (m + 1) k * x k ^ 2
          + (if k = 0 then 0 else w (m + 1) (k - 1) / w (m + 1) k * x k ^ 2) := by
      intro k hk
      have hk' : k < m + 1 := Finset.mem_range.mp hk
      have hwpos := w_pos (m + 1) k hk'
      have hrec := w_rec (m + 1) k
      have hne : w (m + 1) k ≠ 0 := ne_of_gt hwpos
      split_ifs with h0
      · simp only [h0, ite_true] at hrec
        rw [h0] at hne ⊢
        field_simp
        rw [hc]; push_cast at hrec ⊢; nlinarith [hrec]
      · simp only [h0, ite_false] at hrec
        field_simp
        rw [hc]; push_cast at hrec ⊢; nlinarith [hrec]
    have hR : c * ∑ j ∈ Finset.range (m + 1), x j ^ 2
        = ∑ j ∈ Finset.range m, (w (m + 1) (j + 1) / w (m + 1) j * x j ^ 2
            + w (m + 1) j / w (m + 1) (j + 1) * x (j + 1) ^ 2) := by
      rw [Finset.mul_sum, Finset.sum_congr rfl key, Finset.sum_add_distrib,
        Finset.sum_range_succ (fun k => w (m + 1) (k + 1) / w (m + 1) k * x k ^ 2), w_last,
        Finset.sum_range_succ' (fun k => if k = 0 then 0 else w (m + 1) (k - 1) / w (m + 1) k * x k ^ 2)]
      simp only [ite_true, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel, zero_div, zero_mul, add_zero]
      rw [← Finset.sum_add_distrib]
    rw [hR, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hj' : j < m := Finset.mem_range.mp hj
    have hp := w_pos (m + 1) j (by omega)
    have hq := w_pos (m + 1) (j + 1) (by omega)
    exact amgm (x j) (x (j + 1)) (w (m + 1) j) (w (m + 1) (j + 1)) hp hq


end PathGraph

namespace SchurTest


theorem schur_test {n : ℕ} (K : Fin n → Fin n → ℝ) (hK : ∀ i j, 0 ≤ K i j)
    (hsym : ∀ i j, K i j = K j i) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (Lam : ℝ)
    (hKw : ∀ i, ∑ j, K i j * w j ≤ Lam * w i) (x : Fin n → ℝ) :
    ∑ i, ∑ j, x i * K i j * x j ≤ Lam * ∑ i, x i ^ 2 := by
  -- pointwise AM-GM with weights
  have h1 : ∀ i j, x i * K i j * x j ≤
      K i j * (x i ^ 2 * (w j / w i)) / 2 + K i j * (x j ^ 2 * (w i / w j)) / 2 := by
    intro i j
    have hwi := hw i
    have hwj := hw j
    have hsq : 0 ≤ (x i * w j - x j * w i) ^ 2 := sq_nonneg _
    have key : x i * x j ≤ (x i ^ 2 * (w j / w i) + x j ^ 2 * (w i / w j)) / 2 := by
      have e : (x i ^ 2 * (w j / w i) + x j ^ 2 * (w i / w j)) / 2 - x i * x j
          = (x i * w j - x j * w i) ^ 2 / (2 * w i * w j) := by
        field_simp; ring
      have : 0 ≤ (x i * w j - x j * w i) ^ 2 / (2 * w i * w j) := by positivity
      linarith
    have := mul_le_mul_of_nonneg_left key (hK i j)
    nlinarith [this]
  calc ∑ i, ∑ j, x i * K i j * x j
      ≤ ∑ i, ∑ j, (K i j * (x i ^ 2 * (w j / w i)) / 2 + K i j * (x j ^ 2 * (w i / w j)) / 2) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => h1 i j))
    _ = ∑ i, ∑ j, K i j * (x i ^ 2 * (w j / w i)) := by
        have hB : ∑ i, ∑ j, K i j * (x j ^ 2 * (w i / w j))
            = ∑ i, ∑ j, K i j * (x i ^ 2 * (w j / w i)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
          rw [hsym j i]
        have hsplit : ∑ i, ∑ j, (K i j * (x i ^ 2 * (w j / w i)) / 2 + K i j * (x j ^ 2 * (w i / w j)) / 2)
            = (∑ i, ∑ j, K i j * (x i ^ 2 * (w j / w i))) / 2
              + (∑ i, ∑ j, K i j * (x j ^ 2 * (w i / w j))) / 2 := by
          simp only [Finset.sum_add_distrib, Finset.sum_div]
        rw [hsplit, hB]
        ring
    _ = ∑ i, x i ^ 2 / w i * ∑ j, K i j * w j := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        have := hw i
        field_simp
    _ ≤ ∑ i, x i ^ 2 / w i * (Lam * w i) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        exact mul_le_mul_of_nonneg_left (hKw i) (div_nonneg (sq_nonneg _) (le_of_lt (hw i)))
    _ = Lam * ∑ i, x i ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        have := hw i
        field_simp


end SchurTest

/-! ## 3. Lemma A in continuous form (window-aware comb bound) -/

namespace LemmaA


/-- index of the translation cell of `u` in the window `[-A, A]` for the shift `τ`. -/
noncomputable def cell (A τ u : ℝ) : ℝ := (⌊(u + A) / τ⌋ : ℝ)

/-- the path-graph angle `θ = π/(K + 2)`, `K = ⌊2A/τ⌋` (orbits have at most `K + 1` points). -/
noncomputable def θ (A τ : ℝ) : ℝ := π / ((⌊2 * A / τ⌋ : ℝ) + 2)

/-- Perron weight placed on the window: `sin(θ (j(u) + 1))` on `[-A, A]`, zero outside. -/
noncomputable def W (A τ u : ℝ) : ℝ :=
  if u ∈ Set.Icc (-A) A then Real.sin (θ A τ * (cell A τ u + 1)) else 0

lemma cell_nonneg {A τ u : ℝ} (hτ : 0 < τ) (hu : u ∈ Set.Icc (-A) A) : 0 ≤ cell A τ u := by
  unfold cell
  have : (0:ℝ) ≤ (u + A) / τ := div_nonneg (by linarith [hu.1]) hτ.le
  exact_mod_cast Int.floor_nonneg.mpr this

lemma cell_le {A τ u : ℝ} (hτ : 0 < τ) (hu : u ∈ Set.Icc (-A) A) :
    cell A τ u ≤ (⌊2 * A / τ⌋ : ℝ) := by
  unfold cell
  have : (u + A) / τ ≤ 2 * A / τ := div_le_div_of_nonneg_right (by linarith [hu.2]) hτ.le
  exact_mod_cast Int.floor_mono this

lemma K_nonneg {A τ : ℝ} (hτ : 0 < τ) (hA : 0 ≤ A) : (0:ℝ) ≤ (⌊2 * A / τ⌋ : ℝ) := by
  have : (0:ℝ) ≤ 2 * A / τ := div_nonneg (by linarith) hτ.le
  exact_mod_cast Int.floor_nonneg.mpr this

lemma cell_add {A τ u : ℝ} (hτ : 0 < τ) : cell A τ (u + τ) = cell A τ u + 1 := by
  unfold cell
  have h : (u + τ + A) / τ = (u + A) / τ + 1 := by field_simp; ring
  rw [h, Int.floor_add_one]
  push_cast; ring

lemma cell_sub {A τ u : ℝ} (hτ : 0 < τ) : cell A τ (u - τ) = cell A τ u - 1 := by
  unfold cell
  have h : (u - τ + A) / τ = (u + A) / τ - 1 := by field_simp; ring
  rw [h, Int.floor_sub_one]
  push_cast; ring

lemma θ_pos {A τ : ℝ} (hτ : 0 < τ) (hA : 0 ≤ A) : 0 < θ A τ := by
  unfold θ
  have := K_nonneg hτ hA
  exact div_pos Real.pi_pos (by linarith)

lemma θ_mul {A τ : ℝ} (hτ : 0 < τ) (hA : 0 ≤ A) : θ A τ * ((⌊2 * A / τ⌋ : ℝ) + 2) = π := by
  unfold θ
  have := K_nonneg hτ hA
  field_simp

lemma sin_ge_of_mem {t x : ℝ} (ht : 0 < t) (ht2 : t ≤ π / 2) (hx1 : t ≤ x) (hx2 : x ≤ π - t) :
    Real.sin t ≤ Real.sin x := by
  rcases le_total x (π / 2) with h | h
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) h hx1
  · rw [← Real.sin_pi_sub x]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)

lemma W_ge {A τ u : ℝ} (hτ : 0 < τ) (hu : u ∈ Set.Icc (-A) A) :
    Real.sin (θ A τ) ≤ W A τ u := by
  have hA : 0 ≤ A := by linarith [hu.1, hu.2]
  have hθ := θ_pos hτ hA
  have hθm := θ_mul hτ hA
  have hK := K_nonneg hτ hA
  have hc0 := cell_nonneg hτ hu
  have hc1 := cell_le hτ hu
  unfold W
  simp only [hu, ite_true]
  apply sin_ge_of_mem hθ
  · -- θ ≤ π/2
    have : θ A τ * 2 ≤ π := by nlinarith
    linarith
  · nlinarith
  · nlinarith

lemma W_nonneg (A τ u : ℝ) (hτ : 0 < τ) : 0 ≤ W A τ u := by
  unfold W
  split_ifs with hu
  · have hA : 0 ≤ A := by linarith [hu.1, hu.2]
    have hθ := θ_pos hτ hA
    have hθm := θ_mul hτ hA
    have hc0 := cell_nonneg hτ hu
    have hc1 := cell_le hτ hu
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · positivity
    · nlinarith
  · exact le_rfl

lemma W_le_one (A τ u : ℝ) : W A τ u ≤ 1 := by
  unfold W
  split_ifs
  · exact Real.sin_le_one _
  · norm_num

lemma W_pos {A τ u : ℝ} (hτ : 0 < τ) (hu : u ∈ Set.Icc (-A) A) : 0 < W A τ u := by
  have hA : 0 ≤ A := by linarith [hu.1, hu.2]
  have hθ := θ_pos hτ hA
  have hθm := θ_mul hτ hA
  have hK := K_nonneg hτ hA
  have h1 : 0 < Real.sin (θ A τ) := by
    apply Real.sin_pos_of_pos_of_lt_pi hθ
    nlinarith
  exact lt_of_lt_of_le h1 (W_ge hτ hu)

/-- The Perron recursion on the window: `W(u+τ) + W(u-τ) ≤ 2 cos θ W(u)` for `u` in the window. -/
lemma W_rec {A τ u : ℝ} (hτ : 0 < τ) (hu : u ∈ Set.Icc (-A) A) :
    W A τ (u + τ) + W A τ (u - τ) ≤ 2 * Real.cos (θ A τ) * W A τ u := by
  have hA : 0 ≤ A := by linarith [hu.1, hu.2]
  have hθ := θ_pos hτ hA
  have hθm := θ_mul hτ hA
  have hK := K_nonneg hτ hA
  have hc0 := cell_nonneg hτ hu
  have hc1 := cell_le hτ hu
  have hWu : W A τ u = Real.sin (θ A τ * (cell A τ u + 1)) := by
    unfold W; simp only [hu, ite_true]
  have hplus : W A τ (u + τ) ≤ Real.sin (θ A τ * (cell A τ u + 2)) := by
    unfold W
    split_ifs with h
    · rw [cell_add hτ]
      apply le_of_eq; congr 1; ring
    · apply Real.sin_nonneg_of_nonneg_of_le_pi
      · positivity
      · nlinarith
  have hminus : W A τ (u - τ) ≤ Real.sin (θ A τ * cell A τ u) := by
    unfold W
    split_ifs with h
    · rw [cell_sub hτ]
      apply le_of_eq; congr 1; ring
    · apply Real.sin_nonneg_of_nonneg_of_le_pi
      · positivity
      · nlinarith
  have hid : Real.sin (θ A τ * (cell A τ u + 2)) + Real.sin (θ A τ * cell A τ u)
      = 2 * Real.cos (θ A τ) * Real.sin (θ A τ * (cell A τ u + 1)) := by
    have e1 : θ A τ * (cell A τ u + 2) = θ A τ * (cell A τ u + 1) + θ A τ := by ring
    have e2 : θ A τ * cell A τ u = θ A τ * (cell A τ u + 1) - θ A τ := by ring
    rw [e1, e2, Real.sin_add, Real.sin_sub]
    ring
  rw [hWu]
  linarith

lemma W_measurable (A τ : ℝ) : Measurable (W A τ) := by
  unfold W
  refine Measurable.ite measurableSet_Icc ?_ measurable_const
  unfold cell
  have h1 : Measurable (fun u : ℝ => ⌊(u + A) / τ⌋) :=
    ((measurable_id.add_const A).div_const τ).floor
  have h2 : Measurable (fun u : ℝ => ((⌊(u + A) / τ⌋ : ℤ) : ℝ)) :=
    (measurable_of_countable (fun n : ℤ => (n : ℝ))).comp h1
  exact Real.measurable_sin.comp ((h2.add_const 1).const_mul (θ A τ))

lemma amgm_abs (a b p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    2 * (|a| * |b|) ≤ p / q * b ^ 2 + q / p * a ^ 2 := by
  have h1 : 0 ≤ (p * |b| - q * |a|) ^ 2 := sq_nonneg _
  have h2 : p / q * b ^ 2 + q / p * a ^ 2 - 2 * (|a| * |b|) = (p * |b| - q * |a|) ^ 2 / (p * q) := by
    have ha : a ^ 2 = |a| ^ 2 := (sq_abs a).symm
    have hb : b ^ 2 = |b| ^ 2 := (sq_abs b).symm
    rw [ha, hb]
    field_simp
    ring
  have h3 : 0 ≤ (p * |b| - q * |a|) ^ 2 / (p * q) := div_nonneg h1 (le_of_lt (mul_pos hp hq))
  linarith

/-- **Lemma A (continuous form, one shift).**  For a real square-integrable `g` vanishing outside
`[-A, A]` and a shift `τ > 0`,
  `2 ∫ |g(u+τ)| |g(u)| du ≤ 2 cos(π/(⌊2A/τ⌋ + 2)) ∫ g(u)^2 du`.
The translation orbits of the window have at most `⌊2A/τ⌋ + 1` points, and on each orbit `S_τ + S_τ^*`
is a path-graph adjacency; the proof is the weighted AM-GM with the Perron weight `W`, integrated
(translation invariance of Lebesgue measure), with no orbit decomposition needed. -/
theorem shift_bound (A τ : ℝ) (hτ : 0 < τ) (g : ℝ → ℝ) (hgm : Measurable g)
    (hg2 : Integrable (fun u => g u ^ 2)) (hsupp : ∀ u, g u ≠ 0 → u ∈ Set.Icc (-A) A) :
    2 * ∫ u, |g (u + τ)| * |g u| ≤ 2 * Real.cos (θ A τ) * ∫ u, g u ^ 2 := by
  by_cases hA : 0 ≤ A
  swap
  · have hg0 : ∀ u, g u = 0 := by
      intro u
      by_contra h
      have := hsupp u h
      exact hA (by linarith [this.1, this.2])
    simp [hg0]
  have hθ := θ_pos hτ hA
  have hθm := θ_mul hτ hA
  have hK := K_nonneg hτ hA
  set s := Real.sin (θ A τ) with hs
  have hspos : 0 < s := by
    apply Real.sin_pos_of_pos_of_lt_pi hθ
    nlinarith
  -- the three auxiliary functions
  set φ1 : ℝ → ℝ := fun u => W A τ (u + τ) / W A τ u * g u ^ 2 with hφ1
  set ψ : ℝ → ℝ := fun v => W A τ (v - τ) / W A τ v * g v ^ 2 with hψ
  set φ2 : ℝ → ℝ := fun u => W A τ u / W A τ (u + τ) * g (u + τ) ^ 2 with hφ2
  have hWm := W_measurable A τ
  have hφ1_nn : ∀ u, 0 ≤ φ1 u := fun u =>
    mul_nonneg (div_nonneg (W_nonneg _ _ _ hτ) (W_nonneg _ _ _ hτ)) (sq_nonneg _)
  have hψ_nn : ∀ u, 0 ≤ ψ u := fun u =>
    mul_nonneg (div_nonneg (W_nonneg _ _ _ hτ) (W_nonneg _ _ _ hτ)) (sq_nonneg _)
  have hφ2_nn : ∀ u, 0 ≤ φ2 u := fun u =>
    mul_nonneg (div_nonneg (W_nonneg _ _ _ hτ) (W_nonneg _ _ _ hτ)) (sq_nonneg _)
  -- ratio bound: W(x)/W(u) ≤ 1/s
  have hratio : ∀ x u, W A τ x / W A τ u ≤ 1 / s := by
    intro x u
    by_cases hu : u ∈ Set.Icc (-A) A
    · have hWu := W_ge hτ hu
      have hWpos := W_pos hτ hu
      rw [div_le_div_iff₀ hWpos hspos]
      have := W_le_one A τ x
      have := W_nonneg A τ x hτ
      nlinarith
    · have : W A τ u = 0 := by unfold W; simp [hu]
      rw [this, div_zero]
      positivity
  have hφ1_le : ∀ u, φ1 u ≤ g u ^ 2 / s := by
    intro u
    have := hratio (u + τ) u
    have hg := sq_nonneg (g u)
    calc φ1 u = W A τ (u + τ) / W A τ u * g u ^ 2 := rfl
      _ ≤ 1 / s * g u ^ 2 := mul_le_mul_of_nonneg_right this hg
      _ = g u ^ 2 / s := by ring
  have hψ_le : ∀ u, ψ u ≤ g u ^ 2 / s := by
    intro u
    have := hratio (u - τ) u
    have hg := sq_nonneg (g u)
    calc ψ u = W A τ (u - τ) / W A τ u * g u ^ 2 := rfl
      _ ≤ 1 / s * g u ^ 2 := mul_le_mul_of_nonneg_right this hg
      _ = g u ^ 2 / s := by ring
  -- integrability
  have hφ1_int : Integrable φ1 := by
    refine Integrable.mono' (hg2.div_const s) ?_ (Filter.Eventually.of_forall (fun u => ?_))
    · exact ((hWm.comp (measurable_add_const τ)).div hWm |>.mul (hgm.pow_const 2)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (hφ1_nn u)]; exact hφ1_le u
  have hψ_int : Integrable ψ := by
    refine Integrable.mono' (hg2.div_const s) ?_ (Filter.Eventually.of_forall (fun u => ?_))
    · exact ((hWm.comp (measurable_sub_const τ)).div hWm |>.mul (hgm.pow_const 2)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (hψ_nn u)]; exact hψ_le u
  have hφ2_eq : φ2 = fun u => ψ (u + τ) := by
    funext u
    simp only [hφ2, hψ, add_sub_cancel_right]
  have hφ2_int : Integrable φ2 := by
    rw [hφ2_eq]; exact hψ_int.comp_add_right τ
  have hL_int : Integrable (fun u => 2 * (|g (u + τ)| * |g u|)) := by
    refine Integrable.mono' ((hg2.comp_add_right τ).add hg2) ?_ (Filter.Eventually.of_forall (fun u => ?_))
    · exact (((hgm.comp (measurable_add_const τ)).abs.mul hgm.abs).const_mul 2).aestronglyMeasurable
    · have h1 : 0 ≤ 2 * (|g (u + τ)| * |g u|) := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg h1]
      have h2 : 0 ≤ (|g (u + τ)| - |g u|) ^ 2 := sq_nonneg _
      have h3 : g (u + τ) ^ 2 = |g (u + τ)| ^ 2 := (sq_abs _).symm
      have h4 : g u ^ 2 = |g u| ^ 2 := (sq_abs _).symm
      simp only [Pi.add_apply]
      nlinarith
  -- pointwise AM-GM
  have hpt : ∀ u, 2 * (|g (u + τ)| * |g u|) ≤ φ1 u + φ2 u := by
    intro u
    by_cases h1 : g u = 0
    · rw [h1, abs_zero, mul_zero, mul_zero]
      exact add_nonneg (hφ1_nn u) (hφ2_nn u)
    by_cases h2 : g (u + τ) = 0
    · rw [h2, abs_zero, zero_mul, mul_zero]
      exact add_nonneg (hφ1_nn u) (hφ2_nn u)
    have hu := hsupp u h1
    have hu' := hsupp (u + τ) h2
    have hp := W_pos hτ hu'
    have hq := W_pos hτ hu
    have := amgm_abs (g (u + τ)) (g u) (W A τ (u + τ)) (W A τ u) hp hq
    simpa only [hφ1, hφ2] using this
  -- pointwise Perron recursion
  have hpt2 : ∀ u, φ1 u + ψ u ≤ 2 * Real.cos (θ A τ) * g u ^ 2 := by
    intro u
    by_cases h1 : g u = 0
    · simp only [hφ1, hψ, h1]; norm_num
    have hu := hsupp u h1
    have hq := W_pos hτ hu
    have hrec := W_rec hτ hu
    have hsum : φ1 u + ψ u = (W A τ (u + τ) + W A τ (u - τ)) / W A τ u * g u ^ 2 := by
      simp only [hφ1, hψ]; rw [add_div]; ring
    rw [hsum]
    have hg := sq_nonneg (g u)
    have hdiv : (W A τ (u + τ) + W A τ (u - τ)) / W A τ u ≤ 2 * Real.cos (θ A τ) := by
      rw [div_le_iff₀ hq]; exact hrec
    exact mul_le_mul_of_nonneg_right hdiv hg
  -- integrate
  have hI2 : ∫ u, φ2 u = ∫ u, ψ u := by
    rw [hφ2_eq]; exact integral_add_right_eq_self ψ τ
  calc 2 * ∫ u, |g (u + τ)| * |g u|
      = ∫ u, 2 * (|g (u + τ)| * |g u|) := (integral_const_mul 2 _).symm
    _ ≤ ∫ u, (φ1 u + φ2 u) := integral_mono hL_int (hφ1_int.add hφ2_int) hpt
    _ = (∫ u, φ1 u) + ∫ u, φ2 u := integral_add hφ1_int hφ2_int
    _ = (∫ u, φ1 u) + ∫ u, ψ u := by rw [hI2]
    _ = ∫ u, (φ1 u + ψ u) := (integral_add hφ1_int hψ_int).symm
    _ ≤ ∫ u, 2 * Real.cos (θ A τ) * g u ^ 2 :=
        integral_mono (hφ1_int.add hψ_int) (hg2.const_mul _) hpt2
    _ = 2 * Real.cos (θ A τ) * ∫ u, g u ^ 2 := integral_const_mul _ _

/-- Signed form: `|2 ∫ g(u+τ) g(u) du| ≤ 2 cos(π/(⌊2A/τ⌋+2)) ∫ g^2`. -/
theorem shift_bound_signed (A τ : ℝ) (hτ : 0 < τ) (g : ℝ → ℝ) (hgm : Measurable g)
    (hg2 : Integrable (fun u => g u ^ 2)) (hsupp : ∀ u, g u ≠ 0 → u ∈ Set.Icc (-A) A) :
    |∫ u, g (u + τ) * g u| ≤ Real.cos (θ A τ) * ∫ u, g u ^ 2 := by
  have h := shift_bound A τ hτ g hgm hg2 hsupp
  have h1 : |∫ u, g (u + τ) * g u| ≤ ∫ u, |g (u + τ)| * |g u| := by
    have := norm_integral_le_integral_norm (μ := volume) (fun u => g (u + τ) * g u)
    simpa only [Real.norm_eq_abs, abs_mul] using this
  linarith

/-- **Lemma A (window-aware comb bound).**  For finitely many shifts `τ_i > 0` with real weights `c_i`,
and `g` as above,
  `∑ c_i ∫ g(u + τ_i) g(u) du ≤ (∑ |c_i| cos(π/(⌊2A/τ_i⌋ + 2))) ∫ g^2`.
With `τ_n = log n`, `c_n = 2Λ(n)/√n` the left side is `<P_A g, g>` for the compressed prime comb
`P_A = ∑ (c_n/2)(S_{log n} + S_{log n}^*)` on `L^2(-A, A)`, and the bracket is `A'(A)`. -/
theorem comb_bound {ι : Type*} (s : Finset ι) (c τ : ι → ℝ) (hτ : ∀ i ∈ s, 0 < τ i) (A : ℝ)
    (g : ℝ → ℝ) (hgm : Measurable g) (hg2 : Integrable (fun u => g u ^ 2))
    (hsupp : ∀ u, g u ≠ 0 → u ∈ Set.Icc (-A) A) :
    ∑ i ∈ s, c i * ∫ u, g (u + τ i) * g u
      ≤ (∑ i ∈ s, |c i| * Real.cos (θ A (τ i))) * ∫ u, g u ^ 2 := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have h := shift_bound_signed A (τ i) (hτ i hi) g hgm hg2 hsupp
  calc c i * ∫ u, g (u + τ i) * g u ≤ |c i * ∫ u, g (u + τ i) * g u| := le_abs_self _
    _ = |c i| * |∫ u, g (u + τ i) * g u| := abs_mul _ _
    _ ≤ |c i| * (Real.cos (θ A (τ i)) * ∫ u, g u ^ 2) := mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = |c i| * Real.cos (θ A (τ i)) * ∫ u, g u ^ 2 := by ring

/-- **Lemma A for the prime comb.**  With `τ_n = log n` and `c_n = 2Λ(n)/√n` (`n` in `[2, N)`), for every real
square-integrable `g` vanishing outside `[-A, A]`:
  `∑ c_n ∫ g(u + log n) g(u) du ≤ A'(A) ∫ g²`,  `A'(A) = ∑ c_n cos(π/(⌊2A/log n⌋ + 2))`,
i.e. `<P_A g, g> ≤ A'(A) ‖g‖²` for the compressed prime comb (Λ = Mathlib's von Mangoldt function).
At `x = 11.006`, `A = 307/256 + 0.34`, this is the constant `A' = 5.02558` of the window-aware certificate
(Zhu's pointwise constant is `A_L = ∑ c_n = 8.52099`). -/
theorem prime_comb_bound (N : ℕ) (A : ℝ) (g : ℝ → ℝ) (hgm : Measurable g)
    (hg2 : Integrable (fun u => g u ^ 2)) (hsupp : ∀ u, g u ≠ 0 → u ∈ Set.Icc (-A) A) :
    ∑ n ∈ Finset.Ico 2 N, (2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        ∫ u, g (u + Real.log n) * g u
      ≤ (∑ n ∈ Finset.Ico 2 N, (2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
          Real.cos (π / ((⌊2 * A / Real.log n⌋ : ℝ) + 2))) * ∫ u, g u ^ 2 := by
  have hτ : ∀ n ∈ Finset.Ico 2 N, 0 < Real.log (n : ℝ) := by
    intro n hn
    have h2 : (2 : ℕ) ≤ n := (Finset.mem_Ico.mp hn).1
    apply Real.log_pos
    exact_mod_cast (show 1 < n by omega)
  have h := comb_bound (Finset.Ico 2 N) (fun n : ℕ => 2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n)
    (fun n : ℕ => Real.log n) hτ A g hgm hg2 hsupp
  have habs : ∀ n : ℕ, |2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n|
      = 2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n := by
    intro n
    apply abs_of_nonneg
    exact div_nonneg (mul_nonneg (by norm_num) ArithmeticFunction.vonMangoldt_nonneg) (Real.sqrt_nonneg _)
  simp only [habs] at h
  exact h


end LemmaA

/-! ## 4. Certificate cores -/

namespace Core_x6996_even

/-!
### Certificate core `Core_x6996_even`
x = e^{249/128} = 6.9958 (a = 249/256; prime powers 2, 3, 4, 5), EVEN sector.  M = leading 450 x 450 Legendre block of Zhu-type reduction R_{T#} (T# = 560, beta* = 0.1068), lam0 = 4.39e-28.  Arb: C - lam0 I >= 1e-40 I (verified LDL^T, residual 2.9e-72), Schur complement radius 4.3e-72.
The kernel checks only the exact rational part below; the Arb facts are the hypotheses `hbox`, `hC` of
`core_posdef` / `core_schur`.
-/

/-- Arb-computed Schur complement, rounded to rationals with denominator `10^48`. -/
def Sq : Fin 8 → Fin 8 → ℚ :=
  ![![((877745862771268607752056736643870413447345979 : ℚ) / 25000000000000000000000000000000000000000000000), ((81491842425415967921444313908780186102220737581 : ℚ) / 1000000000000000000000000000000000000000000000000), ((27114815515760539635930849183191268747780667487 : ℚ) / 250000000000000000000000000000000000000000000000), ((94634023814098222599265407000297942963285200539 : ℚ) / 1000000000000000000000000000000000000000000000000), ((17109496495792639108466175720485771417285169127 : ℚ) / 1000000000000000000000000000000000000000000000000), ((-881970621401306360399477013827136610462568677 : ℚ) / 100000000000000000000000000000000000000000000000), ((80766921478289967977837354726664518784345729529 : ℚ) / 500000000000000000000000000000000000000000000000), ((-28205337832845857635045831965750790186427911539 : ℚ) / 500000000000000000000000000000000000000000000000)],
    ![((81491842425415967921444313908780186102220737581 : ℚ) / 1000000000000000000000000000000000000000000000000), ((94708631823271461992008241463100558060885208621 : ℚ) / 500000000000000000000000000000000000000000000000), ((7878131889202422222644774362831377643311146131 : ℚ) / 31250000000000000000000000000000000000000000000), ((217260481007930584664595181461937930804038473017 : ℚ) / 1000000000000000000000000000000000000000000000000), ((23902489151928818724299312088633332682648813 : ℚ) / 800000000000000000000000000000000000000000000), ((-31803851354175913211267972899612881807994030919 : ℚ) / 1000000000000000000000000000000000000000000000000), ((95331021690242649417103233976159195277453431133 : ℚ) / 250000000000000000000000000000000000000000000000), ((-139261066753733834948451303376402781535442009803 : ℚ) / 1000000000000000000000000000000000000000000000000)],
    ![((27114815515760539635930849183191268747780667487 : ℚ) / 250000000000000000000000000000000000000000000000), ((7878131889202422222644774362831377643311146131 : ℚ) / 31250000000000000000000000000000000000000000000), ((167902658476051078898056168455284008766131508981 : ℚ) / 500000000000000000000000000000000000000000000000), ((290928335589929982832314295933102538469671051681 : ℚ) / 1000000000000000000000000000000000000000000000000), ((22380856600291829291136049330671304928365045931 : ℚ) / 500000000000000000000000000000000000000000000000), ((-36423597110971679140874942120550954716769676063 : ℚ) / 1000000000000000000000000000000000000000000000000), ((63368660590864790833261400223786132410622491993 : ℚ) / 125000000000000000000000000000000000000000000000), ((-90787261912141675930051371019207368392218621643 : ℚ) / 500000000000000000000000000000000000000000000000)],
    ![((94634023814098222599265407000297942963285200539 : ℚ) / 1000000000000000000000000000000000000000000000000), ((217260481007930584664595181461937930804038473017 : ℚ) / 1000000000000000000000000000000000000000000000000), ((290928335589929982832314295933102538469671051681 : ℚ) / 1000000000000000000000000000000000000000000000000), ((287549889018582973790766155899085023691643113529 : ℚ) / 1000000000000000000000000000000000000000000000000), ((165110130283342553560943357345878229433952503469 : ℚ) / 1000000000000000000000000000000000000000000000000), ((114295430974149373817994685389073008988184376423 : ℚ) / 1000000000000000000000000000000000000000000000000), ((187568303388798933363331186391375239473836143089 : ℚ) / 500000000000000000000000000000000000000000000000), ((-6775434183363926925229739200588885020470074353 : ℚ) / 125000000000000000000000000000000000000000000000)],
    ![((17109496495792639108466175720485771417285169127 : ℚ) / 1000000000000000000000000000000000000000000000000), ((23902489151928818724299312088633332682648813 : ℚ) / 800000000000000000000000000000000000000000000), ((22380856600291829291136049330671304928365045931 : ℚ) / 500000000000000000000000000000000000000000000000), ((165110130283342553560943357345878229433952503469 : ℚ) / 1000000000000000000000000000000000000000000000000), ((114152256740012161415949906217455837399890058897 : ℚ) / 250000000000000000000000000000000000000000000000), ((64368164880054501009407162019791628313531320327 : ℚ) / 125000000000000000000000000000000000000000000000), ((-164427876581532090296487922216398744920352819899 : ℚ) / 1000000000000000000000000000000000000000000000000), ((343876052696230763169076477043693264617116634843 : ℚ) / 1000000000000000000000000000000000000000000000000)],
    ![((-881970621401306360399477013827136610462568677 : ℚ) / 100000000000000000000000000000000000000000000000), ((-31803851354175913211267972899612881807994030919 : ℚ) / 1000000000000000000000000000000000000000000000000), ((-36423597110971679140874942120550954716769676063 : ℚ) / 1000000000000000000000000000000000000000000000000), ((114295430974149373817994685389073008988184376423 : ℚ) / 1000000000000000000000000000000000000000000000000), ((64368164880054501009407162019791628313531320327 : ℚ) / 125000000000000000000000000000000000000000000000), ((603730788316633153129015824813779181561394958017 : ℚ) / 1000000000000000000000000000000000000000000000000), ((-160541248931083393980489418692095630235398173951 : ℚ) / 500000000000000000000000000000000000000000000000), ((444139331584077410632230601109672470892404071443 : ℚ) / 1000000000000000000000000000000000000000000000000)],
    ![((80766921478289967977837354726664518784345729529 : ℚ) / 500000000000000000000000000000000000000000000000), ((95331021690242649417103233976159195277453431133 : ℚ) / 250000000000000000000000000000000000000000000000), ((63368660590864790833261400223786132410622491993 : ℚ) / 125000000000000000000000000000000000000000000000), ((187568303388798933363331186391375239473836143089 : ℚ) / 500000000000000000000000000000000000000000000000), ((-164427876581532090296487922216398744920352819899 : ℚ) / 1000000000000000000000000000000000000000000000000), ((-160541248931083393980489418692095630235398173951 : ℚ) / 500000000000000000000000000000000000000000000000), ((895750232483631665827513647065318080361095916297 : ℚ) / 1000000000000000000000000000000000000000000000000), ((-464505083245119558144126846520167091371328410051 : ℚ) / 1000000000000000000000000000000000000000000000000)],
    ![((-28205337832845857635045831965750790186427911539 : ℚ) / 500000000000000000000000000000000000000000000000), ((-139261066753733834948451303376402781535442009803 : ℚ) / 1000000000000000000000000000000000000000000000000), ((-90787261912141675930051371019207368392218621643 : ℚ) / 500000000000000000000000000000000000000000000000), ((-6775434183363926925229739200588885020470074353 : ℚ) / 125000000000000000000000000000000000000000000000), ((343876052696230763169076477043693264617116634843 : ℚ) / 1000000000000000000000000000000000000000000000000), ((444139331584077410632230601109672470892404071443 : ℚ) / 1000000000000000000000000000000000000000000000000), ((-464505083245119558144126846520167091371328410051 : ℚ) / 1000000000000000000000000000000000000000000000000), ((199448277522957170903757512319448888428265356779 : ℚ) / 500000000000000000000000000000000000000000000000)]]

/-- `Sq` as a real matrix. -/
noncomputable def Smat : Fin 8 → Fin 8 → ℝ := fun i j => (Sq i j : ℝ)

/-- entrywise half-width covering the Arb ball radius of the Schur complement and the rounding. -/
noncomputable def w0 : ℝ := ((20000000000000000000001 : ℝ) / 10000000000000000000000000000000000000000000000000000000000000000000000)

/-- exact lower bound for the form of `Smat`. -/
noncomputable def δ : ℝ := ((1972152263 : ℝ) / 625000000000000000000000000000000000000)

/-- EXACT rational congruence `Sq - δ I = L D Lᵀ`, written as a sum of squares (closed by `ring`). -/
theorem Sq_ldl (v : Fin 8 → ℝ) :
    qf Smat v - δ * ∑ i, v i ^ 2 =
    ((877745862771268607752056736564984322927345979 : ℝ) / 25000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 0 + ((81491842425415967921444313908780186102220737581 : ℝ) / 35109834510850744310082269462599372917093839160) * v 1 + ((3873545073680077090847264169027324106825809641 : ℝ) / 1253922661101812296788652480807120461324779970) * v 2 + ((94634023814098222599265407000297942963285200539 : ℝ) / 35109834510850744310082269462599372917093839160) * v 3 + ((17109496495792639108466175720485771417285169127 : ℝ) / 35109834510850744310082269462599372917093839160) * v 4 + ((-881970621401306360399477013827136610462568677 : ℝ) / 3510983451085074431008226946259937291709383916) * v 5 + ((80766921478289967977837354726664518784345729529 : ℝ) / 17554917255425372155041134731299686458546919580) * v 6 + ((-9401779277615285878348610655250263395475970513 : ℝ) / 5851639085141790718347044910433228819515639860) * v 7) ^ 2
    + ((9488398239480988727415456533011800333850267192246591105302019816589598380351474449173065159 : ℝ) / 35109834510850744310082269462599372917093839160000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 1 + ((12651926687367658245951087292146846493425809530832223652044683916202269989551937019666362932 : ℝ) / 9488398239480988727415456533011800333850267192246591105302019816589598380351474449173065159) * v 2 + ((-83921422805280624551058019123580801740308290484850029184458289166610211138588080453480810439 : ℝ) / 9488398239480988727415456533011800333850267192246591105302019816589598380351474449173065159) * v 3 + ((-345268844261307949205400741695052839475380825996592228941808644548565938890503052540623511787 : ℝ) / 9488398239480988727415456533011800333850267192246591105302019816589598380351474449173065159) * v 4 + ((-397893848821998034884171712523070428982942349654059686174144820792435056196890924321379484670 : ℝ) / 9488398239480988727415456533011800333850267192246591105302019816589598380351474449173065159) * v 5 + ((224535104589467753508987437970292059043808185440253899435217670345151737330703401586730814422 : ℝ) / 9488398239480988727415456533011800333850267192246591105302019816589598380351474449173065159) * v 6 + ((-292423115068337158862302492757263492368413502235196723731386459501464484538508359375623591162 : ℝ) / 9488398239480988727415456533011800333850267192246591105302019816589598380351474449173065159) * v 7) ^ 2
    + ((1322513706974593764880788642040295190452016832362019266594708050131642859154522412771910275624391275940549814416826982588343409184263971 : ℝ) / 4744199119740494363707728266505900166925133596123295552651009908294799190175737224586532579500000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 2 + ((16866513140670693644914823106476420555522232344211707013587199698780046594221927872272744886672151013827075697048215286831913948318941739 : ℝ) / 2645027413949187529761577284080590380904033664724038533189416100263285718309044825543820551248782551881099628833653965176686818368527942) * v 3 + ((23819473482489958231635645744048525186346857030222899268312800703188076604292334831944924932491022801747808570168354855573867643576924165 : ℝ) / 1322513706974593764880788642040295190452016832362019266594708050131642859154522412771910275624391275940549814416826982588343409184263971) * v 4 + ((56295049493886384209300857057633084452963997040758099557393243905219130910570040755062107316223412008359886472030846508144540071655944771 : ℝ) / 2645027413949187529761577284080590380904033664724038533189416100263285718309044825543820551248782551881099628833653965176686818368527942) * v 5 + ((-161619281200613395623469653304279359864766884832653132247938432093930351683805702601822315906894726975434460128835102213367211387512260 : ℝ) / 77794923939681986169458155414135011203059813668354074505571061772449579950266024280700604448493604467091165553930998975784906422603763) * v 6 + ((17988953786242970140452766439819338508635438590607756742489442594810114211170953989855651473323150556857814973199488627976131442166113657 : ℝ) / 1322513706974593764880788642040295190452016832362019266594708050131642859154522412771910275624391275940549814416826982588343409184263971) * v 7) ^ 2
    + ((51610914962906661237215835099636062886591910247070693772832206299493688061079271132573700616976592247561230221698774040491023160521273442198853733680892726285814501468850590991 : ℝ) / 2645027413949187529761577284080590380904033664724038533189416100263285718309044825543820551248782551881099628833653965176686818368527942000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 3 + ((13433392821632992436144400955237754211913958564366742954278298131678119863310237007199894595250787642839813794666377310955288086591171145695464150265056748449573033600740006714 : ℝ) / 3970070381762050864401218084587389452814762326697745674833246638422591389313790087121053893613584019043171555515290310807001781578559495553757979513914825098908807805296199307) * v 4 + ((-262285623510557658177671643735200967857344902744159755917517206259894092496649834322174497670195531474425382954844751966045470803093585405676984217385336721321114190553307692323 : ℝ) / 51610914962906661237215835099636062886591910247070693772832206299493688061079271132573700616976592247561230221698774040491023160521273442198853733680892726285814501468850590991) * v 5 + ((-1740175416505876039500443272941136226787673913128716043372106034405636249681155845818059783577349704174943533318449633094479012389146548778503062679428856513093941591366894995304 : ℝ) / 51610914962906661237215835099636062886591910247070693772832206299493688061079271132573700616976592247561230221698774040491023160521273442198853733680892726285814501468850590991) * v 6 + ((-141250506553154889973357155986954097669545177525645413717791353226088568441901632622520014912296394313069145205236430382452525447972534910187162355457695156925548043322328906944 : ℝ) / 51610914962906661237215835099636062886591910247070693772832206299493688061079271132573700616976592247561230221698774040491023160521273442198853733680892726285814501468850590991) * v 7) ^ 2
    + ((102974222707080864011771023219868805104859949671957601994373748526686947798255922766557835187095711554507874950569773478725701870905984532627498791191424858415967934624867007218182877769591087012534935080893717429 : ℝ) / 1985035190881025432200609042293694726407381163348872837416623319211295694656895043560526946806792009521585777757645155403500890789279747776878989756957412549454403902648099653500000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 4 + ((1705321563533078065086303881718244761617485519055620236356388383807240100130666927629411104163559227149785435968233808213363296148024944552957252811553315563271256839622982166190736979951274838217011588616259369379 : ℝ) / 205948445414161728023542046439737610209719899343915203988747497053373895596511845533115670374191423109015749901139546957451403741811969065254997582382849716831935869249734014436365755539182174025069870161787434858) * v 5 + ((4628292839196724358648383635770996337803533126765150387298169042112286893083061554336070196012734536603141645291354533979104738582473499636486992290703633437273935963233543890868229635945988486698423244868354968651 : ℝ) / 205948445414161728023542046439737610209719899343915203988747497053373895596511845533115670374191423109015749901139546957451403741811969065254997582382849716831935869249734014436365755539182174025069870161787434858) * v 6 + ((751270664381455676974888218743643690062192549920547136838795793123545798908703036646289450627161060854861494071339835709242066928945713841465252514206782550615645819876683047128808516260254350326334255507367352131 : ℝ) / 102974222707080864011771023219868805104859949671957601994373748526686947798255922766557835187095711554507874950569773478725701870905984532627498791191424858415967934624867007218182877769591087012534935080893717429) * v 7) ^ 2
    + ((28973570939154076989164805190665354821695866632713862245877120956734222363921637576574217601794579601355496540958167007479474440016574404582194426846095970373676215310375462395058871724141916514168788113630665845489076659617864337955964663279037433 : ℝ) / 2677329790384102464306046603716588932726358691470897651853717461693860642754653991930503714864488500417204748714814110446868248643555597848314968570977046318815166300246542187672754822009368262325908312103236653154000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 5 + ((109165296792984356020374057990488108531110690891132681936286090789124584217879667697371875807448978651173363026680150251804655893560040209612680148169178754630387245920064588729875667927381870077384166667393748833851958293720966188167331587924817545 : ℝ) / 28973570939154076989164805190665354821695866632713862245877120956734222363921637576574217601794579601355496540958167007479474440016574404582194426846095970373676215310375462395058871724141916514168788113630665845489076659617864337955964663279037433) * v 6 + ((-37374757388884206538583234097515339983084566235878020161482874484401825517642112388454770970593397079907073118273499231170122728496144858887839154063297285088015014957660138690777800883798965196713642971999683297677340183916755483174742311213622614 : ℝ) / 28973570939154076989164805190665354821695866632713862245877120956734222363921637576574217601794579601355496540958167007479474440016574404582194426846095970373676215310375462395058871724141916514168788113630665845489076659617864337955964663279037433) * v 7) ^ 2
    + ((1872637169365840022963830132158360003987197151210726804323445498920961582274798910148346806788976193023309615406941789988270689099049900840727261523845725271840057346852396171771410812965896295182287701629514419658326269908187709484333824499638807623022359925576082873828075237 : ℝ) / 28973570939154076989164805190665354821695866632713862245877120956734222363921637576574217601794579601355496540958167007479474440016574404582194426846095970373676215310375462395058871724141916514168788113630665845489076659617864337955964663279037433000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 6 + ((6368903156993274741338884780975747618532228945239980955392759527139151314794751366374819825517975525796526413442754074868714769184573903302665949075632699071811927067664598112412825297523971291984497739981956271568535273542502845508832241222434819139652819118463364415838114581 : ℝ) / 624212389788613340987943377386120001329065717070242268107815166306987194091599636716115602262992064341103205135647263329423563033016633613575753841281908423946685782284132057257136937655298765060762567209838139886108756636062569828111274833212935874340786641858694291276025079) * v 7) ^ 2
    + ((2896010541873106320424982094554405406520544313986883533694342872375531937990518487150195893563464594933015397896124677466462216516738426637678018228240819840069360982097229629176729410645637651643918325291111212207916142895552556538368666642495053881602930870656073043478272406218273157668864298151733 : ℝ) / 624212389788613340987943377386120001329065717070242268107815166306987194091599636716115602262992064341103205135647263329423563033016633613575753841281908423946685782284132057257136937655298765060762567209838139886108756636062569828111274833212935874340786641858694291276025079000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 7) ^ 2 := by
  simp only [qf, Smat, Sq, δ, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ]
  push_cast
  ring

theorem Smat_ge (v : Fin 8 → ℝ) : δ * ∑ i, v i ^ 2 ≤ qf Smat v := by
  have h := Sq_ldl v
  have hp : 0 ≤
    ((877745862771268607752056736564984322927345979 : ℝ) / 25000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 0 + ((81491842425415967921444313908780186102220737581 : ℝ) / 35109834510850744310082269462599372917093839160) * v 1 + ((3873545073680077090847264169027324106825809641 : ℝ) / 1253922661101812296788652480807120461324779970) * v 2 + ((94634023814098222599265407000297942963285200539 : ℝ) / 35109834510850744310082269462599372917093839160) * v 3 + ((17109496495792639108466175720485771417285169127 : ℝ) / 35109834510850744310082269462599372917093839160) * v 4 + ((-881970621401306360399477013827136610462568677 : ℝ) / 3510983451085074431008226946259937291709383916) * v 5 + ((80766921478289967977837354726664518784345729529 : ℝ) / 17554917255425372155041134731299686458546919580) * v 6 + ((-9401779277615285878348610655250263395475970513 : ℝ) / 5851639085141790718347044910433228819515639860) * v 7) ^ 2
    + ((9488398239480988727415456533011800333850267192246591105302019816589598380351474449173065159 : ℝ) / 35109834510850744310082269462599372917093839160000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 1 + ((12651926687367658245951087292146846493425809530832223652044683916202269989551937019666362932 : ℝ) / 9488398239480988727415456533011800333850267192246591105302019816589598380351474449173065159) * v 2 + ((-83921422805280624551058019123580801740308290484850029184458289166610211138588080453480810439 : ℝ) / 9488398239480988727415456533011800333850267192246591105302019816589598380351474449173065159) * v 3 + ((-345268844261307949205400741695052839475380825996592228941808644548565938890503052540623511787 : ℝ) / 9488398239480988727415456533011800333850267192246591105302019816589598380351474449173065159) * v 4 + ((-397893848821998034884171712523070428982942349654059686174144820792435056196890924321379484670 : ℝ) / 9488398239480988727415456533011800333850267192246591105302019816589598380351474449173065159) * v 5 + ((224535104589467753508987437970292059043808185440253899435217670345151737330703401586730814422 : ℝ) / 9488398239480988727415456533011800333850267192246591105302019816589598380351474449173065159) * v 6 + ((-292423115068337158862302492757263492368413502235196723731386459501464484538508359375623591162 : ℝ) / 9488398239480988727415456533011800333850267192246591105302019816589598380351474449173065159) * v 7) ^ 2
    + ((1322513706974593764880788642040295190452016832362019266594708050131642859154522412771910275624391275940549814416826982588343409184263971 : ℝ) / 4744199119740494363707728266505900166925133596123295552651009908294799190175737224586532579500000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 2 + ((16866513140670693644914823106476420555522232344211707013587199698780046594221927872272744886672151013827075697048215286831913948318941739 : ℝ) / 2645027413949187529761577284080590380904033664724038533189416100263285718309044825543820551248782551881099628833653965176686818368527942) * v 3 + ((23819473482489958231635645744048525186346857030222899268312800703188076604292334831944924932491022801747808570168354855573867643576924165 : ℝ) / 1322513706974593764880788642040295190452016832362019266594708050131642859154522412771910275624391275940549814416826982588343409184263971) * v 4 + ((56295049493886384209300857057633084452963997040758099557393243905219130910570040755062107316223412008359886472030846508144540071655944771 : ℝ) / 2645027413949187529761577284080590380904033664724038533189416100263285718309044825543820551248782551881099628833653965176686818368527942) * v 5 + ((-161619281200613395623469653304279359864766884832653132247938432093930351683805702601822315906894726975434460128835102213367211387512260 : ℝ) / 77794923939681986169458155414135011203059813668354074505571061772449579950266024280700604448493604467091165553930998975784906422603763) * v 6 + ((17988953786242970140452766439819338508635438590607756742489442594810114211170953989855651473323150556857814973199488627976131442166113657 : ℝ) / 1322513706974593764880788642040295190452016832362019266594708050131642859154522412771910275624391275940549814416826982588343409184263971) * v 7) ^ 2
    + ((51610914962906661237215835099636062886591910247070693772832206299493688061079271132573700616976592247561230221698774040491023160521273442198853733680892726285814501468850590991 : ℝ) / 2645027413949187529761577284080590380904033664724038533189416100263285718309044825543820551248782551881099628833653965176686818368527942000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 3 + ((13433392821632992436144400955237754211913958564366742954278298131678119863310237007199894595250787642839813794666377310955288086591171145695464150265056748449573033600740006714 : ℝ) / 3970070381762050864401218084587389452814762326697745674833246638422591389313790087121053893613584019043171555515290310807001781578559495553757979513914825098908807805296199307) * v 4 + ((-262285623510557658177671643735200967857344902744159755917517206259894092496649834322174497670195531474425382954844751966045470803093585405676984217385336721321114190553307692323 : ℝ) / 51610914962906661237215835099636062886591910247070693772832206299493688061079271132573700616976592247561230221698774040491023160521273442198853733680892726285814501468850590991) * v 5 + ((-1740175416505876039500443272941136226787673913128716043372106034405636249681155845818059783577349704174943533318449633094479012389146548778503062679428856513093941591366894995304 : ℝ) / 51610914962906661237215835099636062886591910247070693772832206299493688061079271132573700616976592247561230221698774040491023160521273442198853733680892726285814501468850590991) * v 6 + ((-141250506553154889973357155986954097669545177525645413717791353226088568441901632622520014912296394313069145205236430382452525447972534910187162355457695156925548043322328906944 : ℝ) / 51610914962906661237215835099636062886591910247070693772832206299493688061079271132573700616976592247561230221698774040491023160521273442198853733680892726285814501468850590991) * v 7) ^ 2
    + ((102974222707080864011771023219868805104859949671957601994373748526686947798255922766557835187095711554507874950569773478725701870905984532627498791191424858415967934624867007218182877769591087012534935080893717429 : ℝ) / 1985035190881025432200609042293694726407381163348872837416623319211295694656895043560526946806792009521585777757645155403500890789279747776878989756957412549454403902648099653500000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 4 + ((1705321563533078065086303881718244761617485519055620236356388383807240100130666927629411104163559227149785435968233808213363296148024944552957252811553315563271256839622982166190736979951274838217011588616259369379 : ℝ) / 205948445414161728023542046439737610209719899343915203988747497053373895596511845533115670374191423109015749901139546957451403741811969065254997582382849716831935869249734014436365755539182174025069870161787434858) * v 5 + ((4628292839196724358648383635770996337803533126765150387298169042112286893083061554336070196012734536603141645291354533979104738582473499636486992290703633437273935963233543890868229635945988486698423244868354968651 : ℝ) / 205948445414161728023542046439737610209719899343915203988747497053373895596511845533115670374191423109015749901139546957451403741811969065254997582382849716831935869249734014436365755539182174025069870161787434858) * v 6 + ((751270664381455676974888218743643690062192549920547136838795793123545798908703036646289450627161060854861494071339835709242066928945713841465252514206782550615645819876683047128808516260254350326334255507367352131 : ℝ) / 102974222707080864011771023219868805104859949671957601994373748526686947798255922766557835187095711554507874950569773478725701870905984532627498791191424858415967934624867007218182877769591087012534935080893717429) * v 7) ^ 2
    + ((28973570939154076989164805190665354821695866632713862245877120956734222363921637576574217601794579601355496540958167007479474440016574404582194426846095970373676215310375462395058871724141916514168788113630665845489076659617864337955964663279037433 : ℝ) / 2677329790384102464306046603716588932726358691470897651853717461693860642754653991930503714864488500417204748714814110446868248643555597848314968570977046318815166300246542187672754822009368262325908312103236653154000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 5 + ((109165296792984356020374057990488108531110690891132681936286090789124584217879667697371875807448978651173363026680150251804655893560040209612680148169178754630387245920064588729875667927381870077384166667393748833851958293720966188167331587924817545 : ℝ) / 28973570939154076989164805190665354821695866632713862245877120956734222363921637576574217601794579601355496540958167007479474440016574404582194426846095970373676215310375462395058871724141916514168788113630665845489076659617864337955964663279037433) * v 6 + ((-37374757388884206538583234097515339983084566235878020161482874484401825517642112388454770970593397079907073118273499231170122728496144858887839154063297285088015014957660138690777800883798965196713642971999683297677340183916755483174742311213622614 : ℝ) / 28973570939154076989164805190665354821695866632713862245877120956734222363921637576574217601794579601355496540958167007479474440016574404582194426846095970373676215310375462395058871724141916514168788113630665845489076659617864337955964663279037433) * v 7) ^ 2
    + ((1872637169365840022963830132158360003987197151210726804323445498920961582274798910148346806788976193023309615406941789988270689099049900840727261523845725271840057346852396171771410812965896295182287701629514419658326269908187709484333824499638807623022359925576082873828075237 : ℝ) / 28973570939154076989164805190665354821695866632713862245877120956734222363921637576574217601794579601355496540958167007479474440016574404582194426846095970373676215310375462395058871724141916514168788113630665845489076659617864337955964663279037433000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 6 + ((6368903156993274741338884780975747618532228945239980955392759527139151314794751366374819825517975525796526413442754074868714769184573903302665949075632699071811927067664598112412825297523971291984497739981956271568535273542502845508832241222434819139652819118463364415838114581 : ℝ) / 624212389788613340987943377386120001329065717070242268107815166306987194091599636716115602262992064341103205135647263329423563033016633613575753841281908423946685782284132057257136937655298765060762567209838139886108756636062569828111274833212935874340786641858694291276025079) * v 7) ^ 2
    + ((2896010541873106320424982094554405406520544313986883533694342872375531937990518487150195893563464594933015397896124677466462216516738426637678018228240819840069360982097229629176729410645637651643918325291111212207916142895552556538368666642495053881602930870656073043478272406218273157668864298151733 : ℝ) / 624212389788613340987943377386120001329065717070242268107815166306987194091599636716115602262992064341103205135647263329423563033016633613575753841281908423946685782284132057257136937655298765060762567209838139886108756636062569828111274833212935874340786641858694291276025079000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 7) ^ 2 := by positivity
  linarith

theorem box_margin : (8 : ℝ) * w0 < δ := by norm_num [w0, δ]

/-- Every real `8 x 8` matrix in the Arb box around `Smat` is positive definite. -/
theorem core_posdef (G : Fin 8 → Fin 8 → ℝ) (hbox : ∀ i j, |G i j - Smat i j| ≤ w0)
    (v : Fin 8 → ℝ) (hv : v ≠ 0) : 0 < qf G v :=
  posdef_of_box G Smat w0 δ hbox Smat_ge box_margin v hv

/-- For every real symmetric block matrix `[[A, B], [Bᵀ, C]]` (`C` of any finite size) with `C` positive
definite and Schur complement in the Arb box, the block matrix is positive semidefinite.  With the block
matrix `= M - lam0 I` this is `lam_min(M) >= lam0`. -/
theorem core_schur {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix (Fin 8) (Fin 8) ℝ) (hA : A.IsHermitian) (B : Matrix (Fin 8) m ℝ)
    (C : Matrix m m ℝ) (hC : C.PosDef) (hbox : ∀ i j, |(A - B * C⁻¹ * Bᴴ) i j - Smat i j| ≤ w0) :
    (Matrix.fromBlocks A B Bᴴ C).PosSemidef :=
  schur_link Smat w0 δ Smat_ge box_margin A hA B C hC hbox

end Core_x6996_even

namespace Core_x6996_odd

/-!
### Certificate core `Core_x6996_odd`
x = 6.9958, ODD sector.  M = leading 620 x 620 Legendre block of R_{T#} (T# = 800, beta* = 0.464), lam0 = 1.25e-24.  Arb: C - lam0 I >= 1e-40 I (residual 5.8e-72), Schur radius 1.5e-72.
The kernel checks only the exact rational part below; the Arb facts are the hypotheses `hbox`, `hC` of
`core_posdef` / `core_schur`.
-/

/-- Arb-computed Schur complement, rounded to rationals with denominator `10^44`. -/
def Sq : Fin 8 → Fin 8 → ℚ :=
  ![![((318439016985242365033827649110241994029689 : ℚ) / 10000000000000000000000000000000000000000000), ((1866738370980511777818291049533080836996301 : ℚ) / 50000000000000000000000000000000000000000000), ((1085417747531089944220266474976279702075141 : ℚ) / 50000000000000000000000000000000000000000000), ((291322176567294263041006284432079798456733 : ℚ) / 50000000000000000000000000000000000000000000), ((1272586777141951760039439491999989100380773 : ℚ) / 25000000000000000000000000000000000000000000), ((6551092094602503907218495005041282510432723 : ℚ) / 50000000000000000000000000000000000000000000), ((-87914297484221275938713446778563694213401 : ℚ) / 10000000000000000000000000000000000000000000), ((1307238633632272681982601087701274926534937 : ℚ) / 25000000000000000000000000000000000000000000)],
    ![((1866738370980511777818291049533080836996301 : ℚ) / 50000000000000000000000000000000000000000000), ((1164349927505799470390812792714480093987421 : ℚ) / 20000000000000000000000000000000000000000000), ((302002631941521653739020253425198244492343 : ℚ) / 4000000000000000000000000000000000000000000), ((4494875433280554115218241516838327233629537 : ℚ) / 50000000000000000000000000000000000000000000), ((4787592431517752406503560943782950430891547 : ℚ) / 50000000000000000000000000000000000000000000), ((9415872116255641126633506058448454077545461 : ℚ) / 100000000000000000000000000000000000000000000), ((10190472723884320673863194024139677429260889 : ℚ) / 100000000000000000000000000000000000000000000), ((202473971960708619081438078554129267989981 : ℚ) / 4000000000000000000000000000000000000000000)],
    ![((1085417747531089944220266474976279702075141 : ℚ) / 50000000000000000000000000000000000000000000), ((302002631941521653739020253425198244492343 : ℚ) / 4000000000000000000000000000000000000000000), ((18822717976855988319501639768000516009038703 : ℚ) / 100000000000000000000000000000000000000000000), ((29206692336767799291408109223479735350435589 : ℚ) / 100000000000000000000000000000000000000000000), ((16106105070851544415816105624621355249488597 : ℚ) / 100000000000000000000000000000000000000000000), ((-11372669770347155495295143655985642205660909 : ℚ) / 100000000000000000000000000000000000000000000), ((38502318555437092563083795680045678143253601 : ℚ) / 100000000000000000000000000000000000000000000), ((58224564247465864640551576747764879891627 : ℚ) / 100000000000000000000000000000000000000000000)],
    ![((291322176567294263041006284432079798456733 : ℚ) / 50000000000000000000000000000000000000000000), ((4494875433280554115218241516838327233629537 : ℚ) / 50000000000000000000000000000000000000000000), ((29206692336767799291408109223479735350435589 : ℚ) / 100000000000000000000000000000000000000000000), ((48356781322115110361344060195520050891098349 : ℚ) / 100000000000000000000000000000000000000000000), ((24034591875213920487062893146218288472906327 : ℚ) / 100000000000000000000000000000000000000000000), ((-13366962638958142798129128104622257562356797 : ℚ) / 50000000000000000000000000000000000000000000), ((8512859901355882168588515506809374221922689 : ℚ) / 12500000000000000000000000000000000000000000), ((-463624644201039204411380742525538029615913 : ℚ) / 25000000000000000000000000000000000000000000)],
    ![((1272586777141951760039439491999989100380773 : ℚ) / 25000000000000000000000000000000000000000000), ((4787592431517752406503560943782950430891547 : ℚ) / 50000000000000000000000000000000000000000000), ((16106105070851544415816105624621355249488597 : ℚ) / 100000000000000000000000000000000000000000000), ((24034591875213920487062893146218288472906327 : ℚ) / 100000000000000000000000000000000000000000000), ((14360828719238719421324424769759846325645931 : ℚ) / 50000000000000000000000000000000000000000000), ((15457366540602530636423496245074601037362361 : ℚ) / 50000000000000000000000000000000000000000000), ((5609987030119571406989636595104123280376187 : ℚ) / 12500000000000000000000000000000000000000000), ((5505538731032192315371101449053602595509371 : ℚ) / 25000000000000000000000000000000000000000000)],
    ![((6551092094602503907218495005041282510432723 : ℚ) / 50000000000000000000000000000000000000000000), ((9415872116255641126633506058448454077545461 : ℚ) / 100000000000000000000000000000000000000000000), ((-11372669770347155495295143655985642205660909 : ℚ) / 100000000000000000000000000000000000000000000), ((-13366962638958142798129128104622257562356797 : ℚ) / 50000000000000000000000000000000000000000000), ((15457366540602530636423496245074601037362361 : ℚ) / 50000000000000000000000000000000000000000000), ((32895211662558189618076649897480753092865701 : ℚ) / 25000000000000000000000000000000000000000000), ((-2132668350813540938939256873373012250186003 : ℚ) / 20000000000000000000000000000000000000000000), ((30459558503178209496580392519459589956585203 : ℚ) / 50000000000000000000000000000000000000000000)],
    ![((-87914297484221275938713446778563694213401 : ℚ) / 10000000000000000000000000000000000000000000), ((10190472723884320673863194024139677429260889 : ℚ) / 100000000000000000000000000000000000000000000), ((38502318555437092563083795680045678143253601 : ℚ) / 100000000000000000000000000000000000000000000), ((8512859901355882168588515506809374221922689 : ℚ) / 12500000000000000000000000000000000000000000), ((5609987030119571406989636595104123280376187 : ℚ) / 12500000000000000000000000000000000000000000), ((-2132668350813540938939256873373012250186003 : ℚ) / 20000000000000000000000000000000000000000000), ((2908066740149325758819013396853973017711331 : ℚ) / 2500000000000000000000000000000000000000000), ((8028113941841755139278148797355960909271929 : ℚ) / 50000000000000000000000000000000000000000000)],
    ![((1307238633632272681982601087701274926534937 : ℚ) / 25000000000000000000000000000000000000000000), ((202473971960708619081438078554129267989981 : ℚ) / 4000000000000000000000000000000000000000000), ((58224564247465864640551576747764879891627 : ℚ) / 100000000000000000000000000000000000000000000), ((-463624644201039204411380742525538029615913 : ℚ) / 25000000000000000000000000000000000000000000), ((5505538731032192315371101449053602595509371 : ℚ) / 25000000000000000000000000000000000000000000), ((30459558503178209496580392519459589956585203 : ℚ) / 50000000000000000000000000000000000000000000), ((8028113941841755139278148797355960909271929 : ℚ) / 50000000000000000000000000000000000000000000), ((32430523145542204019736433778527753539023499 : ℚ) / 100000000000000000000000000000000000000000000)]]

/-- `Sq` as a real matrix. -/
noncomputable def Smat : Fin 8 → Fin 8 → ℝ := fun i j => (Sq i j : ℝ)

/-- entrywise half-width covering the Arb ball radius of the Schur complement and the rounding. -/
noncomputable def w0 : ℝ := ((200000000000000000000000001 : ℝ) / 10000000000000000000000000000000000000000000000000000000000000000000000)

/-- exact lower bound for the form of `Smat`. -/
noncomputable def δ : ℝ := ((12924697071141 : ℝ) / 1000000000000000000000000000000000000000)

/-- EXACT rational congruence `Sq - δ I = L D Lᵀ`, written as a sum of squares (closed by `ring`). -/
theorem Sq_ldl (v : Fin 8 → ℝ) :
    qf Smat v - δ * ∑ i, v i ^ 2 =
    ((318439016985242365033827519863271282619689 : ℝ) / 10000000000000000000000000000000000000000000) * ((1 : ℝ) * v 0 + ((1866738370980511777818291049533080836996301 : ℝ) / 1592195084926211825169137599316356413098445) * v 1 + ((1085417747531089944220266474976279702075141 : ℝ) / 1592195084926211825169137599316356413098445) * v 2 + ((291322176567294263041006284432079798456733 : ℝ) / 1592195084926211825169137599316356413098445) * v 3 + ((848391184761301173359626327999992733587182 : ℝ) / 530731694975403941723045866438785471032815) * v 4 + ((6551092094602503907218495005041282510432723 : ℝ) / 1592195084926211825169137599316356413098445) * v 5 + ((-87914297484221275938713446778563694213401 : ℝ) / 318439016985242365033827519863271282619689) * v 6 + ((871492422421515121321734058467516617689958 : ℝ) / 530731694975403941723045866438785471032815) * v 7) ^ 2
    + ((2299936867162675215199692411199017826768868278979199957580667123974809123583973436523 : ℝ) / 159219508492621182516913759931635641309844500000000000000000000000000000000000000000000) * ((1 : ℝ) * v 1 + ((7968795739582717533272727966059707143912834543423209320760223797359284880507610558993 : ℝ) / 2299936867162675215199692411199017826768868278979199957580667123974809123583973436523) * v 2 + ((13225792573818294241699485664402247305582201204120387747062029840578312295868822450664 : ℝ) / 2299936867162675215199692411199017826768868278979199957580667123974809123583973436523) * v 3 + ((5743216007011767087299656923832399847144537008153068658446824611752725392761288606138 : ℝ) / 2299936867162675215199692411199017826768868278979199957580667123974809123583973436523) * v 4 + ((-9466444665847173408569058324317193414908148825133001763132003601395830061990764807101 : ℝ) / 2299936867162675215199692411199017826768868278979199957580667123974809123583973436523) * v 5 + ((17866350508759154397400295396671035044817174714041702127639935217041047175672161514615 : ℝ) / 2299936867162675215199692411199017826768868278979199957580667123974809123583973436523) * v 6 + ((-1701638495184797760399374187160142337079830526780440650690724851076795716860398083523 : ℝ) / 2299936867162675215199692411199017826768868278979199957580667123974809123583973436523) * v 7) ^ 2
    + ((2152755603140157868189831773517971014913191480242299011621957670458962687887643505692731397559054116732935770315056888914417 : ℝ) / 114996843358133760759984620559950891338443413948959997879033356198740456179198671826150000000000000000000000000000000000000000000) * ((1 : ℝ) * v 2 + ((66100774360623472506226524777593385676858812110606485036989061554609552801678494401853500158662330143228355051733728856784385 : ℝ) / 4305511206280315736379663547035942029826382960484598023243915340917925375775287011385462795118108233465871540630113777828834) * v 3 + ((317614054412310785082346964854962216824202305733199912632849600580588316365218556158459596829427997940742988920732348778006729 : ℝ) / 4305511206280315736379663547035942029826382960484598023243915340917925375775287011385462795118108233465871540630113777828834) * v 4 + ((113244599002452101529392136034777850051386606299577951903275603675904099085758990644591761553786947297962807994332709504069040 : ℝ) / 717585201046719289396610591172657004971063826747433003873985890152987562629214501897577132519684705577645256771685629638139) * v 5 + ((255899269886004418574547957077811216667062951899609308951974010535534086003817457563869661423246684116222175290525991826810923 : ℝ) / 2152755603140157868189831773517971014913191480242299011621957670458962687887643505692731397559054116732935770315056888914417) * v 6 + ((226009717539987710486754134983927331331923105767513605423897905798821421701491370526928343532989944686234016054116130703674278 : ℝ) / 2152755603140157868189831773517971014913191480242299011621957670458962687887643505692731397559054116732935770315056888914417) * v 7) ^ 2
    + ((35804684284593949852047854545410089807685847209746479231348198361891730570737831479451417315998796390030518073802569681265080845843178802610952374106468127027642151 : ℝ) / 86110224125606314727593270940718840596527659209691960464878306818358507515505740227709255902362164669317430812602275556576680000000000000000000000000000000000000000000) * ((1 : ℝ) * v 3 + ((1035049734534770317818663654625623162832870753375071888217461615210164806712638987647992327284205387381838704405317831631115251610203203004369363034943591041033078059 : ℝ) / 179023421422969749260239272727050449038429236048732396156740991809458652853689157397257086579993981950152590369012848406325404229215894013054761870532340635138210755) * v 4 + ((2251661669785330013091083369778147242030268132315005857081374978274717062429147512130197401041974903350678089709430605185068440765164532021968741928071129401184531984 : ℝ) / 179023421422969749260239272727050449038429236048732396156740991809458652853689157397257086579993981950152590369012848406325404229215894013054761870532340635138210755) * v 5 + ((275369133640019024455762162092248882199198422532034712052450278515460206423296692001799190819786172452472965124771591163653630266212762792452286611220325184388687370 : ℝ) / 35804684284593949852047854545410089807685847209746479231348198361891730570737831479451417315998796390030518073802569681265080845843178802610952374106468127027642151) * v 6 + ((1365756385029261629352230158762534315031102157299359561162890277086971012714152993817800152154294219933615823500408764454590703321942148636488485420464677588288803868 : ℝ) / 179023421422969749260239272727050449038429236048732396156740991809458652853689157397257086579993981950152590369012848406325404229215894013054761870532340635138210755) * v 7) ^ 2
    + ((92236696489391948942419040557454482229118905600651207047972707705435442052128491659143244013678330555016055026706831019047792326085454115098818518321734263910148738654524345947401238210483605327421 : ℝ) / 17902342142296974926023927272705044903842923604873239615674099180945865285368915739725708657999398195015259036901284840632540422921589401305476187053234063513821075500000000000000000000000000000000000000000000) * ((1 : ℝ) * v 4 + ((7825458587674866143182520463769133597931194530351545689469596242181425994724346843927487006803126235170352282851333649398560048225978776992988961905424387108445616625450986845896318932116427501356436 : ℝ) / 92236696489391948942419040557454482229118905600651207047972707705435442052128491659143244013678330555016055026706831019047792326085454115098818518321734263910148738654524345947401238210483605327421) * v 5 + ((37651167737527288121726183944016730769654191527004860109944257251667042023215817033954403064380135030304771502446210969568570300100590269740509858900424071467332889600028882568322692257527196464311000 : ℝ) / 92236696489391948942419040557454482229118905600651207047972707705435442052128491659143244013678330555016055026706831019047792326085454115098818518321734263910148738654524345947401238210483605327421) * v 6 + ((24943319758911640370210135229713252663264897353393031854324255486672054860371362908581023578389292181602324501800351380594516725517087869088958867393642620515003012896465656752272403396575997034193762 : ℝ) / 92236696489391948942419040557454482229118905600651207047972707705435442052128491659143244013678330555016055026706831019047792326085454115098818518321734263910148738654524345947401238210483605327421) * v 7) ^ 2
    + ((40655118756919869093363418473542198662928991480727826850674451292318353911592419421202750456199223159916226316880985514855232095619584541626124805128352760563957022119597038108653036240570352948153023462105260156516689987329881028311 : ℝ) / 9223669648939194894241904055745448222911890560065120704797270770543544205212849165914324401367833055501605502670683101904779232608545411509881851832173426391014873865452434594740123821048360532742100000000000000000000000000000000000000000000) * ((1 : ℝ) * v 5 + ((202762034956009843076922855344421691474453588720336683096988300174277981586076541541309672127713507809726545545648686754348555180570344718125718772062296298401682007939703566708433210849533978400588525978910212947095026034612141841628 : ℝ) / 40655118756919869093363418473542198662928991480727826850674451292318353911592419421202750456199223159916226316880985514855232095619584541626124805128352760563957022119597038108653036240570352948153023462105260156516689987329881028311) * v 6 + ((132672813958959006345397121491433707151731317588046281723468161960565513794083354953965391264018692172094235896644708980576803516125420098311913648345087506653471134472116340949949540498046978334877925443999190904621211407012025468405 : ℝ) / 40655118756919869093363418473542198662928991480727826850674451292318353911592419421202750456199223159916226316880985514855232095619584541626124805128352760563957022119597038108653036240570352948153023462105260156516689987329881028311) * v 7) ^ 2
    + ((85978633901010264212019392195263235100069068041172896860043275640217574053045852279299615747282677633223980210378828935726564823582035273330630828292269836159235861164263753221752459931540458749212409707989419701755496830441906781124974056018227093291580713093 : ℝ) / 4065511875691986909336341847354219866292899148072782685067445129231835391159241942120275045619922315991622631688098551485523209561958454162612480512835276056395702211959703810865303624057035294815302346210526015651668998732988102831100000000000000000000000000000000000000000000) * ((1 : ℝ) * v 6 + ((-339473679394513128769467168357924970383852541601898212534093273068041008870663500783373385802920070521717873125721099696280218630636340203582873842121641257588237088079853925116334622603951348772054221547677210781989739936586365184885668056703268638454879750261 : ℝ) / 85978633901010264212019392195263235100069068041172896860043275640217574053045852279299615747282677633223980210378828935726564823582035273330630828292269836159235861164263753221752459931540458749212409707989419701755496830441906781124974056018227093291580713093) * v 7) ^ 2
    + ((9455925345332460208059709593203237876610797967123424250055566500627530929836287267261997383480694654087459903862972907456070978038866708195119344514450909590585187463317436190391215744727381262041640618479052136897785526781594336920457775286726902267690156313756023001279555121065341 : ℝ) / 4298931695050513210600969609763161755003453402058644843002163782010878702652292613964980787364133881661199010518941446786328241179101763666531541414613491807961793058213187661087622996577022937460620485399470985087774841522095339056248702800911354664579035654650000000000000000000000000000000000000000000) * ((1 : ℝ) * v 7) ^ 2 := by
  simp only [qf, Smat, Sq, δ, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ]
  push_cast
  ring

theorem Smat_ge (v : Fin 8 → ℝ) : δ * ∑ i, v i ^ 2 ≤ qf Smat v := by
  have h := Sq_ldl v
  have hp : 0 ≤
    ((318439016985242365033827519863271282619689 : ℝ) / 10000000000000000000000000000000000000000000) * ((1 : ℝ) * v 0 + ((1866738370980511777818291049533080836996301 : ℝ) / 1592195084926211825169137599316356413098445) * v 1 + ((1085417747531089944220266474976279702075141 : ℝ) / 1592195084926211825169137599316356413098445) * v 2 + ((291322176567294263041006284432079798456733 : ℝ) / 1592195084926211825169137599316356413098445) * v 3 + ((848391184761301173359626327999992733587182 : ℝ) / 530731694975403941723045866438785471032815) * v 4 + ((6551092094602503907218495005041282510432723 : ℝ) / 1592195084926211825169137599316356413098445) * v 5 + ((-87914297484221275938713446778563694213401 : ℝ) / 318439016985242365033827519863271282619689) * v 6 + ((871492422421515121321734058467516617689958 : ℝ) / 530731694975403941723045866438785471032815) * v 7) ^ 2
    + ((2299936867162675215199692411199017826768868278979199957580667123974809123583973436523 : ℝ) / 159219508492621182516913759931635641309844500000000000000000000000000000000000000000000) * ((1 : ℝ) * v 1 + ((7968795739582717533272727966059707143912834543423209320760223797359284880507610558993 : ℝ) / 2299936867162675215199692411199017826768868278979199957580667123974809123583973436523) * v 2 + ((13225792573818294241699485664402247305582201204120387747062029840578312295868822450664 : ℝ) / 2299936867162675215199692411199017826768868278979199957580667123974809123583973436523) * v 3 + ((5743216007011767087299656923832399847144537008153068658446824611752725392761288606138 : ℝ) / 2299936867162675215199692411199017826768868278979199957580667123974809123583973436523) * v 4 + ((-9466444665847173408569058324317193414908148825133001763132003601395830061990764807101 : ℝ) / 2299936867162675215199692411199017826768868278979199957580667123974809123583973436523) * v 5 + ((17866350508759154397400295396671035044817174714041702127639935217041047175672161514615 : ℝ) / 2299936867162675215199692411199017826768868278979199957580667123974809123583973436523) * v 6 + ((-1701638495184797760399374187160142337079830526780440650690724851076795716860398083523 : ℝ) / 2299936867162675215199692411199017826768868278979199957580667123974809123583973436523) * v 7) ^ 2
    + ((2152755603140157868189831773517971014913191480242299011621957670458962687887643505692731397559054116732935770315056888914417 : ℝ) / 114996843358133760759984620559950891338443413948959997879033356198740456179198671826150000000000000000000000000000000000000000000) * ((1 : ℝ) * v 2 + ((66100774360623472506226524777593385676858812110606485036989061554609552801678494401853500158662330143228355051733728856784385 : ℝ) / 4305511206280315736379663547035942029826382960484598023243915340917925375775287011385462795118108233465871540630113777828834) * v 3 + ((317614054412310785082346964854962216824202305733199912632849600580588316365218556158459596829427997940742988920732348778006729 : ℝ) / 4305511206280315736379663547035942029826382960484598023243915340917925375775287011385462795118108233465871540630113777828834) * v 4 + ((113244599002452101529392136034777850051386606299577951903275603675904099085758990644591761553786947297962807994332709504069040 : ℝ) / 717585201046719289396610591172657004971063826747433003873985890152987562629214501897577132519684705577645256771685629638139) * v 5 + ((255899269886004418574547957077811216667062951899609308951974010535534086003817457563869661423246684116222175290525991826810923 : ℝ) / 2152755603140157868189831773517971014913191480242299011621957670458962687887643505692731397559054116732935770315056888914417) * v 6 + ((226009717539987710486754134983927331331923105767513605423897905798821421701491370526928343532989944686234016054116130703674278 : ℝ) / 2152755603140157868189831773517971014913191480242299011621957670458962687887643505692731397559054116732935770315056888914417) * v 7) ^ 2
    + ((35804684284593949852047854545410089807685847209746479231348198361891730570737831479451417315998796390030518073802569681265080845843178802610952374106468127027642151 : ℝ) / 86110224125606314727593270940718840596527659209691960464878306818358507515505740227709255902362164669317430812602275556576680000000000000000000000000000000000000000000) * ((1 : ℝ) * v 3 + ((1035049734534770317818663654625623162832870753375071888217461615210164806712638987647992327284205387381838704405317831631115251610203203004369363034943591041033078059 : ℝ) / 179023421422969749260239272727050449038429236048732396156740991809458652853689157397257086579993981950152590369012848406325404229215894013054761870532340635138210755) * v 4 + ((2251661669785330013091083369778147242030268132315005857081374978274717062429147512130197401041974903350678089709430605185068440765164532021968741928071129401184531984 : ℝ) / 179023421422969749260239272727050449038429236048732396156740991809458652853689157397257086579993981950152590369012848406325404229215894013054761870532340635138210755) * v 5 + ((275369133640019024455762162092248882199198422532034712052450278515460206423296692001799190819786172452472965124771591163653630266212762792452286611220325184388687370 : ℝ) / 35804684284593949852047854545410089807685847209746479231348198361891730570737831479451417315998796390030518073802569681265080845843178802610952374106468127027642151) * v 6 + ((1365756385029261629352230158762534315031102157299359561162890277086971012714152993817800152154294219933615823500408764454590703321942148636488485420464677588288803868 : ℝ) / 179023421422969749260239272727050449038429236048732396156740991809458652853689157397257086579993981950152590369012848406325404229215894013054761870532340635138210755) * v 7) ^ 2
    + ((92236696489391948942419040557454482229118905600651207047972707705435442052128491659143244013678330555016055026706831019047792326085454115098818518321734263910148738654524345947401238210483605327421 : ℝ) / 17902342142296974926023927272705044903842923604873239615674099180945865285368915739725708657999398195015259036901284840632540422921589401305476187053234063513821075500000000000000000000000000000000000000000000) * ((1 : ℝ) * v 4 + ((7825458587674866143182520463769133597931194530351545689469596242181425994724346843927487006803126235170352282851333649398560048225978776992988961905424387108445616625450986845896318932116427501356436 : ℝ) / 92236696489391948942419040557454482229118905600651207047972707705435442052128491659143244013678330555016055026706831019047792326085454115098818518321734263910148738654524345947401238210483605327421) * v 5 + ((37651167737527288121726183944016730769654191527004860109944257251667042023215817033954403064380135030304771502446210969568570300100590269740509858900424071467332889600028882568322692257527196464311000 : ℝ) / 92236696489391948942419040557454482229118905600651207047972707705435442052128491659143244013678330555016055026706831019047792326085454115098818518321734263910148738654524345947401238210483605327421) * v 6 + ((24943319758911640370210135229713252663264897353393031854324255486672054860371362908581023578389292181602324501800351380594516725517087869088958867393642620515003012896465656752272403396575997034193762 : ℝ) / 92236696489391948942419040557454482229118905600651207047972707705435442052128491659143244013678330555016055026706831019047792326085454115098818518321734263910148738654524345947401238210483605327421) * v 7) ^ 2
    + ((40655118756919869093363418473542198662928991480727826850674451292318353911592419421202750456199223159916226316880985514855232095619584541626124805128352760563957022119597038108653036240570352948153023462105260156516689987329881028311 : ℝ) / 9223669648939194894241904055745448222911890560065120704797270770543544205212849165914324401367833055501605502670683101904779232608545411509881851832173426391014873865452434594740123821048360532742100000000000000000000000000000000000000000000) * ((1 : ℝ) * v 5 + ((202762034956009843076922855344421691474453588720336683096988300174277981586076541541309672127713507809726545545648686754348555180570344718125718772062296298401682007939703566708433210849533978400588525978910212947095026034612141841628 : ℝ) / 40655118756919869093363418473542198662928991480727826850674451292318353911592419421202750456199223159916226316880985514855232095619584541626124805128352760563957022119597038108653036240570352948153023462105260156516689987329881028311) * v 6 + ((132672813958959006345397121491433707151731317588046281723468161960565513794083354953965391264018692172094235896644708980576803516125420098311913648345087506653471134472116340949949540498046978334877925443999190904621211407012025468405 : ℝ) / 40655118756919869093363418473542198662928991480727826850674451292318353911592419421202750456199223159916226316880985514855232095619584541626124805128352760563957022119597038108653036240570352948153023462105260156516689987329881028311) * v 7) ^ 2
    + ((85978633901010264212019392195263235100069068041172896860043275640217574053045852279299615747282677633223980210378828935726564823582035273330630828292269836159235861164263753221752459931540458749212409707989419701755496830441906781124974056018227093291580713093 : ℝ) / 4065511875691986909336341847354219866292899148072782685067445129231835391159241942120275045619922315991622631688098551485523209561958454162612480512835276056395702211959703810865303624057035294815302346210526015651668998732988102831100000000000000000000000000000000000000000000) * ((1 : ℝ) * v 6 + ((-339473679394513128769467168357924970383852541601898212534093273068041008870663500783373385802920070521717873125721099696280218630636340203582873842121641257588237088079853925116334622603951348772054221547677210781989739936586365184885668056703268638454879750261 : ℝ) / 85978633901010264212019392195263235100069068041172896860043275640217574053045852279299615747282677633223980210378828935726564823582035273330630828292269836159235861164263753221752459931540458749212409707989419701755496830441906781124974056018227093291580713093) * v 7) ^ 2
    + ((9455925345332460208059709593203237876610797967123424250055566500627530929836287267261997383480694654087459903862972907456070978038866708195119344514450909590585187463317436190391215744727381262041640618479052136897785526781594336920457775286726902267690156313756023001279555121065341 : ℝ) / 4298931695050513210600969609763161755003453402058644843002163782010878702652292613964980787364133881661199010518941446786328241179101763666531541414613491807961793058213187661087622996577022937460620485399470985087774841522095339056248702800911354664579035654650000000000000000000000000000000000000000000) * ((1 : ℝ) * v 7) ^ 2 := by positivity
  linarith

theorem box_margin : (8 : ℝ) * w0 < δ := by norm_num [w0, δ]

/-- Every real `8 x 8` matrix in the Arb box around `Smat` is positive definite. -/
theorem core_posdef (G : Fin 8 → Fin 8 → ℝ) (hbox : ∀ i j, |G i j - Smat i j| ≤ w0)
    (v : Fin 8 → ℝ) (hv : v ≠ 0) : 0 < qf G v :=
  posdef_of_box G Smat w0 δ hbox Smat_ge box_margin v hv

/-- For every real symmetric block matrix `[[A, B], [Bᵀ, C]]` (`C` of any finite size) with `C` positive
definite and Schur complement in the Arb box, the block matrix is positive semidefinite.  With the block
matrix `= M - lam0 I` this is `lam_min(M) >= lam0`. -/
theorem core_schur {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix (Fin 8) (Fin 8) ℝ) (hA : A.IsHermitian) (B : Matrix (Fin 8) m ℝ)
    (C : Matrix m m ℝ) (hC : C.PosDef) (hbox : ∀ i j, |(A - B * C⁻¹ * Bᴴ) i j - Smat i j| ≤ w0) :
    (Matrix.fromBlocks A B Bᴴ C).PosSemidef :=
  schur_link Smat w0 δ Smat_ge box_margin A hA B C hC hbox

end Core_x6996_odd

namespace Core_x11006_even

/-!
### Certificate core `Core_x11006_even`
x = e^{307/128} = 11.006 (a = 307/256; prime powers 2, 3, 4, 5, 7, 8, 9, 11), EVEN sector.  M = leading 2300 x 2300 Legendre block of the window-aware reduction R'' (eps = 0.34, w = 66, Tc = 1170, Tk = 1698, Tmax = 2457), lam0 = 6.6018e-49.  Arb (matrix reloaded from the saved 70-digit file with radii inflated by 2% + 1e-69 relative): C - lam0 I >= 1e-55 I (verified Cholesky), Schur complement box.
The kernel checks only the exact rational part below; the Arb facts are the hypotheses `hbox`, `hC` of
`core_posdef` / `core_schur`.
-/

/-- Arb-computed Schur complement, rounded to rationals with denominator `10^60`. -/
def Sq : Fin 8 → Fin 8 → ℚ :=
  ![![((62797988687385136780851592818295665706565891203579 : ℚ) / 3125000000000000000000000000000000000000000000000000000000), ((2088239941130550181008894509996488567010272535567759 : ℚ) / 50000000000000000000000000000000000000000000000000000000000), ((9407223788551168188476073260481290260329753742848023 : ℚ) / 200000000000000000000000000000000000000000000000000000000000), ((21177366237029420904544478769319151414051715209681287 : ℚ) / 500000000000000000000000000000000000000000000000000000000000), ((31658626071406161884638189923873523473083248931270693 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000), ((19311980763439558475428685499870426638209405175062061 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000), ((463608415754022440175031137516011063315349628637791 : ℚ) / 50000000000000000000000000000000000000000000000000000000000), ((818489144401768949123622815848069075169141874501633 : ℚ) / 250000000000000000000000000000000000000000000000000000000000)],
    ![((2088239941130550181008894509996488567010272535567759 : ℚ) / 50000000000000000000000000000000000000000000000000000000000), ((2170027285061092384534026647081350969833550548125923 : ℚ) / 25000000000000000000000000000000000000000000000000000000000), ((48878349251631818389493310285528252299147222945832839 : ℚ) / 500000000000000000000000000000000000000000000000000000000000), ((8802729839889396062822506544435137812514000179889443 : ℚ) / 100000000000000000000000000000000000000000000000000000000000), ((6579728715428246170098039563179327645080451424912197 : ℚ) / 100000000000000000000000000000000000000000000000000000000000), ((20068427172070708472779230660115128303828231150298777 : ℚ) / 500000000000000000000000000000000000000000000000000000000000), ((9635373301025198383181266700291869845737429502802203 : ℚ) / 500000000000000000000000000000000000000000000000000000000000), ((17011047937536609248753553636356184410774571905193 : ℚ) / 2500000000000000000000000000000000000000000000000000000000)],
    ![((9407223788551168188476073260481290260329753742848023 : ℚ) / 200000000000000000000000000000000000000000000000000000000000), ((48878349251631818389493310285528252299147222945832839 : ℚ) / 500000000000000000000000000000000000000000000000000000000000), ((344047549751480903678845756442857060778011734008229 : ℚ) / 3125000000000000000000000000000000000000000000000000000000), ((49569002547653370000653673673873395480644867985505351 : ℚ) / 500000000000000000000000000000000000000000000000000000000000), ((14820467987564987577376526215368033465570763287161239 : ℚ) / 200000000000000000000000000000000000000000000000000000000000), ((11300785232729928363676010992453637740669548460080371 : ℚ) / 250000000000000000000000000000000000000000000000000000000000), ((10851642526283813368778317299653737262164866332578813 : ℚ) / 500000000000000000000000000000000000000000000000000000000000), ((3831687512559370854030997043729224765455736579027249 : ℚ) / 500000000000000000000000000000000000000000000000000000000000)],
    ![((21177366237029420904544478769319151414051715209681287 : ℚ) / 500000000000000000000000000000000000000000000000000000000000), ((8802729839889396062822506544435137812514000179889443 : ℚ) / 100000000000000000000000000000000000000000000000000000000000), ((49569002547653370000653673673873395480644867985505351 : ℚ) / 500000000000000000000000000000000000000000000000000000000000), ((44635791590675463550041636543086134772956824875190969 : ℚ) / 500000000000000000000000000000000000000000000000000000000000), ((66727783162513984799167403213583755259129934377765533 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000), ((40704781318400529055369687086041782096974331314650071 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000), ((3908722031485478739457690545438162585762390612957003 : ℚ) / 200000000000000000000000000000000000000000000000000000000000), ((6900849464093662448079268811431667703842982554452699 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000)],
    ![((31658626071406161884638189923873523473083248931270693 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000), ((6579728715428246170098039563179327645080451424912197 : ℚ) / 100000000000000000000000000000000000000000000000000000000000), ((14820467987564987577376526215368033465570763287161239 : ℚ) / 200000000000000000000000000000000000000000000000000000000000), ((66727783162513984799167403213583755259129934377765533 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000), ((49877233841680157328475065042142597842415597321438417 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000), ((15212959636685769741381131832954602071698809606101183 : ℚ) / 500000000000000000000000000000000000000000000000000000000000), ((7304261213131044265629313585794966184526823364797013 : ℚ) / 500000000000000000000000000000000000000000000000000000000000), ((515831801711984928398563115507783269026233163791279 : ℚ) / 100000000000000000000000000000000000000000000000000000000000)],
    ![((19311980763439558475428685499870426638209405175062061 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000), ((20068427172070708472779230660115128303828231150298777 : ℚ) / 500000000000000000000000000000000000000000000000000000000000), ((11300785232729928363676010992453637740669548460080371 : ℚ) / 250000000000000000000000000000000000000000000000000000000000), ((40704781318400529055369687086041782096974331314650071 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000), ((15212959636685769741381131832954602071698809606101183 : ℚ) / 500000000000000000000000000000000000000000000000000000000000), ((928021799058242165970263967860408285284310880638497 : ℚ) / 50000000000000000000000000000000000000000000000000000000000), ((8911577402008423552000010337020061229665189539038157 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000), ((1573371349215392177847621374055727667008694426191363 : ℚ) / 500000000000000000000000000000000000000000000000000000000000)],
    ![((463608415754022440175031137516011063315349628637791 : ℚ) / 50000000000000000000000000000000000000000000000000000000000), ((9635373301025198383181266700291869845737429502802203 : ℚ) / 500000000000000000000000000000000000000000000000000000000000), ((10851642526283813368778317299653737262164866332578813 : ℚ) / 500000000000000000000000000000000000000000000000000000000000), ((3908722031485478739457690545438162585762390612957003 : ℚ) / 200000000000000000000000000000000000000000000000000000000000), ((7304261213131044265629313585794966184526823364797013 : ℚ) / 500000000000000000000000000000000000000000000000000000000000), ((8911577402008423552000010337020061229665189539038157 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000), ((4278836522255619822344616050301975711810338998694939 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000), ((302181775713034916259493020961975812533808945847251 : ℚ) / 200000000000000000000000000000000000000000000000000000000000)],
    ![((818489144401768949123622815848069075169141874501633 : ℚ) / 250000000000000000000000000000000000000000000000000000000000), ((17011047937536609248753553636356184410774571905193 : ℚ) / 2500000000000000000000000000000000000000000000000000000000), ((3831687512559370854030997043729224765455736579027249 : ℚ) / 500000000000000000000000000000000000000000000000000000000000), ((6900849464093662448079268811431667703842982554452699 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000), ((515831801711984928398563115507783269026233163791279 : ℚ) / 100000000000000000000000000000000000000000000000000000000000), ((1573371349215392177847621374055727667008694426191363 : ℚ) / 500000000000000000000000000000000000000000000000000000000000), ((302181775713034916259493020961975812533808945847251 : ℚ) / 200000000000000000000000000000000000000000000000000000000000), ((53352937078654708752168410296081285629185834902947 : ℚ) / 100000000000000000000000000000000000000000000000000000000000)]]

/-- `Sq` as a real matrix. -/
noncomputable def Smat : Fin 8 → Fin 8 → ℝ := fun i j => (Sq i j : ℝ)

/-- entrywise half-width covering the Arb ball radius of the Schur complement and the rounding. -/
noncomputable def w0 : ℝ := ((1992046558788915560449 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000)

/-- exact lower bound for the form of `Smat`. -/
noncomputable def δ : ℝ := ((267276471 : ℝ) / 50000000000000000000000000000000000000000000000000000000000)

/-- EXACT rational congruence `Sq - δ I = L D Lᵀ`, written as a sum of squares (closed by `ring`). -/
theorem Sq_ldl (v : Fin 8 → ℝ) :
    qf Smat v - δ * ∑ i, v i ^ 2 =
    ((1004767818998162188493625485092730651305053991980793 : ℝ) / 50000000000000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 0 + ((2088239941130550181008894509996488567010272535567759 : ℝ) / 1004767818998162188493625485092730651305053991980793) * v 1 + ((9407223788551168188476073260481290260329753742848023 : ℝ) / 4019071275992648753974501940370922605220215967923172) * v 2 + ((21177366237029420904544478769319151414051715209681287 : ℝ) / 10047678189981621884936254850927306513050539919807930) * v 3 + ((31658626071406161884638189923873523473083248931270693 : ℝ) / 20095356379963243769872509701854613026101079839615860) * v 4 + ((19311980763439558475428685499870426638209405175062061 : ℝ) / 20095356379963243769872509701854613026101079839615860) * v 5 + ((463608415754022440175031137516011063315349628637791 : ℝ) / 1004767818998162188493625485092730651305053991980793) * v 6 + ((818489144401768949123622815848069075169141874501633 : ℝ) / 5023839094990810942468127425463653256525269959903965) * v 7) ^ 2
    + ((556510875133056056493500130751621040417465736864503371579707096011300248754949844767052194845147 : ℝ) / 25119195474954054712340637127318266282626349799519825000000000000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 1 + ((82495555096814241662119399274310541454432471983982080603138650605930683992012995606324875574870369 : ℝ) / 22260435005322242259740005230064841616698629474580134863188283840452009950197993790682087793805880) * v 2 + ((2934160158873265559162792040444658669930061408954036312522898699116632383763374782553325792865987 : ℝ) / 428085288563889274225769331347400800321127489895771824292082381547154037503807572897732457573190) * v 3 + ((189266376877896696450052930356891629208118431406273629025147278463448652933276246013019935281935223 : ℝ) / 22260435005322242259740005230064841616698629474580134863188283840452009950197993790682087793805880) * v 4 + ((170028250541827112504582250463079451343026191071988219307122932838297557479610529457340145295089023 : ℝ) / 22260435005322242259740005230064841616698629474580134863188283840452009950197993790682087793805880) * v 5 + ((56908686136507813354691877804625653816372528288098732988063301111093397824857647708401324568283289 : ℝ) / 11130217502661121129870002615032420808349314737290067431594141920226004975098996895341043896902940) * v 6 + ((13630785640024220012087910672336563983287649760037587195492214525774496931892638890843712468154453 : ℝ) / 5565108751330560564935001307516210404174657368645033715797070960113002487549498447670521948451470) * v 7) ^ 2
    + ((3499752714540199673897071745373434658632969400655395858849905962864088126976305142906256932218161960629880825415302531049414721514998041473 : ℝ) / 22260435005322242259740005230064841616698629474580134863188283840452009950197993790682087793805880000000000000000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 2 + ((16153901720907364062652030156857379852197160577267029989924309552855594152949127874901470866356910091452591755126585280937472976803439348888 : ℝ) / 3499752714540199673897071745373434658632969400655395858849905962864088126976305142906256932218161960629880825415302531049414721514998041473) * v 3 + ((35449996433212063425743597729514600600477636261744740785411254526721169303826162350517521400487440633214950759265435867766091742165071991231 : ℝ) / 3499752714540199673897071745373434658632969400655395858849905962864088126976305142906256932218161960629880825415302531049414721514998041473) * v 4 + ((49041320124154760192496426826138598466358846187362352532233229827760833061868309340380798722215174818948913264171238381902786150214301578591 : ℝ) / 3499752714540199673897071745373434658632969400655395858849905962864088126976305142906256932218161960629880825415302531049414721514998041473) * v 5 + ((48324424105620702274849071558584878294595979723049262842288507348534867006042851053921288147843492320462833264299314020050792971650325661206 : ℝ) / 3499752714540199673897071745373434658632969400655395858849905962864088126976305142906256932218161960629880825415302531049414721514998041473) * v 6 + ((32360422040094037548581096924114524651554678089391270293753649076413744374141052828460828883422947741863007065153047367791259381188735201204 : ℝ) / 3499752714540199673897071745373434658632969400655395858849905962864088126976305142906256932218161960629880825415302531049414721514998041473) * v 7) ^ 2
    + ((20375609954145050539344574333030137426621165809997972752205086075585134681141957653619680173896220536659803807824509992413239142536218183450039084081980309160581691763341802231 : ℝ) / 17498763572700998369485358726867173293164847003276979294249529814320440634881525714531284661090809803149404127076512655247073607574990207365000000000000000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 3 + ((106306778468725583184088918947051067880579411933348560147301007341299768797586438017351282358774884613252159115425646482268875447123215777640047534140007645507717803956125592807 : ℝ) / 20375609954145050539344574333030137426621165809997972752205086075585134681141957653619680173896220536659803807824509992413239142536218183450039084081980309160581691763341802231) * v 4 + ((268907055713717875369406676919471444123836956445326036629711157622280946041684340387113682380097162020617662838258876835165517043366839457981047286209570070717195660517799140409 : ℝ) / 20375609954145050539344574333030137426621165809997972752205086075585134681141957653619680173896220536659803807824509992413239142536218183450039084081980309160581691763341802231) * v 5 + ((147481752818801692141850659864738549237482248056103961844054217749550365516732567746826444099228829486869713831495021559553111374179300020448948009197131399617014495919673897770 : ℝ) / 6791869984715016846448191444343379142207055269999324250735028691861711560380652551206560057965406845553267935941503330804413047512072727816679694693993436386860563921113934077) * v 6 + ((427039921576139036428596821415894948680336628185003784396719706432390008837905488707271985058484517032256011624660323537915607770374655109847712335561749314683999634572254946003 : ℝ) / 20375609954145050539344574333030137426621165809997972752205086075585134681141957653619680173896220536659803807824509992413239142536218183450039084081980309160581691763341802231) * v 7) ^ 2
    + ((132041163595418310419111784848004346327052656851616281891886017040610448904647655085074252952475494801791070888734873064880566277150493165795612634402657520458965236338623071396609045808154443860901116175453 : ℝ) / 5093902488536262634836143583257534356655291452499493188051271518896283670285489413404920043474055134164950951956127498103309785634054545862509771020495077290145422940835450557750000000000000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 4 + ((854005759028707002333009145126750567523095070659058358576503677718332379828949678918178712004709306515490752594243022545384487751806148789041644493395864790784755088809291399160853047872939659330057010345217 : ℝ) / 132041163595418310419111784848004346327052656851616281891886017040610448904647655085074252952475494801791070888734873064880566277150493165795612634402657520458965236338623071396609045808154443860901116175453) * v 5 + ((2481035138319807413828629561411176591172656063114989755752148203899421166837881569631969841349490526147377055277913206422149010531572176642117188021872298055794942045132215765953381446557727970048943013874901 : ℝ) / 132041163595418310419111784848004346327052656851616281891886017040610448904647655085074252952475494801791070888734873064880566277150493165795612634402657520458965236338623071396609045808154443860901116175453) * v 6 + ((12937048120899479110356175861785734525966509908796610138628671921978053747241358349684055672960360253812754178211408522506342678780345223260791904593033392073796836783005187524198310203602838097770429364509251 : ℝ) / 528164654381673241676447139392017385308210627406465127567544068162441795618590620340297011809901979207164283554939492259522265108601972663182450537610630081835860945354492285586436183232617775443604464701812) * v 7) ^ 2
    + ((184622489939423918140909297680873039698058549100272624279426461965792835461937404375882154560366100033748609215817561885189516737941072133666419939877449738974319030418947837145341546747101257373909094919979643838613528963317214790921 : ℝ) / 132041163595418310419111784848004346327052656851616281891886017040610448904647655085074252952475494801791070888734873064880566277150493165795612634402657520458965236338623071396609045808154443860901116175453000000000000000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 5 + ((993816237723746138277803852039384265820090680414808126212726569299573947279042720920770539307270160943343459306184738870962210775377859064310975218964135504642998524745233369712977460236450445762668568575781470000516411435151952032493 : ℝ) / 184622489939423918140909297680873039698058549100272624279426461965792835461937404375882154560366100033748609215817561885189516737941072133666419939877449738974319030418947837145341546747101257373909094919979643838613528963317214790921) * v 6 + ((1676776385728148474486134792800681819014134793365086596583992297714199528018342199737850781632572618050117212736045610172055468845268597996573504782149548213198764229860149331212087345370990732181982143931632806007555413196067822382014 : ℝ) / 184622489939423918140909297680873039698058549100272624279426461965792835461937404375882154560366100033748609215817561885189516737941072133666419939877449738974319030418947837145341546747101257373909094919979643838613528963317214790921) * v 7) ^ 2
    + ((812423374818082639145408768414557175831507605743084049119007496341622075077666338788933094936308804373552521454209252051722987644879459677403093134336843970160941724209847334314062063932252498970190971431254219288883331661130254559494707212781462380244679 : ℝ) / 184622489939423918140909297680873039698058549100272624279426461965792835461937404375882154560366100033748609215817561885189516737941072133666419939877449738974319030418947837145341546747101257373909094919979643838613528963317214790921000000000000000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 6 + ((2380996603313742932111485265038851133600094364298052167278361890350207111108632299964411980174620494007325996711230778418691196937272071789203640638639282733741364282494551228761679991529700366794396472915559075493610099415098366314774301719398639051715710 : ℝ) / 812423374818082639145408768414557175831507605743084049119007496341622075077666338788933094936308804373552521454209252051722987644879459677403093134336843970160941724209847334314062063932252498970190971431254219288883331661130254559494707212781462380244679) * v 7) ^ 2
    + ((116640426599988040940460806199060490964246312071497749476807336693090606342105065363074074648264505179698268206744088154505081508983763430097151612675616539869885341904246169408820955063528600798257542362512700503802581503829981280453725857180135640210150364308641314583 : ℝ) / 3249693499272330556581635073658228703326030422972336196476029985366488300310665355155732379745235217494210085816837008206891950579517838709612372537347375880643766896839389337256248255729009995880763885725016877155533326644521018237978828851125849520978716000000000000000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 7) ^ 2 := by
  simp only [qf, Smat, Sq, δ, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ]
  push_cast
  ring

theorem Smat_ge (v : Fin 8 → ℝ) : δ * ∑ i, v i ^ 2 ≤ qf Smat v := by
  have h := Sq_ldl v
  have hp : 0 ≤
    ((1004767818998162188493625485092730651305053991980793 : ℝ) / 50000000000000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 0 + ((2088239941130550181008894509996488567010272535567759 : ℝ) / 1004767818998162188493625485092730651305053991980793) * v 1 + ((9407223788551168188476073260481290260329753742848023 : ℝ) / 4019071275992648753974501940370922605220215967923172) * v 2 + ((21177366237029420904544478769319151414051715209681287 : ℝ) / 10047678189981621884936254850927306513050539919807930) * v 3 + ((31658626071406161884638189923873523473083248931270693 : ℝ) / 20095356379963243769872509701854613026101079839615860) * v 4 + ((19311980763439558475428685499870426638209405175062061 : ℝ) / 20095356379963243769872509701854613026101079839615860) * v 5 + ((463608415754022440175031137516011063315349628637791 : ℝ) / 1004767818998162188493625485092730651305053991980793) * v 6 + ((818489144401768949123622815848069075169141874501633 : ℝ) / 5023839094990810942468127425463653256525269959903965) * v 7) ^ 2
    + ((556510875133056056493500130751621040417465736864503371579707096011300248754949844767052194845147 : ℝ) / 25119195474954054712340637127318266282626349799519825000000000000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 1 + ((82495555096814241662119399274310541454432471983982080603138650605930683992012995606324875574870369 : ℝ) / 22260435005322242259740005230064841616698629474580134863188283840452009950197993790682087793805880) * v 2 + ((2934160158873265559162792040444658669930061408954036312522898699116632383763374782553325792865987 : ℝ) / 428085288563889274225769331347400800321127489895771824292082381547154037503807572897732457573190) * v 3 + ((189266376877896696450052930356891629208118431406273629025147278463448652933276246013019935281935223 : ℝ) / 22260435005322242259740005230064841616698629474580134863188283840452009950197993790682087793805880) * v 4 + ((170028250541827112504582250463079451343026191071988219307122932838297557479610529457340145295089023 : ℝ) / 22260435005322242259740005230064841616698629474580134863188283840452009950197993790682087793805880) * v 5 + ((56908686136507813354691877804625653816372528288098732988063301111093397824857647708401324568283289 : ℝ) / 11130217502661121129870002615032420808349314737290067431594141920226004975098996895341043896902940) * v 6 + ((13630785640024220012087910672336563983287649760037587195492214525774496931892638890843712468154453 : ℝ) / 5565108751330560564935001307516210404174657368645033715797070960113002487549498447670521948451470) * v 7) ^ 2
    + ((3499752714540199673897071745373434658632969400655395858849905962864088126976305142906256932218161960629880825415302531049414721514998041473 : ℝ) / 22260435005322242259740005230064841616698629474580134863188283840452009950197993790682087793805880000000000000000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 2 + ((16153901720907364062652030156857379852197160577267029989924309552855594152949127874901470866356910091452591755126585280937472976803439348888 : ℝ) / 3499752714540199673897071745373434658632969400655395858849905962864088126976305142906256932218161960629880825415302531049414721514998041473) * v 3 + ((35449996433212063425743597729514600600477636261744740785411254526721169303826162350517521400487440633214950759265435867766091742165071991231 : ℝ) / 3499752714540199673897071745373434658632969400655395858849905962864088126976305142906256932218161960629880825415302531049414721514998041473) * v 4 + ((49041320124154760192496426826138598466358846187362352532233229827760833061868309340380798722215174818948913264171238381902786150214301578591 : ℝ) / 3499752714540199673897071745373434658632969400655395858849905962864088126976305142906256932218161960629880825415302531049414721514998041473) * v 5 + ((48324424105620702274849071558584878294595979723049262842288507348534867006042851053921288147843492320462833264299314020050792971650325661206 : ℝ) / 3499752714540199673897071745373434658632969400655395858849905962864088126976305142906256932218161960629880825415302531049414721514998041473) * v 6 + ((32360422040094037548581096924114524651554678089391270293753649076413744374141052828460828883422947741863007065153047367791259381188735201204 : ℝ) / 3499752714540199673897071745373434658632969400655395858849905962864088126976305142906256932218161960629880825415302531049414721514998041473) * v 7) ^ 2
    + ((20375609954145050539344574333030137426621165809997972752205086075585134681141957653619680173896220536659803807824509992413239142536218183450039084081980309160581691763341802231 : ℝ) / 17498763572700998369485358726867173293164847003276979294249529814320440634881525714531284661090809803149404127076512655247073607574990207365000000000000000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 3 + ((106306778468725583184088918947051067880579411933348560147301007341299768797586438017351282358774884613252159115425646482268875447123215777640047534140007645507717803956125592807 : ℝ) / 20375609954145050539344574333030137426621165809997972752205086075585134681141957653619680173896220536659803807824509992413239142536218183450039084081980309160581691763341802231) * v 4 + ((268907055713717875369406676919471444123836956445326036629711157622280946041684340387113682380097162020617662838258876835165517043366839457981047286209570070717195660517799140409 : ℝ) / 20375609954145050539344574333030137426621165809997972752205086075585134681141957653619680173896220536659803807824509992413239142536218183450039084081980309160581691763341802231) * v 5 + ((147481752818801692141850659864738549237482248056103961844054217749550365516732567746826444099228829486869713831495021559553111374179300020448948009197131399617014495919673897770 : ℝ) / 6791869984715016846448191444343379142207055269999324250735028691861711560380652551206560057965406845553267935941503330804413047512072727816679694693993436386860563921113934077) * v 6 + ((427039921576139036428596821415894948680336628185003784396719706432390008837905488707271985058484517032256011624660323537915607770374655109847712335561749314683999634572254946003 : ℝ) / 20375609954145050539344574333030137426621165809997972752205086075585134681141957653619680173896220536659803807824509992413239142536218183450039084081980309160581691763341802231) * v 7) ^ 2
    + ((132041163595418310419111784848004346327052656851616281891886017040610448904647655085074252952475494801791070888734873064880566277150493165795612634402657520458965236338623071396609045808154443860901116175453 : ℝ) / 5093902488536262634836143583257534356655291452499493188051271518896283670285489413404920043474055134164950951956127498103309785634054545862509771020495077290145422940835450557750000000000000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 4 + ((854005759028707002333009145126750567523095070659058358576503677718332379828949678918178712004709306515490752594243022545384487751806148789041644493395864790784755088809291399160853047872939659330057010345217 : ℝ) / 132041163595418310419111784848004346327052656851616281891886017040610448904647655085074252952475494801791070888734873064880566277150493165795612634402657520458965236338623071396609045808154443860901116175453) * v 5 + ((2481035138319807413828629561411176591172656063114989755752148203899421166837881569631969841349490526147377055277913206422149010531572176642117188021872298055794942045132215765953381446557727970048943013874901 : ℝ) / 132041163595418310419111784848004346327052656851616281891886017040610448904647655085074252952475494801791070888734873064880566277150493165795612634402657520458965236338623071396609045808154443860901116175453) * v 6 + ((12937048120899479110356175861785734525966509908796610138628671921978053747241358349684055672960360253812754178211408522506342678780345223260791904593033392073796836783005187524198310203602838097770429364509251 : ℝ) / 528164654381673241676447139392017385308210627406465127567544068162441795618590620340297011809901979207164283554939492259522265108601972663182450537610630081835860945354492285586436183232617775443604464701812) * v 7) ^ 2
    + ((184622489939423918140909297680873039698058549100272624279426461965792835461937404375882154560366100033748609215817561885189516737941072133666419939877449738974319030418947837145341546747101257373909094919979643838613528963317214790921 : ℝ) / 132041163595418310419111784848004346327052656851616281891886017040610448904647655085074252952475494801791070888734873064880566277150493165795612634402657520458965236338623071396609045808154443860901116175453000000000000000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 5 + ((993816237723746138277803852039384265820090680414808126212726569299573947279042720920770539307270160943343459306184738870962210775377859064310975218964135504642998524745233369712977460236450445762668568575781470000516411435151952032493 : ℝ) / 184622489939423918140909297680873039698058549100272624279426461965792835461937404375882154560366100033748609215817561885189516737941072133666419939877449738974319030418947837145341546747101257373909094919979643838613528963317214790921) * v 6 + ((1676776385728148474486134792800681819014134793365086596583992297714199528018342199737850781632572618050117212736045610172055468845268597996573504782149548213198764229860149331212087345370990732181982143931632806007555413196067822382014 : ℝ) / 184622489939423918140909297680873039698058549100272624279426461965792835461937404375882154560366100033748609215817561885189516737941072133666419939877449738974319030418947837145341546747101257373909094919979643838613528963317214790921) * v 7) ^ 2
    + ((812423374818082639145408768414557175831507605743084049119007496341622075077666338788933094936308804373552521454209252051722987644879459677403093134336843970160941724209847334314062063932252498970190971431254219288883331661130254559494707212781462380244679 : ℝ) / 184622489939423918140909297680873039698058549100272624279426461965792835461937404375882154560366100033748609215817561885189516737941072133666419939877449738974319030418947837145341546747101257373909094919979643838613528963317214790921000000000000000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 6 + ((2380996603313742932111485265038851133600094364298052167278361890350207111108632299964411980174620494007325996711230778418691196937272071789203640638639282733741364282494551228761679991529700366794396472915559075493610099415098366314774301719398639051715710 : ℝ) / 812423374818082639145408768414557175831507605743084049119007496341622075077666338788933094936308804373552521454209252051722987644879459677403093134336843970160941724209847334314062063932252498970190971431254219288883331661130254559494707212781462380244679) * v 7) ^ 2
    + ((116640426599988040940460806199060490964246312071497749476807336693090606342105065363074074648264505179698268206744088154505081508983763430097151612675616539869885341904246169408820955063528600798257542362512700503802581503829981280453725857180135640210150364308641314583 : ℝ) / 3249693499272330556581635073658228703326030422972336196476029985366488300310665355155732379745235217494210085816837008206891950579517838709612372537347375880643766896839389337256248255729009995880763885725016877155533326644521018237978828851125849520978716000000000000000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 7) ^ 2 := by positivity
  linarith

theorem box_margin : (8 : ℝ) * w0 < δ := by norm_num [w0, δ]

/-- Every real `8 x 8` matrix in the Arb box around `Smat` is positive definite. -/
theorem core_posdef (G : Fin 8 → Fin 8 → ℝ) (hbox : ∀ i j, |G i j - Smat i j| ≤ w0)
    (v : Fin 8 → ℝ) (hv : v ≠ 0) : 0 < qf G v :=
  posdef_of_box G Smat w0 δ hbox Smat_ge box_margin v hv

/-- For every real symmetric block matrix `[[A, B], [Bᵀ, C]]` (`C` of any finite size) with `C` positive
definite and Schur complement in the Arb box, the block matrix is positive semidefinite.  With the block
matrix `= M - lam0 I` this is `lam_min(M) >= lam0`. -/
theorem core_schur {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix (Fin 8) (Fin 8) ℝ) (hA : A.IsHermitian) (B : Matrix (Fin 8) m ℝ)
    (C : Matrix m m ℝ) (hC : C.PosDef) (hbox : ∀ i j, |(A - B * C⁻¹ * Bᴴ) i j - Smat i j| ≤ w0) :
    (Matrix.fromBlocks A B Bᴴ C).PosSemidef :=
  schur_link Smat w0 δ Smat_ge box_margin A hA B C hC hbox

end Core_x11006_even

namespace Core_x11006_odd

/-!
### Certificate core `Core_x11006_odd`
x = 11.006, ODD sector.  M = leading 2300 x 2300 Legendre block of R'' (Tc = 2000, Tk = 2528, Tmax = 3287), lam0 = 4.4579e-45.  Arb: C - lam0 I >= 1e-55 I (verified Cholesky), Schur complement box.
The kernel checks only the exact rational part below; the Arb facts are the hypotheses `hbox`, `hC` of
`core_posdef` / `core_schur`.
-/

/-- Arb-computed Schur complement, rounded to rationals with denominator `10^60`. -/
def Sq : Fin 8 → Fin 8 → ℚ :=
  ![![((2158143429021554166860617344235696753526958454052432817 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000), ((7463324065480324657648592365918441671135828594858123 : ℚ) / 2500000000000000000000000000000000000000000000000000000000), ((1557527060817740013996712926255297295071904389514160341 : ℚ) / 500000000000000000000000000000000000000000000000000000000000), ((1376067609607759527164682735762180027691619838396139309 : ℚ) / 500000000000000000000000000000000000000000000000000000000000), ((518595050395513309286723829922488649762164400220192551 : ℚ) / 250000000000000000000000000000000000000000000000000000000000), ((1279508694753775847382399644702384520848900798590463631 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000), ((621095446452132075748290616154321775876902106167046023 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000), ((140383493714806044534783975920494577652775239950629553 : ℚ) / 500000000000000000000000000000000000000000000000000000000000)],
    ![((7463324065480324657648592365918441671135828594858123 : ℚ) / 2500000000000000000000000000000000000000000000000000000000), ((165182807663642541704968291734989804934815880127944803 : ℚ) / 40000000000000000000000000000000000000000000000000000000000), ((1077256659860361754089889432817205565780536946013933647 : ℚ) / 250000000000000000000000000000000000000000000000000000000000), ((3807016603495560742439915340913915650472905139962617081 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000), ((1434746107933330576889981113995812627520344123413991073 : ℚ) / 500000000000000000000000000000000000000000000000000000000000), ((442488201724407446546087452160710060994080400400680529 : ℚ) / 250000000000000000000000000000000000000000000000000000000000), ((107396177145214252215061734927240056571811824515484607 : ℚ) / 125000000000000000000000000000000000000000000000000000000000), ((388391533017947696547322315201908667790816602935716333 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000)],
    ![((1557527060817740013996712926255297295071904389514160341 : ℚ) / 500000000000000000000000000000000000000000000000000000000000), ((1077256659860361754089889432817205565780536946013933647 : ℚ) / 250000000000000000000000000000000000000000000000000000000000), ((4496300399601665057674863368831700562818978276769320543 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000), ((794499135864305719097595273615182780419698691604588031 : ℚ) / 200000000000000000000000000000000000000000000000000000000000), ((748560182865150972965038451687636507945480742470350071 : ℚ) / 250000000000000000000000000000000000000000000000000000000000), ((230864138240949947030966225189264948673606610857804437 : ℚ) / 125000000000000000000000000000000000000000000000000000000000), ((896534841152307393214335547077514627709705749693078589 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000), ((405288128616292909270216311961320902356579512896991733 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000)],
    ![((1376067609607759527164682735762180027691619838396139309 : ℚ) / 500000000000000000000000000000000000000000000000000000000000), ((3807016603495560742439915340913915650472905139962617081 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000), ((794499135864305719097595273615182780419698691604588031 : ℚ) / 200000000000000000000000000000000000000000000000000000000000), ((1754870454841084258762229348059517497504899527675212591 : ℚ) / 500000000000000000000000000000000000000000000000000000000000), ((1322733999460835528335864290534938999909565807890837281 : ℚ) / 500000000000000000000000000000000000000000000000000000000000), ((326359747842690062890912093356941239991925456818265201 : ℚ) / 200000000000000000000000000000000000000000000000000000000000), ((99015299083759918756546752216973159395099334767324219 : ℚ) / 125000000000000000000000000000000000000000000000000000000000), ((17904699203078553691569185289751259928966156857377147 : ℚ) / 50000000000000000000000000000000000000000000000000000000000)],
    ![((518595050395513309286723829922488649762164400220192551 : ℚ) / 250000000000000000000000000000000000000000000000000000000000), ((1434746107933330576889981113995812627520344123413991073 : ℚ) / 500000000000000000000000000000000000000000000000000000000000), ((748560182865150972965038451687636507945480742470350071 : ℚ) / 250000000000000000000000000000000000000000000000000000000000), ((1322733999460835528335864290534938999909565807890837281 : ℚ) / 500000000000000000000000000000000000000000000000000000000000), ((398808978351478340188501744016182364732877717345981691 : ℚ) / 200000000000000000000000000000000000000000000000000000000000), ((1229997315584665807008850949217010142970043422837035327 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000), ((119416899080475309884055844050795019918244134124152061 : ℚ) / 200000000000000000000000000000000000000000000000000000000000), ((269929325808533255268511115513765796698722221725164121 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000)],
    ![((1279508694753775847382399644702384520848900798590463631 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000), ((442488201724407446546087452160710060994080400400680529 : ℚ) / 250000000000000000000000000000000000000000000000000000000000), ((230864138240949947030966225189264948673606610857804437 : ℚ) / 125000000000000000000000000000000000000000000000000000000000), ((326359747842690062890912093356941239991925456818265201 : ℚ) / 200000000000000000000000000000000000000000000000000000000000), ((1229997315584665807008850949217010142970043422837035327 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000), ((379357562218129781181298356780009717822253311595413657 : ℚ) / 500000000000000000000000000000000000000000000000000000000000), ((73662511839595948892314998210213178885857047473820113 : ℚ) / 200000000000000000000000000000000000000000000000000000000000), ((166510147410819269689385649247324190036147955040936229 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000)],
    ![((621095446452132075748290616154321775876902106167046023 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000), ((107396177145214252215061734927240056571811824515484607 : ℚ) / 125000000000000000000000000000000000000000000000000000000000), ((896534841152307393214335547077514627709705749693078589 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000), ((99015299083759918756546752216973159395099334767324219 : ℚ) / 125000000000000000000000000000000000000000000000000000000000), ((119416899080475309884055844050795019918244134124152061 : ℚ) / 200000000000000000000000000000000000000000000000000000000000), ((73662511839595948892314998210213178885857047473820113 : ℚ) / 200000000000000000000000000000000000000000000000000000000000), ((89398742420060472325192764886940353078543086412398493 : ℚ) / 500000000000000000000000000000000000000000000000000000000000), ((20208635644945385551345556553769258747406019060219361 : ℚ) / 250000000000000000000000000000000000000000000000000000000000)],
    ![((140383493714806044534783975920494577652775239950629553 : ℚ) / 500000000000000000000000000000000000000000000000000000000000), ((388391533017947696547322315201908667790816602935716333 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000), ((405288128616292909270216311961320902356579512896991733 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000), ((17904699203078553691569185289751259928966156857377147 : ℚ) / 50000000000000000000000000000000000000000000000000000000000), ((269929325808533255268511115513765796698722221725164121 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000), ((166510147410819269689385649247324190036147955040936229 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000), ((20208635644945385551345556553769258747406019060219361 : ℚ) / 250000000000000000000000000000000000000000000000000000000000), ((18273465085264773449267114780849824662419229217988393 : ℚ) / 500000000000000000000000000000000000000000000000000000000000)]]

/-- `Sq` as a real matrix. -/
noncomputable def Smat : Fin 8 → Fin 8 → ℝ := fun i j => (Sq i j : ℝ)

/-- entrywise half-width covering the Arb ball radius of the Schur complement and the rounding. -/
noncomputable def w0 : ℝ := ((45951445639421504717 : ℝ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000)

/-- exact lower bound for the form of `Smat`. -/
noncomputable def δ : ℝ := ((875811540203 : ℝ) / 20000000000000000000000000000000000000000000000000000000000)

/-- EXACT rational congruence `Sq - δ I = L D Lᵀ`, written as a sum of squares (closed by `ring`). -/
theorem Sq_ldl (v : Fin 8 → ℝ) :
    qf Smat v - δ * ∑ i, v i ^ 2 =
    ((2158143429021554166860617344235696753526914663475422667 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 0 + ((2985329626192129863059436946367376668454331437943249200 : ℝ) / 2158143429021554166860617344235696753526914663475422667) * v 1 + ((3115054121635480027993425852510594590143808779028320682 : ℝ) / 2158143429021554166860617344235696753526914663475422667) * v 2 + ((2752135219215519054329365471524360055383239676792278618 : ℝ) / 2158143429021554166860617344235696753526914663475422667) * v 3 + ((2074380201582053237146895319689954599048657600880770204 : ℝ) / 2158143429021554166860617344235696753526914663475422667) * v 4 + ((1279508694753775847382399644702384520848900798590463631 : ℝ) / 2158143429021554166860617344235696753526914663475422667) * v 5 + ((621095446452132075748290616154321775876902106167046023 : ℝ) / 2158143429021554166860617344235696753526914663475422667) * v 6 + ((280766987429612089069567951840989155305550479901259106 : ℝ) / 2158143429021554166860617344235696753526914663475422667) * v 7) ^ 2
    + ((471865803698564393823653944275990984506855418868550522624518356909099577773491584884774619770963061199 : ℝ) / 86325737160862166674424693769427870141076586539016906680000000000000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 1 + ((34170879087565688758228820821341121292275381126940110276189503755001482083767480548682996060963831151796 : ℝ) / 11796645092464109845591348606899774612671385471713763065612958922727489444337289622119365494274076529975) * v 2 + ((57061799039043434059274851243916715773142690848721426093764802207380185309704156143740149304957343169427 : ℝ) / 11796645092464109845591348606899774612671385471713763065612958922727489444337289622119365494274076529975) * v 3 + ((67098531827840398819204416938716224437569224279822253984214498880417135814425498298061697311421772866582 : ℝ) / 11796645092464109845591348606899774612671385471713763065612958922727489444337289622119365494274076529975) * v 4 + ((56806465505814003384991413806104618775524972125736312337436137172032797980590227638009200180836278758172 : ℝ) / 11796645092464109845591348606899774612671385471713763065612958922727489444337289622119365494274076529975) * v 5 + ((36195077254159029780275554710689311094931491661930481426022581739354231362738425736329103934646701163352 : ℝ) / 11796645092464109845591348606899774612671385471713763065612958922727489444337289622119365494274076529975) * v 6 + ((22629239957534245615450557591858523807401431328590591434912514913905843707019652217837277075014863104911 : ℝ) / 11796645092464109845591348606899774612671385471713763065612958922727489444337289622119365494274076529975) * v 7) ^ 2
    + ((787729747450034612941969113885202714650500629856818047287512871203852435654082415043780062463477612484807310150888694792831559903328684308117041627 : ℝ) / 11796645092464109845591348606899774612671385471713763065612958922727489444337289622119365494274076529975000000000000000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 2 + ((3027753063733555992061048594004008854147436945880995012968566943160451116919714350475961527446447754483894665991427785989745108835812055400188662149 : ℝ) / 787729747450034612941969113885202714650500629856818047287512871203852435654082415043780062463477612484807310150888694792831559903328684308117041627) * v 3 + ((5729229844034514634489765211197723748994659231404684404973188896684196302767592288475903857177539780235477665302399182792243867378278723186762771684 : ℝ) / 787729747450034612941969113885202714650500629856818047287512871203852435654082415043780062463477612484807310150888694792831559903328684308117041627) * v 4 + ((6613965734247425057808353933201565850650960949881977504950095959987015231662433808281616949132285016469149800606074146935681586292527670353299555514 : ℝ) / 787729747450034612941969113885202714650500629856818047287512871203852435654082415043780062463477612484807310150888694792831559903328684308117041627) * v 5 + ((5802543027561998332646180823771895746965161957705240049718027766462441420073605387090819024080120998147167329620323696644800992827036494895761769149 : ℝ) / 787729747450034612941969113885202714650500629856818047287512871203852435654082415043780062463477612484807310150888694792831559903328684308117041627) * v 6 + ((5412574460170618008902602598397166871671501363132562957841881258094733461240283707333356706285660909362432824416825544194041260384397416271478702107 : ℝ) / 787729747450034612941969113885202714650500629856818047287512871203852435654082415043780062463477612484807310150888694792831559903328684308117041627) * v 7) ^ 2
    + ((181255558122250927668419897635250491706780099357388997754085142281330415437242059281852158366632344982521630312961673917912417913240930334224094144486756801909480280920050068060549764211 : ℝ) / 393864873725017306470984556942601357325250314928409023643756435601926217827041207521890031231738806242403655075444347396415779951664342154058520813500000000000000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 3 + ((650600292271708832159306862224931879910600044980349372551703384105831549323586373101264755922013330553512264586181942394489273100613979239188650069855844902728039981176210238307403055346 : ℝ) / 181255558122250927668419897635250491706780099357388997754085142281330415437242059281852158366632344982521630312961673917912417913240930334224094144486756801909480280920050068060549764211) * v 4 + ((2173760044697910215209259667534670166673282685865053850231022208910059562300375856863484787418228702230699447974221080258316307025537798459296013221079881532098427330608154309299249761207 : ℝ) / 362511116244501855336839795270500983413560198714777995508170284562660830874484118563704316733264689965043260625923347835824835826481860668448188288973513603818960561840100136121099528422) * v 5 + ((3828680071418613574656151364756896682790055121886210957172812107452727319952086760287538076733361680558022573849601093754194558969130318477253219492371348977346168979835136766991892220451 : ℝ) / 362511116244501855336839795270500983413560198714777995508170284562660830874484118563704316733264689965043260625923347835824835826481860668448188288973513603818960561840100136121099528422) * v 6 + ((3454935672653314204061130506267071722252135460115514468054697137309842709490009390795135660466686074021783111582560607215449196795228402594813851039494753963273845494863686291989357984282 : ℝ) / 181255558122250927668419897635250491706780099357388997754085142281330415437242059281852158366632344982521630312961673917912417913240930334224094144486756801909480280920050068060549764211) * v 7) ^ 2
    + ((135570582315097276854533394333641855957151592653744048164563923518731651718574914567191082710237081035752804229915140266757814358390739464455908065770413931929355778330641242854162579081664105414026247013945079122439859 : ℝ) / 36251111624450185533683979527050098341356019871477799550817028456266083087448411856370431673326468996504326062592334783582483582648186066844818828897351360381896056184010013612109952842200000000000000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 4 + ((1771863784383479943039086834215164479200298690292493051609036198312080390713224369061489675438164434875272492808220878048057522642383731658005933066346564366890780186013826887510271999697677872920828074622062335982665343 : ℝ) / 677852911575486384272666971668209279785757963268720240822819617593658258592874572835955413551185405178764021149575701333789071791953697322279540328852069659646778891653206214270812895408320527070131235069725395612199295) * v 5 + ((-164409287776330781382367241737096088199645861849644676374383968935663900208228428464245373360791703893465343764097506883824790222315877145162926443185342470361260530547043905590627640226207942812151979059965640459705423 : ℝ) / 13833732889295640495360550442208352648688938025892249812710604440686903236589276996652151296962967452627837166317871455791613710039871373924072251609225911421362834523534820699404344804251439327961861940198477461473455) * v 6 + ((-129390421229433524724924345610830312989261052591409421978100871641551190339420071845928679456822931392042923786374797647596371326377936226762695069768586601920800382173125798121915279717185055773081053843434655193122403 : ℝ) / 2766746577859128099072110088441670529737787605178449962542120888137380647317855399330430259392593490525567433263574291158322742007974274784814450321845182284272566904706964139880868960850287865592372388039695492294691) * v 7) ^ 2
    + ((451908963293081376493471421077373690449659003248517595123899635043426006184700871767811328985273263363702260785485668935765141170666628543725705652203763047811369626146787554370780300693251448084722157118877978927830460856812190175604068791637970417 : ℝ) / 1355705823150972768545333943336418559571515926537440481645639235187316517185749145671910827102370810357528042299151402667578143583907394644559080657704139319293557783306412428541625790816641054140262470139450791224398590000000000000000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 5 + ((6699155366953439013161149541161021542888855573378464704109436199638685123542047096414073638557030644725139553899880812557518347570070170992413934461252254288126602497507295811451731317848216343506875916230111650750607204245054612764922930984360753627 : ℝ) / 451908963293081376493471421077373690449659003248517595123899635043426006184700871767811328985273263363702260785485668935765141170666628543725705652203763047811369626146787554370780300693251448084722157118877978927830460856812190175604068791637970417) * v 6 + ((19173909010230068203992503046975042139575728786494394216357203941030451983119494589599235457729467204092585048386801790161723076032695847669401846366668333767718397887407939407718518978141122504091884165831742155998823578739265750569693880817000153440 : ℝ) / 451908963293081376493471421077373690449659003248517595123899635043426006184700871767811328985273263363702260785485668935765141170666628543725705652203763047811369626146787554370780300693251448084722157118877978927830460856812190175604068791637970417) * v 7) ^ 2
    + ((61338569409856667481612836571735952040723945520209916939830543980637218292218385896080617713267558008179075518855208902169480860538862311234388535514386900676598878897611376106154710334565073395940744232261373466710852367616101382032784389876422322491047000097914832977123903 : ℝ) / 451908963293081376493471421077373690449659003248517595123899635043426006184700871767811328985273263363702260785485668935765141170666628543725705652203763047811369626146787554370780300693251448084722157118877978927830460856812190175604068791637970417000000000000000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 6 + ((207476815337056026290580205630610532351177552546037028580378454695585939877255663836503193808901056240960753061028599618167110257710519119504751000918250845579388341384636005714285269667549181550004200997752700691669377990603307228492630987712297888115318259876882016254982308 : ℝ) / 61338569409856667481612836571735952040723945520209916939830543980637218292218385896080617713267558008179075518855208902169480860538862311234388535514386900676598878897611376106154710334565073395940744232261373466710852367616101382032784389876422322491047000097914832977123903) * v 7) ^ 2
    + ((4853206098686579949335117997849694212758682121173371173035143351114259724228711769434390730861317888757757397401545886203013302982575204978311882516905709078551811339155612288033912503575590908283027557797967867361060641956530404827424236241554439849555316460092117544425157988003807261333871 : ℝ) / 61338569409856667481612836571735952040723945520209916939830543980637218292218385896080617713267558008179075518855208902169480860538862311234388535514386900676598878897611376106154710334565073395940744232261373466710852367616101382032784389876422322491047000097914832977123903000000000000000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 7) ^ 2 := by
  simp only [qf, Smat, Sq, δ, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ]
  push_cast
  ring

theorem Smat_ge (v : Fin 8 → ℝ) : δ * ∑ i, v i ^ 2 ≤ qf Smat v := by
  have h := Sq_ldl v
  have hp : 0 ≤
    ((2158143429021554166860617344235696753526914663475422667 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 0 + ((2985329626192129863059436946367376668454331437943249200 : ℝ) / 2158143429021554166860617344235696753526914663475422667) * v 1 + ((3115054121635480027993425852510594590143808779028320682 : ℝ) / 2158143429021554166860617344235696753526914663475422667) * v 2 + ((2752135219215519054329365471524360055383239676792278618 : ℝ) / 2158143429021554166860617344235696753526914663475422667) * v 3 + ((2074380201582053237146895319689954599048657600880770204 : ℝ) / 2158143429021554166860617344235696753526914663475422667) * v 4 + ((1279508694753775847382399644702384520848900798590463631 : ℝ) / 2158143429021554166860617344235696753526914663475422667) * v 5 + ((621095446452132075748290616154321775876902106167046023 : ℝ) / 2158143429021554166860617344235696753526914663475422667) * v 6 + ((280766987429612089069567951840989155305550479901259106 : ℝ) / 2158143429021554166860617344235696753526914663475422667) * v 7) ^ 2
    + ((471865803698564393823653944275990984506855418868550522624518356909099577773491584884774619770963061199 : ℝ) / 86325737160862166674424693769427870141076586539016906680000000000000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 1 + ((34170879087565688758228820821341121292275381126940110276189503755001482083767480548682996060963831151796 : ℝ) / 11796645092464109845591348606899774612671385471713763065612958922727489444337289622119365494274076529975) * v 2 + ((57061799039043434059274851243916715773142690848721426093764802207380185309704156143740149304957343169427 : ℝ) / 11796645092464109845591348606899774612671385471713763065612958922727489444337289622119365494274076529975) * v 3 + ((67098531827840398819204416938716224437569224279822253984214498880417135814425498298061697311421772866582 : ℝ) / 11796645092464109845591348606899774612671385471713763065612958922727489444337289622119365494274076529975) * v 4 + ((56806465505814003384991413806104618775524972125736312337436137172032797980590227638009200180836278758172 : ℝ) / 11796645092464109845591348606899774612671385471713763065612958922727489444337289622119365494274076529975) * v 5 + ((36195077254159029780275554710689311094931491661930481426022581739354231362738425736329103934646701163352 : ℝ) / 11796645092464109845591348606899774612671385471713763065612958922727489444337289622119365494274076529975) * v 6 + ((22629239957534245615450557591858523807401431328590591434912514913905843707019652217837277075014863104911 : ℝ) / 11796645092464109845591348606899774612671385471713763065612958922727489444337289622119365494274076529975) * v 7) ^ 2
    + ((787729747450034612941969113885202714650500629856818047287512871203852435654082415043780062463477612484807310150888694792831559903328684308117041627 : ℝ) / 11796645092464109845591348606899774612671385471713763065612958922727489444337289622119365494274076529975000000000000000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 2 + ((3027753063733555992061048594004008854147436945880995012968566943160451116919714350475961527446447754483894665991427785989745108835812055400188662149 : ℝ) / 787729747450034612941969113885202714650500629856818047287512871203852435654082415043780062463477612484807310150888694792831559903328684308117041627) * v 3 + ((5729229844034514634489765211197723748994659231404684404973188896684196302767592288475903857177539780235477665302399182792243867378278723186762771684 : ℝ) / 787729747450034612941969113885202714650500629856818047287512871203852435654082415043780062463477612484807310150888694792831559903328684308117041627) * v 4 + ((6613965734247425057808353933201565850650960949881977504950095959987015231662433808281616949132285016469149800606074146935681586292527670353299555514 : ℝ) / 787729747450034612941969113885202714650500629856818047287512871203852435654082415043780062463477612484807310150888694792831559903328684308117041627) * v 5 + ((5802543027561998332646180823771895746965161957705240049718027766462441420073605387090819024080120998147167329620323696644800992827036494895761769149 : ℝ) / 787729747450034612941969113885202714650500629856818047287512871203852435654082415043780062463477612484807310150888694792831559903328684308117041627) * v 6 + ((5412574460170618008902602598397166871671501363132562957841881258094733461240283707333356706285660909362432824416825544194041260384397416271478702107 : ℝ) / 787729747450034612941969113885202714650500629856818047287512871203852435654082415043780062463477612484807310150888694792831559903328684308117041627) * v 7) ^ 2
    + ((181255558122250927668419897635250491706780099357388997754085142281330415437242059281852158366632344982521630312961673917912417913240930334224094144486756801909480280920050068060549764211 : ℝ) / 393864873725017306470984556942601357325250314928409023643756435601926217827041207521890031231738806242403655075444347396415779951664342154058520813500000000000000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 3 + ((650600292271708832159306862224931879910600044980349372551703384105831549323586373101264755922013330553512264586181942394489273100613979239188650069855844902728039981176210238307403055346 : ℝ) / 181255558122250927668419897635250491706780099357388997754085142281330415437242059281852158366632344982521630312961673917912417913240930334224094144486756801909480280920050068060549764211) * v 4 + ((2173760044697910215209259667534670166673282685865053850231022208910059562300375856863484787418228702230699447974221080258316307025537798459296013221079881532098427330608154309299249761207 : ℝ) / 362511116244501855336839795270500983413560198714777995508170284562660830874484118563704316733264689965043260625923347835824835826481860668448188288973513603818960561840100136121099528422) * v 5 + ((3828680071418613574656151364756896682790055121886210957172812107452727319952086760287538076733361680558022573849601093754194558969130318477253219492371348977346168979835136766991892220451 : ℝ) / 362511116244501855336839795270500983413560198714777995508170284562660830874484118563704316733264689965043260625923347835824835826481860668448188288973513603818960561840100136121099528422) * v 6 + ((3454935672653314204061130506267071722252135460115514468054697137309842709490009390795135660466686074021783111582560607215449196795228402594813851039494753963273845494863686291989357984282 : ℝ) / 181255558122250927668419897635250491706780099357388997754085142281330415437242059281852158366632344982521630312961673917912417913240930334224094144486756801909480280920050068060549764211) * v 7) ^ 2
    + ((135570582315097276854533394333641855957151592653744048164563923518731651718574914567191082710237081035752804229915140266757814358390739464455908065770413931929355778330641242854162579081664105414026247013945079122439859 : ℝ) / 36251111624450185533683979527050098341356019871477799550817028456266083087448411856370431673326468996504326062592334783582483582648186066844818828897351360381896056184010013612109952842200000000000000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 4 + ((1771863784383479943039086834215164479200298690292493051609036198312080390713224369061489675438164434875272492808220878048057522642383731658005933066346564366890780186013826887510271999697677872920828074622062335982665343 : ℝ) / 677852911575486384272666971668209279785757963268720240822819617593658258592874572835955413551185405178764021149575701333789071791953697322279540328852069659646778891653206214270812895408320527070131235069725395612199295) * v 5 + ((-164409287776330781382367241737096088199645861849644676374383968935663900208228428464245373360791703893465343764097506883824790222315877145162926443185342470361260530547043905590627640226207942812151979059965640459705423 : ℝ) / 13833732889295640495360550442208352648688938025892249812710604440686903236589276996652151296962967452627837166317871455791613710039871373924072251609225911421362834523534820699404344804251439327961861940198477461473455) * v 6 + ((-129390421229433524724924345610830312989261052591409421978100871641551190339420071845928679456822931392042923786374797647596371326377936226762695069768586601920800382173125798121915279717185055773081053843434655193122403 : ℝ) / 2766746577859128099072110088441670529737787605178449962542120888137380647317855399330430259392593490525567433263574291158322742007974274784814450321845182284272566904706964139880868960850287865592372388039695492294691) * v 7) ^ 2
    + ((451908963293081376493471421077373690449659003248517595123899635043426006184700871767811328985273263363702260785485668935765141170666628543725705652203763047811369626146787554370780300693251448084722157118877978927830460856812190175604068791637970417 : ℝ) / 1355705823150972768545333943336418559571515926537440481645639235187316517185749145671910827102370810357528042299151402667578143583907394644559080657704139319293557783306412428541625790816641054140262470139450791224398590000000000000000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 5 + ((6699155366953439013161149541161021542888855573378464704109436199638685123542047096414073638557030644725139553899880812557518347570070170992413934461252254288126602497507295811451731317848216343506875916230111650750607204245054612764922930984360753627 : ℝ) / 451908963293081376493471421077373690449659003248517595123899635043426006184700871767811328985273263363702260785485668935765141170666628543725705652203763047811369626146787554370780300693251448084722157118877978927830460856812190175604068791637970417) * v 6 + ((19173909010230068203992503046975042139575728786494394216357203941030451983119494589599235457729467204092585048386801790161723076032695847669401846366668333767718397887407939407718518978141122504091884165831742155998823578739265750569693880817000153440 : ℝ) / 451908963293081376493471421077373690449659003248517595123899635043426006184700871767811328985273263363702260785485668935765141170666628543725705652203763047811369626146787554370780300693251448084722157118877978927830460856812190175604068791637970417) * v 7) ^ 2
    + ((61338569409856667481612836571735952040723945520209916939830543980637218292218385896080617713267558008179075518855208902169480860538862311234388535514386900676598878897611376106154710334565073395940744232261373466710852367616101382032784389876422322491047000097914832977123903 : ℝ) / 451908963293081376493471421077373690449659003248517595123899635043426006184700871767811328985273263363702260785485668935765141170666628543725705652203763047811369626146787554370780300693251448084722157118877978927830460856812190175604068791637970417000000000000000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 6 + ((207476815337056026290580205630610532351177552546037028580378454695585939877255663836503193808901056240960753061028599618167110257710519119504751000918250845579388341384636005714285269667549181550004200997752700691669377990603307228492630987712297888115318259876882016254982308 : ℝ) / 61338569409856667481612836571735952040723945520209916939830543980637218292218385896080617713267558008179075518855208902169480860538862311234388535514386900676598878897611376106154710334565073395940744232261373466710852367616101382032784389876422322491047000097914832977123903) * v 7) ^ 2
    + ((4853206098686579949335117997849694212758682121173371173035143351114259724228711769434390730861317888757757397401545886203013302982575204978311882516905709078551811339155612288033912503575590908283027557797967867361060641956530404827424236241554439849555316460092117544425157988003807261333871 : ℝ) / 61338569409856667481612836571735952040723945520209916939830543980637218292218385896080617713267558008179075518855208902169480860538862311234388535514386900676598878897611376106154710334565073395940744232261373466710852367616101382032784389876422322491047000097914832977123903000000000000000000000000000000000000000000000000000000000000) * ((1 : ℝ) * v 7) ^ 2 := by positivity
  linarith

theorem box_margin : (8 : ℝ) * w0 < δ := by norm_num [w0, δ]

/-- Every real `8 x 8` matrix in the Arb box around `Smat` is positive definite. -/
theorem core_posdef (G : Fin 8 → Fin 8 → ℝ) (hbox : ∀ i j, |G i j - Smat i j| ≤ w0)
    (v : Fin 8 → ℝ) (hv : v ≠ 0) : 0 < qf G v :=
  posdef_of_box G Smat w0 δ hbox Smat_ge box_margin v hv

/-- For every real symmetric block matrix `[[A, B], [Bᵀ, C]]` (`C` of any finite size) with `C` positive
definite and Schur complement in the Arb box, the block matrix is positive semidefinite.  With the block
matrix `= M - lam0 I` this is `lam_min(M) >= lam0`. -/
theorem core_schur {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix (Fin 8) (Fin 8) ℝ) (hA : A.IsHermitian) (B : Matrix (Fin 8) m ℝ)
    (C : Matrix m m ℝ) (hC : C.PosDef) (hbox : ∀ i j, |(A - B * C⁻¹ * Bᴴ) i j - Smat i j| ≤ w0) :
    (Matrix.fromBlocks A B Bᴴ C).PosSemidef :=
  schur_link Smat w0 δ Smat_ge box_margin A hA B C hC hbox

end Core_x11006_odd

end Crux2KappaCertify

#print axioms Crux2KappaCertify.block_assembly
#print axioms Crux2KappaCertify.schur_link
#print axioms Crux2KappaCertify.posdef_of_box
#print axioms Crux2KappaCertify.PathGraph.path_quad_le
#print axioms Crux2KappaCertify.SchurTest.schur_test
#print axioms Crux2KappaCertify.LemmaA.W_rec
#print axioms Crux2KappaCertify.LemmaA.shift_bound
#print axioms Crux2KappaCertify.LemmaA.shift_bound_signed
#print axioms Crux2KappaCertify.LemmaA.comb_bound
#print axioms Crux2KappaCertify.LemmaA.prime_comb_bound
#print axioms Crux2KappaCertify.Core_x6996_even.Sq_ldl
#print axioms Crux2KappaCertify.Core_x6996_even.core_posdef
#print axioms Crux2KappaCertify.Core_x6996_even.core_schur
#print axioms Crux2KappaCertify.Core_x6996_odd.Sq_ldl
#print axioms Crux2KappaCertify.Core_x6996_odd.core_posdef
#print axioms Crux2KappaCertify.Core_x6996_odd.core_schur
#print axioms Crux2KappaCertify.Core_x11006_even.Sq_ldl
#print axioms Crux2KappaCertify.Core_x11006_even.core_posdef
#print axioms Crux2KappaCertify.Core_x11006_even.core_schur
#print axioms Crux2KappaCertify.Core_x11006_odd.Sq_ldl
#print axioms Crux2KappaCertify.Core_x11006_odd.core_posdef
#print axioms Crux2KappaCertify.Core_x11006_odd.core_schur
