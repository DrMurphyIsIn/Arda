/- HAND-AUTHORED (not telperion-generated): discharge of the SumEqProd target --
   the general-k identity  gSum n k = gProd n k  (alternating sum = product
   form), upgrading the knapsack certificate to UNIFORM DEGREE.

   Route (the W2 creative-telescoping proof, made elementary):
     1. gSum n k = 2^k * (-1)^k * (forward difference)^[k] (f n) (k)
        via mathlib's `fwdDiff_iter_eq_sum_shift` (Newton expansion) plus a
        sum reflection -- no hand-rolled Pascal induction needed;
     2. the iterated difference has hypergeometric closed form
          Delta^[j] (f n) q = (-1)^j * pnum(j) * f n q / pden(q, j),
        pnum(j) = prod_{u<j} (n/2 - u),  pden(q,j) = prod_{u<j} (n - q - u),
        by a ONE-STEP telescoping induction (the contiguous relation);
     3. at q = j = k the closed form telescopes against f(k) to gProd n k
        by a second product induction.

   Result: `sumEqProd_general` -- for every k and every rational n > 2k,
   gSum n k = gProd n k -- and with it `sumEqProd_holds : SumEqProd`.
   Combined with KnapsackSOS.gProd_pos this yields the uniform-in-degree
   scalar certificate: for every d and every odd n >= 2d+1 all block scalars
   of the degree-2d moment matrix are positive. -/
import Mathlib
import KnapsackSOS

namespace KnapsackSOS

/-! ### Auxiliary products -/

/-- pnum(j) = prod_{u<j} (n/2 - u): the q-independent numerator product. -/
def pnum (n : ℚ) : ℕ → ℚ
  | 0 => 1
  | j + 1 => pnum n j * (n / 2 - j)

/-- pden(q, j) = prod_{u<j} (n - q - u): the shifting denominator product. -/
def pden (n : ℚ) (q : ℕ) : ℕ → ℚ
  | 0 => 1
  | j + 1 => pden n q j * (n - q - j)

theorem pden_pos (n : ℚ) (q j : ℕ) (h : (q : ℚ) + j < n + 1) : 0 < pden n q j := by
  induction j with
  | zero => norm_num [pden]
  | succ j ih =>
    have h' : (q : ℚ) + j < n + 1 := by push_cast at h ⊢; linarith
    have hf : (0 : ℚ) < n - q - j := by push_cast at h; linarith
    rw [pden]
    exact mul_pos (ih h') hf

/-- Shift law: pden(q, j+1) = (n-q) * pden(q+1, j). -/
theorem pden_shift (n : ℚ) (q j : ℕ) :
    pden n q (j + 1) = (n - q) * pden n (q + 1) j := by
  induction j with
  | zero => norm_num [pden]
  | succ j ih =>
    conv_lhs => rw [pden]
    rw [ih]
    conv_rhs => rw [pden]
    push_cast
    ring

/-! ### The telescoping closed form for iterated forward differences -/

/-- The contiguous-relation induction: the j-th forward difference of the
pseudo-moment sequence is hypergeometric with explicit numerator and
denominator products. This is the W2 creative-telescoping step. -/
theorem fwdDiff_iter_f (n : ℚ) (j : ℕ) :
    ∀ q : ℕ, (q : ℚ) + j < n →
      (fwdDiff 1)^[j] (f n) q = (-1) ^ j * pnum n j * f n q / pden n q j := by
  induction j with
  | zero =>
    intro q _
    norm_num [pnum, pden]
  | succ j ih =>
    intro q hq
    have hq1 : ((q + 1 : ℕ) : ℚ) + j < n := by push_cast at hq ⊢; linarith
    have hq0 : (q : ℚ) + j < n := by push_cast at hq ⊢; linarith
    have hjn : (0 : ℚ) ≤ (j : ℚ) := Nat.cast_nonneg j
    have hnq : (0 : ℚ) < n - q := by push_cast at hq; linarith
    have hnqj : (0 : ℚ) < n - q - j := by push_cast at hq; linarith
    have hB : (0 : ℚ) < pden n q j :=
      pden_pos n q j (by push_cast at hq ⊢; linarith)
    have hA : (0 : ℚ) < pden n (q + 1) j :=
      pden_pos n (q + 1) j (by push_cast at hq ⊢; linarith)
    have hd : pden n q (j + 1) = pden n q j * (n - q - j) := by rw [pden]
    have hArel : pden n (q + 1) j = pden n q j * (n - q - j) / (n - q) := by
      rw [eq_div_iff (ne_of_gt hnq)]
      linear_combination hd - pden_shift n q j
    rw [Function.iterate_succ_apply']
    have hstep : fwdDiff 1 ((fwdDiff 1)^[j] (f n)) q
        = (fwdDiff 1)^[j] (f n) (q + 1) - (fwdDiff 1)^[j] (f n) q := rfl
    rw [hstep, ih (q + 1) hq1, ih q hq0]
    have hf1 : f n (q + 1) = f n q * (n / 2 - q) / (n - q) := by rw [f]
    have hpn : pnum n (j + 1) = pnum n j * (n / 2 - j) := by rw [pnum]
    rw [hf1, hpn, hd, hArel, pow_succ]
    field_simp
    ring

/-! ### gSum as an iterated forward difference -/

theorem gSum_eq_fwdDiff (n : ℚ) (k : ℕ) :
    gSum n k = 2 ^ k * ((-1) ^ k * (fwdDiff 1)^[k] (f n) k) := by
  rw [gSum, fwdDiff_iter_eq_sum_shift]
  congr 1
  rw [Finset.mul_sum]
  conv_lhs => rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hu' : u ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hu)
  have e1 : k + 1 - 1 - u = k - u := by omega
  rw [e1]
  have e2 : k - (k - u) = u := by omega
  have e3 : 2 * k - (k - u) = k + u := by omega
  rw [e2, e3, Nat.choose_symm hu']
  simp only [smul_eq_mul, mul_one, zsmul_eq_mul]
  push_cast
  have key : ((-1 : ℚ)) ^ k = (-1) ^ u * (-1) ^ (k - u) := by
    rw [← pow_add, Nat.add_sub_cancel' hu']
  rw [key]
  have hsq : ((-1 : ℚ)) ^ (k - u) * (-1) ^ (k - u) = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨k - u, rfl⟩
  linear_combination (-(-1 : ℚ) ^ u * (k.choose u : ℚ) * f n (k + u)) * hsq

/-! ### The product induction closing the assembly -/

theorem prod_form (n : ℚ) (k : ℕ) (hn : (2 * k : ℚ) < n) :
    2 ^ k * pnum n k * f n k / pden n k k = gProd n k := by
  induction k with
  | zero => norm_num [pnum, pden, f, gProd]
  | succ k ih =>
    have hn' : (2 * k : ℚ) < n := by push_cast at hn ⊢; linarith
    have hkn : (0 : ℚ) ≤ (k : ℚ) := Nat.cast_nonneg k
    have h2k : (0 : ℚ) < n - 2 * k := by push_cast at hn; linarith
    have h2k1 : (0 : ℚ) < n - 2 * k - 1 := by push_cast at hn; linarith
    have hnk : (0 : ℚ) < n - k := by push_cast at hn; linarith
    have hB : (0 : ℚ) < pden n k k :=
      pden_pos n k k (by push_cast at hn ⊢; linarith)
    have hshift := pden_shift n k k
    have hd1 : pden n k (k + 1) = pden n k k * (n - k - k) := by rw [pden]
    have hd2 : pden n (k + 1) (k + 1)
        = pden n (k + 1) k * (n - ((k : ℚ) + 1) - k) := by
      rw [pden]; push_cast; ring
    have hval : pden n (k + 1) (k + 1)
        = pden n k k * (n - 2 * k) * (n - 2 * k - 1) / (n - k) := by
      rw [eq_div_iff (ne_of_gt hnk), hd2]
      linear_combination (n - 2 * (k : ℚ) - 1) * hd1
        - (n - 2 * (k : ℚ) - 1) * hshift
    have hf1 : f n (k + 1) = f n k * (n / 2 - k) / (n - k) := by rw [f]
    have hpn : pnum n (k + 1) = pnum n k * (n / 2 - k) := by rw [pnum]
    have hgp : gProd n (k + 1)
        = gProd n k * (n - 2 * k) / (2 * (n - (2 * k + 1))) := by rw [gProd]
    have h2k1' : n - (2 * (k : ℚ) + 1) ≠ 0 := by
      intro hz; push_cast at hn; nlinarith [h2k1]
    rw [pow_succ, hf1, hpn, hgp, hval, ← ih hn']
    field_simp
    ring

/-! ### The discharge -/

/-- General-k sum = product: the former open W2 target, now a theorem.
For every k and every rational n > 2k (in particular every odd n >= 2k+1),
the alternating-sum block scalar equals the product form. -/
theorem sumEqProd_general (n : ℚ) (k : ℕ) (hn : (2 * k : ℚ) < n) :
    gSum n k = gProd n k := by
  have hkk : (k : ℚ) + k < n := by linarith
  rw [gSum_eq_fwdDiff, fwdDiff_iter_f n k k hkk]
  have hsq : ((-1 : ℚ)) ^ k * (-1) ^ k = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨k, rfl⟩
  have collapse : (-1 : ℚ) ^ k * ((-1) ^ k * pnum n k * f n k / pden n k k)
      = pnum n k * f n k / pden n k k := by
    have hre : (-1 : ℚ) ^ k * ((-1) ^ k * pnum n k * f n k / pden n k k)
        = ((-1) ^ k * (-1) ^ k) * (pnum n k * f n k / pden n k k) := by ring
    rw [hre, hsq, one_mul]
  rw [collapse, ← prod_form n k hn]
  ring

/-- Uniform-in-degree scalar certificate: for every block level k and every
rational n > 2k, the alternating-sum scalar (the object the Gram formula
produces) is positive. Grigoriev's lower bound, all degrees at once. -/
theorem gSum_pos (n : ℚ) (k : ℕ) (hn : (2 * k : ℚ) < n) : 0 < gSum n k := by
  rw [sumEqProd_general n k hn]
  exact gProd_pos n k (by linarith)

/-- The named target from KnapsackSOS.lean, discharged. -/
theorem sumEqProd_holds : SumEqProd := fun n k hn => sumEqProd_general n k hn

end KnapsackSOS

#print axioms KnapsackSOS.sumEqProd_holds
#print axioms KnapsackSOS.fwdDiff_iter_f
#print axioms KnapsackSOS.gSum_eq_fwdDiff
#print axioms KnapsackSOS.prod_form
#print axioms KnapsackSOS.sumEqProd_general
#print axioms KnapsackSOS.gSum_pos
