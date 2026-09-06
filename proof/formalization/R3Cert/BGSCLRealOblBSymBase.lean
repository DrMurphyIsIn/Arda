/-
  RealObligationB — Case B: the SYMMETRIC-STAR base case (Aobj-NEUTRAL, parametric in k).

  The Case-B straightening move relocates one `k`-star onto a leaf of the sibling `k`-star,
  collapsing the two-child root to a SINGLE child.  In the exact cavity model
  (`R47Tree` / `R47RootRate`) this move is Aobj-NEUTRAL: `dAobj = 0` EXACTLY, with the
  closed form `Aobj = (4k+2)/(k+1)` on both sides, for every `k`.  (Verified exactly in
  `telperion/scratch/a3_symbase.py` for k=2..12, and — a strictly stronger fact — the
  ASYMMETRIC analogue `node[j-star, k-star]` is *also* exactly neutral for all j≠k in
  2..8: see the sibling report.)

  The `k`-star is `kstar k = node (replicate k (node []))` (root degree `k`, subtree
  degree `k+1`).  Its exact cavity values:

      Ztot (dtSub (kstar k)) = (2k+1)/(k+1),   Zopen (dtSub (kstar k)) = 1,   udeg = k+1.

  BEFORE:  `node [kstar k, kstar k]`  (root degree 2)
  AFTER:   `afterB k = node [ node (replicate (k-1) (node []) ++ [node [kstar k]]) ]`
           (root collapsed to a single child; one leaf of the first star replaced by a
           stem `node [kstar k]` carrying the relocated sibling star).

  Using the root-degree factorization `Aobj (node cs) = P(cs)·(1 + qSum(cs)/|cs|)`
  (`Aobj_factor`, from `Ztot_node_deg`), both sides evaluate to `(4k+2)/(k+1)`, hence the
  neutrality `Aobj (node [kstar k, kstar k]) = Aobj (afterB k)`.

  Kernel-checked, no `sorry`, axiom-clean.  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47Tree
import R3Cert.R47Head
import R3Cert.R47RootRate
import R3Cert.BGSCLRealOblACaseAIdentity

namespace R3Cert
namespace Step3

open RTree

/-! ### Cavity of a replicated-leaf block

    `dtChildren d (replicate n leaf)`: every child is a leaf (`Ztot=Zopen=1`), realized at
    edge weight `1/(d·1)`.  The leave-one-out matched sum is `n/d`; the open product is `1`. -/

/-- `Popen (dtChildren d (replicate n leaf)) = 1` — a product of `n` leaf totals (`=1`). -/
theorem Popen_dtChildren_replicate_leaf (d n : ℕ) :
    Popen (dtChildren d (List.replicate n flpLeaf)) = 1 := by
  induction n with
  | zero => rw [List.replicate_zero, dtChildren_nil, Popen]
  | succ m ih =>
    rw [List.replicate_succ, dtChildren_cons, Popen_cons, ih, Ztot_dtSub_flpLeaf]; ring

/-- `Matched (dtChildren d (replicate n leaf)) = n/d` — the leave-one-out matched sum of
    `n` leaves each attached with weight `1/(d·1)`. -/
theorem Matched_dtChildren_replicate_leaf (d n : ℕ) :
    Matched (dtChildren d (List.replicate n flpLeaf)) = (n : ℝ) / (d : ℝ) := by
  induction n with
  | zero => rw [List.replicate_zero, dtChildren_nil, Matched]; norm_num
  | succ m ih =>
    rw [List.replicate_succ, dtChildren_cons, Matched_cons, ih,
      Popen_dtChildren_replicate_leaf, Zopen_dtSub_flpLeaf, Ztot_dtSub_flpLeaf, udeg_flpLeaf]
    push_cast
    ring

/-- `qSum (replicate n leaf) = n` — each leaf child contributes `Zopen/Ztot/udeg = 1/1/1`. -/
theorem qSum_replicate_leaf (n : ℕ) : qSum (List.replicate n flpLeaf) = (n : ℝ) := by
  induction n with
  | zero => rw [List.replicate_zero, qSum]; simp
  | succ m ih =>
    rw [List.replicate_succ, qSum_cons, ih, Zopen_dtSub_flpLeaf, Ztot_dtSub_flpLeaf,
      udeg_flpLeaf]
    push_cast
    ring

/-! ### The k-star -/

/-- The `k`-star: a root carrying `k` bare leaves. -/
def kstar (k : ℕ) : UTree := UTree.node (List.replicate k flpLeaf)

theorem udeg_kstar (k : ℕ) : udeg (kstar k) = k + 1 := by
  rw [kstar, udeg_node, List.length_replicate]

/-- `Zopen (dtSub (kstar k)) = 1` (the open product over `k` leaves). -/
theorem Zopen_dtSub_kstar (k : ℕ) : Zopen (dtSub (kstar k)) = 1 := by
  rw [kstar, dtSub_node, List.length_replicate, Zopen, Popen_dtChildren_replicate_leaf]

/-- `Ztot (dtSub (kstar k)) = (2k+1)/(k+1)`: realized at subtree degree `k+1`, the matched
    sum is `k/(k+1)`, so `Ztot = 1 + k/(k+1) = (2k+1)/(k+1)`. -/
theorem Ztot_dtSub_kstar (k : ℕ) :
    Ztot (dtSub (kstar k)) = (2 * (k : ℝ) + 1) / ((k : ℝ) + 1) := by
  rw [kstar, dtSub_node, List.length_replicate, Ztot, Popen_dtChildren_replicate_leaf,
    Matched_dtChildren_replicate_leaf]
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-! ### The stem `node [kstar k]` -/

/-- The stem carrying a relocated `k`-star: `node [kstar k]` (subtree degree 2). -/
def stemK (k : ℕ) : UTree := UTree.node [kstar k]

theorem udeg_stemK (k : ℕ) : udeg (stemK k) = 2 := by
  rw [stemK, udeg_node, List.length_cons, List.length_nil]

/-- `Zopen (dtSub (stemK k)) = (2k+1)/(k+1) = Ztot(dtSub (kstar k))` (open product = the
    single child's total). -/
theorem Zopen_dtSub_stemK (k : ℕ) :
    Zopen (dtSub (stemK k)) = (2 * (k : ℝ) + 1) / ((k : ℝ) + 1) := by
  rw [stemK, dtSub_node]
  simp only [List.length_cons, List.length_nil, dtChildren_cons, dtChildren_nil]
  rw [Zopen, Popen_cons, Popen, Ztot_dtSub_kstar]; ring

/-- `Ztot (dtSub (stemK k)) = (4k+3)/(2(k+1))`: subtree degree 2, single `k`-star child
    (`Ztot=(2k+1)/(k+1)`, `Zopen=1`, `udeg=k+1`) with edge weight `1/(2·(k+1))`. -/
theorem Ztot_dtSub_stemK (k : ℕ) :
    Ztot (dtSub (stemK k)) = (4 * (k : ℝ) + 3) / (2 * ((k : ℝ) + 1)) := by
  rw [stemK, dtSub_node]
  simp only [List.length_cons, List.length_nil, dtChildren_cons, dtChildren_nil]
  rw [Ztot, Matched_cons, Matched, Popen_cons, Popen, Ztot_dtSub_kstar, Zopen_dtSub_kstar,
    udeg_kstar]
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-! ### The `first` child of the AFTER tree -/

/-- The single child of the AFTER tree: the first `k`-star with one leaf child replaced by
    the stem carrying the sibling — `node (replicate (k-1) leaf ++ [stemK k])`. -/
def afterFirst (k : ℕ) : UTree :=
  UTree.node (List.replicate (k - 1) flpLeaf ++ [stemK k])

/-- The AFTER tree: root collapsed to the single child `afterFirst k`. -/
def afterB (k : ℕ) : UTree := UTree.node [afterFirst k]

theorem afterFirst_children_length (k : ℕ) (hk : 1 ≤ k) :
    (List.replicate (k - 1) flpLeaf ++ [stemK k]).length = k := by
  rw [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
  omega

/-- `udeg (afterFirst k) = k + 1` for `k ≥ 1`: `(k-1)` leaves + `1` stem + parent edge. -/
theorem udeg_afterFirst (k : ℕ) (hk : 1 ≤ k) : udeg (afterFirst k) = k + 1 := by
  rw [afterFirst, udeg_node, afterFirst_children_length k hk]

/-- `Zopen (dtSub (afterFirst k)) = (4k+3)/(2(k+1))`: the open product over `(k-1)` leaves
    (`=1`) times the stem's total. -/
theorem Zopen_dtSub_afterFirst (k : ℕ) :
    Zopen (dtSub (afterFirst k)) = (4 * (k : ℝ) + 3) / (2 * ((k : ℝ) + 1)) := by
  rw [afterFirst, dtSub_node, Zopen, dtChildren_append, Popen_append,
    Popen_dtChildren_replicate_leaf]
  simp only [dtChildren_cons, dtChildren_nil, Popen_cons, Popen]
  rw [Ztot_dtSub_stemK]; ring

/-- `qSum (children of afterFirst k) = (k-1) + (2k+1)/(4k+3)` for `k ≥ 1`.  The `(k-1)`
    leaf children each contribute `1`; the stem contributes
    `Zopen/Ztot/udeg = ((2k+1)/(k+1))/((4k+3)/(2(k+1)))/2 = (2k+1)/(4k+3)`. -/
theorem qSum_afterFirst_children (k : ℕ) (hk : 1 ≤ k) :
    qSum (List.replicate (k - 1) flpLeaf ++ [stemK k])
      = ((k : ℝ) - 1) + (2 * (k : ℝ) + 1) / (4 * (k : ℝ) + 3) := by
  have hsplit : qSum (List.replicate (k - 1) flpLeaf ++ [stemK k])
      = qSum (List.replicate (k - 1) flpLeaf) + qSum [stemK k] := by
    simp only [qSum, List.map_append, List.sum_append]
  rw [hsplit, qSum_replicate_leaf, qSum_cons, qSum]
  simp only [List.map_nil, List.sum_nil, add_zero]
  rw [Zopen_dtSub_stemK, Ztot_dtSub_stemK, udeg_stemK]
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hk43 : (4 * (k : ℝ) + 3) ≠ 0 := by positivity
  have hkcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    have : 1 ≤ (k : ℝ) := by exact_mod_cast hk
    rw [Nat.cast_sub hk]; push_cast; ring
  rw [hkcast]
  congr 1
  field_simp
  ring

/-- `Ztot (dtSub (afterFirst k)) = (8k²+8k+1)/(2(k+1)²)` for `k ≥ 1`: the stem-and-leaves
    child block dressed at subtree degree `udeg = k+1`, collapsed to a single fraction. -/
theorem Ztot_dtSub_afterFirst (k : ℕ) (hk : 1 ≤ k) :
    Ztot (dtSub (afterFirst k))
      = (8 * (k : ℝ) ^ 2 + 8 * (k : ℝ) + 1) / (2 * ((k : ℝ) + 1) ^ 2) := by
  rw [afterFirst, dtSub_node, afterFirst_children_length k hk,
    show k + 1 = (List.replicate (k - 1) flpLeaf ++ [stemK k]).length + 1 by
      rw [afterFirst_children_length k hk],
    Ztot_node_deg, List.map_append, List.prod_append, List.map_replicate, List.prod_replicate,
    Ztot_dtSub_flpLeaf, one_pow, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Ztot_dtSub_stemK, one_mul, mul_one, qSum_afterFirst_children k hk,
    afterFirst_children_length k hk]
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hk43 : (4 * (k : ℝ) + 3) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-! ### The two objectives, and the base-case neutrality -/

/-- **BEFORE objective**: `Aobj (node [kstar k, kstar k]) = (4k+2)/(k+1)`.
    Root degree 2; two equal `k`-star children each `Ztot=(2k+1)/(k+1)`, each `qContrib =
    1/(2k+1)`; `Aobj = ((2k+1)/(k+1))²·(1 + (1/(2k+1))) = (4k+2)/(k+1)`. -/
theorem Aobj_before (k : ℕ) :
    Aobj (UTree.node [kstar k, kstar k]) = (4 * (k : ℝ) + 2) / ((k : ℝ) + 1) := by
  rw [Aobj_factor]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    List.length_cons, List.length_nil]
  rw [qSum_cons, qSum_cons, qSum, List.map_nil, List.sum_nil, add_zero,
    Ztot_dtSub_kstar, Zopen_dtSub_kstar, udeg_kstar]
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hk21 : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- **AFTER objective**: `Aobj (afterB k) = (4k+2)/(k+1)` for `k ≥ 1`.
    Root degree 1, single child `afterFirst k`; `Aobj = Ztot(dtSub first)·(1 + qContrib
    first)`.  Collapses to `(4k+2)/(k+1)`. -/
theorem Aobj_afterB (k : ℕ) (hk : 1 ≤ k) :
    Aobj (afterB k) = (4 * (k : ℝ) + 2) / ((k : ℝ) + 1) := by
  rw [afterB, Aobj_factor]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    List.length_cons, List.length_nil, mul_one]
  -- root degree 1, single child `afterFirst k`: peel the one-element qSum.
  rw [qSum_cons, qSum, List.map_nil, List.sum_nil, add_zero,
    Ztot_dtSub_afterFirst k hk, Zopen_dtSub_afterFirst k, udeg_afterFirst k hk]
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hk43 : (4 * (k : ℝ) + 3) ≠ 0 := by positivity
  have hk21 : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
  have hnum : (8 * (k : ℝ) ^ 2 + 8 * (k : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- **Case-B symmetric base-case neutrality (parametric in k)**: the two-`k`-star
    straightening move is Aobj-NEUTRAL for every `k ≥ 1`.  Both sides equal `(4k+2)/(k+1)`.
    In particular `Aobj (before) ≤ Aobj (after)` (Aobj-non-decreasing). -/
theorem symmetric_star_neutral (k : ℕ) (hk : 1 ≤ k) :
    Aobj (UTree.node [kstar k, kstar k]) = Aobj (afterB k) := by
  rw [Aobj_before, Aobj_afterB k hk]

/-- The base-case straightening does not decrease `Aobj` (immediate from neutrality). -/
theorem symmetric_star_monotone (k : ℕ) (hk : 1 ≤ k) :
    Aobj (UTree.node [kstar k, kstar k]) ≤ Aobj (afterB k) :=
  le_of_eq (symmetric_star_neutral k hk)

end Step3
end R3Cert
