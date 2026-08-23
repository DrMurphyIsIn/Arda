/-
  R4-R7 campaign, PHASE 2 (GAP-3): ROOT-INVARIANCE of the objective.

  `Aobj` (R47Tree.lean) is defined on ROOTED trees `UTree` via the true-degree realization
  `dtRealize`.  The paper's objects are UNROOTED (Design decision 1, R47_CAMPAIGN.md); the
  plan calls for "root-invariance lemmas where surgery demands it".  This file supplies the
  reusable ENGINE for that invariance.

  The P1 capstone `pi_utree` already factors the objective through a pure graph quantity:

      Aobj t = (lapl (aGraph (realize (dtRealize t)))).permanent
                 / (∏ v, (aGraph (realize (dtRealize t))).degree v).

  So `Aobj` depends on the rooted tree ONLY through the realized SimpleGraph, up to
  relabeling of its vertex type.  The genuine mathematical content of root-invariance is
  therefore: *the permanent ratio is invariant under any relabeling (index `Equiv`) of the
  vertex type*.  We PROVE that here, end to end, with no `sorry`:

  * `permanent_submatrix_equiv`   -- `per (M.submatrix e e) = per M` for `e : m ≃ n`
                                     (reindex the permutation sum by `e.permCongr`, then the
                                     inner product by `e`).  This is the reindex-invariance
                                     of the permanent that Mathlib does not ship (it has only
                                     `permanent_permute_cols/rows` on a FIXED type).
  * `lapl_submatrix_of_transport` -- if `e` transports adjacency and degree of `G` to `H`,
                                     then `lapl H = (lapl G).submatrix e.symm e.symm`
                                     (entrywise: diagonal = degree, off-diagonal = adjacency).
  * `permanent_lapl_eq_of_transport` / `degprod_eq_of_transport` -- the permanent and the
                                     degree product are equal for two transport-related
                                     graphs.
  * `piRatio_eq_of_transport`     -- hence the permanent RATIO is equal.
  * `Aobj_root_invariant`         -- **the P2 capstone**: two rooted trees whose realized
                                     graphs are transport-related have equal `Aobj`.

  HONEST SCOPE.  This file discharges the ALGEBRAIC engine of root-invariance (permanent
  ratio is a vertex-labeling invariant) as genuine theorems.  The remaining seam is
  purely COMBINATORIAL: exhibiting, for a concrete re-rooting `dtRealize t₁` vs
  `dtRealize t₂` of the same abstract unrooted tree, the vertex `Equiv` that transports
  adjacency and degree (a `SimpleGraph.Iso` between the two address graphs).  That
  address-graph iso is the object of a later combinatorial phase; it is NOT stubbed to
  `True` here -- `Aobj_root_invariant` takes the transport data as an explicit typed
  hypothesis, so any consumer that produces the iso gets invariance for free.  Nothing in
  this file asserts that such an iso always exists, and nothing here advances
  `conjecture1_proved` (still False).

  Genuine proofs (no `sorry`).  Lean draft, name-checked against pinned Mathlib +
  R3Cert; CI-pending (no local lake build).
-/
import Mathlib
import R3Cert.R47Tree

namespace R3Cert
namespace Step3

open Matrix Equiv

/-! ### 1. Reindex-invariance of the permanent (the engine) -/

/-- **Reindexing the vertex type leaves the permanent unchanged.**  For `e : m ≃ n` and a
    square matrix `M` on `n`, the relabeled matrix `M.submatrix e e` (entry `(i,j) =
    M (e i) (e j)`) has the same permanent as `M`.

    Proof: `per (M.submatrix e e) = ∑_{σ : Perm m} ∏_i M (e (σ i)) (e i)`.  Reindex the
    outer sum by the bijection `e.permCongr : Perm m ≃ Perm n` (`Fintype.sum_equiv`) and the
    inner product by `e : m ≃ n` (`Fintype.prod_equiv`); the `permCongr`/`submatrix` β-redexes
    collapse so both sides become `∑_{τ : Perm n} ∏_j M (τ j) j = per M`.

    Mathlib ships only `permanent_permute_cols/rows` (a `Perm n` on a FIXED index type);
    this is the missing cross-type version. -/
theorem permanent_submatrix_equiv {m n R : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [CommRing R] (e : m ≃ n) (M : Matrix n n R) :
    (M.submatrix e e).permanent = M.permanent := by
  -- Unfold both permanents to sums over permutations.
  simp only [Matrix.permanent]
  -- Reindex the outer sum by `e.permCongr : Perm m ≃ Perm n`
  -- (`Fintype.sum_equiv φ f g h : ∑ f = ∑ g`, so no `.symm`).
  refine Fintype.sum_equiv e.permCongr _ _ ?_
  intro σ
  -- For a fixed `σ : Perm m`, reindex the inner product by `e : m ≃ n`.
  refine Fintype.prod_equiv e _ _ ?_
  intro i
  -- LHS: `(M.submatrix e e) (σ i) i = M (e (σ i)) (e i)`;
  -- RHS at `e i`: `M ((e.permCongr σ) (e i)) (e i) = M (e (σ i)) (e i)`.
  simp only [Matrix.submatrix_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply]

/-! ### 2. Transport of the Laplacian along a degree/adjacency-preserving `Equiv` -/

section Transport
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- The transport hypothesis: `e : V ≃ W` sends `G` onto `H` preserving degree and
    adjacency.  (Exactly the data of a `SimpleGraph.Iso G H` together with degree equality,
    which for a finite graph iso is automatic; we keep both as explicit fields so a consumer
    may supply whichever it has.) -/
structure GraphTransport (e : V ≃ W) : Prop where
  deg  : ∀ v : V, H.degree (e v) = G.degree v
  adj  : ∀ u v : V, H.Adj (e u) (e v) ↔ G.Adj u v

/-- Under a transport `e`, the Laplacian of `H` is the relabeled Laplacian of `G`:
    `lapl H = (lapl G).submatrix e.symm e.symm`.  Entrywise: diagonal from `deg`,
    off-diagonal from `adj` (and the `-1`/`0` split matches). -/
theorem lapl_submatrix_of_transport {e : V ≃ W} (ht : GraphTransport G H e) :
    lapl H = (lapl G).submatrix e.symm e.symm := by
  ext a b
  rw [Matrix.submatrix_apply]
  -- write `a = e u`, `b = e v` so we can use the transport equalities.
  obtain ⟨u, rfl⟩ := e.surjective a
  obtain ⟨v, rfl⟩ := e.surjective b
  simp only [Equiv.symm_apply_apply]
  simp only [lapl]
  by_cases hab : (e u) = (e v)
  · have huv : u = v := e.injective hab
    rw [if_pos hab, if_pos huv, ht.deg u]
  · have huv : u ≠ v := fun h => hab (by rw [h])
    rw [if_neg hab, if_neg huv]
    by_cases hAdj : G.Adj u v
    · rw [if_pos ((ht.adj u v).mpr hAdj), if_pos hAdj]
    · rw [if_neg (fun h => hAdj ((ht.adj u v).mp h)), if_neg hAdj]

/-- The Laplacian permanents agree under transport (reindex-invariance of `permanent`
    applied to `lapl_submatrix_of_transport`). -/
theorem permanent_lapl_eq_of_transport {e : V ≃ W} (ht : GraphTransport G H e) :
    (lapl H).permanent = (lapl G).permanent := by
  rw [lapl_submatrix_of_transport G H ht, permanent_submatrix_equiv e.symm (lapl G)]

/-- The degree products agree under transport (reindex the product by `e` and use `deg`). -/
theorem degprod_eq_of_transport {e : V ≃ W} (ht : GraphTransport G H e) :
    (∏ w, (H.degree w : ℝ)) = ∏ v, (G.degree v : ℝ) := by
  -- reindex the `W`-product by `e.symm : W ≃ V`; `deg` at `e.symm w` gives the summand.
  refine Fintype.prod_equiv e.symm _ _ ?_
  intro w
  have := ht.deg (e.symm w)
  rw [Equiv.apply_symm_apply] at this
  rw [this]

/-- **The permanent ratio is a transport invariant.**  This is the vertex-labeling
    invariance that makes the objective independent of the rooting/labeling. -/
theorem piRatio_eq_of_transport {e : V ≃ W} (ht : GraphTransport G H e) :
    (lapl H).permanent / (∏ w, (H.degree w : ℝ))
      = (lapl G).permanent / (∏ v, (G.degree v : ℝ)) := by
  rw [permanent_lapl_eq_of_transport G H ht, degprod_eq_of_transport G H ht]

end Transport

/-! ### 3. The P2 root-invariance capstone -/

/-- **P2 ROOT-INVARIANCE CAPSTONE (conditional on the address-graph transport).**

    If the realized address graphs of two rooted trees `t₁`, `t₂` are transport-related by a
    vertex `Equiv` `e` (same abstract unrooted tree, different roots), then their objectives
    coincide: `Aobj t₁ = Aobj t₂`.

    Proof: both sides equal the permanent ratio via `pi_utree` (P1), and the ratio is a
    transport invariant (`piRatio_eq_of_transport`).  The permanent-ratio ALGEBRA is fully
    discharged here; the only input is the combinatorial transport `e` between the two
    address graphs -- the honest remaining seam (a later phase's `SimpleGraph.Iso`
    construction), supplied as an explicit hypothesis, never stubbed. -/
theorem Aobj_root_invariant (t₁ t₂ : UTree)
    (e : AVert (realize (dtRealize t₁)) ≃ AVert (realize (dtRealize t₂)))
    (ht : GraphTransport (aGraph (realize (dtRealize t₁)))
            (aGraph (realize (dtRealize t₂))) e) :
    Aobj t₁ = Aobj t₂ := by
  rw [← pi_utree t₁, ← pi_utree t₂]
  -- `piRatio_eq_of_transport G H ht : ratio H = ratio G`; here `G = t₁`, `H = t₂`,
  -- so it gives `ratio t₂ = ratio t₁`; the goal is the reverse, hence `.symm`.
  exact
    (piRatio_eq_of_transport (aGraph (realize (dtRealize t₁)))
      (aGraph (realize (dtRealize t₂))) ht).symm

end Step3
end R3Cert
