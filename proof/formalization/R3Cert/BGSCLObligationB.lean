/-
  OBLIGATION B — the ROOT-INVARIANCE SEAM of `Aobj` (Hnorm gap iii).

  `R47RootInvariance` supplies the ALGEBRAIC engine of root-invariance: the permanent ratio
  `per(lapl)/∏deg` is a vertex-labeling invariant, and `Aobj_root_invariant` upgrades that to
  `Aobj t₁ = Aobj t₂` *conditional* on a `GraphTransport` between the two realized address
  graphs.  `GraphTransport G H e` (that file) is the data of a vertex `Equiv` `e : V ≃ W`
  together with degree- and adjacency-preservation.

  The design handoff (`DEBRANCH_MOVE_DESIGN_20260831.md`, Obligation B) names the remaining
  seam precisely: "constructing, for two re-rootings of the same abstract tree, the vertex
  `Equiv` / `SimpleGraph.Iso` transporting adjacency + degree".  This file discharges that
  seam at the level Mathlib names it: **a `SimpleGraph.Iso` between the two address graphs is
  EXACTLY a `GraphTransport`**, and hence yields root-invariance UNCONDITIONALLY.

  The mathematical content proven here (all genuine, no `sorry`):

  * `GraphTransport.of_iso`      -- a `SimpleGraph.Iso G H` (Mathlib `G ≃g H`, i.e. an
                                    adjacency-respecting vertex bijection) is a
                                    `GraphTransport G H` along its underlying `Equiv`.
                                    Adjacency is `RelIso.map_rel_iff`; DEGREE preservation is
                                    the real content and is Mathlib's `SimpleGraph.Iso.degree_eq`
                                    (a finite graph iso preserves every vertex degree).  This is
                                    the step that makes root-invariance need only a bare
                                    `SimpleGraph.Iso`, not a separately-supplied degree law.
  * `Aobj_root_invariant_of_iso` -- **the OBLIGATION-B capstone**: if the realized address
                                    graphs of two rooted trees are isomorphic as `SimpleGraph`s
                                    (`aGraph … ≃g aGraph …`), then `Aobj t₁ = Aobj t₂`.  No
                                    `GraphTransport` hypothesis, no degree hypothesis — the
                                    single input is the address-graph iso the design doc calls
                                    for.

  HONEST SCOPE.  This closes the *seam* between `SimpleGraph.Iso` and `GraphTransport`
  unconditionally: any consumer that exhibits a `aGraph (realize (dtRealize t₁)) ≃g
  aGraph (realize (dtRealize t₂))` — the natural output of a re-rooting of the same abstract
  unrooted tree — now gets `Aobj t₁ = Aobj t₂` with no side conditions.  What is NOT asserted
  here (and would be false in general): that such an iso exists for ARBITRARY `t₁, t₂` — it
  exists exactly when they are re-rootings of the same unrooted tree, which is the meaning of
  root-invariance.  Producing the concrete iso for a specific SPR re-rooting is a downstream
  instantiation that plugs directly into `Aobj_root_invariant_of_iso`.  Nothing here advances
  `conjecture1_proved` (still False).

  Genuine proofs (no `sorry`).  Lean 4 / Mathlib v4.32.0; verify with `lake build`.
-/
import Mathlib
import R3Cert.R47RootInvariance

namespace R3Cert
namespace Step3

open Matrix

/-! ### 1. A `SimpleGraph.Iso` IS a `GraphTransport` (the seam, unconditional) -/

section IsoTransport
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]

omit [DecidableEq V] [DecidableEq W] in
/-- **The root-invariance seam.**  A `SimpleGraph.Iso` `f : G ≃g H` is a `GraphTransport G H`
    along its underlying vertex `Equiv` `f.toEquiv`.

    * adjacency: `H.Adj (f u) (f v) ↔ G.Adj u v` is `RelIso.map_rel_iff` (the defining property
      of a graph iso — it respects adjacency in both directions);
    * degree: `H.degree (f v) = G.degree v` is `SimpleGraph.Iso.degree_eq` — a finite graph iso
      preserves every vertex degree.  This is the genuine content that makes a bare iso enough:
      the caller need not separately prove degrees match. -/
theorem GraphTransport.of_iso (f : G ≃g H) :
    GraphTransport G H f.toEquiv where
  deg v := by
    -- `f.toEquiv v` reduces to `f v`; `Iso.degree_eq f v : H.degree (f v) = G.degree v`.
    show H.degree (f v) = G.degree v
    exact f.degree_eq v
  adj u v := by
    -- `f.toEquiv u = f u`; the RelIso property is exactly the adjacency iff.
    show H.Adj (f u) (f v) ↔ G.Adj u v
    exact f.map_rel_iff

/-- Consequently, the permanent RATIO is invariant under a graph iso (no transport data needed;
    the iso is the data).  A convenience specialization of `piRatio_eq_of_transport`. -/
theorem piRatio_eq_of_iso (f : G ≃g H) :
    (lapl H).permanent / (∏ w, (H.degree w : ℝ))
      = (lapl G).permanent / (∏ v, (G.degree v : ℝ)) :=
  piRatio_eq_of_transport G H (GraphTransport.of_iso f)

end IsoTransport

/-! ### 2. OBLIGATION-B CAPSTONE: root-invariance from an address-graph iso -/

/-- **OBLIGATION B (root-invariance seam), discharged.**

    If the realized address graphs of two rooted trees `t₁`, `t₂` are ISOMORPHIC as
    `SimpleGraph`s (the natural certificate that they are re-rootings of the same abstract
    unrooted tree), then their objectives coincide: `Aobj t₁ = Aobj t₂`.

    Unlike `Aobj_root_invariant` (which takes a `GraphTransport` + explicit `Equiv`), this
    consumes only a bare `SimpleGraph.Iso` — the object the design handoff names as the seam.
    The degree-preservation half is discharged internally via `SimpleGraph.Iso.degree_eq`, so
    a downstream re-rooting witness needs to produce nothing beyond the adjacency-respecting
    vertex bijection.

    Proof: `GraphTransport.of_iso` turns the iso into a transport, then
    `Aobj_root_invariant` closes it (both sides equal the permanent ratio via `pi_utree`, and
    the ratio is a transport invariant). -/
theorem Aobj_root_invariant_of_iso (t₁ t₂ : UTree)
    (f : aGraph (realize (dtRealize t₁)) ≃g aGraph (realize (dtRealize t₂))) :
    Aobj t₁ = Aobj t₂ :=
  Aobj_root_invariant t₁ t₂ f.toEquiv (GraphTransport.of_iso f)

/-- Reflexivity sanity check: the identity iso gives back `Aobj t = Aobj t`.  (Confirms the
    capstone actually fires on a concrete, closed iso — the trivial same-rooting witness.) -/
theorem Aobj_root_invariant_of_iso_refl (t : UTree) :
    Aobj t = Aobj t :=
  Aobj_root_invariant_of_iso t t
    (SimpleGraph.Iso.refl (G := aGraph (realize (dtRealize t))))

end Step3
end R3Cert
