/-  H11K_EdgeSplit.lean -- lane H11K: the Arb4 edge checker `Arb4.edgeOK` assembled from one
    kernel check PER OCTANT PIECE.

    `Arb4.edgeOK` is one Boolean per edge, checked by ONE `decide +kernel`; the Arb4 lane measured its
    memory at about 19 GB for an edge at height 1e4 (25 pieces, EM cut N = 0.3 T).  Here the piece
    conjunct of `edgeOK` is split off:

      * `pieceJ E j`   -- piece `j`: `Arb4.pieceOK` and both breakpoints inside its radius;
      * `edgeRest E`   -- everything else in `edgeOK` (label steps, endpoints, the two endpoint boxes
                          with their corners, the final `π` / `arctan` inequalities);
      * `edgeOK_of_split` -- `edgeRest E = true` and `pieceJ E j = true` for every `j < E.m` give
                          `edgeOK E = true`, hence `Arb4.edgeOK_sound`.

    Each `pieceJ E j` is then one small `decide +kernel` (one evaluator run of N terms).
    Trust: proved from its stated hypotheses; axioms within [propext, Classical.choice, Quot.sound]
    (H11K_AxiomGuard).  No `sorry`.  conjecture1_proved = False.
-/
import Arb4_Edge

open Complex

namespace H11K

open Arb4 Arb4.Q

/-- Piece `j` of edge `E`: the octant piece check and both of its breakpoints inside its radius. -/
noncomputable def pieceJ (E : EdgeD) (j : ℕ) : Bool :=
  pieceOK E.tn E.tq E.N E.L (E.pc j) && inRad (E.x j) (E.pc j) && inRad (E.x (j + 1)) (E.pc j)

/-- Every conjunct of `Arb4.edgeOK` except the pieces. -/
noncomputable def edgeRest (E : EdgeD) : Bool :=
  Nat.ble 1 E.m && Nat.ble 1 E.tn && eqB (E.x 0) (ofNat 2) && eqB (E.x E.m) (ofInt (-1)) &&
    (List.range (E.m - 1)).all (fun j => decide (|(E.pc (j + 1)).kk - (E.pc j).kk| ≤ 3)) &&
    eqB (E.pc 0).σQ (ofNat 2) && eqB (E.pc (E.m - 1)).σQ (ofInt (-1)) &&
    boxOK E.tn E.tq E.N (E.pc 0) E.D0 E.reLo0 E.reHi0 E.imLo0 E.imHi0 E.Qp0 E.Rn0 E.Rd0 E.qlo0 E.qhi0 &&
    boxOK E.tn E.tq E.N (E.pc (E.m - 1)) E.D1 E.reLo1 E.reHi1 E.imLo1 E.imHi1 E.Qp1 E.Rn1 E.Rd1
      E.qlo1 E.qhi1 &&
    finalLoOK ((E.pc (E.m - 1)).kk - (E.pc 0).kk) E.qhi0 E.qlo1 E.Lo &&
    finalHiOK ((E.pc (E.m - 1)).kk - (E.pc 0).kk) E.qlo0 E.qhi1 E.Hi

/-- **`edgeOK` from its split checks.** -/
theorem edgeOK_of_split (E : EdgeD) (hr : edgeRest E = true)
    (hp : ∀ j, j < E.m → pieceJ E j = true) : edgeOK E = true := by
  simp only [edgeRest, Bool.and_eq_true] at hr
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hm, htn⟩, hx0⟩, hxm⟩, hsteps⟩, hc0⟩, hc1⟩, hb0⟩, hb1⟩, hlo⟩, hhi⟩ := hr
  have hpcs : (List.range E.m).all (fun j => pieceOK E.tn E.tq E.N E.L (E.pc j) &&
      inRad (E.x j) (E.pc j) && inRad (E.x (j + 1)) (E.pc j)) = true := by
    rw [List.all_eq_true]
    intro j hj
    exact hp j (List.mem_range.mp hj)
  simp only [edgeOK, hm, htn, hx0, hxm, hpcs, hsteps, hc0, hc1, hb0, hb1, hlo, hhi, Bool.and_self]

/-- **The edge enclosure from the split checks** (`Arb4.edgeOK_sound`). -/
theorem edge_sound_of_split (E : EdgeD) (hr : edgeRest E = true)
    (hp : ∀ j, j < E.m → pieceJ E j = true) :
    DiffractionCore.argChangeHoriz riemannZeta E.T 2 (-1) ∈ Set.Icc E.Lo.val E.Hi.val :=
  edgeOK_sound E (edgeOK_of_split E hr hp)

end H11K
