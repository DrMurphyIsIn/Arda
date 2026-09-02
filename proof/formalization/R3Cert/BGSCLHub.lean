/-
  SCL FlowedHubStep assembly — the list machinery + tangent connection tying the per-degree decouple
  residuals (`BGSCLDecouple`) to the actual hub `node cs`.
  `child_bell_sum_le`: from the per-child SCL at a price `ν`, the sum bound `Σ bell(c) ≤ |cs|·bV_ν(cherry) − ν·S`.
  This feeds `bell_node_tangent` + `bY_node` + `decouple_d` to give `bV μ (node cs) ≤ bV μ cherry` for d≤6.
  (d≥7 needs the branch ceiling `bell (node cs) ≤ 0`, a separate result not yet in the SCL Lean.)
  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.BGSCLInduction
import R3Cert.BGSCLStep

namespace R3Cert
namespace BGSCL

/-- **The child-sum bound.**  If every child `c ∈ cs` satisfies the SCL at price `ν`
    (`bV ν c ≤ bV ν cherry`), then `Σ_c bell(c) ≤ |cs|·bV_ν(cherry) − ν·Σ_c bY(c)`.  (Since
    `bell c = bV ν c − ν·bY c ≤ bV ν cherry − ν·bY c`, summed.)  This is the list-machinery half of the
    per-hub decouple: it converts the per-child hypotheses into the single scalar `Σ bell` bound the
    tangent needs. -/
theorem child_bell_sum_le (ν : ℝ) (cs : List Branch) (h : ∀ c ∈ cs, bV ν c ≤ bV ν cherry) :
    (cs.map bell).sum ≤ (cs.length : ℝ) * bV ν cherry - ν * (cs.map bY).sum := by
  induction cs with
  | nil => simp
  | cons a t ih =>
    have ha : bell a + ν * bY a ≤ bell cherry + ν * bY cherry := by
      have h1 : bV ν a = bell a + ν * bY a := rfl
      have h2 : bV ν cherry = bell cherry + ν * bY cherry := rfl
      have := h a (List.mem_cons.mpr (Or.inl rfl)); rw [h1, h2] at this; exact this
    have iht : (t.map bell).sum ≤ (t.length : ℝ) * bV ν cherry - ν * (t.map bY).sum :=
      ih (fun c hc => h c (List.mem_cons.mpr (Or.inr hc)))
    have hVc : bV ν cherry = bell cherry + ν * bY cherry := rfl
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    rw [hVc] at iht ⊢
    nlinarith [ha, iht]

end BGSCL
end R3Cert
