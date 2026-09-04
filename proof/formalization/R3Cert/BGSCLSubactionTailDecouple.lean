/-
  The tail (deg≥5) DECOUPLE reduction (2026-09-03).

  Reusable backbone for the mixed-degree tail cells of `IsSubaction ρwit`, per the counts-exchange
  dissolution (`proof/docs/BG_SUBACTION_CONSOLIDATED_HANDOFF.md` §3.3): for a node of degree
  `d = |cs|+1 ≥ 5` (so `ρwit(node cs) = 0`), the subaction inequality
  `(log(1 + S/d) − F*) + 0 ≤ Σ_c ρwit(c)`  (`S = Σ bY(c)`)
  follows, via the concave-log tangent at ANY reference `S0`, from
    (i) a per-child lower bound  `ρwit(c) ≥ m + bY(c)/(d+S0)`  for all children, and
    (ii) `B(S0) := (d−1)·m + [F* − log(1+S0/d) + S0/(d+S0)] ≥ 0`.
  No discrete convexity: the tangent decouples the coupled `log`, and `Σ` lifts the per-child bound.
  Kernel-checked vs `R3Cert.BGSCLInduction`/`BGSCLSubaction`.  No `sorry`.  `conjecture1_proved = False`.
-/
import Mathlib
import R3Cert.BGSCLInduction
import R3Cert.BGSCLSubaction

namespace R3Cert
namespace BGSCL

open Real

/-- **List-lift.**  A per-child affine lower bound `m + σ·bY c ≤ ρwit c` sums to
    `(|cs|)·m + σ·(Σ bY) ≤ Σ ρwit`. -/
theorem sum_rhowit_ge (σ m : ℝ) : ∀ (cs : List Branch),
    (∀ c ∈ cs, m + σ * bY c ≤ ρwit c) →
    (cs.length : ℝ) * m + σ * (cs.map bY).sum ≤ (cs.map ρwit).sum
  | [], _ => by simp
  | a :: t, h => by
    have ha : m + σ * bY a ≤ ρwit a := h a (by simp)
    have ht := sum_rhowit_ge σ m t (fun c hc => h c (by simp [hc]))
    simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_one]
    calc ((t.length : ℝ) + 1) * m + σ * (bY a + (t.map bY).sum)
        = (m + σ * bY a) + ((t.length : ℝ) * m + σ * (t.map bY).sum) := by ring
      _ ≤ ρwit a + (t.map ρwit).sum := add_le_add ha ht

/-- `ρwit(node cs) = 0` when the degree is ≥ 5 (`|cs| ≥ 4`). -/
theorem ρwit_node_high {cs : List Branch} (hlen : 4 ≤ cs.length) :
    ρwit (Branch.node cs) = 0 := by
  rw [ρwit]
  simp only [bcc]
  rcases hcl : cs.length with _ | _ | _ | _ | n
  · omega
  · omega
  · omega
  · omega
  · rfl

/-- **The tail DECOUPLE reduction.**  For a node of degree `d = |cs|+1 ≥ 5` (`ρwit(node cs)=0`), the
    subaction inequality reduces — via the concave-log tangent at any reference `S0 ≥ 0` — to a per-child
    lower bound (`hpc`) plus `B(S0) ≥ 0` (`hB`).  This is the mixed-degree tail closer; instantiate with the
    per-degree-class min `m` and the `S0 ∈ {(d−1)/3, (d−1)/4, (d−1)/5}` d-split. -/
theorem tail_decouple (cs : List Branch) (S0 m : ℝ)
    (hlen : 4 ≤ cs.length) (hS0 : 0 ≤ S0)
    (hpc : ∀ c ∈ cs, m + (1 / (((cs.length : ℝ) + 1) + S0)) * bY c ≤ ρwit c)
    (hB : 0 ≤ (cs.length : ℝ) * m
            + (FSTAR - Real.log (1 + S0 / ((cs.length : ℝ) + 1))
               + S0 / (((cs.length : ℝ) + 1) + S0))) :
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node cs) ≤ (cs.map ρwit).sum := by
  have hd_pos : (0 : ℝ) < (cs.length : ℝ) + 1 := by positivity
  have hdS0 : (0 : ℝ) < ((cs.length : ℝ) + 1) + S0 := by positivity
  have hS_nn : (0 : ℝ) ≤ (cs.map bY).sum :=
    List.sum_nonneg (fun x hx => by
      rw [List.mem_map] at hx; obtain ⟨c, _, rfl⟩ := hx; exact bY_nonneg c)
  have htan := log_tangent (d := (cs.length : ℝ) + 1) (s := (cs.map bY).sum) (s0 := S0)
    hd_pos hS_nn hS0
  have hsum := sum_rhowit_ge (1 / (((cs.length : ℝ) + 1) + S0)) m cs hpc
  have hsp : ((cs.map bY).sum - S0) / (((cs.length : ℝ) + 1) + S0)
      = (1 / (((cs.length : ℝ) + 1) + S0)) * (cs.map bY).sum
        - S0 / (((cs.length : ℝ) + 1) + S0) := by
    field_simp
  rw [ρwit_node_high hlen]
  linarith [htan, hsum, hB, hsp]

end BGSCL
end R3Cert
