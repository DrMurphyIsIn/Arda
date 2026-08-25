/-
  R47 R6 balancing-transfer TERMINATION + FLOOR -- the well-foundedness and cherry-floor
  bookkeeping for the single-hub transfer `BalanceStep` (R47R6BalanceInduction, #120).

  `BalanceStep` moves a cherry from the longer arm `b` to the shorter arm `a`
  (`(a,b) -> (a+1,b-1)`, `3 <= a`, `a+2 <= b`). This file proves the two ingredients the
  `Hreach` reachability obligation of `single_hub_balanced_ge` needs from the transfer
  dynamics:

    * TERMINATION.  The sum of squares of the arm lengths STRICTLY DECREASES at every step
      (`balanceStep_measure_lt`), hence `BalanceStep` is WELL-FOUNDED (`balanceStep_wf`) --
      no infinite balancing chain.  (Exact drop: `a^2+b^2 -> (a+1)^2+(b-1)^2` falls by
      `2*(b-a-1) >= 2`.)
    * FLOOR.  The `3 <= arm` cherry-structure invariant is PRESERVED
      (`balanceStep_preserves_floor`): if every arm is `>= 3` before a step, so is every
      arm after (`a+1 >= 4`, and `b-1 >= a+1 >= 4`).

  HONEST SCOPE.  These are the termination + floor halves of `Hreach`.  What remains for
  full reachability of the balanced form -- and is NOT proved here -- is (i) the PROGRESS
  half: whenever a single-hub distribution with all arms `>= 3` is not balanced-to-within-1,
  SOME `BalanceStep` applies; and (ii) arm-PERMUTATION invariance of `Aobj`/`BalanceStep`
  (the step as defined acts on the first two arms only, so reaching an arbitrary pair needs
  reordering).  Both are left as explicit further work, not `sorry`-ed.

  Self-contained; genuine proof (no `sorry`, no `axiom`, no vacuous hypothesis).
  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47R6BalanceInduction

namespace R3Cert
namespace Step3

open RTree

/-- Sum of squares of one hub's arm lengths. -/
def armSumSq (h : Hub) : ℕ := (h.1.map (· ^ 2)).sum

/-- Termination measure of a hub-state: total sum of squares of all arm lengths. -/
def stateMeasure (s : List Hub) : ℕ := (s.map armSumSq).sum

/-- The arithmetic core of termination: moving a unit from `b` down to `a` up, when
    `a + 2 <= b`, strictly lowers `a^2 + b^2`. -/
theorem sq_transfer_lt {a b : ℕ} (hb : a + 2 ≤ b) :
    (a + 1) ^ 2 + (b - 1) ^ 2 < a ^ 2 + b ^ 2 := by
  obtain ⟨e, rfl⟩ : ∃ e, b = a + e + 2 := ⟨b - a - 2, by omega⟩
  have hb1 : a + e + 2 - 1 = a + e + 1 := by omega
  rw [hb1]
  nlinarith

/-- **Termination measure strictly decreases.**  Every `BalanceStep` lowers the
    total sum of squares of arm lengths. -/
theorem balanceStep_measure_lt {s s' : List Hub} (h : BalanceStep s s') :
    stateMeasure s' < stateMeasure s := by
  obtain ⟨a, b, rest, c, ha, hb, hd, rfl, rfl⟩ := h
  simp only [stateMeasure, armSumSq, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.add_zero]
  linarith [sq_transfer_lt hb]

/-- **`BalanceStep` is well-founded.**  Termination of the balancing process: the
    sum-of-squares measure descends into `ℕ`, so there is no infinite chain of transfers. -/
theorem balanceStep_wf : WellFounded (fun s' s : List Hub => BalanceStep s s') :=
  Subrelation.wf (fun h => balanceStep_measure_lt h)
    (InvImage.wf stateMeasure Nat.lt_wfRel.wf)

/-- **The `3 <= arm` cherry floor is preserved.**  If every arm of every hub is `>= 3`
    before a `BalanceStep`, then so is every arm after it. -/
theorem balanceStep_preserves_floor {s s' : List Hub} (h : BalanceStep s s')
    (hfloor : ∀ hub ∈ s, ∀ x ∈ hub.1, 3 ≤ x) :
    ∀ hub ∈ s', ∀ x ∈ hub.1, 3 ≤ x := by
  obtain ⟨a, b, rest, c, ha, hb, hd, rfl, rfl⟩ := h
  have hbase : ∀ x ∈ (a :: b :: rest), 3 ≤ x :=
    hfloor (a :: b :: rest, c) (List.mem_singleton.mpr rfl)
  intro hub hmem x hx
  rw [List.mem_singleton] at hmem; subst hmem
  simp only [List.mem_cons] at hx
  rcases hx with rfl | rfl | hxr
  · omega
  · omega
  · exact hbase x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hxr))

end Step3
end R3Cert
