/-
  R47 R6 balancing-transfer INDUCTION -- the inductive engine over the single-hub
  cherry-transfer step `Aobj_balance_le` (#118).

  `Aobj_balance_le` (R47R6BalanceLeCert) shows ONE valid transfer -- moving a cherry
  from the longer arm `b` to the shorter arm `a` (`(a,b) -> (a+1,b-1)`, in the certified
  regime `3 <= a`, `a+2 <= b`, many-arm `6 <= |arms|+c`) -- does not decrease `Aobj`.

  This file lifts that single step to a full CHAIN: the reflexive-transitive closure of
  the transfer relation `BalanceStep` is `Aobj`-monotone (`Aobj_balanceStar_le`).  That is
  the "transfer induction" that iterates `Aobj_balance_le` toward the balanced canonical
  form -- the connective identity for the Hnorm (arbitrary single hub -> balanced star)
  direction of the R7' assembly.

  HONEST SCOPE.  This proves ONLY the monotonicity of the transfer closure (the inductive
  half).  It does NOT prove that every single-hub arm distribution REACHES the balanced
  form under `BalanceStep` (the combinatorial reachability half -- termination + the
  `3 <= a` floor -- is left as the explicit hypothesis `Hreach` in `single_hub_balanced_ge`,
  mirroring the conditional style of `conjecture1_of_layers`).  It also stays SINGLE-HUB
  (the multi-hub lift is separate).  Self-contained; genuine proof (no `sorry`, no `axiom`,
  no vacuous hypothesis).  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47R6BalanceLeCert

namespace R3Cert
namespace Step3

open RTree

/-- A single valid balancing transfer on a single hub: move one cherry from the longer
    arm `b` to the shorter arm `a` (`(a,b) -> (a+1,b-1)`), in the certified many-arm
    regime `3 <= a`, `a+2 <= b`, `6 <= |arms|+c`.  Relates the two singleton hub-lists
    exactly as `Aobj_balance_le` compares them. -/
def BalanceStep (s s' : List Hub) : Prop :=
  ∃ (a b : ℕ) (rest : List ℕ) (c : ℕ),
    3 ≤ a ∧ a + 2 ≤ b ∧ 6 ≤ (a :: b :: rest).length + c ∧
    s = [(a :: b :: rest, c)] ∧ s' = [((a + 1) :: (b - 1) :: rest, c)]

/-- One transfer step does not decrease `Aobj` -- a direct repackaging of the
    connective identity `Aobj_balance_le`. -/
theorem Aobj_balanceStep_le {s s' : List Hub} (h : BalanceStep s s') :
    Aobj (backboneU s) ≤ Aobj (backboneU s') := by
  obtain ⟨a, b, rest, c, ha, hb, hd, rfl, rfl⟩ := h
  exact Aobj_balance_le a b rest c ha hb hd

/-- **Transfer induction.**  Any finite chain of balancing transfers does not decrease
    `Aobj`: the reflexive-transitive closure of `BalanceStep` is `Aobj`-monotone.  This is
    the inductive engine that lifts the single-step `Aobj_balance_le` to a full reduction
    toward the balanced canonical form. -/
theorem Aobj_balanceStar_le {s s' : List Hub}
    (h : Relation.ReflTransGen BalanceStep s s') :
    Aobj (backboneU s) ≤ Aobj (backboneU s') := by
  induction h with
  | refl => exact le_refl _
  | tail _ hstep ih => exact le_trans ih (Aobj_balanceStep_le hstep)

/-- **Conditional single-hub balanced-maximality.**  Given that a hub-state `s` can be
    balanced by a finite chain of transfers to a canonical `sbal` (`Hreach`, the open
    combinatorial reachability -- termination + the `3 <= a` floor), the balanced form has
    `Aobj` at least that of `s`.  This is the shape the Hnorm normalization layer consumes:
    an arbitrary single hub is dominated (in `Aobj`) by its balanced star.  The remaining
    obligation is exactly `Hreach`, isolated as a hypothesis (not `sorry`-ed). -/
theorem single_hub_balanced_ge {s sbal : List Hub}
    (Hreach : Relation.ReflTransGen BalanceStep s sbal) :
    Aobj (backboneU s) ≤ Aobj (backboneU sbal) :=
  Aobj_balanceStar_le Hreach

end Step3
end R3Cert
