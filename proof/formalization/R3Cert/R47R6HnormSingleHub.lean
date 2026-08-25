/-
  R47 R6 SINGLE-HUB Hnorm -- the balancing reduction, assembled.

  This ties together the four dynamical ingredients of the arbitrary-pair balancing transfer:

    * the monotone transfer engine `Aobj_transferStar_le` (R47R6TransferArb),
    * termination via the sum-of-squares measure (re-derived here for `TransferStep`),
    * the `3 <= arm` floor (carried through the recursion),
    * progress `transferStep_progress` (R47R6TransferProgress),

  into the single-hub normalization statement (`single_hub_Hnorm`): every hub whose arms are
  all `>= 3` (in the many-arm regime `6 <= |arms| + c`) is dominated in `Aobj` by a hub with
  the SAME arms rebalanced to within one.  I.e. an arbitrary single-hub arm distribution is
  `Aobj`-dominated by its balanced form -- the single-hub case of the `Hnorm` layer.

  Proof: well-founded recursion on the sum-of-squares measure.  If the arms are already
  balanced, done; otherwise `transferStep_progress` gives a strictly-lower-measure neighbour
  reachable by one `TransferStep` (which preserves the floor and the arm count), recurse, and
  prepend the step.  `Aobj_transferStar_le` turns the resulting transfer chain into the `Aobj`
  inequality.

  HONEST SCOPE.  This is the SINGLE-HUB case (one hub, its arms).  Lifting to arbitrary trees
  / multi-hub states -- the full `Hnorm` of `conjecture1_of_layers` -- is separate.
  Self-contained; genuine proof (no `sorry`, no `axiom`).  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.R47R6TransferProgress

namespace R3Cert
namespace Step3

open RTree

/-- The arithmetic core of termination (moving a unit from `b` down to `a` lowers `a^2+b^2`
    when `a + 2 <= b`). -/
private theorem sq_dec {a b : ℕ} (hb : a + 2 ≤ b) :
    (a + 1) ^ 2 + (b - 1) ^ 2 < a ^ 2 + b ^ 2 := by
  obtain ⟨e, rfl⟩ : ∃ e, b = a + e + 2 := ⟨b - a - 2, by omega⟩
  have he : a + e + 2 - 1 = a + e + 1 := by omega
  rw [he]; nlinarith

/-- A `TransferStep` out of a single all-arms-`>=3` hub yields a concrete more-balanced hub:
    strictly smaller sum-of-squares measure, floor preserved, arm count preserved. -/
theorem transferStep_dest {arms : List ℕ} {c : ℕ} {s' : List Hub}
    (hfloor : ∀ x ∈ arms, 3 ≤ x) (h : TransferStep [(arms, c)] s') :
    ∃ arms', s' = [(arms', c)]
      ∧ (arms'.map (· ^ 2)).sum < (arms.map (· ^ 2)).sum
      ∧ (∀ x ∈ arms', 3 ≤ x)
      ∧ arms'.length = arms.length := by
  obtain ⟨a, b, rest, A, A', C, ha, hb, _hd, hp, hp', hs, hs'⟩ := h
  simp only [List.cons.injEq, Prod.mk.injEq, and_true] at hs
  obtain ⟨rfl, rfl⟩ := hs
  have hmA : (arms.map (· ^ 2)).sum = a ^ 2 + b ^ 2 + (rest.map (· ^ 2)).sum := by
    rw [(hp.map (· ^ 2)).sum_eq]; simp only [List.map_cons, List.sum_cons]; ring
  have hmA' : (A'.map (· ^ 2)).sum = (a + 1) ^ 2 + (b - 1) ^ 2 + (rest.map (· ^ 2)).sum := by
    rw [(hp'.map (· ^ 2)).sum_eq]; simp only [List.map_cons, List.sum_cons]; ring
  refine ⟨A', hs', ?_, ?_, ?_⟩
  · rw [hmA, hmA']; linarith [sq_dec hb]
  · intro x hx
    have hx2 : x ∈ (a + 1) :: (b - 1) :: rest := (hp'.mem_iff).mp hx
    simp only [List.mem_cons] at hx2
    rcases hx2 with rfl | rfl | hxr
    · omega
    · omega
    · exact hfloor x ((hp.mem_iff).mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hxr)))
  · rw [hp'.length_eq, hp.length_eq]; simp

/-- **Single-hub reachability of the balanced form.**  Every all-arms-`>=3` hub (in the
    many-arm regime) reaches a balanced-to-within-one hub by a chain of `TransferStep`s. -/
theorem single_hub_reaches_balanced {arms : List ℕ} {c : ℕ}
    (hfloor : ∀ x ∈ arms, 3 ≤ x) (hd6 : 6 ≤ arms.length + c) :
    ∃ arms_bal, ArmBalanced arms_bal ∧
      Relation.ReflTransGen TransferStep [(arms, c)] [(arms_bal, c)] := by
  suffices H : ∀ n (arms : List ℕ), (arms.map (· ^ 2)).sum ≤ n →
      (∀ x ∈ arms, 3 ≤ x) → 6 ≤ arms.length + c →
      ∃ arms_bal, ArmBalanced arms_bal ∧
        Relation.ReflTransGen TransferStep [(arms, c)] [(arms_bal, c)] by
    exact H _ arms le_rfl hfloor hd6
  intro n
  induction n with
  | zero =>
    intro arms hle hfloor hd6
    refine ⟨arms, ?_, Relation.ReflTransGen.refl⟩
    by_contra hbal
    obtain ⟨s', hstep⟩ := transferStep_progress hfloor hbal hd6
    obtain ⟨arms', _, hlt, _, _⟩ := transferStep_dest hfloor hstep
    omega
  | succ n ih =>
    intro arms hle hfloor hd6
    by_cases hbal : ArmBalanced arms
    · exact ⟨arms, hbal, Relation.ReflTransGen.refl⟩
    · obtain ⟨s', hstep⟩ := transferStep_progress hfloor hbal hd6
      obtain ⟨arms', rfl, hlt, hfloor', hlen⟩ := transferStep_dest hfloor hstep
      have hd6' : 6 ≤ arms'.length + c := hlen ▸ hd6
      have hle' : (arms'.map (· ^ 2)).sum ≤ n := by omega
      obtain ⟨arms_bal, hb, hreach⟩ := ih arms' hle' hfloor' hd6'
      exact ⟨arms_bal, hb, Relation.ReflTransGen.head hstep hreach⟩

/-- **Single-hub `Hnorm`.**  An arbitrary single-hub arm distribution (all arms `>= 3`, in the
    many-arm regime) is `Aobj`-dominated by the SAME arms rebalanced to within one.  This is the
    single-hub case of the normalization layer: the balanced star dominates its unbalanced
    variants. -/
theorem single_hub_Hnorm {arms : List ℕ} {c : ℕ}
    (hfloor : ∀ x ∈ arms, 3 ≤ x) (hd6 : 6 ≤ arms.length + c) :
    ∃ arms_bal, ArmBalanced arms_bal ∧
      Aobj (backboneU [(arms, c)]) ≤ Aobj (backboneU [(arms_bal, c)]) := by
  obtain ⟨arms_bal, hbal, hreach⟩ := single_hub_reaches_balanced hfloor hd6
  exact ⟨arms_bal, hbal, Aobj_transferStar_le hreach⟩

end Step3
end R3Cert
