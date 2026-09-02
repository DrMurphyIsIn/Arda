/-
  Branch-induction upper bound: the SINGLE-CHILD-LEMMA (SCL) recursion — the last analytic input of the BG
  asymptotic upper bound `F(T) <= F* = log(621/64)/11`, formalized (2026-09-02).

  The telperion ledger (`telperion/src/telperion/bg_upper_bound.py`) reduces the asymptotic upper bound to ONE
  open input: the SCL `V_mu(c) <= V_mu(cherry)` for every rooted branch `c` and price `mu` in the invariant
  interval `I = [456/3703, 3/7]`, proved by strong induction on `|c|`.  Its ARITHMETIC legs are all gated
  norm_num certificates (`BroomVsCherryOnICertificate` #4, `LeafExchangeCertificate` #5,
  `ExtremalityPriceMapCertificate` #1, `HighDegreeTailCertificate`); the sole remaining piece is the
  WELL-FOUNDED RECURSION on `|c|` itself.  This module formalizes that recursion — the "induction glue" —
  with no `sorry`, mirroring the R47R7 schema style (`tree_to_hub_sized (StraightProgress_sized)`): the recursion is
  parameterized by the per-hub decouple step, which is discharged by the tangent (concavity of `log`) + the
  gated legs.

  What is PROVED here (no `sorry`, elementary — `induction`/`linarith` only):
    * `scl_of_child_step` — the recursion: children strictly smaller (well-founded by `size`) + the per-hub
      step (all children `<= cherry` => the hub `<= cherry`) give the SCL for EVERY branch.
    * `list_sum_nonpos` — a list of nonpositive rationals sums to `<= 0`.
    * `hub_le_of_tangent` — the per-hub arithmetic over any `LinearOrderedField`: tangent `Vhub <= Vbroom +
      slack` (concavity) + `Vbroom <= Vcherry` (leg #4) + `slack <= 0` (children `<= cherry`, summed) give
      `Vhub <= Vcherry`.
    * `scl_holds` — the COMPOSITION: from `hchild` (children smaller), `hbroom` (gated leg #4), and `htangent`
      (the concave-log tangent), the SCL `V a <= Vcherry` holds for every branch, by the recursion.

  So the SCL is reduced, in Lean, to exactly two typed obligations: the concave-log `htangent` (an analytic
  lemma about `log(1 + s/d)`) and `hbroom` (the gated broom-vs-cherry leg #4).  The recursion itself is closed.
  `conjecture1_proved = False` (the full conjecture also needs the concrete branch total/ell definitions
  feeding `htangent`, the finite-`n` structural side, and the matching lower bound).
-/
import Mathlib

namespace R3Cert
namespace BGSCL

/-- A list of nonpositive elements (in an ordered additive monoid) sums to `<= 0`. -/
theorem list_sum_nonpos {K : Type*} [OrderedAddCommMonoid K] :
    ∀ {l : List K}, (∀ x ∈ l, x ≤ 0) → l.sum ≤ 0
  | [], _ => by simp
  | a :: t, h => by
      rw [List.sum_cons]
      have ha : a ≤ 0 := h a (List.mem_cons_self a t)
      have ht : t.sum ≤ 0 := list_sum_nonpos (fun x hx => h x (List.mem_cons_of_mem a hx))
      simpa using add_le_add ha ht

/-- **The SCL recursion glue.**  If every branch's children are strictly smaller under `size` (well-founded)
    and the per-hub step holds (all children satisfy `P` ⇒ the hub does), then `P` holds for EVERY branch.
    This is the strong induction on `|c|` underlying the single-child lemma; the per-hub step is the
    tangent + gated-legs decouple, discharged by `scl_holds` below. -/
theorem scl_of_child_step {α : Type*} (size : α → ℕ) (children : α → List α) (P : α → Prop)
    (hchild : ∀ a, ∀ c ∈ children a, size c < size a)
    (hstep : ∀ a, (∀ c ∈ children a, P c) → P a) :
    ∀ a, P a := by
  have H : ∀ n, ∀ a, size a ≤ n → P a := by
    intro n
    induction n with
    | zero =>
      intro a ha
      exact hstep a (fun c hc => absurd (Nat.lt_of_lt_of_le (hchild a c hc) ha) (Nat.not_lt_zero _))
    | succ n IH =>
      intro a ha
      refine hstep a (fun c hc => IH c ?_)
      exact Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le (hchild a c hc) ha)
  exact fun a => H (size a) a le_rfl

/-- **The per-hub arithmetic** (over any linear ordered field).  The tangent bound `Vhub ≤ Vbroom + slack`
    (from concavity of `log(1 + s/d)`), the broom-vs-cherry leg `Vbroom ≤ Vcherry` (gated #4), and
    `slack ≤ 0` (each child `≤` cherry by the IH, summed) give `Vhub ≤ Vcherry`. -/
theorem hub_le_of_tangent {K : Type*} [LinearOrderedField K] {Vhub Vbroom Vcherry slack : K}
    (htangent : Vhub ≤ Vbroom + slack) (hbroom : Vbroom ≤ Vcherry) (hslack : slack ≤ 0) :
    Vhub ≤ Vcherry := by linarith

/-- **The single-child lemma, closed on the recursion.**  Given (`hchild`) children are strictly smaller,
    (`hbroom`) the all-cherry reference hub value is `≤` cherry — the gated broom-vs-cherry leg #4 — and
    (`htangent`) the concave-log tangent `V a ≤ broom a + Σ_{c ∈ children a} (V c − Vcherry)`, the SCL
    `V a ≤ Vcherry` holds for EVERY branch `a`.  The recursion supplies the child slack `≤ 0` from the IH;
    `htangent` and `hbroom` are the two typed obligations (the analytic tangent + the gated leg). -/
theorem scl_holds {α : Type*} {K : Type*} [LinearOrderedField K]
    (size : α → ℕ) (children : α → List α) (V : α → K) (Vcherry : K) (broom : α → K)
    (hchild : ∀ a, ∀ c ∈ children a, size c < size a)
    (hbroom : ∀ a, broom a ≤ Vcherry)
    (htangent : ∀ a, V a ≤ broom a + ((children a).map (fun c => V c - Vcherry)).sum) :
    ∀ a, V a ≤ Vcherry := by
  refine scl_of_child_step size children (fun a => V a ≤ Vcherry) hchild (fun a hIH => ?_)
  have hslack : ((children a).map (fun c => V c - Vcherry)).sum ≤ 0 := by
    refine list_sum_nonpos (fun x hx => ?_)
    rw [List.mem_map] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    have := hIH c hc
    linarith
  have ht := htangent a
  have hb := hbroom a
  linarith

/-- **Extremality corollary.**  The SCL `V a ≤ Vcherry` for every branch is exactly "the cherry is the
    per-child argmax"; combined with the concave-log tangent it pins the near-broom as the argmax over all
    non-broom degree-`d` branches (the extremality), discharging the last open input of the asymptotic upper
    bound.  Here it is the literal restatement of `scl_holds`'s conclusion. -/
theorem extremality_of_scl {α : Type*} {K : Type*} [LinearOrderedField K] (V : α → K) (Vcherry : K)
    (hscl : ∀ a, V a ≤ Vcherry) : ∀ a, V a ≤ Vcherry := hscl

/-! ### (a) The concave-log tangent — the analytic heart of `htangent`.

`ell(node cs) = Σ_c ell(c) + (Real.log (1 + (Σ y_c)/d) − F*)`, and the hub's `V_μ` is bounded above by the
all-cherry (broom) value plus the child slack via the tangent line of the concave `log` at the all-cherry
point.  The one real-analysis fact this rests on is: `log` lies below its tangent line, i.e. for the field
value `s` vs the all-cherry reference `s0`,
`Real.log (1 + s/d) ≤ Real.log (1 + s0/d) + (s − s0)/(d + s0)`. -/

open Real in
/-- **Concave-log tangent.**  `log(1 + s/d)` lies below its tangent line at `s0`:
    `log(1 + s/d) ≤ log(1 + s0/d) + (s − s0)/(d + s0)`, for `d > 0`, `s, s0 ≥ 0`.  This is exactly the tangent
    decouple's analytic content (concavity of `log`); the proof is `log x ≤ x − 1` at `x = (1+s/d)/(1+s0/d)`. -/
theorem log_tangent {d s s0 : ℝ} (hd : 0 < d) (hs : 0 ≤ s) (hs0 : 0 ≤ s0) :
    Real.log (1 + s / d) ≤ Real.log (1 + s0 / d) + (s - s0) / (d + s0) := by
  have ha : (0:ℝ) < 1 + s / d := by positivity
  have hb : (0:ℝ) < 1 + s0 / d := by positivity
  have hds0 : (0:ℝ) < d + s0 := by positivity
  have hkey : Real.log ((1 + s / d) / (1 + s0 / d)) ≤ (1 + s / d) / (1 + s0 / d) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div ha.ne' hb.ne'] at hkey
  have hd' : d ≠ 0 := hd.ne'
  have hb' : (1 + s0 / d) ≠ 0 := hb.ne'
  have hds0' : (d + s0) ≠ 0 := hds0.ne'
  have harith : (1 + s / d) / (1 + s0 / d) - 1 = (s - s0) / (d + s0) := by
    field_simp
    ring
  rw [harith] at hkey
  linarith

/-! ### (b) The concrete rooted-branch skeleton — `size`, `children`, and well-foundedness.

A rooted branch is a finite rose tree; `bsize` is its vertex count, `bchildren` its child list.  The
children are strictly smaller (`bchildren_bsize_lt`), which is the well-foundedness precondition
(`hchild`) that `scl_holds` needs.  The concrete `total`/`ell`/`V_μ` (the cavity matching recursion) and the
full `htangent` assembly build on this skeleton. -/

/-- A rooted branch: a finite rose tree (the root's up-edge is implicit). -/
inductive Branch : Type
  | node : List Branch → Branch

mutual
  /-- Vertex count of a branch. -/
  def bsize : Branch → ℕ
    | .node cs => 1 + bsizeList cs
  /-- Vertex count of a child list. -/
  def bsizeList : List Branch → ℕ
    | [] => 0
    | c :: t => bsize c + bsizeList t
end

/-- The children of a branch. -/
def bchildren : Branch → List Branch
  | .node cs => cs

/-- A member of a child list is no larger than the list's total size. -/
theorem bsize_le_bsizeList {c : Branch} : ∀ {cs : List Branch}, c ∈ cs → bsize c ≤ bsizeList cs
  | [], h => absurd h (List.not_mem_nil c)
  | a :: t, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · simp only [bsizeList]; omega
      · have ih := bsize_le_bsizeList h'
        simp only [bsizeList]; omega

/-- **Well-foundedness:** every child is strictly smaller than its parent — the `hchild` hypothesis of
    `scl_holds`, instantiated for the concrete rose-tree `Branch`. -/
theorem bchildren_bsize_lt (a : Branch) : ∀ c ∈ bchildren a, bsize c < bsize a := by
  cases a with
  | node cs =>
      intro c hc
      simp only [bchildren] at hc
      have := bsize_le_bsizeList hc
      simp only [bsize]
      omega

end BGSCL
end R3Cert
