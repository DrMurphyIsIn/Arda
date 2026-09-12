/-
  Statements.BGDefs -- vocabulary mirror for the BG missions registry.  NOT a node statement.

  Every definition below is a VERBATIM line-range copy from the proof/ R3Cert island
  (toolchain leanprover/lean4:v4.32.0), source module cited above each block; the copies are
  regenerated/diffed by missions/bg/build_bgdefs.py.  Where the original lives in section
  variables, the section is reproduced verbatim.  This file exists so that node statement
  files elaborate standalone against Mathlib; the *registry statements* are the node files,
  which the verify gate matches against the real proof/ artifacts by normalized containment.

  The final PROVISIONAL block (hubCount*) is registry-only vocabulary (no proof/ counterpart)
  used by the DRAFT node BG_r2_multihub_maximality; it is NOT part of any proved statement.
-/
import Mathlib

namespace R3Cert

-- ===== ExactCruxes.lean:70 =====
noncomputable def rhoB : ℝ := (621 / 64 : ℝ) ^ ((1 : ℝ) / 11)

-- ===== Sweep.lean:24,26 =====
noncomputable def Lval : ℝ := Real.log (621 / 64) / 11
noncomputable def omegaVal : ℝ := Real.log (3 / 2) - 2 * Lval

-- ===== Potential.lean:33,37-40 =====
noncomputable def T0 : ℝ := rhoB - 1
noncomputable def Pval (y : ℝ) : ℝ :=
  if y = 1 / 3 then -omegaVal
  else if y = 1 then Lval
  else (11 / 50) * max 0 (y - T0)

-- ===== Reach.lean:24-25,27-35,160-178 =====
inductive Branch where
  | node (c : ℕ) (children : List Branch)

mutual
/-- Branch cavity `mu = 3 / (3 + 3·n_ch + 4 c + 3 S)`, `S` = sum of child cavities. -/
noncomputable def cav : Branch → ℝ
  | .node c ch => 3 / (3 + 3 * (ch.length : ℝ) + 4 * (c : ℝ) + 3 * cavSum ch)
/-- Sum of child cavities. -/
noncomputable def cavSum : List Branch → ℝ
  | [] => 0
  | b :: rest => cav b + cavSum rest
end

noncomputable def zc (c nch : ℕ) : ℝ := 3 / (3 * ((nch : ℝ) + 1 + (c : ℝ)) + (c : ℝ))

/-- `a(d,c) = (3/2)^c · (1 + c/(3d)) / rhoB^(1+2c)`, `d = n_ch + 1 + c`. -/
noncomputable def ac (c nch : ℕ) : ℝ :=
  (3 / 2) ^ c * (1 + (c : ℝ) / (3 * ((nch : ℝ) + 1 + (c : ℝ)))) / rhoB ^ (1 + 2 * c)

/-- The root increment `e_root = log a(d,c) + log(1 + z·S)`, `S = Σ child cavities`. -/
noncomputable def eroot (c : ℕ) (ch : List Branch) : ℝ :=
  Real.log (ac c ch.length) + Real.log (1 + zc c ch.length * cavSum ch)

mutual
/-- The branch log-amplitude `log Φ(B) = Σ_children log Φ + e_root`. -/
noncomputable def logPhi : Branch → ℝ
  | .node c ch => logPhiSum ch + eroot c ch
/-- Sum of child log-amplitudes. -/
noncomputable def logPhiSum : List Branch → ℝ
  | [] => 0
  | b :: rest => logPhi b + logPhiSum rest
end

-- ===== NearStar.lean:43,46 =====
def armB : Branch := Branch.node 0 [Branch.node 0 []]
def nearStarB (c k : ℕ) : Branch := Branch.node c (List.replicate k armB)

-- ===== Plainify.lean:182-189 =====
mutual
def IsPlain : Branch → Prop
  | .node c ch => c = 0 ∧ IsPlainList ch
def IsPlainList : List Branch → Prop
  | [] => True
  | b :: rest => IsPlain b ∧ IsPlainList rest
end


-- ===== PotentialBound.lean:24-28 =====
def ValidPotentialPlain (P : ℝ → ℝ) : Prop :=
  (∀ m, 0 ≤ P m) ∧
    (∀ ch : List Branch, IsPlainList ch →
      eroot 0 ch ≤ (ch.map (fun b => P (cav b))).sum - P (cav (Branch.node 0 ch)))


-- ===== CavityTree.lean:31-49 (RTree + partition functions) =====
inductive RTree where
  | node : List (ℝ × RTree) → RTree

namespace RTree

/- `Zopen t` / `Ztot t` -- the matching partition functions of the rooted tree `t` (root unmatched / all
   matchings); `Popen cs` = `∏ Ztot(child)`, `Matched cs` = the leave-one-out matched sum (division-free). -/
mutual
  def Zopen : RTree → ℝ
    | .node cs => Popen cs
  def Ztot : RTree → ℝ
    | .node cs => Popen cs + Matched cs
  def Popen : List (ℝ × RTree) → ℝ
    | [] => 1
    | (_, c) :: rest => Ztot c * Popen rest
  def Matched : List (ℝ × RTree) → ℝ
    | [] => 0
    | (w, c) :: rest => w * Zopen c * Popen rest + Ztot c * Matched rest
end
end RTree

-- ===== Matching.lean:57-64 (lapl, in its verbatim section context) =====
section Combinatorial
open Equiv Function
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The Laplacian matrix over ℝ: diagonal `deg`, `-1` on edges, `0` elsewhere. -/
noncomputable def lapl : Matrix V V ℝ :=
  fun i j => if i = j then (G.degree i : ℝ) else if G.Adj i j then -1 else 0

end Combinatorial

namespace Step3

open RTree

-- ===== BridgeStep3.lean:85-100 (address realization) =====
mutual
/-- Realize an `RTree` rooted at address `a` as an edge list (address vertices), root edges first. -/
def rEdges : List ℕ → RTree → List (List ℕ × List ℕ × ℝ)
  | a, .node cs => rRoot a 0 cs ++ rSub a 0 cs
/-- The root's incident edges `(a, i :: a, w)` for each child `i`. -/
def rRoot : List ℕ → ℕ → List (ℝ × RTree) → List (List ℕ × List ℕ × ℝ)
  | _, _, [] => []
  | a, i, (w, _) :: rest => (a, i :: a, w) :: rRoot a (i + 1) rest
/-- The children's subtree edges (rooted at `i :: a`). -/
def rSub : List ℕ → ℕ → List (ℝ × RTree) → List (List ℕ × List ℕ × ℝ)
  | _, _, [] => []
  | a, i, (_, c) :: rest => rEdges (i :: a) c ++ rSub a (i + 1) rest
end

/-- The realized edge list of a whole tree (root address `[]`). -/
def realize (t : RTree) : List (List ℕ × List ℕ × ℝ) := rEdges [] t

-- ===== BridgeStep3e.lean:31,34,47-48,50-52,55,58-70 (address graph) =====
abbrev AEdge := List ℕ × List ℕ × ℝ
def vertsOf (E : List AEdge) : List (List ℕ) := E.map Prod.fst ++ E.map (fun e => e.2.1)
def HasKey (E : List AEdge) (a b : List ℕ) : Prop :=
  ∃ e ∈ E, (e.1 = a ∧ e.2.1 = b) ∨ (e.1 = b ∧ e.2.1 = a)
theorem HasKey.symm {E : List AEdge} {a b : List ℕ} (h : HasKey E a b) : HasKey E b a := by
  obtain ⟨e, he, hor⟩ := h
  exact ⟨e, he, hor.symm⟩
abbrev AVert (E : List AEdge) := {a : List ℕ // a ∈ (vertsOf E).toFinset}
instance hasKey_decidable (E : List AEdge) (a b : List ℕ) : Decidable (HasKey E a b) :=
  decidable_of_iff (∃ e ∈ E, (e.1 = a ∧ e.2.1 = b) ∨ (e.1 = b ∧ e.2.1 = a)) Iff.rfl

def aGraph (E : List AEdge) : SimpleGraph (AVert E) where
  Adj u v := u ≠ v ∧ HasKey E u.val v.val
  symm := ⟨fun u v h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun u h => h.1 rfl⟩

theorem aGraph_adj (E : List AEdge) (u v : AVert E) :
    (aGraph E).Adj u v ↔ u ≠ v ∧ HasKey E u.val v.val := Iff.rfl

instance aGraph_adjDecidable (E : List AEdge) : DecidableRel (aGraph E).Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ HasKey E u.val v.val))

-- ===== R47Tree.lean:33-34,37-38,45-57,132 (UTree, realization, Aobj) =====
inductive UTree where
  | node : List UTree → UTree

def udeg : UTree → ℕ
  | .node cs => cs.length + 1

mutual
/-- Realize a NON-ROOT subtree (its own degree is `udeg`). -/
noncomputable def dtSub : UTree → RTree
  | .node cs => RTree.node (dtChildren (cs.length + 1) cs)
/-- The weighted children of a node of full degree `d`. -/
noncomputable def dtChildren : ℕ → List UTree → List (ℝ × RTree)
  | _, [] => []
  | d, K :: rest => (1 / ((d : ℝ) * (udeg K : ℝ)), dtSub K) :: dtChildren d rest
end

/-- Realize the ROOT (true degree = child count, no parent edge). -/
noncomputable def dtRealize : UTree → RTree
  | .node cs => RTree.node (dtChildren cs.length cs)

noncomputable def Aobj (t : UTree) : ℝ := Ztot (dtRealize t)

-- ===== R47HubState.lean:30,33,36,40-46 (hub states) =====
def cherryU : UTree := UTree.node [UTree.node []]
def armU (j : ℕ) : UTree := UTree.node (List.replicate j cherryU)
abbrev Hub := List ℕ × ℕ
def backboneU : List Hub → UTree
  | [] => UTree.node []
  | (arms, c) :: rest =>
      UTree.node (arms.map armU ++ List.replicate c cherryU ++
        (match rest with
         | [] => []
         | _ :: _ => [backboneU rest]))

-- ===== R47Backbone.lean:24-26 (tailU) =====
def tailU : List Hub → List UTree
  | [] => []
  | h :: t => [backboneU (h :: t)]

-- ===== R47StepSize.lean:30-38,83,86 (sizes) =====
mutual
/-- Number of vertices of a bare rooted tree. -/
def usize : UTree → ℕ
  | .node cs => 1 + usizeList cs
/-- Total vertex count of a child list. -/
def usizeList : List UTree → ℕ
  | [] => 0
  | K :: rest => usize K + usizeList rest
end

def hubSize (h : Hub) : ℕ := 1 + (h.1.length + 2 * h.1.sum) + 2 * h.2
def stateSize (s : List Hub) : ℕ := (s.map hubSize).sum

-- ===== R47Step.lean:41,45 / R47Capped.lean:39 (families) =====
def BalancedArms (arms : List ℕ) : Prop := ∀ j ∈ arms, j = 4 ∨ j = 5
def Balanced (s : List Hub) : Prop := ∀ h ∈ s, BalancedArms h.1 ∧ h.2 ≤ 5
def Capped (s : List Hub) : Prop := ∀ h ∈ s, 5 ≤ h.1.length

-- ===== R47OrderedStep.lean:43-58 (the ordered merge relation) =====
inductive OrderedStep : List Hub → List Hub → Prop
  | merge {armsA : List ℕ} {cA : ℕ} {armsB others : List ℕ} {cb : ℕ} {rest : List Hub}
      (hcb : cb ≤ 5)
      (hsplit : armsB.Perm (List.replicate (5 - cb) 5 ++ others))
      (hord : armsB.length + (tailU rest).length ≤ armsA.length) :
      OrderedStep ((armsA, cA) :: (armsB, cb) :: rest)
        ((armsA ++ List.replicate (5 - cb) 4 ++ others ++ [5], cA) :: rest)
  | mergeRev {armsA othersA : List ℕ} {cA : ℕ} {armsB : List ℕ} {cb : ℕ}
      {rest : List Hub}
      (hcA : cA ≤ 5)
      (hsplit : armsA.Perm (List.replicate (5 - cA) 5 ++ othersA))
      (hord : armsA.length + 1 ≤ armsB.length + (tailU rest).length) :
      OrderedStep ((armsA, cA) :: (armsB, cb) :: rest)
        ((armsB ++ List.replicate (5 - cA) 4 ++ othersA ++ [5], cb) :: rest)
  | tail {h : Hub} {s s' : List Hub} :
      OrderedStep s s' → OrderedStep (h :: s) (h :: s')

-- ===== PROVISIONAL (registry-only; no proof/ counterpart; used only by the DRAFT node
-- BG_r2_multihub_maximality).  Hub count of a bare rooted tree: vertices of structural
-- degree >= 3 (root degree = child count; non-root degree = children + parent edge). =====
mutual
def hubCountRoot : UTree → ℕ
  | .node cs => (if 3 ≤ cs.length then 1 else 0) + hubCountList cs
def hubCountSub : UTree → ℕ
  | .node cs => (if 3 ≤ cs.length + 1 then 1 else 0) + hubCountList cs
def hubCountList : List UTree → ℕ
  | [] => 0
  | K :: rest => hubCountSub K + hubCountList rest
end

end Step3
end R3Cert

-- ===== GStepCore.lean:25 / CappedJointConfig.lean:33-46 / CappedJointAchievable.lean:30 =====
namespace R3Cert.GStepCore

def W : ℚ := 64 / 621
end R3Cert.GStepCore

namespace R3Cert.CappedJointConfig

open R3Cert.GStepCore

def glemma (μ : ℚ) : ℚ := W ^ 2 * (5 / 3) ^ 11 / (1 + μ / 3) ^ 11
def master_ub (μ : ℚ) : ℚ := W * (3 / (2 + μ)) ^ 11
def Bcap (μ : ℚ) : ℚ := min (master_ub μ) (min (glemma μ) 1)
def baseOf (l : List ℚ) : ℚ :=
  (3 * ((l.length : ℚ) + 1) + 3 * l.sum + 1) / (3 * ((l.length : ℚ) + 1))
def prodBcap (l : List ℚ) : ℚ := (l.map Bcap).prod
def Achievable (μ : ℚ) : Prop := 0 < μ ∧ (μ ≤ 1 / 2 ∨ μ = 1)

end R3Cert.CappedJointConfig
