/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
R2Rigidity.lean — MIRRORMERE Wave-2 W2b (qc2-defect), the R2 DEFECT-RIGIDITY RUNG.

`DefectDictionary.defect_le_offline_pairs` proves the DETECTION half of the dictionary:
`defect A ≤ p` (the off-line pair count is an UPPER bound on the negative index — a snapshot with
`p` off-line pairs cannot leak more than `p` negative directions). This file proves the RIGIDITY
half, the CONVERSE inequality `p ≤ defect A`: the instrument does not merely detect off-line pairs,
it COUNTS them. Combined, `defect A = p` exactly — the R2 rung of `QC_RIGIDITY_MEMO.md` §R2.

## The honest independence hypothesis (why `p ≤ defect` is NOT free)

`defect A ≤ p` is unconditional because the negative channel `imPart = Σ 2m y_j y_jᵀ` has rank ≤ p by
construction (each pair adds one rank-one `y_j y_jᵀ`). The converse can FAIL: the off-line `y_j`
directions could be neutralized by the on-line/real positive channels `onPart + rePart`, or be
linearly dependent, so that `A` is NOT negative on the space they span and the negative index falls
below `p`. So `p ≤ defect` requires an explicit CHECKABLE non-degeneracy input, and the whole point
of the R2 rung is to state it honestly and NOT smuggle in RH strength.

The condition we settled on — `NegativeWitness` — is the cleanest sufficient one that is directly
verifiable for a concrete finite configuration:

    there is a submodule `W` of dimension `p` on which `A` is NEGATIVE DEFINITE
    (equivalently `-A` is positive definite, `PosDefOn (-A) W`).

This is honest for three reasons:
  * It is FINITE and CHECKABLE: for a concrete block one exhibits `W` (e.g. the span of the off-line
    coordinate axes) and verifies `⟨x, A x⟩ < 0` for `x ∈ W \ {0}` by kernel arithmetic — exactly
    what `BraggDefect.defect_witness_offline` already does for the one-pair block (⟨e₁, A e₁⟩ < 0).
  * It is NOT RH in disguise: it asserts the off-line pairs DO leak `p` independent negative
    directions in THIS finite window; it says nothing about zeros outside the window, nothing about
    the comb being crystalline, and it can be FALSE (a config with `p` off-line pairs whose `y_j`
    collapse has a smaller such `W` — and then, correctly, `defect < p`).
  * It matches the paper's inertia machinery exactly: `finrank_le_posIndex_of_posDefOn` (Sylvester's
    hard direction, §3) applied to `-A` turns a `p`-dimensional negative-definite subspace directly
    into `p ≤ n₊(-A) = defect A`.

The `defect_le_offline_pairs` side then squeezes: with a `PairDecomp` supplying `defect ≤ p` and a
`NegativeWitness` of dimension `p` supplying `p ≤ defect`, we get `defect = p` two-sided.

## Provenance

Uses only the §3 `RHLinalg` prelude (`finrank_le_posIndex_of_posDefOn`) and the row-(a)/row-(c)
machinery of `DefectDictionary.lean`. ζ-free, finite. conjecture1_proved = False — this is an
inertia counting fact about finite Hermitian compressions and one (resp. two) synthetic pair(s),
and proves NOTHING new about the Riemann Hypothesis.
-/
import DefectDictionary

noncomputable section

open Matrix Finset Submodule RHLinalg
open scoped ComplexOrder BigOperators

namespace DefectDictionary

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Section 1. The abstract rigidity theorem

A single strictly-negative-definite subspace of dimension `p` forces `defect ≥ p`. This is the exact
dual of `finrank_le_posIndex_of_posDefOn` read on `-A`: it says the negative index counts at least
the dimension of any subspace on which `A` is negative definite. -/

/-- **A negative-definite witness of dimension `p`**: a submodule `W` on which `A` is negative
definite (`-A` positive definite) together with the record that `dim W = p`. This is the honest,
finite, checkable rigidity input — the `p` independent negative directions the off-line pairs leak.
-/
structure NegativeWitness {A : Matrix n n 𝕜} (hA : A.IsHermitian) (p : ℕ) where
  /-- the subspace on which `A` is negative definite -/
  W : Submodule 𝕜 (n → 𝕜)
  /-- `-A` is positive definite on `W` (i.e. `A` is negative definite there) -/
  posDefOn_neg : PosDefOn (-A) W
  /-- `W` has dimension exactly `p` -/
  finrank_eq : Module.finrank 𝕜 W = p

/-- **The rigidity direction (abstract).** If `A` is negative definite on a `p`-dimensional subspace
then `p ≤ defect A`. Dual to `finrank_le_posIndex_of_posDefOn` applied to `-A`: a `p`-dimensional
negative-definite subspace is a `p`-dimensional positive-definite subspace of `-A`, so
`p = dim W ≤ n₊(-A) = defect A`. The off-line pairs are COUNTED, not merely detected. -/
theorem offline_pairs_le_defect {A : Matrix n n 𝕜} (hA : A.IsHermitian) {p : ℕ}
    (hwit : NegativeWitness hA p) :
    p ≤ defect hA := by
  unfold defect
  calc p = Module.finrank 𝕜 hwit.W := hwit.finrank_eq.symm
    _ ≤ posIndex hA.neg := finrank_le_posIndex_of_posDefOn hA.neg hwit.posDefOn_neg

/-- **A one-dimensional negative witness from a single negative direction.** The concrete builder for
the `p = 1` instantiation: a single vector `x₀ ≠ 0` with `hermForm A x₀ < 0` (a strictly-negative
direction — exactly `BraggDefect.defect_witness_offline`'s `⟨e₁, A e₁⟩ < 0`) yields a
`NegativeWitness hA 1` on the line it spans. This is the `NegativeWitness` counterpart of
`defect_ge_one_of_neg_dir`. -/
def NegativeWitness.ofNegDir {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {x₀ : n → 𝕜} (hx₀ : x₀ ≠ 0) (hneg : hermForm A x₀ < 0) :
    NegativeWitness hA 1 where
  W := Submodule.span 𝕜 {x₀}
  posDefOn_neg := by
    intro x hx hxne
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨c, rfl⟩ := hx
    have hc : c ≠ 0 := by rintro rfl; simp at hxne
    rw [hermForm_neg, hermForm_smul_sq]
    have : (0 : ℝ) < ‖c‖ ^ 2 := by positivity
    nlinarith [this, hneg]
  finrank_eq := finrank_span_singleton hx₀

/-- **A `k`-dimensional negative witness from `k` independent negative directions.** The scalable
builder for `p = k`: a linearly independent family `v : Fin k → (n → 𝕜)` whose span is
negative-definite for `A` (`PosDefOn (-A)`) is a `NegativeWitness hA k`. The two hypotheses are
exactly the honest, checkable content of the rigidity condition for `k` off-line pairs — `k`
genuinely independent leaked negative directions — and neither is RH strength: linear independence
and negativity-on-the-span are both finite kernel checks for a concrete block. -/
def NegativeWitness.ofLinearIndependent {A : Matrix n n 𝕜} (hA : A.IsHermitian) {k : ℕ}
    {v : Fin k → (n → 𝕜)} (hli : LinearIndependent 𝕜 v)
    (hpd : PosDefOn (-A) (Submodule.span 𝕜 (Set.range v))) :
    NegativeWitness hA k where
  W := Submodule.span 𝕜 (Set.range v)
  posDefOn_neg := hpd
  finrank_eq := (finrank_span_eq_card hli).trans (Fintype.card_fin k)

/-! ## Section 2. The two-sided count `defect = p`

Combine the rigidity direction with the existing detection direction `defect ≤ p` of a `PairDecomp`.
When a compression carries BOTH a `PairDecomp` (whose `imPart` rank ≤ `p` bounds the defect above)
AND a `NegativeWitness` of dimension `p` (bounding it below), the defect equals `p` on the nose. -/

/-! ### A single-pair block is crystalline up to defect one

The concrete upper bound specialised to a bare `pairBlock x y = x xᵀ − y yᵀ`: its negative channel is
the single rank-one `y yᵀ`, so `defect ≤ 1`. This is `defect_le_offline_pairs` for `p = 1` without
having to package a full `PairDecomp` — it lets the one-pair instantiation squeeze to `defect = 1`
directly. -/

/-- **A single off-line pair block has defect ≤ 1.** `defect (x xᵀ − y yᵀ) = n₊(y yᵀ − x xᵀ) ≤
rank (y yᵀ) ≤ 1`: the pure negative channel of one pair is a single rank-one term. -/
theorem defect_pairBlock_le_one {d : Type*} [Fintype d] [DecidableEq d] (x y : d → ℝ) :
    defect (pairBlock_isHermitian x y) ≤ 1 := by
  have hyy : (vecMulVec y y).PosSemidef := by
    have h := posSemidef_vecMulVec_self_star y
    rwa [show (star y) = y from rfl] at h
  have hxx : (vecMulVec x x).PosSemidef := by
    have h := posSemidef_vecMulVec_self_star x
    rwa [show (star x) = x from rfl] at h
  have hstep := posIndex_sub_le_rank hyy hxx
  have hrk : (vecMulVec y y).rank ≤ 1 := Matrix.rank_vecMulVec_le y y
  unfold defect
  rw [posIndex_congr (pairBlock_isHermitian x y).neg
        (hyy.isHermitian.sub hxx.isHermitian) (by unfold pairBlock; rw [neg_sub])]
  exact hstep.trans hrk

/-- The two-pair block `x₁x₁ᵀ + x₂x₂ᵀ − y₁y₁ᵀ − y₂y₂ᵀ` — two off-line pairs' worth of channels. -/
def twoPairBlock {d : Type*} (x₁ y₁ x₂ y₂ : d → ℝ) : Matrix d d ℝ :=
  vecMulVec x₁ x₁ + vecMulVec x₂ x₂ - (vecMulVec y₁ y₁ + vecMulVec y₂ y₂)

lemma twoPairBlock_isHermitian {d : Type*} [Fintype d] [DecidableEq d] (x₁ y₁ x₂ y₂ : d → ℝ) :
    (twoPairBlock x₁ y₁ x₂ y₂).IsHermitian := by
  have hpsd (v : d → ℝ) : (vecMulVec v v).PosSemidef := by
    have h := posSemidef_vecMulVec_self_star v
    rwa [show (star v) = v from rfl] at h
  exact ((hpsd x₁).add (hpsd x₂)).isHermitian.sub ((hpsd y₁).add (hpsd y₂)).isHermitian

/-- **A two-pair block has defect ≤ 2.** `defect = n₊((y₁y₁ᵀ+y₂y₂ᵀ) − (x₁x₁ᵀ+x₂x₂ᵀ)) ≤
rank(y₁y₁ᵀ) + rank(y₂y₂ᵀ) ≤ 2` via `posIndex` subadditivity — the two independent rank-one negative
channels. Scales the single-pair `defect_pairBlock_le_one` to two pairs. -/
theorem defect_twoPairBlock_le_two {d : Type*} [Fintype d] [DecidableEq d] (x₁ y₁ x₂ y₂ : d → ℝ) :
    defect (twoPairBlock_isHermitian x₁ y₁ x₂ y₂) ≤ 2 := by
  have hpsd (v : d → ℝ) : (vecMulVec v v).PosSemidef := by
    have h := posSemidef_vecMulVec_self_star v
    rwa [show (star v) = v from rfl] at h
  set Y := vecMulVec y₁ y₁ + vecMulVec y₂ y₂ with hY
  set X := vecMulVec x₁ x₁ + vecMulVec x₂ x₂ with hX
  have hYpsd : Y.PosSemidef := (hpsd y₁).add (hpsd y₂)
  have hXpsd : X.PosSemidef := (hpsd x₁).add (hpsd x₂)
  -- defect(twoPairBlock) = n₊(Y − X) ≤ rank Y ≤ rank(y₁y₁ᵀ) + rank(y₂y₂ᵀ) ≤ 2.
  unfold defect
  rw [posIndex_congr (twoPairBlock_isHermitian x₁ y₁ x₂ y₂).neg
        (hYpsd.isHermitian.sub hXpsd.isHermitian) (by unfold twoPairBlock; rw [neg_sub])]
  -- n₊(Y − X) ≤ rank Y (subadditivity via the PSD split)
  have hle : posIndex (hYpsd.isHermitian.sub hXpsd.isHermitian) ≤ Y.rank :=
    posIndex_sub_le_rank hYpsd hXpsd
  -- rank Y = n₊(y₁y₁ᵀ + y₂y₂ᵀ) ≤ n₊(y₁y₁ᵀ) + n₊(y₂y₂ᵀ) ≤ 1 + 1
  have hrk : Y.rank ≤ 2 := by
    rw [← posIndex_eq_rank_of_posSemidef hYpsd]
    have hsub := posIndex_add_le (hpsd y₁).isHermitian (hpsd y₂).isHermitian
    rw [posIndex_eq_rank_of_posSemidef (hpsd y₁), posIndex_eq_rank_of_posSemidef (hpsd y₂)] at hsub
    have h1 : (vecMulVec y₁ y₁).rank ≤ 1 := Matrix.rank_vecMulVec_le y₁ y₁
    have h2 : (vecMulVec y₂ y₂).rank ≤ 1 := Matrix.rank_vecMulVec_le y₂ y₂
    calc posIndex hYpsd.isHermitian
        = (vecMulVec y₁ y₁ + vecMulVec y₂ y₂).rank := by
          rw [posIndex_eq_rank_of_posSemidef hYpsd]
      _ ≤ (vecMulVec y₁ y₁).rank + (vecMulVec y₂ y₂).rank := by
          rw [posIndex_eq_rank_of_posSemidef ((hpsd y₁).add (hpsd y₂))] at hsub; exact hsub
      _ ≤ 2 := by omega
  exact hle.trans hrk

namespace PairDecomp

variable {d : Type*} [Fintype d] [DecidableEq d] (D : PairDecomp d)

/-- **The two-sided dictionary equality `defect A = p`.** Squeezing `defect_le_offline_pairs`
(`defect ≤ p`) against `offline_pairs_le_defect` (`p ≤ defect`, from a `NegativeWitness` of the SAME
dimension `p`) gives the exact count. This is the R2 rung realized abstractly: the finite Weil
compression's defect is EXACTLY the number of off-line pairs it carries. -/
theorem defect_eq_offline_pairs (hwit : NegativeWitness D.blockA_isHermitian D.p) :
    defect D.blockA_isHermitian = D.p :=
  le_antisymm D.defect_le_offline_pairs (offline_pairs_le_defect D.blockA_isHermitian hwit)

end PairDecomp

end DefectDictionary


/-! ## Standalone restatement for the missions grant gate

The registry node `MM_offline_pairs_le_defect` states `offline_pairs_le_defect` with the section
variables `{𝕜} [RCLike 𝕜] {n} [Fintype n] [DecidableEq n]` inlined as explicit binders (so the
statement module elaborates on its own).  The grant gate is syntactic containment of that statement
in this artifact, which the section form above cannot satisfy; this restatement is the same theorem
with the binders explicit, proved by the section theorem.  It lives in its own sub-namespace so that
`open DefectDictionary` users of `offline_pairs_le_defect` see no ambiguity. -/
namespace DefectDictionary.Standalone

theorem offline_pairs_le_defect {𝕜 : Type*} [RCLike 𝕜]
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {p : ℕ}
    (hwit : NegativeWitness hA p) :
    p ≤ defect hA :=
  DefectDictionary.offline_pairs_le_defect hA hwit

end DefectDictionary.Standalone
