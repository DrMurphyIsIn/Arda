/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
DefectDictionary.lean — MIRRORMERE QC-B3 (qc-wedge), deliverable (1): THE INERTIA DICTIONARY.

Connects the finite-compression inertia language of Alpöge–Furman (arXiv:2608.13637, §3/§4) —
`posIndex` / `negIndex` of a `d×d` Hermitian compression of Weil's form — to the
"crystalline up to defect k" reading of Variant D of the QC axioms
(`telperion/docs/QC_AXIOMS_DRAFT.md` §4). The bridge that makes partial Weil positivity a formal
wedge candidate: **defect := the negative index of the finite compression**, and the three
dictionary rows relate it to the number of off-line (β ≠ 1/2) zero pairs in the window.

## What is honestly proved (kernel, ζ-free, finite)

Everything here is a KERNEL fact about a FINITE Hermitian matrix built from an abstract
`ZeroBlockData` (the paper §4 block structure: distinct points with multiplicities, the involution
σ = (ρ ↦ 1−ρ̄), evaluation vectors `v ρ = (φ̂(γ_ρ − τ_k))_k` with `v(σρ) = conj (v ρ)`). It proves
NOTHING new about RH. The RH-hard converse of row (b) is carried as an EXPLICIT named hypothesis
`honline_of_defect_zero`, flagged loudly (the D4 `hcomp` discipline). conjecture1_proved = False.

## The three rows (charter B3 (i))

  (a) `offline_pair_negIndex` — an off-line pair contributes ≥ 1 to the negative index of the
      compressed form (the (1,1)-block fact of Prop 4.1). Generalizes D4's
      `weilGram_neg_posIndex_ge_one` from the diagonal scalar channel to a genuine off-line
      evaluation vector: the imaginary-part direction `y = Im u ≠ 0` is a strictly-negative
      direction of the pair block `2m(x xᵀ − y yᵀ)`.
  (b) `defect_zero_iff_onLine` (FINITE form) — for the compression built from the window,
      defect = 0 ↔ every zero in the window is on the line, under an explicit non-degeneracy
      witness for the (⇐ is unconditional; ⇒ carries the RH-hard geometric hypothesis).
  (c) `defect_le_offline_pairs` — defect ≤ #(off-line pairs) `p`: the quantitative dictionary row,
      the DUAL of the paper's `posIndex_blockA_le` (`n₊(A) ≤ s₁+s₂+p`), obtained by applying the
      §3 inertia machinery to `−A`.

## Provenance

The `RHLinalg` prelude (posIndex / hermForm / PosDefOn / finrank_le_posIndex_of_posDefOn /
posIndex_conj_le / posIndex_add_le) is the verbatim §3 port; see `RHLinalg.lean`. The generic
negative-index helper lemmas in Section 0 are transcribed from the "Section 1. Generic lemmas"
of `anthropics/formal-math` path `zeta23/Zeta23/ZeroSide.lean` at commit
`fbdc36bbf17d20af3fd0447c6d1a8a02773c9844` (Apache-2.0) — reproduced here (that file is ζ-adjacent
and not itself ported) with the source cited. The abstract pair-block algebra
(`aaᵀ − bbᵀ` decomposition) mirrors that file's `pair_term` / `blockA_decomp` / Prop 4.1.
-/
import RHLinalg.PosIndex
import RHLinalg.HermitianPosPart
import RHLinalg.Sylvester
import RHLinalg.Inertia

noncomputable section

open Matrix Finset Submodule RHLinalg
open scoped ComplexOrder BigOperators

namespace DefectDictionary

/-! ## Section 0. The defect (negative index) and its generic lemmas

`defect hA := posIndex hA.neg` — the number of strictly-negative directions of the Hermitian form,
i.e. the negative index `n₋`. We use the `posIndex hA.neg` presentation (as D4 does in
`weilGram_neg_posIndex_ge_one`) so that the whole §3 pull-back / subadditivity toolkit
(`posIndex_conj_le`, `posIndex_add_le`, `finrank_le_posIndex_of_posDefOn`) applies to `−A` directly.
-/

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The defect of a Hermitian compression**: the number of strictly-negative eigen-directions,
`n₋(A) = n₊(−A)`. "Crystalline up to defect k" ⟺ this is ≤ k. -/
def defect {A : Matrix n n 𝕜} (hA : A.IsHermitian) : ℕ := posIndex hA.neg

/-- `hermForm (−A) x = − hermForm A x`. -/
lemma hermForm_neg (A : Matrix n n 𝕜) (x : n → 𝕜) :
    hermForm (-A) x = - hermForm A x := by
  unfold hermForm; rw [neg_mulVec, dotProduct_neg, map_neg]

omit [DecidableEq n] in
/-- The Hermitian form scales by `‖c‖²` under scalar multiplication of the argument. -/
lemma hermForm_smul_sq {A : Matrix n n 𝕜} (c : 𝕜) (x : n → 𝕜) :
    hermForm A (c • x) = ‖c‖ ^ 2 * hermForm A x := by
  unfold hermForm
  rw [mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct, smul_smul, smul_eq_mul]
  have h1 : c * star c = ((‖c‖ ^ 2 : ℝ) : 𝕜) := by
    rw [RCLike.star_def, mul_comm, RCLike.conj_mul]; push_cast; ring
  rw [show (c * star c * (star x ⬝ᵥ A *ᵥ x)) = ((‖c‖ ^ 2 : ℝ) : 𝕜) * (star x ⬝ᵥ A *ᵥ x) by rw [h1],
     RCLike.re_ofReal_mul]

/-- If the Hermitian form of `A` is nonpositive everywhere then `n₊(A) = 0`.
(Transcribed from `zeta23/Zeta23/ZeroSide.lean` §1, `posIndex_eq_zero_of_hermForm_nonpos`.) -/
lemma posIndex_eq_zero_of_hermForm_nonpos {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (h : ∀ x, hermForm A x ≤ 0) : posIndex hA = 0 := by
  obtain ⟨W, hW, hdim⟩ := posIndex_eq_max_finrank_posDefOn hA
  rw [← hdim, Submodule.finrank_eq_zero]
  by_contra hne
  obtain ⟨x, hxW, hx0⟩ := (Submodule.ne_bot_iff W).mp hne
  exact absurd (hW x hxW hx0) (not_lt.mpr (h x))

/-- `n₊(−N) = 0` for `N ⪰ 0`: a positive-semidefinite matrix has zero defect... no negative
directions of `N` means no positive directions of `−N`.
(Transcribed from `zeta23/Zeta23/ZeroSide.lean` §1, `posIndex_neg_eq_zero_of_posSemidef`.) -/
lemma posIndex_neg_eq_zero_of_posSemidef {N : Matrix n n 𝕜} (hN : N.PosSemidef) :
    posIndex hN.isHermitian.neg = 0 := by
  refine posIndex_eq_zero_of_hermForm_nonpos _ fun x => ?_
  rw [hermForm_neg, neg_nonpos]
  exact hermForm_nonneg_of_posSemidef hN x

/-- **The defect of a PSD matrix is zero.** A positive-semidefinite compression is
crystalline (defect 0) — no negative direction. -/
lemma defect_posSemidef {A : Matrix n n 𝕜} (hA : A.PosSemidef) : defect hA.isHermitian = 0 :=
  posIndex_neg_eq_zero_of_posSemidef hA

/-- `n₊(P − N) ≤ rank P` for `P, N ⪰ 0` (subadditivity of the positive index + `n₊(P)=rank P`,
`n₊(−N)=0`). Transcribed from `zeta23/Zeta23/ZeroSide.lean` §1, `posIndex_sub_le_rank`. -/
lemma posIndex_sub_le_rank {P N : Matrix n n 𝕜} (hP : P.PosSemidef) (hN : N.PosSemidef) :
    posIndex (hP.isHermitian.sub hN.isHermitian) ≤ P.rank := by
  have h := posIndex_add_le hP.isHermitian hN.isHermitian.neg
  rw [posIndex_eq_rank_of_posSemidef hP, posIndex_neg_eq_zero_of_posSemidef hN, add_zero] at h
  convert h using 2; exact (sub_eq_add_neg P N)

/-! ## Section 1. Row (a): an off-line pair forces defect ≥ 1

The generic engine: a single strictly-negative test direction pins the defect at ≥ 1, via the
Sylvester subspace bound applied to `−A` on the line it spans. Then the concrete Prop 4.1 pair
block `x xᵀ − y yᵀ` (`x = Re u`, `y = Im u`) supplies such a direction whenever `y ≠ 0` — i.e.
whenever the zero is genuinely off the line. -/

/-- **Row (a), generic form.** A single strictly-negative direction of the Hermitian form forces
`defect ≥ 1`. This is the abstract content of Prop 4.1 (off-line pair ⇒ negative index ≥ 1) and the
direct generalization of D4's `weilGram_neg_posIndex_ge_one` (the diagonal scalar-channel case). -/
theorem defect_ge_one_of_neg_dir {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {x₀ : n → 𝕜} (hx₀ : x₀ ≠ 0) (hneg : hermForm A x₀ < 0) :
    1 ≤ defect hA := by
  have hpd : PosDefOn (-A) (Submodule.span 𝕜 {x₀}) := by
    intro x hx hxne
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨c, rfl⟩ := hx
    have hc : c ≠ 0 := by rintro rfl; simp at hxne
    rw [hermForm_neg, hermForm_smul_sq]
    have : (0 : ℝ) < ‖c‖ ^ 2 := by positivity
    nlinarith [this, hneg]
  calc (1 : ℕ)
      = Module.finrank 𝕜 (Submodule.span 𝕜 {x₀}) := (finrank_span_singleton hx₀).symm
    _ ≤ posIndex hA.neg := finrank_le_posIndex_of_posDefOn hA.neg hpd

/-- The `d×d` **off-line pair block** `x xᵀ − y yᵀ` of a single conjugate pair `{ρ, 1−ρ̄}`, with
`x, y : d → ℝ` the real and imaginary parts of the (scaled) evaluation vector `u = x + i y`.
Prop 4.1: `m(u uᵀ + ū ūᵀ) = 2m(x xᵀ − y yᵀ)`; here we absorb `2m > 0` (defect is scale-invariant)
and read the signature of the bare `x xᵀ − y yᵀ`. -/
def pairBlock {d : Type*} (x y : d → ℝ) : Matrix d d ℝ :=
  vecMulVec x x - vecMulVec y y

lemma pairBlock_isHermitian {d : Type*} [Fintype d] [DecidableEq d] (x y : d → ℝ) :
    (pairBlock x y).IsHermitian := by
  unfold pairBlock Matrix.IsHermitian
  rw [conjTranspose_sub, conjTranspose_vecMulVec, conjTranspose_vecMulVec]
  simp only [star_trivial]

/-- `hermForm (vecMulVec x x) w = ⟨x,w⟩²` for a real vector `x` (the rank-one channel). -/
lemma hermForm_vecMulVec_real {d : Type*} [Fintype d] [DecidableEq d] (x w : d → ℝ) :
    hermForm (vecMulVec x x) w = (∑ k, w k * x k) ^ 2 := by
  have expand : hermForm (vecMulVec x x) w = ∑ i, ∑ j, (w i * x i) * (w j * x j) := by
    unfold hermForm
    simp only [dotProduct, mulVec, vecMulVec_apply, Pi.star_apply, star_trivial,
      Finset.mul_sum, RCLike.re_to_real]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [expand, sq, Finset.sum_mul_sum]

/-- The pair block's quadratic form: `hermForm (x xᵀ − y yᵀ) w = ⟨x,w⟩² − ⟨y,w⟩²` (real dot
products). The `−⟨y,·⟩²` term is the (1,1)-signature's negative channel. -/
lemma pairBlock_hermForm {d : Type*} [Fintype d] [DecidableEq d] (x y w : d → ℝ) :
    hermForm (pairBlock x y) w = (∑ k, w k * x k) ^ 2 - (∑ k, w k * y k) ^ 2 := by
  unfold pairBlock
  rw [hermForm_sub, hermForm_vecMulVec_real, hermForm_vecMulVec_real]

/-- **Row (a), concrete (Prop 4.1).** An off-line pair whose evaluation vector has a genuine
imaginary part gives the compression a negative direction, hence defect ≥ 1. Concretely: for the
pair block `x xᵀ − y yᵀ`, if there is a test vector `w` orthogonal to `x` but not to `y`
(`⟨w,x⟩ = 0 ≠ ⟨w,y⟩` — the geometric meaning of "genuinely off the line, β ≠ 1/2"), then the block
is indefinite and its defect is ≥ 1. This is the (1,1)-signature obstruction of Prop 4.1, and the
vector generalization of D4's diagonal `weilGram_neg_posIndex_ge_one`. -/
theorem offline_pair_negIndex {d : Type*} [Fintype d] [DecidableEq d] (x y : d → ℝ)
    {w : d → ℝ} (hwx : ∑ k, w k * x k = 0) (hwy : ∑ k, w k * y k ≠ 0) :
    1 ≤ defect (pairBlock_isHermitian x y) := by
  refine defect_ge_one_of_neg_dir (pairBlock_isHermitian x y) (x₀ := w) ?_ ?_
  · intro hw0; apply hwy; rw [hw0]; simp
  · rw [pairBlock_hermForm, hwx]
    have : (0 : ℝ) < (∑ k, w k * y k) ^ 2 := by positivity
    simpa using this

/-! ## Section 2. Row (c): the defect is at most the number of off-line pairs

The DUAL of the paper's `posIndex_blockA_le` (`n₊(A) ≤ s₁+s₂+p`). A finite compression that decomposes
as `A = onPart + (rePart − imPart)` with all three parts positive-semidefinite (the paper's
`blockA_decomp`: `onPart = Σ_on m u uᵀ`, `rePart = Σ_𝒫 2m x xᵀ`, `imPart = Σ_𝒫 2m y yᵀ`) has
`defect A = n₊(−A) ≤ rank imPart ≤ p`. We package the paper's decomposition as an abstract
`PairDecomp` so the dictionary is self-contained and ζ-free. -/

/-- `posIndex` respects matrix equality (the Hermitian proof is irrelevant).
(Transcribed from `zeta23/Zeta23/ZeroSide.lean` §2, `posIndex_congr`.) -/
lemma posIndex_congr {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A = B) :
    posIndex hA = posIndex hB := by subst h; rfl

/-- **An abstract Prop-4.1 compression**: a Hermitian `d×d` form presented as `onPart + rePart − imPart`
with all three summands positive-semidefinite and a declared off-line-pair count `p` bounding
`rank imPart` (the negative-channel rank). This is exactly the shape of the paper's `blockA_decomp`:
`onPart` = on-line squares, `rePart`/`imPart` = the real/imaginary halves of the `p` pair blocks. -/
structure PairDecomp (d : Type*) [Fintype d] [DecidableEq d] where
  /-- on-line part `Σ_{on} m u uᵀ` ⪰ 0 -/
  onPart : Matrix d d ℝ
  /-- real pair channel `Σ_𝒫 2m x xᵀ` ⪰ 0 -/
  rePart : Matrix d d ℝ
  /-- imaginary pair channel `Σ_𝒫 2m y yᵀ` ⪰ 0 (the negative-signature channel) -/
  imPart : Matrix d d ℝ
  onPart_psd : onPart.PosSemidef
  rePart_psd : rePart.PosSemidef
  imPart_psd : imPart.PosSemidef
  /-- number of off-line pairs `p`, with `rank imPart ≤ p` (each pair adds one rank-one `y yᵀ`) -/
  p : ℕ
  rank_imPart_le : imPart.rank ≤ p

namespace PairDecomp

variable {d : Type*} [Fintype d] [DecidableEq d] (D : PairDecomp d)

/-- The compressed Weil form `A = onPart + (rePart − imPart)` [paper `blockA_decomp`]. -/
def blockA : Matrix d d ℝ := D.onPart + (D.rePart - D.imPart)

lemma blockA_isHermitian : D.blockA.IsHermitian :=
  D.onPart_psd.isHermitian.add (D.rePart_psd.isHermitian.sub D.imPart_psd.isHermitian)

/-- **Row (c): `defect A ≤ p`.** The compressed Weil form is crystalline up to defect `p`, the number
of off-line pairs. Dual to `posIndex_blockA_le`: `−A = imPart + (−(onPart + rePart))`, so
`n₊(−A) ≤ n₊(imPart) + n₊(−(onPart+rePart)) = rank imPart + 0 ≤ p`. -/
theorem defect_le_offline_pairs : defect D.blockA_isHermitian ≤ D.p := by
  have hOnRe := D.onPart_psd.add D.rePart_psd
  have hstep := posIndex_add_le D.imPart_psd.isHermitian hOnRe.isHermitian.neg
  rw [posIndex_eq_rank_of_posSemidef D.imPart_psd,
      posIndex_neg_eq_zero_of_posSemidef hOnRe, add_zero] at hstep
  unfold defect
  rw [posIndex_congr D.blockA_isHermitian.neg
        (D.imPart_psd.isHermitian.add hOnRe.isHermitian.neg) (by unfold blockA; abel)]
  exact hstep.trans D.rank_imPart_le

/-! ## Section 3. Row (b): defect = 0 ⟺ on-line (finite form)

The clean equivalence.  The `⇐` (crystalline direction) is UNCONDITIONAL: if the compression is
positive-semidefinite (no off-line pairs contributing a negative channel), defect = 0.  The `⇒`
(RH-hard direction) — defect 0 forces every zero on the line — needs the geometric non-degeneracy of
the evaluation vectors (that a real off-line pair genuinely produces a negative direction, not a
cancellation), which at the zeta comb is RH-content.  It is carried as an EXPLICIT named hypothesis
`hcryst_forces_online`, flagged loudly. -/

/-- **Row (b), `⇐` (unconditional, crystalline direction).** If the compression is positive
semidefinite — the "no off-line negative channel" configuration, e.g. `imPart = 0` — then defect = 0
(the finite snapshot is crystalline). -/
theorem defect_zero_of_posSemidef (hpsd : D.blockA.PosSemidef) :
    defect D.blockA_isHermitian = 0 :=
  posIndex_neg_eq_zero_of_posSemidef hpsd

/-- **No off-line pairs ⟹ defect 0 (UNCONDITIONAL).** The `⇐` half of `defect_zero_iff_onLine`, an
immediate corollary of row (c) `defect ≤ p`.  So the ONLY genuinely RH-hard direction of the finite
iff is `⇒` (`defect 0 ⟹ p = 0`). -/
theorem defect_zero_of_no_pairs (hp : D.p = 0) : defect D.blockA_isHermitian = 0 :=
  Nat.le_zero.mp (hp ▸ D.defect_le_offline_pairs)

/-- **Row (b), the finite iff.** `defect A = 0 ↔ p = 0` ("defect-0 crystallinity of the finite
snapshot ⇔ every zero in the window on the line").  The `⇐` direction is proved UNCONDITIONALLY here
(via row (c)); only the `⇒` direction — "no negative direction forces the off-line count to vanish",
which for the zeta comb IS RH — is carried, as the EXPLICIT named hypothesis `hcryst_forces_online`
(the D4 `hcomp` discipline).  It is the RH-hard wall and is never discharged here.  No RH claim is
made.  conjecture1_proved = False. -/
theorem defect_zero_iff_onLine
    (hcryst_forces_online : defect D.blockA_isHermitian = 0 → D.p = 0) :
    defect D.blockA_isHermitian = 0 ↔ D.p = 0 :=
  ⟨hcryst_forces_online, D.defect_zero_of_no_pairs⟩

end PairDecomp

end DefectDictionary
