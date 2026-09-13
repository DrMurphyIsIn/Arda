/-
RvMRoutePInertia — Route P Brick D4 (optional, cross-pollination): the diffraction/inertia bridge.

Unifies the Route P diffraction reading (`RvMRouteP`, `BraggFloor`, `RvMOnLinePositivity`) with the
Weil-positivity / Bombieri-inertia track (assessment §2.3), through the ported §3 linear-algebra
prelude `RHLinalg` (PosIndex / HermitianPosPart / Sylvester / Inertia; namespace `RHLinalg`).

## The honest object

The Route P diffraction reading is a per-order, two-channel positivity statement:

  * the **on-line paired Li summands are perfect squares** (`onLine_liPairedSummand_eq_normSq`, #466):
    `liPairedSummand n ρ = ‖1 - (1-1/ρ)^(n+1)‖²` when `ρ.re = 1/2` — the manifest `+` direction, an
    already-certified nonnegative "square" channel;
  * the **Bragg (log-prime / von Mangoldt) amplitude carries the arithmetic** (`BraggFloor`, D3): the
    certified truncated amplitude, net of a certified tail, is compared to the explicit archimedean
    floor `-(1 + Re taylorCoeff Γℝ n)` — the "clearance" channel `q := braggLo - tailHi - floor`.

We assemble the finite `2×2` real Weil–Gram form `weilGram s q := diagonal ![s, q]` from these two
channels and read its inertia with the ported `RHLinalg.posIndex` / Sylvester subspace machinery:

  * `s` (the on-line square channel) is `≥ 0` **unconditionally** (a `Complex.normSq`);
  * `q` (the Bragg-clearance channel) is `≥ 0` **exactly when the certified Bragg rung clears the
    floor** — which is what every `BraggFloor.bragg_rung_*` establishes.

So the diffraction spectrum's inertia signature reads:

  * both channels clear ⟹ the form is positive semidefinite, `posIndex = 2` (the `(2,0)`,
    RH-consistent reading — no negative direction);
  * a certified **sub-floor** Bragg datum (`q < 0`) forces a negative direction: `negIndex ≥ 1`, the
    `(1,1)`-signature obstruction (Bombieri inertia at the Li/prime level).  Through Route P this is
    exactly the falsifiability face `BraggFloor.bragg_below_floor_refutes_rh`.

## Honest scope (category-(b)/structural)

Everything below is a KERNEL fact about a FINITE Hermitian matrix built from already-certified data.
It proves NOTHING new about RH or the zeros: it re-reads the D3 certificate as an inertia signature.

The RH-hard seams are NOT touched: the passage from a finite Bragg datum to
`(taylorCoeff zetaPoleCompanion n).re` runs through the CONDITIONAL, undischarged
`taylorCoeff_companion_bragg_of_exhaustion_limits` (the exhaustion/extraction limits), and the uniform
`∀ n` direction IS RH.  Where a statement needs those, they are carried as EXPLICIT hypotheses named
RH-hard.  The `s` and `q` inputs are the same Arb (python-flint) enclosures the D3 ladder documents as
its trust seam.  Kernel axioms `[propext, Classical.choice, Quot.sound]`.  conjecture1_proved = False.
-/
import Mathlib
import RHLinalg.PosIndex
import RHLinalg.HermitianPosPart
import RHLinalg.Sylvester
import RHLinalg.Inertia
import RvMOnLinePositivity
import RvMRoutePFalsify

open Matrix Finset
open scoped ComplexOrder

namespace RvMWeierstrass

/-! ## The finite Weil–Gram diffraction form -/

/-- **The `2×2` Weil–Gram diffraction form.**  Diagonal channels `s` (on-line square amplitude,
`≥ 0` unconditionally) and `q` (Bragg-vs-floor clearance, `≥ 0` iff the certified rung clears the
archimedean floor).  Real symmetric, hence Hermitian; its inertia is the `(1,1)`-signature reading. -/
noncomputable def weilGram (s q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal ![s, q]

lemma weilGram_isHermitian (s q : ℝ) : (weilGram s q).IsHermitian := by
  apply Matrix.isHermitian_diagonal_of_self_adjoint
  ext i; fin_cases i <;> simp

/-- The Weil–Gram quadratic form: `hermForm (weilGram s q) x = s·x₀² + q·x₁²`.  The diffraction
reading of a test vector: the on-line square channel weighted by `s`, the Bragg channel by `q`. -/
lemma weilGram_hermForm (s q : ℝ) (x : Fin 2 → ℝ) :
    RHLinalg.hermForm (weilGram s q) x = s * (x 0) ^ 2 + q * (x 1) ^ 2 := by
  unfold RHLinalg.hermForm weilGram
  simp only [Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, RCLike.star_def,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    RCLike.conj_to_real, RCLike.re_to_real]
  ring

/-! ## Inertia signature dichotomy -/

/-- **The RH-consistent `(2,0)` reading.**  When both diffraction channels are strictly positive —
the on-line square channel `s > 0` and the Bragg-clearance channel `q > 0` (the certified rung clears
the floor with margin) — the Weil–Gram form is positive definite: `hermForm > 0` on every nonzero
test vector.  No negative direction: the diffraction spectrum's inertia is `(2,0)`. -/
lemma weilGram_posDef_of_pos {s q : ℝ} (hs : 0 < s) (hq : 0 < q) (x : Fin 2 → ℝ) (hx : x ≠ 0) :
    0 < RHLinalg.hermForm (weilGram s q) x := by
  rw [weilGram_hermForm]
  have h0 : 0 ≤ s * (x 0) ^ 2 := mul_nonneg hs.le (sq_nonneg _)
  have h1 : 0 ≤ q * (x 1) ^ 2 := mul_nonneg hq.le (sq_nonneg _)
  rcases Function.ne_iff.mp hx with ⟨i, hi⟩
  have hsq : ∀ j : Fin 2, x j ≠ 0 → 0 < (x j) ^ 2 := fun j hj => by positivity
  fin_cases i
  · have hpos : 0 < s * (x 0) ^ 2 := mul_pos hs (hsq 0 hi)
    linarith
  · have hpos : 0 < q * (x 1) ^ 2 := mul_pos hq (hsq 1 hi)
    linarith

/-- **The RH-consistent `(2,0)` reading, at the inertia level.**  Both channels strictly positive ⟹
the Weil–Gram form is positive semidefinite with `posIndex = 2`: the diffraction spectrum has two
positive directions and no negative one.  (`posIndex` via `RHLinalg.posIndex_eq_rank_of_posSemidef` +
`Matrix.rank_diagonal`.) -/
lemma weilGram_posIndex_eq_two {s q : ℝ} (hs : 0 < s) (hq : 0 < q) :
    RHLinalg.posIndex (weilGram_isHermitian s q) = 2 := by
  have hpsd : (weilGram s q).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i; fin_cases i <;> simp <;> linarith
  rw [RHLinalg.posIndex_eq_rank_of_posSemidef hpsd]
  show (Matrix.diagonal ![s, q]).rank = 2
  rw [Matrix.rank_diagonal, Fintype.card_subtype,
    show (Finset.univ.filter (fun i => ![s, q] i ≠ 0)) = Finset.univ from ?_]
  · simp
  · ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
    fin_cases i <;> simp <;> [exact hs.ne'; exact hq.ne']

/-- **The `(1,1)`-signature obstruction, at the form level.**  A certified **sub-floor** Bragg datum
(`q < 0`, i.e. the truncated log-prime amplitude net of tail falls below the archimedean floor) forces
a strictly negative direction: `hermForm (weilGram s q) e₁ = q < 0`.  Hence the form is not positive
semidefinite.  Through Route P this is the shadow of `bragg_below_floor_refutes_rh`. -/
lemma weilGram_neg_dir_of_floor_below {s q : ℝ} (hq : q < 0) :
    RHLinalg.hermForm (weilGram s q) ![0, 1] < 0 := by
  rw [weilGram_hermForm]
  simpa using hq

/-- A certified sub-floor Bragg datum makes the diffraction form **not** positive semidefinite —
positivity of the whole spectrum fails at the Bragg channel. -/
lemma weilGram_not_posSemidef_of_floor_below {s q : ℝ} (hq : q < 0) :
    ¬ (weilGram s q).PosSemidef := by
  intro hpsd
  have h := hpsd.re_dotProduct_nonneg (![0, 1] : Fin 2 → ℝ)
  have hneg : RHLinalg.hermForm (weilGram s q) ![0, 1] < 0 := weilGram_neg_dir_of_floor_below hq
  exact absurd h (not_le.mpr hneg)

/-- **The `(1,1)`-signature obstruction, at the inertia level.**  A certified sub-floor Bragg datum
gives the diffraction form a genuine negative eigen-direction: `posIndex (-weilGram s q) ≥ 1`, i.e.
`weilGram s q` has `negIndex ≥ 1`.  This is the Bombieri `(1,1)`-inertia reading of a Route P
falsification — a negative direction in the Weil–Gram form, dual to the on-line square channel.
(Via the Sylvester subspace bound `RHLinalg.finrank_le_posIndex_of_posDefOn` on `span{e₁}`.) -/
lemma weilGram_neg_posIndex_ge_one {s q : ℝ} (hq : q < 0) :
    1 ≤ RHLinalg.posIndex ((weilGram_isHermitian s q).neg) := by
  set hHn : (-weilGram s q).IsHermitian := (weilGram_isHermitian s q).neg with hHn_def
  have hpd : RHLinalg.PosDefOn (-weilGram s q) (Submodule.span ℝ {![(0 : ℝ), 1]}) := by
    intro x hx hxne
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨c, rfl⟩ := hx
    have hc : c ≠ 0 := by rintro rfl; simp at hxne
    unfold RHLinalg.hermForm weilGram
    simp only [Matrix.neg_mulVec, Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_two,
      Pi.smul_apply, Pi.star_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      smul_eq_mul, Pi.neg_apply, RCLike.star_def, RCLike.conj_to_real, RCLike.re_to_real]
    nlinarith [mul_self_pos.mpr hc]
  calc (1 : ℕ)
      = Module.finrank ℝ (Submodule.span ℝ {![(0 : ℝ), 1]}) := by
        rw [finrank_span_singleton]; intro h; simpa using congrFun h 1
    _ ≤ RHLinalg.posIndex hHn := RHLinalg.finrank_le_posIndex_of_posDefOn hHn hpd

/-! ## Bridge to Route P: the on-line square channel and the Bragg falsification -/

/-- **Bridge — the on-line square channel is a certified paired Li summand.**  Feeding the on-line
square amplitude `s := ‖1 - (1-1/ρ)^(n+1)‖²` (the `+` direction of the diffraction reading) into the
Weil–Gram form, the on-line diagonal entry equals the on-line paired Li summand of the zero `ρ`
(via `onLine_liPairedSummand_eq_normSq`, #466).  So the `s`-channel of `weilGram` literally carries
the manifest on-line perfect square.  Unconditional; proves nothing new about RH. -/
theorem weilGram_onLine_channel_eq_liPairedSummand (n : ℕ) (ρ : LiCriterion.NontrivialZero)
    (hρ : ρ.val.re = 1 / 2) :
    ((Complex.normSq (1 - (1 - 1 / ρ.val) ^ (n + 1)) : ℝ) : ℂ)
      = LiCriterion.liPairedSummand n ρ :=
  (onLine_liPairedSummand_eq_normSq n ρ hρ).symm

/-- **Bridge — a sub-floor Bragg channel refutes RH (through the RH-hard seam).**  If the Bragg
channel `q` is the clearance `braggVal - floor` of the companion coefficient at order `n` (this
equality is the CONDITIONAL, RH-hard `hcomp` seam — the exhaustion/extraction passage from the finite
D3 Bragg datum to `(taylorCoeff zetaPoleCompanion n).re`, NEVER discharged here), and that channel is
strictly negative (the `(1,1)` obstruction `weilGram_neg_dir_of_floor_below`), then RH is false.

The Weil–Gram negative direction and the Route P falsification are the same event, viewed as inertia
vs. contrapositive.  `hcomp` is carried as an explicit hypothesis and is the RH-hard wall; the finite
inertia facts above touch it not at all.  conjecture1_proved = False. -/
theorem weilGram_floor_below_refutes_rh (n : ℕ) (s braggVal : ℝ)
    (hcomp : (LiCriterion.taylorCoeff DiffractionCore.zetaPoleCompanion n).re = braggVal)
    (hchannel : braggVal + (1 + (LiCriterion.taylorCoeff Complex.Gammaℝ n).re) < 0) :
    ¬ RiemannHypothesis := by
  refine companion_below_floor_refutes_rh n ?_
  rw [hcomp]; linarith

end RvMWeierstrass
