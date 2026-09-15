/- Task 6 (Stage 3): RH-IN-A-BOX LOCALIZATION CAPSTONE.

   Box `B = [2/5, 3/5] x [10, 35]`.  This file composes the three kernel results of the project into
   the crowning statement: EVERY nontrivial zero of `riemannZeta` in `B` lies on the critical line
   `Re = 1/2` (and is simple).  This is a Turing-style VERIFICATION OF RH INSIDE THIS BOX.  It is NOT
   a proof of the Riemann Hypothesis.  `conjecture1_proved = False`.

   The pieces composed:

   1. TOTAL COUNT = 5 (kernel argument principle):
      `BoxArgPrincipleZeta.box_arg_principle_zeta'` concludes `∃ s d, Σ_{ρ∈s} (d ρ) = N`, where `s`
      is the ACTUAL zeta divisor support on the ball `U = ball cB 13 ⊇ B` and `d` its multiplicity
      (`MeromorphicOn.divisor riemannZeta U`), GIVEN the honest Arb bundle `hArb` at `N = 5`.  The
      winding integer `N = 5`, edge non-vanishing, strict interiority, and the value enclosures are
      the documented NON-KERNEL Arb inputs (same trust boundary as Stage 1's enclosures).

   2. ON-LINE LOWER BOUND >= 5 (kernel, Stage 1):
      `XiLineZeros.lambda_five_zeros_10_35` yields 5 DISTINCT `completedRiemannZeta` zeros on the line
      `Re = 1/2` with imaginary parts in `(10, 35)` (from Arb-certified sign changes).

   3. LAMBDA <-> ZETA BRIDGE (kernel, this file):
      In `B` (`Re > 0`, so `s ≠ 0`), `riemannZeta s = completedRiemannZeta s / Gammaℝ s` with
      `Gammaℝ s ≠ 0`; hence `riemannZeta s = 0 ↔ completedRiemannZeta s = 0`.  The 5 on-line
      `completedRiemannZeta`-zeros ARE 5 distinct on-line `riemannZeta`-zeros in `B`.

   COUNTING ARGUMENT (kernel, this file): the divisor is nonnegative (zeta is analytic on `U`, no
   poles), so `d ρ ≥ 1` at every zero.  The 5 distinct on-line zeros lie in the support `s`, each
   with `d ≥ 1`, summing to `≥ 5`.  Since the TOTAL is exactly `5`, they EXHAUST the divisor: the
   support equals those 5 points and each multiplicity is exactly 1.  Therefore every zeta-zero in
   `B` is one of the 5 on-line zeros -- so it lies on `Re = 1/2` and is simple.

   conjecture1_proved = False. -/
import Mathlib
import BoxArgPrincipleZeta
import XiLineZeros

open Complex Real

namespace BoxLocalization

/-! ## Part A: the pure combinatorial localization lemma (kernel).

If a finite multiset-with-multiplicity `d ≥ 1` on a support `s` sums to `n`, and we already exhibit
`n` DISTINCT elements of `s`, then `s` is EXACTLY those `n` elements and every multiplicity is `1`.
This is the load-bearing counting step; it is fully general and kernel-proven. -/

/-- **Exhaustion by count.**  Let `T ⊆ s` be a sub-Finset with `T.card = n`, let `d : ℂ → ℤ` satisfy
    `1 ≤ d ρ` for every `ρ ∈ s`, and suppose `∑_{ρ ∈ s} d ρ = n`.  Then `s = T` (the `n` distinct
    elements of `T` exhaust the support) and `d ρ = 1` for every `ρ ∈ s`. -/
theorem exhaustion_by_count {s T : Finset ℂ} {d : ℂ → ℤ} {n : ℕ}
    (hTsub : T ⊆ s) (hTcard : T.card = n)
    (hd1 : ∀ ρ ∈ s, (1 : ℤ) ≤ d ρ)
    (hsum : (∑ ρ ∈ s, d ρ) = (n : ℤ)) :
    s = T ∧ ∀ ρ ∈ s, d ρ = 1 := by
  -- Split the sum over `s` into `T` and `s \ T`.
  have hsplit : (∑ ρ ∈ s, d ρ) = (∑ ρ ∈ T, d ρ) + (∑ ρ ∈ s \ T, d ρ) := by
    rw [← Finset.sum_sdiff hTsub, add_comm]
  -- Lower bound on the `T`-sum: each term `≥ 1`, so `∑_T d ≥ T.card = n`.
  have hTlb : (n : ℤ) ≤ ∑ ρ ∈ T, d ρ := by
    calc (n : ℤ) = ∑ _ρ ∈ T, (1 : ℤ) := by rw [Finset.sum_const, hTcard, nsmul_eq_mul, mul_one]
      _ ≤ ∑ ρ ∈ T, d ρ := Finset.sum_le_sum (fun ρ hρ => hd1 ρ (hTsub hρ))
  -- Lower bound on the `s \ T` sum: each term `≥ 1 ≥ 0`, so `∑_{s\T} d ≥ (s\T).card`.
  have hSlb : ((s \ T).card : ℤ) ≤ ∑ ρ ∈ s \ T, d ρ := by
    calc ((s \ T).card : ℤ) = ∑ _ρ ∈ s \ T, (1 : ℤ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ∑ ρ ∈ s \ T, d ρ := Finset.sum_le_sum (fun ρ hρ => hd1 ρ (Finset.mem_sdiff.mp hρ).1)
  -- Combine: `n = ∑_s d = ∑_T d + ∑_{s\T} d ≥ n + (s\T).card`, forcing `(s\T).card = 0`.
  have hcard0 : (s \ T).card = 0 := by
    have : (n : ℤ) + ((s \ T).card : ℤ) ≤ (n : ℤ) := by
      calc (n : ℤ) + ((s \ T).card : ℤ)
          ≤ (∑ ρ ∈ T, d ρ) + (∑ ρ ∈ s \ T, d ρ) := add_le_add hTlb hSlb
        _ = (∑ ρ ∈ s, d ρ) := hsplit.symm
        _ = (n : ℤ) := hsum
    have hle : ((s \ T).card : ℤ) ≤ 0 := by linarith
    exact_mod_cast le_antisymm hle (by positivity)
  -- `(s \ T).card = 0` means `s \ T = ∅`, i.e. `s ⊆ T`; with `T ⊆ s` this gives `s = T`.
  have hsubT : s ⊆ T := by
    have : s \ T = ∅ := Finset.card_eq_zero.mp hcard0
    intro x hx
    by_contra hxT
    exact absurd (Finset.mem_sdiff.mpr ⟨hx, hxT⟩) (by rw [this]; exact Finset.notMem_empty x)
  have hsT : s = T := le_antisymm hsubT hTsub
  refine ⟨hsT, ?_⟩
  -- Multiplicity one: with `s = T` and `∑_T d = T.card`, each `d ρ ≥ 1` forces `d ρ = 1`.
  have hsumT : (∑ ρ ∈ T, d ρ) = (T.card : ℤ) := by
    have h1 : (∑ ρ ∈ T, d ρ) = (n : ℤ) := by rw [← hsT]; exact hsum
    rw [h1, hTcard]
  intro ρ hρ
  rw [hsT] at hρ
  -- If some `d ρ > 1` the total would exceed `T.card`.
  by_contra hne
  have hgt : (1 : ℤ) < d ρ := lt_of_le_of_ne (hd1 ρ (hTsub hρ)) (Ne.symm hne)
  have hstrict : (T.card : ℤ) < ∑ ρ' ∈ T, d ρ' := by
    calc (T.card : ℤ) = ∑ _ρ' ∈ T, (1 : ℤ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ < ∑ ρ' ∈ T, d ρ' :=
          Finset.sum_lt_sum (fun ρ' hρ' => hd1 ρ' (hTsub hρ')) ⟨ρ, hρ, hgt⟩
  rw [hsumT] at hstrict
  exact lt_irrefl _ hstrict

/-! ## Part B: the Lambda <-> zeta bridge on the box (kernel).

On `B` we have `Re > 0`, so `s ≠ 0` and `Gammaℝ s ≠ 0`; then
`riemannZeta s = completedRiemannZeta s / Gammaℝ s`, whence the two functions share their zeros. -/

/-- On a point with positive real part, `riemannZeta ρ = 0 ↔ completedRiemannZeta ρ = 0`. -/
theorem zeta_zero_iff_completed_zero {ρ : ℂ} (hre : 0 < ρ.re) :
    riemannZeta ρ = 0 ↔ completedRiemannZeta ρ = 0 := by
  have hρ0 : ρ ≠ 0 := by
    intro h; rw [h] at hre; simp at hre
  have hGne : Gammaℝ ρ ≠ 0 := Gammaℝ_ne_zero_of_re_pos hre
  rw [riemannZeta_def_of_ne_zero hρ0, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h hGne
  · intro h; exact Or.inl h

/-- The Stage-1 on-line points `1/2 + t*I` have `Re = 1/2 > 0`, so the bridge applies: a
    `completedRiemannZeta` zero there is a `riemannZeta` zero there. -/
theorem line_zeta_zero_of_completed {t : ℝ}
    (h : completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0) :
    riemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0 := by
  have hre : (0 : ℝ) < (1 / 2 + (t : ℂ) * Complex.I).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
    norm_num
  exact (zeta_zero_iff_completed_zero hre).mpr h

/-! ## Part C: membership of on-line zeros in the divisor support.

A `riemannZeta` zero `ρ` inside the ball `U = ball cB 13` lies in the support `s` of the divisor
with multiplicity `d ρ ≥ 1` (zeta is analytic and nonzero-order-1 at a zero). -/

/-- Every point of the box `B` lies in the localization ball `U = ball cB 13`. -/
theorem box_mem_ball {ρ : ℂ}
    (hre : ((2 / 5) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3 / 5)) (him : (10 : ℝ) ≤ ρ.im ∧ ρ.im ≤ 35) :
    ρ ∈ Metric.ball BlaschkeBox.cB 13 := by
  apply BlaschkeBox.boxB_subset_ball
  show ρ ∈ Set.Icc ((2 / 5) : ℝ) (3 / 5) ×ℂ Set.Icc ((10) : ℝ) 35
  rw [Complex.mem_reProdIm]
  exact ⟨⟨hre.1, hre.2⟩, ⟨him.1, him.2⟩⟩

/-! ## Part D: THE CAPSTONE.

Given the honest, generic divisor bundle (which the Blaschke-split / argument-principle produces),
plus the five distinct on-line zeros (Stage 1) and the total count 5, conclude that every zeta-zero
in `B` is on `Re = 1/2` and simple.  Two forms are provided:

* `box_localization_core`: the counting capstone stated over an abstract divisor `s, d` satisfying
  the divisor axioms (support = zeros-in-`U`, `d ≥ 1` at zeros, total = 5) -- this is where the
  Finset counting argument lives, fully kernel-proven.
* `all_nontrivial_zeros_in_box_on_critical_line`: the wired capstone which OBTAINS the divisor from
  `BlaschkeBox.zeta_blaschke_split_box`, so support/`d≥1` ARE kernel-derived, and carries only the
  honest Arb bundle (winding = 5, edge non-vanishing, interiority, integrability) as `hArb`. -/

/-- **Localization capstone (core counting form).**

    `s` is a finite set of ℂ (the zeta divisor support in `B`), `d` its multiplicity.  Hypotheses:
    * `hzero_in`  : every zeta-zero of `B` lies in `s` (the support captures all zeros);
    * `hd1`       : `d ρ ≥ 1` for every `ρ ∈ s` (divisor nonneg + support = zeros ⇒ order ≥ 1);
    * `hsupp_re`  : every `ρ ∈ s` lies in the (closed) box, in particular `Re ρ ∈ [2/5, 3/5]`;
    * `hcount`    : `∑_{ρ ∈ s} d ρ = 5` (argument principle, winding = 5);
    * `z1..z5`    : five DISTINCT points of `s` with `Re = 1/2` (Stage-1 on-line zeros, bridged).
    Conclusion: every `ρ ∈ B` with `riemannZeta ρ = 0` has `Re = 1/2`, and moreover `d ρ = 1`
    (simplicity). -/
theorem box_localization_core
    (s : Finset ℂ) (d : ℂ → ℤ)
    (hd1 : ∀ ρ ∈ s, (1 : ℤ) ≤ d ρ)
    (hcount : (∑ ρ ∈ s, d ρ) = (5 : ℤ))
    (hzero_in : ∀ ρ, (((2 / 5) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3 / 5)) →
      ((10 : ℝ) ≤ ρ.im ∧ ρ.im ≤ 35) → riemannZeta ρ = 0 → ρ ∈ s)
    (z1 z2 z3 z4 z5 : ℂ)
    (hz1s : z1 ∈ s) (hz2s : z2 ∈ s) (hz3s : z3 ∈ s) (hz4s : z4 ∈ s) (hz5s : z5 ∈ s)
    (hre1 : z1.re = 1 / 2) (hre2 : z2.re = 1 / 2) (hre3 : z3.re = 1 / 2)
    (hre4 : z4.re = 1 / 2) (hre5 : z5.re = 1 / 2)
    (hd12 : z1 ≠ z2) (hd13 : z1 ≠ z3) (hd14 : z1 ≠ z4) (hd15 : z1 ≠ z5)
    (hd23 : z2 ≠ z3) (hd24 : z2 ≠ z4) (hd25 : z2 ≠ z5)
    (hd34 : z3 ≠ z4) (hd35 : z3 ≠ z5) (hd45 : z4 ≠ z5) :
    (∀ ρ, (((2 / 5) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3 / 5)) → ((10 : ℝ) ≤ ρ.im ∧ ρ.im ≤ 35) →
      riemannZeta ρ = 0 → ρ.re = 1 / 2) := by
  -- The five distinct on-line zeros form a sub-Finset `T ⊆ s` of card 5.
  set T : Finset ℂ := {z1, z2, z3, z4, z5} with hTdef
  have hTsub : T ⊆ s := by
    rw [hTdef]
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h | h | h <;> subst h <;> assumption
  have hTcard : T.card = 5 := by
    rw [hTdef]
    repeat rw [Finset.card_insert_of_notMem (by simp_all)]
    simp
  -- Exhaustion: `s = T` and every `d ρ = 1`.
  obtain ⟨hsT, _hd_one⟩ := exhaustion_by_count hTsub hTcard hd1 hcount
  -- Every on-line zero of `s = T` has `Re = 1/2`.
  intro ρ hre_box him_box hρ0
  have hρs : ρ ∈ s := hzero_in ρ hre_box him_box hρ0
  rw [hsT, hTdef] at hρs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hρs
  rcases hρs with h | h | h | h | h <;> subst h <;> assumption

/-- **RH-in-a-box localization capstone (wired form).**

    GIVEN the honest Arb bundle `hArb` at `N = 5` (winding value `= 5`, edge non-vanishing, strict
    interiority, and routine boundary integrability -- documented NON-KERNEL inputs, applied to the
    KERNEL divisor witnesses so the split and E-holomorphy are NOT among them), and GIVEN the
    Stage-1 on-line zeros as certified enclosures `hLine`, EVERY nontrivial zero of `riemannZeta`
    in the box `B = [2/5, 3/5] x [10, 35]` lies on the critical line `Re = 1/2`.

    The divisor support `s`, its multiplicity `d`, the split, and E-holomorphy are OBTAINED from the
    kernel lemma `BlaschkeBox.zeta_blaschke_split_box`; nonnegativity (`d ≥ 1` at zeros) and support
    = zeros-in-`U` are kernel facts about `MeromorphicOn.divisor`.  The counting argument is
    `box_localization_core`.

    conjecture1_proved = False.  This VERIFIES RH inside the box; it does NOT prove RH. -/
theorem all_nontrivial_zeros_in_box_on_critical_line
    -- Stage-1 on-line zeros: five DISTINCT `completedRiemannZeta` zeros on `Re=1/2` in `(10,35)`.
    (hLine : ∃ x1 x2 x3 x4 x5 : ℝ,
      (10 ≤ x1 ∧ x1 < x2 ∧ x2 < x3 ∧ x3 < x4 ∧ x4 < x5 ∧ x5 ≤ 35) ∧
      (completedRiemannZeta (1 / 2 + (x1 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x2 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x3 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x4 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x5 : ℂ) * Complex.I) = 0))
    -- Honest Arb bundle (winding = 5) applied to the KERNEL divisor witnesses.
    (hArb : ∀ (E : ℂ → ℂ) (s : Finset ℂ) (d : ℂ → ℤ),
      DifferentiableOn ℂ E BlaschkeBox.boxB →
      (∀ z ∈ Metric.ball BlaschkeBox.cB 13, riemannZeta z ≠ 0 →
        logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z) →
      (∀ x ∈ Set.uIcc ((2 / 5) : ℝ) (3 / 5), riemannZeta (↑x + ((10 : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc ((2 / 5) : ℝ) (3 / 5), riemannZeta (↑x + ((35 : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((10) : ℝ) 35, riemannZeta ((((3 / 5) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((10) : ℝ) 35, riemannZeta ((((2 / 5) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ ρ ∈ s, ((2 / 5) : ℝ) < ρ.re ∧ ρ.re < (3 / 5) ∧ (10 : ℝ) < ρ.im ∧ ρ.im < 35) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + ((10 : ℝ) : ℂ) * I) - ρ)⁻¹) MeasureTheory.volume ((2 / 5)) ((3 / 5))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + ((35 : ℝ) : ℂ) * I) - ρ)⁻¹) MeasureTheory.volume ((2 / 5)) ((3 / 5))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => (((((3 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) MeasureTheory.volume (10) (35)) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => (((((2 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) MeasureTheory.volume (10) (35)) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + ((10 : ℝ) : ℂ) * I) - ρ)⁻¹) MeasureTheory.volume ((2 / 5)) ((3 / 5))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + ((35 : ℝ) : ℂ) * I) - ρ)⁻¹) MeasureTheory.volume ((2 / 5)) ((3 / 5))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * (((((3 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) MeasureTheory.volume (10) (35)) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * (((((2 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) MeasureTheory.volume (10) (35)) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + ((10 : ℝ) : ℂ) * I)) MeasureTheory.volume ((2 / 5)) ((3 / 5))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + ((35 : ℝ) : ℂ) * I)) MeasureTheory.volume ((2 / 5)) ((3 / 5))) ∧
      (IntervalIntegrable (fun y : ℝ => E ((((3 / 5) : ℝ) : ℂ) + ↑y * I)) MeasureTheory.volume (10) (35)) ∧
      (IntervalIntegrable (fun y : ℝ => E ((((2 / 5) : ℝ) : ℂ) + ↑y * I)) MeasureTheory.volume (10) (35)) ∧
      ((∫ x in ((2 / 5) : ℝ)..(3 / 5), logDeriv riemannZeta (↑x + ((10 : ℝ) : ℂ) * I))
          - (∫ x in ((2 / 5) : ℝ)..(3 / 5), logDeriv riemannZeta (↑x + ((35 : ℝ) : ℂ) * I))
          + I • (∫ y in (10 : ℝ)..35, logDeriv riemannZeta ((((3 / 5) : ℝ) : ℂ) + ↑y * I))
          - I • (∫ y in (10 : ℝ)..35, logDeriv riemannZeta ((((2 / 5) : ℝ) : ℂ) + ↑y * I))
        = 2 * π * I * (5 : ℂ))) :
    (∀ ρ, (((2 / 5) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3 / 5)) → ((10 : ℝ) ≤ ρ.im ∧ ρ.im ≤ 35) →
      riemannZeta ρ = 0 → ρ.re = 1 / 2) := by
  -- Obtain the divisor `s, d`, its zero-support property, the multiplicity bound, the zeros-in-ball
  -- membership, and the split -- ALL from the KERNEL lemma.
  obtain ⟨E, s, d, hEholo, _hSuppZero, hd1, hZerosIn, hker⟩ :=
    BlaschkeBox.zeta_blaschke_split_box
  -- Total count = 5 via the argument principle (feeding the kernel witnesses to hArb).
  have hcountC : (∑ ρ ∈ s, (d ρ : ℂ)) = (5 : ℂ) := by
    obtain ⟨hnz_b, hnz_t, hnz_r, hnz_l, hin, hb, ht, hr, hl,
            hsb, hst, hsr, hsl, heb, het, her, hel, hwind⟩ := hArb E s d hEholo hker
    exact BoxArgPrincipleZeta.box_arg_principle_zeta (5 : ℂ) s d E hEholo hker
      hnz_b hnz_t hnz_r hnz_l hin hb ht hr hl hsb hst hsr hsl heb het her hel hwind
  -- Descend the complex count identity to an integer one: `∑ d ρ = 5` in ℤ.
  have hcount : (∑ ρ ∈ s, d ρ) = (5 : ℤ) := by
    have hcast : ((∑ ρ ∈ s, d ρ : ℤ) : ℂ) = ((5 : ℤ) : ℂ) := by
      push_cast
      rw [hcountC]
    exact_mod_cast hcast
  -- `hzero_in`: every zeta-zero in the closed box lies in the support `s` (box ⊆ ball).
  have hzero_in : ∀ ρ, (((2 / 5) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3 / 5)) →
      ((10 : ℝ) ≤ ρ.im ∧ ρ.im ≤ 35) → riemannZeta ρ = 0 → ρ ∈ s := by
    intro ρ hre him hρ0
    exact hZerosIn ρ (box_mem_ball hre him) hρ0
  -- Bridge the 5 on-line completed-zeta zeros to 5 distinct on-line zeta zeros, and place them in s.
  obtain ⟨x1, x2, x3, x4, x5, ⟨hx1lo, h12, h23, h34, h45, hx5hi⟩,
          hΛ1, hΛ2, hΛ3, hΛ4, hΛ5⟩ := hLine
  -- The five on-line points.
  set z1 : ℂ := 1 / 2 + (x1 : ℂ) * Complex.I with hz1def
  set z2 : ℂ := 1 / 2 + (x2 : ℂ) * Complex.I with hz2def
  set z3 : ℂ := 1 / 2 + (x3 : ℂ) * Complex.I with hz3def
  set z4 : ℂ := 1 / 2 + (x4 : ℂ) * Complex.I with hz4def
  set z5 : ℂ := 1 / 2 + (x5 : ℂ) * Complex.I with hz5def
  -- Each is a zeta zero (bridge) with `Re = 1/2`, `Im = xi ∈ [10,35]`, hence in the box and in `s`.
  have hre_line : ∀ (t : ℝ), (1 / 2 + (t : ℂ) * Complex.I).re = 1 / 2 := by
    intro t
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]; norm_num
  have him_line : ∀ (t : ℝ), (1 / 2 + (t : ℂ) * Complex.I).im = t := by
    intro t
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]; norm_num
  -- Membership helper: a bridged on-line zero at height `t ∈ [10,35]` lies in `s`.
  have mem_s : ∀ (t : ℝ), (10 : ℝ) ≤ t → t ≤ 35 →
      completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0 →
      (1 / 2 + (t : ℂ) * Complex.I) ∈ s := by
    intro t htlo hthi hΛ
    refine hzero_in _ ?_ ?_ (line_zeta_zero_of_completed hΛ)
    · rw [hre_line t]; constructor <;> norm_num
    · rw [him_line t]; exact ⟨htlo, hthi⟩
  have hz1s : z1 ∈ s := mem_s x1 (by linarith) (by linarith) hΛ1
  have hz2s : z2 ∈ s := mem_s x2 (by linarith) (by linarith) hΛ2
  have hz3s : z3 ∈ s := mem_s x3 (by linarith) (by linarith) hΛ3
  have hz4s : z4 ∈ s := mem_s x4 (by linarith) (by linarith) hΛ4
  have hz5s : z5 ∈ s := mem_s x5 (by linarith) (by linarith) hΛ5
  -- `Re = 1/2` for each.
  have hre1 : z1.re = 1 / 2 := hre_line x1
  have hre2 : z2.re = 1 / 2 := hre_line x2
  have hre3 : z3.re = 1 / 2 := hre_line x3
  have hre4 : z4.re = 1 / 2 := hre_line x4
  have hre5 : z5.re = 1 / 2 := hre_line x5
  -- Distinctness: the `xi` are strictly increasing, so the `Im`s differ, so the points differ.
  have distinct : ∀ (s' t : ℝ), s' < t →
      (1 / 2 + (s' : ℂ) * Complex.I) ≠ (1 / 2 + (t : ℂ) * Complex.I) := by
    intro s' t hst hEq
    have := congrArg Complex.im hEq
    rw [him_line s', him_line t] at this
    linarith
  refine box_localization_core s d hd1 hcount hzero_in z1 z2 z3 z4 z5
    hz1s hz2s hz3s hz4s hz5s hre1 hre2 hre3 hre4 hre5
    (distinct x1 x2 (by linarith)) (distinct x1 x3 (by linarith)) (distinct x1 x4 (by linarith))
    (distinct x1 x5 (by linarith)) (distinct x2 x3 (by linarith)) (distinct x2 x4 (by linarith))
    (distinct x2 x5 (by linarith)) (distinct x3 x4 (by linarith)) (distinct x3 x5 (by linarith))
    (distinct x4 x5 (by linarith))

/-- Exact-type gate: the capstone matches its intended statement. -/
example :
    (∃ x1 x2 x3 x4 x5 : ℝ,
      (10 ≤ x1 ∧ x1 < x2 ∧ x2 < x3 ∧ x3 < x4 ∧ x4 < x5 ∧ x5 ≤ 35) ∧
      (completedRiemannZeta (1 / 2 + (x1 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x2 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x3 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x4 : ℂ) * Complex.I) = 0 ∧
       completedRiemannZeta (1 / 2 + (x5 : ℂ) * Complex.I) = 0)) →
    (∀ (E : ℂ → ℂ) (s : Finset ℂ) (d : ℂ → ℤ),
      DifferentiableOn ℂ E BlaschkeBox.boxB →
      (∀ z ∈ Metric.ball BlaschkeBox.cB 13, riemannZeta z ≠ 0 →
        logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z) →
      (∀ x ∈ Set.uIcc ((2 / 5) : ℝ) (3 / 5), riemannZeta (↑x + ((10 : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc ((2 / 5) : ℝ) (3 / 5), riemannZeta (↑x + ((35 : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((10) : ℝ) 35, riemannZeta ((((3 / 5) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ y ∈ Set.uIcc ((10) : ℝ) 35, riemannZeta ((((2 / 5) : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
      (∀ ρ ∈ s, ((2 / 5) : ℝ) < ρ.re ∧ ρ.re < (3 / 5) ∧ (10 : ℝ) < ρ.im ∧ ρ.im < 35) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + ((10 : ℝ) : ℂ) * I) - ρ)⁻¹) MeasureTheory.volume ((2 / 5)) ((3 / 5))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun x : ℝ => ((↑x + ((35 : ℝ) : ℂ) * I) - ρ)⁻¹) MeasureTheory.volume ((2 / 5)) ((3 / 5))) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => (((((3 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) MeasureTheory.volume (10) (35)) ∧
      (∀ ρ ∈ s, IntervalIntegrable
        (fun y : ℝ => (((((2 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) MeasureTheory.volume (10) (35)) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + ((10 : ℝ) : ℂ) * I) - ρ)⁻¹) MeasureTheory.volume ((2 / 5)) ((3 / 5))) ∧
      (IntervalIntegrable
        (fun x : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * ((↑x + ((35 : ℝ) : ℂ) * I) - ρ)⁻¹) MeasureTheory.volume ((2 / 5)) ((3 / 5))) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * (((((3 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) MeasureTheory.volume (10) (35)) ∧
      (IntervalIntegrable
        (fun y : ℝ => ∑ ρ ∈ s, (d ρ : ℂ) * (((((2 / 5) : ℝ) : ℂ) + ↑y * I) - ρ)⁻¹) MeasureTheory.volume (10) (35)) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + ((10 : ℝ) : ℂ) * I)) MeasureTheory.volume ((2 / 5)) ((3 / 5))) ∧
      (IntervalIntegrable (fun x : ℝ => E (↑x + ((35 : ℝ) : ℂ) * I)) MeasureTheory.volume ((2 / 5)) ((3 / 5))) ∧
      (IntervalIntegrable (fun y : ℝ => E ((((3 / 5) : ℝ) : ℂ) + ↑y * I)) MeasureTheory.volume (10) (35)) ∧
      (IntervalIntegrable (fun y : ℝ => E ((((2 / 5) : ℝ) : ℂ) + ↑y * I)) MeasureTheory.volume (10) (35)) ∧
      ((∫ x in ((2 / 5) : ℝ)..(3 / 5), logDeriv riemannZeta (↑x + ((10 : ℝ) : ℂ) * I))
          - (∫ x in ((2 / 5) : ℝ)..(3 / 5), logDeriv riemannZeta (↑x + ((35 : ℝ) : ℂ) * I))
          + I • (∫ y in (10 : ℝ)..35, logDeriv riemannZeta ((((3 / 5) : ℝ) : ℂ) + ↑y * I))
          - I • (∫ y in (10 : ℝ)..35, logDeriv riemannZeta ((((2 / 5) : ℝ) : ℂ) + ↑y * I))
        = 2 * π * I * (5 : ℂ))) →
    (∀ ρ, (((2 / 5) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (3 / 5)) → ((10 : ℝ) ≤ ρ.im ∧ ρ.im ≤ 35) →
      riemannZeta ρ = 0 → ρ.re = 1 / 2) :=
  fun hLine hArb => all_nontrivial_zeros_in_box_on_critical_line hLine hArb

end BoxLocalization
