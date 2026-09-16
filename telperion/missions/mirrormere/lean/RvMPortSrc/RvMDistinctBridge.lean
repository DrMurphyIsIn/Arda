/-
  RvMGlue.lean — the DISTINCT-BRIDGE glue for `RvMUnboundedMeanDensity zetaOrdinates`.

  This file proves, IN KERNEL and taking as an explicit hypothesis the ported
  cc-chen-tech superlinear DISTINCT lower bound
  (`selberg_odd_zero_proportion_target_proved_mainline`), the reduction to our
  registry target `RvMUnboundedMeanDensity zetaOrdinates`.

  The hypothesis `hSelberg` below is the EXACT interface of the ported theorem:
    ∃ c > 0, ∃ T0, ∀ T ≥ T0,
      (oddCount T : ℝ) ≥ c * (T / (2π) * log T)
  where `oddCount T` is the cardinality of a finset of DISTINCT critical-line
  zeta zeros of odd analytic multiplicity with `0 ≤ im ≤ T`.  We model that finset
  abstractly by a `zerosFinset : ℝ → Finset ℂ` together with the two structural
  facts the bridge actually consumes:
    (Z1) membership ⇒ genuine nontrivial zero with re = 1/2 and 0 ≤ im ≤ T
         (so the ordinate lands in `zetaOrdinates` and in the window [0,T]);
    (Z2) `oddCount T = (zerosFinset T).card`.
  Both (Z1) and (Z2) hold verbatim for `criticalLineOddZerosFinset` /
  `criticalLineOddZeroCount` in the source (see CriticalLineMultiplicity.lean).

  Once the 255-module Selberg mollifier mainline is ported to v4.32, `hSelberg`,
  `zerosFinset`, (Z1), (Z2) are all discharged by the ported artifacts and this
  bridge yields `rvm_unbounded_mean_density` with a clean 3-axiom closure.

  conjecture1_proved = False.
-/
import Mathlib

open Complex Filter
open scoped Topology

namespace RvMGlue

/-- Verbatim from MMDefs.lean (BoundaryLemmas.lean:342-344). -/
def RvMUnboundedMeanDensity (S : Set ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ∃ (F : Finset ℝ) (a L : ℝ),
    0 ≤ L ∧ (↑F ⊆ S) ∧ (∀ x ∈ F, x ∈ Set.Icc a (a + L)) ∧ r * L + 1 < F.card

/-- Verbatim from MMDefs.lean.  Matches `RiemannHypothesis.IsNontrivialZero`
(RiemannExplorer.lean:64 in the source) exactly. -/
def zetaOrdinates : Set ℝ :=
  {t : ℝ | ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ρ.im = t}

/-! ### The distinct bridge (kernel-proved from the abstract Selberg interface). -/

/-- **Distinct-bridge reduction.**  Given
* `zerosFinset T` : the DISTINCT critical-line odd-order zeros up to height `T`,
* (Z1) each element is a genuine nontrivial zero with `re = 1/2`, `0 ≤ im ≤ T`,
* (Z2) `oddCount T = (zerosFinset T).card`,
* `hSelberg` : the superlinear lower bound `oddCount T ≥ c·(T/2π)·log T`,

the ordinate set `zetaOrdinates` has unbounded windowed mean density.

Window used: `a = 0`, `L = T`; distinct count = `(zerosFinset T).card`; the
`im`-map is injective on `zerosFinset T` because every element has `re = 1/2`. -/
theorem rvm_unbounded_mean_density_of_selberg
    (zerosFinset : ℝ → Finset ℂ)
    (oddCount : ℝ → ℕ)
    (hZcard : ∀ T, oddCount T = (zerosFinset T).card)
    (hZmem : ∀ T, ∀ ρ ∈ zerosFinset T,
        riemannZeta ρ = 0 ∧ ρ.re = 1 / 2 ∧ 0 ≤ ρ.im ∧ ρ.im ≤ T)
    (hSelberg : ∃ c : ℝ, 0 < c ∧ ∃ T0 : ℝ, ∀ T ≥ T0,
        (oddCount T : ℝ) ≥ c * (T / (2 * Real.pi) * Real.log T)) :
    RvMUnboundedMeanDensity zetaOrdinates := by
  classical
  obtain ⟨c, hc, T0, hT⟩ := hSelberg
  intro r hr
  -- Choose T large enough that c·(T/2π)·log T > r·T + 1, and T ≥ max T0 (exp 1) 1.
  -- Since (c/2π)·log T → ∞, such T exists.  We produce it via an explicit threshold.
  -- Threshold: T ≥ T0, T ≥ 1, and (c/(2π))·log T ≥ r + 1  (then c·(T/2π)logT ≥ (r+1)T ≥ rT+1).
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  set K : ℝ := (r + 1) * (2 * Real.pi) / c with hK
  -- pick T = max (max T0 1) (exp K), so log T ≥ K.
  set T : ℝ := max (max T0 1) (Real.exp K) with hTdef
  have hTge0 : T ≥ T0 := le_trans (le_max_left _ _) (le_max_left _ _)
  have hT1 : (1 : ℝ) ≤ T := le_trans (le_max_right _ _) (le_max_left _ _)
  have hTpos : 0 < T := lt_of_lt_of_le one_pos hT1
  have hTexpK : Real.exp K ≤ T := le_max_right _ _
  have hlogT : K ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos K) hTexpK
    simpa [Real.log_exp] using this
  -- The finset of ordinates in the window [0, T].
  refine ⟨(zerosFinset T).image (fun ρ => ρ.im), 0, T, hTpos.le, ?_, ?_, ?_⟩
  · -- image ⊆ zetaOrdinates
    intro t ht
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at ht
    obtain ⟨ρ, hρ, rfl⟩ := ht
    obtain ⟨hzero, hre, _, _⟩ := hZmem T ρ hρ
    exact ⟨ρ, hzero, by rw [hre]; norm_num, by rw [hre]; norm_num, rfl⟩
  · -- image ⊆ Icc 0 (0 + T)
    intro t ht
    simp only [Finset.mem_image] at ht
    obtain ⟨ρ, hρ, rfl⟩ := ht
    obtain ⟨_, _, him0, himT⟩ := hZmem T ρ hρ
    exact ⟨by simpa using him0, by simpa using himT⟩
  · -- cardinality: r * T + 1 < (image im).card = (zerosFinset T).card
    have hinj : Set.InjOn (fun ρ : ℂ => ρ.im) (zerosFinset T) := by
      intro x hx y hy hxy
      obtain ⟨_, hxre, _, _⟩ := hZmem T x (by simpa using hx)
      obtain ⟨_, hyre, _, _⟩ := hZmem T y (by simpa using hy)
      apply Complex.ext
      · rw [hxre, hyre]
      · exact hxy
    have hcardimg : ((zerosFinset T).image (fun ρ => ρ.im)).card = (zerosFinset T).card :=
      Finset.card_image_of_injOn hinj
    rw [hcardimg]
    -- lower bound on (zerosFinset T).card via Selberg
    have hSel := hT T hTge0
    rw [hZcard] at hSel
    -- c * (T/2π) * log T ≥ (r+1) * T  from log T ≥ K = (r+1)(2π)/c
    have hstep : c * (T / (2 * Real.pi) * Real.log T) ≥ (r + 1) * T := by
      have hmul : c * (T / (2 * Real.pi) * K) ≤ c * (T / (2 * Real.pi) * Real.log T) := by
        apply mul_le_mul_of_nonneg_left _ hc.le
        apply mul_le_mul_of_nonneg_left hlogT
        positivity
      have heq : c * (T / (2 * Real.pi) * K) = (r + 1) * T := by
        have hcne : c ≠ 0 := ne_of_gt hc
        have hpine : (2 * Real.pi) ≠ 0 := ne_of_gt hpi
        rw [hK]
        field_simp
      linarith [hmul, heq]
    have hcardReal : (r + 1) * T ≤ ((zerosFinset T).card : ℝ) := le_trans hstep hSel
    -- r*T + 1 < (r+1)*T  since T ≥ 1  ⇒  r*T + 1 ≤ (r+1)*T ... need strict.
    -- (r+1)*T = r*T + T ≥ r*T + 1, and we need STRICT r*T+1 < card.
    -- Use: r*T + 1 ≤ (r+1)*T ≤ card; strictness from T > 1 OR card being a nat > (r+1)*T is not given.
    -- Instead bump threshold: we actually have card ≥ (r+1)*T ≥ r*T + T ≥ r*T + 1.
    -- For STRICT, note (r+1)*T = r*T + T and T ≥ 1, giving r*T + 1 ≤ card. Need <.
    -- Strengthen: since we only need SOME window, use r' := r and the +1 slack from T>1
    -- when T>1 strictly. Ensure T>1 strictly by threshold max ... 2.
    -- (Handled by choosing exp K possibly =1; we instead argue via nat strictness below.)
    have hTgt1 : (1 : ℝ) < T := by
      -- exp K ≥ 1 and if K>0 strict; ensure via K ≥ 0 and exp K ≥ 1, plus max with...
      -- Fallback: T ≥ exp K ≥ 1; if equality, then log T = 0 < K unless K ≤ 0.
      -- Simplest: r*T+1 < (r+1)*T ⟺ 1 < T. We secure 1 < T from K ≥ 0 ⇒ needs K>0.
      have hKpos : 0 < K := by
        rw [hK]; positivity
      have : Real.exp K > 1 := by
        have := Real.add_one_lt_exp (ne_of_gt hKpos)
        linarith
      linarith [le_trans this.le hTexpK, this]
    have : r * T + 1 < (r + 1) * T := by nlinarith [hTgt1, hr]
    calc r * T + 1 < (r + 1) * T := this
      _ ≤ ((zerosFinset T).card : ℝ) := hcardReal
      _ = ((zerosFinset T).card : ℝ) := rfl

end RvMGlue
