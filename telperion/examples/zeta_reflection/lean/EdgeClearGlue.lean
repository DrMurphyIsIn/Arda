/-  EdgeClearGlue.lean -- brick K1 of the ANDURIL Arb discharge
    (telperion/docs/ANDURIL_ARB_DISCHARGE_2026-09-23.md, section 1.3: `hArbT_nonvanishing_of_edge_clear`).

    Every emitted Turing band `RHInBoxT_*.rh_in_box_*` states the canonical
    `TuringBand.BandStatement` and takes an Arb binder `hArbT` with nine conjuncts.  The first four
    are non-vanishing and confinement facts about the RvM rectangle `[-1, 2] x [T0, T1]` and the
    Blaschke ball `ball c R` that covers it:

      hnzb : ∀ x ∈ [-1, 2], ζ(x + T0 i) ≠ 0                      (H2a, bottom edge)
      hnzt : ∀ x ∈ [-1, 2], ζ(x + T1 i) ≠ 0                      (H2a, top edge)
      hnzl : ∀ y ∈ [T0, T1], ζ(-1 + y i) ≠ 0                     (H2b, left edge)
      hins : every zero of ζ in `ball c R` lies in (-1, 2) x (T0, T1)   (H2c, confinement)

    This file derives all four from
      * `ZetaZeroConfinement.zeta_zero_re_mem_strip`: an off-real zero of ζ has 0 < Re < 1;
      * the ball geometry: three rational/sqrt inequalities about c, R, T0, T1 (decidable per band);
      * two EDGE-CLEARANCE facts, the memo's E(T0, δ0) and E(T1, δ1), as zero-free SLABS on the
        OUTER side of each edge: `SlabClear (T0 - δ0) T0` and `SlabClear T1 (T1 + δ1)`, where
        `SlabClear a b` says ζ has no zero with 0 < Re < 1 and a ≤ Im ≤ b.

    H2b needs no input at all: `hnzl_discharged` proves the conjunct for EVERY `T0`, `T1`, with no
    hypotheses (off the real axis by the strip theorem; at y = 0 by ζ(-1) = -1/12).  That removes
    one binder from each of the 10,379 bands of the h280000 ladder.

    What remains numerical after this file: two one-sided slab facts per band, about the open strip
    0 < Re < 1 only.  WHY ONE-SIDED, AND HOW TALL (measured on the h280000 ladder with the float
    zero list at grid 0.01, the tight cases refined with mpmath; untrusted numerics, design only):
      * ONE-SIDED: at about 2,831 band edges a zero lies on the INNER side of the edge closer than
        the ball cap (as close as the grid resolves), so even a two-sided window of half-height
        equal to the cap would be false there.  Inner-side zeros are counted by the band; only
        the outer side must be clear, and that is all `hins` needs.
      * TALL ENOUGH, NOT TOO TALL: the slab must reach past the ball cap (δ ≥ cap; caps are 0.0574
        to 0.0922) and must stop before the nearest zero beyond the edge.  The margin between the
        two is as small as 4.3e-5 (top edge 154974: cap 0.092160, zero at 154974.092203).  So δ
        must be the band's own cap rounded up finely (emit_band_glue.py uses 1e-6); a round
        δ = 1/10 would make the slab hypothesis false at about 385 of the 10,379 bands.

    Trust: no hypotheses beyond those named in each statement; axioms
    [propext, Classical.choice, Quot.sound] (see AxiomGuardBandGlue.lean).  No `sorry`.

    conjecture1_proved = False.  This is glue for a finite verification up to a fixed height; it
    says nothing about the Riemann Hypothesis. -/
import Mathlib
import TuringBand
import ZetaZeroConfinement

open Complex

namespace EdgeClearGlue

/-! ## Zeta off the critical strip -/

/-- ζ has no zero with `Re s ≤ 0` off the real axis (the strip theorem, contrapositive). -/
theorem riemannZeta_ne_zero_of_re_nonpos {s : ℂ} (hre : s.re ≤ 0) (him : s.im ≠ 0) :
    riemannZeta s ≠ 0 := fun hz =>
  absurd (ZetaZeroConfinement.zeta_zero_re_mem_strip him hz).1 (not_lt.mpr hre)

/-- `ζ(-1) = -1/12`, via `riemannZeta_neg_nat_eq_bernoulli` at `k = 1` and `bernoulli 2 = 1/6`. -/
theorem riemannZeta_neg_one : riemannZeta (-1) = -1 / 12 := by
  have h := riemannZeta_neg_nat_eq_bernoulli 1
  simp only [Nat.cast_one, pow_one, Nat.reduceAdd] at h
  rw [h, bernoulli_two]
  norm_num

/-- `ζ(-1) ≠ 0`. -/
theorem riemannZeta_neg_one_ne_zero : riemannZeta (-1) ≠ 0 := by
  rw [riemannZeta_neg_one]; norm_num

/-- **H2b, pointwise**: `ζ(-1 + y i) ≠ 0` for EVERY real `y`. -/
theorem riemannZeta_neg_one_add_mul_I_ne_zero (y : ℝ) :
    riemannZeta (((-1 : ℝ) : ℂ) + (y : ℂ) * I) ≠ 0 := by
  by_cases hy : y = 0
  · subst hy
    have h : (((-1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I) = -1 := by push_cast; ring
    rw [h]; exact riemannZeta_neg_one_ne_zero
  · apply riemannZeta_ne_zero_of_re_nonpos
    · simp
    · simpa using hy

/-- **H2b DISCHARGED** (the `hnzl` conjunct of every Turing band, verbatim shape): no
    hypotheses, for all `T0`, `T1`. -/
theorem hnzl_discharged (T0 T1 : ℝ) :
    ∀ y ∈ Set.uIcc T0 T1, riemannZeta (((-1 : ℝ) : ℂ) + ↑y * I) ≠ 0 :=
  fun y _ => riemannZeta_neg_one_add_mul_I_ne_zero y

/-! ## Edge clearance: zero-free slabs -/

/-- **Zero-free slab**: ζ has no zero with `0 < Re < 1` and `a ≤ Im ≤ b`.  The edge-clearance
    facts E(T0, δ0), E(T1, δ1) of the memo are `SlabClear (T0 - δ0) T0` (below the bottom edge)
    and `SlabClear T1 (T1 + δ1)` (above the top edge).  Outside `0 < Re < 1` the strip theorem
    already rules zeros out, so this is the only numerical input the four conjuncts need. -/
def SlabClear (a b : ℝ) : Prop :=
  ∀ x y : ℝ, 0 < x → x < 1 → a ≤ y → y ≤ b → riemannZeta ((x : ℂ) + (y : ℂ) * I) ≠ 0

/-- A sub-slab of a zero-free slab is zero-free. -/
theorem SlabClear.mono {a b a' b' : ℝ} (hE : SlabClear a b) (ha : a ≤ a') (hb : b' ≤ b) :
    SlabClear a' b' :=
  fun x y h0 h1 hy0 hy1 => hE x y h0 h1 (le_trans ha hy0) (le_trans hy1 hb)

/-- **H2a from a slab containing the edge height**: the whole horizontal edge `[-1, 2] + T i` is
    zero-free (in fact every `x`, not only `x ∈ [-1, 2]`), given `T ≠ 0`. -/
theorem hnz_edge_of_slabClear {T a b : ℝ} (hT : T ≠ 0) (ha : a ≤ T) (hb : T ≤ b)
    (hE : SlabClear a b) :
    ∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta (↑x + (T : ℂ) * I) ≠ 0 := by
  intro x _ hz
  have him : ((x : ℂ) + (T : ℂ) * I).im ≠ 0 := by simpa using hT
  obtain ⟨h0, h1⟩ := ZetaZeroConfinement.zeta_zero_re_mem_strip him hz
  have hre : ((x : ℂ) + (T : ℂ) * I).re = x := by simp
  rw [hre] at h0 h1
  exact hE x T h0 h1 ha hb hz

/-! ## Confinement of the Blaschke-ball zeros -/

/-- A point of the divisor support of ζ over `ball c R` lies in the ball and is a zero of ζ. -/
theorem mem_ball_and_zero_of_mem_zeroFinset {c : ℂ} {R : ℝ} (hs1 : (1 : ℂ) ∉ Metric.ball c R)
    {ρ : ℂ} (h : ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1) :
    ρ ∈ Metric.ball c R ∧ riemannZeta ρ = 0 := by
  rw [RHInBoxAnalytic.mem_zeroFinset] at h
  have hU : ρ ∈ Metric.ball c R :=
    (MeromorphicOn.divisor riemannZeta (Metric.ball c R)).supportWithinDomain h
  refine ⟨hU, ?_⟩
  have hUsub : Metric.ball c R ⊆ ({1}ᶜ : Set ℂ) := by
    intro z hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl; exact hs1 hz
  have hζU : AnalyticOnNhd ℂ riemannZeta (Metric.ball c R) := analyticOn_riemannZeta.mono hUsub
  by_contra hne
  rw [Function.mem_support] at h
  apply h
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hζU hU,
    (hζU ρ hU).analyticOrderAt_eq_zero.mpr hne]
  simp

/-- The imaginary part of a point of `ball c R` lies strictly within `R` of `c.im`. -/
theorem im_mem_of_mem_ball {c ρ : ℂ} {R : ℝ} (h : ρ ∈ Metric.ball c R) :
    c.im - R < ρ.im ∧ ρ.im < c.im + R := by
  rw [Metric.mem_ball, Complex.dist_eq] at h
  have h1 : |(ρ - c).im| ≤ ‖ρ - c‖ := Complex.abs_im_le_norm _
  rw [Complex.sub_im] at h1
  have h2 := abs_lt.mp (lt_of_le_of_lt h1 h)
  constructor <;> linarith [h2.1, h2.2]

/-- **H2c from E(T0, δ0), E(T1, δ1) and the ball geometry.**  If the ball sits above the real
    axis (`0 ≤ c.im - R`) and its bottom and top caps stay within the zero-free slabs below `T0`
    and above `T1` (`T0 - δ0 ≤ c.im - R`, `c.im + R ≤ T1 + δ1`), every zero of ζ in the ball lies
    in the open rectangle `(-1, 2) x (T0, T1)`. -/
theorem hins_of_slabClear {T0 T1 δ0 δ1 : ℝ} {c : ℂ} {R : ℝ} (hs1 : (1 : ℂ) ∉ Metric.ball c R)
    (hpos : 0 ≤ c.im - R) (hlo : T0 - δ0 ≤ c.im - R) (hhi : c.im + R ≤ T1 + δ1)
    (hE0 : SlabClear (T0 - δ0) T0) (hE1 : SlabClear T1 (T1 + δ1)) :
    ∀ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
      (-1 : ℝ) < ρ.re ∧ ρ.re < 2 ∧ T0 < ρ.im ∧ ρ.im < T1 := by
  intro ρ hρ
  obtain ⟨hball, hz⟩ := mem_ball_and_zero_of_mem_zeroFinset hs1 hρ
  obtain ⟨him_lo, him_hi⟩ := im_mem_of_mem_ball hball
  have him : ρ.im ≠ 0 := ne_of_gt (by linarith)
  obtain ⟨hre0, hre1⟩ := ZetaZeroConfinement.zeta_zero_re_mem_strip him hz
  have hρeq : ((ρ.re : ℂ) + (ρ.im : ℂ) * I) = ρ := Complex.re_add_im ρ
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · by_contra hle'
    have hle : ρ.im ≤ T0 := not_lt.mp hle'
    exact hE0 ρ.re ρ.im hre0 hre1 (by linarith) hle (by rw [hρeq]; exact hz)
  · by_contra hle'
    have hle : T1 ≤ ρ.im := not_lt.mp hle'
    exact hE1 ρ.re ρ.im hre0 hre1 hle (by linarith) (by rw [hρeq]; exact hz)

/-- **K1: `hArbT_nonvanishing_of_edge_clear`.**  The four non-vanishing / confinement conjuncts
    of a Turing band's `hArbT` binder, in the verbatim shape of `TuringBand.BandStatement`, from
    the two edge-clearance slabs (below `T0`, above `T1`) and the ball geometry.  `hnzl` needs
    neither. -/
theorem hArbT_nonvanishing_of_edge_clear {T0 T1 δ0 δ1 : ℝ} {c : ℂ} {R : ℝ}
    (hs1 : (1 : ℂ) ∉ Metric.ball c R)
    (hT0 : T0 ≠ 0) (hT1 : T1 ≠ 0) (hδ0 : 0 ≤ δ0) (hδ1 : 0 ≤ δ1)
    (hpos : 0 ≤ c.im - R) (hlo : T0 - δ0 ≤ c.im - R) (hhi : c.im + R ≤ T1 + δ1)
    (hE0 : SlabClear (T0 - δ0) T0) (hE1 : SlabClear T1 (T1 + δ1)) :
    (∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta (↑x + (T0 : ℂ) * I) ≠ 0) ∧
    (∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta (↑x + (T1 : ℂ) * I) ≠ 0) ∧
    (∀ y ∈ Set.uIcc T0 T1, riemannZeta (((-1 : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
    (∀ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
      (-1 : ℝ) < ρ.re ∧ ρ.re < 2 ∧ T0 < ρ.im ∧ ρ.im < T1) :=
  ⟨hnz_edge_of_slabClear hT0 (by linarith) le_rfl hE0,
    hnz_edge_of_slabClear hT1 le_rfl (by linarith) hE1, hnzl_discharged T0 T1,
    hins_of_slabClear hs1 hpos hlo hhi hE0 hE1⟩

/-! ## Ball geometry for a `Real.sqrt` radius (the emitted bands use `R = √q`, `q` rational) -/

/-- Bottom cap: `T0 - δ0 ≤ c.im - √q` from `q ≤ (c.im - T0 + δ0)²` with `0 ≤ c.im - T0 + δ0`. -/
theorem cap_lo_of_sq {cim T0 δ0 q : ℝ} (hb : 0 ≤ cim - T0 + δ0) (hq : q ≤ (cim - T0 + δ0) ^ 2) :
    T0 - δ0 ≤ cim - Real.sqrt q := by
  have h : Real.sqrt q ≤ cim - T0 + δ0 := Real.sqrt_le_iff.mpr ⟨hb, hq⟩
  linarith

/-- Top cap: `c.im + √q ≤ T1 + δ1` from `q ≤ (T1 + δ1 - c.im)²` with `0 ≤ T1 + δ1 - c.im`. -/
theorem cap_hi_of_sq {cim T1 δ1 q : ℝ} (hb : 0 ≤ T1 + δ1 - cim) (hq : q ≤ (T1 + δ1 - cim) ^ 2) :
    cim + Real.sqrt q ≤ T1 + δ1 := by
  have h : Real.sqrt q ≤ T1 + δ1 - cim := Real.sqrt_le_iff.mpr ⟨hb, hq⟩
  linarith

/-- Ball above the real axis: `0 ≤ c.im - √q` from `q ≤ c.im²` with `0 ≤ c.im`. -/
theorem ball_above_of_sq {cim q : ℝ} (hb : 0 ≤ cim) (hq : q ≤ cim ^ 2) :
    0 ≤ cim - Real.sqrt q := by
  have h : Real.sqrt q ≤ cim := Real.sqrt_le_iff.mpr ⟨hb, hq⟩
  linarith

end EdgeClearGlue
