/-  ArgChangeGlue.lean -- bricks K6a + K6b + K6c consumed by the K0/K1 band glue
    (telperion/docs/ANDURIL_ARB_DISCHARGE_2026-09-23.md, section 1.3; `BandGlue.lean`,
    `EdgeClearGlue.lean`).

    `BandGlue.BandData.EnclHyp` is the five-enclosure tail of the `hArbT` binder of every emitted
    Turing band.  After this file:
      * conjunct 5 (`hAV2`, σ = 2 vertical of ζ) is discharged for EVERY band by K6a
        (`ArgZetaTwo.hAV2_of_le`), given the rational side condition `[L1, H1] ⊇ [-249/250, 249/250]`;
      * conjuncts 8, 9 (`hAG1`, `hAG2`, Γℝ verticals) are discharged for every band with
        `0 ≤ T0`, `0 ≤ T1` by K6b (`ArgGammaR.hAG1_of_bounds`, `hAG2_of_bounds`), given rational
        side conditions comparing `L4 H4 L5 H5` with the closed-form brackets `Sm1`, `S2`;
      * conjuncts 6, 7 (`hAHt`, `hAHb`, the horizontal edges) remain as `HorizHyp`, which K6c
        (`ArgHoriz.hAH_of_octCert_boxes`) reduces to an octant certificate plus two point
        enclosures per edge (`HorizHyp.of_octCerts`).
    Combined with K1 (`EdgeClearGlue`), the per-band input becomes `K6Inputs`: the on-line zeros,
    two zero-free edge slabs and the two horizontal enclosures.  `BoxCert.of_K6`,
    `segBandHyp_of_K6` and `ladder_of_K6` feed it into the K0 composition unchanged.

    Trust: no hypotheses beyond those stated; axioms [propext, Classical.choice, Quot.sound]
    (see AxiomGuardArgChange.lean).  No `sorry`.

    conjecture1_proved = False.  Glue for a finite verification up to a fixed height. -/
import Mathlib
import BandGlue
import ArgZetaTwo
import ArgGammaR
import ArgHoriz

open Complex

namespace ArgChangeGlue

open BandGlue BandGlue.BandData

/-- The rational side conditions under which K6a and K6b discharge conjuncts 5, 8 and 9 of a
    band's `hArbT` binder. -/
structure K6Side (d : BandData) : Prop where
  hT0 : 0 ≤ d.T0
  hT1 : 0 ≤ d.T1
  hL1 : d.L1 ≤ -(249 / 250)
  hH1 : 249 / 250 ≤ d.H1
  hL4 : d.L4 ≤ ArgGammaR.Sm1 d.T1 - ArgGammaR.Sm1 d.T0 - ArgGammaR.em1 d.T1
  hH4 : ArgGammaR.Sm1 d.T1 - ArgGammaR.Sm1 d.T0 + ArgGammaR.em1 d.T0 ≤ d.H4
  hL5 : d.L5 ≤ ArgGammaR.S2 d.T1 - ArgGammaR.S2 d.T0 - ArgGammaR.e2 d.T1
  hH5 : ArgGammaR.S2 d.T1 - ArgGammaR.S2 d.T0 + ArgGammaR.e2 d.T0 ≤ d.H5

/-- The two horizontal conjuncts of `EnclHyp` (6 and 7), the only enclosures K6a/K6b leave. -/
def HorizHyp (d : BandData) : Prop :=
  DiffractionCore.argChangeHoriz riemannZeta d.T1 2 (-1) ∈ Set.Icc d.L2 d.H2 ∧
    DiffractionCore.argChangeHoriz riemannZeta d.T0 2 (-1) ∈ Set.Icc d.L3 d.H3

/-- **K6a + K6b inside a band**: the five enclosures from the side conditions and the two
    horizontal ones. -/
theorem enclHyp_of_K6 {d : BandData} (hS : K6Side d) (hH : HorizHyp d) : d.EnclHyp :=
  ⟨ArgZetaTwo.hAV2_of_le hS.hL1 hS.hH1, hH.1, hH.2,
    ArgGammaR.hAG1_of_bounds hS.hT0 hS.hT1 hS.hL4 hS.hH4,
    ArgGammaR.hAG2_of_bounds hS.hT0 hS.hT1 hS.hL5 hS.hH5⟩

/-- **K6c inside a band**: the two horizontal conjuncts from any proofs of the binder form (for
    instance two applications of `ArgHoriz.hAH_of_octCert_boxes`, one per edge). -/
theorem HorizHyp.of_edges {d : BandData}
    (ht : DiffractionCore.argChangeHoriz riemannZeta d.T1 2 (-1) ∈ Set.Icc d.L2 d.H2)
    (hb : DiffractionCore.argChangeHoriz riemannZeta d.T0 2 (-1) ∈ Set.Icc d.L3 d.H3) :
    HorizHyp d := ⟨ht, hb⟩

/-- **K6c inside a band, certificate form**: an octant certificate from `2` to `-1` at each edge
    height (valid labels, no crossing) makes `HorizHyp` equivalent to the two exact octant-angle
    differences lying in `[L2, H2]` and `[L3, H3]`: only the four endpoint values of ζ remain. -/
theorem HorizHyp.of_octCerts {d : BandData} (hT0 : d.T0 ≠ 0) (hT1 : d.T1 ≠ 0)
    (ct cb : ArgHoriz.OctCert) (hmt : 1 ≤ ct.m) (hmb : 1 ≤ cb.m)
    (hpt0 : ct.p 0 = 2) (hptm : ct.p ct.m = -1) (hpb0 : cb.p 0 = 2) (hpbm : cb.p cb.m = -1)
    (hst : ct.StepOK) (hsb : cb.StepOK)
    (hnt : ct.NoCross riemannZeta d.T1) (hnb : cb.NoCross riemannZeta d.T0)
    (ht : ArgHoriz.octAngle (ct.k (ct.m - 1)) (riemannZeta (((-1 : ℝ) : ℂ) + (d.T1 : ℂ) * I))
        - ArgHoriz.octAngle (ct.k 0) (riemannZeta (((2 : ℝ) : ℂ) + (d.T1 : ℂ) * I))
        ∈ Set.Icc d.L2 d.H2)
    (hb : ArgHoriz.octAngle (cb.k (cb.m - 1)) (riemannZeta (((-1 : ℝ) : ℂ) + (d.T0 : ℂ) * I))
        - ArgHoriz.octAngle (cb.k 0) (riemannZeta (((2 : ℝ) : ℂ) + (d.T0 : ℂ) * I))
        ∈ Set.Icc d.L3 d.H3) :
    HorizHyp d := by
  refine ⟨?_, ?_⟩
  · rw [ArgHoriz.argChangeHoriz_zeta_eq_of_octCert hT1 ct hmt hpt0 hptm hst hnt]; exact ht
  · rw [ArgHoriz.argChangeHoriz_zeta_eq_of_octCert hT0 cb hmb hpb0 hpbm hsb hnb]; exact hb

/-- The per-band input after K1 + K6a + K6b: the on-line zeros, the two edge-clearance slabs and
    the two horizontal argument-change enclosures (four of the nine `hArbT` conjuncts are gone:
    `hnzl` by K1, `hAV2` by K6a, `hAG1`/`hAG2` by K6b). -/
def K6Inputs (δ0 δ1 : ℝ) (d : BandData) : Prop :=
  d.LineHyp ∧ EdgeClearGlue.SlabClear (d.T0 - δ0) d.T0 ∧
    EdgeClearGlue.SlabClear d.T1 (d.T1 + δ1) ∧ HorizHyp d

/-- K1 + K6: the reduced input, the cap geometry and the rational side conditions give the full
    `Inputs` of the band. -/
theorem inputs_of_K6 {δ0 δ1 : ℝ} {d : BandData} (hG : d.CapGeom δ0 δ1) (hS : K6Side d)
    (h : K6Inputs δ0 δ1 d) : d.Inputs :=
  inputs_of_reduced hG ⟨h.1, h.2.1, h.2.2.1, enclHyp_of_K6 hS h.2.2.2⟩

/-- A band certificate for a box from a band statement, the cap geometry, the K6 side conditions
    and the K6-reduced inputs. -/
theorem BoxCert.of_K6 {σ0 σ1 lo hi δ0 δ1 : ℝ} (d : BandData) (hlo : d.T0 ≤ lo) (hhi : hi ≤ d.T1)
    (hstmt : d.Stmt σ0 σ1) (hG : d.CapGeom δ0 δ1) (hS : K6Side d) (hin : K6Inputs δ0 δ1 d) :
    BoxCert σ0 σ1 lo hi :=
  ⟨d, hlo, hhi, hstmt, inputs_of_K6 hG hS hin⟩

/-- **K0 + K1 + K6 (indexed band table)**: the `SegBandHyp` shape from the K6-reduced inputs. -/
theorem segBandHyp_of_K6 {σ0 σ1 : ℝ} {count : ℕ} {lo hi : ℕ → ℝ} {δ0 δ1 : ℕ → ℝ}
    (d : ℕ → BandData)
    (hedge : ∀ i, i < count → (d i).T0 ≤ lo i ∧ hi i ≤ (d i).T1)
    (hstmt : ∀ i, i < count → (d i).Stmt σ0 σ1)
    (hgeom : ∀ i, i < count → (d i).CapGeom (δ0 i) (δ1 i))
    (hside : ∀ i, i < count → K6Side (d i))
    (hin : ∀ i, i < count → K6Inputs (δ0 i) (δ1 i) (d i)) :
    ∀ i, i < count → ∀ ρ : ℂ, (σ0 ≤ ρ.re ∧ ρ.re ≤ σ1) → (lo i ≤ ρ.im ∧ ρ.im ≤ hi i) →
      riemannZeta ρ = 0 → ρ.re = 1 / 2 :=
  segBandHyp_of_bands d hedge hstmt fun i hi' => inputs_of_K6 (hgeom i hi') (hside i hi') (hin i hi')

/-- **K0 + K1 + K6, ladder form** (`∀ k, k < K → SegBandHyp k` at the capstone's parameters). -/
theorem ladder_of_K6 {σ0 σ1 : ℝ} {K : ℕ} {count : ℕ → ℕ} {lo hi : ℕ → ℕ → ℝ}
    {δ0 δ1 : ℕ → ℕ → ℝ} (d : ℕ → ℕ → BandData)
    (hedge : ∀ k, k < K → ∀ i, i < count k → (d k i).T0 ≤ lo k i ∧ hi k i ≤ (d k i).T1)
    (hstmt : ∀ k, k < K → ∀ i, i < count k → (d k i).Stmt σ0 σ1)
    (hgeom : ∀ k, k < K → ∀ i, i < count k → (d k i).CapGeom (δ0 k i) (δ1 k i))
    (hside : ∀ k, k < K → ∀ i, i < count k → K6Side (d k i))
    (hin : ∀ k, k < K → ∀ i, i < count k → K6Inputs (δ0 k i) (δ1 k i) (d k i)) :
    ∀ k, k < K → ∀ i, i < count k → ∀ ρ : ℂ, (σ0 ≤ ρ.re ∧ ρ.re ≤ σ1) →
      (lo k i ≤ ρ.im ∧ ρ.im ≤ hi k i) → riemannZeta ρ = 0 → ρ.re = 1 / 2 :=
  fun k hk => segBandHyp_of_K6 (d k) (hedge k hk) (hstmt k hk) (hgeom k hk) (hside k hk) (hin k hk)

/-! ## Band-table helpers (for emitted K6 segments) -/

/-- The ball `ball ⟨1/2, m⟩ √q` covers the RvM rectangle `[-1, 2] x [T0, T1]` once
    `9/4 + (T1 - m)² < q` and `9/4 + (m - T0)² < q` (the squared distances to its corners). -/
theorem ball_of_sq {T0 T1 m q : ℝ} {c : ℂ} {R : ℝ} (hcre : c.re = 1 / 2) (hcim : c.im = m)
    (hR : R = Real.sqrt q) (hq1 : 9 / 4 + (T1 - m) ^ 2 < q) (hq0 : 9 / 4 + (m - T0) ^ 2 < q) :
    ∀ ρ : ℂ, ((-1 : ℝ) ≤ ρ.re ∧ ρ.re ≤ 2) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) → ρ ∈ Metric.ball c R := by
  intro ρ hre him
  rw [Metric.mem_ball, Complex.dist_eq_re_im, hR, hcre, hcim]
  have hx : (ρ.re - 1 / 2) ^ 2 ≤ 9 / 4 := by nlinarith [hre.1, hre.2]
  have hy : (ρ.im - m) ^ 2 < q - 9 / 4 := by
    rcases le_total m ρ.im with h | h
    · nlinarith [him.2]
    · nlinarith [him.1]
  exact Real.sqrt_lt_sqrt (by positivity) (by linarith)

/-- `CapGeom` only depends on `T0`, `T1`, `c`, `R`: it transfers between band data that agree on
    them (for instance a band and its K6 re-parametrisation). -/
theorem capGeom_transfer {δ0 δ1 : ℝ} {d d' : BandData} (hT0 : d'.T0 = d.T0) (hT1 : d'.T1 = d.T1)
    (hc : d'.c = d.c) (hR : d'.R = d.R) (h : d.CapGeom δ0 δ1) : d'.CapGeom δ0 δ1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨by rw [hT0]; exact h1, by rw [hT1]; exact h2, h3, h4, by rw [hc, hR]; exact h5,
    by rw [hT0, hc, hR]; exact h6, by rw [hT1, hc, hR]; exact h7⟩

/-! ## K6a feeding K6c: the `x = 2` endpoint of every horizontal edge -/

/-- At the `x = 2` end of a horizontal edge, octant `0` (`Re w > 0`) never needs an evaluator:
    `ζ(2 + i T)` is in the open right half-plane for every `T` (K6a). -/
theorem octX_zero_zeta_two_pos (T : ℝ) :
    0 < ArgHoriz.octX 0 (riemannZeta (((2 : ℝ) : ℂ) + (T : ℂ) * I)) := by
  have hA : ArgHoriz.octA 0 = 1 := by decide
  have hB : ArgHoriz.octB 0 = 0 := by decide
  unfold ArgHoriz.octX
  rw [hA, hB, show (((2 : ℝ)) : ℂ) = (2 : ℂ) by norm_num]
  simpa using ArgZetaTwo.re_zeta_two_pos T

/-- The octant-`0` angle at the `x = 2` end is the principal argument of `ζ(2 + i T)`, so K6a
    encloses it generically: `|octAngle 0 ζ(2 + i T)| ≤ log ζ(2) < 249/500`.  A coarse endpoint
    enclosure with no evaluation at all (width about 1 rad). -/
theorem octAngle_zero_zeta_two_abs_le (T : ℝ) :
    |ArgHoriz.octAngle 0 (riemannZeta (((2 : ℝ) : ℂ) + (T : ℂ) * I))| ≤ Real.log (Real.pi ^ 2 / 6) := by
  have hA : ArgHoriz.octA 0 = 1 := by decide
  have hB : ArgHoriz.octB 0 = 0 := by decide
  have h2 : (((2 : ℝ)) : ℂ) = (2 : ℂ) := by norm_num
  have hre := ArgZetaTwo.re_zeta_two_pos T
  have harg := ThetaValue.arg_eq_arctan_of_re_pos hre
  unfold ArgHoriz.octAngle ArgHoriz.octY ArgHoriz.octX
  rw [hA, hB, h2]
  simp only [Int.cast_zero, zero_mul, zero_div, Int.cast_one, one_mul, zero_add, sub_zero, add_zero]
  rw [← harg]
  exact ArgZetaTwo.abs_arg_zeta_two_le T

end ArgChangeGlue
