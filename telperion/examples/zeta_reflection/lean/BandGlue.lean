/-  BandGlue.lean -- brick K0 of the ANDURIL Arb discharge
    (telperion/docs/ANDURIL_ARB_DISCHARGE_2026-09-23.md, section 1.3: `segBandHyp_of_bands`).

    THE GAP IT CLOSES.  The h280000 capstone
    `AllZeros_h280000_Indexed.all_nontrivial_zeros_up_to_height_280000` takes
    `hbands : ∀ k, k < 280 → SegBandHyp k`, and each `SegBandHyp k` is a list of BOX CLAIMS
    ("every zero of ζ in `[1/4000000, 3999999/4000000] x [segLo k i, segHi k i]` is on the line").
    Every box claim is the conclusion of one emitted band theorem `RHInBoxT_*.rh_in_box_*`, but the
    capstone ASSUMES the claims: nothing composes them.  This file makes the composition a theorem,
    parametric in the per-band Arb inputs, so a future evaluator only has to supply those inputs.

    CONTENTS.
      * `BandData`: the parameters of one Turing band, i.e. the arguments of the canonical
        `TuringBand.BandStatement` other than the strip.  `Stmt`, `LineHyp`, `ArbHyp`, `EnclHyp`,
        `Box`, `Inputs`.  `stmt_iff` checks, by `Iff.rfl`, that `LineHyp`/`ArbHyp` are EXACTLY the
        two binders of `BandStatement` (so `Inputs` is what `hLine`/`hArbT` ask for, verbatim).
      * `stmt_of_valid`: the band statement from its decidable side conditions (pins, ball
        geometry), via `TuringBand.turing_band_on_line`; the generic proof of every `rh_in_box_*`.
      * K0 generic: `segBandHyp_of_bands` (indexed band table: the `SegBandHyp` shape),
        `segBandHyp_of_bandList` (a `List` of bands), `ladder_of_bands` (a ladder of segments: the
        `∀ k, k < K → SegBandHyp k` shape the capstone consumes).  Bands may COVER their boxes
        (`T0 ≤ lo`, `hi ≤ T1`); the emitted ladder has equality.
      * K0 + K1: `ReducedInputs` (on-line zeros, two one-sided edge-clearance slabs, five
        enclosures) and `CapGeom` (decidable ball-cap geometry); `inputs_of_reduced`,
        `segBandHyp_of_reduced`, `ladder_of_reduced` (per-band slab heights).  With K1 the `hnzl`
        binder disappears and `hnzb`/`hnzt`/`hins` reduce to two zero-free slabs per band.
      * Certificate form: `BoxCert σ0 σ1 lo hi` (some band covering the box, with its statement
        and its inputs), constructors `of_stmt` / `of_valid` / `of_reduced`, and
        `segBandHyp_of_certs`, `ladder_of_certs`.  A future evaluator may pick its own band
        parameters here (for instance enclosures much wider than the 1e-12 Arb ones, as long as
        the pins hold), which the fixed-table form does not allow.

    The real-segment instantiation (segment 0 of the ladder, 25 bands, the real `rh_in_box_*`
    theorems) is `BandGlue_h1000.lean`.

    Trust: every theorem here is proved outright from its stated hypotheses; axioms
    [propext, Classical.choice, Quot.sound] (see AxiomGuardBandGlue.lean).  No `sorry`.

    conjecture1_proved = False.  Glue for a finite verification up to a fixed height; nothing
    here says anything about the Riemann Hypothesis. -/
import Mathlib
import TuringBand
import RHInBox
import EdgeClearGlue

open Complex

namespace BandGlue

/-- The parameters of one Turing band certificate: exactly the arguments of
    `TuringBand.BandStatement` other than the strip `σ0, σ1`. -/
structure BandData where
  T0 : ℝ
  T1 : ℝ
  n : ℕ
  L1 : ℝ
  H1 : ℝ
  L2 : ℝ
  H2 : ℝ
  L3 : ℝ
  H3 : ℝ
  L4 : ℝ
  H4 : ℝ
  L5 : ℝ
  H5 : ℝ
  c : ℂ
  R : ℝ
  hs1 : (1 : ℂ) ∉ Metric.ball c R

/-- A default band (empty ball), so that band tables can have a catch-all arm. -/
instance : Inhabited BandData :=
  ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, by simp⟩⟩

namespace BandData

variable (σ0 σ1 : ℝ) (d : BandData)

/-- The band's canonical statement: the Prop every emitted `rh_in_box_*` theorem proves (its
    `statement_match` gate). -/
def Stmt : Prop :=
  TuringBand.BandStatement σ0 σ1 d.T0 d.T1 d.n d.L1 d.H1 d.L2 d.H2 d.L3 d.H3 d.L4 d.H4 d.L5 d.H5
    d.c d.R d.hs1

/-- The `hLine` binder: `n` increasing on-line zeros of `completedRiemannZeta` in `[T0, T1]`. -/
def LineHyp : Prop :=
  ∃ xs : List ℝ, xs.length = d.n ∧ xs.IsChain (· < ·) ∧
    (∀ t ∈ xs, d.T0 ≤ t ∧ t ≤ d.T1) ∧
    (∀ t ∈ xs, completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0)

/-- Conjuncts 5 to 9 of the `hArbT` binder: the five RvM edge argument-change enclosures. -/
def EnclHyp : Prop :=
  DiffractionCore.argChangeVert riemannZeta 2 d.T0 d.T1 ∈ Set.Icc d.L1 d.H1 ∧
  DiffractionCore.argChangeHoriz riemannZeta d.T1 2 (-1) ∈ Set.Icc d.L2 d.H2 ∧
  DiffractionCore.argChangeHoriz riemannZeta d.T0 2 (-1) ∈ Set.Icc d.L3 d.H3 ∧
  DiffractionCore.argChangeVert Gammaℝ (-1) d.T0 d.T1 ∈ Set.Icc d.L4 d.H4 ∧
  DiffractionCore.argChangeVert Gammaℝ 2 d.T0 d.T1 ∈ Set.Icc d.L5 d.H5

/-- The `hArbT` binder: edge non-vanishing (`hnzb`, `hnzt`, `hnzl`), ball confinement (`hins`)
    and the five enclosures. -/
def ArbHyp : Prop :=
  (∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta (↑x + (d.T0 : ℂ) * I) ≠ 0) ∧
  (∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta (↑x + (d.T1 : ℂ) * I) ≠ 0) ∧
  (∀ y ∈ Set.uIcc d.T0 d.T1, riemannZeta (((-1 : ℝ) : ℂ) + ↑y * I) ≠ 0) ∧
  (∀ ρ ∈ RHInBoxAnalytic.zeroFinset d.c d.R d.hs1,
    (-1 : ℝ) < ρ.re ∧ ρ.re < 2 ∧ d.T0 < ρ.im ∧ ρ.im < d.T1) ∧
  d.EnclHyp

/-- The per-band Arb inputs: `hLine` and `hArbT`. -/
def Inputs : Prop := d.LineHyp ∧ d.ArbHyp

/-- The box claim: every zero of ζ in `[σ0, σ1] x [T0, T1]` is on the critical line. -/
def Box : Prop :=
  ∀ ρ : ℂ, (σ0 ≤ ρ.re ∧ ρ.re ≤ σ1) → (d.T0 ≤ ρ.im ∧ ρ.im ≤ d.T1) →
    riemannZeta ρ = 0 → ρ.re = 1 / 2

/-- **Binder match**: `Stmt` is literally `LineHyp → ArbHyp → Box` (proof `Iff.rfl`), so `Inputs`
    asks for exactly the two binders `hLine`, `hArbT` of `TuringBand.BandStatement`. -/
theorem stmt_iff : d.Stmt σ0 σ1 ↔ (d.LineHyp → d.ArbHyp → d.Box σ0 σ1) := Iff.rfl

variable {σ0 σ1 d}

/-- A band theorem plus its inputs gives its box claim. -/
theorem box_of_stmt (hS : d.Stmt σ0 σ1) (hin : d.Inputs) : d.Box σ0 σ1 := hS hin.1 hin.2

/-- The decidable side conditions under which `TuringBand.turing_band_on_line` proves the band
    statement (the facts each emitted band module discharges by `norm_num`/`nlinarith`). -/
structure Valid (σ0 σ1 : ℝ) (d : BandData) : Prop where
  hT0 : 0 < d.T0
  hT : d.T0 ≤ d.T1
  hs0 : (-1 : ℝ) ≤ σ0
  hs2 : σ1 ≤ 2
  hre_lo : σ0 ≤ 1 / 2
  hre_hi : 1 / 2 ≤ σ1
  hRpos : 0 < d.R
  hN1 : 1 ≤ d.n
  hbox_ball : ∀ ρ : ℂ, ((-1 : ℝ) ≤ ρ.re ∧ ρ.re ≤ 2) → (d.T0 ≤ ρ.im ∧ ρ.im ≤ d.T1) →
    ρ ∈ Metric.ball d.c d.R
  hpinL : 2 * 3.1416 * ((d.n : ℝ) - 1) < 2 * d.L1 + d.L2 - d.H3 + d.L4 + d.L5
  hpinH : 2 * d.H1 + d.H2 - d.L3 + d.H4 + d.H5 < 2 * 3.14 * ((d.n : ℝ) + 1)

/-- **The band statement from its side conditions**: the generic form of every emitted
    `rh_in_box_*` proof, via `TuringBand.turing_band_on_line`. -/
theorem stmt_of_valid (hV : d.Valid σ0 σ1) : d.Stmt σ0 σ1 := by
  intro hLine hArbT
  obtain ⟨xsL, hlen, hchain, hbnd, hzeros⟩ := hLine
  obtain ⟨hnzb, hnzt, hnzl, hins, hAV2, hAHt, hAHb, hAG1, hAG2⟩ := hArbT
  have hre_line : ∀ (t : ℝ), (1 / 2 + (t : ℂ) * Complex.I).re = 1 / 2 := by
    intro t
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]; norm_num
  have him_line : ∀ (t : ℝ), (1 / 2 + (t : ℂ) * Complex.I).im = t := by
    intro t
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]; norm_num
  set T : Finset ℂ :=
    (xsL.map fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * Complex.I).toFinset with hTdef
  have hTcard : T.card = d.n := by
    rw [hTdef, RHInBox.line_toFinset_card xsL hchain, hlen]
  have hTline : ∀ z ∈ T, z.re = 1 / 2 := by
    rw [hTdef]
    exact RHInBox.line_toFinset_forall xsL (fun t _ => hre_line t)
  have hTzero : ∀ z ∈ T, riemannZeta z = 0 := by
    rw [hTdef]
    exact RHInBox.line_toFinset_forall xsL
      (fun t ht => BoxLocalization.line_zeta_zero_of_completed (hzeros t ht))
  have hTbox : ∀ z ∈ T, (σ0 ≤ z.re ∧ z.re ≤ σ1) ∧ (d.T0 ≤ z.im ∧ z.im ≤ d.T1) := by
    rw [hTdef]
    refine RHInBox.line_toFinset_forall xsL (fun t ht => ?_)
    exact ⟨⟨by rw [hre_line]; exact hV.hre_lo, by rw [hre_line]; exact hV.hre_hi⟩,
      by rw [him_line]; exact (hbnd t ht).1, by rw [him_line]; exact (hbnd t ht).2⟩
  have hcountN : ((d.n : ℕ) : ℤ) = (T.card : ℤ) := by rw [hTcard]
  exact TuringBand.turing_band_on_line σ0 σ1 d.T0 d.T1 hV.hT0 hV.hT hV.hs0 hV.hs2
    d.c d.R hV.hRpos d.n hV.hN1 d.L1 d.H1 d.L2 d.H2 d.L3 d.H3 d.L4 d.H4 d.L5 d.H5
    hV.hbox_ball d.hs1 hnzb hnzt hnzl hins hAV2 hAHt hAHb hAG1 hAG2 hV.hpinL hV.hpinH
    T hTline hTzero hTbox hcountN

/-! ## K1 inside the band: the reduced per-band input -/

/-- The per-band input after brick K1: the on-line zeros, the two edge-clearance slabs (zero-free
    `(0, 1) x [T0 - δ0, T0]` below the bottom edge and `(0, 1) x [T1, T1 + δ1]` above the top
    edge) and the five enclosures.  (`hnzl` is gone; `hnzb`, `hnzt`, `hins` come from the slabs.) -/
def ReducedInputs (δ0 δ1 : ℝ) (d : BandData) : Prop :=
  d.LineHyp ∧ EdgeClearGlue.SlabClear (d.T0 - δ0) d.T0 ∧ EdgeClearGlue.SlabClear d.T1 (d.T1 + δ1) ∧
    d.EnclHyp

/-- The decidable ball-cap geometry K1 needs: the edges avoid the real axis, the ball sits above
    it, and its bottom/top caps stay inside the clearance slabs (`δ0`, `δ1` at least the caps). -/
structure CapGeom (δ0 δ1 : ℝ) (d : BandData) : Prop where
  hT0 : d.T0 ≠ 0
  hT1 : d.T1 ≠ 0
  hδ0 : 0 ≤ δ0
  hδ1 : 0 ≤ δ1
  hpos : 0 ≤ d.c.im - d.R
  hlo : d.T0 - δ0 ≤ d.c.im - d.R
  hhi : d.c.im + d.R ≤ d.T1 + δ1

/-- `CapGeom` for a band with `R = √q`, from rational inequalities on explicit values
    (`t0 t1 cim q` are the band's `T0`, `T1`, `c.im` and squared radius). -/
theorem CapGeom.of_sqrt {δ0 δ1 : ℝ} {d : BandData} (t0 t1 cim q : ℝ)
    (hT0v : d.T0 = t0) (hT1v : d.T1 = t1) (hcv : d.c.im = cim) (hRv : d.R = Real.sqrt q)
    (ht0 : t0 ≠ 0) (ht1 : t1 ≠ 0) (hδ0 : 0 ≤ δ0) (hδ1 : 0 ≤ δ1)
    (hc0 : 0 ≤ cim) (hq0 : q ≤ cim ^ 2)
    (hlo0 : 0 ≤ cim - t0 + δ0) (hlo : q ≤ (cim - t0 + δ0) ^ 2)
    (hhi0 : 0 ≤ t1 + δ1 - cim) (hhi : q ≤ (t1 + δ1 - cim) ^ 2) :
    d.CapGeom δ0 δ1 := by
  refine ⟨?_, ?_, hδ0, hδ1, ?_, ?_, ?_⟩
  · rw [hT0v]; exact ht0
  · rw [hT1v]; exact ht1
  · rw [hcv, hRv]; exact EdgeClearGlue.ball_above_of_sq hc0 hq0
  · rw [hT0v, hcv, hRv]; exact EdgeClearGlue.cap_lo_of_sq hlo0 hlo
  · rw [hT1v, hcv, hRv]; exact EdgeClearGlue.cap_hi_of_sq hhi0 hhi

/-- **K1 applied to a band**: the reduced input and the cap geometry give the full `Inputs`. -/
theorem inputs_of_reduced {δ0 δ1 : ℝ} (hG : d.CapGeom δ0 δ1) (h : d.ReducedInputs δ0 δ1) :
    d.Inputs := by
  obtain ⟨hL, hE0, hE1, hEn⟩ := h
  obtain ⟨hnzb, hnzt, hnzl, hins⟩ :=
    EdgeClearGlue.hArbT_nonvanishing_of_edge_clear d.hs1 hG.hT0 hG.hT1 hG.hδ0 hG.hδ1
      hG.hpos hG.hlo hG.hhi hE0 hE1
  exact ⟨hL, hnzb, hnzt, hnzl, hins, hEn⟩

/-- A band's box claim covers every sub-box `[lo, hi] ⊆ [T0, T1]`. -/
theorem box_mono {σ0 σ1 lo hi : ℝ} {d : BandData} (hB : d.Box σ0 σ1) (hlo : d.T0 ≤ lo)
    (hhi : hi ≤ d.T1) :
    ∀ ρ : ℂ, (σ0 ≤ ρ.re ∧ ρ.re ≤ σ1) → (lo ≤ ρ.im ∧ ρ.im ≤ hi) →
      riemannZeta ρ = 0 → ρ.re = 1 / 2 :=
  fun ρ hre him hz => hB ρ hre ⟨le_trans hlo him.1, le_trans him.2 hhi⟩ hz

end BandData

open BandData

/-! ## Band certificates for a box -/

/-- **A band certificate for the box `[σ0, σ1] x [lo, hi]`**: a Turing band covering the box
    whose statement holds and whose Arb inputs hold.  The statement can come from an emitted
    `rh_in_box_*` theorem (`BoxCert.of_stmt`) or from the band's decidable side conditions
    (`BoxCert.of_valid`); the inputs can be the raw `hLine`/`hArbT` or the K1-reduced ones
    (`BoxCert.of_reduced`).  This is the interface a future evaluator fills: it may choose its own
    band parameters (for instance enclosures wider than the 1e-12 Arb ones, as long as the pins
    hold). -/
def BoxCert (σ0 σ1 lo hi : ℝ) : Prop :=
  ∃ d : BandData, d.T0 ≤ lo ∧ hi ≤ d.T1 ∧ d.Stmt σ0 σ1 ∧ d.Inputs

/-- A band certificate gives the box claim. -/
theorem BoxCert.box {σ0 σ1 lo hi : ℝ} (h : BoxCert σ0 σ1 lo hi) :
    ∀ ρ : ℂ, (σ0 ≤ ρ.re ∧ ρ.re ≤ σ1) → (lo ≤ ρ.im ∧ ρ.im ≤ hi) →
      riemannZeta ρ = 0 → ρ.re = 1 / 2 := by
  obtain ⟨d, hlo, hhi, hS, hin⟩ := h
  exact box_mono (box_of_stmt hS hin) hlo hhi

/-- A certificate from a band theorem (for instance an emitted `rh_in_box_*`) and its inputs. -/
theorem BoxCert.of_stmt {σ0 σ1 lo hi : ℝ} (d : BandData) (hlo : d.T0 ≤ lo) (hhi : hi ≤ d.T1)
    (hS : d.Stmt σ0 σ1) (hin : d.Inputs) : BoxCert σ0 σ1 lo hi :=
  ⟨d, hlo, hhi, hS, hin⟩

/-- A certificate from the band's decidable side conditions and its inputs (no band module). -/
theorem BoxCert.of_valid {σ0 σ1 lo hi : ℝ} (d : BandData) (hlo : d.T0 ≤ lo) (hhi : hi ≤ d.T1)
    (hV : d.Valid σ0 σ1) (hin : d.Inputs) : BoxCert σ0 σ1 lo hi :=
  ⟨d, hlo, hhi, stmt_of_valid hV, hin⟩

/-- A certificate from a band statement, the K1 cap geometry and the K1-reduced inputs. -/
theorem BoxCert.of_reduced {σ0 σ1 lo hi δ0 δ1 : ℝ} (d : BandData) (hlo : d.T0 ≤ lo)
    (hhi : hi ≤ d.T1) (hS : d.Stmt σ0 σ1) (hG : d.CapGeom δ0 δ1)
    (hin : d.ReducedInputs δ0 δ1) : BoxCert σ0 σ1 lo hi :=
  ⟨d, hlo, hhi, hS, inputs_of_reduced hG hin⟩

/-! ## K0: segments and ladders -/

/-- **K0, generic (indexed band table).**  For any table `d` of bands covering the boxes
    `[lo i, hi i]`, whose band statements hold (the `rh_in_box_*` theorems, or
    `stmt_of_valid`), and whose per-band Arb inputs hold, every box claim holds.  The conclusion
    is the `SegBandHyp` shape verbatim (count, edges and strip as parameters). -/
theorem segBandHyp_of_bands {σ0 σ1 : ℝ} {count : ℕ} {lo hi : ℕ → ℝ} (d : ℕ → BandData)
    (hedge : ∀ i, i < count → (d i).T0 ≤ lo i ∧ hi i ≤ (d i).T1)
    (hstmt : ∀ i, i < count → (d i).Stmt σ0 σ1)
    (hin : ∀ i, i < count → (d i).Inputs) :
    ∀ i, i < count → ∀ ρ : ℂ, (σ0 ≤ ρ.re ∧ ρ.re ≤ σ1) → (lo i ≤ ρ.im ∧ ρ.im ≤ hi i) →
      riemannZeta ρ = 0 → ρ.re = 1 / 2 := fun i hi' =>
  box_mono (box_of_stmt (hstmt i hi') (hin i hi')) (hedge i hi').1 (hedge i hi').2

/-- **K0, generic (a `List` of bands).**  The same composition for a band list `bs`, box `i`
    being covered by `bs[i]`. -/
theorem segBandHyp_of_bandList {σ0 σ1 : ℝ} {lo hi : ℕ → ℝ} (bs : List BandData)
    (hedge : ∀ i (h : i < bs.length), bs[i].T0 ≤ lo i ∧ hi i ≤ bs[i].T1)
    (hstmt : ∀ b ∈ bs, b.Stmt σ0 σ1) (hin : ∀ b ∈ bs, b.Inputs) :
    ∀ i, i < bs.length → ∀ ρ : ℂ, (σ0 ≤ ρ.re ∧ ρ.re ≤ σ1) → (lo i ≤ ρ.im ∧ ρ.im ≤ hi i) →
      riemannZeta ρ = 0 → ρ.re = 1 / 2 := fun i hi' =>
  box_mono (box_of_stmt (hstmt _ (List.getElem_mem hi')) (hin _ (List.getElem_mem hi')))
    (hedge i hi').1 (hedge i hi').2

/-- **K0, certificate form.**  One band certificate per box gives the `SegBandHyp` shape. -/
theorem segBandHyp_of_certs {σ0 σ1 : ℝ} {count : ℕ} {lo hi : ℕ → ℝ}
    (hcert : ∀ i, i < count → BoxCert σ0 σ1 (lo i) (hi i)) :
    ∀ i, i < count → ∀ ρ : ℂ, (σ0 ≤ ρ.re ∧ ρ.re ≤ σ1) → (lo i ≤ ρ.im ∧ ρ.im ≤ hi i) →
      riemannZeta ρ = 0 → ρ.re = 1 / 2 := fun i hi' => (hcert i hi').box

/-- **K0 + K1 (indexed band table).**  As `segBandHyp_of_bands`, with the per-band input reduced
    by K1: on-line zeros, two edge-clearance slabs and five enclosures, plus the decidable cap
    geometry.  The slab heights `δ0 i`, `δ1 i` are per band (each band's own caps, rounded up). -/
theorem segBandHyp_of_reduced {σ0 σ1 : ℝ} {count : ℕ} {lo hi : ℕ → ℝ} {δ0 δ1 : ℕ → ℝ}
    (d : ℕ → BandData)
    (hedge : ∀ i, i < count → (d i).T0 ≤ lo i ∧ hi i ≤ (d i).T1)
    (hstmt : ∀ i, i < count → (d i).Stmt σ0 σ1)
    (hgeom : ∀ i, i < count → (d i).CapGeom (δ0 i) (δ1 i))
    (hin : ∀ i, i < count → (d i).ReducedInputs (δ0 i) (δ1 i)) :
    ∀ i, i < count → ∀ ρ : ℂ, (σ0 ≤ ρ.re ∧ ρ.re ≤ σ1) → (lo i ≤ ρ.im ∧ ρ.im ≤ hi i) →
      riemannZeta ρ = 0 → ρ.re = 1 / 2 :=
  segBandHyp_of_bands d hedge hstmt fun i hi' => inputs_of_reduced (hgeom i hi') (hin i hi')

/-- **K0, ladder form.**  A ladder of `K` segments, segment `k` holding `count k` bands covering
    the boxes `[lo k i, hi k i]`: the conclusion is `∀ k, k < K → SegBandHyp k` verbatim when
    `(count, lo, hi, σ0, σ1)` are the capstone's `(segCount, segLo, segHi, 1/4000000,
    3999999/4000000)`. -/
theorem ladder_of_bands {σ0 σ1 : ℝ} {K : ℕ} {count : ℕ → ℕ} {lo hi : ℕ → ℕ → ℝ}
    (d : ℕ → ℕ → BandData)
    (hedge : ∀ k, k < K → ∀ i, i < count k → (d k i).T0 ≤ lo k i ∧ hi k i ≤ (d k i).T1)
    (hstmt : ∀ k, k < K → ∀ i, i < count k → (d k i).Stmt σ0 σ1)
    (hin : ∀ k, k < K → ∀ i, i < count k → (d k i).Inputs) :
    ∀ k, k < K → ∀ i, i < count k → ∀ ρ : ℂ, (σ0 ≤ ρ.re ∧ ρ.re ≤ σ1) →
      (lo k i ≤ ρ.im ∧ ρ.im ≤ hi k i) → riemannZeta ρ = 0 → ρ.re = 1 / 2 :=
  fun k hk => segBandHyp_of_bands (d k) (hedge k hk) (hstmt k hk) (hin k hk)

/-- **K0 + K1, ladder form** (per-band slab heights `δ0 k i`, `δ1 k i`). -/
theorem ladder_of_reduced {σ0 σ1 : ℝ} {K : ℕ} {count : ℕ → ℕ} {lo hi : ℕ → ℕ → ℝ}
    {δ0 δ1 : ℕ → ℕ → ℝ} (d : ℕ → ℕ → BandData)
    (hedge : ∀ k, k < K → ∀ i, i < count k → (d k i).T0 ≤ lo k i ∧ hi k i ≤ (d k i).T1)
    (hstmt : ∀ k, k < K → ∀ i, i < count k → (d k i).Stmt σ0 σ1)
    (hgeom : ∀ k, k < K → ∀ i, i < count k → (d k i).CapGeom (δ0 k i) (δ1 k i))
    (hin : ∀ k, k < K → ∀ i, i < count k → (d k i).ReducedInputs (δ0 k i) (δ1 k i)) :
    ∀ k, k < K → ∀ i, i < count k → ∀ ρ : ℂ, (σ0 ≤ ρ.re ∧ ρ.re ≤ σ1) →
      (lo k i ≤ ρ.im ∧ ρ.im ≤ hi k i) → riemannZeta ρ = 0 → ρ.re = 1 / 2 :=
  fun k hk => segBandHyp_of_reduced (d k) (hedge k hk) (hstmt k hk) (hgeom k hk) (hin k hk)

/-- **K0, certificate ladder form.**  One band certificate per box of every segment gives
    `∀ k, k < K → SegBandHyp k` (verbatim at the capstone's parameters). -/
theorem ladder_of_certs {σ0 σ1 : ℝ} {K : ℕ} {count : ℕ → ℕ} {lo hi : ℕ → ℕ → ℝ}
    (hcert : ∀ k, k < K → ∀ i, i < count k → BoxCert σ0 σ1 (lo k i) (hi k i)) :
    ∀ k, k < K → ∀ i, i < count k → ∀ ρ : ℂ, (σ0 ≤ ρ.re ∧ ρ.re ≤ σ1) →
      (lo k i ≤ ρ.im ∧ ρ.im ≤ hi k i) → riemannZeta ρ = 0 → ρ.re = 1 / 2 :=
  fun k hk => segBandHyp_of_certs (hcert k hk)

end BandGlue
