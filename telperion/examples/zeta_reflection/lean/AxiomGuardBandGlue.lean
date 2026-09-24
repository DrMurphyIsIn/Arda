/-  AxiomGuardBandGlue.lean -- kernel-axiom guard of bricks K0 (`BandGlue`) and K1
    (`EdgeClearGlue`) of the ANDURIL Arb discharge, and of their real-segment instantiation
    (`BandGlue_h1000`, segment `[1, 1000]` of the h280000 ladder).

    A `lean_lib` (not a default target).  Run as

        lake build AxiomGuardBandGlue && lake env lean AxiomGuardBandGlue.lean

    Expected on EVERY `#print axioms` line: a subset of {propext, Classical.choice, Quot.sound}.
    No `sorryAx`, no `Lean.ofReduceBool`, no new axiom.  Every new theorem of the three modules is
    listed.

    The `example`s at the end are type-level checks: they only elaborate if the per-band inputs
    of the glue are EXACTLY the two Arb binders (`hLine`, `hArbT`) of the emitted band theorems,
    and if the glue's conclusion is EXACTLY the segment's `BandHyp`.

    conjecture1_proved = False (glue for a finite verification up to a fixed height).
-/
import EdgeClearGlue
import BandGlue
import BandGlue_h1000

/-! ### K1: EdgeClearGlue -/
#print axioms EdgeClearGlue.riemannZeta_ne_zero_of_re_nonpos
#print axioms EdgeClearGlue.riemannZeta_neg_one
#print axioms EdgeClearGlue.riemannZeta_neg_one_ne_zero
#print axioms EdgeClearGlue.riemannZeta_neg_one_add_mul_I_ne_zero
#print axioms EdgeClearGlue.hnzl_discharged
#print axioms EdgeClearGlue.SlabClear.mono
#print axioms EdgeClearGlue.hnz_edge_of_slabClear
#print axioms EdgeClearGlue.mem_ball_and_zero_of_mem_zeroFinset
#print axioms EdgeClearGlue.im_mem_of_mem_ball
#print axioms EdgeClearGlue.hins_of_slabClear
#print axioms EdgeClearGlue.hArbT_nonvanishing_of_edge_clear
#print axioms EdgeClearGlue.cap_lo_of_sq
#print axioms EdgeClearGlue.cap_hi_of_sq
#print axioms EdgeClearGlue.ball_above_of_sq

/-! ### K0: BandGlue -/
#print axioms BandGlue.BandData.stmt_iff
#print axioms BandGlue.BandData.box_of_stmt
#print axioms BandGlue.BandData.stmt_of_valid
#print axioms BandGlue.BandData.CapGeom.of_sqrt
#print axioms BandGlue.BandData.inputs_of_reduced
#print axioms BandGlue.BandData.box_mono
#print axioms BandGlue.BoxCert.box
#print axioms BandGlue.BoxCert.of_stmt
#print axioms BandGlue.BoxCert.of_valid
#print axioms BandGlue.BoxCert.of_reduced
#print axioms BandGlue.segBandHyp_of_bands
#print axioms BandGlue.segBandHyp_of_bandList
#print axioms BandGlue.segBandHyp_of_certs
#print axioms BandGlue.segBandHyp_of_reduced
#print axioms BandGlue.ladder_of_bands
#print axioms BandGlue.ladder_of_reduced
#print axioms BandGlue.ladder_of_certs

/-! ### K0 + K1 on the real segment `[1, 1000]` (25 bands) -/
#print axioms BandGlue_h1000.seg_edge
#print axioms BandGlue_h1000.seg_stmt
#print axioms BandGlue_h1000.seg_geom
#print axioms BandGlue_h1000.boxCert_of_inputs
#print axioms BandGlue_h1000.bandHyp_of_inputs
#print axioms BandGlue_h1000.bandHyp_of_reduced
#print axioms BandGlue_h1000.all_nontrivial_zeros_up_to_height_1000_of_inputs
#print axioms BandGlue_h1000.all_nontrivial_zeros_up_to_height_1000_of_reduced

/-! ### Type-level checks -/

/-- The glue's per-band input for box 0 is exactly the pair of binders of the emitted band
    theorem: the band theorem applies to its two components as they are. -/
example (h : (BandGlue_h1000.seg 0).Inputs) :
    ∀ ρ, ((((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((1) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (41)) → riemannZeta ρ = 0 → ρ.re = 1 / 2 :=
  RHInBoxT_1d4000000_3999999d4000000_1_41.rh_in_box_1d4000000_3999999d4000000_1_41 h.1 h.2

/-- The same for the last box of the segment (band `[960, 1000]`). -/
example (h : (BandGlue_h1000.seg 24).Inputs) :
    ∀ ρ, ((((1 / 4000000)) : ℝ) ≤ ρ.re ∧ ρ.re ≤ ((3999999 / 4000000))) →
      (((960) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1000)) → riemannZeta ρ = 0 → ρ.re = 1 / 2 :=
  RHInBoxT_1d4000000_3999999d4000000_960_1000.rh_in_box_1d4000000_3999999d4000000_960_1000 h.1 h.2

/-- Conversely, the band theorem's binders ARE the glue's `Inputs` (both directions of the
    binder match, at the stretched box `[201, 965/4]`). -/
example : (BandGlue_h1000.seg 5).Stmt (1 / 4000000) (3999999 / 4000000) =
    TuringBand.BandStatement (((1 / 4000000)) : ℝ) ((3999999 / 4000000)) (201) ((965 / 4)) 24
      (446599682219 / 1000000000000) (22329984111 / 50000000000) (267783356193 / 100000000000)
      (2677833561931 / 1000000000000) (-791192772177 / 200000000000)
      (-988990965221 / 250000000000) (4477189784393 / 62500000000)
      (71635036550289 / 1000000000000) (35817207017383 / 500000000000)
      (71634414034767 / 1000000000000) RHInBoxT_1d4000000_3999999d4000000_201_965d4.cPB
      RHInBoxT_1d4000000_3999999d4000000_201_965d4.RPB
      RHInBoxT_1d4000000_3999999d4000000_201_965d4.hs1PB := rfl

/-- The glue's conclusion is the segment's band hypothesis itself (not a look-alike): the
    island's height-1000 theorem consumes it unchanged. -/
example (hin : ∀ i, i < 25 → (BandGlue_h1000.seg i).Inputs)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1000 → ρ.re = 1 / 2 :=
  AllZeros_h1000.all_nontrivial_zeros_up_to_height_1000_of_bands
    (BandGlue_h1000.bandHyp_of_inputs hin) hγ

/-- K1 removes `hnzl` outright: the reduced input carries no left-edge binder, and the full
    `hArbT` left-edge conjunct holds for every band with no input at all. -/
example (i : ℕ) : ∀ y ∈ Set.uIcc (BandGlue_h1000.seg i).T0 (BandGlue_h1000.seg i).T1,
    riemannZeta (((-1 : ℝ) : ℂ) + ↑y * Complex.I) ≠ 0 :=
  EdgeClearGlue.hnzl_discharged _ _
