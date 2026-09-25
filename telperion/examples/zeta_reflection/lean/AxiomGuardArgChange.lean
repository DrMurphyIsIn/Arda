/-  AxiomGuardArgChange.lean -- kernel-axiom guard of the argument-change bricks K6a / K6b / K6c of
    the ANDURIL Arb discharge (telperion/docs/ANDURIL_ARB_DISCHARGE_2026-09-23.md, section 1.3) and of
    their consumption by the K0/K1 band glue on the real segment `[1, 1000]`.

    Modules: `ArgZetaTwo` (K6a), `ArgGammaR` (K6b + the T6 bridge), `ArgHoriz` (K6c reduction),
    `ArgChangeGlue` (K6 inside `BandGlue`), `ArgChangeH1000` (GENERATED: K6 on AllZeros_h1000).

    Run as `lake build AxiomGuardArgChange` (elaborates every check below) and
    `lake env lean AxiomGuardArgChange.lean` (prints the axiom lines).  Expected on EVERY
    `#print axioms` line: a subset of {propext, Classical.choice, Quot.sound}.  No `sorryAx`, no
    `Lean.ofReduceBool`, no new axiom.  Every theorem of the five modules is listed.

    The `example`s are type-level checks that the bricks state EXACTLY the binders the emitted band
    theorems (`TuringBand.BandStatement`) and `BandGlue.BandData.EnclHyp` consume, verbatim, and a
    non-vacuity check of the K6c certificate format.

    conjecture1_proved = False (finite verification only).
-/
import ArgZetaTwo
import ArgGammaR
import ArgHoriz
import ArgChangeGlue
import ArgChangeH1000

open Complex

/-! ### Binder-form checks -/

/-- K6a: conjunct 5 of `hArbT` (`hAV2`), verbatim, for EVERY band (`L1 = -249/250`, `H1 = 249/250`). -/
example (T0 T1 : ℝ) :
    DiffractionCore.argChangeVert riemannZeta 2 T0 T1 ∈ Set.Icc (-(249 / 250 : ℝ)) (249 / 250) :=
  ArgZetaTwo.hAV2_generic T0 T1

/-- K6a: the bound is `2 log ζ(2)` with `log ζ(2) = log (π²/6) < 0.498`. -/
example (t : ℝ) : |Complex.arg (riemannZeta ((2 : ℂ) + (t : ℂ) * I))| ≤ Real.log (Real.pi ^ 2 / 6) ∧
    Real.log (Real.pi ^ 2 / 6) < 249 / 500 :=
  ⟨ArgZetaTwo.abs_arg_zeta_two_le t, ArgZetaTwo.log_pi_sq_div_six_lt⟩

/-- K6b: conjuncts 8 and 9 of `hArbT` (`hAG1`, `hAG2`), verbatim, hypothesis-free for `0 ≤ T0`,
    `0 ≤ T1`, with explicit closed-form endpoints. -/
example {T0 T1 : ℝ} (h0 : 0 ≤ T0) (h1 : 0 ≤ T1) :
    DiffractionCore.argChangeVert Gammaℝ (-1) T0 T1
        ∈ Set.Icc (ArgGammaR.Sm1 T1 - ArgGammaR.Sm1 T0 - ArgGammaR.em1 T1)
          (ArgGammaR.Sm1 T1 - ArgGammaR.Sm1 T0 + ArgGammaR.em1 T0) ∧
      DiffractionCore.argChangeVert Gammaℝ 2 T0 T1
        ∈ Set.Icc (ArgGammaR.S2 T1 - ArgGammaR.S2 T0 - ArgGammaR.e2 T1)
          (ArgGammaR.S2 T1 - ArgGammaR.S2 T0 + ArgGammaR.e2 T0) :=
  ⟨ArgGammaR.hAG1_closed h0 h1, ArgGammaR.hAG2_closed h0 h1⟩

/-- K6b: the T6 bridge (the Gauss branch of `RSTheta.lam_bracket` IS the integral of `Re ψ`). -/
example {x : ℝ} (hx : 0 < x) (a b : ℝ) :
    ∫ y in a..b, (1 / 2 : ℝ) * (Complex.digamma ((x : ℂ) + ((y / 2 : ℝ) : ℂ) * I)).re
      = ArgGammaR.gaussLam x (b / 2) - ArgGammaR.gaussLam x (a / 2) :=
  ArgGammaR.integral_half_re_digamma hx a b

/-- K6c: conjuncts 6 and 7 of `hArbT` (`hAHt` at `T = T1`, `hAHb` at `T = T0`) are EXACTLY the
    octant-angle difference of the two endpoint values once a valid certificate exists. -/
example {T : ℝ} (hT : T ≠ 0) (c : ArgHoriz.OctCert) (hm : 1 ≤ c.m) (hp0 : c.p 0 = 2)
    (hpm : c.p c.m = -1) (hstep : c.StepOK) (hnc : c.NoCross riemannZeta T) :
    DiffractionCore.argChangeHoriz riemannZeta T 2 (-1)
      = ArgHoriz.octAngle (c.k (c.m - 1)) (riemannZeta (((-1 : ℝ) : ℂ) + (T : ℂ) * I))
        - ArgHoriz.octAngle (c.k 0) (riemannZeta (((2 : ℝ) : ℂ) + (T : ℂ) * I)) :=
  ArgHoriz.argChangeHoriz_zeta_eq_of_octCert hT c hm hp0 hpm hstep hnc

/-- K6c non-vacuity: the certificate format evaluates `f = id` exactly, and pins the winding. -/
example : DiffractionCore.argChangeHoriz (fun s : ℂ => s) 1 2 (-1) = Real.pi / 4 + Real.arctan 2 ∧
    DiffractionCore.argChangeHoriz (fun s : ℂ => s) 1 2 (-1)
      ≠ Real.pi / 4 + Real.arctan 2 - 2 * Real.pi :=
  ⟨ArgHoriz.argChangeHoriz_id_one, ArgHoriz.argChangeHoriz_id_one_ne⟩

/-- Inside `BandGlue`: the five enclosures of `EnclHyp` from the K6 side conditions and the two
    horizontal enclosures. -/
example (d : BandGlue.BandData) (hS : ArgChangeGlue.K6Side d) (hH : ArgChangeGlue.HorizHyp d) :
    d.EnclHyp :=
  ArgChangeGlue.enclHyp_of_K6 hS hH

/-- On the real band `[1, 41]` (box 0 of AllZeros_h1000): the K6-reduced input is EXACTLY the seven
    on-line zeros, the two edge slabs, and the band's own two horizontal Arb enclosures. -/
example : ArgChangeGlue.K6Inputs (BandGlue_h1000.capLo 0) (BandGlue_h1000.capHi 0)
      (ArgChangeH1000.segK 0) ↔
    ((∃ xs : List ℝ, xs.length = 7 ∧ xs.IsChain (· < ·) ∧ (∀ t ∈ xs, (1 : ℝ) ≤ t ∧ t ≤ 41) ∧
      (∀ t ∈ xs, completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0)) ∧
     EdgeClearGlue.SlabClear (1 - BandGlue_h1000.capLo 0) 1 ∧
     EdgeClearGlue.SlabClear 41 (41 + BandGlue_h1000.capHi 0) ∧
     (DiffractionCore.argChangeHoriz riemannZeta 41 2 (-1)
        ∈ Set.Icc (2696557998383 / 1000000000000) (168534874899 / 62500000000) ∧
      DiffractionCore.argChangeHoriz riemannZeta 1 2 (-1)
        ∈ Set.Icc (-106057832647 / 100000000000) (-1060578326469 / 1000000000000))) :=
  Iff.rfl

/-- The re-parametrised band `[1, 41]` states the canonical band statement at its new parameters. -/
example : (ArgChangeH1000.segK 0).Stmt (1 / 4000000) (3999999 / 4000000) =
    TuringBand.BandStatement (1 / 4000000) (3999999 / 4000000) 1 41 7 (-(249 / 250)) (249 / 250)
      (2696557998383 / 1000000000000) (168534874899 / 62500000000)
      (-106057832647 / 100000000000) (-1060578326469 / 1000000000000)
      (ArgChangeH1000.L4t 0) (ArgChangeH1000.H4t 0) (ArgChangeH1000.L5t 0) (ArgChangeH1000.H5t 0)
      RHInBoxT_1d4000000_3999999d4000000_1_41.cPB RHInBoxT_1d4000000_3999999d4000000_1_41.RPB
      RHInBoxT_1d4000000_3999999d4000000_1_41.hs1PB := rfl

/-- The height-1000 statement from the K6-reduced inputs alone (the height floor is discharged). -/
example (hin : ∀ i, i < 25 → ArgChangeGlue.K6Inputs (BandGlue_h1000.capLo i)
    (BandGlue_h1000.capHi i) (ArgChangeH1000.segK i)) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1000 → ρ.re = 1 / 2 :=
  ArgChangeH1000.all_nontrivial_zeros_up_to_height_1000_of_K6 hin


/-! ### ArgZetaTwo -/
#print axioms ArgZetaTwo.exp_primeLog
#print axioms ArgZetaTwo.norm_neg_log_one_sub_le
#print axioms ArgZetaTwo.neg_log_one_sub_le_two_mul
#print axioms ArgZetaTwo.neg_log_one_sub_nonneg
#print axioms ArgZetaTwo.prime_inv_sq_le
#print axioms ArgZetaTwo.prime_inv_sq_nonneg
#print axioms ArgZetaTwo.primeTerm_nonneg
#print axioms ArgZetaTwo.summable_prime_inv_sq
#print axioms ArgZetaTwo.summable_primeTerm
#print axioms ArgZetaTwo.hasSum_primeTerm
#print axioms ArgZetaTwo.primeLog_two
#print axioms ArgZetaTwo.exp_primeSum
#print axioms ArgZetaTwo.primeSum_eq
#print axioms ArgZetaTwo.log_pi_sq_div_six_lt
#print axioms ArgZetaTwo.primeSum_lt
#print axioms ArgZetaTwo.primeSum_nonneg
#print axioms ArgZetaTwo.re_two_add
#print axioms ArgZetaTwo.norm_primeLog_le
#print axioms ArgZetaTwo.log_zeta_two_eq
#print axioms ArgZetaTwo.arg_zeta_eq_im_primeLog
#print axioms ArgZetaTwo.abs_arg_zeta_two_le
#print axioms ArgZetaTwo.re_zeta_two_pos
#print axioms ArgZetaTwo.zeta_two_mem_slitPlane
#print axioms ArgZetaTwo.argChangeVert_zeta_two_eq
#print axioms ArgZetaTwo.abs_argChangeVert_zeta_two_le
#print axioms ArgZetaTwo.hAV2_generic
#print axioms ArgZetaTwo.hAV2_of_le

/-! ### ArgGammaR -/
#print axioms ArgGammaR.tendsto_gaussLam
#print axioms ArgGammaR.gaussLam_mem
#print axioms ArgGammaR.hasDerivAt_imLnVal_half
#print axioms ArgGammaR.continuous_dImLn
#print axioms ArgGammaR.integral_dImLn
#print axioms ArgGammaR.ray_re
#print axioms ArgGammaR.continuous_half_re_digamma
#print axioms ArgGammaR.re_inv_ray
#print axioms ArgGammaR.half_re_digamma_sub_dImLn
#print axioms ArgGammaR.abs_remainder_le
#print axioms ArgGammaR.integral_half_re_digamma
#print axioms ArgGammaR.logDeriv_gammaR_of_ne
#print axioms ArgGammaR.re_logDeriv_gammaR_two
#print axioms ArgGammaR.half_neg_one_ne_pole
#print axioms ArgGammaR.neg_half_ne_pole
#print axioms ArgGammaR.logDeriv_gammaR_neg_one
#print axioms ArgGammaR.re_neg_inv_neg_half
#print axioms ArgGammaR.re_logDeriv_gammaR_neg_one
#print axioms ArgGammaR.continuous_logDeriv_gammaR_neg_one
#print axioms ArgGammaR.argChangeVert_gammaR_two_eq
#print axioms ArgGammaR.argChangeVert_gammaR_neg_one_eq
#print axioms ArgGammaR.hAG2_mem
#print axioms ArgGammaR.hAG1_mem
#print axioms ArgGammaR.phase2_zero
#print axioms ArgGammaR.phaseM1_zero
#print axioms ArgGammaR.lamE_one_zero
#print axioms ArgGammaR.lamE_half_zero
#print axioms ArgGammaR.hAG2_closed
#print axioms ArgGammaR.hAG1_closed
#print axioms ArgGammaR.hAG2_of_bounds
#print axioms ArgGammaR.hAG1_of_bounds
#print axioms ArgGammaR.S2_mem_of
#print axioms ArgGammaR.Sm1_mem_of
#print axioms ArgGammaR.arctan_mem_large
#print axioms ArgGammaR.log_one_sub_mem

/-! ### ArgHoriz -/
#print axioms ArgHoriz.rot_re
#print axioms ArgHoriz.rot_im
#print axioms ArgHoriz.norm_rot
#print axioms ArgHoriz.norm_mul_exp_chartAngle
#print axioms ArgHoriz.chartAngle_eq
#print axioms ArgHoriz.piece_eq
#print axioms ArgHoriz.argChangeHoriz_chain
#print axioms ArgHoriz.octIdx_lt
#print axioms ArgHoriz.octIdx_cast
#print axioms ArgHoriz.octant_trig_residue
#print axioms ArgHoriz.octant_trig
#print axioms ArgHoriz.rot_oct
#print axioms ArgHoriz.rot_oct_re_pos
#print axioms ArgHoriz.chartAngle_oct
#print axioms ArgHoriz.theta_step_lt
#print axioms ArgHoriz.argChangeHoriz_eq_of_octCert
#print axioms ArgHoriz.affine_nonneg_of_corners
#print axioms ArgHoriz.affine_pos_of_corners
#print axioms ArgHoriz.octX_pos_of_box
#print axioms ArgHoriz.OctCert.noCross_of_boxes
#print axioms ArgHoriz.octAngle_mem_of_box
#print axioms ArgHoriz.atanLo_le
#print axioms ArgHoriz.le_atanHi
#print axioms ArgHoriz.zeta_analyticAt_horiz
#print axioms ArgHoriz.argChangeHoriz_zeta_eq_of_octCert
#print axioms ArgHoriz.hAH_of_octCert_boxes
#print axioms ArgHoriz.argChangeHoriz_id_one
#print axioms ArgHoriz.argChangeHoriz_id_one_ne

/-! ### ArgChangeGlue -/
#print axioms ArgChangeGlue.enclHyp_of_K6
#print axioms ArgChangeGlue.HorizHyp.of_edges
#print axioms ArgChangeGlue.HorizHyp.of_octCerts
#print axioms ArgChangeGlue.inputs_of_K6
#print axioms ArgChangeGlue.BoxCert.of_K6
#print axioms ArgChangeGlue.segBandHyp_of_K6
#print axioms ArgChangeGlue.ladder_of_K6
#print axioms ArgChangeGlue.ball_of_sq
#print axioms ArgChangeGlue.capGeom_transfer
#print axioms ArgChangeGlue.octX_zero_zeta_two_pos
#print axioms ArgChangeGlue.octAngle_zero_zeta_two_abs_le

/-! ### ArgChangeH1000 -/
#print axioms ArgChangeH1000.log_v2_1
#print axioms ArgChangeH1000.log_vm_1
#print axioms ArgChangeH1000.atan_half_1
#print axioms ArgChangeH1000.atan_1
#print axioms ArgChangeH1000.S2_box_1
#print axioms ArgChangeH1000.Sm1_box_1
#print axioms ArgChangeH1000.log_v2_41
#print axioms ArgChangeH1000.log_vm_41
#print axioms ArgChangeH1000.atan_half_41
#print axioms ArgChangeH1000.atan_41
#print axioms ArgChangeH1000.S2_box_41
#print axioms ArgChangeH1000.Sm1_box_41
#print axioms ArgChangeH1000.log_v2_81
#print axioms ArgChangeH1000.log_vm_81
#print axioms ArgChangeH1000.atan_half_81
#print axioms ArgChangeH1000.atan_81
#print axioms ArgChangeH1000.S2_box_81
#print axioms ArgChangeH1000.Sm1_box_81
#print axioms ArgChangeH1000.log_v2_121
#print axioms ArgChangeH1000.log_vm_121
#print axioms ArgChangeH1000.atan_half_121
#print axioms ArgChangeH1000.atan_121
#print axioms ArgChangeH1000.S2_box_121
#print axioms ArgChangeH1000.Sm1_box_121
#print axioms ArgChangeH1000.log_v2_161
#print axioms ArgChangeH1000.log_vm_161
#print axioms ArgChangeH1000.atan_half_161
#print axioms ArgChangeH1000.atan_161
#print axioms ArgChangeH1000.S2_box_161
#print axioms ArgChangeH1000.Sm1_box_161
#print axioms ArgChangeH1000.log_v2_201
#print axioms ArgChangeH1000.log_vm_201
#print axioms ArgChangeH1000.atan_half_201
#print axioms ArgChangeH1000.atan_201
#print axioms ArgChangeH1000.S2_box_201
#print axioms ArgChangeH1000.Sm1_box_201
#print axioms ArgChangeH1000.log_v2_241
#print axioms ArgChangeH1000.log_vm_241
#print axioms ArgChangeH1000.atan_half_241
#print axioms ArgChangeH1000.atan_241
#print axioms ArgChangeH1000.S2_box_241
#print axioms ArgChangeH1000.Sm1_box_241
#print axioms ArgChangeH1000.log_v2_965d4
#print axioms ArgChangeH1000.log_vm_965d4
#print axioms ArgChangeH1000.atan_half_965d4
#print axioms ArgChangeH1000.atan_965d4
#print axioms ArgChangeH1000.S2_box_965d4
#print axioms ArgChangeH1000.Sm1_box_965d4
#print axioms ArgChangeH1000.log_v2_281
#print axioms ArgChangeH1000.log_vm_281
#print axioms ArgChangeH1000.atan_half_281
#print axioms ArgChangeH1000.atan_281
#print axioms ArgChangeH1000.S2_box_281
#print axioms ArgChangeH1000.Sm1_box_281
#print axioms ArgChangeH1000.log_v2_321
#print axioms ArgChangeH1000.log_vm_321
#print axioms ArgChangeH1000.atan_half_321
#print axioms ArgChangeH1000.atan_321
#print axioms ArgChangeH1000.S2_box_321
#print axioms ArgChangeH1000.Sm1_box_321
#print axioms ArgChangeH1000.log_v2_361
#print axioms ArgChangeH1000.log_vm_361
#print axioms ArgChangeH1000.atan_half_361
#print axioms ArgChangeH1000.atan_361
#print axioms ArgChangeH1000.S2_box_361
#print axioms ArgChangeH1000.Sm1_box_361
#print axioms ArgChangeH1000.log_v2_401
#print axioms ArgChangeH1000.log_vm_401
#print axioms ArgChangeH1000.atan_half_401
#print axioms ArgChangeH1000.atan_401
#print axioms ArgChangeH1000.S2_box_401
#print axioms ArgChangeH1000.Sm1_box_401
#print axioms ArgChangeH1000.log_v2_441
#print axioms ArgChangeH1000.log_vm_441
#print axioms ArgChangeH1000.atan_half_441
#print axioms ArgChangeH1000.atan_441
#print axioms ArgChangeH1000.S2_box_441
#print axioms ArgChangeH1000.Sm1_box_441
#print axioms ArgChangeH1000.log_v2_481
#print axioms ArgChangeH1000.log_vm_481
#print axioms ArgChangeH1000.atan_half_481
#print axioms ArgChangeH1000.atan_481
#print axioms ArgChangeH1000.S2_box_481
#print axioms ArgChangeH1000.Sm1_box_481
#print axioms ArgChangeH1000.log_v2_520
#print axioms ArgChangeH1000.log_vm_520
#print axioms ArgChangeH1000.atan_half_520
#print axioms ArgChangeH1000.atan_520
#print axioms ArgChangeH1000.S2_box_520
#print axioms ArgChangeH1000.Sm1_box_520
#print axioms ArgChangeH1000.log_v2_560
#print axioms ArgChangeH1000.log_vm_560
#print axioms ArgChangeH1000.atan_half_560
#print axioms ArgChangeH1000.atan_560
#print axioms ArgChangeH1000.S2_box_560
#print axioms ArgChangeH1000.Sm1_box_560
#print axioms ArgChangeH1000.log_v2_600
#print axioms ArgChangeH1000.log_vm_600
#print axioms ArgChangeH1000.atan_half_600
#print axioms ArgChangeH1000.atan_600
#print axioms ArgChangeH1000.S2_box_600
#print axioms ArgChangeH1000.Sm1_box_600
#print axioms ArgChangeH1000.log_v2_640
#print axioms ArgChangeH1000.log_vm_640
#print axioms ArgChangeH1000.atan_half_640
#print axioms ArgChangeH1000.atan_640
#print axioms ArgChangeH1000.S2_box_640
#print axioms ArgChangeH1000.Sm1_box_640
#print axioms ArgChangeH1000.log_v2_680
#print axioms ArgChangeH1000.log_vm_680
#print axioms ArgChangeH1000.atan_half_680
#print axioms ArgChangeH1000.atan_680
#print axioms ArgChangeH1000.S2_box_680
#print axioms ArgChangeH1000.Sm1_box_680
#print axioms ArgChangeH1000.log_v2_720
#print axioms ArgChangeH1000.log_vm_720
#print axioms ArgChangeH1000.atan_half_720
#print axioms ArgChangeH1000.atan_720
#print axioms ArgChangeH1000.S2_box_720
#print axioms ArgChangeH1000.Sm1_box_720
#print axioms ArgChangeH1000.log_v2_760
#print axioms ArgChangeH1000.log_vm_760
#print axioms ArgChangeH1000.atan_half_760
#print axioms ArgChangeH1000.atan_760
#print axioms ArgChangeH1000.S2_box_760
#print axioms ArgChangeH1000.Sm1_box_760
#print axioms ArgChangeH1000.log_v2_800
#print axioms ArgChangeH1000.log_vm_800
#print axioms ArgChangeH1000.atan_half_800
#print axioms ArgChangeH1000.atan_800
#print axioms ArgChangeH1000.S2_box_800
#print axioms ArgChangeH1000.Sm1_box_800
#print axioms ArgChangeH1000.log_v2_840
#print axioms ArgChangeH1000.log_vm_840
#print axioms ArgChangeH1000.atan_half_840
#print axioms ArgChangeH1000.atan_840
#print axioms ArgChangeH1000.S2_box_840
#print axioms ArgChangeH1000.Sm1_box_840
#print axioms ArgChangeH1000.log_v2_880
#print axioms ArgChangeH1000.log_vm_880
#print axioms ArgChangeH1000.atan_half_880
#print axioms ArgChangeH1000.atan_880
#print axioms ArgChangeH1000.S2_box_880
#print axioms ArgChangeH1000.Sm1_box_880
#print axioms ArgChangeH1000.log_v2_920
#print axioms ArgChangeH1000.log_vm_920
#print axioms ArgChangeH1000.atan_half_920
#print axioms ArgChangeH1000.atan_920
#print axioms ArgChangeH1000.S2_box_920
#print axioms ArgChangeH1000.Sm1_box_920
#print axioms ArgChangeH1000.log_v2_960
#print axioms ArgChangeH1000.log_vm_960
#print axioms ArgChangeH1000.atan_half_960
#print axioms ArgChangeH1000.atan_960
#print axioms ArgChangeH1000.S2_box_960
#print axioms ArgChangeH1000.Sm1_box_960
#print axioms ArgChangeH1000.log_v2_1000
#print axioms ArgChangeH1000.log_vm_1000
#print axioms ArgChangeH1000.atan_half_1000
#print axioms ArgChangeH1000.atan_1000
#print axioms ArgChangeH1000.S2_box_1000
#print axioms ArgChangeH1000.Sm1_box_1000
#print axioms ArgChangeH1000.segK_valid_0
#print axioms ArgChangeH1000.segK_side_0
#print axioms ArgChangeH1000.segK_valid_1
#print axioms ArgChangeH1000.segK_side_1
#print axioms ArgChangeH1000.segK_valid_2
#print axioms ArgChangeH1000.segK_side_2
#print axioms ArgChangeH1000.segK_valid_3
#print axioms ArgChangeH1000.segK_side_3
#print axioms ArgChangeH1000.segK_valid_4
#print axioms ArgChangeH1000.segK_side_4
#print axioms ArgChangeH1000.segK_valid_5
#print axioms ArgChangeH1000.segK_side_5
#print axioms ArgChangeH1000.segK_valid_6
#print axioms ArgChangeH1000.segK_side_6
#print axioms ArgChangeH1000.segK_valid_7
#print axioms ArgChangeH1000.segK_side_7
#print axioms ArgChangeH1000.segK_valid_8
#print axioms ArgChangeH1000.segK_side_8
#print axioms ArgChangeH1000.segK_valid_9
#print axioms ArgChangeH1000.segK_side_9
#print axioms ArgChangeH1000.segK_valid_10
#print axioms ArgChangeH1000.segK_side_10
#print axioms ArgChangeH1000.segK_valid_11
#print axioms ArgChangeH1000.segK_side_11
#print axioms ArgChangeH1000.segK_valid_12
#print axioms ArgChangeH1000.segK_side_12
#print axioms ArgChangeH1000.segK_valid_13
#print axioms ArgChangeH1000.segK_side_13
#print axioms ArgChangeH1000.segK_valid_14
#print axioms ArgChangeH1000.segK_side_14
#print axioms ArgChangeH1000.segK_valid_15
#print axioms ArgChangeH1000.segK_side_15
#print axioms ArgChangeH1000.segK_valid_16
#print axioms ArgChangeH1000.segK_side_16
#print axioms ArgChangeH1000.segK_valid_17
#print axioms ArgChangeH1000.segK_side_17
#print axioms ArgChangeH1000.segK_valid_18
#print axioms ArgChangeH1000.segK_side_18
#print axioms ArgChangeH1000.segK_valid_19
#print axioms ArgChangeH1000.segK_side_19
#print axioms ArgChangeH1000.segK_valid_20
#print axioms ArgChangeH1000.segK_side_20
#print axioms ArgChangeH1000.segK_valid_21
#print axioms ArgChangeH1000.segK_side_21
#print axioms ArgChangeH1000.segK_valid_22
#print axioms ArgChangeH1000.segK_side_22
#print axioms ArgChangeH1000.segK_valid_23
#print axioms ArgChangeH1000.segK_side_23
#print axioms ArgChangeH1000.segK_valid_24
#print axioms ArgChangeH1000.segK_side_24
#print axioms ArgChangeH1000.segK_edge
#print axioms ArgChangeH1000.segK_geom
#print axioms ArgChangeH1000.segK_stmt
#print axioms ArgChangeH1000.segK_side
#print axioms ArgChangeH1000.bandHyp_of_K6
#print axioms ArgChangeH1000.all_nontrivial_zeros_up_to_height_1000_of_K6
#print axioms ArgChangeH1000.k6Inputs_of_reduced
