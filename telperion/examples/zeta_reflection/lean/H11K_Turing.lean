/-  H11K_Turing.lean -- lane H11K: the Turing band template with SHARP pi pins, for WIDE bands.

    `TuringBand.band_count_eq` pins the band count with `3.14 < π < 3.1416`.  The upper pin
    `2 H1 + H2 - L3 + H4 + H5 < 2 * 3.14 * (N + 1)` then loses `2 (π - 3.14) N ≈ 0.0032 N` radians,
    which (with the K6a range `[-249/250, 249/250]` alone costing about 4 radians) caps a band at
    roughly 700 zeros.  A single band over `[31851/4, 11004]` holds 3541 zeros.  This file re-proves
    the same template with `3.141592 < π < 3.141593` (`Real.pi_gt_d6`, `Real.pi_lt_d6`); the RvM
    edge decomposition (`DiffractionCore.zero_count_band_edge_decomp`), the Blaschke split and the
    count-exhaustion core are reused unchanged.

      * `band_count_eq_sharp`, `turing_band_on_line_sharp` -- `TuringBand.band_count_eq` /
        `turing_band_on_line` with the sharp pins (proofs copied, constants changed);
      * `ValidS`, `stmt_of_validS` -- `BandGlue.BandData.Valid` / `stmt_of_valid` with the sharp
        pins; the conclusion is the band's canonical statement `d.Stmt σ0 σ1` (the same Prop,
        `TuringBand.BandStatement`, whatever the pins), so every other piece of `BandGlue` applies;
      * `validBS`, `validS_of_B` -- the decidable side conditions as ONE Boolean (as `Arb4.validB`);
      * `boxCert_of_parts_sharp` -- `Arb4.boxCert_of_parts` with `ValidS`.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (H11K_AxiomGuard).  No `sorry`.  conjecture1_proved = False.
-/
import Arb4_Seg

open Complex

namespace H11K

/-- **Count pinning with sharp `π` bounds**: as `TuringBand.band_count_eq`, with the pins
    `2 * 3.141593 * (N - 1) < …` and `… < 2 * 3.141592 * (N + 1)`. -/
theorem band_count_eq_sharp
    (T0 T1 : ℝ) (hT0 : 0 < T0) (hT : T0 ≤ T1)
    (c : ℂ) (R : ℝ) (N : ℕ) (hN1 : 1 ≤ N)
    (L1 H1 L2 H2 L3 H3 L4 H4 L5 H5 : ℝ)
    (hbox_ball : ∀ ρ : ℂ, ((-1 : ℝ) ≤ ρ.re ∧ ρ.re ≤ 2) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      ρ ∈ Metric.ball c R)
    (hs1 : (1 : ℂ) ∉ Metric.ball c R)
    (hnzb : ∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta (↑x + (T0 : ℂ) * I) ≠ 0)
    (hnzt : ∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta (↑x + (T1 : ℂ) * I) ≠ 0)
    (hnzl : ∀ y ∈ Set.uIcc T0 T1, riemannZeta (((-1 : ℝ) : ℂ) + ↑y * I) ≠ 0)
    (hins : ∀ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
      (-1 : ℝ) < ρ.re ∧ ρ.re < 2 ∧ T0 < ρ.im ∧ ρ.im < T1)
    (hAV2 : DiffractionCore.argChangeVert riemannZeta 2 T0 T1 ∈ Set.Icc L1 H1)
    (hAHt : DiffractionCore.argChangeHoriz riemannZeta T1 2 (-1) ∈ Set.Icc L2 H2)
    (hAHb : DiffractionCore.argChangeHoriz riemannZeta T0 2 (-1) ∈ Set.Icc L3 H3)
    (hAG1 : DiffractionCore.argChangeVert Gammaℝ (-1) T0 T1 ∈ Set.Icc L4 H4)
    (hAG2 : DiffractionCore.argChangeVert Gammaℝ 2 T0 T1 ∈ Set.Icc L5 H5)
    (hpinL : 2 * 3.141593 * ((N : ℝ) - 1) < 2 * L1 + L2 - H3 + L4 + L5)
    (hpinH : 2 * H1 + H2 - L3 + H4 + H5 < 2 * 3.141592 * ((N : ℝ) + 1)) :
    (∑ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
      (MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ) ρ) = (N : ℤ) := by
  have hdecomp := DiffractionCore.zero_count_band_edge_decomp T0 T1 hT0 hT c R
    hbox_ball hs1 hnzb hnzt hnzl hins
  set Sz : ℤ := ∑ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
    (MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ) ρ with hSz
  have hSreal : (2 : ℝ) * Real.pi * (Sz : ℝ)
      = 2 * DiffractionCore.argChangeVert riemannZeta 2 T0 T1
        + DiffractionCore.argChangeHoriz riemannZeta T1 2 (-1)
        - DiffractionCore.argChangeHoriz riemannZeta T0 2 (-1)
        + DiffractionCore.argChangeVert Gammaℝ (-1) T0 T1
        + DiffractionCore.argChangeVert Gammaℝ 2 T0 T1 := by
    have hcast : ((Sz : ℤ) : ℝ) = ∑ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
        (((MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ) ρ : ℤ) : ℝ) := by
      rw [hSz]; push_cast; ring
    rw [hcast]; exact hdecomp
  have hpigt : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hpilt : Real.pi < 3.141593 := Real.pi_lt_d6
  have hlo : 2 * Real.pi * ((N : ℝ) - 1) < 2 * Real.pi * (Sz : ℝ) := by
    have h1 : 2 * Real.pi * ((N : ℝ) - 1) ≤ 2 * 3.141593 * ((N : ℝ) - 1) := by
      have hN0 : (0 : ℝ) ≤ (N : ℝ) - 1 := by
        have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
        linarith
      nlinarith [hN0, hpilt]
    have h2 : 2 * L1 + L2 - H3 + L4 + L5 ≤ 2 * Real.pi * (Sz : ℝ) := by
      rw [hSreal]
      obtain ⟨l1, h1'⟩ := hAV2; obtain ⟨l2, h2'⟩ := hAHt; obtain ⟨l3, h3'⟩ := hAHb
      obtain ⟨l4, h4'⟩ := hAG1; obtain ⟨l5, h5'⟩ := hAG2
      linarith
    linarith
  have hhi : 2 * Real.pi * (Sz : ℝ) < 2 * Real.pi * ((N : ℝ) + 1) := by
    have h1 : 2 * 3.141592 * ((N : ℝ) + 1) ≤ 2 * Real.pi * ((N : ℝ) + 1) := by
      have hN0 : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
      nlinarith [hN0, hpigt]
    have h2 : 2 * Real.pi * (Sz : ℝ) ≤ 2 * H1 + H2 - L3 + H4 + H5 := by
      rw [hSreal]
      obtain ⟨l1, h1'⟩ := hAV2; obtain ⟨l2, h2'⟩ := hAHt; obtain ⟨l3, h3'⟩ := hAHb
      obtain ⟨l4, h4'⟩ := hAG1; obtain ⟨l5, h5'⟩ := hAG2
      linarith
    linarith
  have hpipos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hltN : ((N : ℝ) - 1) < (Sz : ℝ) :=
    lt_of_mul_lt_mul_left (by linarith [hlo]) (le_of_lt hpipos)
  have hgtN : (Sz : ℝ) < ((N : ℝ) + 1) :=
    lt_of_mul_lt_mul_left (by linarith [hhi]) (le_of_lt hpipos)
  have hzlt : (N : ℤ) - 1 < Sz := by exact_mod_cast hltN
  have hzgt : Sz < (N : ℤ) + 1 := by exact_mod_cast hgtN
  omega

/-- **Turing band template with sharp `π` pins**: `TuringBand.turing_band_on_line` with the pins of
    `band_count_eq_sharp`. -/
theorem turing_band_on_line_sharp
    (sigma0 sigma1 T0 T1 : ℝ) (hT0 : 0 < T0) (hT : T0 ≤ T1)
    (hs0 : (-1 : ℝ) ≤ sigma0) (hs2 : sigma1 ≤ 2)
    (c : ℂ) (R : ℝ) (hRpos : 0 < R) (N : ℕ) (hN1 : 1 ≤ N)
    (L1 H1 L2 H2 L3 H3 L4 H4 L5 H5 : ℝ)
    (hbox_ball : ∀ ρ : ℂ, ((-1 : ℝ) ≤ ρ.re ∧ ρ.re ≤ 2) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      ρ ∈ Metric.ball c R)
    (hs1 : (1 : ℂ) ∉ Metric.ball c R)
    (hnzb : ∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta (↑x + (T0 : ℂ) * I) ≠ 0)
    (hnzt : ∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta (↑x + (T1 : ℂ) * I) ≠ 0)
    (hnzl : ∀ y ∈ Set.uIcc T0 T1, riemannZeta (((-1 : ℝ) : ℂ) + ↑y * I) ≠ 0)
    (hins : ∀ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
      (-1 : ℝ) < ρ.re ∧ ρ.re < 2 ∧ T0 < ρ.im ∧ ρ.im < T1)
    (hAV2 : DiffractionCore.argChangeVert riemannZeta 2 T0 T1 ∈ Set.Icc L1 H1)
    (hAHt : DiffractionCore.argChangeHoriz riemannZeta T1 2 (-1) ∈ Set.Icc L2 H2)
    (hAHb : DiffractionCore.argChangeHoriz riemannZeta T0 2 (-1) ∈ Set.Icc L3 H3)
    (hAG1 : DiffractionCore.argChangeVert Gammaℝ (-1) T0 T1 ∈ Set.Icc L4 H4)
    (hAG2 : DiffractionCore.argChangeVert Gammaℝ 2 T0 T1 ∈ Set.Icc L5 H5)
    (hpinL : 2 * 3.141593 * ((N : ℝ) - 1) < 2 * L1 + L2 - H3 + L4 + L5)
    (hpinH : 2 * H1 + H2 - L3 + H4 + H5 < 2 * 3.141592 * ((N : ℝ) + 1))
    (T : Finset ℂ)
    (hTline : ∀ z ∈ T, z.re = 1 / 2)
    (hTzero : ∀ z ∈ T, riemannZeta z = 0)
    (hTbox : ∀ z ∈ T, (sigma0 ≤ z.re ∧ z.re ≤ sigma1) ∧ (T0 ≤ z.im ∧ z.im ≤ T1))
    (hcard : (N : ℤ) = (T.card : ℤ)) :
    ∀ ρ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      riemannZeta ρ = 0 → ρ.re = 1 / 2 := by
  obtain ⟨E, _hE, hd1, hzin_ball, _hsplit⟩ :=
    RHInBoxAnalytic.zeta_blaschke_split_ball (-1) 2 T0 T1 c R hRpos hbox_ball hs1
  have hcnt := band_count_eq_sharp T0 T1 hT0 hT c R N hN1 L1 H1 L2 H2 L3 H3 L4 H4 L5 H5
    hbox_ball hs1 hnzb hnzt hnzl hins hAV2 hAHt hAHb hAG1 hAG2 hpinL hpinH
  have hball_of_box : ∀ ρ : ℂ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) →
      (T0 ≤ ρ.im ∧ ρ.im ≤ T1) → ρ ∈ Metric.ball c R := fun ρ hre him =>
    hbox_ball ρ ⟨le_trans hs0 hre.1, le_trans hre.2 hs2⟩ him
  have hTsub : T ⊆ RHInBoxAnalytic.zeroFinset c R hs1 := fun z hz =>
    hzin_ball z (hball_of_box z (hTbox z hz).1 (hTbox z hz).2) (hTzero z hz)
  have hcount' : (∑ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
      (MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ) ρ) = (T.card : ℤ) := by
    rw [hcnt, hcard]
  have hzero_in : ∀ ρ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      riemannZeta ρ = 0 → ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1 := fun ρ hre him hz =>
    hzin_ball ρ (hball_of_box ρ hre him) hz
  exact RHInBoxCore.rh_in_box_core sigma0 sigma1 T0 T1
    (RHInBoxAnalytic.zeroFinset c R hs1) T
    (MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ)
    hd1 hTsub hTline hcount' hzero_in

open BandGlue BandGlue.BandData

/-- `BandGlue.BandData.Valid` with the sharp pins. -/
structure ValidS (σ0 σ1 : ℝ) (d : BandData) : Prop where
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
  hpinL : 2 * 3.141593 * ((d.n : ℝ) - 1) < 2 * d.L1 + d.L2 - d.H3 + d.L4 + d.L5
  hpinH : 2 * d.H1 + d.H2 - d.L3 + d.H4 + d.H5 < 2 * 3.141592 * ((d.n : ℝ) + 1)

/-- **The band's canonical statement from the sharp side conditions** (`stmt_of_valid` with
    `turing_band_on_line_sharp`). -/
theorem stmt_of_validS {σ0 σ1 : ℝ} {d : BandData} (hV : ValidS σ0 σ1 d) : d.Stmt σ0 σ1 := by
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
  exact turing_band_on_line_sharp σ0 σ1 d.T0 d.T1 hV.hT0 hV.hT hV.hs0 hV.hs2
    d.c d.R hV.hRpos d.n hV.hN1 d.L1 d.H1 d.L2 d.H2 d.L3 d.H3 d.L4 d.H4 d.L5 d.H5
    hV.hbox_ball d.hs1 hnzb hnzt hnzl hins hAV2 hAHt hAHb hAG1 hAG2 hV.hpinL hV.hpinH
    T hTline hTzero hTbox hcountN

/-- `ValidS` for a band with ball `1/2 + i cim`, radius `√q` (as `H1000Line.valid_of_sqrt`). -/
theorem validS_of_sqrt (d : BandData) (t0 t1 cim q : ℝ) (hT0v : d.T0 = t0) (hT1v : d.T1 = t1)
    (hcv : d.c = (⟨1 / 2, cim⟩ : ℂ)) (hRv : d.R = Real.sqrt q) (hn : 1 ≤ d.n)
    (ht0 : 0 < t0) (ht : t0 ≤ t1) (hq : 0 < q) (h0 : t0 ≤ cim) (h1 : cim ≤ t1)
    (ha : 9 / 4 + (cim - t0) ^ 2 < q) (hb : 9 / 4 + (t1 - cim) ^ 2 < q)
    (hpinL : 2 * 3.141593 * ((d.n : ℝ) - 1) < 2 * d.L1 + d.L2 - d.H3 + d.L4 + d.L5)
    (hpinH : 2 * d.H1 + d.H2 - d.L3 + d.H4 + d.H5 < 2 * 3.141592 * ((d.n : ℝ) + 1)) :
    ValidS (1 / 4000000) (3999999 / 4000000) d where
  hT0 := by rw [hT0v]; exact ht0
  hT := by rw [hT0v, hT1v]; exact ht
  hs0 := by norm_num
  hs2 := by norm_num
  hre_lo := by norm_num
  hre_hi := by norm_num
  hRpos := by rw [hRv]; exact Real.sqrt_pos.mpr hq
  hN1 := hn
  hbox_ball := by
    intro ρ hre him
    rw [hcv, hRv]
    rw [hT0v, hT1v] at him
    exact H1000Line.box_ball_of_sqrt h0 h1 ha hb ρ hre him
  hpinL := hpinL
  hpinH := hpinH

open Arb4 Arb4.Q

/-- The decidable side conditions of `ValidS` (as `Arb4.validB`, sharp pins). -/
def validBS (t0 t1 cim q : Q) (n : ℕ) (E : EnclQ) : Bool :=
  lt (ofNat 0) t0 && le t0 t1 && lt (ofNat 0) q && le t0 cim && le cim t1 &&
    lt (add (frac 9 4) (npow (sub cim t0) 2)) q && lt (add (frac 9 4) (npow (sub t1 cim) 2)) q &&
    Nat.ble 1 n &&
    lt (mul (mul (ofNat 2) (frac 3141593 1000000)) (sub (ofNat n) (ofNat 1))) (pinLQ E) &&
    lt (pinHQ E) (mul (mul (ofNat 2) (frac 3141592 1000000)) (add (ofNat n) (ofNat 1)))

set_option maxHeartbeats 1000000 in
theorem validS_of_B (d : BandData) (t0 t1 cim q : Q) (E : EnclQ) (hT0 : d.T0 = t0.val)
    (hT1 : d.T1 = t1.val) (hc : d.c = (⟨1 / 2, cim.val⟩ : ℂ)) (hR : d.R = Real.sqrt q.val)
    (h : validBS t0 t1 cim q d.n E = true) :
    ValidS (1 / 4000000) (3999999 / 4000000) (withEncl d E) := by
  simp only [validBS, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨ht0, ht⟩, hq⟩, h0⟩, h1⟩, ha⟩, hb⟩, hn⟩, hpL⟩, hpH⟩ := h
  have ht0' := lt_sound ht0
  have ht' := le_sound ht
  have hq' := lt_sound hq
  have h0' := le_sound h0
  have h1' := le_sound h1
  have ha' := lt_sound ha
  have hb' := lt_sound hb
  have hpL' := lt_sound hpL
  have hpH' := lt_sound hpH
  rw [val_ofNat, Nat.cast_zero] at ht0' hq'
  rw [val_add, val_npow, val_sub, val_frac _ (by norm_num)] at ha' hb'
  simp only [pinLQ, pinHQ, val_add, val_sub, val_mul, val_ofNat,
    val_frac _ (by norm_num : 1 ≤ 1000000)] at hpL' hpH'
  refine validS_of_sqrt (withEncl d E) t0.val t1.val cim.val q.val hT0 hT1 hc hR hn ht0' ht'
    hq' h0' h1' (by push_cast at ha' ⊢; linarith) (by push_cast at hb' ⊢; linarith) ?_ ?_
  · show 2 * 3.141593 * ((d.n : ℝ) - 1) < 2 * E.L1.val + E.L2.val - E.H3.val + E.L4.val + E.L5.val
    push_cast at hpL' ⊢
    norm_num at hpL' ⊢
    linarith
  · show 2 * E.H1.val + E.H2.val - E.L3.val + E.H4.val + E.H5.val < 2 * 3.141592 * ((d.n : ℝ) + 1)
    push_cast at hpH' ⊢
    norm_num at hpH' ⊢
    linarith

/-- **The band's box certificate from its parts, sharp pins** (`Arb4.boxCert_of_parts` with
    `ValidS` in place of `Valid`). -/
theorem boxCert_of_parts_sharp {lo hi δ0 δ1 : ℝ} (d : BandData) (E : EnclQ) (hlo : d.T0 ≤ lo)
    (hhi : hi ≤ d.T1) (hV : ValidS (1 / 4000000) (3999999 / 4000000) (withEncl d E))
    (hG : d.CapGeom δ0 δ1) (hL : d.LineHyp) (hs0 : EdgeClearGlue.SlabClear (d.T0 - δ0) d.T0)
    (hs1 : EdgeClearGlue.SlabClear d.T1 (d.T1 + δ1)) (hS : ArgChangeGlue.K6Side (withEncl d E))
    (hH1 : DiffractionCore.argChangeHoriz riemannZeta d.T1 2 (-1) ∈ Set.Icc E.L2.val E.H2.val)
    (hH0 : DiffractionCore.argChangeHoriz riemannZeta d.T0 2 (-1) ∈ Set.Icc E.L3.val E.H3.val) :
    BoxCert (1 / 4000000) (3999999 / 4000000) lo hi :=
  BoxCert.of_stmt (withEncl d E) hlo hhi (stmt_of_validS hV)
    (inputs_of_reduced (ArgChangeGlue.capGeom_transfer (d := d) (d' := withEncl d E) rfl rfl rfl rfl hG)
      ⟨hL, hs0, hs1, ArgChangeGlue.enclHyp_of_K6 hS ⟨hH1, hH0⟩⟩)

end H11K
