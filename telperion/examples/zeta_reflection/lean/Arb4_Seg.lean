/-  Arb4_Seg.lean -- lane Arb4: the band-level glue of a COMPACT hypothesis-free ladder segment.

    For a Turing band `d : BandGlue.BandData` of a ladder segment (its edges, count and Blaschke ball
    from the zeta_zero_localization band plan), the certificate route of `BandGlue` needs: the
    decidable side conditions `Valid` for the band with OUR enclosures, the K1 cap geometry, the
    on-line zeros, two zero-free slabs, the K6 side conditions and the two horizontal edges.  Here:

      * `EnclQ`, `withEncl`  -- the five enclosures as rationals, and the band with them swapped in;
      * `validB`, `valid_of_B` -- `Valid` (ball cover of the RvM rectangle, the two pins) from ONE
                               Boolean over the band's rational table values;
      * `k6sideB`, `k6side_of_B` -- `ArgChangeGlue.K6Side` (K6a range, K6b brackets) from ONE Boolean;
      * `boxCert_of_parts`   -- the band's `BandGlue.BoxCert` from the parts (K0 + K1 + K6).

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (Arb4_AxiomGuard).  No `sorry`.  conjecture1_proved = False.
-/
import Arb4_Gamma
import Arb4_Slab
import Arb4_Line
import ArgChangeGlue
import H1000Glue

open Complex

namespace Arb4

open Q BandGlue BandGlue.BandData

/-- The five RvM enclosures `[L1,H1] … [L5,H5]` as rationals. -/
structure EnclQ where
  L1 : Q
  H1 : Q
  L2 : Q
  H2 : Q
  L3 : Q
  H3 : Q
  L4 : Q
  H4 : Q
  L5 : Q
  H5 : Q

/-- Band `d` with its five enclosures replaced by `E` (same `T0`, `T1`, `n`, ball). -/
noncomputable def withEncl (d : BandData) (E : EnclQ) : BandData :=
  ⟨d.T0, d.T1, d.n, E.L1.val, E.H1.val, E.L2.val, E.H2.val, E.L3.val, E.H3.val, E.L4.val, E.H4.val,
    E.L5.val, E.H5.val, d.c, d.R, d.hs1⟩

/-- `2 L1 + L2 - H3 + L4 + L5`. -/
def pinLQ (E : EnclQ) : Q := add (add (sub (add (mul (ofNat 2) E.L1) E.L2) E.H3) E.L4) E.L5

/-- `2 H1 + H2 - L3 + H4 + H5`. -/
def pinHQ (E : EnclQ) : Q := add (add (sub (add (mul (ofNat 2) E.H1) E.H2) E.L3) E.H4) E.H5

/-- The decidable side conditions of `BandGlue.BandData.Valid` for band `(t0, t1, n)` with ball
    `1/2 + i cim`, radius `√q`, and enclosures `E`. -/
def validB (t0 t1 cim q : Q) (n : ℕ) (E : EnclQ) : Bool :=
  lt (ofNat 0) t0 && le t0 t1 && lt (ofNat 0) q && le t0 cim && le cim t1 &&
    lt (add (frac 9 4) (npow (sub cim t0) 2)) q && lt (add (frac 9 4) (npow (sub t1 cim) 2)) q &&
    Nat.ble 1 n &&
    lt (mul (mul (ofNat 2) (frac 31416 10000)) (sub (ofNat n) (ofNat 1))) (pinLQ E) &&
    lt (pinHQ E) (mul (mul (ofNat 2) (frac 314 100)) (add (ofNat n) (ofNat 1)))

set_option maxHeartbeats 1000000 in
theorem valid_of_B (d : BandData) (t0 t1 cim q : Q) (E : EnclQ) (hT0 : d.T0 = t0.val)
    (hT1 : d.T1 = t1.val) (hc : d.c = (⟨1 / 2, cim.val⟩ : ℂ)) (hR : d.R = Real.sqrt q.val)
    (h : validB t0 t1 cim q d.n E = true) :
    (withEncl d E).Valid (1 / 4000000) (3999999 / 4000000) := by
  simp only [validB, Bool.and_eq_true, Nat.ble_eq] at h
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
  simp only [pinLQ, pinHQ, val_add, val_sub, val_mul, val_ofNat, val_frac _ (by norm_num : 1 ≤ 10000),
    val_frac _ (by norm_num : 1 ≤ 100)] at hpL' hpH'
  refine H1000Line.valid_of_sqrt (withEncl d E) t0.val t1.val cim.val q.val hT0 hT1 hc hR hn ht0' ht'
    hq' h0' h1' (by push_cast at ha' ⊢; linarith) (by push_cast at hb' ⊢; linarith) ?_ ?_
  · show 2 * 3.1416 * ((d.n : ℝ) - 1) < 2 * E.L1.val + E.L2.val - E.H3.val + E.L4.val + E.L5.val
    push_cast at hpL' ⊢
    norm_num at hpL' ⊢
    linarith
  · show 2 * E.H1.val + E.H2.val - E.L3.val + E.H4.val + E.H5.val < 2 * 3.14 * ((d.n : ℝ) + 1)
    push_cast at hpH' ⊢
    norm_num at hpH' ⊢
    linarith

/-- The K6a range of `[L1, H1]` and the K6b comparisons of `[L4, H4]`, `[L5, H5]`. -/
def k6sideB (G0 G1 : GamD) (E : EnclQ) : Bool :=
  le E.L1 (frac (-249) 250) && le (frac 249 250) E.H1 && k6B G0 G1 E.L4 E.H4 E.L5 E.H5

theorem k6side_of_B (d : BandData) (G0 G1 : GamD) (E : EnclQ) (hT0 : d.T0 = G0.T.val)
    (hT1 : d.T1 = G1.T.val) (h : k6sideB G0 G1 E = true) : ArgChangeGlue.K6Side (withEncl d E) := by
  simp only [k6sideB, Bool.and_eq_true] at h
  obtain ⟨⟨hL1, hH1⟩, hk⟩ := h
  obtain ⟨a0, a1, l4, h4, l5, h5⟩ := k6B_sound G0 G1 E.L4 E.H4 E.L5 E.H5 hk
  have hL1' := le_sound hL1
  have hH1' := le_sound hH1
  rw [val_frac _ (by norm_num)] at hL1' hH1'
  have hT0' : (withEncl d E).T0 = G0.T.val := hT0
  have hT1' : (withEncl d E).T1 = G1.T.val := hT1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hT0']; exact a0
  · rw [hT1']; exact a1
  · show E.L1.val ≤ -(249 / 250); push_cast at hL1'; linarith
  · show 249 / 250 ≤ E.H1.val; push_cast at hH1'; linarith
  · rw [hT0', hT1']; exact l4
  · rw [hT0', hT1']; exact h4
  · rw [hT0', hT1']; exact l5
  · rw [hT0', hT1']; exact h5

/-- **The band's box certificate from its parts** (K0 + K1 + K6): the ball cover and pins of `Valid`
    for the band with enclosures `E`, the cap geometry, the on-line zeros, the two zero-free slabs,
    the K6 side conditions and the two horizontal argument changes. -/
theorem boxCert_of_parts {lo hi δ0 δ1 : ℝ} (d : BandData) (E : EnclQ) (hlo : d.T0 ≤ lo)
    (hhi : hi ≤ d.T1) (hV : (withEncl d E).Valid (1 / 4000000) (3999999 / 4000000))
    (hG : d.CapGeom δ0 δ1) (hL : d.LineHyp) (hs0 : EdgeClearGlue.SlabClear (d.T0 - δ0) d.T0)
    (hs1 : EdgeClearGlue.SlabClear d.T1 (d.T1 + δ1)) (hS : ArgChangeGlue.K6Side (withEncl d E))
    (hH1 : DiffractionCore.argChangeHoriz riemannZeta d.T1 2 (-1) ∈ Set.Icc E.L2.val E.H2.val)
    (hH0 : DiffractionCore.argChangeHoriz riemannZeta d.T0 2 (-1) ∈ Set.Icc E.L3.val E.H3.val) :
    BoxCert (1 / 4000000) (3999999 / 4000000) lo hi :=
  BoxCert.of_valid (withEncl d E) hlo hhi hV
    (inputs_of_reduced (ArgChangeGlue.capGeom_transfer (d := d) (d' := withEncl d E) rfl rfl rfl rfl hG)
      ⟨hL, hs0, hs1, ArgChangeGlue.enclHyp_of_K6 hS ⟨hH1, hH0⟩⟩)

end Arb4
