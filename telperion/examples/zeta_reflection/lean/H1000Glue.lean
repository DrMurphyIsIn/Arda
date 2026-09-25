/-  H1000Glue.lean -- integration glue for the height-1000 segment (lane h1000-prep).

    The segment's band table `BandGlue_h1000.seg` carries the TIGHT Arb enclosures (width about 1e-12)
    of the five RvM argument changes, and each band's `rh_in_box_*` theorem has its pins and its
    ball-cover geometry baked in for exactly those numbers.  A kernel evaluator will certify WIDER
    enclosures.  This file lets the integration stage swap in its own enclosures band by band:

      * `Encl`            : five enclosures `[L1,H1] … [L5,H5]` (the order of `BandGlue.BandData`);
      * `segWith i E`     : band `i` of the segment with its enclosures replaced by `E` (same `T0`, `T1`,
                            `n`, ball `c`, `R`);
      * `PinOk i E`       : the two pin inequalities of `BandGlue.BandData.Valid` for `segWith i E`
                            (decidable: `norm_num` on rationals);
      * `box_ball_of_sqrt`, `valid_of_sqrt` : the ball-cover geometry and the full `Valid` structure
                            from the band's explicit numbers (`T0`, `T1`, `c = 1/2 + i·cim`, `R = √q`);
      * `capGeom_segWith` : the K1 cap geometry transfers from `seg i` to `segWith i E`;
      * `slabClear_low`, `slab0_band0` : an edge-clearance slab below height `55/16` is zero-free by
                            the height floor (`HeightFloor.strip_clear_low`); this discharges the lower
                            slab of band 0 (`[1 - capLo 0, 1]`), leaving 49 slab facts.

    The per-band `Valid` instances and the final theorem are generated into `H1000Line_All.lean`.

    Pin budget (computed from the `seg` table, see LANE_NOTES_h1000-prep.md): the lower pin has slack
    at least 6.2827 rad and the upper at least 6.178 rad in every band, so the one-sided enclosure
    errors `2 e1 + e2 + e3 + e4 + e5` may total about 6.18 rad (for example ±1 rad each).

    Trust: axioms [propext, Classical.choice, Quot.sound] (AxiomGuardH1000Line.lean); no `sorry`.
    conjecture1_proved = False.  Glue for a finite verification; nothing here bears on RH.
-/
import BandGlue_h1000
import HeightFloor

open Complex

namespace H1000Line

/-- Five RvM enclosures `[L1,H1], …, [L5,H5]`, in the order of `BandGlue.BandData`:
    `argChangeVert ζ 2`, `argChangeHoriz ζ T1`, `argChangeHoriz ζ T0`, `argChangeVert Γℝ (-1)`,
    `argChangeVert Γℝ 2`. -/
structure Encl where
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

/-- Band `i` of the height-1000 segment with its five enclosures replaced by `E`. -/
noncomputable def segWith (i : ℕ) (E : Encl) : BandGlue.BandData :=
  { BandGlue_h1000.seg i with
    L1 := E.L1, H1 := E.H1, L2 := E.L2, H2 := E.H2, L3 := E.L3, H3 := E.H3,
    L4 := E.L4, H4 := E.H4, L5 := E.L5, H5 := E.H5 }

/-- The enclosures of `seg i` itself (so `segWith i (segEncl i) = seg i` field by field). -/
noncomputable def segEncl (i : ℕ) : Encl :=
  ⟨(BandGlue_h1000.seg i).L1, (BandGlue_h1000.seg i).H1, (BandGlue_h1000.seg i).L2,
   (BandGlue_h1000.seg i).H2, (BandGlue_h1000.seg i).L3, (BandGlue_h1000.seg i).H3,
   (BandGlue_h1000.seg i).L4, (BandGlue_h1000.seg i).H4, (BandGlue_h1000.seg i).L5,
   (BandGlue_h1000.seg i).H5⟩

/-- The two pins of `BandGlue.BandData.Valid` for `segWith i E`. -/
def PinOk (i : ℕ) (E : Encl) : Prop :=
  2 * 3.1416 * (((BandGlue_h1000.seg i).n : ℝ) - 1) < 2 * E.L1 + E.L2 - E.H3 + E.L4 + E.L5 ∧
    2 * E.H1 + E.H2 - E.L3 + E.H4 + E.H5 < 2 * 3.14 * (((BandGlue_h1000.seg i).n : ℝ) + 1)

/-- **Ball-cover geometry**: the RvM rectangle `[-1, 2] × [T0, T1]` lies in the ball of centre
    `1/2 + i cim` and radius `√q` when both far corners do (`9/4 + (cim - T0)² < q`,
    `9/4 + (T1 - cim)² < q`). -/
theorem box_ball_of_sqrt {T0 T1 cim q : ℝ} (h0 : T0 ≤ cim) (h1 : cim ≤ T1)
    (ha : 9 / 4 + (cim - T0) ^ 2 < q) (hb : 9 / 4 + (T1 - cim) ^ 2 < q) :
    ∀ ρ : ℂ, ((-1 : ℝ) ≤ ρ.re ∧ ρ.re ≤ 2) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      ρ ∈ Metric.ball (⟨1 / 2, cim⟩ : ℂ) (Real.sqrt q) := by
  intro ρ hre him
  rw [Metric.mem_ball, Complex.dist_eq_re_im]
  apply Real.sqrt_lt_sqrt (by positivity)
  simp only
  have hx : (ρ.re - 1 / 2) ^ 2 ≤ 9 / 4 := by nlinarith [hre.1, hre.2]
  have hy : (ρ.im - cim) ^ 2 ≤ max ((cim - T0) ^ 2) ((T1 - cim) ^ 2) := by
    rcases le_total ρ.im cim with h | h
    · have : (ρ.im - cim) ^ 2 ≤ (cim - T0) ^ 2 := by nlinarith [him.1]
      exact le_trans this (le_max_left _ _)
    · have : (ρ.im - cim) ^ 2 ≤ (T1 - cim) ^ 2 := by nlinarith [him.2]
      exact le_trans this (le_max_right _ _)
  rcases le_total ((cim - T0) ^ 2) ((T1 - cim) ^ 2) with hm | hm
  · rw [max_eq_right hm] at hy; linarith
  · rw [max_eq_left hm] at hy; linarith

/-- **`Valid` from the band's explicit numbers** (`T0 = t0`, `T1 = t1`, `c = 1/2 + i cim`,
    `R = √q`): the decidable side conditions of `BandGlue.BandData.stmt_of_valid`. -/
theorem valid_of_sqrt (d : BandGlue.BandData) (t0 t1 cim q : ℝ) (hT0v : d.T0 = t0) (hT1v : d.T1 = t1)
    (hcv : d.c = (⟨1 / 2, cim⟩ : ℂ)) (hRv : d.R = Real.sqrt q) (hn : 1 ≤ d.n)
    (ht0 : 0 < t0) (ht : t0 ≤ t1) (hq : 0 < q) (h0 : t0 ≤ cim) (h1 : cim ≤ t1)
    (ha : 9 / 4 + (cim - t0) ^ 2 < q) (hb : 9 / 4 + (t1 - cim) ^ 2 < q)
    (hpinL : 2 * 3.1416 * ((d.n : ℝ) - 1) < 2 * d.L1 + d.L2 - d.H3 + d.L4 + d.L5)
    (hpinH : 2 * d.H1 + d.H2 - d.L3 + d.H4 + d.H5 < 2 * 3.14 * ((d.n : ℝ) + 1)) :
    d.Valid (1 / 4000000) (3999999 / 4000000) where
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
    exact box_ball_of_sqrt h0 h1 ha hb ρ hre him
  hpinL := hpinL
  hpinH := hpinH

/-- The K1 cap geometry of `seg i` is that of `segWith i E` (same `T0`, `T1`, `c`, `R`). -/
theorem capGeom_segWith {i : ℕ} (E : Encl) {δ0 δ1 : ℝ}
    (g : (BandGlue_h1000.seg i).CapGeom δ0 δ1) : (segWith i E).CapGeom δ0 δ1 :=
  ⟨g.hT0, g.hT1, g.hδ0, g.hδ1, g.hpos, g.hlo, g.hhi⟩

/-- A slab below the height floor is zero-free: `0 < a`, `b ≤ 55/16`. -/
theorem slabClear_low {a b : ℝ} (ha : 0 < a) (hb : b ≤ 55 / 16) : EdgeClearGlue.SlabClear a b := by
  intro x y hx0 hx1 hya hyb hz
  have hre : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
  have him : ((x : ℂ) + (y : ℂ) * I).im = y := by simp
  exact HeightFloor.strip_clear_low ((x : ℂ) + (y : ℂ) * I) hz (by rw [hre]; exact hx0)
    (by rw [hre]; exact hx1) (by rw [him]; linarith) (by rw [him]; linarith)

/-- **The lower edge-clearance slab of band 0 is discharged** (it lies in `[0.94227, 1]`, below the
    height floor). -/
theorem slab0_band0 :
    EdgeClearGlue.SlabClear ((BandGlue_h1000.seg 0).T0 - BandGlue_h1000.capLo 0) (BandGlue_h1000.seg 0).T0 := by
  show EdgeClearGlue.SlabClear ((1 : ℝ) - 5773 / 100000) 1
  exact slabClear_low (by norm_num) (by norm_num)

end H1000Line
