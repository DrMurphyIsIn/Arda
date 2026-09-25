/-  EMZetaOfflineSlabBand.lean -- lane offline: the kernel-checked slab of `EMZetaOfflineSlab_T1000`
    IS the top-edge clearance input of band 24 of the real `[1, 1000]` segment (`BandGlue_h1000`).

    `BandGlue.BandData.ReducedInputs δ0 δ1 d` asks, for each band `d`, for the two one-sided slabs
    `SlabClear (d.T0 - δ0) d.T0` and `SlabClear d.T1 (d.T1 + δ1)`; `BandGlue_h1000` fixes
    `δ1 = capHi i` (band `i`'s top ball cap rounded up to 1e-6).  For band 24 (`[960, 1000]`) the top
    slab is `SlabClear 1000 (1000 + 5773/100000)`, proved here with NO hypotheses.  As a corollary
    (`EdgeClearGlue.hnz_edge_of_slabClear`) the segment's top edge `[-1, 2] + 1000 i` is zero-free.

    Axioms [propext, Classical.choice, Quot.sound] (AxiomGuardEMZetaOffline).  No `sorry`.
    conjecture1_proved = False.  One finite slab; nothing about RH.
-/
import EMZetaOfflineSlab_T1000
import BandGlue_h1000

open Complex

namespace ArbEcon.Off.Slab_T1000

/-- **Band 24 of `AllZeros_h1000`: the top-edge clearance slab, hypothesis-free.**  This is the
    `SlabClear d.T1 (d.T1 + δ1)` conjunct of `BandGlue.BandData.ReducedInputs` for
    `d = BandGlue_h1000.seg 24`, `δ1 = BandGlue_h1000.capHi 24`. -/
theorem band24_top_slabClear :
    EdgeClearGlue.SlabClear (BandGlue_h1000.seg 24).T1
      ((BandGlue_h1000.seg 24).T1 + BandGlue_h1000.capHi 24) := by
  have h1 : (BandGlue_h1000.seg 24).T1 = 1000 := by
    simp [BandGlue_h1000.seg]
  have h2 : BandGlue_h1000.capHi 24 = 5773 / 100000 := by
    simp [BandGlue_h1000.capHi]
  rw [h1, h2]
  exact slabClear

/-- **The top edge of the `[1, 1000]` segment is zero-free**: `ζ(x + 1000 i) ≠ 0` for every
    `x ∈ [-1, 2]` (the `hnzt` conjunct of band 24), from the slab and the strip theorem. -/
theorem top_edge_1000_nonvanishing :
    ∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta (↑x + ((1000 : ℝ) : ℂ) * I) ≠ 0 :=
  EdgeClearGlue.hnz_edge_of_slabClear (by norm_num) le_rfl (by norm_num) slabClear

end ArbEcon.Off.Slab_T1000
