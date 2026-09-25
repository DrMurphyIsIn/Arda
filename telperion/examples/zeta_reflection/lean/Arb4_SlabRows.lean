/-  Arb4_SlabRows.lean -- lane Arb4 (scaling past height 2000): stacking zero-free slabs.

    From height about 2500 on, a band edge can sit a few hundredths above or below a zero on the
    critical line (for example the zero near 2479.977 under the edge `T = 2480`), and the
    edge-clearance slab `[T, T + cap]` next to it cannot be covered by full-height x-columns: the
    cells touching the zero must be short as well as narrow.  The slab planner then cuts the slab
    into horizontal ROWS `lo = y0 < y1 < ... < yk = hi`, certifies each row with its own
    `Arb4.slabOK` (x-columns only, `Arb4_Slab.lean` unchanged), and the rows are stacked here:

      * `slabClear_join` -- `SlabClear a m` and `SlabClear m b` give `SlabClear a b`.

    Trust: proved from its hypotheses; axioms [propext, Classical.choice, Quot.sound]
    (Arb4_AxiomGuard).  No `sorry`.  conjecture1_proved = False.
-/
import EdgeClearGlue

namespace Arb4

/-- Two zero-free slabs that meet at height `m` make one zero-free slab. -/
theorem slabClear_join {a m b : ℝ} (h1 : EdgeClearGlue.SlabClear a m)
    (h2 : EdgeClearGlue.SlabClear m b) : EdgeClearGlue.SlabClear a b := by
  intro x y hx0 hx1 hya hyb
  rcases le_total y m with hym | hym
  · exact h1 x y hx0 hx1 hya hym
  · exact h2 x y hx0 hx1 hym hyb

end Arb4
