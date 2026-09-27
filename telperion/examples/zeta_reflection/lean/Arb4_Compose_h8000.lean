/-  Arb4_Compose_h8000.lean -- the height-8000 ladder as an IMPLICATION from its eight segment
    band hypotheses, for the COMPOSITIONAL independent judge (missions-comparator-heavy.yml).

        ladder_h8000_of_bands :
          AllZeros_h1000.BandHyp → AllZeros_h2000.BandHyp → … → AllZeros_h8000.BandHyp →
          ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 8000 → ρ.re = 1 / 2

    Why: the Comparator replays a theorem's whole dependency closure in ONE single-threaded kernel
    run. For `Arb4_h8000.all_nontrivial_zeros_up_to_height_8000` that closure is every segment's
    edge / slab / line certificate (run 36274981386: > 4 h, cancelled). The judge therefore checks
    the eight `Arb4_h<H>.hbands : AllZeros_h<H>.BandHyp` separately (one closure per segment) and
    THIS implication once. Its proof is the capstone's own composition (`height_chain` over the
    `segment_*` lemmas + `HeightFloor.height_floor`) with the eight `hbands` abstracted as binders,
    so its closure contains NO certificate module: the judge asserts that mechanically (no
    constant of an `Arb4_h<H>` / `Arb4_H<H>{Edges,Slabs,Lines}_<i>` module in its closure).

    Imports: statements and glue only -- never a certificate module.
    Axioms [propext, Classical.choice, Quot.sound]; no `sorry`.  conjecture1_proved = False.
-/
import AllZeros_h1000
import AllZeros_h2000
import AllZeros_h3000
import AllZeros_h4000
import AllZeros_h5000
import AllZeros_h6000
import AllZeros_h7000
import AllZeros_h8000
import AllZerosUpToHeight
import HeightFloor

namespace Arb4_Compose_h8000

/-- **The height-8000 ladder from its eight segment band hypotheses** (no certificate inside). -/
theorem ladder_h8000_of_bands
    (b1000 : AllZeros_h1000.BandHyp) (b2000 : AllZeros_h2000.BandHyp)
    (b3000 : AllZeros_h3000.BandHyp) (b4000 : AllZeros_h4000.BandHyp)
    (b5000 : AllZeros_h5000.BandHyp) (b6000 : AllZeros_h6000.BandHyp)
    (b7000 : AllZeros_h7000.BandHyp) (b8000 : AllZeros_h8000.BandHyp) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 8000 → ρ.re = 1 / 2 :=
  have h1000 := AllZeros_h1000.all_nontrivial_zeros_up_to_height_1000_of_bands b1000
    (HeightFloor.height_floor 1000)
  have h2000 := AllZerosUpToHeight.height_chain 1000 2000 h1000
    (AllZeros_h2000.segment_1000_2000 b2000 (HeightFloor.height_floor 2000))
  have h3000 := AllZerosUpToHeight.height_chain 2000 3000 h2000
    (AllZeros_h3000.segment_2000_3000 b3000 (HeightFloor.height_floor 3000))
  have h4000 := AllZerosUpToHeight.height_chain 3000 4000 h3000
    (AllZeros_h4000.segment_3000_4000 b4000 (HeightFloor.height_floor 4000))
  have h5000 := AllZerosUpToHeight.height_chain 4000 5000 h4000
    (AllZeros_h5000.segment_4000_5000 b5000 (HeightFloor.height_floor 5000))
  have h6000 := AllZerosUpToHeight.height_chain 5000 6000 h5000
    (AllZeros_h6000.segment_5000_6000 b6000 (HeightFloor.height_floor 6000))
  have h7000 := AllZerosUpToHeight.height_chain 6000 7000 h6000
    (AllZeros_h7000.segment_6000_7000 b7000 (HeightFloor.height_floor 7000))
  AllZerosUpToHeight.height_chain 7000 8000 h7000
    (AllZeros_h8000.segment_7000_8000 b8000 (HeightFloor.height_floor 8000))

end Arb4_Compose_h8000
