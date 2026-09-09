/-
Li positivity ladder — certified rungs of Li's criterion.

Each theorem certifies the n-th rung `0 ≤ (taylorCoeff riemannXi n).re` from a
certified positive rational lower bound `hlo` (the external Arb enclosure of ξ's
n-th Taylor coefficient — the documented trust seam).  Together with the upstream

    LiCriterion.li_criterion_rh_iff :
        RiemannHypothesis ↔ (∀ n, 0 ≤ (taylorCoeff riemannXi n).re)

each rung is a FINITE prefix of the RH-equivalent ladder.  The uniform `∀ n` IS
RH; a rung is NOT.  conjecture1_proved = False.

Emitted by telperion's LiPositivityLadderEmitter (kind `li_positivity`); this
file is the wiring example that compiles the emitted rung against the upstream
`LiCriterion` library (see docs/LI_POSITIVITY_LADDER.md).
-/
import Lc.LiCriterion.XiOrderBridge

open LiCriterion

-- li_rung_1: Li-criterion rung n=1 — witnessed by the certified lower bound lo=1/100.
theorem li_rung_1 (hlo : ((1 / 100) : ℝ) ≤ (taylorCoeff riemannXi 1).re) :
    0 ≤ (taylorCoeff riemannXi 1).re :=
  le_trans (by norm_num : (0 : ℝ) ≤ (1 / 100)) hlo
