/- telperion 0.1.6 | family BagchiRecurrence | input-hash 7b4085ea0c0452b3
   3 theorems, 3 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace BagchiRecurrence

-- bagchi_recurrence_refutes: the falsifiability face.  RH ⟺ ζ strongly
-- recurrent; a certified recurrence-FAILURE (every large shift keeps the
-- deviation dev ≥ L with the recurrence tolerance ε ≤ L) contradicts
-- recurrence-below-ε, hence ¬RH (carried as hRH : RH → dev < ε).  Not
-- expected to fire; makes the recurrence observation falsifiable.
theorem bagchi_recurrence_refutes {P : Prop} (dev L eps : ℝ)
    (hRH : P → dev < eps) (hLo : L ≤ dev) (hbad : eps ≤ L) : ¬P :=
  fun hP => absurd (hRH hP) (not_lt.mpr (le_trans hbad hLo))

-- bagchi_tau1: Bagchi recurrence at shift τ = 1 over the box K = [3/5,7/10]×[10,12] (9 grid points).
-- Certified grid-max |ζ(s+iτ) − ζ(s)| ≤ M = 786800500196967263557182344103077379839630722219/1461501637330902918203684832716283019655932542976 (Arb acb_zeta, the trust
-- seam via hypothesis hdev) is ≤ ε = 538351/1000000.  Face 4 (Bagchi 1981: RH ⟺ ζ
-- strongly recurrent).  Scope: sup over the GRID (continuous sup needs a modulus
-- argument).  A finite recurrence observation; NOT RH.
theorem bagchi_tau1 (dev : ℝ) (hdev : dev ≤ ((786800500196967263557182344103077379839630722219 / 1461501637330902918203684832716283019655932542976) : ℝ)) : dev ≤ ((538351 / 1000000) : ℝ) :=
  le_trans hdev (by norm_num)

-- bagchi_tau8: Bagchi recurrence at shift τ = 8 over the box K = [3/5,7/10]×[10,12] (9 grid points).
-- Certified grid-max |ζ(s+iτ) − ζ(s)| ≤ M = 515418618750905243192970334858339927351097622369/730750818665451459101842416358141509827966271488 (Arb acb_zeta, the trust
-- seam via hypothesis hdev) is ≤ ε = 44083/62500.  Face 4 (Bagchi 1981: RH ⟺ ζ
-- strongly recurrent).  Scope: sup over the GRID (continuous sup needs a modulus
-- argument).  A finite recurrence observation; NOT RH.
theorem bagchi_tau8 (dev : ℝ) (hdev : dev ≤ ((515418618750905243192970334858339927351097622369 / 730750818665451459101842416358141509827966271488) : ℝ)) : dev ≤ ((44083 / 62500) : ℝ) :=
  le_trans hdev (by norm_num)

-- bagchi_tau24: Bagchi recurrence at shift τ = 24 over the box K = [3/5,7/10]×[10,12] (9 grid points).
-- Certified grid-max |ζ(s+iτ) − ζ(s)| ≤ M = 1300299596007043601736254452487895827490808773829/730750818665451459101842416358141509827966271488 (Arb acb_zeta, the trust
-- seam via hypothesis hdev) is ≤ ε = 177941/100000.  Face 4 (Bagchi 1981: RH ⟺ ζ
-- strongly recurrent).  Scope: sup over the GRID (continuous sup needs a modulus
-- argument).  A finite recurrence observation; NOT RH.
theorem bagchi_tau24 (dev : ℝ) (hdev : dev ≤ ((1300299596007043601736254452487895827490808773829 / 730750818665451459101842416358141509827966271488) : ℝ)) : dev ≤ ((177941 / 100000) : ℝ) :=
  le_trans hdev (by norm_num)

end BagchiRecurrence
