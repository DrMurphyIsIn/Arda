/- telperion 0.1.6 | family LiPositivity | input-hash c4e9883e70bc4828
   20 theorems, 20 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Lc.LiCriterion.XiOrderBridge

namespace LiPositivity

open LiCriterion

-- li_neg_refutes_rh: the falsifiability face of the ladder.  A certified
-- NEGATIVE upper bound on any rung would refute RH via the upstream
-- equivalence.  Not expected to fire; emitted so the ladder is falsifiable,
-- not confirmation-only.  hhi carries the same Arb trust seam as hlo.
theorem li_neg_refutes_rh (n : ℕ) (hi : ℝ)
    (hhi : (taylorCoeff riemannXi n).re ≤ hi) (hneg : hi < 0) :
    ¬RiemannHypothesis :=
  fun hRH => absurd (li_criterion_rh_iff.mp hRH n)
    (not_le.mpr (lt_of_le_of_lt hhi hneg))

-- li_rung_0: Li-criterion rung n=0 — 0 ≤ (taylorCoeff riemannXi 0).re, witnessed by the certified lower bound lo=230957089661/10000000000000.
-- Trust seam: hlo (the Arb enclosure of ξ's Taylor coefficient) is a HYPOTHESIS.
-- Feeds LiCriterion.li_criterion_rh_iff (RH ⟺ ∀ n, 0 ≤ this); a finite rung, NOT RH.
theorem li_rung_0 (hlo : ((230957089661 / 10000000000000) : ℝ) ≤ (taylorCoeff riemannXi 0).re) : 0 ≤ (taylorCoeff riemannXi 0).re :=
  le_trans (by norm_num : (0:ℝ) ≤ (230957089661 / 10000000000000)) hlo

-- li_rung_1: Li-criterion rung n=1 — 0 ≤ (taylorCoeff riemannXi 1).re, witnessed by the certified lower bound lo=23086433807/250000000000.
-- Trust seam: hlo (the Arb enclosure of ξ's Taylor coefficient) is a HYPOTHESIS.
-- Feeds LiCriterion.li_criterion_rh_iff (RH ⟺ ∀ n, 0 ≤ this); a finite rung, NOT RH.
theorem li_rung_1 (hlo : ((23086433807 / 250000000000) : ℝ) ≤ (taylorCoeff riemannXi 1).re) : 0 ≤ (taylorCoeff riemannXi 1).re :=
  le_trans (by norm_num : (0:ℝ) ≤ (23086433807 / 250000000000)) hlo

-- li_rung_2: Li-criterion rung n=2 — 0 ≤ (taylorCoeff riemannXi 2).re, witnessed by the certified lower bound lo=103819460277/500000000000.
-- Trust seam: hlo (the Arb enclosure of ξ's Taylor coefficient) is a HYPOTHESIS.
-- Feeds LiCriterion.li_criterion_rh_iff (RH ⟺ ∀ n, 0 ≤ this); a finite rung, NOT RH.
theorem li_rung_2 (hlo : ((103819460277 / 500000000000) : ℝ) ≤ (taylorCoeff riemannXi 2).re) : 0 ≤ (taylorCoeff riemannXi 2).re :=
  le_trans (by norm_num : (0:ℝ) ≤ (103819460277 / 500000000000)) hlo

-- li_rung_3: Li-criterion rung n=3 — 0 ≤ (taylorCoeff riemannXi 3).re, witnessed by the certified lower bound lo=92197619873/250000000000.
-- Trust seam: hlo (the Arb enclosure of ξ's Taylor coefficient) is a HYPOTHESIS.
-- Feeds LiCriterion.li_criterion_rh_iff (RH ⟺ ∀ n, 0 ≤ this); a finite rung, NOT RH.
theorem li_rung_3 (hlo : ((92197619873 / 250000000000) : ℝ) ≤ (taylorCoeff riemannXi 3).re) : 0 ≤ (taylorCoeff riemannXi 3).re :=
  le_trans (by norm_num : (0:ℝ) ≤ (92197619873 / 250000000000)) hlo

-- li_rung_4: Li-criterion rung n=4 — 0 ≤ (taylorCoeff riemannXi 4).re, witnessed by the certified lower bound lo=575542714461/1000000000000.
-- Trust seam: hlo (the Arb enclosure of ξ's Taylor coefficient) is a HYPOTHESIS.
-- Feeds LiCriterion.li_criterion_rh_iff (RH ⟺ ∀ n, 0 ≤ this); a finite rung, NOT RH.
theorem li_rung_4 (hlo : ((575542714461 / 1000000000000) : ℝ) ≤ (taylorCoeff riemannXi 4).re) : 0 ≤ (taylorCoeff riemannXi 4).re :=
  le_trans (by norm_num : (0:ℝ) ≤ (575542714461 / 1000000000000)) hlo

-- li_rung_5: Li-criterion rung n=5 — 0 ≤ (taylorCoeff riemannXi 5).re, witnessed by the certified lower bound lo=413783006141/500000000000.
-- Trust seam: hlo (the Arb enclosure of ξ's Taylor coefficient) is a HYPOTHESIS.
-- Feeds LiCriterion.li_criterion_rh_iff (RH ⟺ ∀ n, 0 ≤ this); a finite rung, NOT RH.
theorem li_rung_5 (hlo : ((413783006141 / 500000000000) : ℝ) ≤ (taylorCoeff riemannXi 5).re) : 0 ≤ (taylorCoeff riemannXi 5).re :=
  le_trans (by norm_num : (0:ℝ) ≤ (413783006141 / 500000000000)) hlo

-- li_rung_6: Li-criterion rung n=6 — 0 ≤ (taylorCoeff riemannXi 6).re, witnessed by the certified lower bound lo=112446011757/100000000000.
-- Trust seam: hlo (the Arb enclosure of ξ's Taylor coefficient) is a HYPOTHESIS.
-- Feeds LiCriterion.li_criterion_rh_iff (RH ⟺ ∀ n, 0 ≤ this); a finite rung, NOT RH.
theorem li_rung_6 (hlo : ((112446011757 / 100000000000) : ℝ) ≤ (taylorCoeff riemannXi 6).re) : 0 ≤ (taylorCoeff riemannXi 6).re :=
  le_trans (by norm_num : (0:ℝ) ≤ (112446011757 / 100000000000)) hlo

-- li_rung_7: Li-criterion rung n=7 — 0 ≤ (taylorCoeff riemannXi 7).re, witnessed by the certified lower bound lo=73287783857/50000000000.
-- Trust seam: hlo (the Arb enclosure of ξ's Taylor coefficient) is a HYPOTHESIS.
-- Feeds LiCriterion.li_criterion_rh_iff (RH ⟺ ∀ n, 0 ≤ this); a finite rung, NOT RH.
theorem li_rung_7 (hlo : ((73287783857 / 50000000000) : ℝ) ≤ (taylorCoeff riemannXi 7).re) : 0 ≤ (taylorCoeff riemannXi 7).re :=
  le_trans (by norm_num : (0:ℝ) ≤ (73287783857 / 50000000000)) hlo

-- li_rung_8: Li-criterion rung n=8 — 0 ≤ (taylorCoeff riemannXi 8).re, witnessed by the certified lower bound lo=92545802419/50000000000.
-- Trust seam: hlo (the Arb enclosure of ξ's Taylor coefficient) is a HYPOTHESIS.
-- Feeds LiCriterion.li_criterion_rh_iff (RH ⟺ ∀ n, 0 ≤ this); a finite rung, NOT RH.
theorem li_rung_8 (hlo : ((92545802419 / 50000000000) : ℝ) ≤ (taylorCoeff riemannXi 8).re) : 0 ≤ (taylorCoeff riemannXi 8).re :=
  le_trans (by norm_num : (0:ℝ) ≤ (92545802419 / 50000000000)) hlo

-- li_rung_9: Li-criterion rung n=9 — 0 ≤ (taylorCoeff riemannXi 9).re, witnessed by the certified lower bound lo=227933936319/100000000000.
-- Trust seam: hlo (the Arb enclosure of ξ's Taylor coefficient) is a HYPOTHESIS.
-- Feeds LiCriterion.li_criterion_rh_iff (RH ⟺ ∀ n, 0 ≤ this); a finite rung, NOT RH.
theorem li_rung_9 (hlo : ((227933936319 / 100000000000) : ℝ) ≤ (taylorCoeff riemannXi 9).re) : 0 ≤ (taylorCoeff riemannXi 9).re :=
  le_trans (by norm_num : (0:ℝ) ≤ (227933936319 / 100000000000)) hlo

-- li_rung_10: Li-criterion rung n=10 — 0 ≤ (taylorCoeff riemannXi 10).re, witnessed by the certified lower bound lo=137518041911/50000000000.
-- Trust seam: hlo (the Arb enclosure of ξ's Taylor coefficient) is a HYPOTHESIS.
-- Feeds LiCriterion.li_criterion_rh_iff (RH ⟺ ∀ n, 0 ≤ this); a finite rung, NOT RH.
theorem li_rung_10 (hlo : ((137518041911 / 50000000000) : ℝ) ≤ (taylorCoeff riemannXi 10).re) : 0 ≤ (taylorCoeff riemannXi 10).re :=
  le_trans (by norm_num : (0:ℝ) ≤ (137518041911 / 50000000000)) hlo

-- li_rung_11: Li-criterion rung n=11 — 0 ≤ (taylorCoeff riemannXi 11).re, witnessed by the certified lower bound lo=163162766031/50000000000.
-- Trust seam: hlo (the Arb enclosure of ξ's Taylor coefficient) is a HYPOTHESIS.
-- Feeds LiCriterion.li_criterion_rh_iff (RH ⟺ ∀ n, 0 ≤ this); a finite rung, NOT RH.
theorem li_rung_11 (hlo : ((163162766031 / 50000000000) : ℝ) ≤ (taylorCoeff riemannXi 11).re) : 0 ≤ (taylorCoeff riemannXi 11).re :=
  le_trans (by norm_num : (0:ℝ) ≤ (163162766031 / 50000000000)) hlo

-- li_rung_12: Li-criterion rung n=12 — 0 ≤ (taylorCoeff riemannXi 12).re, witnessed by the certified lower bound lo=47715500723/12500000000.
-- Trust seam: hlo (the Arb enclosure of ξ's Taylor coefficient) is a HYPOTHESIS.
-- Feeds LiCriterion.li_criterion_rh_iff (RH ⟺ ∀ n, 0 ≤ this); a finite rung, NOT RH.
theorem li_rung_12 (hlo : ((47715500723 / 12500000000) : ℝ) ≤ (taylorCoeff riemannXi 12).re) : 0 ≤ (taylorCoeff riemannXi 12).re :=
  le_trans (by norm_num : (0:ℝ) ≤ (47715500723 / 12500000000)) hlo

-- li_rung_13: Li-criterion rung n=13 — 0 ≤ (taylorCoeff riemannXi 13).re, witnessed by the certified lower bound lo=110286941967/25000000000.
-- Trust seam: hlo (the Arb enclosure of ξ's Taylor coefficient) is a HYPOTHESIS.
-- Feeds LiCriterion.li_criterion_rh_iff (RH ⟺ ∀ n, 0 ≤ this); a finite rung, NOT RH.
theorem li_rung_13 (hlo : ((110286941967 / 25000000000) : ℝ) ≤ (taylorCoeff riemannXi 13).re) : 0 ≤ (taylorCoeff riemannXi 13).re :=
  le_trans (by norm_num : (0:ℝ) ≤ (110286941967 / 25000000000)) hlo

-- li_rung_14: Li-criterion rung n=14 — 0 ≤ (taylorCoeff riemannXi 14).re, witnessed by the certified lower bound lo=252253968601/50000000000.
-- Trust seam: hlo (the Arb enclosure of ξ's Taylor coefficient) is a HYPOTHESIS.
-- Feeds LiCriterion.li_criterion_rh_iff (RH ⟺ ∀ n, 0 ≤ this); a finite rung, NOT RH.
theorem li_rung_14 (hlo : ((252253968601 / 50000000000) : ℝ) ≤ (taylorCoeff riemannXi 14).re) : 0 ≤ (taylorCoeff riemannXi 14).re :=
  le_trans (by norm_num : (0:ℝ) ≤ (252253968601 / 50000000000)) hlo

-- li_rung_15: Li-criterion rung n=15 — 0 ≤ (taylorCoeff riemannXi 15).re, witnessed by the certified lower bound lo=285855412443/50000000000.
-- Trust seam: hlo (the Arb enclosure of ξ's Taylor coefficient) is a HYPOTHESIS.
-- Feeds LiCriterion.li_criterion_rh_iff (RH ⟺ ∀ n, 0 ≤ this); a finite rung, NOT RH.
theorem li_rung_15 (hlo : ((285855412443 / 50000000000) : ℝ) ≤ (taylorCoeff riemannXi 15).re) : 0 ≤ (taylorCoeff riemannXi 15).re :=
  le_trans (by norm_num : (0:ℝ) ≤ (285855412443 / 50000000000)) hlo

-- li_rung_16: Li-criterion rung n=16 — 0 ≤ (taylorCoeff riemannXi 16).re, witnessed by the certified lower bound lo=642658287211/100000000000.
-- Trust seam: hlo (the Arb enclosure of ξ's Taylor coefficient) is a HYPOTHESIS.
-- Feeds LiCriterion.li_criterion_rh_iff (RH ⟺ ∀ n, 0 ≤ this); a finite rung, NOT RH.
theorem li_rung_16 (hlo : ((642658287211 / 100000000000) : ℝ) ≤ (taylorCoeff riemannXi 16).re) : 0 ≤ (taylorCoeff riemannXi 16).re :=
  le_trans (by norm_num : (0:ℝ) ≤ (642658287211 / 100000000000)) hlo

-- li_rung_17: Li-criterion rung n=17 — 0 ≤ (taylorCoeff riemannXi 17).re, witnessed by the certified lower bound lo=717248093829/100000000000.
-- Trust seam: hlo (the Arb enclosure of ξ's Taylor coefficient) is a HYPOTHESIS.
-- Feeds LiCriterion.li_criterion_rh_iff (RH ⟺ ∀ n, 0 ≤ this); a finite rung, NOT RH.
theorem li_rung_17 (hlo : ((717248093829 / 100000000000) : ℝ) ≤ (taylorCoeff riemannXi 17).re) : 0 ≤ (taylorCoeff riemannXi 17).re :=
  le_trans (by norm_num : (0:ℝ) ≤ (717248093829 / 100000000000)) hlo

-- li_rung_18: Li-criterion rung n=18 — 0 ≤ (taylorCoeff riemannXi 18).re, witnessed by the certified lower bound lo=795374309431/100000000000.
-- Trust seam: hlo (the Arb enclosure of ξ's Taylor coefficient) is a HYPOTHESIS.
-- Feeds LiCriterion.li_criterion_rh_iff (RH ⟺ ∀ n, 0 ≤ this); a finite rung, NOT RH.
theorem li_rung_18 (hlo : ((795374309431 / 100000000000) : ℝ) ≤ (taylorCoeff riemannXi 18).re) : 0 ≤ (taylorCoeff riemannXi 18).re :=
  le_trans (by norm_num : (0:ℝ) ≤ (795374309431 / 100000000000)) hlo

-- li_rung_19: Li-criterion rung n=19 — 0 ≤ (taylorCoeff riemannXi 19).re, witnessed by the certified lower bound lo=876927687209/100000000000.
-- Trust seam: hlo (the Arb enclosure of ξ's Taylor coefficient) is a HYPOTHESIS.
-- Feeds LiCriterion.li_criterion_rh_iff (RH ⟺ ∀ n, 0 ≤ this); a finite rung, NOT RH.
theorem li_rung_19 (hlo : ((876927687209 / 100000000000) : ℝ) ≤ (taylorCoeff riemannXi 19).re) : 0 ≤ (taylorCoeff riemannXi 19).re :=
  le_trans (by norm_num : (0:ℝ) ≤ (876927687209 / 100000000000)) hlo

end LiPositivity
