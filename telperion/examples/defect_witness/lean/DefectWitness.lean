/- telperion 0.1.6 | family DefectWitness | input-hash ba6dc1c2bc039bfa
   6 theorems, 2 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace DefectWitness

/-- The defect functional `q(d) = FLOOR − d² = −d²` (test vector `w = (0,1)`, FLOOR = 0):
    on the pure off-line channel it reads the amplification excess `d`. -/
def defect_delta_tenth_defectFunctional (d : ℝ) : ℝ := -(d ^ 2)

/-- **On-line witness** (defect_delta_tenth): the honest (all on-line) configuration's defect
    functional is 0, consistently inside `[0, 0]` (no negative direction). -/
theorem defect_delta_tenth_online :
    defect_delta_tenth_defectFunctional 0 = 0 ∧ ((0) : ℝ) ≤ defect_delta_tenth_defectFunctional 0 ∧ defect_delta_tenth_defectFunctional 0 ≤ (0) := by
  unfold defect_delta_tenth_defectFunctional
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **Off-line witness** (defect_delta_tenth): for the synthetic off-line pair with amplification
    excess `d ∈ [(1 / 10), (11 / 100)]` (`d > 0`), the defect functional is bracketed strictly
    negative, `q(d) ∈ [(-(121 / 10000)), (-(1 / 100))]` with `(-(1 / 100)) < 0` — the measured
    signature-(1,1) leakage. -/
theorem defect_delta_tenth_offline (d : ℝ) (hlo : (((1 / 10)) : ℝ) ≤ d) (hhi : d ≤ ((11 / 100))) :
    (((-(121 / 10000))) : ℝ) ≤ defect_delta_tenth_defectFunctional d ∧ defect_delta_tenth_defectFunctional d ≤ ((-(1 / 100))) := by
  have hdpos : (0 : ℝ) < d := lt_of_lt_of_le (by norm_num) hlo
  unfold defect_delta_tenth_defectFunctional
  constructor
  · nlinarith [hhi, hlo, hdpos]
  · nlinarith [hlo, hdpos]

/-- **Leakage gap** (defect_delta_tenth): the off-line functional's upper bound `(-(1 / 100))` is strictly
    below the on-line value `q(0) = 0`.  The defect is a kernel-observable separation, not
    a rounding artifact. -/
theorem defect_delta_tenth_leakage_gap (d : ℝ) (hlo : (((1 / 10)) : ℝ) ≤ d) (hhi : d ≤ ((11 / 100))) :
    defect_delta_tenth_defectFunctional d ≤ ((-(1 / 100))) ∧ (((-(1 / 100))) : ℝ) < defect_delta_tenth_defectFunctional 0 := by
  refine ⟨(defect_delta_tenth_offline d hlo hhi).2, ?_⟩
  have h0 : defect_delta_tenth_defectFunctional 0 = 0 := by unfold defect_delta_tenth_defectFunctional; norm_num
  rw [h0]; norm_num

/-- The defect functional `q(d) = FLOOR − d² = −d²` (test vector `w = (0,1)`, FLOOR = 0):
    on the pure off-line channel it reads the amplification excess `d`. -/
def defect_delta_fifth_defectFunctional (d : ℝ) : ℝ := -(d ^ 2)

/-- **On-line witness** (defect_delta_fifth): the honest (all on-line) configuration's defect
    functional is 0, consistently inside `[0, 0]` (no negative direction). -/
theorem defect_delta_fifth_online :
    defect_delta_fifth_defectFunctional 0 = 0 ∧ ((0) : ℝ) ≤ defect_delta_fifth_defectFunctional 0 ∧ defect_delta_fifth_defectFunctional 0 ≤ (0) := by
  unfold defect_delta_fifth_defectFunctional
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **Off-line witness** (defect_delta_fifth): for the synthetic off-line pair with amplification
    excess `d ∈ [(1 / 5), (21 / 100)]` (`d > 0`), the defect functional is bracketed strictly
    negative, `q(d) ∈ [(-(441 / 10000)), (-(1 / 25))]` with `(-(1 / 25)) < 0` — the measured
    signature-(1,1) leakage. -/
theorem defect_delta_fifth_offline (d : ℝ) (hlo : (((1 / 5)) : ℝ) ≤ d) (hhi : d ≤ ((21 / 100))) :
    (((-(441 / 10000))) : ℝ) ≤ defect_delta_fifth_defectFunctional d ∧ defect_delta_fifth_defectFunctional d ≤ ((-(1 / 25))) := by
  have hdpos : (0 : ℝ) < d := lt_of_lt_of_le (by norm_num) hlo
  unfold defect_delta_fifth_defectFunctional
  constructor
  · nlinarith [hhi, hlo, hdpos]
  · nlinarith [hlo, hdpos]

/-- **Leakage gap** (defect_delta_fifth): the off-line functional's upper bound `(-(1 / 25))` is strictly
    below the on-line value `q(0) = 0`.  The defect is a kernel-observable separation, not
    a rounding artifact. -/
theorem defect_delta_fifth_leakage_gap (d : ℝ) (hlo : (((1 / 5)) : ℝ) ≤ d) (hhi : d ≤ ((21 / 100))) :
    defect_delta_fifth_defectFunctional d ≤ ((-(1 / 25))) ∧ (((-(1 / 25))) : ℝ) < defect_delta_fifth_defectFunctional 0 := by
  refine ⟨(defect_delta_fifth_offline d hlo hhi).2, ?_⟩
  have h0 : defect_delta_fifth_defectFunctional 0 = 0 := by unfold defect_delta_fifth_defectFunctional; norm_num
  rw [h0]; norm_num

end DefectWitness
