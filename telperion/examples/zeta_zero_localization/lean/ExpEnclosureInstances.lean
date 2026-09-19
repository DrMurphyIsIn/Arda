/- telperion 0.1.6 | family ExpEnclosureInstances | input-hash 83a662d62bb41760
   10 theorems, 4 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib
import BraggDefect

namespace ExpEnclosureInstances

/-- `exp_tenth_bracket` -- a certified RATIONAL ENCLOSURE of `Real.exp (1/10)`.
    Order-14 `Real.exp_bound` box `[S - r, S + r]` (exact rationals,
    S = sum_(m < 14) x^m/m!, r = |x|^14 * (14+1)/(14! * 14)),
    which lies inside the claimed bracket with slack (75976562500000000119119/4767562800000000000000000000000000000000000000, 198025173611111118808189/119189070000000000000000000000000000000000000000) >= 0;
    box = [26977135394095642634038549/24409921536000000000000000, 5395427078819128526807711/4881984307200000000000000].  The order is the LEAST one whose box fits -- the
    generator REFUSES a bracket the box does not imply rather than widening it.
    A finite arithmetic fact about a transcendental constant at one rational
    point; nothing about RH.  conjecture1_proved = False. -/

theorem exp_tenth_bracket : (((442068367230259049924676660787771898883 / 400000000000000000000000000000000000000)) : ℝ) ≤ Real.exp ((1 / 10)) ∧ Real.exp ((1 / 10)) ≤ (((11051709180756476248117094953514706601127 / 10000000000000000000000000000000000000000)) : ℝ) := by
  have hx : |(((1 / 10)) : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num
  have hb := Real.exp_bound hx (n := 14) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hb
  rw [abs_le] at hb
  obtain ⟨h1, h2⟩ := hb
  constructor
  · norm_num [Nat.factorial] at h1 ⊢; linarith
  · norm_num [Nat.factorial] at h2 ⊢; linarith

/-- `deficit_tenth_bracket` -- a certified RATIONAL ENCLOSURE of `Real.exp (1/10) + Real.exp (-(1/10)) - 2`.
    Order-14 `Real.exp_bound` box `[S - r, S + r]` (exact rationals,
    S = sum_(m < 14) x^m/m!, r = |x|^14 * (14+1)/(14! * 14)),
    which lies inside the claimed bracket with slack (899183891901596078882526032824609234226561405642718335619647113/52689717566593052019606631944444444444447523275600000000000000000000000000000000000000, 23782320894641569211942655988551850468682727291129747405465239/1596658108078577333927447916666666666666630570000000000000000000000000000000000000000) >= 0;
    box = [122151349595123520722957/12204960768000000000000000, 11104668145011229156633/1109541888000000000000000].  The order is the LEAST one whose box fits -- the
    generator REFUSES a bracket the box does not imply rather than widening it.
    A finite arithmetic fact about a transcendental constant at one rational
    point; nothing about RH.  conjecture1_proved = False. -/

-- the `exp (1/10)` face of deficit_tenth_bracket (its own exact order-14 box)
theorem deficit_tenth_bracket_pos : (((26977135394095642634038549 / 24409921536000000000000000)) : ℝ) ≤ Real.exp ((1 / 10)) ∧ Real.exp ((1 / 10)) ≤ (((5395427078819128526807711 / 4881984307200000000000000)) : ℝ) := by
  have hx : |(((1 / 10)) : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num
  have hb := Real.exp_bound hx (n := 14) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hb
  rw [abs_le] at hb
  obtain ⟨h1, h2⟩ := hb
  constructor
  · norm_num [Nat.factorial] at h1 ⊢; linarith
  · norm_num [Nat.factorial] at h2 ⊢; linarith

-- the `exp (-(1/10))` face of deficit_tenth_bracket (same order, same remainder)
theorem deficit_tenth_bracket_neg : (((1472467358472973627160491 / 1627328102400000000000000)) : ℝ) ≤ Real.exp (-((1 / 10))) ∧ Real.exp (-((1 / 10))) ≤ (((7362336792364868135802457 / 8136640512000000000000000)) : ℝ) := by
  have hx : |(((1 / 10)) : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num
  have hx' : |((-((1 / 10))) : ℝ)| ≤ 1 := by rwa [abs_neg]
  have hb := Real.exp_bound hx' (n := 14) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hb
  rw [abs_le] at hb
  obtain ⟨h1, h2⟩ := hb
  constructor
  · norm_num [Nat.factorial] at h1 ⊢; linarith
  · norm_num [Nat.factorial] at h2 ⊢; linarith

theorem deficit_tenth_bracket : (((44243688035498337190547890814412959087189025996450853896963629856431657841141 / 4420683672302590499246837981405882640450800000000000000000000000000000000000000)) : ℝ) ≤ Real.exp ((1 / 10)) + Real.exp (-((1 / 10))) - 2 ∧
    Real.exp ((1 / 10)) + Real.exp (-((1 / 10))) - 2 ≤ (((44243688035498337190690637870740262328789025996450853896963629856431657841141 / 4420683672302590499246766607877718988830000000000000000000000000000000000000000)) : ℝ) := by
  constructor <;> linarith [deficit_tenth_bracket_pos.1, deficit_tenth_bracket_pos.2, deficit_tenth_bracket_neg.1, deficit_tenth_bracket_neg.2]

/-- `deficit_fifth_bracket` -- a certified RATIONAL ENCLOSURE of `Real.exp (1/5) + Real.exp (-(1/5)) - 2`.
    Order-16 `Real.exp_bound` box `[S - r, S + r]` (exact rationals,
    S = sum_(m < 16) x^m/m!, r = |x|^16 * (16+1)/(16! * 16)),
    which lies inside the claimed bracket with slack (31727/5108103000000000000000000000, 4722833/51081030000000000000000000000) >= 0;
    box = [1025030545780681876895983/25540515000000000000000000, 1025030545780681876896017/25540515000000000000000000].  The order is the LEAST one whose box fits -- the
    generator REFUSES a bracket the box does not imply rather than widening it.
    A finite arithmetic fact about a transcendental constant at one rational
    point; nothing about RH.  conjecture1_proved = False. -/

-- the `exp (1/5)` face of deficit_fifth_bracket (its own exact order-16 box)
theorem deficit_fifth_bracket_pos : (((6932278992406931121290807 / 5675670000000000000000000)) : ℝ) ≤ Real.exp ((1 / 5)) ∧ Real.exp ((1 / 5)) ≤ (((62390510931662380091617297 / 51081030000000000000000000)) : ℝ) := by
  have hx : |(((1 / 5)) : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num
  have hb := Real.exp_bound hx (n := 16) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hb
  rw [abs_le] at hb
  obtain ⟨h1, h2⟩ := hb
  constructor
  · norm_num [Nat.factorial] at h1 ⊢; linarith
  · norm_num [Nat.factorial] at h2 ⊢; linarith

-- the `exp (-(1/5))` face of deficit_fifth_bracket (same order, same remainder)
theorem deficit_fifth_bracket_neg : (((853502248161203748207647 / 1042470000000000000000000)) : ℝ) ≤ Real.exp (-((1 / 5))) ∧ Real.exp (-((1 / 5))) ≤ (((4646845573322109295797193 / 5675670000000000000000000)) : ℝ) := by
  have hx : |(((1 / 5)) : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num
  have hx' : |((-((1 / 5))) : ℝ)| ≤ 1 := by rwa [abs_neg]
  have hb := Real.exp_bound hx' (n := 16) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hb
  rw [abs_le] at hb
  obtain ⟨h1, h2⟩ := hb
  constructor
  · norm_num [Nat.factorial] at h1 ⊢; linarith
  · norm_num [Nat.factorial] at h2 ⊢; linarith

theorem deficit_fifth_bracket : (((40133511238151692591 / 1000000000000000000000)) : ℝ) ≤ Real.exp ((1 / 5)) + Real.exp (-((1 / 5))) - 2 ∧
    Real.exp ((1 / 5)) + Real.exp (-((1 / 5))) - 2 ≤ (((401335112381516925911 / 10000000000000000000000)) : ℝ) := by
  constructor <;> linarith [deficit_fifth_bracket_pos.1, deficit_fifth_bracket_pos.2, deficit_fifth_bracket_neg.1, deficit_fifth_bracket_neg.2]

/-- `cosh_zoodh_bracket` -- a certified RATIONAL ENCLOSURE of `Real.cosh (21487557/100000000)`.
    Order-6 `Real.exp_bound` box `[S - r, S + r]` (exact rationals,
    S = sum_(m < 6) x^m/m!, r = |x|^6 * (6+1)/(6! * 6)),
    which lies inside the claimed bracket with slack (137747013258117884884353491/160000000000000000000000000000000000000000000000000, 99559546458117884884353491/160000000000000000000000000000000000000000000000000) >= 0;
    box = [163707907383974683468965577747013258117884884353491/160000000000000000000000000000000000000000000000000, 163707958421137299354192860440453541882115115646509/160000000000000000000000000000000000000000000000000].  The order is the LEAST one whose box fits -- the
    generator REFUSES a bracket the box does not imply rather than widening it.
    A finite arithmetic fact about a transcendental constant at one rational
    point; nothing about RH.  conjecture1_proved = False. -/

-- the `exp (21487557/100000000)` face of cosh_zoodh_bracket (its own exact order-6 box)
theorem cosh_zoodh_bracket_pos : (((198353172806144997105636607607597427668492484353491 / 160000000000000000000000000000000000000000000000000)) : ℝ) ≤ Real.exp ((21487557 / 100000000)) ∧ Real.exp ((21487557 / 100000000)) ≤ (((198353223843307612990863890301037711432722715646509 / 160000000000000000000000000000000000000000000000000)) : ℝ) := by
  have hx : |(((21487557 / 100000000)) : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num
  have hb := Real.exp_bound hx (n := 6) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hb
  rw [abs_le] at hb
  obtain ⟨h1, h2⟩ := hb
  constructor
  · norm_num [Nat.factorial] at h1 ⊢; linarith
  · norm_num [Nat.factorial] at h2 ⊢; linarith

-- the `exp (-(21487557/100000000))` face of cosh_zoodh_bracket (same order, same remainder)
theorem cosh_zoodh_bracket_neg : (((129062641961804369832294547886429088567277284353491 / 160000000000000000000000000000000000000000000000000)) : ℝ) ≤ Real.exp (-((21487557 / 100000000))) ∧ Real.exp (-((21487557 / 100000000))) ≤ (((129062692998966985717521830579869372331507515646509 / 160000000000000000000000000000000000000000000000000)) : ℝ) := by
  have hx : |(((21487557 / 100000000)) : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num
  have hx' : |((-((21487557 / 100000000))) : ℝ)| ≤ 1 := by rwa [abs_neg]
  have hb := Real.exp_bound hx' (n := 6) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hb
  rw [abs_le] at hb
  obtain ⟨h1, h2⟩ := hb
  constructor
  · norm_num [Nat.factorial] at h1 ⊢; linarith
  · norm_num [Nat.factorial] at h2 ⊢; linarith

theorem cosh_zoodh_bracket : (((511587210574920885840517 / 500000000000000000000000)) : ℝ) ≤ Real.cosh ((21487557 / 100000000)) ∧ Real.cosh ((21487557 / 100000000)) ≤ (((511587370066054060481853 / 500000000000000000000000)) : ℝ) := by
  rw [Real.cosh_eq]
  constructor <;> linarith [cosh_zoodh_bracket_pos.1, cosh_zoodh_bracket_pos.2, cosh_zoodh_bracket_neg.1, cosh_zoodh_bracket_neg.2]

/-- `exp_tenth_bracket_defs` -- the SAME certified bracket in BraggDefect's own vocabulary:
    `expLo`/`expHi` are by definition the two literals `exp_tenth_bracket` brackets between,
    so this is a pure unfolding.  It is the exact shape of the `hexp` hypothesis that
    `BraggDefect.bragg_defect_witness` (and the MIRRORMERE node `MM_bragg_defect_witness`)
    carries as an Arb input.  conjecture1_proved = False. -/
theorem exp_tenth_bracket_defs :
    BraggDefect.expLo ≤ Real.exp (1 / 10) ∧ Real.exp (1 / 10) ≤ BraggDefect.expHi := by
  unfold BraggDefect.expLo BraggDefect.expHi
  exact exp_tenth_bracket

/-- **`bragg_defect_witness_unconditional`** -- the MIRRORMERE defect witness with its Arb
    exponential-enclosure hypothesis DISCHARGED in the kernel.  Identical conclusion to
    `BraggDefect.bragg_defect_witness`; the `hexp` binder is gone, supplied by
    `exp_tenth_bracket_defs` (order-14 `Real.exp_bound`).

    SCOPE, unchanged: this is the finite synthetic-pair diffraction experiment of
    `BraggDefect.lean` -- the on-line configuration's defect functional is exactly 0 and the
    one-off-line-pair configuration's is bracketed strictly below 0.  Discharging a NUMERIC
    hypothesis makes the witness unconditional; it does not enlarge what the witness says, and
    the experiment's other trust seams (the BraggH100 Arb sign boxes, the band `hLine`) are
    untouched.  Nothing here is about RH.  conjecture1_proved = False. -/
theorem bragg_defect_witness_unconditional :
    BraggDefect.defectFunctional 0 = 0 ∧
    ((-1957503930982498711627558116252003079150110082803036995985602456729126067929069837779873677055641334915004924707647824293913235373458273903210508792181881 / 19542444130562717342736579894714125276139669165907166175656490622972757664768900000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ BraggDefect.defectFunctional BraggDefect.excess ∧
      BraggDefect.defectFunctional BraggDefect.excess ≤ (-1957503930982498711614926803795741251867682177931660778058090203284392257792384397626586656512971699612677910422316624293913235373458273903210508792181881 / 19542444130562717342737210934295300643770643047158621178046789521488913388427220640000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) :=
  BraggDefect.bragg_defect_witness exp_tenth_bracket_defs

/-- The hypothesis-carrying form, kept so the MIRRORMERE grant gate's syntactic match against
    `Statements/MM_bragg_defect_witness.lean` still finds its statement.  The hypothesis is now
    inert -- the conclusion is `bragg_defect_witness_unconditional`. -/
theorem bragg_defect_witness_hyp_form
    (_hexp : BraggDefect.expLo ≤ Real.exp (1 / 10) ∧ Real.exp (1 / 10) ≤ BraggDefect.expHi) :
    BraggDefect.defectFunctional 0 = 0 ∧
    ((-1957503930982498711627558116252003079150110082803036995985602456729126067929069837779873677055641334915004924707647824293913235373458273903210508792181881 / 19542444130562717342736579894714125276139669165907166175656490622972757664768900000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ BraggDefect.defectFunctional BraggDefect.excess ∧
      BraggDefect.defectFunctional BraggDefect.excess ≤ (-1957503930982498711614926803795741251867682177931660778058090203284392257792384397626586656512971699612677910422316624293913235373458273903210508792181881 / 19542444130562717342737210934295300643770643047158621178046789521488913388427220640000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) :=
  bragg_defect_witness_unconditional

-- STATEMENT GATE (kernel-enforced): the node statement of MM_bragg_defect_witness, written
-- exactly as `Statements/MM_bragg_defect_witness.lean` writes it (under `open BraggDefect`),
-- is inhabited by the hypothesis-carrying form.  A drift in either statement fails the build.
open BraggDefect in
example (hexp : expLo ≤ Real.exp (1 / 10) ∧ Real.exp (1 / 10) ≤ expHi) :
    defectFunctional 0 = 0 ∧
    ((-1957503930982498711627558116252003079150110082803036995985602456729126067929069837779873677055641334915004924707647824293913235373458273903210508792181881 / 19542444130562717342736579894714125276139669165907166175656490622972757664768900000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ defectFunctional excess ∧
      defectFunctional excess ≤ (-1957503930982498711614926803795741251867682177931660778058090203284392257792384397626586656512971699612677910422316624293913235373458273903210508792181881 / 19542444130562717342737210934295300643770643047158621178046789521488913388427220640000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) :=
  bragg_defect_witness_hyp_form hexp

end ExpEnclosureInstances
