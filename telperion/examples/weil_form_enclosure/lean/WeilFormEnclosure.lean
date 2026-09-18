/- telperion 0.1.6 | family WeilFormEnclosure | input-hash 31ebec3f4cd01e0c
   2 theorems, 2 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace WeilFormEnclosure

-- Instances the certificate REFUSED (recorded, not hidden):
--   REFUSED: gaussian a=1/2, omega=-3/10 (off the zero comb) -- enclosure [-51/100000000000000, 51/100000000000000]: enclosure straddles zero: sign of the Weil form UNDECIDED at this precision -- refused

-- weil_form_neg_refutes_rh: the falsifiability face of the Weil-form instrument.
-- GIVEN Weil's criterion in the forward direction (hcrit, classical, UNDISCHARGED and
-- not in Mathlib), a certified strictly negative Weil form at an admissible test
-- function refutes RH.  The instrument is therefore an experiment that could have
-- falsified; it does not.  conjecture1_proved = False.
theorem weil_form_neg_refutes_rh
    (Wre : (ℝ → ℂ) → ℝ) (IsTest : (ℝ → ℂ) → Prop) (g : ℝ → ℂ) (W : ℝ)
    (hcrit : RiemannHypothesis → ∀ f : ℝ → ℂ, IsTest f → 0 ≤ Wre f)
    (hg : IsTest g) (heval : Wre g = W) (hneg : W < 0) :
    ¬ RiemannHypothesis := by
  intro hrh
  exact absurd (heval ▸ hcrit hrh g hg) (not_le.mpr hneg)

-- weil_form_instance_of_enclosure: a certified positive enclosure at ONE admissible
-- test function gives the membership goal's conclusion AT THAT g -- and nothing more.
-- The goal MM_zeta_comb_membership quantifies over the entire class; no finite family
-- of instances approaches that quantifier (roadmap section 1).  conjecture1_proved = False.
theorem weil_form_instance_of_enclosure
    (Wre : (ℝ → ℂ) → ℝ) (g : ℝ → ℂ) (lo W : ℝ)
    (heval : Wre g = W) (hpos : 0 < lo) (hlo : lo ≤ W) :
    0 ≤ Wre g := by
  rw [heval]
  exact le_trans hpos.le hlo

-- weil_form_zero1: certified enclosure of the Weil form W = Re (weilForm (autocorr g))
-- at the test function gaussian a=1/2, omega=-14.1347 (centred on the first zeta ordinate): 1963509301/1250000000 <= W <= 15708074409/10000000000 -- zero-side sum over the first 40 zero pairs = 1.5708074408343442739.
-- Trust seam: lo/hi are Arb (python-flint) enclosures produced by
-- telperion.weil_gauss (closed forms anchored against the DEFINING integrals of
-- WeilExplicit.autocorr / weilKernel, and cross-checked against the independent
-- zero-side reading of the same functional).  A forged enclosure falsifies the
-- hypotheses and leaves this implication kernel-valid.
-- This is a FINITE value certificate at ONE test function.  It proves NOTHING
-- about RH: the registry goal MM_zeta_comb_membership quantifies over the whole
-- class and is RH-equivalent (Weil 1952 / Bombieri 2000).
-- conjecture1_proved = False.
theorem weil_form_zero1 (W : ℝ) (hlo : ((1963509301 / 1250000000) : ℝ) ≤ W) (hhi : W ≤ ((15708074409 / 10000000000) : ℝ)) :
    (0 : ℝ) < W ∧ W ≤ ((15708074409 / 10000000000) : ℝ) :=
  ⟨lt_of_lt_of_le (by norm_num) hlo, hhi⟩

-- weil_form_zero2: certified enclosure of the Weil form W = Re (weilForm (autocorr g))
-- at the test function gaussian a=1/2, omega=-21.02 (centred on the second zeta ordinate): 16001063093/10000000000 <= W <= 8000531547/5000000000 -- zero-side sum over the first 40 zero pairs = 1.6001063093683198989.
-- Trust seam: lo/hi are Arb (python-flint) enclosures produced by
-- telperion.weil_gauss (closed forms anchored against the DEFINING integrals of
-- WeilExplicit.autocorr / weilKernel, and cross-checked against the independent
-- zero-side reading of the same functional).  A forged enclosure falsifies the
-- hypotheses and leaves this implication kernel-valid.
-- This is a FINITE value certificate at ONE test function.  It proves NOTHING
-- about RH: the registry goal MM_zeta_comb_membership quantifies over the whole
-- class and is RH-equivalent (Weil 1952 / Bombieri 2000).
-- conjecture1_proved = False.
theorem weil_form_zero2 (W : ℝ) (hlo : ((16001063093 / 10000000000) : ℝ) ≤ W) (hhi : W ≤ ((8000531547 / 5000000000) : ℝ)) :
    (0 : ℝ) < W ∧ W ≤ ((8000531547 / 5000000000) : ℝ) :=
  ⟨lt_of_lt_of_le (by norm_num) hlo, hhi⟩

end WeilFormEnclosure
