/-
  Probes.MMWeilGramCertSamples -- COMPILE SAMPLES of the two D2 certificate tools built for
  MM_weil_gram_trace: telperion/src/telperion/emit_weil_form_enclosure.py (kind
  weil_form_enclosure) and emit_interval_gram_inertia.py (kind interval_gram_inertia).

  Every theorem below was EMITTED, not hand-written; the generator is recorded in the design
  memo telperion/docs/MM_mm-d2-weil-gram-trace_DESIGN_2026-09-18.md section 8, and the script
  that produced this file is Probes/regen_samples.py next to it.  The numbers are
  ILLUSTRATIVE (hand-chosen intervals), NOT Weil-form data of any test family: the point of the
  file is that the emitted Lean shapes elaborate and their tactics close at the mirrormere pin
  (leanprover/lean4:v4.32.0).  Outside defaultTargets, no sorry, no RH content.
  conjecture1_proved = False.
-/
import Mathlib

-- sample_weil_form_01_re_fold: the PRIME-SIDE FOLD of the Weil-form value '0,1:re'.
-- supp f subset [-R, R] with R = 3/2, so primeSide f is the FINITE sum over the prime powers n in [2, 3, 4]
-- (Lambda(0) = Lambda(1) = 0).  Each term interval encloses Lambda(n)/sqrt n * (f (log n) + f (-log n)) (Arb, python-flint -- the trust seam);
-- the kernel re-does the interval ADDITION exactly in the rationals.  A corrupted endpoint is kernel-rejected.  conjecture1_proved = False.
theorem sample_weil_form_01_re_fold : ((7 / 40) : ℝ) = (1 / 10) + (1 / 20) + (1 / 40) ∧ ((1 / 5) : ℝ) = (11 / 100) + (3 / 50) + (3 / 100) := by
  constructor <;> norm_num

-- sample_weil_form_01_re: the ENTRY ENCLOSURE for '0,1:re'.  For EVERY real arch in the
-- certified archimedean interval [11/10, 6/5] (the pole terms,
-- the -f 0 * log pi term and the digamma integral, enclosed as ONE Arb interval --
-- the trust seam) and EVERY real prime in the folded prime interval
-- [7/40, 1/5], the Weil-form value arch - prime lies in
-- [9/10, 41/40] (width 1/8).  Pure interval arithmetic; the
-- identification of arch - prime with a Weil-Gram entry is the Lean node
-- MM_weil_gram_trace, NOT this certificate.  conjecture1_proved = False.
theorem sample_weil_form_01_re (arch prime : ℝ)
    (harchLo : ((11 / 10) : ℝ) ≤ arch) (harchHi : arch ≤ ((6 / 5) : ℝ))
    (hprimeLo : ((7 / 40) : ℝ) ≤ prime) (hprimeHi : prime ≤ ((1 / 5) : ℝ)) :
    ((9 / 10) : ℝ) ≤ arch - prime ∧ arch - prime ≤ ((41 / 40) : ℝ) := by
  constructor <;> linarith

-- sample_gram_negative_dir: CERTIFIED NEGATIVE DIRECTION of the enclosed Hermitian matrix 'illustrative 3x3, witness (1, i, 1+i)' (k = 3).
-- Witness x = ((1 + 0 i), (0 + 1 i), (1 + 1 i)).  For a Hermitian A with A i i = a_ii (real), A i j = a_ij + i b_ij (i < j)
-- and A j i = conj (A i j), RHLinalg.hermForm A x is exactly the rational linear functional below
-- (diagonal coefficients |x i|^2, off-diagonal 2 Re(conj (x i) * x j) and -2 Im(conj (x i) * x j)).
-- Every matrix in the certified entry box makes it <= -29/10 < 0, so EVERY such matrix has a negative
-- direction: 1 <= defect, via NegativeWitness.ofNegDir + offline_pairs_le_defect (MM_offline_pairs_le_defect).
-- The entry intervals are Arb (python-flint) enclosures of Weil-form values (emit_weil_form_enclosure) --
-- the documented trust seam; the kernel re-does the interval maximisation.  On genuine zeta data this
-- certificate is the FALSIFIABILITY face and is not expected to fire.  conjecture1_proved = False.
set_option linter.unusedVariables false in
theorem sample_gram_negative_dir (a00 a11 a22 a01 b01 a02 b02 a12 b12 : ℝ)
    (ha00lo : ((-1) : ℝ) ≤ a00) (ha00hi : a00 ≤ ((-(1 / 2)) : ℝ))
    (ha11lo : ((-1) : ℝ) ≤ a11) (ha11hi : a11 ≤ ((-(1 / 2)) : ℝ))
    (ha22lo : ((-2) : ℝ) ≤ a22) (ha22hi : a22 ≤ ((-1) : ℝ))
    (ha01lo : ((-(1 / 100)) : ℝ) ≤ a01) (ha01hi : a01 ≤ ((1 / 100) : ℝ))
    (hb01lo : ((-(1 / 100)) : ℝ) ≤ b01) (hb01hi : b01 ≤ ((1 / 100) : ℝ))
    (ha02lo : ((-(1 / 100)) : ℝ) ≤ a02) (ha02hi : a02 ≤ ((1 / 100) : ℝ))
    (hb02lo : ((-(1 / 100)) : ℝ) ≤ b02) (hb02hi : b02 ≤ ((1 / 100) : ℝ))
    (ha12lo : ((-(1 / 100)) : ℝ) ≤ a12) (ha12hi : a12 ≤ ((1 / 100) : ℝ))
    (hb12lo : ((-(1 / 100)) : ℝ) ≤ b12) (hb12hi : b12 ≤ ((1 / 100) : ℝ)) :
    1 * a00 + 1 * a11 + 2 * a22 + (-2) * b01 + 2 * a02 + (-2) * b02 + 2 * a12 + 2 * b12 ≤ (-(29 / 10)) := by
  linarith

-- sample_gram_dominance: CERTIFIED STRICT DIAGONAL DOMINANCE of the enclosed Hermitian matrix 'illustrative 3x3, dominance' (k = 3).
-- Per off-diagonal entry a modulus bound |A i j|^2 <= m_ij^2 valid on the whole entry box, and per row the
-- constant inequality (sum over j != i of m_ij) < (certified lower bound for a_ii); row slacks 79289/500000, 79289/500000, 79289/500000.
-- READING (not emitted as a claim): strict Hermitian diagonal dominance with positive diagonal is positive
-- definiteness (Gershgorin), so this enclosed family has defect 0 and posIndex 3.  The dominance -> PosDef
-- lemma belongs to the consuming island's RHLinalg prelude and is NOT asserted here.  defect = 0 for ONE test
-- family is DATA; for EVERY test family it is Weil's criterion and therefore RH, which is NOT claimed.
-- Entry intervals are Arb enclosures (emit_weil_form_enclosure) -- the trust seam.  conjecture1_proved = False.
set_option linter.unusedVariables false in
theorem sample_gram_dominance (a00 a11 a22 a01 b01 a02 b02 a12 b12 : ℝ)
    (ha00lo : ((3 / 10) : ℝ) ≤ a00) (ha00hi : a00 ≤ ((2 / 5) : ℝ))
    (ha11lo : ((3 / 10) : ℝ) ≤ a11) (ha11hi : a11 ≤ ((2 / 5) : ℝ))
    (ha22lo : ((3 / 10) : ℝ) ≤ a22) (ha22hi : a22 ≤ ((2 / 5) : ℝ))
    (ha01lo : ((-(1 / 20)) : ℝ) ≤ a01) (ha01hi : a01 ≤ ((1 / 20) : ℝ))
    (hb01lo : ((-(1 / 20)) : ℝ) ≤ b01) (hb01hi : b01 ≤ ((1 / 20) : ℝ))
    (ha02lo : ((-(1 / 20)) : ℝ) ≤ a02) (ha02hi : a02 ≤ ((1 / 20) : ℝ))
    (hb02lo : ((-(1 / 20)) : ℝ) ≤ b02) (hb02hi : b02 ≤ ((1 / 20) : ℝ))
    (ha12lo : ((-(1 / 20)) : ℝ) ≤ a12) (ha12hi : a12 ≤ ((1 / 20) : ℝ))
    (hb12lo : ((-(1 / 20)) : ℝ) ≤ b12) (hb12hi : b12 ≤ ((1 / 20) : ℝ)) :
    a01 ^ 2 + b01 ^ 2 ≤ (5000045521 / 1000000000000) ∧
      a02 ^ 2 + b02 ^ 2 ≤ (5000045521 / 1000000000000) ∧
      a12 ^ 2 + b12 ^ 2 ≤ (5000045521 / 1000000000000) ∧
      ((70711 / 500000) : ℝ) < (3 / 10) ∧
      ((70711 / 500000) : ℝ) < (3 / 10) ∧
      ((70711 / 500000) : ℝ) < (3 / 10) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals nlinarith [ha01lo, ha01hi, hb01lo, hb01hi, ha02lo, ha02hi, hb02lo, hb02hi, ha12lo, ha12hi, hb12lo, hb12hi]

