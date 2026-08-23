/-
  R47 R6 interpolation-lemma sub-hub curve (I1) -- the exact cavity of a load-0 sub-hub.

  SOURCE: proof/verification/interpolation_lemma.py, `verify_I1` (exact, one-line induction).

  CONTEXT.  In the same-n domination of stars-of-hubs (R7' Stage II), a load-0 sub-hub with
  `q` level-5 cherry-bundle arms attached to the top has, exactly,
      cavity  cav = 23 / (26 q + 23)   in  (0, 23/49],
  whence its opening amplitude is the rational function `subOpen(cav) = 26 / (23 + 3 cav)`
  of its cavity alone.  This closed cavity is what lets the sign dichotomy (I2,
  `R47R6InterpSignCert`) place the supremum over all size vectors at an endpoint.

  This brick computes that cavity IN THE Branch MODEL of `Reach.lean`: the level-5 arm is
  `Branch.node 5 []` (`cav = 3/23`), the sub-hub is `Branch.node 0 (replicate q (node 5 []))`,
  and its `cav` unfolds (via `cav_eq` + `cavSum_replicate`) to `23/(26 q + 23)` for every `q`.
  Also the exact opening identity `subOpen(m) * (23 + 3 m) = 26`.  Verified against the exact
  cavity recursion in `sympy`/`Fraction`.

  HONEST SCOPE.  The exact I1 sub-hub cavity curve -- one input to the same-n interpolation
  lemma feeding Hdom.  NOT the endpoint certificates, the full lemma, nor the conjecture.
  Self-contained modulo `Reach`/`NearStar`; genuine proofs (no `sorry`, no `axiom`, no
  vacuous hypothesis).  conjecture1_proved = False.
-/
import Mathlib
import R3Cert.NearStar

namespace R3Cert

/-- The level-5 cherry-bundle arm `node 5 []` has cavity `3/23`. -/
theorem cav_fiveArm : cav (Branch.node 5 []) = 3 / 23 := by
  rw [cav_eq]; simp only [List.length_nil, cavSum, Nat.cast_zero]; norm_num

/-- **(I1) The sub-hub curve.**  A load-0 sub-hub of `q` level-5 arms has cavity
    `23 / (26 q + 23)`. -/
theorem subhub_cav (q : ℕ) :
    cav (Branch.node 0 (List.replicate q (Branch.node 5 [])))
      = 23 / (26 * (q : ℝ) + 23) := by
  rw [cav_eq, List.length_replicate, cavSum_replicate, cav_fiveArm]
  have h1 : (3 + 3 * (q : ℝ) + 4 * ((0 : ℕ) : ℝ) + 3 * ((q : ℝ) * (3 / 23))) ≠ 0 := by
    push_cast; positivity
  have h2 : (26 * (q : ℝ) + 23) ≠ 0 := by positivity
  field_simp
  ring

/-- The sub-hub opening identity `subOpen(m) * (23 + 3 m) = 26`. -/
theorem subOpen_mul (m : ℝ) (hm : (23 : ℝ) + 3 * m ≠ 0) :
    (26 / (23 + 3 * m)) * (23 + 3 * m) = 26 := by
  field_simp

/-- The sub-hub cavity is at most `23/49` (attained at `q = 1`), hence in `(0, 23/49]`. -/
theorem subhub_cav_le (q : ℕ) (hq : 1 ≤ q) :
    cav (Branch.node 0 (List.replicate q (Branch.node 5 []))) ≤ 23 / 49 := by
  rw [subhub_cav]
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  gcongr
  nlinarith [hq1]

end R3Cert
