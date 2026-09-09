import Mathlib

namespace BGP212

/- Exact verification of the bgp212 Appendix B slack ledger (Table 6) — the
   complete published exact-rational arithmetic-side parameter inequalities of
   "A New Bound for Small Gaps Between Primes" (Axiom Math, 2026), H1 <= 212.
   Each conjunct is one ledger row, left </= right with the paper's exact
   fractions; slacks independently re-verified pre-emission. The kernel
   re-decides all 21 comparisons. conjecture1_proved = False. -/
theorem appendixB_slack_ledger :
    (0 : ℚ) < (41 / 2500 : ℚ) ∧
    (41 / 2500 : ℚ) < (777 / 5000 : ℚ) ∧
    (0 : ℚ) < (17 / 5000 : ℚ) ∧
    (81 / 5000 : ℚ) < (41 / 2500 : ℚ) ∧
    (777 / 5000 : ℚ) < (389 / 2500 : ℚ) ∧
    (2 / 5 : ℚ) = (2 / 5 : ℚ) ∧
    (2 / 5 : ℚ) = (2 / 5 : ℚ) ∧
    (49 / 25 : ℚ) < (2 : ℚ) ∧
    (199 / 50 : ℚ) < (4 : ℚ) ∧
    (1 : ℚ) < (29 / 25 : ℚ) ∧
    (34 / 5 : ℚ) < (7 : ℚ) ∧
    (41 / 2500 : ℚ) < (279999997 / 15000000000 : ℚ) ∧
    (41 / 2500 : ℚ) < (1309999993 / 35000000000 : ℚ) ∧
    (0 : ℚ) < (69599997 / 2000000000 : ℚ) ∧
    (41 / 2500 : ℚ) < (87999999 / 5000000000 : ℚ) ∧
    (41 / 2500 : ℚ) < (82499999 / 5000000000 : ℚ) ∧
    (41 / 2500 : ℚ) < (127499999 / 5000000000 : ℚ) ∧
    (3937000001 / 5000000000 : ℚ) < (63 / 80 : ℚ) ∧
    (455 : ℚ) = (455 : ℚ) ∧
    (11 / 400000000000 : ℚ) < (109 / 1000000000000 : ℚ) ∧
    (11 / 200000000000 : ℚ) = (11 / 200000000000 : ℚ) := by norm_num

end BGP212
