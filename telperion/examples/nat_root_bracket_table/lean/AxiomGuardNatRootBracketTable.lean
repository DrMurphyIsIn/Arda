/-
Axiom guard for the nat-root-bracket-table island.

Run AFTER `lake build` (CI does): it prints the axiom dependencies of the NatRootBracket
transport lemmas and of every emitted bracket.  A clean run shows nothing beyond Mathlib's
three axioms `[propext, Classical.choice, Quot.sound]`; CI additionally fails the job if
`sorryAx` (or `Lean.ofReduceBool`, the native_decide axiom) appears anywhere in the output.
`decide +kernel` adds no axiom: the kernel evaluates `Decidable.decide` itself.

This file is HAND-WRITTEN (it is not emitted, so it is not part of the generate.py drift check)
and lists the capstones by name: adding an instance without adding its guard line is a visible
omission in the diff.

conjecture1_proved = False -- finite arithmetic facts about rational powers and their partial
sums; nothing here concerns zeta or class numbers.
-/
import NatRootBracketTable

-- The once-proved transport lemmas (no instance data).
#print axioms NatRootBracket.rpow_neg_div_lower
#print axioms NatRootBracket.rpow_neg_div_upper
#print axioms NatRootBracket.rpow_rat_neg_div_lower
#print axioms NatRootBracket.sum_block_lo_neg
#print axioms NatRootBracket.sum_block_hi_neg
#print axioms NatRootBracket.sum_range_chunk

-- The emitted brackets.
#print axioms NatRootBracketTable.sum_neg34_400
#print axioms NatRootBracketTable.sum_neg78_400
#print axioms NatRootBracketTable.pow_1001_pos14
#print axioms NatRootBracketTable.rat_64003_8_neg58
