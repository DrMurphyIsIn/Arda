/-
  ArchS12_Guard -- `#print axioms` for every top-level theorem of stage S12.
  Required output: exactly [propext, Classical.choice, Quot.sound] (no sorryAx, no new axioms).
  Check: `lake build ArchS12_Main && lake env lean ArchS12_Guard.lean`.
  conjecture1_proved = False.
-/
import ArchS12_Index

-- A3: the certified enumeration
#print axioms ArchS12.disjOK_eq
#print axioms ArchS12.window_sep
#print axioms ArchS12.window_unique
#print axioms ArchS12.T_phiR'
#print axioms ArchS12.ip_phiR'
#print axioms ArchS12.window_existsUnique
#print axioms ArchS12.winIdx_spec
#print axioms ArchS12.winIdx_injective
#print axioms ArchS12.exists_equiv_prefix
#print axioms ArchS12.exists_certBasis_enumeration
#print axioms ArchS12.exists_certified_prolate
