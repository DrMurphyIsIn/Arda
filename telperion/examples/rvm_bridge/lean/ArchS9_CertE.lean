/-
  ArchS9_CertE -- kernel evaluation of S9 certificate checkers (archimedean stage S9, 2026-10-11).
  `decide +kernel`: the Lean kernel reduces the Boolean checker of ArchS9_Data itself (exact
  integer / rational arithmetic, GMP-accelerated Nat); no compiled code is trusted.
  Row bounds of E = diag(aR) - B^T Theta B (40 rows).
  conjecture1_proved = False.  No `sorry`.
-/
import ArchS9_Data

namespace ArchS9.Data

set_option maxRecDepth 100000

theorem e_rows_1 : (List.range' 0 20).all eRowOK = true := by decide +kernel

theorem e_rows_2 : (List.range' 20 20).all eRowOK = true := by decide +kernel

end ArchS9.Data
