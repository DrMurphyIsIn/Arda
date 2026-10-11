/-
  ArchS9_CertGram3 -- kernel evaluation of S9 certificate checkers (archimedean stage S9, 2026-10-11).
  `decide +kernel`: the Lean kernel reduces the Boolean checker of ArchS9_Data itself (exact
  integer / rational arithmetic, GMP-accelerated Nat); no compiled code is trusted.
  Gram rows 13-21.
  conjecture1_proved = False.  No `sorry`.
-/
import ArchS9_Data

namespace ArchS9.Data

set_option maxRecDepth 100000

theorem gram_rows_3 : (List.range' 13 9).all gramRowOK = true := by decide +kernel

end ArchS9.Data
