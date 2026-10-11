/-
  ArchS11_CertT1 -- kernel evaluation of S11 certificate checkers (the |I| = 1/2 certificate).
  `decide +kernel` only: the Lean kernel reduces each Boolean checker in exact rational arithmetic.
  conjecture1_proved = False.  No `sorry`.
-/
import ArchS11_Data

namespace ArchS11.Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem okT1_ok : okT1 = true := by decide +kernel

end ArchS11.Data
