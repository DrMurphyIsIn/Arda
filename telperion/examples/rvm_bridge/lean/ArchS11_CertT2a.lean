/-
  ArchS11_CertT2a -- kernel evaluation of S11 certificate checkers (the |I| = log 2 top and gamma certificates).
  `decide +kernel` only: the Lean kernel reduces each Boolean checker in exact rational arithmetic.
  conjecture1_proved = False.  No `sorry`.
-/
import ArchS11_Data

namespace ArchS11.Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem okTop_ok : okTop = true := by decide +kernel
theorem okGam_ok : okGam = true := by decide +kernel

end ArchS11.Data
