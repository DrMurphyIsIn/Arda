/-
  ArchS11_CertT2b -- kernel evaluation of S11 certificate checkers (the |I| = log 2 lambda_2 and overlap certificates).
  `decide +kernel` only: the Lean kernel reduces each Boolean checker in exact rational arithmetic.
  conjecture1_proved = False.  No `sorry`.
-/
import ArchS11_Data

namespace ArchS11.Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem okLam2_ok : okLam2 = true := by decide +kernel
theorem okOvl_ok : okOvl = true := by decide +kernel

end ArchS11.Data
