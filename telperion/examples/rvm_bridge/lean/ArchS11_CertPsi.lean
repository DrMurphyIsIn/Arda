/-
  ArchS11_CertPsi -- kernel evaluation of the central-formula tables `Psi_m = hatT E (t^m)` (stage S11).
  `decide +kernel`: the Lean kernel reduces each Boolean checker in exact rational arithmetic.
  conjecture1_proved = False.  No `sorry`.
-/
import ArchS11_Data

namespace ArchS11.Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem bin_ok : binOK = true := by decide +kernel
theorem psiA_ok : psiOK EA PsiA = true := by decide +kernel
theorem psiH_ok : psiOK EH PsiH = true := by decide +kernel
theorem psiL_ok : psiOK EL PsiL = true := by decide +kernel
theorem lenA_ok : lenOK PsiA = true := by decide +kernel
theorem lenH_ok : lenOK PsiH = true := by decide +kernel
theorem lenL_ok : lenOK PsiL = true := by decide +kernel

end ArchS11.Data
