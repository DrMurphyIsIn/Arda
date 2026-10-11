/-
  ArchS9_CertMisc -- kernel evaluation of S9 certificate checkers (archimedean stage S9, 2026-10-11).
  `decide +kernel`: the Lean kernel reduces the Boolean checker of ArchS9_Data itself (exact
  integer / rational arithmetic, GMP-accelerated Nat); no compiled code is trusted.
  Constants (eta, pi-spread, zeta, eps, C), the 13 windows, localization; plus a NEGATIVE CONTROL.
  conjecture1_proved = False.  No `sorry`.
-/
import ArchS9_Data

namespace ArchS9.Data

set_option maxRecDepth 100000

theorem lc_ok : lcOK = true := by decide +kernel

theorem const_ok : constOK = true := by decide +kernel

theorem windows_ok : (List.range (NCw + 1)).all windowOK = true := by decide +kernel

theorem loc_ok : locOK = true := by decide +kernel

/-- NEGATIVE CONTROL: shrinking the second-round window of n = 0 by a factor 10 breaks the
certificate (the residual bound eps forces |λ - θ 0| up to about 6.7e-43), so `windows_ok` is not
vacuous. -/
theorem window_negative_control :
    roundOK 0 (w1q 0) (R1q 0) (pi1q 0) (w2q 0 / 10) = false := by decide +kernel

end ArchS9.Data
