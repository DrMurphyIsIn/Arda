/-  Probes/ArbEconomics_T100_P0.lean -- ArbEconomics kernel chunks 0..0 (GENERATED; do not edit).
    Each `chunk_i` is a kernel `decide +kernel` check that `ArbEcon.run` maps s_i to s_(i+1).
    conjecture1_proved = False.
-/
import Probes.ArbEconomics_T100_Cfg

namespace ArbEcon.I_T100

theorem chunk_0 : ArbEcon.St.beq (ArbEcon.run cfg 498 s0) s1 = true := by decide +kernel
theorem chunk_N : ArbEcon.St.beq (ArbEcon.run cfg 1 s1) sN = true := by decide +kernel

end ArbEcon.I_T100
