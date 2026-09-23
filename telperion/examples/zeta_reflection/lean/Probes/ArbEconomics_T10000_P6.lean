/-  Probes/ArbEconomics_T10000_P6.lean -- ArbEconomics kernel chunks 240..250 (GENERATED; do not edit).
    Each `chunk_i` is a kernel `decide +kernel` check that `ArbEcon.run` maps s_i to s_(i+1).
    conjecture1_proved = False.
-/
import Probes.ArbEconomics_T10000_Cfg

namespace ArbEcon.I_T10000

theorem chunk_240 : ArbEcon.St.beq (ArbEcon.run cfg 500 s240) s241 = true := by decide +kernel
theorem chunk_241 : ArbEcon.St.beq (ArbEcon.run cfg 500 s241) s242 = true := by decide +kernel
theorem chunk_242 : ArbEcon.St.beq (ArbEcon.run cfg 500 s242) s243 = true := by decide +kernel
theorem chunk_243 : ArbEcon.St.beq (ArbEcon.run cfg 500 s243) s244 = true := by decide +kernel
theorem chunk_244 : ArbEcon.St.beq (ArbEcon.run cfg 500 s244) s245 = true := by decide +kernel
theorem chunk_245 : ArbEcon.St.beq (ArbEcon.run cfg 500 s245) s246 = true := by decide +kernel
theorem chunk_246 : ArbEcon.St.beq (ArbEcon.run cfg 500 s246) s247 = true := by decide +kernel
theorem chunk_247 : ArbEcon.St.beq (ArbEcon.run cfg 500 s247) s248 = true := by decide +kernel
theorem chunk_248 : ArbEcon.St.beq (ArbEcon.run cfg 500 s248) s249 = true := by decide +kernel
theorem chunk_249 : ArbEcon.St.beq (ArbEcon.run cfg 500 s249) s250 = true := by decide +kernel
theorem chunk_250 : ArbEcon.St.beq (ArbEcon.run cfg 498 s250) s251 = true := by decide +kernel
theorem chunk_N : ArbEcon.St.beq (ArbEcon.run cfg 1 s251) sN = true := by decide +kernel

end ArbEcon.I_T10000
