/-  Probes/ArbEconomics_T1000_P0.lean -- ArbEconomics kernel chunks 0..15 (GENERATED; do not edit).
    Each `chunk_i` is a kernel `decide +kernel` check that `ArbEcon.run` maps s_i to s_(i+1).
    conjecture1_proved = False.
-/
import Probes.ArbEconomics_T1000_Cfg

namespace ArbEcon.I_T1000

theorem chunk_0 : ArbEcon.St.beq (ArbEcon.run cfg 500 s0) s1 = true := by decide +kernel
theorem chunk_1 : ArbEcon.St.beq (ArbEcon.run cfg 500 s1) s2 = true := by decide +kernel
theorem chunk_2 : ArbEcon.St.beq (ArbEcon.run cfg 500 s2) s3 = true := by decide +kernel
theorem chunk_3 : ArbEcon.St.beq (ArbEcon.run cfg 500 s3) s4 = true := by decide +kernel
theorem chunk_4 : ArbEcon.St.beq (ArbEcon.run cfg 500 s4) s5 = true := by decide +kernel
theorem chunk_5 : ArbEcon.St.beq (ArbEcon.run cfg 500 s5) s6 = true := by decide +kernel
theorem chunk_6 : ArbEcon.St.beq (ArbEcon.run cfg 500 s6) s7 = true := by decide +kernel
theorem chunk_7 : ArbEcon.St.beq (ArbEcon.run cfg 500 s7) s8 = true := by decide +kernel
theorem chunk_8 : ArbEcon.St.beq (ArbEcon.run cfg 500 s8) s9 = true := by decide +kernel
theorem chunk_9 : ArbEcon.St.beq (ArbEcon.run cfg 500 s9) s10 = true := by decide +kernel
theorem chunk_10 : ArbEcon.St.beq (ArbEcon.run cfg 500 s10) s11 = true := by decide +kernel
theorem chunk_11 : ArbEcon.St.beq (ArbEcon.run cfg 500 s11) s12 = true := by decide +kernel
theorem chunk_12 : ArbEcon.St.beq (ArbEcon.run cfg 500 s12) s13 = true := by decide +kernel
theorem chunk_13 : ArbEcon.St.beq (ArbEcon.run cfg 500 s13) s14 = true := by decide +kernel
theorem chunk_14 : ArbEcon.St.beq (ArbEcon.run cfg 500 s14) s15 = true := by decide +kernel
theorem chunk_15 : ArbEcon.St.beq (ArbEcon.run cfg 498 s15) s16 = true := by decide +kernel
theorem chunk_N : ArbEcon.St.beq (ArbEcon.run cfg 1 s16) sN = true := by decide +kernel

end ArbEcon.I_T1000
