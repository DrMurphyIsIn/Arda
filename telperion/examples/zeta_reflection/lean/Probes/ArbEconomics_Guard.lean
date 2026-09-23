/-  Probes/ArbEconomics_Guard.lean -- axiom battery for the ArbEconomics certified enclosures.

    Every enclosure theorem must depend on exactly [propext, Classical.choice, Quot.sound]
    (no placeholder axiom, no compiled-evaluation trust axiom, no custom axiom).
    conjecture1_proved = False.
-/
import Probes.ArbEconomics_T100
import Probes.ArbEconomics_T1000
import Probes.ArbEconomics_T10000
import Probes.ArbEconomics_T30000

/-- info: 'ArbEcon.I_T100.zeta_re' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ArbEcon.I_T100.zeta_re
/-- info: 'ArbEcon.I_T100.zeta_im' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ArbEcon.I_T100.zeta_im
/-- info: 'ArbEcon.I_T1000.zeta_re' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ArbEcon.I_T1000.zeta_re
/-- info: 'ArbEcon.I_T1000.zeta_im' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ArbEcon.I_T1000.zeta_im
/-- info: 'ArbEcon.I_T10000.zeta_re' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ArbEcon.I_T10000.zeta_re
/-- info: 'ArbEcon.I_T10000.zeta_im' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ArbEcon.I_T10000.zeta_im
/-- info: 'ArbEcon.I_T30000.zeta_re' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ArbEcon.I_T30000.zeta_re
/-- info: 'ArbEcon.I_T30000.zeta_im' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ArbEcon.I_T30000.zeta_im
/-- info: 'ArbEcon.chunk_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ArbEcon.chunk_sound
/-- info: 'ArbEcon.zeta_re_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ArbEcon.zeta_re_bounds

#check @ArbEcon.I_T30000.zeta_re
#check @ArbEcon.I_T30000.zeta_im
