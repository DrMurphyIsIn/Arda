/-  negctrl_emhigh.lean -- negative controls for EMZetaHighCheck.checkK (lane emhigh).  NOT a lean_lib.
    Run by hand from telperion/examples/zeta_reflection/lean (after `lake build EMZetaHighK_T10000`):
        cp ../arbecon/negctrl_emhigh.lean ZZneg.lean && lake env lean ZZneg.lean; rm ZZneg.lean
    Expected: `neg1`..`neg4` FAIL (`decide` proves the checker returns false); `pos` passes.
    conjecture1_proved = False.
-/
import EMZetaHighK_T10000
namespace ArbEcon.IKK_T10000
-- NEG 1: an upper bound for Re zeta BELOW the true value -0.3393738026 must be rejected.
theorem neg1 : ArbEcon.OrderK.checkK (ArbEcon.OrderK.cfg64 10000 0) 6 3212 s7 sN 100000000 (-34037097) (-33937381) (-3808812) (-3609534) 81920299520396227755155944589916323388398098619357652226 56 true = true := by
  decide +kernel

-- NEG 2: Q - 1 (Q^2 < pnK(2K+1)) must be rejected.
theorem neg2 : ArbEcon.OrderK.checkK (ArbEcon.OrderK.cfg64 10000 0) 6 3212 s7 sN 100000000 (-34037097) (-33837819) (-3808812) (-3609534) 81920299520396227755155944589916323388398098619357652225 56 true = true := by
  decide +kernel

-- NEG 3: a lower bound tightened by 1e-8 must be rejected (the certified bound is the floor).
theorem neg3 : ArbEcon.OrderK.checkK (ArbEcon.OrderK.cfg64 10000 0) 6 3212 s7 sN 100000000 (-34037096) (-33837819) (-3808812) (-3609534) 81920299520396227755155944589916323388398098619357652226 56 true = true := by
  decide +kernel

-- NEG 4: the odd-saw Q under the EVEN certificate: the even remainder is larger, the box must be rejected.
theorem neg4 : ArbEcon.OrderK.checkK (ArbEcon.OrderK.cfg64 10000 0) 6 3212 s7 sN 100000000 (-34037097) (-33837819) (-3808812) (-3609534) 81920299520396227755155944589916323388398098619357652226 56 false = true := by
  decide +kernel

-- POS: the emitted data passes.
theorem pos : ArbEcon.OrderK.checkK (ArbEcon.OrderK.cfg64 10000 0) 6 3212 s7 sN 100000000 (-34037097) (-33837819) (-3808812) (-3609534) 81920299520396227755155944589916323388398098619357652226 56 true = true := by
  decide +kernel

end ArbEcon.IKK_T10000
