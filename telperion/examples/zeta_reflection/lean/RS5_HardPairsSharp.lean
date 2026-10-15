/-  RS5_HardPairsSharp.lean -- lane B5, RSC0 Phase 4: the Tier-1 payoff at the two hardest known close pairs among the
    first 10^5 zeta zeros, decided by the KERNEL (`decide +kernel`) under the sharpened predicate `RS5.sampleOK'`
    (margin (3/5) t^(-3/4), t >= 4250; `RSInt.rs_Z_C0'`).

      * `p87761` : the 1/64-grid sample inside the gap of zeros n = 87761, 87762 (66678.07586, 66678.09534) at
        t = 4267397 / 2^6 = 66678.078125.  The OLD predicate (13/5) rejects it; the new one accepts it; its sign
        `gLine > 0` follows through `sampleOK'_sign`.
      * `p95248` : the only 1/64-grid sample inside the gap of zeros n = 95248, 95249 (71732.90121, 71732.91591; raw gap
        0.0147 < 1/64) at t = 4590906 / 2^6 = 71732.90625.  Same: 13/5 rejects, 3/5 accepts, sign `gLine < 0`.
      * `p87761f` : a finer dyadic sample t = 8534795 / 2^7 = 66678.0859375 in the 87761 gap, accepted even by the OLD
        predicate (13/5).

    The certificates are honest RS4 certificates (P = 64) emitted by the UNTRUSTED pipeline of the rsc0-hw agent
    (~/rh-team/rsc0/out/phase3b/hardpairs.json: certgen logic, margin numerator E = least E + 1 as the band emitters
    use), re-checked here by the kernel.  The proofs of `*_sign` are term proofs from `sampleOK'_sign`; every
    predicate verdict is `decide +kernel`.

    conjecture1_proved = False.  Three certified signs; nothing about RH.
-/
import RS5_BandSharp

open Complex

namespace RS5.HardPairsSharp

open RS5

/-- 1/64 sample in the n = 87761 gap. -/
noncomputable def p87761 : Sample :=
  ⟨4267397, 6, 4445620816017781, ⟨103, 1900296310297693859291, 1900296310297693859423, 2734667044757697, 2734667044757699, 2734464362246372, 2734464362246375, 5085864626563943614219416, 5085864627117251359352260, 1817476989865512866, 1817476989865512867, 1769789238951927912, 1769789238951928742, 8986785078024810662, 8986785078024811519, 16375941209393296414, 16375941209393298038, 166031034605146660252085156913383980, 181184712440112512276170325174247274⟩⟩

/-- The only 1/64 sample in the n = 95248 gap. -/
noncomputable def p95248 : Sample :=
  ⟨4590906, 6, 4208534605128296, ⟨106, 1971010789276199617735, 1971010789276199617872, 147697334556482513, 147697334556482515, 147109188593015289, 147109188593015302, 5519768490458742801983690, 5519768490973060436577587, 1784576143371643528, 1784576143371643529, 98369030573857145886, 98369030573857146762, 22126369812129577382, 22126369812129579708, 11516417416279366038, 11516417416279371040, -173384981289131650709591160956997146, -165498851786449474995328439289959822⟩⟩

/-- A 1/128 sample in the n = 87761 gap. -/
noncomputable def p87761f : Sample :=
  ⟨8534795, 7, 4445620425356299, ⟨103, 1900296421624121575911, 1900296421624121576043, 2735747883861742, 2735747883861744, 2735545041111793, 2735545041111796, 5085865294520150690252931, 5085865295073458370556159, 1817476936628233303, 1817476936628233304, 1770488723526857769, 1770488723526858599, 8987463196959435011, 8987463196959435868, 16375682052805164565, 16375682052805166189, 404086419716692114303942901821114075, 418882458060176913613923761567574408⟩⟩

theorem p87761_old_rejected : sampleOK p87761 = false := by decide +kernel

theorem p87761_new_accepted : sampleOK' p87761 = true := by decide +kernel

theorem p87761_pos : p87761.pos = true := by decide +kernel

theorem p87761_sign : 0 < XiLineZeros.gLine p87761.t :=
  (sampleOK'_sign p87761_new_accepted).1 p87761_pos

theorem p95248_old_rejected : sampleOK p95248 = false := by decide +kernel

theorem p95248_new_accepted : sampleOK' p95248 = true := by decide +kernel

theorem p95248_pos : p95248.pos = false := by decide +kernel

theorem p95248_sign : XiLineZeros.gLine p95248.t < 0 :=
  (sampleOK'_sign p95248_new_accepted).2 p95248_pos

theorem p87761f_old_accepted : sampleOK p87761f = true := by decide +kernel

theorem p87761f_new_accepted : sampleOK' p87761f = true := by decide +kernel

end RS5.HardPairsSharp
