/-  RS5_DemoSharp.lean -- lane B5, RSC0 Phase 3: read-back controls for the sharpened band predicate
    `RS5.bandOK'` / `RS5.sampleOK'` (margin (3/5) t^(-3/4), t >= 4250; `RSInt.rs_Z_C0'`).  Every predicate
    verdict (`sampleOK`, `sampleOK'`, `bandOK'`, `HeightOK`, `MarginOK`, `PosOK`, `PosOK'`, `NegOK'`) is decided by the KERNEL
    (`decide +kernel`); `knife_t` is `norm_num` and `knife_sign` / `neg_sign` are term proofs from `sampleOK'_sign`.

      * `knife` : an honest RS4 certificate (P = 64) at t = 40960269 / 2^12 = 10000.0656738..., just past
        the first zero above 10000 (10000.06534...), with the TIGHT margin numerator E (the least E with
        `MarginOK`).  Its box is [0.001110, 0.001913] (UNTRUSTED decimals; the kernel decides the integer
        tests): it FAILS the 13/5 test (`knife_old_rejected`: (13/5) E/2^64 = 0.002600) and PASSES the 3/5 test
        (`knife_new_accepted`: (3/5) E/2^64 = 0.000600); `knife_sign` is the sign of `gLine` it certifies,
        glued by `sampleOK'_sign` -> `rs5_sign_pos'` -> `RSInt.rs_Z_C0'`.
      * `knife_Edec` : the same sample with E decremented by one is REJECTED (`MarginOK` fails).
      * `low` : the honest first sample of the [510, 520] band (accepted by the OLD `sampleOK`) is REFUSED
        by `sampleOK'`, because the height test `HeightOK` (t >= 4250) fails.
      * boundary (RSC0 Phase 3c, bb nit 7): honest certificates at tn = 4250 * 2^6 (t = 4250, accepted by `sampleOK'`) and
        tn - 1 (t = 4249.984..., accepted by the OLD `sampleOK`, refused by `sampleOK'`: `HeightOK` alone fails);
      * the knife box at its exact PosOK' threshold: with E raised to the least E' with 3 E' one >= 5 zlo, `PosOK'` decides
        FALSE (box just inside (3/5) E'); with E' - 1 it decides TRUE (MarginOK holds for both: E' > tight E);
      * a NEGATIVE sample at t >= 4250 (the first sample of the committed [10000, 11000] band, chunk 0) is accepted by
        `sampleOK'` through `NegOK'`; `neg_sign` is its certified sign gLine < 0.

    The knife certificate was emitted by the UNTRUSTED generator ~/rh-team/rsc0/out/phase3/certgen.py
    (rebuilt from the RS4_Eval check list; the lane-B4 emitter is gone).

    conjecture1_proved = False.  One certified sign; nothing about RH.
-/
import RS5_BandSharp
import RS5_Band_T510_C0
import RS5_Band_T10000_C0

open Complex

namespace RS5.DemoSharp

open RS5

/-- The knife-edge sample: t = 40960269 / 2^12, tight E, honest RS4 certificate. -/
noncomputable def knife : Sample :=
  ⟨40960269, 12, 18446653214109191, ⟨39, 735921031200393396260, 735921031200393396312, 423025957069766236, 423025957069766239, 418248384107444778, 418248384107574203, 587753218475144086366376, 587753222164469977349989, 2920545499447242229, 2920545499447242230, 103660068642637171632, 103660068642637171974, 18194768595996360334, 18194768595996361249, 12921374816769689318, 12921374816769690831, 377755505729972886773177015911525660, 651109329596426144563058463232682940⟩⟩

theorem knife_height : HeightOK knife := by decide +kernel

theorem knife_tight : MarginOK knife.cfg knife.E := by decide +kernel

/-- The OLD predicate (13/5) rejects the knife-edge sample. -/
theorem knife_old_rejected : sampleOK knife = false := by decide +kernel

theorem knife_old_PosOK_fails : ¬ PosOK knife.cfg knife.z knife.E := by decide +kernel

/-- The NEW predicate (3/5, t >= 4250) accepts it. -/
theorem knife_new_accepted : sampleOK' knife = true := by decide +kernel

theorem knife_pos : knife.pos = true := by decide +kernel

theorem knife_band : bandOK' [knife] = true := by decide +kernel

theorem knife_t : knife.t = (40960269 / 4096 : ℝ) := by
  show (((40960269 : ℕ) : ℝ)) / 2 ^ (12 : ℕ) = (40960269 / 4096 : ℝ)
  norm_num

/-- **The certified sign, glued by the sharpened lemma**: `gLine (40960269 / 2^12) > 0`. -/
theorem knife_sign : 0 < XiLineZeros.gLine (40960269 / 4096 : ℝ) := by
  rw [← knife_t]
  exact (sampleOK'_sign knife_new_accepted).1 knife_pos

/-- The same sample with E decremented by one. -/
noncomputable def knife_Edec : Sample := { knife with E := knife.E - 1 }

theorem knife_Edec_rejected : sampleOK' knife_Edec = false := by decide +kernel

theorem knife_Edec_margin_fails : ¬ MarginOK knife_Edec.cfg knife_Edec.E := by decide +kernel

/-- An honest sample below the threshold: the first sample of the [510, 520] band. -/
noncomputable def low : Sample := RS5.BandT510.C0.s0

theorem low_old_accepted : sampleOK low = true := by decide +kernel

theorem low_height_fails : ¬ HeightOK low := by decide +kernel

/-- Below t = 4250 the sharpened predicate REFUSES it (the hypothesis of `rs_Z_C0'`). -/
theorem low_refused : sampleOK' low = false := by decide +kernel

/-! ## RSC0 Phase 3c additions (bb nit 7) -/

/-- Honest certificate at exactly t = 4250 = 272000 / 2^6 (tight E). -/
noncomputable def at4250 : Sample :=
  ⟨272000, 6, 35045158212224973, ⟨26, 479760240282090266857, 479760240282090266891, 5572860216997109, 5572860216997111, 5572018591034651, 5572018591034654, 216247511830876519834306, 216247520511697264118009, 3617157813501497961, 3617157813501497962, 910398149294448852, 910398149294449067, 8147266667249211400, 8147266667249211619, 16696953477061612229, 16696953477061612665, 554915892960393347950986348500725141902, 555793373233652429148052704646650662091⟩⟩

/-- Honest certificate one grid step below, t = 271999 / 2^6 < 4250 (tight E). -/
noncomputable def below4250 : Sample :=
  ⟨271999, 6, 35045254844405901, ⟨26, 479759358369073283394, 479759358369073283428, 5538940485574668, 5538940485574670, 5538109072683091, 5538109072683094, 216246572661671997328200, 216246581342524656511358, 3617161138102715799, 3617161138102715801, 904856926383927936, 904856926383928151, 8141812229143314497, 8141812229143314716, 16699040046680364307, 16699040046680364743, 500457790070530037736458077803286107257, 501331190921070626978723779122977545251⟩⟩

theorem at4250_height : HeightOK at4250 := by decide +kernel

theorem at4250_accepted : sampleOK' at4250 = true := by decide +kernel

theorem below4250_height_fails : ¬ HeightOK below4250 := by decide +kernel

theorem below4250_old_accepted : sampleOK below4250 = true := by decide +kernel

theorem below4250_refused : sampleOK' below4250 = false := by decide +kernel

/-- The knife box with E raised to the least E' with `3 E' one >= 5 zlo` (E' = 34130278331733086). -/
noncomputable def knife_E35 : Sample := { knife with E := 34130278331733086 }

/-- ... and one less. -/
noncomputable def knife_E35m : Sample := { knife with E := 34130278331733085 }

theorem knife_E35_margin : MarginOK knife_E35.cfg knife_E35.E := by decide +kernel

theorem knife_E35_PosOK'_false : ¬ PosOK' knife_E35.cfg knife_E35.z knife_E35.E := by decide +kernel

theorem knife_E35_rejected : sampleOK' knife_E35 = false := by decide +kernel

theorem knife_E35m_PosOK'_true : PosOK' knife_E35m.cfg knife_E35m.z knife_E35m.E := by decide +kernel

theorem knife_E35m_accepted : sampleOK' knife_E35m = true := by decide +kernel

/-- A negative sample at t = 10000 (committed band [10000, 11000], chunk 0, first sample). -/
noncomputable def negs : Sample := RS5.BandT10000.C0.s0

theorem negs_pos : negs.pos = false := by decide +kernel

theorem negs_NegOK' : NegOK' negs.cfg negs.z negs.E := by decide +kernel

theorem negs_accepted : sampleOK' negs = true := by decide +kernel

/-- Its certified sign through the sharpened lemma: `gLine 10000 < 0`. -/
theorem neg_sign : XiLineZeros.gLine negs.t < 0 :=
  (sampleOK'_sign negs_accepted).2 negs_pos

end RS5.DemoSharp
