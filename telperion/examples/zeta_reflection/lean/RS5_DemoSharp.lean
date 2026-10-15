/-  RS5_DemoSharp.lean -- lane B5, RSC0 Phase 3: read-back controls for the sharpened band predicate
    `RS5.bandOK'` / `RS5.sampleOK'` (margin (3/5) t^(-3/4), t >= 4250; `RSInt.rs_Z_C0'`).  Every verdict
    below is decided by the KERNEL (`decide +kernel`).

      * `knife` : an honest RS4 certificate (P = 64) at t = 40960269 / 2^12 = 10000.0656738..., just past
        the first zero above 10000 (10000.06534...), with the TIGHT margin numerator E (the least E with
        `MarginOK`).  Its box is [0.001110, 0.001913] (UNTRUSTED decimals; the kernel decides the integer
        tests): it FAILS the 13/5 test (`knife_old_rejected`: (13/5) E/2^64 = 0.002600) and PASSES the 3/5 test
        (`knife_new_accepted`: (3/5) E/2^64 = 0.000600); `knife_sign` is the sign of `gLine` it certifies,
        glued by `sampleOK'_sign` -> `rs5_sign_pos'` -> `RSInt.rs_Z_C0'`.
      * `knife_Edec` : the same sample with E decremented by one is REJECTED (`MarginOK` fails).
      * `low` : the honest first sample of the [510, 520] band (accepted by the OLD `sampleOK`) is REFUSED
        by `sampleOK'`, because the height test `HeightOK` (t >= 4250) fails.

    The knife certificate was emitted by the UNTRUSTED generator ~/rh-team/rsc0/out/phase3/certgen.py
    (rebuilt from the RS4_Eval check list; the lane-B4 emitter is gone).

    conjecture1_proved = False.  One certified sign; nothing about RH.
-/
import RS5_BandSharp
import RS5_Band_T510_C0

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

end RS5.DemoSharp
