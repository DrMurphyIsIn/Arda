/-  RS5_AxiomGuard.lean -- lane B5: `#print axioms` for every RS5_ headline (and, per band chunk, its
    kernel acceptance `ok`, its sign-change `count` and its `zeros`).  Every line must print a subset of
    [propext, Classical.choice, Quot.sound].  Not a default target.

    conjecture1_proved = False.
-/
import RS5_Eval
import RS5_Sound
import RS5_Z
import RS5_Band
import RS5_Demo
import RS5_Band_Joint
import RS5_Band_T1000
import RS5_Band_T10000
import RS5_Band_T10000_C0
import RS5_Band_T10000_C1
import RS5_Band_T10000_C2
import RS5_Band_T10000_C3
import RS5_Band_T1000_C0
import RS5_Band_T1000_C1
import RS5_Band_T1000_C10
import RS5_Band_T1000_C11
import RS5_Band_T1000_C12
import RS5_Band_T1000_C13
import RS5_Band_T1000_C14
import RS5_Band_T1000_C15
import RS5_Band_T1000_C16
import RS5_Band_T1000_C17
import RS5_Band_T1000_C18
import RS5_Band_T1000_C19
import RS5_Band_T1000_C2
import RS5_Band_T1000_C20
import RS5_Band_T1000_C21
import RS5_Band_T1000_C22
import RS5_Band_T1000_C23
import RS5_Band_T1000_C24
import RS5_Band_T1000_C25
import RS5_Band_T1000_C26
import RS5_Band_T1000_C27
import RS5_Band_T1000_C28
import RS5_Band_T1000_C29
import RS5_Band_T1000_C3
import RS5_Band_T1000_C30
import RS5_Band_T1000_C31
import RS5_Band_T1000_C4
import RS5_Band_T1000_C5
import RS5_Band_T1000_C6
import RS5_Band_T1000_C7
import RS5_Band_T1000_C8
import RS5_Band_T1000_C9
import RS5_Band_T510
import RS5_Band_T510_C0

#print axioms RS5.checks5_of
#print axioms RS5.oneR
#print axioms RS5.pi_lo
#print axioms RS5.pi_hi
#print axioms RS5.t_ge
#print axioms RS5.t_pos
#print axioms RS5.alpha_sq
#print axioms RS5.alpha_nonneg
#print axioms RS5.alpha_key
#print axioms RS5.A0_le
#print axioms RS5.A1_ge
#print axioms RS5.N_lt_alpha
#print axioms RS5.alpha_lt_N1
#print axioms RS5.N_eq
#print axioms RS5.frac_eq
#print axioms RS5.frac_pos
#print axioms RS5.NO_le_A0
#print axioms RS5.NO_le_A1
#print axioms RS5.p_lo
#print axioms RS5.p_hi
#print axioms RS5.N_pos
#print axioms RS5.y_lo
#print axioms RS5.y_hi
#print axioms RS5.y_nonneg
#print axioms RS5.y_le_half
#print axioms RS5.log_alpha
#print axioms RS5.lg_lo
#print axioms RS5.lg_hi
#print axioms RS5.dstate_inv
#print axioms RS5.loga_lo
#print axioms RS5.loga_hi
#print axioms RS5.thetaMain_eq
#print axioms RS5.phase_scaled
#print axioms RS5.tn_pos
#print axioms RS5.phase_lo
#print axioms RS5.phase_hi
#print axioms RS5.alpha_pos
#print axioms RS5.w_sq_alpha
#print axioms RS5.w_lo
#print axioms RS5.w_hi
#print axioms RS5.U_lo
#print axioms RS5.U_hi
#print axioms RS5.G_bounds
#print axioms RS5.V_lo
#print axioms RS5.V_hi
#print axioms RS5.psi_num_eq
#print axioms RS5.lin_le_max
#print axioms RS5.lin_ge_min
#print axioms RS5.quot_sound
#print axioms RS5.main_sum_eq
#print axioms RS5.mainBox_mem
#print axioms RS5.neg_one_pow_eq
#print axioms RS5.c0Box_mem
#print axioms RS5.zBox_e
#print axioms RS5.check5_sound
#print axioms RS5.rs5_Z_enclosure
#print axioms RS5.tpow_le_margin
#print axioms RS5.rs5_Z_enclosure_E
#print axioms RS5.posOK_real
#print axioms RS5.negOK_real
#print axioms RS5.rs5_sign_pos
#print axioms RS5.rs5_sign_neg
#print axioms RS5.Sample.valid
#print axioms RS5.sampleOK_sign
#print axioms RS5.line_ne_zero'
#print axioms RS5.zeta_zero_of_completed_zero
#print axioms RS5.exists_zeta_zero_of_sign_change
#print axioms RS5.exists_zeta_zero_of_signs
#print axioms RS5.le_lastOf
#print axioms RS5.sign_mul_neg
#print axioms RS5.chain_zeros
#print axioms RS5.ltH_real
#print axioms RS5.bandOK_facts
#print axioms RS5.band_sound
#print axioms RS5.band_sound_finset
#print axioms RS5.bandZeros_of_ok
#print axioms RS5.BandZeros.glue
#print axioms RS5.BandZeros.mono
#print axioms RS5.BandZeros.zeta
#print axioms RS5.BandZeros.finset
#print axioms RS5.BandZeros.hLine
#print axioms RS5.Demo.zeta_zero_10000
#print axioms RS5.Demo.bad_flip
#print axioms RS5.Demo.bad_margin
#print axioms RS5.Demo.bad_order
#print axioms RS5.Demo.bad_floor
#print axioms RS5.BandJoint.zeros
#print axioms RS5.BandJoint.zeta_zeros
#print axioms RS5.BandJoint.zeta_zeros_finset
#print axioms RS5.BandJoint.hLine
#print axioms RS5.BandT1000.zeros
#print axioms RS5.BandT1000.zeta_zeros
#print axioms RS5.BandT1000.zeta_zeros_finset
#print axioms RS5.BandT1000.hLine
#print axioms RS5.BandT10000.zeros
#print axioms RS5.BandT10000.zeta_zeros
#print axioms RS5.BandT10000.zeta_zeros_finset
#print axioms RS5.BandT10000.hLine
#print axioms RS5.BandT10000.C0.ok
#print axioms RS5.BandT10000.C0.count
#print axioms RS5.BandT10000.C0.zeros
#print axioms RS5.BandT10000.C1.ok
#print axioms RS5.BandT10000.C1.count
#print axioms RS5.BandT10000.C1.zeros
#print axioms RS5.BandT10000.C2.ok
#print axioms RS5.BandT10000.C2.count
#print axioms RS5.BandT10000.C2.zeros
#print axioms RS5.BandT10000.C3.ok
#print axioms RS5.BandT10000.C3.count
#print axioms RS5.BandT10000.C3.zeros
#print axioms RS5.BandT1000.C0.ok
#print axioms RS5.BandT1000.C0.count
#print axioms RS5.BandT1000.C0.zeros
#print axioms RS5.BandT1000.C1.ok
#print axioms RS5.BandT1000.C1.count
#print axioms RS5.BandT1000.C1.zeros
#print axioms RS5.BandT1000.C10.ok
#print axioms RS5.BandT1000.C10.count
#print axioms RS5.BandT1000.C10.zeros
#print axioms RS5.BandT1000.C11.ok
#print axioms RS5.BandT1000.C11.count
#print axioms RS5.BandT1000.C11.zeros
#print axioms RS5.BandT1000.C12.ok
#print axioms RS5.BandT1000.C12.count
#print axioms RS5.BandT1000.C12.zeros
#print axioms RS5.BandT1000.C13.ok
#print axioms RS5.BandT1000.C13.count
#print axioms RS5.BandT1000.C13.zeros
#print axioms RS5.BandT1000.C14.ok
#print axioms RS5.BandT1000.C14.count
#print axioms RS5.BandT1000.C14.zeros
#print axioms RS5.BandT1000.C15.ok
#print axioms RS5.BandT1000.C15.count
#print axioms RS5.BandT1000.C15.zeros
#print axioms RS5.BandT1000.C16.ok
#print axioms RS5.BandT1000.C16.count
#print axioms RS5.BandT1000.C16.zeros
#print axioms RS5.BandT1000.C17.ok
#print axioms RS5.BandT1000.C17.count
#print axioms RS5.BandT1000.C17.zeros
#print axioms RS5.BandT1000.C18.ok
#print axioms RS5.BandT1000.C18.count
#print axioms RS5.BandT1000.C18.zeros
#print axioms RS5.BandT1000.C19.ok
#print axioms RS5.BandT1000.C19.count
#print axioms RS5.BandT1000.C19.zeros
#print axioms RS5.BandT1000.C2.ok
#print axioms RS5.BandT1000.C2.count
#print axioms RS5.BandT1000.C2.zeros
#print axioms RS5.BandT1000.C20.ok
#print axioms RS5.BandT1000.C20.count
#print axioms RS5.BandT1000.C20.zeros
#print axioms RS5.BandT1000.C21.ok
#print axioms RS5.BandT1000.C21.count
#print axioms RS5.BandT1000.C21.zeros
#print axioms RS5.BandT1000.C22.ok
#print axioms RS5.BandT1000.C22.count
#print axioms RS5.BandT1000.C22.zeros
#print axioms RS5.BandT1000.C23.ok
#print axioms RS5.BandT1000.C23.count
#print axioms RS5.BandT1000.C23.zeros
#print axioms RS5.BandT1000.C24.ok
#print axioms RS5.BandT1000.C24.count
#print axioms RS5.BandT1000.C24.zeros
#print axioms RS5.BandT1000.C25.ok
#print axioms RS5.BandT1000.C25.count
#print axioms RS5.BandT1000.C25.zeros
#print axioms RS5.BandT1000.C26.ok
#print axioms RS5.BandT1000.C26.count
#print axioms RS5.BandT1000.C26.zeros
#print axioms RS5.BandT1000.C27.ok
#print axioms RS5.BandT1000.C27.count
#print axioms RS5.BandT1000.C27.zeros
#print axioms RS5.BandT1000.C28.ok
#print axioms RS5.BandT1000.C28.count
#print axioms RS5.BandT1000.C28.zeros
#print axioms RS5.BandT1000.C29.ok
#print axioms RS5.BandT1000.C29.count
#print axioms RS5.BandT1000.C29.zeros
#print axioms RS5.BandT1000.C3.ok
#print axioms RS5.BandT1000.C3.count
#print axioms RS5.BandT1000.C3.zeros
#print axioms RS5.BandT1000.C30.ok
#print axioms RS5.BandT1000.C30.count
#print axioms RS5.BandT1000.C30.zeros
#print axioms RS5.BandT1000.C31.ok
#print axioms RS5.BandT1000.C31.count
#print axioms RS5.BandT1000.C31.zeros
#print axioms RS5.BandT1000.C4.ok
#print axioms RS5.BandT1000.C4.count
#print axioms RS5.BandT1000.C4.zeros
#print axioms RS5.BandT1000.C5.ok
#print axioms RS5.BandT1000.C5.count
#print axioms RS5.BandT1000.C5.zeros
#print axioms RS5.BandT1000.C6.ok
#print axioms RS5.BandT1000.C6.count
#print axioms RS5.BandT1000.C6.zeros
#print axioms RS5.BandT1000.C7.ok
#print axioms RS5.BandT1000.C7.count
#print axioms RS5.BandT1000.C7.zeros
#print axioms RS5.BandT1000.C8.ok
#print axioms RS5.BandT1000.C8.count
#print axioms RS5.BandT1000.C8.zeros
#print axioms RS5.BandT1000.C9.ok
#print axioms RS5.BandT1000.C9.count
#print axioms RS5.BandT1000.C9.zeros
#print axioms RS5.BandT510.zeros
#print axioms RS5.BandT510.zeta_zeros
#print axioms RS5.BandT510.zeta_zeros_finset
#print axioms RS5.BandT510.hLine
#print axioms RS5.BandT510.C0.ok
#print axioms RS5.BandT510.C0.count
#print axioms RS5.BandT510.C0.zeros
