/-  AxiomGuardEMZetaOffline.lean -- trust-base guard of lane offline (the OFF-LINE kernel evaluator
    of zeta: general-sigma Euler-Maclaurin, three off-line enclosures, one hypothesis-free SlabClear).
    Prints `#print axioms` for EVERY theorem of the 12 new modules (157 theorems).  Every line must read
        [propext, Classical.choice, Quot.sound]
    or a SUBSET of it (the kernel `decide` chunk theorems depend on no axioms at all).

    conjecture1_proved = False.
-/
import EMZetaOffline

-- EMZetaOfflineCore.lean
#print axioms ZetaReflection.EMOff.emTail_eq_mellin
#print axioms ZetaReflection.EMOff.sawCut_norm_le
#print axioms ZetaReflection.EMOff.sawCut_measurable
#print axioms ZetaReflection.EMOff.mellin_sawCut_differentiableAt
#print axioms ZetaReflection.EMOff.poch_differentiable
#print axioms ZetaReflection.EMOff.emC_differentiable
#print axioms ZetaReflection.EMOff.emTail_differentiableAt
#print axioms ZetaReflection.EMOff.emFiniteM_differentiableAt
#print axioms ZetaReflection.EMOff.em_zeta_order_ext
#print axioms ZetaReflection.EMOff.emTail_norm_le_ext
#print axioms ZetaReflection.EMOff.em_zeta_orderK_enclosure_ext
#print axioms ZetaReflection.EMOff.em_zeta_orderK_enclosure_odd_ext

-- EMZetaOfflineSound.lean
#print axioms ArbEcon.Off.imul_sound
#print axioms ArbEcon.Off.tbMul_sound
#print axioms ArbEcon.Off.accAdd_sound
#print axioms ArbEcon.Off.addChain_sound
#print axioms ArbEcon.Off.rpow_neg_sigma_pow
#print axioms ArbEcon.Off.ampl_sound
#print axioms ArbEcon.Off.cpow_termG
#print axioms ArbEcon.Off.termTB_sound
#print axioms ArbEcon.Off.psumK_succ
#print axioms ArbEcon.Off.psumK_one_zero
#print axioms ArbEcon.Off.psumK_one_succ
#print axioms ArbEcon.Off.stepO_sound
#print axioms ArbEcon.Off.runO_sound
#print axioms ArbEcon.Off.Acc.beq_eq
#print axioms ArbEcon.Off.accsBeq_eq
#print axioms ArbEcon.Off.StO.beq_eq
#print axioms ArbEcon.Off.chunkO_sound
#print axioms ArbEcon.Off.accsOK_zero
#print axioms ArbEcon.Off.initO_sound

-- EMZetaOfflineCheck.lean
#print axioms ArbEcon.Off.gpochG_succ
#print axioms ArbEcon.Off.pochRI_eq_gpochG
#print axioms ArbEcon.Off.gsumG_eq
#print axioms ArbEcon.Off.corr_eqG
#print axioms ArbEcon.Off.pochNormSq_eq_pnG
#print axioms ArbEcon.Off.rpow_neg_le_of_pow
#print axioms ArbEcon.Off.remOddG_sound
#print axioms ArbEcon.Off.psumK_zero_eq
#print axioms ArbEcon.Off.emFinite_split
#print axioms ArbEcon.Off.zeta_ballG
#print axioms ArbEcon.Off.checkCoreG_sound
#print axioms ArbEcon.Off.checkG_sound
#print axioms ArbEcon.Off.accOK_head

-- EMZetaOfflineI_S03_T1000.lean
#print axioms ArbEcon.Off.I_S03_T1000.chunk_0
#print axioms ArbEcon.Off.I_S03_T1000.chunk_1
#print axioms ArbEcon.Off.I_S03_T1000.chunk_N
#print axioms ArbEcon.Off.I_S03_T1000.ht
#print axioms ArbEcon.Off.I_S03_T1000.hσ
#print axioms ArbEcon.Off.I_S03_T1000.valid
#print axioms ArbEcon.Off.I_S03_T1000.ovalid
#print axioms ArbEcon.Off.I_S03_T1000.inv_0
#print axioms ArbEcon.Off.I_S03_T1000.inv_1
#print axioms ArbEcon.Off.I_S03_T1000.inv_2
#print axioms ArbEcon.Off.I_S03_T1000.inv_N
#print axioms ArbEcon.Off.I_S03_T1000.check
#print axioms ArbEcon.Off.I_S03_T1000.check_neg
#print axioms ArbEcon.Off.I_S03_T1000.zeta_box
#print axioms ArbEcon.Off.I_S03_T1000.zeta_re_im

-- EMZetaOfflineI_S12_T1000.lean
#print axioms ArbEcon.Off.I_S12_T1000.chunk_0
#print axioms ArbEcon.Off.I_S12_T1000.chunk_1
#print axioms ArbEcon.Off.I_S12_T1000.chunk_N
#print axioms ArbEcon.Off.I_S12_T1000.ht
#print axioms ArbEcon.Off.I_S12_T1000.hσ
#print axioms ArbEcon.Off.I_S12_T1000.valid
#print axioms ArbEcon.Off.I_S12_T1000.ovalid
#print axioms ArbEcon.Off.I_S12_T1000.inv_0
#print axioms ArbEcon.Off.I_S12_T1000.inv_1
#print axioms ArbEcon.Off.I_S12_T1000.inv_2
#print axioms ArbEcon.Off.I_S12_T1000.inv_N
#print axioms ArbEcon.Off.I_S12_T1000.check
#print axioms ArbEcon.Off.I_S12_T1000.check_neg
#print axioms ArbEcon.Off.I_S12_T1000.zeta_box
#print axioms ArbEcon.Off.I_S12_T1000.zeta_re_im

-- EMZetaOfflineI_SM1_T9995.lean
#print axioms ArbEcon.Off.I_SM1_T9995.chunk_0
#print axioms ArbEcon.Off.I_SM1_T9995.chunk_1
#print axioms ArbEcon.Off.I_SM1_T9995.chunk_N
#print axioms ArbEcon.Off.I_SM1_T9995.ht
#print axioms ArbEcon.Off.I_SM1_T9995.hσ
#print axioms ArbEcon.Off.I_SM1_T9995.valid
#print axioms ArbEcon.Off.I_SM1_T9995.ovalid
#print axioms ArbEcon.Off.I_SM1_T9995.inv_0
#print axioms ArbEcon.Off.I_SM1_T9995.inv_1
#print axioms ArbEcon.Off.I_SM1_T9995.inv_2
#print axioms ArbEcon.Off.I_SM1_T9995.inv_N
#print axioms ArbEcon.Off.I_SM1_T9995.check
#print axioms ArbEcon.Off.I_SM1_T9995.check_neg
#print axioms ArbEcon.Off.I_SM1_T9995.zeta_box
#print axioms ArbEcon.Off.I_SM1_T9995.zeta_re_im

-- EMZetaOfflineSlab.lean
#print axioms ArbEcon.Off.Cp_nonneg
#print axioms ArbEcon.Off.exp_taylor_le
#print axioms ArbEcon.Off.natCpow_neg_add
#print axioms ArbEcon.Off.norm_natCpow_neg_le_one
#print axioms ArbEcon.Off.norm_poch_sub_le
#print axioms ArbEcon.Off.emCorr_sub_le
#print axioms ArbEcon.Off.exp_one_le_three
#print axioms ArbEcon.Off.emFinite_taylor_le
#print axioms ArbEcon.Off.CK_nonneg
#print axioms ArbEcon.Off.CK_le
#print axioms ArbEcon.Off.pochNormSq_mono
#print axioms ArbEcon.Off.em_remainder_region
#print axioms ArbEcon.Off.norm_emCorr_le
#print axioms ArbEcon.Off.zeta_ne_zero_of_cell

-- EMZetaOfflineSlabCheck.lean
#print axioms ArbEcon.Off.Wk_eq_psumK
#print axioms ArbEcon.Off.wball_sound
#print axioms ArbEcon.Off.wUpper_sound
#print axioms ArbEcon.Off.sumM_sound
#print axioms ArbEcon.Off.checkCell_sound

-- EMZetaOfflineSlabClear.lean
#print axioms ArbEcon.Off.norm_add_nat_le
#print axioms ArbEcon.Off.cell_zeta_ne_zero
#print axioms ArbEcon.Off.slabClear_of_right_half
#print axioms ArbEcon.Off.dist_le_of_box

-- EMZetaOfflineSlab_T1000.lean
#print axioms ArbEcon.Off.Slab_T1000.chunk0_1
#print axioms ArbEcon.Off.Slab_T1000.chunk0_N
#print axioms ArbEcon.Off.Slab_T1000.check0
#print axioms ArbEcon.Off.Slab_T1000.check0_neg
#print axioms ArbEcon.Off.Slab_T1000.chunk1_1
#print axioms ArbEcon.Off.Slab_T1000.chunk1_N
#print axioms ArbEcon.Off.Slab_T1000.check1
#print axioms ArbEcon.Off.Slab_T1000.check1_neg
#print axioms ArbEcon.Off.Slab_T1000.chunk2_1
#print axioms ArbEcon.Off.Slab_T1000.chunk2_N
#print axioms ArbEcon.Off.Slab_T1000.check2
#print axioms ArbEcon.Off.Slab_T1000.check2_neg
#print axioms ArbEcon.Off.Slab_T1000.ht
#print axioms ArbEcon.Off.Slab_T1000.valid
#print axioms ArbEcon.Off.Slab_T1000.abs_bern
#print axioms ArbEcon.Off.Slab_T1000.budget
#print axioms ArbEcon.Off.Slab_T1000.hQ
#print axioms ArbEcon.Off.Slab_T1000.hσ0
#print axioms ArbEcon.Off.Slab_T1000.ovalid0
#print axioms ArbEcon.Off.Slab_T1000.inv0_1
#print axioms ArbEcon.Off.Slab_T1000.inv0_N
#print axioms ArbEcon.Off.Slab_T1000.cell0
#print axioms ArbEcon.Off.Slab_T1000.hσ1
#print axioms ArbEcon.Off.Slab_T1000.ovalid1
#print axioms ArbEcon.Off.Slab_T1000.inv1_1
#print axioms ArbEcon.Off.Slab_T1000.inv1_N
#print axioms ArbEcon.Off.Slab_T1000.cell1
#print axioms ArbEcon.Off.Slab_T1000.hσ2
#print axioms ArbEcon.Off.Slab_T1000.ovalid2
#print axioms ArbEcon.Off.Slab_T1000.inv2_1
#print axioms ArbEcon.Off.Slab_T1000.inv2_N
#print axioms ArbEcon.Off.Slab_T1000.cell2
#print axioms ArbEcon.Off.Slab_T1000.right_half
#print axioms ArbEcon.Off.Slab_T1000.slabClear

-- EMZetaOfflineSlabBand.lean
#print axioms ArbEcon.Off.Slab_T1000.band24_top_slabClear
#print axioms ArbEcon.Off.Slab_T1000.top_edge_1000_nonvanishing

-- EMZetaOffline.lean
#print axioms ArbEcon.Off.Headline.em_zeta_order_offline
#print axioms ArbEcon.Off.Headline.offline_evaluator_sound
#print axioms ArbEcon.Off.Headline.offline_evaluator_init
#print axioms ArbEcon.Off.Headline.offline_enclosure_sound
#print axioms ArbEcon.Off.Headline.zeta_03_1000
#print axioms ArbEcon.Off.Headline.zeta_12_1000
#print axioms ArbEcon.Off.Headline.zeta_m1_9995
#print axioms ArbEcon.Off.Headline.slabClear_1000
#print axioms ArbEcon.Off.Headline.band24_top_slabClear
