/-  AxiomGuardEMZetaHigh.lean -- kernel-axiom guard of lane emhigh (general-order Euler-Maclaurin ζ
    evaluator).  Prints `#print axioms` for every theorem of EMZetaHigh, EMZetaHighEval and
    EMZetaHighCheck, the reused ArbEconomics soundness anchors, and the named theorems of the three
    kernel-checked instances (t = 10000, 30000, 280000).  Every line must read
        [propext, Classical.choice, Quot.sound]
    or a SUBSET of it.  An instance's `zeta_box` depends on every chunk / invariant theorem of that
    instance, so its axiom line covers them transitively.
    Not a default target: building it only prints axiom lines.

    conjecture1_proved = False.
-/
import EMZetaHighK_T10000
import EMZetaHighK_T30000
import EMZetaHighK_T280000

-- EMZetaHigh (the general-order Euler-Maclaurin identity and remainder, any K)
#print axioms ZetaReflection.EMHigh.poch_zero
#print axioms ZetaReflection.EMHigh.poch_succ
#print axioms ZetaReflection.EMHigh.norm_poch_succ
#print axioms ZetaReflection.EMHigh.emC_succ
#print axioms ZetaReflection.EMHigh.norm_emC
#print axioms ZetaReflection.EMHigh.emC_one
#print axioms ZetaReflection.EMHigh.hasDerivAt_emTerm
#print axioms ZetaReflection.EMHigh.sawBernoulli_bounded
#print axioms ZetaReflection.EMHigh.emTail_integrableOn
#print axioms ZetaReflection.EMHigh.em_tail_step
#print axioms ZetaReflection.EMHigh.emTail_unroll_step
#print axioms ZetaReflection.EMHigh.emTail_unroll
#print axioms ZetaReflection.EMHigh.em_zeta_order
#print axioms ZetaReflection.EMHigh.emTail_norm_le
#print axioms ZetaReflection.EMHigh.abs_bernoulliFun_even_le
#print axioms ZetaReflection.EMHigh.abs_sawBernoulli_even_le
#print axioms ZetaReflection.EMHigh.hasSum_one_div_pow_le
#print axioms ZetaReflection.EMHigh.abs_bernoulliFun_odd_le
#print axioms ZetaReflection.EMHigh.abs_sawBernoulli_odd_le
#print axioms ZetaReflection.EMHigh.emFinite_eq_emFiniteM
#print axioms ZetaReflection.EMHigh.em_zeta_orderK_enclosure
#print axioms ZetaReflection.EMHigh.emFiniteM_odd_eq
#print axioms ZetaReflection.EMHigh.em_zeta_orderK_enclosure_odd
#print axioms ZetaReflection.EMHigh.norm_poch_sq
#print axioms ZetaReflection.EMHigh.norm_poch_le
#print axioms ZetaReflection.EMHigh.em_line_remainder_le
#print axioms ZetaReflection.EMHigh.em_line_remainder_odd_le
#print axioms ZetaReflection.EMHigh.poch_re_im
#print axioms ZetaReflection.EMHigh.emCorr_re_im
#print axioms ZetaReflection.EMHigh.bernoulli'_five
#print axioms ZetaReflection.EMHigh.bernoulli'_seven
#print axioms ZetaReflection.EMHigh.bernoulli'_nine
#print axioms ZetaReflection.EMHigh.bernoulli'_eleven
#print axioms ZetaReflection.EMHigh.bernoulli'_six
#print axioms ZetaReflection.EMHigh.bernoulli'_eight
#print axioms ZetaReflection.EMHigh.bernoulli'_ten
#print axioms ZetaReflection.EMHigh.bernoulli'_twelve
#print axioms ZetaReflection.EMHigh.bernoulli_four'
#print axioms ZetaReflection.EMHigh.bernoulli_six'
#print axioms ZetaReflection.EMHigh.bernoulli_eight'
#print axioms ZetaReflection.EMHigh.bernoulli_ten'
#print axioms ZetaReflection.EMHigh.bernoulli_twelve'
#print axioms ZetaReflection.EMHigh.bernoulli_odd_vanish

-- EMZetaHighEval (the evaluator bridge)
#print axioms ArbEcon.OrderK.sOf_eq
#print axioms ArbEcon.OrderK.emFinite_line_split
#print axioms ArbEcon.OrderK.emCorr_line_re_im
#print axioms ArbEcon.OrderK.zeta_ballK
#print axioms ArbEcon.OrderK.zetaK_re_bounds
#print axioms ArbEcon.OrderK.zetaK_im_bounds

-- EMZetaHighCheck (the kernel-only assembly)
#print axioms ArbEcon.OrderK.valid64
#print axioms ArbEcon.OrderK.betaN_spec
#print axioms ArbEcon.OrderK.gpoch_succ
#print axioms ArbEcon.OrderK.pochRI_eq_gpoch
#print axioms ArbEcon.OrderK.gsum_eq
#print axioms ArbEcon.OrderK.corr_eq
#print axioms ArbEcon.OrderK.pochNormSq_eq_pnK
#print axioms ArbEcon.OrderK.remEven_sound
#print axioms ArbEcon.OrderK.remOdd_sound
#print axioms ArbEcon.OrderK.real_le_of_int_le
#print axioms ArbEcon.OrderK.checkCore_sound
#print axioms ArbEcon.OrderK.checkK_sound

-- reused ArbEconomics soundness anchors (Probes/, promoted to libs by this lane)
#print axioms ArbEcon.chunk_sound
#print axioms ArbEcon.run_sound
#print axioms ArbEcon.step_sound
#print axioms ArbEcon.inv_init
#print axioms ArbEcon.trig_sound
#print axioms ArbEcon.psum_succ

-- instance T10000
#print axioms ArbEcon.IKK_T10000.ht
#print axioms ArbEcon.IKK_T10000.valid
#print axioms ArbEcon.IKK_T10000.chunk_0
#print axioms ArbEcon.IKK_T10000.chunk_N
#print axioms ArbEcon.IKK_T10000.inv_N
#print axioms ArbEcon.IKK_T10000.check
#print axioms ArbEcon.IKK_T10000.zeta_box
#print axioms ArbEcon.IKK_T10000.zeta_re
#print axioms ArbEcon.IKK_T10000.zeta_im

-- instance T30000
#print axioms ArbEcon.IKK_T30000.ht
#print axioms ArbEcon.IKK_T30000.valid
#print axioms ArbEcon.IKK_T30000.chunk_0
#print axioms ArbEcon.IKK_T30000.chunk_N
#print axioms ArbEcon.IKK_T30000.inv_N
#print axioms ArbEcon.IKK_T30000.check
#print axioms ArbEcon.IKK_T30000.zeta_box
#print axioms ArbEcon.IKK_T30000.zeta_re
#print axioms ArbEcon.IKK_T30000.zeta_im

-- instance T280000
#print axioms ArbEcon.IKK_T280000.ht
#print axioms ArbEcon.IKK_T280000.valid
#print axioms ArbEcon.IKK_T280000.chunk_0
#print axioms ArbEcon.IKK_T280000.chunk_N
#print axioms ArbEcon.IKK_T280000.inv_N
#print axioms ArbEcon.IKK_T280000.check
#print axioms ArbEcon.IKK_T280000.zeta_box
#print axioms ArbEcon.IKK_T280000.zeta_re
#print axioms ArbEcon.IKK_T280000.zeta_im
