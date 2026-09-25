/-  Arb4_AxiomGuard.lean -- lane Arb4: `#print axioms` of every theorem of the checker modules
    (Arb4_Q, Arb4_Side, Arb4_Edge, Arb4_Slab, Arb4_Line, Arb4_Gamma, Arb4_Seg; appended: Arb4_SlabRows)
    and kernel NEGATIVE CONTROLS on real height-1000 certificate data: each perturbed certificate
    below is REJECTED by the same `decide +kernel` that accepts the emitted one.  Expected: every
    `#print axioms` line within [propext, Classical.choice, Quot.sound].  conjecture1_proved = False.
-/
import Arb4_h1000
import Arb4_SlabRows

open Arb4 Arb4.Q

#print axioms Arb4.Q.den_pos
#print axioms Arb4.Q.den_ne
#print axioms Arb4.Q.val_frac
#print axioms Arb4.Q.cast_den_mul
#print axioms Arb4.Q.val_add
#print axioms Arb4.Q.val_sub
#print axioms Arb4.Q.val_mul
#print axioms Arb4.Q.val_neg
#print axioms Arb4.Q.val_qabs
#print axioms Arb4.Q.val_npow
#print axioms Arb4.Q.val_div
#print axioms Arb4.Q.val_sumQ
#print axioms Arb4.Q.le_sound
#print axioms Arb4.Q.lt_sound
#print axioms Arb4.Q.val_pos
#print axioms Arb4.Q.val_nonneg
#print axioms Arb4.Q.val_ne_zero
#print axioms Arb4.Q.cv_nat
#print axioms Arb4.Q.cv_one
#print axioms Arb4.Q.cv_frac
#print axioms Arb4.Q.cv_sub
#print axioms Arb4.Q.cv_add
#print axioms Arb4.val_CpQ
#print axioms Arb4.val_betaQ
#print axioms Arb4.val_emcBQ
#print axioms Arb4.npow_two_n_pos
#print axioms Arb4.val_corrVarQ
#print axioms Arb4.val_budgetQ
#print axioms Arb4.val_pochQ
#print axioms Arb4.val_tQ
#print axioms Arb4.PieceD.val_σQ
#print axioms Arb4.PieceD.val_rQ
#print axioms Arb4.PieceD.val_GQ
#print axioms Arb4.PieceD.val_FQ
#print axioms Arb4.PieceD.val_xloQ
#print axioms Arb4.gOK_sound
#print axioms Arb4.remOK_sound
#print axioms Arb4.pieceOK_sound
#print axioms Arb4.eqB_sound
#print axioms Arb4.inRad_sound
#print axioms Arb4.runs_inv
#print axioms Arb4.cornerOK_sound
#print axioms Arb4.boxOK_sound
#print axioms Arb4.val_nonneg_iff
#print axioms Arb4.val_atanLoQ
#print axioms Arb4.val_atanHiQ
#print axioms Arb4.piL_le
#print axioms Arb4.le_piH
#print axioms Arb4.finalLo_sound
#print axioms Arb4.finalHi_sound
#print axioms Arb4.edgeOK_sound
#print axioms Arb4.slabBudget_le
#print axioms Arb4.CellD.val_σQ
#print axioms Arb4.runs_inv_cell
#print axioms Arb4.cellOK_sound
#print axioms Arb4.exists_col
#print axioms Arb4.slabOK_sound
#print axioms Arb4.allB_sound
#print axioms Arb4.bandB_sound
#print axioms Arb4.ptCheckC_spec
#print axioms Arb4.pt_inv
#print axioms Arb4.ptCheckC_sound
#print axioms Arb4.allC_append
#print axioms Arb4.bandC_of
#print axioms Arb4.bandC_sound
#print axioms Arb4.log2_mem
#print axioms Arb4.logpi_mem
#print axioms Arb4.pi_mem
#print axioms Arb4.val_pow2Q
#print axioms Arb4.pow2Q_n_pos
#print axioms Arb4.val_lserQ
#print axioms Arb4.kl2_mem
#print axioms Arb4.omx_n_pos
#print axioms Arb4.log_mem
#print axioms Arb4.odd_n_pos
#print axioms Arb4.val_atanPSQ
#print axioms Arb4.val_atanErrQ
#print axioms Arb4.two_n_pos
#print axioms Arb4.four_n_pos
#print axioms Arb4.arctan_mem
#print axioms Arb4.GamD.val_v2
#print axioms Arb4.GamD.val_vm
#print axioms Arb4.GamD.val_half
#print axioms Arb4.S2_mem
#print axioms Arb4.Sm1_mem
#print axioms Arb4.npow_two_nonneg_n
#print axioms Arb4.val_em1Q
#print axioms Arb4.val_e2Q
#print axioms Arb4.k6B_sound
#print axioms Arb4.valid_of_B
#print axioms Arb4.k6side_of_B
#print axioms Arb4.boxCert_of_parts

/-! ## Negative controls (each `= false` is decided by the kernel) -/

/-- An octant piece with the opposite octant label (`kk + 4`) is rejected. -/
example : pieceOK 520 0 156 (Q.frac 101 20) { Arb4.H1000.E_T520.pc 0 with kk := 4 } = false := by
  decide +kernel

/-- An octant piece with an error budget 1000 times too small is rejected. -/
example : pieceOK 520 0 156 (Q.frac 101 20) { Arb4.H1000.E_T520.pc 0 with FN := 52, FD := 3125000 } = false := by
  decide +kernel

/-- An edge claiming a lower bound above the certified one (`Lo := Hi`) is rejected. -/
example : edgeOK { Arb4.H1000.E_T520 with Lo := Arb4.H1000.E_T520.Hi } = false := by
  decide +kernel

/-- A slab with an error budget 1000 times too small is rejected. -/
example : slabOK { Arb4.H1000.S_U520 with FD := Arb4.H1000.S_U520.FD * 1000 } = false := by
  decide +kernel

/-- A slab claiming a taller region (`hi + 1/10`) is rejected (the cells no longer cover it). -/
example : slabOK { Arb4.H1000.S_U520 with hi := Q.add Arb4.H1000.S_U520.hi (Q.frac 1 10) } = false := by
  decide +kernel

/-- A band chunk with every claimed sign flipped is rejected. -/
example : (Arb4.H1000.B12_0.map (fun d => { d with pos := !d.pos })).all (fun d => ptCheckC d.pt)
    = false := by
  decide +kernel

/-- A band claiming one more zero than its grid shows is rejected. -/
example : H1000Line.bandOk 481 1 520 1 28 (Arb4.H1000.B12.map PtD.pt) = false := by
  decide +kernel

/-- K6b: an `L4` above the certified bracket is rejected. -/
example : k6sideB Arb4_h1000.G_T481 Arb4_h1000.G_T520 { Arb4_h1000.E12 with L4 := Arb4_h1000.E12.H4 } = false := by
  decide +kernel

/-- The pins reject a band with 3 more zeros than the argument change allows. -/
example : validB (Q.ofNat 481) (Q.ofNat 520) (Q.frac 1001 2) (Q.frac 6121 16) 30 Arb4_h1000.E12 = false := by
  decide +kernel

/-! Appended (scaling past height 2000): stacking zero-free slabs. -/
#print axioms Arb4.slabClear_join
