/-  H11K_AxiomGuard.lean -- lane H11K: `#print axioms` of every theorem of the lane, the capstone
    statement-shape check, and kernel NEGATIVE CONTROLS.

    Expected: every line within [propext, Classical.choice, Quot.sound].
    conjecture1_proved = False.  Finite verification up to a fixed height only.
-/
import H11K_Turing
import H11K_EdgeSplit
import H11K_Edge_T11004
import H11K_Slab_U11004
import RS5_Band_T8000Lo_C0
import RS5_Band_T8000Hi_C0
import H11K_Line
import H11K_h11000

open Arb4 Arb4.Q

/-! ## The capstone: statement shape (hypothesis-free, the TARGET statement verbatim) -/

example : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 11000 → ρ.re = 1 / 2 :=
  H11K_h11000.all_nontrivial_zeros_up_to_height_11000

#print axioms H11K_h11000.all_nontrivial_zeros_up_to_height_11000
#print axioms H11K_h11000.all_nontrivial_zeros_up_to_height_11004

/-! ### H11K_Turing -/
#print axioms H11K.band_count_eq_sharp
#print axioms H11K.turing_band_on_line_sharp
#print axioms H11K.stmt_of_validS
#print axioms H11K.validS_of_sqrt
#print axioms H11K.validS_of_B
#print axioms H11K.boxCert_of_parts_sharp

/-! ### H11K_EdgeSplit -/
#print axioms H11K.edgeOK_of_split
#print axioms H11K.edge_sound_of_split

/-! ### H11K_Edge_T11004 -/
#print axioms H11K.Edge.E_T11004_rest
#print axioms H11K.Edge.E_T11004_p0
#print axioms H11K.Edge.E_T11004_p1
#print axioms H11K.Edge.E_T11004_p2
#print axioms H11K.Edge.E_T11004_p3
#print axioms H11K.Edge.E_T11004_p4
#print axioms H11K.Edge.E_T11004_p5
#print axioms H11K.Edge.E_T11004_p6
#print axioms H11K.Edge.E_T11004_p7
#print axioms H11K.Edge.E_T11004_p8
#print axioms H11K.Edge.E_T11004_p9
#print axioms H11K.Edge.E_T11004_p10
#print axioms H11K.Edge.E_T11004_p11
#print axioms H11K.Edge.E_T11004_p12
#print axioms H11K.Edge.E_T11004_p13
#print axioms H11K.Edge.E_T11004_p14
#print axioms H11K.Edge.E_T11004_p15
#print axioms H11K.Edge.E_T11004_p16
#print axioms H11K.Edge.E_T11004_p17
#print axioms H11K.Edge.E_T11004_p18
#print axioms H11K.Edge.E_T11004_p19
#print axioms H11K.Edge.E_T11004_p20
#print axioms H11K.Edge.E_T11004_p21
#print axioms H11K.Edge.E_T11004_p22
#print axioms H11K.Edge.E_T11004_p23
#print axioms H11K.Edge.E_T11004_p24
#print axioms H11K.Edge.E_T11004_pieces
#print axioms H11K.Edge.E_T11004_hAH

/-! ### H11K_Slab_U11004 -/
#print axioms H11K.Slab.S_U11004_ok
#print axioms H11K.Slab.S_U11004_clear

/-! ### RS5_Band_T8000Lo_C0 -/
#print axioms RS5.BandT8000Lo.C0.ok
#print axioms RS5.BandT8000Lo.C0.count
#print axioms RS5.BandT8000Lo.C0.last_eq
#print axioms RS5.BandT8000Lo.C0.t0_eq
#print axioms RS5.BandT8000Lo.C0.t1_eq
#print axioms RS5.BandT8000Lo.C0.zeros

/-! ### RS5_Band_T8000Hi_C0 -/
#print axioms RS5.BandT8000Hi.C0.ok
#print axioms RS5.BandT8000Hi.C0.count
#print axioms RS5.BandT8000Hi.C0.last_eq
#print axioms RS5.BandT8000Hi.C0.t0_eq
#print axioms RS5.BandT8000Hi.C0.t1_eq
#print axioms RS5.BandT8000Hi.C0.zeros

/-! ### H11K_Line -/
#print axioms H11K.Line.zeros_lo
#print axioms H11K.Line.zeros_hi
#print axioms H11K.Line.zeros
#print axioms H11K.Line.hLine

/-! ### H11K_h11000 -/
#print axioms H11K_h11000.hs1B
#print axioms H11K_h11000.chk
#print axioms H11K_h11000.box
#print axioms H11K_h11000.haC_11004
#print axioms H11K_h11000.bnd_mono
#print axioms H11K_h11000.segment_8000_11004
#print axioms H11K_h11000.all_nontrivial_zeros_up_to_height_11004
#print axioms H11K_h11000.all_nontrivial_zeros_up_to_height_11000

/-! ## Negative controls (each `= false` by the kernel) -/

/-- The OLD pins (`3.14 < π < 3.1416`, `Arb4.validB`) REJECT this wide band: the reason for H11K_Turing. -/
example : Arb4.validB (Q.frac 31851 4) (Q.ofNat 11004) (Q.frac 75867 8) (Q.frac 147987481 64) 3541
    H11K_h11000.E = false := by decide +kernel

/-- The sharp pins reject a count one too high. -/
example : H11K.validBS (Q.frac 31851 4) (Q.ofNat 11004) (Q.frac 75867 8) (Q.frac 147987481 64) 3542
    H11K_h11000.E = false := by decide +kernel

/-- ... and one too low. -/
example : H11K.validBS (Q.frac 31851 4) (Q.ofNat 11004) (Q.frac 75867 8) (Q.frac 147987481 64) 3540
    H11K_h11000.E = false := by decide +kernel

/-- A ball too small to cover the rectangle is rejected. -/
example : H11K.validBS (Q.frac 31851 4) (Q.ofNat 11004) (Q.frac 75867 8) (Q.frac 147987225 64) 3541
    H11K_h11000.E = false := by decide +kernel

/-- The top edge with its enclosure shifted by 1/10 is rejected (the `edgeRest` final inequalities). -/
example : H11K.edgeRest { H11K.Edge.E_T11004 with Lo := Q.add H11K.Edge.E_T11004.Lo (Q.frac 1 10) } = false := by
  decide +kernel
