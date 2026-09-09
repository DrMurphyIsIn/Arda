/-  AxiomGuardRHInBox -- CI kernel-axiom guard for the RH-in-box family.

    Mirrors `AxiomGuardDlvp.lean` (zero_free_bridge) for the zeta_zero_localization
    family.  Like that file, this is NOT a `lean_lib`; CI runs it explicitly with

        lake env lean AxiomGuardRHInBox.lean

    AFTER `lake build`, and FAILS if any `#print axioms` output mentions `sorryAx`.

    Guarded anchors:
      * RHInBox.rh_in_box_of_certificate -- the GENERIC box capstone: for any box
        corners, Blaschke ball, on-line-zero count, and Arb boundary bundle, every zero
        of riemannZeta in the box lies on Re = 1/2.  Kernel-verified reduction;
        Arb-non-kernel inputs enter only through the `harb` hypothesis.
      * RHInBox.rh_in_box_10_35 -- the REGRESSION instantiation: the generic theorem
        at sigma0=2/5, sigma1=3/5, T0=10, T1=35, cB, R=13, N=5 reproduces the merged
        BoxLocalization capstone conclusion.
      * RHInBox_2d5_3d5_0_100.rh_in_box_2d5_3d5_0_100 -- the T=100 BOX MILESTONE:
        the generic theorem instantiated at [2/5,3/5]x[0,100] with N=29 on-line zeros.
      * AllZerosUpToHeight.all_nontrivial_zeros_up_to_height_on_line -- the GENERIC
        COMBINATION theorem: composes ZetaZeroConfinement (dVP+FE band) with the
        box-localization certificate to conclude every nontrivial zeta zero up to
        height T lies on Re = 1/2.
      * AllZeros_h100.all_nontrivial_zeros_up_to_height_100 -- the CONCRETE T=100
        certificate: ALL nontrivial zeta zeros up to height 100 lie on Re = 1/2.
        Composes ZetaZeroConfinement.zero_in_band (band [1/10^6, 1-1/10^6]) with the
        wide-box atom RHInBox_1d1000000_999999d1000000_0_100 (winding N=29).
      * NoZerosInBox_1d1000_999d1000_0_55d16.no_zeros_in_box_1d1000_999d1000_0_55d16 --
        the EMPTY-BAND (zero-free) certificate: the box [1/1000, 999/1000] x [0, 55/16]
        has boundary winding N=0, so it holds no zeta zero.  Instantiates
        zeta_count_eq_winding_generic at N=0 (empty divisor support); the box-driver half
        of the 55/16 no-low-zeros closure.
      * NoZerosInBox_0_1d1000_0_55d16.no_zeros_in_box_0_1d1000_0_55d16 -- the LEFT-SLIVER
        (zero-free) certificate: [0, 1/1000] x [0, 55/16], winding N=0.  With the band cert
        this clears [0, 999/1000] x [0, 55/16]; the reflection rho -> 1 - conj(rho) carries
        the right sliver here, completing the full-strip clearing for
        no_low_zeros_of_strip_clear.

      * AllZeros_h200.all_nontrivial_zeros_up_to_height_200 -- the BAND-STACKED T=200
        certificate: two per-band box atoms ([0,100] N=29, [100,200] N=50) glued by
        rh_box_two_bands, composed with zero_in_band at a=1/10^6, T=200 (haC_200 in-kernel).

    All are kernel-verified reductions.  conjecture1_proved = False (NOT a proof of RH).
    Axioms expected: {propext, Classical.choice, Quot.sound} -- no sorryAx.
-/
import RHInBox
import RHInBox_2d5_3d5_0_100
import AllZerosUpToHeight
import AllZeros_h100
import RHInBoxBands
import NoZerosInBox_1d1000_999d1000_0_55d16
import NoZerosInBox_0_1d1000_0_55d16
import RHInBox_1d1000000_999999d1000000_100_200
import AllZeros_h200

#print axioms RHInBox.rh_in_box_of_certificate
#print axioms RHInBox.rh_in_box_10_35
#print axioms RHInBox_2d5_3d5_0_100.rh_in_box_2d5_3d5_0_100
#print axioms AllZerosUpToHeight.all_nontrivial_zeros_up_to_height_on_line
#print axioms AllZeros_h100.all_nontrivial_zeros_up_to_height_100
#print axioms RHInBoxBands.rh_box_two_bands
#print axioms RHInBoxBands.rh_box_of_bands
#print axioms RHInBoxBands.rh_full_box_of_left_half
#print axioms ZetaZeroConfinement.zeta_zero_re_mem_strip
#print axioms ZetaZeroConfinement.no_low_zeros_of_strip_clear
#print axioms NoZerosInBox_1d1000_999d1000_0_55d16.no_zeros_in_box_1d1000_999d1000_0_55d16
#print axioms NoZerosInBox_0_1d1000_0_55d16.no_zeros_in_box_0_1d1000_0_55d16
#print axioms RHInBox_1d1000000_999999d1000000_100_200.rh_in_box_1d1000000_999999d1000000_100_200
#print axioms AllZeros_h200.all_nontrivial_zeros_up_to_height_200
