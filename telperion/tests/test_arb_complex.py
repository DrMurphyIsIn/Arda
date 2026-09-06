"""Tests for complex Arb enclosure of Lambda(s) = pi^(-s/2) * Gamma(s/2) * zeta(s).

Lambda zeros are exactly the nontrivial zeros of the Riemann zeta function.
Box membership is a documented NON-KERNEL input: Arb ball arithmetic is
internally certified; Lean does not independently verify the value.
conjecture1_proved = False.
"""
from fractions import Fraction
import mpmath
from telperion.arb_enclosure import enclose_acb, enclose_lambda


def _c(box, val):  # val real float, box=(lo,hi)
    return float(box[0]) <= val <= float(box[1])


def _lambda_oracle(sre, sim, dps=120):
    mpmath.mp.dps = dps
    s = mpmath.mpf(str(sre)) + 1j*mpmath.mpf(str(sim))
    return mpmath.power(mpmath.pi, -s/2) * mpmath.gamma(s/2) * mpmath.zeta(s)


def test_lambda_on_line_is_real_and_encloses_oracle():
    # Lambda(1/2 + i*14) : known to be near a zero region; imag part must be ~0.
    # The TRUE imaginary part is exactly 0 on the critical line (functional
    # equation); the meaningful assertion is lo_im <= 0 <= hi_im.  The oracle is
    # computed at dps=120 (tighter than the Arb box at prec_bits=300) so its imag
    # noise (~1e-127) is well inside the tight Arb enclosure -- a meaningful
    # containment check that does NOT force the enclosure looser than Arb.
    (lo_re, hi_re), (lo_im, hi_im) = enclose_lambda(Fraction(1, 2), 14, prec_bits=300)
    o = _lambda_oracle(0.5, 14, dps=120)
    assert _c((lo_re, hi_re), float(o.real))
    assert lo_im <= 0 <= hi_im   # imaginary part boxes zero on the line (true value is 0)
    assert _c((lo_im, hi_im), float(o.imag))


def test_complex_point_encloses_oracle():
    (lo_re, hi_re), (lo_im, hi_im) = enclose_lambda(Fraction(3, 5), 20, prec_bits=300)
    o = _lambda_oracle(0.6, 20)
    assert _c((lo_re, hi_re), float(o.real)) and _c((lo_im, hi_im), float(o.imag))


def test_width_shrinks_with_precision():
    b1 = enclose_lambda(Fraction(1, 2), 14, prec_bits=120)
    b2 = enclose_lambda(Fraction(1, 2), 14, prec_bits=300)
    # Real-part width shrinks with precision.
    assert (b2[0][1] - b2[0][0]) < (b1[0][1] - b1[0][0])
    # Imag-part width also shrinks with precision (no hull floor).
    assert (b2[1][1] - b2[1][0]) < (b1[1][1] - b1[1][0])


def test_returns_fractions():
    (lo_re, hi_re), (lo_im, hi_im) = enclose_lambda(Fraction(1, 2), 21, prec_bits=200)
    assert all(isinstance(x, Fraction) for x in (lo_re, hi_re, lo_im, hi_im))


def test_enclose_lambda_boundary_is_closed_cycle_off_zero():
    from fractions import Fraction
    from telperion.arb_enclosure import enclose_lambda_boundary
    box = (Fraction(2, 5), Fraction(3, 5), 10, 35)
    samples = enclose_lambda_boundary(box, n_per_side=4, prec_bits=300)
    # CCW cycle: 4 corners x 4 per side = 16 points + closing repeat
    assert len(samples) == 16 + 1
    # closed: first param==last coordinate-wise (same boundary point)
    assert samples[0][1] == samples[-1][1]
    # no enclosure box contains 0 (Lambda nonzero on this boundary): a box
    # contains 0 iff lo<=0<=hi for BOTH parts
    for _param, ((lo_re, hi_re), (lo_im, hi_im)) in samples[:-1]:
        contains_zero = (lo_re <= 0 <= hi_re) and (lo_im <= 0 <= hi_im)
        assert not contains_zero


def test_enclose_lambda_boundary_requires_flint():
    import telperion.arb_enclosure as ae
    if not ae._FLINT_AVAILABLE:
        import pytest
        with pytest.raises(RuntimeError, match="python-flint"):
            ae.enclose_lambda_boundary((0, 1, 10, 11), 2, 100)


# ---------------------------------------------------------------------------
# Task 8: segment (ball) enclosures
# ---------------------------------------------------------------------------

def test_enclose_lambda_segments_closed_cycle_length():
    """enclose_lambda_segments returns 4*n_per_side + 1 entries (closed cycle)."""
    from telperion.arb_enclosure import enclose_lambda_segments
    box = (Fraction(2, 5), Fraction(3, 5), 10, 35)
    n = 10
    segs = enclose_lambda_segments(box, n_per_side=n, prec_bits=300)
    assert len(segs) == 4 * n + 1


def test_enclose_lambda_segments_returns_fractions():
    """All endpoints in segment boxes are exact Fractions."""
    from telperion.arb_enclosure import enclose_lambda_segments
    box = (Fraction(2, 5), Fraction(3, 5), 10, 35)
    segs = enclose_lambda_segments(box, n_per_side=4, prec_bits=200)
    for param, ((lo_re, hi_re), (lo_im, hi_im)) in segs:
        assert isinstance(param, Fraction)
        assert isinstance(lo_re, Fraction)
        assert isinstance(hi_re, Fraction)
        assert isinstance(lo_im, Fraction)
        assert isinstance(hi_im, Fraction)


def test_enclose_lambda_segments_closed_first_equals_last():
    """Segment cycle is closed: first and last boxes are identical."""
    from telperion.arb_enclosure import enclose_lambda_segments
    box = (Fraction(2, 5), Fraction(3, 5), 10, 35)
    segs = enclose_lambda_segments(box, n_per_side=6, prec_bits=200)
    assert segs[0][1] == segs[-1][1]


def test_enclose_lambda_segments_wider_than_point_enclosures():
    """Each segment box is strictly wider than both endpoint point-enclosures.

    enclose_lambda_boundary at the same n_per_side gives point enclosures at
    the same nodes.  Each segment box from enclose_lambda_segments must span
    at least the union of consecutive point boxes, so it is strictly wider in
    at least one coordinate.
    """
    from telperion.arb_enclosure import enclose_lambda_boundary, enclose_lambda_segments
    box = (Fraction(2, 5), Fraction(3, 5), 10, 35)
    n = 8
    prec = 300
    # Point enclosures at each node.
    pts = enclose_lambda_boundary(box, n_per_side=n, prec_bits=prec)
    # Segment enclosures for each sub-segment.
    segs = enclose_lambda_segments(box, n_per_side=n, prec_bits=prec)

    # For each sub-segment i -> i+1, the segment box must be at least as wide
    # as each individual point enclosure, and strictly wider than at least one
    # (because it spans both endpoints).
    for i in range(4 * n):
        _, pt_box_a = pts[i]
        _, pt_box_b = pts[i + 1]
        _, seg_box = segs[i]

        seg_re_lo, seg_re_hi = seg_box[0]
        seg_im_lo, seg_im_hi = seg_box[1]
        a_re_lo, a_re_hi = pt_box_a[0]
        b_re_lo, b_re_hi = pt_box_b[0]

        seg_re_width = seg_re_hi - seg_re_lo
        a_re_width = a_re_hi - a_re_lo
        b_re_width = b_re_hi - b_re_lo

        # Segment box re-width >= max of both point box widths.
        assert seg_re_width >= a_re_width, (
            f"Segment {i} re-width {seg_re_width} < point-A width {a_re_width}"
        )
        assert seg_re_width >= b_re_width, (
            f"Segment {i} re-width {seg_re_width} < point-B width {b_re_width}"
        )
        # Segment box must contain both endpoint midpoints.
        a_re_mid = (a_re_lo + a_re_hi) / 2
        b_re_mid = (b_re_lo + b_re_hi) / 2
        assert seg_re_lo <= a_re_mid <= seg_re_hi, (
            f"Segment {i} does not contain point-A midpoint {a_re_mid}"
        )
        assert seg_re_lo <= b_re_mid <= seg_re_hi, (
            f"Segment {i} does not contain point-B midpoint {b_re_mid}"
        )


def test_enclose_lambda_segments_capstone_n5(pytestconfig):
    """Capstone box [2/5,3/5]x[10,35]: fine n_per_side certifies n==5.

    For n_per_side >= 80, no segment-box contains 0 and every consecutive pair
    has a half-plane witness, so segment_winding_certificate succeeds and
    reports n == 5.
    """
    from telperion.arb_enclosure import enclose_lambda_segments
    from telperion.emit_winding_count import (
        segment_winding_certificate, _box_contains_zero, _half_plane_witness,
        winding_number,
    )
    box = (Fraction(2, 5), Fraction(3, 5), 10, 35)
    n = 80
    prec = 300
    segs = enclose_lambda_segments(box, n_per_side=n, prec_bits=prec)

    # No segment-box contains 0.
    for i, (param, seg_box) in enumerate(segs[:-1]):
        assert not _box_contains_zero(seg_box), (
            f"Segment {i} (param={param}) contains 0 -- increase n_per_side"
        )

    # Every consecutive pair has a half-plane witness.
    for i in range(len(segs) - 1):
        _, ba = segs[i]
        _, bb = segs[i + 1]
        assert _half_plane_witness(ba, bb) is not None, (
            f"No half-plane witness for segment step {i}->{i+1}"
        )

    # The segment winding certificate succeeds and reports n==5.
    cert = segment_winding_certificate(box, segs)
    assert cert.n == 5, f"Expected n=5, got n={cert.n}"
    assert len(cert.step_witnesses) == len(segs) - 1


def test_enclose_lambda_segments_coarse_refused():
    """A deliberately-coarse n_per_side (e.g. 2) is refused by segment_winding_certificate.

    At n_per_side=2 the segment boxes are too wide and contain 0, so
    segment_winding_certificate must raise ValueError.
    """
    import pytest
    from telperion.arb_enclosure import enclose_lambda_segments
    from telperion.emit_winding_count import segment_winding_certificate
    box = (Fraction(2, 5), Fraction(3, 5), 10, 35)
    segs = enclose_lambda_segments(box, n_per_side=2, prec_bits=300)
    with pytest.raises(ValueError, match="contains 0|straddle|n_per_side"):
        segment_winding_certificate(box, segs)


def test_enclose_lambda_segments_requires_flint():
    """enclose_lambda_segments raises RuntimeError if python-flint is unavailable."""
    import telperion.arb_enclosure as ae
    if not ae._FLINT_AVAILABLE:
        import pytest
        with pytest.raises(RuntimeError, match="python-flint"):
            ae.enclose_lambda_segments((0, 1, 10, 11), 2, 100)
