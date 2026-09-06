"""Tests for winding_count numeric core (Task 3).

Toy polynomials with known winding numbers, plus negative-control refusals.
"""
from __future__ import annotations

from fractions import Fraction

import pytest


def _poly_boundary(box, n_per_side, poly):
    """Build an exact rational boundary cycle for a polynomial on a box boundary.

    Each sample is a degenerate (point) enclosure box: lo == hi == value.
    The boundary traverses: bottom (left to right), right (bottom to top),
    top (right to left), left (top to bottom).

    Returns a closed cycle: last sample == first sample.

    Args:
        box: (lo_re, hi_re, lo_im, hi_im) as Fraction-compatible values.
        n_per_side: number of sample points per side (exclusive of corners, so
            n_per_side+1 intervals, n_per_side+2 points including both endpoints
            -- we use n_per_side+1 steps per side, endpoints included).
        poly: callable z -> complex, evaluated at rational complex z.

    Returns:
        list of (param, ((lo_re, hi_re), (lo_im, hi_im))) with Fraction values.
    """
    lo_re, hi_re, lo_im, hi_im = (Fraction(v) for v in box)
    n = n_per_side  # steps per side

    def make_box(z_val):
        re = Fraction(z_val.real).limit_denominator(10 ** 15)
        im = Fraction(z_val.imag).limit_denominator(10 ** 15)
        return (re, re), (im, im)

    samples = []
    param = Fraction(0)

    # Bottom side: left to right, y = lo_im
    for k in range(n):
        t = Fraction(k, n)
        re = lo_re + t * (hi_re - lo_re)
        z = complex(float(re), float(lo_im))
        w = poly(z)
        samples.append((param, make_box(w)))
        param += Fraction(1, 4 * n)

    # Right side: bottom to top, x = hi_re
    for k in range(n):
        t = Fraction(k, n)
        im = lo_im + t * (hi_im - lo_im)
        z = complex(float(hi_re), float(im))
        w = poly(z)
        samples.append((param, make_box(w)))
        param += Fraction(1, 4 * n)

    # Top side: right to left, y = hi_im
    for k in range(n):
        t = Fraction(k, n)
        re = hi_re + t * (lo_re - hi_re)
        z = complex(float(re), float(hi_im))
        w = poly(z)
        samples.append((param, make_box(w)))
        param += Fraction(1, 4 * n)

    # Left side: top to bottom, x = lo_re
    for k in range(n):
        t = Fraction(k, n)
        im = hi_im + t * (lo_im - hi_im)
        z = complex(float(lo_re), float(im))
        w = poly(z)
        samples.append((param, make_box(w)))
        param += Fraction(1, 4 * n)

    # Close the cycle: append copy of first point with param=1
    first = samples[0]
    samples.append((Fraction(1), first[1]))

    return samples


def test_winding_number_z_squared_is_two():
    # f(z)=z^2 on a box around 0 winds twice
    box = (Fraction(-1), Fraction(1), Fraction(-1), Fraction(1))
    samples = _poly_boundary(box, 8, lambda z: z * z)
    from telperion.emit_winding_count import winding_number

    assert winding_number(samples) == 2


def test_winding_number_zero_free_is_zero():
    # f(z)=z-10 on a box near 0 (10 not enclosed) winds zero times
    box = (Fraction(-1), Fraction(1), Fraction(-1), Fraction(1))
    samples = _poly_boundary(box, 8, lambda z: z - 10)
    from telperion.emit_winding_count import winding_number

    assert winding_number(samples) == 0


def test_winding_count_refuses_box_containing_zero():
    from telperion.emit_winding_count import winding_count_certificate

    box = (0, 1, 0, 1)
    bad = [(0, ((-1, 1), (-1, 1)))]  # straddles 0
    with pytest.raises(ValueError, match="contains 0|straddle"):
        winding_count_certificate(box, bad * 2)


def test_winding_number_z_is_one():
    # f(z)=z winds once around 0
    box = (Fraction(-1), Fraction(1), Fraction(-1), Fraction(1))
    samples = _poly_boundary(box, 8, lambda z: z)
    from telperion.emit_winding_count import winding_number

    assert winding_number(samples) == 1


def test_winding_number_z_cubed_is_three():
    # f(z)=z^3 winds three times
    box = (Fraction(-1), Fraction(1), Fraction(-1), Fraction(1))
    samples = _poly_boundary(box, 12, lambda z: z ** 3)
    from telperion.emit_winding_count import winding_number

    assert winding_number(samples) == 3


def test_half_plane_witness_adjacent_first_quadrant():
    # Two boxes both in the first quadrant share the (1,1) witness direction
    from fractions import Fraction
    from telperion.emit_winding_count import _half_plane_witness

    box_a = ((Fraction(1), Fraction(2)), (Fraction(1), Fraction(2)))
    box_b = ((Fraction(2), Fraction(3)), (Fraction(1), Fraction(3)))
    w = _half_plane_witness(box_a, box_b)
    assert w is not None


def test_half_plane_witness_opposite_boxes_returns_none():
    # Boxes on opposite sides of 0 should have no common half-plane witness
    from fractions import Fraction
    from telperion.emit_winding_count import _half_plane_witness

    # box_a in Q1, box_b in Q3 -- no single direction has all corners positive
    box_a = ((Fraction(1), Fraction(2)), (Fraction(1), Fraction(2)))
    box_b = ((Fraction(-3), Fraction(-1)), (Fraction(-3), Fraction(-1)))
    w = _half_plane_witness(box_a, box_b)
    assert w is None


def test_winding_count_certificate_zero_free():
    # A curve that does not straddle 0 and has witnesses -> certificate produced
    from fractions import Fraction
    from telperion.emit_winding_count import winding_count_certificate

    box = (Fraction(-1), Fraction(1), Fraction(-1), Fraction(1))
    # z-10 stays in the half-plane Re(w) < 0 so witnesses always exist
    samples = _poly_boundary(box, 8, lambda z: z - 10)
    cert = winding_count_certificate(box, samples)
    assert cert.n == 0


def test_winding_count_certificate_missing_witness_raises():
    # A two-step cycle where step crosses 0 should raise (no half-plane witness)
    from fractions import Fraction
    from telperion.emit_winding_count import winding_count_certificate

    box = (Fraction(1), Fraction(2), Fraction(1), Fraction(2))
    # Two boxes on opposite sides: Q1 then Q3 -> no witness
    sample_a = (Fraction(0), ((Fraction(1), Fraction(2)), (Fraction(1), Fraction(2))))
    sample_b = (Fraction(Fraction(1, 2)), ((Fraction(-3), Fraction(-1)), (Fraction(-3), Fraction(-1))))
    sample_c = (Fraction(1), ((Fraction(1), Fraction(2)), (Fraction(1), Fraction(2))))  # close cycle
    with pytest.raises(ValueError):
        winding_count_certificate(box, [sample_a, sample_b, sample_c])
