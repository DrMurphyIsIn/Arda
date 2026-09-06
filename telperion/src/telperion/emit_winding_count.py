"""Winding-count numeric core -- certificate + integer N + refusals.

Computes the integer winding number of an ordered cycle of complex enclosure boxes
about 0, and produces a certificate with per-step half-plane witnesses.

The cycle format matches the output of Task 2's ``enclose_lambda_boundary``:
  list of (param, ((lo_re, hi_re), (lo_im, hi_im))) -- Fraction-valued, closed
  (last sample has the same box as the first).

This file is PURE NUMERIC (certificate + algorithm).  The emitter class/family
are in Task 4.  conjecture1_proved = False (NOT a proof of RH).
"""
from __future__ import annotations

import math
from dataclasses import dataclass
from fractions import Fraction
from typing import Sequence

# ---------------------------------------------------------------------------
# Types
# ---------------------------------------------------------------------------

# A single sample point from the boundary cycle (output of Task 2).
# param: Fraction in [0,1]
# box: ((lo_re, hi_re), (lo_im, hi_im))  -- all Fraction
_Box = tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction]]
_Sample = tuple[Fraction, _Box]


# ---------------------------------------------------------------------------
# Fixed rational test directions for the half-plane witness search.
# Each entry is (d_re, d_im) representing the direction d = d_re + i*d_im.
# The inner product of a complex number w with direction d is Re(conj(d)*w)
# = d_re * w_re + d_im * w_im.
# ---------------------------------------------------------------------------
_DIRECTIONS: tuple[tuple[Fraction, Fraction], ...] = (
    (Fraction(1), Fraction(0)),    # 1
    (Fraction(-1), Fraction(0)),   # -1
    (Fraction(0), Fraction(1)),    # i
    (Fraction(0), Fraction(-1)),   # -i
    (Fraction(1), Fraction(1)),    # 1+i
    (Fraction(1), Fraction(-1)),   # 1-i
    (Fraction(-1), Fraction(1)),   # -1+i
    (Fraction(-1), Fraction(-1)),  # -1-i
)


def _box_corners(box: _Box) -> tuple[
    tuple[Fraction, Fraction],
    tuple[Fraction, Fraction],
    tuple[Fraction, Fraction],
    tuple[Fraction, Fraction],
]:
    """Return the four corners of a box as (re, im) pairs."""
    (lo_re, hi_re), (lo_im, hi_im) = box
    return (
        (lo_re, lo_im),
        (lo_re, hi_im),
        (hi_re, lo_im),
        (hi_re, hi_im),
    )


def _inner_product(d_re: Fraction, d_im: Fraction, w_re: Fraction, w_im: Fraction) -> Fraction:
    """Compute Re(conj(d) * w) = d_re * w_re + d_im * w_im."""
    return d_re * w_re + d_im * w_im


def _half_plane_witness(box_a: _Box, box_b: _Box) -> tuple[Fraction, Fraction] | None:
    """Find a rational direction proving box_a and box_b share an open half-plane.

    Tests the eight fixed rational directions {1, -1, i, -i, 1+i, 1-i, -1+i, -1-i}.
    For each direction d, checks that ALL FOUR corners of BOTH boxes have
    strictly positive real inner product with d (exact Fraction arithmetic).
    Returns the first such direction (d_re, d_im), or None if no direction works.

    A returned witness certifies that the argument of any complex number in either
    box stays within a half-plane, so the argument increment between the two box
    centres is strictly less than pi (the winding step is unambiguous).
    """
    corners_a = _box_corners(box_a)
    corners_b = _box_corners(box_b)
    all_corners = corners_a + corners_b

    for d_re, d_im in _DIRECTIONS:
        if all(
            _inner_product(d_re, d_im, w_re, w_im) > Fraction(0)
            for w_re, w_im in all_corners
        ):
            return (d_re, d_im)

    return None


def _box_contains_zero(box: _Box) -> bool:
    """Return True if the box contains 0, i.e. both real and imaginary parts straddle 0."""
    (lo_re, hi_re), (lo_im, hi_im) = box
    return lo_re <= Fraction(0) <= hi_re and lo_im <= Fraction(0) <= hi_im


def _box_center(box: _Box) -> tuple[float, float]:
    """Return the float centre of a box as (re, im)."""
    (lo_re, hi_re), (lo_im, hi_im) = box
    return (float(lo_re + hi_re) / 2.0, float(lo_im + hi_im) / 2.0)


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

def winding_number(samples: Sequence[_Sample]) -> int:
    """Compute the integer winding number of the boundary cycle about 0.

    Algorithm: accumulate the signed argument increment between consecutive
    box CENTRES using atan2 on rational-centre floats.  Divide the total by
    2*pi and round to nearest integer.

    The float accumulation is sufficient for the integer result; exact
    arithmetic lives in the per-step half-plane witnesses.

    ``samples`` must be a closed cycle (last box == first box in content).
    """
    if len(samples) < 2:
        return 0

    total_angle = 0.0
    prev_re, prev_im = _box_center(samples[0][1])

    for _, box in samples[1:]:
        curr_re, curr_im = _box_center(box)
        # Argument increment: arg(curr) - arg(prev) normalised to (-pi, pi]
        # Use atan2(Im(curr * conj(prev)), Re(curr * conj(prev)))
        # = atan2(curr_im*prev_re - curr_re*prev_im, curr_re*prev_re + curr_im*prev_im)
        cross = curr_im * prev_re - curr_re * prev_im
        dot = curr_re * prev_re + curr_im * prev_im
        delta = math.atan2(cross, dot)
        total_angle += delta
        prev_re, prev_im = curr_re, curr_im

    return round(total_angle / (2.0 * math.pi))


@dataclass(frozen=True)
class WindingCountCertificate:
    """A verified winding-count certificate.

    Attributes:
        box: The query box as (lo_re, hi_re, lo_im, hi_im) -- 4 Fractions.
        n: The integer winding number of the boundary cycle about 0.
        step_witnesses: A tuple of length (len(samples)-1) holding the
            half-plane witness for each consecutive pair of boxes, as
            (d_re, d_im) Fraction pairs.
    """

    box: tuple[Fraction, Fraction, Fraction, Fraction]
    n: int
    step_witnesses: tuple[tuple[Fraction, Fraction], ...]


def winding_count_certificate(
    box: tuple,
    samples: Sequence[_Sample],
) -> WindingCountCertificate:
    """Build and self-check a WindingCountCertificate.

    Raises ValueError if:
    - Any sample box contains 0 (Lambda may vanish on the boundary).
    - Any consecutive pair of sample boxes lacks a half-plane witness
      (winding number would be ambiguous for that step).

    Args:
        box: The query box (lo_re, hi_re, lo_im, hi_im) -- used as metadata.
        samples: Closed boundary cycle from Task 2's ``enclose_lambda_boundary``.

    Returns:
        WindingCountCertificate with self-checked witnesses and integer n.
    """
    # Normalise box to 4-tuple of Fraction
    lo_re, hi_re, lo_im, hi_im = (Fraction(v) for v in box)
    cert_box = (lo_re, hi_re, lo_im, hi_im)

    # Check each sample box for 0-containment
    for i, (param, sample_box) in enumerate(samples):
        if _box_contains_zero(sample_box):
            (slo_re, shi_re), (slo_im, shi_im) = sample_box
            raise ValueError(
                f"Sample {i} (param={param}) contains 0: box "
                f"re=[{slo_re}, {shi_re}] im=[{slo_im}, {shi_im}] "
                f"straddles the origin -- winding_count_certificate refuses."
            )

    # Build step witnesses for each consecutive pair
    witnesses: list[tuple[Fraction, Fraction]] = []
    for i in range(len(samples) - 1):
        _, box_a = samples[i]
        _, box_b = samples[i + 1]
        w = _half_plane_witness(box_a, box_b)
        if w is None:
            raise ValueError(
                f"No half-plane witness for step {i}->{i+1}: "
                f"boxes straddle a half-plane through 0; winding is ambiguous."
            )
        witnesses.append(w)

    n = winding_number(samples)
    return WindingCountCertificate(
        box=cert_box,
        n=n,
        step_witnesses=tuple(witnesses),
    )


def certify_winding_count_point(family, pt, name):
    """Certify one winding-count instance from a family evaluated at point ``pt``.

    Expects ``family.special[1](pt)`` to return a dict with keys:
    - ``"box"``: 4-tuple (lo_re, hi_re, lo_im, hi_im)
    - ``"samples"``: closed boundary cycle (list of _Sample)

    Returns (CertifiedInstance, 1).
    """
    try:
        from .certify import CertifiedInstance
    except ImportError:
        import os
        import sys
        sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
        from telperion.certify import CertifiedInstance

    spec = family.special[1](pt)
    cert = winding_count_certificate(spec["box"], spec["samples"])
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1
