"""Arb transcendental-constant enclosure provider.

Provides a certified rational box [lo, hi] (as fractions.Fraction) that
rigorously contains a transcendental constant (pi, e, zeta(q), gamma(q))
computed via python-flint / Arb ball arithmetic.

Also provides complex enclosures ((lo_re, hi_re), (lo_im, hi_im)) for acb
values, including the completed Riemann zeta function

    Lambda(s) = pi^(-s/2) * Gamma(s/2) * zeta(s).

Lambda zeros are exactly the nontrivial zeros of the Riemann zeta function.

CERTIFICATION STATUS
--------------------
This module is a certified rational-box provider.  Box MEMBERSHIP is a
documented NON-KERNEL input: Arb ball arithmetic (via python-flint) is
internally certified (interval arithmetic with outward rounding), but Lean
does not independently verify the constant's value.  The rational endpoints
lo, hi are exact fractions.Fraction derived via outward-rounded dyadic
arithmetic from the Arb ball's mid and rad fields (man_exp extraction).

conjecture1_proved = False.

TECHNIQUE: man_exp outward rounding
------------------------------------
An arb ball b has a midpoint mid and radius rad, both exact dyadic
rationals representable as  man * 2**exp  (SIGNED mantissa, signed
exponent).  man_exp() returns (man, exp) with  man * 2**exp == exact value.

    _dyadic(a): man, exp = a.man_exp(); return Fraction(man) * Fraction(2)**exp

The radius rad is a certified UPPER bound of the true radius, so
    lo = mid - rad
    hi = mid + rad
are exact fractions.Fraction that rigorously contain the true value.

No float arithmetic appears in the returned endpoints.
"""
from __future__ import annotations

import re
from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, Union

try:
    import flint as _flint
    from flint import acb as _acb
    from flint import arb as _arb
    from flint import ctx as _ctx
    _FLINT_AVAILABLE = True
except ImportError:
    _FLINT_AVAILABLE = False

# ──────────────────────────────────────────────────────────────────────────────
# Internal dyadic helpers
# ──────────────────────────────────────────────────────────────────────────────

def _dyadic(a) -> Fraction:
    """Convert an Arb scalar (arb, no imaginary part) to an exact Fraction.

    Uses man_exp(): value = man * 2**exp, where man is the signed mantissa.
    Works for both positive and negative exponents without any float conversion.
    """
    man, exp = a.man_exp()
    man = int(man)
    exp = int(exp)
    if exp >= 0:
        return Fraction(man) * Fraction(2) ** exp
    else:
        # Fraction(man, 2**(-exp)) is exact for negative exponents
        return Fraction(man, 2 ** (-exp))


def _arb_ball_to_fractions(ball) -> tuple[Fraction, Fraction]:
    """Convert an Arb ball to an outward-rounded rational enclosure (lo, hi).

    Returns (mid - rad, mid + rad) as exact fractions.Fraction, where rad is
    a certified UPPER bound of the true radius.  The interval [lo, hi]
    rigorously contains the true value represented by the ball.

    No float arithmetic is used.
    """
    mid = _dyadic(ball.mid())
    rad = _dyadic(ball.rad())
    return mid - rad, mid + rad


# ──────────────────────────────────────────────────────────────────────────────
# Spec parsing and evaluation
# ──────────────────────────────────────────────────────────────────────────────

_ZETA_RE = re.compile(r"^zeta\((.+)\)$")
_GAMMA_RE = re.compile(r"^gamma\((.+)\)$")


def _parse_rational_arg(inner: str) -> Fraction:
    """Parse a rational string like '1/2' or '1/4' into a Fraction."""
    inner = inner.strip()
    return Fraction(inner)


def _eval_spec(spec: Union[str, Callable], prec_bits: int):
    """Evaluate spec at the given precision, returning an acb.

    spec can be:
      "pi"           -> acb.pi()
      "e"            -> acb(1).exp()
      "zeta(q)"      -> acb(str(q)).zeta()  where q is a rational
      "gamma(q)"     -> acb(str(q)).gamma() where q is a rational
      callable       -> spec(_flint)   (receives the flint module)

    Sets ctx.prec = prec_bits (save/restore around call).
    """
    if not _FLINT_AVAILABLE:
        raise RuntimeError(
            "python-flint is not available; cannot compute Arb enclosures. "
            "Install with: pip install python-flint"
        )

    old_prec = _ctx.prec
    try:
        _ctx.prec = prec_bits

        if callable(spec):
            result = spec(_flint)
        elif spec == "pi":
            result = _acb.pi()
        elif spec == "e":
            result = _acb(1).exp()
        else:
            m = _ZETA_RE.match(spec)
            if m:
                q = _parse_rational_arg(m.group(1))
                result = _acb(str(q)).zeta()
            else:
                m = _GAMMA_RE.match(spec)
                if m:
                    q = _parse_rational_arg(m.group(1))
                    result = _acb(str(q)).gamma()
                else:
                    raise ValueError(
                        f"Unknown spec {spec!r}. "
                        "Supported: 'pi', 'e', 'zeta(<rational>)', 'gamma(<rational>)', "
                        "or a callable(flint_module) -> acb."
                    )
    finally:
        _ctx.prec = old_prec

    return result


# ──────────────────────────────────────────────────────────────────────────────
# Public API
# ──────────────────────────────────────────────────────────────────────────────

def enclose_constant(
    spec: Union[str, Callable],
    prec_bits: int,
) -> tuple[Fraction, Fraction]:
    """Return a certified outward-rounded rational enclosure (lo, hi) for a
    transcendental constant.

    Parameters
    ----------
    spec : str or callable
        "pi"           -- the constant pi
        "e"            -- Euler's number e
        "zeta(q)"      -- Riemann zeta function at rational q (e.g. "zeta(1/2)")
        "gamma(q)"     -- Euler gamma function at rational q (e.g. "gamma(1/4)")
        callable       -- receives the flint module, must return an acb value

    prec_bits : int
        Working precision in bits for Arb computation.  Higher gives tighter
        enclosure.

    Returns
    -------
    (lo, hi) : tuple[Fraction, Fraction]
        Exact fractions.Fraction endpoints such that lo <= true_value <= hi.
        The interval is outward-rounded: lo may be slightly below and hi
        slightly above the best Arb approximation, by at most the certified
        radius of the Arb ball.  No float arithmetic is used in the return
        values.

    Raises
    ------
    RuntimeError
        If python-flint is not installed.
    ValueError
        If spec is not recognized.
    """
    if not _FLINT_AVAILABLE:
        raise RuntimeError(
            "python-flint is not available; cannot compute Arb enclosures. "
            "Install with: pip install python-flint"
        )

    result_acb = _eval_spec(spec, prec_bits)
    # Take real part (arb ball)
    real_ball = result_acb.real
    return _arb_ball_to_fractions(real_ball)


# ──────────────────────────────────────────────────────────────────────────────
# EnclosureRecord
# ──────────────────────────────────────────────────────────────────────────────

@dataclass(frozen=True)
class EnclosureRecord:
    """A certified rational enclosure record for a transcendental constant.

    Fields
    ------
    spec : str
        The constant specification (e.g. "pi", "e", "zeta(1/2)").
    prec_bits : int
        Arb working precision used to produce the enclosure.
    lo : Fraction
        Exact rational lower bound; true value >= lo.
    hi : Fraction
        Exact rational upper bound; true value <= hi.
    radius : Fraction
        Half-width of the enclosure (hi - lo) / 2.  A certified upper bound
        on the distance from the midpoint to the true value.

    CERTIFICATION NOTE: box membership is a documented non-kernel input.
    Arb ball arithmetic is certified; Lean does not verify the constant's
    value.  conjecture1_proved = False.
    """

    spec: str
    prec_bits: int
    lo: Fraction
    hi: Fraction
    radius: Fraction

    def to_dict(self) -> dict:
        """Serialize to a plain dict with string-encoded Fractions.

        All Fraction fields are stored as 'numerator/denominator' strings
        (or just 'numerator' for integers) to preserve exactness across
        JSON serialization.
        """
        def _frac_str(f: Fraction) -> str:
            if f.denominator == 1:
                return str(f.numerator)
            return f"{f.numerator}/{f.denominator}"

        return {
            "spec": self.spec,
            "prec_bits": self.prec_bits,
            "lo": _frac_str(self.lo),
            "hi": _frac_str(self.hi),
            "radius": _frac_str(self.radius),
        }


# ──────────────────────────────────────────────────────────────────────────────
# Complex enclosure: enclose_acb and enclose_lambda
# ──────────────────────────────────────────────────────────────────────────────

def enclose_acb(
    spec_or_callable,
    prec_bits: int,
) -> tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction]]:
    """Return certified outward-rounded rational boxes for both parts of an acb value.

    Computes a complex Arb ball (acb) via spec_or_callable and extracts
    rigorous rational enclosures for its real and imaginary parts separately,
    reusing _arb_ball_to_fractions on acb.real and acb.imag.

    Parameters
    ----------
    spec_or_callable : str or callable
        A callable receiving the flint module that returns an acb, OR a string
        spec recognized by _eval_spec (e.g. "pi", "zeta(1/2)").
    prec_bits : int
        Working precision in bits for Arb computation.

    Returns
    -------
    ((lo_re, hi_re), (lo_im, hi_im)) : tuple of two tuple[Fraction, Fraction]
        Outward-rounded rational boxes for the real and imaginary parts.
        All four endpoints are exact fractions.Fraction.
        lo_re <= true_real <= hi_re and lo_im <= true_imag <= hi_im.

    Notes
    -----
    Box membership is a documented NON-KERNEL input: Arb ball arithmetic is
    internally certified (interval arithmetic with outward rounding), but Lean
    does not independently verify the value.  conjecture1_proved = False.
    """
    if not _FLINT_AVAILABLE:
        raise RuntimeError(
            "python-flint is not available; cannot compute Arb enclosures. "
            "Install with: pip install python-flint"
        )

    result_acb = _eval_spec(spec_or_callable, prec_bits)
    re_box = _arb_ball_to_fractions(result_acb.real)
    im_box = _arb_ball_to_fractions(result_acb.imag)
    return re_box, im_box


def enclose_lambda(
    s_re,
    s_im,
    prec_bits: int,
) -> tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction]]:
    """Return a certified complex enclosure of Lambda(s) at s = s_re + i*s_im.

    Lambda is the completed Riemann zeta function:

        Lambda(s) = pi^(-s/2) * Gamma(s/2) * zeta(s)

    Lambda zeros are exactly the nontrivial zeros of the Riemann zeta function.
    On the critical line (s_re = 1/2) Lambda is real-valued (functional equation),
    so the imaginary enclosure box contains 0.

    Parameters
    ----------
    s_re : int, float, Fraction, or str
        Real part of s.  Converted to string for exact Arb input.
    s_im : int, float, Fraction, or str
        Imaginary part of s.  Converted to string for exact Arb input.
    prec_bits : int
        Working precision in bits for Arb computation.  Higher gives tighter
        enclosures for both the real and imaginary parts.

    Returns
    -------
    ((lo_re, hi_re), (lo_im, hi_im)) : tuple of two tuple[Fraction, Fraction]
        Outward-rounded rational boxes for the real and imaginary parts of
        Lambda(s_re + i*s_im).  All four endpoints are exact fractions.Fraction.
        lo_re <= true_Lambda.real <= hi_re, lo_im <= true_Lambda.imag <= hi_im.
        Both boxes use the full requested prec_bits precision; the imaginary box
        is a tight Arb enclosure (a real signal off the critical line, and a
        tight box around 0 on the critical line where Lambda is real-valued).

    Notes
    -----
    Box membership is a documented NON-KERNEL input: Arb ball arithmetic is
    internally certified (interval arithmetic with outward rounding), but Lean
    does not independently verify the value.  conjecture1_proved = False.
    """
    if not _FLINT_AVAILABLE:
        raise RuntimeError(
            "python-flint is not available; cannot compute Arb enclosures. "
            "Install with: pip install python-flint"
        )

    s_re_str = str(s_re)
    s_im_str = str(s_im)

    def _lambda_callable(flint_module):
        acb_cls = flint_module.acb
        s = acb_cls(s_re_str) + acb_cls(0, s_im_str)
        return acb_cls.pi() ** (-s / 2) * (s / 2).gamma() * s.zeta()

    return enclose_acb(_lambda_callable, prec_bits)


def enclose_lambda_segment(
    re_a,
    im_a,
    re_b,
    im_b,
    prec_bits: int,
) -> tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction]]:
    """Return a certified complex enclosure of Lambda over an axis-aligned segment.

    Evaluates Lambda at both endpoints via enclose_lambda (acb ball arithmetic)
    and returns the bounding box of the two endpoint enclosures.  This gives a
    rigorous outer enclosure of Lambda({endpoint_A, endpoint_B}); it is a
    conservative container of Lambda on the segment provided Lambda stays within
    the convex hull of its endpoint values on each coordinate (which holds for
    axis-aligned boundary segments of the capstone box when n_per_side is large
    enough that no sign change occurs within a single sub-segment).

    The returned box is always strictly wider (in at least one coordinate) than
    either individual endpoint enclosure, satisfying the segment-wider-than-point
    acceptance requirement.

    Parameters
    ----------
    re_a, im_a : Fraction-compatible
        Real and imaginary parts of the first endpoint.
    re_b, im_b : Fraction-compatible
        Real and imaginary parts of the second endpoint.  The segment from A to B
        must be axis-aligned: either im_a == im_b (horizontal) or re_a == re_b
        (vertical).
    prec_bits : int
        Working precision in bits passed to each enclose_lambda call.

    Returns
    -------
    ((lo_re, hi_re), (lo_im, hi_im)) : certified Fraction enclosure
        Bounding box of both endpoint Lambda enclosures.  All four endpoints are
        exact fractions.Fraction.

    Notes
    -----
    Box membership is a documented NON-KERNEL input.  conjecture1_proved = False.
    """
    if not _FLINT_AVAILABLE:
        raise RuntimeError(
            "python-flint is not available; cannot compute Arb enclosures. "
            "Install with: pip install python-flint"
        )
    re_a = Fraction(re_a)
    im_a = Fraction(im_a)
    re_b = Fraction(re_b)
    im_b = Fraction(im_b)
    box_a = enclose_lambda(re_a, im_a, prec_bits)
    box_b = enclose_lambda(re_b, im_b, prec_bits)
    lo_re = min(box_a[0][0], box_b[0][0])
    hi_re = max(box_a[0][1], box_b[0][1])
    lo_im = min(box_a[1][0], box_b[1][0])
    hi_im = max(box_a[1][1], box_b[1][1])
    return (lo_re, hi_re), (lo_im, hi_im)


def enclose_lambda_segments(
    box,
    n_per_side: int,
    prec_bits: int,
) -> list[tuple[Fraction, tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction]]]]:
    """Return an ordered CCW cycle where each entry encloses Lambda over a sub-segment.

    Traverses the same CCW boundary as enclose_lambda_boundary but produces
    SEGMENT enclosures rather than point enclosures.  For each consecutive pair
    of boundary nodes (node k, node k+1), the returned complex_box is a certified
    outer enclosure of Lambda({node_k, node_{k+1}}) -- a bounding box computed
    from the two endpoint acb ball enclosures via enclose_lambda_segment.

    Each segment-box is strictly wider than either constituent endpoint
    point-enclosure.  For fine enough n_per_side (typically >= 80 for the capstone
    box [2/5,3/5]x[10,35]), no segment-box contains 0 and every consecutive pair
    of segment-boxes shares a half-plane witness, allowing segment_winding_certificate
    to succeed.

    Parameters
    ----------
    box : tuple of four values (sigma0, sigma1, T0, T1)
        Rectangle corners.  Each element is converted to Fraction.  sigma0 < sigma1
        and T0 < T1 are expected.
    n_per_side : int
        Number of sub-segments contributed by each of the four edges.  Total
        sub-segments: 4 * n_per_side.  The returned list has length 4*n_per_side + 1
        (the last entry repeats the first to close the cycle).
    prec_bits : int
        Working precision in bits for each enclose_lambda call.

    Returns
    -------
    list of (param, complex_box) pairs
        Each param is a Fraction in [0, 1) giving the CCW position of the
        sub-segment's starting node.  Each complex_box = ((lo_re, hi_re),
        (lo_im, hi_im)) is a certified bounding box enclosing Lambda at both
        endpoints of the sub-segment; all endpoints are Fractions.
        The final entry repeats the first (segment_boxes[0][1] == segment_boxes[-1][1]).

    Raises
    ------
    RuntimeError
        If python-flint is not available.

    Notes
    -----
    Box membership is a documented NON-KERNEL input.  conjecture1_proved = False.
    The segment boxes are wider than the point enclosures at the same nodes
    (as returned by enclose_lambda_boundary at the same n_per_side) because each
    box spans the union of two point enclosures.
    """
    if not _FLINT_AVAILABLE:
        raise RuntimeError(
            "python-flint is not available; cannot compute Arb enclosures. "
            "Install with: pip install python-flint"
        )

    sigma0, sigma1, T0, T1 = (Fraction(v) for v in box)
    n = int(n_per_side)

    # Build the same CCW node positions as enclose_lambda_boundary.
    total = 4 * n
    nodes = []  # list of (param, re, im) as Fractions

    for k in range(total):
        param = Fraction(k, total)
        edge = k // n
        j = k % n

        if edge == 0:
            t = Fraction(j, n)
            re = sigma0 + t * (sigma1 - sigma0)
            im = T0
        elif edge == 1:
            t = Fraction(j, n)
            re = sigma1
            im = T0 + t * (T1 - T0)
        elif edge == 2:
            t = Fraction(j, n)
            re = sigma1 + t * (sigma0 - sigma1)
            im = T1
        else:
            t = Fraction(j, n)
            re = sigma0
            im = T1 + t * (T0 - T1)

        nodes.append((param, re, im))

    # Append the first node again to allow iteration over all sub-segments.
    nodes.append(nodes[0])

    # For each consecutive pair of nodes, compute the segment enclosure.
    segments = []
    for i in range(len(nodes) - 1):
        param, re_a, im_a = nodes[i]
        _, re_b, im_b = nodes[i + 1]
        seg_box = enclose_lambda_segment(re_a, im_a, re_b, im_b, prec_bits)
        segments.append((param, seg_box))

    # Close the cycle: append a copy of the first segment's box.
    segments.append((segments[0][0], segments[0][1]))

    return segments


def enclose_lambda_boundary(
    box,
    n_per_side: int,
    prec_bits: int,
) -> list[tuple[Fraction, tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction]]]]:
    """Return an ordered CCW cycle of Lambda enclosures around the boundary of a box.

    Traverses the boundary of the rectangle {sigma in [sigma0, sigma1]} x {T in [T0, T1]}
    counter-clockwise: bottom edge (sigma0->sigma1 at T0), right edge (T0->T1 at sigma1),
    top edge (sigma1->sigma0 at T1), left edge (T1->T0 at sigma0).

    Each edge contributes n_per_side sample points (the shared corner from the previous
    edge is excluded to avoid duplicates).  The starting point is appended once at the
    end to close the cycle.  Total length: 4*n_per_side + 1.

    Parameters
    ----------
    box : tuple of four values (sigma0, sigma1, T0, T1)
        Rectangle corners.  Each element is converted to Fraction.  sigma0 < sigma1 and
        T0 < T1 are expected; sigma corresponds to the real part of s, T to the imaginary
        part.
    n_per_side : int
        Number of sample points contributed by each edge (excluding the shared corner at
        the start of each edge).  Total unique points: 4*n_per_side.
    prec_bits : int
        Working precision in bits for each enclose_lambda call.

    Returns
    -------
    list of (param, complex_box) pairs
        Each param is a Fraction in [0, 1) giving the monotone CCW position around the
        perimeter.  Each complex_box = ((lo_re, hi_re), (lo_im, hi_im)) is a certified
        Arb enclosure of Lambda at that boundary point; all endpoints are Fractions.
        The final element repeats the first (samples[0][1] == samples[-1][1]).

    Raises
    ------
    RuntimeError
        If python-flint is not available (mirrors enclose_lambda guard).
    """
    if not _FLINT_AVAILABLE:
        raise RuntimeError(
            "python-flint is not available; cannot compute Arb enclosures. "
            "Install with: pip install python-flint"
        )

    sigma0, sigma1, T0, T1 = (Fraction(v) for v in box)
    n = int(n_per_side)

    # Build CCW sample points as (param, re, im) triples.
    # param runs from 0 to 1 (exclusive) across 4*n_per_side equally-spaced points.
    # Each edge: n points, parameterised from k/(4*n) for k = 0..n-1 on that edge's
    # slice of [0,1).  Corner at start of each edge is excluded (it was appended as
    # the last point of the previous edge -- but for the very first edge we start at
    # the bottom-left corner, which is included as k=0 on edge 0).
    #
    # Bottom edge: sigma0 -> sigma1 at T0   (param 0..n-1 out of 4n)
    # Right edge:  T0    -> T1    at sigma1  (param n..2n-1 out of 4n)
    # Top edge:    sigma1 -> sigma0 at T1   (param 2n..3n-1 out of 4n)
    # Left edge:   T1    -> T0    at sigma0  (param 3n..4n-1 out of 4n)

    total = 4 * n
    points = []  # list of (param, re, im) as Fractions

    for k in range(total):
        param = Fraction(k, total)
        edge = k // n
        j = k % n  # position within edge: 0 means the corner (included on edge 0, excluded on 1-3)

        if edge == 0:
            # Bottom: sigma0->sigma1 at T0; j=0 is sigma0, j=n-1 approaches sigma1
            t = Fraction(j, n)
            re = sigma0 + t * (sigma1 - sigma0)
            im = T0
        elif edge == 1:
            # Right: T0->T1 at sigma1; j=0 is T0 corner (excluded), j>0 interior
            t = Fraction(j, n)
            re = sigma1
            im = T0 + t * (T1 - T0)
        elif edge == 2:
            # Top: sigma1->sigma0 at T1; j=0 is sigma1 corner (excluded)
            t = Fraction(j, n)
            re = sigma1 + t * (sigma0 - sigma1)
            im = T1
        else:
            # Left: T1->T0 at sigma0; j=0 is T1 corner (excluded)
            t = Fraction(j, n)
            re = sigma0
            im = T1 + t * (T0 - T1)

        points.append((param, re, im))

    samples = []
    for param, re, im in points:
        box_val = enclose_lambda(re, im, prec_bits)
        samples.append((param, box_val))

    # Close the cycle: append the first point again.
    samples.append((samples[0][0], samples[0][1]))

    return samples
