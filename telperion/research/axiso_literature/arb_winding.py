"""Rigorous (Arb ball arithmetic) zero counting on a rectangle by the argument principle.

conjecture1_proved = False.  Trust class: Arb interval arithmetic (python-flint), not Lean kernel.

Method.  The rectangle boundary is cut into axis-parallel pieces.  For each piece [z0, z1]
the function is evaluated on the complex BALL that covers the whole piece, so the result
encloses f on every point of the piece, not only at its endpoints.  A piece is accepted only
if that enclosure lies in one open half-plane {Re > 0}, {Re < 0}, {Im > 0} or {Im < 0}.
Then f has no zero on the piece and its argument stays inside a branch of arg that is
continuous on that half-plane, so the change of argument along the piece equals the
difference of the (branch-adjusted) arguments of the two endpoint values, computed as Arb
intervals.  A piece that fails the test is bisected (to a maximum depth).  The winding
number is the interval sum of the pieces divided by 2 pi; it is returned only if that
interval contains exactly one integer.

This closes a gap in node-only sampling (as in telperion.arb_dh.winding_number), where
consecutive node values in adjacent quadrants do not exclude the path turning the long way
round between the nodes.
"""
from __future__ import annotations

from fractions import Fraction

from flint import acb, arb, ctx


def _arb_from_frac(x: Fraction) -> arb:
    return arb(x.numerator) / arb(x.denominator)


def _ball(re_lo: Fraction, re_hi: Fraction, im_lo: Fraction, im_hi: Fraction) -> acb:
    """Complex ball containing the closed rectangle [re_lo, re_hi] x [im_lo, im_hi].

    Each coordinate is the Arb union of the two endpoint enclosures; a ball is convex, so it
    contains the whole segment between them."""
    re_part = _arb_from_frac(re_lo).union(_arb_from_frac(re_hi))
    im_part = _arb_from_frac(im_lo).union(_arb_from_frac(im_hi))
    return acb(re_part, im_part)


def _halfplane(v: acb):
    """Return which open half-plane the enclosure v lies in, or None."""
    re, im = v.real, v.imag
    if re > 0:
        return "re+"
    if re < 0:
        return "re-"
    if im > 0:
        return "im+"
    if im < 0:
        return "im-"
    return None


def _arg_in(v: acb, hp: str) -> arb:
    """Argument of v on a branch continuous on the half-plane hp (v must lie in hp)."""
    if hp == "re-":
        return (-v).arg()          # -v in {Re > 0}: principal arg continuous there
    return v.arg()                 # principal branch is continuous on re+, im+, im-


def _piece_delta(f, z0: tuple, z1: tuple, depth: int, max_depth: int, stats: dict) -> arb:
    (x0, y0), (x1, y1) = z0, z1
    ball = _ball(min(x0, x1), max(x0, x1), min(y0, y1), max(y0, y1))
    enc = f(ball)
    hp = _halfplane(enc)
    if hp is not None:
        v0 = f(acb(_arb_from_frac(x0), _arb_from_frac(y0)))
        v1 = f(acb(_arb_from_frac(x1), _arb_from_frac(y1)))
        if _halfplane_ok(v0, hp) and _halfplane_ok(v1, hp):
            stats["pieces"] += 1
            return _arg_in(v1, hp) - _arg_in(v0, hp)
    if depth >= max_depth:
        raise RuntimeError(f"piece {z0}->{z1} not certified at depth {depth} "
                           f"(enclosure {enc}); a zero may lie on or near the contour")
    xm, ym = (x0 + x1) / 2, (y0 + y1) / 2
    return (_piece_delta(f, z0, (xm, ym), depth + 1, max_depth, stats)
            + _piece_delta(f, (xm, ym), z1, depth + 1, max_depth, stats))


def _halfplane_ok(v: acb, hp: str) -> bool:
    re, im = v.real, v.imag
    return {"re+": re > 0, "re-": re < 0, "im+": im > 0, "im-": im < 0}[hp]


def winding_number(f, re0, re1, im0, im1, n_per_side: int = 16, max_depth: int = 14,
                   prec: int = 128) -> dict:
    """Rigorous count of zeros of an analytic f inside the open rectangle
    (re0, re1) x (im0, im1) (f must be analytic on a neighbourhood of the closed rectangle).

    Returns a dict with the certified integer and the interval it was read from."""
    old = ctx.prec
    ctx.prec = prec
    try:
        re0, re1, im0, im1 = map(Fraction, (re0, re1, im0, im1))
        corners = [(re0, im0), (re1, im0), (re1, im1), (re0, im1)]
        stats = {"pieces": 0}
        total = arb(0)
        for c in range(4):
            a, b = corners[c], corners[(c + 1) % 4]
            for k in range(n_per_side):
                p0 = (a[0] + (b[0] - a[0]) * Fraction(k, n_per_side),
                      a[1] + (b[1] - a[1]) * Fraction(k, n_per_side))
                p1 = (a[0] + (b[0] - a[0]) * Fraction(k + 1, n_per_side),
                      a[1] + (b[1] - a[1]) * Fraction(k + 1, n_per_side))
                total += _piece_delta(f, p0, p1, 0, max_depth, stats)
        w = total / (2 * arb.pi())
        n = w.unique_fmpz()
        if n is None:
            raise RuntimeError(f"winding interval {w} does not pin a unique integer")
        return {
            "box": {"re": [str(re0), str(re1)], "im": [str(im0), str(im1)]},
            "winding": int(n),
            "winding_interval": str(w),
            "certified_pieces": stats["pieces"],
            "prec": prec,
            "trust": "Arb ball arithmetic, whole-segment enclosures; NOT Lean kernel",
        }
    finally:
        ctx.prec = old
