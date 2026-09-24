"""Segment-certified winding numbers (Arb ball arithmetic) for the crux_dynamics-ergodic lane.

conjecture1_proved = False.  Trust class: Arb interval arithmetic (python-flint), not the Lean
kernel.

Method.  The boundary of a rational rectangle is cut into axis-parallel pieces.  For each piece
the function is evaluated on a complex BALL containing the whole piece, so the enclosure covers
every point of the piece, not only its endpoints.  A piece is accepted only if that enclosure
lies in one open half-plane (Re > 0, Re < 0, Im > 0 or Im < 0).  Then f has no zero on the
piece and its argument stays in a branch of arg that is continuous on that half-plane, so the
change of argument along the piece equals the difference of the branch arguments of the two
endpoint values (computed as Arb intervals).  A piece that fails is bisected.  The winding
number is the interval sum divided by 2 pi and is returned only if that interval contains
exactly one integer.

This is the fix for node-only sampling (telperion.arb_dh.winding_number encloses D only at the
nodes, so two consecutive node values in adjacent quadrants do not exclude the path turning the
long way round between them).  The same gap and an equivalent fix were found independently in
telperion/research/axiso_literature/arb_winding.py; this file is a self-contained copy of the
method so that this lane's certificates do not depend on another lane's untracked files.
"""
from __future__ import annotations

from fractions import Fraction

from flint import acb, arb


def arb_q(x: Fraction) -> arb:
    return arb(x.numerator) / arb(x.denominator)


def ball(re_lo: Fraction, re_hi: Fraction, im_lo: Fraction, im_hi: Fraction) -> acb:
    """A complex ball containing the closed rectangle [re_lo, re_hi] x [im_lo, im_hi]."""
    return acb(arb_q(re_lo).union(arb_q(re_hi)), arb_q(im_lo).union(arb_q(im_hi)))


def halfplane(v: acb):
    if v.real > 0:
        return "re+"
    if v.real < 0:
        return "re-"
    if v.imag > 0:
        return "im+"
    if v.imag < 0:
        return "im-"
    return None


def in_halfplane(v: acb, hp: str) -> bool:
    return {"re+": v.real > 0, "re-": v.real < 0, "im+": v.imag > 0, "im-": v.imag < 0}[hp]


def branch_arg(v: acb, hp: str) -> arb:
    """arg v on a branch that is continuous on the open half-plane hp (v must lie in hp)."""
    if hp == "re-":
        return (-v).arg()  # -v lies in Re > 0, where the principal branch is continuous
    return v.arg()         # principal branch is continuous on Re > 0, Im > 0 and Im < 0


def piece_delta(f, z0, z1, depth, max_depth, stats) -> arb:
    (x0, y0), (x1, y1) = z0, z1
    enc = f(ball(min(x0, x1), max(x0, x1), min(y0, y1), max(y0, y1)))
    hp = halfplane(enc)
    if hp is not None:
        v0 = f(acb(arb_q(x0), arb_q(y0)))
        v1 = f(acb(arb_q(x1), arb_q(y1)))
        if in_halfplane(v0, hp) and in_halfplane(v1, hp):
            stats["pieces"] += 1
            return branch_arg(v1, hp) - branch_arg(v0, hp)
    if depth >= max_depth:
        raise RuntimeError(f"piece {z0}->{z1} not certified at depth {depth}: enclosure {enc}")
    xm, ym = (x0 + x1) / 2, (y0 + y1) / 2
    return (piece_delta(f, z0, (xm, ym), depth + 1, max_depth, stats)
            + piece_delta(f, (xm, ym), z1, depth + 1, max_depth, stats))


def winding_number(f, re0, re1, im0, im1, n_per_side: int = 8, max_depth: int = 18) -> dict:
    """Certified number of zeros of f (analytic on a neighbourhood of the closed rectangle)
    inside the open rectangle (re0, re1) x (im0, im1), counted with multiplicity."""
    re0, re1, im0, im1 = (Fraction(v) for v in (re0, re1, im0, im1))
    corners = [(re0, im0), (re1, im0), (re1, im1), (re0, im1), (re0, im0)]
    stats = {"pieces": 0}
    total = arb(0)
    for (a0, b0), (a1, b1) in zip(corners, corners[1:]):
        for k in range(n_per_side):
            p = (a0 + (a1 - a0) * Fraction(k, n_per_side), b0 + (b1 - b0) * Fraction(k, n_per_side))
            q = (a0 + (a1 - a0) * Fraction(k + 1, n_per_side),
                 b0 + (b1 - b0) * Fraction(k + 1, n_per_side))
            total += piece_delta(f, p, q, 0, max_depth, stats)
    w = total / (2 * arb.pi())
    lo = int(w.lower().floor().unique_fmpz())
    hi = int(w.upper().ceil().unique_fmpz())
    ints = [k for k in range(lo, hi + 1) if w.contains(arb(k))]
    if len(ints) != 1:
        raise RuntimeError(f"winding interval {w} does not isolate one integer")
    return {"box": [str(re0), str(re1), str(im0), str(im1)], "winding": ints[0],
            "winding_interval": str(w), "certified_pieces": stats["pieces"]}
