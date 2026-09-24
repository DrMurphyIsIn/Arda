"""Directed rounding, exact box hulls and exact tilings (repair of 2026-09-23, README section 4.6).

Every certificate in this directory covers a region by finitely many boxes whose endpoints are binary
doubles, and hands each box to Arb as a ball.  Two rules make the cover exact:

  1. A box [xa, xb] (xa <= xb doubles) is passed to Arb as hull(xa, xb) = arb(xa).union(arb(xb)), a
     ball that CONTAINS the closed interval.  (The pre-repair code used arb(fl((xa+xb)/2), (xb-xa)/2),
     which misses an endpoint by up to half an ulp whenever the float midpoint is rounded.)
     For Taylor models the box is then described EXACTLY by the ball's own centre and radius:
     Z = zc + [-hx, hx] x [-hy, hy] with zc = mid(Z) and hx = rad(Re Z), hy = rad(Im Z) as exact
     Arb numbers, so the region certified is literally the ball that was evaluated.
  2. Region limits and segment boundaries are rounded OUTWARD to doubles with f_down / f_up (exact
     Arb comparisons, no fixed epsilons), and tilings are built with exact first and last breakpoints
     (grid) so consecutive pieces share bit-identical endpoints.

check_* helpers below are used by the streaming coverage audits in canopy_mesh.py, smallx.py and
barrier_large.py; each returns True only if the property is certain (exact Arb comparisons).
"""
import math

from flint import arb, acb


def f_down(v):
    """A double d with d <= lower(v), i.e. d <= every point of the ball v (v: arb, float, int or decimal
    string; float() rounding is corrected by nextafter steps, checked by exact Arb comparison).  Needs
    ctx.prec >= 53 so that doubles convert to Arb exactly."""
    lo = arb(v).lower()
    if not lo.is_finite():
        raise ValueError('f_down: non-finite bound')
    d = float(lo)
    while not (arb(d) <= lo):
        d = math.nextafter(d, -math.inf)
    return d


def f_up(v):
    """A double d with d >= upper(v)."""
    hi = arb(v).upper()
    if not hi.is_finite():
        raise ValueError('f_up: non-finite bound')
    d = float(hi)
    while not (arb(d) >= hi):
        d = math.nextafter(d, math.inf)
    return d


def hull(a, b):
    """Arb ball containing the closed interval [a, b] (a, b doubles or arb balls)."""
    return arb(a).union(arb(b))


def box(xa, xb, ya, yb):
    """The Arb box for [xa, xb] x [ya, yb]:  (Z, zc, hx, hy, rho) with
         Z  = acb(hull(xa, xb), hull(ya, yb))    (contains the closed rectangle),
         zc = exact centre of Z,  hx, hy = exact half-widths of Z  (Z = zc + [-hx,hx] x [-hy,hy] exactly),
         rho = an Arb ball containing sqrt(hx^2 + hy^2)  (so |w| <= upper(rho) for every w in Z - zc)."""
    X = hull(xa, xb)
    Y = hull(ya, yb)
    Z = acb(X, Y)
    zc = acb(X.mid(), Y.mid())
    hx, hy = X.rad(), Y.rad()
    rho = (hx * hx + hy * hy).sqrt()
    return Z, zc, hx, hy, rho


def grid(a, b, n):
    """n + 1 monotone breakpoints with p[0] = a and p[n] = b exactly (a <= b doubles)."""
    n = max(1, int(n))
    pts = [a] + [a + (b - a) * k / n for k in range(1, n)] + [b]
    for k in range(1, n + 1):
        if pts[k] < pts[k - 1]:
            pts[k] = pts[k - 1]
    return pts


def ball_contains_interval(B, lo, hi):
    """True iff the (real) ball B certainly contains [lo, hi]."""
    return bool(B.lower() <= arb(lo)) and bool(B.upper() >= arb(hi))


def box_contains(Z, xa, xb, ya, yb):
    return ball_contains_interval(Z.real, xa, xb) and ball_contains_interval(Z.imag, ya, yb)


def chain_ok(pieces, a, b):
    """pieces: list of (lo, hi) doubles.  True iff they tile [a, b]: first lo == a, last hi == b,
    consecutive hi == next lo (bit-identical), and lo <= hi throughout."""
    if not pieces:
        return False
    if pieces[0][0] != a or pieces[-1][1] != b:
        return False
    for (l0, h0), (l1, h1) in zip(pieces, pieces[1:]):
        if h0 != l1:
            return False
    return all(lo <= hi for lo, hi in pieces)
