"""Small-x certifications for the X = 55/8 design (Arb):

  * cond_i_rect   : Thm 1.2(i) at X = 55/8  <=>  H_0 has no zeros in [0, X] x [y0, 1]
                    (H_0(x+iy) = xi((1-y+ix)/2)/8, so zeta(sigma+iT) = 0 with (1+y0)/2 <= sigma <= 1,
                     0 <= T <= X/2 would give H_0(2T + i(2 sigma - 1)... ) = 0 after conjugation).
  * barrier_3d    : Thm 1.2(iii) at X = 55/8: H_t != 0 on X <= x <= X + sqrt(1-y0^2),
                    sqrt(y0^2 + 2(t0 - t)) <= y <= sqrt(1 - 2t), 0 <= t <= t0.
  * left_edge     : dist(E H_t/B_t, (-inf,0]) > 0 on {x_L} x [y0, 1] (argument-principle left edge).

The barrier and (i) use the Phi-integral (P15 (4)) with ball parameters; a box is certified when the
enclosure of H over the whole (x, y[, t]) box excludes 0.

Exact cover (repair 2026-09-23, README 4.6): every box is handed to Arb as the hull of its float
endpoints (rigor.hull), initial grids have exact first/last breakpoints (rigor.grid), bisection children
share the parent's float midpoint, and region limits are computed in Arb from the exact parameters and
rounded outward (rigor.f_down / f_up).  Each accepted box is audited (Arb box contains the float box).
"""
import math

from flint import arb, acb, ctx

import p15_arb as pa
import rigor as rg


def _new_stats(**kw):
    d = dict(boxes=0, evals=0, ok=True, audit_violations=0, audit_first=None)
    d.update(kw)
    return d


def _audit(stats, msg):
    stats['audit_violations'] += 1
    if stats.get('audit_first') is None:
        stats['audit_first'] = msg


def _box_H_phi(xa, xb, ya, yb, ta, tb, stats=None):
    """Enclosure of H_t(z) over the closed box [xa,xb] x [ya,yb] x [ta,tb] (ends: doubles or Arb balls)."""
    X, Y, T = rg.hull(xa, xb), rg.hull(ya, yb), rg.hull(ta, tb)
    if stats is not None:
        if not (rg.ball_contains_interval(X, xa, xb) and rg.ball_contains_interval(Y, ya, yb)
                and bool(T.lower() <= arb(ta).lower()) and bool(T.upper() >= arb(tb).upper())):
            _audit(stats, f'Arb box misses [{xa},{xb}]x[{ya},{yb}]x[{ta},{tb}]')
    return pa.Ht_phi(acb(X, Y), T, rel_tol_bits=30)


def _excl0(H):
    """Lower bound of |H| over the ball (0 if the ball contains 0)."""
    return float(H.abs_lower())


def cover_2d_phi(x0, x1, y0, y1, t, w=0.25, h=0.25, wmin=1e-3, stats=None):
    """Certify H_t != 0 on [x0,x1] x [y0,y1] (doubles; t a double or Arb ball) by adaptive bisection."""
    if stats is None:
        stats = _new_stats(min_absH=float('inf'))
    xs = rg.grid(x0, x1, int(math.ceil((x1 - x0) / w)))
    ys = rg.grid(y0, y1, int(math.ceil((y1 - y0) / h)))
    stack = [(xs[i], xs[i + 1], ys[j], ys[j + 1]) for i in range(len(xs) - 1) for j in range(len(ys) - 1)]
    while stack:
        xa, xb, ya, yb = stack.pop()
        H = _box_H_phi(xa, xb, ya, yb, t, t, stats)
        stats['evals'] += 1
        m = _excl0(H)
        if m > 0:
            stats['boxes'] += 1
            stats['min_absH'] = min(stats['min_absH'], m)
            continue
        if xb - xa < wmin:
            stats['ok'] = False
            stats['where'] = (xa, xb, ya, yb)
            return stats
        xm, ym = (xa + xb) / 2, (ya + yb) / 2
        stack += [(xa, xm, ya, ym), (xm, xb, ya, ym), (xa, xm, ym, yb), (xm, xb, ym, yb)]
    if stats['audit_violations']:
        stats['ok'] = False
    return stats


def cond_i_rect(X, y0):
    """Thm 1.2(i) (strong, zeta form) at X: H_0 zero-free on [0, X] x [y0, 1] (X, y0 doubles; pass
    y0 already rounded down and X already rounded up)."""
    return cover_2d_phi(0.0, X, y0, 1.0, 0.0)


def slab_limits(X, T0, Y0, T):
    """Outward-rounded (x, y) limits of the P15 (iii) region for t in the Arb ball T:
    x in [X, X + sqrt(1-y0^2)],  sqrt(y0^2 + 2(t0 - t)) <= y <= sqrt(1 - 2t)."""
    xr = rg.f_up(arb(X) + (1 - Y0 * Y0).sqrt())
    ylo = rg.f_down((Y0 * Y0 + 2 * (T0 - T)).sqrt())
    s = (1 - 2 * T)
    yhi = 1.0 if not (s > 0) else min(1.0, rg.f_up(s.sqrt()))
    return xr, ylo, yhi


def t_slabs(T0, nt):
    """nt slabs tiling [0, t0]: (ta, tb) with doubles, except that the last slab's upper end is the Arb
    ball T0 itself (so the exact t0 is covered)."""
    t0f = float(T0.mid())
    ts = [0.0] + [t0f * k / nt for k in range(1, nt)]
    return [(ts[k], ts[k + 1]) for k in range(nt - 1)] + [(ts[nt - 1], T0)]


def barrier_3d(X, t0, y0, nt=40, wx=0.25, wy=0.2, wmin=1e-3):
    """Thm 1.2(iii) region at X (exact curved y-limits, handled slab by slab in t).  t0, y0: decimal
    strings or Arb balls containing the exact parameters."""
    T0, Y0 = arb(t0), arb(y0)
    stats = _new_stats(min_absH=float('inf'), slabs=0)
    for (ta, tb) in t_slabs(T0, nt):
        T = rg.hull(ta, tb)
        xr, ylo, yhi = slab_limits(X, T0, Y0, T)
        stats['slabs'] += 1
        xs = rg.grid(X, xr, int(math.ceil((xr - X) / wx)))
        ys = rg.grid(ylo, yhi, int(math.ceil((yhi - ylo) / wy)))
        stack = [(xs[i], xs[i + 1], ys[j], ys[j + 1], ta, tb) for i in range(len(xs) - 1) for j in range(len(ys) - 1)]
        while stack:
            xa, xb, ya, yb, a, b = stack.pop()
            H = _box_H_phi(xa, xb, ya, yb, a, b, stats)
            stats['evals'] += 1
            m = _excl0(H)
            if m > 0:
                stats['boxes'] += 1
                stats['min_absH'] = min(stats['min_absH'], m)
                continue
            if xb - xa < wmin:
                stats['ok'] = False
                stats['where'] = (xa, xb, ya, yb, float(arb(a).mid()), float(arb(b).mid()))
                return stats
            xm, ym = (xa + xb) / 2, (ya + yb) / 2
            tm = (float(arb(a).mid()) + float(arb(b).mid())) / 2
            for (p, q) in ((xa, xm), (xm, xb)):
                for (r, s) in ((ya, ym), (ym, yb)):
                    for (u, v) in ((a, tm), (tm, b)):
                        stack.append((p, q, r, s, u, v))
    if stats['audit_violations']:
        stats['ok'] = False
    return stats


def left_edge(xL, y0, t, primes, C, N, dy=0.05, dymin=1e-4, y1=1.0):
    """Certify dist(E(z) H_t(z)/B_t(z), (-inf,0]) > 0 on the vertical segment {xL} x [y0, y1]
    (y0 a double, already rounded down), using |E (H/B - (f - C/B))| <= |E| (e_A + e_B + e_C) (or the
    e_{C,0} variant).  N must be the correct N at xL."""
    stats = _new_stats(min_margin=float('inf'))
    ys = rg.grid(y0, y1, int(math.ceil((y1 - y0) / dy)))
    stack = [(ys[j], ys[j + 1]) for j in range(len(ys) - 1)]
    t = arb(t)
    while stack:
        ya, yb = stack.pop()
        Y = rg.hull(ya, yb)
        if not rg.ball_contains_interval(Y, ya, yb):
            _audit(stats, f'Arb ball misses [{ya},{yb}]')
        z = acb(arb(xL), Y)
        Q = pa.ft_all(z, t, N, C, want_deriv=False, want_err=True, want_C=True, moll=primes)
        stats['evals'] += 1
        E = Q['E']
        best = -1e300
        cands = []
        K = Q['CB']
        if K is not None and K.is_finite():
            cands.append((E * (Q['f'] - K), Q['err_AB'] + Q['common'] * Q['et']))
        cands.append((E * Q['f'], Q['err_AB'] + Q['common'] * (1 + Q['et'])))
        for G, err in cands:
            c = G.mid()                 # exact centre; dist(., (-inf,0]) is 1-Lipschitz
            if c.real >= 0:             # exact Arb comparison (no float sign rounding)
                d = c.abs_lower()
            else:
                d = c.imag.abs_lower()
            m = d - G.rad() - E.abs_upper() * err
            best = max(best, float(m.lower()))
        if best > 0:
            stats['boxes'] += 1
            stats['min_margin'] = min(stats['min_margin'], best)
            continue
        if yb - ya < dymin:
            stats['ok'] = False
            stats['where'] = (ya, yb)
            return stats
        ym = (ya + yb) / 2
        stack += [(ya, ym), (ym, yb)]
    if stats['audit_violations']:
        stats['ok'] = False
    return stats
