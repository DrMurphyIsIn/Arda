"""Box certification of H_t(z) != 0 on regions in the (x, y) plane at a fixed time t (canopy), or on
(x, y, t) boxes (barrier), with Arb.  Two evaluators:

  * 'abc'    : P15 Thm 1.3 / Cor 6.4 (x >= 200):  |H/B| >= |f - C/B| - (e_A + e_B + e_C)
                                                   or |H/B| >= |f| - (e_A + e_B + e_{C,0})
  * 'direct' : P15 (35) heat-kernel integral of xi (exact up to Arb enclosures), any x in [7, 2000].

Taylor-model criterion on a box Z = z_c + W, W = [-hx, hx] x [-hy, hy] (README section 4.4):
    for w in W:  F(z_c + w) = F(z_c) + F'(z_c) w + R,   |R| <= |w| (rad(B1) + |mid(B1) - F'(z_c)|),
    where B1 is an Arb enclosure of F' on the whole box.  Hence
    min_W |F| >= |F'(z_c)| dist(-F(z_c)/F'(z_c), W) - rho (rad B1 + |mid B1 - F'(z_c)|) - (ball radii),
    rho >= sqrt(hx^2 + hy^2).  The box is certified when this exceeds the approximation error.

Exact cover (repair 2026-09-23, README section 4.6): the float box [xa,xb] x [ya,yb] is handed to Arb
as the hull ball Z = acb(hull(xa,xb), hull(ya,yb)) (rigor.box), and the Taylor model uses Z's own exact
centre and half-widths, so the certified set is Z itself and Z contains the closed float box.  The
N-segments of the A+B-C evaluator are built with directed rounding (n_segments) so that every x lies in
a box whose N is correct on the closed segment [x_N, x_{N+1}].  cover_strip audits both properties as it
goes (exact Arb comparisons) and reports any violation as a failure.
"""
import math

from flint import arb, acb, ctx

import p15_arb as pa
import rigor as rg

I = acb(0, 1)


def _dist_to_rect_lower(p, hx, hy):
    """Lower bound for dist(p, [-hx,hx] x [-hy,hy]) for an acb ball p (hx, hy: arb)."""
    rx = p.real.abs_lower() - hx
    ry = p.imag.abs_lower() - hy
    rx = rx if rx > 0 else arb(0)
    ry = ry if ry > 0 else arb(0)
    return (rx * rx + ry * ry).sqrt().lower()


def linear_min_lower(a, b, hx, hy, rho):
    """Lower bound for min_{w in W} |a + b w| where a, b are acb balls, W = [-hx,hx]x[-hy,hy] (hx, hy
    exact arbs) and rho is an Arb ball containing sqrt(hx^2 + hy^2)."""
    am, bm = a.mid(), b.mid()
    if float(bm.abs_upper()) == 0.0:
        lin = am.abs_lower()
    else:
        p = -am / bm
        lin = bm.abs_lower() * _dist_to_rect_lower(p, hx, hy)
    return (lin - a.rad() - b.rad() * rho).lower()


def certify_box_abc(xa, xb, ya, yb, t, C, N):
    """Returns (ok, margin_estimate, cost_terms, centre_value, Z).  N must be the correct N on the part
    of the box that this box is relied on for (cover_strip arranges that)."""
    Z, zc, hx, hy, rho = rg.box(xa, xb, ya, yb)
    P = pa.ft_all(zc, t, N, C, want_deriv=True, want_err=False, want_C=False)
    Q = pa.ft_all(Z, t, N, C, want_deriv=True, want_err=True, want_C=True)
    f0, b = P['f'], P['df']
    B1 = Q['df']
    lip = (B1.rad() + (B1.mid() - b).abs_upper()).upper()
    errAB, common, et = Q['err_AB'], Q['common'], Q['et']
    best = -1e300
    center = -1e300          # certified lower bound for |H_t/B_t| at the box centre (pointwise margin)
    # (a) with the C-correction
    K = Q['CB']
    if K is not None and K.is_finite():
        a0 = f0 - K.mid()
        lin = linear_min_lower(a0, b, hx, hy, rho)
        m = lin - rho * lip - K.rad() - (errAB + common * et)
        best = max(best, float(m.lower()))
        center = max(center, float((a0.abs_lower() - a0.rad() - K.rad() - (errAB + common * et)).lower()))
    # (b) without it (|C/B| folded into e_{C,0})
    lin0 = linear_min_lower(f0, b, hx, hy, rho)
    m0 = lin0 - rho * lip - (errAB + common * (1 + et))
    best = max(best, float(m0.lower()))
    center = max(center, float((f0.abs_lower() - (errAB + common * (1 + et))).lower()))
    return best > 0, best, 4 * N, center, Z


def certify_box_direct(xa, xb, ya, yb, t):
    """Taylor-model certification with the direct heat-kernel evaluator (t > 0)."""
    Z, zc, hx, hy, rho = rg.box(xa, xb, ya, yb)
    H0, D0 = pa.Ht_direct(zc, t, want_deriv=True)
    _, B1 = pa.Ht_direct(Z, t, want_deriv=True)
    lip = (B1.rad() + (B1.mid() - D0).abs_upper()).upper()
    lin = linear_min_lower(H0, D0, hx, hy, rho)
    m = lin - rho * lip
    # report the margin relative to |H(z_c)| so that it is scale free
    rel = float(m.lower()) / max(float(H0.abs_upper()), 1e-300)
    # centre value normalised by |B_t| (no approximation error in this mode)
    Bc = pa.log_Mt(arb(t), (1 - I * zc) / 2).real.exp()
    center = float((H0.abs_lower() / Bc).lower())
    return float(m.lower()) > 0, rel, 3, center, Z


def n_segments(x0, x1, t):
    """Pieces (a, b, N), consecutive N, that cover [x0, x1] (doubles, x0 < x1) such that every x in
    [x0, x1] lies in the piece whose N satisfies x_N(t) <= x <= x_{N+1}(t), for every t in the ball t
    (x_N = 4 pi N^2 - pi t/4, P15 (19)).  Construction (README 4.6):
      N0 = the largest N with x_N(t) <= x0 certainly;
      piece N = [a_N, b_N] with a_{N0} = x0, a_N = max(x0, f_down(lower x_N)) (N > N0),
                b_N = min(x1, f_up(upper x_{N+1})), stopping at the first N with x1 <= lower x_{N+1}.
    (audit_segments checks the stricter a_N <= lower x_N for N > N0.)"""
    tb = arb(t)
    N = max(0, int(math.floor(math.sqrt(max(x0, 0.0) / (4 * math.pi) + float(tb.mid()) / 16))))
    while N > 0 and not (pa.xN(N, tb).upper() <= x0):
        N -= 1
    while pa.xN(N + 1, tb).upper() <= x0:
        N += 1
    pieces = []
    a = x0
    while True:
        hi = pa.xN(N + 1, tb)
        if arb(x1) <= hi.lower():
            pieces.append((a, x1, N))
            return pieces
        pieces.append((a, min(x1, rg.f_up(hi.upper())), N))
        a = max(a, rg.f_down(hi.lower()))
        N += 1


def audit_segments(pieces, x0, x1, t):
    """Independent exact check of the coverage lemma for n_segments output.  Returns a list of
    violations (empty = the lemma's hypotheses hold):
      first piece starts at x0 and x_{N0} <= x0;  consecutive N;  a_N <= x_N (N > N0);
      b_N >= x_{N+1} or b_N = x1 (all but the last);  last piece ends at x1 and x1 <= x_{N_last+1}."""
    tb = arb(t)
    v = []
    if not pieces:
        return ['no pieces']
    a0, _, N0 = pieces[0]
    if a0 != x0 or not (pa.xN(N0, tb).upper() <= x0):
        v.append(f'first piece: start {a0} != x0 or x_N0 not <= x0 (N0={N0})')
    for i, (a, b, N) in enumerate(pieces):
        if not a < b:
            v.append(f'empty piece N={N}: [{a}, {b}]')
        if i > 0:
            if N != pieces[i - 1][2] + 1:
                v.append(f'N not consecutive at piece {i}')
            if not (arb(a) <= pa.xN(N, tb).lower()):
                v.append(f'piece N={N} starts at {a} above x_N')
        if i < len(pieces) - 1 and not (b == x1 or arb(b) >= pa.xN(N + 1, tb).upper()):
            v.append(f'piece N={N} ends at {b} below x_(N+1)')
    a, b, N = pieces[-1]
    if b != x1 or not (arb(x1) <= pa.xN(N + 1, tb).lower()):
        v.append(f'last piece N={N}: end {b} != x1 or x1 not <= x_(N+1)')
    return v


def _audit(stats, msg):
    stats['audit_violations'] += 1
    if stats.get('audit_first') is None:
        stats['audit_first'] = msg


def cover_strip(x0, x1, ya, yb, t, mode, C=None, w0=0.05, wmin=1e-5, grow=1.5, max_boxes=10 ** 9,
                ysplit_max=64, max_evals=None):
    """Cover [x0, x1] x [ya, yb] (doubles) at time t (an Arb ball; every t in it is covered) by
    certified boxes.
    mode 'abc': one piece per N from n_segments; inside a piece every box uses that N.  mode 'direct':
    one piece.  Inside a piece the float boxes [xa, xb] tile the piece exactly (xa of each box = xb of
    the previous one, first xa = piece start, last xb = piece end), each box's y-pieces tile [ya, yb]
    exactly (rigor.grid), and each Arb box contains its float box (rigor.box).  All three facts and the
    n_segments lemma are re-checked here (audit); any violation makes the result ok=False.
    Returns a stats dict."""
    t_arb = arb(t)
    stats = dict(boxes=0, evals=0, terms=0, min_margin=float('inf'), fails=0, ok=True, where=None,
                 min_width=float('inf'), max_width=0.0, ysplits=0, segments=0, audit_violations=0,
                 audit_first=None, audit_boxes=0)
    if not x0 < x1 or not ya <= yb:
        stats.update(ok=False, where='degenerate strip')
        return stats
    if mode == 'direct':
        pieces = [(x0, x1, None)]
    else:
        pieces = n_segments(x0, x1, t_arb)
        for msg in audit_segments(pieces, x0, x1, t_arb):
            _audit(stats, msg)
    for (sa, sb, N) in pieces:
        stats['segments'] += 1
        if mode == 'abc' and C.Nmax < N:
            C.extend(N + 16)
        xa = sa
        expect = sa           # audit: next box must start exactly here
        w = w0
        while xa < sb:
            xb = min(xa + w, sb)
            if not xb > xa:
                stats.update(ok=False, where=(xa, 'no float progress'))
                return stats
            ok, margin, _ = _try_box(xa, xb, ya, yb, t_arb, mode, C, N, ysplit_max, stats)
            if ok:
                if xa != expect:
                    _audit(stats, f'x-chain break at {xa} (expected {expect})')
                expect = xb
                stats['min_margin'] = min(stats['min_margin'], margin)
                stats['min_width'] = min(stats['min_width'], xb - xa)
                stats['max_width'] = max(stats['max_width'], xb - xa)
                xa = xb
                w = min(w * grow, 8.0)
            else:
                stats['fails'] += 1
                w = (xb - xa) / 2
                if w < wmin:
                    stats.update(ok=False, where=(xa, xb))
                    return stats
            if stats['boxes'] > max_boxes:
                stats.update(ok=False, where=(xa, 'max_boxes'))
                return stats
            if max_evals is not None and stats['evals'] > max_evals:
                # evaluation budget exhausted (e.g. crawling towards a point where the A+B-C criterion
                # cannot hold): report failure so the caller can switch evaluator
                stats.update(ok=False, where=(xa, 'max_evals'))
                return stats
        if expect != sb:
            _audit(stats, f'piece [{sa}, {sb}] (N={N}) covered only to {expect}')
    if stats['audit_violations']:
        stats['ok'] = False
        stats['where'] = 'coverage audit: ' + str(stats['audit_first'])
    return stats


def _try_box(xa, xb, ya, yb, t, mode, C, N, ysplit_max, stats):
    """Try the full-height box; if it fails, try splitting in y (up to ysplit_max pieces).  The y-pieces
    are rigor.grid(ya, yb, k): bit-identical shared endpoints, first = ya, last = yb."""
    k = 1
    while k <= ysplit_max:
        ys = rg.grid(ya, yb, k)
        allok = True
        mm = float('inf')
        Zs = []
        for j in range(k):
            y_lo, y_hi = ys[j], ys[j + 1]
            if mode == 'abc':
                ok, margin, cost, center, Z = certify_box_abc(xa, xb, y_lo, y_hi, t, C, N)
                stats['terms'] += cost
            else:
                ok, margin, cost, center, Z = certify_box_direct(xa, xb, y_lo, y_hi, t)
            stats['evals'] += 1
            if not ok:
                allok = False
                break
            Zs.append((Z, y_lo, y_hi))
            mm = min(mm, margin)
            stats['min_center'] = min(stats.get('min_center', float('inf')), center)
        if allok:
            # audit: y-pieces tile [ya, yb] and every Arb box contains its float box
            if not rg.chain_ok([(lo, hi) for _, lo, hi in Zs], ya, yb):
                _audit(stats, f'y-chain does not tile [{ya}, {yb}] at x=[{xa}, {xb}]')
            for Z, lo, hi in Zs:
                stats['audit_boxes'] += 1
                if not rg.box_contains(Z, xa, xb, lo, hi):
                    _audit(stats, f'Arb box misses float box [{xa},{xb}]x[{lo},{hi}]')
            stats['boxes'] += k
            if k > 1:
                stats['ysplits'] += 1
            return True, mm, None
        k *= 2
        if (xb - xa) > 4 * (yb - ya) / k:
            # splitting y further than the box aspect makes no sense; let the caller shrink x
            break
    return False, None, None
