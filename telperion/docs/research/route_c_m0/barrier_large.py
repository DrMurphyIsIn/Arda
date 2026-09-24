"""Barrier (P15 Thm 1.2 (iii)) at large X with the A+B-C approximation, plus the designs that use it:

  design 'ladder' : X <= 1.28e6, hypothesis (i) = RH verified to height X/2 by the Arb ladder (ASSUMED).
  design 'dvp'    : X ~ 4 pi N_s^2, hypothesis (i) (Prop 3.3 form) from the kernel-proved effective
                    de la Vallee Poussin region beta <= 1 - c/log|gamma| (c >= 9/1369088, |gamma| >= 55/16)
                    plus the height floor; this forces c0 >= (1 - 2c/log(X/2))^2 / 2 (README 5.3).

Barrier region (exact P15 (iii)): X <= x <= X + sqrt(1-y0^2), sqrt(y0^2 + 2(t0-t)) <= y <= sqrt(1-2t),
0 <= t <= t0, covered slab-by-slab in t by Taylor-model boxes (canopy_mesh.certify_box_abc with t a ball).
At t = 0 the P15 bound is used by continuity in t (README section 8).
Exact cover (repair 2026-09-23, README 4.6): t0, y0 are exact decimal rationals (Arb balls); the t-slabs
tile [0, t0] (last slab closed by the t0 ball); each slab's (x, y)-limits are computed in Arb and rounded
outward (smallx.slab_limits); the boxes are hull balls and cover_strip audits the cover; the left edge
sits at x_L = f_up(X + sqrt(1-y0^2)) = the barrier's right end, inside a rigorously identified N-segment.
"""
import argparse
import json
import math
import os
import sys
import time
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from flint import arb, acb, ctx  # noqa: E402

import canopy_analytic_arb as cb  # noqa: E402
import canopy_mesh as cm  # noqa: E402
import p15_arb as pa  # noqa: E402
import p15_float as pf  # noqa: E402
import rigor as rg  # noqa: E402
import smallx  # noqa: E402

PREC = 80


def scan_X(x_lo, x_hi, t0, y0, step=0.125, primes=(2, 3, 5, 7)):
    """Float heuristic (P15 section 8.1): choose X in [x_lo, x_hi] maximising the minimum of |f_t|
    over a coarse sample of the barrier region and of dist(E f, (-inf,0]) on the left edge."""
    best = None
    w = math.sqrt(1 - y0 * y0)
    for X in np.arange(x_lo, x_hi, step):
        worst = float('inf')
        for t in (0.0, t0 / 3, 2 * t0 / 3, t0):
            ylo = math.sqrt(y0 * y0 + 2 * (t0 - t))
            yhi = math.sqrt(max(1 - 2 * t, 0.0))
            for x in (X, X + w / 2, X + w):
                for y in np.linspace(ylo, yhi, 3):
                    f = pf.ft_parts(x, y, max(t, 1e-9))['f']
                    worst = min(worst, abs(f))
        xs = X + w
        for y in np.linspace(y0, 1, 7):
            P = pf.ft_parts(xs, y, t0)
            E = 1
            for p in primes:
                E *= 1 - math.exp((t0 / 4) * math.log(p) ** 2) * complex(p) ** (-P['sstar'])
            G = E * P['f']
            d = abs(G) if G.real >= 0 else abs(G.imag)
            worst = min(worst, d)
        if best is None or worst > best[1]:
            best = (float(X), worst)
    return best


def _slab(args):
    """One t-slab of the barrier.  t0, y0 are decimal strings (exact parameters); ta is a double and tb a
    double or None (None = the last slab, whose upper end is the exact t0 as an Arb ball)."""
    X, t0s, y0s, ta, tb = args
    ctx.prec = PREC
    T0, Y0 = arb(t0s), arb(y0s)
    tt = rg.hull(ta, T0 if tb is None else tb)
    xr, ylo, yhi = smallx.slab_limits(X, T0, Y0, tt)
    Nmax = int(math.sqrt(xr / (4 * math.pi) + 1)) + 4
    C = pa.Coeffs(tt, Nmax)
    t_start = time.time()
    st = cm.cover_strip(X, xr, ylo, yhi, tt, 'abc', C, w0=0.05, grow=1.3)
    st.update(ta=ta, tb=(t0s if tb is None else tb), sec=time.time() - t_start, xr=xr, ylo=ylo, yhi=yhi,
              t_ball=[rg.f_down(tt), rg.f_up(tt)])
    return st


def barrier_abc(X, t0s, y0s, nt=40, workers=30):
    """P15 (iii) at X: slabs tile [0, t0] (smallx.t_slabs: double breakpoints, last slab closed by the exact
    t0 ball); each slab covers the outward-rounded (x, y) limits for all t in its hull."""
    ctx.prec = PREC
    T0 = arb(t0s)
    slabs = smallx.t_slabs(T0, nt)
    jobs = [(X, t0s, y0s, ta, (None if k == nt - 1 else tb)) for k, (ta, tb) in enumerate(slabs)]
    with ProcessPoolExecutor(workers) as ex:
        res = list(ex.map(_slab, jobs))
    # audit: t-slabs tile [0, t0] (bit-identical shared ends, first 0, last closed by the t0 ball)
    t_ok = (res[0]['ta'] == 0.0 and all(res[k]['tb'] == res[k + 1]['ta'] for k in range(nt - 1))
            and res[-1]['tb'] == t0s and bool(arb(res[-1]['t_ball'][1]) >= T0.upper()))
    ok = all(r['ok'] for r in res) and t_ok
    out = dict(ok=ok, slabs=nt, boxes=sum(r['boxes'] for r in res), evals=sum(r['evals'] for r in res),
               terms=sum(r['terms'] for r in res), cpu_sec=sum(r['sec'] for r in res),
               min_margin=min(r['min_margin'] for r in res),
               x_range=[X, max(r['xr'] for r in res)],
               coverage_audit=dict(t_slabs_tile_0_t0=t_ok,
                                   violations=sum(r['audit_violations'] for r in res),
                                   boxes_checked=sum(r['audit_boxes'] for r in res),
                                   n_segments=sum(r['segments'] for r in res)),
               failures=[(r['ta'], r['tb'], r.get('where')) for r in res if not r['ok']])
    return out


def dvp_c0_min(X):
    """Smallest c0 for which the kernel dVP region + height floor give P15 Prop 3.3 (i) at X:
    need (1+sqrt(2 c0))/2 > 1 - c/log(X/2) with c = 9/1369088 (proved lower bound for dlvpRateC)."""
    c = arb(9) / 1369088
    L = (arb(X) / 2).log()
    v = (1 - 2 * c / L)
    return (v * v / 2).upper()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--design', required=True, choices=['ladder', 'dvp'])
    ap.add_argument('--t0', required=True, help='exact decimal (e.g. 0.4549989); used as an Arb ball')
    ap.add_argument('--y0', required=True, help='exact decimal (e.g. 0.3); used as an Arb ball')
    ap.add_argument('--primes', default='2,3,5,7')
    ap.add_argument('--Xmax', type=float, default=1.28e6)
    ap.add_argument('--nt', type=int, default=40)
    ap.add_argument('--workers', type=int, default=30)
    ap.add_argument('--nscan', default='40,1500')
    ap.add_argument('--out', required=True)
    args = ap.parse_args()
    ctx.prec = PREC
    t0s, y0s = args.t0, args.y0
    T0a, Y0a = arb(t0s), arb(y0s)              # Arb balls containing the exact rationals
    t0, y0 = float(t0s), float(y0s)            # floats: heuristics (X scan, printing) only
    c0q = Fraction(t0s) + Fraction(y0s) ** 2 / 2
    primes = tuple(int(p) for p in args.primes.split(','))
    rec = dict(design=args.design, t0=t0s, y0=y0s, c0=float(c0q), c0_exact=f'{c0q.numerator}/{c0q.denominator}',
               params='t0, y0 exact decimal rationals; all Arb computations use balls containing them',
               primes=list(primes), date='2026-09-23', prec_bits=PREC, code='post-repair (exact cover, README 4.6)')
    wall0 = time.time()
    lo, hi = (int(v) for v in args.nscan.split(','))
    cert = cb.analytic_certificate(T0a, Y0a, primes, N_scan=(lo, hi))
    rec['analytic'] = {k: v for k, v in cert.items() if k not in ('bottom', 'top', 'crude', 't0', 'y0')}
    print(f'== {args.design} t0={t0s} y0={y0s} c0={rec["c0_exact"]}: analytic ok={cert["ok"]} N_s={cert["N_s"]} N1={cert.get("N1")}')
    if not cert['ok']:
        json.dump(rec, open(args.out, 'w'), indent=1, default=float)
        return
    Ns = cert['N_s']
    w = math.sqrt(1 - y0 * y0)
    xNs = float(pa.xN(Ns, T0a).upper())
    xNs1 = float(pa.xN(Ns + 1, T0a).lower())
    if args.design == 'dvp':
        # canopy starts at X + w inside the N_s segment
        X_lo, X_hi = xNs - w + 1e-6, xNs1 - w - 1e-6
    else:
        X_hi = args.Xmax
        X_lo = X_hi - 300.0
        if X_hi + w < xNs:
            rec['note'] = f'N_s={Ns} beyond the ladder: canopy strip needed on [X+w, x_L] (use certify_route.py)'
    X, score = scan_X(X_lo, X_hi, t0, y0, primes=primes)
    # canopy start rounded UP: the barrier covers [X, xs] for every t in [0, t0] (t0 included), so the
    # canopy sliver [X + sqrt(1-y0^2), xs] at t0 lies in the barrier; the argument-principle rectangle
    # starts at x_L = xs.
    xs = rg.f_up(arb(X) + (1 - Y0a * Y0a).sqrt())
    ya = rg.f_down(Y0a)
    rec['X'] = X
    rec['X_scan_score'] = score
    N_at_xs = int(math.floor(math.sqrt(xs / (4 * math.pi) + t0 / 16)))
    N_ok = bool(pa.xN(N_at_xs, T0a).upper() <= xs) and bool(arb(xs) < pa.xN(N_at_xs + 1, T0a).lower())
    rec['N_at_canopy_start'] = N_at_xs
    rec['N_at_canopy_start_certified'] = N_ok
    C = pa.Coeffs(T0a, N_at_xs + 20)
    if N_ok and N_at_xs >= Ns:
        le = smallx.left_edge(xs, ya, T0a, primes, C, N_at_xs)
        rec['left_edge'] = dict(x_L=xs, y_range=[ya, 1.0], **le)
        print(f'  X={X:.3f} (score {score:.3f}); left edge at x={xs:.6f}: ok={le["ok"]} margin={le["min_margin"]:.3e}')
    else:
        rec['left_edge'] = dict(ok=False, note='canopy start below N_s (numeric strip required) or N not certified')
    br = barrier_abc(X, t0s, y0s, nt=args.nt, workers=args.workers)
    if not br['x_range'][1] >= xs:
        br['ok'] = False
        br['note'] = 'barrier x-range ends below the left edge'
    rec['barrier'] = br
    print(f'  barrier: ok={br["ok"]} boxes={br["boxes"]} evals={br["evals"]} min_margin={br["min_margin"]:.3e} '
          f'audit={br["coverage_audit"]} cpu {br["cpu_sec"]:.0f}s')
    if args.design == 'dvp':
        cmin = dvp_c0_min(X)
        c0_arb = T0a + Y0a ** 2 / 2               # ball containing the exact rational t0 + y0^2/2
        ok_i = bool((c0_arb - cmin) > 0)
        rec['cond_i'] = dict(kind='kernel dVP region (c >= 9/1369088) + height floor + no real zeros in (0,1)',
                             c0_required_gt=float(cmin), c0=float(c0q), c0_exact=rec['c0_exact'],
                             c0_ball=c0_arb.str(20), ok=ok_i)
        print(f'  (i) via dVP: need c0 > {float(cmin):.11f}; have {rec["c0_exact"]}: ok={rec["cond_i"]["ok"]}')
    else:
        rec['cond_i'] = dict(kind='ASSUMED: RH verified to height X/2 (Arb-conditional ladder to 640000)', ok=None)
    rec['wall_sec'] = time.time() - wall0
    rec['all_certified_here'] = bool(cert['ok'] and rec['left_edge'].get('ok') and br['ok'] and
                                     (rec['cond_i']['ok'] if args.design == 'dvp' else True))
    json.dump(rec, open(args.out, 'w'), indent=1, default=float)
    print(f'  => all_certified_here={rec["all_certified_here"]} ({"(i) assumed" if args.design == "ladder" else "(i) from dVP"})  -> {args.out}')


if __name__ == '__main__':
    main()
