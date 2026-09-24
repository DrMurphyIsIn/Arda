"""Certified analytic envelope: for each target c0, the smallest N_s from which the P15 canopy is
closed analytically (Lemma 8.5 bottom/top edges + crude tail, one fixed mollifier), at the y0 that
minimises N_s on a float pre-scan and at y0 = 0.4 (the cost-optimal choice for the numeric strip).

x_s = 4 pi N_s^2 is then the right end of the numeric canopy strip that design X = 55/8 must cover.
Writes results/envelope.json.  Float pre-scan: canopy_analytic.py; certification: canopy_analytic_arb.py.
"""
import json
import math
import os
import sys
import time
from concurrent.futures import ProcessPoolExecutor

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import numpy as np  # noqa: E402

import canopy_analytic as ca  # noqa: E402

PRIMES = (2, 3, 5, 7)


def float_Ns(t, y0, Nmax=8000):
    ds, lam = ca.mollifier(t, list(PRIMES))
    last = None
    for N in list(range(20, 1200)) + list(range(1200, Nmax, 4)):
        if ca.edge_bound(N, y0, t, list(PRIMES), ds, lam) <= 0:
            last = N
    return (last + 1) if last else 20


def certify(args):
    c0, y0 = args
    from flint import arb, ctx
    import canopy_analytic_arb as cb
    ctx.prec = 80
    t0 = c0 - y0 * y0 / 2
    Nf = float_Ns(t0, y0)
    lo = max(20, int(Nf * 0.9))
    hi = int(Nf * 1.25) + 20
    s = time.time()
    cert = cb.analytic_certificate(t0, y0, PRIMES, N_scan=(lo, hi), log=lambda *a: None)
    out = {k: v for k, v in cert.items() if k not in ('bottom', 'top', 'crude')}
    out.update(c0=c0, y0=y0, t0=t0, N_s_float=Nf, sec=time.time() - s,
               n_bottom=len(cert['bottom']), n_top=len(cert['top']), n_crude=len(cert['crude']))
    if cert['ok']:
        out['x_s'] = 4 * math.pi * cert['N_s'] ** 2
    return out


if __name__ == '__main__':
    c0s = [0.30, 0.32, 0.34, 0.36, 0.38, 0.40, 0.42, 0.43, 0.44, 0.45, 0.46, 0.47, 0.48, 0.49, 0.4999989]
    best_y0 = {0.30: 0.14, 0.32: 0.16, 0.34: 0.18, 0.36: 0.18, 0.38: 0.18, 0.40: 0.20, 0.42: 0.22, 0.43: 0.22,
               0.44: 0.22, 0.45: 0.24, 0.46: 0.24, 0.47: 0.24, 0.48: 0.26, 0.49: 0.26, 0.4999989: 0.30}
    tasks = [(c0, best_y0[c0]) for c0 in c0s] + [(c0, 0.4) for c0 in c0s]
    workers = int(os.environ.get('ENV_WORKERS', '6'))
    with ProcessPoolExecutor(workers) as ex:
        res = list(ex.map(certify, tasks))
    here = os.path.dirname(os.path.abspath(__file__))
    json.dump(res, open(os.path.join(here, 'results', 'envelope.json'), 'w'), indent=1, default=float)
    for r in res:
        print(f"c0={r['c0']:<10} y0={r['y0']:<5} t0={r['t0']:.5f} ok={r['ok']} N_s={r['N_s']} (float {r['N_s_float']}) "
              f"N1={r.get('N1')} x_s={r.get('x_s', float('nan')):.3e} minBot={r.get('min_bottom_margin', float('nan')):.2e} "
              f"maxCrude={r.get('max_crude_rho', float('nan')):.3f} {r['sec']:.0f}s")
