"""Cost model for the numeric canopy strip of design X = 55/8 at c0 values not fully run here.

For (c0, y0) the strip is [X + sqrt(1-y0^2), x_s] x [y0, sqrt(1-2 t0)] with x_s = 4 pi N_s^2 from the
certified envelope.  We certify short windows (length L) at several x with the same box algorithm as
certify_route.py and record boxes / evaluations / Dirichlet terms / CPU seconds per unit length, then
fit each rate as a power of x (log-log least squares) and integrate from 200 to x_s.

These are PROJECTIONS (each window is itself certified, for the binary doubles of its parameters, with the
repaired exact-cover code; the extrapolation between windows is not).
Writes results/cost_model.json.
"""
import json
import math
import os
import sys
import time
from concurrent.futures import ProcessPoolExecutor

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import numpy as np  # noqa: E402


def window(args):
    c0, y0, x0, L = args
    from flint import arb, ctx
    import canopy_mesh as cm
    import p15_arb as pa
    import rigor as rg
    ctx.prec = 80
    t0 = c0 - y0 * y0 / 2
    tt = arb(t0)
    ytop = rg.f_up((1 - 2 * tt).sqrt())
    C = pa.Coeffs(tt, int(math.sqrt(x0 / 12.566 + 1)) + 20)
    s = time.time()
    st = cm.cover_strip(x0, x0 + L, y0, ytop, tt, 'abc', C, w0=0.1, grow=1.3)
    el = time.time() - s
    return dict(c0=c0, y0=y0, t0=t0, x0=x0, L=L, ok=st['ok'], boxes=st['boxes'] / L, evals=st['evals'] / L,
                terms=st['terms'] / L, cpu=el / L, min_center=st.get('min_center'),
                audit_violations=st['audit_violations'])


def fit_integrate(xs, rates, x_lo, x_hi):
    lx = np.log(np.array(xs))
    lr = np.log(np.array(rates))
    b, a = np.polyfit(lx, lr, 1)          # rate ~ exp(a) x^b
    A = math.exp(a)
    total = A / (b + 1) * (x_hi ** (b + 1) - x_lo ** (b + 1))
    return dict(A=A, b=b, total=total)


if __name__ == '__main__':
    here = os.path.dirname(os.path.abspath(__file__))
    env = json.load(open(os.path.join(here, 'results', 'envelope.json')))
    targets = {}
    for r in env:
        if r.get('ok') and abs(r['y0'] - 0.4) < 1e-9:
            targets[r['c0']] = r
    tasks = []
    for c0, r in sorted(targets.items()):
        xs_ = r['x_s']
        pts = [x for x in (2e3, 2e4, 2e5, 2e6, 2e7, 1e8) if x < xs_] + [0.9 * xs_]
        for x0 in pts:
            L = 40.0 if x0 < 1e7 else 12.0
            tasks.append((c0, 0.4, x0, L))
    workers = int(os.environ.get('CM_WORKERS', '8'))
    with ProcessPoolExecutor(workers) as ex:
        res = list(ex.map(window, tasks))
    out = dict(windows=res, projections=[])
    for c0, r in sorted(targets.items()):
        W = [w for w in res if w['c0'] == c0 and w['ok']]
        if len(W) < 2:
            continue
        xs = [w['x0'] for w in W]
        proj = dict(c0=c0, y0=0.4, t0=r['t0'], N_s=r['N_s'], x_s=r['x_s'])
        for key in ('boxes', 'evals', 'terms', 'cpu'):
            fr = fit_integrate(xs, [w[key] for w in W], 200.0, r['x_s'])
            proj[key + '_total'] = fr['total']
            proj[key + '_rate_exponent'] = fr['b']
        out['projections'].append(proj)
        print(f"c0={c0} N_s={r['N_s']} x_s={r['x_s']:.3e}: boxes~{proj['boxes_total']:.3e} evals~{proj['evals_total']:.3e} "
              f"terms~{proj['terms_total']:.3e} cpu~{proj['cpu_total']:.3e}s ({proj['cpu_total']/3600:.1f} core-h)")
    json.dump(out, open(os.path.join(here, 'results', 'cost_model.json'), 'w'), indent=1, default=float)
