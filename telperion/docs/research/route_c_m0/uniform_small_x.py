"""Parameter-free certificates at X = 55/8 (valid for EVERY 0 < y0 <= 1 and 0 < t0 <= 1/2):

  (U1)  H_0(x+iy) != 0 on [0, 55/8] x [0, 1]          => P15 Thm 1.2(i) and Prop 3.3(i) at X = 55/8, all y0.
  (U2)  H_t(x+iy) != 0 on [55/8, 55/8+1] x [0, 1] x [0, 1/2]
                                                      => P15 Thm 1.2(iii) at X = 55/8 for all (t0, y0), since
                                                         the (iii) region is contained in this box.
  (U2') H_t(x+iy) != 0 on [6.8, 7.8] x [0, 1] x [0, 1/2]   => the same for X = 6.8 < 55/8 (kernel-friendlier X).
Both by Arb enclosures of the Phi-integral (P15 (4)) over boxes (smallx._box_H_phi), adaptive bisection.
Exact cover (repair 2026-09-23): boxes are Arb hulls of their float ends, grids have exact end breakpoints,
and the non-binary limits 6.8, 7.8 of U2' are rounded outward.
Writes results/uniform_small_x.json.
"""
import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from flint import arb, ctx  # noqa: E402

import rigor as rg  # noqa: E402
import smallx  # noqa: E402


def cover_3d(x0, x1, y0, y1, t0, t1, w=0.25, h=0.25, dt=0.05, wmin=1e-3):
    """Certify H_t != 0 on [x0,x1] x [y0,y1] x [t0,t1] (doubles) by adaptive bisection; initial grids
    have exact end breakpoints (rigor.grid), children share the parent's float midpoints, and each
    box is handed to Arb as its hull (smallx._box_H_phi, audited)."""
    import math
    stats = smallx._new_stats(min_absH=float('inf'))
    xs = rg.grid(x0, x1, int(math.ceil((x1 - x0) / w)))
    ys = rg.grid(y0, y1, int(math.ceil((y1 - y0) / h)))
    ts = rg.grid(t0, t1, int(math.ceil((t1 - t0) / dt)))
    stack = [(xs[i], xs[i + 1], ys[j], ys[j + 1], ts[k], ts[k + 1])
             for i in range(len(xs) - 1) for j in range(len(ys) - 1) for k in range(len(ts) - 1)]
    while stack:
        xa, xb, ya, yb, ta, tb = stack.pop()
        H = smallx._box_H_phi(xa, xb, ya, yb, ta, tb, stats)
        stats['evals'] += 1
        m = float(H.abs_lower())
        if m > 0:
            stats['boxes'] += 1
            stats['min_absH'] = min(stats['min_absH'], m)
            continue
        if xb - xa < wmin:
            stats.update(ok=False, where=(xa, xb, ya, yb, ta, tb))
            return stats
        xm, ym, tm = (xa + xb) / 2, (ya + yb) / 2, (ta + tb) / 2
        for (p, q) in ((xa, xm), (xm, xb)):
            for (r, s) in ((ya, ym), (ym, yb)):
                for (u, v) in ((ta, tm), (tm, tb)):
                    stack.append((p, q, r, s, u, v))
    if stats['audit_violations']:
        stats['ok'] = False
    return stats


if __name__ == '__main__':
    ctx.prec = 100
    X = 55 / 8
    out = {}
    s = time.time()
    out['U1_cond_i'] = dict(region='H_0 on [0, 55/8] x [0, 1]', **smallx.cover_2d_phi(0.0, X, 0.0, 1.0, 0.0), sec=time.time() - s)
    s = time.time()
    out['U2_barrier'] = dict(region='H_t on [55/8, 55/8+1] x [0,1] x [0,1/2]', **cover_3d(X, X + 1, 0.0, 1.0, 0.0, 0.5),
                             sec=time.time() - s)
    s = time.time()
    # 6.8 and 7.8 are not binary doubles: round the x-limits outward so the exact [34/5, 39/5] is covered
    a68, b78 = rg.f_down(arb('6.8')), rg.f_up(arb('7.8'))
    out['U2prime_barrier_X6.8'] = dict(region='H_t on [6.8, 7.8] x [0,1] x [0,1/2]  (barrier for X = 6.8 < 55/8, all (t0,y0))',
                                       x_range_doubles=[a68, b78],
                                       **cover_3d(a68, b78, 0.0, 1.0, 0.0, 0.5), sec=time.time() - s)
    here = os.path.dirname(os.path.abspath(__file__))
    json.dump(out, open(os.path.join(here, 'results', 'uniform_small_x.json'), 'w'), indent=1, default=float)
    print(json.dumps(out, indent=1, default=float))
