"""Driver: certify the three P15 hypotheses (Thm 1.2 / Prop 3.3) for one parameter row and write a
JSON record.  Usage (see README section 6 for the exact commands used):

    python certify_route.py --design X55o8 --t0 0.4 --y0 0.4 --primes 2,3,5,7 --out results/row.json

Design X55o8 (README section 5.1): X = 55/8.  (i) certified here (H_0 zero-free on [0,X]x[y0,1], Arb);
(iii) barrier certified here (Phi-integral boxes over the exact P15 (iii) region); (ii) canopy = numeric
strip [X+sqrt(1-y0^2), x_L] x [y0, sqrt(1-2t0)] (direct evaluator below x = 200, P15 A+B-C Taylor-model
boxes above) + analytic R_big (Lemma 8.5 edges, crude tail, far bound) + left edge at x_L.
The large-X designs ('ladder': (i) assumed from the Arb ladder; 'dvp': (i) from the kernel dVP region)
are driven by barrier_large.py; the --design flag here only changes what is recorded for (i)/(iii).

Exact cover (repair 2026-09-23, README 4.6): --t0/--y0/--X are exact rationals (Arb balls); the strip
limits are computed in Arb and rounded outward (start and bottom down, top up); the chunks tile
[x_start, x_L] exactly (rigor.grid) and the tiling is audited; every chunk's cover is audited inside
canopy_mesh.cover_strip; the left edge x_L is checked to lie inside the N_s segment.
"""
import argparse
import json
import math
import os
import sys
import time
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from flint import arb, acb, ctx  # noqa: E402

import canopy_analytic_arb as cb  # noqa: E402
import canopy_mesh as cm  # noqa: E402
import p15_arb as pa  # noqa: E402
import rigor as rg  # noqa: E402
import smallx  # noqa: E402

PREC = 80


def _chunk_abc(args):
    x0, x1, ya, yb, t = args          # t: exact decimal string (Arb ball containing it)
    ctx.prec = PREC
    tt = arb(t)
    Nmax = int(math.sqrt(x1 / (4 * math.pi) + 1)) + 4
    C = pa.Coeffs(tt, Nmax)
    t_start = time.time()
    st = cm.cover_strip(x0, x1, ya, yb, tt, 'abc', C, w0=0.1, grow=1.3, max_evals=int(400 * (x1 - x0)) + 20000)
    st['x0'], st['x1'], st['mode'] = x0, x1, 'abc'
    st['sec'] = time.time() - t_start
    st['Nmax'] = int(math.floor(math.sqrt(x1 / (4 * math.pi) + float(t) / 16)))
    return st


def _chunk_direct(args):
    x0, x1, ya, yb, t = args
    ctx.prec = PREC
    t_start = time.time()
    st = cm.cover_strip(x0, x1, ya, yb, arb(t), 'direct', w0=0.2, grow=1.3)
    st['x0'], st['x1'], st['mode'] = x0, x1, 'direct'
    st['sec'] = time.time() - t_start
    return st


def chunks(a, b, n):
    """n chunks tiling [a, b] with bit-identical shared endpoints (first = a, last = b exactly)."""
    pts = rg.grid(a, b, n)
    return list(zip(pts[:-1], pts[1:]))


def chunk_tiling_ok(res, a, b):
    """Audit: the certified chunks (ok records) tile [a, b] exactly."""
    good = sorted([r for r in res if r['ok']], key=lambda r: (r['x0'], r['x1']))
    return rg.chain_ok([(r['x0'], r['x1']) for r in good], a, b)


def run_strip(xs, xe, ya, yb, t0, workers, x_direct_max=200.0, abc_chunk=2000.0, direct_chunk=4.0, log=print):
    """Canopy numeric strip [xs, xe] x [ya, yb] at t0: direct below x_direct_max, A+B-C above; ABC
    chunks that fail are re-run with the direct evaluator if they lie below 5000."""
    jobs_d, jobs_a = [], []
    xd = min(max(xs, x_direct_max), xe)
    if xs < xd:
        n = max(1, int(math.ceil((xd - xs) / direct_chunk)))
        jobs_d = [(a, b, ya, yb, t0) for a, b in chunks(xs, xd, n)]
    if xd < xe:
        n = max(1, int(math.ceil((xe - xd) / abc_chunk)))
        n = max(n, min(workers * 4, int((xe - xd) / 50) + 1))
        jobs_a = [(a, b, ya, yb, t0) for a, b in chunks(xd, xe, n)]
    res = []
    t_start = time.time()
    with ProcessPoolExecutor(workers) as ex:
        # submit direct chunks first (slowest per unit), then the A+B-C chunks, all concurrently
        fut_d = [ex.submit(_chunk_direct, j) for j in jobs_d]
        fut_a = [ex.submit(_chunk_abc, j) for j in jobs_a]
        fa = [f.result() for f in fut_a]
        redo = [(r['x0'], r['x1'], ya, yb, t0) for r in fa if not r['ok'] and r['x1'] <= 5000]
        fail_hard = [r for r in fa if not r['ok'] and r['x1'] > 5000]
        fut_r = [ex.submit(_chunk_direct, j) for j in redo]
        fd = [f.result() for f in fut_d] + [f.result() for f in fut_r]
    res = [r for r in fa if r['ok']] + fd + fail_hard
    tiling = chunk_tiling_ok(res, xs, xe)
    ok = all(r['ok'] for r in res) and tiling
    log(f'  [strip] {len(jobs_a)} abc chunks ({len(redo)} redone direct), {len(jobs_d)} direct chunks: ok={ok} '
        f'(chunk tiling audit {tiling}) wall {time.time() - t_start:.0f}s')
    return ok, res, tiling


def summarize(res):
    s = dict(boxes=0, evals=0, terms=0, cpu_sec=0.0, min_margin_abc=float('inf'), min_rel_margin_direct=float('inf'),
             boxes_abc=0, boxes_direct=0, evals_abc=0, evals_direct=0, ysplits=0, failures=[])
    for r in res:
        s['boxes'] += r['boxes']
        s['evals'] += r['evals']
        s['terms'] += r['terms']
        s['cpu_sec'] += r['sec']
        s['ysplits'] += r['ysplits']
        s['min_center_abs_HB'] = min(s.get('min_center_abs_HB', float('inf')), r.get('min_center', float('inf')))
        if r['mode'] == 'abc':
            s['boxes_abc'] += r['boxes']
            s['evals_abc'] += r['evals']
            s['min_margin_abc'] = min(s['min_margin_abc'], r['min_margin'])
        else:
            s['boxes_direct'] += r['boxes']
            s['evals_direct'] += r['evals']
            s['min_rel_margin_direct'] = min(s['min_rel_margin_direct'], r['min_margin'])
        s['audit_violations'] = s.get('audit_violations', 0) + r.get('audit_violations', 0)
        s['audit_boxes_checked'] = s.get('audit_boxes_checked', 0) + r.get('audit_boxes', 0)
        s['n_segment_pieces'] = s.get('n_segment_pieces', 0) + (r.get('segments', 0) if r['mode'] == 'abc' else 0)
        if not r['ok']:
            s['failures'].append(dict(x0=r['x0'], x1=r['x1'], where=r.get('where')))
    return s


def pick_left_edge(Ns, t0, y0, primes, C, npts=400):
    """Float scan over the N_s segment for the x maximising min_y dist(E f, (-inf,0]); returns x_L."""
    old_prec = ctx.prec
    ctx.prec = 64
    a = float(pa.xN(Ns, arb(t0)).upper()) + 1e-6
    b = float(pa.xN(Ns + 1, arb(t0)).lower()) - 1e-6
    best = None
    for k in range(npts):
        x = a + (b - a) * (k + 0.5) / npts
        worst = float('inf')
        for y in [y0 + (1 - y0) * j / 8 for j in range(9)]:
            Q = pa.ft_all(acb(x, y), arb(t0), Ns, C, want_deriv=False, want_err=False, want_C=False, moll=primes)
            G = Q['E'] * Q['f']
            c = complex(float(G.real.mid()), float(G.imag.mid()))
            d = abs(c) if c.real >= 0 else abs(c.imag)
            worst = min(worst, d)
        if best is None or worst > best[1]:
            best = (x, worst)
    ctx.prec = old_prec
    return best


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--design', default='X55o8', choices=['X55o8', 'ladder', 'dvp'])
    ap.add_argument('--t0', required=True, help='exact decimal (e.g. 0.34); used as an Arb ball')
    ap.add_argument('--y0', required=True, help='exact decimal (e.g. 0.4); used as an Arb ball')
    ap.add_argument('--primes', default='2,3,5,7')
    ap.add_argument('--X', default='55/8', help='exact rational; must be a binary double (55/8 = 6.875 is)')
    ap.add_argument('--workers', type=int, default=30)
    ap.add_argument('--out', required=True)
    ap.add_argument('--skip-strip', action='store_true')
    ap.add_argument('--nscan', default='40,1500')
    ap.add_argument('--xdirect', type=float, default=200.0,
                    help='use the direct (heat-kernel) evaluator below this x; A+B-C (P15 Thm 1.3, x >= 200) above')
    args = ap.parse_args()
    ctx.prec = PREC
    t0s, y0s = args.t0, args.y0
    T0a, Y0a = arb(t0s), arb(y0s)              # Arb balls containing the exact rationals
    t0, y0 = float(t0s), float(y0s)            # floats: heuristics and printing only
    Xq = Fraction(args.X)
    X = float(Xq)
    assert Fraction(X) == Xq, 'X must be exactly representable as a double'
    c0q = Fraction(t0s) + Fraction(y0s) ** 2 / 2
    primes = tuple(int(p) for p in args.primes.split(','))
    rec = dict(design=args.design, t0=t0s, y0=y0s, c0=float(c0q), c0_exact=f'{c0q.numerator}/{c0q.denominator}',
               params='t0, y0 exact decimal rationals; all Arb computations use balls containing them',
               primes=list(primes), X=X, X_exact=f'{Xq.numerator}/{Xq.denominator}',
               date='2026-09-23', prec_bits=PREC, code='post-repair (exact cover, README 4.6)')
    wall0 = time.time()
    print(f'== row design={args.design} t0={t0s} y0={y0s} c0={rec["c0_exact"]} X={rec["X_exact"]}')
    # ---- analytic part (all designs)
    lo, hi = (int(v) for v in args.nscan.split(','))
    cert = cb.analytic_certificate(T0a, Y0a, primes, N_scan=(lo, hi))
    rec['analytic'] = {k: v for k, v in cert.items() if k not in ('bottom', 'top', 'crude', 't0', 'y0')}
    rec['analytic']['n_bottom_pieces'] = len(cert['bottom'])
    rec['analytic']['n_top_pieces'] = len(cert['top'])
    rec['analytic']['n_crude_pieces'] = len(cert['crude'])
    print(f'  analytic: ok={cert["ok"]} N_s={cert["N_s"]} N1={cert.get("N1")}')
    if not cert['ok']:
        rec['status'] = 'analytic part failed'
        json.dump(rec, open(args.out, 'w'), indent=1, default=float)
        return
    Ns = cert['N_s']
    C = pa.Coeffs(T0a, Ns + 20)
    xL, score = pick_left_edge(Ns, T0a, y0, primes, C)
    ctx.prec = PREC
    # outward-rounded region limits (Arb from the exact parameters, then f_down / f_up to doubles):
    # canopy region = {x >= X + sqrt(1-y0^2), y0 <= y <= sqrt(1-2t0)}; left edge on [y0, 1]
    ya = rg.f_down(Y0a)
    ytop = rg.f_up((1 - 2 * T0a).sqrt())
    xs = rg.f_down(arb(X) + (1 - Y0a * Y0a).sqrt())
    xL_seg_ok = bool(pa.xN(Ns, T0a).upper() <= xL) and bool(arb(xL) < pa.xN(Ns + 1, T0a).lower())
    le = smallx.left_edge(xL, ya, T0a, primes, C, Ns)
    le['ok'] = bool(le['ok'] and xL_seg_ok)
    rec['left_edge'] = dict(x_L=xL, float_score=score, y_range=[ya, 1.0], N=Ns, x_L_inside_N_s_segment=xL_seg_ok, **le)
    print(f'  left edge at x_L={xL:.6f}: ok={le["ok"]} min_margin={le["min_margin"]:.3e}')
    rec['canopy_strip'] = dict(x_start=xs, x_L=xL, y_range=[ya, ytop])
    if args.design == 'X55o8':
        ci = smallx.cond_i_rect(X, ya)
        rec['cond_i'] = dict(kind='certified: H_0 zero-free on [0,X]x[y0,1] (zeta form of Thm 1.2(i))', **ci)
        print(f'  (i): ok={ci["ok"]} boxes={ci["boxes"]} min|H0|>={ci["min_absH"]:.4f}')
        br = smallx.barrier_3d(X, T0a, Y0a, nt=40)
        rec['barrier'] = dict(kind='certified: Phi-integral boxes over the exact P15 (iii) region', **br)
        print(f'  (iii): ok={br["ok"]} boxes={br["boxes"]} min|H|>={br["min_absH"]:.4f}')
    else:
        rec['cond_i'] = dict(kind='ASSUMED' if args.design == 'ladder' else 'dVP arithmetic, see README 5.3')
        rec['barrier'] = dict(kind='see barrier_large.py (separate run)')
    if not args.skip_strip and xs < xL:
        ok, res, tiling = run_strip(xs, xL, ya, ytop, t0s, args.workers, x_direct_max=max(200.0, args.xdirect))
        rec['canopy_strip']['x_direct_max'] = max(200.0, args.xdirect)
        rec['strip'] = summarize(res)
        rec['strip']['ok'] = ok
        rec['strip']['coverage_audit'] = dict(
            chunk_tiling_xstart_to_xL=tiling, violations=rec['strip']['audit_violations'],
            boxes_checked=rec['strip']['audit_boxes_checked'], n_segment_pieces=rec['strip']['n_segment_pieces'],
            checks='per box: Arb box contains its float box; per x-box: y-pieces tile [y0, ytop]; per N-piece: '
                   'x-boxes tile the piece; per chunk: N-pieces satisfy the n_segments lemma; chunks tile [x_start, x_L]')
    rec['wall_sec'] = time.time() - wall0
    parts = [cert['ok'], le['ok'], rec.get('strip', {}).get('ok', args.skip_strip)]
    if args.design == 'X55o8':
        parts += [rec['cond_i']['ok'], rec['barrier']['ok']]
    rec['all_certified_here'] = all(parts)
    json.dump(rec, open(args.out, 'w'), indent=1, default=float)
    print(f'  => all_certified_here={rec["all_certified_here"]}  wall {rec["wall_sec"]:.0f}s  -> {args.out}')


if __name__ == '__main__':
    main()
