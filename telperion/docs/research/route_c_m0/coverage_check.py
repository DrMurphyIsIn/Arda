"""Independent coverage check of the exact-cover repair (README section 4.6), with negative controls.

The certifiers audit their own cover as they run (canopy_mesh.cover_strip, smallx, barrier_large).  This
script checks the same property a second way, from the Arb boxes that were actually evaluated: every
accepted box is recorded (as returned by the certifier), and the check asks only
  (x) does the union of the recorded x-balls cover the region's x-range, with no gap;
  (N) for every N, does the union of the balls evaluated with that N cover [max(x0, x_N), min(x1, x_{N+1})]
      (exact x_N = 4 pi N^2 - pi t/4 for every t in the ball), i.e. every x lies in a box whose N is the
      correct one on the closed segment;
  (y) do the y-balls of every x-box cover the region's y-range;
  (t) (barrier) do the t-balls of every slab contain the slab, and do the slabs cover [0, t0].
It does not use the construction's own claims (grid endpoints, n_segments); it looks only at the balls.

Runs:
  B1  every slab of the design-B (dvp) barrier       (40 slabs, N = 140)
  B2  every slab of the design-C (ladder) barrier    (60 slabs, N = 319)
  W*  design-A canopy windows where the pre-repair code left slivers: [2097200, 2097302] and
      [1500000, 1500060] (c0 = 0.42), and 3-unit windows around the N-jumps 350, 380, 400, 408 (c0 = 0.42)
      and 170 (c0 = 0.48).
  NEG negative controls: the same checks on the PRE-REPAIR ball (float midpoint) and N-segment padding
      (+-1e-12), which must fail both this check and cover_strip's built-in audit; and the pre-repair
      chunk grid of the c0 = 0.45 row, whose direct chunks ended 2.8e-14 below x = 200.
Writes results/coverage_check.json.

Full-row mode:  python coverage_check.py --full-row results/row_X55o8_....json [workers]
re-runs every chunk of a complete design-A strip with recording, checks each chunk's cover
independently (x, N, y as above), checks that the chunks tile [x_start, x_L], and writes
results/coverage_full_<row>.json.
"""
import json
import math
import os
import sys
import time
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from flint import arb, acb, ctx  # noqa: E402

import canopy_mesh as cm  # noqa: E402
import p15_arb as pa  # noqa: E402
import rigor as rg  # noqa: E402
import smallx  # noqa: E402

PREC = 80
REC = []
_ORIG_BOX_ABC = cm.certify_box_abc


def _recording_box_abc(xa, xb, ya, yb, t, C, N):
    r = _ORIG_BOX_ABC(xa, xb, ya, yb, t, C, N)
    if r[0]:
        Z = r[4]
        REC.append(dict(xl=Z.real.lower(), xu=Z.real.upper(), yl=Z.imag.lower(), yu=Z.imag.upper(),
                        tl=arb(t).lower(), tu=arb(t).upper(), N=N, key=(xa, xb)))
    return r


_ORIG_BOX_DIRECT = cm.certify_box_direct


def _recording_box_direct(xa, xb, ya, yb, t):
    r = _ORIG_BOX_DIRECT(xa, xb, ya, yb, t)
    if r[0]:
        Z = r[4]
        REC.append(dict(xl=Z.real.lower(), xu=Z.real.upper(), yl=Z.imag.lower(), yu=Z.imag.upper(),
                        tl=arb(t).lower(), tu=arb(t).upper(), N=None, key=(xa, xb)))
    return r


def union_gaps(intervals, lo, hi):
    """Gaps of the union of [a, b] (exact arbs) inside [lo, hi]; returns a list of gap widths (floats)."""
    iv = sorted(intervals, key=lambda p: float(p[0].mid()))
    gaps = []
    cover = lo
    for a, b in iv:
        if not (a <= cover):
            gaps.append(float((a - cover).mid()))
        if b > cover:
            cover = b
    if not (cover >= hi):
        gaps.append(float((hi - cover).mid()))
    return gaps


def check_records(x0, x1, ya, yb, t_lo, t_hi, t_ball):
    """Independent checks (x), (N), (y), (t) on REC for the region [x0,x1] x [ya,yb] x [t_lo,t_hi]."""
    X0, X1, YA, YB = arb(x0), arb(x1), arb(ya), arb(yb)
    xg = union_gaps([(r['xl'], r['xu']) for r in REC], X0, X1)
    bad_n = []
    for N in sorted(set(r['N'] for r in REC if r['N'] is not None)):
        lo, hi = pa.xN(N, t_ball), pa.xN(N + 1, t_ball)
        L = X0 if X0 >= lo.upper() else lo.lower()
        U = X1 if X1 <= hi.lower() else hi.upper()
        g = union_gaps([(r['xl'], r['xu']) for r in REC if r['N'] == N], L, U)
        if g:
            bad_n.append(dict(N=N, n_gaps=len(g), max_gap=max(g)))
    by = defaultdict(list)
    for r in REC:
        by[r['key']].append((r['yl'], r['yu']))
    y_bad = sum(1 for v in by.values() if union_gaps(v, YA, YB))
    t_bad = sum(1 for r in REC if not (r['tl'] <= arb(t_lo) and r['tu'] >= arb(t_hi)))
    return dict(boxes=len(REC), x_gaps=len(xg), max_x_gap=max(xg, default=0.0), N_segments_uncovered=bad_n,
                x_boxes_with_y_gap=y_bad, boxes_missing_t=t_bad,
                covered=(not xg and not bad_n and y_bad == 0 and t_bad == 0))


def barrier_rows():
    """B1, B2: every slab of the certified dvp and ladder barriers (parameters from results/*.json)."""
    here = os.path.dirname(os.path.abspath(__file__))
    out = {}
    for name, fn, nt in (('B1_dvp', 'row_dvp_c0_0.4999989.json', 40), ('B2_ladder', 'row_ladder_c0_0.4288.json', 60)):
        row = json.load(open(os.path.join(here, 'results', fn)))
        X, t0s, y0s = row['X'], row['t0'], row['y0']
        T0, Y0 = arb(t0s), arb(y0s)
        slabs = smallx.t_slabs(T0, nt)
        res = []
        for k, (ta, tb) in enumerate(slabs):
            REC.clear()
            tt = rg.hull(ta, tb)
            xr, ylo, yhi = smallx.slab_limits(X, T0, Y0, tt)
            # the region limits themselves, re-derived: x <= X + sqrt(1-y0^2); y-range for every t in the slab
            lim_ok = (bool(arb(xr) >= (arb(X) + (1 - Y0 * Y0).sqrt()).upper())
                      and bool(arb(ylo) <= (Y0 * Y0 + 2 * (T0 - tt)).sqrt().lower())
                      and (yhi == 1.0 or bool(arb(yhi) >= (1 - 2 * tt).sqrt().upper())))
            C = pa.Coeffs(tt, int(math.sqrt(xr / (4 * math.pi) + 1)) + 4)
            st = cm.cover_strip(X, xr, ylo, yhi, tt, 'abc', C, w0=0.05, grow=1.3)
            chk = check_records(X, xr, ylo, yhi, arb(ta).lower(), arb(tb).upper(), tt)
            chk.update(slab=k, ok=st['ok'], builtin_audit_violations=st['audit_violations'], limits_ok=lim_ok)
            res.append(chk)
        t_cover = (slabs[0][0] == 0.0 and all(slabs[k][1] == slabs[k + 1][0] for k in range(nt - 1))
                   and slabs[-1][1] is T0)
        out[name] = dict(X=X, t0=t0s, y0=y0s, slabs=nt, t_slabs_cover_0_t0=t_cover,
                         all_slabs_covered=all(r['covered'] and r['ok'] and r['limits_ok'] for r in res),
                         boxes=sum(r['boxes'] for r in res), x_gaps=sum(r['x_gaps'] for r in res),
                         builtin_audit_violations=sum(r['builtin_audit_violations'] for r in res))
        print(name, out[name], flush=True)
    return out


def window(t0s, y0s, a, b):
    T = arb(t0s)
    ya = rg.f_down(arb(y0s))
    ytop = rg.f_up((1 - 2 * T).sqrt())
    REC.clear()
    C = pa.Coeffs(T, int(math.sqrt(b / (4 * math.pi) + 1)) + 20)
    st = cm.cover_strip(a, b, ya, ytop, T, 'abc', C, w0=0.1, grow=1.3)
    chk = check_records(a, b, ya, ytop, T.lower(), T.upper(), T)
    chk.update(window=[a, b], t0=t0s, ok=st['ok'], builtin_audit_violations=st['audit_violations'],
               builtin_audit_first=st.get('audit_first'), segments=st['segments'])
    return chk


def canopy_windows():
    wins = [('0.34', '0.4', 2097200.0, 2097302.0), ('0.34', '0.4', 1500000.0, 1500060.0)]
    for t0s, N in (('0.34', 350), ('0.34', 380), ('0.34', 400), ('0.34', 408), ('0.4', 170)):
        a = math.floor(float(pa.xN(N, arb(t0s)).mid())) - 1.0
        wins.append((t0s, '0.4', a, a + 3.0))
    out = []
    for t0s, y0s, a, b in wins:
        r = window(t0s, y0s, a, b)
        out.append(r)
        print('W', r['window'], 't0', t0s, 'covered', r['covered'], 'ok', r['ok'], 'x_gaps', r['x_gaps'],
              'N-bad', r['N_segments_uncovered'], 'audit', r['builtin_audit_violations'], flush=True)
    return out


# ---------------- negative controls: the pre-repair constructions ----------------

def _old_box(xa, xb, ya, yb):
    """PRE-REPAIR box: arb(fl((xa+xb)/2), (xb-xa)/2) -- may miss an endpoint by half an ulp."""
    xm, ym = (xa + xb) / 2, (ya + yb) / 2
    hx, hy = (xb - xa) / 2, (yb - ya) / 2
    return (acb(arb(xm, hx), arb(ym, hy)), acb(xm, ym), arb(hx), arb(hy), arb(math.hypot(hx, hy)))


def _old_n_segments(x0, x1, t):
    """PRE-REPAIR N-segments: ends padded by +-1e-12 in double arithmetic."""
    t = arb(t)
    N = int(math.floor(math.sqrt(x0 / (4 * math.pi) + float(t.mid()) / 16)))
    while True:
        lo, hi = pa.xN(N, t), pa.xN(N + 1, t)
        if float(lo.upper()) <= x0 < float(hi.lower()):
            break
        N = N - 1 if x0 < float(lo.upper()) else N + 1
    pieces, a = [], x0
    while a < x1:
        hi = pa.xN(N + 1, t)
        b = min(x1, float(hi.upper()) + 1e-12)
        pieces.append((a, b, N))
        a = max(a, float(hi.lower()) - 1e-12)
        if b >= x1:
            break
        N += 1
    return pieces


def negative_controls():
    out = {}
    saved_box, saved_seg = rg.box, cm.n_segments
    try:
        rg.box = _old_box
        r = window('0.34', '0.4', 2097200.0, 2097302.0)
        out['NEG1_old_ball_window_2097200'] = dict(independent_check_fails=not r['covered'], x_gaps=r['x_gaps'],
                                                   max_x_gap=r['max_x_gap'],
                                                   builtin_audit_flags=r['builtin_audit_violations'] > 0)
        rg.box = saved_box
        cm.n_segments = _old_n_segments
        a = math.floor(float(pa.xN(408, arb('0.34')).mid())) - 1.0
        r = window('0.34', '0.4', a, a + 3.0)
        out['NEG2_old_padding_N408'] = dict(independent_check_fails=not r['covered'],
                                            N_segments_uncovered=r['N_segments_uncovered'],
                                            builtin_audit_flags=r['builtin_audit_violations'] > 0,
                                            builtin_audit_first=r['builtin_audit_first'])
    finally:
        rg.box, cm.n_segments = saved_box, saved_seg
    # pre-repair chunk grid of the c0 = 0.45 row: direct chunks on [x_start, 200], abc chunks from 200
    xs, xd = 7.791515138991168, 200.0
    n = max(1, int(math.ceil((xd - xs) / 4.0)))
    old_pts = [xs + (xd - xs) * k / n for k in range(n + 1)]
    new_pts = rg.grid(xs, xd, n)
    out['NEG3_old_chunk_grid_c0_0.45'] = dict(old_last_point=old_pts[-1], target=xd,
                                              old_gap_below_200=xd - old_pts[-1],
                                              old_tiles=rg.chain_ok(list(zip(old_pts[:-1], old_pts[1:])), xs, xd),
                                              new_tiles=rg.chain_ok(list(zip(new_pts[:-1], new_pts[1:])), xs, xd))
    out['all_negative_controls_behave'] = (out['NEG1_old_ball_window_2097200']['independent_check_fails']
                                           and out['NEG1_old_ball_window_2097200']['builtin_audit_flags']
                                           and out['NEG2_old_padding_N408']['independent_check_fails']
                                           and out['NEG2_old_padding_N408']['builtin_audit_flags']
                                           and not out['NEG3_old_chunk_grid_c0_0.45']['old_tiles']
                                           and out['NEG3_old_chunk_grid_c0_0.45']['new_tiles'])
    print('NEG', json.dumps(out, default=str), flush=True)
    return out


def _full_row_chunk(args):
    """Worker: re-run one strip chunk exactly as certify_route does, record every accepted Arb box, and
    check the chunk's cover independently.  Returns only the verdict and counts."""
    x0, x1, ya, yb, t0s, mode = args
    ctx.prec = PREC
    cm.certify_box_abc = _recording_box_abc
    cm.certify_box_direct = _recording_box_direct
    REC.clear()
    T = arb(t0s)
    if mode == 'abc':
        C = pa.Coeffs(T, int(math.sqrt(x1 / (4 * math.pi) + 1)) + 4)
        st = cm.cover_strip(x0, x1, ya, yb, T, 'abc', C, w0=0.1, grow=1.3, max_evals=int(400 * (x1 - x0)) + 20000)
    else:
        st = cm.cover_strip(x0, x1, ya, yb, T, 'direct', w0=0.2, grow=1.3)
    chk = check_records(x0, x1, ya, yb, T.lower(), T.upper(), T)
    return dict(x0=x0, x1=x1, mode=mode, ok=st['ok'], covered=chk['covered'], boxes=chk['boxes'],
                x_gaps=chk['x_gaps'], n_bad=len(chk['N_segments_uncovered']), y_bad=chk['x_boxes_with_y_gap'],
                t_bad=chk['boxes_missing_t'], builtin_audit_violations=st['audit_violations'])


def full_row(row_path, workers):
    """Independent check of a COMPLETE design-A strip: the same chunks as certify_route.run_strip (read
    from the row record), every chunk re-run with recording and checked, and the chunk tiling checked."""
    from concurrent.futures import ProcessPoolExecutor
    import certify_route as cr
    row = json.load(open(row_path))
    cs = row['canopy_strip']
    xs, xe = cs['x_start'], cs['x_L']
    ya, yb = cs['y_range']
    t0s = row['t0']
    xd = min(max(xs, cs.get('x_direct_max', 200.0)), xe)
    jobs = []
    if xs < xd:
        n = max(1, int(math.ceil((xd - xs) / 4.0)))
        jobs += [(a, b, ya, yb, t0s, 'direct') for a, b in cr.chunks(xs, xd, n)]
    n = max(1, int(math.ceil((xe - xd) / 2000.0)))
    n = max(n, min(workers * 4, int((xe - xd) / 50) + 1))
    jobs += [(a, b, ya, yb, t0s, 'abc') for a, b in cr.chunks(xd, xe, n)]
    t_start = time.time()
    with ProcessPoolExecutor(workers) as ex:
        res = list(ex.map(_full_row_chunk, jobs))
    tiles = rg.chain_ok([(r['x0'], r['x1']) for r in sorted(res, key=lambda r: r['x0'])], xs, xe)
    out = dict(row=os.path.basename(row_path), strip=[xs, xe], y_range=[ya, yb], t0=t0s, chunks=len(res),
               chunks_tile_strip=tiles, all_chunks_ok=all(r['ok'] for r in res),
               all_chunks_covered=all(r['covered'] for r in res),
               boxes=sum(r['boxes'] for r in res), boxes_in_row_record=row['strip']['boxes'],
               x_gaps=sum(r['x_gaps'] for r in res), N_segments_uncovered=sum(r['n_bad'] for r in res),
               x_boxes_with_y_gap=sum(r['y_bad'] for r in res), boxes_missing_t=sum(r['t_bad'] for r in res),
               builtin_audit_violations=sum(r['builtin_audit_violations'] for r in res),
               wall_sec=time.time() - t_start)
    out['verdict_covered'] = bool(tiles and out['all_chunks_ok'] and out['all_chunks_covered'])
    return out


if __name__ == '__main__' and len(sys.argv) > 1 and sys.argv[1] == '--full-row':
    ctx.prec = PREC
    path, workers = sys.argv[2], int(sys.argv[3]) if len(sys.argv) > 3 else 30
    res = full_row(path, workers)
    here = os.path.dirname(os.path.abspath(__file__))
    name = os.path.basename(path).replace('row_', 'coverage_full_')
    json.dump(res, open(os.path.join(here, 'results', name), 'w'), indent=1, default=str)
    print(json.dumps(res, indent=1, default=str))
    sys.exit(0)

if __name__ == '__main__':
    ctx.prec = PREC
    cm.certify_box_abc = _recording_box_abc
    t_start = time.time()
    res = dict(barriers=barrier_rows(), canopy_windows=canopy_windows(), negative_controls=negative_controls())
    res['all_repaired_runs_covered'] = (all(v['all_slabs_covered'] and v['t_slabs_cover_0_t0']
                                            for v in res['barriers'].values())
                                        and all(w['covered'] and w['ok'] and w['builtin_audit_violations'] == 0
                                                for w in res['canopy_windows']))
    res['sec'] = time.time() - t_start
    here = os.path.dirname(os.path.abspath(__file__))
    json.dump(res, open(os.path.join(here, 'results', 'coverage_check.json'), 'w'), indent=1, default=str)
    print('all_repaired_runs_covered =', res['all_repaired_runs_covered'],
          ' negative controls behave =', res['negative_controls']['all_negative_controls_behave'])
