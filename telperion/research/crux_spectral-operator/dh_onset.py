"""Onset of indefiniteness of the Davenport-Heilbronn window form, in BOTH parity sectors, with a
stability study (Galerkin size N, working precision dps, quadrature panels).

Galerkin compression can only RAISE eigenvalues (min-max), so a negative Galerkin eigenvalue computed
accurately certifies indefiniteness of the full window form; nested bases make lambda_1 nonincreasing
in N.  The negative values near the onset are tiny (1e-31 at x = 31), so the question is only whether
the matrix entries are accurate to far better than that: we vary dps and the quadrature panels.

usage: python3 dh_onset.py scan | stability
"""
import sys
import json
import time
import mpmath as mp
import wpw


def lam1(x, N, sector, dps, panels=None):
    mp.mp.dps = dps
    Lam = wpw.lambda_dh(int(mp.floor(mp.mpf(x))))
    Q, L = wpw.build(mp.mpf(x), N, 'dh', sector, Lam=Lam, panels=panels)
    E = mp.eigsy(Q, eigvals_only=True)
    E = sorted(E)
    return E[0], E[1]


def scan():
    rows = []
    for x in ['28', '29', '30', '30.5', '31', '31.5', '32', '33', '34', '35', '36', '38', '40']:
        for sector in ('even', 'odd'):
            t0 = time.time()
            l1, l2 = lam1(x, 60, sector, 120)
            row = dict(x=x, sector=sector, N=60, dps=120, lambda1=mp.nstr(l1, 5), lambda2=mp.nstr(l2, 5),
                       seconds=round(time.time() - t0, 1))
            rows.append(row)
            print(json.dumps(row), flush=True)
    json.dump(rows, open('dh_onset_scan.json', 'w'), indent=1)


def stability():
    rows = []
    for (x, sector) in [('31', 'even'), ('30.5', 'even')]:
        for (N, dps, pan) in [(50, 100, None), (60, 120, None), (60, 200, None), (60, 120, 360), (70, 140, None), (80, 160, None)]:
            t0 = time.time()
            l1, l2 = lam1(x, N, sector, dps, pan)
            row = dict(x=x, sector=sector, N=N, dps=dps, panels=pan if pan else max(40, 2 * N),
                       lambda1=mp.nstr(l1, 8), lambda2=mp.nstr(l2, 5), seconds=round(time.time() - t0, 1))
            rows.append(row)
            print(json.dumps(row), flush=True)
    json.dump(rows, open('dh_onset_stability.json', 'w'), indent=1)


if __name__ == '__main__':
    {'scan': scan, 'stability': stability}[sys.argv[1]]()
