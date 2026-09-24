"""Two-sided coefficient rigidity: Lambda(n0) -> Lambda(n0)(1+s*delta), all else zeta; find onset window x."""
import sys, json
import mpmath as mp
import wpw

def lam_pert(nmax, n0, fac):
    lam = wpw.von_mangoldt(nmax)
    if n0 <= nmax:
        lam[n0] = lam[n0] * fac
    return lam

def lmin(x, n0, fac, N=28, dps=50):
    mp.mp.dps = dps
    out = []
    for sector in ('even', 'odd'):
        Lam = lam_pert(int(mp.floor(mp.mpf(x))), n0, mp.mpf(fac))
        Q, L = wpw.build(mp.mpf(x), N, 'zeta', sector, Lam=Lam)
        E = sorted(mp.eigsy(Q, eigvals_only=True))
        out.append(E[0])
    return min(out), out

def onset(n0, fac, lo, hi, it=12):
    # assume PSD at lo (lo <= n0 means identical to zeta) and find first x where lmin<0 on grid then bisect
    grid = [lo + (hi - lo) * k / 16 for k in range(1, 17)]
    prev = lo
    for x in grid:
        m, _ = lmin(x, n0, fac)
        if m < 0:
            a, b = prev, x
            for _ in range(it):
                c = (a + b) / 2
                if lmin(c, n0, fac)[0] < 0: b = c
                else: a = c
            return (a + b) / 2
        prev = x
    return None

n0 = int(sys.argv[1]); sign = int(sys.argv[2])
rows = []
for d in [1.0, 0.1, 0.01, 1e-3, 1e-4, 1e-5]:
    fac = 1 + sign * d
    hi = n0 + 3.0
    x = onset(n0, fac, float(n0) + 1e-3, hi)
    rows.append(dict(n0=n0, factor=fac, delta=sign * d, onset_x=x, onset_minus_n0=(x - n0) if x else None))
    print(json.dumps(rows[-1]), flush=True)
json.dump(rows, open(f'precision_n{n0}_s{sign}.json', 'w'), indent=1)
