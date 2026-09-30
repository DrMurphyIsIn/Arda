from amp import *
gD = 85.699348
for x, kmax in [(31., 3), (20., 4), (12., 5), (8., 6)]:
    best = None
    for frac in [0.2, 0.3, 0.45]:
        for tau in np.arange(-1.5, 1.51, 0.25):
            te = Test(x, frac, 2, gD - tau)
            P = prime_side('D', te, list(range(1, kmax + 1)))
            s = [P[k]['s'].real for k in range(1, kmax + 1)]
            neg = [k for k in range(1, kmax + 1) if s[k - 1] < 0]
            if neg and (best is None or neg[0] < best[0]): best = (neg[0], frac, tau, s)
    if best:
        k, frac, tau, s = best
        print(f'D x={x}: first neg k={k} window x^k={x**k:.4g} frac={frac} tau={tau:+.2f}  s=' + ' '.join(f'{v:+.3e}' for v in s), flush=True)
    else:
        print(f'D x={x}: no neg up to k={kmax} (window {x**kmax:.3g})', flush=True)
