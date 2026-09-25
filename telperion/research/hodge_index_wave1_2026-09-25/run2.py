from sq import *
N = 48
def build(x):
    A = mp.log(x) / 2; nm = int(x)
    wZ = weights_mp('ZK', nm); wL = w_LG(nm); cr = cross_weights(nm, None)
    avg = [(wZ[n] + wL[n]) / 2 for n in range(nm + 1)]
    out = []
    for par in (0, 1):
        fm = form_with(A, [mp.mpf(0)] * (nm + 1)); G, P = sector_parts(fm, A, N, par)
        def comb(w):
            f2 = form_with(A, w); f2.fams = fm.fams
            return sector_parts(f2, A, N, par)[1]['comb']
        atoms = {}
        for n in range(2, nm + 1):
            if abs(cr[n]) > 1e-20:
                e = [mp.mpf(0)] * (nm + 1); e[n] = cr[n]; atoms[n] = comb(e)
        out.append((G, P['pole'], P['arch'], comb(avg), atoms))
    return out
def lmin(M, G): return gmin(M, G)[0]
for x in [12, 16, 18, 19, 19.5, 19.82, 20, 21, 22, 24, 28]:
    secs = build(x)
    def Qt(t, s): G, pole, arch, CA, atoms = s; return pole + arch - CA - t * sum(atoms.values())
    def tstar():
        lo, hi = 0.0, 4.0
        if min(lmin(Qt(hi, s), s[0]) for s in secs) > 0: return '>4'
        for _ in range(30):
            m = (lo + hi) / 2
            if min(lmin(Qt(m, s), s[0]) for s in secs) > 0: lo = m
            else: hi = m
        return '%.4f' % lo
    # attribution on E's lowest eigvec
    best = None
    for par, s in enumerate(secs):
        G = s[0]; e, V = gmin(Qt(1, s), G, vec=True); v = V[:, 0]; v = v / np.sqrt(v @ G @ v)
        if best is None or e[0] < best[0]: best = (e[0], par, v, s)
    e0, par, v, s = best; G, pole, arch, CA, atoms = s
    att = ' '.join('%d:%+.3f' % (n, -(v @ C @ v)) for n, C in sorted(atoms.items()))
    print('x=%.2f t*=%s | lamE=%+.2e par%d pole=%+.3f arch=%+.3f -avgcomb=%+.3f cross atoms[%s]' % (x, tstar(), e0, par, v @ pole @ v, v @ arch @ v, -(v @ CA @ v), att), flush=True)
