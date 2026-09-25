from sq import *
import time
def mins(M, G): return gmin(M, G)[0]
N = int(sys.argv[1]) if len(sys.argv) > 1 else 64
xs = [float(v) for v in sys.argv[2].split(',')] if len(sys.argv) > 2 else [18, 19, 19.5, 19.8, 19.9, 20.5, 21, 22, 24]
for x in xs:
    t = time.time(); A = mp.log(x) / 2; nm = int(x)
    wZ = weights_mp('ZK', nm); wL = w_LG(nm); cE = weights_mp('E', nm)
    cr = cross_weights(nm, None); c2 = cross_weights(nm, 2)
    avg = [(wZ[n] + wL[n]) / 2 for n in range(nm + 1)]
    res = {}
    for par in (0, 1):
        fm = form_with(A, [mp.mpf(0)] * (nm + 1))
        G, P = sector_parts(fm, A, N, par)
        pole, arch = P['pole'], P['arch']
        def comb(w):
            f2 = form_with(A, w); f2.fams = fm.fams
            return sector_parts(f2, A, N, par)[1]['comb']
        CZ, CL, CE, CC, C2 = comb(wZ), comb(wL), comb(cE), comb(cr), comb(c2)
        forms = dict(ZK=pole + arch - CZ, LG=arch - CL, E=pole + arch - CE,
                     avg=0.5 * pole + arch - (CZ + CL) / 2,
                     R=0.5 * pole - CC, Equad=pole + arch - (CZ + CL) / 2 - C2,
                     ArchPole=pole + arch)
        for k, M in forms.items():
            res.setdefault(k, []).append(mins(M, G))
        # alignment: lowest eigvec of E, evaluate avg and R on it
        e, V = gmin(forms['E'], G, vec=True); v = V[:, 0]; v = v / np.sqrt(v @ G @ v)
        res.setdefault('E_vec', []).append((e[0], v @ forms['avg'] @ v, v @ forms['R'] @ v))
    line = 'x=%.2f ' % x + ' '.join('%s=%+.3e' % (k, min(v)) for k, v in res.items() if k != 'E_vec')
    pe = int(np.argmin([t_[0] for t_ in res['E_vec']])); ev = res['E_vec'][pe]
    print(line, '| Evec(par%d): Q_E=%+.3e avg=%+.3e R=%+.3e  (%.0fs)' % (pe, ev[0], ev[1], ev[2], time.time() - t), flush=True)
