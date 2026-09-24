# Faster certificate generator: vectorised float power iteration on the max-operator, then ONE exact
# integer check with the Lean-mirror algorithm (cert_gen.Cert.lam_of).
import sys, json, math
import numpy as np
from fractions import Fraction as Fr
from cert_gen import Cert, galerkin_vec

def ranges(cert):
    N, H = cert.N, cert.H
    k = np.arange(N, dtype=object)
    out = []
    for d in cert.ds:
        A, B = d['A'], d['B']
        # minus side
        mlo = np.array([max(int(kk) * H - B, 0) // H for kk in range(N)])
        mhi = np.array([min(((kk + 1) * H - A) // H, N - 1) for kk in range(N)])
        mok = np.array([not ((kk + 1) * H < A) for kk in range(N)])
        plo0 = np.array([(kk * H + A) // H for kk in range(N)])
        pok = plo0 <= N
        plo = np.minimum(plo0, N - 1)
        phi = np.array([min((kk * H + H + B) // H, N - 1) for kk in range(N)])
        out.append((d['C'], mlo, mhi, mok, plo, phi, pok))
    return out

def apply_max(w, rg, S):
    N = len(w)
    tot = np.zeros(N)
    for (C, mlo, mhi, mok, plo, phi, pok) in rg:
        c = C / S
        for (lo, hi, ok) in ((mlo, mhi, mok), (plo, phi, pok)):
            L = hi - lo + 1
            m = np.zeros(N)
            valid = ok & (L >= 1)
            maxlen = int(L[valid].max()) if valid.any() else 0
            for t in range(maxlen):
                idx = np.clip(lo + t, 0, N - 1)
                sel = valid & (t < L)
                m = np.where(sel, np.maximum(m, w[idx]), m)
            tot += c * m
    return tot

if __name__ == "__main__":
    Lp = Fr(int(sys.argv[1]), int(sys.argv[2])); N = int(sys.argv[3]); iters = int(sys.argv[4])
    out = sys.argv[5] if len(sys.argv) > 5 else None
    cert = Cert(Lp, N)
    lam_g, v = galerkin_vec(cert.Lp, cert.N, cert.pp)
    rg = ranges(cert)
    w = v / v.max(); best = None
    for it in range(iters):
        r = apply_max(w, rg, cert.S)
        ratio = (r / w).max()
        if best is None or ratio < best[0]:
            best = (ratio, w.copy())
        w = 0.5 * w + 0.5 * r / r.max(); w = w / w.max()
    wf = best[1]
    wi = [max(1, int(round(1e9 * x))) for x in wf]
    Lam, rs = cert.lam_of(wi)
    assert all(r <= Lam * wk for r, wk in zip(rs, wi)) and all(x > 0 for x in wi)
    print(f"L'={Lp} N={N} galerkin_lower={lam_g:.6f} float_best={best[0]:.6f} exact Lam/S={Lam}/{cert.S}={Lam / cert.S:.6f} Wmax={max(wi)} minw={min(wi)}")
    if out:
        json.dump(dict(Lp=[Lp.numerator, Lp.denominator], N=N, H=cert.H, S=cert.S, Lam=Lam, w=wi, Wmax=max(wi),
                       ds=[dict(n=d['n'], p=d['p'], k=d['k'], A=d['A'], B=d['B'], C=d['C'],
                                s=[d['s'].numerator, d['s'].denominator]) for d in cert.ds],
                       galerkin_lower=lam_g), open(out, 'w'))
        print("wrote", out)
