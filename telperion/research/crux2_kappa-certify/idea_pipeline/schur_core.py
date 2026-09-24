"""Kernel-checkable core of the a = 249/256 even-sector certificate.
M = leading 450x450 block of R_560 (even).  With lam0 fixed, split M - lam0 I = [[A, B], [B^T, C]]
(A = k x k leading modes).  Arb certifies C := C - lam0 I > 0 (verified LDL^T) and computes the Schur
complement S = A - B C^{-1} B^T rigorously (arb_mat.solve).  M - lam0 I >= 0  <=>  S >= 0 (C > 0).
Output: S midpoints rounded to rationals s_ij/10^P with a uniform half-width w0 covering the Arb ball +
rounding, and an EXACT rational LDL^T of S_mid - delta I (delta > k w0) for the Lean kernel."""
import flint, json, sys, time
from flint import arb, arb_mat, fmpq, fmpz
from certify import Window, build_leading
import vldlt

def main(k=8, lam0=4.39e-28, P=48, sector='even', T=560.0, N=450, tag=''):
    flint.ctx.prec = 256
    a = arb(249) / 256
    win = Window(a, T)
    M, _ = build_leading(win, sector, N)
    n = M.nrows()
    l0 = arb(lam0)
    # C - lam0 I > 0
    C = arb_mat([[M[i, j] - (l0 if i == j else 0) for j in range(k, n)] for i in range(k, n)])
    vr = vldlt.verify(C, 0.0 + 1e-40, b=64)   # certify C - lam0 I >= 1e-40 I (> 0)
    print("C - lam0 I > 1e-40 I certified:", vr['ok'], "resid", vr['Efro'].str(3) if vr['ok'] else vr)
    assert vr['ok']
    Bt = arb_mat([[M[i, j] for j in range(k)] for i in range(k, n)])        # (n-k) x k
    X = C.solve(Bt)                                                        # C^{-1} B^T, rigorous
    A = arb_mat([[M[i, j] - (l0 if i == j else 0) for j in range(k)] for i in range(k)])
    S = A - Bt.transpose() * X
    S = arb_mat([[(S[i, j] + S[j, i]) / 2 for j in range(k)] for i in range(k)])   # symmetrize (true S is symmetric)
    maxrad = max(float(S[i, j].rad()) for i in range(k) for j in range(k))
    print("Schur complement S (k=%d): max radius %.3e" % (k, maxrad))
    # rational midpoints
    den = fmpz(10) ** P
    Smid = [[fmpq(int((S[i, j].mid() * arb(den)).floor().unique_fmpz() if False else 0), 1) for j in range(k)] for i in range(k)]
    Sq = []
    for i in range(k):
        row = []
        for j in range(k):
            v = S[i, j].mid() * arb(10) ** P
            # round to nearest integer
            f = v.floor()
            num = int(f.unique_fmpz()) if f.unique_fmpz() is not None else int(float(f.mid()))
            row.append(fmpq(num, 10 ** P))
        Sq.append(row)
    for i in range(k):
        for j in range(i):
            Sq[i][j] = Sq[j][i]
    # half-width: |S_true - Sq| <= rad(S) + |mid - Sq| (<= 10^-P) ; take w0 = 2*10^-P + maxrad (rounded up)
    w0 = fmpq(2, 10 ** P) + fmpq(int(maxrad * 1e70) + 1, 10 ** 70)
    for i in range(k):
        for j in range(k):
            d = abs(S[i, j] - arb(Sq[i][j]))
            assert d < arb(w0), (i, j)
    # lam_min of Sq (floating, for choosing delta)
    Sm = arb_mat([[arb(Sq[i][j]) for j in range(k)] for i in range(k)])
    def pd(l):
        L_, D_, jj, s = vldlt.floating_ldlt(Sm, l, b=64)
        return L_ is not None
    hi_ = 1.0
    while pd(hi_): hi_ *= 2
    lo_ = hi_ / 2
    while not pd(lo_):
        lo_ /= 2
        if lo_ < 1e-300: raise SystemExit("S not PD")
    for _ in range(50):
        m = (lo_ + hi_) / 2
        if pd(m): lo_ = m
        else: hi_ = m
    print("lam_min(S_mid) ~ %.6e ; k*w0 = %.3e" % (lo_, float(k * w0.p) / float(w0.q)))
    # delta: a short rational below lam_min, above k*w0
    delta = fmpq(int(lo_ * 0.5 * 1e40) , 10 ** 40)
    kw0 = k * w0
    print("delta =", float(delta.p) / float(delta.q), " k*w0 =", float(kw0.p) / float(kw0.q), " delta > k w0:", delta > kw0)
    assert delta > kw0
    # exact rational LDL^T of Sq - delta I
    Aq = [[Sq[i][j] - (delta if i == j else 0) for j in range(k)] for i in range(k)]
    L = [[fmpq(0)] * k for _ in range(k)]
    D = [fmpq(0)] * k
    for j in range(k):
        s = Aq[j][j] - sum((L[j][m] * L[j][m] * D[m] for m in range(j)), fmpq(0))
        assert s > 0, ("pivot", j, s)
        D[j] = s
        L[j][j] = fmpq(1)
        for i in range(j + 1, k):
            L[i][j] = (Aq[i][j] - sum((L[i][m] * L[j][m] * D[m] for m in range(j)), fmpq(0))) / s
    # exact check
    for i in range(k):
        for j in range(k):
            assert sum((L[i][m] * D[m] * L[j][m] for m in range(k)), fmpq(0)) == Aq[i][j]
    maxdig = max(max(len(str(abs(x.p))), len(str(x.q))) for x in D + [L[i][j] for i in range(k) for j in range(k)])
    print("exact LDL^T ok; max digits in L, D:", maxdig)
    out = dict(k=k, lam0=str(lam0), P=P, w0=[int(w0.p), int(w0.q)], delta=[int(delta.p), int(delta.q)],
               S=[[[int(Sq[i][j].p), int(Sq[i][j].q)] for j in range(k)] for i in range(k)],
               L=[[[int(L[i][j].p), int(L[i][j].q)] for j in range(k)] for i in range(k)],
               D=[[int(d.p), int(d.q)] for d in D],
               lam_min_S=lo_, C_certified_resid=vr['Efro'].str(5))
    json.dump(out, open('schur_core_k%d%s.json' % (k, tag), 'w'))
    return out

if __name__ == '__main__':
    if len(sys.argv) > 2 and sys.argv[2] == 'odd':
        main(k=int(sys.argv[1]), lam0=1.25e-24, P=44, sector='odd', T=800.0, N=620, tag='_odd')
    else:
        main(k=int(sys.argv[1]) if len(sys.argv) > 1 else 8)
