"""Schur-complement core (k x k) from a saved certificate matrix file (lines of 'mid|rad' entries), for the Lean kernel
check.  Usage: schur_core_file.py M_file lam0 k P out.json"""
import sys, json, time
import flint
from flint import arb, arb_mat, fmpq, fmpz
import vldlt

def load(fn):
    rows = []
    for line in open(fn):
        row = []
        for tok in line.split():
            m, r = tok.split('|')
            v = arb(m)
            # saved midpoint has 70 significant digits: add |v| 1e-69 (string rounding) + saved radius (inflated)
            extra = abs(v) * arb('1e-69') + arb(float(r) * 1.02 if float(r) > 0 else 0)   # BUILDER FIX: 3-digit radius strings can round down by up to 1%; inflate by 2%
            row.append(v + arb(0, extra.upper()))
        rows.append(row)
    return arb_mat(rows)

def main(fn, lam0, k, P, out, prec=256):
    flint.ctx.prec = prec
    t0 = time.time()
    M = load(fn)
    n = M.nrows()
    print("loaded %s: n=%d (%.0fs)" % (fn, n, time.time() - t0), flush=True)
    l0 = arb(lam0)
    C = arb_mat([[M[i, j] - (l0 if i == j else 0) for j in range(k, n)] for i in range(k, n)])
    vr = vldlt.verify_chol(C, 1e-55, b=64, fprec=384)   # C - lam0 I >= 1e-55 - resid > 0
    print("C - lam0 I > 0 certified:", vr['ok'], vr.get('Efro').str(3) if vr['ok'] else vr, flush=True)
    assert vr['ok'] and vr['lower'] > 0
    Bt = arb_mat([[M[i, j] for j in range(k)] for i in range(k, n)])
    X = C.solve(Bt)
    A = arb_mat([[M[i, j] - (l0 if i == j else 0) for j in range(k)] for i in range(k)])
    S = A - Bt.transpose() * X
    S = arb_mat([[(S[i, j] + S[j, i]) / 2 for j in range(k)] for i in range(k)])
    maxrad = max(float(S[i, j].rad()) for i in range(k) for j in range(k))
    print("S radius %.3e" % maxrad, flush=True)
    Sq = []
    for i in range(k):
        row = []
        for j in range(k):
            v = (S[i, j].mid() * arb(10) ** P).floor()
            row.append(fmpq(int(v.unique_fmpz()), 10 ** P))
        Sq.append(row)
    for i in range(k):
        for j in range(i):
            Sq[i][j] = Sq[j][i]
    w0 = fmpq(2, 10 ** P) + fmpq(int(maxrad * 10 ** (P + 20)) + 1, 10 ** (P + 20))
    for i in range(k):
        for j in range(k):
            assert abs(S[i, j] - arb(Sq[i][j])) < arb(w0)
    Sm = arb_mat([[arb(Sq[i][j]) for j in range(k)] for i in range(k)])
    # lam_min(Sq) by bisection with floating Cholesky
    def pd(l):
        R_, j_, s_ = vldlt.floating_chol(Sm, l, b=64, fprec=512)
        return R_ is not None
    hi = 1.0
    while pd(hi): hi *= 2
    lo = hi / 2
    while not pd(lo):
        lo /= 2
        if lo < 1e-300: raise SystemExit("S not PD")
    for _ in range(60):
        m = (lo + hi) / 2
        if pd(m): lo = m
        else: hi = m
    delta = fmpq(int(lo * 0.5 * 10 ** 60), 10 ** 60) if lo > 1e-50 else fmpq(int(lo * 0.5 * 10 ** 100), 10 ** 100)
    print("lam_min(Sq) ~ %.6e  delta=%.4e  k*w0=%.3e" % (lo, float(delta.p) / float(delta.q), k * float(w0.p) / float(w0.q)), flush=True)
    assert delta > k * w0
    Aq = [[Sq[i][j] - (delta if i == j else 0) for j in range(k)] for i in range(k)]
    L = [[fmpq(0)] * k for _ in range(k)]
    D = [fmpq(0)] * k
    for j in range(k):
        s = Aq[j][j] - sum((L[j][m] * L[j][m] * D[m] for m in range(j)), fmpq(0))
        assert s > 0
        D[j] = s
        L[j][j] = fmpq(1)
        for i in range(j + 1, k):
            L[i][j] = (Aq[i][j] - sum((L[i][m] * L[j][m] * D[m] for m in range(j)), fmpq(0))) / s
    for i in range(k):
        for j in range(k):
            assert sum((L[i][m] * D[m] * L[j][m] for m in range(k)), fmpq(0)) == Aq[i][j]
    json.dump(dict(k=k, lam0=str(lam0), P=P, w0=[int(w0.p), int(w0.q)], delta=[int(delta.p), int(delta.q)],
                   S=[[[int(Sq[i][j].p), int(Sq[i][j].q)] for j in range(k)] for i in range(k)],
                   L=[[[int(L[i][j].p), int(L[i][j].q)] for j in range(k)] for i in range(k)],
                   D=[[int(d.p), int(d.q)] for d in D], lam_min_S=lo,
                   C_certified_resid=vr['Efro'].str(5)), open(out, 'w'))
    print("wrote", out, flush=True)

if __name__ == '__main__':
    main(sys.argv[1], float(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5])
