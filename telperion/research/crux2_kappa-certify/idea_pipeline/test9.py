import flint, time
from flint import arb, arb_mat
flint.ctx.prec = 256
from certify import Window, build_leading
import vldlt
a = arb(249)/256
win = Window(a, 560.0)
M, cmax2 = build_leading(win, 'odd', 450)
def inertia(M, lam0):
    # count negative pivots of floating LDL^T (no early stop)
    n = M.nrows()
    A = [[arb(M[i,j].mid()) for j in range(n)] for i in range(n)]
    for i in range(n): A[i][i] = arb((A[i][i] - lam0).mid())
    neg = 0; pivs = []
    L = [[arb(0)]*n for _ in range(n)]; D=[None]*n
    for j in range(n):
        s = A[j][j]
        for k in range(j): s -= L[j][k]*L[j][k]*D[k]
        s = arb(s.mid()); D[j] = s; pivs.append(s)
        if s < 0: neg += 1
        inv = 1/s
        for i in range(j+1, n):
            v = A[i][j]
            for k in range(j): v -= L[i][k]*L[j][k]*D[k]
            L[i][j] = arb((v*inv).mid())
    return neg, pivs
for lam0 in (0.0, -1e-30, -1e-26, -1e-22, -1e-18, -1e-14, -1e-10):
    t = time.time()
    neg, pivs = inertia(M, arb(lam0))
    print("lam0=%.1e  #negative pivots=%d  (%.0fs)" % (lam0, neg, time.time()-t), flush=True)
