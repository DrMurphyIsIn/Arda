"""Verified LDL^T (Rump / Zhu Lemma 5.2 style).
1. floating LDL^T of mid(M) - lam0 I computed with exact dyadic midpoints (no ball propagation),
2. rigorous residual E = (M - lam0 I) - L D L^T in Arb ball arithmetic (M given as balls),
3. if all D_ii > 0 then for every symmetric G in the ball box:  G - lam0 I = L D L^T + E_G  with
   L D L^T >= 0, hence lam_min(G) >= lam0 - ||E||_2 >= lam0 - ||E||_F.
Blocked right-looking elimination; the block products use Arb matrix multiplication on midpoints."""
import flint, time
from flint import arb, arb_mat

def _mid(x):
    return arb(x.mid())

def floating_ldlt(M, lam0, b=64, verbose=False):
    n = M.nrows()
    lam0m = _mid(arb(lam0))
    A = [[_mid(M[i, j]) for j in range(n)] for i in range(n)]
    for i in range(n):
        A[i][i] = _mid(A[i][i] - lam0m)
    L = [[arb(0)] * n for _ in range(n)]
    D = [arb(0)] * n
    t0 = time.time()
    for J0 in range(0, n, b):
        J1 = min(n, J0 + b)
        # scalar LDL^T of the diagonal block (it already carries all previous Schur updates)
        for j in range(J0, J1):
            s = A[j][j]
            Lj = L[j]
            for k in range(J0, j):
                s -= Lj[k] * Lj[k] * D[k]
            s = _mid(s)
            if not (s > 0):
                return None, None, j, s
            D[j] = s
            inv = 1 / s
            for i in range(j + 1, J1):
                v = A[i][j]
                Li = L[i]
                for k in range(J0, j):
                    v -= Li[k] * Lj[k] * D[k]
                Li[j] = _mid(v * inv)
            L[j][j] = arb(1)
        if J1 == n:
            break
        # panel: L_IJ = (A_IJ * (L_JJ^T)^{-1}) D_J^{-1}  -- multiply by the unit-triangular inverse FIRST,
        # then scale columns by 1/D_j (scaling before multiplying loses the SPD cancellation when D_j is tiny)
        bb = J1 - J0
        LJJ = arb_mat([[L[J0 + r][J0 + c] if c <= r else arb(0) for c in range(bb)] for r in range(bb)])
        # backward-stable triangular solve  L_JJ Y^T = A_IJ^T  (Y = L_IJ D_J), floating 'approx' LU
        AIJt = arb_mat([[A[i][J0 + c] for i in range(J1, n)] for c in range(bb)])
        Yt = LJJ.solve(AIJt, algorithm='approx')
        invD = [1 / D[J0 + c] for c in range(bb)]
        for r, i in enumerate(range(J1, n)):
            for c in range(bb):
                L[i][J0 + c] = _mid(Yt[c, r] * invD[c])
        # Schur update: A_II -= L_IJ D_J L_IJ^T
        LIJm = arb_mat([[L[i][J0 + c] for c in range(bb)] for i in range(J1, n)])
        DJ = arb_mat([[D[J0 + r] if r == c else arb(0) for c in range(bb)] for r in range(bb)])
        U = LIJm * DJ * LIJm.transpose()
        for r, i in enumerate(range(J1, n)):
            Ai = A[i]
            for c, j in enumerate(range(J1, n)):
                Ai[j] = _mid(Ai[j] - U[r, c])
        if verbose:
            print("   block", J0, "done  %.1fs" % (time.time() - t0), flush=True)
    return L, D, None, None

def verify(M, lam0, b=64, verbose=False):
    n = M.nrows()
    t0 = time.time()
    L, D, fail_j, fail_s = floating_ldlt(M, lam0, b, verbose)
    if L is None:
        return dict(ok=False, reason="negative floating pivot at %d: %s" % (fail_j, fail_s.str(5)))
    t1 = time.time()
    Lm = arb_mat(L)
    Dm = arb_mat([[D[r] if r == c else arb(0) for c in range(n)] for r in range(n)])
    LDLt = (Lm * Dm) * Lm.transpose()
    lam0b = arb(lam0)
    fro2 = arb(0)
    emax = arb(0)
    for i in range(n):
        for j in range(n):
            e = M[i, j] - LDLt[i, j]
            if i == j:
                e -= lam0b
            ea = arb(abs(e).upper())
            fro2 += ea * ea
            emax = emax.max(ea)
    fro = fro2.sqrt()
    dmin = min(D, key=lambda v: float(v.mid()))
    ok = all(d > 0 for d in D)
    return dict(ok=bool(ok), Emax=emax, Efro=fro, dmin=dmin, lower=arb(lam0) - fro,
                t_ldlt=t1 - t0, t_resid=time.time() - t1)

if __name__ == "__main__":
    import sys
    flint.ctx.prec = 256
    from certify import Window, build_leading
    a = arb(249) / 256
    win = Window(a, 560.0)
    M, cmax2 = build_leading(win, 'even', 450)
    for lam0 in (4.40e-28, 4.48e-28, 4.49e-28):
        r = verify(M, lam0, b=64)
        print(lam0, {k: (v.str(5) if hasattr(v, 'str') else v) for k, v in r.items()}, flush=True)


# ----------------------------------------------------------------------------------------------------------------
# Blocked CHOLESKY variant (bounded factor entries |R_ij| <= sqrt(M_ii)): backward stable even when lam_min/||M||
# ~ 1e-50, where the unit-L LDL^T form has entries ~ D^{-1/2} and its blocked Schur updates lose all accuracy.
def floating_chol(M, lam0, b=64, fprec=None):
    """Floating (midpoint) blocked Cholesky R R^T = mid(M) - lam0 I, lower-triangular R, at working precision
    fprec (default: current).  Returns (R as list of lists, None, None) or (None, j, s) at a non-positive pivot."""
    old = flint.ctx.prec
    if fprec is not None:
        flint.ctx.prec = fprec
    try:
        n = M.nrows()
        lam0m = arb(arb(lam0).mid())
        A = [[arb(M[i, j].mid()) for j in range(n)] for i in range(n)]
        for i in range(n):
            A[i][i] = _mid(A[i][i] - lam0m)
        R = [[arb(0)] * n for _ in range(n)]
        for J0 in range(0, n, b):
            J1 = min(n, J0 + b)
            for j in range(J0, J1):
                s = A[j][j]
                Rj = R[j]
                for k in range(J0, j):
                    s -= Rj[k] * Rj[k]
                s = _mid(s)
                if not (s > 0):
                    return None, j, s
                r = _mid(s.sqrt())
                Rj[j] = r
                inv = 1 / r
                for i in range(j + 1, J1):
                    v = A[i][j]
                    Ri = R[i]
                    for k in range(J0, j):
                        v -= Ri[k] * Rj[k]
                    Ri[j] = _mid(v * inv)
            if J1 == n:
                break
            bb = J1 - J0
            RJJ = arb_mat([[R[J0 + r_][J0 + c] if c <= r_ else arb(0) for c in range(bb)] for r_ in range(bb)])
            AIJt = arb_mat([[A[i][J0 + c] for i in range(J1, n)] for c in range(bb)])
            Xt = RJJ.solve(AIJt, algorithm='approx')          # R_JJ X^T = A_IJ^T  ->  X = R_IJ
            for r_, i in enumerate(range(J1, n)):
                for c in range(bb):
                    R[i][J0 + c] = _mid(Xt[c, r_])
            RIJ = arb_mat([[R[i][J0 + c] for c in range(bb)] for i in range(J1, n)])
            U = RIJ * RIJ.transpose()
            for r_, i in enumerate(range(J1, n)):
                Ai = A[i]
                for c_, j in enumerate(range(J1, n)):
                    Ai[j] = _mid(Ai[j] - U[r_, c_])
        return R, None, None
    finally:
        flint.ctx.prec = old


def verify_chol(M, lam0, b=64, fprec=None):
    """Rigorous: if the floating Cholesky of mid(M) - lam0 I succeeds, then for every symmetric G in the ball
    box of M:  G - lam0 I = R R^T + E_G,  R R^T >= 0,  so  lam_min(G) >= lam0 - ||E||_F  (E in Arb)."""
    n = M.nrows()
    t0 = time.time()
    R, j, s = floating_chol(M, lam0, b, fprec)
    if R is None:
        return dict(ok=False, reason="non-positive pivot at %d: %s" % (j, s.str(5)))
    t1 = time.time()
    old = flint.ctx.prec
    if fprec is not None:
        flint.ctx.prec = fprec
    try:
        Rm = arb_mat([[R[i][k] if k <= i else arb(0) for k in range(n)] for i in range(n)])
        RRt = Rm * Rm.transpose()
        lam0b = arb(lam0)
        fro2 = arb(0)
        emax = arb(0)
        for i in range(n):
            for k in range(n):
                e = M[i, k] - RRt[i, k]
                if i == k:
                    e -= lam0b
                ea = arb(abs(e).upper())
                fro2 += ea * ea
                emax = emax.max(ea)
        fro = fro2.sqrt()
    finally:
        flint.ctx.prec = old
    return dict(ok=True, Emax=emax, Efro=fro, lower=arb(lam0) - fro, t_chol=t1 - t0, t_resid=time.time() - t1)
