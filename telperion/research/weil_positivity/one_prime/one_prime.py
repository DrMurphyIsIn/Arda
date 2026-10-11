#!/usr/bin/env python3
"""
Weil positivity on the one-prime window log(2)/2 < a < log(3)/2.

SEARCH / numerical exploration only.  Nothing here is progress on RH.  conjecture1_proved = False.

Reuses (imports, does not edit) ../weil_form.py (validated explicit formula, B-spline Gram) and
../gram_experiments.py (parity blocks).  Spline basis phi_j = M4((x - c_j)/h), h = 2a/(n+3), in [-a, a].

On the window the only prime-power term in W(f * f~) is n = 2:
    G = A - w2 * Q,   w2 = log 2 / sqrt 2,
    A = POLE - CONST + ARCH  (archimedean place + poles),
    Q(f) = (f*f~)(L) + (f*f~)(-L) = 2 int f(y) f(y - L) dy,   L = log 2.
NOTE: Q is NOT rank <= 2.  It is the lag-L correlation form.  For supp f in [-a, a] it vanishes on
functions supported in |x| <= L - a and pairs the two end strips [-a, a-L] and [L-a, a] (length
2a - L each); on L^2(ends) it is unitarily [[0, 1], [1, 0]] (spectrum +-1, infinite multiplicity).
In the n-dim spline space its rank grows like 2 * (number of splines meeting an end strip).

Subcommands:
  build A N [DPS]        cache Toeplitz columns of POLE, CONST, ARCH (zeta) and DH archimedean part
  analyse                all tables from the cache (tasks 1-4)
"""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ.setdefault(_v, "1")
import sys
import json
import time
import mpmath as mp

HERE = os.path.dirname(os.path.abspath(__file__))
PARENT = os.path.dirname(HERE)
sys.path.insert(0, PARENT)
import weil_form as wf  # noqa: E402
from gram_experiments import parity_blocks  # noqa: E402

RES = os.path.join(HERE, "results")
SCR = "/private/tmp/claude-0/-Users-peterwmurphy/d468a49a-41a3-402a-a634-199ecc771fa2/scratchpad/one_prime"
COLS = os.path.join(SCR, "cols")
os.makedirs(RES, exist_ok=True)
os.makedirs(COLS, exist_ok=True)


def dh_lfun():
    return dict(arch_exp=mp.mpf(3) / 2, const_coef=mp.euler + mp.log(mp.pi) - mp.log(5), pole=False)


def dh_kappa():
    return (mp.sqrt(10 - 2 * mp.sqrt(5)) - 2) / (mp.sqrt(5) - 1)


def colfile(a, n):
    return os.path.join(COLS, "cols_a%s_n%d.json" % (a, n))


def build(a, n, dps=50):
    """Toeplitz columns (m = 0..n-1) of POLE, CONST, ARCH for zeta and ARCH-CONST for DH; mass."""
    mp.mp.dps = int(dps)
    n = int(n)
    a_ = mp.mpf(a)
    h = 2 * a_ / (n + 3)
    t = time.time()
    out = dict(a=a, n=n, dps=int(dps), pole=[], const=[], arch=[], dh_ac=[], mass=[])
    for m in range(n):
        c = wf.spline_entry(h, m, prime_lambda=[])
        out["pole"].append(mp.nstr(c["pole"], mp.mp.dps))
        out["const"].append(mp.nstr(c["const"], mp.mp.dps))
        out["arch"].append(mp.nstr(c["arch"], mp.mp.dps))
        d = wf.spline_entry(h, m, prime_lambda=[], lfun=dh_lfun())
        out["dh_ac"].append(mp.nstr(d["arch"] - d["const"], mp.mp.dps))
        out["mass"].append(mp.nstr(h * wf.bspline(8, m), mp.mp.dps))
    out["seconds"] = round(time.time() - t, 1)
    json.dump(out, open(colfile(a, n), "w"))
    print("built a=%s n=%d in %.1fs" % (a, n, out["seconds"]), flush=True)


def load(a, n):
    d = json.load(open(colfile(a, n)))
    mp.mp.dps = d["dps"]
    for k in ("pole", "const", "arch", "dh_ac", "mass"):
        d[k] = [mp.mpf(x) for x in d[k]]
    d["h"] = 2 * mp.mpf(a) / (n + 3)
    return d


def q_col(a, n, lag):
    """Toeplitz column of Q_lag: g_m(lag) + g_m(-lag), g_m(x) = h M8((x - m h)/h)."""
    h = 2 * mp.mpf(a) / (n + 3)
    lag = mp.mpf(lag)
    return [h * (wf.bspline(8, (lag - m * h) / h) + wf.bspline(8, (-lag - m * h) / h)) for m in range(n)]


def mats(a, n, lag=None):
    d = load(a, n)
    L = mp.log(2) if lag is None else mp.mpf(lag)
    T = wf.toeplitz
    A = T([p - c + r for p, c, r in zip(d["pole"], d["const"], d["arch"])])
    return dict(A=A, POLE=T(d["pole"]), K=T([r - c for c, r in zip(d["const"], d["arch"])]),
                Q=T(q_col(a, n, L)), M=T(d["mass"]), DHA=T(d["dh_ac"]), h=d["h"])


# ----------------------------------------------------------------------------------------------
# linear algebra (mpmath, 60 digits, parity-split)
# ----------------------------------------------------------------------------------------------
W2 = None


def w2():
    return mp.log(2) / mp.sqrt(2)


def sym(S):
    n = S.rows
    for i in range(n):
        for j in range(i + 1, n):
            v = (S[i, j] + S[j, i]) / 2
            S[i, j] = S[j, i] = v
    return S


def sectors(Mx, n):
    """Even / odd blocks (reflection j -> n-1-j) of a centrosymmetric matrix, plus the embeddings."""
    _, _, Ue, Uo = parity_blocks(Mx, n)
    return dict(even=(Ue.T * Mx * Ue, Ue), odd=(Uo.T * Mx * Uo, Uo))


def pencil(X, Y):
    """Eigen-decomposition of X v = mu Y v with Y SPD.  Returns (mu ascending, V (Y-orthonormal))."""
    return wf.gen_eig(sym(X.copy()), sym(Y.copy()))


def mu_extremes(Q, G):
    """Eigenvalues of the pencil (Q, G), G SPD: returns sorted list."""
    ev, _ = pencil(Q, G)
    return ev


def numrank(X, Mm, tol=mp.mpf("1e-40")):
    ev, _ = pencil(X, Mm)
    mx = max(abs(e) for e in ev)
    return sum(1 for e in ev if abs(e) > tol * mx), ev


def to_np(Mx):
    import numpy as np
    return np.array([[float(Mx[i, j]) for j in range(Mx.cols)] for i in range(Mx.rows)])


def phi_np(A, Q, Mm, c):
    """float64 lambda_min of the pencil (A - cQ, M)  (coarse search only)."""
    import numpy as np
    import scipy.linalg as sl
    return sl.eigh(A - c * Q, Mm, eigvals_only=True)[0]


def interval_general(Am, Qm, Mm, w=None, lo=-3.0, hi=4.0):
    """{c : A - cQ >= 0} (on the finite basis), without assuming A - wQ > 0.
    Coarse float64 golden-section for argmax of the concave phi(c) = lambda_min(A - cQ, M), then an
    exact 60-digit pencil (Q, A - c0 Q) at c0: c in [c0 + 1/mu_min, c0 + 1/mu_max]."""
    An, Qn, Mn = to_np(Am), to_np(Qm), to_np(Mm)
    gr = (5 ** 0.5 - 1) / 2
    a_, b_ = lo, hi
    x1, x2 = b_ - gr * (b_ - a_), a_ + gr * (b_ - a_)
    f1, f2 = phi_np(An, Qn, Mn, x1), phi_np(An, Qn, Mn, x2)
    for _ in range(80):
        if f1 < f2:
            a_, x1, f1 = x1, x2, f2
            x2 = a_ + gr * (b_ - a_)
            f2 = phi_np(An, Qn, Mn, x2)
        else:
            b_, x2, f2 = x2, x1, f1
            x1 = b_ - gr * (b_ - a_)
            f1 = phi_np(An, Qn, Mn, x1)
    c0 = mp.mpf((a_ + b_) / 2)
    if w is not None:
        # prefer the true weight as base point if it is admissible (better conditioned for zeta)
        evw, _ = pencil(Am - w * Qm, Mm)
        if evw[0] > 0:
            c0 = w
    B = Am - c0 * Qm
    evB, _ = pencil(B, Mm)
    if evB[0] <= 0:
        return dict(empty=True, c0=c0, phi_max=evB[0])
    mu, _ = pencil(Qm, B)
    c_hi = c0 + 1 / mu[-1] if mu[-1] > 0 else mp.inf
    c_lo = c0 + 1 / mu[0] if mu[0] < 0 else -mp.inf
    return dict(empty=False, c0=c0, phi_c0=evB[0], c_lo=c_lo, c_hi=c_hi, mu=mu)


def spline_values_np(a, n, coef, xs):
    import numpy as np
    a = float(a)
    h = 2 * a / (n + 3)
    c = np.array([float(x) for x in coef])
    centers = -a + (np.arange(n) + 2) * h
    u = (xs[:, None] - centers[None, :]) / h
    au = np.abs(u)
    B = np.where(au < 1, 2 / 3 - au ** 2 + au ** 3 / 2, np.where(au < 2, (2 - au) ** 3 / 6, 0.0))
    return B @ c


def strip_fraction(a, n, coef):
    """Fraction of int f^2 carried by the end strips |x| >= log2 - a (where Q lives)."""
    import numpy as np
    a_ = float(a)
    xs = np.linspace(-a_, a_, 20001)
    f = spline_values_np(a, n, coef, xs)
    L = float(mp.log(2))
    tot = np.trapezoid(f ** 2, xs)
    ends = np.trapezoid(np.where(np.abs(xs) >= L - a_, f ** 2, 0.0), xs)
    return ends / tot


def embed(U, v):
    return U * v


# ----------------------------------------------------------------------------------------------
def analyse_one(a, n, controls=True):
    n = int(n)
    m = mats(a, n)
    w = w2()
    A, K, P, Q, Mm = m["A"], m["K"], m["POLE"], m["Q"], m["M"]
    G = A - w * Q
    rec = dict(a=a, n=n, h=float(m["h"]), strip_len=float(2 * mp.mpf(a) - mp.log(2)))
    secs = {}
    for name, X in (("A", A), ("K", K), ("P", P), ("Q", Q), ("M", Mm), ("G", G), ("DHA", m["DHA"])):
        for sec, (B, U) in sectors(X, n).items():
            secs[(name, sec)] = B
            secs[("U", sec)] = U
    out = {}
    for sec in ("even", "odd"):
        Ms = secs[("M", sec)]
        Gs, As, Ks, Qs, Ps = (secs[(k, sec)] for k in ("G", "A", "K", "Q", "P"))
        evG, VG = pencil(Gs, Ms)
        evA, VA = pencil(As, Ms)
        evK, _ = pencil(Ks, Ms)
        rQ, evQ = numrank(Qs, Ms) if float(rec["strip_len"]) > 0 else (0, [mp.mpf(0)])
        r = dict(minG=evG[0], minA=evA[0], minA2=evA[1], minK=evK[0], negK=sum(1 for e in evK if e < 0),
                 rankQ=rQ, Qspec=(evQ[0], evQ[-1]))
        # pole: rank one, sign
        evP, VP = pencil(Ps, Ms)
        r["pole_eigs"] = (evP[0], evP[-1])
        if rQ > 0:
            mu = mu_extremes(Qs, Gs)
            r["mu_min"], r["mu_max"] = mu[0], mu[-1]
            r["mu_top"] = [mu[-1], mu[-2], mu[-3]] if len(mu) >= 3 else mu[::-1]
            r["mu_bot"] = [mu[0], mu[1], mu[2]] if len(mu) >= 3 else mu
            r["c_lo"] = w + 1 / mu[0] if mu[0] < 0 else -mp.inf
            r["c_hi"] = w + 1 / mu[-1] if mu[-1] > 0 else mp.inf
        # G minimal eigenvector: strip fraction, Q value
        U = secs[("U", sec)]
        vG = U * VG[:, 0]
        r["G_min_strip"] = strip_fraction(a, n, vG)
        vA = U * VA[:, 0]
        r["A_min_strip"] = strip_fraction(a, n, vA)
        # Rayleigh quotient of Q (normalized by ||f||^2 = v^T M v = 1)
        r["A_min_Qray"] = (VA[:, 0].T * Qs * VA[:, 0])[0]
        r["G_min_Qray"] = (VG[:, 0].T * Qs * VG[:, 0])[0]
        # projection of A's min eigvec onto range(M^{-1}Q) (M-orthogonal to ker Q)
        if rQ > 0:
            evq, Vq = pencil(Qs, Ms)
            mx = max(abs(e) for e in evq)
            proj = mp.mpf(0)
            for k in range(len(evq)):
                if abs(evq[k]) > mp.mpf("1e-40") * mx:
                    proj += ((Vq[:, k].T * Ms * VA[:, 0])[0]) ** 2
            r["A_min_in_rangeQ"] = proj
            projG = mp.mpf(0)
            for k in range(len(evq)):
                if abs(evq[k]) > mp.mpf("1e-40") * mx:
                    projG += ((Vq[:, k].T * Ms * VG[:, 0])[0]) ** 2
            r["G_min_in_rangeQ"] = projG
        # rank-one pole reduction: POLE_sec = sigma * s s^T
        if abs(evP[0]) > abs(evP[-1]):
            lam, idx = evP[0], 0
        else:
            lam, idx = evP[-1], len(evP) - 1
        svec = Ms * VP[:, idx] * mp.sqrt(abs(lam))  # POLE_sec = sign * s s^T in coefficient space
        r["pole_sign"] = 1 if lam > 0 else -1
        for cname, c in (("0", mp.mpf(0)), ("w2", w)):
            Kc = Ks - c * Qs
            evKc, _ = pencil(Kc, Ms)
            r["minK_minus_cQ_" + cname] = evKc[0]
            r["negK_minus_cQ_" + cname] = sum(1 for e in evKc if e < 0)
            u = mp.lu_solve(Kc, svec)
            r["rho_" + cname] = (svec.T * u)[0]
        u0 = mp.lu_solve(Ks, svec)
        r["rho1"] = (u0.T * Qs * u0)[0]  # d rho / dc at c=0
        if rQ > 0:
            evKQ, _ = pencil(Qs, Ks) if evK[0] > 0 else ([mp.nan], None)
            r["specrad_w2KinvQ"] = w * max(abs(e) for e in evKQ) if evK[0] > 0 else mp.nan
        out[sec] = r
    rec["sectors"] = out
    rec["minG"] = min(out["even"]["minG"], out["odd"]["minG"])
    rec["minA"] = min(out["even"]["minA"], out["odd"]["minA"])
    if all("c_lo" in out[s] for s in out):
        rec["c_lo"] = max(out["even"]["c_lo"], out["odd"]["c_lo"])
        rec["c_hi"] = min(out["even"]["c_hi"], out["odd"]["c_hi"])
    # controls: fake lags and DH
    if controls:
        ctl = {}
        Mfull = Mm
        for q in ("1.8", "2.2", "2.5"):
            lag = mp.log(mp.mpf(q))
            if lag >= 2 * mp.mpf(a):
                ctl[q] = dict(active=False)
                continue
            Qq = wf.toeplitz(q_col(a, n, lag))
            wq = lag / mp.sqrt(mp.mpf(q))
            dd = dict(active=True, w=wq)
            for sec in ("even", "odd"):
                Ue = secs[("U", sec)]
                As, Ms = secs[("A", sec)], secs[("M", sec)]
                Qs = Ue.T * Qq * Ue
                evw, _ = pencil(As - wq * Qs, Ms)
                it = interval_general(As, Qs, Ms, w=wq)
                dd[sec] = dict(minG=evw[0], **{k: v for k, v in it.items() if k != "mu"})
            ctl[q] = dd
        # DH: G_DH = DHA - kappa log2/sqrt2 * Q
        wdh = dh_kappa() * mp.log(2) / mp.sqrt(2)
        dd = dict(active=True, w=wdh)
        for sec in ("even", "odd"):
            Ds, Qs, Ms = secs[("DHA", sec)], secs[("Q", sec)], secs[("M", sec)]
            evD, _ = pencil(Ds, Ms)
            evw, _ = pencil(Ds - wdh * Qs, Ms)
            it = interval_general(Ds, Qs, Ms, w=wdh)
            dd[sec] = dict(minA=evD[0], minG=evw[0], **{k: v for k, v in it.items() if k != "mu"})
        ctl["DH"] = dd
        rec["controls"] = ctl
    return rec


def jsonable(x):
    if isinstance(x, dict):
        return {str(k): jsonable(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [jsonable(v) for v in x]
    if isinstance(x, mp.mpf):
        return mp.nstr(x, 20)
    if isinstance(x, bool):
        return x
    if isinstance(x, (int, float, str)) or x is None:
        return x
    try:
        return float(x)
    except Exception:
        return str(x)


def analyse(a, n, controls="1"):
    t = time.time()
    rec = analyse_one(a, n, controls == "1" and int(n) <= 120)
    rec["seconds"] = round(time.time() - t, 1)
    path = os.path.join(SCR, "rec_a%s_n%s.json" % (a, n))
    json.dump(jsonable(rec), open(path, "w"), indent=1)
    print("a=%s n=%s minG=%s minA=%s c_lo=%s c_hi=%s (%.0fs)" % (
        a, n, mp.nstr(rec["minG"], 5), mp.nstr(rec["minA"], 5), mp.nstr(rec.get("c_lo", mp.nan), 10),
        mp.nstr(rec.get("c_hi", mp.nan), 10), rec["seconds"]), flush=True)


def schur_check(a="0.45", n="30"):
    """Cross-check: the admissible interval from the explicit Schur complement onto range(Q)
    (r x r generalized eigenproblem) equals the one from the (Q, G) pencil."""
    n = int(n)
    m = mats(a, n)
    A, Q, Mm = m["A"], m["Q"], m["M"]
    w = w2()
    # basis of ker Q and of its M-orthogonal complement from the (Q, M) pencil
    evq, Vq = pencil(Q, Mm)
    mx = max(abs(e) for e in evq)
    ker = [k for k in range(n) if abs(evq[k]) <= mp.mpf("1e-40") * mx]
    rng = [k for k in range(n) if k not in ker]
    N = mp.matrix(n, len(ker))
    Wm = mp.matrix(n, len(rng))
    for i, k in enumerate(ker):
        N[:, i] = Vq[:, k]
    for i, k in enumerate(rng):
        Wm[:, i] = Vq[:, k]
    ANN = N.T * A * N
    ANW = N.T * A * Wm
    AWW = Wm.T * A * Wm
    QWW = Wm.T * Q * Wm
    S0 = AWW - ANW.T * mp.inverse(ANN) * ANW
    evANN, _ = pencil(ANN, N.T * Mm * N)
    # interval {c : S0 - c QWW >= 0}: pencil (QWW, S0 - w QWW)
    Sw = S0 - w * QWW
    mu, _ = pencil(QWW, Sw)
    lo, hi = w + 1 / mu[0], w + 1 / mu[-1]
    G = A - w * Q
    mu2, _ = pencil(Q, G)
    lo2, hi2 = w + 1 / mu2[0], w + 1 / mu2[-1]
    print("a=%s n=%d: rank Q = %d, dim ker Q = %d, min eig A|kerQ (M-normalized) = %s" % (a, n, len(rng), len(ker), mp.nstr(evANN[0], 6)))
    print("  Schur r x r:   c_lo = %s  c_hi = %s" % (mp.nstr(lo, 25), mp.nstr(hi, 25)))
    print("  (Q,G) pencil:  c_lo = %s  c_hi = %s" % (mp.nstr(lo2, 25), mp.nstr(hi2, 25)))
    print("  differences %s %s" % (mp.nstr(lo - lo2, 3), mp.nstr(hi - hi2, 3)))


# ----------------------------------------------------------------------------------------------
# CC-type compression: K - cQ on the hyperplane(s) where the pole functionals vanish
# ----------------------------------------------------------------------------------------------
def null_basis(funcs, m):
    """Columns spanning {v in R^m : l.v = 0 for l in funcs} (Gaussian elimination with pivoting)."""
    Z = mp.eye(m)
    for l in funcs:
        lv = (l.T * Z)  # 1 x k
        k = Z.cols
        piv = max(range(k), key=lambda j: abs(lv[0, j]))
        Znew = mp.matrix(Z.rows, k - 1)
        c = 0
        for j in range(k):
            if j == piv:
                continue
            Znew[:, c] = Z[:, j] - (lv[0, j] / lv[0, piv]) * Z[:, piv]
            c += 1
        Z = Znew
    return Z


def ccplus_one(a, n):
    n = int(n)
    m = mats(a, n)
    w = w2()
    K, Q, P, Mm, h = m["K"], m["Q"], m["POLE"], m["M"], m["h"]
    one = mp.matrix([h] * n)  # int phi_j = h
    out = dict(a=a, n=n)
    for sec, (Ps, U) in sectors(P, n).items():
        Ks, Qs, Ms = U.T * K * U, U.T * Q * U, U.T * Mm * U
        evP, VP = pencil(Ps, Ms)
        idx = 0 if abs(evP[0]) > abs(evP[-1]) else len(evP) - 1
        pole_fun = Ms * VP[:, idx]
        cons = [("pole", [pole_fun])]
        if sec == "even":
            cons.append(("pole+mean", [pole_fun, U.T * one]))
        for cname, fl in cons:
            Z = null_basis(fl, Ks.rows)
            for lab, c in (("0", mp.mpf(0)), ("w2", w)):
                X = Z.T * (Ks - c * Qs) * Z
                ev, _ = pencil(X, Z.T * Ms * Z)
                out["%s|%s|c=%s" % (sec, cname, lab)] = mp.nstr(ev[0], 12)
    json.dump(out, open(os.path.join(SCR, "cc_a%s_n%d.json" % (a, n)), "w"), indent=1)
    print(json.dumps(out), flush=True)


def ccplus(a, n):
    ccplus_one(a, n)


# ----------------------------------------------------------------------------------------------
# tables
# ----------------------------------------------------------------------------------------------
A_GRID = ["0.30", "0.3466", "0.36", "0.38", "0.40", "0.42", "0.45", "0.48", "0.50", "0.52", "0.54", "0.549"]
N_GRID = [30, 60, 90, 120, 180, 240]


def recs():
    out = {}
    for a in A_GRID:
        for n in N_GRID:
            p = os.path.join(SCR, "rec_a%s_n%d.json" % (a, n))
            if os.path.exists(p):
                out[(a, n)] = json.load(open(p))
    return out


def f(x, k=4):
    try:
        return mp.nstr(mp.mpf(x), k)
    except Exception:
        return str(x)


def tables():
    mp.mp.dps = 30
    R = recs()
    w = w2()
    lines = []
    P = lines.append
    P("# generated by one_prime.py tables; w2 = log2/sqrt2 = %s" % mp.nstr(w, 20))
    P("\n## T1  lambda_min of (G, M) and of (A, M), by sector\n")
    P("| a | n | min G even | min G odd | min A even | min A odd | min K even | min K odd |")
    P("|---|---|---|---|---|---|---|---|")
    for (a, n), r in sorted(R.items(), key=lambda t: (float(t[0][0]), t[0][1])):
        e, o = r["sectors"]["even"], r["sectors"]["odd"]
        P("| %s | %d | %s | %s | %s | %s | %s | %s |" % (a, n, f(e["minG"]), f(o["minG"]), f(e["minA"]), f(o["minA"]), f(e["minK"]), f(o["minK"])))
    P("\n## T2  admissible interval {c : A - cQ >= 0} = [c_lo, c_hi]; sector that binds; margins\n")
    P("| a | n | c_lo (sector) | c_hi (sector) | w2 - c_lo | c_hi - w2 | rank Q (even+odd) | mu_max even, next | mu_min odd, next |")
    P("|---|---|---|---|---|---|---|---|---|")
    for (a, n), r in sorted(R.items(), key=lambda t: (float(t[0][0]), t[0][1])):
        if "c_lo" not in r:
            P("| %s | %d | Q = 0 (no prime) | | | | 0 | | |" % (a, n))
            continue
        e, o = r["sectors"]["even"], r["sectors"]["odd"]
        slo = "even" if mp.mpf(e["c_lo"]) >= mp.mpf(o["c_lo"]) else "odd"
        shi = "even" if mp.mpf(e["c_hi"]) <= mp.mpf(o["c_hi"]) else "odd"
        P("| %s | %d | %s (%s) | %s (%s) | %s | %s | %d+%d | %s, %s | %s, %s |" % (
            a, n, f(r["c_lo"], 10), slo, f(r["c_hi"], 10), shi, f(w - mp.mpf(r["c_lo"])), f(mp.mpf(r["c_hi"]) - w),
            e["rankQ"], o["rankQ"], f(e["mu_top"][0]), f(e["mu_top"][1], 3), f(o["mu_bot"][0]), f(o["mu_bot"][1], 3)))
    P("\n## T2b  per-sector intervals\n")
    P("| a | n | even [c_lo, c_hi] | odd [c_lo, c_hi] |")
    P("|---|---|---|---|")
    for (a, n), r in sorted(R.items(), key=lambda t: (float(t[0][0]), t[0][1])):
        if "c_lo" not in r:
            continue
        e, o = r["sectors"]["even"], r["sectors"]["odd"]
        P("| %s | %d | [%s, %s] | [%s, %s] |" % (a, n, f(e["c_lo"], 8), f(e["c_hi"], 8), f(o["c_lo"], 8), f(o["c_hi"], 8)))
    P("\n## T3  mechanism: minimal eigenvector of A (per sector): mass in end strips |x| >= log2 - a, ")
    P("M-norm^2 of its projection on range(Q), Rayleigh quotient Q(v)/||v||^2; same for G's minimal eigenvector\n")
    P("| a | n | sector | min A | A-vec strip mass | A-vec in range(Q) | Q(vA) | G-vec strip mass | G-vec in range(Q) | Q(vG) |")
    P("|---|---|---|---|---|---|---|---|---|---|")
    for (a, n), r in sorted(R.items(), key=lambda t: (float(t[0][0]), t[0][1])):
        for sec in ("even", "odd"):
            x = r["sectors"][sec]
            P("| %s | %d | %s | %s | %.3f | %s | %s | %.3f | %s | %s |" % (a, n, sec, f(x["minA"]), x["A_min_strip"], f(x.get("A_min_in_rangeQ", "-"), 3),
                                                                     f(x["A_min_Qray"], 3), x["G_min_strip"], f(x.get("G_min_in_rangeQ", "-"), 3), f(x["G_min_Qray"], 3)))
    P("\n## T4  rank-one pole reduction.  POLE = +2 C(f)^2 on even f (C = int f cosh(x/2)), -2 S(f)^2 on odd f (S = int f sinh(x/2)).")
    P("rho_sec(c) = 2 <p, (K - cQ)^{-1} p> with K = ARCH - CONST, p = cosh(x/2) (even) or sinh(x/2) (odd).")
    P("Exact criterion: odd sector PSD  <=>  K - cQ > 0 on odd and rho_odd(c) <= 1;")
    P("even sector PSD  <=>  K - cQ has exactly one negative eigenvalue on even and rho_even(c) <= -1.\n")
    P("| a | n | #neg(K-0Q) e/o | #neg(K-w2Q) e/o | rho_even(0) | rho_even(w2) | margin_even = -1 - rho_even(w2) | rho_odd(0) | rho_odd(w2) | margin_odd = 1 - rho_odd(w2) |")
    P("|---|---|---|---|---|---|---|---|---|---|")
    for (a, n), r in sorted(R.items(), key=lambda t: (float(t[0][0]), t[0][1])):
        e, o = r["sectors"]["even"], r["sectors"]["odd"]
        P("| %s | %d | %d/%d | %d/%d | %s | %s | %s | %s | %s | %s |" % (
            a, n, e["negK_minus_cQ_0"], o["negK_minus_cQ_0"], e["negK_minus_cQ_w2"], o["negK_minus_cQ_w2"],
            f(e["rho_0"], 8), f(e["rho_w2"], 10), f(-1 - mp.mpf(e["rho_w2"])), f(o["rho_0"], 6), f(o["rho_w2"], 8), f(1 - mp.mpf(o["rho_w2"]))))
    P("\n## T5  controls (n <= 120): fake lag log q with weight log q/sqrt q, and Davenport-Heilbronn (lag log 2, weight kappa log2/sqrt2)\n")
    P("| a | n | form | w | min G even | min G odd | even interval | odd interval |")
    P("|---|---|---|---|---|---|---|---|")
    for (a, n), r in sorted(R.items(), key=lambda t: (float(t[0][0]), t[0][1])):
        if "controls" not in r:
            continue
        for q, d in r["controls"].items():
            if not d.get("active"):
                P("| %s | %d | %s | - | lag >= 2a: no term | | | |" % (a, n, "q=" + q if q != "DH" else q))
                continue
            iv = []
            for sec in ("even", "odd"):
                x = d[sec]
                iv.append("EMPTY (max_c lambda_min = %s)" % f(x["phi_max"], 3) if x["empty"] else "[%s, %s]" % (f(x["c_lo"], 6), f(x["c_hi"], 6)))
            P("| %s | %d | %s | %s | %s | %s | %s | %s |" % (a, n, "q=" + q if q != "DH" else "DH", f(d["w"], 6), f(d["even"]["minG"]), f(d["odd"]["minG"]), iv[0], iv[1]))
    txt = "\n".join(lines) + "\n"
    open(os.path.join(RES, "tables.md"), "w").write(txt)
    print(txt)


def lagscan(n="120", alist=None, check="1"):
    """How special is p = 2?  With the natural weight w_q = log q/sqrt q at lag log q, find the set of q
    near 2 for which A - w_q Q_q is PSD on the n-dim basis (float64 search on the 60-digit cached A,
    then 60-digit confirmation at the reported endpoints).  Analogue of Connes-Consani 2106.01715 sec 2.3."""
    import numpy as np
    import scipy.linalg as sl
    n = int(n)
    out = ["# lag tolerance: q-interval around 2 with A - (log q/sqrt q) Q_{log q} PSD (n=%d)" % n, "",
           "| a | q_lo | q_hi | q_hi - q_lo | 2 - q_lo | q_hi - 2 | 60-digit check: lambda_min at q_lo-, q_lo+, q_hi-, q_hi+ |", "|---|---|---|---|---|---|---|"]
    for a in (alist.split(",") if alist else ["0.40", "0.42", "0.45", "0.48", "0.50", "0.52", "0.54", "0.549"]):
        m = mats(a, n)
        A, Mm = m["A"], m["M"]
        An, Mn = to_np(A), to_np(Mm)

        def lam(q, prec=False):
            q = mp.mpf(q)
            Qq = wf.toeplitz(q_col(a, n, mp.log(q)))
            wq = mp.log(q) / mp.sqrt(q)
            if prec:
                ev, _ = pencil(A - wq * Qq, Mm)
                return ev[0]
            return sl.eigh(An - float(wq) * to_np(Qq), Mn, eigvals_only=True)[0]

        if lam(2) <= 0:
            out.append("| %s | lambda_min(q=2) <= 0 in float64 | | | | | |" % a)
            continue

        def edge(lo, hi):  # lam(lo) > 0, lam(hi) <= 0
            for _ in range(45):
                mid = (lo + hi) / 2
                if lam(mid) > 0:
                    lo = mid
                else:
                    hi = mid
            return lo, hi
        # walk outwards geometrically to find a sign change
        def bracket(direction):
            d = 1e-7
            while d < 0.5:
                if lam(2 + direction * d) <= 0:
                    return d
                d *= 2
            return None
        dl, dh = bracket(-1), bracket(+1)
        qlo = edge(2.0, 2 - dl)[0] if dl else float("nan")
        qhi = edge(2.0, 2 + dh)[0] if dh else float("nan")
        eps = 1e-9
        chk = []
        for q in (qlo - eps * 50, qlo + eps * 50, qhi - eps * 50, qhi + eps * 50):
            chk.append(mp.nstr(lam(mp.mpf(q), prec=True), 3) if check == "1" else "float64 only")
        out.append("| %s | %.10f | %.10f | %.3e | %.3e | %.3e | %s |" % (a, qlo, qhi, qhi - qlo, 2 - qlo, qhi - 2, ", ".join(chk)))
        print(out[-1], flush=True)
    txt = "\n".join(out) + "\n"
    open(os.path.join(RES, "lag_tolerance_n%d%s.md" % (n, "" if check == "1" else "_float64")), "w").write(txt)
    print(txt)


def rates():
    """Empirical exponential rate in a of lambda_min(G) and of the margins (n = 240)."""
    import numpy as np
    R = recs()
    w = w2()
    rows = []
    for a in ["0.42", "0.45", "0.48", "0.50", "0.52", "0.54", "0.549"]:
        r = R[(a, 240)]
        rows.append((float(a), float(r["minG"]), float(mp.mpf(r["c_hi"]) - w), float(w - mp.mpf(r["c_lo"])),
                     float(-1 - mp.mpf(r["sectors"]["even"]["rho_w2"])), float(1 - mp.mpf(r["sectors"]["odd"]["rho_w2"]))))
    X = np.array(rows)
    names = ["min G", "c_hi - w2", "w2 - c_lo", "-1 - rho_even(w2)", "1 - rho_odd(w2)"]
    out = ["# empirical decay rates (n = 240, a in [0.42, 0.549]): quantity ~ C exp(-kappa a)", "",
           "| quantity | kappa (LSQ slope of -log) | kappa / gamma_1 |", "|---|---|---|"]
    g1 = 14.134725141734693
    for j, nm in enumerate(names):
        k = -np.polyfit(X[:, 0], np.log(X[:, j + 1]), 1)[0]
        out.append("| %s | %.2f | %.3f |" % (nm, k, k / g1))
    out.append("")
    out.append("| a | min G | c_hi - w2 | w2 - c_lo | -1 - rho_even | 1 - rho_odd | (c_hi - w2)/min G |")
    out.append("|---|---|---|---|---|---|---|")
    for r in rows:
        out.append("| %.3f | %.3e | %.3e | %.3e | %.3e | %.3e | %.1f |" % (r + (r[2] / r[1],)))
    txt = "\n".join(out) + "\n"
    open(os.path.join(RES, "rates.md"), "w").write(txt)
    print(txt)


def cctable():
    """CC-type quantity: lambda_min of K - cQ (K = ARCH - CONST) on the hyperplane(s) where the pole
    functionals vanish (even: int f cosh(x/2) = 0 [and int f = 0]; odd: int f sinh(x/2) = 0)."""
    import glob
    rows = []
    for p_ in glob.glob(os.path.join(SCR, "cc_a*_n*.json")):
        d = json.load(open(p_))
        rows.append(d)
    rows.sort(key=lambda d: (float(d["a"]), d["n"]))
    keys = ["even|pole|c=0", "even|pole|c=w2", "even|pole+mean|c=0", "even|pole+mean|c=w2", "odd|pole|c=0", "odd|pole|c=w2"]
    out = ["# lambda_min of (K - cQ, M) restricted to the pole-free hyperplane (CC1-type object, plus one prime)",
           "# a > log3/2 = 0.549: rows are archimedean information only (c = w2 there is NOT the Weil form: p = 3 enters)", "",
           "| a | n | " + " | ".join(keys) + " |", "|---|---|" + "---|" * len(keys)]
    for d in rows:
        out.append("| %s | %d | %s |" % (d["a"], d["n"], " | ".join(f(d[k], 4) for k in keys)))
    txt = "\n".join(out) + "\n"
    open(os.path.join(RES, "cc_hyperplane.md"), "w").write(txt)
    print(txt)


def aitken(x0, x1, x2):
    d = (x2 - x1) - (x1 - x0)
    return x2 - (x2 - x1) ** 2 / d if d != 0 else x2


def extrap():
    """n -> infinity extrapolation of c_lo, c_hi (and the margins) per a, plus mp.identify attempts."""
    mp.mp.dps = 30
    R = recs()
    w = w2()
    lines = ["# n -> inf extrapolation of the admissible interval (Aitken on n = 60, 120, 240 and on 90, 180 + fit)", "",
             "| a | quantity | n=30 | 60 | 90 | 120 | 180 | 240 | Aitken(60,120,240) | power fit c_inf + C n^-p (120,180,240) | identify(Aitken) |",
             "|---|---|---|---|---|---|---|---|---|---|---|"]
    for a in A_GRID:
        if (a, 240) not in R or "c_lo" not in R[(a, 240)]:
            continue
        for q in ("c_lo", "c_hi", "rho_even_w2", "rho_odd_w2", "minG"):
            vals = {}
            for n in N_GRID:
                r = R.get((a, n))
                if r is None:
                    continue
                if q in ("c_lo", "c_hi", "minG"):
                    vals[n] = mp.mpf(r[q])
                elif q == "rho_even_w2":
                    vals[n] = mp.mpf(r["sectors"]["even"]["rho_w2"])
                else:
                    vals[n] = mp.mpf(r["sectors"]["odd"]["rho_w2"])
            ait = aitken(vals[60], vals[120], vals[240]) if all(k in vals for k in (60, 120, 240)) else mp.nan
            # power fit through 120, 180, 240: c + C n^-p
            fit = mp.nan
            try:
                y1, y2, y3 = vals[120], vals[180], vals[240]
                g = lambda p_: (y1 - y2) / (y2 - y3) - (mp.mpf(120) ** -p_ - mp.mpf(180) ** -p_) / (mp.mpf(180) ** -p_ - mp.mpf(240) ** -p_)
                p_ = mp.findroot(g, 1.0)
                C = (y2 - y3) / (mp.mpf(180) ** -p_ - mp.mpf(240) ** -p_)
                fit = "%s (p=%s)" % (mp.nstr(y3 - C * mp.mpf(240) ** -p_, 10), mp.nstr(p_, 3))
            except Exception as e:
                fit = "no fit"
            ident = "-"
            if q in ("c_lo", "c_hi") and ait == ait:
                try:
                    ident = mp.identify(ait, ["log(2)", "pi", "euler", "sqrt(2)"], tol=mp.mpf(10) ** -7) or "none"
                except Exception:
                    ident = "err"
            lines.append("| %s | %s | %s | %s | %s |" % (a, q, " | ".join(mp.nstr(vals.get(n, mp.nan), 10) for n in N_GRID),
                                                         mp.nstr(ait, 10), fit + " | " + str(ident)))
    lines.append("")
    lines.append("w2 = %s" % mp.nstr(w, 20))
    txt = "\n".join(lines) + "\n"
    open(os.path.join(RES, "extrapolation.md"), "w").write(txt)
    print(txt)


if __name__ == "__main__":
    cmd = sys.argv[1]
    if cmd == "build":
        build(*sys.argv[2:])
    else:
        globals()[cmd](*sys.argv[2:])
