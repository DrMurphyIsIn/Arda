#!/usr/bin/env python3
"""
Experiments on Gram matrices of Weil's quadratic functional (see weil_form.py for the validated
explicit formula).  Exploration only; nothing here is progress on RH.  conjecture1_proved = False.

Subcommands (each writes into results/):
  exp1_spline              Gram spectra, B-spline basis, all (a, n)
  exp12_hermite A N        Gram spectra + decomposition, Hermite basis, one a (run in parallel)
  exp2_spline              decomposition G = A - P, B-spline basis, coarse grid + fine a-scan
  exp3_ccm                 minimal-eigenvector Fourier zeros vs zeta zeros (+ arch-only control)
  exp3_prolate             overlaps of Weil eigenvectors with prolate spheroidal functions (+ control)
  exp3_th                  Toeplitz+Hankel fit in the Hermite basis (+ controls)
  exp3_jacobi              Lanczos / Jacobi coefficients (+ controls)
  exp4_fake                perturbed-prime control: critical epsilon for loss of positivity
"""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ.setdefault(_v, "1")
import sys
import json
import time
import math
import mpmath as mp
import numpy as np
import weil_form as wf

HERE = os.path.dirname(os.path.abspath(__file__))
RES = os.path.join(HERE, "results")
MAT = os.path.join(RES, "matrices")
os.makedirs(MAT, exist_ok=True)
A_LIST = ["0.5", "1", "1.5", "2", "3", "4", "5"]


def nzeros_below(T, zeros):
    return sum(1 for g in zeros if g < T)


def N_rvm(T):
    T = mp.mpf(T)
    return T / (2 * mp.pi) * mp.log(T / (2 * mp.pi * mp.e)) + mp.mpf(7) / 8


def mp2np(M):
    return np.array([[float(M[i, j]) for j in range(M.cols)] for i in range(M.rows)])


def save_matrix(M, path):
    json.dump([[mp.nstr(M[i, j], mp.mp.dps) for j in range(M.cols)] for i in range(M.rows)], open(path, "w"))


def load_matrix(path):
    L = json.load(open(path))
    return mp.matrix([[mp.mpf(x) for x in row] for row in L])


def spectrum_stats(ev):
    mx = max(ev)
    mn = min(ev)
    pos = [e for e in ev if e > 0]
    return dict(min=mn, max=mx, cond=(mx / mn if mn > 0 else mp.inf),
                n_abs=sum(1 for e in ev if e > mp.mpf("1e-8")),
                n_rel=sum(1 for e in ev if e > mp.mpf("1e-8") * mx))


# ----------------------------------------------------------------------------------------------
def exp1_spline():
    mp.mp.dps = 50
    zeros = wf.load_zeros()
    out = open(os.path.join(RES, "exp1_spline_spectra.csv"), "w")
    out.write("a,n,h,T_nyquist,zeros_below_T,two_N_T,min_gen_eig,max_gen_eig,cond_gen,count_gt_1e-8,count_gt_1e-8_rel,min_eig_G_plain\n")
    spec = open(os.path.join(RES, "exp1_spline_full_spectra.txt"), "w")
    for a in A_LIST:
        for n in (10, 20, 40, 60):
            t = time.time()
            S = wf.spline_gram(a, n)
            ev, V = wf.gen_eig(S["G"], S["MASS"])
            evG = sorted(mp.eigsy(S["G"], eigvals_only=True))
            st = spectrum_stats(ev)
            T = mp.pi / S["h"]
            nz = nzeros_below(T, zeros)
            out.write("%s,%d,%s,%s,%d,%d,%s,%s,%s,%d,%d,%s\n" % (
                a, n, mp.nstr(S["h"], 6), mp.nstr(T, 6), nz, 2 * nz, mp.nstr(st["min"], 6), mp.nstr(st["max"], 6),
                mp.nstr(st["cond"], 6), st["n_abs"], st["n_rel"], mp.nstr(evG[0], 6)))
            out.flush()
            spec.write("a=%s n=%d generalized eigenvalues (ascending):\n%s\n\n" % (a, n, " ".join(mp.nstr(e, 6) for e in ev)))
            spec.flush()
            if n == 60:
                for k in ("G", "pole", "prime", "const", "arch", "MASS"):
                    save_matrix(S[k], os.path.join(MAT, "mat_spline_a%s_n60_%s.json" % (a, k)))
            print(a, n, "min", mp.nstr(st["min"], 5), "count", st["n_abs"], "2N(T)", 2 * nz, "%.1fs" % (time.time() - t), flush=True)


def exp12_hermite(a, n):
    mp.mp.dps = 40
    zeros = wf.load_zeros()
    t = time.time()
    H = wf.hermite_gram(a, int(n))
    n = int(n)
    G = H["G"]
    Amat = H["pole"] - H["const"] + H["arch"]
    P = H["prime"]
    tag = "a%s_n%d" % (a, n)
    for k, M in (("G", G), ("A", Amat), ("P", P)):
        save_matrix(M, os.path.join(MAT, "mat_hermite_%s_%s.json" % (tag, k)))
    evG = sorted(mp.eigsy(G, eigvals_only=True))
    evA = sorted(mp.eigsy(Amat, eigvals_only=True))
    evP = sorted(mp.eigsy(P, eigvals_only=True)) if any(P[i, j] != 0 for i in range(n) for j in range(n)) else [mp.mpf(0)] * n
    st = spectrum_stats(evG)
    T = H["ustar"] / H["sigma"]
    nz = nzeros_below(T, zeros)
    rec = dict(a=a, n=n, sigma=mp.nstr(H["sigma"], 8), ustar=mp.nstr(H["ustar"], 6), T_band=mp.nstr(T, 6), zeros_below_T=nz,
               min_eig_G=mp.nstr(st["min"], 6), max_eig_G=mp.nstr(st["max"], 6), cond=mp.nstr(st["cond"], 6),
               count_gt_1e8=st["n_abs"], count_gt_1e8_rel=st["n_rel"],
               min_eig_A=mp.nstr(evA[0], 6), max_eig_A=mp.nstr(evA[-1], 6),
               min_eig_P=mp.nstr(evP[0], 6), max_eig_P=mp.nstr(evP[-1], 6),
               normP=mp.nstr(max(abs(evP[0]), abs(evP[-1])), 6), seconds=round(time.time() - t, 1),
               spectrum_G=[mp.nstr(e, 6) for e in evG], spectrum_A=[mp.nstr(e, 6) for e in evA], spectrum_P=[mp.nstr(e, 6) for e in evP])
    json.dump(rec, open(os.path.join(RES, "exp12_hermite_%s.json" % tag), "w"), indent=1)
    print(json.dumps({k: v for k, v in rec.items() if not k.startswith("spectrum")}), flush=True)


def exp2_spline():
    mp.mp.dps = 50
    out = open(os.path.join(RES, "exp2_spline_decomposition.csv"), "w")
    out.write("a,n,primes_in_play,min_gen_eig_G,min_gen_eig_A,max_gen_eig_A,min_gen_eig_P,max_gen_eig_P,normP_over_minA,A_alone_PSD\n")
    grid = [("0.2", 30), ("0.3", 30), ("0.3466", 30), ("0.4", 30), ("0.5", 30), ("0.6", 30), ("0.7", 30), ("0.8", 30),
            ("0.9", 30), ("1", 30), ("1.25", 30), ("1.5", 30), ("2", 30), ("2.5", 30), ("3", 30), ("4", 30), ("5", 30),
            ("1", 60), ("2", 60), ("3", 60), ("5", 60)]
    for a, n in grid:
        S = wf.spline_gram(a, n)
        M = S["MASS"]
        Am = S["pole"] - S["const"] + S["arch"]
        P = S["prime"]
        evG, _ = wf.gen_eig(S["G"], M)
        evA, _ = wf.gen_eig(Am, M)
        if any(P[i, j] != 0 for i in range(n) for j in range(n)):
            evP, _ = wf.gen_eig(P, M)
        else:
            evP = [mp.mpf(0)]
        pp = [q for q, _ in wf.prime_powers(mp.exp(2 * mp.mpf(a)))]
        normP = max(abs(evP[0]), abs(evP[-1]))
        ratio = normP / abs(evA[0]) if evA[0] != 0 else mp.inf
        out.write("%s,%d,%s,%s,%s,%s,%s,%s,%s,%s\n" % (a, n, "|".join(map(str, pp[:12])) + ("..." if len(pp) > 12 else ""),
                                                      mp.nstr(evG[0], 6), mp.nstr(evA[0], 6), mp.nstr(evA[-1], 6), mp.nstr(evP[0], 6),
                                                      mp.nstr(evP[-1], 6), mp.nstr(ratio, 6), evA[0] >= 0))
        out.flush()
        print(a, n, "minG", mp.nstr(evG[0], 5), "minA", mp.nstr(evA[0], 5), "P range", mp.nstr(evP[0], 5), mp.nstr(evP[-1], 5), flush=True)


# ----------------------------------------------------------------------------------------------
def spline_FT(a, n, c, t):
    """F(1/2 + i t) of f = sum c_j phi_j (spline basis)."""
    a = mp.mpf(a)
    h = 2 * a / (n + 3)
    s = wf.sinc(t * h / 2) ** 4 * h
    return s * mp.fsum(c[j] * mp.expj(t * (-a + (j + 2) * h)) for j in range(n))


def real_zeros_of(fun, T, step):
    """Sign changes of a real function on (0, T], refined by bisection-secant (mp.findroot anderson)."""
    zs = []
    t0 = mp.mpf(step) / 7
    f0 = fun(t0)
    t = t0
    while t < T:
        t1 = t + step
        f1 = fun(t1)
        if f0 == 0:
            zs.append(t)
        elif f0 * f1 < 0:
            try:
                z = mp.findroot(fun, (t, t1), solver="anderson")
            except Exception:
                z = (t + t1) / 2
            zs.append(z)
        t, f0 = t1, f1
    return zs


def exp3_ccm():
    """Connes-Consani-Moscovici-type check: Fourier zeros of the minimal eigenvector vs zeta zeros."""
    mp.mp.dps = 50
    zeros = wf.load_zeros(200)
    out = open(os.path.join(RES, "exp3a_min_eigvec_fourier_zeros.txt"), "w")
    for a, n in (("1", 60), ("2", 60), ("3", 60), ("2", 100), ("3", 100)):
        S = wf.spline_gram(a, n)
        M = S["MASS"]
        for label, Gm in (("weil G=A-P", S["G"]), ("control: A only (no primes)", S["pole"] - S["const"] + S["arch"])):
            ev, V = wf.gen_eig(Gm, M)
            for which in (0, 1):
                c = [V[r, which] for r in range(n)]
                # parity
                even = abs(sum(c[j] - c[n - 1 - j] for j in range(n))) < abs(sum(c[j] + c[n - 1 - j] for j in range(n)))
                if even:
                    fun = lambda t: mp.re(spline_FT(a, n, c, t))
                else:
                    fun = lambda t: mp.im(spline_FT(a, n, c, t))
                Tchk = min(mp.mpf(80), mp.pi / S["h"] * mp.mpf("0.6"))
                fz = real_zeros_of(fun, Tchk, mp.mpf("0.05"))
                out.write("a=%s n=%d %s eigvec #%d (eig=%s, %s): Fourier zeros in (0,%s):\n" % (
                    a, n, label, which, mp.nstr(ev[which], 6), "even" if even else "odd", mp.nstr(Tchk, 4)))
                matches = []
                for g in zeros:
                    if g > Tchk:
                        break
                    if fz:
                        z = min(fz, key=lambda u: abs(u - g))
                        matches.append((g, z, z - g))
                for g, z, d in matches:
                    out.write("   gamma=%s  nearest FT zero=%s  diff=%s\n" % (mp.nstr(g, 12), mp.nstr(z, 15), mp.nstr(d, 4)))
                extra = [z for z in fz if all(abs(z - g) > mp.mpf("0.5") for g in zeros if g < Tchk + 5)]
                out.write("   FT zeros total=%d, zeta zeros below=%d, FT zeros farther than 0.5 from any zeta zero: %s\n\n" % (
                    len(fz), len(matches), [mp.nstr(z, 6) for z in extra]))
                out.flush()
                print(a, n, label, which, "eig", mp.nstr(ev[which], 4), "diffs", [mp.nstr(d, 3) for _, _, d in matches[:8]], flush=True)


# ---------- prolates ----------
def pswf_legendre(c, K, N=200):
    """Prolate spheroidal wave functions on [-1,1], bandwidth c, as coefficient vectors in the
    L2-normalized Legendre basis (Bouwkamp tridiagonal method, even/odd blocks).  Returns list of
    (chi, coeff) for the first K, ordered by increasing chi."""
    res = []
    for par in (0, 1):
        ks = np.arange(par, N, 2)
        m = len(ks)
        Mx = np.zeros((m, m))
        for i, k in enumerate(ks):
            Mx[i, i] = k * (k + 1) + c * c * (2.0 * k * (k + 1) - 1) / ((2 * k + 3) * (2 * k - 1))
            if i + 1 < m:
                v = c * c * (k + 2) * (k + 1) / ((2 * k + 3) * math.sqrt((2 * k + 1) * (2 * k + 5)))
                Mx[i, i + 1] = Mx[i + 1, i] = v
        w, U = np.linalg.eigh(Mx)
        for j in range(m):
            coef = np.zeros(N)
            coef[ks] = U[:, j]
            res.append((w[j], coef))
    res.sort(key=lambda r: r[0])
    return res[:K]


def legendre_norm_eval(N, x):
    """L2([-1,1])-normalized Legendre P_k(x) for k < N, x array -> (N, len(x))."""
    P = np.zeros((N, len(x)))
    P[0] = 1
    if N > 1:
        P[1] = x
    for k in range(1, N - 1):
        P[k + 1] = ((2 * k + 1) * x * P[k] - k * P[k - 1]) / (k + 1)
    return P * np.sqrt((2 * np.arange(N) + 1) / 2)[:, None]


def spline_eval_np(a, n, x):
    h = 2 * a / (n + 3)
    out = np.zeros((n, len(x)))
    for j in range(n):
        u = np.abs((x - (-a + (j + 2) * h)) / h)
        out[j] = np.where(u < 1, 2.0 / 3 - u * u + u ** 3 / 2, np.where(u < 2, (2 - u) ** 3 / 6, 0.0))
    return out


def exp3_prolate():
    mp.mp.dps = 50
    a, n = 2, 80
    S = wf.spline_gram(a, n)
    M = S["MASS"]
    xg, wg = np.polynomial.legendre.leggauss(600)
    B = spline_eval_np(a, n, a * xg)  # basis on nodes of [-a, a]
    L = legendre_norm_eval(200, xg)
    out = open(os.path.join(RES, "exp3a_prolate_overlaps.txt"), "w")
    for label, Gm in (("weil G", S["G"]), ("control A only", S["pole"] - S["const"] + S["arch"])):
        ev, V = wf.gen_eig(Gm, M)
        Vn = mp2np(V)
        funcs = Vn.T @ B  # each row: eigenfunction values on a*xg
        nrm = np.sqrt((funcs ** 2 * wg).sum(1) * a)
        funcs = funcs / nrm[:, None]
        # as functions on [-1,1] (u = x/a), L2-normalized: f(u) * sqrt(a)
        fu = funcs * math.sqrt(a)
        best = None
        for c in np.concatenate([np.linspace(0.25, 10, 40), np.linspace(11, 80, 24)]):
            ps = pswf_legendre(c, 20)
            Pv = np.array([coef @ L for _, coef in ps])  # (20, nodes)
            O = np.abs((fu[:, None, :] * Pv[None, :, :] * wg).sum(2))  # (n, 20)
            for side, idx in (("lowest", range(10)), ("highest", range(n - 1, n - 11, -1))):
                score = np.mean([O[i].max() for i in idx])
                if best is None or (side, ) == ("lowest",) and False:
                    pass
                key = (label, side)
                if not hasattr(exp3_prolate, "b"):
                    exp3_prolate.b = {}
                if key not in exp3_prolate.b or score > exp3_prolate.b[key][0]:
                    exp3_prolate.b[key] = (score, c, O[list(idx)].copy())
        for side in ("lowest", "highest"):
            score, c, O = exp3_prolate.b[(label, side)]
            out.write("%s, %s 10 eigenvectors (a=%d, n=%d): best bandwidth c=%.3f, mean max-overlap=%.4f\n" % (label, side, a, n, c, score))
            for r in range(10):
                k = int(O[r].argmax())
                out.write("   eigvec %d: max |<v, PSWF_k>| = %.4f at k=%d ; |<v, PSWF_r>| = %.4f\n" % (r, O[r].max(), k, O[r][r] if r < O.shape[1] else float('nan')))
            out.write("\n")
        out.flush()
        print(label, {k: (round(v[0], 4), round(float(v[1]), 2)) for k, v in exp3_prolate.b.items()}, flush=True)
    # baseline: random functions in the same spline space (orthonormalized)
    rng = np.random.default_rng(1)
    Mn = mp2np(M)
    Lm = np.linalg.cholesky(Mn)
    Q, _ = np.linalg.qr(rng.standard_normal((n, n)))
    C = np.linalg.solve(Lm.T, Q)
    funcs = C.T @ B
    funcs /= np.sqrt((funcs ** 2 * wg).sum(1) * a)[:, None]
    fu = funcs * math.sqrt(a)
    bestr = 0
    for c in np.linspace(0.25, 40, 60):
        ps = pswf_legendre(c, 20)
        Pv = np.array([coef @ L for _, coef in ps])
        O = np.abs((fu[:, None, :] * Pv[None, :, :] * wg).sum(2))
        bestr = max(bestr, np.mean([O[i].max() for i in range(10)]))
    out.write("baseline: 10 random orthonormal functions in the same spline space: best mean max-overlap over c = %.4f\n" % bestr)
    print("random baseline", bestr)


def th_fit(Mx):
    n = Mx.shape[0]
    rows, cols = [], []
    A = np.zeros((n * n, 2 * n - 1 + 2 * n - 1))
    b = np.zeros(n * n)
    r = 0
    for i in range(n):
        for j in range(n):
            A[r, (i - j) + n - 1] = 1
            A[r, 2 * n - 1 + i + j] = 1
            b[r] = Mx[i, j]
            r += 1
    x, *_ = np.linalg.lstsq(A, b, rcond=None)
    res = b - A @ x
    resT = None
    At = A[:, :2 * n - 1]
    xt, *_ = np.linalg.lstsq(At, b, rcond=None)
    return np.linalg.norm(res) / np.linalg.norm(b), np.linalg.norm(b - At @ xt) / np.linalg.norm(b)


def exp3_th():
    out = open(os.path.join(RES, "exp3b_toeplitz_hankel.txt"), "w")
    out.write("relative Frobenius residual of best Toeplitz+Hankel fit (and Toeplitz-only fit), Hermite basis\n")
    rng = np.random.default_rng(7)
    for f in sorted(os.listdir(MAT)):
        if f.startswith("mat_hermite_") and f.endswith("_G.json"):
            tag = f[len("mat_hermite_"):-len("_G.json")]
            mp.mp.dps = 40
            res = {}
            for k in ("G", "A", "P"):
                Mx = mp2np(load_matrix(os.path.join(MAT, "mat_hermite_%s_%s.json" % (tag, k))))
                res[k] = th_fit(Mx) if np.linalg.norm(Mx) > 0 else (float("nan"), float("nan"))
            Gn = mp2np(load_matrix(os.path.join(MAT, "mat_hermite_%s_G.json" % tag)))
            w, U = np.linalg.eigh(Gn)
            Q, _ = np.linalg.qr(rng.standard_normal(Gn.shape))
            res["control: same spectrum, random eigenbasis"] = th_fit(Q @ np.diag(w) @ Q.T)
            # control: multiplication by a smooth symbol in frequency (log(1+r^2)) in the same Hermite basis
            n = Gn.shape[0]
            a = float(tag.split("_")[0][1:])
            ustar = float(wf.hermite_ustar(n, mp.mpf("1e-30")))
            sigma = a / ustar
            r, wr = np.polynomial.hermite.hermgauss(200)
            # psi_k(u) e^{u^2/2} at Gauss-Hermite nodes u = r
            V = np.zeros((n, len(r)))
            V[0] = np.pi ** -0.25
            if n > 1:
                V[1] = np.sqrt(2) * r * V[0]
            for k in range(1, n - 1):
                V[k + 1] = np.sqrt(2 / (k + 1)) * r * V[k] - np.sqrt(k / (k + 1)) * V[k - 1]
            sym = np.log(1 + (r / sigma) ** 2)
            Mmul = (V * wr * sym) @ V.T
            ph = np.array([[(1j) ** (j - k) for k in range(n)] for j in range(n)]).real
            res["control: multiplication by log(1+r^2) in frequency"] = th_fit(Mmul * ph)
            for k, (r1, r2) in res.items():
                out.write("%-12s %-55s T+H residual = %.3e   T-only residual = %.3e\n" % (tag, k, r1, r2))
            out.flush()
            print(tag, {k: "%.2e/%.2e" % v for k, v in res.items()}, flush=True)


def lanczos(S, b, steps):
    n = S.rows
    q = b / mp.norm(b)
    Qs = [q]
    alph, bet = [], []
    qprev = mp.matrix(n, 1)
    beta = mp.mpf(0)
    for k in range(steps):
        w = S * q - beta * qprev
        al = (q.T * w)[0]
        w = w - al * q
        for qq in Qs:  # full reorthogonalization
            w = w - (qq.T * w)[0] * qq
        alph.append(al)
        beta = mp.norm(w)
        if beta < mp.mpf(10) ** (-mp.mp.dps + 10):
            break
        bet.append(beta)
        qprev, q = q, w / beta
        Qs.append(q)
    return alph, bet


def exp3_jacobi():
    mp.mp.dps = 60
    out = open(os.path.join(RES, "exp3c_jacobi.txt"), "w")
    a, n = 2, 60
    S = wf.spline_gram(a, n)
    M = S["MASS"]
    Lc = mp.cholesky(M)
    Li = mp.inverse(Lc)
    u = mp.matrix([S["h"]] * n)  # coefficients of int phi_j  (F_j(1/2))
    b0 = Li * u
    for label, Gm in (("weil G", S["G"]), ("control A only", S["pole"] - S["const"] + S["arch"])):
        St = Li * Gm * Li.T
        for start, b in (("pole-direction start (int f)", b0), ("random start", mp.matrix([mp.mpf(math.sin(7.3 * k + 1.1)) for k in range(n)]))):
            al, be = lanczos(St, b, 30)
            out.write("%s, %s, a=%d n=%d\n k  alpha_k  beta_k  beta_k/beta_{k-1}\n" % (label, start, a, n))
            for k in range(len(al)):
                bk = be[k] if k < len(be) else mp.mpf(0)
                ratio = be[k] / be[k - 1] if 0 < k < len(be) else mp.mpf(0)
                out.write(" %2d  %s  %s  %s\n" % (k, mp.nstr(al[k], 8), mp.nstr(bk, 8), mp.nstr(ratio, 5)))
            out.write("\n")
            out.flush()
            print(label, start, [mp.nstr(x, 3) for x in be[:12]], flush=True)


# ----------------------------------------------------------------------------------------------
def chi4(n):
    return 0 if n % 2 == 0 else (1 if n % 4 == 1 else -1)


def exp4_fake():
    """G(eps) = G - eps * P_chi, P_chi = prime form with Lambda(n) chi(n).  Critical eps from the
    generalized eigenproblem (P_chi, G): eps+ = 1/max mu, eps- = 1/min mu."""
    mp.mp.dps = 50
    out = open(os.path.join(RES, "exp4_fake_prime_control.csv"), "w")
    out.write("a,n,chi,eps_crit_plus,eps_crit_minus,min_gen_eig_G,normP_chi_gen\n")
    for chiname, chi in (("chi_-4", chi4), ("chi_-3", lambda m: 0 if m % 3 == 0 else (1 if m % 3 == 1 else -1))):
        for a in ("0.5", "1", "2", "3"):
            for n in (10, 20, 40, 60):
                pp = [(m, L * chi(m)) for m, L in wf.prime_powers(mp.exp(2 * mp.mpf(a)))]
                Sx = wf.spline_gram(a, n, prime_lambda=pp)
                S = wf.spline_gram(a, n)
                Pchi = Sx["prime"]
                G = S["G"]
                mu, _ = wf.gen_eig(Pchi, G)
                epsp = 1 / mu[-1] if mu[-1] > 0 else mp.inf
                epsm = 1 / mu[0] if mu[0] < 0 else -mp.inf
                evG, _ = wf.gen_eig(G, S["MASS"])
                evP, _ = wf.gen_eig(Pchi, S["MASS"]) if any(Pchi[i, j] for i in range(n) for j in range(n)) else ([mp.mpf(0)], None)
                out.write("%s,%d,%s,%s,%s,%s,%s\n" % (a, n, chiname, mp.nstr(epsp, 6), mp.nstr(epsm, 6), mp.nstr(evG[0], 6),
                                                       mp.nstr(max(abs(evP[0]), abs(evP[-1])), 6)))
                out.flush()
                print(chiname, a, n, "eps+", mp.nstr(epsp, 4), "eps-", mp.nstr(epsm, 4), flush=True)




def parity_blocks(Mx, n):
    """Restrict an n x n reflection-symmetric matrix to even / odd coefficient vectors
    (basis e_j +- e_{n-1-j}, normalized)."""
    m_e = (n + 1) // 2
    m_o = n // 2
    Ue = mp.matrix(n, m_e)
    Uo = mp.matrix(n, m_o)
    for j in range(m_e):
        if j == n - 1 - j:
            Ue[j, j] = 1
        else:
            Ue[j, j] = Ue[n - 1 - j, j] = 1 / mp.sqrt(2)
    for j in range(m_o):
        Uo[j, j] = 1 / mp.sqrt(2)
        Uo[n - 1 - j, j] = -1 / mp.sqrt(2)
    return Ue.T * Mx * Ue, Uo.T * Mx * Uo, Ue, Uo


def exp2_extra():
    """Fine a-scan near log(2)/2 and a split A = POLE + (ARCH - CONST), by parity sector."""
    mp.mp.dps = 50
    out = open(os.path.join(RES, "exp2_spline_decomposition_extra.csv"), "w")
    out.write("a,n,sector,min_G,min_A,min_P,max_P,min_POLE,max_POLE,min_ARCHminusCONST,max_ARCHminusCONST\n")
    for a in ("0.30", "0.3466", "0.35", "0.36", "0.37", "0.38", "0.39", "0.4", "0.5", "1", "2", "3", "5"):
        n = 30
        S = wf.spline_gram(a, n)
        mats = dict(G=S["G"], A=S["pole"] - S["const"] + S["arch"], P=S["prime"], POLE=S["pole"], AC=S["arch"] - S["const"])
        Me, Mo, Ue, Uo = parity_blocks(S["MASS"], n)
        for sec, U, Ms in (("even", Ue, Me), ("odd", Uo, Mo)):
            r = {}
            for k, Mx in mats.items():
                B = U.T * Mx * U
                ev, _ = wf.gen_eig(B, Ms)
                r[k] = (ev[0], ev[-1])
            out.write("%s,%d,%s,%s,%s,%s,%s,%s,%s,%s,%s\n" % (a, n, sec, mp.nstr(r["G"][0], 5), mp.nstr(r["A"][0], 5),
                      mp.nstr(r["P"][0], 5), mp.nstr(r["P"][1], 5), mp.nstr(r["POLE"][0], 5), mp.nstr(r["POLE"][1], 5),
                      mp.nstr(r["AC"][0], 5), mp.nstr(r["AC"][1], 5)))
            out.flush()
            print(a, sec, {k: (mp.nstr(v[0], 4), mp.nstr(v[1], 4)) for k, v in r.items()}, flush=True)


def exp3_prolate2():
    """Finer bandwidth scan: for several a, which prolate bandwidth c best matches the lowest
    Weil eigenvectors, and does Omega = c/a track the first zeta ordinate 14.1347?"""
    mp.mp.dps = 50
    out = open(os.path.join(RES, "exp3a_prolate_bandwidth_scan.txt"), "w")
    out.write("a,n,operator,best_c,Omega=c/a,mean_overlap_lowest8,overlaps_k=0..7 (eigvec k vs PSWF_k)\n")
    xg, wg = np.polynomial.legendre.leggauss(600)
    L = legendre_norm_eval(200, xg)
    for a, n in ((1, 60), (2, 80), (3, 100), (4, 120)):
        S = wf.spline_gram(a, n)
        M = S["MASS"]
        B = spline_eval_np(a, n, a * xg)
        for label, Gm in (("weil G", S["G"]), ("control A only", S["pole"] - S["const"] + S["arch"])):
            ev, V = wf.gen_eig(Gm, M)
            fu = mp2np(V).T @ B
            fu = fu / np.sqrt((fu ** 2 * wg).sum(1))[:, None]
            best = (-1, None, None)
            for c in np.arange(0.5, 25 * a + 0.01, 0.25):
                ps = pswf_legendre(c, 12)
                Pv = np.array([coef @ L for _, coef in ps])
                O = np.abs((fu[:8, None, :] * Pv[None, :8, :] * wg).sum(2))
                d = np.diag(O)
                if d.mean() > best[0]:
                    best = (d.mean(), c, d.copy())
            out.write("%d,%d,%s,%.2f,%.3f,%.4f,%s\n" % (a, n, label, best[1], best[1] / a, best[0], " ".join("%.3f" % x for x in best[2])))
            out.flush()
            print(a, n, label, "best c", best[1], "Omega", best[1] / a, "mean", round(best[0], 4), flush=True)


def exp2_bisect():
    """Locate a* where the archimedean+pole form A alone stops being PSD (odd sector), for n=30, 60."""
    mp.mp.dps = 50
    out = open(os.path.join(RES, "exp2_A_alone_threshold.txt"), "w")
    for n in (30, 60, 90):
        def minA(a):
            S = wf.spline_gram(a, n)
            ev, _ = wf.gen_eig(S["pole"] - S["const"] + S["arch"], S["MASS"])
            return ev[0]
        lo, hi = mp.mpf("0.3466"), mp.mpf("0.40")
        flo, fhi = minA(lo), minA(hi)
        for _ in range(14):
            mid = (lo + hi) / 2
            fm = minA(mid)
            if fm > 0:
                lo, flo = mid, fm
            else:
                hi, fhi = mid, fm
        out.write("n=%d: A alone PSD at a=%s (min %s), not PSD at a=%s (min %s); log(2)/2 = %s\n" % (
            n, mp.nstr(lo, 8), mp.nstr(flo, 4), mp.nstr(hi, 8), mp.nstr(fhi, 4), mp.nstr(mp.log(2) / 2, 8)))
        out.flush()
        print(n, mp.nstr(lo, 8), mp.nstr(hi, 8), flush=True)


def exp2_bisect_n(n, steps="11"):
    """Same as exp2_bisect for one n (appends to exp2_A_alone_threshold_n.txt)."""
    mp.mp.dps = 50
    n = int(n)
    def minA(a):
        S = wf.spline_gram(a, n)
        ev, _ = wf.gen_eig(S["pole"] - S["const"] + S["arch"], S["MASS"])
        return ev[0]
    lo, hi = mp.mpf("0.3466"), mp.mpf("0.40")
    flo, fhi = minA(lo), minA(hi)
    for _ in range(int(steps)):
        mid = (lo + hi) / 2
        fm = minA(mid)
        if fm > 0:
            lo, flo = mid, fm
        else:
            hi, fhi = mid, fm
    with open(os.path.join(RES, "exp2_A_alone_threshold_n%d.txt" % n), "w") as out:
        out.write("n=%d: A alone PSD at a=%s (min %s), not PSD at a=%s (min %s); log(2)/2 = %s\n" % (
            n, mp.nstr(lo, 8), mp.nstr(flo, 4), mp.nstr(hi, 8), mp.nstr(fhi, 4), mp.nstr(mp.log(2) / 2, 8)))
    print(n, mp.nstr(lo, 8), mp.nstr(hi, 8), flush=True)


if __name__ == "__main__":
    cmd = sys.argv[1]
    globals()[cmd](*sys.argv[2:])
