#!/usr/bin/env python3
"""
Follow-up to the Weil Gram experiments, set up as in the Connes-Consani papers:
  CC1 = arXiv:2006.13771 (archimedean positivity, window 2L <= log 2),
  CC2 = arXiv:2106.01715 (semilocal numerics; section 2.2 archimedean sign change, section 3 prolates),
  CvS = arXiv:2511.23257 (Connes-van Suijlekom, abstract only: real zeros of the lowest eigenvector).
Reading notes: ~/rh-team/B/connes_consani_reading.md.  Exploration only; nothing here is progress
on RH.  conjecture1_proved = False.

Basis: L2-normalised Legendre polynomials on [-a, a] (a = L = half-width of supp f), which do NOT
vanish at the endpoints.  (The cubic-spline basis of gram_experiments.py vanishes to second order
at +-a and converges only like 1/n for the smallest eigenvalues; see the note.)

  phi_j(x) = sqrt((2j+1)/(2a)) P_j(x/a) on [-a, a];  M = I.
  C_jk(x) = int phi_j(y) phi_k(y - x) dy  (exact Gauss-Legendre: polynomial integrand),
  s_jk(x) = C_jk(x) + C_kj(x) = (1 + (-1)^{j+k}) C_jk(x),  x in [0, 2a].
  G = POLE - PRIME - CONST + ARCH exactly as in weil_form.py (validated convention).

Subcommands: check | cc_crosscheck | a_sweep | cc2_prolate | cvs
"""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ.setdefault(_v, "1")
import sys
import math
import time
import json
import mpmath as mp
import numpy as np
import weil_form as wf

HERE = os.path.dirname(os.path.abspath(__file__))
RES = os.path.join(HERE, "results")


def leg_vals(K, t):
    """Normalised (on [-1,1]) Legendre values sqrt((2j+1)/2) P_j(t), j < K."""
    P = [mp.mpf(1), t]
    for j in range(1, K - 1):
        P.append(((2 * j + 1) * t * P[j] - j * P[j - 1]) / (j + 1))
    return [P[j] * mp.sqrt(mp.mpf(2 * j + 1) / 2) for j in range(K)]


def phi_vals(K, a, x):
    if abs(x) > a:
        return [mp.mpf(0)] * K
    s = 1 / mp.sqrt(a)
    return [v * s for v in leg_vals(K, x / a)]


def corr(K, a, x, q):
    """C_jk(x), x in [0, 2a], by q-point Gauss-Legendre on the overlap [x - a, a]."""
    xs, ws = wf.gl_nodes(q)
    lo, hi = x - a, a
    hm = (hi - lo) / 2
    mid = (hi + lo) / 2
    A = []
    B = []
    W = []
    for t, w in zip(xs, ws):
        y = mid + hm * t
        A.append(phi_vals(K, a, y))
        B.append(phi_vals(K, a, y - x))
        W.append(w * hm)
    C = [[mp.mpf(0)] * K for _ in range(K)]
    for j in range(K):
        Aj = [A[l][j] * W[l] for l in range(len(W))]
        for k in range(j % 2, K, 2):  # only j+k even is needed (s_jk = 0 otherwise)
            C[j][k] = mp.fdot(Aj, [B[l][k] for l in range(len(W))])
    return C


def legendre_gram(a, K, prime_lambda=None, panels=4, q_outer=None, verbose=False):
    a = mp.mpf(a)
    q_in = K + 4
    if q_outer is None:
        q_outer = K + 40
    # pole terms
    xs, ws = wf.gl_nodes(120)
    F0 = [mp.mpf(0)] * K
    for t, w in zip(xs, ws):
        v = phi_vals(K, a, a * t)
        e = mp.exp(-a * t / 2) * w * a
        for j in range(K):
            F0[j] += v[j] * e
    F1 = [(-1) ** j * F0[j] for j in range(K)]
    POLE = mp.matrix(K, K)
    for j in range(K):
        for k in range(K):
            POLE[j, k] = F0[j] * F1[k] + F1[j] * F0[k]
    CONST = (mp.log(mp.pi) + mp.euler) * mp.eye(K)
    # primes
    PRIME = mp.matrix(K, K)
    pp = prime_lambda if prime_lambda is not None else wf.prime_powers(mp.exp(2 * a))
    for n, L in pp:
        ln = mp.log(n)
        if ln >= 2 * a:
            break
        C = corr(K, a, ln, q_in)
        w = L / mp.sqrt(n)
        for j in range(K):
            for k in range(j % 2, K, 2):
                PRIME[j, k] += w * 2 * C[j][k]
    # arch: scalar part (delta_jk) + polynomial part on Gauss-Legendre panels
    with mp.extradps(20):
        scal = mp.quad(lambda x: (2 * mp.exp(-2 * x) - 2 * mp.exp(-x / 2)) / (-mp.expm1(-2 * x)), [0, a, 2 * a]) \
            - mp.log(-mp.expm1(-4 * a))
    ARCH = scal * mp.eye(K)
    xo, wo = wf.gl_nodes(q_outer)
    X = 2 * a
    for p in range(panels):
        lo = X * p / panels
        hm = X / (2 * panels)
        for t, w in zip(xo, wo):
            x = lo + hm * (1 + t)
            with mp.extradps(20):
                ker = mp.exp(-x / 2) / (-mp.expm1(-2 * x))
            C = corr(K, a, x, q_in)
            for j in range(K):
                for k in range(j % 2, K, 2):
                    s = 2 * C[j][k] - (2 if j == k else 0)
                    ARCH[j, k] -= w * hm * ker * s
    G = POLE - PRIME - CONST + ARCH
    return dict(G=G, pole=POLE, prime=PRIME, const=CONST, arch=ARCH, F0=F0, F1=F1)


def sector(Mx, par):
    idx = [j for j in range(Mx.rows) if j % 2 == par]
    B = mp.matrix(len(idx), len(idx))
    for r, i in enumerate(idx):
        for c, j in enumerate(idx):
            B[r, c] = Mx[i, j]
    return B, idx


def eig_sym(B):
    n = B.rows
    for i in range(n):
        for j in range(i + 1, n):
            s = (B[i, j] + B[j, i]) / 2
            B[i, j] = B[j, i] = s
    E, Q = mp.eigsy(B)
    order = sorted(range(n), key=lambda i: E[i])
    return [E[i] for i in order], Q, order


def constrained_min(B, cons):
    """Smallest eigenvalue of B restricted to the orthogonal complement of span(cons).
    Complement basis = eigenvectors of the projector I - C C^T with eigenvalue 1."""
    n = B.rows
    cs = []
    for v in cons:
        w = mp.matrix(v)
        for u in cs:
            w = w - (u.T * w)[0] * u
        for u in cs:  # second pass
            w = w - (u.T * w)[0] * u
        nv = mp.sqrt((w.T * w)[0])
        if nv > mp.mpf(10) ** (-mp.mp.dps // 2):
            cs.append(w / nv)
    P = mp.eye(n)
    for u in cs:
        P = P - u * u.T
    E, U = mp.eigsy(P)
    cols = [i for i in range(n) if E[i] > mp.mpf("0.5")]
    Q = mp.matrix(n, len(cols))
    for c, i in enumerate(cols):
        for r in range(n):
            Q[r, c] = U[r, i]
    ev, _, _ = eig_sym(Q.T * B * Q)
    return ev[0]


# ----------------------------------------------------------------------------------------------
def check():
    """Cross-validate the Legendre Gram against the validated generic functional W_components
    (g = phi_j * phi_k~ evaluated by exact inner Gauss-Legendre) and a quadrature-doubling test."""
    mp.mp.dps = 40
    a = mp.log(2) / 2 + mp.mpf("0.25")  # includes the primes 2, 3 (2a = 1.19)
    K = 12
    S = legendre_gram(a, K)
    S2 = legendre_gram(a, K, panels=8)
    dd = max(abs(S2["G"][i, j] - S["G"][i, j]) for i in range(K) for j in range(K))
    out = ["Legendre Gram cross-check, a=%s, K=%d: panel-doubling change %s" % (mp.nstr(a, 8), K, mp.nstr(dd, 4))]
    for j, k in ((0, 0), (1, 1), (2, 0), (5, 3), (11, 11)):
        def g(x, j=j, k=k):
            x = mp.mpf(x)
            if x >= 0:
                return corr(K, a, x, K + 4)[j][k] if x < 2 * a else mp.mpf(0)
            return corr(K, a, -x, K + 4)[k][j] if -x < 2 * a else mp.mpf(0)
        comp = wf.W_components(g, 2 * a, [0])
        out.append("  entry (%d,%d): Legendre-Gram %s   generic W_components %s   diff %s" % (
            j, k, mp.nstr(S["G"][j, k], 20), mp.nstr(comp["W"], 20), mp.nstr(S["G"][j, k] - comp["W"], 4)))
    open(os.path.join(RES, "cc_legendre_check.txt"), "w").write("\n".join(out) + "\n")
    print("\n".join(out))


def cc_crosscheck():
    """At 2L = log 2 (a = log(2)/2, no prime enters): smallest eigenvalues of
    (i) the full form (= archimedean + poles), (ii) W_inf = ARCH - CONST alone,
    (iii) W_inf on {F(0) = F(1) = 0} (CC1: ghat(+-i/2) = 0), (iv) W_inf on {F(0)=F(1)=0, int f = 0},
    per parity sector, for growing K.  Team cross-check value: 1.33e-3 (full form, even sector)."""
    mp.mp.dps = 50
    a = mp.log(2) / 2
    out = open(os.path.join(RES, "cc_crosscheck_log2.csv"), "w")
    out.write("K,sector,min_full_form,min_Winf_alone,min_Winf_on_ghat(i/2)=0,min_Winf_on_ghat(i/2)=ghat(0)=0\n")
    for K in (10, 16, 20, 24, 30, 40):
        t = time.time()
        S = legendre_gram(a, K)
        assert all(S["prime"][i, j] == 0 for i in range(K) for j in range(K))
        Winf = S["arch"] - S["const"]
        for par, name in ((0, "even"), (1, "odd")):
            Gs, idx = sector(S["G"], par)
            Ws, _ = sector(Winf, par)
            f0 = [S["F0"][j] for j in idx]
            f1 = [S["F1"][j] for j in idx]
            one = [mp.sqrt(2 * a) if j == 0 else mp.mpf(0) for j in idx]  # int phi_j = sqrt(2a) delta_j0
            r = (eig_sym(Gs)[0][0], eig_sym(Ws)[0][0], constrained_min(Ws, [f0, f1]), constrained_min(Ws, [f0, f1, one]))
            out.write("%d,%s,%s\n" % (K, name, ",".join(mp.nstr(x, 8) for x in r)))
            out.flush()
            print(K, name, [mp.nstr(x, 6) for x in r], "%.0fs" % (time.time() - t), flush=True)


def a_sweep():
    """Where does the smallest eigenvalue of A = POLE - CONST + ARCH (no primes) cross zero,
    per parity sector?  Also W_inf on {ghat(+-i/2)=0}.  CC2 section 2.2: 'a little past log 2'."""
    mp.mp.dps = 40
    out = open(os.path.join(RES, "cc_A_alone_sweep.csv"), "w")
    out.write("K,a,2a,mu=e^{2a},min_A_even,min_A_odd,min_Winf_constrained_even,min_Winf_constrained_odd\n")
    for K in (20, 30):
        for a in ("0.3466", "0.355", "0.36", "0.365", "0.37", "0.375", "0.38", "0.39", "0.40", "0.42", "0.45", "0.50"):
            a_ = mp.mpf(a)
            S = legendre_gram(a_, K)
            A = S["pole"] - S["const"] + S["arch"]
            Winf = S["arch"] - S["const"]
            r = []
            for par in (0, 1):
                As, idx = sector(A, par)
                r.append(eig_sym(As)[0][0])
            for par in (0, 1):
                Ws, idx = sector(Winf, par)
                r.append(constrained_min(Ws, [[S["F0"][j] for j in idx], [S["F1"][j] for j in idx]]))
            out.write("%d,%s,%s,%s,%s\n" % (K, a, mp.nstr(2 * a_, 6), mp.nstr(mp.exp(2 * a_), 6), ",".join(mp.nstr(x, 6) for x in r)))
            out.flush()
            print(K, a, [mp.nstr(x, 5) for x in r], flush=True)


def bisect_A(K, par, lo="0.3466", hi="0.45", steps=12):
    mp.mp.dps = 40
    def f(a):
        S = legendre_gram(a, int(K))
        As, _ = sector(S["pole"] - S["const"] + S["arch"], int(par))
        return eig_sym(As)[0][0]
    lo, hi = mp.mpf(lo), mp.mpf(hi)
    for _ in range(int(steps)):
        mid = (lo + hi) / 2
        if f(mid) > 0:
            lo = mid
        else:
            hi = mid
    line = "K=%s sector=%s: A alone PSD at a=%s, not at a=%s (2a in [%s,%s], mu in [%s,%s])" % (
        K, "even" if int(par) == 0 else "odd", mp.nstr(lo, 7), mp.nstr(hi, 7), mp.nstr(2 * lo, 6), mp.nstr(2 * hi, 6),
        mp.nstr(mp.exp(2 * lo), 6), mp.nstr(mp.exp(2 * hi), 6))
    open(os.path.join(RES, "cc_A_threshold_K%s_%s.txt" % (K, "even" if int(par) == 0 else "odd")), "w").write(line + "\n")
    print(line, flush=True)


# ----------------------------------------------------------------------------------------------
def pswf_eval(c, m_list, x):
    """Even prolates PS_{2m,0}(c, x) for x in [-1,1] (numpy, Legendre expansion, unnormalised sign
    fixed by value at 0 > 0 for even, derivative>0 for odd)."""
    import gram_experiments as ge
    N = 200
    ps = ge.pswf_legendre(c, 2 * max(m_list) + 4, N)
    L = ge.legendre_norm_eval(N, np.atleast_1d(x))
    vals = {}
    for idx, (chi, coef) in enumerate(ps):
        vals[idx] = coef @ L
    return vals  # index = prolate order (0,1,2,...) sorted by chi


def cc2_prolate():
    """CC2 section 3 setup (reconstructed from the reading notes): full semilocal Gram on
    [-L, L] (a = L, lambda = e^L, mu = e^{2L}); prolates psi_m(q) = PS_{2m,0}(c = 2 pi mu, q/lambda)
    in the additive variable q in [-lambda, lambda]; phi_n = psi_n psi_0(0) - psi_0 psi_n(0);
    E(phi)(u) = u^{1/2} sum_{1 <= r < lambda/u} phi(r u), u in [1/lambda, lambda] (our x = log u);
    Gram-Schmidt within each x -> -x parity class; compare with the eigenvectors of the smallest
    eigenvalues of the Gram matrix in the same class."""
    import gram_experiments as ge
    mp.mp.dps = 60
    out = open(os.path.join(RES, "cc2_prolate_comparison.txt"), "w")
    xg, wg = np.polynomial.legendre.leggauss(800)
    for mu, K in ((3.5, 40), (5.0, 48), (7.0, 56)):
        t0 = time.time()
        a = mp.log(mp.mpf(mu)) / 2
        af = float(a)
        lam = math.sqrt(mu)
        S = legendre_gram(a, K)
        G = S["G"]
        xs = af * xg  # nodes in x = log u
        ws = af * wg
        # Legendre basis on nodes (float) to express eigenvectors as functions
        Lb = ge.legendre_norm_eval(K, xg) / math.sqrt(af)  # (K, nodes)
        # prolates
        c = 2 * math.pi * mu
        nu = int(2 * mu - 1)
        ps = ge.pswf_legendre(c, 2 * nu + 4, 260)
        even_ps = [coef for chi, coef in ps if abs(coef[1::2]).sum() < 1e-12][: nu + 1]
        def psi(m, tq):
            return even_ps[m] @ ge.legendre_norm_eval(260, np.atleast_1d(tq))
        psi0_0 = [float(psi(m, 0.0)[0]) for m in range(nu + 1)]
        u = np.exp(xs)
        Ef = []
        for nidx in range(1, nu + 1):
            vals = np.zeros_like(u)
            rmax = np.floor(lam / u - 1e-12).astype(int)
            for r in range(1, int(rmax.max()) + 1):
                m = rmax >= r
                tq = r * u[m] / lam
                vals[m] += psi(nidx, tq) * psi0_0[0] - psi(0, tq) * psi0_0[nidx]
            Ef.append(np.sqrt(u) * vals)
        Ef = np.array(Ef)
        out.write("mu=%.2f (a=L=%.5f, lambda=%.4f, c=2 pi mu=%.3f, K=%d Legendre, nu=%d prolate differences)\n" % (mu, af, lam, c, K, nu))
        for par, pname in ((0, "even"), (1, "odd")):
            # parity parts of E-functions (x -> -x): nodes are symmetric (xg[::-1] = -xg)
            P = 0.5 * (Ef + (1 if par == 0 else -1) * Ef[:, ::-1])
            # Gram-Schmidt in L2(dx)
            Qs = []
            for v in P:
                w = v.copy()
                for q in Qs:
                    w -= (w * q * ws).sum() * q
                nv = math.sqrt((w * w * ws).sum())
                if nv > 1e-10 * math.sqrt((v * v * ws).sum()) and nv > 0:
                    Qs.append(w / nv)
            Gs, idx = sector(G, par)
            ev, Q, order = eig_sym(Gs)
            Vf = []
            for col in order[: max(1, len(Qs))]:
                cvec = np.array([float(Q[r, col]) for r in range(len(idx))])
                f = cvec @ Lb[idx]
                f /= math.sqrt((f * f * ws).sum())
                Vf.append(f)
            out.write("  %s sector: %d Gram-Schmidt E-functions; smallest Gram eigenvalues %s\n" % (
                pname, len(Qs), " ".join(mp.nstr(ev[i], 4) for i in range(min(6, len(ev))))))
            for k in range(min(len(Qs), len(Vf))):
                ov = abs((Qs[k] * Vf[k] * ws).sum())
                proj = math.sqrt(sum(((Vf[k] * q * ws).sum()) ** 2 for q in Qs))
                out.write("    k=%d: |<GS_k, v_k>| = %.6f ; norm of projection of v_k onto span(E-functions) = %.6f\n" % (k, ov, proj))
            # subspace diagnostics: cosines of principal angles between span(v_0..v_{m-1}) and span(E)
            Qm = np.array(Qs)
            Vm_all = np.array(Vf)
            cosines = []
            for m in range(1, min(len(Qs), len(Vf)) + 1):
                Mx = (Vm_all[:m] * ws) @ Qm.T
                cosines.append(np.linalg.svd(Mx, compute_uv=False).min())
            out.write("    min principal-angle cosine, span(v_0..v_{m-1}) vs span(E), m=1..: %s\n" % " ".join("%.6f" % x for x in cosines))
            # Rayleigh quotients of the E-functions (projected on the Legendre space) under G and under A only
            Gn = np.array([[float(Gs[i, j]) for j in range(Gs.cols)] for i in range(Gs.rows)])
            As_, _ = sector(S["pole"] - S["const"] + S["arch"], par)
            An = np.array([[float(As_[i, j]) for j in range(As_.cols)] for i in range(As_.rows)])
            rq = []
            for q in Qs:
                cq = (Lb[idx] * ws) @ q
                res = math.sqrt(max(0.0, 1 - cq @ cq))
                rq.append((cq @ Gn @ cq / (cq @ cq), cq @ An @ cq / (cq @ cq), res))
            out.write("    E-function Rayleigh quotients (G | A-only | L2 residual outside Legendre space):\n")
            for i, (g1, g2, r) in enumerate(rq):
                out.write("      GS_%d: %.3e | %.3e | %.1e\n" % (i, g1, g2, r))
            # control: random function projection
            rng = np.random.default_rng(3)
            rv = rng.standard_normal(K)
            rv[[j for j in range(K) if j % 2 != par]] = 0
            f = rv @ Lb
            f /= math.sqrt((f * f * ws).sum())
            proj = math.sqrt(sum(((f * q * ws).sum()) ** 2 for q in Qs))
            out.write("    control: random %s function in the same Legendre space, projection norm = %.4f\n" % (pname, proj))
        out.write("  (%.0fs)\n\n" % (time.time() - t0))
        out.flush()
        print(open(os.path.join(RES, "cc2_prolate_comparison.txt")).read(), flush=True)


# ----------------------------------------------------------------------------------------------
def leg_ft(K, a, z):
    """F_j(1/2 + i z) = int phi_j(x) e^{izx} dx = sqrt((2j+1)/(2a)) * 2a * i^j * j_j(a z) (spherical
    Bessel), computed by Gauss-Legendre (entire in z) for complex z."""
    xs, ws = wf.gl_nodes(K + 60)
    out = [mp.mpc(0)] * K
    for t, w in zip(xs, ws):
        v = phi_vals(K, a, a * t)
        e = mp.exp(1j * z * a * t) * w * a
        for j in range(K):
            out[j] += v[j] * e
    return out


def count_zeros_box(fun, T, Y, npts):
    """Argument principle on the rectangle [-T, T] x [-Y, Y]; returns the winding number."""
    pts = []
    for i in range(npts):
        pts.append(mp.mpc(-T + 2 * T * i / npts, -Y))
    for i in range(npts):
        pts.append(mp.mpc(T, -Y + 2 * Y * i / npts))
    for i in range(npts):
        pts.append(mp.mpc(T - 2 * T * i / npts, Y))
    for i in range(npts):
        pts.append(mp.mpc(-T, Y - 2 * Y * i / npts))
    vals = [fun(p) for p in pts]
    tot = mp.mpf(0)
    for i in range(len(vals)):
        d = mp.arg(vals[(i + 1) % len(vals)] / vals[i])
        tot += d
    return tot / (2 * mp.pi)


def cvs():
    """Connes-van Suijlekom-type test (reconstructed from the abstract): if the lowest eigenvalue is
    simple and isolated with an even eigenvector xi, all zeros of xihat should be real.  Count zeros
    of xihat in a box by the argument principle and compare with the number of real zeros."""
    mp.mp.dps = 40
    out = open(os.path.join(RES, "cvs_real_zeros_test.txt"), "w")
    for a, K, T in (("0.3466", 24, 60), ("0.5", 30, 60), ("1", 40, 40), ("1.5", 48, 32)):
        a_ = mp.mpf(a)
        S = legendre_gram(a_, K)
        for label, M in (("weil G", S["G"]), ("control A only (no primes)", S["pole"] - S["const"] + S["arch"])):
            res = []
            for par in (0, 1):
                Bs, idx = sector(M, par)
                ev, Q, order = eig_sym(Bs)
                res.append((ev[0], ev[1], par, idx, Q, order))
            res.sort(key=lambda r: r[0])
            e0, e1, par, idx, Q, order = res[0]
            c = [mp.mpf(0)] * K
            for r, j in enumerate(idx):
                c[j] = Q[r, order[0]]
            def xihat(z):
                v = leg_ft(K, a_, z)
                return mp.fsum(c[j] * v[j] for j in range(K))
            # real zeros on (-T, T): xihat real (even) or imaginary (odd) on R
            real_part = (lambda t: mp.re(xihat(t))) if par == 0 else (lambda t: mp.im(xihat(t)))
            nreal = 0
            step = mp.mpf("0.05")
            t = -mp.mpf(T) + step / 3
            fprev = real_part(t)
            while t < T:
                t += step
                fc = real_part(t)
                if fprev * fc < 0:
                    nreal += 1
                fprev = fc
            Y = mp.mpf(3)
            wind = count_zeros_box(xihat, mp.mpf(T) + mp.mpf("0.37"), Y, 1500)
            gap = (e1 - e0) / abs(e0) if e0 != 0 else mp.inf
            line = "a=%s K=%d %s: lowest eig %s (%s sector; next in that sector %s), zeros of xihat in box |Re|<%s,|Im|<3: %s ; real sign changes: %d" % (
                a, K, label, mp.nstr(e0, 5), "even" if par == 0 else "odd", mp.nstr(e1, 5), T, mp.nstr(wind, 6), nreal)
            out.write(line + "\n")
            out.flush()
            print(line, flush=True)


if __name__ == "__main__":
    globals()[sys.argv[1]](*sys.argv[2:])
