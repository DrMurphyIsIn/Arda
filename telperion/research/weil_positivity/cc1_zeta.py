#!/usr/bin/env python3
"""
Reconstruction of Connes-Consani CC1 (arXiv:2006.13771) section 5-6 objects, float64:
  xi_n = PS_{2n,0}(2 pi, x) on [-1,1], normalised by <xi|xi> = int_0^1 xi^2 = 1   (CC1 (16))
  lambda(n) from  int_{-1}^1 xi_n(y) exp(2 pi i x y) dy = lambda(n) xi_n(x)          (CC1 (68))
  xi_n^an(x) = lambda(n)^{-1} int_{-1}^1 xi_n(y) cos(2 pi x y) dy  (analytic continuation)
  eps(rho) = sum_n lambda^2/(1-lambda^2) rho^{1/2} int_{1/rho}^1 xi_n^an(x) xi_n^an(rho x) dx, rho >= 1
             (proof of CC1 Lemma 5.4)
  eps'(1+) = sum_n lambda^2/(1-lambda^2) xi_n(1)^2       (CC1: ~ 22.9965)
  Q = -(rho d/drho)^2 + 1/4, i.e. -d^2/dx^2 + 1/4 with rho = e^x
  chi(x) = (Q eps)(e^x) / (2 eps'(1+)),  K_I = convolution by chi(|x - y|) on L2(I),
  I = [-log2/2, log2/2]  (CC1 Prop 5.5 (104));  zeta = top eigenvector (CC1 Lemma 6.4 builds the
  finite-rank model T with ||K_I - T|| <= 0.00122; lambda_max(T) = 1.05158; Fact 6.5:
  <xi_0 | zeta> = 0.94865 with xi_0 = (log 2)^{-1/2}).
Then compares zeta with eigenvectors of our Weil Gram (Legendre basis) at a = log(2)/2.
Exploration only; conjecture1_proved = False.
"""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS"):
    os.environ.setdefault(_v, "1")
import sys, math
import numpy as np
import gram_experiments as ge

HERE = os.path.dirname(os.path.abspath(__file__))
RES = os.path.join(HERE, "results")
NMAX = 7
c = 2 * math.pi
yg, wg = np.polynomial.legendre.leggauss(300)

ps = ge.pswf_legendre(c, 2 * NMAX + 2, 120)
even = [coef for chi, coef in ps if np.abs(coef[1::2]).sum() < 1e-13][:NMAX]
XI, LAM = [], []
for coef in even:
    coef = coef * math.sqrt(2) / np.linalg.norm(coef)   # int_0^1 xi^2 = 1
    vals = coef @ ge.legendre_norm_eval(120, yg)
    lam = (vals * wg).sum() / (coef @ ge.legendre_norm_eval(120, np.array([0.0])))[0]
    XI.append(vals)
    LAM.append(lam)
LAM = np.array(LAM)


def xi_an(n, x):
    x = np.atleast_1d(x)
    return (np.cos(2 * math.pi * np.outer(x, yg)) @ (XI[n] * wg)) / LAM[n]


W = LAM ** 2 / (1 - LAM ** 2)
xi1 = np.array([xi_an(n, 1.0)[0] for n in range(NMAX)])
epsp = (W * xi1 ** 2).sum()


def eps_rho(rho):
    # rho^{1/2} int_{1/rho}^1 xi(x) xi(rho x) dx by Gauss-Legendre on [1/rho, 1]
    t, w = np.polynomial.legendre.leggauss(80)
    lo = 1 / rho
    x = lo + (1 - lo) * (t + 1) / 2
    ww = w * (1 - lo) / 2
    s = 0.0
    for n in range(NMAX):
        s += W[n] * (xi_an(n, x) * xi_an(n, rho * x) * ww).sum()
    return math.sqrt(rho) * s


# eps(e^x) on [0, log 2]: Chebyshev fit, then Q = -d2/dx2 + 1/4
L2 = math.log(2)
deg = 60
xc = (np.cos(np.pi * (np.arange(deg + 1) + 0.5) / (deg + 1)) + 1) * L2 / 2
E = np.array([eps_rho(math.exp(x)) for x in xc])
cheb = np.polynomial.chebyshev.Chebyshev.fit(xc, E, deg, domain=[0, L2])
QE = lambda x: -cheb.deriv(2)(x) + cheb(x) / 4
chi = lambda x: QE(np.abs(x)) / (2 * epsp)

# K_I by Nystrom on I = [-L2/2, L2/2]
out = []
out.append("lambda(n) = " + " ".join("%.6g" % l for l in LAM) + "   (CC1: 0.999971 -0.979485 0.524086 -0.0589766 0.00273233 -7.6e-5)")
out.append("t(n) = " + " ".join("%.6g" % v for v in W * xi1 ** 2) + "   (CC1: 11.9719 8.77574 2.20528 0.0433983 0.000125459)")
out.append("eps'(1+) = %.6f (CC1 ~ 22.9965);  (Q eps)(1) = %.3e (CC1 Remark 5.6: 0);  sum lambda^2 xi(1)^2 = %.6f (CC1: 2)"
           % (epsp, QE(0.0), (LAM ** 2 * xi1 ** 2).sum()))
results = {}
for N in (200, 400, 800):
    x, w = np.polynomial.legendre.leggauss(N)
    x = x * L2 / 2
    w = w * L2 / 2
    Kmat = chi(x[:, None] - x[None, :]) * np.sqrt(w[:, None] * w[None, :])
    ev, U = np.linalg.eigh(Kmat)
    zeta = U[:, -1] / np.sqrt(w)
    zeta *= np.sign((zeta * w).sum())
    xi0 = (zeta * w).sum() / math.sqrt(L2)   # <xi_0 | zeta>, xi_0 = (log 2)^{-1/2}
    results[N] = (x, w, zeta)
    out.append("Nystrom N=%d: top eigenvalues of K_I %s ; <xi_0|zeta> = %.5f  (CC1: lambda_max(T)=1.05158, lambda_2=0.686494, lambda_3=0.0288921; Fact 6.5: 0.94865)"
               % (N, " ".join("%.6f" % e for e in ev[::-1][:4]), xi0))

# comparison with our Weil-form eigenvectors at a = log(2)/2 (Legendre basis, cc_followup)
import mpmath as mp
import cc_followup as cf
mp.mp.dps = 40
a = mp.log(2) / 2
K = 40
S = cf.legendre_gram(a, K)
x, w, zeta = results[800]
Lb = ge.legendre_norm_eval(K, x / (L2 / 2)) / math.sqrt(L2 / 2)
mats = {"full form (poles + W_inf; = G here)": S["G"], "W_inf alone": S["arch"] - S["const"]}
for name, Mx in mats.items():
    Bs, idx = cf.sector(Mx, 0)
    ev, Q, order = cf.eig_sym(Bs)
    for k in range(3):
        cvec = np.zeros(K)
        for r, j in enumerate(idx):
            cvec[j] = float(Q[r, order[k]])
        f = cvec @ Lb
        f /= math.sqrt((f * f * w).sum())
        out.append("%s, even eigvec #%d (eig %s): |<v, zeta>| = %.5f" % (name, k, mp.nstr(ev[order[k]] if False else ev[k], 6), abs((f * zeta * w).sum())))
# constrained W_inf (ghat(+-i/2)=0): lowest eigenvector
Winf = S["arch"] - S["const"]
Bs, idx = cf.sector(Winf, 0)
f0 = np.array([float(S["F0"][j]) for j in idx])
v = f0 / np.linalg.norm(f0)
P = np.eye(len(idx)) - np.outer(v, v)
Bn = np.array([[float(Bs[i, j]) for j in range(Bs.cols)] for i in range(Bs.rows)])
e2, U2 = np.linalg.eigh(P @ Bn @ P + 1e3 * np.outer(v, v))
cvec = np.zeros(K)
cvec[idx] = U2[:, 0]
f = cvec @ Lb
f /= math.sqrt((f * f * w).sum())
out.append("W_inf on ghat(+-i/2)=0, lowest even eigvec (eig %.5f): |<v, zeta>| = %.5f" % (e2[0], abs((f * zeta * w).sum())))
out.append("constant function (xi_0): |<xi_0, zeta>| = %.5f" % abs((zeta * w).sum() / math.sqrt(L2)))
out.append("zeta samples x=0, +-0.1, +-0.2, +-0.3, +-0.34: " + " ".join("%.4f" % np.interp(t, x, zeta) for t in (0, 0.1, 0.2, 0.3, 0.34)))
open(os.path.join(RES, "cc1_zeta_comparison.txt"), "w").write("\n".join(out) + "\n")
print("\n".join(out))
