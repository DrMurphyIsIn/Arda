#!/usr/bin/env python3
"""
Control experiment: the Davenport-Heilbronn function (DH), which satisfies a Riemann-type functional
equation but has no Euler product and has zeros OFF the critical line (first at ~0.8085 + 85.699i).
Its Weil form must therefore fail positivity once the test space can see that zero.  The point is to
show that the Gram-matrix test in weil_form.py is able to fail.  Exploration only; nothing here is
progress on RH.  conjecture1_proved = False.

  chi mod 5 with chi(2) = i;  kappa = (sqrt(10 - 2 sqrt5) - 2)/(sqrt5 - 1)
  f(s) = (1 - i kappa)/2 L(s, chi) + (1 + i kappa)/2 L(s, chibar) = sum a(n) n^{-s},
  a(n) = (0, 1, kappa, -kappa, -1)[n mod 5]   (real coefficients)
  Lambda_f(s) = (5/pi)^{s/2} Gamma((s+1)/2) f(s) = Lambda_f(1 - s)      (checked numerically)
  -f'/f(s) = sum c(n) n^{-s},  a(n) log n = sum_{d|n} c(d) a(n/d)

Explicit formula (same derivation as for zeta, Gamma((s+1)/2) instead of Gamma(s/2), no pole):
  sum_rho F(rho) = - sum_n c(n) n^{-1/2} (g(log n) + g(-log n)) - (euler + log pi - log 5) g(0)
                   + int_0^inf [2 e^{-2x} g(0) - e^{-3x/2}(g(x) + g(-x))]/(1 - e^{-2x}) dx

Usage:  dh_control.py validate | gram
"""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ.setdefault(_v, "1")
import sys
import time
import math
import mpmath as mp
import numpy as np
import weil_form as wf

HERE = os.path.dirname(os.path.abspath(__file__))
RES = os.path.join(HERE, "results")
os.makedirs(RES, exist_ok=True)


def kappa():
    return (mp.sqrt(10 - 2 * mp.sqrt(5)) - 2) / (mp.sqrt(5) - 1)


def coeffs(N):
    k = kappa()
    tab = [mp.mpf(0), mp.mpf(1), k, -k, mp.mpf(-1)]
    return [mp.mpf(0)] + [tab[n % 5] for n in range(1, N + 1)]


def cn(N):
    """c(n), n <= N, coefficients of -f'/f."""
    a = coeffs(N)
    c = [mp.mpf(0)] * (N + 1)
    # accumulate sum_{d|n, d<n} c(d) a(n/d) by sieve
    acc = [mp.mpf(0)] * (N + 1)
    for n in range(1, N + 1):
        c[n] = a[n] * mp.log(n) - acc[n]
        if c[n] != 0:
            for m in range(2 * n, N + 1, n):
                if a[m // n] != 0:
                    acc[m] += c[n] * a[m // n]
    return c


def f_dh(s):
    k = kappa()
    s = mp.mpc(s)
    return mp.power(5, -s) * (mp.zeta(s, mp.mpf(1) / 5) + k * mp.zeta(s, mp.mpf(2) / 5)
                              - k * mp.zeta(s, mp.mpf(3) / 5) - mp.zeta(s, mp.mpf(4) / 5))


def Lam(s):
    s = mp.mpc(s)
    return mp.power(5 / mp.pi, s / 2) * mp.gamma((s + 1) / 2) * f_dh(s)


LFUN = None


def lfun():
    return dict(arch_exp=mp.mpf(3) / 2, const_coef=mp.euler + mp.log(mp.pi) - mp.log(5), pole=False)


def prime_list(X):
    N = int(mp.floor(X))
    c = cn(N)
    return [(n, c[n]) for n in range(2, N + 1) if c[n] != 0]


def online_zeros(T, step=mp.mpf("0.02")):
    Z = lambda t: mp.re(Lam(mp.mpf(1) / 2 + 1j * t))
    out = []
    t = mp.mpf(step) / 3
    f0 = Z(t)
    while t < T:
        t1 = t + step
        f1 = Z(t1)
        if f0 * f1 < 0:
            out.append(mp.findroot(Z, (t, t1), solver="anderson"))
        t, f0 = t1, f1
    return out


def validate():
    mp.mp.dps = 30
    log = open(os.path.join(RES, "exp4_dh_validation.txt"), "w")
    s0 = mp.mpf("0.3") + 2j
    fe = abs(Lam(s0) - Lam(1 - s0)) / abs(Lam(s0))
    im = abs(mp.im(Lam(mp.mpf(1) / 2 + 7.3j))) / abs(Lam(mp.mpf(1) / 2 + 7.3j))
    log.write("functional equation |Lam(s)-Lam(1-s)|/|Lam(s)| at s=0.3+2i: %s ; |Im Lam(1/2+7.3i)|/|Lam| = %s\n" % (mp.nstr(fe, 5), mp.nstr(im, 5)))
    # real axis: any real zeros in (0,1)?
    vals = [mp.re(Lam(mp.mpf(k) / 20)) for k in range(1, 20)]
    log.write("Lam on (0,1) signs: %s\n" % "".join("+" if v > 0 else "-" for v in vals))
    t0 = time.time()
    zs = online_zeros(22)
    log.write("on-line zeros 0<t<22 (%d, %.0fs): %s\n" % (len(zs), time.time() - t0, [mp.nstr(z, 15) for z in zs]))
    # off-line zero near 0.8085 + 85.699i
    rho = mp.findroot(f_dh, mp.mpc("0.8085", "85.6993"))
    log.write("off-line zero refined: %s   |f(rho)| = %s\n" % (mp.nstr(rho, 15), mp.nstr(abs(f_dh(rho)), 3)))
    # Gaussian validation: g(x) = exp(-(x-d)^2/(2 s^2)); F(rho) = s sqrt(2pi) exp(z d + s^2 z^2 / 2), z = rho - 1/2
    lf = lfun()
    for s, d in ((mp.mpf("0.7"), 0), (mp.mpf("0.7"), mp.mpf("0.9")), (mp.mpf("0.6"), mp.mpf("-1.3")), (mp.mpf("0.8"), mp.mpf("0.4"))):
        g = lambda x, s=s, d=d: mp.exp(-(x - d) ** 2 / (2 * s * s))
        A = abs(d) + 13 * s
        pl = prime_list(mp.exp(A))
        comp = wf.W_components(g, A, [d], prime_lambda=pl, lfun=lf)
        zside = mp.mpf(0)
        for gm in zs:
            for z in (1j * gm, -1j * gm):
                zside += s * mp.sqrt(2 * mp.pi) * mp.exp(z * d + s * s * z * z / 2)
        zside = mp.re(zside)
        nextt = 22
        tail = s * mp.sqrt(2 * mp.pi) * mp.exp(-s * s * nextt ** 2 / 2) * 10
        log.write("gaussian s=%s d=%s: formula side=%s zero side=%s diff=%s (tail<~%s)\n" % (
            mp.nstr(s, 3), mp.nstr(d, 3), mp.nstr(comp["W"], 22), mp.nstr(zside, 22), mp.nstr(comp["W"] - zside, 4), mp.nstr(tail, 3)))
        log.flush()
    log.close()
    print(open(os.path.join(RES, "exp4_dh_validation.txt")).read())


def gram():
    """DH and zeta Weil Gram matrices (B-spline basis, h ~ pi/150 so frequency ~ 86 is resolved)."""
    mp.mp.dps = 30
    out = open(os.path.join(RES, "exp4_dh_gram.csv"), "w")
    out.write("function,a,n,h,min_gen_eig_float64,max_gen_eig_float64,min_gen_eig_mp,peak_|F|_of_min_eigvec_at_t\n")
    lf = lfun()
    for a in ("1", "2", "3", "4"):
        a_ = mp.mpf(a)
        n = int(mp.ceil(2 * a_ * 150 / mp.pi)) - 3
        pl = prime_list(mp.exp(2 * a_))
        for name, kw in (("DH", dict(prime_lambda=pl, lfun=lf)), ("zeta", {})):
            t0 = time.time()
            S = wf.spline_gram(a, n, **kw)
            G = mp2np(S["G"])
            M = mp2np(S["MASS"])
            L = np.linalg.cholesky(M)
            Li = np.linalg.inv(L)
            St = Li @ G @ Li.T
            St = (St + St.T) / 2
            w, U = np.linalg.eigh(St)
            c = Li.T @ U[:, 0]
            # where is the minimal eigenvector's Fourier transform concentrated?
            h = float(S["h"])
            cent = np.array([-float(a_) + (j + 2) * h for j in range(n)])
            ts = np.linspace(0.5, 160, 3200)
            F = np.array([abs(np.sum(c * np.exp(1j * t * cent))) * np.sinc(t * h / 2 / np.pi) ** 4 for t in ts])
            peak = ts[F.argmax()]
            mpmin = ""
            if name == "DH" and w[0] < 0 and n <= 200:
                ev, _ = wf.gen_eig(S["G"], S["MASS"])
                mpmin = mp.nstr(ev[0], 6)
            out.write("%s,%s,%d,%.5f,%.6e,%.6e,%s,%.2f\n" % (name, a, n, h, w[0], w[-1], mpmin, peak))
            out.flush()
            print(name, a, n, "min %.3e max %.3e peak t=%.2f  (%.0fs)" % (w[0], w[-1], peak, time.time() - t0), mpmin, flush=True)


def gram_scan():
    """Finer a-scan for the DH failure onset + mp confirmation of zeta positivity on the same basis."""
    mp.mp.dps = 30
    out = open(os.path.join(RES, "exp4_dh_onset_scan.csv"), "w")
    out.write("function,a,n,min_gen_eig_mp,max_gen_eig_mp\n")
    lf = lfun()
    for a in ("1.25", "1.5", "1.75"):
        a_ = mp.mpf(a)
        n = int(mp.ceil(2 * a_ * 150 / mp.pi)) - 3
        S = wf.spline_gram(a, n, prime_lambda=prime_list(mp.exp(2 * a_)), lfun=lf)
        ev, _ = wf.gen_eig(S["G"], S["MASS"])
        out.write("DH,%s,%d,%s,%s\n" % (a, n, mp.nstr(ev[0], 6), mp.nstr(ev[-1], 6)))
        out.flush()
        print("DH", a, n, mp.nstr(ev[0], 5), flush=True)
    mp.mp.dps = 40
    for a in ("2",):
        a_ = mp.mpf(a)
        n = int(mp.ceil(2 * a_ * 150 / mp.pi)) - 3
        S = wf.spline_gram(a, n)
        ev, _ = wf.gen_eig(S["G"], S["MASS"])
        out.write("zeta,%s,%d,%s,%s\n" % (a, n, mp.nstr(ev[0], 6), mp.nstr(ev[-1], 6)))
        out.flush()
        print("zeta", a, n, mp.nstr(ev[0], 5), flush=True)


def mp2np(M):
    return np.array([[float(M[i, j]) for j in range(M.cols)] for i in range(M.rows)])


if __name__ == "__main__":
    {"validate": validate, "gram": gram, "gram_scan": gram_scan}[sys.argv[1]]()
