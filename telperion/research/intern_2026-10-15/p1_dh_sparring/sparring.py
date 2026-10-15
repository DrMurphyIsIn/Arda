#!/usr/bin/env python3
"""
Pitch 1: Davenport-Heilbronn as a sparring partner.  Exploration only; nothing here is progress on
RH.  conjecture1_proved = False.

The Davenport-Heilbronn function f = (1 - i kappa)/2 L(s, chi) + (1 + i kappa)/2 L(s, chibar)
(chi mod 5, chi(2) = i) has the functional equation of an odd degree-1 L-function of conductor 5
and no Euler product.  Its Weil form fails positivity at the off-line zero 0.8085 + 85.699i
(../../weil_positivity/dh_control.py, a = 2, n = 188: min eigenvalue -0.6398).

The control this script adds is an EULER-PRODUCT SIBLING with identical archimedean data.  For
real test functions f, g = f * f~ is even, and the Weil form of L(s, chi) restricted to real f is

    W_sib(g) = ARCH - CONST - sum_n Lambda(n) Re chi(n) n^{-1/2} (g(log n) + g(-log n)),

with exactly DH's ARCH (Gamma((s+1)/2)) and CONST (euler + log pi - log 5), because both the
gamma factor and the conductor are shared.  Under GRH for L(s, chi mod 5), which is numerically
known at these heights, W_sib(f * f~) = sum over zeros of L(s, chi) of |F_f(rho)|^2 >= 0.
So DH and the sibling differ ONLY in the coefficient sequence c(n) of -L'/L:

    DH:      c_DH(n)  from -f'/f by Dirichlet division (not supported on prime powers; at primes
             c_DH(p) = a(p) log p with a(p) in {1, kappa, -kappa, -1} for p = 1, 2, 3, 4 mod 5)
    sibling: c_sib(n) = Lambda(n) Re chi(n), Re chi(n) in {1, 0, 0, -1} for n = 1, 2, 3, 4 mod 5

and the Gram matrix is G(c) = ARCH - CONST - sum_n c(n) P_n with P_n Toeplitz (B-spline basis of
weil_form.py).  Everything below is an experiment on the coefficient sequence with the archimedean
side held fixed.

Usage:
  sparring.py build    --a 2          # mp (dps 30) ARCH/CONST/MASS columns, cached as JSON
  sparring.py validate                # sibling explicit formula vs zeros of L(s, chi mod 5)
  sparring.py analyse  --a 2          # float64 experiments E1-E5, writes results/
"""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ.setdefault(_v, "1")
import sys
import json
import math
import time
import argparse
import mpmath as mp
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
WP = os.path.normpath(os.path.join(HERE, "..", "..", "weil_positivity"))
sys.path.insert(0, WP)
import weil_form as wf  # noqa: E402
import dh_control as dh  # noqa: E402

RES = os.path.join(HERE, "results")
os.makedirs(RES, exist_ok=True)
CHI = [0, 1, 1j, -1j, -1]  # chi mod 5, chi(2) = i, indexed by n mod 5


def n_for(a):
    return int(mp.ceil(2 * mp.mpf(a) * 150 / mp.pi)) - 3  # same grid as dh_control.gram


# ------------------------------------------------------------------------------------------------
# coefficient sequences
# ------------------------------------------------------------------------------------------------
def lambda_table(N):
    """(Lambda(n), p, k) for n <= N (Lambda = 0, p = 0 for non prime powers)."""
    out = [(0.0, 0, 0)] * (N + 1)
    for n, L in wf.prime_powers(N):
        p = int(round(math.exp(float(L))))
        k = round(math.log(n) / math.log(p))
        out[n] = (float(L), p, k)
    return out


def coeff_sets(N):
    """Named coefficient sequences c(n), n = 0..N (float64)."""
    lt = lambda_table(N)
    c_dh = np.array([float(x) for x in dh.cn(N)])
    kap = float(dh.kappa())
    a_tab = [0.0, 1.0, kap, -kap, -1.0]
    rechi = np.array([CHI[n % 5].real if isinstance(CHI[n % 5], complex) else float(CHI[n % 5]) for n in range(N + 1)])
    lam = np.array([lt[n][0] for n in range(N + 1)])
    is_pp = lam > 0
    is_p = np.array([lt[n][2] == 1 for n in range(N + 1)])
    c_sib = lam * rechi
    # formal Euler product with DH's prime values: -d/ds log prod_p (1 - a(p) p^-s)^-1
    c_euler_dh = np.zeros(N + 1)
    for n in range(2, N + 1):
        L, p, k = lt[n]
        if L > 0:
            c_euler_dh[n] = L * a_tab[p % 5] ** k
    sets = {
        "DH": c_dh,
        "sibling L(chi)": c_sib,
        "DH on prime powers only": np.where(is_pp, c_dh, 0.0),
        "DH off prime powers only": np.where(is_pp, 0.0, c_dh),
        "Euler product of DH's a(p) (no FE)": c_euler_dh,
        "sibling at primes, DH elsewhere": np.where(is_p, c_sib, c_dh),
        "DH at primes, sibling elsewhere": np.where(is_p, c_dh, c_sib),
        "sibling + DH's p^k (k>=2) terms": np.where(is_pp & ~is_p, c_dh, c_sib),
        "sibling + DH's non-prime-power terms": np.where(is_pp, c_sib, c_dh),
        "no primes at all": np.zeros(N + 1),
    }
    meta = dict(lam=lam, is_pp=is_pp, is_p=is_p, rechi=rechi)
    return sets, meta


# ------------------------------------------------------------------------------------------------
# build: archimedean columns in mp, cached
# ------------------------------------------------------------------------------------------------
def cache_path(a, n):
    return os.path.join(RES, "base_a%s_n%d.json" % (a, n))


def build(a):
    mp.mp.dps = 30
    n = n_for(a)
    t0 = time.time()
    S = wf.spline_gram(a, n, prime_lambda=[], lfun=dh.lfun())
    cols = S["cols"]
    mass = [S["MASS"][0, m] for m in range(n)]
    out = dict(a=a, n=n, h=str(S["h"]), dps=30,
               arch=[str(x) for x in cols["arch"]], const=[str(x) for x in cols["const"]],
               pole=[str(x) for x in cols["pole"]], prime=[str(x) for x in cols["prime"]],
               mass=[str(x) for x in mass])
    json.dump(out, open(cache_path(a, n), "w"))
    print("built a=%s n=%d in %.0fs" % (a, n, time.time() - t0))


def toep(col):
    col = np.asarray(col, dtype=float)
    n = len(col)
    idx = np.abs(np.arange(n)[:, None] - np.arange(n)[None, :])
    return col[idx]


def load_base(a):
    n = n_for(a)
    d = json.load(open(cache_path(a, n)))
    h = float(d["h"])
    A = toep([float(x) for x in d["arch"]]) - toep([float(x) for x in d["const"]]) + toep([float(x) for x in d["pole"]])
    assert max(abs(float(x)) for x in d["prime"]) == 0.0
    M = toep([float(x) for x in d["mass"]])
    return n, h, A, M


def prime_mats(a, n, h, N):
    """P[nn] = Toeplitz matrix of n^{-1/2} (g_m(log n) + g_m(-log n)), g_m = h M8((x - m h)/h)."""
    P = {}
    for nn in range(2, N + 1):
        ln = math.log(nn)
        col = []
        for m in range(n):
            v = 0.0
            for x in (ln, -ln):
                u = (x - m * h) / h
                if -4 < u < 4:
                    v += float(wf.bspline(8, u))
            col.append(h * v / math.sqrt(nn))
        if any(col):
            P[nn] = toep(col)
    return P


# ------------------------------------------------------------------------------------------------
# linear algebra
# ------------------------------------------------------------------------------------------------
class Pencil:
    def __init__(self, A, M, P):
        self.A, self.P = A, P
        L = np.linalg.cholesky(M)
        self.Li = np.linalg.inv(L)
        self.keys = sorted(P)
        # P in the orthonormalised basis
        self.Pt = {k: self.Li @ P[k] @ self.Li.T for k in self.keys}
        self.At = self.Li @ A @ self.Li.T

    def form(self, c):
        X = self.At.copy()
        for k in self.keys:
            if c[k] != 0:
                X -= c[k] * self.Pt[k]
        return (X + X.T) / 2

    def eig(self, c):
        return np.linalg.eigh(self.form(c))


def neg_stats(w, scale):
    tau = 1e-10 * scale
    neg = w[w < -tau]
    return len(neg), float(-neg.sum()) if len(neg) else 0.0


def fourier_peak(pen, a, n, h, u):
    """Peak |F| of the test function with orthonormal-coordinates vector u (B-spline coeffs Li^T u)."""
    c = pen.Li.T @ u
    cent = np.array([-a + (j + 2) * h for j in range(n)])
    ts = np.linspace(0.5, 160, 6400)
    F = np.abs(np.exp(1j * np.outer(ts, cent)) @ c) * np.sinc(ts * h / 2 / np.pi) ** 4
    return float(ts[F.argmax()]), ts, F


# ------------------------------------------------------------------------------------------------
# validation of the sibling's explicit formula
# ------------------------------------------------------------------------------------------------
def Lchi(s):
    return mp.dirichlet(s, CHI)


def Lam_chi(s):
    s = mp.mpc(s)
    return mp.power(5 / mp.pi, (s + 1) / 2) * mp.gamma((s + 1) / 2) * Lchi(s)


def chi_zeros(T, step=mp.mpf("0.05")):
    """Ordinates (both signs) of zeros of L(s, chi) on the line with |t| < T, by sign changes of the
    real rotation eps^{-1/2} Lambda(1/2 + it, chi)."""
    s0 = mp.mpf(1) / 2 + 3j
    eps = Lam_chi(s0) / mp.conj(Lam_chi(s0))
    rot = 1 / mp.sqrt(eps)
    Z = lambda t: mp.re(rot * Lam_chi(mp.mpf(1) / 2 + 1j * t))
    imag_check = abs(mp.im(rot * Lam_chi(mp.mpf(1) / 2 + mp.mpf("7.7") * 1j))) / abs(Lam_chi(mp.mpf(1) / 2 + mp.mpf("7.7") * 1j))
    out = []
    t = -T + step / 7
    f0 = Z(t)
    while t < T:
        t1 = t + step
        f1 = Z(t1)
        if f0 * f1 < 0:
            out.append(mp.findroot(Z, (t, t1), solver="anderson"))
        t, f0 = t1, f1
    return out, eps, imag_check


def validate():
    mp.mp.dps = 30
    lines = []
    t0 = time.time()
    zs, eps, ic = chi_zeros(40)
    lines.append("L(s, chi mod 5), chi(2) = i: root number eps = %s (|eps| = %s); |Im(eps^-1/2 Lambda)|/|Lambda| at t=7.7: %s"
                 % (mp.nstr(eps, 12), mp.nstr(abs(eps), 12), mp.nstr(ic, 3)))
    lines.append("zeros on the line with |t| < 40: %d (%.0fs); first positive: %s; first negative: %s" % (
        len(zs), time.time() - t0, [mp.nstr(z, 12) for z in zs if z > 0][:3], [mp.nstr(z, 12) for z in zs if z < 0][-3:]))
    # Riemann-von Mangoldt check of the count: N(T) for L(chi) with |t|<T  ~ (T/pi) log(5T/(2 pi e)) + O(log T)
    T = 40
    lines.append("count check: %d zeros vs (T/pi) log(5T/(2 pi e)) = %.2f (+O(log T))" % (len(zs), T / math.pi * math.log(5 * T / (2 * math.pi * math.e))))
    sib = [(n, L * mp.re(mp.mpc(CHI[n % 5]))) for n, L in wf.prime_powers(10 ** 6)]
    for s, d in ((mp.mpf("0.7"), 0), (mp.mpf("0.7"), mp.mpf("0.9")), (mp.mpf("0.6"), mp.mpf("-1.3")), (mp.mpf("0.8"), mp.mpf("0.4"))):
        g = lambda x, s=s, d=d: mp.exp(-(x - d) ** 2 / (2 * s * s))
        A = abs(d) + 13 * s
        pl = [(n, c) for n, c in sib if mp.log(n) < A]
        comp = wf.W_components(g, A, [d], prime_lambda=pl, lfun=dh.lfun())
        zside = mp.mpf(0)
        for gm in zs:
            z = 1j * gm
            zside += mp.re(s * mp.sqrt(2 * mp.pi) * mp.exp(z * d + s * s * z * z / 2))
        tail = s * mp.sqrt(2 * mp.pi) * mp.exp(-s * s * 40 ** 2 / 2) * 40
        lines.append("gaussian s=%s d=%s: formula side=%s zero side=%s diff=%s (tail<~%s)" % (
            mp.nstr(s, 3), mp.nstr(d, 3), mp.nstr(comp["W"], 22), mp.nstr(zside, 22), mp.nstr(comp["W"] - zside, 4), mp.nstr(tail, 3)))
    txt = "\n".join(lines) + "\n"
    open(os.path.join(RES, "validation_sibling.txt"), "w").write(txt)
    print(txt)


# ------------------------------------------------------------------------------------------------
# analyse
# ------------------------------------------------------------------------------------------------
def classify(nn, meta):
    if meta["is_p"][nn]:
        r = nn % 5
        return "primes = +-1 mod 5" if r in (1, 4) else ("primes = +-2 mod 5" if r in (2, 3) else "p = 5")
    if meta["is_pp"][nn]:
        return "prime powers p^k, k >= 2"
    return "non prime powers"


def analyse(a, ga_seed=1):
    af = float(a)
    n, h, A, M = load_base(a)
    N = int(math.floor(math.exp(2 * af)))
    t0 = time.time()
    P = prime_mats(af, n, h, N)
    pen = Pencil(A, M, P)
    sets, meta = coeff_sets(N)
    rep = []
    rep.append("a = %s, n = %d, h = %.5f, prime-side n <= %d (%d nonzero P_n); built in %.0fs" % (a, n, h, N, len(P), time.time() - t0))

    # E0: reproduce dh_control's DH minimum
    wDH, UDH = pen.eig(sets["DH"])
    scale = float(np.abs(wDH).max())
    rep.append("E0 reproduce: DH min eigenvalue %.6e (dh_control.py mp value at a=2: -0.639788)" % wDH[0])

    # E1: named coefficient surgeries
    rows = []
    for name, c in sets.items():
        w, U = pen.eig(c)
        k, e = neg_stats(w, scale)
        peak = fourier_peak(pen, af, n, h, U[:, 0])[0]
        rows.append((name, w[0], k, e, peak))
    with open(os.path.join(RES, "E1_surgeries_a%s.csv" % a), "w") as f:
        f.write("coefficients,min_eig,n_negative(<-1e-10*max),sum_negative,peak_t_of_min_eigvec\n")
        for r in rows:
            f.write("%s,%.6e,%d,%.6e,%.2f\n" % r)
    rep.append("E1 surgeries (min eig | #neg | sum|neg| | peak t of the min eigenvector's transform):")
    for r in rows:
        rep.append("   %-40s %+.4e  %4d  %.4e  t=%.2f" % r)

    # E2: interpolation DH -> sibling
    rows = []
    for th in np.linspace(0, 1, 41):
        c = (1 - th) * sets["DH"] + th * sets["sibling L(chi)"]
        w, U = pen.eig(c)
        k, e = neg_stats(w, scale)
        rows.append((th, w[0], k, e, fourier_peak(pen, af, n, h, U[:, 0])[0]))
    with open(os.path.join(RES, "E2_interpolation_a%s.csv" % a), "w") as f:
        f.write("theta,min_eig,n_negative,sum_negative,peak_t\n")
        for r in rows:
            f.write("%.4f,%.6e,%d,%.6e,%.2f\n" % r)
    rep.append("E2 interpolation c = (1-theta) c_DH + theta c_sib (theta, min eig, #neg, peak t):")
    for r in rows[::5] + [rows[-2]]:
        rep.append("   theta=%.3f  %+.4e  %3d  t=%.2f" % (r[0], r[1], r[2], r[4]))
    # G(theta) = (1 - theta) G_DH + theta G_sib (shared archimedean part), so lambda_min is concave in
    # theta; bisect for the onset of positivity and compare with the rank-one estimate at DH's witness.
    lo, hi = 0.0, 1.0
    for th in (r[0] for r in rows):
        if rows[[x[0] for x in rows].index(th)][1] >= 0:
            hi = th
            break
        lo = th
    for _ in range(50):
        mid = (lo + hi) / 2
        if np.linalg.eigvalsh(pen.form((1 - mid) * sets["DH"] + mid * sets["sibling L(chi)"]))[0] >= 0:
            hi = mid
        else:
            lo = mid
    v0 = UDH[:, 0]
    wd = float(v0 @ pen.form(sets["DH"]) @ v0)
    ws = float(v0 @ pen.form(sets["sibling L(chi)"]) @ v0)
    rep.append("   onset of positivity theta* = %.6f (bisection); witness-only estimate -W_DH(v)/(W_sib(v) - W_DH(v)) = %.6f"
               % (hi, -wd / (ws - wd)))

    # E3: witness attribution.  v = DH's minimal eigenvector (orthonormal coordinates)
    v = UDH[:, 0]
    q = {k: float(v @ pen.Pt[k] @ v) for k in pen.keys}
    arch_v = float(v @ pen.At @ v)
    dDH = sets["DH"]
    dS = sets["sibling L(chi)"]
    W_DH = arch_v - sum(dDH[k] * q[k] for k in pen.keys)
    W_S = arch_v - sum(dS[k] * q[k] for k in pen.keys)
    groups = {}
    for k in pen.keys:
        g = classify(k, meta)
        groups.setdefault(g, 0.0)
        groups[g] += -(dDH[k] - dS[k]) * q[k]
    rep.append("E3 at the DH witness v (||v|| = 1):  arch+const = %.6f,  W_DH(v) = %.6f,  W_sib(v) = %.6f" % (arch_v, W_DH, W_S))
    rep.append("   W_DH(v) - W_sib(v) = %.6f, by group of n:" % (W_DH - W_S))
    for g, val in sorted(groups.items(), key=lambda kv: kv[1]):
        rep.append("      %-28s %+.6f" % (g, val))
    top = sorted(pen.keys, key=lambda k: -(dDH[k] - dS[k]) * q[k])[:12]
    rep.append("   most negative single-n contributions -(c_DH - c_sib)(n) v^T P_n v:")
    rep.append("      " + ", ".join("n=%d: %+.4f" % (k, -(dDH[k] - dS[k]) * q[k]) for k in sorted(top, key=lambda k: -(dDH[k] - dS[k]) * q[k])[::-1][:12]))
    with open(os.path.join(RES, "E3_witness_terms_a%s.csv" % a), "w") as f:
        f.write("n,group,c_DH,c_sib,vPv,contribution_to_WDH_minus_Wsib\n")
        for k in pen.keys:
            f.write("%d,%s,%.10f,%.10f,%.6e,%.6e\n" % (k, classify(k, meta), dDH[k], dS[k], q[k], -(dDH[k] - dS[k]) * q[k]))

    # E4: Hellmann-Feynman gradient of lambda_min(DH) w.r.t. c(n): d lambda / d c(n) = -v^T P_n v
    # (sign and size of how each coefficient moves the bottom of the spectrum)

    # E5: sparse repair.  Replace c_DH(n) by c_sib(n) on a set S; smallest S with lambda_min >= -tau?
    diff_keys = [k for k in pen.keys if abs(dDH[k] - dS[k]) > 1e-14]
    tau = 1e-9 * scale

    def lam_min(mask):
        c = dDH.copy()
        for k, m in zip(diff_keys, mask):
            if m:
                c[k] = dS[k]
        return float(np.linalg.eigvalsh(pen.form(c))[0])

    # greedy
    mask = np.zeros(len(diff_keys), bool)
    traj = [(0, lam_min(mask))]
    while traj[-1][1] < -tau and not mask.all():
        best, bi = -np.inf, None
        for i in np.where(~mask)[0]:
            mask[i] = True
            v_ = lam_min(mask)
            mask[i] = False
            if v_ > best:
                best, bi = v_, i
        mask[bi] = True
        traj.append((int(mask.sum()), best))
    greedy_order = [diff_keys[i] for i in np.where(mask)[0]]
    rep.append("E5 sparse repair (replace c_DH(n) -> c_sib(n) on a set S; target lambda_min >= -%.1e): %d coefficients differ" % (tau, len(diff_keys)))
    rep.append("   greedy: |S| = %d reaches lambda_min = %.3e; trajectory (|S|, lambda_min) = %s" % (
        traj[-1][0], traj[-1][1], ", ".join("(%d, %.2e)" % t for t in traj[:: max(1, len(traj) // 12)] + [traj[-1]])))
    # genetic algorithm on masks: fitness = |S| + 1e3 * max(0, -lambda_min - tau) / scale
    rng = np.random.default_rng(ga_seed)
    D = len(diff_keys)
    pop = [rng.random(D) < p for p in np.linspace(0.3, 1.0, 40)]
    pop.append(mask.copy())

    def fit(m):
        lm = lam_min(m)
        return m.sum() + 1e4 * max(0.0, -lm - tau) / scale, lm

    scores = [fit(m) for m in pop]
    for gen in range(60):
        order = np.argsort([s[0] for s in scores])
        elite = [pop[i] for i in order[:10]]
        children = []
        while len(children) < 30:
            p1, p2 = rng.choice(10, 2, replace=False)
            cut = rng.random(D) < 0.5
            ch = np.where(cut, elite[p1], elite[p2])
            flip = rng.random(D) < 1.5 / D
            ch = ch ^ flip
            children.append(ch)
        pop = elite + children
        scores = [fit(m) for m in pop]
    bi = int(np.argmin([s[0] for s in scores]))
    ga_best = pop[bi]
    rep.append("   GA (40 pop, 60 gens, seed %d): best |S| = %d with lambda_min = %.3e (feasible: %s)" % (
        ga_seed, int(ga_best.sum()), scores[bi][1], scores[bi][1] >= -tau))
    with open(os.path.join(RES, "E5_repair_a%s.txt" % a), "w") as f:
        f.write("differing n: %s\n" % diff_keys)
        f.write("greedy order: %s\n" % greedy_order)
        f.write("greedy trajectory: %s\n" % traj)
        f.write("GA best set: %s\n" % [diff_keys[i] for i in np.where(ga_best)[0]])
        f.write("GA best lambda_min: %.6e\n" % scores[bi][1])
    txt = "\n".join(rep) + "\n"
    open(os.path.join(RES, "summary_a%s.txt" % a), "w").write(txt)
    print(txt)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["build", "validate", "analyse"])
    ap.add_argument("--a", default="2")
    ap.add_argument("--seed", type=int, default=1)
    args = ap.parse_args()
    if args.cmd == "build":
        build(args.a)
    elif args.cmd == "validate":
        validate()
    else:
        analyse(args.a, args.seed)
