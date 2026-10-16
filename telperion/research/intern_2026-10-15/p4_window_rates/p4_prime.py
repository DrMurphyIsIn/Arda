#!/usr/bin/env python3
"""
Pitch 4, prime side: the Weil floor  floor(L) = lambda_min( W, Gram )  over polynomials of degree < 2N
on [-L, L] (both parity sectors), and how it changes as prime powers enter at L = log(n)/2.

Numerical exploration only.  Nothing here is progress on RH.  conjecture1_proved = False.
Finite-window Weil positivity is not RH.

This is a ball-arithmetic (python-flint arb) re-implementation of
../../weil_positivity/one_prime/one_prime.py :: PolyForm / poly_forms (same formulas, same quadrature
rules, same basis  phi_k(x) = P_{2k+par}(x/L) * (1 - (x/L)^2)^v ), done because the mpmath version
costs ~40 s per sector at N = 24.  `validate` checks it against poly_forms entry by entry.

  W(g*g~) = POLE - PRIME - CONST + ARCH       (convention of WEIL_POSITIVITY_SEARCH_2026-10-11.md sec 1)
  POLE  = gm gp^T + gp gm^T,  gp_j = int phi_j e^{x/2},  gm_j = int phi_j e^{-x/2}
  ARCH  = int_0^{2L} [2 e^{-2t} M - e^{-t/2} (F(t) + F(t)^T)] / (1 - e^{-2t}) dt - M log(1 - e^{-4L})
  PRIME = sum_{log n < 2L} Lambda(n) n^{-1/2} (F(log n) + F(log n)^T),
  F_jk(t) = int_{t-L}^{L} phi_j(x) phi_k(x - t) dx.

Subcommands
  validate                         compare with one_prime.poly_forms (mpmath) at a few (L, N, v)
  run  --L ... --N ... [--v 0]     floors on a list of L (comma list, or 'grid'), appends to a CSV
  analyse                          slopes, kink fits, predicted kinks -> results/*.md, *.csv
"""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ.setdefault(_v, "1")
import sys
import math
import json
import time
import argparse
import mpmath as mp
from flint import arb, arb_mat, ctx

HERE = os.path.dirname(os.path.abspath(__file__))
WP = os.path.normpath(os.path.join(HERE, "..", "..", "weil_positivity"))
sys.path.insert(0, WP)
import weil_form as wf  # noqa: E402  (imported, not edited)

RES = os.path.join(HERE, "results")
os.makedirs(RES, exist_ok=True)

THRESH = [(2, "2"), (3, "3"), (4, "4=2^2"), (5, "5"), (7, "7"), (8, "8=2^3"), (9, "9=3^2"), (11, "11")]


def lam_mangoldt(n):
    for p in range(2, n + 1):
        if n % p == 0:
            m = n
            while m % p == 0:
                m //= p
            return math.log(p) if m == 1 else 0.0
    return 0.0


# ----------------------------------------------------------------------------------------------
# arb helpers
# ----------------------------------------------------------------------------------------------
_GL = {}


def gl(q):
    key = (q, ctx.prec)
    if key not in _GL:
        xs, ws = [], []
        for k in range(q):
            x, w = arb.legendre_p_root(q, k, weight=True)
            xs.append(x)
            ws.append(w)
        _GL[key] = (xs, ws)
    return _GL[key]


def to_mp(x):
    """exact midpoint of an arb as mpf (at the current mp precision)."""
    m, e = x.mid().man_exp()
    return mp.ldexp(mp.mpf(int(m)), int(e))


def mat_to_mp(A):
    n, m = A.nrows(), A.ncols()
    out = mp.matrix(n, m)
    for i in range(n):
        for j in range(m):
            out[i, j] = to_mp(A[i, j])
    return out


def max_rad(A):
    r = 0.0
    for i in range(A.nrows()):
        for j in range(A.ncols()):
            r = max(r, float(A[i, j].rad()))
    return r


def legendre_list(D, u):
    v = [arb(1), u]
    for k in range(1, D):
        v.append(((2 * k + 1) * u * v[k] - k * v[k - 1]) / (k + 1))
    return v[:D + 1]


class FastForm:
    """Same object as one_prime.PolyForm, in arb.  L given as a decimal string."""

    def __init__(self, L, N, par, v=0, dps=60, nt=None, nv=None, extra_bits=160):
        ctx.prec = int(dps * 3.3219) + extra_bits
        mp.mp.dps = dps
        self.Ls = str(L)
        self.L = Lr = arb(self.Ls)
        self.N, self.par, self.v, self.dps = N, par, v, dps
        self.degs = [2 * k + par for k in range(N)]
        D = self.degs[-1] + 2 * v
        self.D = D
        self.nv = nv or (D + 3)
        self.nt = nt or (2 * D + 40)
        xs, ws = gl(self.nv)
        self.xs, self.ws = xs, ws
        Phi = [self.phi(Lr * x) for x in xs]
        rowsW = [[w * Lr * p for p in ph] for w, ph in zip(ws, Phi)]
        P = arb_mat(Phi)
        PW = arb_mat(rowsW)
        self.M = P.transpose() * PW
        ep = [(Lr * x / 2).exp() for x in xs]
        self.gp = [sum((rowsW[i][j] * ep[i] for i in range(self.nv)), arb(0)) for j in range(N)]
        self.gm = [sum((rowsW[i][j] / ep[i] for i in range(self.nv)), arb(0)) for j in range(N)]
        ts, wt = gl(self.nt)
        self.tn = [Lr * (t + 1) for t in ts]
        self.tw = [Lr * w for w in wt]

    def phi(self, x):
        u = x / self.L
        P = legendre_list(self.degs[-1] + 1, u)
        if self.v:
            fac = (1 - u * u) ** self.v
            return [P[d] * fac for d in self.degs]
        return [P[d] for d in self.degs]

    def corr(self, t):
        Lr = self.L
        lo, hi = t - Lr, Lr
        if not (hi > lo):
            return arb_mat(self.N, self.N)
        half, mid = (hi - lo) / 2, (hi + lo) / 2
        R1, R2 = [], []
        for x, w in zip(self.xs, self.ws):
            y = half * x + mid
            ww = w * half
            R1.append([ww * p for p in self.phi(y)])
            R2.append(self.phi(y - t))
        return arb_mat(R1).transpose() * arb_mat(R2)

    def pole(self):
        N = self.N
        return arb_mat([[self.gm[j] * self.gp[k] + self.gp[j] * self.gm[k] for k in range(N)] for j in range(N)])

    def arch(self, e=None):
        e = arb(1) / 2 if e is None else e
        N = self.N
        A = arb_mat(N, N)
        twoM = self.M * arb(2)
        for t, w in zip(self.tn, self.tw):
            F = self.corr(t)
            den = -((-2 * t).expm1())
            A += (twoM * (-2 * t).exp() - (F + F.transpose()) * (-e * t).exp()) * (w / den)
        return A - self.M * (-((-4 * self.L).expm1())).log()

    def lag(self, ell):
        F = self.corr(ell)
        return F + F.transpose()

    def forms(self, primes=True, weights=None):
        """dict of arb matrices M, POLE, K = ARCH - CONST, PR (prime matrix), G."""
        const = arb.pi().log() + arb.const_euler()
        K = self.arch() - self.M * const
        PO = self.pole()
        N = self.N
        PR = arb_mat(N, N)
        terms = []
        if primes:
            X = math.exp(2 * float(self.Ls)) + 2
            for n, lp in wf.prime_powers(X):
                ln = arb(n).log()
                if ln < 2 * self.L:
                    p = int(round(math.exp(float(lp))))  # the prime base, Lambda(n) = log p
                    wgt = arb(p).log() / arb(n).sqrt()
                    if weights is not None:
                        wgt = wgt * arb(str(weights.get(n, 1)))
                    PR += self.lag(ln) * wgt
                    terms.append(n)
        return dict(M=self.M, POLE=PO, K=K, PR=PR, G=PO + K - PR, terms=terms)


def floor_from(G, M, want_vec=True):
    """lambda_min of the pencil (G, M) in mpmath (current dps); returns (ev list, coefficient vectors)."""
    Gm, Mm = mat_to_mp(G), mat_to_mp(M)
    for i in range(Gm.rows):
        for j in range(i + 1, Gm.rows):
            s = (Gm[i, j] + Gm[j, i]) / 2
            Gm[i, j] = Gm[j, i] = s
            s = (Mm[i, j] + Mm[j, i]) / 2
            Mm[i, j] = Mm[j, i] = s
    return wf.gen_eig(Gm, Mm)


def endpoint_values(ff, c):
    """g(L), g(-L) for g = sum c_j phi_j (v = 0: P_d(+-1) = (+-1)^d)."""
    if ff.v:
        return mp.mpf(0), mp.mpf(0)
    gL = sum(c[j] for j in range(ff.N))
    gmL = sum(c[j] * (-1) ** d for j, d in enumerate(ff.degs))
    return gL, gmL


def case(L, N, par, v, dps, nt=None):
    t0 = time.time()
    ff = FastForm(L, N, par, v=v, dps=dps, nt=nt)
    F = ff.forms()
    rad = max_rad(F["G"])
    ev, V = floor_from(F["G"], F["M"])
    c = [V[r, 0] for r in range(N)]
    gL, gmL = endpoint_values(ff, c)
    return dict(L=str(L), N=N, par=par, v=v, dps=dps, nt=ff.nt, lam0=ev[0], lam1=ev[1], gL=gL, gmL=gmL,
                maxrad=rad, terms=F["terms"], sec=time.time() - t0)


# ----------------------------------------------------------------------------------------------
# validate against one_prime.poly_forms
# ----------------------------------------------------------------------------------------------
def cmd_validate(args):
    sys.path.insert(0, os.path.join(WP, "one_prime"))
    import one_prime as op
    for (L, N, par, v, dps) in [("0.549", 12, 0, 0, 60), ("0.75", 10, 1, 0, 60), ("1.0", 10, 0, 3, 80)]:
        t = time.time()
        R = op.poly_forms(L, N, par, dps=dps, vanish=v)
        t1 = time.time() - t
        t = time.time()
        ff = FastForm(L, N, par, v=v, dps=dps)
        F = ff.forms()
        t2 = time.time() - t
        out = []
        for key, keyR in (("M", "M"), ("G", "G"), ("PR", "PR")):
            A = mat_to_mp(F[key])
            B = R[keyR]
            d = max(abs(A[i, j] - B[i, j]) for i in range(N) for j in range(N))
            s = max(abs(B[i, j]) for i in range(N) for j in range(N))
            out.append("%s max|diff| %s (max entry %s)" % (key, mp.nstr(d, 3), mp.nstr(s, 3)))
        ev1, _ = op.pencil(R["G"], R["M"])
        ev2, _ = floor_from(F["G"], F["M"])
        print("L=%s N=%d par=%d v=%d dps=%d: %s; lam_min mpmath %s arb %s; time mpmath %.1fs arb %.1fs; arb max radius %.1e"
              % (L, N, par, v, dps, "; ".join(out), mp.nstr(ev1[0], 15), mp.nstr(ev2[0], 15), t1, t2, max_rad(F["G"])),
              flush=True)


# ----------------------------------------------------------------------------------------------
# runs
# ----------------------------------------------------------------------------------------------
def default_grid():
    g = [round(0.30 + 0.025 * k, 4) for k in range(int(round((1.175 - 0.30) / 0.025)) + 1)]
    for n, _ in THRESH:
        t = math.log(n) / 2
        if t < 1.18:
            for d in (-0.005, 0.005):
                g.append(round(t + d, 4))
    return sorted(set(g))


def est_log10_floor(L):
    return 3 + 38 * max(0.0, L - 0.33)


def cmd_run(args):
    Ls = default_grid() if args.L == "grid" else [float(x) for x in args.L.split(",")]
    if args.Lmin is not None:
        Ls = [x for x in Ls if x >= args.Lmin]
    if args.Lmax is not None:
        Ls = [x for x in Ls if x <= args.Lmax]
    out = args.out or os.path.join(RES, "prime_floor_raw.csv")
    new = not os.path.exists(out)
    fh = open(out, "a")
    if new:
        fh.write("L,N,par,v,dps,nt,lam0,lam1,gL,gmL,maxrad,terms,seconds\n")
    pars = [0, 1] if args.par == "both" else [int(args.par)]
    for L in Ls:
        dps = args.dps or int(40 + 2 * math.ceil(est_log10_floor(L)) + args.dps_extra)
        for par in pars:
            r = case("%.4f" % L, args.N, par, args.v, dps, nt=args.nt)
            fh.write("%s,%d,%d,%d,%d,%d,%s,%s,%s,%s,%.2e,%s,%.1f\n" % (
                r["L"], r["N"], par, r["v"], dps, r["nt"], mp.nstr(r["lam0"], 25), mp.nstr(r["lam1"], 12),
                mp.nstr(r["gL"], 15), mp.nstr(r["gmL"], 15), r["maxrad"], "|".join(map(str, r["terms"])), r["sec"]))
            fh.flush()
            print("L=%s N=%d par=%d v=%d dps=%d lam0=%s lam1=%s g(L)=%s g(-L)=%s (%.0fs)" % (
                r["L"], r["N"], par, r["v"], dps, mp.nstr(r["lam0"], 10), mp.nstr(r["lam1"], 5),
                mp.nstr(r["gL"], 5), mp.nstr(r["gmL"], 5), r["sec"]), flush=True)


# ----------------------------------------------------------------------------------------------
# analysis
# ----------------------------------------------------------------------------------------------
def load_raw(path):
    import csv
    rows = list(csv.DictReader(open(path)))
    return rows


def floors_table(rows, N, v, dpsmin=0):
    """{L: (floor, sector, gL, gmL)} using the latest row per (L, par) with given N, v."""
    d = {}
    for r in rows:
        if int(r["N"]) != N or int(r["v"]) != v or int(r["dps"]) < dpsmin:
            continue
        d[(float(r["L"]), int(r["par"]))] = r
    out = {}
    for (L, par), r in d.items():
        if (L, 1 - par) not in d:
            continue
        r0, r1 = d[(L, 0)], d[(L, 1)]
        lam0, lam1 = mp.mpf(r0["lam0"]), mp.mpf(r1["lam0"])
        b = r0 if lam0 <= lam1 else r1
        out[L] = dict(floor=min(lam0, lam1), even=lam0, odd=lam1, sec="even" if lam0 <= lam1 else "odd",
                      gL=mp.mpf(b["gL"]), gmL=mp.mpf(b["gmL"]), dps=int(b["dps"]))
    return dict(sorted(out.items()))


def linfit(xs, ys):
    import numpy as np
    A = np.vstack([np.ones(len(xs)), xs]).T
    coef, res, *_ = np.linalg.lstsq(A, np.array(ys), rcond=None)
    return coef


def kink_fits(F, thresholds, width=0.06, gap=0.0, order=2):
    """For each threshold Lt, fit log(floor) on [Lt - width, Lt) and (Lt, Lt + width] with polynomials of
    degree `order` (in L - Lt) and report one-sided slopes -d log floor/dL at Lt."""
    import numpy as np
    Ls = np.array(list(F.keys()))
    y = np.array([float(mp.log(F[L]["floor"])) for L in Ls])
    out = []
    for n, name in thresholds:
        Lt = math.log(n) / 2
        left = (Ls < Lt - gap) & (Ls >= Lt - width)
        right = (Ls > Lt + gap) & (Ls <= Lt + width)
        if left.sum() < order + 1 or right.sum() < order + 1:
            continue
        cl = np.polyfit(Ls[left] - Lt, y[left], order)
        cr = np.polyfit(Ls[right] - Lt, y[right], order)
        out.append(dict(n=n, name=name, Lt=Lt, sl=-cl[-2], sr=-cr[-2], nl=int(left.sum()), nr=int(right.sum()),
                        vl=cl[-1], vr=cr[-1]))
    return out


def predicted_kink(F, n):
    """first-order jump of -d log floor/dL at L = log(n)/2:  4 Lambda(n)/sqrt(n) g(L) g(-L) / floor,
    using the minimiser at the grid point nearest the threshold from below (g normalised, ||g|| = 1)."""
    Lt = math.log(n) / 2
    below = [L for L in F if L < Lt]
    if not below:
        return None
    L = max(below)
    r = F[L]
    lam = lam_mangoldt(n)
    return dict(L=L, val=float(4 * lam / math.sqrt(n) * r["gL"] * r["gmL"] / r["floor"]),
                g2=float(r["gL"] * r["gmL"]), floor=float(r["floor"]))


def cmd_analyse(args):
    import numpy as np
    rows = load_raw(args.raw)
    lines = []
    for N in sorted({int(r["N"]) for r in rows if int(r["v"]) == args.v}):
        F = floors_table(rows, N, args.v)
        if len(F) < 5:
            continue
        Ls = np.array(list(F.keys()))
        lf = np.array([float(mp.log(F[L]["floor"])) for L in Ls])
        lines.append("\n## N = %d per sector, v = %d (%d L values)\n" % (N, args.v, len(Ls)))
        lines.append("| L | floor | binding sector | even | odd | local slope -dlog/dL (centred) | slope/gamma_1 |")
        lines.append("|---|---|---|---|---|---|---|")
        for i, L in enumerate(Ls):
            if 0 < i < len(Ls) - 1:
                s = -(lf[i + 1] - lf[i - 1]) / (Ls[i + 1] - Ls[i - 1])
                ss = "%.2f | %.3f" % (s, s / 14.134725)
            else:
                ss = "- | -"
            r = F[L]
            lines.append("| %.4f | %s | %s | %s | %s | %s |" % (L, mp.nstr(r["floor"], 6), r["sec"], mp.nstr(r["even"], 4),
                                                              mp.nstr(r["odd"], 4), ss))
        csvp = os.path.join(RES, "prime_floor_N%d_v%d.csv" % (N, args.v))
        with open(csvp, "w") as fh:
            fh.write("L,floor,sector,even,odd,gL,gmL,dps\n")
            for L in Ls:
                r = F[L]
                fh.write("%.4f,%s,%s,%s,%s,%s,%s,%d\n" % (L, mp.nstr(r["floor"], 20), r["sec"], mp.nstr(r["even"], 15),
                                                          mp.nstr(r["odd"], 15), mp.nstr(r["gL"], 12), mp.nstr(r["gmL"], 12), r["dps"]))
        lines.append("\nKink fits (quadratic fits of log floor on each side, window 0.06, threshold points at +-0.005 included):\n")
        lines.append("| n | L_n = log(n)/2 | left slope | right slope | jump (right - left) | predicted jump 4 Lambda(n) n^-1/2 g(L)g(-L)/floor | g(L)g(-L) at grid point below |")
        lines.append("|---|---|---|---|---|---|---|")
        for k in kink_fits(F, THRESH, width=args.width, order=args.order):
            p = predicted_kink(F, k["n"])
            lines.append("| %s | %.4f | %.2f (%d pts) | %.2f (%d pts) | %+.2f | %s | %s |" % (
                k["name"], k["Lt"], k["sl"], k["nl"], k["sr"], k["nr"], k["sr"] - k["sl"],
                "%+.3g" % p["val"] if p else "-", "%.3g (L=%.4f)" % (p["g2"], p["L"]) if p else "-"))
    txt = "\n".join(lines) + "\n"
    open(os.path.join(RES, "prime_floor_v%d.md" % args.v), "w").write("# prime-side floors and kink fits\n" + txt)
    print(txt)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("validate")
    r = sub.add_parser("run")
    r.add_argument("--L", default="grid")
    r.add_argument("--Lmin", type=float)
    r.add_argument("--Lmax", type=float)
    r.add_argument("--N", type=int, default=24)
    r.add_argument("--v", type=int, default=0)
    r.add_argument("--par", default="both")
    r.add_argument("--dps", type=int, default=0)
    r.add_argument("--dps_extra", type=int, default=0)
    r.add_argument("--nt", type=int)
    r.add_argument("--out")
    a = sub.add_parser("analyse")
    a.add_argument("--raw", default=os.path.join(RES, "prime_floor_raw.csv"))
    a.add_argument("--v", type=int, default=0)
    a.add_argument("--width", type=float, default=0.06)
    a.add_argument("--order", type=int, default=2)
    args = ap.parse_args()
    dict(validate=cmd_validate, run=cmd_run, analyse=cmd_analyse)[args.cmd](args)


if __name__ == "__main__":
    main()
