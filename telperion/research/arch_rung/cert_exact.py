"""Exact-rational certificate for the pole-free archimedean rung (r-space route R).  2026-10-11.
Certified-in-script (exact rationals via python-flint fmpq; psiR floors cross-checked against arb
digamma).  NOT kernel-checked.  conjecture1_proved = False.

THEOREM SHAPE (blueprint section 1-3).  g : R -> C smooth, compact support, tsupport g in [-L, L],
L = L1 (rational, >= (log 2)/2), int g(u) e^{-u/2} du = 0  (paperFT g (I/2) = 0).  Then
    Re archSide (autocorr g) = -log(pi) ||g||^2 + (1/2pi) int |ghat|^2 psiR >= margin * ||g||^2.

CHAIN (every symbol below is a rational produced by this script, except pi, log pi, gamma,
which enter only through the rational bounds PI_LO <= pi, log pi <= LOGPI_UP, gamma <= GAMMA_UP):
  (S1) step floors: psiR(r) >= f_j for |r| >= r_j  (psiR_mono + psiR_ge_rational at r_j);
       s_j := f_j - LOGPI_UP;  v(r) := s_j on r_j <= |r| < r_{j+1}, v := s_J for |r| >= R = r_J.
  (S2) Q >= (1/2pi) int |ghat|^2 v = s_J ||g||^2 - (1/2pi) int_{|r|<R} |ghat|^2 d,  d := s_J - v >= 0.
  (S3) Taylor: for |r| <= R, ghat(r) = P(r) + E(r),  P(r) = sum_{k<M} q_k(r) mt_k,
       mt_k = int g(u) P_k(u/L) du  (Legendre moments),  q_k(r) = sum_{j<M} (i r L)^j S_{jk} / j!,
       t^j = sum_k S_{jk} P_k(t);   |E(r)| <= 2 ||g||_1 (|r| L)^M / M!  (Complex.exp_bound', needs R L <= (M+1)/2).
       |ghat|^2 <= (1+eta)|P|^2 + (1+1/eta)|E|^2.
  (S4) (1/2pi) int_{|r|<R} |P|^2 d = mt^* Z mt with Z = Zs / (2pi), Zs rational (computed here);
       (1/2pi) int_{|r|<R} |E|^2 d <= EPS ||g||^2  (uses ||g||_1^2 <= 2L ||g||^2, sq_l1_le).
  (S5) Bessel: ||g||^2 >= sum_k w_k |mt_k|^2,  w_k = (2k+1)/(2L).
  (S6) constraint: |c^T mt| <= ||g||_1 DELTA,  c_k = q_k(i/2) (real), DELTA = 2 (L/2)^M / M!  (Complex.exp_bound').
  (S7) CERTIFICATE: C := 2 PI_LO KAPPA W + 2 PI_LO RHO c c^T - (1+eta) Zs  is PSD (exact LDL^T,
       all pivots > 0), W = diag(w).  Hence (1+eta) mt^* Z mt <= KAPPA ||g||^2 + RHO |c^T mt|^2.
  (S8) margin := s_J - KAPPA - (1+1/eta) EPS - 2 L RHO DELTA^2 > 0.

usage: python cert_exact.py [config-name]
"""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[_v] = "1"
import sys
import time
import json
from fractions import Fraction as Fr
import numpy as np
from flint import fmpq, fmpq_poly, fmpq_mat, arb, acb, ctx

ctx.prec = 200

# ----------------------------------------------------------------------------- constants
GAMMA_UP = fmpq(58112, 100000)        # E6Bridge30 eulerMascheroni_le
PI_LO = fmpq(314159, 100000)          # Mathlib Real.pi_gt_d6 gives 3.141592 < pi; 3.14159 is weaker
E_HALF_L_UP = fmpq(12, 10)            # e^{L/2} <= 1.2 for L <= 0.36 (crude)
E_UP = fmpq(27183, 10000)             # e < 2.7183 (Mathlib Real.exp_one_lt_d9)

_GRID30 = [fmpq(j, 4) for j in range(121)]
CONFIGS = {
    # A: no new log-pi lemma (E6Bridge31 log_pi_le, 1.159).  R = 30, h = 1/4 (121 floors), M = 36.
    "A": dict(L=fmpq(1733, 5000), grid=_GRID30, M=36, eta=fmpq(1, 10000), rho=fmpq(10 ** 3),
              buf=fmpq(1, 1000), logpi=fmpq(1159, 1000), nser=40, mtail=10 ** 6),
    # B: with a new lemma log pi <= 1.1455 (3-term log(1-x) series at x = 1 - pi/4).
    "B": dict(L=fmpq(1733, 5000), grid=_GRID30, M=36, eta=fmpq(1, 10000), rho=fmpq(10 ** 3),
              buf=fmpq(1, 1000), logpi=fmpq(11455, 10000), nser=40, mtail=10 ** 6),
    # C: smaller (R = 24, 97 floors, M = 32), log pi <= 1.1455.
    "C": dict(L=fmpq(1733, 5000), grid=[fmpq(j, 4) for j in range(97)], M=32, eta=fmpq(1, 10000),
              rho=fmpq(10 ** 3), buf=fmpq(1, 1000), logpi=fmpq(11455, 10000), nser=40, mtail=10 ** 6),
    # first prototype (R = 40, M = 56)
    "full": dict(L=fmpq(1733, 5000), R=40, h=fmpq(1, 4), M=56, eta=fmpq(1, 10000),
                 rho=fmpq(10 ** 6), buf=fmpq(1, 1000), logpi=fmpq(11448, 10000), nser=40, mtail=10 ** 6),
}


def psiR_ge_rational(r, N, Mt, gamma_up=GAMMA_UP):
    """EXACT value of the left side of E6Bridge30 psiR_ge_rational r N Mt (gamma <- gamma_up)."""
    t = r / 2
    q = fmpq(1, 4)
    val = -gamma_up - q / (q * q + t * t)
    for n in range(N):
        x = fmpq(n)
        val += 1 / (x + 1) - (x + 1 + q) / ((x + 1 + q) ** 2 + t * t)
    Nn = fmpq(N)
    val += fmpq(1, 2) * (1 - (Nn + 1) ** 2 / ((Nn + 1 + q) ** 2 + t * t))
    NM = fmpq(N + Mt)
    val -= fmpq(1, 2) * (((NM + 1 + q) ** 2 + t * t) / (NM + 1) ** 2 - 1)
    return val


def round_down(x, den=10 ** 6):
    p, q = int(x.p), int(x.q)
    return fmpq((p * den) // q, den)


def psiR_arb(r):
    z = acb(arb(1) / 4, arb(r.p) / arb(r.q) / 2)
    return z.digamma().real


def legendre_T(M):
    """rows: P_k(t) as fmpq_poly, k < M."""
    t = fmpq_poly([0, 1])
    P = [fmpq_poly([1]), t]
    for k in range(1, M - 1):
        P.append(((2 * k + 1) * t * P[k] - k * P[k - 1]) / (k + 1))
    return P[:M]


def build(cfg):
    L, M = cfg["L"], cfg["M"]
    R, h = cfg.get("R"), cfg.get("h")
    eta, rho, logpi = cfg["eta"], cfg["rho"], cfg["logpi"]
    t0 = time.time()
    # ---- grid and floors
    if "grid" in cfg:
        grid = [fmpq(x) if not isinstance(x, fmpq) else x for x in cfg["grid"]]
    else:
        grid = [h * j for j in range(int(fmpq(R) / h) + 1)]
    J = len(grid) - 1
    floors = []
    for r in grid:
        ns = cfg["nser"](r) if callable(cfg["nser"]) else cfg["nser"]
        f = round_down(psiR_ge_rational(r, ns, cfg["mtail"]))
        tv = psiR_arb(r)
        assert arb(f.p) / arb(f.q) < tv, ("floor above psiR", r)
        floors.append(f)
    s = [f - logpi for f in floors]
    for j in range(J):
        assert s[j] <= s[J]
    sJ = s[J]
    d = [sJ - s[j] for j in range(J)]                     # weight on band j = [r_j, r_{j+1})
    # ---- Legendre / Taylor data
    P = legendre_T(M)
    T = fmpq_mat(M, M)
    for k in range(M):
        co = P[k].coeffs()
        for j, c in enumerate(co):
            T[k, j] = c
    S = T.inv()                                           # t^j = sum_k S[j,k] P_k  (S = T^{-1}: rows j)
    # check: T S = I  (T rows = P_k coefficients; t^j = sum_k S[j,k] P_k means S T = I as row ops)
    St = S
    fact = [fmpq(1)]
    for j in range(1, 2 * M + 2):
        fact.append(fact[-1] * j)
    # Q_k(r) = sum_{j = k mod 2} (-1)^{(j-k)/2} (rL)^j S[j,k] / j!
    Q = []
    for k in range(M):
        co = [fmpq(0)] * M
        for j in range(k % 2, M, 2):
            if St[j, k] != 0:
                sg = -1 if ((j - k) // 2) % 2 else 1
                co[j] = sg * L ** j * St[j, k] / fact[j]
        Q.append(co)
    # band moments mu_n = sum_j d_j (r_{j+1}^{n+1} - r_j^{n+1}) / (n+1), n < 2M
    pw = [[fmpq(1)] * (J + 1)]
    for n in range(1, 2 * M + 2):
        pw.append([pw[-1][j] * grid[j] for j in range(J + 1)])
    mu = []
    for n in range(2 * M):
        acc = fmpq(0)
        for j in range(J):
            acc += d[j] * (pw[n + 1][j + 1] - pw[n + 1][j])
        mu.append(acc / (n + 1))
    # Zs_kl = 2 * i^{l-k} * sum_{a,b} Q_k[a] Q_l[b] mu_{a+b}  (k+l even), 0 otherwise
    Zs = fmpq_mat(M, M)
    for k in range(M):
        for l in range(k, M):
            if (k + l) % 2:
                continue
            acc = fmpq(0)
            for a in range(k % 2, M, 2):
                qa = Q[k][a]
                if qa == 0:
                    continue
                for b in range(l % 2, M, 2):
                    qb = Q[l][b]
                    if qb != 0:
                        acc += qa * qb * mu[a + b]
            sg = -1 if ((l - k) // 2) % 2 else 1
            Zs[k, l] = Zs[l, k] = 2 * sg * acc
    # constraint vector c_k = q_k(i/2) = sum_j (-L/2)^j S[j,k] / j!
    c = [sum((((-L / 2) ** j) * St[j, k] / fact[j] for j in range(M)), fmpq(0)) for k in range(M)]
    w = [fmpq(2 * k + 1) / (2 * L) for k in range(M)]
    # EPS and DELTA
    eps_s = fmpq(0)
    for j in range(J):
        eps_s += d[j] * (pw[2 * M + 1][j + 1] - pw[2 * M + 1][j])
    # Mathlib Complex.exp_bound' : |x|/(M+1) <= 1/2 -> |e^x - T_M(x)| <= 2 |x|^M / M!.
    # Applied with x = i r u, |x| <= R L (needs R L <= (M+1)/2), and with x = -u/2 for the constraint.
    RL = grid[-1] * L
    assert 2 * RL <= M + 1, "exp_bound' side condition |x|/(M+1) <= 1/2 fails"
    EPS = 4 * 2 * L / (2 * PI_LO) * 2 * L ** (2 * M) * eps_s / ((2 * M + 1) * fact[M] ** 2)
    DELTA = 2 * (L / 2) ** M / fact[M]
    return dict(L=L, M=M, grid=grid, floors=floors, s=s, sJ=sJ, d=d, Zs=Zs, c=c, w=w,
                EPS=EPS, DELTA=DELTA, eta=eta, rho=rho, P=P, t_build=time.time() - t0)


def float_kappa(B):
    """kappa_opt ~ lambda_max of (1+eta) Z on c^perp in the W metric (float), for choosing KAPPA."""
    M = B["M"]
    Z = np.array([[float(B["Zs"][i, j]) for j in range(M)] for i in range(M)]) / (2 * np.pi)
    W = np.array([float(x) for x in B["w"]])
    c = np.array([float(x) for x in B["c"]])
    from scipy.linalg import null_space, eigh
    Ns = null_space(c[None, :])
    A = Ns.T @ Z @ Ns
    G = Ns.T @ np.diag(W) @ Ns
    return eigh(A, G, eigvals_only=True)[-1] * (1 + float(B["eta"]))


def ldl_psd(C):
    """Exact LDL^T; returns (ok, min pivot, D list)."""
    n = C.nrows()
    A = [[C[i, j] for j in range(n)] for i in range(n)]
    D = []
    for k in range(n):
        p = A[k][k]
        D.append(p)
        if p <= 0:
            return False, p, D
        for i in range(k + 1, n):
            f = A[i][k] / p
            if f == 0:
                continue
            Ai, Ak = A[i], A[k]
            for j in range(k + 1, i + 1):
                Ai[j] -= f * Ak[j]
        for i in range(k + 1, n):
            for j in range(k + 1, i):
                A[j][i] = A[i][j]
    return True, min(D), D


def certify(name):
    cfg = CONFIGS[name]
    B = build(cfg)
    M, L = B["M"], B["L"]
    kf = float_kappa(B)
    KAPPA = round_down(fmpq(int(kf * 10 ** 9), 10 ** 9) + cfg["buf"], 10 ** 6) + fmpq(1, 10 ** 6)
    t1 = time.time()
    C = fmpq_mat(M, M)
    for i in range(M):
        for j in range(M):
            v = 2 * PI_LO * B["rho"] * B["c"][i] * B["c"][j] - (1 + B["eta"]) * B["Zs"][i, j]
            if i == j:
                v += 2 * PI_LO * KAPPA * B["w"][i]
            C[i, j] = v
    ok, pmin, D = ldl_psd(C)
    t_ldl = time.time() - t1
    eta, rho = B["eta"], B["rho"]
    margin = B["sJ"] - KAPPA - (1 + 1 / eta) * B["EPS"] - 2 * L * rho * B["DELTA"] ** 2
    out = dict(config=name, L=str(L), M=M, R=str(B["grid"][-1]), bands=len(B["grid"]) - 1,
               sJ=float(B["sJ"]), kappa_float=kf, KAPPA=str(KAPPA), EPS=float(B["EPS"]),
               DELTA=float(B["DELTA"]), LDL_ok=ok, min_pivot=float(pmin),
               margin=float(margin), margin_exact=str(margin),
               t_build=round(B["t_build"], 1), t_ldl=round(t_ldl, 1))
    print(json.dumps(out, indent=1))
    return B, out, KAPPA, C, D


def ldl_factor(C):
    """exact LDL^T (unit lower L as list of rows, D list)."""
    n = C.nrows()
    A = [[C[i, j] for j in range(n)] for i in range(n)]
    Lm = [[fmpq(0)] * n for _ in range(n)]
    D = [fmpq(0)] * n
    for j in range(n):
        s = A[j][j] - sum((Lm[j][k] * Lm[j][k] * D[k] for k in range(j)), fmpq(0))
        D[j] = s
        Lm[j][j] = fmpq(1)
        for i in range(j + 1, n):
            t = A[i][j] - sum((Lm[i][k] * Lm[j][k] * D[k] for k in range(j)), fmpq(0))
            Lm[i][j] = t / s
    return Lm, D


def rounded_certificate(C, den=10 ** 12, delta=None):
    """Lean-sized certificate: C = Lt Dt Lt^T + Res with Lt, Dt short rationals and Res diagonally
    dominant with nonnegative diagonal (hence PSD).  Lt Dt is the rounded exact LDL^T of C - delta I,
    so Res = delta I + (rounding error).  Returns (Lt, Dt, ok, min dominance slack, max digits)."""
    n = C.nrows()
    if delta is None:
        Cf = np.array([[float(C[i, j]) for j in range(n)] for i in range(n)])
        lmin = np.linalg.eigvalsh(Cf)[0]
        delta = fmpq(int(lmin / 2 * 10 ** 6), 10 ** 6)
        assert delta > 0, lmin
    Cs = fmpq_mat(C)
    for i in range(n):
        Cs[i, i] -= delta
    Lm, D = ldl_factor(Cs)
    shrink = fmpq(1)
    Lt = [[round_down(Lm[i][j], den) if j < i else (fmpq(1) if i == j else fmpq(0)) for j in range(n)]
          for i in range(n)]
    Dt = [round_down(D[i] * shrink, den) for i in range(n)]
    LD = fmpq_mat(n, n)
    for i in range(n):
        for j in range(n):
            LD[i, j] = Lt[i][j] * Dt[j]
    Lt_m = fmpq_mat(n, n)
    for i in range(n):
        for j in range(n):
            Lt_m[i, j] = Lt[i][j]
    Res = C - LD * Lt_m.transpose()
    slack = None
    for i in range(n):
        off = sum((abs(Res[i, j]) for j in range(n) if j != i), fmpq(0))
        sl = Res[i, i] - off
        slack = sl if slack is None or sl < slack else slack
    digits = max(max(len(str(x.p)) + len(str(x.q)) for x in row) for row in Lt)
    digits = max(digits, max(len(str(x.p)) + len(str(x.q)) for x in Dt))
    return Lt, Dt, slack >= 0, slack, digits


if __name__ == "__main__":
    name = sys.argv[1] if len(sys.argv) > 1 else "A"
    B, out, KAPPA, C, D = certify(name)
    t = time.time()
    Lt, Dt, ok, slack, digits = rounded_certificate(C)
    print(f"rounded LDL certificate (LDL of C - delta I, entries rounded to 1e-12): residual diagonally dominant = {ok},"
          f" min slack = {float(slack):.3e}, max numerator+denominator digits = {digits}, {time.time() - t:.1f}s")
    dump = dict(out, grid=[str(x) for x in B["grid"]], floors=[str(x) for x in B["floors"]],
                eta=str(B["eta"]), rho=str(B["rho"]), PI_LO=str(PI_LO), GAMMA_UP=str(GAMMA_UP),
                LOGPI_UP=str(CONFIGS[name]["logpi"]), nser=CONFIGS[name]["nser"], mtail=CONFIGS[name]["mtail"],
                rounded_ok=ok, rounded_min_slack=float(slack),
                Dt=[str(x) for x in Dt], Lt=[[str(x) for x in row[:i]] for i, row in enumerate(Lt)])
    with open(f"cert_{name}.json", "w") as fh:
        json.dump(dump, fh)
    print(f"wrote cert_{name}.json")
