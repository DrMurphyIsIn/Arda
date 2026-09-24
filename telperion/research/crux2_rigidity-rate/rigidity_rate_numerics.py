"""Crux round 2, lens rigidity-rate: numerics for the pole-shadow fakes.

conjecture1_proved = False.  Nothing here says anything about the zeros of zeta.  These are float /
mpmath computations (not interval-certified) that illustrate, and cross-check, the kernel-checked
statements in telperion/examples/li_positivity/lean/Crux/Crux2_rigidity_rate.lean.

The fake:  F(s) = zeta(s) / (zeta_{>=X}(s + d - i t) * zeta_{>=X}(s + d + i t)),
           zeta_{>=X}(w) = zeta(w) * prod_{p < X} (1 - p^{-w}),
with Dirichlet coefficients a_n = prod_{p^j || n} c_p(j), c_p(j) = 1 (p < X),
c_p(1) = 1 - 2 p^{-d} cos(t log p), c_p(j >= 2) = |1 - p^{-d + i t}|^2 (p >= X).

Sections:
  N1  zero of F at s0 = 1 - d + i t: winding numbers, and the kernel-checked limit
      F(s)/(s - s0) -> zeta(s0) / (prod_{p<X}(1 - 1/p) * zeta_{>=X}(1 + 2 i t))   (t != 0)
  N2  t = 0: double real zero, F(s)/(s - s0)^2 -> zeta(1 - d) / prod_{p<X}(1 - 1/p)^2
  N3  Dirichlet series vs closed form at s = 2 + 3i (identification on Re s > 1)
  N4  the MTY instance T = 14, A = 3.86 (X = T^A, d = log 2 / log X)
  N5  theta-window defect: rigorous bound for X = 1e6, Y = 1e10 (sharper than round-1 script)
  N6  expulsion: the kernel lower bound for |F(sigma)| (t = 0) and the implied counting constant
  N7  t != 0: growth of |F(sigma + i t)| left of the zero (heuristic companion of N6)
Run:  /usr/bin/python3 rigidity_rate_numerics.py   (writes rigidity_rate_numerics_out.json)
"""
import json
import math
import time

import mpmath as mp
import numpy as np

OUT = {}


def primes_below(n):
    sieve = np.ones(max(n, 2), dtype=bool)
    sieve[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = False
    return np.nonzero(sieve)[0]


def log_prod_one_minus(ps, w):
    """sum_{p in ps} log(1 - p^{-w}) for complex w (numpy complex128, principal logs)."""
    w = complex(w)
    lp = np.log(ps.astype(np.float64))
    z = np.exp(-w * lp)
    return np.sum(np.log1p(-z))


def zeta_tail(ps, w):
    """zeta_{>=X}(w) = zeta(w) * prod_{p<X} (1 - p^{-w}) as an mpmath complex."""
    return mp.zeta(w) * mp.exp(mp.mpc(log_prod_one_minus(ps, w)))


def F(ps, d, t, s):
    return mp.zeta(s) / (zeta_tail(ps, s + d - 1j * t) * zeta_tail(ps, s + d + 1j * t))


def winding(fun, center, r, N=400):
    acc = mp.mpf(0)
    prev = fun(center + r)
    for k in range(1, N + 1):
        cur = fun(center + r * mp.exp(2j * mp.pi * k / N))
        acc += mp.im(mp.log(cur / prev))
        prev = cur
    return float(acc / (2 * mp.pi))


mp.mp.dps = 30
t0 = time.time()

# ---------------- N1: the zero and its order ----------------
N1 = []
for (X, d, t) in [(50, 0.2, 10.0), (50, math.log(2) / math.log(50) * 1.0001, 14.0),
                  (200, math.log(2) / math.log(200) * 1.0001, 40.0),
                  (10 ** 6, math.log(2) / math.log(10 ** 6) * 1.0001, 10.0)]:
    ps = primes_below(X)
    s0 = mp.mpc(1 - d, t)
    f = lambda s: F(ps, d, t, s)
    P1 = mp.exp(mp.mpf(float(np.sum(np.log1p(-1.0 / ps.astype(np.float64))))))
    C0 = mp.zeta(s0) / (P1 * zeta_tail(ps, 1 + 2j * t))
    fd = [abs(f(s0 + h) / h) for h in (1e-4, 1e-6)]
    N1.append({
        "X": X, "delta": d, "t": t, "s0": [float(mp.re(s0)), t],
        "Xdelta": X ** d,
        "abs_F_over_h_(h=1e-4,1e-6)": [float(v) for v in fd],
        "kernel_limit_abs_zeta(s0)/(P1*|zeta_>=X(1+2it)|)": float(abs(C0)),
        "abs_zeta_s0": float(abs(mp.zeta(s0))),
        "winding_F_r=0.01": winding(f, s0, mp.mpf('0.01'), 200 if X > 10 ** 5 else 400),
        "winding_zeta_r=0.01": winding(mp.zeta, s0, mp.mpf('0.01'), 200),
    })
OUT["N1_zero_and_order"] = N1

# ---------------- N2: double real zero at t = 0 ----------------
X, d = 50, 0.2
ps = primes_below(X)
s0 = mp.mpf(1 - d)
P1 = mp.exp(mp.mpf(float(np.sum(np.log1p(-1.0 / ps.astype(np.float64))))))
C2 = mp.zeta(s0) / P1 ** 2
fd2 = [abs(F(ps, d, 0.0, s0 + h) / h ** 2) for h in (1e-3, 1e-5)]
OUT["N2_double_real_zero"] = {
    "X": X, "delta": d, "s0": float(s0),
    "abs_F/h^2_(h=1e-3,1e-5)": [float(v) for v in fd2],
    "kernel_limit_abs_zeta(1-d)/P1^2": float(abs(C2)),
    "zeta(1-d)": float(mp.re(mp.zeta(s0))),
    "winding_F_r=0.01": winding(lambda s: F(ps, d, 0.0, s), mp.mpc(s0), mp.mpf('0.01'), 400),
}

# ---------------- N3: Dirichlet series = closed form on Re s > 1 ----------------
def fake_coeffs(X, d, t, nmax):
    spf = np.zeros(nmax + 1, dtype=np.int64)
    for i in range(2, nmax + 1):
        if spf[i] == 0:
            spf[i::i][spf[i::i] == 0] = i
    a = np.ones(nmax + 1)
    a[0] = 0.0
    for n in range(2, nmax + 1):
        p = int(spf[n]); m = n; j = 0
        while m % p == 0:
            m //= p; j += 1
        if p < X:
            c = 1.0
        else:
            al = p ** (-d) * complex(math.cos(t * math.log(p)), math.sin(t * math.log(p)))
            c = 1 - 2 * al.real if j == 1 else abs(1 - al) ** 2
        a[n] = a[m] * c
    return a


X, d, t = 50, 0.2, 10.0
a = fake_coeffs(X, d, t, 200000)
s = 2 + 3j
ns = np.arange(1, len(a))
dir_sum = complex(np.sum(a[1:] * np.exp(-s * np.log(ns))))
closed = complex(F(primes_below(X), d, t, mp.mpc(2, 3)))
tail_bound = float(sum((n ** (math.log(2.25) / math.log(X))) * n ** -2.0 for n in range(200001, 400001)) +
                   (400000 ** (math.log(2.25) / math.log(X) - 1)))
OUT["N3_identification_Re_s>1"] = {
    "X": X, "delta": d, "t": t, "s": [2, 3], "N_terms": 200000,
    "dirichlet_partial_sum": [dir_sum.real, dir_sum.imag],
    "closed_form_F": [closed.real, closed.imag],
    "abs_diff": abs(dir_sum - closed),
    "crude_tail_bound": tail_bound,
    "min_a_n": float(a[1:].min()), "all_a_n_eq_1_below_X": bool(np.all(a[1:X] == 1.0)),
}

# ---------------- N4: MTY instance ----------------
T, A = 14.0, 3.86
X = T ** A
d = math.log(2) / math.log(X)
ps = primes_below(int(math.ceil(X)))
s0 = mp.mpc(1 - d, T)
mty = 1 - 1 / (5.558691 * math.log(T))
OUT["N4_MTY_instance"] = {
    "T": T, "A": A, "X=T^A": X, "num_primes_below_X": int(len(ps)),
    "delta=log2/logX": d, "Xdelta": X ** d,
    "s0": [1 - d, T], "MTY_boundary_1-1/(5.558691 log T)": mty, "s0_re_minus_boundary": (1 - d) - mty,
    "winding_F_r=0.01": winding(lambda z: F(ps, d, T, z), s0, mp.mpf('0.01'), 300),
    "winding_zeta_r=0.01": winding(mp.zeta, s0, mp.mpf('0.01'), 200),
    "abs_zeta_s0": float(abs(mp.zeta(s0))),
    "note": "a_n = 1 for all n < T^A by construction (fakeCoeff_eq_one_of_lt)",
}

# ---------------- N5: theta window, rigorous bound ----------------
# |D(y)| <= 2 (1 + sqrt Y) sum_{n >= X} |a_n - 1| e^{-pi n^2 / Y},  |a_n - 1| <= n^kappa,
# kappa = log(9/4)/log X (a_n >= 0 and a_n <= (9/4)^{#p>=X dividing n} <= n^kappa);
# f(x) = x^kappa e^{-a x^2} decreasing on [X, inf) and x^kappa <= X^{kappa-1} x there, so
# sum_{n>=X} f(n) <= X^kappa e^{-a X^2} (1 + 1/(2 a X)),  a = pi / Y.
mp.mp.dps = 50
Xb, Y = mp.mpf(10) ** 6, mp.mpf(10) ** 10
kap = mp.log(mp.mpf(9) / 4) / mp.log(Xb)
aa = mp.pi / Y
tail = Xb ** kap * mp.e ** (-aa * Xb * Xb) * (1 + 1 / (2 * aa * Xb))
bound = 2 * (1 + mp.sqrt(Y)) * tail
decreasing_check = bool(Xb ** 2 > kap / (2 * aa))
OUT["N5_theta_window"] = {
    "X": 1e6, "Y": 1e10, "kappa": float(kap),
    "rigorous_bound_|D(y)|_on_[1/Y,Y]": mp.nstr(bound, 6), "log10_bound": float(mp.log10(bound)),
    "f_decreasing_on_[X,inf)": decreasing_check,
    "round1_script_bound_log10": -121.63347812871082,
    "note": "Riemann theta relation theta_F(1/y) = sqrt(y) theta_F(y) holds for zeta exactly; for "
            "the fake the defect is carried by the coefficients n >= X only.",
}
mp.mp.dps = 30

# ---------------- N6: expulsion (t = 0), the kernel lower bound ----------------
N6 = []
theta = 0.5
sigma = 0.6
for X in [50, 200, 10 ** 3, 10 ** 4, 10 ** 5, 10 ** 6]:
    eta = math.log(2) / math.log(X) * 1.0001
    if sigma + eta >= 1:
        continue
    ps = primes_below(X)
    sp = sigma + eta
    S = float(np.sum(ps.astype(np.float64) ** (-sp)))
    LB_log = (math.log(sigma / (1 - sigma) - 0.5) + 2 * S - 2 * math.log(sp / (1 - sp) + 0.5))
    Fsig = F(ps, eta, 0.0, mp.mpf(sigma))
    zs = mp.zeta(mp.mpf(sigma))
    ub_zeta = sigma / (1 - sigma) + 0.5
    # K >= (sigma-theta) X^{sigma-theta} / sigma * (|F(sigma)| - |zeta(sigma)|)
    Kmin_log_actual = math.log((sigma - theta) / sigma) + (sigma - theta) * math.log(X) + float(mp.log(abs(Fsig) - abs(zs)))
    LB = math.exp(LB_log)
    Kmin_log_kernel = (math.log((sigma - theta) / sigma) + (sigma - theta) * math.log(X) + math.log(LB - ub_zeta)) if LB > ub_zeta else None
    N6.append({
        "X": X, "eta": eta, "sigma": sigma, "theta": theta,
        "S=sum_{p<X} p^{-(sigma+eta)}": S,
        "log_kernel_lower_bound_|F(sigma)|": LB_log,
        "log_|F(sigma)|_mpmath": float(mp.log(abs(Fsig))),
        "zeta(sigma)": float(mp.re(zs)),
        "log_Kmin_from_kernel_bound": Kmin_log_kernel,
        "log_Kmin_from_actual_|F|": Kmin_log_actual,
        "X^(1-theta-eta)/log X": X ** (1 - theta - eta) / math.log(X),
    })
OUT["N6_expulsion_real_fake"] = N6

# ---------------- N7: t != 0, growth left of the zero ----------------
N7 = []
t = 10.0
for X in [50, 10 ** 3, 10 ** 4, 10 ** 6]:
    eta = math.log(2) / math.log(X) * 1.0001
    ps = primes_below(X)
    row = {"X": X, "eta": eta, "t": t}
    for sig in [0.55, 0.6, 0.7]:
        v = F(ps, eta, t, mp.mpc(sig, t))
        row["log|F(%.2f+it)|" % sig] = float(mp.log(abs(v)))
        row["log|zeta(%.2f+it)|" % sig] = float(mp.log(abs(mp.zeta(mp.mpc(sig, t)))))
        row["S(%.2f)=sum p^-(sig+eta)" % sig] = float(np.sum(ps.astype(np.float64) ** (-(sig + eta))))
    N7.append(row)
OUT["N7_growth_t_nonzero"] = N7

OUT["runtime_s"] = time.time() - t0
OUT["conjecture1_proved"] = False
json.dump(OUT, open("rigidity_rate_numerics_out.json", "w"), indent=1, default=str)
print(json.dumps(OUT, indent=1, default=str))
